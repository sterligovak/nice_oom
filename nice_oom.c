/*
Copyright (c) 2013, Alexander Sterligov
All rights reserved.

Redistribution and use in source and binary forms, with or without modification,
are permitted provided that the following conditions are met:

* Redistributions of source code must retain the above copyright notice, this
  list of conditions and the following disclaimer.

* Redistributions in binary form must reproduce the above copyright notice, this
  list of conditions and the following disclaimer in the documentation and/or
  other materials provided with the distribution.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR
ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
(INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON
ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*/

#include <sys/param.h>
#include <sys/module.h>
#include <sys/kernel.h>
#include <sys/systm.h>
#include <sys/lock.h>
#include <sys/mutex.h>
#include <sys/proc.h>
#include <sys/sched.h>
#include <sys/syslog.h>
#include <sys/mman.h>

#include <vm/vm.h>
#include <vm/vm_param.h>
#include <vm/vm_object.h>
#include <vm/vm_page.h>
#include <vm/vm_map.h>
#include <vm/vm_pageout.h>
#include <vm/vm_pager.h>
#include <vm/swap_pager.h>
#include <vm/vm_extern.h>
#include <vm/uma.h>

static int event_handler(struct module* module, int event, void *arg);

static moduledata_t 
nice_oom_conf = 
{
    "nice_oom",
    event_handler,
    NULL
};

DECLARE_MODULE(nice_oom, nice_oom_conf, SI_SUB_KTHREAD_PAGE, SI_ORDER_FIRST);

/*
* Original vm_pageout_oom, will be called if LRU pageout_oom will fail
*/
static void
original_vm_pageout_oom(int shortage)
{
	struct proc *p, *bigproc;
	vm_offset_t size, bigsize;
	struct thread *td;
	struct vmspace *vm;

	/*
	 * We keep the process bigproc locked once we find it to keep anyone
	 * from messing with it; however, there is a possibility of
	 * deadlock if process B is bigproc and one of it's child processes
	 * attempts to propagate a signal to B while we are waiting for A's
	 * lock while walking this list.  To avoid this, we don't block on
	 * the process lock but just skip a process if it is already locked.
	 */
	bigproc = NULL;
	bigsize = 0;
	sx_slock(&allproc_lock);
	FOREACH_PROC_IN_SYSTEM(p) {
		int breakout;

		if (PROC_TRYLOCK(p) == 0)
			continue;
		/*
		 * If this is a system, protected or killed process, skip it.
		 */
		if (p->p_state != PRS_NORMAL ||
		    (p->p_flag & (P_INEXEC | P_PROTECTED | P_SYSTEM)) ||
		    (p->p_pid == 1) || P_KILLED(p) ||
		    ((p->p_pid < 48) && (swap_pager_avail != 0))) {
			PROC_UNLOCK(p);
			continue;
		}
		/*
		 * If the process is in a non-running type state,
		 * don't touch it.  Check all the threads individually.
		 */
		breakout = 0;
		FOREACH_THREAD_IN_PROC(p, td) {
			thread_lock(td);
			if (!TD_ON_RUNQ(td) &&
			    !TD_IS_RUNNING(td) &&
			    !TD_IS_SLEEPING(td)) {
				thread_unlock(td);
				breakout = 1;
				break;
			}
			thread_unlock(td);
		}
		if (breakout) {
			PROC_UNLOCK(p);
			continue;
		}
		/*
		 * get the process size
		 */
		vm = vmspace_acquire_ref(p);
		if (vm == NULL) {
			PROC_UNLOCK(p);
			continue;
		}
		if (!vm_map_trylock_read(&vm->vm_map)) {
			vmspace_free(vm);
			PROC_UNLOCK(p);
			continue;
		}
		size = vmspace_swap_count(vm);
		vm_map_unlock_read(&vm->vm_map);
		if (shortage == VM_OOM_MEM)
			size += vmspace_resident_count(vm);
		vmspace_free(vm);
		/*
		 * if the this process is bigger than the biggest one
		 * remember it.
		 */
		if (size > bigsize) {
			if (bigproc != NULL)
				PROC_UNLOCK(bigproc);
			bigproc = p;
			bigsize = size;
		} else
			PROC_UNLOCK(p);
	}
	sx_sunlock(&allproc_lock);
	if (bigproc != NULL) {
		killproc(bigproc, "out of swap space");
		sched_nice(bigproc, PRIO_MIN);
		PROC_UNLOCK(bigproc);
		wakeup(&cnt.v_free_count);
	}
}

/*
* Pathed version of vm_pageout_oom
* It tries to unload LRU pages, if then it's still needed to find more memory, calls original vm_pageout_oom
*/
static void
vm_pageout_oom_unload_lru(int shortage)
{
	int addl_page_shortage_init, page_shortage, deactivated_count;
	int maxscan;
	vm_page_t m, next;
	struct vm_page marker;
	boolean_t unchanged;
	vm_object_t object;
	
	bzero(&marker, sizeof(marker));
	marker.flags = PG_MARKER;
	marker.oflags = VPO_BUSY;
	marker.queue = PQ_ACTIVE;
	marker.hold_count = 1;
	
	vm_page_lock_queues();
	
	addl_page_shortage_init = atomic_readandclear_int(&vm_pageout_deficit);
	page_shortage = vm_paging_target() + addl_page_shortage_init;
	deactivated_count = 0;
	
	maxscan = cnt.v_active_count;
	
	m = TAILQ_FIRST(&vm_page_queues[PQ_ACTIVE].pl);
	while ((m != NULL) && (maxscan-- > 0) && (page_shortage > 0)) {
	
		KASSERT(m->queue == PQ_ACTIVE,
		    ("vm_pageout_oom_unload_lru: page %p isn't active", m));
		
		next = TAILQ_NEXT(m, pageq);
		
		/*
		 * skip marker pages
		 */
		if ((m->flags & PG_MARKER) != 0) {
			m = next;
			continue;
		}
		
		/*
		* Lock the page while holding the page queue lock.  Use marker page
		* to detect page queue changes and maintain notion of next page on
		* page queue
		*/
		if ( !vm_page_trylock(m) ) {
			TAILQ_INSERT_AFTER(&vm_page_queues[PQ_ACTIVE].pl, m, &marker, pageq);
			vm_page_unlock_queues();
			vm_page_lock(m);
			vm_page_lock_queues();
			unchanged = (m->queue == PQ_ACTIVE && 
						&marker == TAILQ_NEXT(m, pageq));
			TAILQ_REMOVE(&vm_page_queues[PQ_ACTIVE].pl, &marker, pageq);
			
			if (!unchanged){
				vm_page_unlock(m);
				++page_shortage;
				m = next;
				continue;
			}
		}
		
		object = m->object;
		if (!VM_OBJECT_TRYLOCK(object)){
			/*
			* To avoid lock order violation, unlock the page queues
            * while locking the vm object.  Use marker page to detect page queue
            * changes and maintain notion of next page on page queue. 
			*/
			TAILQ_INSERT_AFTER(&vm_page_queues[PQ_ACTIVE].pl, m, &marker, pageq);
			vm_page_unlock_queues();
			vm_page_unlock(m);
			VM_OBJECT_LOCK(object);
			vm_page_lock(m);
			vm_page_lock_queues();
			next = TAILQ_NEXT(&marker, pageq);
			unchanged = (m->queue == PQ_ACTIVE && 
						m->object == object && 
						&marker == TAILQ_NEXT(m, pageq));
			TAILQ_REMOVE(&vm_page_queues[PQ_ACTIVE].pl, &marker, pageq);
		
			if (!unchanged) {
				VM_OBJECT_UNLOCK(object);
				vm_page_unlock(m);
				++page_shortage;
				m = next;
				continue;
			}
		}
		
		
		if (m->hold_count ||
			m->wire_count ||
			m->dirty ||
			m->busy ||
		    (m->oflags & VPO_BUSY) ) {
			vm_page_unlock(m);
			VM_OBJECT_UNLOCK(object);
			m = next;
			continue;
		}
		
		++deactivated_count;
		--page_shortage;
		
		m->act_count = 0;
		//vm_page_dontneed(m);
		vm_page_deactivate(m);
		
		vm_page_unlock(m);
		VM_OBJECT_UNLOCK(object);
		m = next;
	}
	vm_page_unlock_queues();
	
	if (page_shortage > 0 &&
		deactivated_count < 100) {
		log(LOG_ERR, "Deactivated %d pages to avoid OOM, still need %d\n", deactivated_count, page_shortage);
		if ((swap_pager_avail < 64 && vm_page_count_min()) ||
			 (swap_pager_full && vm_paging_target() > 0)) {
			original_vm_pageout_oom(shortage);
		}
	} else {
		log(LOG_ERR, "Deactivated %d pages to avoid OOM\n", deactivated_count);
	}
}

static int 
kernel_is_known(void) {
    static const unsigned char expected_vm_pageout_oom_begin[] = { 0x55, 0x89, 0xE5, 0x57 };
	static const unsigned char expected_vm_pageout_oom_begin_x64[] = { 0x55, 0x48, 0x89, 0xE5 };
	
    if (memcmp(vm_pageout_oom, expected_vm_pageout_oom_begin, sizeof(expected_vm_pageout_oom_begin)) != 0 &&
		memcmp(vm_pageout_oom, expected_vm_pageout_oom_begin_x64, sizeof(expected_vm_pageout_oom_begin_x64)) != 0 ){
        uprintf("Beginning of vm_pageout_oom is unexpected! Cannot patch kernel!\n");   
        return FALSE;
    }
    
    return TRUE;
}

static void
patch_kernel( void (*patched_vm_pageout_oom)(int) ) {
	static unsigned char jmp_shellcode[] = { 0xe9, 0x00, 0x00, 0x00, 0x00 }; /* jmp <displacement> */
	
    size_t destination_address = (size_t)patched_vm_pageout_oom;
    size_t source_address = (size_t)vm_pageout_oom;
    
    size_t instruction_address_after_inserted_jmp = source_address + sizeof(jmp_shellcode);
    size_t displacement = destination_address - instruction_address_after_inserted_jmp;

    *((int*)&jmp_shellcode[1]) = displacement;
	memcpy(vm_pageout_oom, jmp_shellcode, sizeof(jmp_shellcode));
}

static int
event_handler(struct module* module, int event, void *arg) {
	static char kernel_backup[100];
	static int kernel_is_patched = FALSE;
	
	int result = 0;
    
    switch (event) {
    case MOD_LOAD:
        if (kernel_is_known()) {
            memcpy(kernel_backup, vm_pageout_oom, sizeof(kernel_backup));
            patch_kernel(vm_pageout_oom_unload_lru);
			kernel_is_patched = TRUE;
        }
        else {    
		    uprintf("It's not safe to patch this kernel! Nice OOM has not been loaded!\n");
            result = EOPNOTSUPP;
        }
        break;
    case MOD_UNLOAD:
		if (kernel_is_patched){
			memcpy(vm_pageout_oom, kernel_backup, sizeof(kernel_backup));
			kernel_is_patched = FALSE;
		}
        break;
    default:
        result = EOPNOTSUPP;
        break;
    }

    return result;
}

