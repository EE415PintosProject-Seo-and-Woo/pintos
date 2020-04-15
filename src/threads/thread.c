#include "threads/thread.h"
#include <debug.h>
#include <stddef.h>
#include <random.h>
#include <stdio.h>
#include <string.h>
#include <limits.h>
#include "threads/flags.h"
#include "threads/interrupt.h"
#include "threads/intr-stubs.h"
#include "threads/palloc.h"
#include "threads/switch.h"
#include "threads/synch.h"
#include "threads/vaddr.h"
#include "fixed_point.h"
#ifdef USERPROG
#include "userprog/process.h"
#endif

/* Random value for struct thread's `magic' member.
   Used to detect stack overflow.  See the big comment at the top
   of thread.h for details. */
#define THREAD_MAGIC 0xcd6abf4b

/* List of processes in THREAD_READY state, that is, processes
   that are ready to run but not actually running. */
static struct list ready_list;

/* List of all processes.  Processes are added to this list
   when they are first scheduled and removed when they exit. */
static struct list all_list;

/* List of sleeping processes which called sleep function.
   Processes are added to this list with THREAD_BLOCKED state 
   when they call sleep and removed when the tick is over. */
static struct list sleep_list;

/* The minimum value of ticks of threads which in the sleep_list */
static int64_t global_tick = INT64_MAX;

/* Idle thread. */
static struct thread *idle_thread;

/* Initial thread, the thread running init.c:main(). */
static struct thread *initial_thread;

/* Lock used by allocate_tid(). */
static struct lock tid_lock;

/* Stack frame for kernel_thread(). */
struct kernel_thread_frame 
  {
    void *eip;                  /* Return address. */
    thread_func *function;      /* Function to call. */
    void *aux;                  /* Auxiliary data for function. */
  };

/* Statistics. */
static long long idle_ticks;    /* # of timer ticks spent idle. */
static long long kernel_ticks;  /* # of timer ticks in kernel threads. */
static long long user_ticks;    /* # of timer ticks in user programs. */

/* Scheduling. */
#define TIME_SLICE 4            /* # of timer ticks to give each thread. */
static unsigned thread_ticks;   /* # of timer ticks since last yield. */

/* If false (default), use round-robin scheduler.
   If true, use multi-level feedback queue scheduler.
   Controlled by kernel command-line option "-o mlfqs". */
bool thread_mlfqs;

#define INITIAL_CPU 0 /* Initial value of recent_cpu */
#define INITIAL_NICE 0 /* Initial value of nice */

/* load_avg is used to calculate advanced scheduling. */
static int load_avg = 0;

static void kernel_thread (thread_func *, void *aux);


static void idle (void *aux UNUSED);
static struct thread *running_thread (void);
static struct thread *next_thread_to_run (void);
static void init_thread (struct thread *, const char *name, int priority);
static bool is_thread (struct thread *) UNUSED;
static void *alloc_frame (struct thread *, size_t size);
static void schedule (void);
void thread_schedule_tail (struct thread *prev);
static tid_t allocate_tid (void);
void update_global_tick (int64_t ticks);
int64_t get_global_tick (void);
void thread_sleep (int64_t ticks);
void check_sleep_list (int64_t tt);
bool compare_priority(const struct list_elem *cur,
                  const struct list_elem *next,
		      void *aux UNUSED);
/* Initializes the threading system by transforming the code
   that's currently running into a thread.  This can't work in
   general and it is possible in this case only because loader.S
   was careful to put the bottom of the stack at a page boundary.

   Also initializes the run queue and the tid lock.

   After calling this function, be sure to initialize the page
   allocator before trying to create any threads with
   thread_create().

   It is not safe to call thread_current() until this function
   finishes. */
void
thread_init (void) 
{
  ASSERT (intr_get_level () == INTR_OFF);

  lock_init (&tid_lock);
  list_init (&ready_list);
  list_init (&all_list);
  list_init (&sleep_list);
  load_avg = 0;
  /* Set up a thread structure for the running thread. */
  initial_thread = running_thread ();
  init_thread (initial_thread, "main", PRI_DEFAULT);
  initial_thread->status = THREAD_RUNNING;
  initial_thread->tid = allocate_tid ();
  initial_thread->nice = INITIAL_NICE;
  initial_thread->recent_cpu = INITIAL_CPU;
}

/* Starts preemptive thread scheduling by enabling interrupts.
   Also creates the idle thread. */
void
thread_start (void) 
{
  /* Create the idle thread. */
  struct semaphore idle_started;
  sema_init (&idle_started, 0);
  thread_create ("idle", PRI_MIN, idle, &idle_started);

  /* Start preemptive thread scheduling. */
  intr_enable ();

  /* Wait for the idle thread to initialize idle_thread. */
  sema_down (&idle_started);
}

/* Called by the timer interrupt handler at each timer tick.
   Thus, this function runs in an external interrupt context. */
void
thread_tick (void) 
{
  struct thread *t = thread_current ();

  /* Update statistics. */
  if (t == idle_thread)
    idle_ticks++;
#ifdef USERPROG
  else if (t->pagedir != NULL)
    user_ticks++;
#endif
  else
    kernel_ticks++;

  /* Enforce preemption. */
  if (++thread_ticks >= TIME_SLICE)
    intr_yield_on_return ();
}

/* Prints thread statistics. */
void
thread_print_stats (void) 
{
  printf ("Thread: %lld idle ticks, %lld kernel ticks, %lld user ticks\n",
          idle_ticks, kernel_ticks, user_ticks);
}

/* Creates a new kernel thread named NAME with the given initial
   PRIORITY, which executes FUNCTION passing AUX as the argument,
   and adds it to the ready queue.  Returns the thread identifier
   for the new thread, or TID_ERROR if creation fails.

   If thread_start() has been called, then the new thread may be
   scheduled before thread_create() returns.  It could even exit
   before thread_create() returns.  Contrariwise, the original
   thread may run for any amount of time before the new thread is
   scheduled.  Use a semaphore or some other form of
   synchronization if you need to ensure ordering.

   The code provided sets the new thread's `priority' member to
   PRIORITY, but no actual priority scheduling is implemented.
   Priority scheduling is the goal of Problem 1-3. */
tid_t
thread_create (const char *name, int priority,
               thread_func *function, void *aux) 
{
  struct thread *t;
  struct kernel_thread_frame *kf;
  struct switch_entry_frame *ef;
  struct switch_threads_frame *sf;
  tid_t tid;
  enum intr_level old_level;

  ASSERT (function != NULL);

  /* Allocate thread. */
  t = palloc_get_page (PAL_ZERO);
  if (t == NULL)
    return TID_ERROR;

  /* Initialize thread. */
  init_thread (t, name, priority);
  tid = t->tid = allocate_tid ();

  /* Prepare thread for first run by initializing its stack.
     Do this atomically so intermediate values for the 'stack' 
     member cannot be observed. */
  old_level = intr_disable ();

  /* Stack frame for kernel_thread(). */
  kf = alloc_frame (t, sizeof *kf);
  kf->eip = NULL;
  kf->function = function;
  kf->aux = aux;

  /* Stack frame for switch_entry(). */
  ef = alloc_frame (t, sizeof *ef);
  ef->eip = (void (*) (void)) kernel_thread;

  /* Stack frame for switch_threads(). */
  sf = alloc_frame (t, sizeof *sf);
  sf->eip = switch_entry;
  sf->ebp = 0;

  intr_set_level (old_level);

  /* Add to run queue. */
  thread_unblock (t);

  /* Yields the CPU if the newly arriving thread has higher priority than
     currently running thread. */
  if (t->priority > thread_current()->priority)
    thread_yield();

  return tid;
}

/* Puts the current thread to sleep.  It will not be scheduled
   again until awoken by thread_unblock().

   This function must be called with interrupts turned off.  It
   is usually a better idea to use one of the synchronization
   primitives in synch.h. */
void
thread_block (void) 
{
  ASSERT (!intr_context ());
  ASSERT (intr_get_level () == INTR_OFF);

  thread_current ()->status = THREAD_BLOCKED;
  schedule ();
}

/* Transitions a blocked thread T to the ready-to-run state.
   This is an error if T is not blocked.  (Use thread_yield() to
   make the running thread ready.)

   This function does not preempt the running thread.  This can
   be important: if the caller had disabled interrupts itself,
   it may expect that it can atomically unblock a thread and
   update other data. */
void
thread_unblock (struct thread *t) 
{
  enum intr_level old_level;

  ASSERT (is_thread (t));

  old_level = intr_disable ();
  ASSERT (t->status == THREAD_BLOCKED);
  /* Inserts the thread into ready_list with priority order */
  list_insert_ordered (&ready_list, &t->elem, compare_priority, NULL);
  t->status = THREAD_READY;
  intr_set_level (old_level);
}

/* Returns the name of the running thread. */
const char *
thread_name (void) 
{
  return thread_current ()->name;
}

/* Returns the running thread.
   This is running_thread() plus a couple of sanity checks.
   See the big comment at the top of thread.h for details. */
struct thread *
thread_current (void) 
{
  struct thread *t = running_thread ();
  
  /* Make sure T is really a thread.
     If either of these assertions fire, then your thread may
     have overflowed its stack.  Each thread has less than 4 kB
     of stack, so a few big automatic arrays or moderate
     recursion can cause stack overflow. */
  ASSERT (is_thread (t));
  ASSERT (t->status == THREAD_RUNNING);

  return t;
}

/* Returns the running thread's tid. */
tid_t
thread_tid (void) 
{
  return thread_current ()->tid;
}

/* Deschedules the current thread and destroys it.  Never
   returns to the caller. */
void
thread_exit (void) 
{
  ASSERT (!intr_context ());

#ifdef USERPROG
  process_exit ();
#endif

  /* Remove thread from all threads list, set our status to dying,
     and schedule another process.  That process will destroy us
     when it calls thread_schedule_tail(). */
  intr_disable ();
  list_remove (&thread_current()->allelem);
  thread_current ()->status = THREAD_DYING;
  schedule ();
  NOT_REACHED ();
}

/* Yields the CPU. The current thread is not put to sleep and
   may be scheduled again immediately at the scheduler's whim. */
void
thread_yield (void) 
{
  struct thread *cur = thread_current ();
  enum intr_level old_level;
  
  ASSERT (!intr_context ());

  old_level = intr_disable ();
  if (cur != idle_thread)
    /* Insert the thread into ready_list with priority order if the thread
       is not idle thread */
    list_insert_ordered (&ready_list, &cur->elem, compare_priority, NULL);
  cur->status = THREAD_READY;
  schedule ();
  intr_set_level (old_level);
}

/* Invoke function 'func' on all threads, passing along 'aux'.
   This function must be called with interrupts off. */
void
thread_foreach (thread_action_func *func, void *aux)
{
  struct list_elem *e;

  ASSERT (intr_get_level () == INTR_OFF);

  for (e = list_begin (&all_list); e != list_end (&all_list);
       e = list_next (e))
    {
      struct thread *t = list_entry (e, struct thread, allelem);
      func (t, aux);
    }
}

/* Sets the current thread's priority to new_priority. 
   The change of current thread's priority can cause 
   change of donation status so it updates priorities by
   calling update_lock_priority() and donate_priority()*/
void
thread_set_priority (int new_priority) 
{
  if (!thread_mlfqs) {
    intr_disable();
  
    thread_current()->priority = new_priority;
    thread_current()->original_priority = new_priority;
  
    update_lock_priority();
    donate_priority();
  
    intr_enable();
    check_preempt();
  }
}

/* Returns the current thread's priority. */
int
thread_get_priority (void) 
{
  enum intr_level old_level = intr_disable();
  int p = thread_current()->priority;
  intr_set_level(old_level);
  return p;
}

/* Sets the current thread's nice value to "nice". 
   After change nice, re-calculates priority and
   check whether the current thread should yield or not*/
void
thread_set_nice (int nice) 
{
  enum intr_level old_level = intr_disable();
  struct thread* t = thread_current();
  t->nice = nice;
  calculate_priority(t);
  if (t->priority > PRI_MAX)
    t->priority = PRI_MAX;
  if (t->priority < PRI_MIN)
    t->priority = PRI_MIN;
  check_preempt();
  intr_set_level(old_level);
}

/* Returns the current thread's nice value. */
int
thread_get_nice (void) 
{
  enum intr_level old_level = intr_disable();
  struct thread *t = thread_current();
  int nice = t->nice;
  intr_set_level(old_level);
  return nice;
}

/* Returns 100 times the system load average. */
int
thread_get_load_avg (void) 
{
  enum intr_level old_level = intr_disable();
  int f = mul_f_i(load_avg, 100);
  intr_set_level(old_level);
  return f_to_i(f);
}

/* Returns 100 times the current thread's recent_cpu value. */
int
thread_get_recent_cpu (void) 
{
  enum intr_level old_level = intr_disable();
  int f = mul_f_i(thread_current()->recent_cpu, 100);
  intr_set_level(old_level);
  return f_to_i(f);
}

/* Idle thread.  Executes when no other thread is ready to run.

   The idle thread is initially put on the ready list by
   thread_start().  It will be scheduled once initially, at which
   point it initializes idle_thread, "up"s the semaphore passed
   to it to enable thread_start() to continue, and immediately
   blocks.  After that, the idle thread never appears in the
   ready list.  It is returned by next_thread_to_run() as a
   special case when the ready list is empty. */
static void
idle (void *idle_started_ UNUSED) 
{
  struct semaphore *idle_started = idle_started_;
  idle_thread = thread_current ();
  sema_up (idle_started);

  for (;;) 
    {
      /* Let someone else run. */
      intr_disable ();
      thread_block ();

      /* Re-enable interrupts and wait for the next one.

         The `sti' instruction disables interrupts until the
         completion of the next instruction, so these two
         instructions are executed atomically.  This atomicity is
         important; otherwise, an interrupt could be handled
         between re-enabling interrupts and waiting for the next
         one to occur, wasting as much as one clock tick worth of
         time.

         See [IA32-v2a] "HLT", [IA32-v2b] "STI", and [IA32-v3a]
         7.11.1 "HLT Instruction". */
      asm volatile ("sti; hlt" : : : "memory");
    }
}

/* Function used as the basis for a kernel thread. */
static void
kernel_thread (thread_func *function, void *aux) 
{
  ASSERT (function != NULL);

  intr_enable ();       /* The scheduler runs with interrupts off. */
  function (aux);       /* Execute the thread function. */
  thread_exit ();       /* If function() returns, kill the thread. */
}

/* Returns the running thread. */
struct thread *
running_thread (void) 
{
  uint32_t *esp;

  /* Copy the CPU's stack pointer into `esp', and then round that
     down to the start of a page.  Because `struct thread' is
     always at the beginning of a page and the stack pointer is
     somewhere in the middle, this locates the curent thread. */
  asm ("mov %%esp, %0" : "=g" (esp));
  return pg_round_down (esp);
}

/* Returns true if T appears to point to a valid thread. */
static bool
is_thread (struct thread *t)
{
  return t != NULL && t->magic == THREAD_MAGIC;
}

/* Does basic initialization of T as a blocked thread named
   NAME. */
static void
init_thread (struct thread *t, const char *name, int priority)
{
  ASSERT (t != NULL);
  ASSERT (PRI_MIN <= priority && priority <= PRI_MAX);
  ASSERT (name != NULL);

  memset (t, 0, sizeof *t);
  t->status = THREAD_BLOCKED;
  strlcpy (t->name, name, sizeof t->name);
  t->stack = (uint8_t *) t + PGSIZE;
  t->priority = priority;
  t->magic = THREAD_MAGIC;
  list_push_back (&all_list, &t->allelem);
  t->original_priority = priority;
  list_init (&t->donations);
  t->recent_cpu = INITIAL_CPU;
  t->nice = INITIAL_NICE;
}

/* Allocates a SIZE-byte frame at the top of thread T's stack and
   returns a pointer to the frame's base. */
static void *
alloc_frame (struct thread *t, size_t size) 
{
  /* Stack data is always allocated in word-size units. */
  ASSERT (is_thread (t));
  ASSERT (size % sizeof (uint32_t) == 0);

  t->stack -= size;
  return t->stack;
}

/* Chooses and returns the next thread to be scheduled.  Should
   return a thread from the run queue, unless the run queue is
   empty.  (If the running thread can continue running, then it
   will be in the run queue.)  If the run queue is empty, return
   idle_thread. */
static struct thread *
next_thread_to_run (void) 
{
  if (list_empty (&ready_list))
    return idle_thread;
  else
    return list_entry (list_pop_front (&ready_list), struct thread, elem);
}

/* Completes a thread switch by activating the new thread's page
   tables, and, if the previous thread is dying, destroying it.

   At this function's invocation, we just switched from thread
   PREV, the new thread is already running, and interrupts are
   still disabled.  This function is normally invoked by
   thread_schedule() as its final action before returning, but
   the first time a thread is scheduled it is called by
   switch_entry() (see switch.S).

   It's not safe to call printf() until the thread switch is
   complete.  In practice that means that printf()s should be
   added at the end of the function.

   After this function and its caller returns, the thread switch
   is complete. */
void
thread_schedule_tail (struct thread *prev)
{
  struct thread *cur = running_thread ();
  
  ASSERT (intr_get_level () == INTR_OFF);

  /* Mark us as running. */
  cur->status = THREAD_RUNNING;

  /* Start new time slice. */
  thread_ticks = 0;

#ifdef USERPROG
  /* Activate the new address space. */
  process_activate ();
#endif

  /* If the thread we switched from is dying, destroy its struct
     thread.  This must happen late so that thread_exit() doesn't
     pull out the rug under itself.  (We don't free
     initial_thread because its memory was not obtained via
     palloc().) */
  if (prev != NULL && prev->status == THREAD_DYING && prev != initial_thread)
    {
      ASSERT (prev != cur);
      palloc_free_page (prev);
    }
}

/* Schedules a new process.  At entry, interrupts must be off and
   the running process's state must have been changed from
   running to some other state.  This function finds another
   thread to run and switches to it.

   It's not safe to call printf() until thread_schedule_tail()
   has completed. */
static void
schedule (void) 
{
  struct thread *cur = running_thread ();
  struct thread *next = next_thread_to_run ();
  struct thread *prev = NULL;

  ASSERT (intr_get_level () == INTR_OFF);
  ASSERT (cur->status != THREAD_RUNNING);
  ASSERT (is_thread (next));

  if (cur != next)
    prev = switch_threads (cur, next);
  thread_schedule_tail (prev);
}

/* Returns a tid to use for a new thread. */
static tid_t
allocate_tid (void) 
{
  static tid_t next_tid = 1;
  tid_t tid;

  lock_acquire (&tid_lock);
  tid = next_tid++;
  lock_release (&tid_lock);

  return tid;
}
/* Recalculates priority of all threads in all_list. */
void calculate_all_priority(void)
{
  if (!list_empty(&all_list)) {
    struct list_elem * e;
    struct thread *t;
    for (e = list_begin (&all_list); e != list_end (&all_list);
	 e = list_next (e)){
      t = list_entry(e, struct thread, allelem);
      calculate_priority(t);
      if(t->priority < PRI_MIN)
        t->priority=PRI_MIN;
      if(t->priority > PRI_MAX)
        t->priority=PRI_MAX;
    }
  }
}

/* Calculates the priority of input thread t by the equation
   "priority = PRI_MAX - (recent_cpu / 4) - (nice*2)". */
void calculate_priority(struct thread *t) {
  if (t == idle_thread)
    return;
  int recent_cpu = t->recent_cpu;
  int nice = t->nice;
  int p = i_to_f(PRI_MAX);
  int r = div_f_i(recent_cpu, 4);
  int n = mul_f_i(i_to_f(nice), 2);
  int result = sub_f_f(p, r);
  result = sub_f_f(result, n);

  t->priority = f_to_i(result);
}

/* Calculates the recent_cpu of input thread t by the equations
   "recent_cpu = decay * recent_cpu + nice",
   "decay = (2 * load_avg) / (2 * load_avg + 1)". */
void calculate_recent_cpu(struct thread *t){
  if (t == idle_thread)
    return;
  int recent_cpu = t->recent_cpu;
  int nice = t->nice;
  int l = mul_f_i(load_avg,2);
  int decay = div_f_f(l, add_f_i(l, 1));
  int result = add_f_i(mul_f_f(decay,recent_cpu),nice);

  t->recent_cpu = result;
}

/* Calculates the load_avg by the equation
   "load_avg = (59/60) * load_avg + (1/60) * ready_threads"
   and return the load_avg value. The variable ready_threads is the number of
    threads in ready_list and threads in executing at the time of calculation.
   */
int calculate_load_avg(){
  int l = mul_f_i(load_avg,59);
  int ready_threads = list_size(&ready_list);
  if(thread_current()!=idle_thread)
    ready_threads=ready_threads+1;
  int m = add_f_i(l,ready_threads);
  int result = div_f_i(m, 60);
  if (result < 0)
    result = 0;
  return result;
}

/* Increases recent_cpu of current running thread by 1. */
void increase_recent_cpu(void)
{
  enum intr_level old_level = intr_disable();
  struct thread* t = thread_current();
  if (t == idle_thread)
    return;
  t->recent_cpu = add_f_i(t->recent_cpu, 1);
  intr_set_level(old_level);
}

/* Recalculates load_avg and update priority, recent_cpu of all threads. */
void update_priority_recent_cpu(){
  struct thread *t;
  struct list_elem *e;
  
  load_avg = calculate_load_avg();
  for (e = list_begin (&all_list); e != list_end (&all_list);
       e = list_next (e)){
    t = list_entry(e, struct thread, allelem);
    calculate_recent_cpu(t);
    calculate_priority(t);
    if(t->priority < PRI_MIN)
      t->priority=PRI_MIN;
    if(t->priority > PRI_MAX)
      t->priority=PRI_MAX;
  }
}

/* Changes global_tick to ticks. */
void update_global_tick (int64_t ticks)
{
  enum intr_level old_level = intr_disable ();
  global_tick = ticks;
  intr_set_level (old_level);
}

/* Returns current global_tick value */
int64_t get_global_tick (void)
{
  enum intr_level old_level = intr_disable ();
  int64_t t = global_tick;
  intr_set_level (old_level);
  return t;
}

/* Changes the state of the caller thread to 'blocked' and put it to the sleep
   queue. 

   It maintains increasing order of wakeup_tick of threads by inserting
   elems in order. 

   If newly inserted threads has the lowest value of wakeup_tick, update
   global tick. */
void thread_sleep (int64_t ticks) 
{
  struct thread *cur = thread_current ();
  enum intr_level old_level = intr_disable();
 
  ASSERT (cur != idle_thread);

  cur -> wakeup_tick = ticks;

  struct list_elem *e = list_begin (&sleep_list);

  if (list_empty (&sleep_list))
    list_insert (e, &(cur -> elem));
 
  else {
    while (e != list_tail(&sleep_list) &&
           list_entry (e, struct thread, elem) -> wakeup_tick < ticks)
      e = list_next (e);
    list_insert (e, &(cur -> elem));
  }
  
  if (get_global_tick() > ticks)
    update_global_tick(ticks);

  thread_block();
  intr_set_level (old_level);
}
/* Check which threads need to wake up. 

   It iterates sleep list from the start thread and scans wakeup_tick
   of threads by order. Since the threads are sorted by wakeup_tick 
   with increasing order first n threads may wake up by this function.

   After unblock threads, it needs to update global tick with the smallest
   value of wakeup_tick. If the sleep list is empty, it sets global tick
   as INT64_MAX. */
void check_sleep_list (int64_t tt)
{
  enum intr_level old_level = intr_disable ();
  int64_t gt = get_global_tick();

  if (!list_empty (&sleep_list) && gt <= tt) {

    struct list_elem *e = list_begin (&sleep_list);
    struct thread *t = list_entry (e, struct thread, elem);

    while (e != list_tail(&sleep_list) && t -> wakeup_tick <= tt) {
      e = list_remove(&t -> elem);
      thread_unblock (t); 
      t = list_entry (e, struct thread, elem);
    }

    if (!list_empty (&sleep_list))
      update_global_tick (t -> wakeup_tick);
    else
      update_global_tick (INT64_MAX);
  }
  intr_set_level (old_level);
}

/* Compares priority value of cur and next and returns true if cur's priority
   is bigger than next's. Else returns false. */
bool compare_priority(const struct list_elem *cur,
                  const struct list_elem *next,
                  void *aux UNUSED)
{
  ASSERT (cur != NULL);
  ASSERT (next != NULL);
  struct thread *cur_t = list_entry(cur, struct thread, elem);
  struct thread *next_t = list_entry(next, struct thread, elem);
  return (cur_t->priority > next_t->priority)?true:false;
}

/* Checks preemption and yields cpu if priority of current running thread is
   smaller than the maximum priority in ready_list */
void check_preempt(void)
{
  enum intr_level old_level;

  old_level = intr_disable();

  if (!list_empty(&ready_list) && thread_current()->priority < list_entry(list_begin(&ready_list), struct thread, elem)->priority) {
    intr_set_level(old_level);
    thread_yield();
  }
  intr_set_level(old_level);
}


/* Offset of `stack' member within `struct thread'.
   Used by switch.S, which can't figure it out on its own. */
uint32_t thread_stack_ofs = offsetof (struct thread, stack);
