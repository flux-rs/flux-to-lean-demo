use flux_rs::{opaque, refined_by, spec, trusted};

flux_rs::defs! {

    opaque sort FSlice<T>;
    fn fslice_len<T>(s: FSlice<T>) -> int;
    fn fslice_set<T>(s: FSlice<T>, pos: int, val: T) -> FSlice<T>;
    fn fslice_get<T>(s: FSlice<T>, pos: int) -> T;
    fn fslice_push<T>(s: FSlice<T>, val: T) -> FSlice<T>;
    fn fslice_pop_front<T>(s: FSlice<T>) -> FSlice<T>;
    fn fslice_append<T>(s1: FSlice<T>, s2: FSlice<T>) -> FSlice<T>;
    fn fslice_subslice<T>(s: FSlice<T>, l: int, r: int) -> FSlice<T>;

    fn init_inv(num_enqueues: int, len: int, init: Map<int, bool>) -> bool {
        forall idx {
            (0 <= idx && idx < min(num_enqueues, len)) => map_get(init, idx)
        }
    }
        // forall|idx: int| (0 <= idx && idx < min(num_enqueues, len)) ==> map_get(init, idx)
        // ∀ idx, (0 <= idx ∧ idx < my_min num_enqueues len) → SmtMap_select init idx

    fn map_set<K, V>(m:Map<K, V>, k: K, v: V) -> Map<K, V> { map_store(m, k, v) }

    fn map_get<K, V>(m: Map<K, V>, k:K) -> V { map_select(m, k) }

    fn map_def<K, V>(v:V) -> Map<K, V> { map_default(v) }

    fn min(a: int, b: int) -> int {
        if a < b { a } else { b }
    }

    fn is_init(len: int, num_enqueues: int, index: int) -> bool {
        0 <= index && index < min(num_enqueues, len)
    }

    fn rb_len<T>(rb: RingBuffer<T>) -> int {
         if rb.tl > rb.hd { rb.tl - rb.hd }
        else if rb.tl < rb.hd { rb.len - rb.hd + rb.tl }
        else { 0 }
    }

    fn rb_next_index(x:int, rlen: int) -> int { (x + 1) % rlen }
    fn rb_next_hd<T>(rb: RingBuffer<T>) -> int { rb_next_index(rb.hd, fslice_len(rb.elems)) }
    fn rb_next_tl<T>(rb: RingBuffer<T>) -> int { rb_next_index(rb.tl, fslice_len(rb.elems)) }

    fn rb_is_full<T>(rb: RingBuffer<T>) -> bool {
        rb.hd == rb_next_tl(rb)
    }

    fn rb_is_empty<T>(rb: RingBuffer<T>) -> bool {
        rb.hd == rb.tl
    }

    fn rb_is_valid<T>(rb: RingBuffer<T>, index: int) -> bool {
        ((index + rb.len - rb.hd) % rb.len) < rb_len(rb)
    }

    fn rb_push<T>(old: RingBuffer<T>, val: T) -> RingBuffer<T> {
        RingBuffer {
            len          : old.len,
            hd           : if rb_is_full(old) { rb_next_hd(old) } else { old.hd },
            tl           : rb_next_tl(old),
            num_enqueues : old.num_enqueues + 1,
            elems        : fslice_set(old.elems, old.tl, val),
            init         : map_set(old.init, old.tl, true)
        }
    }

    fn rb_enqueue<T>(old: RingBuffer<T>, val: T) -> RingBuffer<T> {
        if !rb_is_full(old) {
            rb_push(old, val)
        } else {
            old
        }
    }

    fn rb_dequeue<T>(old: RingBuffer<T>) -> RingBuffer<T> {
        if !rb_is_empty(old) {
            RingBuffer { ..old, hd: rb_next_hd(old) }
        } else {
            old
        }
    }

    fn rb_matches_lqueue<T>(rb: RingBuffer<T>, vq: FSlice<T>) -> bool {
        vq == if rb.hd > rb.tl {
            fslice_append(
                fslice_subslice(rb.elems, rb.hd, fslice_len(rb.elems)), 
                fslice_subslice(rb.elems, 0, rb.tl)
            )
        } else {
            fslice_subslice(rb.elems, rb.hd, rb.tl)
        }
    }
}

// ======== Extern specs ========

mod flux_specs {
    #[flux_rs::extern_spec]
    #[flux_rs::refined_by(b: bool)]
    enum Option<T> {
        #[variant(Option<T>[false])]
        None,
        #[variant({T} -> Option<T>[true])]
        Some(T),
    }
}

// Ghost "counter" type; will be used to count the number of enqueues in the ring buffer.
#[opaque]
#[refined_by(n: int)]
pub struct Ghost;

impl Ghost {
    #[trusted]
    #[spec(fn () -> Self[0])]
    pub fn new() -> Self {
        Self
    }
    #[trusted]
    #[spec(fn (me: &mut Self[@n]) ensures me: Self[n+1])]
    pub fn bump(&mut self) {}
}
// ===== FluxSlice ============================================================

#[flux_rs::opaque]
#[flux_rs::refined_by(len: int, init: Map<int, bool>, elems: FSlice<T>)]
#[flux_rs::invariant(len == fslice_len(elems))]
#[repr(transparent)]
pub struct FluxSlice<'a, T>(&'a mut [T]);

impl<'a, T> FluxSlice<'a, T> {
    #[flux_rs::trusted]
    #[flux_rs::sig(fn(&mut [T][@n]) -> FluxSlice<T>{fs: fs.len == n})]
    pub fn from_mut(slice: &'a mut [T]) -> Self {
        // SAFETY: FluxSlice<T> is repr(transparent) over [T]
        // EVAN? unsafe { &mut *(slice as *mut [T] as *mut FluxSlice<T>) }
        FluxSlice(slice)
    }

    #[flux_rs::trusted]
    #[flux_rs::sig(fn(&FluxSlice<T>[@n, @f, @e]) -> usize[n])]
    pub fn len(&self) -> usize {
        self.0.len()
    }

    #[flux_rs::trusted]
    #[flux_rs::sig(fn(&FluxSlice<T>[@n, @f, @e], index: usize{index < n && map_get(f, index)}) -> T[fslice_get(e, index)])]
    pub fn get(&self, index: usize) -> T
    where
        T: Copy,
    {
        self.0[index]
    }

    #[flux_rs::trusted]
    #[flux_rs::sig(
        fn(self: &mut FluxSlice<T>[@n, @f, @e], index: usize{index < n}, T[@val])
        ensures self: FluxSlice<T>[n, map_set(f, index, true), fslice_set(e, index, val)]
    )]
    pub fn set(&mut self, index: usize, val: T) {
        self.0[index] = val;
    }
}

// ===== RingBuffer ==========================================================

#[flux_rs::refined_by(len: int, hd: int, tl: int, num_enqueues: int, init: Map<int, bool>, elems: FSlice<T>)]
#[flux_rs::invariant(1 < len && 0 <= hd && hd < len && 0 <= tl && tl < len && 0 <= num_enqueues && len == fslice_len(elems))]
#[flux_rs::invariant(num_enqueues < len => (tl == num_enqueues && hd <= tl))]
#[flux_rs::invariant(init_inv(num_enqueues, len, init))]
pub struct RingBuffer<'a, T: Copy + 'a> {
    #[flux_rs::field(FluxSlice<T>[len, init, elems])]
    ring: FluxSlice<'a, T>,
    #[flux_rs::field(usize[hd])]
    head: usize,
    #[flux_rs::field(usize[tl])]
    tail: usize,
    #[flux_rs::field(Ghost[num_enqueues])]
    ghost: Ghost,
}

impl<'a, T: Copy> RingBuffer<'a, T> {
    #[flux_rs::proven_externally(proof)]
    #[flux_rs::sig(fn({FluxSlice<T>[@len, @f, @e] | 1 < len}) -> RingBuffer<T>[len, 0, 0, 0, f, e])]
    pub fn new(ring: FluxSlice<'a, T>) -> RingBuffer<'a, T> {
        RingBuffer {
            head: 0,
            tail: 0,
            ring,
            ghost: Ghost::new(),
        }
    }

    #[flux_rs::proven_externally(proof)]
    #[flux_rs::sig(fn(self: &RingBuffer<T>[@s]) -> bool[rb_is_full(s)])]
    pub fn is_full(&self) -> bool {
        self.head == ((self.tail + 1) % self.ring.len())
    }

    #[flux_rs::proven_externally(proof)]
    #[flux_rs::sig(fn(self: &RingBuffer<T>[@s]) -> bool[!rb_is_empty(s)])]
    pub fn has_elements(&self) -> bool {
        self.head != self.tail
    }

    #[flux_rs::proven_externally(proof)]
    #[flux_rs::sig(fn(self: &RingBuffer<T>[@s]) -> usize[rb_len(s)])]
    fn len(&self) -> usize {
        if self.tail > self.head {
            self.tail - self.head
        } else if self.tail < self.head {
            (self.ring.len() - self.head) + self.tail
        } else {
            0
        }
    }

    #[flux_rs::proven_externally(proof)]
    #[flux_rs::sig(fn(self: &RingBuffer<T>[@s], index: usize) -> bool[rb_is_valid(s, index)])]
    fn is_valid(&self, index: usize) -> bool {
        let capacity = self.ring.len();
        let position_in_ring = (index + capacity - self.head) % capacity;
        position_in_ring < self.len()
    }

    #[flux_rs::proven_externally(proof)]
    #[flux_rs::sig(fn(self: &RingBuffer<T>[@s], index: usize{index < s.len}) -> Option<T[fslice_get(s.elems, index)]>[rb_is_valid(s, index)])]
    fn get_internal(&self, index: usize) -> Option<T> {
        if !self.is_valid(index) {
            None
        } else {
            Some(self.ring.get(index))
        }
    }

    #[flux_rs::proven_externally(proof)]
    #[flux_rs::sig(fn(self: &strg RingBuffer<T>[@s], T[@val]) -> bool[#b] 
        ensures self: RingBuffer<T>[#nrb],
                b == !rb_is_full(s),
                nrb == rb_enqueue(s, val)
    )]
    pub fn enqueue(&mut self, val: T) -> bool {
        if self.is_full() {
            false
        } else {
            self.ring.set(self.tail, val);
            self.tail = (self.tail + 1) % self.ring.len();
            self.ghost.bump();
            true
        }
    }

    #[flux_rs::proven_externally]
    #[flux_rs::sig(
        fn(self: &strg RingBuffer<T>[@old]) -> Option<T[fslice_get(old.elems, old.hd)]>[!rb_is_empty(old)]
            ensures self: Self[rb_dequeue(old)]
    )]
    pub fn dequeue(&mut self) -> Option<T> {
        if self.has_elements() {
            let val = self.get_internal(self.head);
            self.head = (self.head + 1) % self.ring.len();
            val
        } else {
            None
        }
    }

    /// Returns the number of elements that can be enqueued until the ring buffer is full.
    #[flux_rs::trusted]
    #[flux_rs::sig(fn(self: &RingBuffer<T>[@s]) -> usize[s.len - 1 - rb_len(s)])]
    pub fn available_len(&self) -> usize {
        self.ring.len().saturating_sub(1 + self.len())
    }

    /// Adds a new element to the back of the ring buffer, overwriting the oldest
    /// (head) element if the buffer is full. Returns the overwritten element, if any.
    #[flux_rs::proven_externally(proof)]
    #[flux_rs::sig(
        fn(self: &strg RingBuffer<T>[@s], T[@val]) -> Option<T>[rb_is_full(s)]
        ensures self: RingBuffer<T>[rb_push(s, val)]
    )]
    pub fn push(&mut self, val: T) -> Option<T> {
        let result = if self.is_full() {
            let old = self.ring.get(self.head);
            self.head = (self.head + 1) % self.ring.len();
            Some(old)
        } else {
            None
        };
        self.ring.set(self.tail, val);
        self.tail = (self.tail + 1) % self.ring.len();
        self.ghost.bump();
        result
    }
}

mod vec_queue {

    use crate::ringbuffer::RingBuffer;

    #[flux_rs::opaque]
    #[flux_rs::refined_by(elems: FSlice<T>)]
    struct LQueue<T> {
        inner: T
    }

    #[flux_rs::trusted]
    impl<T> LQueue<T> {

        #[flux_rs::spec(fn(self: &mut Self[@slf], T[@elem])
            ensures self: Self[fslice_push(slf, elem)]
        )]
        fn push_back(&mut self, elem: T) {}

        #[flux_rs::spec(fn(self: &mut Self[@slf])
            ensures self: Self[fslice_pop_front(slf)]
        )]
        fn pop_front(&mut self) {}
    }

    #[flux_rs::proven_externally]
    #[flux_rs::spec(fn(r: &mut RingBuffer<T>[@rb], v: &mut LQueue<T>[@vq], T[@e], T[e]) -> bool[#res]
        requires rb_matches_lqueue(rb, vq),
        ensures  r: RingBuffer<T>[#nrb],
                 v: LQueue<T>[#nvq],
                 res => rb_matches_lqueue(nrb, nvq)
    )]
    fn push_correct<T: Copy>(r: &mut RingBuffer<'_, T>, v: &mut LQueue<T>, e1: T, e2: T) -> bool {
        v.push_back(e1);
        r.enqueue(e2)
    }

    #[flux_rs::proven_externally]
    #[flux_rs::spec(fn(r: &mut RingBuffer<T>[@rb], v: &mut LQueue<T>[@vq])
        requires rb_matches_lqueue(rb, vq),
                 !rb_is_empty(rb), fslice_len(vq) > 0
        ensures r: RingBuffer<T>[#nrb],
                v: LQueue<T>[#nvq],
                rb_matches_lqueue(nrb, nvq)
    )]
    fn pop_correct<T: Copy>(r: &mut RingBuffer<'_, T>, v: &mut LQueue<T>) {
        v.pop_front();
        r.dequeue();
    }
}
