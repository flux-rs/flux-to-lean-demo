use std::mem::MaybeUninit;

use flux_rs::{opaque, refined_by, spec, trusted};

flux_rs::defs! {

    fn map_set<K, V>(m:Map<K, V>, k: K, v: V) -> Map<K, V> { map_store(m, k, v) }

    fn map_get<K, V>(m: Map<K, V>, k:K) -> V { map_select(m, k) }

    fn map_def<K, V>(v:V) -> Map<K, V> { map_default(v) }

    fn min(a: int, b: int) -> int {
        if a < b { a } else { b }
    }

    fn is_init(len: int, num_enqueues: int, index: int) -> bool {
        0 <= index && index < min(num_enqueues, len)
    }

    fn rb_len(rb: RingBuffer) -> int {
         if rb.tl > rb.hd { rb.tl - rb.hd }
        else if rb.tl < rb.hd { rb.len - rb.hd + rb.tl }
        else { 0 }
    }

    fn rb_is_full(rb: RingBuffer) -> bool {
        rb.hd == (rb.tl + 1) % rb.len
    }

    fn rb_is_empty(rb: RingBuffer) -> bool {
        rb.hd == rb.tl
    }

    fn rb_is_valid(rb: RingBuffer, index: int) -> bool {
        ((index + rb.len - rb.hd) % rb.len) < rb_len(rb)
    }

    fn init_inv(rb: RingBuffer, init: Map<int, bool>) -> bool {
        forall idx {
            (0 <= idx && idx < rb.len) => (rb_is_valid(rb, idx) => map_get(init, idx))
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

// ===== FluxSlice ============================================================

#[flux_rs::opaque]
#[flux_rs::refined_by(len: int, init: Map<int, bool>)]
#[repr(transparent)]
pub struct FluxSlice<'a, T>(&'a mut [MaybeUninit<T>]);

impl<'a, T> FluxSlice<'a, T> {
    #[flux_rs::trusted]
    #[flux_rs::sig(fn(&mut [MaybeUninit<T>][@n]) -> FluxSlice<T>{fs: fs.len == n})]
    pub fn from_mut(slice: &'a mut [MaybeUninit<T>]) -> Self {
        // SAFETY: FluxSlice<T> is repr(transparent) over [T]
        // EVAN? unsafe { &mut *(slice as *mut [T] as *mut FluxSlice<T>) }
        FluxSlice(slice)
    }

    #[flux_rs::trusted]
    #[flux_rs::sig(fn(&FluxSlice<T>[@n, @f]) -> usize[n])]
    pub fn len(&self) -> usize {
        self.0.len()
    }

    #[flux_rs::trusted]
    #[flux_rs::sig(fn(&FluxSlice<T>[@n, @f], index: usize{index < n && map_get(f, index)}) -> T)]
    pub fn get(&self, index: usize) -> T
    where
        T: Copy,
    {
        unsafe { self.0[index].assume_init() }
    }

    #[flux_rs::trusted]
    #[flux_rs::sig(
        fn(self: &mut FluxSlice<T>[@n, @f], index: usize{index < n}, val: T)
        ensures self: FluxSlice<T>[n, map_set(f, index, true)]
    )]
    pub fn set(&mut self, index: usize, val: T) {
        self.0[index] = MaybeUninit::new(val);
    }
}

// ===== RingBuffer ==========================================================

#[flux_rs::refined_by(len: int, hd: int, tl: int, init: Map<int, bool>)]
#[flux_rs::invariant(0 < len && 0 <= hd && hd < len && 0 <= tl && tl < len)]
#[flux_rs::invariant(init_inv(RingBuffer{ len: len, hd: hd, tl: tl, init: init}, init))]
pub struct RingBuffer<'a, T: Copy + 'a> {
    #[flux_rs::field(FluxSlice<T>[len, init])]
    ring: FluxSlice<'a, T>,
    #[flux_rs::field(usize[hd])]
    head: usize,
    #[flux_rs::field(usize[tl])]
    tail: usize,
}

impl<'a, T: Copy> RingBuffer<'a, T> {
    #[flux_rs::proven_externally(proof)]
    #[flux_rs::sig(fn({FluxSlice<T>[@len, @f] | 0 < len}) -> RingBuffer<T>[len, 0, 0, f])]
    pub fn new(ring: FluxSlice<'a, T>) -> RingBuffer<'a, T> {
        RingBuffer {
            head: 0,
            tail: 0,
            ring,
        }
    }

    #[flux_rs::proven_externally]
    #[flux_rs::sig(fn(self: &RingBuffer<T>[@s]) -> bool[rb_is_full(s)])]
    pub fn is_full(&self) -> bool {
        self.head == ((self.tail + 1) % self.ring.len())
    }

    #[flux_rs::proven_externally]
    #[flux_rs::sig(fn(self: &RingBuffer<T>[@s]) -> bool[!rb_is_empty(s)])]
    pub fn has_elements(&self) -> bool {
        self.head != self.tail
    }

    #[flux_rs::proven_externally]
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

    #[flux_rs::proven_externally]
    #[flux_rs::sig(fn(self: &RingBuffer<T>[@s], index: usize) -> bool[rb_is_valid(s, index)])]
    fn is_valid(&self, index: usize) -> bool {
        let capacity = self.ring.len();
        let position_in_ring = (index + capacity - self.head) % capacity;
        position_in_ring < self.len()
    }

    #[flux_rs::proven_externally(proof)]
    #[flux_rs::sig(fn(self: &strg RingBuffer<T>[@s], val: T) -> bool[#b] ensures self: RingBuffer<T>)]
    pub fn enqueue(&mut self, val: T) -> bool {
        if self.is_full() {
            false
        } else {
            self.ring.set(self.tail, val);
            self.tail = (self.tail + 1) % self.ring.len();
            true
        }
    }

    #[flux_rs::proven_externally]
    #[flux_rs::sig(fn(self: &strg RingBuffer<T>[@s]) -> Option<T> ensures self: RingBuffer<T>)]
    pub fn dequeue(&mut self) -> Option<T> {
        if self.head != self.tail {
            let val = self.ring.get(self.head);
            self.head = (self.head + 1) % self.ring.len();
            Some(val)
        } else {
            None
        }
    }
}
