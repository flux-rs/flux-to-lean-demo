use flux_rs::{attrs::*};

#[spec(fn(n: usize) -> usize[n + 1])]
pub fn incr(n: usize) -> usize {
   n + 1
}

defs! {
    fn spec_seven() -> int;
    fn spec_sum(n: int) -> int;
    fn spec_ninety() -> int;
    fn spec_ten() -> int { 10 }
}

#[proven_externally(proof)]
#[spec(fn() -> usize[spec_seven()])]
pub fn seven() -> usize {
    3 + 2 + 2
}

#[proven_externally(proof)]
#[spec(fn() -> usize[spec_ninety()])]
pub fn ninety() -> usize {
    42 + 48
}

#[proven_externally(proof)]
#[spec(fn() -> usize[spec_ten()])]
pub fn ten() -> usize {
    5 + 5
}


#[proven_externally(proof)]
#[spec(fn(n: usize) -> usize[spec_sum(n)])]
pub fn sum_loop(n: usize) -> usize {
    let mut total = 0;
    let mut i = 0;
    while i < n {
        // i, total = 0, 0
        // i, total = 1, 1
        // i, total = 2, 3
        // i, total = 3, 6
        i += 1;
        total += i;
    }
    // i = n + 1
    // total = sum(n+1)
    total
}

/*
defs! {
    fn fib(n: int) -> int;
    fn sum(n: int) -> int;
}



#[proven_externally]
#[spec(fn(usize[@n]) -> usize[fib(n)])]
fn fib_slow(n: usize) -> usize {
    if n <= 1 {
        1
    } else {
        fib_slow(n - 1) + fib_slow(n - 2)
    }
}

#[proven_externally]
#[spec(fn(usize[@n]) -> usize[fib(n)])]
fn fib_fast(n: usize) -> usize {
    if n <= 1 {
        return 1;
    }
    let mut prev = 1;
    let mut curr = 2;
    let mut i = 2;
    while i < n {
        let next = prev + curr;
        prev = curr;
        curr = next;
        i += 1;
    }
    return curr;
}
*/
