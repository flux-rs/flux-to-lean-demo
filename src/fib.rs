use flux_rs::{attrs::*};

#[spec(fn(n: usize) -> usize[n + 1])]
pub fn incr(n: usize) -> usize {
   n + 1
}

defs! {
    fn seven() -> int;
}

#[proven_externally]
#[spec(fn() -> usize[seven()])]
pub fn seven() -> usize {
    3 + 2 + 2
}

/*
defs! {
    fn fib(n: int) -> int;
    fn sum(n: int) -> int;
}

#[proven_externally]
#[spec(fn(n: usize) -> usize[sum(n)])]
fn sum_loop(n: usize) -> usize {
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
