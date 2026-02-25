use flux_rs::attrs::*;

#[spec(fn(n: usize) -> usize[n + 2])]
pub fn incr(n: usize) -> usize {
    n + 2
}

defs! {
    fn is_sqrt(res: int, x: int) -> bool {
        (res * res <= x) && (x < (res + 1) * (res + 1))
    }
    fn spec_seven() -> int;
    fn spec_twelve() -> int;
    fn spec_ninety() -> int { 90 }
    fn spec_sum(n: int) -> int;
    fn spec_fib(n: int) -> int;
    fn bozo_val(b: Bozo) -> int {
        if b.y  { b.x + 10 } else { b.x + 20 }
    }
}

#[proven_externally(proof)]
#[spec(fn() -> usize[spec_seven()])]
pub fn seven() -> usize {
    let grmp = 3 + 2 + 2;
    grmp
}

#[proven_externally(proof)]
#[spec(fn() -> usize[spec_ninety()])]
pub fn ninety() -> usize {
    42 + 48
}

#[proven_externally(proof)]
#[spec(fn() -> usize[spec_twelve()])]
pub fn twelve() -> usize {
    3 + 9
}

#[refined_by(x: int, y: bool)]
pub struct Bozo {
    #[field(usize[x])]
    x: usize,
    #[field(bool[y])]
    y: bool,
}

#[proven_externally(proof)]
#[spec(fn(&Bozo[@b]) -> usize[bozo_val(b)])]
pub fn test_bozo(b: &Bozo) -> usize {
    if b.y { b.x + 10 } else { b.x + 20 }
}

#[proven_externally(proof)]
#[spec(fn(n: usize) -> usize[spec_sum(n)])]
pub fn sum_loop(n: usize) -> usize {
    let mut total = 0;
    let mut i = 0;
    while i < n {
        i += 1;
        total += i;
    }
    total
}

#[proven_externally]
#[spec(fn(usize[@n]) -> usize[spec_fib(n)])]
pub fn fib_slow(n: usize) -> usize {
    if n <= 1 {
        1
    } else {
        fib_slow(n - 1) + fib_slow(n - 2)
    }
}

#[proven_externally]
#[spec(fn(usize[@n]) -> usize[spec_fib(n)])]
pub fn fib_fast(n: usize) -> usize {
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

#[proven_externally(proof)]
#[spec(fn (x: usize) -> usize{res: is_sqrt(res, x)})]
pub fn sqrt(x: usize) -> usize {
    if x == 0 {
        0
    } else {
        let mut i = 0;
        while i * i <= x {
            i += 1;
        }
        i - 1
    }
}

#[cfg(test)]
mod test {

    #[test]
    fn test_sqrt() {
        for x in 0..100 {
            let res = super::sqrt(x);
            assert!((res * res <= x) && (x < (res + 1) * (res + 1)))
        }
    }

    #[test]
    fn test_fast_eq_slow() {
        for i in 0..20 {
            assert_eq!(super::fib_fast(i), super::fib_slow(i));
        }
    }
}
