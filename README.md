# README

Small repo that illustrates how you can use lean with flux.

## Setup

1. `git clone https://github.com/flux-rs/flux-to-lean-demo.git`
2. `cd flux-to-lean-demo`
3. `code --add vscode lean_proofs`

The last line adds the `lean_proofs` folder to the vscode workspace.

## Use

1. Open in vscode `code .`
2. Toggle flux mode on and off using the command palette `Ctrl+Shift+P` and then `Flux: Toggle Flux Mode`
3. Squash the red squiggles!

## Command Line

Run `runlean.sh`

1. `cargo flux` generates a bunch of errors
2. `cp -r UserProofs/* lean_proofs/LeanProofs/User/`
3. `cargo flux` should generate no errors!

```rust
fn contains(seq: AVec<i32>, target: int) -> bool; // implement in lean

fn find(arr: &AVec<i32>[@me], target: i32) -> Option<usize>[contains(me, target)] // verify in lean

fn find_by(arr: &AVec<i32>[@me], f: Closure<i32, bool>[@clos]) -> Option<usize>[contains_clos(me, clos)]

fn find_by(arr: &AVec<i32>[@me], f: fn(i32) -> bool) -> Option<usize>

fn find_by<F>(arr: &AVec<i32>[@me], f: F) -> Option<usize>[contains_clos(me, F::rel)]
    where F: fn(i32) -> bool
{
        for i in 0..arr.len() {
            if f.call(arr[i]) {
                return Some(i);
            }
        }
        None
}

fn client(...) {
    ...
}

#[assoc(fn rel(input: I, output: O) -> bool)]
trait Fn<I, O> {
    fn call(&self, x: I) -> O;
}


def contains_clos(seq: AVec<i32>, clos: (i32, bool) -> bool) -> bool {
    exists i in 0..seq.len() {
        clos(seq[i], true)
    }
}



struct Closure<I, O>[clos: (I, O) -> bool]
{
    f: fn(x:I) -> O{v: clos(x, v)},
}

```
