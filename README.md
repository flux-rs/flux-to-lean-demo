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

1. `cargo flux`  generates a bunch of errors
2. `cp -r UserProofs/* lean_proofs/LeanProofs/User/`
3. `cargo flux` should generate no errors!



