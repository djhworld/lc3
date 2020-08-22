# LC3

An implementation of the Little Computer 3 (https://justinmeiners.github.io/lc3-vm/supplies/lc3-isa.pdf) in Rust.

Developed purely out of boredom but I enjoy writing VMs. A good tutorial on how to write the LC3 can be found here https://justinmeiners.github.io/lc3-vm/index.html

Currently does not support the `RES` and `RTI` instructions


## Usage

```
cargo run <program>
```

e.g.

```
cargo run ./2048.obj
```

Example programs can be found here

* https://justinmeiners.github.io/lc3-vm/supplies/2048.obj
* https://justinmeiners.github.io/lc3-vm/supplies/rogue.obj
