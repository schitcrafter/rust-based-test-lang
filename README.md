# Some language (written in Rust obv.)

This is the beginning of a heavily rust-inspired language. I'm not sure I'll finish this, really just wanted to see if I could make a language, and try out a different parser crate (I use `pest` here).

The code quality isn't good (mainly error handling is missing), that's because I wanted to first of all figure out how to use `pest`, I might add errors later if the language gets somewhat close to done, or if I feel like it.

## TODOs

### features

 - [x] boolean operators
 - [x] comparisons
 - [ ] chained comparators
 - [x] assignment without let
 - [x] control structures (if, while, for)
 - [ ] match
 - [x] functions
 - [x] nested modules
 - [ ] static/const elements
 - [ ] traits
 - [ ] impl blocks
 - [x] constructors
 - [x] field access (`my_struct.something`)

### internal

 - [x] Parser struct with context
 - [x] put all ast into a single file
 - [x] node id's

### Name resolution

rustc builds map of NodeId -> Res
NodeId here is the NodeId of a specific path (i.e. a reference to another thing, like an ident)