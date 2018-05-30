# broadword-rs: broadword algorithms

[![Build Status](https://travis-ci.org/tov/broadword-rs.svg?branch=master)](https://travis-ci.org/tov/broadword-rs)
[![Crates.io](https://img.shields.io/crates/v/broadword.svg?maxAge=2592000)](https://crates.io/crates/broadword)
[![License: MIT](https://img.shields.io/badge/license-MIT-blue.svg)](LICENSE-MIT)
[![License: Apache 2.0](https://img.shields.io/badge/license-Apache_2.0-blue.svg)](LICENSE-APACHE)

This crate includes broadword algorithms that treat a `u64` as a parallel vector
of eight `u8`s or `i8`s, as well as population count and select algorithms.

## Usage

It’s [on crates.io](https://crates.io/crates/broadword), so you can add

```toml
[dependencies]
broadword = "0.2.2"
```

to your `Cargo.toml` and

```rust
extern crate broadword;
```

to your crate root.
