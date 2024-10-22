
This is a lab for me to experiment with type systems.

## HM Driven System F

Divided into two parts, the driver and engine:
- The engine is System F, and includes the important primitives needed to
  build a type checker
- The driver is a HM reconstruction algorithm

### Run

Run with `ocaml system-f.ml`. There is no parser so programs have to
be hard-coded.

### Todo

- Add polymorphic-compatible unification or subtyping, not sure which
- Add abstraction optimization
- Add effect logs

## HM

A Hindley-Damas-Milner style type system.

Based on a mixture of ideas, largely from *Types and Programming
Langues* and Wikipedia.

### Run

This requires a sufficiently-recent version of Ocaml. Not sure
which.

Run with `ocaml hm.ml`. There is no parser so programs have to
be hard-coded.

### Todo

- Add occurs check
- Add abstraction optimization described in *[Efficient and Insightful Generalization](https://okmij.org/ftp/ML/generalization.html)*
- Clean up logging
	- The `let= _ = log_context ...` pattern is bad
	- Add helpers to log various types
	- Allow format strings in logs
	- Rename string conversion functions from `print_*` to
		`fmt_*`

