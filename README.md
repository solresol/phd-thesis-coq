# Coq formalisation of fixed-prime regression hardness

This repository is the Coq formalisation companion for the NP-hardness part
of Greg Baker's PhD thesis on p-adic and ultrametric regression. Its specific
goal is a kernel-checked proof that the thesis's signed affine regression
decision problem at the fixed prime `p = 5` is NP-hard.

This is a supplementary research artifact. The thesis remains the
authoritative source for the mathematical claims and exposition.

## Target theorem

The final development should prove, in the complexity framework of the Coq
Library of Complexity Theory, that:

> the language of finite signed affine regression instances at `p = 5` whose
> objective attains a supplied threshold is NP-hard under polynomial-time
> many-one reductions.

The planned reduction starts with exact 3-SAT. For a formula with `n`
variables and `m` clauses, it constructs:

- two positive Boolean-pinning observations per variable;
- one negative reward observation per clause;
- pinning weight `1 + Δ`, where `Δ` is the maximum variable occurrence
  count; and
- threshold `(1 + Δ)n - m`.

The essential correctness statement is:

```text
F is satisfiable  <->  compile(F) attains its threshold.
```

The final NP-hardness declaration must compose this equivalence and a checked
polynomial-time implementation of `compile` with the upstream theorem
`CookLevin0 : NPcomplete (kSAT 3)`.

## Current status

The repository begins with a build-level connection to the upstream 3-SAT
theorem. The project-specific target language, compiler, p-adic correctness
proof, polynomial-time implementation, and final hardness composition remain
to be formalised. See [THEOREM_STATUS.md](THEOREM_STATUS.md) for the exact
ledger and [docs/ARCHITECTURE.md](docs/ARCHITECTURE.md) for the intended proof
layers.

No result is counted as complete merely because its Lean analogue exists.
Coq and Lean check separate proof terms.

## Related repositories

### [`solresol/phd-thesis`](https://github.com/solresol/phd-thesis)

The thesis repository owns the prose, notation, and theorem statements. Once
the Coq result is substantive and stable, the thesis should cite this
repository alongside the Lean formalisation companion.

### [`solresol/phd-thesis-lean`](https://github.com/solresol/phd-thesis-lean)

The Lean repository contains the broader formalisation. Its
[`FixedPrimeHardness.lean`](https://github.com/solresol/phd-thesis-lean/blob/main/PhdThesisLean/FixedPrimeHardness.lean)
already proves the concrete `p = 5` reduction's semantic equivalence, exact
observation count, quadratic dense output-size bound, and quadratic
unit-cell construction bound.

That Lean development does not currently have a library-native P/NP and
Cook--Levin foundation. This Coq repository addresses that missing
complexity-theoretic layer while independently rechecking the mathematical
reduction needed to compose the final theorem.

### [`uds-psl/coq-library-complexity`](https://github.com/uds-psl/coq-library-complexity)

The upstream library supplies polynomial-time many-one reductions, NP, and a
formal Cook--Levin development. In particular it proves exact 3-SAT
NP-complete. This project pins upstream commit
`14b5f413d2fb7adecde79c5451b483f9a1af59a8`, from its `coq-8.16` branch.

The upstream project is distributed under CeCILL 2.1. Its dependency is used
as an external Coq library; its source is not copied into this repository.

## Toolchain

The pinned complexity library supports Coq 8.16 and version
`1.0.1+8.16` of the Coq Library of Undecidability Proofs. Use an isolated
opam switch:

```sh
opam switch create . --empty
eval "$(opam env)"
opam repo add coq-released https://coq.inria.fr/opam/released
opam pin add coq-library-complexity \
  'git+https://github.com/uds-psl/coq-library-complexity.git#14b5f413d2fb7adecde79c5451b483f9a1af59a8' \
  --no-action
opam install ocaml-base-compiler.4.14.2
opam install . --deps-only
make
```

The initial build checks that the pinned upstream theorem can be imported
under the name and type on which this project depends.

## Proof policy

A completed headline theorem must:

- quantify over a concrete `5`-adic domain, not an uninstantiated valued-field
  interface;
- preserve satisfiability in both directions;
- use an explicit finite encoding of source and target instances;
- establish polynomial-time construction in the upstream computational model;
- compose with the checked exact-3-SAT hardness theorem; and
- contain no `Admitted`, project-defined axioms, or hidden external hardness
  premise.

Run `Print Assumptions` on each headline theorem. Record partial results
plainly in the status ledger.

## Repository layout

```text
theories/             Coq source
docs/ARCHITECTURE.md  proof decomposition and design decisions
docs/RELATED_REPOS.md ownership and correspondence across repositories
THEOREM_STATUS.md     statement-by-statement completion ledger
AGENTS.md             working and proof-quality instructions
```
