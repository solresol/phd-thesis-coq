# Repository working instructions

## Purpose

This repository has one primary goal: give a self-contained Coq proof that
the fixed-prime signed affine regression decision problem used in Greg
Baker's PhD thesis is NP-hard.

The intended final result composes:

1. the existing Coq proof that exact 3-SAT is NP-complete;
2. a concrete compiler from exact 3-CNF instances to signed affine
   regression instances at `p = 5`;
3. a proof that the compiler preserves yes-instances and no-instances; and
4. a proof that the compiler runs in polynomial time in the same complexity
   model used by the upstream Coq library.

Do not describe the target theorem as complete until all four layers are
machine-checked and composed.

## Related repositories

- `../phd-thesis` is the authoritative thesis source. It owns the prose and
  published theorem statements.
- `../phd-thesis-lean` is the broader Lean 4 formalisation companion. In
  particular, `PhdThesisLean/FixedPrimeHardness.lean` is the mathematical
  reference for the concrete `p = 5` reduction.
- `https://github.com/uds-psl/coq-library-complexity` supplies the formal
  definitions of NP, polynomial-time many-one reduction, and the theorem
  `CookLevin0 : NPcomplete (kSAT 3)`.

Do not edit sibling repositories unless the current task explicitly includes
them. Cross-reference their current state rather than copying large bodies of
source.

## Proof standards

- The final theorem must not depend on `Admitted`, `admit`, project-defined
  axioms, or an uninstantiated abstract model of the `5`-adic numbers.
- Keep semantic correctness, encoding-size bounds, executable construction,
  and polynomial-time analysis as separately named results.
- Run `Print Assumptions` on headline theorems and record the result when a
  milestone is marked complete.
- Preserve repeated clauses and observations unless a proved normalization
  theorem justifies removing them.
- Reconcile the upstream `kSAT 3` syntax, which permits repeated literals,
  with the distinct-variable clause convention used by the current Lean
  development. Do not silently treat the two languages as identical.
- Pin the upstream complexity development. Upgrade it only in a dedicated,
  verified change.
- Keep `THEOREM_STATUS.md` accurate. A theorem skeleton, conditional theorem,
  or size-only result is not a completed NP-hardness proof.

## Working practice

- Build the complete project before committing a proof increment.
- Commit and push completed, verified increments regularly instead of
  allowing large batches of finished work to remain uncommitted.
- Keep the default branch usable. If a dependency or mathematical obstacle
  blocks the main route, document the exact boundary and preserve the last
  passing build.
