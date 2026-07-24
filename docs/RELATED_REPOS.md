# Related repository map

## `phd-thesis`

- Location: `../phd-thesis`
- Remote: <https://github.com/solresol/phd-thesis>

This is the authority for thesis prose, notation, labels, and the claim being
made. It should link to formal proof artifacts, but it should not vendor their
toolchains into the thesis build.

For this project, the relevant thesis material is the finite-domain compiler
and signed NP-hardness discussion. Any change in the formal theorem's scope
must be checked against the current thesis statement.

## `phd-thesis-lean`

- Location: `../phd-thesis-lean`
- Remote: <https://github.com/solresol/phd-thesis-lean>

This is the broad formalisation companion. The relevant chain is:

- `FiniteDomainCompiler.lean`: snapping and finite-domain minimization over
  all of `ℚ_p`;
- `ClauseCompiler.lean`: the clause indicator and maximum-satisfaction
  objective;
- `FixedPrimeHardness.lean`: the concrete `p = 5` compiler, semantic
  correctness, observation count, and unit-cell polynomial bounds.

Its remaining limitation for `cor:signed-nphard` is foundational: its pinned
mathlib revision does not supply a complete P/NP/Cook--Levin framework with
the required polynomial-time composition theorem. This Coq project is meant
to give an independent end-to-end proof using an existing formal complexity
library.

## `coq-library-complexity`

Remote: <https://github.com/uds-psl/coq-library-complexity>

This is an external dependency and the authority for:

- encodings and the computational cost model;
- polynomial-time computation;
- polynomial-time many-one reductions;
- NP and NP-hardness; and
- exact 3-SAT NP-completeness.

Pinned commit:

```text
14b5f413d2fb7adecde79c5451b483f9a1af59a8
```

The pin is deliberate because the upstream branch supports Coq 8.16 and
Coq Library of Undecidability Proofs `1.0.1+8.16`. Do not update only one of
these components.

## Correspondence policy

The repositories do not import proofs from one another:

- the thesis states and explains the result;
- Lean checks the broader p-adic mathematics;
- Coq checks the end-to-end complexity-theoretic hardness result.

Cross-repository agreement is maintained by comparing explicit source syntax,
compiler rows, pinning weight, threshold, and theorem quantifiers. A theorem
proved in one assistant is evidence and guidance for the other, but is not a
kernel-checked dependency.
