# Proof architecture

## 1. Imported complexity foundation

The project uses the Coq Library of Complexity Theory rather than defining a
second ad hoc notion of polynomial reduction. The pinned upstream theorem is:

```coq
CookLevin0 : NPcomplete (kSAT 3)
```

All project-specific encodings and running-time arguments must inhabit that
same framework so that the final transitive reduction is a theorem rather
than an informal appeal to Cook--Levin.

## 2. Source-language boundary

The upstream predicate `kSAT 3` requires every clause to contain exactly
three literals, but it does not require the three variables to be distinct.
The current Lean `Clause` structure does require distinct variables.

The Coq development must make one of these routes explicit:

1. prove the regression compiler correct directly for all upstream
   exact-three-literal clauses, including repetitions; or
2. define and verify a polynomial normalization into the distinct-variable
   convention.

The first route is preferred if the clause indicator and variable-influence
bounds survive unchanged or with a simple inequality. A silent restriction
to distinct-variable clauses is not sufficient for the final hardness
composition.

## 3. Target syntax and semantics

Separate the target into:

- a finite syntax containing the number of variables, integer coefficient
  rows, signs or row classes, weights, targets, and decision threshold; and
- a semantic interpretation over the actual field of `5`-adic numbers.

The compiler emits only a small fragment:

- integer coefficients and targets;
- positive Boolean-pinning rows for `x_i = 0` and `x_i = 1`;
- negative unit-weight clause rows; and
- a natural pinning weight and integer threshold.

Keep this fragment explicit. A smaller concrete target makes encoding and
running-time proofs easier and still proves hardness of any larger problem
that contains the fragment by a checked inclusion reduction.

## 4. Mathematical correctness

The semantic proof should be factored into the following results:

1. norms of the small integers needed at `p = 5`;
2. the three-literal clause-row indicator;
3. a coordinate-snapping inequality for the Boolean domain `{0, 1}`;
4. existence of a Boolean global minimizer when the pinning weight dominates
   variable influence;
5. the objective formula on Boolean assignments; and
6. satisfiability if and only if the compiled threshold is attainable.

The Lean files `FiniteDomainCompiler.lean`, `ClauseCompiler.lean`, and
`FixedPrimeHardness.lean` are mathematical references, not trusted inputs.
The Coq proof must reconstruct the argument in its own kernel.

## 5. Complexity correctness

Semantic equivalence alone is not the final theorem. Define concrete
encodings for the source formula and target instance, implement the compiler,
and prove:

- the implementation denotes the semantic compiler;
- the encoded output length is polynomially bounded; and
- the implementation runs in polynomial time according to the upstream
  call-by-value lambda-calculus cost model.

Then construct an upstream polynomial many-one reduction from `kSAT 3` to the
target language and use transitivity to derive NP-hardness.

## 6. Axiom and parity audit

At each major milestone:

- run `Print Assumptions`;
- search for `Admitted`, `admit`, and project-defined `Axiom` declarations;
- compare the compiler, threshold, and source convention with the Lean
  analogue; and
- update `THEOREM_STATUS.md`.

The final handoff should state both what Coq checks and whether the Coq and
Lean theorem statements are extensionally aligned.
