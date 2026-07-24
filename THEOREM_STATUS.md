# Theorem status

This ledger distinguishes imported foundations, project-specific semantic
results, polynomial-time implementation results, and the final hardness
composition.

| Result | Status | Completion criterion |
|---|---|---|
| Upstream exact 3-SAT is NP-complete | Complete, imported | `Project.upstream_three_sat_is_np_complete` type-checks against the pinned theorem `CookLevin0`. |
| Source-language adapter | In progress | `SourceAdapter.v` now uses upstream `kCNF 3` directly, proves variable bounds, and decomposes exact three-literal clauses without normalising repetitions. The remaining reduction theorem must connect the total compiler's rejection branch to `kCNF_decb 3`. |
| Concrete signed-regression instance encoding | In progress | `SignedInt.v` and `TargetSyntax.v` provide finite MetaCoq encodings for canonical signed integers, observations, and instances. The syntax is not complete until its acceptance predicate is connected to the concrete `5`-adic model. |
| Concrete `5`-adic acceptance semantics | Pending | Acceptance is defined over an actual `5`-adic field, with the required norm facts proved rather than postulated. |
| Boolean pinning and clause indicator | In progress | `BooleanSemantics.v` proves the pin-pair constant, repeated-literal clause residual identity, clause indicator, and exact Boolean loss formula. The arbitrary-`5`-adic pinning theorem remains. |
| Compiler semantic correctness | In progress | `compile_valid_boolean_correct` proves correctness for Boolean points and upstream SAT assignments. The converse from an arbitrary accepting `5`-adic point, plus the invalid-input branch of `compile`, remains. |
| Compiler output-size bound | Pending | The target encoding length is bounded by a polynomial in the encoded source length. |
| Compiler polynomial-time implementation | Pending | The executable compiler is proved polynomial-time in the upstream Coq complexity model. |
| Signed fixed-prime regression is NP-hard | Pending | The compiler reduction is composed with `CookLevin0`, and `Print Assumptions` reveals no project-defined axioms or admitted facts. |

## Headline target

The precise declaration name may change as the upstream APIs are integrated,
but its content should be equivalent to:

```coq
Theorem fixed_prime_signed_regression_is_NP_hard :
  NPhard FixedPrimeSignedRegression.
```

If the project later proves membership in NP, record NP-completeness as a
separate theorem. NP membership is not required for the thesis's NP-hardness
claim.

## Initial audit

With Coq 8.16.1 and the pinned dependencies:

- the complete project builds;
- `Print Assumptions Project.upstream_three_sat_is_np_complete` reports
  `Closed under the global context`; and
- the project source contains no `Admitted`, `admit`, or project-defined
  `Axiom` declaration.

## First compiler milestone

The first project-specific increment adds:

- a total compiler with an explicit rejecting instance for non-`kCNF 3`
  inputs;
- dense clause rows that accumulate every literal occurrence, including
  repeated variables and cancelling positive/negative occurrences;
- two pinning rows per source variable and one reward row per source clause;
- exact observation-count and threshold-value theorems; and
- Boolean semantic correctness
  (`BooleanSemantics.compile_valid_boolean_correct`).

The full project builds with Coq 8.16.1. `Print Assumptions` reports
`Closed under the global context` for
`CompilerSyntax.compile_well_formed`,
`CompilerSyntax.compile_valid_observation_count`,
`CompilerSyntax.compile_valid_threshold`, and
`BooleanSemantics.compile_valid_boolean_correct`.

This milestone is not the NP-hardness theorem: it does not yet supply a
concrete `5`-adic field, arbitrary-point soundness, an encoded-size bound,
or a polynomial-time reduction proof.
