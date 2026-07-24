# Theorem status

This ledger distinguishes imported foundations, project-specific semantic
results, polynomial-time implementation results, and the final hardness
composition.

| Result | Status | Completion criterion |
|---|---|---|
| Upstream exact 3-SAT is NP-complete | Complete, imported | `Project.upstream_three_sat_is_np_complete` type-checks against the pinned theorem `CookLevin0`. |
| Source-language adapter | Complete | `SourceAdapter.v` uses upstream `kCNF 3` directly, proves variable bounds, and decomposes exact three-literal clauses without normalising repetitions. `compile_five_adic_correct` also proves that the total compiler's rejection branch rejects every non-`kCNF 3` input. |
| Concrete signed-regression instance encoding | Complete | `SignedInt.v` and `TargetSyntax.v` provide finite MetaCoq encodings for canonical signed integers, observations, and instances, together with constructor computability instances used by the reduction. |
| Concrete `5`-adic acceptance semantics | Complete | `FiveAdic.v` constructs `Q5` as the fraction field of the inverse-limit `5`-adic integers supplied by the pinned `fpseries` development. Its norm laws, including multiplicativity, are proved from that concrete model rather than postulated. |
| Boolean pinning and clause indicator | Complete | `BooleanSemantics.v` proves the pin-pair constant, repeated-literal clause residual identity, clause indicator, and exact Boolean loss formula. `RegressionSemantics.v` proves the arbitrary-point pinning lower bound and coordinate-rounding inequality. |
| Compiler semantic correctness | Complete | `compile_five_adic_correct` proves `kSAT 3 formula <-> FixedPrimeSignedRegression (compile formula)`, including reconstruction of a finite SAT assignment from an arbitrary accepting `5`-adic point and the total compiler's invalid-input branch. |
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

## Concrete five-adic semantic milestone

The second project-specific increment adds:

- a pinned snapshot of `fpseries`, patched only for Coq 8.16 and MathComp
  compatibility and built in a repository-local namespace;
- a proof of multiplicativity for the inverse-limit `5`-adic valuation;
- the concrete field `Q5`, its norm, and the norm laws used by the reduction;
- an exact interpretation of the signed target encoding over `Q5`;
- a coordinate-rounding proof showing that every accepting arbitrary
  `5`-adic point yields an accepting Boolean point; and
- the semantic equivalence theorem
  `RegressionSemantics.compile_five_adic_correct`.

The full project builds with Coq 8.16.1. `Print Assumptions` for
`compile_valid_five_adic_sound` and `compile_five_adic_correct` reports only
MathComp's standard classical support
(`propositional_extensionality`, dependent functional extensionality, and
constructive indefinite description). It reports no project-defined axiom or
admitted result.

This milestone is still not the NP-hardness theorem: the compiler's encoded
output-size and polynomial-time bounds, the `reducesPolyMO` value, and the
composition with `CookLevin0` remain.
