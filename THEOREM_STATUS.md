# Theorem status

This ledger distinguishes imported foundations, project-specific semantic
results, polynomial-time implementation results, and the final hardness
composition.

| Result | Status | Completion criterion |
|---|---|---|
| Upstream exact 3-SAT is NP-complete | Complete, imported | `Project.upstream_three_sat_is_np_complete` type-checks against the pinned theorem `CookLevin0`. |
| Source-language adapter | Pending | The accepted 3-CNF syntax is proved equivalent to upstream `kSAT 3`, including a deliberate treatment of repeated variables and literals. |
| Concrete signed-regression instance encoding | Pending | A finite, encodable syntax represents the `p = 5` integer-coefficient instances and threshold used by the reduction. |
| Concrete `5`-adic acceptance semantics | Pending | Acceptance is defined over an actual `5`-adic field, with the required norm facts proved rather than postulated. |
| Boolean pinning and clause indicator | Pending | The unary pinning and three-literal reward identities are machine-checked for the chosen syntax. |
| Compiler semantic correctness | Pending | `F` is satisfiable if and only if `compile F` accepts. |
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
