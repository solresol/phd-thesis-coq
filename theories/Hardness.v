From Complexity Require Import Complexity.NP Complexity.Definitions.
From Complexity.NP.SAT Require Import kSAT CookLevin.
From PhdThesisCoq Require Import
  CompilerComplexity RegressionSemantics.

Theorem exact_three_sat_reduces_to_fixed_prime_signed_regression :
  kSAT 3 ⪯p FixedPrimeSignedRegression.
Proof.
  eapply reducesPolyMO_intro with (f := compile_timed).
  - exact compile_timed_polytime.
  - intros formula.
    rewrite compile_timed_eq.
    apply compile_five_adic_correct.
Qed.

Theorem fixed_prime_signed_regression_is_NP_hard :
  NPhard FixedPrimeSignedRegression.
Proof.
  eapply red_NPhard.
  - apply exact_three_sat_reduces_to_fixed_prime_signed_regression.
  - exact (proj1 CookLevin0).
Qed.

Print Assumptions exact_three_sat_reduces_to_fixed_prime_signed_regression.
Print Assumptions fixed_prime_signed_regression_is_NP_hard.
