From Complexity.Complexity Require Import NP.
From Complexity.NP.SAT Require Import kSAT CookLevin.

(**
  This file is the initial dependency smoke test for the project.

  The theorem below deliberately aliases the exact upstream result that will
  supply the source hardness theorem for the fixed-prime regression
  reduction. Project-specific source syntax, target semantics, compiler
  correctness, and polynomial-time construction will be added in separate
  modules.
*)

Module Project.

Theorem upstream_three_sat_is_np_complete :
  NPcomplete (kSAT 3).
Proof.
  exact CookLevin0.
Qed.

Print Assumptions upstream_three_sat_is_np_complete.

End Project.
