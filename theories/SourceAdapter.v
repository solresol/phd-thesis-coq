From Coq Require Import List Arith Lia.
From Complexity.NP.SAT Require Import SAT kSAT.

Import ListNotations.

Definition literal_variable (l : bool * nat) : nat := snd l.

Definition max_literal_variable (l : bool * nat) : nat :=
  literal_variable l.

Fixpoint max_clause_variable (clause : list (bool * nat)) : nat :=
  match clause with
  | [] => 0
  | literal :: rest =>
      Nat.max (max_literal_variable literal) (max_clause_variable rest)
  end.

Fixpoint max_cnf_variable (formula : list (list (bool * nat))) : nat :=
  match formula with
  | [] => 0
  | clause :: rest =>
      Nat.max (max_clause_variable clause) (max_cnf_variable rest)
  end.

Fixpoint cnf_has_variables (formula : list (list (bool * nat))) : bool :=
  match formula with
  | [] => false
  | clause :: rest =>
      negb (Nat.eqb (length clause) 0) || cnf_has_variables rest
  end.

Definition source_num_variables (formula : list (list (bool * nat))) : nat :=
  if cnf_has_variables formula then S (max_cnf_variable formula) else 0.

Lemma max_clause_variable_bounds clause sign variable :
  In (sign, variable) clause ->
  variable <= max_clause_variable clause.
Proof.
  unfold max_literal_variable, literal_variable.
  induction clause as [|[s v] clause IH]; cbn.
  - contradiction.
  - intros [Heq | Hin].
    + inversion Heq; subst. apply Nat.le_max_l.
    + eapply Nat.le_trans.
      * apply IH. exact Hin.
      * apply Nat.le_max_r.
Qed.

Lemma max_cnf_variable_bounds formula clause sign variable :
  In clause formula ->
  In (sign, variable) clause ->
  variable <= max_cnf_variable formula.
Proof.
  induction formula as [|head tail IH]; cbn.
  - contradiction.
  - intros [Heq | Hin] Hliteral.
    + subst head. eapply Nat.le_trans.
      * apply (max_clause_variable_bounds
          (clause := clause) (sign := sign) (variable := variable)).
        exact Hliteral.
      * apply Nat.le_max_l.
    + eapply Nat.le_trans.
      * eapply IH; eassumption.
      * apply Nat.le_max_r.
Qed.

Lemma source_variable_lt_num_variables formula clause sign variable :
  In clause formula ->
  In (sign, variable) clause ->
  variable < source_num_variables formula.
Proof.
  intros Hclause Hliteral.
  unfold source_num_variables.
  assert (Hexists :
      cnf_has_variables formula = true).
  {
    induction formula as [|head tail IH]; cbn in *.
    - contradiction.
    - destruct Hclause as [Heq | Hin].
      + subst head.
        apply Bool.orb_true_iff.
        left.
        apply Bool.negb_true_iff.
        apply Nat.eqb_neq.
        intro Hzero.
        apply length_zero_iff_nil in Hzero.
        subst clause.
        contradiction.
      + apply Bool.orb_true_iff.
        right.
        apply IH.
        exact Hin.
  }
  rewrite Hexists.
  apply Nat.lt_succ_r.
  eapply max_cnf_variable_bounds; eassumption.
Qed.

(**
  Upstream [kSAT 3] requires exactly three list entries in every clause.  It
  does not require distinct variables or distinct literals.  The compiler
  deliberately consumes this syntax without a normalization pass.
*)
Definition exact_three_cnf (formula : list (list (bool * nat))) : Prop :=
  kCNF 3 formula.

Lemma exact_three_clause_decompose formula clause :
  exact_three_cnf formula ->
  In clause formula ->
  exists l0 l1 l2, clause = [l0; l1; l2].
Proof.
  intros Hthree Hin.
  unfold exact_three_cnf in Hthree.
  pose proof
    ((proj1 (kCNF_clause_length 3 formula)) Hthree clause Hin)
    as Hlength.
  destruct clause as [|l0 [|l1 [|l2 [|l3 rest]]]]; cbn in Hlength;
    try discriminate.
  exists l0, l1, l2.
  reflexivity.
Qed.
