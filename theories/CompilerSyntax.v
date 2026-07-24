From Coq Require Import List Arith Bool ZArith Lia.
From Complexity.NP.SAT Require Import SAT kSAT.
From PhdThesisCoq Require Import SignedInt TargetSyntax SourceAdapter.

Import ListNotations.

Definition literal_coefficient (literal : bool * nat) : signed_integer :=
  if fst literal then signed_minus_one else signed_one.

Definition coefficient_for_variable
    (variable : nat) (clause : list (bool * nat)) : signed_integer :=
  fold_right
    (fun literal coefficient =>
      if Nat.eqb (literal_variable literal) variable
      then signed_add (literal_coefficient literal) coefficient
      else coefficient)
    signed_zero
    clause.

Definition clause_target (clause : list (bool * nat)) : signed_integer :=
  Nonnegative
    (length (filter (fun literal => negb (fst literal)) clause)).

Definition dense_clause_coefficients
    (num_variables : nat) (clause : list (bool * nat)) :
    list signed_integer :=
  map (fun variable => coefficient_for_variable variable clause)
    (seq 0 num_variables).

Definition clause_observation
    (num_variables : nat) (clause : list (bool * nat)) :
    affine_observation :=
  {| observation_is_positive := false;
     observation_weight := 1;
     observation_coefficients :=
       dense_clause_coefficients num_variables clause;
     observation_target := clause_target clause |}.

Definition unit_coefficients
    (num_variables variable : nat) : list signed_integer :=
  map
    (fun index =>
      if Nat.eqb index variable then signed_one else signed_zero)
    (seq 0 num_variables).

Definition pin_observation
    (num_variables variable pin_weight target : nat) :
    affine_observation :=
  {| observation_is_positive := true;
     observation_weight := pin_weight;
     observation_coefficients :=
       unit_coefficients num_variables variable;
     observation_target := Nonnegative target |}.

Fixpoint variable_occurs_in_clause
    (variable : nat) (clause : list (bool * nat)) : bool :=
  match clause with
  | [] => false
  | literal :: rest =>
      Nat.eqb (literal_variable literal) variable ||
      variable_occurs_in_clause variable rest
  end.

Definition variable_occurrence_count
    (variable : nat) (formula : list (list (bool * nat))) : nat :=
  length (filter (variable_occurs_in_clause variable) formula).

Definition maximum_occurrence
    (num_variables : nat) (formula : list (list (bool * nat))) : nat :=
  fold_right Nat.max 0
    (map
      (fun variable => variable_occurrence_count variable formula)
      (seq 0 num_variables)).

Definition pin_weight (formula : list (list (bool * nat))) : nat :=
  S (maximum_occurrence (source_num_variables formula) formula).

Definition pinning_observations_for_variable
    (num_variables weight variable : nat) : list affine_observation :=
  [ pin_observation num_variables variable weight 0;
    pin_observation num_variables variable weight 1 ].

Definition all_pinning_observations
    (num_variables weight : nat) : list affine_observation :=
  flat_map
    (pinning_observations_for_variable num_variables weight)
    (seq 0 num_variables).

Definition rejecting_instance : signed_regression_instance :=
  {| instance_num_variables := 0;
     instance_observations := [];
     instance_threshold := signed_minus_one |}.

Definition compile_valid
    (formula : list (list (bool * nat))) : signed_regression_instance :=
  let num_variables := source_num_variables formula in
  let weight := pin_weight formula in
  {| instance_num_variables := num_variables;
     instance_observations :=
       all_pinning_observations num_variables weight ++
       map (clause_observation num_variables) formula;
     instance_threshold :=
       signed_of_difference
         (weight * num_variables)
         (length formula) |}.

Definition compile
    (formula : list (list (bool * nat))) : signed_regression_instance :=
  if kCNF_decb 3 formula then compile_valid formula else rejecting_instance.

Lemma dense_clause_coefficients_length num_variables clause :
  length (dense_clause_coefficients num_variables clause) = num_variables.
Proof.
  unfold dense_clause_coefficients.
  rewrite map_length, seq_length.
  reflexivity.
Qed.

Lemma unit_coefficients_length num_variables variable :
  length (unit_coefficients num_variables variable) = num_variables.
Proof.
  unfold unit_coefficients.
  rewrite map_length, seq_length.
  reflexivity.
Qed.

Lemma clause_observation_well_formed num_variables clause :
  observation_well_formed num_variables
    (clause_observation num_variables clause).
Proof.
  unfold observation_well_formed, clause_observation; cbn.
  apply dense_clause_coefficients_length.
Qed.

Lemma pin_observation_well_formed num_variables variable weight target :
  observation_well_formed num_variables
    (pin_observation num_variables variable weight target).
Proof.
  unfold observation_well_formed, pin_observation; cbn.
  apply unit_coefficients_length.
Qed.

Lemma all_pinning_observations_well_formed num_variables weight :
  Forall (observation_well_formed num_variables)
    (all_pinning_observations num_variables weight).
Proof.
  unfold all_pinning_observations.
  apply Forall_flat_map.
  apply Forall_forall.
  intros variable Hin.
  unfold pinning_observations_for_variable.
  repeat constructor; apply pin_observation_well_formed.
Qed.

Lemma compile_valid_well_formed formula :
  instance_well_formed (compile_valid formula).
Proof.
  unfold instance_well_formed, compile_valid; cbn.
  apply Forall_app.
  split.
  - apply all_pinning_observations_well_formed.
  - apply Forall_forall.
    intros row Hin.
    apply in_map_iff in Hin.
    destruct Hin as [clause [Heq Hin]].
    subst row.
    apply clause_observation_well_formed.
Qed.

Lemma rejecting_instance_well_formed :
  instance_well_formed rejecting_instance.
Proof. constructor. Qed.

Theorem compile_well_formed formula :
  instance_well_formed (compile formula).
Proof.
  unfold compile.
  destruct (kCNF_decb 3 formula).
  - apply compile_valid_well_formed.
  - apply rejecting_instance_well_formed.
Qed.

Lemma all_pinning_observations_length num_variables weight :
  length (all_pinning_observations num_variables weight) =
    2 * num_variables.
Proof.
  unfold all_pinning_observations.
  replace (2 * num_variables) with
    (2 * length (seq 0 num_variables)) by now rewrite seq_length.
  generalize (seq 0 num_variables).
  intros variables.
  induction variables as [|variable variables IH]; cbn.
  - lia.
  - unfold pinning_observations_for_variable in *; cbn.
    lia.
Qed.

Theorem compile_valid_observation_count formula :
  length (instance_observations (compile_valid formula)) =
    2 * source_num_variables formula + length formula.
Proof.
  unfold compile_valid; cbn.
  rewrite app_length, all_pinning_observations_length, map_length.
  reflexivity.
Qed.

Theorem compile_valid_threshold formula :
  signed_integer_value (instance_threshold (compile_valid formula)) =
    (Z.of_nat (pin_weight formula * source_num_variables formula) -
      Z.of_nat (length formula))%Z.
Proof.
  unfold compile_valid; cbn.
  apply signed_of_difference_value.
Qed.
