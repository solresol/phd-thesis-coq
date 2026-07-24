From Coq Require Import List Arith Bool ZArith Lia.
From Complexity.NP.SAT Require Import SAT kSAT.
From PhdThesisCoq Require Import SignedInt TargetSyntax SourceAdapter.

Import ListNotations.

Definition literal_coefficient (literal : bool * nat) : signed_integer :=
  if fst literal then signed_minus_one else signed_one.

Fixpoint coefficient_for_variable
    (variable : nat) (clause : list (bool * nat)) : signed_integer :=
  match clause with
  | [] => signed_zero
  | literal :: rest =>
      if Nat.eqb (literal_variable literal) variable
      then
        signed_add
          (literal_coefficient literal)
          (coefficient_for_variable variable rest)
      else coefficient_for_variable variable rest
  end.

Fixpoint negative_literal_count (clause : list (bool * nat)) : nat :=
  match clause with
  | [] => 0
  | literal :: rest =>
      if negb (fst literal)
      then S (negative_literal_count rest)
      else negative_literal_count rest
  end.

Definition clause_target (clause : list (bool * nat)) : signed_integer :=
  Nonnegative (negative_literal_count clause).

Fixpoint dense_clause_coefficients_from
    (start count : nat) (clause : list (bool * nat)) :
    list signed_integer :=
  match count with
  | 0 => []
  | S count' =>
      coefficient_for_variable start clause ::
      dense_clause_coefficients_from (S start) count' clause
  end.

Definition dense_clause_coefficients
    (num_variables : nat) (clause : list (bool * nat)) :
    list signed_integer :=
  dense_clause_coefficients_from 0 num_variables clause.

Definition clause_observation
    (num_variables : nat) (clause : list (bool * nat)) :
    affine_observation :=
  {| observation_is_positive := false;
     observation_weight := 1;
     observation_coefficients :=
       dense_clause_coefficients num_variables clause;
     observation_target := clause_target clause |}.

Fixpoint unit_coefficients_from
    (start count variable : nat) : list signed_integer :=
  match count with
  | 0 => []
  | S count' =>
      (if Nat.eqb start variable then signed_one else signed_zero) ::
      unit_coefficients_from (S start) count' variable
  end.

Definition unit_coefficients
    (num_variables variable : nat) : list signed_integer :=
  unit_coefficients_from 0 num_variables variable.

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

Fixpoint variable_occurrence_count
    (variable : nat) (formula : list (list (bool * nat))) : nat :=
  match formula with
  | [] => 0
  | clause :: rest =>
      if variable_occurs_in_clause variable clause
      then S (variable_occurrence_count variable rest)
      else variable_occurrence_count variable rest
  end.

Fixpoint maximum_occurrence
    (num_variables : nat) (formula : list (list (bool * nat))) : nat :=
  match num_variables with
  | 0 => 0
  | S num_variables' =>
      Nat.max
        (variable_occurrence_count num_variables' formula)
        (maximum_occurrence num_variables' formula)
  end.

Definition pin_weight (formula : list (list (bool * nat))) : nat :=
  S (maximum_occurrence (source_num_variables formula) formula).

Definition pinning_observations_for_variable
    (num_variables weight variable : nat) : list affine_observation :=
  [ pin_observation num_variables variable weight 0;
    pin_observation num_variables variable weight 1 ].

Fixpoint all_pinning_observations_from
    (num_variables weight start count : nat) :
    list affine_observation :=
  match count with
  | 0 => []
  | S count' =>
      pinning_observations_for_variable num_variables weight start ++
      all_pinning_observations_from
        num_variables weight (S start) count'
  end.

Definition all_pinning_observations
    (num_variables weight : nat) : list affine_observation :=
  all_pinning_observations_from
    num_variables weight 0 num_variables.

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
  generalize 0 as start.
  induction num_variables as [|num_variables IH]; cbn.
  - reflexivity.
  - intros start.
    rewrite IH.
    reflexivity.
Qed.

Lemma unit_coefficients_length num_variables variable :
  length (unit_coefficients num_variables variable) = num_variables.
Proof.
  unfold unit_coefficients.
  generalize 0 as start.
  induction num_variables as [|num_variables IH]; cbn.
  - reflexivity.
  - intros start.
    rewrite IH.
    reflexivity.
Qed.

Lemma negative_literal_count_filter_length clause :
  negative_literal_count clause =
  length (filter (fun literal => negb (fst literal)) clause).
Proof.
  induction clause as [|literal rest IH]; cbn.
  - reflexivity.
  - destruct (negb (fst literal)); cbn; lia.
Qed.

Lemma dense_clause_coefficients_from_map_seq start count clause :
  dense_clause_coefficients_from start count clause =
  map
    (fun variable => coefficient_for_variable variable clause)
    (seq start count).
Proof.
  revert start.
  induction count as [|count IH]; intros start; cbn.
  - reflexivity.
  - rewrite IH.
    reflexivity.
Qed.

Lemma dense_clause_coefficients_map_seq num_variables clause :
  dense_clause_coefficients num_variables clause =
  map
    (fun variable => coefficient_for_variable variable clause)
    (seq 0 num_variables).
Proof.
  apply dense_clause_coefficients_from_map_seq.
Qed.

Lemma unit_coefficients_from_map_seq start count variable :
  unit_coefficients_from start count variable =
  map
    (fun index =>
      if Nat.eqb index variable then signed_one else signed_zero)
    (seq start count).
Proof.
  revert start.
  induction count as [|count IH]; intros start; cbn.
  - reflexivity.
  - rewrite IH.
    reflexivity.
Qed.

Lemma unit_coefficients_map_seq num_variables variable :
  unit_coefficients num_variables variable =
  map
    (fun index =>
      if Nat.eqb index variable then signed_one else signed_zero)
    (seq 0 num_variables).
Proof.
  apply unit_coefficients_from_map_seq.
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
  assert (H :
    forall count start,
      Forall
        (observation_well_formed num_variables)
        (all_pinning_observations_from
          num_variables weight start count)).
  {
    induction count as [|count IH]; intros start; cbn.
    - constructor.
    - unfold pinning_observations_for_variable.
      cbn.
      constructor.
      + apply pin_observation_well_formed.
      + constructor.
        * apply pin_observation_well_formed.
        * apply IH.
  }
  apply H.
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
  assert (H :
    forall count start,
      length
        (all_pinning_observations_from
          num_variables weight start count) =
      2 * count).
  {
    induction count as [|count IH]; intros start; cbn.
    - lia.
    - unfold pinning_observations_for_variable.
      rewrite IH.
      cbn.
      lia.
  }
  apply H.
Qed.

Lemma all_pinning_observations_from_flat_map_seq
    num_variables weight start count :
  all_pinning_observations_from num_variables weight start count =
  flat_map
    (pinning_observations_for_variable num_variables weight)
    (seq start count).
Proof.
  revert start.
  induction count as [|count IH]; intros start; cbn.
  - reflexivity.
  - rewrite IH.
    reflexivity.
Qed.

Lemma all_pinning_observations_flat_map_seq num_variables weight :
  all_pinning_observations num_variables weight =
  flat_map
    (pinning_observations_for_variable num_variables weight)
    (seq 0 num_variables).
Proof.
  apply all_pinning_observations_from_flat_map_seq.
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
