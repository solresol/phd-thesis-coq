From Coq Require Import List Arith Lia.
From Undecidability.L.Tactics Require Import LTactics.
From Undecidability.L.Datatypes Require Import LNat Lists LBool LProd.
From Complexity Require Import
  Complexity.NP Complexity.Definitions CookPrelim.PolyBounds.
From Complexity.NP.SAT Require Import SAT kSAT.
From Complexity.L Require Import ComparisonTimeBoundDerivation.
From PhdThesisCoq Require Import
  SignedInt TargetSyntax SourceAdapter CompilerSyntax.

Import ListNotations.
Import explicit_bounds.

Definition signed_of_difference_time (a b : nat) : nat :=
  if b <=? a
  then c__leb2 + leb_time b a + c__sub1 + sub_time a b + 5
  else c__leb2 + leb_time b a + 2 * c__sub1 +
    sub_time b a + sub_time (b - a) 1 + 6.

#[global] Instance term_signed_of_difference :
  computableTime' signed_of_difference
    (fun a _ => (1, fun b _ => (signed_of_difference_time a b, tt))).
Proof.
  unfold signed_of_difference.
  extract.
  solverec.
  all: unfold signed_of_difference_time.
  all: rewrite H.
  all: reflexivity.
Qed.

Lemma formula_length_le_size
    (formula : list (list (bool * nat))) :
  length formula <= size (enc formula).
Proof.
  apply size_list_enc_r.
Qed.

Lemma clause_length_le_size (clause : list (bool * nat)) :
  length clause <= size (enc clause).
Proof.
  apply size_list_enc_r.
Qed.

Lemma clause_size_le_formula_size
    (formula : list (list (bool * nat)))
    (clause : list (bool * nat)) :
  In clause formula ->
  size (enc clause) <= size (enc formula).
Proof.
  apply size_list_In.
Qed.

Lemma literal_size_le_clause_size
    (clause : list (bool * nat)) (literal : bool * nat) :
  In literal clause ->
  size (enc literal) <= size (enc clause).
Proof.
  apply size_list_In.
Qed.

Lemma literal_variable_le_literal_size (literal : bool * nat) :
  snd literal <= size (enc literal).
Proof.
  destruct literal as [sign variable].
  rewrite size_prod.
  cbn.
  pose proof (size_nat_enc_r variable).
  lia.
Qed.

Lemma literal_variable_le_formula_size
    (formula : list (list (bool * nat)))
    (clause : list (bool * nat)) (literal : bool * nat) :
  In clause formula ->
  In literal clause ->
  snd literal <= size (enc formula).
Proof.
  intros Hclause Hliteral.
  eapply Nat.le_trans.
  - apply literal_variable_le_literal_size.
  - eapply Nat.le_trans.
    + apply literal_size_le_clause_size.
      exact Hliteral.
    + apply clause_size_le_formula_size.
      exact Hclause.
Qed.

Lemma max_clause_variable_le_size (clause : list (bool * nat)) :
  max_clause_variable clause <= size (enc clause).
Proof.
  induction clause as [|literal rest IH]; cbn [max_clause_variable].
  - lia.
  - rewrite list_size_cons.
    apply Nat.max_lub.
    + eapply Nat.le_trans.
      * unfold max_literal_variable, literal_variable.
        apply literal_variable_le_literal_size.
      * lia.
    + lia.
Qed.

Lemma max_cnf_variable_le_size
    (formula : list (list (bool * nat))) :
  max_cnf_variable formula <= size (enc formula).
Proof.
  induction formula as [|clause rest IH]; cbn [max_cnf_variable].
  - lia.
  - rewrite list_size_cons.
    apply Nat.max_lub.
    + eapply Nat.le_trans.
      * apply max_clause_variable_le_size.
      * lia.
    + lia.
Qed.

Lemma source_num_variables_le_size_succ
    (formula : list (list (bool * nat))) :
  source_num_variables formula <= S (size (enc formula)).
Proof.
  unfold source_num_variables.
  destruct (cnf_has_variables formula).
  - cbn.
    pose proof (max_cnf_variable_le_size formula).
    lia.
  - lia.
Qed.

Lemma variable_occurrence_count_le_formula_length
    variable (formula : list (list (bool * nat))) :
  variable_occurrence_count variable formula <= length formula.
Proof.
  induction formula as [|head rest IH].
  - cbn [variable_occurrence_count].
    lia.
  - cbn [variable_occurrence_count].
    destruct (variable_occurs_in_clause variable head) eqn:Hoccurs;
      cbn; lia.
Qed.

Lemma maximum_occurrence_le_formula_length
    num_variables (formula : list (list (bool * nat))) :
  maximum_occurrence num_variables formula <= length formula.
Proof.
  induction num_variables as [|num_variables IH];
    cbn [maximum_occurrence].
  - lia.
  - apply Nat.max_lub.
    + apply variable_occurrence_count_le_formula_length.
    + exact IH.
Qed.

Lemma pin_weight_le_size_succ
    (formula : list (list (bool * nat))) :
  pin_weight formula <= S (size (enc formula)).
Proof.
  unfold pin_weight.
  pose proof
    (maximum_occurrence_le_formula_length
      (source_num_variables formula) formula).
  pose proof (formula_length_le_size formula).
  lia.
Qed.

Definition signed_add_time (x y : signed_integer) : nat :=
  match x, y with
  | Nonnegative a, Nonnegative b => c__add1 + add_time a + 10
  | Nonnegative a, Negative b =>
      signed_of_difference_time a (1 + b) + 11
  | Negative a, Nonnegative b =>
      signed_of_difference_time b (1 + a) + 11
  | Negative a, Negative b => c__add1 + add_time a + 11
  end.

#[global] Instance term_signed_add :
  computableTime' signed_add
    (fun a _ => (1, fun b _ => (signed_add_time a b, tt))).
Proof.
  unfold signed_add.
  extract.
  solverec.
  all: unfold signed_add_time.
  all: reflexivity.
Qed.

Fixpoint max_clause_variable_time (clause : list (bool * nat)) : nat :=
  match clause with
  | [] => 8
  | literal :: rest =>
      max_clause_variable_time rest + c__max1 +
      max_time (snd literal) (max_clause_variable rest) + 15
  end.

#[global] Instance term_max_clause_variable :
  computableTime' max_clause_variable
    (fun clause _ => (max_clause_variable_time clause, tt)).
Proof.
  unfold max_clause_variable, max_literal_variable, literal_variable.
  extract.
  solverec.
  all: cbn [max_clause_variable_time].
  all: try reflexivity.
Qed.

Fixpoint max_cnf_variable_time
    (formula : list (list (bool * nat))) : nat :=
  match formula with
  | [] => 8
  | clause :: rest =>
      max_cnf_variable_time rest +
      max_clause_variable_time clause + c__max1 +
      max_time (max_clause_variable clause) (max_cnf_variable rest) + 10
  end.

#[global] Instance term_max_cnf_variable :
  computableTime' max_cnf_variable
    (fun formula _ => (max_cnf_variable_time formula, tt)).
Proof.
  unfold max_cnf_variable.
  extract.
  solverec.
  all: cbn [max_cnf_variable_time].
  all: try reflexivity.
Qed.

Fixpoint cnf_has_variables_time
    (formula : list (list (bool * nat))) : nat :=
  match formula with
  | [] => 8
  | clause :: rest =>
      cnf_has_variables_time rest +
      c__length * length clause + c__length +
      EqBool.eqbTime (size (enc (length clause))) (size (enc 0)) + 24
  end.

#[global] Instance term_cnf_has_variables :
  computableTime' cnf_has_variables
    (fun formula _ => (cnf_has_variables_time formula, tt)).
Proof.
  unfold cnf_has_variables.
  extract.
  solverec.
  all: cbn [cnf_has_variables_time].
  all: try reflexivity.
Qed.

Definition source_num_variables_time
    (formula : list (list (bool * nat))) : nat :=
  if cnf_has_variables formula
  then cnf_has_variables_time formula + max_cnf_variable_time formula + 5
  else cnf_has_variables_time formula + 4.

#[global] Instance term_source_num_variables :
  computableTime' source_num_variables
    (fun formula _ => (source_num_variables_time formula, tt)).
Proof.
  unfold source_num_variables.
  extract.
  solverec.
  all: unfold source_num_variables_time.
  all: rewrite H.
  all: reflexivity.
Qed.

#[global] Instance term_literal_coefficient :
  computableTime' literal_coefficient
    (fun _ _ => (9, tt)).
Proof.
  unfold literal_coefficient.
  extract.
  solverec.
Qed.

Fixpoint coefficient_for_variable_time
    (variable : nat) (clause : list (bool * nat)) : nat :=
  match clause with
  | [] => 8
  | literal :: rest =>
      EqBool.eqbTime
        (size (enc (snd literal))) (size (enc variable)) +
      coefficient_for_variable_time variable rest +
      if Nat.eqb (snd literal) variable
      then
        signed_add_time
          (literal_coefficient literal)
          (coefficient_for_variable variable rest) + 34
      else 24
  end.

#[global] Instance term_coefficient_for_variable :
  computableTime' coefficient_for_variable
    (fun variable _ =>
      (5, fun clause _ =>
        (coefficient_for_variable_time variable clause, tt))).
Proof.
  unfold coefficient_for_variable, literal_variable.
  extract.
  solverec.
  all: cbn [coefficient_for_variable_time].
  all: try rewrite H0.
  all: try reflexivity.
  all: lia.
Qed.

Fixpoint negative_literal_count_time
    (clause : list (bool * nat)) : nat :=
  match clause with
  | [] => 8
  | literal :: rest =>
      negative_literal_count_time rest +
      if negb (fst literal) then 23 else 22
  end.

#[global] Instance term_negative_literal_count :
  computableTime' negative_literal_count
    (fun clause _ => (negative_literal_count_time clause, tt)).
Proof.
  unfold negative_literal_count.
  extract.
  solverec.
  all: cbn [negative_literal_count_time].
  all: try rewrite H0.
  all: reflexivity.
Qed.

Definition clause_target_time (clause : list (bool * nat)) : nat :=
  negative_literal_count_time clause + 2.

#[global] Instance term_clause_target :
  computableTime' clause_target
    (fun clause _ => (clause_target_time clause, tt)).
Proof.
  unfold clause_target.
  extract.
  solverec.
  unfold clause_target_time.
  reflexivity.
Qed.

Fixpoint dense_clause_coefficients_from_time
    (start count : nat) (clause : list (bool * nat)) : nat :=
  match count with
  | 0 => 4
  | S count' =>
      dense_clause_coefficients_from_time (S start) count' clause +
      coefficient_for_variable_time start clause + 23
  end.

#[global] Instance term_dense_clause_coefficients_from :
  computableTime' dense_clause_coefficients_from
    (fun start _ =>
      (5, fun count _ =>
        (5, fun clause _ =>
          (dense_clause_coefficients_from_time start count clause, tt)))).
Proof.
  unfold dense_clause_coefficients_from.
  extract.
  solverec.
  all: cbn [dense_clause_coefficients_from_time].
  all: try reflexivity.
Qed.

Definition dense_clause_coefficients_time
    (num_variables : nat) (clause : list (bool * nat)) : nat :=
  dense_clause_coefficients_from_time 0 num_variables clause + 11.

#[global] Instance term_dense_clause_coefficients :
  computableTime' dense_clause_coefficients
    (fun num_variables _ =>
      (5, fun clause _ =>
        (dense_clause_coefficients_time num_variables clause, tt))).
Proof.
  unfold dense_clause_coefficients.
  extract.
  solverec.
  unfold dense_clause_coefficients_time.
  reflexivity.
Qed.

Definition clause_observation_time
    (num_variables : nat) (clause : list (bool * nat)) : nat :=
  clause_target_time clause +
  dense_clause_coefficients_time num_variables clause + 110.

#[global] Instance term_clause_observation :
  computableTime' clause_observation
    (fun num_variables _ =>
      (5, fun clause _ =>
        (clause_observation_time num_variables clause, tt))).
Proof.
  unfold clause_observation.
  extract.
  solverec.
  unfold clause_observation_time.
  reflexivity.
Qed.

Fixpoint unit_coefficients_from_time
    (start count variable : nat) : nat :=
  match count with
  | 0 => 4
  | S count' =>
      unit_coefficients_from_time (S start) count' variable +
      EqBool.eqbTime (size (enc start)) (size (enc variable)) + 26
  end.

#[global] Instance term_unit_coefficients_from :
  computableTime' unit_coefficients_from
    (fun start _ =>
      (5, fun count _ =>
        (5, fun variable _ =>
          (unit_coefficients_from_time start count variable, tt)))).
Proof.
  unfold unit_coefficients_from.
  extract.
  solverec.
  all: cbn [unit_coefficients_from_time].
  all: try reflexivity.
Qed.

Definition unit_coefficients_time
    (num_variables variable : nat) : nat :=
  unit_coefficients_from_time 0 num_variables variable + 11.

#[global] Instance term_unit_coefficients :
  computableTime' unit_coefficients
    (fun num_variables _ =>
      (5, fun variable _ =>
        (unit_coefficients_time num_variables variable, tt))).
Proof.
  unfold unit_coefficients.
  extract.
  solverec.
  unfold unit_coefficients_time.
  reflexivity.
Qed.

Definition pin_observation_time
    (num_variables variable weight target : nat) : nat :=
  unit_coefficients_time num_variables variable + 110.

#[global] Instance term_pin_observation :
  computableTime' pin_observation
    (fun num_variables _ =>
      (5, fun variable _ =>
        (5, fun weight _ =>
          (5, fun target _ =>
            (pin_observation_time
              num_variables variable weight target, tt))))).
Proof.
  unfold pin_observation.
  extract.
  solverec.
  unfold pin_observation_time.
  reflexivity.
Qed.

Fixpoint variable_occurs_in_clause_time
    (variable : nat) (clause : list (bool * nat)) : nat :=
  match clause with
  | [] => 4
  | literal :: rest =>
      variable_occurs_in_clause_time variable rest +
      EqBool.eqbTime
        (size (enc (snd literal))) (size (enc variable)) + 26
  end.

#[global] Instance term_variable_occurs_in_clause :
  computableTime' variable_occurs_in_clause
    (fun variable _ =>
      (5, fun clause _ =>
        (variable_occurs_in_clause_time variable clause, tt))).
Proof.
  unfold variable_occurs_in_clause, literal_variable.
  extract.
  solverec.
  all: cbn [variable_occurs_in_clause_time].
  all: lia.
Qed.

Fixpoint variable_occurrence_count_time
    (variable : nat) (formula : list (list (bool * nat))) : nat :=
  match formula with
  | [] => 4
  | clause :: rest =>
      variable_occurs_in_clause_time variable clause +
      variable_occurrence_count_time variable rest +
      if variable_occurs_in_clause variable clause then 20 else 19
  end.

#[global] Instance term_variable_occurrence_count :
  computableTime' variable_occurrence_count
    (fun variable _ =>
      (5, fun formula _ =>
        (variable_occurrence_count_time variable formula, tt))).
Proof.
  unfold variable_occurrence_count.
  extract.
  solverec.
  all: cbn [variable_occurrence_count_time].
  all: try rewrite H0.
  all: lia.
Qed.

Fixpoint maximum_occurrence_time
    (num_variables : nat) (formula : list (list (bool * nat))) : nat :=
  match num_variables with
  | 0 => 4
  | S num_variables' =>
      maximum_occurrence_time num_variables' formula +
      variable_occurrence_count_time num_variables' formula + c__max1 +
      max_time
        (variable_occurrence_count num_variables' formula)
        (maximum_occurrence num_variables' formula) + 15
  end.

#[global] Instance term_maximum_occurrence :
  computableTime' maximum_occurrence
    (fun num_variables _ =>
      (5, fun formula _ =>
        (maximum_occurrence_time num_variables formula, tt))).
Proof.
  unfold maximum_occurrence.
  extract.
  solverec.
  all: cbn [maximum_occurrence_time].
  all: try reflexivity.
Qed.

Definition pin_weight_time
    (formula : list (list (bool * nat))) : nat :=
  source_num_variables_time formula +
  maximum_occurrence_time (source_num_variables formula) formula + 7.

#[global] Instance term_pin_weight :
  computableTime' pin_weight
    (fun formula _ => (pin_weight_time formula, tt)).
Proof.
  unfold pin_weight.
  extract.
  solverec.
  unfold pin_weight_time.
  reflexivity.
Qed.

Definition pinning_observations_for_variable_time
    (num_variables weight variable : nat) : nat :=
  pin_observation_time num_variables variable weight 1 +
  pin_observation_time num_variables variable weight 0 + 36.

#[global] Instance term_pinning_observations_for_variable :
  computableTime' pinning_observations_for_variable
    (fun num_variables _ =>
      (5, fun weight _ =>
        (5, fun variable _ =>
          (pinning_observations_for_variable_time
            num_variables weight variable, tt)))).
Proof.
  unfold pinning_observations_for_variable.
  extract.
  solverec.
  unfold pinning_observations_for_variable_time.
  reflexivity.
Qed.

Fixpoint all_pinning_observations_from_time
    (num_variables weight start count : nat) : nat :=
  match count with
  | 0 => 4
  | S count' =>
      all_pinning_observations_from_time
        num_variables weight (S start) count' +
      pinning_observations_for_variable_time
        num_variables weight start +
      3 * c__app + 28
  end.

#[global] Instance term_all_pinning_observations_from :
  computableTime' all_pinning_observations_from
    (fun num_variables _ =>
      (5, fun weight _ =>
        (1, fun start _ =>
          (1, fun count _ =>
            (all_pinning_observations_from_time
              num_variables weight start count, tt))))).
Proof.
  unfold all_pinning_observations_from.
  extract.
  solverec.
  all: cbn [all_pinning_observations_from_time].
  all: lia.
Qed.

Definition all_pinning_observations_time
    (num_variables weight : nat) : nat :=
  all_pinning_observations_from_time
    num_variables weight 0 num_variables + 8.

#[global] Instance term_all_pinning_observations :
  computableTime' all_pinning_observations
    (fun num_variables _ =>
      (5, fun weight _ =>
        (all_pinning_observations_time num_variables weight, tt))).
Proof.
  unfold all_pinning_observations.
  extract.
  solverec.
  unfold all_pinning_observations_time.
  reflexivity.
Qed.

Fixpoint clause_observations
    (num_variables : nat) (formula : list (list (bool * nat))) :
    list affine_observation :=
  match formula with
  | [] => []
  | clause :: rest =>
      clause_observation num_variables clause ::
      clause_observations num_variables rest
  end.

Lemma clause_observations_map num_variables formula :
  clause_observations num_variables formula =
  map (clause_observation num_variables) formula.
Proof.
  induction formula as [|clause rest IH]; cbn.
  - reflexivity.
  - rewrite IH.
    reflexivity.
Qed.

Fixpoint clause_observations_time
    (num_variables : nat) (formula : list (list (bool * nat))) : nat :=
  match formula with
  | [] => 4
  | clause :: rest =>
      clause_observations_time num_variables rest +
      clause_observation_time num_variables clause + 18
  end.

#[global] Instance term_clause_observations :
  computableTime' clause_observations
    (fun num_variables _ =>
      (5, fun formula _ =>
        (clause_observations_time num_variables formula, tt))).
Proof.
  unfold clause_observations.
  extract.
  solverec.
  all: cbn [clause_observations_time].
  all: lia.
Qed.

Definition compile_valid_timed
    (formula : list (list (bool * nat))) : signed_regression_instance :=
  let num_variables := source_num_variables formula in
  let weight := pin_weight formula in
  {| instance_num_variables := num_variables;
     instance_observations :=
       all_pinning_observations num_variables weight ++
       clause_observations num_variables formula;
     instance_threshold :=
       signed_of_difference
         (weight * num_variables)
         (length formula) |}.

Lemma compile_valid_timed_eq formula :
  compile_valid_timed formula = compile_valid formula.
Proof.
  unfold compile_valid_timed, compile_valid.
  rewrite clause_observations_map.
  reflexivity.
Qed.

Definition compile_timed
    (formula : list (list (bool * nat))) : signed_regression_instance :=
  if kCNF_decb 3 formula
  then compile_valid_timed formula
  else rejecting_instance.

Lemma compile_timed_eq formula :
  compile_timed formula = compile formula.
Proof.
  unfold compile_timed, compile.
  destruct (kCNF_decb 3 formula).
  - apply compile_valid_timed_eq.
  - reflexivity.
Qed.

Definition compile_valid_timed_time
    (formula : list (list (bool * nat))) : nat :=
  c__length * length formula + c__length +
  4 * source_num_variables_time formula +
  2 * pin_weight_time formula + c__mult1 +
  mult_time (pin_weight formula) (source_num_variables formula) +
  signed_of_difference_time
    (pin_weight formula * source_num_variables formula)
    (length formula) +
  clause_observations_time (source_num_variables formula) formula +
  all_pinning_observations_time
    (source_num_variables formula) (pin_weight formula) +
  length
    (all_pinning_observations
      (source_num_variables formula) (pin_weight formula)) * c__app +
  c__app + 119.

#[global] Instance term_compile_valid_timed :
  computableTime' compile_valid_timed
    (fun formula _ => (compile_valid_timed_time formula, tt)).
Proof.
  unfold compile_valid_timed.
  extract.
  solverec.
  unfold compile_valid_timed_time.
  reflexivity.
Qed.

Definition compile_timed_time
    (formula : list (list (bool * nat))) : nat :=
  if kCNF_decb 3 formula
  then kCNF_decb_time 3 formula + compile_valid_timed_time formula + 8
  else kCNF_decb_time 3 formula + 8.

#[global] Instance term_compile_timed :
  computableTime' compile_timed
    (fun formula _ => (compile_timed_time formula, tt)).
Proof.
  unfold compile_timed.
  extract.
  solverec.
  all: unfold compile_timed_time.
  all: rewrite H.
  all: reflexivity.
Qed.

Lemma nat_eqb_time_bound B a b :
  a <= B ->
  b <= B ->
  EqBool.eqbTime (size (enc a)) (size (enc b)) <=
  4 * (B + 1) * EqBool.c__eqbComp nat.
Proof.
  intros Ha Hb.
  eapply Nat.le_trans.
  - apply EqBool.eqbTime_le_l.
  - rewrite size_nat_enc.
  unfold c__natsizeS, c__natsizeO.
  nia.
Qed.

Lemma max_time_bound B a b :
  a <= B ->
  b <= B ->
  max_time a b <= 15 * (B + 1).
Proof.
  intros Ha Hb.
  unfold max_time, c__max2.
  pose proof (Nat.le_min_l a b).
  nia.
Qed.

Lemma add_time_bound B a :
  a <= B ->
  add_time a <= 11 * (B + 1).
Proof.
  intros Ha.
  unfold add_time, c__add.
  nia.
Qed.

Lemma sub_time_bound B a b :
  a <= B ->
  b <= B ->
  sub_time a b <= 14 * (B + 1).
Proof.
  intros Ha Hb.
  unfold sub_time, c__sub.
  pose proof (Nat.le_min_l a b).
  nia.
Qed.

Lemma leb_time_bound B a b :
  a <= B ->
  b <= B ->
  leb_time a b <= 14 * (B + 1).
Proof.
  intros Ha Hb.
  unfold leb_time, c__leb.
  pose proof (Nat.le_min_l a b).
  nia.
Qed.

Lemma mult_time_bound B a b :
  a <= B ->
  b <= B ->
  mult_time a b <= 26 * (B + 1) * (B + 1).
Proof.
  intros Ha Hb.
  unfold mult_time, c__mult, c__add, c__add1.
  nia.
Qed.

Definition signed_magnitude (z : signed_integer) : nat :=
  match z with
  | Nonnegative n => n
  | Negative n => S n
  end.

Lemma literal_coefficient_magnitude literal :
  signed_magnitude (literal_coefficient literal) = 1.
Proof.
  destruct literal as [sign variable].
  unfold literal_coefficient, signed_magnitude.
  cbn.
  destruct sign; reflexivity.
Qed.

Lemma signed_add_magnitude_le x y :
  signed_magnitude (signed_add x y) <=
  signed_magnitude x + signed_magnitude y.
Proof.
  destruct x as [a|a], y as [b|b];
    unfold signed_add, signed_magnitude, signed_of_difference;
    cbn.
  - lia.
  - destruct (S b <=? a) eqn:Hle.
    + apply Nat.leb_le in Hle.
      lia.
    + apply Nat.leb_gt in Hle.
      cbn.
      change (S (S b - a - 1) <= a + S b).
      pose proof (Nat.le_sub_l (S b) a).
      pose proof (Nat.le_sub_l (S b - a) 1).
      lia.
  - destruct (S a <=? b) eqn:Hle.
    + apply Nat.leb_le in Hle.
      lia.
    + apply Nat.leb_gt in Hle.
      cbn.
      change (S (S a - b - 1) <= S a + b).
      pose proof (Nat.le_sub_l (S a) b).
      pose proof (Nat.le_sub_l (S a - b) 1).
      lia.
  - lia.
Qed.

Lemma coefficient_for_variable_magnitude_le variable clause :
  signed_magnitude (coefficient_for_variable variable clause) <=
  length clause.
Proof.
  induction clause as [|literal rest IH].
  - cbn [coefficient_for_variable signed_zero signed_magnitude].
    lia.
  - cbn [coefficient_for_variable].
    destruct (Nat.eqb (literal_variable literal) variable).
    + eapply Nat.le_trans.
      * apply signed_add_magnitude_le.
      * rewrite literal_coefficient_magnitude.
        cbn.
        lia.
    + cbn.
      lia.
Qed.

Lemma signed_of_difference_time_bound B a b :
  a <= B ->
  b <= B ->
  signed_of_difference_time a b <= 80 * (B + 1).
Proof.
  intros Ha Hb.
  unfold signed_of_difference_time.
  destruct (b <=? a) eqn:Hle.
  - pose proof (@leb_time_bound B b a Hb Ha).
    pose proof (@sub_time_bound B a b Ha Hb).
    unfold c__leb2, c__sub1.
    nia.
  - pose proof (@leb_time_bound B b a Hb Ha).
    pose proof (@sub_time_bound B b a Hb Ha).
    assert (Hsub : b - a <= B) by lia.
    assert (Hone : 1 <= B).
    {
      apply Nat.leb_gt in Hle.
      lia.
    }
    pose proof (@sub_time_bound B (b - a) 1 Hsub Hone).
    unfold c__leb2, c__sub1.
    nia.
Qed.

Lemma signed_add_time_bound B x y :
  signed_magnitude x <= B ->
  signed_magnitude y <= B ->
  signed_add_time x y <= 100 * (B + 1).
Proof.
  destruct x as [a|a], y as [b|b]; cbn [signed_magnitude];
    intros Ha Hb; unfold signed_add_time.
  - pose proof (@add_time_bound B a Ha).
    unfold c__add1.
    nia.
  - pose proof (@signed_of_difference_time_bound B a (S b) Ha Hb).
    cbn [signed_add_time].
    replace (1 + b) with (S b) by lia.
    nia.
  - pose proof (@signed_of_difference_time_bound B b (S a) Hb Ha).
    cbn [signed_add_time].
    replace (1 + a) with (S a) by lia.
    nia.
  - pose proof (@add_time_bound B a) as Hadd.
    assert (a <= B) by lia.
    specialize (Hadd H).
    unfold c__add1.
    nia.
Qed.

Definition compiler_cost_constant : nat :=
  1000 *
    (EqBool.c__eqbComp nat + 1) *
    (c__app + 1).

Definition compiler_input_bound
    (formula : list (list (bool * nat))) : nat :=
  size (enc formula) + 1.

Lemma compiler_cost_constant_positive :
  0 < compiler_cost_constant.
Proof.
  unfold compiler_cost_constant.
  apply Nat.mul_pos.
  split.
  - apply Nat.mul_pos.
    lia.
  - lia.
Qed.

Lemma compiler_cost_constant_at_least :
  1000 <= compiler_cost_constant.
Proof.
  unfold compiler_cost_constant.
  replace 1000 with (1000 * 1 * 1) by lia.
  apply Nat.mul_le_mono.
  - apply Nat.mul_le_mono; lia.
  - lia.
Qed.

Lemma max_time_bound_l B a b :
  a <= B ->
  max_time a b <= 15 * (B + 1).
Proof.
  intros Ha.
  unfold max_time, c__max2.
  pose proof (Nat.le_min_l a b).
  nia.
Qed.

Lemma kcnf_three_clause_length formula clause :
  kCNF 3 formula ->
  In clause formula ->
  length clause = 3.
Proof.
  intros Hthree Hin.
  exact ((proj1 (kCNF_clause_length 3 formula)) Hthree clause Hin).
Qed.

Lemma kcnf_three_literal_bound formula clause literal :
  kCNF 3 formula ->
  In clause formula ->
  In literal clause ->
  snd literal <= compiler_input_bound formula.
Proof.
  intros Hthree Hclause Hliteral.
  destruct literal as [sign variable].
  cbn.
  assert (Hlt :
    variable < source_num_variables formula).
  {
    eapply source_variable_lt_num_variables; eassumption.
  }
  pose proof (source_num_variables_le_size_succ formula).
  unfold compiler_input_bound.
  lia.
Qed.

Lemma max_clause_variable_time_three_bound B clause :
  length clause = 3 ->
  (forall literal, In literal clause -> snd literal <= B) ->
  max_clause_variable_time clause <=
  compiler_cost_constant * (B + 1).
Proof.
  intros Hlength Hvariables.
  destruct clause as [|l0 [|l1 [|l2 [|l3 rest]]]];
    cbn in Hlength; try discriminate.
  destruct l0 as [s0 v0], l1 as [s1 v1], l2 as [s2 v2].
  assert (Hv0 : v0 <= B).
  {
    apply (Hvariables (s0, v0)).
    cbn.
    tauto.
  }
  assert (Hv1 : v1 <= B).
  {
    apply (Hvariables (s1, v1)).
    cbn.
    tauto.
  }
  assert (Hv2 : v2 <= B).
  {
    apply (Hvariables (s2, v2)).
    cbn.
    tauto.
  }
  cbn
    [max_clause_variable_time max_clause_variable
     max_literal_variable literal_variable].
  pose proof (@max_time_bound_l B v2 0 Hv2).
  pose proof
    (@max_time_bound_l B v1 (Nat.max v2 0) Hv1).
  pose proof
    (@max_time_bound_l
      B v0 (Nat.max v1 (Nat.max v2 0)) Hv0).
  pose proof compiler_cost_constant_at_least.
  unfold c__max1.
  cbn [max_literal_variable literal_variable fst snd].
  eapply Nat.le_trans with (m := 200 * (B + 1)).
  - nia.
  - apply Nat.mul_le_mono_r.
    lia.
Qed.

Lemma compiler_cost_times_mono n :
  1000 * n <= compiler_cost_constant * n.
Proof.
  apply Nat.mul_le_mono_r.
  apply compiler_cost_constant_at_least.
Qed.

Lemma compiler_base_cost_le :
  1000 * (EqBool.c__eqbComp nat + 1) <=
  compiler_cost_constant.
Proof.
  unfold compiler_cost_constant.
  rewrite <- Nat.mul_1_r at 1.
  apply Nat.mul_le_mono_l.
  lia.
Qed.

Lemma max_cnf_variable_time_three_bound B formula :
  (forall clause, In clause formula -> length clause = 3) ->
  (forall clause literal,
      In clause formula ->
      In literal clause ->
      snd literal <= B) ->
  max_cnf_variable_time formula <=
  2 * compiler_cost_constant * (length formula + 1) * (B + 1).
Proof.
  intros Hlength Hvariables.
  remember compiler_cost_constant as K eqn:HK.
  change
    (max_cnf_variable_time formula <=
      2 * K * (length formula + 1) * (B + 1)).
  induction formula as [|clause rest IH].
  - cbn [max_cnf_variable_time].
    pose proof compiler_cost_constant_at_least.
    rewrite <- HK in H.
    assert (Hscale :
      K <= 2 * K * (0 + 1) * (B + 1)).
    {
      rewrite Nat.mul_1_r.
      eapply Nat.le_trans with
        (m := 2 * K).
      - pose proof
          (Nat.mul_le_mono_r 1 2 K (ltac:(lia))) as Hdouble.
        rewrite Nat.mul_1_l in Hdouble.
        exact Hdouble.
      - pose proof
          (Nat.mul_le_mono_l 1 (B + 1) (2 * K)
            (ltac:(lia))) as Hscale0.
        rewrite Nat.mul_1_r in Hscale0.
        exact Hscale0.
    }
    lia.
  - assert (Hclause_length : length clause = 3).
    {
      apply Hlength.
      left.
      reflexivity.
    }
    assert (Hclause_variables :
      forall literal,
        In literal clause -> snd literal <= B).
    {
      intros literal Hliteral.
      eapply Hvariables.
      - left.
        reflexivity.
      - exact Hliteral.
    }
    specialize (IH
      (fun clause0 Hclause =>
        Hlength clause0 (or_intror Hclause))
      (fun clause0 literal Hclause Hliteral =>
        Hvariables clause0 literal
          (or_intror Hclause) Hliteral)).
    pose proof
      (@max_clause_variable_time_three_bound
        B clause Hclause_length Hclause_variables) as Hclause_time.
    rewrite <- HK in Hclause_time.
    assert (Hmax_clause :
      max_clause_variable clause <= B).
    {
      destruct clause as [|l0 [|l1 [|l2 [|l3 tail]]]];
        cbn in Hclause_length; try discriminate.
      destruct l0 as [s0 v0], l1 as [s1 v1], l2 as [s2 v2].
      cbn [max_clause_variable max_literal_variable literal_variable].
      apply Nat.max_lub.
      - apply Hclause_variables.
        cbn.
        tauto.
      - apply Nat.max_lub.
        + apply Hclause_variables.
          cbn.
          tauto.
        + apply Nat.max_lub.
          * apply Hclause_variables.
            cbn.
            tauto.
          * lia.
    }
    pose proof
      (@max_time_bound_l
        B (max_clause_variable clause)
        (max_cnf_variable rest) Hmax_clause) as Hmax_time.
    pose proof (compiler_cost_times_mono (B + 1)) as Hcost_scale.
    rewrite <- HK in Hcost_scale.
    cbn [max_cnf_variable_time].
    replace
      (2 * K *
        (length (clause :: rest) + 1) * (B + 1))
      with
      (2 * K * (length rest + 1) * (B + 1) +
       2 * K * (B + 1)) by
      (cbn; ring).
    unfold c__max1.
    nia.
Qed.

Lemma cnf_has_variables_time_three_bound formula :
  (forall clause, In clause formula -> length clause = 3) ->
  cnf_has_variables_time formula <=
  compiler_cost_constant * (length formula + 1).
Proof.
  intros Hlength.
  induction formula as [|clause rest IH].
  - cbn [cnf_has_variables_time].
    pose proof compiler_cost_constant_at_least.
    lia.
  - assert (Hclause_length : length clause = 3).
    {
      apply Hlength.
      left.
      reflexivity.
    }
    specialize (IH
      (fun clause0 Hclause =>
        Hlength clause0 (or_intror Hclause))).
    cbn [cnf_has_variables_time].
    rewrite Hclause_length.
    eapply Nat.le_trans with
      (m :=
        compiler_cost_constant * (length rest + 1) +
        compiler_cost_constant).
    + pose proof compiler_base_cost_le as Hbase.
      pose proof
        (@nat_eqb_time_bound 3 3 0
          (ltac:(lia)) (ltac:(lia))) as Heqb.
      unfold c__length.
      nia.
    + replace
        (compiler_cost_constant *
          (length (clause :: rest) + 1))
        with
        (compiler_cost_constant * (length rest + 1) +
         compiler_cost_constant) by (cbn; ring).
      lia.
Qed.

Lemma coefficient_for_variable_time_three_bound N variable clause :
  length clause = 3 ->
  variable <= N ->
  (forall literal, In literal clause -> snd literal <= N) ->
  coefficient_for_variable_time variable clause <=
  4 * compiler_cost_constant * (N + 1).
Proof.
  intros Hlength Hvariable Hvariables.
  destruct clause as [|l0 [|l1 [|l2 [|l3 rest]]]];
    cbn in Hlength; try discriminate.
  destruct l0 as [s0 v0], l1 as [s1 v1], l2 as [s2 v2].
  assert (Hv0 : v0 <= N).
  {
    apply (Hvariables (s0, v0)).
    cbn.
    tauto.
  }
  assert (Hv1 : v1 <= N).
  {
    apply (Hvariables (s1, v1)).
    cbn.
    tauto.
  }
  assert (Hv2 : v2 <= N).
  {
    apply (Hvariables (s2, v2)).
    cbn.
    tauto.
  }
  pose proof
    (@nat_eqb_time_bound N v0 variable Hv0 Hvariable) as Heqb0.
  pose proof
    (@nat_eqb_time_bound N v1 variable Hv1 Hvariable) as Heqb1.
  pose proof
    (@nat_eqb_time_bound N v2 variable Hv2 Hvariable) as Heqb2.
  pose proof
    (@signed_add_time_bound 3
      (literal_coefficient (s2, v2))
      (coefficient_for_variable variable [])
      (ltac:(rewrite literal_coefficient_magnitude; lia))
      (ltac:(pose proof
        (coefficient_for_variable_magnitude_le variable []);
        cbn in *; lia))) as Hadd2.
  pose proof
    (@signed_add_time_bound 3
      (literal_coefficient (s1, v1))
      (coefficient_for_variable variable [(s2, v2)])
      (ltac:(rewrite literal_coefficient_magnitude; lia))
      (ltac:(pose proof
        (coefficient_for_variable_magnitude_le
          variable [(s2, v2)]);
        cbn in *; lia))) as Hadd1.
  pose proof
    (@signed_add_time_bound 3
      (literal_coefficient (s0, v0))
      (coefficient_for_variable variable [(s1, v1); (s2, v2)])
      (ltac:(rewrite literal_coefficient_magnitude; lia))
      (ltac:(pose proof
        (coefficient_for_variable_magnitude_le
          variable [(s1, v1); (s2, v2)]);
        cbn in *; lia))) as Hadd0.
  pose proof compiler_base_cost_le as Hbase.
  pose proof compiler_cost_constant_at_least as Hleast.
  cbn [coefficient_for_variable_time fst snd literal_variable].
  destruct (v2 =? variable), (v1 =? variable), (v0 =? variable);
    nia.
Qed.

Lemma negative_literal_count_time_bound clause :
  negative_literal_count_time clause <= 30 * (length clause + 1).
Proof.
  induction clause as [|literal rest IH].
  - cbn [negative_literal_count_time].
    lia.
  - cbn [negative_literal_count_time].
    destruct (negb (fst literal)); cbn; lia.
Qed.

Lemma dense_clause_coefficients_from_time_three_bound
    N start count clause :
  length clause = 3 ->
  (forall literal, In literal clause -> snd literal <= N) ->
  start + count <= N ->
  dense_clause_coefficients_from_time start count clause <=
  6 * compiler_cost_constant * (count + 1) * (N + 1).
Proof.
  intros Hlength Hvariables.
  remember compiler_cost_constant as K eqn:HK.
  revert start.
  induction count as [|count IH]; intros start Hrange.
  - cbn [dense_clause_coefficients_from_time].
    pose proof compiler_cost_constant_at_least as Hleast.
    rewrite <- HK in Hleast.
    nia.
  - assert (Hstart : start <= N) by lia.
    specialize (IH (S start) (ltac:(lia))).
    pose proof
      (@coefficient_for_variable_time_three_bound
        N start clause Hlength Hstart Hvariables) as Hcoefficient.
    rewrite <- HK in Hcoefficient.
    pose proof compiler_cost_constant_at_least as Hleast.
    rewrite <- HK in Hleast.
    cbn [dense_clause_coefficients_from_time].
    nia.
Qed.

Lemma dense_clause_coefficients_time_three_bound
    N num_variables clause :
  length clause = 3 ->
  (forall literal, In literal clause -> snd literal <= N) ->
  num_variables <= N ->
  dense_clause_coefficients_time num_variables clause <=
  7 * compiler_cost_constant * (N + 1) * (N + 1).
Proof.
  intros Hlength Hvariables Hnum.
  pose proof
    (@dense_clause_coefficients_from_time_three_bound
      N 0 num_variables clause Hlength Hvariables (ltac:(lia)))
    as Hdense.
  pose proof compiler_cost_constant_at_least as Hleast.
  unfold dense_clause_coefficients_time.
  nia.
Qed.

Lemma clause_observation_time_three_bound N num_variables clause :
  length clause = 3 ->
  (forall literal, In literal clause -> snd literal <= N) ->
  num_variables <= N ->
  clause_observation_time num_variables clause <=
  8 * compiler_cost_constant * (N + 1) * (N + 1).
Proof.
  intros Hlength Hvariables Hnum.
  pose proof
    (@dense_clause_coefficients_time_three_bound
      N num_variables clause Hlength Hvariables Hnum) as Hdense.
  pose proof (negative_literal_count_time_bound clause) as Hnegative.
  pose proof compiler_cost_constant_at_least as Hleast.
  unfold clause_observation_time, clause_target_time.
  nia.
Qed.

Lemma clause_observations_time_three_bound N num_variables formula :
  (forall clause, In clause formula -> length clause = 3) ->
  (forall clause literal,
      In clause formula ->
      In literal clause ->
      snd literal <= N) ->
  num_variables <= N ->
  clause_observations_time num_variables formula <=
  10 * compiler_cost_constant * (length formula + 1) *
    ((N + 1) * (N + 1)).
Proof.
  intros Hlength Hvariables Hnum.
  remember compiler_cost_constant as K eqn:HK.
  remember ((N + 1) * (N + 1)) as Q eqn:HQ.
  assert (HQpositive : 1 <= Q).
  {
    subst Q.
    nia.
  }
  induction formula as [|clause rest IH].
  - cbn [clause_observations_time].
    pose proof compiler_cost_constant_at_least as Hleast.
    rewrite <- HK in Hleast.
    nia.
  - assert (Hclause_length : length clause = 3).
    {
      apply Hlength.
      left.
      reflexivity.
    }
    assert (Hclause_variables :
      forall literal, In literal clause -> snd literal <= N).
    {
      intros literal Hliteral.
      eapply Hvariables.
      - left.
        reflexivity.
      - exact Hliteral.
    }
    specialize (IH
      (fun clause0 Hclause =>
        Hlength clause0 (or_intror Hclause))
      (fun clause0 literal Hclause Hliteral =>
        Hvariables clause0 literal
          (or_intror Hclause) Hliteral)).
    pose proof
      (@clause_observation_time_three_bound
        N num_variables clause
        Hclause_length Hclause_variables Hnum) as Hclause.
    rewrite <- HK in Hclause.
    replace
      (8 * K * (N + 1) * (N + 1))
      with
      (8 * K * ((N + 1) * (N + 1)))
      in Hclause by ring.
    rewrite <- HQ in Hclause.
    pose proof compiler_cost_constant_at_least as Hleast.
    rewrite <- HK in Hleast.
    cbn [clause_observations_time].
    replace
      (10 * K * (length (clause :: rest) + 1) * Q)
      with
      (10 * K * (length rest + 1) * Q + 10 * K * Q)
      by (cbn; ring).
    replace
      (clause_observations_time num_variables rest +
       clause_observation_time num_variables clause + 18)
      with
      (clause_observations_time num_variables rest +
       (clause_observation_time num_variables clause + 18))
      by ring.
    apply Nat.add_le_mono.
    + exact IH.
    + eapply Nat.le_trans with (m := 8 * K * Q + 18).
      * apply Nat.add_le_mono_r.
        exact Hclause.
      * replace (10 * K * Q) with (8 * K * Q + 2 * K * Q)
          by ring.
        apply Nat.add_le_mono_l.
        nia.
Qed.

Lemma compiler_app_cost_le :
  c__app <= compiler_cost_constant.
Proof.
  unfold compiler_cost_constant.
  replace c__app with (1 * 1 * c__app) by ring.
  apply Nat.mul_le_mono.
  - apply Nat.mul_le_mono; lia.
  - lia.
Qed.

Lemma unit_coefficients_from_time_bound N start count variable :
  start + count <= N ->
  variable <= N ->
  unit_coefficients_from_time start count variable <=
  5 * compiler_cost_constant * (count + 1) * (N + 1).
Proof.
  intros Hrange Hvariable.
  remember compiler_cost_constant as K eqn:HK.
  revert start Hrange.
  induction count as [|count IH]; intros start Hrange.
  - cbn [unit_coefficients_from_time].
    pose proof compiler_cost_constant_at_least as Hleast.
    rewrite <- HK in Hleast.
    nia.
  - assert (Hstart : start <= N) by lia.
    specialize (IH (S start) (ltac:(lia))).
    pose proof
      (@nat_eqb_time_bound N start variable Hstart Hvariable) as Heqb.
    pose proof compiler_base_cost_le as Hbase.
    rewrite <- HK in Hbase.
    pose proof compiler_cost_constant_at_least as Hleast.
    rewrite <- HK in Hleast.
    cbn [unit_coefficients_from_time].
    nia.
Qed.

Lemma unit_coefficients_time_bound N num_variables variable :
  num_variables <= N ->
  variable <= N ->
  unit_coefficients_time num_variables variable <=
  6 * compiler_cost_constant * (N + 1) * (N + 1).
Proof.
  intros Hnum Hvariable.
  pose proof
    (@unit_coefficients_from_time_bound
      N 0 num_variables variable (ltac:(lia)) Hvariable) as Hunit.
  pose proof compiler_cost_constant_at_least.
  unfold unit_coefficients_time.
  nia.
Qed.

Lemma pinning_observations_for_variable_time_bound
    N num_variables weight variable :
  num_variables <= N ->
  variable <= N ->
  pinning_observations_for_variable_time
      num_variables weight variable <=
  15 * compiler_cost_constant * (N + 1) * (N + 1).
Proof.
  intros Hnum Hvariable.
  pose proof
    (@unit_coefficients_time_bound
      N num_variables variable Hnum Hvariable) as Hunit.
  pose proof compiler_cost_constant_at_least.
  unfold
    pinning_observations_for_variable_time,
    pin_observation_time.
  nia.
Qed.

Lemma all_pinning_observations_from_time_bound
    N num_variables weight start count :
  num_variables <= N ->
  start + count <= num_variables ->
  all_pinning_observations_from_time
      num_variables weight start count <=
  16 * compiler_cost_constant * (count + 1) *
    (N + 1) * (N + 1).
Proof.
  intros Hnum.
  remember compiler_cost_constant as K eqn:HK.
  revert start.
  induction count as [|count IH]; intros start Hrange.
  - cbn [all_pinning_observations_from_time].
    pose proof compiler_cost_constant_at_least as Hleast.
    rewrite <- HK in Hleast.
    nia.
  - assert (Hstart : start <= N) by lia.
    specialize (IH (S start) (ltac:(lia))).
    pose proof
      (@pinning_observations_for_variable_time_bound
        N num_variables weight start Hnum Hstart) as Hpin.
    rewrite <- HK in Hpin.
    pose proof compiler_app_cost_le as Happ.
    rewrite <- HK in Happ.
    pose proof compiler_cost_constant_at_least as Hleast.
    rewrite <- HK in Hleast.
    cbn [all_pinning_observations_from_time].
    nia.
Qed.

Lemma all_pinning_observations_time_bound N num_variables weight :
  num_variables <= N ->
  all_pinning_observations_time num_variables weight <=
  17 * compiler_cost_constant * (N + 1) *
    (N + 1) * (N + 1).
Proof.
  intros Hnum.
  pose proof
    (@all_pinning_observations_from_time_bound
      N num_variables weight 0 num_variables
      Hnum (ltac:(lia))) as Hall.
  pose proof compiler_cost_constant_at_least.
  unfold all_pinning_observations_time.
  nia.
Qed.

Lemma variable_occurs_in_clause_time_three_bound N variable clause :
  length clause = 3 ->
  variable <= N ->
  (forall literal, In literal clause -> snd literal <= N) ->
  variable_occurs_in_clause_time variable clause <=
  2 * compiler_cost_constant * (N + 1).
Proof.
  intros Hlength Hvariable Hvariables.
  destruct clause as [|l0 [|l1 [|l2 [|l3 rest]]]];
    cbn in Hlength; try discriminate.
  destruct l0 as [s0 v0], l1 as [s1 v1], l2 as [s2 v2].
  assert (Hv0 : v0 <= N).
  {
    apply (Hvariables (s0, v0)).
    cbn.
    tauto.
  }
  assert (Hv1 : v1 <= N).
  {
    apply (Hvariables (s1, v1)).
    cbn.
    tauto.
  }
  assert (Hv2 : v2 <= N).
  {
    apply (Hvariables (s2, v2)).
    cbn.
    tauto.
  }
  pose proof
    (@nat_eqb_time_bound N v0 variable Hv0 Hvariable) as Heqb0.
  pose proof
    (@nat_eqb_time_bound N v1 variable Hv1 Hvariable) as Heqb1.
  pose proof
    (@nat_eqb_time_bound N v2 variable Hv2 Hvariable) as Heqb2.
  pose proof compiler_base_cost_le as Hbase.
  pose proof compiler_cost_constant_at_least as Hleast.
  cbn [variable_occurs_in_clause_time fst snd literal_variable].
  nia.
Qed.

Lemma variable_occurrence_count_time_three_bound N variable formula :
  (forall clause, In clause formula -> length clause = 3) ->
  (forall clause literal,
      In clause formula ->
      In literal clause ->
      snd literal <= N) ->
  variable <= N ->
  variable_occurrence_count_time variable formula <=
  3 * compiler_cost_constant * (length formula + 1) * (N + 1).
Proof.
  intros Hlength Hvariables Hvariable.
  remember compiler_cost_constant as K eqn:HK.
  remember (N + 1) as R eqn:HR.
  assert (HRpositive : 1 <= R) by (subst R; lia).
  induction formula as [|clause rest IH].
  - cbn [variable_occurrence_count_time].
    pose proof compiler_cost_constant_at_least as Hleast.
    rewrite <- HK in Hleast.
    nia.
  - assert (Hclause_length : length clause = 3).
    {
      apply Hlength.
      left.
      reflexivity.
    }
    assert (Hclause_variables :
      forall literal, In literal clause -> snd literal <= N).
    {
      intros literal Hliteral.
      eapply Hvariables.
      - left.
        reflexivity.
      - exact Hliteral.
    }
    specialize (IH
      (fun clause0 Hclause =>
        Hlength clause0 (or_intror Hclause))
      (fun clause0 literal Hclause Hliteral =>
        Hvariables clause0 literal
          (or_intror Hclause) Hliteral)).
    pose proof
      (@variable_occurs_in_clause_time_three_bound
        N variable clause
        Hclause_length Hvariable Hclause_variables) as Hoccurs.
    rewrite <- HK, <- HR in Hoccurs.
    pose proof compiler_cost_constant_at_least as Hleast.
    rewrite <- HK in Hleast.
    cbn [variable_occurrence_count_time].
    destruct (variable_occurs_in_clause variable clause); cbn.
    all: assert (HKR : K <= K * R) by (
      rewrite <- Nat.mul_1_r at 1;
      apply Nat.mul_le_mono_l;
      exact HRpositive).
    all:
      eapply Nat.le_trans with
        (m :=
          2 * K * R +
          3 * K * (length rest + 1) * R + 20).
    all: try lia.
    all:
      replace
        (3 * K * (length (clause :: rest) + 1) * R)
        with
        (3 * K * (length rest + 1) * R + 3 * K * R)
        by (cbn; ring).
    all: lia.
Qed.

Lemma maximum_occurrence_time_three_bound N num_variables formula :
  (forall clause, In clause formula -> length clause = 3) ->
  (forall clause literal,
      In clause formula ->
      In literal clause ->
      snd literal <= N) ->
  num_variables <= N ->
  maximum_occurrence_time num_variables formula <=
  5 * compiler_cost_constant * (num_variables + 1) *
    ((length formula + 1) * (N + 1)).
Proof.
  intros Hlength Hvariables Hnum.
  remember compiler_cost_constant as K eqn:HK.
  remember ((length formula + 1) * (N + 1)) as R eqn:HR.
  assert (HRpositive : 1 <= R).
  {
    subst R.
    nia.
  }
  induction num_variables as [|num_variables IH].
  - cbn [maximum_occurrence_time].
    pose proof compiler_cost_constant_at_least as Hleast.
    rewrite <- HK in Hleast.
    nia.
  - assert (Hvariable : num_variables <= N) by lia.
    specialize (IH (ltac:(lia))).
    pose proof
      (@variable_occurrence_count_time_three_bound
        N num_variables formula Hlength Hvariables Hvariable) as Hcount.
    rewrite <- HK in Hcount.
    replace
      (3 * K * (length formula + 1) * (N + 1))
      with
      (3 * K * ((length formula + 1) * (N + 1)))
      in Hcount by ring.
    rewrite <- HR in Hcount.
    pose proof
      (@max_time_bound
        (length formula)
        (variable_occurrence_count num_variables formula)
        (maximum_occurrence num_variables formula)
        (variable_occurrence_count_le_formula_length
          num_variables formula)
        (maximum_occurrence_le_formula_length
          num_variables formula)) as Hmax.
    pose proof compiler_cost_constant_at_least as Hleast.
    rewrite <- HK in Hleast.
    cbn [maximum_occurrence_time].
    replace
      (5 * K * (S num_variables + 1) * R)
      with
      (5 * K * (num_variables + 1) * R + 5 * K * R)
      by ring.
    replace
      (maximum_occurrence_time num_variables formula +
       variable_occurrence_count_time num_variables formula +
       c__max1 +
       max_time
         (variable_occurrence_count num_variables formula)
         (maximum_occurrence num_variables formula) + 15)
      with
      (maximum_occurrence_time num_variables formula +
       (variable_occurrence_count_time num_variables formula +
        c__max1 +
        max_time
          (variable_occurrence_count num_variables formula)
          (maximum_occurrence num_variables formula) + 15))
      by ring.
    apply Nat.add_le_mono.
    + exact IH.
    + unfold c__max1.
      subst R.
      nia.
Qed.

Lemma source_num_variables_time_three_bound N formula :
  (forall clause, In clause formula -> length clause = 3) ->
  (forall clause literal,
      In clause formula ->
      In literal clause ->
      snd literal <= N) ->
  source_num_variables_time formula <=
  4 * compiler_cost_constant *
    ((length formula + 1) * (N + 1)).
Proof.
  intros Hlength Hvariables.
  remember compiler_cost_constant as K eqn:HK.
  remember ((length formula + 1) * (N + 1)) as R eqn:HR.
  assert (HRpositive : 1 <= R).
  {
    subst R.
    nia.
  }
  pose proof
    (@cnf_has_variables_time_three_bound formula Hlength) as Hhas.
  rewrite <- HK in Hhas.
  assert (HhasR :
    cnf_has_variables_time formula <= K * R).
  {
    eapply Nat.le_trans.
    - exact Hhas.
    - rewrite HR.
      apply Nat.mul_le_mono_l.
      rewrite <- Nat.mul_1_r at 1.
      apply Nat.mul_le_mono_l.
      lia.
  }
  pose proof
    (@max_cnf_variable_time_three_bound
      N formula Hlength Hvariables) as Hmax.
  rewrite <- HK in Hmax.
  replace
    (2 * K * (length formula + 1) * (N + 1))
    with
    (2 * K * R)
    in Hmax by (rewrite HR; ring).
  pose proof compiler_cost_constant_at_least as Hleast.
  rewrite <- HK in Hleast.
  assert (HKR : K <= K * R).
  {
    rewrite <- Nat.mul_1_r at 1.
    apply Nat.mul_le_mono_l.
    exact HRpositive.
  }
  unfold source_num_variables_time.
  destruct (cnf_has_variables formula); lia.
Qed.

Lemma pin_weight_time_three_bound N formula :
  (forall clause, In clause formula -> length clause = 3) ->
  (forall clause literal,
      In clause formula ->
      In literal clause ->
      snd literal <= N) ->
  source_num_variables formula <= N ->
  pin_weight_time formula <=
  10 * compiler_cost_constant * (N + 1) *
    ((length formula + 1) * (N + 1)).
Proof.
  intros Hlength Hvariables Hnum.
  remember compiler_cost_constant as K eqn:HK.
  remember ((length formula + 1) * (N + 1)) as R eqn:HR.
  assert (HRpositive : 1 <= R).
  {
    subst R.
    nia.
  }
  pose proof
    (@source_num_variables_time_three_bound
      N formula Hlength Hvariables) as Hsource.
  rewrite <- HK in Hsource.
  rewrite <- HR in Hsource.
  pose proof
    (@maximum_occurrence_time_three_bound
      N (source_num_variables formula) formula
      Hlength Hvariables Hnum) as Hmaximum.
  rewrite <- HK in Hmaximum.
  rewrite <- HR in Hmaximum.
  assert (Hmaximum' :
    maximum_occurrence_time
        (source_num_variables formula) formula <=
    5 * K * (N + 1) * R).
  {
    eapply Nat.le_trans.
    - exact Hmaximum.
    - apply Nat.mul_le_mono_r.
      apply Nat.mul_le_mono_l.
      lia.
  }
  assert (Hsource' :
    source_num_variables_time formula <=
    4 * K * (N + 1) * R).
  {
    eapply Nat.le_trans.
    - exact Hsource.
    - apply Nat.mul_le_mono_r.
      replace (4 * K) with (4 * K * 1) at 1 by ring.
      apply Nat.mul_le_mono_l.
      lia.
  }
  pose proof compiler_cost_constant_at_least as Hleast.
  rewrite <- HK in Hleast.
  assert (HKscale : K <= K * (N + 1) * R).
  {
    eapply Nat.le_trans with (m := K * (N + 1)).
    - rewrite <- Nat.mul_1_r at 1.
      apply Nat.mul_le_mono_l.
      lia.
    - rewrite <- Nat.mul_1_r at 1.
      apply Nat.mul_le_mono_l.
      exact HRpositive.
  }
  unfold pin_weight_time.
  lia.
Qed.

Lemma compile_valid_timed_time_bound formula :
  kCNF 3 formula ->
  compile_valid_timed_time formula <=
  200 * compiler_cost_constant *
    ((compiler_input_bound formula + 1) *
     (compiler_input_bound formula + 1) *
     (compiler_input_bound formula + 1)).
Proof.
  intros Hthree.
  remember (compiler_input_bound formula) as N eqn:HN.
  remember compiler_cost_constant as K eqn:HK.
  remember ((N + 1) * (N + 1) * (N + 1)) as R eqn:HR.
  assert (HNpositive : 1 <= N).
  {
    rewrite HN.
    unfold compiler_input_bound.
    lia.
  }
  assert (HRpositive : 1 <= R).
  {
    subst R.
    nia.
  }
  assert (Hformula : length formula + 1 <= N).
  {
    pose proof (formula_length_le_size formula).
    rewrite HN.
    unfold compiler_input_bound.
    lia.
  }
  assert (Hlength :
    forall clause, In clause formula -> length clause = 3).
  {
    intros clause Hclause.
    eapply kcnf_three_clause_length; eassumption.
  }
  assert (Hvariables :
    forall clause literal,
      In clause formula ->
      In literal clause ->
      snd literal <= N).
  {
    intros clause literal Hclause Hliteral.
    pose proof
      (@kcnf_three_literal_bound
        formula clause literal Hthree Hclause Hliteral) as Hbound.
    rewrite <- HN in Hbound.
    exact Hbound.
  }
  assert (Hnum : source_num_variables formula <= N).
  {
    pose proof (source_num_variables_le_size_succ formula).
    rewrite HN.
    unfold compiler_input_bound.
    lia.
  }
  assert (Hweight : pin_weight formula <= N).
  {
    pose proof (pin_weight_le_size_succ formula).
    rewrite HN.
    unfold compiler_input_bound.
    lia.
  }
  pose proof
    (@source_num_variables_time_three_bound
      N formula Hlength Hvariables) as Hsource.
  rewrite <- HK in Hsource.
  pose proof
    (@pin_weight_time_three_bound
      N formula Hlength Hvariables Hnum) as Hpinweight.
  rewrite <- HK in Hpinweight.
  pose proof
    (@clause_observations_time_three_bound
      N (source_num_variables formula) formula
      Hlength Hvariables Hnum) as Hclauses.
  rewrite <- HK in Hclauses.
  pose proof
    (@all_pinning_observations_time_bound
      N (source_num_variables formula) (pin_weight formula) Hnum) as Hpins.
  rewrite <- HK in Hpins.
  assert (HsourceR :
    source_num_variables_time formula <= 4 * K * R).
  {
    eapply Nat.le_trans.
    - exact Hsource.
    - rewrite HR.
      apply Nat.mul_le_mono_l.
      apply Nat.mul_le_mono_r.
      nia.
  }
  assert (HpinweightR :
    pin_weight_time formula <= 10 * K * R).
  {
    eapply Nat.le_trans.
    - exact Hpinweight.
    - rewrite HR.
      replace
        (10 * K * (N + 1) *
          ((length formula + 1) * (N + 1)))
        with
        (10 * K *
          ((N + 1) * ((length formula + 1) * (N + 1))))
        by ring.
      replace
        (10 * K * ((N + 1) * (N + 1) * (N + 1)))
        with
        (10 * K *
          ((N + 1) * ((N + 1) * (N + 1))))
        by ring.
      apply Nat.mul_le_mono_l.
      apply Nat.mul_le_mono_l.
      apply Nat.mul_le_mono_r.
      lia.
  }
  assert (HclausesR :
    clause_observations_time
        (source_num_variables formula) formula <=
    10 * K * R).
  {
    eapply Nat.le_trans.
    - exact Hclauses.
    - rewrite HR.
      replace
        (10 * K * (length formula + 1) *
          ((N + 1) * (N + 1)))
        with
        (10 * K *
          ((length formula + 1) * ((N + 1) * (N + 1))))
        by ring.
      replace
        (10 * K * ((N + 1) * (N + 1) * (N + 1)))
        with
        (10 * K *
          ((N + 1) * ((N + 1) * (N + 1))))
        by ring.
      apply Nat.mul_le_mono_l.
      apply Nat.mul_le_mono_r.
      lia.
  }
  assert (HpinsR :
    all_pinning_observations_time
        (source_num_variables formula) (pin_weight formula) <=
    17 * K * R).
  {
    eapply Nat.le_trans.
    - exact Hpins.
    - rewrite HR.
      ring_simplify.
      apply Nat.le_refl.
  }
  pose proof
    (@mult_time_bound
      N (pin_weight formula) (source_num_variables formula)
      Hweight Hnum) as Hmult.
  pose proof
    (@signed_of_difference_time_bound
      (N * N)
      (pin_weight formula * source_num_variables formula)
      (length formula)
      (ltac:(apply Nat.mul_le_mono; assumption))
      (ltac:(
        assert (Hlen : length formula <= N) by lia;
        nia))) as Hsigned.
  pose proof compiler_cost_constant_at_least as Hleast.
  rewrite <- HK in Hleast.
  pose proof compiler_app_cost_le as Happ.
  rewrite <- HK in Happ.
  assert (Hsquare_cube :
    (N + 1) * (N + 1) <= R).
  {
    rewrite HR.
    rewrite <- Nat.mul_1_r at 1.
    apply Nat.mul_le_mono_l.
    lia.
  }
  assert (Hproduct_cube : N * N + 1 <= R).
  {
    rewrite HR.
    nia.
  }
  assert (HmultR :
    mult_time
      (pin_weight formula) (source_num_variables formula) <=
    K * R).
  {
    eapply Nat.le_trans.
    - exact Hmult.
    - eapply Nat.le_trans with (m := K * ((N + 1) * (N + 1))).
      + replace
          (26 * (N + 1) * (N + 1))
          with
          (26 * ((N + 1) * (N + 1)))
          by ring.
        apply Nat.mul_le_mono_r.
        lia.
      + apply Nat.mul_le_mono_l.
        exact Hsquare_cube.
  }
  assert (HsignedR :
    signed_of_difference_time
      (pin_weight formula * source_num_variables formula)
      (length formula) <=
    K * R).
  {
    eapply Nat.le_trans.
    - exact Hsigned.
    - eapply Nat.le_trans with (m := K * (N * N + 1)).
      + apply Nat.mul_le_mono_r.
        lia.
      + apply Nat.mul_le_mono_l.
        exact Hproduct_cube.
  }
  assert (HKR : K <= K * R).
  {
    rewrite <- Nat.mul_1_r at 1.
    apply Nat.mul_le_mono_l.
      exact HRpositive.
  }
  assert (HNR : N <= R).
  {
    eapply Nat.le_trans with (m := N * N + 1).
    - eapply Nat.le_trans with (m := N * N).
      + rewrite <- Nat.mul_1_r at 1.
        apply Nat.mul_le_mono_l.
        exact HNpositive.
      + rewrite Nat.add_1_r.
        exact (Nat.le_succ_diag_r (N * N)).
    - exact Hproduct_cube.
  }
  assert (HRKR : R <= K * R).
  {
    rewrite <- Nat.mul_1_l at 1.
    apply Nat.mul_le_mono_r.
    lia.
  }
  assert (HNKR : N <= K * R) by lia.
  replace (4 * K * R) with (4 * (K * R))
    in HsourceR by ring.
  replace (10 * K * R) with (10 * (K * R))
    in HpinweightR by ring.
  replace (10 * K * R) with (10 * (K * R))
    in HclausesR by ring.
  replace (17 * K * R) with (17 * (K * R))
    in HpinsR by ring.
  replace (200 * K * R) with (200 * (K * R)) by ring.
  remember (K * R) as T eqn:HT.
  unfold compile_valid_timed_time.
  rewrite all_pinning_observations_length.
  unfold c__length, c__mult1, c__app.
  lia.
Qed.

Lemma signed_integer_size_bound z :
  size (enc z) <= 5 * (signed_magnitude z + 2).
Proof.
  destruct z as [n|n].
  - change
      (size (L.lam (L.lam (L.app (L.var 1) (enc n)))) <=
       5 * (n + 2)).
    cbn.
    rewrite size_nat_enc.
    unfold c__natsizeS, c__natsizeO.
    nia.
  - change
      (size (L.lam (L.lam (L.app (L.var 0) (enc n)))) <=
       5 * (S n + 2)).
    cbn.
    rewrite size_nat_enc.
    unfold c__natsizeS, c__natsizeO.
    nia.
Qed.

Lemma affine_observation_size_bound B row :
  observation_weight row <= B ->
  length (observation_coefficients row) <= B ->
  (forall coefficient,
      In coefficient (observation_coefficients row) ->
      signed_magnitude coefficient <= B) ->
  signed_magnitude (observation_target row) <= B ->
  size (enc row) <= 100 * (B + 2) * (B + 2).
Proof.
  destruct row as [sign weight coefficients target].
  cbn.
  intros Hweight Hlength Hcoefficients Htarget.
  assert (Hcoefficient_size :
    forall coefficient,
      In coefficient coefficients ->
      size (enc coefficient) <= 5 * (B + 2)).
  {
    intros coefficient Hcoefficient.
    eapply Nat.le_trans.
    - apply signed_integer_size_bound.
    - apply Nat.mul_le_mono_l.
      specialize (Hcoefficients coefficient Hcoefficient).
      lia.
  }
  pose proof
    (@list_size_of_el
      signed_integer encodable_signed_integer_enc
      coefficients (5 * (B + 2)) Hcoefficient_size) as Hlist.
  assert (Hlist' :
    size (enc coefficients) <=
    10 * (B + 2) * (B + 2)).
  {
    unfold c__listsizeCons, c__listsizeNil in Hlist.
    assert (Hitems :
      5 * (B + 2) * length coefficients <=
      5 * (B + 2) * B).
    {
      apply Nat.mul_le_mono_l.
      exact Hlength.
    }
    assert (Hconstructors :
      5 * length coefficients <= 5 * B).
    {
      apply Nat.mul_le_mono_l.
      exact Hlength.
    }
    nia.
  }
  pose proof (signed_integer_size_bound target) as Htarget_size.
  assert (Htarget_size' :
    size (enc target) <= 5 * (B + 2)).
  {
    eapply Nat.le_trans.
    - exact Htarget_size.
    - apply Nat.mul_le_mono_l.
      lia.
  }
  pose proof (size_bool sign) as Hsign.
  change
    (size (enc (sign, (weight, (coefficients, target)))) <=
     100 * (B + 2) * (B + 2)).
  repeat rewrite size_prod.
  cbn [fst snd].
  rewrite size_nat_enc.
  unfold c__natsizeS, c__natsizeO.
  unfold c__sizeBool in Hsign.
  remember ((B + 2) * (B + 2)) as Q eqn:HQ.
  replace (10 * (B + 2) * (B + 2)) with (10 * Q)
    in Hlist' by (rewrite HQ; ring).
  replace (100 * (B + 2) * (B + 2)) with (100 * Q)
    by (rewrite HQ; ring).
  assert (HQpositive : 1 <= Q).
  {
    rewrite HQ.
    nia.
  }
  assert (HbaseQ : B + 2 <= Q).
  {
    rewrite HQ.
    rewrite <- Nat.mul_1_r at 1.
    apply Nat.mul_le_mono_l.
    lia.
  }
  assert (HweightQ : weight <= Q) by lia.
  assert (Hweight_size : weight * 4 + 4 <= 5 * Q).
  {
    assert (Hproduct : weight * 4 <= Q * 4).
    {
      apply Nat.mul_le_mono_r.
      exact HweightQ.
    }
    lia.
  }
  assert (HtargetQ : size (enc target) <= 5 * Q).
  {
    eapply Nat.le_trans.
    - exact Htarget_size'.
    - apply Nat.mul_le_mono_l.
      exact HbaseQ.
  }
  lia.
Qed.

Lemma unit_coefficients_from_magnitude_le_one
    start count variable coefficient :
  In coefficient (unit_coefficients_from start count variable) ->
  signed_magnitude coefficient <= 1.
Proof.
  revert start coefficient.
  induction count as [|count IH];
    intros start coefficient Hin; cbn in Hin.
  - contradiction.
  - destruct Hin as [<-|Hin].
    + destruct (start =? variable); cbn [signed_one signed_zero signed_magnitude];
        lia.
    + eapply (IH (S start)).
      exact Hin.
Qed.

Lemma unit_coefficients_magnitude_le_one
    num_variables variable coefficient :
  In coefficient (unit_coefficients num_variables variable) ->
  signed_magnitude coefficient <= 1.
Proof.
  unfold unit_coefficients.
  apply unit_coefficients_from_magnitude_le_one.
Qed.

Lemma dense_clause_coefficient_magnitude_le
    num_variables clause coefficient :
  In coefficient (dense_clause_coefficients num_variables clause) ->
  signed_magnitude coefficient <= length clause.
Proof.
  rewrite dense_clause_coefficients_map_seq.
  intros Hin.
  apply in_map_iff in Hin.
  destruct Hin as [variable [<- Hin]].
  apply coefficient_for_variable_magnitude_le.
Qed.

Lemma negative_literal_count_le_length clause :
  negative_literal_count clause <= length clause.
Proof.
  induction clause as [|literal rest IH]; cbn [negative_literal_count].
  - lia.
  - destruct (negb (fst literal)); cbn; lia.
Qed.

Lemma pin_observation_size_bound
    B num_variables variable weight target :
  num_variables <= B ->
  weight <= B ->
  target <= B ->
  size
    (enc (pin_observation
      num_variables variable weight target)) <=
  100 * (B + 2) * (B + 2).
Proof.
  intros Hnum Hweight Htarget.
  apply affine_observation_size_bound.
  - exact Hweight.
  - change (length (unit_coefficients num_variables variable) <= B).
    rewrite unit_coefficients_length.
    exact Hnum.
  - change
      (forall coefficient,
        In coefficient (unit_coefficients num_variables variable) ->
        signed_magnitude coefficient <= B).
    intros coefficient Hcoefficient.
    pose proof
      (@unit_coefficients_magnitude_le_one
        num_variables variable coefficient Hcoefficient) as Hmagnitude.
    destruct num_variables as [|num_variables].
    + cbn [unit_coefficients unit_coefficients_from] in Hcoefficient.
      contradiction.
    + lia.
  - change (target <= B).
    exact Htarget.
Qed.

Lemma clause_observation_size_bound
    B num_variables clause :
  num_variables <= B ->
  length clause = 3 ->
  3 <= B ->
  size (enc (clause_observation num_variables clause)) <=
  100 * (B + 2) * (B + 2).
Proof.
  intros Hnum Hlength HB.
  apply affine_observation_size_bound.
  - change (1 <= B).
    lia.
  - change
      (length (dense_clause_coefficients num_variables clause) <= B).
    rewrite dense_clause_coefficients_length.
    exact Hnum.
  - change
      (forall coefficient,
        In coefficient
          (dense_clause_coefficients num_variables clause) ->
        signed_magnitude coefficient <= B).
    intros coefficient Hcoefficient.
    eapply Nat.le_trans.
    + exact
        (@dense_clause_coefficient_magnitude_le
          num_variables clause coefficient Hcoefficient).
    + lia.
  - change (negative_literal_count clause <= B).
    pose proof (negative_literal_count_le_length clause).
    lia.
Qed.

Lemma all_pinning_observations_from_row_size_bound
    B num_variables weight start count row :
  num_variables <= B ->
  weight <= B ->
  start + count <= num_variables ->
  In row
    (all_pinning_observations_from
      num_variables weight start count) ->
  size (enc row) <= 100 * (B + 2) * (B + 2).
Proof.
  intros Hnum Hweight.
  revert start row.
  induction count as [|count IH]; intros start row Hrange Hin.
  - cbn [all_pinning_observations_from] in Hin.
    contradiction.
  - cbn [all_pinning_observations_from] in Hin.
    apply in_app_iff in Hin.
    destruct Hin as [Hhead|Htail].
    + unfold pinning_observations_for_variable in Hhead.
      cbn in Hhead.
      destruct Hhead as [<-|[<-|Hfalse]].
      * apply pin_observation_size_bound; lia.
      * apply pin_observation_size_bound; lia.
      * contradiction.
    + eapply (IH (S start) row).
      * lia.
      * exact Htail.
Qed.

Lemma all_pinning_observations_row_size_bound
    B num_variables weight row :
  num_variables <= B ->
  weight <= B ->
  In row (all_pinning_observations num_variables weight) ->
  size (enc row) <= 100 * (B + 2) * (B + 2).
Proof.
  intros Hnum Hweight Hin.
  unfold all_pinning_observations in Hin.
  exact
    (@all_pinning_observations_from_row_size_bound
      B num_variables weight 0 num_variables row
      Hnum Hweight (ltac:(lia)) Hin).
Qed.

Lemma signed_of_difference_magnitude_le a b :
  signed_magnitude (signed_of_difference a b) <= a + b.
Proof.
  unfold signed_of_difference.
  destruct (b <=? a) eqn:Hle.
  - apply Nat.leb_le in Hle.
    cbn [signed_magnitude].
    lia.
  - apply Nat.leb_gt in Hle.
    cbn [signed_magnitude].
    assert (Hdifference : S (b - a - 1) = b - a) by lia.
    rewrite Hdifference.
    lia.
Qed.

Lemma compile_valid_timed_size_bound formula :
  kCNF 3 formula ->
  size (enc (compile_valid_timed formula)) <=
  500 *
    ((compiler_input_bound formula + 2) *
     (compiler_input_bound formula + 2) *
     (compiler_input_bound formula + 2)).
Proof.
  intros Hthree.
  rewrite compile_valid_timed_eq.
  remember (compiler_input_bound formula) as N eqn:HN.
  assert (HNpositive : 1 <= N).
  {
    rewrite HN.
    unfold compiler_input_bound.
    lia.
  }
  assert (Hformula : length formula <= N).
  {
    pose proof (formula_length_le_size formula).
    rewrite HN.
    unfold compiler_input_bound.
    lia.
  }
  assert (Hnum : source_num_variables formula <= N).
  {
    pose proof (source_num_variables_le_size_succ formula).
    rewrite HN.
    unfold compiler_input_bound.
    lia.
  }
  assert (Hweight : pin_weight formula <= N).
  {
    pose proof (pin_weight_le_size_succ formula).
    rewrite HN.
    unfold compiler_input_bound.
    lia.
  }
  set (observations :=
    all_pinning_observations
      (source_num_variables formula) (pin_weight formula) ++
    map
      (clause_observation (source_num_variables formula))
      formula).
  assert (Hobservations_length :
    length observations <= 3 * N).
  {
    unfold observations.
    rewrite app_length, all_pinning_observations_length, map_length.
    lia.
  }
  assert (Hrow :
    forall row,
      In row observations ->
      size (enc row) <= 100 * (N + 2) * (N + 2)).
  {
    intros row Hrow.
    unfold observations in Hrow.
    apply in_app_iff in Hrow.
    destruct Hrow as [Hpin|Hclause].
    - eapply all_pinning_observations_row_size_bound.
      + exact Hnum.
      + exact Hweight.
      + exact Hpin.
    - apply in_map_iff in Hclause.
      destruct Hclause as [clause [<- Hclause]].
      assert (Hlength : length clause = 3).
      {
        eapply kcnf_three_clause_length; eassumption.
      }
      assert (HthreeN : 3 <= N).
      {
        pose proof (clause_length_le_size clause).
        pose proof
          (@clause_size_le_formula_size formula clause Hclause).
        rewrite HN.
        unfold compiler_input_bound.
        lia.
      }
      apply clause_observation_size_bound.
      + exact Hnum.
      + exact Hlength.
      + exact HthreeN.
  }
  pose proof
    (@list_size_of_el
      affine_observation encodable_affine_observation
      observations (100 * (N + 2) * (N + 2)) Hrow) as Hlist.
  remember ((N + 2) * (N + 2)) as Q eqn:HQ.
  remember (Q * (N + 2)) as T eqn:HT.
  assert (HQpositive : 1 <= Q).
  {
    subst Q.
    nia.
  }
  assert (HTpositive : 1 <= T).
  {
    subst T.
    nia.
  }
  assert (HNQ : N <= Q).
  {
    rewrite HQ.
    eapply Nat.le_trans with (m := N + 2).
    - lia.
    - rewrite <- Nat.mul_1_r at 1.
      apply Nat.mul_le_mono_l.
      lia.
  }
  assert (HNT : N <= T).
  {
    eapply Nat.le_trans.
    - exact HNQ.
    - rewrite HT.
      rewrite <- Nat.mul_1_r at 1.
      apply Nat.mul_le_mono_l.
      lia.
  }
  assert (HQNT : Q * N <= T).
  {
    rewrite HT.
    apply Nat.mul_le_mono_l.
    lia.
  }
  replace
    (100 * (N + 2) * (N + 2))
    with (100 * Q) in Hlist
    by (rewrite HQ; ring).
  assert (Hlist' : size (enc observations) <= 350 * T).
  {
    unfold c__listsizeCons, c__listsizeNil in Hlist.
    assert (Hitems :
      100 * Q * length observations <=
      100 * Q * (3 * N)).
    {
      apply Nat.mul_le_mono_l.
      exact Hobservations_length.
    }
    assert (Hconstructors :
      5 * length observations <= 15 * N).
    {
      eapply Nat.le_trans.
      - apply Nat.mul_le_mono_l.
        exact Hobservations_length.
      - ring_simplify.
        apply Nat.le_refl.
    }
    nia.
  }
  pose proof
    (signed_of_difference_magnitude_le
      (pin_weight formula * source_num_variables formula)
      (length formula)) as Hthreshold_magnitude.
  pose proof
    (signed_integer_size_bound
      (signed_of_difference
        (pin_weight formula * source_num_variables formula)
        (length formula))) as Hthreshold_size.
  assert (Hthreshold_size' :
    size
      (enc
        (signed_of_difference
          (pin_weight formula * source_num_variables formula)
          (length formula))) <=
    20 * T).
  {
    assert (Hproduct :
      pin_weight formula * source_num_variables formula <= N * N).
    {
      apply Nat.mul_le_mono; assumption.
    }
    assert (Hquadratic : N * N + N + 2 <= 4 * T).
    {
      assert (HNNQ : N * N <= Q).
      {
        rewrite HQ.
        apply Nat.mul_le_mono; lia.
      }
      nia.
    }
    eapply Nat.le_trans.
    - exact Hthreshold_size.
    - replace (20 * T) with (5 * (4 * T)) by ring.
      apply Nat.mul_le_mono_l.
      lia.
  }
  assert (Hnum_size :
    size (enc (source_num_variables formula)) <= 5 * T).
  {
    rewrite size_nat_enc.
    unfold c__natsizeS, c__natsizeO.
    nia.
  }
  replace
    (size (enc (compile_valid formula)))
    with
    (size
      (enc
        (signed_regression_instance_representation
          (compile_valid formula))))
    by reflexivity.
  unfold signed_regression_instance_representation, compile_valid.
  cbn [instance_num_variables instance_observations instance_threshold].
  fold observations.
  repeat rewrite size_prod.
  cbn [fst snd].
  replace
    ((N + 2) * (N + 2) * (N + 2))
    with T by (rewrite HT, HQ; ring).
  lia.
Qed.

Definition compiler_time_polynomial (n : nat) : nat :=
  poly__kCNFDecb (n + size (enc 3)) +
  200 * compiler_cost_constant *
    ((n + 2) * (n + 2) * (n + 2)) + 8.

Definition compiler_size_polynomial (n : nat) : nat :=
  500 * ((n + 3) * (n + 3) * (n + 3)).

Lemma compile_timed_time_bound formula :
  compile_timed_time formula <=
  compiler_time_polynomial (size (enc formula)).
Proof.
  unfold compile_timed_time, compiler_time_polynomial.
  destruct (kCNF_decb 3 formula) eqn:Hthree.
  - apply kCNF_decb_iff in Hthree.
    pose proof
      (@compile_valid_timed_time_bound formula Hthree) as Hcompile.
    unfold compiler_input_bound in Hcompile.
    pose proof (kCNF_decb_time_bound 3 formula) as Hcheck.
    nia.
  - pose proof (kCNF_decb_time_bound 3 formula) as Hcheck.
    nia.
Qed.

Lemma rejecting_instance_size_bound :
  size (enc rejecting_instance) <= 500.
Proof.
  unfold rejecting_instance.
  change
    (size
      (enc
        (signed_regression_instance_representation
          {| instance_num_variables := 0;
             instance_observations := [];
             instance_threshold := signed_minus_one |})) <= 500).
  cbn [signed_regression_instance_representation signed_minus_one].
  vm_compute.
  lia.
Qed.

Lemma compile_timed_size_bound formula :
  size (enc (compile_timed formula)) <=
  compiler_size_polynomial (size (enc formula)).
Proof.
  unfold compile_timed, compiler_size_polynomial.
  destruct (kCNF_decb 3 formula) eqn:Hthree.
  - apply kCNF_decb_iff in Hthree.
    pose proof
      (@compile_valid_timed_size_bound formula Hthree) as Hcompile.
    unfold compiler_input_bound in Hcompile.
    nia.
  - eapply Nat.le_trans.
    + apply rejecting_instance_size_bound.
    + nia.
Qed.

Theorem compile_timed_polytime :
  polyTimeComputable compile_timed.
Proof.
  exists compiler_time_polynomial.
  - eexists (extT compile_timed).
    eapply computesTime_timeLeq.
    2: apply term_compile_timed.
    cbn.
    intros formula _.
    split.
    + apply compile_timed_time_bound.
    + easy.
  - unfold compiler_time_polynomial.
    smpl_inO.
    apply inOPoly_comp.
    + apply kCNF_decb_poly.
    + apply kCNF_decb_poly.
    + smpl_inO.
  - unfold compiler_time_polynomial.
    smpl_inO.
    apply kCNF_decb_poly.
  - exists compiler_size_polynomial.
    + apply compile_timed_size_bound.
    + unfold compiler_size_polynomial.
      smpl_inO.
    + unfold compiler_size_polynomial.
      smpl_inO.
Qed.

Print Assumptions compile_valid_timed_time_bound.
Print Assumptions compile_valid_timed_size_bound.
Print Assumptions compile_timed_polytime.
