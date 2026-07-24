From Coq Require Import List Arith Bool ZArith Lia.
From Complexity.NP.SAT Require Import SAT kSAT.
From PhdThesisCoq Require Import
  SignedInt TargetSyntax SourceAdapter CompilerSyntax.

Import ListNotations.
Open Scope Z_scope.

Definition boolean_value (b : bool) : Z :=
  if b then 1 else 0.

Definition integer_sum (values : list Z) : Z :=
  fold_right Z.add 0 values.

Fixpoint coefficient_dot
    (coefficients : list signed_integer)
    (point : nat -> bool)
    (index : nat) : Z :=
  match coefficients with
  | [] => 0
  | coefficient :: rest =>
      signed_integer_value coefficient * boolean_value (point index) +
      coefficient_dot rest point (S index)
  end.

Definition observation_boolean_residual
    (row : affine_observation) (point : nat -> bool) : Z :=
  coefficient_dot (observation_coefficients row) point 0 -
  signed_integer_value (observation_target row).

Definition five_adic_unit_norm_on_small_integer (value : Z) : nat :=
  if Z.eqb value 0 then 0 else 1.

Definition observation_boolean_contribution
    (row : affine_observation) (point : nat -> bool) : Z :=
  let magnitude :=
    (observation_weight row *
      five_adic_unit_norm_on_small_integer
        (observation_boolean_residual row point))%nat in
  if observation_is_positive row
  then Z.of_nat magnitude
  else - Z.of_nat magnitude.

Definition boolean_loss
    (instance : signed_regression_instance) (point : nat -> bool) : Z :=
  integer_sum
    (map
      (fun row => observation_boolean_contribution row point)
      (instance_observations instance)).

Definition literal_satisfied_by
    (point : nat -> bool) (literal : bool * nat) : bool :=
  Bool.eqb (point (literal_variable literal)) (fst literal).

Definition satisfied_literal_count
    (point : nat -> bool) (clause : list (bool * nat)) : nat :=
  length (filter (literal_satisfied_by point) clause).

Definition satisfied_clause_count
    (point : nat -> bool) (formula : list (list (bool * nat))) : nat :=
  length
    (filter
      (fun clause => existsb (literal_satisfied_by point) clause)
      formula).

Lemma integer_sum_app left right :
  integer_sum (left ++ right) = integer_sum left + integer_sum right.
Proof.
  unfold integer_sum.
  induction left as [|value left IH]; cbn; lia.
Qed.

Lemma integer_sum_map_add {A : Type}
    (values : list A) (f g : A -> Z) :
  integer_sum (map (fun value => f value + g value) values) =
  integer_sum (map f values) + integer_sum (map g values).
Proof.
  unfold integer_sum.
  induction values as [|value values IH].
  - reflexivity.
  - cbn.
    rewrite IH.
    lia.
Qed.

Lemma integer_sum_map_zero {A : Type} (values : list A) :
  integer_sum (map (fun _ : A => 0) values) = 0.
Proof.
  unfold integer_sum.
  induction values; cbn; assumption || reflexivity.
Qed.

Lemma literal_coefficient_value literal :
  signed_integer_value (literal_coefficient literal) =
    if fst literal then -1 else 1.
Proof.
  destruct literal as [sign variable].
  destruct sign; reflexivity.
Qed.

Lemma coefficient_for_variable_value variable clause :
  signed_integer_value (coefficient_for_variable variable clause) =
  integer_sum
    (map
      (fun literal =>
        if Nat.eqb (literal_variable literal) variable
        then signed_integer_value (literal_coefficient literal)
        else 0)
      clause).
Proof.
  induction clause as [|literal clause IH].
  - reflexivity.
  - change
      (signed_integer_value
        (if Nat.eqb (literal_variable literal) variable
         then signed_add
           (literal_coefficient literal)
           (coefficient_for_variable variable clause)
         else coefficient_for_variable variable clause) =
       (if Nat.eqb (literal_variable literal) variable
        then signed_integer_value (literal_coefficient literal)
        else 0) +
       integer_sum
         (map
           (fun literal0 : bool * nat =>
             if Nat.eqb (literal_variable literal0) variable
             then signed_integer_value (literal_coefficient literal0)
             else 0)
           clause))%Z.
    destruct (Nat.eqb (literal_variable literal) variable).
    + change
        (signed_integer_value
          (signed_add
            (literal_coefficient literal)
            (coefficient_for_variable variable clause)) =
         signed_integer_value (literal_coefficient literal) +
           integer_sum
             (map
               (fun literal0 : bool * nat =>
                 if Nat.eqb (literal_variable literal0) variable
                 then signed_integer_value (literal_coefficient literal0)
                 else 0)
               clause))%Z.
      rewrite signed_add_value, IH.
      reflexivity.
    + exact IH.
Qed.

Lemma integer_sum_indicator_seq_in
    (start count variable : nat)
    (coefficient : Z) (point : nat -> bool) :
  In variable (seq start count) ->
  integer_sum
    (map
      (fun index =>
        if Nat.eqb variable index
        then coefficient * boolean_value (point index)
        else 0)
      (seq start count)) =
  coefficient * boolean_value (point variable).
Proof.
  revert start variable.
  induction count as [|count IH]; intros start variable Hin.
  - contradiction.
  - cbn [List.seq] in Hin.
    destruct Hin as [Heq | Hin].
    + subst variable.
      cbn [List.seq].
      change
        (integer_sum
          ((if Nat.eqb start start
            then coefficient * boolean_value (point start)
            else 0) ::
           map
             (fun index : nat =>
               if Nat.eqb start index
               then coefficient * boolean_value (point index)
               else 0)
             (seq (S start) count)) =
         coefficient * boolean_value (point start)).
      rewrite Nat.eqb_refl.
      change
        (coefficient * boolean_value (point start) +
           integer_sum
             (map
               (fun index : nat =>
                 if Nat.eqb start index
                 then coefficient * boolean_value (point index)
                 else 0)
               (seq (S start) count)) =
         coefficient * boolean_value (point start))%Z.
      assert (Hzeros :
        map
          (fun index : nat =>
            if Nat.eqb start index
            then coefficient * boolean_value (point index)
            else 0)
          (seq (S start) count) =
        map (fun _ : nat => 0) (seq (S start) count)).
      {
        apply map_ext_in.
        intros index Hindex.
        apply in_seq in Hindex.
        destruct (Nat.eqb start index) eqn:Heq.
        - apply Nat.eqb_eq in Heq. lia.
        - reflexivity.
      }
      rewrite Hzeros, integer_sum_map_zero.
      lia.
    + destruct (Nat.eqb variable start) eqn:Heq.
      * apply Nat.eqb_eq in Heq.
        subst variable.
        apply in_seq in Hin.
        lia.
      * cbn [List.seq].
        change
          (integer_sum
            ((if Nat.eqb variable start
              then coefficient * boolean_value (point start)
              else 0) ::
             map
               (fun index : nat =>
                 if Nat.eqb variable index
                 then coefficient * boolean_value (point index)
                 else 0)
               (seq (S start) count)) =
           coefficient * boolean_value (point variable)).
        rewrite Heq.
        change
          (0 +
            integer_sum
              (map
                (fun index : nat =>
                  if Nat.eqb variable index
                  then coefficient * boolean_value (point index)
                  else 0)
                (seq (S start) count)) =
           coefficient * boolean_value (point variable))%Z.
        apply IH.
        exact Hin.
Qed.

Lemma integer_sum_indicator_seq
    (num_variables variable : nat)
    (coefficient : Z) (point : nat -> bool) :
  (variable < num_variables)%nat ->
  integer_sum
    (map
      (fun index =>
        if Nat.eqb variable index
        then coefficient * boolean_value (point index)
        else 0)
      (seq 0 num_variables)) =
  coefficient * boolean_value (point variable).
Proof.
  intros Hbound.
  apply integer_sum_indicator_seq_in.
  apply in_seq.
  lia.
Qed.

Lemma coefficient_dot_map_seq
    (coefficient : nat -> signed_integer)
    (start count : nat) (point : nat -> bool) :
  coefficient_dot
    (map coefficient (seq start count)) point start =
  integer_sum
    (map
      (fun index =>
        signed_integer_value (coefficient index) *
        boolean_value (point index))
      (seq start count)).
Proof.
  unfold integer_sum.
  revert start.
  induction count as [|count IH]; intros start.
  - reflexivity.
  - change
      (signed_integer_value (coefficient start) *
          boolean_value (point start) +
        coefficient_dot
          (map coefficient (seq (S start) count)) point (S start) =
       signed_integer_value (coefficient start) *
          boolean_value (point start) +
        fold_right Z.add 0
          (map
            (fun index : nat =>
              signed_integer_value (coefficient index) *
              boolean_value (point index))
            (seq (S start) count)))%Z.
    rewrite IH.
    reflexivity.
Qed.

Lemma coefficient_dot_dense_clause
    (num_variables : nat) (clause : list (bool * nat))
    (point : nat -> bool) :
  (forall sign variable,
      In (sign, variable) clause -> (variable < num_variables)%nat) ->
  coefficient_dot
    (dense_clause_coefficients num_variables clause) point 0 =
  integer_sum
    (map
      (fun literal =>
        signed_integer_value (literal_coefficient literal) *
        boolean_value (point (literal_variable literal)))
      clause).
Proof.
  intros Hbounded.
  unfold dense_clause_coefficients.
  rewrite coefficient_dot_map_seq.
  induction clause as [|[sign variable] clause IH].
  - change
      (integer_sum
        (map (fun _ : nat => 0) (seq 0 num_variables)) = 0).
    apply integer_sum_map_zero.
  -
    assert (Hvariable : (variable < num_variables)%nat).
    {
      apply (Hbounded sign variable).
      left. reflexivity.
    }
    assert (Hrest :
      forall sign0 variable0,
        In (sign0, variable0) clause -> (variable0 < num_variables)%nat).
    {
      intros sign0 variable0 Hin.
      apply (Hbounded sign0 variable0).
      right. exact Hin.
    }
    change
      (integer_sum
        (map
          (fun index : nat =>
            signed_integer_value
              (coefficient_for_variable
                index ((sign, variable) :: clause)) *
            boolean_value (point index))
          (seq 0 num_variables)) =
       signed_integer_value
          (literal_coefficient (sign, variable)) *
          boolean_value (point variable) +
       integer_sum
         (map
           (fun literal : bool * nat =>
             signed_integer_value (literal_coefficient literal) *
             boolean_value (point (literal_variable literal)))
           clause))%Z.
    rewrite <- IH by exact Hrest.
    rewrite <-
      (integer_sum_indicator_seq
        (num_variables := num_variables)
        (variable := variable)
        (signed_integer_value
          (literal_coefficient (sign, variable)))
        point
        Hvariable).
    rewrite <- integer_sum_map_add.
    apply f_equal.
    apply map_ext.
    intros index.
    change
      (signed_integer_value
        (if Nat.eqb variable index
         then signed_add
           (literal_coefficient (sign, variable))
           (coefficient_for_variable index clause)
         else coefficient_for_variable index clause) *
       boolean_value (point index) =
       (if Nat.eqb variable index
        then signed_integer_value
          (literal_coefficient (sign, variable)) *
          boolean_value (point index)
        else 0) +
       signed_integer_value (coefficient_for_variable index clause) *
         boolean_value (point index))%Z.
    destruct (Nat.eqb variable index) eqn:Hindex.
    + rewrite signed_add_value.
      destruct (point index); cbn; lia.
    + destruct (point index); reflexivity.
Qed.

Lemma clause_target_value clause :
  signed_integer_value (clause_target clause) =
  Z.of_nat
    (length (filter (fun literal => negb (fst literal)) clause)).
Proof. reflexivity. Qed.

Lemma clause_residual_is_negative_satisfied_count
    (num_variables : nat) (clause : list (bool * nat))
    (point : nat -> bool) :
  (forall sign variable,
      In (sign, variable) clause -> (variable < num_variables)%nat) ->
  observation_boolean_residual
    (clause_observation num_variables clause) point =
  - Z.of_nat (satisfied_literal_count point clause).
Proof.
  intros Hbounded.
  unfold observation_boolean_residual, clause_observation; cbn.
  rewrite coefficient_dot_dense_clause by exact Hbounded.
  unfold satisfied_literal_count.
  induction clause as [|[sign variable] clause IH].
  - reflexivity.
  - assert (Hrest :
      forall sign0 variable0,
        In (sign0, variable0) clause -> (variable0 < num_variables)%nat).
    {
      intros sign0 variable0 Hin.
      apply (Hbounded sign0 variable0).
      right. exact Hin.
    }
    specialize (IH Hrest).
    unfold integer_sum in *.
    unfold
      literal_coefficient, literal_satisfied_by, boolean_value,
      literal_variable in *.
    destruct sign; destruct (point variable) eqn:Hpoint.
    all: cbn in *.
    all: rewrite Hpoint.
    all: cbn in *.
    all: rewrite ?Nat2Z.inj_succ in *.
    all: lia.
Qed.

Lemma existsb_literal_satisfied_evalClause assignment clause :
  existsb (literal_satisfied_by (evalVar assignment)) clause =
  evalClause assignment clause.
Proof.
  unfold evalClause.
  induction clause as [|[sign variable] clause IH].
  - reflexivity.
  - cbn.
    rewrite IH.
    unfold literal_satisfied_by, literal_variable, evalLiteral.
    cbn.
    reflexivity.
Qed.

Lemma satisfied_literal_count_positive_iff point clause :
  (0 < satisfied_literal_count point clause)%nat <->
  existsb (literal_satisfied_by point) clause = true.
Proof.
  unfold satisfied_literal_count.
  split.
  - intros Hpositive.
    destruct
      (filter (literal_satisfied_by point) clause)
      as [|literal rest] eqn:Hfilter.
    + cbn in Hpositive. lia.
    + assert (Hin :
        In literal (filter (literal_satisfied_by point) clause)).
      {
        rewrite Hfilter.
        left. reflexivity.
      }
      apply filter_In in Hin.
      destruct Hin as [Hin Hsatisfied].
      apply existsb_exists.
      exists literal. split; assumption.
  - intros Hexists.
    apply existsb_exists in Hexists.
    destruct Hexists as [literal [Hin Hsatisfied]].
    assert (HinFilter :
      In literal (filter (literal_satisfied_by point) clause)).
    {
      apply filter_In.
      split; assumption.
    }
    destruct
      (filter (literal_satisfied_by point) clause)
      as [|head rest] eqn:Hfilter.
    + contradiction.
    + cbn. lia.
Qed.

Lemma clause_boolean_indicator
    (num_variables : nat) (clause : list (bool * nat))
    (point : nat -> bool) :
  (forall sign variable,
      In (sign, variable) clause -> (variable < num_variables)%nat) ->
  five_adic_unit_norm_on_small_integer
    (observation_boolean_residual
      (clause_observation num_variables clause) point) =
  if existsb (literal_satisfied_by point) clause then 1%nat else 0%nat.
Proof.
  intros Hbounded.
  rewrite clause_residual_is_negative_satisfied_count by exact Hbounded.
  unfold five_adic_unit_norm_on_small_integer.
  destruct (existsb (literal_satisfied_by point) clause) eqn:Hsatisfied.
  - apply satisfied_literal_count_positive_iff in Hsatisfied.
    destruct
      (Z.eqb (- Z.of_nat (satisfied_literal_count point clause)) 0)
      eqn:Hzero.
    + apply Z.eqb_eq in Hzero.
      assert (Hpositive :
        (0 < Z.of_nat (satisfied_literal_count point clause))%Z).
      {
        apply (proj1
          (Nat2Z.inj_lt 0 (satisfied_literal_count point clause))).
        exact Hsatisfied.
      }
      lia.
    + reflexivity.
  - assert (Hcount : satisfied_literal_count point clause = 0%nat).
    {
      destruct (satisfied_literal_count point clause) as [|count] eqn:Hcount;
        [reflexivity|].
      assert (Hexists :
        existsb (literal_satisfied_by point) clause = true).
      {
        apply satisfied_literal_count_positive_iff.
        lia.
      }
      rewrite Hsatisfied in Hexists.
      discriminate.
    }
    rewrite Hcount.
    reflexivity.
Qed.

Lemma coefficient_dot_unit
    (num_variables variable : nat) (point : nat -> bool) :
  (variable < num_variables)%nat ->
  coefficient_dot (unit_coefficients num_variables variable) point 0 =
  boolean_value (point variable).
Proof.
  intros Hbound.
  unfold unit_coefficients.
  rewrite coefficient_dot_map_seq.
  transitivity
    (integer_sum
      (map
        (fun index =>
          if Nat.eqb variable index
          then 1 * boolean_value (point index)
          else 0)
        (seq 0 num_variables))).
  - apply f_equal.
    apply map_ext.
    intros index.
    rewrite Nat.eqb_sym.
    destruct (Nat.eqb variable index); reflexivity.
  - rewrite
      (integer_sum_indicator_seq
        (num_variables := num_variables)
        (variable := variable)
        1 point Hbound).
    lia.
Qed.

Lemma pin_observation_pair_contribution
    (num_variables variable weight : nat) (point : nat -> bool) :
  (variable < num_variables)%nat ->
  observation_boolean_contribution
      (pin_observation num_variables variable weight 0) point +
  observation_boolean_contribution
      (pin_observation num_variables variable weight 1) point =
  Z.of_nat weight.
Proof.
  intros Hbound.
  unfold observation_boolean_contribution,
    observation_boolean_residual, pin_observation; cbn.
  rewrite !coefficient_dot_unit by exact Hbound.
  unfold five_adic_unit_norm_on_small_integer, boolean_value.
  destruct (point variable); cbn.
  - rewrite Nat.mul_1_r, Nat.mul_0_r. lia.
  - rewrite Nat.mul_0_r, Nat.mul_1_r. lia.
Qed.

(**
  A list-parametric form avoids depending on the starting index of [seq].
*)
Lemma pinning_loss_over_variables
    (variables : list nat) (num_variables weight : nat)
    (point : nat -> bool) :
  (forall variable,
      In variable variables -> (variable < num_variables)%nat) ->
  integer_sum
    (map
      (fun row => observation_boolean_contribution row point)
      (flat_map
        (pinning_observations_for_variable num_variables weight)
        variables)) =
  (Z.of_nat weight * Z.of_nat (length variables))%Z.
Proof.
  intros Hbounded.
  induction variables as [|variable variables IH]; cbn [integer_sum].
  - unfold integer_sum.
    simpl.
    lia.
  - change
      (observation_boolean_contribution
          (pin_observation num_variables variable weight 0) point +
       (observation_boolean_contribution
          (pin_observation num_variables variable weight 1) point +
        integer_sum
          (map
            (fun row => observation_boolean_contribution row point)
            (flat_map
              (pinning_observations_for_variable num_variables weight)
              variables))) =
       Z.of_nat weight * Z.of_nat (S (length variables)))%Z.
    pose proof
      (pin_observation_pair_contribution
        (num_variables := num_variables)
        (variable := variable)
        weight point
        (Hbounded variable (or_introl eq_refl))) as Hpair.
    rewrite IH.
    + rewrite Nat2Z.inj_succ.
      rewrite Z.mul_succ_r.
      lia.
    + intros variable0 Hin.
      apply Hbounded. right. exact Hin.
Qed.

Lemma all_pinning_observations_loss
    (num_variables weight : nat) (point : nat -> bool) :
  integer_sum
    (map
      (fun row => observation_boolean_contribution row point)
      (all_pinning_observations num_variables weight)) =
  (Z.of_nat weight * Z.of_nat num_variables)%Z.
Proof.
  unfold all_pinning_observations.
  rewrite pinning_loss_over_variables.
  - rewrite seq_length. reflexivity.
  - intros variable Hin.
    apply in_seq in Hin.
    lia.
Qed.

Lemma clause_observations_loss
    (formula : list (list (bool * nat))) (num_variables : nat)
    (point : nat -> bool) :
  (forall clause sign variable,
      In clause formula ->
      In (sign, variable) clause ->
      (variable < num_variables)%nat) ->
  integer_sum
    (map
      (fun row => observation_boolean_contribution row point)
      (map (clause_observation num_variables) formula)) =
  - Z.of_nat (satisfied_clause_count point formula).
Proof.
  intros Hbounded.
  induction formula as [|clause formula IH]; cbn [integer_sum].
  - reflexivity.
  - assert (Hclause :
      forall sign variable,
        In (sign, variable) clause -> (variable < num_variables)%nat).
    {
      intros sign variable Hin.
      apply (Hbounded clause sign variable); [left; reflexivity|exact Hin].
    }
    assert (Hrest :
      forall clause0 sign variable,
        In clause0 formula ->
        In (sign, variable) clause0 ->
        (variable < num_variables)%nat).
    {
      intros clause0 sign variable HinClause HinLiteral.
      apply (Hbounded clause0 sign variable);
        [right; exact HinClause|exact HinLiteral].
    }
    change
      (observation_boolean_contribution
          (clause_observation num_variables clause) point +
       integer_sum
         (map
           (fun row => observation_boolean_contribution row point)
           (map (clause_observation num_variables) formula)) =
       - Z.of_nat
          (satisfied_clause_count point (clause :: formula)))%Z.
    rewrite IH by exact Hrest.
    unfold observation_boolean_contribution; cbn.
    rewrite clause_boolean_indicator by exact Hclause.
    unfold satisfied_clause_count.
    destruct (existsb (literal_satisfied_by point) clause); cbn.
    + lia.
    + lia.
Qed.

Theorem compile_valid_boolean_loss formula point :
  boolean_loss (compile_valid formula) point =
  (Z.of_nat (pin_weight formula) *
      Z.of_nat (source_num_variables formula) -
    Z.of_nat (satisfied_clause_count point formula))%Z.
Proof.
  unfold boolean_loss, compile_valid; cbn.
  rewrite map_app, integer_sum_app.
  rewrite all_pinning_observations_loss.
  rewrite clause_observations_loss.
  - change
      (Z.of_nat (pin_weight formula) *
          Z.of_nat (source_num_variables formula) +
        - Z.of_nat (satisfied_clause_count point formula) =
       Z.of_nat (pin_weight formula) *
          Z.of_nat (source_num_variables formula) -
        Z.of_nat (satisfied_clause_count point formula))%Z.
    reflexivity.
  - intros clause sign variable HinClause HinLiteral.
    eapply source_variable_lt_num_variables; eassumption.
Qed.

Theorem compile_valid_boolean_threshold_iff formula point :
  boolean_loss (compile_valid formula) point <=
    signed_integer_value (instance_threshold (compile_valid formula)) <->
  (length formula <= satisfied_clause_count point formula)%nat.
Proof.
  rewrite compile_valid_boolean_loss, compile_valid_threshold.
  rewrite !Nat2Z.inj_mul.
  lia.
Qed.

Lemma satisfied_clause_count_le formula point :
  (satisfied_clause_count point formula <= length formula)%nat.
Proof.
  unfold satisfied_clause_count.
  induction formula as [|clause formula IH].
  - reflexivity.
  - cbn.
    destruct (existsb (literal_satisfied_by point) clause); cbn; lia.
Qed.

Theorem compile_valid_boolean_threshold_iff_all_clauses formula point :
  boolean_loss (compile_valid formula) point <=
    signed_integer_value (instance_threshold (compile_valid formula)) <->
  satisfied_clause_count point formula = length formula.
Proof.
  rewrite compile_valid_boolean_threshold_iff.
  pose proof (satisfied_clause_count_le formula point).
  lia.
Qed.

Lemma satisfied_clause_count_eq_length_iff
    point formula :
  satisfied_clause_count point formula = length formula <->
  forall clause,
    In clause formula ->
    existsb (literal_satisfied_by point) clause = true.
Proof.
  induction formula as [|clause formula IH].
  - split.
    + intros _ clause0 Hin.
      contradiction.
    + intros _.
      reflexivity.
  - destruct
      (existsb (literal_satisfied_by point) clause)
      eqn:Hclause.
    + unfold satisfied_clause_count at 1.
      cbn.
      rewrite Hclause.
      cbn.
      fold (satisfied_clause_count point formula).
      change
        (S (satisfied_clause_count point formula) =
            S (length formula) <->
         forall clause0,
           In clause0 (clause :: formula) ->
           existsb (literal_satisfied_by point) clause0 = true).
      split.
      * intros Hcount clause0 Hin.
        apply Nat.succ_inj in Hcount.
        destruct Hin as [Heq | Hin].
        -- subst clause0. exact Hclause.
        -- apply (proj1 IH Hcount clause0 Hin).
      * intros Hall.
        f_equal.
        apply (proj2 IH).
        intros clause0 Hin.
        apply Hall.
        right. exact Hin.
    + unfold satisfied_clause_count at 1.
      cbn.
      rewrite Hclause.
      cbn.
      fold (satisfied_clause_count point formula).
      change
        (satisfied_clause_count point formula =
            S (length formula) <->
         forall clause0,
           In clause0 (clause :: formula) ->
           existsb (literal_satisfied_by point) clause0 = true).
      split.
      * intros Hcount.
        pose proof (satisfied_clause_count_le formula point).
        lia.
      * intros Hall.
        specialize (Hall clause (or_introl eq_refl)).
        rewrite Hclause in Hall.
        discriminate.
Qed.

Lemma satisfied_clause_count_assignment_iff
    formula assignment :
  satisfied_clause_count (evalVar assignment) formula = length formula <->
  satisfies assignment formula.
Proof.
  rewrite satisfied_clause_count_eq_length_iff.
  unfold satisfies.
  rewrite evalCnf_clause_iff.
  split; intros Hall clause Hin.
  - rewrite <- existsb_literal_satisfied_evalClause.
    apply Hall. exact Hin.
  - rewrite existsb_literal_satisfied_evalClause.
    apply Hall. exact Hin.
Qed.

Theorem compile_valid_boolean_correct formula assignment :
  satisfies assignment formula <->
  boolean_loss (compile_valid formula) (evalVar assignment) <=
    signed_integer_value (instance_threshold (compile_valid formula)).
Proof.
  rewrite compile_valid_boolean_threshold_iff_all_clauses.
  symmetry.
  apply satisfied_clause_count_assignment_iff.
Qed.

Print Assumptions compile_valid_boolean_correct.
