From Coq Require Import List Arith Bool Lia.
From Complexity.NP.SAT Require Import SAT kSAT.
From mathcomp Require Import
  all_ssreflect all_algebra fraction rat ssrnum ssrint.
From PhdThesisCoq Require Import
  SignedInt TargetSyntax SourceAdapter CompilerSyntax BooleanSemantics FiveAdic.

Import ListNotations.
Import GRing.
Import GRing.Theory.
Import Num.Theory.
Import Order.Syntax.
Import Order.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

(** The stored sign-and-magnitude integers are exactly MathComp integers. *)
Definition signed_integer_as_int (z : signed_integer) : int :=
  match z with
  | Nonnegative n => Posz n
  | Negative n => Negz n
  end.

Definition signed_integer_to_five_adic
    (z : signed_integer) : five_adic :=
  (signed_integer_as_int z)%:~R.

Definition signed_integer_to_rat (z : signed_integer) : rat :=
  (signed_integer_as_int z)%:~R.

Lemma signed_integer_as_int_zero :
  signed_integer_as_int signed_zero = 0.
Proof. reflexivity. Qed.

Lemma signed_integer_as_int_one :
  signed_integer_as_int signed_one = 1.
Proof. reflexivity. Qed.

Lemma signed_integer_as_int_minus_one :
  signed_integer_as_int signed_minus_one = -1.
Proof. reflexivity. Qed.

Lemma signed_integer_as_int_opp z :
  signed_integer_as_int (signed_opp z) =
  - signed_integer_as_int z.
Proof. by case: z => [[|n]|n]. Qed.

Lemma signed_integer_as_int_add x y :
  signed_integer_as_int (signed_add x y) =
  signed_integer_as_int x + signed_integer_as_int y.
Proof.
case: x => a; case: y => b.
- by [].
- rewrite /signed_add /signed_of_difference /=.
  case Hle: (b.+1 <=? a).
  + move/Nat.leb_le: Hle => Hle.
    have HltP : (b < a)%coq_nat by lia.
    have Hlt : (b < a)%N := introT ssrnat.ltP HltP.
    change
      (Posz (a - b.+1)%coq_nat =
       intZmod.addz (Posz a) (Negz b)).
    by rewrite /intZmod.addz Hlt subnE.
  + move/Nat.leb_gt: Hle => Hle.
    have Hnlt : ~~ (b < a)%N.
      apply/negP.
      move/ssrnat.ltP=> Hlt.
      lia.
    change
      (Negz (b.+1 - a - 1)%coq_nat =
       intZmod.addz (Posz a) (Negz b)).
    rewrite /intZmod.addz (negPf Hnlt) subnE.
    congr (Negz _).
    change
      (Nat.sub (Nat.sub (S b) a) 1 = Nat.sub b a).
    lia.
- rewrite /signed_add /signed_of_difference /=.
  case Hle: (a.+1 <=? b).
  + move/Nat.leb_le: Hle => Hle.
    have HltP : (a < b)%coq_nat by lia.
    have Hlt : (a < b)%N := introT ssrnat.ltP HltP.
    change
      (Posz (b - a.+1)%coq_nat =
       intZmod.addz (Negz a) (Posz b)).
    by rewrite /intZmod.addz Hlt subnE.
  + move/Nat.leb_gt: Hle => Hle.
    have Hnlt : ~~ (a < b)%N.
      apply/negP.
      move/ssrnat.ltP=> Hlt.
      lia.
    change
      (Negz (a.+1 - b - 1)%coq_nat =
       intZmod.addz (Negz a) (Posz b)).
    rewrite /intZmod.addz (negPf Hnlt) subnE.
    congr (Negz _).
    change
      (Nat.sub (Nat.sub (S a) b) 1 = Nat.sub a b).
    lia.
- by [].
Qed.

Lemma signed_integer_to_five_adic_zero :
  signed_integer_to_five_adic signed_zero = 0.
Proof. by rewrite /signed_integer_to_five_adic signed_integer_as_int_zero.
Qed.

Lemma signed_integer_to_five_adic_one :
  signed_integer_to_five_adic signed_one = 1.
Proof. by rewrite /signed_integer_to_five_adic signed_integer_as_int_one.
Qed.

Lemma signed_integer_to_five_adic_minus_one :
  signed_integer_to_five_adic signed_minus_one = -1.
Proof.
by rewrite /signed_integer_to_five_adic signed_integer_as_int_minus_one
  mulrNz.
Qed.

Lemma signed_integer_to_five_adic_opp z :
  signed_integer_to_five_adic (signed_opp z) =
  - signed_integer_to_five_adic z.
Proof.
by rewrite /signed_integer_to_five_adic signed_integer_as_int_opp mulrNz.
Qed.

Lemma signed_integer_to_five_adic_add x y :
  signed_integer_to_five_adic (signed_add x y) =
  signed_integer_to_five_adic x + signed_integer_to_five_adic y.
Proof.
by rewrite /signed_integer_to_five_adic signed_integer_as_int_add intrD.
Qed.

(** Dot products and signed loss use the concrete fraction field [five_adic]. *)
Fixpoint five_adic_coefficient_dot
    (coefficients : list signed_integer)
    (point : nat -> five_adic)
    (index : nat) : five_adic :=
  match coefficients with
  | [] => 0
  | coefficient :: rest =>
      signed_integer_to_five_adic coefficient * point index +
      five_adic_coefficient_dot rest point (S index)
  end.

Definition observation_five_adic_residual
    (row : affine_observation)
    (point : nat -> five_adic) : five_adic :=
  five_adic_coefficient_dot
    (observation_coefficients row) point 0 -
  signed_integer_to_five_adic (observation_target row).

Definition observation_five_adic_contribution
    (row : affine_observation)
    (point : nat -> five_adic) : rat :=
  let magnitude :=
    (observation_weight row)%:R *
      five_adic_norm (observation_five_adic_residual row point) in
  if observation_is_positive row then magnitude else - magnitude.

Definition rat_sum (values : list rat) : rat :=
  fold_right (fun value total => value + total) 0 values.

Definition five_adic_sum (values : list five_adic) : five_adic :=
  fold_right (fun value total => value + total) 0 values.

Definition five_adic_regression_loss
    (instance : signed_regression_instance)
    (point : nat -> five_adic) : rat :=
  rat_sum
    (map
      (fun row => observation_five_adic_contribution row point)
      (instance_observations instance)).

Definition five_adic_regression_accepts
    (instance : signed_regression_instance) : Prop :=
  exists point : nat -> five_adic,
    five_adic_regression_loss instance point <=
      signed_integer_to_rat (instance_threshold instance).

Definition FixedPrimeSignedRegression
    (instance : signed_regression_instance) : Prop :=
  instance_well_formed instance /\
  five_adic_regression_accepts instance.

Lemma five_adic_sum_app left right :
  five_adic_sum (left ++ right) =
  five_adic_sum left + five_adic_sum right.
Proof.
elim: left => [|value left IH] /=.
- by rewrite add0r.
- by rewrite IH addrA.
Qed.

Lemma five_adic_sum_cons value values :
  five_adic_sum (value :: values) =
  value + five_adic_sum values.
Proof. reflexivity. Qed.

Lemma five_adic_sum_map_add {A : Type}
    (values : list A) (f g : A -> five_adic) :
  five_adic_sum (map (fun value => f value + g value) values) =
  five_adic_sum (map f values) + five_adic_sum (map g values).
Proof.
elim: values => [|value values IH] /=.
- by rewrite add0r.
- rewrite IH.
  rewrite !addrA.
  have Hswap :
      f value + g value + five_adic_sum (map f values) =
      f value + five_adic_sum (map f values) + g value :=
    addrAC (f value) (g value) (five_adic_sum (map f values)).
  by rewrite Hswap.
Qed.

Lemma five_adic_sum_map_zero {A : Type} (values : list A) :
  five_adic_sum (map (fun _ : A => 0) values) = 0.
Proof. by elim: values => [|value values IH] //=; rewrite IH add0r. Qed.

Lemma literal_coefficient_five_adic literal :
  signed_integer_to_five_adic (literal_coefficient literal) =
  if fst literal then -1 else 1.
Proof. by case: literal => [[] variable].
Qed.

Lemma coefficient_for_variable_five_adic variable clause :
  signed_integer_to_five_adic
    (coefficient_for_variable variable clause) =
  five_adic_sum
    (map
      (fun literal =>
        if Nat.eqb (literal_variable literal) variable
        then signed_integer_to_five_adic (literal_coefficient literal)
        else 0)
      clause).
Proof.
elim: clause => [|literal clause IH] /=.
- exact: signed_integer_to_five_adic_zero.
- case Heq: (Nat.eqb (literal_variable literal) variable).
  + by rewrite signed_integer_to_five_adic_add IH.
  + by rewrite add0r IH.
Qed.

Lemma five_adic_sum_indicator_seq_in
    (start count variable : nat)
    (coefficient : five_adic) (point : nat -> five_adic) :
  In variable (List.seq start count) ->
  five_adic_sum
    (map
      (fun index =>
        if Nat.eqb variable index
        then coefficient * point index
        else 0)
      (List.seq start count)) =
  coefficient * point variable.
Proof.
revert start variable.
induction count as [|count IH]; intros start variable Hin.
- contradiction.
- cbn [List.seq] in Hin.
  destruct Hin as [Heq | Hin].
  + subst variable.
    cbn [List.seq].
    rewrite map_cons five_adic_sum_cons Nat.eqb_refl.
    have Hzeros :
      map
        (fun index : nat =>
          if Nat.eqb start index
          then coefficient * point index
          else 0)
        (List.seq (S start) count) =
      map (fun _ : nat => 0) (List.seq (S start) count).
    {
      apply map_ext_in.
      intros index Hindex.
      apply List.in_seq in Hindex.
      destruct (Nat.eqb start index) eqn:Hindex_eq.
      - apply Nat.eqb_eq in Hindex_eq. lia.
      - reflexivity.
    }
    rewrite Hzeros five_adic_sum_map_zero addr0.
    reflexivity.
  + destruct (Nat.eqb variable start) eqn:Hindex_eq.
    * apply Nat.eqb_eq in Hindex_eq.
      subst variable.
      apply List.in_seq in Hin.
      lia.
    * cbn [List.seq].
      rewrite map_cons five_adic_sum_cons Hindex_eq add0r.
      apply IH.
      exact Hin.
Qed.

Lemma five_adic_sum_indicator_seq
    (num_variables variable : nat)
    (coefficient : five_adic) (point : nat -> five_adic) :
  (variable < num_variables)%nat ->
  five_adic_sum
    (map
      (fun index =>
        if Nat.eqb variable index
        then coefficient * point index
        else 0)
      (List.seq 0 num_variables)) =
  coefficient * point variable.
Proof.
intros Hbound.
apply five_adic_sum_indicator_seq_in.
apply List.in_seq.
split.
- lia.
- move/ssrnat.ltP: Hbound.
  lia.
Qed.

Lemma five_adic_coefficient_dot_map_seq
    (coefficient : nat -> signed_integer)
    (start count : nat) (point : nat -> five_adic) :
  five_adic_coefficient_dot
    (map coefficient (List.seq start count)) point start =
  five_adic_sum
    (map
      (fun index =>
        signed_integer_to_five_adic (coefficient index) *
        point index)
      (List.seq start count)).
Proof.
revert start.
induction count as [|count IH]; intros start.
- reflexivity.
- cbn [List.seq].
  rewrite !map_cons five_adic_sum_cons.
  change
    (signed_integer_to_five_adic (coefficient start) * point start +
     five_adic_coefficient_dot
       (map coefficient (List.seq (S start) count)) point (S start) =
     signed_integer_to_five_adic (coefficient start) * point start +
     five_adic_sum
       (map
         (fun index : nat =>
           signed_integer_to_five_adic (coefficient index) * point index)
         (List.seq (S start) count))).
  by rewrite IH.
Qed.

Lemma five_adic_coefficient_dot_dense_clause
    (num_variables : nat) (clause : list (bool * nat))
    (point : nat -> five_adic) :
  (forall sign variable,
      In (sign, variable) clause -> (variable < num_variables)%nat) ->
  five_adic_coefficient_dot
    (dense_clause_coefficients num_variables clause) point 0 =
  five_adic_sum
    (map
      (fun literal =>
        signed_integer_to_five_adic (literal_coefficient literal) *
        point (literal_variable literal))
      clause).
Proof.
intros Hbounded.
unfold dense_clause_coefficients.
rewrite five_adic_coefficient_dot_map_seq.
induction clause as [|[sign variable] clause IH].
- transitivity
    (five_adic_sum
      (map (fun _ : nat => 0) (List.seq 0 num_variables))).
  + apply f_equal.
    apply map_ext.
    intros index.
    rewrite /coefficient_for_variable
      signed_integer_to_five_adic_zero mul0r.
    reflexivity.
  + apply five_adic_sum_map_zero.
- assert (Hvariable : (variable < num_variables)%nat).
  {
    apply (Hbounded sign variable).
    left. reflexivity.
  }
  assert (Hrest :
    forall sign0 variable0,
      In (sign0, variable0) clause ->
      (variable0 < num_variables)%nat).
  {
    intros sign0 variable0 Hin.
    apply (Hbounded sign0 variable0).
    right. exact Hin.
  }
  change
    (five_adic_sum
      (map
        (fun index : nat =>
          signed_integer_to_five_adic
            (coefficient_for_variable
              index ((sign, variable) :: clause)) *
          point index)
        (List.seq 0 num_variables)) =
     signed_integer_to_five_adic
        (literal_coefficient (sign, variable)) *
        point variable +
     five_adic_sum
       (map
         (fun literal : bool * nat =>
           signed_integer_to_five_adic
             (literal_coefficient literal) *
           point (literal_variable literal))
         clause)).
  rewrite <- IH by exact Hrest.
  rewrite <-
    (five_adic_sum_indicator_seq
      (num_variables := num_variables)
      (variable := variable)
      (signed_integer_to_five_adic
        (literal_coefficient (sign, variable)))
      point Hvariable).
  rewrite <- five_adic_sum_map_add.
  apply f_equal.
  apply map_ext.
  intros index.
  change
    (signed_integer_to_five_adic
      (if Nat.eqb variable index
       then signed_add
         (literal_coefficient (sign, variable))
         (coefficient_for_variable index clause)
       else coefficient_for_variable index clause) *
     point index =
     (if Nat.eqb variable index
      then signed_integer_to_five_adic
        (literal_coefficient (sign, variable)) *
        point index
      else 0) +
     signed_integer_to_five_adic
       (coefficient_for_variable index clause) *
       point index).
  destruct (Nat.eqb variable index).
  + by rewrite signed_integer_to_five_adic_add mulrDl.
  + by rewrite add0r.
Qed.

Definition five_adic_boolean_value (b : bool) : five_adic :=
  if b then 1 else 0.

Definition embedded_boolean_point
    (point : nat -> bool) : nat -> five_adic :=
  fun variable => five_adic_boolean_value (point variable).

Lemma clause_target_five_adic clause :
  signed_integer_to_five_adic (clause_target clause) =
  (length (filter (fun literal => negb (fst literal)) clause))%:R.
Proof. reflexivity. Qed.

Lemma five_adic_minus_one_add_sub (a b : five_adic) :
  -1 + (a - b) = a - (b + 1).
Proof.
rewrite opprD.
rewrite [(-1 : five_adic) + (a + - b)]addrC.
by rewrite addrA.
Qed.

Lemma five_adic_one_add_sub (a b : five_adic) :
  1 + (a - b) = (a + 1) - b.
Proof.
rewrite addrA.
apply (f_equal (fun x : five_adic => x - b)).
exact: addrC.
Qed.

Lemma five_adic_succ_sub_succ (a b : five_adic) :
  (a + 1) - (b + 1) = a - b.
Proof.
rewrite opprD addrACA.
by rewrite addrN addr0.
Qed.

Lemma five_adic_sub_self_left (a b : five_adic) :
  (a - b) - a = - b.
Proof.
change (a + - b + - a = - b).
rewrite -addrA [(- b + - a)]addrC addrA.
by rewrite addrN add0r.
Qed.

Lemma five_adic_literal_sum_on_boolean
    (clause : list (bool * nat)) (point : nat -> bool) :
  five_adic_sum
    (map
      (fun literal =>
        signed_integer_to_five_adic (literal_coefficient literal) *
        embedded_boolean_point point (literal_variable literal))
      clause) =
  (length (filter (fun literal => negb (fst literal)) clause))%:R -
  (satisfied_literal_count point clause)%:R.
Proof.
unfold satisfied_literal_count.
induction clause as [|[sign variable] clause IH].
- by rewrite /= subr0.
- rewrite map_cons five_adic_sum_cons IH.
  unfold
    literal_coefficient, literal_satisfied_by,
    literal_variable, embedded_boolean_point,
    five_adic_boolean_value.
  destruct sign; destruct (point variable) eqn:Hpoint.
  all: cbn [fst snd].
  all: rewrite ?Hpoint.
  all: cbn
    [literal_satisfied_by literal_variable
     List.filter length Bool.eqb negb].
  all: rewrite ?Hpoint.
  all: cbn [fst snd List.filter length Bool.eqb negb].
  + rewrite ?signed_integer_to_five_adic_minus_one ?mulN1r -natr1.
    exact: five_adic_minus_one_add_sub.
  + by rewrite ?signed_integer_to_five_adic_minus_one ?mulr0 ?add0r.
  + rewrite ?signed_integer_to_five_adic_one ?mul1r -natr1.
    exact: five_adic_one_add_sub.
  + rewrite ?signed_integer_to_five_adic_one ?mulr0 ?add0r -!natr1.
    symmetry.
    exact: five_adic_succ_sub_succ.
Qed.

Lemma clause_five_adic_residual_on_boolean
    (num_variables : nat) (clause : list (bool * nat))
    (point : nat -> bool) :
  (forall sign variable,
      In (sign, variable) clause -> (variable < num_variables)%nat) ->
  observation_five_adic_residual
    (clause_observation num_variables clause)
    (embedded_boolean_point point) =
  - (satisfied_literal_count point clause)%:R.
Proof.
intros Hbounded.
unfold observation_five_adic_residual, clause_observation; cbn.
rewrite
  (five_adic_coefficient_dot_dense_clause
    (num_variables := num_variables)
    (clause := clause)
    (embedded_boolean_point point)
    Hbounded).
rewrite five_adic_literal_sum_on_boolean.
exact: five_adic_sub_self_left.
Qed.

Lemma rat_sum_app left right :
  rat_sum (left ++ right) = rat_sum left + rat_sum right.
Proof.
elim: left => [|value left IH] /=.
- by rewrite add0r.
- by rewrite IH addrA.
Qed.

Lemma rat_nat_one : (1%:R : rat) = 1.
Proof. by rewrite -[LHS]natr1 mulr0n add0r. Qed.

Lemma rat_nat_succ n :
  ((S n)%:R : rat) = (n%:R : rat) + 1.
Proof. symmetry; exact: natr1. Qed.

Lemma signed_integer_as_int_of_difference a b :
  signed_integer_as_int (signed_of_difference a b) =
  (a%:R - b%:R : int).
Proof.
have Hrepresentation :
    signed_of_difference a b =
    signed_add (Nonnegative a) (signed_opp (Nonnegative b)).
  destruct b as [|b].
  - unfold signed_opp, signed_add, signed_of_difference.
    cbn.
    rewrite Nat.sub_0_r Nat.add_0_r.
    reflexivity.
  - reflexivity.
rewrite Hrepresentation signed_integer_as_int_add signed_integer_as_int_opp.
change ((a%:Z - b%:Z : int) = (a%:R - b%:R : int)).
by rewrite !natz.
Qed.

Lemma signed_integer_to_rat_of_difference a b :
  signed_integer_to_rat (signed_of_difference a b) =
  (a%:R - b%:R : rat).
Proof.
rewrite /signed_integer_to_rat signed_integer_as_int_of_difference.
rewrite intrD mulrNz.
by rewrite !rmorph_nat.
Qed.

Lemma compile_valid_threshold_rat formula :
  signed_integer_to_rat
      (instance_threshold (compile_valid formula)) =
  ((pin_weight formula * source_num_variables formula)%:R -
    (length formula)%:R : rat).
Proof.
unfold compile_valid; cbn.
exact: signed_integer_to_rat_of_difference.
Qed.

Lemma five_adic_coefficient_dot_unit
    (num_variables variable : nat) (point : nat -> five_adic) :
  (variable < num_variables)%nat ->
  five_adic_coefficient_dot
      (unit_coefficients num_variables variable) point 0 =
  point variable.
Proof.
intros Hbound.
unfold unit_coefficients.
rewrite five_adic_coefficient_dot_map_seq.
transitivity
  (five_adic_sum
    (map
      (fun index =>
        if Nat.eqb variable index then point index else 0)
      (List.seq 0 num_variables))).
- apply f_equal.
  apply map_ext.
  intros index.
  rewrite Nat.eqb_sym.
  destruct (Nat.eqb variable index).
  + by rewrite signed_integer_to_five_adic_one mul1r.
  + by rewrite signed_integer_to_five_adic_zero mul0r.
- rewrite <-
    (mul1r (point variable)).
  rewrite <-
    (five_adic_sum_indicator_seq
      (num_variables := num_variables)
      (variable := variable) 1 point Hbound).
  apply f_equal.
  apply map_ext.
  intros index.
  destruct (Nat.eqb variable index); by rewrite ?mul1r.
Qed.

Lemma pin_five_adic_residual
    (num_variables variable weight target : nat)
    (point : nat -> five_adic) :
  (variable < num_variables)%nat ->
  observation_five_adic_residual
      (pin_observation num_variables variable weight target) point =
  point variable - target%:R.
Proof.
intros Hbound.
unfold observation_five_adic_residual, pin_observation; cbn.
rewrite five_adic_coefficient_dot_unit //.
Qed.

Lemma five_adic_norm_nat_three_indicator n :
  (n <= 3)%nat ->
  five_adic_norm (n%:R : five_adic) =
  if Nat.eqb n 0 then 0 else 1.
Proof.
move/ssrnat.leP=> Hbound.
destruct n as [|[|[|[|n]]]]; try lia.
- exact: five_adic_norm_zero.
- apply five_adic_norm_nat_small. by [].
- apply five_adic_norm_nat_small. by [].
- apply five_adic_norm_nat_small. by [].
Qed.

Lemma exact_three_satisfied_literal_count_bound
    formula clause point :
  exact_three_cnf formula ->
  In clause formula ->
  (satisfied_literal_count point clause <= 3)%nat.
Proof.
intros Hthree Hin.
destruct
  (exact_three_clause_decompose
    (formula := formula) (clause := clause) Hthree Hin)
  as [l0 [l1 [l2 Heq]]].
subst clause.
unfold satisfied_literal_count.
cbn [List.filter].
destruct (literal_satisfied_by point l0);
destruct (literal_satisfied_by point l1);
destruct (literal_satisfied_by point l2);
reflexivity.
Qed.

Lemma clause_five_adic_contribution_on_boolean
    (num_variables : nat) formula clause (point : nat -> bool) :
  exact_three_cnf formula ->
  In clause formula ->
  (forall sign variable,
      In (sign, variable) clause -> (variable < num_variables)%N) ->
  observation_five_adic_contribution
      (clause_observation num_variables clause)
      (embedded_boolean_point point) =
  - ((if List.existsb (literal_satisfied_by point) clause
      then 1%nat else 0%nat)%:R : rat).
Proof.
intros Hthree Hin Hbounded.
change
  (- ((1%:R : rat) *
      five_adic_norm
        (observation_five_adic_residual
          (clause_observation num_variables clause)
          (embedded_boolean_point point))) =
   - ((if List.existsb (literal_satisfied_by point) clause
       then 1%nat else 0%nat)%:R : rat)).
rewrite
  (clause_five_adic_residual_on_boolean
    (num_variables := num_variables)
    (clause := clause)
    point).
- rewrite five_adic_norm_neg.
  rewrite five_adic_norm_nat_three_indicator.
  + rewrite mul1r.
    destruct
      (List.existsb (literal_satisfied_by point) clause)
      eqn:Hsatisfied.
    * have Hpositive :
        (0 < satisfied_literal_count point clause)%coq_nat.
        exact:
          (proj2
            (satisfied_literal_count_positive_iff point clause)
            Hsatisfied).
      have Hneq :
          Nat.eqb (satisfied_literal_count point clause) 0 = false.
        apply Nat.eqb_neq. lia.
      by rewrite Hneq.
    * have Hzero :
        satisfied_literal_count point clause = 0%nat.
        destruct (satisfied_literal_count point clause) as [|count] eqn:Hcount.
        -- reflexivity.
        -- exfalso.
           have Hexists :
             List.existsb (literal_satisfied_by point) clause = true.
             apply satisfied_literal_count_positive_iff.
             lia.
           by rewrite Hsatisfied in Hexists.
      by rewrite Hzero.
  + exact:
      (exact_three_satisfied_literal_count_bound
        (formula := formula) (clause := clause) point Hthree Hin).
- exact Hbounded.
Qed.

Lemma pin_observation_pair_five_adic_contribution_on_boolean
    (num_variables variable weight : nat) (point : nat -> bool) :
  (variable < num_variables)%N ->
  observation_five_adic_contribution
      (pin_observation num_variables variable weight 0)
      (embedded_boolean_point point) +
  observation_five_adic_contribution
      (pin_observation num_variables variable weight 1)
      (embedded_boolean_point point) =
  (weight%:R : rat).
Proof.
intros Hbound.
change
  ((weight%:R : rat) *
      five_adic_norm
        (observation_five_adic_residual
          (pin_observation num_variables variable weight 0)
          (embedded_boolean_point point)) +
   (weight%:R : rat) *
      five_adic_norm
        (observation_five_adic_residual
          (pin_observation num_variables variable weight 1)
          (embedded_boolean_point point)) =
   (weight%:R : rat)).
rewrite !pin_five_adic_residual //.
unfold embedded_boolean_point, five_adic_boolean_value.
destruct (point variable).
- by rewrite subr0 subrr five_adic_norm_one five_adic_norm_zero
    mulr1 mulr0 addr0.
- by rewrite subr0 sub0r five_adic_norm_zero five_adic_norm_neg
    five_adic_norm_one mulr0 mulr1 add0r.
Qed.

Lemma pinning_five_adic_loss_over_variables_on_boolean
    (variables : list nat) (num_variables weight : nat)
    (point : nat -> bool) :
  (forall variable,
      In variable variables -> (variable < num_variables)%N) ->
  rat_sum
    (map
      (fun row =>
        observation_five_adic_contribution
          row (embedded_boolean_point point))
      (flat_map
        (pinning_observations_for_variable num_variables weight)
        variables)) =
  (weight%:R : rat) * (length variables)%:R.
Proof.
intros Hbounded.
induction variables as [|variable variables IH].
- by rewrite /= mulr0.
- change
    (observation_five_adic_contribution
        (pin_observation num_variables variable weight 0)
        (embedded_boolean_point point) +
     (observation_five_adic_contribution
        (pin_observation num_variables variable weight 1)
        (embedded_boolean_point point) +
      rat_sum
        (map
          (fun row : affine_observation =>
            observation_five_adic_contribution
              row (embedded_boolean_point point))
          (flat_map
            (pinning_observations_for_variable num_variables weight)
            variables))) =
     (weight%:R : rat) * (S (length variables))%:R).
  rewrite IH.
  + rewrite -natr1 mulrDr mulr1.
    rewrite addrA.
    rewrite
      (pin_observation_pair_five_adic_contribution_on_boolean
        (num_variables := num_variables) (variable := variable)
        weight point
        (Hbounded variable (or_introl (@Logic.eq_refl nat variable)))).
    exact: addrC.
  + intros variable0 Hin.
    apply Hbounded.
    right. exact Hin.
Qed.

Lemma all_pinning_observations_five_adic_loss_on_boolean
    (num_variables weight : nat) (point : nat -> bool) :
  rat_sum
    (map
      (fun row =>
        observation_five_adic_contribution
          row (embedded_boolean_point point))
      (all_pinning_observations num_variables weight)) =
  (weight%:R : rat) * num_variables%:R.
Proof.
unfold all_pinning_observations.
rewrite pinning_five_adic_loss_over_variables_on_boolean.
- by rewrite List.seq_length.
- intros variable Hin.
  apply List.in_seq in Hin.
  apply/ssrnat.ltP.
  lia.
Qed.

Lemma satisfied_clause_count_cons point clause formula :
  satisfied_clause_count point (clause :: formula) =
  if List.existsb (literal_satisfied_by point) clause
  then S (satisfied_clause_count point formula)
  else satisfied_clause_count point formula.
Proof.
unfold satisfied_clause_count.
cbn [List.filter].
destruct (List.existsb (literal_satisfied_by point) clause);
reflexivity.
Qed.

Lemma clause_observations_five_adic_loss_on_boolean
    (formula : list (list (bool * nat))) (num_variables : nat)
    (point : nat -> bool) :
  exact_three_cnf formula ->
  (forall clause sign variable,
      In clause formula ->
      In (sign, variable) clause ->
      (variable < num_variables)%N) ->
  rat_sum
    (map
      (fun row =>
        observation_five_adic_contribution
          row (embedded_boolean_point point))
      (map
        (clause_observation num_variables)
        formula)) =
  - ((satisfied_clause_count point formula)%:R : rat).
Proof.
intros Hthree Hbounded.
induction formula as [|clause formula IH].
- by rewrite /= oppr0.
- inversion Hthree as [|formula0 clause0 Hlength Htail].
  subst formula0 clause0.
  change
    (observation_five_adic_contribution
        (clause_observation
          num_variables clause)
        (embedded_boolean_point point) +
     rat_sum
       (map
         (fun row : affine_observation =>
           observation_five_adic_contribution
             row (embedded_boolean_point point))
         (map
           (clause_observation
             num_variables)
           formula)) =
     - ((satisfied_clause_count point (clause :: formula))%:R : rat)).
  rewrite IH.
  2: exact Htail.
  2: {
    intros clause1 sign variable HinClause HinLiteral.
    apply (Hbounded clause1 sign variable).
    - right. exact HinClause.
    - exact HinLiteral.
  }
  rewrite
    (clause_five_adic_contribution_on_boolean
      (num_variables := num_variables)
      (formula := clause :: formula) (clause := clause)
      point Hthree
      (or_introl
        (@Logic.eq_refl (list (bool * nat)) clause))).
  2: {
    intros sign variable HinLiteral.
    apply (Hbounded clause sign variable).
    - left. reflexivity.
    - exact HinLiteral.
  }
  rewrite satisfied_clause_count_cons.
  destruct (List.existsb (literal_satisfied_by point) clause).
  + rewrite rat_nat_one rat_nat_succ opprD.
    exact: addrC.
  + by rewrite add0r.
Qed.

Theorem compile_valid_five_adic_loss_on_boolean
    formula (point : nat -> bool) :
  exact_three_cnf formula ->
  five_adic_regression_loss
      (compile_valid formula) (embedded_boolean_point point) =
  ((pin_weight formula * source_num_variables formula)%:R -
    (satisfied_clause_count point formula)%:R : rat).
Proof.
intros Hthree.
change
  (rat_sum
    (map
      (fun row : affine_observation =>
        observation_five_adic_contribution
          row (embedded_boolean_point point))
      (all_pinning_observations
        (source_num_variables formula) (pin_weight formula) ++
       map
         (clause_observation (source_num_variables formula))
         formula)) =
   ((pin_weight formula * source_num_variables formula)%:R -
    (satisfied_clause_count point formula)%:R : rat)).
rewrite map_cat rat_sum_app.
rewrite all_pinning_observations_five_adic_loss_on_boolean.
rewrite clause_observations_five_adic_loss_on_boolean.
2: exact Hthree.
2: {
  intros clause sign variable HinClause HinLiteral.
  apply/ssrnat.ltP.
  eapply source_variable_lt_num_variables; eassumption.
}
rewrite natrM.
reflexivity.
Qed.

Theorem compile_valid_five_adic_accepts_of_satisfies
    formula assignment :
  exact_three_cnf formula ->
  SAT.satisfies assignment formula ->
  five_adic_regression_accepts (compile_valid formula).
Proof.
intros Hthree Hsatisfies.
exists (embedded_boolean_point (SAT.evalVar assignment)).
rewrite compile_valid_five_adic_loss_on_boolean //.
rewrite compile_valid_threshold_rat.
have Hcount :
    satisfied_clause_count (SAT.evalVar assignment) formula =
    length formula.
  exact:
    (proj2
      (satisfied_clause_count_assignment_iff formula assignment)
      Hsatisfies).
by rewrite Hcount.
Qed.

(** Coordinate rounding for the arbitrary-[Q5] soundness direction. *)
Definition round_five_adic_to_bool (x : five_adic) : bool :=
  if five_adic_norm x <= five_adic_norm (x - 1)
  then false
  else true.

Definition rounded_five_adic_value (x : five_adic) : five_adic :=
  five_adic_boolean_value (round_five_adic_to_bool x).

Definition five_adic_rounding_distance (x : five_adic) : rat :=
  five_adic_norm (x - rounded_five_adic_value x).

Definition update_five_adic_point
    (point : nat -> five_adic) (variable : nat)
    (value : five_adic) : nat -> five_adic :=
  fun index =>
    if Nat.eqb index variable then value else point index.

Lemma update_five_adic_point_eq point variable value :
  update_five_adic_point point variable value variable = value.
Proof. by rewrite /update_five_adic_point Nat.eqb_refl. Qed.

Lemma update_five_adic_point_neq point variable value index :
  index <> variable ->
  update_five_adic_point point variable value index = point index.
Proof.
move=> Hneq.
rewrite /update_five_adic_point.
apply Nat.eqb_neq in Hneq.
by rewrite Hneq.
Qed.

Lemma five_adic_x_sub_x_sub_one (x : five_adic) :
  x - (x - 1) = 1.
Proof.
apply: (addIr (x - 1)).
rewrite subrK [1 + (x - 1)]addrC.
symmetry.
exact: subrK.
Qed.

Lemma five_adic_norm_one_le_max_distances (x : five_adic) :
  1 <=
  Order.max (five_adic_norm x) (five_adic_norm (x - 1)).
Proof.
have Htriangle :=
  five_adic_norm_add_le_max x (- (x - 1)).
rewrite five_adic_norm_neg in Htriangle.
have Heq : x + - (x - 1) = 1.
  exact: five_adic_x_sub_x_sub_one.
rewrite Heq five_adic_norm_one in Htriangle.
exact Htriangle.
Qed.

Lemma five_adic_rounding_distance_nonnegative x :
  0 <= five_adic_rounding_distance x.
Proof. exact: five_adic_norm_nonnegative. Qed.

Lemma rounded_five_adic_pin_sum x :
  five_adic_norm (rounded_five_adic_value x) +
  five_adic_norm (rounded_five_adic_value x - 1) = 1.
Proof.
unfold rounded_five_adic_value, five_adic_boolean_value.
destruct (round_five_adic_to_bool x).
- by rewrite subrr five_adic_norm_one five_adic_norm_zero addr0.
- by rewrite sub0r five_adic_norm_zero five_adic_norm_neg
    five_adic_norm_one add0r.
Qed.

Lemma five_adic_rounding_pin_lower_bound x :
  1 + five_adic_rounding_distance x <=
  five_adic_norm x + five_adic_norm (x - 1).
Proof.
unfold five_adic_rounding_distance, rounded_five_adic_value,
  round_five_adic_to_bool, five_adic_boolean_value.
case Hle:
  (five_adic_norm x <= five_adic_norm (x - 1)).
- have Hone := five_adic_norm_one_le_max_distances x.
  rewrite (max_idPr Hle) in Hone.
  rewrite subr0.
  rewrite [five_adic_norm x + five_adic_norm (x - 1)]addrC.
  exact: ler_add Hone (lexx (five_adic_norm x)).
- have Hlt :
      five_adic_norm (x - 1) < five_adic_norm x.
    by rewrite ltNge Hle.
  have Hone := five_adic_norm_one_le_max_distances x.
  rewrite (max_idPl (ltW Hlt)) in Hone.
  exact:
    (ler_add Hone (lexx (five_adic_norm (x - 1)))).
Qed.

Lemma weighted_rounding_pin_lower_bound weight x :
  (weight%:R : rat) +
    (weight%:R : rat) * five_adic_rounding_distance x <=
  (weight%:R : rat) *
    (five_adic_norm x + five_adic_norm (x - 1)).
Proof.
have Hfactor :
    (weight%:R : rat) +
      (weight%:R : rat) * five_adic_rounding_distance x =
    (weight%:R : rat) * (1 + five_adic_rounding_distance x).
  by rewrite mulrDr mulr1.
rewrite Hfactor.
apply: ler_wpmul2l.
- exact: ler0n.
- exact: five_adic_rounding_pin_lower_bound.
Qed.

Lemma five_adic_sub_add_sub
    (a b c d : five_adic) :
  (a + b) - (c + d) = (a - c) + (b - d).
Proof.
change (a + b + - (c + d) = (a + - c) + (b + - d)).
rewrite opprD.
exact: addrACA.
Qed.

Lemma rat_add_interchange (a b c d : rat) :
  (a + b) + (c + d) = (a + c) + (b + d).
Proof. exact: addrACA. Qed.

Lemma literal_coefficient_five_adic_norm literal :
  five_adic_norm
    (signed_integer_to_five_adic (literal_coefficient literal)) = 1.
Proof.
rewrite literal_coefficient_five_adic.
destruct (fst literal).
- by rewrite five_adic_norm_neg five_adic_norm_one.
- exact: five_adic_norm_one.
Qed.

Lemma literal_term_update_difference_norm_le
    (point : nat -> five_adic) variable value literal :
  five_adic_norm
    (signed_integer_to_five_adic (literal_coefficient literal) *
       update_five_adic_point point variable value
         (literal_variable literal) -
     signed_integer_to_five_adic (literal_coefficient literal) *
       point (literal_variable literal)) <=
  five_adic_norm (value - point variable).
Proof.
case Heq: (Nat.eqb (literal_variable literal) variable).
- apply Nat.eqb_eq in Heq.
  rewrite Heq update_five_adic_point_eq.
  rewrite -mulrBr five_adic_norm_mul
    literal_coefficient_five_adic_norm mul1r.
  exact: lexx.
- have Hneq :
      literal_variable literal <> variable.
    exact: (proj1 (Nat.eqb_neq _ _) Heq).
  rewrite update_five_adic_point_neq //.
  rewrite subrr five_adic_norm_zero.
  exact: five_adic_norm_nonnegative.
Qed.

Lemma five_adic_literal_sum_update_difference_norm_le
    clause (point : nat -> five_adic) variable value :
  five_adic_norm
    (five_adic_sum
       (map
         (fun literal =>
           signed_integer_to_five_adic (literal_coefficient literal) *
           update_five_adic_point point variable value
             (literal_variable literal))
         clause) -
     five_adic_sum
       (map
         (fun literal =>
           signed_integer_to_five_adic (literal_coefficient literal) *
           point (literal_variable literal))
         clause)) <=
  five_adic_norm (value - point variable).
Proof.
induction clause as [|literal clause IH].
- rewrite /= subrr five_adic_norm_zero.
  exact: five_adic_norm_nonnegative.
- rewrite !map_cons !five_adic_sum_cons five_adic_sub_add_sub.
  apply: (le_trans (five_adic_norm_add_le_max _ _)).
  rewrite leUx.
  apply/andP; split.
  + exact: literal_term_update_difference_norm_le.
  + exact IH.
Qed.

Lemma clause_residual_update_difference_norm_le
    num_variables clause (point : nat -> five_adic) variable value :
  (forall sign index,
      In (sign, index) clause -> (index < num_variables)%N) ->
  five_adic_norm
    (observation_five_adic_residual
       (clause_observation num_variables clause)
       (update_five_adic_point point variable value) -
     observation_five_adic_residual
       (clause_observation num_variables clause) point) <=
  five_adic_norm (value - point variable).
Proof.
intros Hbounded.
unfold observation_five_adic_residual.
rewrite
  (five_adic_coefficient_dot_dense_clause
    (num_variables := num_variables) (clause := clause)
    (update_five_adic_point point variable value) Hbounded).
rewrite
  (five_adic_coefficient_dot_dense_clause
    (num_variables := num_variables) (clause := clause)
    point Hbounded).
rewrite five_adic_sub_add_sub subrr addr0.
exact: five_adic_literal_sum_update_difference_norm_le.
Qed.

Definition pin_pair_objective
    (weight : nat) (point : nat -> five_adic)
    (variable : nat) : rat :=
  (weight%:R : rat) *
    (five_adic_norm (point variable) +
     five_adic_norm (point variable - 1)).

Definition pinning_objective
    (num_variables weight : nat)
    (point : nat -> five_adic) : rat :=
  rat_sum
    (map
      (pin_pair_objective weight point)
      (List.seq 0 num_variables)).

Definition clause_objective
    (num_variables : nat) (clause : list (bool * nat))
    (point : nat -> five_adic) : rat :=
  - five_adic_norm
      (observation_five_adic_residual
        (clause_observation num_variables clause) point).

Definition clauses_objective
    (num_variables : nat)
    (formula : list (list (bool * nat)))
    (point : nat -> five_adic) : rat :=
  rat_sum
    (map
      (fun clause => clause_objective num_variables clause point)
      formula).

Definition compiled_formula_objective
    (formula : list (list (bool * nat)))
    (point : nat -> five_adic) : rat :=
  pinning_objective
    (source_num_variables formula) (pin_weight formula) point +
  clauses_objective (source_num_variables formula) formula point.

Lemma pin_observation_pair_five_adic_contribution
    num_variables variable weight (point : nat -> five_adic) :
  (variable < num_variables)%N ->
  observation_five_adic_contribution
      (pin_observation num_variables variable weight 0) point +
  observation_five_adic_contribution
      (pin_observation num_variables variable weight 1) point =
  pin_pair_objective weight point variable.
Proof.
intros Hbound.
unfold pin_pair_objective.
change
  ((weight%:R : rat) *
      five_adic_norm
        (observation_five_adic_residual
          (pin_observation num_variables variable weight 0) point) +
   (weight%:R : rat) *
      five_adic_norm
        (observation_five_adic_residual
          (pin_observation num_variables variable weight 1) point) =
   (weight%:R : rat) *
     (five_adic_norm (point variable) +
      five_adic_norm (point variable - 1))).
rewrite !pin_five_adic_residual // subr0.
symmetry.
exact: mulrDr.
Qed.

Lemma pinning_observations_loss_over_variables
    variables num_variables weight (point : nat -> five_adic) :
  (forall variable,
      In variable variables -> (variable < num_variables)%N) ->
  rat_sum
    (map
      (fun row => observation_five_adic_contribution row point)
      (flat_map
        (pinning_observations_for_variable num_variables weight)
        variables)) =
  rat_sum
    (map (pin_pair_objective weight point) variables).
Proof.
intros Hbounded.
induction variables as [|variable variables IH].
- reflexivity.
- change
    (observation_five_adic_contribution
        (pin_observation num_variables variable weight 0) point +
     (observation_five_adic_contribution
        (pin_observation num_variables variable weight 1) point +
      rat_sum
        (map
          (fun row : affine_observation =>
            observation_five_adic_contribution row point)
          (flat_map
            (pinning_observations_for_variable num_variables weight)
            variables))) =
     pin_pair_objective weight point variable +
     rat_sum
       (map (pin_pair_objective weight point) variables)).
  rewrite IH.
  2: {
    intros variable0 Hin.
    apply Hbounded.
    right. exact Hin.
  }
  rewrite addrA.
  congr (_ + _).
  exact:
    (pin_observation_pair_five_adic_contribution
      weight point
      (Hbounded variable
        (or_introl (@Logic.eq_refl nat variable)))).
Qed.

Lemma all_pinning_observations_five_adic_loss
    num_variables weight (point : nat -> five_adic) :
  rat_sum
    (map
      (fun row => observation_five_adic_contribution row point)
      (all_pinning_observations num_variables weight)) =
  pinning_objective num_variables weight point.
Proof.
unfold all_pinning_observations, pinning_objective.
apply pinning_observations_loss_over_variables.
intros variable Hin.
apply List.in_seq in Hin.
apply/ssrnat.ltP.
lia.
Qed.

Lemma clause_observation_five_adic_contribution
    num_variables clause (point : nat -> five_adic) :
  observation_five_adic_contribution
      (clause_observation num_variables clause) point =
  clause_objective num_variables clause point.
Proof.
unfold observation_five_adic_contribution, clause_objective.
cbn [observation_weight observation_is_positive].
by rewrite rat_nat_one mul1r.
Qed.

Lemma clause_observations_five_adic_loss
    num_variables formula (point : nat -> five_adic) :
  rat_sum
    (map
      (fun row => observation_five_adic_contribution row point)
      (map (clause_observation num_variables) formula)) =
  clauses_objective num_variables formula point.
Proof.
unfold clauses_objective.
induction formula as [|clause formula IH].
- reflexivity.
- change
    (observation_five_adic_contribution
        (clause_observation num_variables clause) point +
     rat_sum
       (map
         (fun row : affine_observation =>
           observation_five_adic_contribution row point)
         (map (clause_observation num_variables) formula)) =
     clause_objective num_variables clause point +
     rat_sum
       (map
         (fun clause0 : list (bool * nat) =>
           clause_objective num_variables clause0 point)
         formula)).
  rewrite IH clause_observation_five_adic_contribution.
  reflexivity.
Qed.

Theorem compile_valid_five_adic_loss formula point :
  five_adic_regression_loss (compile_valid formula) point =
  compiled_formula_objective formula point.
Proof.
change
  (rat_sum
    (map
      (fun row : affine_observation =>
        observation_five_adic_contribution row point)
      (all_pinning_observations
        (source_num_variables formula) (pin_weight formula) ++
       map
         (clause_observation (source_num_variables formula))
         formula)) =
   compiled_formula_objective formula point).
rewrite map_cat rat_sum_app.
rewrite all_pinning_observations_five_adic_loss.
rewrite clause_observations_five_adic_loss.
reflexivity.
Qed.

Lemma rat_sum_map_zero {A : Type} (values : list A) :
  rat_sum (map (fun _ : A => 0) values) = 0.
Proof. by induction values as [|value values IH]; rewrite /= ?IH ?add0r. Qed.

Lemma rat_sum_indicator_seq
    num_variables variable (value : rat) :
  (variable < num_variables)%N ->
  rat_sum
    (map
      (fun index =>
        if Nat.eqb index variable then value else 0)
      (List.seq 0 num_variables)) =
  value.
Proof.
revert variable.
induction num_variables as [|num_variables IH];
  intros variable Hbound.
- move/ssrnat.ltP: Hbound. lia.
- cbn [List.seq].
  destruct variable as [|variable].
  + change
      (value +
       rat_sum
         (map
           (fun index : nat =>
             if Nat.eqb index 0 then value else 0)
           (List.seq 1 num_variables)) =
       value).
    have Hzero :
        map
          (fun index : nat =>
            if Nat.eqb index 0 then value else 0)
          (List.seq 1 num_variables) =
        map (fun _ : nat => 0) (List.seq 1 num_variables).
      apply map_ext_in.
      intros index Hin.
      apply List.in_seq in Hin.
      destruct (Nat.eqb index 0) eqn:Heq.
      * apply Nat.eqb_eq in Heq. lia.
      * reflexivity.
    by rewrite Hzero rat_sum_map_zero addr0.
  + change
      (0 +
       rat_sum
         (map
           (fun index : nat =>
             if Nat.eqb index (S variable) then value else 0)
           (List.seq 1 num_variables)) =
       value).
    rewrite add0r.
    have Hshift :
        map
          (fun index : nat =>
            if Nat.eqb index (S variable) then value else 0)
          (List.seq 1 num_variables) =
        map
          (fun index : nat =>
            if Nat.eqb index variable then value else 0)
          (List.seq 0 num_variables).
      rewrite <- (List.seq_shift num_variables 0).
      rewrite -map_comp.
      apply map_ext.
      intros index.
      reflexivity.
    rewrite Hshift.
    apply IH.
    exact Hbound.
Qed.

Lemma pin_pair_objective_round_update_term
    weight (point : nat -> five_adic) variable index :
  pin_pair_objective weight
      (update_five_adic_point point variable
        (rounded_five_adic_value (point variable)))
      index +
  (if Nat.eqb index variable
   then
     (weight%:R : rat) *
       five_adic_rounding_distance (point variable)
   else 0) <=
  pin_pair_objective weight point index.
Proof.
unfold pin_pair_objective.
case Heq: (Nat.eqb index variable).
- apply Nat.eqb_eq in Heq.
  subst index.
  rewrite update_five_adic_point_eq.
  rewrite rounded_five_adic_pin_sum mulr1.
  exact: weighted_rounding_pin_lower_bound.
- have Hneq : index <> variable.
    exact: (proj1 (Nat.eqb_neq _ _) Heq).
  rewrite update_five_adic_point_neq // addr0.
  exact: lexx.
Qed.

Lemma pinning_objective_over_variables_round_update
    variables weight (point : nat -> five_adic) variable :
  rat_sum
    (map
      (pin_pair_objective weight
        (update_five_adic_point point variable
          (rounded_five_adic_value (point variable))))
      variables) +
  rat_sum
    (map
      (fun index =>
        if Nat.eqb index variable
        then
          (weight%:R : rat) *
            five_adic_rounding_distance (point variable)
        else 0)
      variables) <=
  rat_sum (map (pin_pair_objective weight point) variables).
Proof.
induction variables as [|index variables IH].
- exact: lexx.
- change
    ((pin_pair_objective weight
        (update_five_adic_point point variable
          (rounded_five_adic_value (point variable)))
        index +
      rat_sum
        (map
          (pin_pair_objective weight
            (update_five_adic_point point variable
              (rounded_five_adic_value (point variable))))
          variables)) +
     ((if Nat.eqb index variable
       then
         (weight%:R : rat) *
           five_adic_rounding_distance (point variable)
       else 0) +
      rat_sum
        (map
          (fun index0 : nat =>
            if Nat.eqb index0 variable
            then
              (weight%:R : rat) *
                five_adic_rounding_distance (point variable)
            else 0)
          variables)) <=
     pin_pair_objective weight point index +
     rat_sum
       (map (pin_pair_objective weight point) variables)).
  rewrite rat_add_interchange.
  exact:
    (ler_add
      (pin_pair_objective_round_update_term
        weight point variable index)
      IH).
Qed.

Lemma pinning_objective_round_update
    num_variables weight (point : nat -> five_adic) variable :
  (variable < num_variables)%N ->
  pinning_objective num_variables weight
      (update_five_adic_point point variable
        (rounded_five_adic_value (point variable))) +
    (weight%:R : rat) *
      five_adic_rounding_distance (point variable) <=
  pinning_objective num_variables weight point.
Proof.
intros Hbound.
unfold pinning_objective.
rewrite <-
  (rat_sum_indicator_seq
    (num_variables := num_variables) (variable := variable)
    ((weight%:R : rat) *
      five_adic_rounding_distance (point variable))
    Hbound).
exact:
  (pinning_objective_over_variables_round_update
    (List.seq 0 num_variables) weight point variable).
Qed.

Lemma variable_occurs_in_clause_false
    variable clause :
  variable_occurs_in_clause variable clause = false ->
  forall literal,
    In literal clause ->
    literal_variable literal <> variable.
Proof.
intros Hoccurs literal Hin.
induction clause as [|head clause IH].
- contradiction.
- cbn [variable_occurs_in_clause] in Hoccurs.
  apply Bool.orb_false_iff in Hoccurs.
  destruct Hoccurs as [Hhead Htail].
  destruct Hin as [Heq | Hin].
  + subst literal.
    exact: (proj1 (Nat.eqb_neq _ _) Hhead).
  + exact: (IH Htail Hin).
Qed.

Lemma five_adic_literal_sum_update_absent
    clause (point : nat -> five_adic) variable value :
  variable_occurs_in_clause variable clause = false ->
  five_adic_sum
    (map
      (fun literal =>
        signed_integer_to_five_adic (literal_coefficient literal) *
        update_five_adic_point point variable value
          (literal_variable literal))
      clause) =
  five_adic_sum
    (map
      (fun literal =>
        signed_integer_to_five_adic (literal_coefficient literal) *
        point (literal_variable literal))
      clause).
Proof.
intros Habsent.
apply f_equal.
apply map_ext_in.
intros literal Hin.
rewrite update_five_adic_point_neq //.
apply
  (variable_occurs_in_clause_false
    (variable := variable) (clause := clause) Habsent).
exact Hin.
Qed.

Lemma clause_residual_update_absent
    num_variables clause (point : nat -> five_adic) variable value :
  (forall sign index,
      In (sign, index) clause -> (index < num_variables)%N) ->
  variable_occurs_in_clause variable clause = false ->
  observation_five_adic_residual
    (clause_observation num_variables clause)
    (update_five_adic_point point variable value) =
  observation_five_adic_residual
    (clause_observation num_variables clause) point.
Proof.
intros Hbounded Habsent.
unfold observation_five_adic_residual.
rewrite
  (five_adic_coefficient_dot_dense_clause
    (num_variables := num_variables) (clause := clause)
    (update_five_adic_point point variable value) Hbounded).
rewrite
  (five_adic_coefficient_dot_dense_clause
    (num_variables := num_variables) (clause := clause)
    point Hbounded).
rewrite
  (five_adic_literal_sum_update_absent
    (clause := clause) (variable := variable)
    point value Habsent).
reflexivity.
Qed.

Lemma clause_objective_update_le
    num_variables clause (point : nat -> five_adic) variable value :
  (forall sign index,
      In (sign, index) clause -> (index < num_variables)%N) ->
  clause_objective num_variables clause
      (update_five_adic_point point variable value) <=
  clause_objective num_variables clause point +
    five_adic_norm (value - point variable).
Proof.
intros Hbounded.
unfold clause_objective.
set new_residual :=
  observation_five_adic_residual
    (clause_observation num_variables clause)
    (update_five_adic_point point variable value).
set old_residual :=
  observation_five_adic_residual
    (clause_observation num_variables clause) point.
have Hresidual :
    five_adic_norm (new_residual - old_residual) <=
    five_adic_norm (value - point variable).
  exact:
    (clause_residual_update_difference_norm_le
      (num_variables := num_variables) (clause := clause)
      point variable value Hbounded).
have Hdifference :
    five_adic_norm old_residual -
      five_adic_norm new_residual <=
    five_adic_norm (value - point variable).
  apply: (le_trans
    (five_adic_norm_sub_difference old_residual new_residual)).
  rewrite five_adic_norm_sub_sym.
  exact Hresidual.
rewrite -(ler_add2l (five_adic_norm old_residual)).
rewrite addrA addrN add0r.
exact Hdifference.
Qed.

Lemma clause_objective_update_absent
    num_variables clause (point : nat -> five_adic) variable value :
  (forall sign index,
      In (sign, index) clause -> (index < num_variables)%N) ->
  variable_occurs_in_clause variable clause = false ->
  clause_objective num_variables clause
      (update_five_adic_point point variable value) =
  clause_objective num_variables clause point.
Proof.
intros Hbounded Habsent.
unfold clause_objective.
rewrite
  (clause_residual_update_absent
    (num_variables := num_variables) (clause := clause)
    (variable := variable) point value Hbounded Habsent).
reflexivity.
Qed.

Definition clause_occurrence_penalty
    (variable : nat) (formula : list (list (bool * nat)))
    (distance : rat) : rat :=
  rat_sum
    (map
      (fun clause =>
        if variable_occurs_in_clause variable clause
        then distance
        else 0)
      formula).

Lemma clauses_objective_update_le
    num_variables formula (point : nat -> five_adic)
    variable value :
  (forall clause sign index,
      In clause formula ->
      In (sign, index) clause ->
      (index < num_variables)%N) ->
  clauses_objective num_variables formula
      (update_five_adic_point point variable value) <=
  clauses_objective num_variables formula point +
  clause_occurrence_penalty variable formula
    (five_adic_norm (value - point variable)).
Proof.
intros Hbounded.
induction formula as [|clause formula IH].
- exact: lexx.
- change
    (clause_objective num_variables clause
        (update_five_adic_point point variable value) +
     clauses_objective num_variables formula
       (update_five_adic_point point variable value) <=
     (clause_objective num_variables clause point +
      clauses_objective num_variables formula point) +
     ((if variable_occurs_in_clause variable clause
       then five_adic_norm (value - point variable)
       else 0) +
      clause_occurrence_penalty variable formula
        (five_adic_norm (value - point variable)))).
  have Hclause_bound :
      forall sign index,
        In (sign, index) clause -> (index < num_variables)%N.
    intros sign index Hin.
    apply (Hbounded clause sign index).
    - left. reflexivity.
    - exact Hin.
  have Hrest_bound :
      forall clause0 sign index,
        In clause0 formula ->
        In (sign, index) clause0 ->
        (index < num_variables)%N.
    intros clause0 sign index HinClause HinLiteral.
    apply (Hbounded clause0 sign index).
    - right. exact HinClause.
    - exact HinLiteral.
  specialize (IH Hrest_bound).
  have Hhead :
      clause_objective num_variables clause
          (update_five_adic_point point variable value) <=
      clause_objective num_variables clause point +
      (if variable_occurs_in_clause variable clause
       then five_adic_norm (value - point variable)
       else 0).
    case Hoccurs:
      (variable_occurs_in_clause variable clause).
    + apply: clause_objective_update_le.
      exact Hclause_bound.
    + rewrite
        (clause_objective_update_absent
          (num_variables := num_variables) (clause := clause)
          point value
          Hclause_bound Hoccurs) addr0.
      exact: lexx.
  have Hsum := ler_add Hhead IH.
  rewrite rat_add_interchange in Hsum.
  exact Hsum.
Qed.

Lemma variable_occurrence_count_cons variable clause formula :
  variable_occurrence_count variable (clause :: formula) =
  if variable_occurs_in_clause variable clause
  then S (variable_occurrence_count variable formula)
  else variable_occurrence_count variable formula.
Proof.
unfold variable_occurrence_count.
cbn [List.filter].
destruct (variable_occurs_in_clause variable clause);
reflexivity.
Qed.

Lemma clause_occurrence_penalty_eq
    variable formula distance :
  clause_occurrence_penalty variable formula distance =
  (variable_occurrence_count variable formula)%:R * distance.
Proof.
induction formula as [|clause formula IH].
- by rewrite /clause_occurrence_penalty
    /variable_occurrence_count /= mul0r.
- change
    ((if variable_occurs_in_clause variable clause
      then distance
      else 0) +
     clause_occurrence_penalty variable formula distance =
     (variable_occurrence_count variable
       (clause :: formula))%:R * distance).
  rewrite variable_occurrence_count_cons.
  case Hoccurs:
    (variable_occurs_in_clause variable clause).
  + rewrite IH rat_nat_succ mulrDl mul1r.
    exact: addrC.
  + by rewrite IH add0r.
Qed.

Lemma fold_right_max_map_ge
    {A : Type} (measure : A -> nat) values value :
  In value values ->
  Nat.le
    (measure value)
    (fold_right Nat.max O (map measure values)).
Proof.
induction values as [|head values IH].
- contradiction.
- intros [Heq | Hin].
  + subst head.
    cbn.
    apply Nat.le_max_l.
  + cbn.
    eapply Nat.le_trans.
    * exact: (IH Hin).
    * apply Nat.le_max_r.
Qed.

Lemma variable_occurrence_count_le_maximum
    num_variables formula variable :
  Nat.lt variable num_variables ->
  Nat.le
    (variable_occurrence_count variable formula)
    (maximum_occurrence num_variables formula).
Proof.
intros Hbound.
unfold maximum_occurrence.
apply
  (fold_right_max_map_ge
    (fun index => variable_occurrence_count index formula)
    (value := variable)).
apply List.in_seq.
lia.
Qed.

Lemma variable_occurrence_count_lt_pin_weight
    formula variable :
  Nat.lt variable (source_num_variables formula) ->
  Nat.lt
    (variable_occurrence_count variable formula)
    (pin_weight formula).
Proof.
intros Hbound.
unfold pin_weight.
apply Nat.lt_succ_r.
exact:
  (variable_occurrence_count_le_maximum
    (num_variables := source_num_variables formula)
    formula (variable := variable) Hbound).
Qed.

Lemma clause_occurrence_penalty_le_pin_budget
    formula variable distance :
  Nat.lt variable (source_num_variables formula) ->
  0 <= distance ->
  clause_occurrence_penalty variable formula distance <=
    ((pin_weight formula)%:R : rat) * distance.
Proof.
intros Hbound Hdistance.
rewrite clause_occurrence_penalty_eq.
apply: ler_wpmul2r.
- exact Hdistance.
- rewrite ler_nat.
  apply/ssrnat.leP.
  apply Nat.lt_le_incl.
  exact:
    (variable_occurrence_count_lt_pin_weight
      (formula := formula) (variable := variable) Hbound).
Qed.

Theorem compiled_formula_objective_round_coordinate_le
    formula (point : nat -> five_adic) variable :
  Nat.lt variable (source_num_variables formula) ->
  compiled_formula_objective formula
      (update_five_adic_point point variable
        (rounded_five_adic_value (point variable))) <=
  compiled_formula_objective formula point.
Proof.
intros Hvariable.
have Hvariable_ssr :
    (variable < source_num_variables formula)%N.
  apply/ssrnat.ltP.
  exact Hvariable.
set rounded_point :=
  update_five_adic_point point variable
    (rounded_five_adic_value (point variable)).
set distance := five_adic_rounding_distance (point variable).
set new_pins :=
  pinning_objective
    (source_num_variables formula) (pin_weight formula)
    rounded_point.
set old_pins :=
  pinning_objective
    (source_num_variables formula) (pin_weight formula) point.
set new_clauses :=
  clauses_objective
    (source_num_variables formula) formula rounded_point.
set old_clauses :=
  clauses_objective
    (source_num_variables formula) formula point.
set penalty := clause_occurrence_penalty variable formula distance.
set budget := ((pin_weight formula)%:R : rat) * distance.
have Hpins : new_pins + budget <= old_pins.
  exact:
    (pinning_objective_round_update
      (num_variables := source_num_variables formula)
      (pin_weight formula) point
      (variable := variable) Hvariable_ssr).
have Hclauses : new_clauses <= old_clauses + penalty.
  have Hraw :
      clauses_objective (source_num_variables formula) formula
          rounded_point <=
      clauses_objective (source_num_variables formula) formula point +
      clause_occurrence_penalty variable formula
        (five_adic_norm
          (rounded_five_adic_value (point variable) -
           point variable)).
    apply
      (clauses_objective_update_le
        (num_variables := source_num_variables formula)
        (formula := formula) point
        variable
        (rounded_five_adic_value (point variable))).
    intros clause sign index Hclause Hliteral.
    apply/ssrnat.ltP.
    exact:
      (source_variable_lt_num_variables
        (formula := formula) (clause := clause)
        (sign := sign) (variable := index) Hclause Hliteral).
  rewrite five_adic_norm_sub_sym in Hraw.
  exact Hraw.
have Hpenalty : penalty <= budget.
  exact:
    (clause_occurrence_penalty_le_pin_budget
      (formula := formula) (variable := variable)
      (distance := distance) Hvariable
      (five_adic_rounding_distance_nonnegative (point variable))).
change (new_pins + new_clauses <= old_pins + old_clauses).
apply: (le_trans (ler_add (lexx new_pins) Hclauses)).
apply: (le_trans
  (ler_add (lexx new_pins) (ler_add (lexx old_clauses) Hpenalty))).
rewrite [old_clauses + budget]addrC addrA.
exact: (ler_add Hpins (lexx old_clauses)).
Qed.

Fixpoint round_first_coordinates
    (count : nat) (point : nat -> five_adic) : nat -> five_adic :=
  match count with
  | O => point
  | S previous =>
      let rounded_prefix := round_first_coordinates previous point in
      update_five_adic_point rounded_prefix previous
        (rounded_five_adic_value (rounded_prefix previous))
  end.

Definition rounded_five_adic_assignment
    (point : nat -> five_adic) (variable : nat) : bool :=
  round_five_adic_to_bool
    (round_first_coordinates variable point variable).

Lemma round_first_coordinates_at_or_above
    count (point : nat -> five_adic) index :
  Nat.le count index ->
  round_first_coordinates count point index = point index.
Proof.
revert index.
induction count as [|count IH]; intros index Hbound.
- reflexivity.
- cbn [round_first_coordinates].
  rewrite update_five_adic_point_neq.
  + apply IH. lia.
  + lia.
Qed.

Lemma round_first_coordinates_on_prefix
    count (point : nat -> five_adic) index :
  Nat.lt index count ->
  round_first_coordinates count point index =
    five_adic_boolean_value
      (rounded_five_adic_assignment point index).
Proof.
revert index.
induction count as [|count IH]; intros index Hbound.
- lia.
- cbn [round_first_coordinates].
  destruct (Nat.eq_dec index count) as [Heq | Hneq].
  + subst index.
    rewrite update_five_adic_point_eq.
    reflexivity.
  + rewrite update_five_adic_point_neq //.
    apply IH.
    lia.
Qed.

Theorem compiled_formula_objective_round_prefix_le
    formula count (point : nat -> five_adic) :
  Nat.le count (source_num_variables formula) ->
  compiled_formula_objective formula
      (round_first_coordinates count point) <=
  compiled_formula_objective formula point.
Proof.
revert point.
induction count as [|count IH]; intros point Hcount.
- exact: lexx.
- cbn [round_first_coordinates].
  apply:
    (le_trans
      (compiled_formula_objective_round_coordinate_le
        (formula := formula)
        (round_first_coordinates count point) (variable := count) _)).
  + lia.
  + apply IH. lia.
Qed.

Lemma pinning_objective_ext
    num_variables weight
    (left right : nat -> five_adic) :
  (forall variable,
      Nat.lt variable num_variables ->
      left variable = right variable) ->
  pinning_objective num_variables weight left =
  pinning_objective num_variables weight right.
Proof.
intros Hequal.
unfold pinning_objective.
apply f_equal.
apply map_ext_in.
intros variable Hin.
unfold pin_pair_objective.
rewrite Hequal.
- reflexivity.
- apply List.in_seq in Hin.
  lia.
Qed.

Lemma clause_objective_ext
    num_variables clause
    (left right : nat -> five_adic) :
  (forall sign variable,
      In (sign, variable) clause ->
      Nat.lt variable num_variables) ->
  (forall variable,
      Nat.lt variable num_variables ->
      left variable = right variable) ->
  clause_objective num_variables clause left =
  clause_objective num_variables clause right.
Proof.
intros Hbounded Hequal.
have Hbounded_ssr :
    forall sign variable,
      In (sign, variable) clause ->
      (variable < num_variables)%N.
  intros sign variable Hin.
  apply/ssrnat.ltP.
  exact: (Hbounded sign variable Hin).
unfold clause_objective, observation_five_adic_residual.
rewrite
  (five_adic_coefficient_dot_dense_clause
    (num_variables := num_variables) (clause := clause)
    left Hbounded_ssr).
rewrite
  (five_adic_coefficient_dot_dense_clause
    (num_variables := num_variables) (clause := clause)
    right Hbounded_ssr).
have Hmap :
    map
      (fun literal =>
        signed_integer_to_five_adic (literal_coefficient literal) *
        left (literal_variable literal))
      clause =
    map
      (fun literal =>
        signed_integer_to_five_adic (literal_coefficient literal) *
        right (literal_variable literal))
      clause.
  apply map_ext_in.
  intros [sign variable] Hin.
  rewrite Hequal.
  + reflexivity.
  + exact: (Hbounded sign variable Hin).
by rewrite Hmap.
Qed.

Lemma clauses_objective_ext
    num_variables formula
    (left right : nat -> five_adic) :
  (forall clause sign variable,
      In clause formula ->
      In (sign, variable) clause ->
      Nat.lt variable num_variables) ->
  (forall variable,
      Nat.lt variable num_variables ->
      left variable = right variable) ->
  clauses_objective num_variables formula left =
  clauses_objective num_variables formula right.
Proof.
intros Hbounded Hequal.
induction formula as [|clause formula IH].
- reflexivity.
- change
    (clause_objective num_variables clause left +
       clauses_objective num_variables formula left =
     clause_objective num_variables clause right +
       clauses_objective num_variables formula right).
  have Hhead :
      clause_objective num_variables clause left =
      clause_objective num_variables clause right.
    apply
      (clause_objective_ext
        (num_variables := num_variables) (clause := clause)).
    + intros sign variable Hliteral.
      exact:
        (Hbounded clause sign variable
          (or_introl Logic.eq_refl) Hliteral).
    + exact Hequal.
  rewrite Hhead.
  have Hrest :
      forall clause0 sign variable,
        In clause0 formula ->
        In (sign, variable) clause0 ->
        Nat.lt variable num_variables.
    intros clause0 sign variable Hclause Hliteral.
    exact:
      (Hbounded clause0 sign variable
        (or_intror Hclause) Hliteral).
  by rewrite (IH Hrest).
Qed.

Lemma compiled_formula_objective_ext
    formula (left right : nat -> five_adic) :
  (forall variable,
      Nat.lt variable (source_num_variables formula) ->
      left variable = right variable) ->
  compiled_formula_objective formula left =
  compiled_formula_objective formula right.
Proof.
intros Hequal.
unfold compiled_formula_objective.
rewrite
  (pinning_objective_ext
    (num_variables := source_num_variables formula)
    (pin_weight formula) (left := left) (right := right) Hequal).
rewrite
  (clauses_objective_ext
    (num_variables := source_num_variables formula)
    (formula := formula) (left := left) (right := right)).
- reflexivity.
- intros clause sign variable Hclause Hliteral.
  exact:
    (source_variable_lt_num_variables
      (formula := formula) (clause := clause)
      (sign := sign) (variable := variable) Hclause Hliteral).
- exact Hequal.
Qed.

Lemma compiled_formula_objective_rounded_point
    formula (point : nat -> five_adic) :
  compiled_formula_objective formula
      (round_first_coordinates
        (source_num_variables formula) point) =
  compiled_formula_objective formula
      (embedded_boolean_point
        (rounded_five_adic_assignment point)).
Proof.
apply compiled_formula_objective_ext.
intros variable Hvariable.
exact:
  (round_first_coordinates_on_prefix
    (count := source_num_variables formula)
    point (index := variable) Hvariable).
Qed.

Theorem compile_valid_five_adic_rounding
    formula (point : nat -> five_adic) :
  five_adic_regression_loss
      (compile_valid formula)
      (embedded_boolean_point
        (rounded_five_adic_assignment point)) <=
  five_adic_regression_loss (compile_valid formula) point.
Proof.
rewrite !compile_valid_five_adic_loss.
rewrite <-
  (compiled_formula_objective_rounded_point
    formula point).
apply compiled_formula_objective_round_prefix_le.
apply Nat.le_refl.
Qed.

Definition boolean_point_assignment
    (num_variables : nat) (point : nat -> bool) : list nat :=
  List.filter point (List.seq 0 num_variables).

Lemma evalVar_boolean_point_assignment
    num_variables (point : nat -> bool) variable :
  Nat.lt variable num_variables ->
  SAT.evalVar (boolean_point_assignment num_variables point) variable =
    point variable.
Proof.
intros Hbound.
destruct (point variable) eqn:Hpoint.
- apply evalVar_in_iff.
  unfold boolean_point_assignment.
  apply List.filter_In.
  split.
  + apply List.in_seq. lia.
  + exact Hpoint.
- destruct
    (SAT.evalVar
      (boolean_point_assignment num_variables point) variable)
    eqn:Heval.
  + exfalso.
    apply evalVar_in_iff in Heval.
    unfold boolean_point_assignment in Heval.
    apply List.filter_In in Heval.
    destruct Heval as [_ Htrue].
    rewrite Hpoint in Htrue.
    discriminate.
  + reflexivity.
Qed.

Lemma boolean_point_assignment_satisfies
    formula (point : nat -> bool) :
  satisfied_clause_count point formula = length formula ->
  SAT.satisfies
    (boolean_point_assignment
      (source_num_variables formula) point)
    formula.
Proof.
intros Hcount.
have Hall :
    forall clause,
      In clause formula ->
      List.existsb (literal_satisfied_by point) clause = true.
  exact:
    (proj1
      (satisfied_clause_count_eq_length_iff point formula)
      Hcount).
unfold SAT.satisfies.
apply evalCnf_clause_iff.
intros clause Hclause.
apply evalClause_literal_iff.
specialize (Hall clause Hclause).
apply List.existsb_exists in Hall.
destruct Hall as [[sign variable] [Hliteral Hsatisfied]].
exists (sign, variable).
split.
- exact Hliteral.
- apply evalLiteral_var_iff.
  unfold literal_satisfied_by in Hsatisfied.
  cbn in Hsatisfied.
  have Hpoint_sign : point variable = sign.
    destruct (point variable);
      destruct sign;
      cbn in Hsatisfied;
      try discriminate;
      reflexivity.
  rewrite
    (evalVar_boolean_point_assignment
      (num_variables := source_num_variables formula)
      point (variable := variable)).
  + exact Hpoint_sign.
  + exact:
      (source_variable_lt_num_variables
        (formula := formula) (clause := clause)
        (sign := sign) (variable := variable)
        Hclause Hliteral).
Qed.

Lemma rat_nat_sub_same_minuend_le
    common left right :
  ((common%:R : rat) - left%:R <=
   (common%:R : rat) - right%:R) ->
  Nat.le right left.
Proof.
intros Horder.
have Hcast : ((right%:R : rat) <= left%:R).
  have Hcancel := Horder.
  rewrite <-
    (ler_add2l (- (common%:R : rat))) in Hcancel.
  rewrite !addrA !addNr !add0r ler_opp2 in Hcancel.
  exact Hcancel.
rewrite ler_nat in Hcast.
apply/ssrnat.leP.
exact Hcast.
Qed.

Theorem compile_valid_five_adic_boolean_threshold_iff
    formula (point : nat -> bool) :
  exact_three_cnf formula ->
  (five_adic_regression_loss
      (compile_valid formula) (embedded_boolean_point point) <=
    signed_integer_to_rat
      (instance_threshold (compile_valid formula)) <->
   satisfied_clause_count point formula = length formula).
Proof.
intros Hthree.
rewrite
  (compile_valid_five_adic_loss_on_boolean
    (formula := formula) point Hthree).
rewrite compile_valid_threshold_rat.
split.
- intros Hthreshold.
  have Hlower :
      Nat.le
        (length formula)
        (satisfied_clause_count point formula).
    exact:
      (rat_nat_sub_same_minuend_le
        (common :=
          pin_weight formula * source_num_variables formula)
        (left := satisfied_clause_count point formula)
        (right := length formula)
        Hthreshold).
  have Hupper :=
    satisfied_clause_count_le formula point.
  lia.
- intros Hequal.
  by rewrite Hequal.
Qed.

Theorem compile_valid_five_adic_sound
    formula :
  exact_three_cnf formula ->
  five_adic_regression_accepts (compile_valid formula) ->
  SAT.SAT formula.
Proof.
intros Hthree [point Haccepts].
have Hrounded :
    five_adic_regression_loss
      (compile_valid formula)
      (embedded_boolean_point
        (rounded_five_adic_assignment point)) <=
    signed_integer_to_rat
      (instance_threshold (compile_valid formula)).
  exact:
    (le_trans
      (compile_valid_five_adic_rounding formula point)
      Haccepts).
have Hcount :
    satisfied_clause_count
      (rounded_five_adic_assignment point) formula =
    length formula.
  exact:
    (proj1
      (compile_valid_five_adic_boolean_threshold_iff
        (formula := formula)
        (rounded_five_adic_assignment point) Hthree)
      Hrounded).
exists
  (boolean_point_assignment
    (source_num_variables formula)
    (rounded_five_adic_assignment point)).
exact:
  (boolean_point_assignment_satisfies
    (formula := formula)
    (point := rounded_five_adic_assignment point)
    Hcount).
Qed.

Lemma rejecting_instance_not_five_adic_accepts :
  ~ five_adic_regression_accepts rejecting_instance.
Proof.
intros [point Haccepts].
change (is_true ((0 : rat) <= (-1 : rat))) in Haccepts.
by move: Haccepts; rewrite leNgt oppr_lt0 ltr01.
Qed.

Theorem compile_five_adic_correct formula :
  kSAT 3 formula <->
  FixedPrimeSignedRegression (compile formula).
Proof.
split.
- intros [_ [Hthree [assignment Hsatisfies]]].
  have Hdec : kCNF_decb 3 formula = true.
    apply kCNF_decb_iff.
    exact Hthree.
  unfold compile.
  rewrite Hdec.
  split.
  + exact: compile_valid_well_formed.
  + exact:
      (compile_valid_five_adic_accepts_of_satisfies
        (formula := formula) (assignment := assignment)
        Hthree Hsatisfies).
- intros [_ Haccepts].
  unfold compile in Haccepts.
  destruct (kCNF_decb 3 formula) eqn:Hdec.
  + split.
    * lia.
    * split.
      -- apply kCNF_decb_iff.
         exact Hdec.
      -- exact:
           (compile_valid_five_adic_sound
             (formula := formula)
             (proj1 (kCNF_decb_iff 3 formula) Hdec)
             Haccepts).
  + exfalso.
    exact:
      (rejecting_instance_not_five_adic_accepts Haccepts).
Qed.

Print Assumptions compile_valid_five_adic_sound.
Print Assumptions compile_five_adic_correct.
