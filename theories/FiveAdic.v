From mathcomp Require Import
  all_ssreflect all_algebra fraction rat ssrnum.
From Combi Require Import natbar invlim padic.
From PhdThesisCoq Require Import PadicFoundation.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.
Import GRing.Theory.
Import Num.Theory.
Import Order.Syntax.
Import Order.Theory.

Local Open Scope ring_scope.
Local Open Scope quotient_scope.

(** The concrete prime used by the reduction. *)
Lemma five_prime : prime 5.
Proof. by []. Qed.

Definition five_adic_integer := padic_int five_prime.
Definition five_adic := {fraction five_adic_integer}.

Local Notation Z5 := five_adic_integer.
Local Notation Q5 := five_adic.

(** The rational value [1/5], used as the base of the 5-adic norm. *)
Definition five_norm_base : rat := (5%:R)^-1.

Definition norm_of_natbar (v : natbar) : rat :=
  match v with
  | Nat n => five_norm_base ^+ n
  | Inf => 0
  end.

Definition five_adic_integer_norm (x : Z5) : rat :=
  norm_of_natbar (valuat x).

Lemma five_norm_base_positive : 0 < five_norm_base.
Proof. by rewrite /five_norm_base invr_gt0 ltr0n. Qed.

Lemma five_norm_base_nonnegative : 0 <= five_norm_base.
Proof. exact: ltW five_norm_base_positive. Qed.

Lemma five_norm_base_at_most_one : five_norm_base <= 1.
Proof.
by rewrite /five_norm_base invr_le1 ?unitfE ?pnatr_eq0 ?ltr0n // ler1n.
Qed.

Lemma norm_of_natbar_nonnegative v : 0 <= norm_of_natbar v.
Proof.
case: v => [n|] /=; last exact: lexx.
exact: exprn_ge0 five_norm_base_nonnegative.
Qed.

Lemma norm_of_natbar_finite_positive n :
  0 < norm_of_natbar (Nat n).
Proof. exact: exprn_gt0 five_norm_base_positive. Qed.

Lemma norm_of_natbar_eq_zero v :
  (norm_of_natbar v == 0) = (v == Inf).
Proof.
case: v => [n|] /=; last by rewrite eqxx.
by rewrite (gt_eqF (norm_of_natbar_finite_positive n)).
Qed.

Lemma norm_of_natbar_add u v :
  norm_of_natbar (addbar u v) =
  norm_of_natbar u * norm_of_natbar v.
Proof. by case: u => [m|]; case: v => [n|] /=; rewrite ?exprD ?mul0r ?mulr0.
Qed.

Lemma norm_of_natbar_antitone (u v : natbar) :
  (u <= v)%O -> norm_of_natbar v <= norm_of_natbar u.
Proof.
case: u => [m|]; case: v => [n|] //=.
- rewrite leEnatbar.
  move=> Hmn.
  exact:
    (ler_wiexpn2l five_norm_base_nonnegative
      five_norm_base_at_most_one Hmn).
- move=> _.
  exact: exprn_ge0 five_norm_base_nonnegative.
Qed.

Lemma norm_of_natbar_min (u v : natbar) :
  norm_of_natbar (Order.min u v) =
  Order.max (norm_of_natbar u) (norm_of_natbar v).
Proof.
case: (leP u v) => Huv.
- by rewrite (max_idPl (norm_of_natbar_antitone Huv)).
- have Hvu : (v <= u)%O := ltW Huv.
  by rewrite (max_idPr (norm_of_natbar_antitone Hvu)).
Qed.

Lemma five_adic_integer_norm_nonnegative x :
  0 <= five_adic_integer_norm x.
Proof. exact: norm_of_natbar_nonnegative. Qed.

Lemma five_adic_integer_norm_eq_zero x :
  (five_adic_integer_norm x == 0) = (x == 0).
Proof. by rewrite /five_adic_integer_norm norm_of_natbar_eq_zero valuat0P.
Qed.

Lemma five_adic_integer_norm_zero :
  five_adic_integer_norm (0 : Z5) = 0.
Proof. by rewrite /five_adic_integer_norm valuat0.
Qed.

Lemma five_adic_integer_norm_one :
  five_adic_integer_norm (1 : Z5) = 1.
Proof. by rewrite /five_adic_integer_norm valuat1.
Qed.

Lemma five_adic_integer_norm_neg x :
  five_adic_integer_norm (- x) = five_adic_integer_norm x.
Proof. by rewrite /five_adic_integer_norm valuatN.
Qed.

Lemma five_adic_integer_norm_mul x y :
  five_adic_integer_norm (x * y) =
  five_adic_integer_norm x * five_adic_integer_norm y.
Proof.
by rewrite /five_adic_integer_norm
  padic_valuation_mul norm_of_natbar_add.
Qed.

Lemma five_adic_integer_norm_add_le_max x y :
  five_adic_integer_norm (x + y) <=
  Order.max (five_adic_integer_norm x) (five_adic_integer_norm y).
Proof.
rewrite /five_adic_integer_norm.
apply: (le_trans
  (norm_of_natbar_antitone (valuatD x y))).
by rewrite norm_of_natbar_min.
Qed.

(** A raw ratio has norm [|numerator|_5 / |denominator|_5]. *)
Definition five_adic_ratio_norm (r : {ratio Z5}) : rat :=
  five_adic_integer_norm \n_r / five_adic_integer_norm \d_r.

Lemma five_adic_ratio_denominator_norm_positive (r : {ratio Z5}) :
  0 < five_adic_integer_norm \d_r.
Proof.
have Hd : \d_r != 0 := denom_ratioP r.
rewrite lt_neqAle five_adic_integer_norm_nonnegative andbT.
by rewrite eq_sym five_adic_integer_norm_eq_zero Hd.
Qed.

Lemma five_adic_ratio_norm_equiv (r s : {ratio Z5}) :
  FracField.equivf r s ->
  five_adic_ratio_norm r = five_adic_ratio_norm s.
Proof.
move=> /eqP Hcross.
have Hnorm := congr1 five_adic_integer_norm Hcross.
rewrite !five_adic_integer_norm_mul in Hnorm.
rewrite /five_adic_ratio_norm.
have Hdr := five_adic_ratio_denominator_norm_positive r.
have Hds := five_adic_ratio_denominator_norm_positive s.
have Udr : five_adic_integer_norm \d_r \in GRing.unit.
  by rewrite unitfE (gt_eqF Hdr).
have Uds : five_adic_integer_norm \d_s \in GRing.unit.
  by rewrite unitfE (gt_eqF Hds).
apply: (mulIr Udr).
apply: (mulIr Uds).
rewrite (divrK Udr) [RHS]mulrAC (divrK Uds) mulrC.
exact Hnorm.
Qed.

Definition five_adic_norm (x : Q5) : rat :=
  five_adic_ratio_norm (repr x).

Lemma five_adic_norm_pi (r : {ratio Z5}) :
  five_adic_norm (\pi r : Q5) = five_adic_ratio_norm r.
Proof.
apply: five_adic_ratio_norm_equiv.
apply/eqP.
exact: FracField.equivf_l r.
Qed.

Lemma five_adic_ratio_norm_nonnegative (r : {ratio Z5}) :
  0 <= five_adic_ratio_norm r.
Proof.
apply: divr_ge0.
- exact: five_adic_integer_norm_nonnegative.
- exact: ltW (five_adic_ratio_denominator_norm_positive r).
Qed.

Lemma five_adic_ratio_norm_eq_zero (r : {ratio Z5}) :
  (five_adic_ratio_norm r == 0) = (\n_r == 0).
Proof.
have Hdr : \d_r != 0 := denom_ratioP r.
rewrite /five_adic_ratio_norm mulf_eq0 invr_eq0.
by rewrite !five_adic_integer_norm_eq_zero (negPf Hdr) orbF.
Qed.

Lemma five_adic_ratio_norm_mulf (r s : {ratio Z5}) :
  five_adic_ratio_norm (FracField.mulf r s) =
  five_adic_ratio_norm r * five_adic_ratio_norm s.
Proof.
have Hdr : \d_r != 0 := denom_ratioP r.
have Hds : \d_s != 0 := denom_ratioP s.
have Hden : \d_r * \d_s != 0 := mulf_neq0 Hdr Hds.
rewrite /five_adic_ratio_norm /FracField.mulf /=
  !numden_Ratio // !five_adic_integer_norm_mul.
have Udr : five_adic_integer_norm \d_r \in GRing.unit.
  by rewrite unitfE (gt_eqF (five_adic_ratio_denominator_norm_positive r)).
have Uds : five_adic_integer_norm \d_s \in GRing.unit.
  by rewrite unitfE (gt_eqF (five_adic_ratio_denominator_norm_positive s)).
rewrite invrM //.
by rewrite [(_ / _)]mulrC mulrACA.
Qed.

Lemma five_adic_ratio_norm_oppf (r : {ratio Z5}) :
  five_adic_ratio_norm (FracField.oppf r) =
  five_adic_ratio_norm r.
Proof.
have Hdr : \d_r != 0 := denom_ratioP r.
by rewrite /five_adic_ratio_norm /FracField.oppf /=
  !numden_Ratio // five_adic_integer_norm_neg.
Qed.

Lemma five_adic_ratio_norm_addf (r s : {ratio Z5}) :
  five_adic_ratio_norm (FracField.addf r s) <=
  Order.max (five_adic_ratio_norm r) (five_adic_ratio_norm s).
Proof.
have Hdr : \d_r != 0 := denom_ratioP r.
have Hds : \d_s != 0 := denom_ratioP s.
have Hden : \d_r * \d_s != 0 := mulf_neq0 Hdr Hds.
rewrite /five_adic_ratio_norm /FracField.addf /=
  !numden_Ratio // !five_adic_integer_norm_mul.
set A := five_adic_integer_norm \n_r.
set B := five_adic_integer_norm \d_r.
set C := five_adic_integer_norm \n_s.
set D := five_adic_integer_norm \d_s.
have HB : 0 < B.
  exact: five_adic_ratio_denominator_norm_positive r.
have HD : 0 < D.
  exact: five_adic_ratio_denominator_norm_positive s.
have HBD : 0 < B * D := mulr_gt0 HB HD.
have UB : B \in GRing.unit by rewrite unitfE (gt_eqF HB).
have UD : D \in GRing.unit by rewrite unitfE (gt_eqF HD).
rewrite (@ler_pdivr_mulr rat_numFieldType
  (B * D) (Order.max (A / B) (C / D))
  (five_adic_integer_norm (\n_r * \d_s + \n_s * \d_r)) HBD).
apply: (le_trans
  (five_adic_integer_norm_add_le_max
    (\n_r * \d_s) (\n_s * \d_r))).
rewrite !five_adic_integer_norm_mul.
rewrite leUx.
apply/andP; split.
- have Hleft :
      (A / B) * (B * D) <=
      Order.max (A / B) (C / D) * (B * D).
    by rewrite (ler_pmul2r HBD); exact: leUl.
  have Hcancel : (A / B) * (B * D) = A * D.
    rewrite -mulrA.
    congr (A * _).
    by rewrite (mulrA (B^-1) B D) (mulVr UB) mul1r.
  rewrite Hcancel in Hleft.
  exact Hleft.
- have Hright :
      (C / D) * (B * D) <=
      Order.max (A / B) (C / D) * (B * D).
    by rewrite (ler_pmul2r HBD); exact: leUr.
  have Hcancel : (C / D) * (B * D) = C * B.
    rewrite -mulrA [B * D]mulrC.
    congr (C * _).
    by rewrite (mulrA (D^-1) D B) (mulVr UD) mul1r.
  rewrite Hcancel in Hright.
  exact Hright.
Qed.

Lemma five_adic_norm_nonnegative x :
  0 <= five_adic_norm x.
Proof. exact: five_adic_ratio_norm_nonnegative. Qed.

Lemma five_adic_norm_eq_zero x :
  (five_adic_norm x == 0) = (x == 0).
Proof.
elim/(@quotW _ (FracField.frac_of_quotType
  (padic_int_idomainType five_prime))): x => r.
rewrite five_adic_norm_pi five_adic_ratio_norm_eq_zero.
rewrite -tofrac0.
unlock FracField.tofrac.
rewrite (@pi_eq_quot _ _
  (FracField.frac_of_eqQuotType
    (padic_int_idomainType five_prime))).
by rewrite /FracField.equivf /= !numden_Ratio ?oner_neq0 //
  mulr1 mulr0.
Qed.

Lemma five_adic_norm_positive x :
  x != 0 -> 0 < five_adic_norm x.
Proof.
move=> Hx.
rewrite lt_neqAle five_adic_norm_nonnegative andbT eq_sym.
by rewrite five_adic_norm_eq_zero Hx.
Qed.

Lemma five_adic_norm_mul x y :
  five_adic_norm (x * y) = five_adic_norm x * five_adic_norm y.
Proof.
elim/(@quotW _ (FracField.frac_of_quotType
  (padic_int_idomainType five_prime))): x => r.
elim/(@quotW _ (FracField.frac_of_quotType
  (padic_int_idomainType five_prime))): y => s.
change (five_adic_norm
  (@FracField.mul (padic_int_idomainType five_prime)
    (\pi_(FracField.frac_of_quotType
      (padic_int_idomainType five_prime)) r)
    (\pi_(FracField.frac_of_quotType
      (padic_int_idomainType five_prime)) s)) =
  five_adic_norm
    (\pi_(FracField.frac_of_quotType
      (padic_int_idomainType five_prime)) r) *
  five_adic_norm
    (\pi_(FracField.frac_of_quotType
      (padic_int_idomainType five_prime)) s)).
rewrite -(@FracField.pi_mul (padic_int_idomainType five_prime) r s)
  !five_adic_norm_pi.
exact: five_adic_ratio_norm_mulf.
Qed.

Lemma five_adic_norm_neg x :
  five_adic_norm (- x) = five_adic_norm x.
Proof.
elim/(@quotW _ (FracField.frac_of_quotType
  (padic_int_idomainType five_prime))): x => r.
change (five_adic_norm
  (@FracField.opp (padic_int_idomainType five_prime)
    (\pi_(FracField.frac_of_quotType
      (padic_int_idomainType five_prime)) r)) =
  five_adic_norm
    (\pi_(FracField.frac_of_quotType
      (padic_int_idomainType five_prime)) r)).
rewrite -(@FracField.pi_opp (padic_int_idomainType five_prime) r)
  !five_adic_norm_pi.
exact: five_adic_ratio_norm_oppf.
Qed.

Lemma five_adic_norm_add_le_max x y :
  five_adic_norm (x + y) <=
  Order.max (five_adic_norm x) (five_adic_norm y).
Proof.
elim/(@quotW _ (FracField.frac_of_quotType
  (padic_int_idomainType five_prime))): x => r.
elim/(@quotW _ (FracField.frac_of_quotType
  (padic_int_idomainType five_prime))): y => s.
change (five_adic_norm
  (@FracField.add (padic_int_idomainType five_prime)
    (\pi_(FracField.frac_of_quotType
      (padic_int_idomainType five_prime)) r)
    (\pi_(FracField.frac_of_quotType
      (padic_int_idomainType five_prime)) s)) <=
  Order.max
    (five_adic_norm
      (\pi_(FracField.frac_of_quotType
        (padic_int_idomainType five_prime)) r))
    (five_adic_norm
      (\pi_(FracField.frac_of_quotType
        (padic_int_idomainType five_prime)) s))).
rewrite -(@FracField.pi_add (padic_int_idomainType five_prime) r s)
  !five_adic_norm_pi.
exact: five_adic_ratio_norm_addf.
Qed.

Lemma five_adic_norm_zero :
  five_adic_norm (0 : Q5) = 0.
Proof.
rewrite -tofrac0.
unlock FracField.tofrac.
rewrite five_adic_norm_pi /five_adic_ratio_norm /=
  !numden_Ratio ?oner_neq0 //
  five_adic_integer_norm_zero five_adic_integer_norm_one.
by rewrite mul0r.
Qed.

Lemma five_adic_norm_one :
  five_adic_norm (1 : Q5) = 1.
Proof.
rewrite -tofrac1.
unlock FracField.tofrac.
rewrite five_adic_norm_pi /five_adic_ratio_norm /=
  !numden_Ratio ?oner_neq0 //
  five_adic_integer_norm_one.
by rewrite divr1.
Qed.

Lemma five_adic_norm_sub_sym x y :
  five_adic_norm (x - y) = five_adic_norm (y - x).
Proof. by rewrite -opprB five_adic_norm_neg. Qed.

Lemma five_adic_norm_add x y :
  five_adic_norm (x + y) <=
  five_adic_norm x + five_adic_norm y.
Proof.
apply: (le_trans (five_adic_norm_add_le_max x y)).
rewrite leUx.
apply/andP; split.
- by rewrite ler_addl five_adic_norm_nonnegative.
- by rewrite addrC ler_addl five_adic_norm_nonnegative.
Qed.

Lemma five_adic_norm_sub_difference x y :
  five_adic_norm x - five_adic_norm y <=
  five_adic_norm (x - y).
Proof.
rewrite ler_subl_addr.
have Hrewrite : x = (x - y) + y by rewrite subrK.
rewrite {1}Hrewrite.
exact: five_adic_norm_add.
Qed.

Lemma five_adic_norm_tofrac (x : Z5) :
  five_adic_norm (FracField.tofrac x) = five_adic_integer_norm x.
Proof.
unlock FracField.tofrac.
rewrite five_adic_norm_pi /five_adic_ratio_norm /=
  !numden_Ratio ?oner_neq0 // five_adic_integer_norm_one.
by rewrite divr1.
Qed.

Lemma five_adic_integer_norm_at_most_one x :
  five_adic_integer_norm x <= 1.
Proof.
rewrite /five_adic_integer_norm.
case: (valuat x) => [n|] /=.
- exact: exprn_ile1 five_norm_base_nonnegative
    five_norm_base_at_most_one.
- exact: ler01.
Qed.

Lemma five_adic_norm_nat_at_most_one n :
  five_adic_norm (n%:R : Q5) <= 1.
Proof.
rewrite -[n%:R](@rmorph_nat
  (padic_int_ringType five_prime)
  (FracField.frac_fieldType (padic_int_idomainType five_prime))
  (tofrac_rmorphism (padic_int_idomainType five_prime)) n).
rewrite five_adic_norm_tofrac.
exact: five_adic_integer_norm_at_most_one.
Qed.

Lemma five_adic_norm_nat_small n :
  (0 < n < 5)%N ->
  five_adic_norm (n%:R : Q5) = 1.
Proof.
move=> /andP[n0 n5].
rewrite -[n%:R](@rmorph_nat
  (padic_int_ringType five_prime)
  (FracField.frac_fieldType (padic_int_idomainType five_prime))
  (tofrac_rmorphism (padic_int_idomainType five_prime)) n).
rewrite five_adic_norm_tofrac /five_adic_integer_norm.
by rewrite padic_nat_valuation // ltn_log0 //=.
Qed.

Lemma five_adic_norm_int_at_most_one (z : int) :
  five_adic_norm (z%:~R : Q5) <= 1.
Proof.
case: z => [n|n].
- exact: five_adic_norm_nat_at_most_one.
- rewrite NegzE mulrNz five_adic_norm_neg.
  exact: five_adic_norm_nat_at_most_one.
Qed.
