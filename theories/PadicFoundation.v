From mathcomp Require Import
  all_ssreflect all_algebra fraction rat.
From Combi Require Import natbar directed invlim padic.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.
Import GRing.Theory.
Import Order.Syntax.
Import Order.Theory.

Local Open Scope ring_scope.

(**
  The pinned upstream development constructs [padic_int p_pr] as the inverse
  limit of the rings Z/(p^(n+1)).  This file supplies the exact
  multiplicative valuation theorem needed to extend that construction to its
  MathComp fraction field.
*)
Section PadicIntegerValuation.

Variables (p : nat) (p_pr : prime p).
Local Notation Zp := (padic_int p_pr).

Implicit Types (x y : Zp) (i j n : nat).

Lemma prime_power_positive n : (0 < p ^ n)%N.
Proof. by rewrite expn_gt0 prime_gt0. Qed.

Lemma padic_nat_projection i n :
  'pi_n (i%:R : Zp) = (i %% p ^ n.+1)%N :> nat.
Proof.
by rewrite rmorph_nat /= Zp_nat /= truncexp.
Qed.

Lemma padic_nat_eq0 (n : nat) :
  (n%:R == 0 :> Zp) = (n == 0%N).
Proof.
apply/eqP/eqP => [|-> //] H.
move/(congr1 'pi_n): H.
rewrite raddf0.
move/(congr1 val) => /=.
rewrite padic_nat_projection modn_small //.
exact: ltnW (ltn_expl n.+1 (prime_gt1 p_pr)).
Qed.

Lemma padic_nat_valuation n :
  (n > 0)%N -> valuat (n%:R : Zp) = Nat (logn p n).
Proof.
move/(pfactor_coprime p_pr) => [r copr {1}->].
move: (logn _ _) => {}n.
apply valuatNatE => [|i ltin].
- rewrite -val_eqE /= padic_nat_projection expnS.
  rewrite -muln_modl muln_eq0 negb_or.
  rewrite -[X in _ && X]lt0n prime_power_positive andbT.
  by rewrite -/(dvdn _ _) -prime_coprime.
- apply/eqP.
  rewrite -val_eqE /= padic_nat_projection.
  by rewrite -(subnK ltin) expnD mulnA modnMl.
Qed.

Lemma padic_power_divides i j :
  (i <= j)%N -> (p ^ i %| p ^ j)%N.
Proof. by move=> /subnK <-; rewrite expnD dvdn_mull. Qed.

Fact divide_by_prime_power_thread n x :
  isthread (padic_invsys p_pr)
    (fun i => inZp (('pi_((i + n)%N) x) %/ p ^ n)%N).
Proof.
move=> i j leij.
have leijn : ((i + n)%N <= (j + n)%N)%O.
  by rewrite leEnat leq_add2r -leEnat.
rewrite -(ilprojE x leijn) /padic_bond /= /Zmn.
apply val_inj => /=.
move: (val _) => value.
rewrite !(truncexp p_pr).
rewrite !modn_dvdm ?padic_power_divides // !modn_divl -expnD.
by rewrite modn_dvdm // padic_power_divides.
Qed.

Definition divide_by_prime_power n x : Zp :=
  ilthr (divide_by_prime_power_thread n x).

Lemma multiply_divide_prime_power_cancel n :
  cancel ( *%R (p%:R ^+ n) ) (divide_by_prime_power n).
Proof.
move=> x.
apply/invlimE => i.
rewrite ilthrP.
have Hcast : (p%:R ^+ n : Zp) = (p ^ n)%:R by rewrite natrX.
rewrite Hcast !rmorphM rmorph_nat /=.
have lei_in : (i <= (i + n)%N)%O by rewrite leEnat leq_addr.
rewrite -(ilprojE x lei_in) /= /padic_bond /Zmn.
apply val_inj => /=.
move: (val ('pi_((i + n)%N) x)) => value.
rewrite Zp_nat /=.
rewrite [(p ^ n %% _)%N]modn_small; first last.
  rewrite (truncexp p_pr) ltn_exp2l ?prime_gt1 //.
  by rewrite ltnS leq_addl.
rewrite !(truncexp p_pr) -addSn divn_modl;
  last exact/padic_power_divides/leq_addl.
rewrite mulKn ?prime_power_positive //.
have Hquot : (p ^ (i.+1 + n) %/ p ^ n = p ^ i.+1)%N.
  by rewrite expnD mulnK // prime_power_positive.
by rewrite Hquot modn_mod.
Qed.

Lemma divide_multiply_prime_power_cancel x n :
  'pi_n x = 0 ->
  p%:R ^+ n.+1 * divide_by_prime_power n.+1 x = x.
Proof.
move=> pin0.
have div_pix i : (p ^ n.+1 %| 'pi_((i + n.+1)%N) x)%N.
  have len_in : (n <= (i.+1 + n)%N)%O by rewrite leEnat leq_addl.
  have Hproj := ilprojE x len_in.
  rewrite pin0 in Hproj.
  move/(congr1 val): Hproj => /=.
  rewrite addSnnS.
  move: (val ('pi_((i + n.+1)%N) x)) => value.
  rewrite (truncexp p_pr) /dvdn.
  by move=> ->.
apply/invlimE => i.
rewrite rmorphM rmorphX rmorph_nat /= ilthrP.
have lei_in : (i <= (i + n.+1)%N)%O by rewrite leEnat leq_addr.
rewrite -(ilprojE x lei_in) /= /padic_bond /Zmn.
move/(_ i): div_pix => /dvdnP[k ->].
rewrite -[RHS]Zp_nat mulnK ?prime_power_positive //.
by rewrite -Zp_nat natrM natrX mulrC.
Qed.

Lemma padic_projection_zero_factor x n :
  'pi_n x = 0 -> {t : Zp | x = p%:R ^+ n.+1 * t}.
Proof.
move=> Hzero.
exists (divide_by_prime_power n.+1 x).
by rewrite divide_multiply_prime_power_cancel.
Qed.

Lemma padic_prime_power_projection_zero n :
  'pi_n (p%:R ^+ n.+1 : Zp) = 0.
Proof.
by apply val_inj; rewrite -natrX /= padic_nat_projection modnn.
Qed.

Lemma shifted_projection_zero x n :
  ('pi_n (p%:R ^+ n * x) == 0) = ('pi_0%N x == 0).
Proof.
apply/eqP/eqP.
- move/padic_projection_zero_factor => [y] /(congr1 (divide_by_prime_power n)).
  rewrite exprSr -mulrA !multiply_divide_prime_power_cancel => ->.
  by rewrite rmorphM /= padic_prime_power_projection_zero mul0r.
- move/padic_projection_zero_factor => [y].
  rewrite expr1 => ->{x}.
  rewrite mulrA -exprSr rmorphM /=.
  by rewrite padic_prime_power_projection_zero mul0r.
Qed.

Variant padic_valuation_spec x : natbar -> Type :=
  | PadicValuationFinite n t of
      'pi_n x != 0 &
      x = p%:R ^+ n * t :
      padic_valuation_spec x (Nat n)
  | PadicValuationInfinite of
      x = 0 :
      padic_valuation_spec x Inf.

Lemma padic_valuationP x :
  padic_valuation_spec x (valuat x).
Proof.
case: valuatP => [[|v] Hv vmin /= |->].
- apply: PadicValuationFinite.
  + exact Hv.
  + by rewrite expr0 mul1r.
- move/(_ _ (ltnSn v)): vmin =>
    /padic_projection_zero_factor[t Hx].
  exact: (PadicValuationFinite (t := t)).
- exact: PadicValuationInfinite.
Qed.

Theorem padic_valuation_mul x y :
  valuat (x * y) = addbar (valuat x) (valuat y).
Proof.
case: (padic_valuationP x) => [vx a pix eqx | ->]; last first.
  by rewrite mul0r valuat0.
case: (padic_valuationP y) => [vy b piy eqy | ->]; last first.
  by rewrite mulr0 valuat0.
rewrite /=.
apply valuatNatE.
- move: pix piy.
  rewrite {x}eqx {y}eqy mulrACA -exprD !shifted_projection_zero
    {vx vy}.
  rewrite rmorphM /=.
  move: (_ a) (_ b) => {}a {}b.
  have Fp_Zcast :
      Zp_trunc (pdiv p) = Zp_trunc p
    by have [] := Fp_Zcast p_pr.
  rewrite expn1 -Fp_Zcast in a b |- *.
  exact: mulf_neq0.
- move=> i lti.
  rewrite eqx eqy mulrACA -exprD -(subnK lti) exprD.
  rewrite !mulrA !rmorphM /=.
  by rewrite padic_prime_power_projection_zero !(mulr0, mul0r).
Qed.

End PadicIntegerValuation.
