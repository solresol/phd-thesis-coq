From Coq Require Import ZArith Lia.
From Undecidability.L.Tactics Require Import GenEncode LTactics.
From Undecidability.L.Datatypes Require Import LNat.

(**
  A small executable integer syntax.

  The upstream complexity library has a canonical encoding for natural
  numbers but not for Coq's [Z].  The target language therefore stores
  integers in sign-and-magnitude form.  [Negative n] denotes [-(n+1)], so
  the representation is canonical.
*)

Inductive signed_integer : Type :=
| Nonnegative : nat -> signed_integer
| Negative : nat -> signed_integer.

Definition signed_integer_value (z : signed_integer) : Z :=
  match z with
  | Nonnegative n => Z.of_nat n
  | Negative n => - Z.of_nat (S n)
  end.

Definition signed_zero : signed_integer := Nonnegative 0.
Definition signed_one : signed_integer := Nonnegative 1.
Definition signed_minus_one : signed_integer := Negative 0.

Definition signed_opp (z : signed_integer) : signed_integer :=
  match z with
  | Nonnegative 0 => signed_zero
  | Nonnegative (S n) => Negative n
  | Negative n => Nonnegative (S n)
  end.

Definition signed_of_difference (a b : nat) : signed_integer :=
  if b <=? a
  then Nonnegative (a - b)
  else Negative (b - a - 1).

Definition signed_add (x y : signed_integer) : signed_integer :=
  match x, y with
  | Nonnegative a, Nonnegative b => Nonnegative (a + b)
  | Negative a, Negative b => Negative (S (a + b))
  | Nonnegative a, Negative b => signed_of_difference a (S b)
  | Negative a, Nonnegative b => signed_of_difference b (S a)
  end.

Definition signed_mul_nat (k : nat) (x : signed_integer) : signed_integer :=
  match k with
  | 0 => signed_zero
  | S k' =>
      match x with
      | Nonnegative n => Nonnegative (k * n)
      | Negative n => Negative (k * S n - 1)
      end
  end.

Lemma signed_zero_value :
  signed_integer_value signed_zero = 0%Z.
Proof. reflexivity. Qed.

Lemma signed_one_value :
  signed_integer_value signed_one = 1%Z.
Proof. reflexivity. Qed.

Lemma signed_minus_one_value :
  signed_integer_value signed_minus_one = (-1)%Z.
Proof. reflexivity. Qed.

Lemma signed_opp_value z :
  signed_integer_value (signed_opp z) = (- signed_integer_value z)%Z.
Proof.
  destruct z as [[|n]|n]; cbn; lia.
Qed.

Lemma signed_of_difference_value a b :
  signed_integer_value (signed_of_difference a b) =
    (Z.of_nat a - Z.of_nat b)%Z.
Proof.
  unfold signed_of_difference.
  destruct (b <=? a) eqn:Hba.
  - apply Nat.leb_le in Hba.
    cbn [signed_integer_value].
    rewrite Nat2Z.inj_sub by exact Hba.
    lia.
  - apply Nat.leb_gt in Hba.
    cbn [signed_integer_value].
    assert (Hsucc : S (b - a - 1) = b - a) by lia.
    rewrite Hsucc, Nat2Z.inj_sub by lia.
    lia.
Qed.

Lemma signed_add_value x y :
  signed_integer_value (signed_add x y) =
    (signed_integer_value x + signed_integer_value y)%Z.
Proof.
  destruct x as [a|a], y as [b|b].
  - change (Z.of_nat (a + b) = Z.of_nat a + Z.of_nat b)%Z.
    apply Nat2Z.inj_add.
  - change (signed_integer_value (signed_of_difference a (S b)) =
      Z.of_nat a + - Z.of_nat (S b))%Z.
    rewrite signed_of_difference_value.
    lia.
  - change (signed_integer_value (signed_of_difference b (S a)) =
      - Z.of_nat (S a) + Z.of_nat b)%Z.
    rewrite signed_of_difference_value.
    lia.
  - change (- Z.of_nat (S (S (a + b))) =
      - Z.of_nat (S a) + - Z.of_nat (S b))%Z.
    rewrite !Nat2Z.inj_succ, Nat2Z.inj_add.
    lia.
Qed.

Lemma signed_mul_nat_value k x :
  signed_integer_value (signed_mul_nat k x) =
    (Z.of_nat k * signed_integer_value x)%Z.
Proof.
  destruct k as [|k], x as [n|n].
  - reflexivity.
  - reflexivity.
  - change (Z.of_nat (S k * n) = Z.of_nat (S k) * Z.of_nat n)%Z.
    apply Nat2Z.inj_mul.
  - change (- Z.of_nat (S (S k * S n - 1)) =
      Z.of_nat (S k) * - Z.of_nat (S n))%Z.
    assert (Hpos : (0 < S k * S n)%nat) by nia.
    assert (Hsucc : S (S k * S n - 1) = S k * S n) by lia.
    rewrite Hsucc, Nat2Z.inj_mul.
    reflexivity.
Qed.

MetaCoq Run (tmGenEncode "signed_integer_enc" signed_integer).
#[export] Hint Resolve signed_integer_enc_correct : Lrewrite.

#[export] Instance term_nonnegative :
  computableTime' Nonnegative (fun _ _ => (1, tt)).
Proof.
  extract constructor.
  solverec.
Qed.

#[export] Instance term_negative :
  computableTime' Negative (fun _ _ => (1, tt)).
Proof.
  extract constructor.
  solverec.
Qed.
