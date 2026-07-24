From Coq Require Import List Arith.
From Undecidability.L.Tactics Require Import LTactics.
From Undecidability.L.Datatypes Require Import LNat Lists LBool LProd.
From PhdThesisCoq Require Import SignedInt.

Import ListNotations.

Record affine_observation : Type := {
  observation_is_positive : bool;
  observation_weight : nat;
  observation_coefficients : list signed_integer;
  observation_target : signed_integer
}.

Record signed_regression_instance : Type := {
  instance_num_variables : nat;
  instance_observations : list affine_observation;
  instance_threshold : signed_integer
}.

Definition observation_well_formed
    (num_variables : nat) (row : affine_observation) : Prop :=
  length (observation_coefficients row) = num_variables.

Definition instance_well_formed (instance : signed_regression_instance) : Prop :=
  Forall
    (observation_well_formed (instance_num_variables instance))
    (instance_observations instance).

Definition positive_observation_count (instance : signed_regression_instance) : nat :=
  length
    (filter
      (fun row =>
        observation_is_positive row)
      (instance_observations instance)).

Definition negative_observation_count (instance : signed_regression_instance) : nat :=
  length
    (filter
      (fun row =>
        negb (observation_is_positive row))
      (instance_observations instance)).

Definition affine_observation_representation (row : affine_observation) :=
  (observation_is_positive row,
    (observation_weight row,
      (observation_coefficients row, observation_target row))).

#[global] Instance encodable_affine_observation :
  encodable affine_observation.
Proof.
  apply (registerAs affine_observation_representation).
Defined.

Definition signed_regression_instance_representation
    (instance : signed_regression_instance) :=
  (instance_num_variables instance,
    (instance_observations instance, instance_threshold instance)).

#[global] Instance encodable_signed_regression_instance :
  encodable signed_regression_instance.
Proof.
  apply (registerAs signed_regression_instance_representation).
Defined.
