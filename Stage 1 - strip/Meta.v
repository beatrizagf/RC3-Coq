Require Coq.Bool.Sumbool.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Arith.EqNat.
Require Import Coq.Bool.Bool.

Require Import Shared.

(*
====
IDs
====
*)

Class ID (A : Type) :=
{
  id_eq_dec : forall (x y : A), {x = y} + {x <> y}
}.

Instance ID_nat : ID nat := {}.
  repeat decide equality.
Qed.

Inductive svar : Type :=
  | SVar : nat -> svar.

Instance ID_svar : ID svar := {}.
  repeat decide equality.
Qed.

Definition this := SVar 0.

Inductive dvar : Type :=
  | DVar : nat -> dvar.

Instance ID_dvar : ID dvar := {}.
  repeat decide equality.
Qed.

(*Atomicity*)

Inductive atomicity : Set :=
  | Atomic : atomicity
  | NonAtomic : atomicity.

Definition field_id := nat.
Definition method_id := nat.
Definition class_id := prod nat atomicity. (*it is now a tuple*)
Definition interface_id := prod nat atomicity. (*it is now a tuple*)
Definition loc := nat.
Definition lock := loc%type.

Definition stripClass (x: class_id) := (fst x, NonAtomic). (*to ignore atomicity, by saying all is NonAtomic*)
Definition stripInterface (x: interface_id) := (fst x, NonAtomic). (*to ignore atomicity, by saying all is NonAtomic*)


(*
====
Equality
====
*)

Definition eqb_atomicity(a a' : atomicity) :=
  match a with
    | Atomic => match a' with
                  | Atomic => true
                  | NonAtomic => false
                end
    | NonAtomic => match a' with
                  | Atomic => false
                  | NonAtomic => true
                end
  end.

(*defining equality for tuples*)
Definition eqb_class_id (c c' : class_id):=
   andb (beq_nat (fst c) (fst c')) (eqb_atomicity (snd c) (snd c')).

Definition eqb_interface_id (c c' : interface_id):=
   andb (beq_nat (fst c) (fst c')) (eqb_atomicity (snd c) (snd c')).


(*******************to help the proofs************************)

(*to help the proof: eqb_class_id_eq*)
Definition eqb_atomicity_eq : forall x y, true = eqb_atomicity x y -> x = y.
Proof.
  double induction x y; simpl in |- *.
    reflexivity.
    congruence. congruence.
    intros. reflexivity.
Defined.

(*to help other proofs*)
Definition eqb_class_id_eq : forall c c', true = eqb_class_id c c' -> c = c'.
Proof.
  double induction c c'.
  intros a b a0 b0.
  unfold eqb_class_id. simpl. 
  intros. apply andb_true_eq in H. (*separate &&*)
  destruct H as [H1 H2]. (*to separate the hypothesis*)
  apply beq_nat_eq in H1.
  apply eqb_atomicity_eq in H2.
  rewrite H1. rewrite H2. reflexivity.
Qed.


Definition eqb_interface_id_eq : forall i i', true = eqb_interface_id i i' -> i = i'.
Proof.
  double induction i i'.
  intros a b a0 b0.
  unfold eqb_interface_id. simpl. 
  intros. apply andb_true_eq in H. (*separate &&*)
  destruct H as [H1 H2]. (*to separate the hypothesis*)
  apply beq_nat_eq in H1.
  apply eqb_atomicity_eq in H2.
  rewrite H1. rewrite H2. reflexivity.
Qed.


(*
====
Map
====
*)

Definition partial_map (from:Type) {eqd : ID from} (to:Type) := from -> option to.

Definition empty {A B:Type} {eqd : ID A} : partial_map A B := (fun _ => None).

Definition extend {A B:Type} {eqd : ID A} (Gamma : partial_map A B) (a:A) (b:B) :=
  fun a' => if id_eq_dec a a' then
              Some b
            else
              Gamma a'.

Hint Unfold extend.

Definition drop {A B:Type} {eqd : ID A} (Gamma : partial_map A B) (a:A) :=
  fun a' => if id_eq_dec a a' then
              None
            else
              Gamma a'.

Hint Unfold drop.

Definition fresh {A B:Type} {eqd : ID A} (Gamma : partial_map A B) (a:A) := Gamma a = None.

Hint Unfold fresh.
