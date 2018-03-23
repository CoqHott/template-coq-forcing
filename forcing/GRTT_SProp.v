Require Import Template.monad_utils Template.Ast
        Template.Template Template.LiftSubst.
Require Import String PeanoNat.
Require Import Template.Checker.
Require Import Template.Typing.
Require Import Forcing.TemplateForcing.
Require Import List.

(* Some axioms *)
Require Import FunctionalExtensionality.
Require Import ProofIrrelevance.

Open Scope string.

Inductive sle (n : nat) : nat -> SProp :=
  sle_n : sle n n
| sle_S : forall m : nat, sle n m -> sle n (S m).


Definition sle_n_Sm {n m : nat} : sle n m -> sle n (S m).
Proof.
  intros H. induction n; constructor; auto.
Defined.

Definition sle_refl (n : nat) : sle n n.
Proof.
  induction n;constructor.
Defined.

Definition sle_trans (n m p : nat) : sle n m -> sle m p -> sle n p.
Proof.
  intros f g. revert f.
  induction g.
  - intros. assumption.
  - intros. constructor. apply IHg. assumption.
Defined.

Definition sle_Sn (n : nat) : sle n (S n).
Proof.
  constructor; apply sle_refl.
Defined.

Definition nat_obj : Type := nat.
Definition nat_hom (P Q : nat_obj): SProp := sle Q P.
Notation "P ≥ Q" := (nat_hom P Q) (at level 70).

Definition id_nat_hom (P : nat_obj) : P ≥ P := sle_refl P.
Notation "# R" := (id_nat_hom R) (at level 70).

Definition nat_comp (A B C : nat_obj) (g : B ≥ C) (f : A ≥ B) : nat_hom A C
  := sle_trans _ _ _ g f.
Notation "f ∘ g" := (nat_comp _ _ _ f g) (at level 40).

Definition Z_le_1 : sle 0 1 := sle_S _ _ (sle_n _).

Eval compute in (fun P Q (g : P ≥ Q) => g ∘ (# P)).

(* Now, laws hold definitionally *)
(* Lemma nat_cat_left_id P R (g : R ≤ P)  : (g ∘ (# R)) = g. *)
(* Proof. reflexivity. Qed. *)

(* Lemma nat_cat_right_id P R (f : P ≤ R)  : f ∘ (# R) = f. *)
(* Proof. reflexivity. Qed. *)

(* Lemma nat_cat_assoc P Q R S (f : P ≤ Q) (g : Q ≤ R) (h : R ≤ S): *)
(*   f ∘ (g ∘ h) = (f ∘ g) ∘ h. *)
(* Proof. reflexivity. Qed. *)

Quote Definition q_nat_obj := nat_obj.
Quote Definition q_nat_hom := nat_hom.
Quote Definition q_id_nat_hom := id_nat_hom.
Quote Definition q_nat_comp := nat_comp.

Definition nat_cat : category :=
  mkCat q_nat_obj q_nat_hom q_id_nat_hom q_nat_comp.


(* The definition of [later] operator *)

Quote Definition qTypeConstr := (Type -> Type).

Check translate_type.
Quote Recursively Definition q_def := nat_hom.
Definition g_ctx := fst q_def.

Definition tr_TypeConstr_syn :=
  Eval vm_compute in
    translate_type true None nil nat_cat
                   {| Environ.env_globals := g_ctx|}
                   tt qTypeConstr.

Import ListNotations.

Make Definition gArrowTypeType := Eval vm_compute in (snd tr_TypeConstr_syn).

Arguments nat_comp {_ _ _}.

Definition later : gArrowTypeType.
Proof.
  unfold gArrowTypeType.
  intros p T q f.
  destruct q.
  - apply unit.
  - apply (T q (sle_Sn q ∘ f) q (# _)).
Defined.
