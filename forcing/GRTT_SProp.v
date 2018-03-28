Require Import Template.monad_utils Template.Ast
        Template.Template Template.LiftSubst.
Require Import String PeanoNat.
Require Import Template.Checker.
Require Import Template.Typing.
Require Import Forcing.TemplateForcing.
Require Import List.

(* Some axioms *)
Require Import FunctionalExtensionality.

(* To be able to work with values in SProp we define boxing/unboxing *)
Inductive sBox (A : SProp) : Prop := sbox : A -> sBox A.

Definition ubox {A : SProp} (bA : sBox A) : A :=
  match bA with
    sbox _ X => X
  end.

(* All attempts use [rewrite] or [subst] fail, because [eq_sind_r] is not defined.
   We define it, but for some reason the tactics still complain about [eq_sind_r] *)
Definition eq_sind_r : forall (A : Type) (x : A) (P : A -> SProp),
    P x -> forall y : A, y = x -> P y.
Proof.
  intros A x P H y Heq. apply ubox. subst. apply sbox. exact H.
Defined.

Inductive sle : nat -> nat -> SProp :=
  sle_0 : forall n, sle 0 n
| sle_S : forall n m : nat, sle n m -> sle (S n) (S m).

Definition sle_refl (n : nat) : sle n n.
Proof.
  induction n;constructor;auto.
Defined.

Definition sle_S_eq {n m} : sle (S n) (S m) -> sle n m.
Proof.
  intros H.
  inversion H. apply ubox. subst. apply sbox. exact H2.
Defined.

Definition sle_trans n m p (H : sle n m) (H': sle m  p) : sle n p.
Proof.
  revert H'. revert p. induction H.
  - intros p H'. apply sle_0.
  - intros p H'. inversion H'. apply ubox. subst. apply sbox. apply sle_S. apply IHsle;auto.
Defined.

(* This does not work, fails with the error:
   Fixpoints on proof irrelevant inductive types should produce proof irrelevant
   values.*)
Fixpoint sle_trans' n m p (H : sle n m) (H': sle m  p) {struct H} : sle n p.
Proof.
  destruct H. apply sle_0.
  inversion H'. apply ubox. subst. apply sbox. apply sle_S. exact (sle_trans _ _ _ H H1).
Abort.

Definition sle_Sn (n : nat) : sle n (S n).
Proof.
  induction n; constructor; auto.
Defined.

Definition nat_obj : Type := nat.
Definition nat_hom (P Q : nat_obj): SProp := sle Q P.
Notation "P ≥ Q" := (nat_hom P Q) (at level 70).

Definition id_nat_hom (P : nat_obj) : P ≥ P := sle_refl P.
Notation "# R" := (id_nat_hom R) (at level 70).

Definition nat_comp (A B C : nat_obj) (g : B ≥ C) (f : A ≥ B) : nat_hom A C
  := sle_trans _ _ _ g f.
Notation "f ∘ g" := (nat_comp _ _ _ f g) (at level 40).

Arguments sbox {_}.

(* Now, laws hold definitionally, thanks to SProp *)
(* We use sbox'ed version to prove this *)
Lemma nat_cat_left_id P R (g : R ≥ P)  : sbox (g ∘ (# _)) = sbox g.
Proof. reflexivity. Qed.

Lemma nat_cat_right_id P R (f : P ≥ R)  : sbox (f ∘ (# _)) = sbox f.
Proof. reflexivity. Qed.

Lemma nat_cat_assoc P Q R S (f : S ≥ Q) (g : R ≥ S) (h : P ≥ R):
  sbox (f ∘ (g ∘ h)) = sbox ((f ∘ g) ∘ h).
Proof. reflexivity. Qed.

Quote Definition q_nat_obj := nat_obj.
Quote Definition q_nat_hom := nat_hom.
Quote Definition q_id_nat_hom := id_nat_hom.
Quote Definition q_nat_comp := nat_comp.

Definition nat_cat : category :=
  mkCat q_nat_obj q_nat_hom q_id_nat_hom q_nat_comp.

(* The definition of [later] operator *)

(* Building required context to pass to the tranlation
   Maybe, we should try to use the template monad here *)


Quote Recursively Definition q_def := nat_hom.
Definition g_ctx := fst q_def.

Quote Definition qTypeConstr := (Type -> Type).

Definition tr_TypeConstr_syn :=
  Eval vm_compute in
    translate_type true None nil nat_cat
                   {| Environ.env_globals := g_ctx|}
                   tt qTypeConstr.

Import ListNotations.

Make Definition gTypeConstr := Eval vm_compute in (snd tr_TypeConstr_syn).

Arguments nat_comp {_ _ _}.

Definition later : gTypeConstr.
Proof.
  unfold gTypeConstr.
  intros p T q f.
  destruct q.
  - apply unit.
  - apply (T q (sle_Sn q ∘ f) q (# _)).
Defined.

Quote Definition qType := Type.

Definition tr_Type_syn :=
  Eval vm_compute in
    translate_type true None nil nat_cat
                   {| Environ.env_globals := g_ctx|}
                   tt qType.

Make Definition gType := Eval vm_compute in (snd tr_Type_syn).

Definition later_type (A : gType) : gType
  := fun p q α => later p (fun p' _ q' => A p' q') q α.

Notation "⊳ A" := (later_type A) (at level 40).

Quote Definition qId := (fun (A : Type) => A).

Definition tr_Arr_syn :=
  Eval vm_compute in
    translate true None nil nat_cat
                   {| Environ.env_globals := g_ctx|}
                   tt qId.

(*A translation of [fun (x : Type) => x] from the original plugin *)
Definition fooᶠ  : forall p : nat_obj,
    (forall p0 : nat_obj, p ≥ p0 -> forall p1 : nat_obj, p0 ≥ p1 -> Type) ->
    forall p0 : nat_obj, p ≥ p0 -> Type
  := (fun (p : nat_obj) (x : forall p0 : nat_obj, p ≥ p0 -> forall p1 : nat_obj, p0 ≥ p1 -> Type) => x p (# _)).

Make Definition gId :=
  Eval vm_compute in (snd tr_Arr_syn).

Lemma eq_gId_fooᶠ : gId = fooᶠ.
Proof. reflexivity. Qed.

(* Definition later_app : forall A B (t : ⊳ (A -> B)) (u : ⊳ A), ⊳ B. *)