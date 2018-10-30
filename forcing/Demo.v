Require Import Template.monad_utils Template.Ast Template.AstUtils
        Template.Template Template.LiftSubst.
Require Import Forcing.TemplateForcing.
Require Import Forcing.translation_utils.
Require Import List.
Require Import Template.Typing.


(* To be able to work with values in SProp we define boxing/unboxing *)
Inductive sBox (A : SProp) : Prop := sbox : A -> sBox A.

Definition ubox {A : SProp} (bA : sBox A) : A :=
  match bA with
    sbox _ X => X
  end.


Inductive sle : nat -> nat -> SProp :=
  sle_0 : forall n, sle 0 n
| sle_S : forall n m : nat, sle n m -> sle (S n) (S m).

Inductive sFalse : SProp :=.

Inductive sTrue : SProp := I.

Definition sle_refl (n : nat) : sle n n.
Proof.
  induction n;constructor;auto.
Qed.

Lemma sle_Sn_0 : forall n, sle (S n) 0 -> sFalse.
Proof.
  unfold Hom; intros n H.
  inversion H.
Qed.

Definition sle_Sn (n : nat) : sle n (S n).
Proof.
  induction n; constructor; auto.
Qed.


Definition sle_trans {n m p} (H : sle n m) (H': sle m  p) : sle n p.
Proof.
  revert H'. revert p. induction H.
  - intros p H'. apply sle_0.
  - intros p H'. inversion H'.
    apply ubox. subst. apply sbox.
    apply sle_S. apply IHsle;auto.
Qed.

(* A category of forcing conditions *)
(* NOTE: we define ℕop *)

Definition nat_obj : Type := nat.
Definition nat_hom (P Q : nat_obj): SProp := sle Q P.
Notation "P ≥ Q" := (nat_hom P Q) (at level 70).

Definition nat_id_hom (P : nat_obj) : P ≥ P := sle_refl P.
Notation "# R" := (nat_id_hom R) (at level 70).

Definition nat_comp (A B C : nat_obj) (g : B ≥ C) (f : A ≥ B) : A ≥ C
  := sle_trans  g f.

Notation "g ∘ f" := (nat_comp _ _ _ g f) (at level 40).

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
Quote Definition q_id_nat_hom := nat_id_hom.
Quote Definition q_nat_comp := nat_comp.


(** A category of nat with the ordering *)
Definition nat_cat : category :=
  mkCat q_nat_obj q_nat_hom q_id_nat_hom q_nat_comp.

(** An instance for the monad *)
Instance GuardRec : Translation := ForcingTranslation nat_cat.

Import ListNotations.
Import MonadNotation.
Open Scope string_scope.

Set Printing Universes.

Check SProp.

Inductive s_and (A B : SProp) : SProp :=  conj : A -> B -> s_and A B.

Check (forall p : SProp, s_and p p).

Check (forall p : Type, prod p p).

(* Initial context *)
Run TemplateProgram (prg <- tmQuoteRec nat_hom ;;
                     tmDefinition "g_ctx" (fst prg)).
Definition ΣE : tsl_context:= (reconstruct_global_context g_ctx,[]).

Definition tTranslateTy {tsl : Translation} (ΣE : tsl_context)
           (id : ident) (A : Type)
  : TemplateMonad (tsl_context) :=
  tA <- tmQuote A ;;
  tA' <- tmEval lazy (tsl_ty ΣE tA) ;;
  match tA' with
  | Error e => print_nf e ;; fail_nf ("Translation error during the translation of the type of " ++ id)
  | Success tA' =>
      id' <- tmEval all (tsl_id id) ;;
      A' <- tmUnquoteTyped Type tA' ;;


Run TemplateProgram (tTranslateTy ΣE "later_type" (Type->Type)).

Run TemplateProgram (tImplementTC ΣE "later_TC" "later" (Type->Type)).
Next Obligation.
  destruct p0.
  - exact unit.
  - exact (X p0 (sle_Sn p0 ∘ H) p0 (# _)).
Defined.

Print later.
Print laterᵗ_obligation_1.