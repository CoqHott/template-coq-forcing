Require Import Template.monad_utils Template.Ast
        Template.Template Template.LiftSubst.
Require Import String PeanoNat.
Require Import Template.Checker.
Require Import Template.Typing.

Require Import Forcing.TemplateForcing.
Require Import Forcing.translation_utils.
Require Import List.

Import ListNotations.
Import MonadNotation.
Open Scope string_scope.

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

Inductive sFalse : SProp :=.

Inductive sTrue : SProp := I.

Inductive sle : nat -> nat -> SProp :=
  sle_0 : forall n, sle 0 n
| sle_S : forall n m : nat, sle n m -> sle (S n) (S m).

(* TODO: try this definition instead *)
Fixpoint sle_fun (n m : nat) : SProp :=
  match n,m with
  | 0,_ => sTrue
  | S n, S m => sle_fun n m
  | S m, 0 => sFalse
  end.

Definition sle_refl (n : nat) : sle n n.
Proof.
  induction n;constructor;auto.
Defined.

Definition sle_Sn_Sm {n m} : sle (S n) (S m) -> sle n m.
Proof.
  intros H.
  inversion H. apply ubox. subst. apply sbox. exact H2.
Defined.

Definition sle_n_m_S {n m} : sle n m -> sle (S n) (S m).
Proof.
  intros H. constructor;exact H.
Defined.

Lemma sle_Sn_0 : forall n, sle (S n) 0 -> sFalse.
Proof.
  unfold Hom; intros n H.
  inversion H.
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
Quote Definition q_id_nat_hom := id_nat_hom.
Quote Definition q_nat_comp := nat_comp.

Definition nat_cat : category :=
  mkCat q_nat_obj q_nat_hom q_id_nat_hom q_nat_comp.

(* The definition of [later] operator *)

Definition f_translate (cat : category) (tsl_ctx : tsl_context) (trm : term)
  : tsl_result term :=
  Success (snd (translate true None
                          (snd tsl_ctx)
                          cat
                          ({| Environ.env_globals := (fst (fst tsl_ctx)) |})
                          tt
                          trm)).

Definition f_translate_type (cat : category) (tsl_ctx : tsl_context) (trm : term)
  : tsl_result term :=
  Success (snd (translate_type true None
                               (snd tsl_ctx)
                               cat
                               ({| Environ.env_globals := (fst (fst tsl_ctx)) |})
                               tt
                               trm)).

Definition ForcingTranslation (cat : category) : Translation :=
  {| tsl_id := tsl_ident;
     tsl_tm := f_translate cat;
     tsl_ty := f_translate_type cat;
     tsl_ind := fun _ _ _ _ => Error TranslationNotHandeled;
     (* tsl_context -> kername -> kername -> mutual_inductive_body *)
     (*             -> tsl_result (tsl_table * list mutual_inductive_body) *)
  |}.

Definition add_translation (ctx : tsl_context) (e : global_reference * term): tsl_context :=
  let (Σ, E) := ctx in
  (Σ, e :: E).

Instance GuardRec : Translation := ForcingTranslation nat_cat.

(* Building required context to pass to the tranlation *)

Run TemplateProgram (prg <- tmQuoteRec nat_hom ;;
                     tmDefinition "g_ctx" (fst prg)).
Definition ΣE : tsl_context:= (reconstruct_global_context g_ctx,[]).


Run TemplateProgram (tImplementTC ΣE "later_TC" "later" (Type->Type)).
Next Obligation.
  destruct p0.
  - apply unit.
  - apply (X p0 (sle_Sn p0 ∘ H) p0 (# _)).
Defined.

Notation "⊳ A" := (later A) (at level 40).

Run TemplateProgram
    (tImplementTC later_TC "later_app_TC" "later_app"
                 (forall A B (t : ⊳ (A -> B)) (u : ⊳ A), ⊳ B)).
Next Obligation.
  destruct p.
  - cbv. exact tt.
  - refine (X (S p) (# _) _). intros q β.
    refine (X0 (S q) (sle_n_m_S β)).
Defined.
Notation "t ⊙ u" := (later_app _ _ t u) (at level 40).

Run TemplateProgram
    (tImplementTC later_app_TC "nextp_TC" "nextp" (forall {T:Type}, T -> ⊳ T)).
Next Obligation.
  destruct p.
  - exact tt.
  - simpl. refine (X p _).
Defined.

Arguments functional_extensionality_dep {_ _} _ _ _.

(* We copy translated definitions of [eq] generated by the OCaml
   forcing plugin, because inducives are not supported yet by the
   template-coq forcing translation *)
Inductive eqᵗ (p : nat_obj) (A : forall p0 : nat_obj, p ≥ p0 -> forall p : nat_obj, p0 ≥ p -> Type)
(x : forall (p0 : nat_obj) (α : p ≥ p0), A p0 (α ∘ (# _)) p0 (# _))
  : (forall (p0 : nat_obj) (α : p ≥ p0), A p0 ((# _) ∘ (α ∘ (# _))) p0 (# _)) -> Type :=
  eq_reflᵗ : eqᵗ p A x x.


(* We use this trick with η-expanded version of application of [eq] to
   be able to use existing translations.  If we just lest plain [eq],
   the application would be of a special kind (of inductive type) and
   it is translated differently, not as an ordinary application of a
   global constant *)
Definition eq_f {A: Type} (a b : A) := a = b.

Definition eq_fᵗ := fun (p : nat_obj) (A : forall p0 : nat_obj, p ≥ p0 -> forall p1 : nat_obj, p0 ≥ p1 -> Type)
  (a b : forall (p0 : nat_obj) (α : p ≥ p0), A p0 (α ∘ (# _)) p0 (# _)) (p0 : nat_obj)
  (α : p ≥ p0) =>
eqᵗ p0
  (fun (p1 : nat_obj) (α0 : p0 ≥ p1) =>
   (fun (p2 : nat_obj) (α1 : p ≥ p2) => A p2 (α1 ∘ (# _))) p1 ((# _) ∘ (α0 ∘ α)))
  (fun (p1 : nat_obj) (α0 : p0 ≥ p1) =>
   (fun (p2 : nat_obj) (α1 : p ≥ p2) => a p2 (α1 ∘ (# _))) p1 ((# _) ∘ (α0 ∘ α)))
  (fun (p1 : nat_obj) (α0 : p0 ≥ p1) =>
     (fun (p2 : nat_obj) (α1 : p ≥ p2) => b p2 (α1 ∘ (# _))) p1 ((# _) ∘ (α0 ∘ α))).


(* This definition will fail if we leave the type of [A] implicit. *)
Definition eq_is_eq :
  forall p (A : forall x : nat_obj, p ≥ x -> forall x1 : nat_obj, x ≥ x1 -> Type)
         (x y: forall p0 (f:p ≥ p0), A p0 f p0 (# _)),
    eq x y -> eqᵗ p _ x y.
Proof.
  intros. rewrite H. apply eq_reflᵗ.
Qed.

(* Smaller example where we get "Bad relevance" if types of some variables left out *)
Run TemplateProgram (tTranslateTm nextp_TC "TypeT" Type).
Definition blah1 : forall (x y :nat) f,
    eq x y ->  TypeTᵗ x y f -> TypeTᵗ x x (# _).
Proof.
  (* Fails with the error "Bad relevance" *)
Abort.

Definition ctx_with_eq := add_translation nextp_TC (ConstRef "Top.eq_f", tConst "eq_fᵗ" []).

Run TemplateProgram
    (tImplement ctx_with_eq "next_id"
                (forall (A : Type) (u : ⊳ A),
                    eq_f (nextp _ (fun (x : A) => x) ⊙ u) u)).
Next Obligation.
  apply eq_is_eq.
  apply functional_extensionality_dep.
  intros q. destruct q.
  + simpl. destruct (u 0 (sle_0 p)). reflexivity.
  + reflexivity.
Defined.

Run TemplateProgram (tImplementTC later_TC "box_TC" "Box" (Type->Type)).
Next Obligation.
  exact (forall p1 (α0 : p0 ≥ p1), X p1 (α0 ∘ H) p1 (# _)).
Defined.

Notation "□ A" := (Box A) (at level 40).

Arguments sle_trans {_ _ _}.

Lemma sle_Sn_m {n m} : sle n m -> sle n (S m).
Proof.
  intros H. destruct n.
  - constructor.
  - constructor;auto. assert (H1 : sle n (S n)) by apply sle_Sn.
    exact (sle_trans H1 H ).
Defined.

Run TemplateProgram
    (tImplement box_TC "fixp_"
                (forall (T:Type), ((⊳ T) ->  T) -> □ T)).
Next Obligation.
  revert X. revert T.
  induction p; intros T f q α; apply f; intros q0 α0.
  - destruct q0.
    + simpl. exact tt.
    + simpl. pose (sle_Sn_0 _ (α0 ∘ α )) as s. inversion s.
  - simpl. destruct q0.
    + simpl. exact tt.
    + simpl.
      simple refine (let T' := _ :
        forall p0 : nat_obj, p ≥ p0 -> forall p1 : nat_obj, p0 ≥ p1 -> Type in _).
      {intros p0 α0' p1 α1. exact (T p0 (sle_Sn_m α0') p1 α1). }
      unfold Boxᵗ,Boxᵗ_obligation_1 in *.
      refine (IHp T' _ q0 (sle_Sn_Sm (α0 ∘ α))).
      intros q1 α1 x. subst T'. simpl.
      pose (f q1 (sle_Sn_m α1)) as f'. apply f'.
      assert (H := f q1 (sle_Sn_m α1)).
      intros.
      exact (x p1 α2).
      (* Not accepded because of "Bad relevance" *)
Abort.
