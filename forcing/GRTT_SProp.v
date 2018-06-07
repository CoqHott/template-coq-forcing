Require Import Template.monad_utils Template.Ast Template.AstUtils
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


(* To be able to work with values in SProp we define boxing/unboxing *)
Inductive sBox (A : SProp) : Prop := sbox : A -> sBox A.

Definition ubox {A : SProp} (bA : sBox A) : A :=
  match bA with
    sbox _ X => X
  end.

Definition fn_out_sbox (P : SProp) (A : Type) (f : P -> A) : sBox P -> A
  := fun x => f (ubox x).

Definition fn_out_sbox_dep (P : SProp) (A : P -> Type) (f : forall (p : P), A p)
  : forall (q : sBox P), A (ubox q) := fun x => f (ubox x).

(* Some axioms *)

Axiom functional_extensionality_dep :
  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
    (forall x : A, f x = g x) -> f = g.

Arguments functional_extensionality_dep {_ _} _ _ _.

(* Now we can prove the version of funext with the first type being SProp - thanks, Gaëtan! *)
Lemma functional_extensionality_dep_s :
  forall (A : SProp) (B : A -> Type) (f g : forall x : A, B x), (forall x : A, f x = g x) -> f = g.
Proof.
  intros A B f g H.
  pose (fn_out_sbox_dep _ _ f) as f'.
  pose (fn_out_sbox_dep _ _ g) as g'.
  assert (H' : f' = g').
  { apply functional_extensionality_dep. intros [x]. apply (H x). }
  (* we precompose each side with [sbox] and use the fact that composition [ubox ∘ sbox] is [id]  *)
  pose (fun (f : forall q : sBox A, B (ubox q)) (x : A) => (f (sbox _ x))) as d.
  apply f_equal with (f:=d) in H'. subst d. apply H'.
Qed.

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
Qed.

Definition sle_Sn_Sm {n m} : sle (S n) (S m) -> sle n m.
Proof.
  intros H.
  inversion H. apply ubox. subst. apply sbox. exact H2.
Qed.

Definition sle_n_m_S {n m} : sle n m -> sle (S n) (S m).
Proof.
  intros H. constructor;exact H.
Qed.

Lemma sle_Sn_0 : forall n, sle (S n) 0 -> sFalse.
Proof.
  unfold Hom; intros n H.
  inversion H.
Qed.

Definition sle_trans n m p (H : sle n m) (H': sle m  p) : sle n p.
Proof.
  revert H'. revert p. induction H.
  - intros p H'. apply sle_0.
  - intros p H'. inversion H'. apply ubox. subst. apply sbox. apply sle_S. apply IHsle;auto.
Qed.

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
Qed.

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


(** A category of nat with the ordering *)
Definition nat_cat : category :=
  mkCat q_nat_obj q_nat_hom q_id_nat_hom q_nat_comp.

Instance GuardRec : Translation := ForcingTranslation nat_cat.

(* Building required context to pass to the translation *)

Run TemplateProgram (prg <- tmQuoteRec nat_hom ;;
                     tmDefinition "g_ctx" (fst prg)).
Definition ΣE : tsl_context:= (reconstruct_global_context g_ctx,[]).


(* We use modules for namespacing, because Template Coq doesn't work well with sections *)
Module Later.
  (** The definition of [later] operator *)
  Run TemplateProgram (tImplementTC ΣE "later_TC" "later" (Type->Type)).
  Next Obligation.
    destruct p0.
    - apply unit.
    - apply (X p0 (sle_Sn p0 ∘ H) p0 (# _)).
  Defined.

  Notation "⊳ A" := (later A) (at level 40).

  (* Iterated version of later *)
  Fixpoint nlater (n : nat) (A : Type) : Type :=
    match n with
    | O => A
    | S m => ⊳ (nlater m A)
    end.

  Notation "'⊳[' n ']' A" := (nlater n A) (at level 40).

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

  Run TemplateProgram
      (tImplementTC later_app_TC "later_unapp_TC" "later_unapp"
                   (forall A B (t : ⊳ A -> ⊳ B), A -> B)).
  Next Obligation.
  Admitted.

  Definition later_funct_arrow : forall A B, (A -> B) -> (⊳A -> ⊳B)
    := fun _ _ x => later_app _ _ (nextp _ x).

  Notation "⊳_f f" := (later_funct_arrow _ _ f) (at level 40).


  (* We copy translated definitions of [eq] generated by the OCaml
     forcing plugin, because inducives are not supported yet by the
     template-coq forcing translation *)
  Inductive eqᵗ (p : nat_obj) (A : forall p0 : nat_obj, p ≥ p0 -> forall p : nat_obj, p0 ≥ p -> Type)
  (a : forall (p0 : nat_obj) (α : p ≥ p0), A p0 α p0 (# _))
    : (forall (p0 : nat_obj) (α : p ≥ p0), A p0 α p0 (# _)) -> Type :=
    eq_reflᵗ : eqᵗ p A a a.

  (* TODO: move the definitions realted to [eq] from the [Later] module *)
  (* We use this trick with η-expanded version of application of [eq] to
     be able to use existing translations.  If we just left plain [eq],
     the application would be of a special kind (of inductive type) application and
     it is translated differently, not as an ordinary application of a
     global constant *)
  Definition eq_f {A: Type} (a b : A) := a = b.

  Definition eq_fᵗ := fun (p : nat_obj) (A : forall p0 : nat_obj, p ≥ p0 -> forall p1 : nat_obj, p0 ≥ p1 -> Type)
    (a b : forall (p0 : nat_obj) (α : p ≥ p0), A p0 (α ∘ (# _)) p0 (# _)) (p0 : nat_obj)
    (α : p ≥ p0) =>
  eqᵗ p0
    (fun (p1 : nat_obj) (α0 : p0 ≥ p1) =>
     (fun (p2 : nat_obj) (α1 : p ≥ p2) => A p2 α1) p1 (α0 ∘ α))
    (fun (p1 : nat_obj) (α0 : p0 ≥ p1) =>
       (fun (p2 : nat_obj) (α1 : p ≥ p2) => a p2 α1) p1 (α0 ∘ α))
    (fun (p1 : nat_obj) (α0 : p0 ≥ p1) =>
       (fun (p2 : nat_obj) (α1 : p ≥ p2) => b p2 α1) p1 (α0 ∘ α)).


  Inductive prodᵗ (p : nat_obj)
            (A : forall p0 : nat_obj, p ≥ p0 -> forall p : nat_obj, p0 ≥ p -> Type)
            (B : forall p0 : nat_obj, p ≥ p0 -> forall p : nat_obj, p0 ≥ p -> Type)
  : Type :=
    pairᵗ : (forall (p0 : nat_obj) (α : p ≥ p0), A p0 α p0 (# _)) ->
            (forall (p0 : nat_obj) (α : p ≥ p0), B p0 α p0 (# _)) -> prodᵗ p A B.

  Definition prod_app_t :=
    fun (p : nat_obj) (A B : forall p0 : nat_obj, p≥ p0 -> forall p1 : nat_obj, p0≥ p1 -> Type)
        (p0 : nat_obj) (α : p≥ p0) =>
      prodᵗ p0
            (fun (p1 : nat_obj) (α0 : p0≥ p1) =>
               (fun (p2 : nat_obj) (α1 : p≥ p2) => A p2 α1) p1 (α0 ∘ α))
            (fun (p1 : nat_obj) (α0 : p0≥ p1) =>
               (fun (p2 : nat_obj) (α1 : p≥ p2) => B p2 α1) p1 (α0 ∘ α)).


  Inductive tBox (A : Type) : Type := tbox : A -> tBox A.
  Inductive tBoxᵗ (p : nat_obj) (A : forall p0 : nat_obj, p ≥ p0 -> forall p : nat_obj, p0 ≥ p -> Type) : Type :=
    tboxᶠ : (forall (p0 : nat_obj) (α : p ≥ p0), A p0 α p0 (# _)) -> tBoxᵗ p A.

  Definition tbox_fnᵗ :=
    fun (p : nat_obj) (x : forall p0 : nat_obj, p ≥ p0 -> forall p1 : nat_obj, p0 ≥ p1 -> Type)
        (p0 : nat_obj) (α : p ≥ p0) =>
      tBoxᵗ p0
            (fun (p1 : nat_obj) (α0 : p0 ≥ p1) =>
               (fun (p2 : nat_obj) (α1 : p ≥ p2) => x p2 (α1)) p1 (α0 ∘ α)).

  (* This definition will fail if we leave the type of [A] implicit. *)
  Definition eq_is_eq :
    forall p (A : forall x : nat_obj, p ≥ x -> forall x1 : nat_obj, x ≥ x1 -> Type)
           (x y: forall p0 (f:p ≥ p0), A p0 f p0 (# _)),
      x = y -> eqᵗ p _ x y.
  Proof.
    intros. rewrite H. apply eq_reflᵗ.
  Qed.

   Quote Definition nat_s := nat.

  Eval compute in (subst (tRel 0) 1
                         (tLambda nAnon Relevant nat_s
                           (tLambda nAnon Relevant nat_s (tRel 2)))).

  Quote Definition barr' := (forall {A : Type}, A = A).
  Definition barr := (forall {A : Type}, A = A).

  Run TemplateProgram (TC <- tAddExistingInd nextp_TC "Coq.Init.Logic.eq" "eqᵗ" ;;
                          tmDefinition "ctx_with_eq" TC).

Definition tTranslateDebug {tsl : Translation} (ΣE : tsl_context) (id : ident)
  : TemplateMonad tsl_context :=
  gr <- tmAbout id ;;
  id' <- tmEval all (tsl_id id) ;;
  mp <- tmCurrentModPath tt ;;
  kn' <- tmEval all (mp ++ "." ++ id') ;;
  match gr with
  | None => fail_nf (id ++ " not found")
  | Some (ConstructRef (mkInd kn n) _)
  | Some (IndRef (mkInd kn n)) =>
      d <- tmQuoteInductive id ;;
      d' <- tmEval lazy (tsl_ind ΣE kn kn' d) ;;
      match d' with
      | Error e => print_nf e ;; fail_nf ("Translation error during the translation of the inductive " ++ id)
      | Success (E, decls) =>
        monad_fold_left (fun _ e => tmMkInductive' e) decls tt ;;
        print_nf  (id ++ " has been translated as " ++ id') ;;
        ret (add_global_decl (InductiveDecl kn d) (fst ΣE), E ++ snd ΣE)%list
      end

  | Some (ConstRef kn) =>
    e <- tmQuoteConstant kn true ;;
    match e with
    | ParameterEntry _ => fail_nf (id ++ "is an axiom, not a definition")
    | DefinitionEntry {| definition_entry_type := A;
                         definition_entry_universes := univs;
                         definition_entry_body := t |} =>
      (* ΣE' <- scan_globals t ΣE ;; *)
      t' <- tmEval lazy (tsl_tm ΣE t) ;;
      print_nf t' ;;
      ret ΣE
      (* match t' with *)
      (* | Error e => print_nf e ;; fail_nf ("Translation error during the translation of the body of " ++ id) *)
      (* | Success t' => *)
      (*   tmMkDefinition id' t' ;; *)
      (*   let decl := {| cst_universes := univs; *)
      (*                  cst_type := A; cst_body := Some t |} in *)
      (*   let Σ' := add_global_decl (ConstantDecl kn decl) (fst ΣE) in *)
      (*   let E' := (ConstRef kn, tConst kn' (UContext.instance (repr univs))) :: (snd ΣE) in *)
      (*   print_nf  (id ++ " has been translated as " ++ id') ;; *)
      (*   ret (Σ', E') *)
      (* end *)
    end
  end.

  Run TemplateProgram
      (tImplement ctx_with_eq "next_id"
                  (forall (A : Type) (u : ⊳ A),
                      (nextp _ (fun (x : A) => x) ⊙ u) = u)).
  Next Obligation.
    apply eq_is_eq.
    apply functional_extensionality_dep.
    intros q. destruct q.
    + simpl. destruct (u 0 (sle_0 p)). reflexivity.
    + reflexivity.
  Defined.

  Run TemplateProgram (
        TC <- tTranslate ctx_with_eq "later_funct_arrow" ;;
        tImplementTC TC "nextp_natural_TC" "nextp_natural"
        (forall {A B : Type} (a : A) (f : A -> B), (nextp _ (f a)) = ((⊳_f f) (nextp _ a)))
      ).
  Next Obligation.
    apply eq_is_eq.
    apply functional_extensionality_dep.
    intros q.
    apply functional_extensionality_dep_s.
    intros α.
    destruct q.
    - reflexivity.
    - reflexivity.
  Qed.
End Later.

Import Later.

Run TemplateProgram (tImplementTC ctx_with_eq "box_TC" "Box" (Type->Type)).
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

Definition s_ex_falso (f : sFalse) : forall x, x := sFalse_rect _ f.

Module Fix.

  (* First, we construct a fixpoint going to □ T, this allows us to get
     a more general induction hypothesis *)
  Run TemplateProgram
      (tImplementTC box_TC "fix_TC" "fixp_"
                  (forall (T:Type), ((⊳ T) ->  T) -> □ T)).
  Next Obligation.
    revert X. revert T.
    induction p; intros T f q α; apply f; intros q0 α0.
    - destruct q0.
      + simpl. exact tt.
      + simpl.
        (* [destruct] doen't work here and [inversion] leads to "Bad relevance at the end." *)
        apply (s_ex_falso (sle_Sn_0 q0 (α0 ∘ α))).
    - simpl. destruct q0.
      + simpl. exact tt.
      + simpl.
        simple refine (let T' := _ :
          forall p0 : nat_obj, p ≥ p0 -> forall p1 : nat_obj, p0 ≥ p1 -> Type in _).
        { intros p0 α0' p1 α1. exact (T p0 (sle_Sn_m α0') p1 α1). }
        unfold Boxᵗ,Boxᵗ_obligation_1 in IHp.
        refine (IHp T' _ q0 (sle_Sn_Sm (α0 ∘ α))).
        intros q1 α1 x. subst T'. simpl.
        apply (f q1 (sle_Sn_m α1)).
        intros p1 α2.
        exact (x p1 α2).
  Defined.

  Run TemplateProgram
      (tImplementTC fix_TC "counit_TC" "Box_counit" (forall (A:Type) , □ A -> A)).
  Next Obligation.
    exact (X p (# _) p (# _)).
  Defined.

  Definition fixp : forall {T:Type}, ((⊳ T) ->  T) -> T  :=
    fun T f => Box_counit _ (fixp_ T f).

  Run TemplateProgram (TC <- tTranslate counit_TC "fixp" ;;
                       tmDefinition "fixp_TC" TC).

  Definition happly {A B : Type} (f g : A -> B) : f = g -> forall x, f x = g x.
  Proof.
    intros p x. destruct p. reflexivity.
  Defined.

  Definition happly_dep {A : Type} {P : A -> Type} {f g : forall (a : A), P a}
    : f = g -> forall x, f x = g x.
  Proof.
    intros p x. destruct p. reflexivity.
  Defined.


  Lemma sle_Sn_m' {n m : nat} : sle (S n) m -> sle n m.
  Proof.
    intros. inversion H. apply ubox. subst. apply sbox.
    apply sle_Sn_m. exact H1.
  Qed.

  Run TemplateProgram
      (tImplementTC fixp_TC "unfold_TC" "unfold_fix"
                    (forall A (f: ⊳ A -> A), (fixp f) = (f (nextp _ (fixp f))))).
  Next Obligation.
    unfold fixpᵗ,Box_counitᵗ,Box_counitᵗ_obligation_1.
    (* First, we generalise the statement to make it work with arbitrary p' *)
    assert ( forall p0 (α0 : p ≥ p0) p' (α' : p0 ≥ p'),
     fixp_ᵗ p0
       (fun (p1 : nat_obj) (α : p0 ≥ p1) =>
        A p1 ( α ∘ α0))
       (fun (p1 : nat_obj) (α : p0 ≥ p1) =>
        f p1 (α ∘ α0)) p'  (α': p0 ≥ p') =

     f p' (α' ∘ α0)
       (fun (p1 : nat_obj) (α1 : p' ≥ p1) =>
        nextpᵗ p1
          (fun (p2 : nat_obj) (α2 : p1 ≥ p2) =>
           A p2 (α2 ∘ α1 ∘ α' ∘ α0))
          (fun (p2 : nat_obj) (α2 : p1 ≥ p2) =>
           fixp_ᵗ p2
             (fun (p3 : nat_obj) (α : p2 ≥ p3) =>
              A p3
                (α ∘ α2 ∘ α1 ∘ α' ∘ α0))
             (fun (p3 : nat_obj) (α : p2 ≥ p3) =>
              f p3
                (α ∘ α2 ∘ α1 ∘ α' ∘ α0))
             p2 (# p2)))).
    { induction p.
      - intros p0 α p' α'.
        destruct p0.
        * simpl. apply f_equal.
          apply functional_extensionality_dep.
          intros q.
          destruct q.
          ** reflexivity.
          ** intros. apply functional_extensionality_dep_s. intros α1.
             apply (s_ex_falso (sle_Sn_0 _ (α1 ∘ α'))).
        * apply (s_ex_falso (sle_Sn_0 _ α)).
      - simpl. intros.
        destruct p0.
        * simpl. apply f_equal.
          apply functional_extensionality_dep.
          intros q.
          destruct q.
          ** reflexivity.
          ** intros. apply functional_extensionality_dep_s. intros α1.
             apply (s_ex_falso (sle_Sn_0 _ (α1 ∘ α'))).
        * simpl. apply f_equal.
          apply functional_extensionality_dep.
          intros q.
          destruct q.
          ** reflexivity.
          ** apply functional_extensionality_dep_s. intros α1. simpl.
             simple refine
                    (let A' : forall p0 : nat_obj, p ≥ p0 -> forall p1 : nat_obj, p0 ≥ p1 -> Type := _
                     in _).
             { intros p3 α3 p4 α4. apply (A p3 (sle_Sn_m α3) p4 α4). }
             simple refine (let f' : forall (p0 : nat_obj) (α : p ≥ p0),
                                (forall (p1 : nat_obj) (α0 : p0 ≥ p1),
                                    laterᵗ p1
                                     (fun (p2 : nat_obj) (α1 : p1 ≥ p2) =>
                                     A' p2 (α1 ∘ α0 ∘ α)) p1 (# p1)) ->
                                A' p0  α p0 (# p0) := _ in _).
             { intros p4 α4 X. exact (f p4 (sle_Sn_m α4) X). }
             assert (HH := IHp A' f' p0 (sle_Sn_Sm α0) q (sle_Sn_Sm (α1 ∘ α'))).
             change (  fixp_ᵗ p0
                        (fun (p1 : nat_obj) (α : p0 ≥ p1) => A' p1 (α ∘ sle_Sn_Sm α0))
                        (fun (p1 : nat_obj) (α : p0 ≥ p1) => f' p1 (α ∘ sle_Sn_Sm α0)) q
                                                                 (sle_Sn_Sm (α1 ∘ α'))
                     = fixp_ᵗ q
                        (fun (p3 : nat_obj) (α : q ≥ p3) =>
                          A p3 ((((α ∘ (sle_Sn q)) ∘ α1) ∘ α') ∘ α0))
                        (fun (p3 : nat_obj) (α : q ≥ p3) =>
                           f p3 ((((α ∘ (sle_Sn q)) ∘ α1) ∘ α') ∘ α0)) q (# q)).
             rewrite HH. clear HH.
             symmetry.
             assert (HH' := IHp A' f' q (sle_Sn_Sm (α1 ∘ α' ∘ α0)) q (# _)).
             apply HH'.
    }
    intros.
    unfold eq_fᵗ.
    apply eq_is_eq.
    refine (functional_extensionality_dep _ _ (fun (p0 : nat_obj) => _)).
    exact (@functional_extensionality_dep_s (p ≥ p0) _ _ _  (fun (a : p ≥ p0) => H p0 a p0 (# p0))).
  Qed.

  Run TemplateProgram (tImplementTC unfold_TC "switchp_TC" "switchp" ((⊳ Type) -> Type)).
  Next Obligation.
    destruct p0.
    - exact unit.
    - exact (X (S p0) H p0 (# _)).
  Defined.

  Run TemplateProgram (tImplementTC switchp_TC "switch_next_TC" "switch_next"
                                    (forall (T:Type), (switchp (nextp Type T)) = (⊳ T))).
  Next Obligation. reflexivity. Defined.

  Definition mu : (Type -> Type) -> Type.
    intros f.
    apply fixp.
    apply (fun x => f (switchp x)).
  Defined.

  Definition mu' : (⊳Type -> Type) -> Type
    := fun f => fixp f.

  Run TemplateProgram (TC <- tTranslate switchp_TC "mu" ;;
                       tmDefinition "mu_TC" TC).

  Lemma unfold_mu : forall (f: Type -> Type), (mu f) = (f (⊳ (mu f))).
  Proof.
    intros.
    unfold mu.
    rewrite unfold_fix at 1.
    rewrite switch_next.
    f_equal.
  Defined.
End Fix.

Import Fix.

(* Auxiliary definitions related to equality *)
Definition transport {A : Type} {F : A -> Type} {a b : A} (p : a = b) : F a -> F b.
Proof.
  destruct p. apply id.
Defined.

(** Concatenation of paths *)
Definition path_concat {A : Type} {x y z : A} : x = y -> y = z -> x = z.
  intros p q. destruct p. apply q. Defined.

(** Lemma 2.3.9 in the HoTT book *)
Definition transp_concat {A : Type} {B : A -> Type} {x y z : A} {u : B x}
           (p : x = y) (q : y = z) :
  transport q (transport p u) = transport (path_concat p q) u.
  destruct p. reflexivity. Defined.


Definition ap {A B} (f : A -> B) {x y} : x = y -> f x = f y.
    destruct 1. reflexivity.
Defined.

(* Lemma 2.3.10 in the HoTT book *)
Definition transp_naturality {A B : Type} {C : B -> Type} {x y : A} {f : A -> B}
           {u : C (f x)} (p : x = y) :
  transport (ap f p) u =  @transport _ (fun x => C (f x)) _ _ p u.
  destruct p. reflexivity. Defined.

(* Lemma 2.3.11 in the HoTT book *)
Definition move_transport {A : Type}{F G : A -> Type}(f : forall {a : A}, F a -> G a)
           {a a' : A} (u : F a) (p : a = a') : f (transport p u) = transport p (f u).
  destruct p. reflexivity. Defined.

Definition concat_inv_r {A : Type} {x y : A} (p : x = y) :
  path_concat p (eq_sym p) = eq_refl.
  destruct p. reflexivity. Defined.

Definition concat_inv_l {A : Type} {x y : A} (p : x = y) :
  path_concat (eq_sym p) p = eq_refl.
  destruct p. reflexivity. Defined.


Definition unfoldp (f : Type -> Type) : mu f -> f (⊳ (mu f))
  := @transport _ (fun x => x) _ _ (unfold_mu f).

(* Iterated versions of fold/unfold. They take an additional parameter
   [later_f] allowint to "push" later application from outside to the
   argument, which is crucial for the recursive case. This is not
   always available for arbitrary [f], so this definitions will work
   only for [f] for which it is possible to define such a function *)
Fixpoint nunfold {n} (f : Type -> Type) (later_f : forall A, ⊳ f A -> f (⊳ A))
  : ⊳[n] (mu f) -> f (⊳[1+n] mu f) :=
    match n with
    | O => fun (x : mu f) => unfoldp f x
    | S m => fun (x : ⊳[1+m] (mu f)) => later_f _ ((⊳_f (nunfold f later_f)) x)
    end.

Definition foldp (f : Type -> Type) : f (⊳ (mu f)) -> mu f
  := @transport _ (fun x => x) _ _ (eq_sym (unfold_mu f)).

Lemma fold_unfold_id f a : foldp f (unfoldp f a) = a.
Proof.
  unfold foldp,unfoldp.
  rewrite transp_concat.
  rewrite concat_inv_r.
  reflexivity.
Qed.

Lemma unfold_fold_id f a : unfoldp f (foldp f a) = a.
Proof.
  unfold foldp,unfoldp.
  rewrite transp_concat.
  rewrite concat_inv_l.
  reflexivity.
Qed.

Section UntypedLambda.
  Definition 𝒟 := mu (fun T : Type => T -> T).

  Definition fun_ (f : ⊳𝒟 -> ⊳𝒟) : 𝒟 := foldp (fun T : Type => T -> T) f.

  Definition defun_ (f : 𝒟) : ⊳𝒟 -> ⊳𝒟 := unfoldp (fun T : Type => T -> T) f.

  Definition switchD : ⊳𝒟 -> 𝒟 := fun t => fun_ (fun _ => t).

  Notation "↓ a" := (switchD a) (at level 40).

  Lemma switchD_nextp t : (↓ (nextp _ t)) = t.
  Proof.
    unfold switchD.
    (* Does it hold in the same way as for switchp? *)
  Abort.

  Definition applD  : 𝒟 -> 𝒟 -> 𝒟 := fun f s => ↓ ((defun_ f) (nextp _ s)).

  Notation "t1 @ t2" := (applD t1 t2) (at level 40).

  Definition idD := fun_ (fun x => x).

  Lemma idD_is_id (t : 𝒟) : idD @ t = t.
  Proof.
    unfold idD,applD,defun_,fun_. rewrite unfold_fold_id.
    Abort.

  Definition Ω := fun_ (fun x => nextp _ (↓x @ ↓x)).

  Definition Y' f := fun_ (fun (x : ⊳𝒟) => nextp _ (f @ (↓ x @ ↓ x))).
  Definition Y : 𝒟 := fun_ (fun f => nextp _ (Y' (↓ f) @ (Y' (↓ f)))).

  Lemma Y_unfold : forall f,  (Y @ f) = (f @ (Y' f) @ (Y' f)).
  Proof.
    intros. f_equal.
    unfold Y'. unfold applD,switchD,defun_,fun_.
    unfold Y,fun_.
  Admitted.

End UntypedLambda.