(* Some sanity tests for several definitions. We test agaist the tranlation acquired from the OCaml
 forcing translation plugin (up to notation) *)
Require Import Template.monad_utils Template.Ast
        Template.Template Template.LiftSubst translation_utils.
Require Import String PeanoNat.
Require Import Forcing.TemplateForcing.

Import List.ListNotations.
Import MonadNotation.
Open Scope string_scope.
Open Scope list_scope.

Import Level.

(* Some examples to play with  *)
Definition Obj := Type.
Definition Hom := (fun x y => x -> y).
Notation "P ≥ Q" := (Hom P Q) (at level 70).

Definition Id_hom := @id.
Notation "# R" := (Id_hom R) (at level 70).

Definition Comp := @Coq.Program.Basics.compose.
Notation "g ∘ f" := (Comp _ _ _ g f) (at level 40).

Definition test_cat : category :=
  makeCatS "Obj" "Hom" "Id_hom" "Comp".


Quote Recursively Definition q_def := Hom.
Definition g_ctx := fst q_def.


Quote Definition qId := (fun (A : Type) => A).

Definition tr_Id_syn :=
  Eval vm_compute in
    translate true None nil test_cat
                   {| Environ.env_globals := g_ctx|}
                   tt qId.

(*A translation of [fun (x : Type) => x] from the OCaml plugin *)
Definition fooᶠ  : forall p : Obj,
    (forall p0 : Obj, p ≥ p0 -> forall p1 : Obj, p0 ≥ p1 -> Type) ->
    forall p0 : Obj, p ≥ p0 -> Type
  := (fun (p : Obj) (x : forall p0 : Obj, p ≥ p0 -> forall p1 : Obj, p0 ≥ p1 -> Type) => x p (# _)).

Make Definition gId :=
  Eval vm_compute in (snd tr_Id_syn).

Lemma eq_gId_fooᶠ : gId = fooᶠ.
Proof. reflexivity. Qed.


Quote Definition qArr := (fun (A B : Type)  => A -> B).

Definition tr_Arr_syn :=
  Eval vm_compute in
    translate true None nil test_cat
                   {| Environ.env_globals := g_ctx|}
                   tt qArr.


(* Translation of [(fun (A B : Type)  => A -> B)] from the OCaml plugin*)
Definition barᶠ : forall p : Obj,
    (forall p0 : Obj, p ≥ p0 -> forall p1 : Obj, p0 ≥ p1 -> Type) ->
    (forall p0 : Obj, p ≥ p0 -> forall p1 : Obj, p0 ≥ p1 -> Type) ->
    forall p0 : Obj, p ≥ p0 -> Type
  := fun (p : Obj) (A B : forall p0 : Obj, p ≥ p0 -> forall p1 : Obj, p0 ≥ p1 -> Type)
         (p0 : Obj) (α : p ≥ p0) =>
       (forall (p1 : Obj) (α0 : p0 ≥ p1), A p1 ((# _) ∘ (α0 ∘ α)) p1 (# _)) -> B p0 (α ∘ (# _)) p0 (# _).

Make Definition bar := Eval vm_compute in (snd tr_Arr_syn).

Lemma eq_bar_barᶠ : bar = barᶠ.
Proof.
  reflexivity.
Qed.

Quote Definition bazz :=  (forall (A : Type), (A -> Type)).

Definition tr_bazz_syn :=
  Eval vm_compute in
    translate_type true None nil test_cat
                   {| Environ.env_globals := g_ctx|}
                   tt bazz.

(* Just testing that the definition can be reflected back from quoted. This covers a bug with
   top-level condition variable when building a chain of moprhisms by composition *)
Make Definition bazz' := Eval vm_compute in (snd tr_bazz_syn).


(* Testing appication of type constructors *)

Inductive prodᵗ (p : Obj)
            (A : forall p0 : Obj, p ≥ p0 -> forall p : Obj, p0 ≥ p -> Type)
            (B : forall p0 : Obj, p ≥ p0 -> forall p : Obj, p0 ≥ p -> Type)
  : Type :=
    pairᵗ : (forall (p0 : Obj) (α : p ≥ p0), A p0 α p0 (# _)) ->
            (forall (p0 : Obj) (α : p ≥ p0), B p0 α p0 (# _)) -> prodᵗ p A B.

(* translation of [fun (A B : Type) => prod A B] from the OCaml plugin *)
Definition prod_app_t :=
    fun (p : Obj) (A B : forall p0 : Obj, p≥ p0 -> forall p1 : Obj, p0≥ p1 -> Type)
        (p0 : Obj) (α : p≥ p0) =>
      prodᵗ p0
            (fun (p1 : Obj) (α0 : p0≥ p1) =>
               (fun (p2 : Obj) (α1 : p≥ p2) => A p2 α1) p1 (α0 ∘ α))
            (fun (p1 : Obj) (α0 : p0≥ p1) =>
               (fun (p2 : Obj) (α1 : p≥ p2) => B p2 α1) p1 (α0 ∘ α)).

Instance TestTranslation : Translation := ForcingTranslation test_cat.

Definition ΣE : tsl_context:= (Typing.reconstruct_global_context [],[]).

Run TemplateProgram (TC <- tAddExistingInd ΣE "Coq.Init.Datatypes.prod" "prodᵗ" ;;
                          tmDefinition "ctx_with_prod" TC).

Definition prod_ := (fun (A B : Type) => prod A B).

Run TemplateProgram (tTranslate ctx_with_prod "prod_").

Lemma prod_tr_eq : prod_ᵗ = prod_app_t.
Proof. reflexivity. Qed.