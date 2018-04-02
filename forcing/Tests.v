(* Some sanity tests for several definitions. We test agaist the tranlation acquired from the OCaml
 forcing translation plugin (up to notation) *)
Require Import Template.monad_utils Template.Ast
        Template.Template Template.LiftSubst.
Require Import String PeanoNat.
Require Import Forcing.TemplateForcing.

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

(*A translation of [fun (x : Type) => x] from the original plugin *)
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


(* Translation of [(fun (A B : Type)  => A -> B)] from the original plugin*)
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