(* Formalisation of Guarded Recursive Types using the cbn forcing translation in Template Coq
   with the ordered set of natural numbers as forcing conditions *)

Require Import String.
Require Import Forcing.TemplateForcing.

Open Scope string.

(** Yoneda embedding  *)
Definition nat_obj := nat.
Definition nat_hom := (fun (P Q : nat_obj) => forall R, Q <= R -> P <= R).
Definition id_nat_hom (P : nat_obj) := (fun (R : nat_obj) (k : P <= R) => k).
Definition nat_comp (P Q R : nat_obj) (g : nat_hom Q R) (f : nat_hom P Q)
  := (fun (S : nat_obj) (k : R <= S) => f S (g S k)).

Notation "P ≤ Q" := (nat_hom P Q) (at level 70).
Notation "#" := id_nat_hom.
Notation "f ∘ g" := (fun (R : nat_obj) (k : _ <= R) => f R (g R k)) (at level 40).

(* Now, laws hold definitionally *)
Lemma nat_cat_left_id P R (g : R ≤ P)  : (id_nat_hom R) ∘ g = g.
Proof. reflexivity. Qed.

Lemma nat_cat_right_id P R (f : P ≤ R)  : f ∘ (id_nat_hom R) = f.
Proof. reflexivity. Qed.

Lemma nat_cat_assoc P Q R S (f : P ≤ Q) (g : Q ≤ R) (h : R ≤ S):
  f ∘ (g ∘ h) = (f ∘ g) ∘ h.
Proof. reflexivity. Qed.

Definition nat_cat : category :=
  makeCat "nat_obj" "nat_hom" "id_nat_hom" "nat_comp".

(** Copied from the template coq demo *)

(** This is just printing **)
Test Quote (fun x : nat => x * x).

Test Quote (fun (f : nat -> nat) (x : nat) => f x).

Test Quote (let x := 2 in x).

Test Quote (let x := 2 in
            match x with
              | 0 => 0
              | S n => n
            end).

(** Build a definition **)
Definition d : Ast.term.
  let t := constr:(fun x : nat => x) in
  let k x := refine x in
  quote_term t k.
Defined.

Print d.

(** Another way **)
Quote Definition d' := (fun x : nat => x).

(** To quote existing definitions **)
Definition id_nat : nat -> nat := fun x => x.

Quote Definition d'' := Eval compute in id_nat.

Print d''.