Require Import Template.All.
Require Import List.
Require Import Template.Ast.
Require Import String.

Open Scope string_scope.


(* Taken from the template-coq parametricity translation *)

Definition tsl_table := list (global_reference * term).

Fixpoint lookup_tsl_table (E : tsl_table) (gr : global_reference)
  : option term :=
  match E with
  | nil => None
  | hd :: tl =>
    if gref_eq_dec gr (fst hd) then Some (snd hd)
    else lookup_tsl_table tl gr
  end.

Definition default_term := tVar "constant_not_found".

Definition lookup_default (E : tsl_table) (gr : global_reference)
  : term :=
  match (lookup_tsl_table E gr) with
  | None => match gr with
            | ConstRef n => tVar ("Not_found_" ++ n)
            | _ => default_term
            end
  | Some t => t
  end.

Import ListNotations.

(* Partly taken from Template.Typing *)
Fixpoint it_mkLambda_or_LetIn (t : term) (l : context) :=
  List.fold_left
    (fun acc d =>
       match d.(decl_body) with
       | None => tLambda d.(decl_name) d.(decl_relevance) d.(decl_type) acc
       | Some b => tLetIn d.(decl_name) d.(decl_relevance) b d.(decl_type) acc
       end) l t.

Fixpoint it_mkProd_or_LetIn (t : term) (l : context) :=
  List.fold_left
    (fun acc d =>
       match d.(decl_body) with
       | None => tProd d.(decl_name) d.(decl_relevance) d.(decl_type) acc
       | Some b => tLetIn d.(decl_name) d.(decl_relevance) b d.(decl_type) acc
       end) l t.

Fixpoint fold_map_internal {A B C : Type} (f : A -> B -> A * C) (a : A)
         (cs : list C) (bs : list B) : A * (list C)
  := match bs with
     | [] => (a, rev cs)
     | hd :: tl => let (a_, c_) := f a hd in fold_map_internal f a_ (c_ :: cs) tl
     end.

Definition fold_map {A B C : Type} (f : A -> B -> A * C) (a : A)
           (bs : list B) : A * (list C) := fold_map_internal f a [] bs.

Fixpoint fold_map' {A B C : Type} (f : A -> B -> A * C) (a : A)
         (bs : list B) : A * (list C)
  := match bs with
     | [] => (a, [])
     | hd :: tl => let (a_, c_) := f a hd in
                   let (a__, cs) := fold_map' f a_ tl in
                   (a__, c_ :: cs)
     end.

Example ex_fold_map : fold_map (fun x y => (x+y, y+1)) 0 [1;2;3] = (6,[2;3;4]).
reflexivity.
Qed.

Example ex_fold_map_fold_map' :
  fold_map (fun x y => (x+y, y+1)) 0 [1;2;3] = fold_map' (fun x y => (x+y, y+1)) 0 [1;2;3].
reflexivity.
Qed.