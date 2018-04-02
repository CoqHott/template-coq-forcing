(** Porting the OCaml version of the forcing translation plugin.

    Some notes:
    - the Yoneda embedding is removed from the translation and should be provided by
      the user, if required;
    - porting the OCaml code required to change de Bruijn indices to start from 0,
      and not from 1 as in the Coq's kernel (hopefully, fixed everywhere);
    - only the translation for the negative fragment is supported for now. *)

Require Import List Arith Nat.
Require Import String.
Require Import Template.monad_utils Template.Ast
        Template.Template Template.LiftSubst Template.Checker Template.utils
        Template.AstUtils.
Require Import Forcing.TFUtils.

Import ListNotations MonadNotation.

Local Open Scope string_scope.

Definition list_to_string {A : Type} f (xs : list A) : string
  := (List.fold_left append (List.map (fun i => f i ++ " ") xs) "").

(** We add a composition and an identity as a part of a categorical structe that must
    be provided by a user, since the Yoneda embedding is not a part of
    the plugin anymore (instead, it could be done externally by a
    user) *)

Record category : Type :=
  mkCat { cat_obj : term;
          (** Objects. Must be of type [Type]. *)

          cat_hom : term;
          (** Morphisms. Must be of type [cat_obj -> cat_obj -> Type]. *)

          cat_id : term;
          (** Identity. Must be of the type [forall {a : cat_obj}, cat_hom a a]  *)

          cat_comp : term;
          (** Composition. Must be of the type
              [forall {a b c : cat_obj}, cat_hom b c -> cat_hom a b -> cat_hom a c] *)
        }.

Definition makeCatS (obj hom id_ comp : string) :=
  {| cat_obj := tConst obj [];
     cat_hom := tConst hom [];
     cat_id := tConst id_ [];
     cat_comp := tConst comp [];
  |}.


Quote Definition cat_def := Eval compute in category.

Definition obj_name := nNamed "R".
Definition knt_name := nNamed "k".

(** We assume that there is a hidden topmost variable [p : Obj] in the context *)

Definition pos_name := nNamed "p".
Definition hom_name := nNamed "α".

(** Optimization of cuts *)
(* TODO: for now it is just ordinary tApp; could be changed if we need it later *)

Definition mkOptApp t args := tApp t args.
(* The original OCaml inplementation  *)
(* let mkOptApp (t, args) = *)
(*   let len = Array.length args in *)
(*   try *)
(*     let (_, t) = Term.decompose_lam_n len t in *)
(*     Vars.substl (CArray.rev_to_list args) t *)
(*   with _ -> *)
(* mkApp (t, args) *)


(** Forcing translation *)
Inductive forcing_condition :=
| fcVar : forcing_condition
| fcLift : forcing_condition.

Record forcing_context :=
  mkFCtxt { f_context : list forcing_condition;
            f_category : category;
            f_translator : tsl_table;
            (* A map associating to all source constant a forced constant *)
          }.

Definition fcond_to_string fc :=
  match fc with
  | fcVar => "fcVar"
  | fcLift => "fcLift"
  end.


(* WARNING: tRel indices start from 0 in Tempalte Coq and *not* from 1 as for mkRel in the kernel  *)
Fixpoint last_internal fctx :=
  match fctx with
  | [] => 0
  | fcVar :: fctx => 1 + last_internal fctx
  | fcLift :: fctx => 1
  end.

Definition last_condition fc :=
  last_internal fc.(f_context).

Fixpoint gather_morphisms_internal i n fctx :=
  if (Nat.eqb n 0) then []
  else match fctx with
       | [] => []
       | fcVar :: fctx => gather_morphisms_internal (i + 1) (n - 1) fctx
       | fcLift :: fctx => i :: gather_morphisms_internal (i + 2) n fctx
       end.

Definition gather_morphisms (n : nat) (fctx : forcing_context) : list nat :=
  gather_morphisms_internal 0 (n+1) (f_context fctx).

Definition top_condition (fctx : forcing_context) : nat :=
  let fld_with acc f :=
      match f with
      | fcVar => 1 + acc
      | fcLift => 2 + acc
      end in
  List.fold_left fld_with fctx.(f_context) 0.

Fixpoint top_is_lift (fctx : list forcing_condition) : bool :=
  match fctx with
  | [] => false
  | [fcLift] => true
  | c :: cs => top_is_lift cs
  end.

Definition morphism_var (n : nat) (fctx : forcing_context) : term :=
  let morphs := gather_morphisms n fctx in
  let last := tRel (last_condition fctx) in
  let cat := (f_category fctx) in
  let fold_with (accu : term) (i j : nat) :=
      tApp cat.(cat_comp) [tRel (j+1); tRel (i+1); last; accu; tRel i] in
  let init := tApp cat.(cat_id) [last] in
  let fix f_left l accu {struct l} :=
      match l with
      | [] => accu
      | i :: t =>
        match t with
        (* We have to use this to handle a special case: the top level condition.
         There are two cases: when the topmost entry in the forcing context is a lift, or a variable*)
        | [] => let is_lift := top_is_lift fctx.(f_context) in
                let top_rel := if is_lift then tRel (i+4) else tRel (top_condition fctx) in
                tApp cat.(cat_comp) [top_rel; tRel (i+1); last; accu; tRel i]
          | j :: t' => f_left t (fold_with accu i j)
        end
      end in
  (* tVar (list_to_string fcond_to_string fctx.(f_context)). *)
  f_left morphs init.
  (* in *)
  (* List.fold_left fold_with morphs init. *)

(* The original OCaml code *)
(* let morphism_var n fctx = *)
(*   let morphs = gather_morphisms n fctx in *)
(*   let last = mkRel (last_condition fctx) in *)
(*   let fold accu i = *)
(*     trns fctx.category dummy dummy last (mkRel i) accu *)
(*   in *)
(* List.fold_left fold (refl fctx.category last) morphs *)


(* Some examples to play with  *)
Definition Obj := Type.
Definition Hom := (fun x y => x -> y).
Definition Id_hom := @id.
Definition Comp := @Coq.Program.Basics.compose.

Definition test_cat : category :=
  makeCatS "Obj" "Hom" "Id_hom" "Comp".

Definition test_fctx :=
  {| f_context := [fcLift; fcLift];
     f_category := test_cat;
     f_translator := []|}.

Eval compute in gather_morphisms 1 test_fctx.
Eval compute in morphism_var 1 test_fctx.

(** A stub for the actual evar_map definition *)
Definition evar_map := unit.

Module Environ.
  (** Stub for global environment Environ *)

  Definition rel_declaration := unit.

  Record env := { env_globals : global_declarations }.

  Definition empty_env := {| env_globals := [] |}.

  Definition rel_context (e : env) : list rel_declaration := [].

  Definition of_global_context (c : global_context) : env :=  {| env_globals := fst c |}.

  Definition to_global_context (E : env) : global_context :=
    Typing.reconstruct_global_context E.(env_globals).
End Environ.

Definition get_var_shift n fctx :=
  let fix get n fctx :=
    if (Nat.eqb n 0 )then 0
    else
      match fctx with
    | [] => n
    | fcVar :: fctx => 1 + get (n - 1) fctx
    | fcLift :: fctx => 2 + get n fctx
         end
  in
  get (n+1) fctx.(f_context).

(* We convert the result of checking for relevance in a stupid way :)
   TODO: think about the error propagation *)
Definition from_rel_result (rl : rel_result) : relevance :=
  match rl with
  | RelOk r => r
  | RelNotSort _ => Relevant
  | RelTypingError _ => Relevant
  end.


(* TODO: use the same style for the record projections everywhere *)

(* While extending the context we need to determine the relevance of the types of morphisms and objects in the category.
   In order to do that we use the [relevance_of_type] function, and this function requires a global context, so now
   [extend] also takes is as a parameter *)
Definition extend (env : Environ.env) (fctx : forcing_context) : list context_decl * forcing_context :=
  let cat := fctx.(f_category) in
  let last := last_condition fctx in
  let g_ctx := Environ.env_globals env in
  let relevance_of_arg := from_rel_result (relevance_of_type g_ctx [] cat.(cat_obj)) in
  (* We are interested in the relevance of [hom x y] for any [x] and [y] of the appropriate type.
     So, we create a dummy context with two entries and the feed it into the [relevance_of_type] *)
  let dummy_ctx :=
      [Build_context_decl nAnon relevance_of_arg None cat.(cat_obj);
       Build_context_decl nAnon relevance_of_arg None cat.(cat_obj)] in
  let dummy_app := (tApp cat.(cat_hom) [tRel 1; tRel 0]) in
  let relevance_hom :=
      from_rel_result (relevance_of_type (Environ.env_globals env) dummy_ctx dummy_app) in
  let ext :=
      [ Build_context_decl
          hom_name
          relevance_hom
          None
          (tApp cat.(cat_hom) [(tRel (1 + last)); (tRel 0)]);
          (* replaced mkRel 1 with tRel 0, see comments for [last_condition] *)
        Build_context_decl
          pos_name
          relevance_of_arg
          None
          cat.(cat_obj) ]
  in
  (ext, {| f_context := fcLift :: fctx.(f_context);
           f_category := cat;
           f_translator := fctx.(f_translator)|}).

Definition add_variable fctx :=
  {| f_context := fcVar :: fctx.(f_context);
     f_category := fctx.(f_category);
     f_translator := fctx.(f_translator)|}.

(** Handling of globals *)

Definition translate_var fctx n :=
  let p := tRel (last_condition fctx) in
  let f := morphism_var n fctx in
  let m := get_var_shift n fctx in
  tApp (tRel (m-1)) [p; f ].

(* TODO: finish with this definition when we add support for inductive definitions *)
Definition get_inductive (fctx : forcing_context) (ind : inductive) : inductive :=
  let gr := IndRef ind in
  let gr_ :=lookup_default fctx.(f_translator) gr in
  match gr_ with
  | tInd ind_ _ => ind_
  | _ => {| inductive_mind := "inductive translation not found"; inductive_ind := 0 |}
  end.

Definition should_not_be_ind := tVar "Should not be an application of an inductive type constructor".

Definition apply_global (env : Environ.env) (sigma : evar_map) gr (u : universe_instance) fctx :=
  (** FIXME -- a comment from the OCaml source code *)
  (* The parameter [u] is never used in the definition *)
  let p' := lookup_default fctx.(f_translator) gr in
  (* let (sigma, c) := Evd.fresh_global env sigma p' in *)
  let last := last_condition fctx in
  match gr with
  | IndRef _ => (sigma, should_not_be_ind)
  | _ => (sigma, tApp p' [ tRel last ])
  end.


(** Forcing translation core *)

Definition not_supported := tVar "Not supported".

Definition is_prop (s : universe) :=
  match s with
  | [(Level.lProp, false)] => true
  | _ => false
  end.

Fixpoint sep_last xs :=
  match xs with
    [] => (tVar "empty_list", [])
  | hd::[] => (hd,[])
  | hd::tl =>let (l,tl) := sep_last tl in (l,hd::tl)
  end.

Definition id_translate sigma c : unit * term :=
  (sigma, c).

Definition otranslate_type (tr : Environ.env -> forcing_context -> evar_map -> term -> unit * term)
           (env : Environ.env) (fctx : forcing_context) (sigma : evar_map) (t : term)
  : unit * term :=
  let (sigma, t_) := tr env fctx sigma t in
  let last := tRel (last_condition fctx) in
  let t_ := mkOptApp t_ [ last; tApp fctx.(f_category).(cat_id) [last]] in
(sigma, t_).

Definition otranslate_boxed (tr : Environ.env -> forcing_context -> evar_map -> term -> unit * term)
           (env : Environ.env) (fctx : forcing_context) (sigma : evar_map) (t : term)
  : unit * term :=
  let (ext, ufctx) := extend env fctx in
  let (sigma, t_) := tr env ufctx sigma t in
  let t_ := it_mkLambda_or_LetIn t_ ext in
  (sigma, t_).

Definition otranslate_boxed_type (tr : Environ.env -> forcing_context -> evar_map -> term -> unit * term) env fctx sigma t :=
  let (ext, ufctx) := extend env fctx in
  let (sigma, t_) := otranslate_type tr env ufctx sigma t in
  let t_ := it_mkProd_or_LetIn t_ ext in
  (sigma, t_).

Quote Recursively Definition q_eq := (forall A a b, eq (A:=A) a b).

Definition lookup_ind Σ ind i (u : list Level.t) (* TODO Universes *) :
  option one_inductive_entry :=
    match lookup_env Σ ind with
    | Some (InductiveDecl _ mib) => nth_error (mind_body_to_entry mib).( mind_entry_inds) i
    |  _ => None
    end.

Fixpoint list_init_rev {A} (n : nat) (f : nat -> A) : list A :=
  match n with
  | O => [f 0]
  | S n' => f (S n') :: list_init_rev n' f
  end.

Definition list_init {A} (n : nat) (f : nat -> A) : list A := List.rev (list_init_rev n f).

(* Not finished attempt to port the translation for the inductive definitions *)
(* Definition otranslate_ind tr (env : Environ.env) fctx sigma ind u args := *)
(*   let ind_ := get_inductive fctx ind in *)
(*   let oib' := lookup_ind (Environ.to_global_context env) ind_.(inductive_mind) ind_.(inductive_ind) [] in *)
(*   (* let (_, oib) := Inductive.lookup_mind_specif env ind_ in *) *)
(*   let fold sigma u := otranslate_boxed tr env fctx sigma u in *)
(*   let (sigma, args_) := fold_map fold sigma args in *)
(*   (** First parameter is the toplevel forcing condition *) *)
(*   let (_, paramtyp) := match oib' with *)
(*                        | Some t => sep_last t.(mind_entry_lc) *)
(*                        | None => (tVar "Inductive not declared",[]) *)
(*                        end in *)
(*   let nparams := List.length paramtyp in *)
(*   let last := last_condition fctx in *)
(*   let fctx := List.fold_left (fun accu _ => add_variable accu) paramtyp fctx in *)
(*   let (ext, fctx) := extend env fctx in *)
(*   let mk_var n := *)
(*     let n := nparams - n in *)
(*     let (ext0, fctx) := extend env fctx in *)
(*     let ans := translate_var fctx n in *)
(*     it_mkLambda_or_LetIn ans ext0 *)
(*   in *)
(*   (* let (sigma, pi) := Evd.fresh_inductive_instance env sigma ind_ in *) *)
(*   let params := list_init nparams mk_var in *)
(*   let app := tApp (tInd ind_ []) (tRel (last_condition fctx) :: params) in *)
(*   (* let map_p i c := Vars.substnl_decl [mkRel last] (nparams - i - 1) c in *) *)
(*   (* let paramtyp := List.mapi map_p paramtyp in *) *)
(*   let ans := it_mkLambda_or_LetIn app (ext ++ paramtyp)%list in *)
(* (sigma, mkOptApp (ans, args_)). *)

Fixpoint otranslate (env : Environ.env) (fctx : forcing_context)
         (sigma : evar_map) (c : term) {struct c} : evar_map * term :=
  match c with
| tRel n =>
  let ans := translate_var fctx n in
  (* let ans := tVar (list_to_string fcond_to_string fctx.(f_context) ++ " | tRel " ++ string_of_int n) in *)
    (sigma, ans)
| tSort s =>
  let (ext0, fctx) := extend env fctx in
  let (ext, fctx) := extend env fctx in
  let (sigma, s') :=
      if is_prop s then (sigma, s)
    else
      (* TODO: Not sure how to deal with the universe variable generation *)
      (* Evd.new_sort_variable Evd.univ_flexible sigma *)
      (* Probably, use an empty list as a universe param *)
      (* For now, we just return the original universe, as it is given in the paper *)
      (sigma, s)
  in
  (* let sigma := Evd.set_leq_sort env sigma s s' in *)
  let tpe := it_mkProd_or_LetIn (tSort s') ext in
  let lam := it_mkLambda_or_LetIn tpe ext0 in
  (sigma, lam)
| tCast c k t =>
  let (sigma, c_) := otranslate env fctx sigma c in
  let (sigma, t_) := otranslate_type otranslate env fctx sigma t in
  let ans := tCast c_ k t_ in
  (sigma, ans)
| tProd na r t u =>
  let (ext0, fctx) := extend env fctx in
  (** Translation of t *)
  let (sigma, t_) := otranslate_boxed_type otranslate env fctx sigma t in
  (** Translation of u *)
  let ufctx := add_variable fctx in
  let (sigma, u_) := otranslate_type otranslate env ufctx sigma u in
  (** Result *)
  let ans := tProd na r t_ u_ in
  let lam := it_mkLambda_or_LetIn ans ext0 in
  (sigma, lam)
| tLambda na r t u =>
  (** Translation of t *)
  let (sigma, t_) := otranslate_boxed_type otranslate env fctx sigma t in
  (** Translation of u *)
  let ufctx := add_variable fctx in
  let (sigma, u_) := otranslate env ufctx sigma u in
  let ans := tLambda na r t_ u_ in
  (sigma, ans)
| tLetIn na r c t u =>
  let (sigma, c_) := otranslate_boxed otranslate env fctx sigma c in
  let (sigma, t_) := otranslate_boxed_type otranslate env fctx sigma t in
  let ufctx := add_variable fctx in
  let (sigma, u_) := otranslate env ufctx sigma u in
  (sigma, tLetIn na r c_ t_ u_)
(* Comment out the case for inductive types for now *)
(* | tApp t args when isInd t => *)
(*   let (ind, u) := destInd t in *)
(*   otranslate_ind env fctx sigma ind u args *)
| tApp t args =>
  let (sigma, t_) := otranslate env fctx sigma t in
  let fold sigma u := otranslate_boxed otranslate env fctx sigma u in
  (* implementing a specialised version of fold_map' from ftUtils as a nested fix *)
  let fix fold_map_fix a args :=
               match args with
               | [] => (a, [])
               | hd :: tl =>
                 let (a_, c_) := fold sigma hd in
                 let (a__, cs) := fold_map_fix a_ tl in
                 (a__, c_ :: cs)
               end in
  let (sigma, args_) := fold_map_fix sigma args in

  (* the original OCaml code *)
  (* let fold sigma u = otranslate_boxed env fctx sigma u in *)
  (* let (sigma, args_) = CArray.fold_map fold sigma args in *)
  let app := tApp t_ args_ in
  (sigma, app)
| tVar id => (sigma, not_supported)
  (* apply_global env sigma (VarRef id) Univ.Instance.empty fctx *)
| tConst p u =>  apply_global env sigma (ConstRef p) u fctx
| tInd ind u =>
  (* Comment out the case for inductive types for now *)
  (sigma, tVar "Inductive definitions are not supported")
  (* otranslate_ind env fctx sigma ind u [||] *)
| tConstruct c u _ => (sigma, not_supported)
  (* apply_global env sigma (ConstructRef c) u fctx *)
| tCase ci rel r c p => (sigma, not_supported)
(* Comment out this case as well, since inductive types are not yet supported by this translation *)
   (* let ind_ = get_inductive fctx ci.ci_ind in *)
   (* let ci_ = Inductiveops.make_case_info env ind_ ci.ci_pp_info.style in *)
   (* let (sigma, c_) = otranslate env fctx sigma c in *)
   (* let fix_return_clause env fctx sigma r = *)
   (*   (** The return clause structure is fun indexes self => Q *)
   (*       All indices must be boxed, but self only needs to be translated *) *)
   (*   let (args, r_) = decompose_lam_assum r in *)
   (*   let ((na, _, self), args) = match args with h :: t -> (h, t) | _ -> assert false in *)
   (*   let fold (sigma, fctx) (na, o, u) =  *)
   (*    (** For every translated index, the corresponding variable is added *)
   (*        to the forcing context *) *)
   (*     let (sigma, u_) = otranslate_boxed_type env fctx sigma u in *)
   (*     let fctx = add_variable fctx in *)
   (*     (sigma, fctx), (na, o, u_) *)
   (*   in *)
   (*   let (sigma, fctx), args = CList.fold_map fold (sigma, fctx) args in *)
   (*   let (sigma, self_) = otranslate_type env fctx sigma self in *)
   (*   let fctx_ = add_variable fctx in *)
   (*   let (sigma, r_) = otranslate_type env fctx_ sigma r_ in *)
   (*   let (ext, ufctx) = extend fctx in *)
   (*   let selfid = Id.of_string "self" in *)
   (*   let r_ = Reductionops.nf_betadeltaiota env Evd.empty r_ in  *)
   (*   let r_ = Vars.substnl [it_mkLambda_or_LetIn (mkVar selfid) ext] 1 (Vars.lift 1 r_) in *)
   (*   let r_ = Reductionops.nf_beta Evd.empty r_ in  *)
   (*   let r_ = Vars.subst_var selfid r_ in *)
   (*   let r_ = it_mkLambda_or_LetIn r_ ((na, None, self_) :: args) in  *)
   (*   (sigma, r_)        *)
   (* in *)
   (* let (sigma, r_) = fix_return_clause env fctx sigma r in *)
   (* let fold sigma u = otranslate env fctx sigma u in *)
   (* let (sigma, p_) = CArray.fold_map fold sigma p in *)
   (* (sigma, mkCase (ci_, r_, c_, p_)) *)
| tFix _ _ => (sigma, not_supported)
| tCoFix _ _ => (sigma, not_supported)
| tProj _ _ => (sigma, not_supported)
| tMeta _ => (sigma, not_supported)
| tEvar _ _ => (sigma, not_supported)
  end.

Definition empty translator cat lift env :=
  let ctx := Environ.rel_context env in
  let empty := {| f_context := []; f_category := cat; f_translator := translator; |} in
  let empty := List.fold_right (fun _ fctx => add_variable fctx) empty ctx in
  let fix flift fctx n :=
      match n with
      | O => fctx
      | S n' => flift (snd (extend env fctx)) n'
      end
  in
  flift empty (match lift with None => 0 | Some n => n end).


(** The toplevel option allows to close over the topmost forcing condition *)

Definition translate (toplevel : bool) lift translator cat env sigma c :=
  let empty := empty translator cat lift env in
  let (sigma, c) := otranslate env empty sigma c in
  let ans := if toplevel then tLambda pos_name Relevant cat.(cat_obj) c else c in
  (sigma, ans).

Definition translate_simple (toplevel : bool) (cat : category) (c : term) : term :=
  let (_, c_) := translate toplevel None [] cat Environ.empty_env tt c in c_.

Definition translate_type (toplevel : bool) lift translator cat env sigma c :=
  let empty := empty translator cat lift env in
  let (sigma, c) := otranslate_type otranslate env empty sigma c in
  let ans := if toplevel then tProd pos_name Relevant cat.(cat_obj) c else c in
  (sigma, ans).

Definition translate_type_simple (toplevel : bool) (cat : category) (c : term) : term :=
  let (_, c_) := translate_type toplevel None [] cat Environ.empty_env tt c in c_.
