Require Import String.
Require Import List.

Require Import Template.monad_utils
        Template.Ast
        Template.AstUtils
        Template.Template
        Template.LiftSubst
        Template.Checker
        Template.Typing
        Template.Induction.

Require Import Forcing.TemplateForcing
        Forcing.translation_utils
        Forcing.TFUtils.

Import MonadNotation.
Import ListNotations.

(* When possible, decomposes a product Π(x₁:τ₁)…(xₙ:τₙ).t into a tuple ([x₁:τ₁ ; … ; xₙ:τₙ] , t) 
   If not possible, returns None. *) 
Definition decompose_prod_n (n : nat) (tm : term) :=
  let fix aux param n tm :=
      match n with
      | 0 => Some (param, tm)
      | S n' => match tm with
               | tProd na r t u => aux ((na, r, t)::param) n' u
               | tCast c _ _ => aux param n c
               | _ => None
               end
      end
  in
  aux [] n tm.

Definition decompose_prod (tm : term) :=
  let fix aux param tm :=
      match tm with
      | tProd na r t u => aux ((na, r, t)::param) u
      | tCast c _ _ => aux param c
      | _ => (param, tm)
      end
  in
  aux [] tm.

Fixpoint compose_prod param tm :=
  match param with
  | nil => tm
  | (na, r, t)::tail => compose_prod tail (tProd na r t tm)
  end.

Inductive test0 (n : nat) : Type -> Prop :=
| c0 : test1 n Set -> test0 n Prop
with test1 (n : nat) : Type -> Prop :=
     | c1 : test0 n Prop -> test1 n Set.

Inductive test2 (a : Type) : nat -> Type :=
| c2 : forall n : nat, test2 a n.

Quote Definition test3 := (Prop -> Set -> Type).

Eval compute in (let (α, β) := decompose_prod test3 in compose_prod α β).

Polymorphic Cumulative Inductive list' {A : Type} :=
| empty' : list'
| cons' : A -> list' -> list'.

Polymorphic Record PackType := {pk : Type}.

Run TemplateProgram (α <- tmQuoteInductive "PackType" ;;
                       β <- tmEval lazy (mind_body_to_entry α) ;;
                       tmPrint α).

(* smh Polymorphic Cumulative = NonPolymorphic *)

(* translates the arity of a one_inductive_body. env should contain the parameters of
 the mutual_inductive_body *)
(* keep in mind that f_translate_arity doesnt need to know about oib names, since by default
 coq does not permit scary stuff like induction-induction *)
Definition f_translate_arity (tsl_ctx : tsl_context) (cat : category)
           (env : Environ.env) (σ : evar_map) (name : kername) (arity : term)
  : tsl_result (evar_map * term) :=
  (* translation the arity *)
  (* the ocaml version translates it with toplevel:=false, but this yields an open term that i cannot reduce *)
  let (l, s) := decompose_prod arity  in
  let n_indices := length l in
  let (σ, arity') := translate_type true None (snd tsl_ctx) cat env σ arity in
  (* now reduce the beta-redexes *)
  arity' <- match hnf_stack [] [] arity' with (** TODO : I should probably put something more interesting than [] *)
           | Checked (tm, args) =>
             match tm, args with
             | tProd _ _ _ a, nil => ret a
             | _, nil => Error (UnexpectedError
                                 ("Something went really wrong during the translation of the arity of " ++ name))
             | _, _ => Error (UnexpectedError ("The arity of " ++ name ++ " does not reduce to a value"))
             (* note to future self : if you run into this, do check the relevance of the TODO right above *)
             end
           | TypeError e => Error (TypingError e)
           end ;;
  (* and then replace the translated sort with the base one *)
  (* the ocaml plugin does something pretty weird here, i dont really know why *)
  a <- match decompose_prod_n n_indices arity' with
      | Some (a, _) => ret a
      | None => Error (UnexpectedError
                        ("Something went really wrong during the translation of the arity of " ++ name))
      end ;;
  ret (σ, compose_prod a s).


(* see coq Vars.substnl *)
Definition substnl l n t :=
  List.fold_left (fun t u => subst u n t) l t.

(* translation of one oib name *)
(* contexts from the ocaml plugin have been converted to list of name * relevance * term *)
Definition f_translate_oib_type (tsl_ctx : tsl_context) (cat : category)
           (env : Environ.env) (σ  : evar_map) (id : kername) (arityctxt : list (name * relevance * term))
  : evar_map * term :=
  (* we translate I as λp params indices q α . (var I) p params indices *)
  (* first, the body of the lambda abstraction *)
  let narityctxt := length arityctxt in
  let args := map tRel (List.rev (seq 3 narityctxt)) in (** TODO Check de Bruijn indices *)
  let fnbody := mkApps (tVar id) args in
  (* then, translate all the params and indices types *)
  let fold := fun (acc : evar_map * context) (decl : name * relevance * term) =>
               let (σ, ctxt) := acc in
               let '(n, rel, t) := decl in
               let (σ, tr_t) := translate_type true None (snd tsl_ctx) cat env σ t in
               (σ, {| decl_name := n ;
                      decl_relevance := rel ;
                      decl_body := None ; 
                      decl_type := tr_t |}::ctxt)
  in
  let (σ, tr_arity) := fold_left fold arityctxt (σ, nil) in
  (* build the arguments of the lambda abstraction *)
  let hom := tApp cat.(cat_hom) [tRel 3 ; tRel (3 + narityctxt)] in (** TODO Check de Bruijn indices *)
  let argctxt := (vass nAnon Relevant hom)::(tr_arity ++ [vass nAnon Relevant cat.(cat_obj)])%list in
  (* put everything together *)
  (* memo : it_mkLambda_or_LetIn is defined both in Template.Typing and Forcing.TFUtils with reversed arguments *)
  (σ, it_mkLambda_or_LetIn fnbody argctxt). 

(* applies f_translate_oib_names to all the inductives of a mutual inductive body,
 in order to build a substitution : list of name * translated type *)
Definition f_translate_oib_types (tsl_ctx : tsl_context) (cat : category)
           (env : Environ.env) (σ : evar_map) (mib : mutual_inductive_body)
  : evar_map * list (ident * term) :=
  let fold := fun (acc : evar_map * list (ident * term)) oib =>
               let (σ, tail) := acc in
               let (arityctxt, _) := decompose_prod oib.(ind_type) in
               let (σ, tr) := f_translate_oib_type tsl_ctx cat env σ oib.(ind_name) arityctxt in
               (σ, (oib.(ind_name), tr)::tail)
  in
  fold_left fold mib.(ind_bodies) (σ, nil).
  
(* see Vars.replace_vars in Coq *)
(* btw, this is some shameless copy paste from templateCoq subst *)
Fixpoint replace_var t k u :=
  match u with
  | tVar x => match eq_string x (fst t) with
             | true => lift0 k (snd t)
             | false => u
             end
  | tEvar ev args => tEvar ev (List.map (replace_var t k) args)
  | tLambda na r T M => tLambda na r (replace_var t k T) (replace_var t (S k) M)
  | tApp u v => tApp (replace_var t k u) (List.map (replace_var t k) v)
  | tProd na r A B => tProd na r (replace_var t k A) (replace_var t (S k) B)
  | tCast c kind ty => tCast (replace_var t k c) kind (replace_var t k ty)
  | tLetIn na r b ty b' => tLetIn na r (replace_var t k b) (replace_var t k ty) (replace_var t (S k) b')
  | tCase ind r p c brs =>
    let brs' := List.map (on_snd (replace_var t k)) brs in
    tCase ind r (replace_var t k p) (replace_var t k c) brs'
  | tProj p c => tProj p (replace_var t k c)
  | tFix mfix idx =>
    let k' := List.length mfix + k in
    let mfix' := List.map (map_def (replace_var t k')) mfix in
    tFix mfix' idx
  | tCoFix mfix idx =>
    let k' := List.length mfix + k in
    let mfix' := List.map (map_def (replace_var t k')) mfix in
    tCoFix mfix' idx
  | x => x
  end.

Fixpoint replace_vars s t :=
  match s with
  | nil => t
  | head::tail => replace_vars tail (replace_var head 0 t)
  end.

(* see Vars.substn_vars in Coq *)
Definition substn_vars (p : nat) (vars : list ident) (c : term)
  : term :=
  let fold := fun acc var =>
               let (n, l) := acc : nat * list (ident * term) in
               ((S n), (var, tRel n)::l)
  in
  let (_, subst) := fold_left fold vars (p,[]) in
  replace_vars (List.rev subst) c.

(* now to translate a single constructor
   as before, env should probably already contain the parameters of the mutual_inductive_body
   it should probably also contain a translation for the name of the one_inductive_body *)
(* the context for constructors is : 0 ~ n parameters, n+1 ~ n+k inductives *)
Definition f_translate_lc_list (tsl_ctx : tsl_context) (cat : category)
           (env : Environ.env) (σ : evar_map) (n_params : nat) (lc : list term)
           (substfn : list (ident * term)) (invsubst : list ident)
  : tsl_result (evar_map * list term) :=
  let f_translate_lc :=
      fun (m : tsl_result (evar_map * list term)) typ =>
        acc <- m ;;
        let (σ, tail) := acc : evar_map * list term in
        (* let (_, typ) := decompose_prod typ in *)
        (* replace the indices for oib's with their names *)
        let typ := substnl (map tVar invsubst) n_params typ in (** TODO adjust *)
        let (σ, typ) := translate_type true None (snd tsl_ctx) cat env σ typ in
        (* replace the names of oib's with their translation *)
        let typ := replace_vars substfn typ in
        typ' <- match hnf_stack [] [] typ with (** TODO should that be empty lists or what *)
               | Checked (tm, args) =>
                 match tm, args with
                 | tProd _ _ _ a, nil => ret a
                 | _, nil => Error (UnexpectedError
                                     ("Something went really wrong during the translation of a constructor."))
                 | _, _ => Error (UnexpectedError ("The arity of some constructor does not reduce to a value"))
                 end
               | TypeError e => Error (TypingError e)
               end ;;
        (* put indices back *)
        let typ' := substn_vars (n_params + 1) invsubst typ' in (** TODO adjust value *)
        (* now some shady stuff happens with sigma in the ocaml plugin, that are commented out below *)
        (** ocaml code *)
        (* let envtyp_ = Environ.push_rel_context [Name (Nameops.add_suffix body.mind_typename "_f"),None, *)
        (*       				  it_mkProd_or_LetIn arity params] env in *)
        (* let envtyp_ = Environ.push_rel_context params envtyp_ in *)
        (* let sigma, ty = Typing.type_of envtyp_ sigma typ_ in                              *)
        (* let sigma, b = Reductionops.infer_conv ~pb:Reduction.CUMUL envtyp_ sigma ty s in *)
        (** end *)
        ret (σ, typ'::tail)
  in
  fold_left f_translate_lc lc (ret (σ, nil)).

(* Vernacular names of the translated inductive and constructors *)
(* Here the ocaml plugin tries to use provided ids before calling the name translation function.
 This might be important, but i dont think so *)
Definition f_translate_names (typename : ident) (consnames : list ident)
  : ident * list ident :=
  (tsl_ident typename, map tsl_ident consnames).
  

(* Apply the translation to one oib *)
Definition f_translate_oib (tsl_ctx : tsl_context) (cat : category) 
           (env : Environ.env) (σ : evar_map)
           (entry : one_inductive_entry)
           (n_params : nat) (substfn : list (ident * term)) (invsubst : list ident)
  : tsl_result (evar_map * one_inductive_entry) :=
  let (typename, consnames) := f_translate_names entry.(mind_entry_typename) entry.(mind_entry_consnames) in
  let template := entry.(mind_entry_template) in   (* not sure how this one works *)
  (** TODO update env 
   Like, really, this WILL not work as is. *)
  x <- f_translate_arity tsl_ctx cat env σ entry.(mind_entry_typename) entry.(mind_entry_arity) ;;
  let (σ, arity) := x : evar_map * term in
  x <- f_translate_lc_list tsl_ctx cat env σ n_params entry.(mind_entry_lc) substfn invsubst ;;
  let (σ, lc) := x : evar_map * list term in
  ret (σ, {| mind_entry_typename := typename ;
             mind_entry_arity := arity ;
             mind_entry_template := template ;
             mind_entry_consnames := consnames ;
             mind_entry_lc := List.rev lc |}).

(** TODO *)
Definition from_env (env : Environ.env)
  : evar_map :=
  tt.

Definition f_translate_params (tsl_ctx : tsl_context) (cat : category)
           (env : Environ.env) (σ : evar_map)
           (params : list (ident * local_entry))
  : evar_map * list (ident * local_entry) :=
  let fold := fun param acc =>
               let (id, e) := param : ident * local_entry in
               let t := match e with
                       | LocalDef x => x
                       | LocalAssum x => x
                       end in
               let '(σ, fctx, tail) := acc : evar_map * forcing_context * list (ident * local_entry)  in
               let (ext, tfctx) := extend env fctx in
               let (σ, t') := otranslate_type otranslate env tfctx σ t in
               let t' := it_mkProd_or_LetIn t' ext in
               let fctx := add_variable fctx in
               (σ, fctx, (id, LocalAssum t')::tail)
  in
  let init := [("p", LocalAssum (cat.(cat_obj)))] in
  let empty := {| f_context := []; f_category := cat; f_translator := (snd tsl_ctx) ; |} in
  let '(σ, _, params) := fold_right fold (σ, empty, init) params in
  (σ, params).

(* main translation function for inductives *)
Definition f_translate_mib (tsl_ctx : tsl_context) (cat : category) (mib : mutual_inductive_body)
  : tsl_result mutual_inductive_entry :=
  (* entries are more pleasant to work with than bodies *)
  let entry := mind_body_to_entry mib in
  (* this should be from the global environment, right ? *)
  (* however, not sure if there is a way to get it from TemplateCoq *)
  let env := Environ.empty_env in (** TODO fix *)
  let σ := from_env env in
  let invsubst := map (fun x => x.(mind_entry_typename)) entry.(mind_entry_inds) in
  let (σ, substfn) := f_translate_oib_types tsl_ctx cat env σ mib in
  let (σ, params) := f_translate_params tsl_ctx cat env σ entry.(mind_entry_params) in
  let fold := fun oib acc =>
               α <- acc ;;
               let (σ, tail) := α : evar_map * (list one_inductive_entry) in
               α <- f_translate_oib tsl_ctx cat env σ oib mib.(ind_npars) substfn invsubst ;;
               let (σ, oib) := α : evar_map * one_inductive_entry in
               ret (σ, oib::tail)
  in
  α <- fold_right fold (ret (σ, nil)) entry.(mind_entry_inds) ;; (* why right and not left though *)
  let (σ, bodies) := α : evar_map * list one_inductive_entry in
  (* let params := List.map make_param params in *)
  (* let (_, uctx) := Evd.universe_context sigma in *)
  let entry := {| mind_entry_record := None ; (* quoting inductives seems to ignore records *)
               mind_entry_finite := Finite ; (* not dealing with coinductives *)
               mind_entry_params := params ;
               mind_entry_inds := bodies ;
               (* Okay so the ocaml plugin somehow gets the universe graph from the evar_map.
                I guess this is because translation could introduce new universe constraints. *)      
               mind_entry_universes := entry.(mind_entry_universes) ; (** TODO fix that *)
               mind_entry_private := None |} (* this is also lost during quoting *)
  in
  ret entry.
 
(* finalizes the translation by adding everything to the translation context *)
Definition f_translate_ind (cat : category) (tsl_ctx : tsl_context)
           (id : kername) (id' : kername) (mib : mutual_inductive_body) :
  tsl_result (tsl_table * mutual_inductive_entry) :=
  mib <- f_translate_mib tsl_ctx cat mib ;;
  let translator := snd tsl_ctx in (** TODO *) (* not really sure what should be added to translator *)
  ret (translator, mib).



