Require Import Omega.
Require Import Forcing.TemplateForcing.
Require Import Template.Typing Template.Ast Template.LiftSubst.
From Template Require Export univ uGraph.

Require Import String.
Local Open Scope string_scope.

Require Import List.
Import ListNotations.
Open Scope list.

Import Environ.

Definition cat : category :=
  makeCatS "Obj" "Hom" "Id_hom" "Comp".

Definition ft_type c Σ σ :=
  (snd (otranslate_type otranslate (Environ.of_global_context Σ) (mkFCtxt σ cat []) tt c)).

Definition ft_term c Σ σ :=
  (snd (otranslate (Environ.of_global_context Σ) (mkFCtxt σ cat []) tt c)).

Definition ft_ctx Γ Σ σ  :=
  (otranslate_context_no_sigma (Environ.of_global_context Σ) (mkFCtxt σ cat []) tt Γ).

Definition ft_type_boxed c Σ σ  :=
  (snd (otranslate_boxed_type otranslate (Environ.of_global_context Σ) (mkFCtxt σ cat []) tt c)).

Notation "'[' c ']ᵗ' " := (ft_term c) (at level 0).
Notation "⟦ Γ ⟧" := (ft_ctx Γ)  (at level 40).
Notation "'⟦' c '⟧ᵀ'" := (ft_type c) (at level 40).
Notation "'⟦' c '⟧!'" := (ft_type_boxed c) (at level 40).

Notation "Hom( a , b )" := (tApp cat.(cat_hom) [a;b]).

Notation "fctx '.ₑ'" := (last_condition fctx) (at level 1, format "fctx .ₑ").
Notation "dom( fctx , n )" := (get_domain_var fctx n) (at level 1).

Definition tID q := tApp (tConst "Id_hom" []) [q].
Notation "# q" := (tID q) (at level 51).
Notation "g ∘ f <:: xs " := (tApp (tConst "Comp" []) (xs ++ [g;f])) (at level 49).
Notation "fctx '.ₚ'" := (first_condition fctx) (at level 1, format "fctx .ₚ").
Definition fctx_size := first_condition.
Notation "^ i" := (tRel i) (at level 50, format "^ i").

(* Forcing context extension *)
Definition f_ctx_ext (σ σ' : list forcing_condition) := σ' ++ σ.
Notation "σ ∙ σ' " := (f_ctx_ext σ σ') (at level 100).


Definition leq_refl sigma t : leq_term sigma t t = true.
Proof.
  induction t.
Admitted.

Definition eq_term_refl sigma t : eq_term sigma t t = true.
Proof.
Admitted.

Lemma compare_string_refl s : compare_string s s = Eq.
Proof.
  unfold compare_string. rewrite Nat.compare_refl. reflexivity.
Qed.

Lemma univ_expr_eq_refl a : Universe.Expr.equal a a = true.
Proof.
  destruct a. simpl.
  induction t;destruct b;simpl; try reflexivity;
  try (unfold  Universe.Expr.equal,Level.equal;simpl;
       try (rewrite compare_string_refl); (try rewrite Nat.compare_refl); reflexivity).
Qed.

Lemma leq_universe_refl uG s :
  leq_universe uG s s = true.
Proof.
  unfold leq_universe.
  assert (HH : Universe.equal s s = true).
  { induction s.
    + reflexivity.
    + simpl. rewrite univ_expr_eq_refl. rewrite IHs. reflexivity. }
  rewrite HH;reflexivity.
Qed.

Definition rlv_obj := Relevant.
Definition rlv_hom := Relevant.
Definition obj_univ := [Universe.Expr.set].
Definition hom_univ := [Universe.Expr.set].
Definition obj_sort := tSort obj_univ.
Definition hom_sort := tSort hom_univ.
Definition comp_type r_obj r_hom a b c :=
  tProd a r_obj cat.(cat_obj)
      (tProd b r_obj cat.(cat_obj)
           (tProd c r_obj cat.(cat_obj)
               (tProd nAnon r_hom Hom(^1,^0)
                  (tProd nAnon r_hom Hom(^3,^2)
                     Hom(^4,^2))))).

(** We assume the following sorts for the objects and morphisms of the base category *)
Axiom obj_sort_type : forall Σ Γ, Σ ;;; Γ |- cat.(cat_obj) : obj_sort.
Axiom hom_sort_type : forall Σ Γ t1 t2,
    Σ ;;; Γ |- t1 : cat.(cat_obj) ->
    Σ ;;; Γ |- t2 : cat.(cat_obj) ->
    Σ ;;; Γ |- tApp cat.(cat_hom) [t1; t2] : hom_sort.
Axiom id_hom_type : forall Σ Γ t,
    Σ ;;; Γ |- t : cat.(cat_obj) ->
    Σ ;;; Γ |- tApp cat.(cat_id) [t] : tApp cat.(cat_hom) [t; t].

Quote Definition bazz := (forall a b c, b <= c -> a <= b -> a <= c).

Axiom cat_comp_type : forall r_obj r_hom a b c Σ Γ,
    Σ ;;; Γ |- cat.(cat_comp) : comp_type r_obj r_hom a b c.

(* We define [weakening] as an axiom, because weakening in [Typing.v]
   contains an assumption about well-formedness of the context and it
   is not clear is it is needed (the proof if weakening is not
   finished.) *)
Axiom weakening : forall uG (Σ := ([], uG)) Γ Γ' (t : term) T,
  wf_graph (snd Σ) ->
  Σ ;;; Γ |- t : T ->
  Σ ;;; Γ ,,, Γ' |- lift0 #|Γ'| t : lift0 #|Γ'| T.

Axiom weakening_cumul : forall uG (Σ := ([], uG)) Γ Γ' (t u : term),
    wf_graph (snd Σ) ->
    Σ ;;; Γ |- t <= u ->
    Σ ;;; Γ ,,, Γ' |- lift0 #|Γ'| t <= lift0 #|Γ'| u.

Lemma wf_init_graph : wf_graph init_graph.
Proof.
  constructor.
  - constructor.
    + apply SetoidList.InA_cons_tl.
      apply SetoidList.InA_cons_hd. reflexivity.
    + intuition. apply SetoidList.InA_cons_tl. apply SetoidList.InA_cons_tl.
      apply SetoidList.InA_cons_hd. reflexivity.
      apply SetoidList.InA_cons_hd; auto.
      simpl. apply SetoidList.InA_cons_hd; eauto.
      (* NOTE: something is not right, either [wf_graph] or [init_graph] *)
      (* In Coq the constraint is [lt], so it's better to fix [wf_graph] *)
Admitted.

Lemma typed_empty_global_env uG :
  wf_graph uG ->
  type_global_env uG [].
Proof.
  constructor; auto.
Qed.

Ltac setctx na :=
  match goal with
    [ |- ?Σ ;;; ?Γ |- _ : _ ] => set(na := Γ)
  | [|- type_local_env ?Σ ?Γ ] => set(na := Γ)
  end.

Ltac setctx_2 na :=
  match goal with
    |- ?Σ ;;; ?v1 :: ?v2 :: ?Γ |- _ : _ => set(na := [v1;v2])
  | |- type_local_env ?Σ ?Γ => match Γ with
                               | ?v1 :: ?v2 :: _ => set(na := [v1;v2])
                               end
  end.


Ltac solve_rel :=
  let Γ' := fresh "Γ" in
  let H' := fresh in
  match goal with
    |- ?Σ ;;; ?Γ |- tRel ?n : _ =>
    setctx Γ';
    assert (H' : n < #|Γ'|) by (subst;simpl; omega);
    subst; apply type_Rel with (isdecl:=H')
  end.

Reserved Notation "E ## Γ => Γ' |= σ" (at level 40).

(* TODO: think about the empty context case *)
Inductive fctx_valid E : context -> context -> list forcing_condition -> Type :=
| fctx_valid_nil : E ## [] => [vass (nNamed "p") rlv_obj (tConst "Obj" nil)] |= nil
| fctx_valid_cons_var Γ Γ' σ T n n' r r':
    E ## Γ => Γ' |= σ ->
    let v := vass n r T in
    let T' := ⟦T⟧! (to_global_context E) σ in
    let v' := vass n' r' T' in
        E ## (Γ ,, v) => (Γ' ,, v') |= (σ ,, fcVar)
| fctx_valid_cons_lift Γ Γ' σ :
    E ## Γ => Γ' |= σ ->
    E ## Γ => (Γ' ,,, get_ctx_lift cat E (last_condition σ)) |= (σ ,, fcLift)
where "E ## Γ => Γ' |= σ" := (fctx_valid E Γ Γ' σ).


Lemma last_condition_sound σ Γ Γ' uG (Σ := ([], uG)) :
  wf_graph uG ->
  (of_global_context Σ) ## Γ => Γ' |= σ ->
  Σ ;;; Γ' |- tRel (last_condition σ) : cat.(cat_obj).
Proof.
  intros wfG FcValid.
  induction FcValid.
  - cbv. solve_rel.
  - simpl.
    change (Σ;;; Γ' ,,, [v'] |- lift0 1 (tRel (last_condition σ)) : lift0 1 cat.(cat_obj)).
    apply weakening.
    + exact wfG.
    + exact IHFcValid.
  - solve_rel.
Qed.

Lemma lift_sound uG (Σ := (nil,uG)) Γ Γ' σ v :
  wf_graph uG ->
  (of_global_context Σ) ## Γ => Γ' |= σ ->
  Σ;;; Γ',, vass v rlv_obj cat.(cat_obj) |- Hom(^(1+σ.ₑ),^0) : obj_sort.
Proof.
  intros wfG FcValid.
  eapply hom_sort_type.
  - pose ([vass v rlv_obj cat.(cat_obj)]) as Γ''.
    change
      (Σ;;; Γ' ,,, Γ'' |- lift0 #|Γ''| (tRel (last_condition σ)) : lift0 #|Γ''| cat.(cat_obj)).
    apply weakening with (Γ' := Γ'').
    * exact wfG.
    * apply last_condition_sound with (Γ := Γ);eauto.
  - solve_rel.
Qed.

Lemma lam_q_f_sound uG (Σ := (nil,uG)) Γ Γ' σ t T :
  let E := (of_global_context Σ) in
  let fctx := (mkFCtxt σ cat []) in
  let ext := get_ctx_lift cat E (last_condition σ) in
  wf_graph uG ->
  (of_global_context Σ) ## Γ => Γ' |= σ ->
  Σ ;;; Γ' ,,, ext |- t : T ->
  Σ ;;; Γ' |- snd (λ_q_f E fctx) t : snd (Π_q_f E fctx) T.
Proof.
  simpl. intros wfG FcValid Ty.
  econstructor.
  + eapply obj_sort_type.
  + econstructor.
    * eapply lift_sound;eauto.
    * eauto.
Qed.

Lemma Π_q_f_lift_sound uG (Σ := (nil,uG)) Γ σ T s :
  let σ_ext := σ ,, fcLift in
  let fctx_ext := (mkFCtxt σ_ext cat []) in
  let E := (of_global_context Σ) in
  let ext1 := get_ctx_lift cat E (last_condition σ) in
  let ext2 := get_ctx_lift cat E (last_condition σ_ext) in
  wf_graph uG ->
  Σ ;;; Γ ,,, ext1 ,,, ext2  |- T : tSort s ->
  Σ ;;; Γ ,,, ext1 |- snd (Π_q_f E fctx_ext) T :
  tSort (Universe.sup obj_univ (Universe.sup hom_univ s)).
Proof.
  simpl.
  intros wfG H.
  apply type_Prod.
  ** apply obj_sort_type.
  ** apply type_Prod.
     *** apply hom_sort_type; solve_rel.
     *** eauto.
Qed.

(* Lemma forcing_context_soundness Σ Γ σ : *)
(*   type_local_env Σ Γ -> type_local_env Σ (⟦Γ⟧ Σ σ). *)
(* Admitted. *)


Ltac type_spine_step :=
  match goal with
    | [  |- typing_spine _ _ _ (?t :: ?ts) _ ] =>
      econstructor;
      [eapply cumul_refl;apply leq_refl | | ]
  end.

Lemma sort_translation_prefix_sound uG (Σ := (nil,uG)) σ Γ Γ' T s:
  let E := (of_global_context Σ) in
  let fctx := (mkFCtxt σ cat []) in
  let srt := tSort (Universe.sup obj_univ  (Universe.sup hom_univ s)) in
  let ext1 := get_ctx_lift cat E (last_condition σ) in
  let ext2 := get_ctx_lift cat E (last_condition (σ ,, fcLift)) in
  wf_graph uG ->
  (of_global_context Σ) ## Γ => Γ' |= σ ->
  Σ ;;; Γ' ,,, ext1 ,,, ext2  |- T : tSort s ->
  Σ ;;; Γ' |- snd (sort_translation_prefix E fctx tt) T
                      : snd (Π_q_f E fctx) srt.
Proof.
  intros ? ? ? ? ? wfG FcValid TyT.
  simpl.
  eapply lam_q_f_sound;simpl;eauto.
  unfold obj_sort.
  eapply Π_q_f_lift_sound;auto.
Qed.

Lemma type_translation_sound uG (Σ := ([],uG)) Γ Γ' σ T s:
  wf_graph uG ->
  (of_global_context Σ) ## Γ => Γ' |= σ ->
  Σ;;; Γ' |- [T ]ᵗ Σ σ : (⟦ tSort s ⟧ᵀ) Σ σ ->
  Σ ;;; Γ' |- ⟦T⟧ᵀ Σ σ : tSort s.
Proof.
  intros wfG FcValid TyT.
  unfold ft_type,otranslate_type. simpl. unfold mkOptApp.
  remember (tRel (last_condition σ)) as last_fcond.
  remember (tApp (tConst "Id_hom" []) [last_fcond]) as id_hom_lfc.
  (* change (Σ;;; Γ' |- tApp ([T]ᵗ Σ σ) [last_fcond; id_hom_lfc] : tSort [Universe.Expr.set]). *)
  eapply type_App.
  - eapply TyT.
  - unfold ft_type. simpl. unfold mkOptApp. econstructor.
    * (* Abstract this reduction to a tactic *)
      eapply cumul_red_r. Focus 2.
      eapply red_beta. simpl.
      eapply cumul_red_r. Focus 2.
      eapply red_beta. simpl.
      eapply cumul_refl. apply leq_refl.
    * subst. eapply last_condition_sound;eauto.
    * econstructor. Focus 2.
      subst. apply id_hom_type. eapply last_condition_sound; eassumption.
      econstructor. subst. eapply leq_refl.
      econstructor.
Qed.

Lemma ctx_with_lift_sound (Σ := ([],init_graph)) Γ Γ' σ:
  let ext := get_ctx_lift cat (of_global_context Σ) (last_condition σ) in
  type_local_env Σ Γ' ->
  (of_global_context Σ) ## Γ => Γ' |= σ ->
  type_local_env Σ (Γ' ,,, ext).
Proof.
  simpl. intros TyCtx FcValid.
  constructor;eauto.
  constructor;eauto.
  econstructor; apply obj_sort_type.
  econstructor; eapply lift_sound;eauto.
  apply wf_init_graph.
Qed.


Ltac change_type T :=
  match goal with
    [ |- ?Σ ;;; ?Γ |- ?t : ?T0 ] => change (Σ ;;; Γ |- t : T)
  end.

Notation "u1 ⊔ u2" := (Universe.sup u1 u2) (at level 40).

Lemma boxed_type_translation_sound uG (Σ := ([],uG)) Γ Γ' σ A s :
  let ext := get_ctx_lift cat (of_global_context Σ) (last_condition σ) in
  wf_graph uG ->
  (of_global_context Σ) ## Γ => Γ' |= σ ->
  Σ ;;; Γ' ,,, ext |- [A]ᵗ Σ (σ ,, fcLift) : (⟦ tSort s ⟧ᵀ) Σ (σ ,, fcLift) ->
  Σ ;;; Γ' |- ⟦A⟧! Σ σ :  tSort (obj_univ ⊔ (hom_univ ⊔ s)).
Proof.
  simpl.
  intros wfG FcValid H.
  (* change_type (tSort (Universe.sup [Universe.Expr.set] [Universe.Expr.set])). *)
  unfold ft_type_boxed,otranslate_boxed_type. simpl.
  destruct (otranslate_type otranslate (of_global_context Σ)
            (extend_forcing_ctx {| f_context := σ; f_category := cat; f_translator := [] |} fcLift)
            tt A) eqn: HA.
  simpl. eapply type_Prod.
  - apply obj_sort_type.
  - replace ([Universe.Expr.set]) with
        (Universe.sup [Universe.Expr.set] [Universe.Expr.set]) by reflexivity.
    eapply type_Prod.
    pose ([vass pos_name rlv_obj cat.(cat_obj)]) as Γ''.
    eapply hom_sort_type.
    + change (Σ;;; Γ' ,,, Γ'' |- lift0 #|Γ''| (tRel (last_condition σ)) : lift0 #|Γ''| (cat.(cat_obj))).
      subst Σ. eapply weakening.
      * exact wfG.
      * eapply last_condition_sound;eauto.
    + solve_rel.
    + unfold mkOptApp. eapply type_translation_sound.
      * exact wfG.
      * constructor. eassumption.
      * apply H.
Qed.

Open Scope type_scope.

Definition lt_universe uG u1 u2 : bool := check_lt uG u1 u2.

Axiom type_Sort_s :
  forall Γ Σ s s', lt_universe (snd Σ) s s' = true -> Σ;;; Γ |- tSort s : tSort s'.

(* This is not quite true, because one can take uG to be [init_graph] *)
Axiom higher_universe_exists :
  forall uG s, wf_graph uG -> {s' | (lt_universe uG s s' = true)}.

Lemma univ_cumul uG (Σ := ([],uG)) Γ s s' s'' T:
  leq_universe uG s s' = true ->
  Σ;;; Γ |- T : tSort s ->
  Σ;;; Γ |- tSort s' : tSort s'' ->
  Σ;;; Γ |- T : tSort s'.
Proof.
  intros Hleq Hty Hsort.
  eapply type_Conv;simpl.
  + apply Hty.
  + eauto.
  + constructor. simpl. apply Hleq.
Qed.

Lemma translation_of_sort_sound uG (Σ := ([],uG)) Γ Γ' σ  s s' s'':
  wf_graph uG ->
  (of_global_context Σ) ## Γ => Γ' |= σ ->
  lt_universe uG s s' = true ->
  leq_universe uG (obj_univ ⊔ (hom_univ ⊔ s')) s'' = true ->
   Σ;;; Γ' |- [tSort s ]ᵗ Σ σ : (⟦ tSort s''⟧ᵀ) Σ σ.
Proof.
  intros wfG FcValid Huniv Huniv'.
  destruct (higher_universe_exists uG s'' wfG) as [s''' ?].
  (* Simplifying the applications in the type first*)
  unfold ft_term,otranslate,lambda_prefix,extend. cbn.
  eapply type_Conv;simpl.
  * eapply lam_q_f_sound;simpl.
    ** assumption.
    ** eassumption.
    ** eapply Π_q_f_lift_sound.
       *** exact wfG.
       *** apply type_Sort_s;eauto.
  * unfold ft_type. simpl in *. unfold mkOptApp.
    eapply type_App.
    ** eapply lam_q_f_sound;simpl.
       *** assumption.
       *** eassumption.
       *** apply Π_q_f_lift_sound.
           exact wfG.
           apply type_Sort_s with (s':=s''');eauto.
    ** simpl. (* typing_spine *)
           type_spine_step. eapply last_condition_sound;eauto.
           type_spine_step. apply id_hom_type. eapply last_condition_sound;eauto.
           apply type_spine_nil.
  * simpl. unfold ft_type. simpl. unfold mkOptApp.
    (* Abstract this reduction to a tactic *)
    eapply cumul_red_r. Focus 2.
    eapply red_beta. simpl.
    eapply cumul_red_r. Focus 2.
    eapply red_beta. simpl.
    eapply cumul_refl.
    simpl. rewrite Huniv'.
    (* rewrite leq_universe_refl. *)
    rewrite Nat.eqb_refl. reflexivity.
Qed.

Lemma unit_unique : forall t : unit, t = tt.
Proof. intros t;destruct t;reflexivity. Qed.

Lemma lt_universe_leq uG s1 s2 : lt_universe uG s1 s2 = true -> leq_universe uG s1 s2 = true.
Proof.
Admitted.

Lemma typed_term_sort uG (Σ := ([],uG)) Γ t T:
  type_local_env Σ Γ ->
  wf_graph uG ->
  Σ ;;; Γ |- t : T ->
  {s : universe &  Σ ;;; Γ |- T : tSort s}.
Proof.
  intros TyCtx wfG Ty.
  induction Ty.
  - (* Use [TyCtx] and something like [rewrite Checker.nth_error_Some_safe_nth.] *)
    admit.
  - admit.
  - auto.
Admitted.

Lemma prod_translation_sound uG (Σ := ([],uG)) (Σ' := Σ) Γ Γ' σ A B n s1 s2 r :
  let ext := get_ctx_lift cat (of_global_context Σ) (last_condition σ) in
  let σ' := (σ ,, fcLift) in
  let ext1 := get_ctx_lift cat (of_global_context Σ) (last_condition σ') in
  let v := vass n r (⟦A⟧! Σ (σ ,, fcLift)) in
  wf_graph uG ->
  (of_global_context Σ) ## Γ => Γ' |= σ ->
  Σ';;; Γ' ,,, ext ,,, ext1 |- [A]ᵗ Σ (σ' ,, fcLift) : (⟦ tSort s1 ⟧ᵀ) Σ (σ' ,, fcLift) ->
  Σ';;; Γ' ,,, ext ,, v |- [B]ᵗ Σ (σ' ,, fcVar) : (⟦ tSort s2 ⟧ᵀ) Σ (σ' ,, fcVar) ->
  Σ;;; Γ' |- [tProd n r A B ]ᵗ Σ σ : (⟦ tSort (s1 ⊔ s2) ⟧ᵀ) Σ σ.
Proof.
  intros ? ? ? ? wfG FcValid TyA TyB.
      unfold ft_type, ft_term.
    (* pose (get_ctx_lift cat (of_global_context Σ) (last_condition σ)) as ext. *)
    (* We first prove that boxed translation of a domain is sound, because we will use this fact
       two times later. *)
    assert (A_boxed: Σ ;;; Γ' ,,, ext |- ⟦A⟧! Σ σ' : tSort (obj_univ ⊔ (hom_univ ⊔ s1))).
    { eapply boxed_type_translation_sound.
      * exact wfG.
      * repeat constructor;eauto.
      * apply TyA;eauto. }
    destruct (higher_universe_exists uG (s1 ⊔ s2) wfG) as [s' ?].
    destruct (higher_universe_exists uG (obj_univ ⊔ (hom_univ ⊔ s')) wfG) as [s'' Hs''].
    eapply type_Conv.
    * simpl. eapply lam_q_f_sound;simpl.
      ** assumption.
      ** eassumption.
      ** apply type_Prod.
         *** eapply A_boxed.
         *** unfold mkOptApp. setctx Γ''.
             assert (BT: Σ ;;; Γ'' |- ⟦B⟧ᵀ Σ (σ ,, fcLift ,, fcVar) : tSort s2).
             { eapply type_translation_sound with (Γ := Γ,, vass n r A).
               + exact wfG.
               + subst Γ''. unfold snoc.
                 eapply fctx_valid_cons_var with (σ:=σ ,, fcLift).
                 constructor;auto.
               + apply TyB;eauto.
             }
             (* NOTE: rewriting with [unit_unique] in the goal doesn't work, so
                we rewrite in the assumption instead. *)
             unfold ft_type in BT.
             erewrite <- unit_unique in BT.
             apply BT.
    * apply lt_universe_leq in Hs''.
      eapply type_translation_sound;eauto.
      eapply translation_of_sort_sound;eauto.
    * eapply cumul_red_r. Focus 2. simpl.
      eapply red_beta. simpl.
      eapply cumul_red_r. Focus 2.
      eapply red_beta. simpl.
      eapply cumul_refl.
      simpl. rewrite Nat.eqb_refl. simpl.
        (* NOTE: works for sure if [s1] or [s2] are [Set] *)
        (* TODO : this is the only thing to fix, the rest is fine *)
        (* reflexivity. *)
        admit.
Admitted.

(* A version of the [prod_translation_sound] which assumes that *type* (ans not term)
   translations are sound *)
(* NOTE: the proof of the theorem [prod_translation_sound] should be an application of this theorem
   with additional work to construct the premises *)
Lemma prod_translation_sound_alt uG (Σ := ([],uG)) (Σ' := Σ) Γ Γ' σ A B n s1 s2 r :
  let ext := get_ctx_lift cat (of_global_context Σ) (last_condition σ) in
  let σ' := (σ ,, fcLift) in
  let ext1 := get_ctx_lift cat (of_global_context Σ) (last_condition σ') in
  let v := vass n r (⟦A⟧! Σ (σ ,, fcLift)) in
  wf_graph uG ->
  (of_global_context Σ) ## Γ => Γ' |= σ ->
  Σ';;; Γ' ,,, ext |- ⟦A⟧! Σ (σ ,, fcLift) : tSort s1 ->
  Σ';;; Γ' ,,, ext ,, v |- ⟦B⟧ᵀ Σ (σ ,, fcLift ,, fcVar) : tSort s2 ->
  Σ;;; Γ' |- [tProd n r A B ]ᵗ Σ σ : (⟦ tSort (s1 ⊔ s2) ⟧ᵀ) Σ σ.
Proof.
  intros ? ? ? ? wfG FcValid TyA TyB.
  unfold ft_type, ft_term.
  destruct (higher_universe_exists uG (s1 ⊔ s2) wfG) as [s' ?].
  destruct (higher_universe_exists uG (obj_univ ⊔ (hom_univ ⊔ s')) wfG) as [s'' Hs''].
  eapply type_Conv.
  * simpl. eapply lam_q_f_sound;simpl.
    ** assumption.
    ** eassumption.
    ** apply type_Prod.
       *** eapply TyA.
       *** unfold mkOptApp. setctx Γ''.
           unfold ft_type in TyB.
           erewrite <- unit_unique in TyB.
           eapply TyB.
  * apply lt_universe_leq in Hs''.
    eapply type_translation_sound;eauto.
    eapply translation_of_sort_sound;eauto.
  * unfold mkOptApp.
    eapply cumul_red_r. Focus 2.
      eapply red_beta. simpl.
      eapply cumul_red_r. Focus 2.
      eapply red_beta. simpl.
      eapply cumul_refl.
      simpl. rewrite Nat.eqb_refl. simpl.
      (* NOTE: works for sure if [s1] or [s2] are [Set] *)
      (* TODO : this is the only thing to fix, the rest is fine *)
      (* reflexivity. *)
      admit.
Admitted.

Definition cat_id_conv_r :=
  forall Σ Γ a b f,
    Σ ;;; Γ |- f ∘ (# a) <:: [a;a;b] : Hom(a,b) ->
    (Σ ;;; Γ |- (f ∘ (# a) <:: [a;a;b]) = f).

Definition cat_id_conv_l :=
  forall Σ Γ a b f,
    Σ ;;; Γ |- (# b) ∘ f <:: [a;b;b] : Hom(a,b) ->
    (Σ ;;; Γ |- ((# b) ∘ f <:: [a;b;b]) = f).


Lemma bin_app_typed Σ Γ u t1 t2 r1 r2 A B C nam1 nam2 :
  Σ ;;; Γ |- t1 : A ->
  Σ ;;; Γ |- t2 : B{0:=t1} ->
  Σ ;;; Γ |- u : tProd nam1 r1 A (tProd nam2 r2 B C) ->
  Σ ;;; Γ |- tApp u [t1;t2] : C {1:=t1} {0:=t2}.
Proof.
  intros HA HB Hu.
  econstructor.
  + eapply Hu.
  + eapply type_spine_const with (na :=nNamed "b") (relevance:=r1) (A:=A).
    * eapply cumul_refl. simpl in *. rewrite eq_term_refl. eapply leq_refl.
    * assumption.
    * eapply type_spine_const with (na :=nNamed "b") (relevance:=r2) (A:=B {0:= t1}).
      ** eapply cumul_refl. simpl in *. rewrite eq_term_refl. eapply leq_refl.
      ** assumption.
      ** econstructor.
Qed.

Lemma composition_typed Σ Γ a b c g f :
  Σ ;;; Γ |- a : cat.(cat_obj) ->
  Σ ;;; Γ |- b : cat.(cat_obj) ->
  Σ ;;; Γ |- c : cat.(cat_obj) ->
  Σ ;;; Γ |- f : Hom(a,b) ->
  Σ ;;; Γ |- g : Hom(b,c) ->
  Σ ;;; Γ |- g ∘ f <:: [a;b;c] : Hom(a,c).
Proof.
  econstructor.
    + eapply (cat_comp_type rlv_obj rlv_hom (nNamed "a") (nNamed "b") (nNamed "c")).
    + eapply type_spine_const with (na :=nNamed "a") (A:=cat.(cat_obj)) (relevance:=rlv_obj).
      - eapply cumul_refl. simpl in *. eapply leq_refl.
      - assumption.
      - simpl. eapply type_spine_const with (na :=nNamed "b") (A:=cat.(cat_obj))(relevance:=rlv_obj).
        * eapply cumul_refl. simpl in *. eapply leq_refl.
        * assumption.
        * simpl. eapply type_spine_const with (na :=nNamed "c") (A:=cat.(cat_obj))
                                              (relevance:=rlv_obj).
           ** eapply cumul_refl. simpl in *. eapply leq_refl.
           ** assumption.
           ** simpl. pose (((lift0 1) b){0:=c}) as x. rewrite lift0_p.
               eapply type_spine_const with (A:=Hom(x,c)).
               *** eapply cumul_refl. subst x. simpl in *.
                   repeat rewrite eq_term_refl. simpl. eapply leq_refl.
               *** subst x. econstructor.
                   **** eassumption.
                   **** eapply hom_sort_type. cbn.
                    Admitted.

Lemma composition_id_typed Σ Γ r_obj r_hom :
  let f := vass hom_name r_hom (tApp (tConst "Hom" []) [^1; ^0]) in
  let q := vass pos_name r_obj (tConst "Obj" []) in
  let p := vass pos_name r_obj (tConst "Obj" []) in
  Σ;;; Γ ,,, [f;q;p] |- (# ^1) ∘ (^0) <:: [^2; ^1; ^1] : Hom( ^2, ^1).
Proof.
  intros ? ?.
  econstructor.
    + eapply (cat_comp_type r_obj r_hom (nNamed "a") (nNamed "b") (nNamed "c")).
    + eapply type_spine_const with (na :=nNamed "a") (A:=cat.(cat_obj)) (relevance:=r_obj).
      - eapply cumul_refl. simpl in *. eapply leq_refl.
      - solve_rel.
      - eapply type_spine_const with (na :=nNamed "b") (A:=cat.(cat_obj)) (relevance:=r_obj).
        * eapply cumul_refl. simpl in *. eapply leq_refl.
        * solve_rel.
        * eapply type_spine_const with (na :=nNamed "c") (A:=cat.(cat_obj)) (relevance:=r_obj).
           ** eapply cumul_refl. simpl in *. eapply leq_refl.
           ** solve_rel.
           ** simpl. eapply type_spine_const with (na := nAnon) (A:=Hom(^1,^1)) (relevance:=r_hom).
               *** eapply cumul_refl. simpl. eapply leq_refl.
               *** apply id_hom_type. solve_rel.
               *** simpl. eapply type_spine_const with
                              (na := nAnon) (A:=Hom(^2,^1)) (relevance:=r_hom).
                   **** eapply cumul_refl. simpl. eapply leq_refl.
                   **** solve_rel.
                   **** econstructor.
Qed.

Definition default_fctx (σ : list forcing_condition) : forcing_context := mkFCtxt σ cat [].

Definition morphism_var_right' i n fctx : term :=
  let q := get_domain_var fctx n in
  morphism_var_alt_right cat q i (1+n) fctx.


Notation "'φ(' q ',' i ',' n ',' σ ')'" :=
  (morphism_var_alt_right cat q i (1+n) σ) (at level 20).

(** This is a step of unfolding of the "morphism for the variable [n]" function.
    See Def. 13 in the paper. This is a case for a morphism:
    [ (σ ∙ (q,f))(x) = f ∘ σ(x) ]
    Note, that in comparison with the paper, we use the usual order in the composition
    ([g ∘ f] means "[g] after [f]")
    Although, the proof is just refl, we keep it here to
    show how variable indices are actually calculated when unfolding. *)
Lemma morphism_var_unfold σ (σ' := [fcLift]) :
  forall n q i,
    φ(q,i,n,σ ∙ σ') = (^i) ∘ φ(q,2+i,n,σ) <:: [^q;^(2+i+σ.ₑ);^((σ ∙ σ').ₑ + i)].
Proof.
  intros n q i. reflexivity.
Qed.

Eval compute in (morphism_var_alt_right cat 0 1 0 [fcLift;fcVar;fcVar;fcLift;fcLift]).

Lemma morphism_var_0 q σ cat : forall i,
  morphism_var_alt_right cat q i 0 σ = tApp (cat_id cat) [^(i + get_domain_var_internal σ 0)].
Proof.
  induction σ;intros i.
  - cbn. rewrite plus_0_r. reflexivity.
  - simpl. destruct a.
    * simpl. rewrite IHσ.
      replace (S i + get_domain_var_internal σ 0)%nat with
          (i + S (get_domain_var_internal σ 0))%nat by omega. reflexivity.
    * simpl. replace (i+1)%nat with (S i) by omega. reflexivity.
Qed.

Lemma nat_compare_lt_Lt m n :
  m < n ->
  m ?= n = Lt.
Proof.
  intros;apply nat_compare_lt;omega.
Qed.

Lemma nat_compare_gt_Gt m n :
  m > n ->
  m ?= n = Gt.
Proof.
  intros;apply nat_compare_gt;omega.
Qed.

Lemma subst_morphism_gt t i j n σ q :
  j <= 1 ->
  j <= i ->
  j <= q ->
  φ(S q,S i,n,σ){j:=t} = φ(q,i,n,σ).
Proof.
  revert j. revert i. revert n.
  induction σ.
  - intros n i j Hj1 Hji Hjq.
     simpl. rewrite nat_compare_lt_Lt by omega. reflexivity.
  - intros n i j Hi1 Hji Hjq. destruct a.
    + simpl. destruct n.
      * repeat rewrite morphism_var_0. simpl.
        rewrite nat_compare_lt_Lt by omega.
        reflexivity.
      * apply IHσ;auto.
    + simpl. repeat rewrite nat_compare_lt_Lt by omega.
      repeat f_equal. apply IHσ;auto.
Qed.

Lemma get_domain_var_sound uG (Σ := ([],uG)) Γ Γ' σ n :
  (of_global_context Σ) ## Γ => Γ' |= σ ->
  Σ ;;; Γ' |-  (^dom(σ,n)) : cat.(cat_obj).
Proof.
Admitted.

Open Scope nat_scope.

Lemma domain_var_last_condition_0 σ : get_domain_var_internal σ 0 = σ.ₑ.
Proof.
  induction σ.
  - reflexivity.
  - destruct a.
    + simpl. congruence.
    + reflexivity.
Qed.

Lemma domain_var_gt_0 σ n :
  σ <> [] -> exists m, get_domain_var σ n = 1 + m.
Proof.
  Admitted.

Lemma lift_morphism_var x σ q i :
  lift0 1 (φ(q,i,x,σ)) = φ( 1 + q, 1+i, x, σ).
Proof.
  revert x. revert i.
  induction σ; intros i x.
  - reflexivity.
  - destruct a.
    + simpl.
      destruct x.
      * repeat rewrite morphism_var_0. reflexivity.
      * rewrite IHσ. reflexivity.
    + simpl. repeat f_equal. apply IHσ.
Qed.

Lemma morphism_var_sound_0 uG (Σ := ([],uG)) Γ Γ' σ x :
  wf_graph uG ->
  (of_global_context Σ) ## Γ => Γ' |= σ ->
  Σ ;;; Γ' |- φ(dom(σ,x),0,x,σ) : Hom(^dom(σ,x), ^σ.ₑ).
Proof.
  intros Hwf FcValid.
  revert x.
  induction FcValid;intros x.
  - cbn. apply id_hom_type. solve_rel.
  - cbn. destruct x.
    + rewrite morphism_var_0. rewrite domain_var_last_condition_0.
      apply id_hom_type.
      change (Σ;;; Γ' ,,, [v'] |- lift0 1 (^σ.ₑ) : lift0 1 (cat_obj cat)).
      eapply weakening;auto. eapply last_condition_sound;eauto.
    + change (Σ ;;; Γ' ,,, [v'] |- φ(1+dom(σ,x),1,x,σ) : lift0 1 Hom(^dom(σ,x), ^σ.ₑ)).
      rewrite <- lift_morphism_var.
      apply weakening. apply Hwf. apply IHFcValid.
  - simpl. econstructor.
    + eapply (cat_comp_type rlv_obj rlv_hom (nNamed "a") (nNamed "b") (nNamed "c")).
    + eapply type_spine_const with (na :=nNamed "a") (A:=cat.(cat_obj)) (relevance:=rlv_obj).
      * eapply cumul_refl. simpl in *. eapply leq_refl.
      * eapply get_domain_var_sound;eauto. econstructor;eauto.
      * eapply type_spine_const with (na :=nNamed "b") (A:=cat.(cat_obj)) (relevance:=rlv_obj).
        ** eapply cumul_refl. simpl in *. eapply leq_refl.
        ** pose [vass hom_name Relevant (tApp (tConst "Hom" []) [^S σ.ₑ; ^0]);
                 vass pos_name Relevant (tConst "Obj" [])] as Γ''.
           change (Σ;;; Γ' ,,, Γ''  |- lift0 2 (^(σ.ₑ)) : lift0 2 (cat_obj cat)).
           apply weakening;auto. eapply last_condition_sound;eauto.
        ** eapply type_spine_const with (na :=nNamed "c") (A:=cat.(cat_obj)) (relevance:=rlv_obj).
           *** eapply cumul_refl. simpl in *. eapply leq_refl.
           *** solve_rel.
           *** simpl. eapply type_spine_const with (A:=Hom(^(2+σ.ₑ),^1))
                                                   (relevance:=rlv_hom)(na:=nAnon).
               **** eapply cumul_refl. simpl in *. rewrite Nat.eqb_refl.
                    simpl. eapply leq_refl.
               **** solve_rel.
               **** simpl.
                    eapply type_spine_const with (A:=Hom(^dom( σ ∙ [fcLift], x),^S (S σ.ₑ)))
                                                 (relevance:=rlv_obj) (na:=nAnon).
                    ***** eapply cumul_refl. simpl in *. rewrite Nat.eqb_refl. rewrite Nat.eqb_refl.
                          simpl. eapply leq_refl.
                    ***** simpl. unfold get_domain_var. simpl. repeat rewrite <- lift_morphism_var.
                          setctx_2 Γ''.
                          change (Σ;;; Γ' ,,, Γ'' |- ((lift0 1) ((lift0 1) (φ(dom(σ,x),0,x,σ)))) :
                                                       lift0 2 (Hom(^dom(σ,x),^σ.ₑ))).
                          rewrite <- simpl_lift.
                          apply weakening;auto.
                    ***** constructor.
Qed.

Fixpoint vars_fctx (n : nat) : list forcing_condition :=
  match n with
  | O => []
  | S m => fcVar :: vars_fctx m
  end.

Definition nvars (σ : list forcing_condition) : nat :=
  fold_right (fun fc i => match fc with fcVar => 1 + i | fcLift => i end) 0 σ.


(** A generalization of morphism_var_sound_0 that works for any initial accumulator value [i] *)
Lemma morphism_var_sound_i uG (Σ := ([],uG)) Γ Γ0 Γ' Γ'' σ x i :
  wf_graph uG ->
  (of_global_context Σ) ## Γ ,,, Γ0 => Γ' ,,, Γ'' |= (σ ∙ vars_fctx i) ->
  #|Γ0| = i ->
  #|Γ''| = i ->
  Σ ;;; Γ' ,,, Γ'' |- φ(i+dom(σ,x),i,x,σ) : Hom(^(i+dom(σ,x)), ^(i+σ.ₑ)).
Proof.
  intros Hwf FcValid HΓ0 HΓ''.
  generalize dependent Γ''. generalize dependent Γ0.
  induction i;intros Γ0 HΓ0 Γ'' FcValid HΓ''.
  - eapply morphism_var_sound_0;eauto.
  - replace (S i + dom( σ, x)) with (1+(i + dom(σ,x))) by reflexivity.
    rewrite <- lift_morphism_var.
    destruct Γ''. inversion HΓ''. simpl in HΓ''.
    destruct Γ0. inversion HΓ0. simpl in HΓ0.
    change
    (Σ;;; Γ',,,Γ'',,, [c] |-(lift0 1)(φ(i + dom(σ,x), i, x, σ)) : (lift0 1 (Hom(^((i + dom(σ,x))), ^(i + σ.ₑ))))).
    apply weakening;auto.
    eapply IHi. inversion HΓ0. reflexivity.
    inversion FcValid;subst. eapply H0.
    inversion HΓ''. reflexivity.
Qed.


Lemma last_cond_gt_0 σ v ψ : exists m, (σ ∙ [v] ∙ ψ).ₑ = 1+m.
Proof.
Admitted.

Lemma last_condition_sum σ ψ :
  only_vars ψ = true ->
  (σ ∙ ψ).ₑ = fctx_size ψ + σ.ₑ.
Proof.
  intros H.
  induction ψ.
  - reflexivity.
  - destruct a.
    + simpl. rewrite IHψ;auto.
    + inversion H.
Qed.

Lemma size_sum σ ψ :
  fctx_size (σ ∙ ψ) = fctx_size σ + fctx_size ψ.
Proof.
  Admitted.

Lemma last_condition_contains_lift σ ψ :
  only_vars ψ = false ->
  (σ ∙ ψ).ₑ = ψ.ₑ.
Proof.
  intros H.
  induction ψ.
  - inversion H.
  - simpl. destruct a.
    + simpl in *. rewrite IHψ;auto.
    + reflexivity.
Qed.

Lemma size_gt_last_cond_lift σ :
  only_vars σ = false ->
  fctx_size σ > σ.ₑ.
Proof.
  intros H.
  induction σ.
  - inversion H.
  - destruct a.
    + simpl in H. simpl. assert (HH := IHσ H). omega.
    + simpl. omega.
Qed.

Fixpoint condition_in (n : nat) (σ : list forcing_condition) : bool :=
  match σ with
  | [] => false
  | fcVar :: σ' => condition_in (pred n) σ'
  | fcLift :: σ' => if (Nat.eqb n 0) then true else condition_in n σ'
  end.

Lemma condition_in_contains_lift σ n :
  condition_in n σ = true -> only_vars σ = false.
Proof.
  intros H.
  generalize dependent n.
  induction σ; intros n H.
  - inversion H.
  - destruct a.
    + simpl in *. eauto.
    + reflexivity.
Qed.

Lemma dom_condition_in_fctx σ ψ n :
  condition_in (1+n) ψ = true -> dom(σ ∙ ψ,n) = dom(ψ,n).
Proof.
  intros H.
  generalize dependent n.
  induction ψ; intros n H.
  - inversion H.
  - destruct a.
    + destruct n.
      * cbn. do 2 rewrite domain_var_last_condition_0.
        simpl in H.
        assert (H1 : only_vars ψ = false) by (eapply condition_in_contains_lift;eauto).
        change (S (σ ∙ ψ).ₑ = S ψ.ₑ).
        rewrite last_condition_contains_lift;auto.
      * cbn. apply f_equal. apply IHψ;auto.
    + cbn. do 2 apply f_equal. simpl in H. apply IHψ;auto.
Qed.

Lemma fctx_size_gt_dom σ n :
  condition_in (1+n) σ = true -> fctx_size σ > dom(σ,n).
Proof.
  revert n.
  induction σ;intros n H.
  - inversion H.
  - destruct a.
    + destruct n.
      * simpl in H. simpl. unfold get_domain_var. simpl. apply gt_n_S.
Admitted.

Lemma fctx_size_lt_dom σ ψ n :
  only_vars ψ = true ->
  fctx_size ψ < dom(σ∙[fcLift]∙ψ,n).
Proof.
  revert n.
  induction ψ;intros n Hv.
  - cbn. omega.
  - destruct a.
    + unfold get_domain_var. simpl.
      destruct n.
      * rewrite domain_var_last_condition_0. simpl in Hv.
        rewrite last_condition_sum by assumption. simpl. omega.
      * simpl. apply gt_n_S. now apply IHψ.
    + unfold get_domain_var. simpl. repeat apply gt_n_S. now apply IHψ.
Qed.

Lemma condition_in_0_contains_lift σ :
  only_vars σ = false ->
  condition_in 0 σ = true.
Proof.
  induction σ; intros H.
  - inversion H.
  - destruct a;easy.
Qed.

Lemma condition_in_0_only_vars σ :
  condition_in 0 σ = false ->
  only_vars σ = true.
Proof.
    induction σ; intros H.
  - reflexivity.
  - destruct a;easy.
Qed.

Lemma dom_0_eq_size σ :
  only_vars σ = true ->
  get_domain_var_internal σ 0 = fctx_size σ.
Proof.
  induction σ;intros.
  - reflexivity.
  - destruct a.
    + simpl;easy.
    + inversion H.
Qed.

Lemma dom_eq_size σ n :
  condition_in (1+n) σ = false ->
  dom(σ,n) = fctx_size σ.
Proof.
  revert n.
  induction σ; intros n H.
  - reflexivity.
  - destruct a.
    + unfold get_domain_var. simpl in *. apply f_equal.
      destruct n.
      * assert (only_vars σ = true) by now apply condition_in_0_only_vars.
        now apply dom_0_eq_size.
      * now apply IHσ.
    + unfold get_domain_var. simpl in *. repeat apply f_equal.
      now apply IHσ.
Qed.

(* WARNING: might be false in the peresent form and requires additional assumptions :) *)
Lemma dom_lift_concat_only_vars_eq σ ψ n :
  condition_in (1 + n) ψ = false ->
  dom(σ∙[fcLift]∙ψ,n) = dom(σ∙ψ∙[fcLift],n).
Proof.
  revert n.
  induction ψ; intros n H.
  - reflexivity.
  - destruct a.
    + simpl in  H. cbn. apply f_equal.
      destruct n.
Admitted.

Import Ring.

Lemma dom_sum' σ ψ n :
  only_vars ψ = true ->
  get_domain_var_internal (σ∙ψ) n = fctx_size ψ + get_domain_var_internal σ (n-#|ψ|).
Proof.
  revert n.
  induction ψ; intros n Hv.
  - simpl in *. replace (n-0) with n by omega. reflexivity.
  - destruct a.
    + simpl in *. apply f_equal.
      replace (n - S #|ψ|) with (pred n - #|ψ|) by omega.
      now apply IHψ.
    + simpl. inversion Hv.
Qed.

Lemma condition_in_0_n n σ:
  condition_in 0 σ = false ->
  condition_in n σ = false.
Proof.
  revert n.
  induction σ; intros n H.
  - reflexivity.
  - destruct a.
    + simpl in *. now apply IHσ.
    + inversion H.
Qed.

Lemma dom_sum'' σ ψ n :
  condition_in n ψ = false ->
  exists m ,
    get_domain_var_internal (σ∙ψ) n = fctx_size ψ + get_domain_var_internal σ m.
Proof.
  revert n.
  induction ψ; intros n Hv.
  - simpl in *. now eexists.
  - destruct a.
    + simpl in *. assert (HH:= IHψ _ Hv ).
      destruct HH as [m Hm]. exists m. congruence.
    + simpl in *. destruct n.
      * inversion Hv.
      * simpl in *.
        simpl in *. assert (HH:= IHψ _ Hv ).
        destruct HH as [m Hm].
        exists m. congruence.
Qed.

Lemma dom_sum''' σ ψ n :
  condition_in n ψ = false ->
  1+nvars ψ > n ->
  get_domain_var_internal (σ∙ψ) n = fctx_size ψ + get_domain_var_internal σ 0.
Proof.
  revert n.
  induction ψ; intros n Hv Hvars.
  - simpl in *. destruct n. reflexivity. inversion_clear Hvars. inversion H.
  - destruct a.
    + simpl.
      (* apply gt_S_n in Hvars. *)
      apply f_equal.
      destruct n.
      * simpl. repeat rewrite domain_var_last_condition_0.
        rewrite last_condition_sum. omega.
        now apply condition_in_0_only_vars.
      * simpl. apply IHψ;auto. simpl in Hvars. omega.
    + simpl in *. destruct n.
      * inversion Hv.
      * simpl in *.
        simpl in *. repeat apply f_equal.
        now apply IHψ.
Qed.

Lemma dom_sum_lift σ ψ n :
  condition_in n ψ = false ->
  1+nvars ψ > n ->
  get_domain_var_internal (σ∙[fcLift]∙ψ) n = 1+fctx_size ψ.
Proof.
  intros. rewrite dom_sum''' by assumption. simpl.  omega.
Qed.

Lemma dom_sum σ ψ n :
  only_vars ψ = true ->
  dom(σ∙ψ,n) = fctx_size ψ + get_domain_var_internal σ (S n-#|ψ|).
Proof.
  intros.  now apply dom_sum'.
Qed.

Lemma fctx_size_gt_dom_lifts σ ψ n :
  condition_in (1+n) ψ = false ->
  fctx_size ψ < dom(σ∙[fcLift]∙ψ,n).
Proof.
  intros.
  generalize dependent n.
  induction ψ; intros n H.
  - cbn. omega.
  - destruct a.
    + unfold get_domain_var. simpl in *.
      destruct n.
      * assert (only_vars ψ = true) by now apply condition_in_0_only_vars.
        apply lt_n_S. rewrite domain_var_last_condition_0.
        rewrite last_condition_sum by assumption.
        simpl. omega.
      * apply gt_n_S. now apply IHψ.
    + unfold get_domain_var. simpl in *. repeat apply gt_n_S. now apply IHψ.
Qed.


Lemma fctx_size_gt_dom_lifts_S σ ψ n :
  condition_in (1+n) ψ = false ->
  nvars ψ <= n ->
  1+fctx_size ψ < dom(σ∙[fcLift]∙ψ,n).
Proof.
  intros.
  generalize dependent n.
  induction ψ; intros n H Hvars.
  - cbn. omega.
  - destruct a.
    + unfold get_domain_var. simpl in *.
      destruct n.
      * assert (only_vars ψ = true) by now apply condition_in_0_only_vars.
        apply lt_n_S. rewrite domain_var_last_condition_0.
        rewrite last_condition_sum by assumption.
        simpl in *. inversion Hvars.
      * apply gt_n_S. now apply IHψ.
    + unfold get_domain_var. simpl in *. repeat apply gt_n_S. now apply IHψ.
Qed.


Conjecture congr_cumul_app_l : forall Σ Γ M1 M2 Ns,
    cumul Σ Γ M1 M2 ->
    cumul Σ Γ (tApp M1 Ns) (tApp M2 Ns).

Conjecture congr_cumul_app_r : forall Σ Γ M Ns1 Ns2,
    Forall2 (cumul Σ Γ) Ns1 Ns2 ->
    cumul Σ Γ (tApp M Ns1) (tApp M Ns2).

Tactic Notation "fold_ft_notation" :=
  repeat
    (match goal with
     | |- context [(snd (otranslate (Environ.of_global_context ?Σ) (mkFCtxt ?σ ?cat []) ?v ?c))] =>
       change (snd (otranslate (Environ.of_global_context Σ) (mkFCtxt σ cat []) v c))
         with ([c]ᵗ Σ σ)
     end).

Tactic Notation "fold_morph_var_notation" :=
  repeat
    (match goal with
     | |- context [morphism_var_alt_right ?cat ?q ?i (S ?n) ?σ] =>
       change(morphism_var_alt_right cat q i (S n) σ) with (φ(q,i,n,σ))
     end).

Tactic Notation "fold_domain_var_notation" :=
  repeat
    (match goal with
     | |- context [get_domain_var_internal ?fctx (S ?n)] => change (get_domain_var_internal fctx (S n)) with dom(fctx,n)
     end).

Tactic Notation "fold_fctx_notation" :=
  repeat
    (match goal with
     | |- context [?xs ++ ?ys] =>
       match type of xs with
       | list forcing_condition => change (xs ++ ys) with (ys∙xs)
       end
     end).

Tactic Notation "fold_fctx_notation_singleton" :=
  repeat
    (match goal with
     | |- context [?x :: ?xs] =>
       match type of x with
       | forcing_condition =>
         match xs with
         | [] => idtac
         | _ => change (x :: xs) with (xs∙[x])
         end
       end
     | |- context [?x :: ?xs ∙ ?ys] =>
       match type of x with
       | forcing_condition =>
         match xs with
         | [] => idtac
         | _ => change (x :: xs ∙ ys) with (xs∙[x]∙ys)
         end
       end
     end).

Tactic Notation "fold_fctx_notation_singleton1" :=
  repeat
    (match goal with
     | |- context [?x :: ?xs ∙ ?ys] =>
       match type of x with
       | forcing_condition =>
         match xs with
         | [] => idtac
         | _ => change (x :: xs ∙ ys) with (xs∙[x]∙ys)
         end
       end
     end).

Tactic Notation "fold_notation" :=
  fold_morph_var_notation; fold_domain_var_notation;
  fold_fctx_notation;fold_fctx_notation_singleton;fold_fctx_notation_singleton1;
  fold_ft_notation.


Tactic Notation "solve_cumul_refl" :=
  eapply cumul_refl; simpl; repeat rewrite Nat.eqb_refl; (reflexivity || eapply leq_refl).


(* Tries to solve as much as possible of the application:
   [Σ ;;; Γ |- tApp M [N11;N12;N13...,N1n] <= tApp M [N21;N22;N23...,N2n]
by applying congruence and resolving subgoals like [N1i <= N2i] by [cumul_refl] *)
Ltac simpl_cumul_app_congr :=
  let rec solve_rec := apply Forall2_cons;
                       [> try solve_cumul_refl | (solve_rec ||apply Forall2_refl)]
  in apply congr_cumul_app_r; solve_rec.

Lemma morph_var_subst σ n uG (Σ := ([],uG)) Γ Γ' ψ :
  let q := 1 + fctx_size ψ in
  let f := fctx_size ψ in
  cat_id_conv_l ->
  wf_graph uG ->
  (of_global_context Σ) ## Γ => Γ' |= (σ ∙ ψ) ->
  Σ ;;; Γ' |- φ(dom(σ∙ψ,n),0,n, σ∙ψ) <= φ(dom(σ∙[fcLift] ∙ ψ,n),0,n,σ∙[fcLift]∙ψ){q:=^σ.ₑ}{f:= # ^σ.ₑ}.
Proof.
  intros ? ? id_left Hwf FcValid.
  subst q. subst f.
  revert n. generalize dependent Γ'. generalize dependent Γ.
  induction ψ;intros Γ Γ' FcValid n.
  - unfold get_domain_var. simpl.
    erewrite subst_morphism_gt;eauto;try omega.
    erewrite subst_morphism_gt;eauto;try omega.
    eapply id_left.
    econstructor.
    + eapply (cat_comp_type rlv_obj rlv_hom (nNamed "a") (nNamed "b") (nNamed "c")).
    + eapply type_spine_const with (na :=nNamed "a") (A:=cat.(cat_obj)) (relevance:=rlv_obj).
      * eapply cumul_refl. simpl in *. eapply leq_refl.
      * eapply get_domain_var_sound;eauto.
      * eapply type_spine_const with (na :=nNamed "b") (A:=cat.(cat_obj)) (relevance:=rlv_obj).
        ** eapply cumul_refl. simpl in *. eapply leq_refl.
        ** eapply last_condition_sound;eauto.
        ** eapply type_spine_const with (na :=nNamed "c") (A:=cat.(cat_obj)) (relevance:=rlv_obj).
           *** eapply cumul_refl. simpl in *. eapply leq_refl.
           *** eapply last_condition_sound;eauto.
           *** simpl. eapply type_spine_const with (A:=Hom(^σ.ₑ,^σ.ₑ)) (na:=nAnon) (relevance:=rlv_hom).
               **** eapply cumul_refl. simpl in *. rewrite Nat.eqb_refl.
                    simpl. eapply leq_refl.
               **** eapply id_hom_type. eapply last_condition_sound;eauto.
               **** simpl.
                    eapply type_spine_const with (A:=Hom(^get_domain_var_internal σ (S n),^σ.ₑ))
                                                 (na:=nAnon)
                                                 (relevance:=rlv_hom).
                    ***** eapply cumul_refl. simpl in *. rewrite Nat.eqb_refl. rewrite Nat.eqb_refl.
                          simpl. eapply leq_refl.
                    ***** eapply morphism_var_sound_0;eauto.
                    ***** constructor.
  - destruct a.
    + destruct n.
      * simpl. repeat rewrite morphism_var_0.
        repeat rewrite domain_var_last_condition_0. simpl.
        destruct (last_cond_gt_0 σ fcLift ψ) as [m HH].
        change (fcLift :: σ ∙ ψ) with (σ ∙ [fcLift] ∙ ψ).
        rewrite HH.
        destruct (only_vars ψ) eqn:Hψ.
        ** simpl.
           rewrite last_condition_sum in *;auto. simpl in HH.
           assert (Hm : m = fctx_size ψ) by omega. subst m.
           rewrite Nat.compare_refl. simpl.
           rewrite nat_compare_lt_Lt by omega.
           eapply cumul_refl. simpl in *. rewrite Nat.eqb_refl. reflexivity.
        ** simpl. assert (Hσ' := last_condition_contains_lift (σ ∙ [fcLift]) _ Hψ).
           assert (fctx_size ψ > ψ.ₑ) by (apply size_gt_last_cond_lift;auto).
           rewrite nat_compare_gt_Gt by omega. simpl.
           rewrite nat_compare_gt_Gt by omega.
           eapply cumul_refl.
           rewrite (last_condition_contains_lift σ) by assumption.
           rewrite (last_condition_contains_lift (σ ∙ [fcLift])) in HH by assumption.
           simpl. rewrite HH. rewrite Nat.eqb_refl. reflexivity.
      * cbn. fold_notation.
        repeat rewrite <- lift_morphism_var.
        repeat rewrite commut_lift_subst.
        inversion FcValid. subst.
        change (Γ'0,, v') with (Γ'0 ,,, [v']).
        apply weakening_cumul;auto.
        eapply IHψ;eauto.
    +  simpl. fold_notation.
       assert (not_empty : (σ ∙ [fcLift] ∙ ψ) <> []).
       { destruct ψ; unfold not; intros H; inversion H. }
       destruct (domain_var_gt_0 (σ ∙ [fcLift] ∙ ψ) n not_empty) as [m HH].
       rewrite HH.
       destruct (last_cond_gt_0 σ fcLift ψ) as [m' HH'].
       destruct (condition_in (1+n) ψ) eqn: Hψ.
       simpl.
       * rewrite dom_condition_in_fctx in HH by assumption.
         assert (fctx_size ψ > dom(ψ,n)) by (apply fctx_size_gt_dom;auto).
         rewrite nat_compare_gt_Gt by omega. simpl.
         fold_notation.
         rewrite dom_condition_in_fctx with (ψ :=ψ) by assumption.
         rewrite nat_compare_gt_Gt by omega. simpl.
         assert (Hψ' : only_vars ψ = false) by (eapply condition_in_contains_lift;eassumption).
         fold_notation.
         rewrite HH'. simpl.
         assert (Hσ' := last_condition_contains_lift (σ ∙ [fcLift]) _ Hψ').
         assert (fctx_size ψ > ψ.ₑ) by (apply size_gt_last_cond_lift;auto).
         rewrite nat_compare_gt_Gt by omega. simpl.
         rewrite nat_compare_gt_Gt by omega.
         cbn. fold_notation.
         replace (^S (S dom( σ ∙ ψ, n))) with (^S (S dom(ψ, n)))
           by (now rewrite dom_condition_in_fctx).
         replace (^S (S dom( (σ ∙ [fcLift]) ∙ ψ, n))) with (^S (S dom(ψ, n)))
           by (now rewrite dom_condition_in_fctx).
         rewrite (last_condition_contains_lift σ) by assumption.
         rewrite (last_condition_contains_lift (σ ∙ [fcLift])) in HH' by assumption.
         simpl in HH'. rewrite <- HH'.
         simpl_cumul_app_congr.
         inversion FcValid;subst.
         repeat rewrite <- lift_morphism_var.
         repeat rewrite commut_lift_subst. repeat rewrite <- simpl_lift.
         apply weakening_cumul;auto.
         now eapply IHψ.
       * destruct (only_vars ψ) eqn:Hvψ.
         ** destruct (le_lt_dec (nvars ψ) n) as [Hle | Hlt].
            *** simpl.
                assert (S (fctx_size ψ) < dom(σ∙[fcLift]∙ψ,n)) by now apply fctx_size_gt_dom_lifts_S.
                rewrite nat_compare_lt_Lt by omega. simpl.
                rewrite nat_compare_lt_Lt by omega.
                replace (S m) with (dom(σ∙[fcLift]∙ψ,n)) by omega.
                rewrite dom_lift_concat_only_vars_eq by assumption. simpl.
                fold_notation.
                rewrite HH'. simpl.
                rewrite last_condition_sum in * by assumption. simpl in HH'.
                assert (Hm : m' = fctx_size ψ) by omega. subst m'.
                rewrite Nat.compare_refl. simpl.
                rewrite nat_compare_lt_Lt by omega.
                simpl_cumul_app_congr.
                cbn. fold_notation.
                inversion FcValid. subst.
                repeat rewrite <- lift_morphism_var.
                repeat rewrite commut_lift_subst.
                repeat rewrite <- simpl_lift.
                apply weakening_cumul;auto.
                eapply IHψ;eauto.
            *** simpl.
                assert (Heq : fctx_size ψ = m).
                { unfold get_domain_var in HH.
                  rewrite dom_sum_lift in HH by assumption ||  omega. auto. }
                rewrite Heq.
                rewrite Nat.compare_refl. simpl.
                rewrite nat_compare_lt_Lt by omega. rewrite <- Heq in *.
                cbn. fold_notation.
                assert (HltS : 1+nvars ψ > 1 +n) by omega.
                assert (Hsum := dom_sum''' σ ψ _ Hψ HltS).
                rewrite Hsum at 1.
                simpl. rewrite domain_var_last_condition_0.
                change (fcLift :: σ ∙ ψ) with (σ ∙ [fcLift] ∙ ψ).
                rewrite HH'. simpl.
                rewrite last_condition_sum in *;auto. simpl in HH'.
                assert (Hm : m' = fctx_size ψ) by omega. subst m'.
                rewrite Nat.compare_refl. simpl.
                rewrite nat_compare_lt_Lt by omega.
                simpl_cumul_app_congr.
                fold_notation.
                inversion FcValid. subst.
                repeat rewrite <- lift_morphism_var.
                repeat rewrite commut_lift_subst.
                repeat rewrite <- simpl_lift.
                apply weakening_cumul;auto.
                eapply IHψ;eauto.
         ** (* only_vars ψ = false *)
            simpl.
            destruct (le_lt_dec (nvars ψ) n) as [Hle | Hlt].
            *** assert (S (fctx_size ψ) < dom(σ∙[fcLift]∙ψ,n)) by now apply fctx_size_gt_dom_lifts_S.
                rewrite nat_compare_lt_Lt by omega.
                simpl. rewrite nat_compare_lt_Lt by omega.
                replace (S m) with (dom( (σ ∙ [fcLift]) ∙ ψ, n)) by omega.
                rewrite dom_lift_concat_only_vars_eq by assumption.
                cbn. fold_notation.
                rewrite HH'. simpl.
                assert (Hσ' := last_condition_contains_lift (σ ∙ [fcLift]) _ Hvψ).
                assert (fctx_size ψ > ψ.ₑ) by (apply size_gt_last_cond_lift;auto).
                rewrite nat_compare_gt_Gt by omega. simpl.
                rewrite nat_compare_gt_Gt by omega.
                rewrite (last_condition_contains_lift σ) by assumption.
                rewrite (last_condition_contains_lift (σ ∙ [fcLift])) in HH' by assumption.
                replace (S m') with ψ.ₑ by omega.
                simpl_cumul_app_congr.
                fold_notation.
                inversion FcValid. subst.
                repeat rewrite <- lift_morphism_var.
                repeat rewrite commut_lift_subst.
                repeat rewrite <- simpl_lift.
                apply weakening_cumul;auto.
                eapply IHψ;eauto.
            *** assert (Heq : fctx_size ψ = m).
                { unfold get_domain_var in HH.
                  rewrite dom_sum_lift in HH by assumption ||  omega. auto. }
                rewrite Heq. rewrite Nat.compare_refl. simpl.
                rewrite nat_compare_lt_Lt by omega. rewrite <- Heq in *.
                cbn. fold_notation.
                assert (HltS : 1+nvars ψ > 1 +n) by omega.
                assert (Hsum := dom_sum''' σ ψ _ Hψ HltS).
                unfold get_domain_var at 1. rewrite Hsum.
                simpl. rewrite domain_var_last_condition_0.
                change (fcLift :: σ ∙ ψ) with (σ ∙ [fcLift] ∙ ψ).
                rewrite HH'. simpl.
                rewrite last_condition_contains_lift in *;auto. simpl in HH'.
                assert (fctx_size ψ > ψ.ₑ) by now apply size_gt_last_cond_lift.
                rewrite nat_compare_gt_Gt by omega. simpl.
                rewrite nat_compare_gt_Gt by omega.
                rewrite HH'. simpl.
                simpl_cumul_app_congr.
                fold_notation.
                inversion FcValid. subst.
                repeat rewrite <- lift_morphism_var.
                repeat rewrite commut_lift_subst.
                repeat rewrite <- simpl_lift.
                apply weakening_cumul;auto.
                eapply IHψ;eauto.
Qed.

(* TODO: Move to utils *)
Lemma universe_equal_refl u :
  Universe.equal u u = true.
Proof.
  induction u.
  - reflexivity.
  - simpl. rewrite univ_expr_eq_refl. auto.
Qed.

(* TODO: Move to utils *)
Lemma eq_universe_refl g u :
  eq_universe g u u = true.
Proof.
  unfold eq_universe.
  rewrite universe_equal_refl. reflexivity.
Qed.

Lemma forcing_cond_subst_id uG (Σ := ([],uG)) t σ ψ Γ Γ' :
  let q := 1 + fctx_size ψ in
  let f := fctx_size ψ in
  cat_id_conv_l ->
  wf_graph uG ->
  (of_global_context Σ) ## Γ => Γ' |= (σ ∙ ψ) ->
  Σ ;;; Γ' |- ([t]ᵗ Σ (σ∙ψ)) <= ([t]ᵗ Σ (σ∙[fcLift]∙ψ)){q:=^σ.ₑ}{f:= # ^σ.ₑ}.
Proof.
  induction t;intros ? ? id_left Hwf FCvalid.
  - (* tRel *)
    unfold ft_term,otranslate,snd. unfold translate_var. unfold morphism_var_right.
    replace (1+n) with (S n) by reflexivity. fold_notation. simpl.
    admit.
    (* NOTE: if we want to prove this for any [ψ], we first should show some
       properties of [get_var_sift]*)
    (* simpl_cumul_app_congr. fold_notation. *)
    (* change (Σ;;; Γ' |- φ(dom(σ∙ψ,n),0,n,σ∙ψ) <=  φ(dom(σ∙[fcLift]∙ψ,n),0,n, σ∙[fcLift]∙ψ) {q := ^σ.ₑ} {f := # ^σ.ₑ}). now eapply morph_var_subst with (ψ := [fcLift]). *)
  - admit. (* [tVar] not supported*)
  - admit. (* [tMeta] not supported*)
  - admit. (* [tEvar] not supported*)
  - (* tSort *) constructor. simpl. admit.
                (* apply eq_universe_refl. *)
Admitted.

Lemma forcing_typing_soundness uG (Σ := ([],uG)) Γ Γ' t T σ :
  cat_id_conv_l ->
  wf_graph uG ->
  (of_global_context Σ) ## Γ => Γ' |= σ ->
  Σ ;;; Γ |- t : T ->
  let Σ' := Σ in
  Σ' ;;; Γ' |- ([t]ᵗ Σ σ) : (⟦T⟧ᵀ Σ σ).
Proof.
  intros id_left wfG FcValid Ty.
  generalize dependent Γ'.
  generalize dependent σ.
  induction Ty; intros σ Γ' FcValid; simpl.
  - (* -- Variables -- *)
    simpl. unfold ft_term,ft_type. simpl. unfold translate_var. simpl.
    eapply type_Conv.
    + eapply type_App.
      * (* something about [get_var_shift] with relation to the valid forcing context *)  admit.
      * (* stuff about [morph_var]  *) admit.
    + admit.
    + admit.
  - (* -- Sorts -- *)
    eapply translation_of_sort_sound with
        (s' := (Universe.super l));eauto.
    (* Admit for now assumptions about how the universe levels are related. *)
    admit.
    admit.
  - admit.
  - (* -- Products -- *)
    eapply prod_translation_sound.
    * exact wfG.
    * eapply FcValid.
    * apply IHTy1;repeat constructor;auto.
    * apply IHTy2;repeat constructor;auto.
  - (* -- Lambda -- *)
    pose (get_ctx_lift cat (of_global_context Σ) (last_condition σ)) as ext.
    pose (σ ,, fcLift) as σ'.
    assert
    (TyCtxExt' : type_local_env Σ (Γ' ,,, ext ,, vass n relevance (⟦t⟧! Σ σ'))).
    { constructor.
      * (* NOTE: here we need the fact that [Γ'] is well-formed *) admit.
      * fold (app (A:=context_decl)). econstructor.
        unfold decl_type,vass.
        eapply boxed_type_translation_sound.
        ** exact wfG.
        ** repeat constructor;eauto.
        ** eapply IHTy1;eauto;repeat constructor;auto. }
    assert
      ( Tyb_tr : Σ;;; Γ' ,,, ext ,, vass n relevance (⟦t⟧! Σ σ') |-
        [b]ᵗ Σ (σ' ,, fcVar) : (⟦ bty ⟧ᵀ) Σ (σ' ,, fcVar)).
    { eapply IHTy2 with (Γ':=Γ' ,,, ext ,, vass n relevance (⟦t⟧! Σ σ')).
      constructor;eauto. eapply fctx_valid_cons_lift. eauto. }
    destruct (typed_term_sort uG _
             ([b ]ᵗ Σ (σ' ,, fcVar)) (⟦ bty ⟧ᵀ Σ (σ' ,, fcVar)) TyCtxExt' wfG Tyb_tr) as [s Hs].
    evar (s' : universe).
    assert (Ty_bty : Σ;;; Γ' |- (⟦ tProd n relevance t bty ⟧ᵀ) Σ σ : tSort ?s').
    { eapply type_translation_sound;eauto.
      eapply prod_translation_sound_alt;eauto.
      ** eapply boxed_type_translation_sound.
         *** exact wfG.
         *** repeat constructor;eauto.
         *** eapply IHTy1;eauto;repeat constructor;auto. }
    (* unfold ft_type, ft_term. simpl. *)
    eapply type_Conv;eauto.
    * eapply type_Lambda;fold otranslate in *.
      ** eapply boxed_type_translation_sound.
         *** exact wfG.
         *** repeat constructor;eauto.
         *** apply IHTy1;eauto.
             repeat constructor;eauto.
      ** setctx Γ''.
         assert (H : Σ;;; Γ'' |- [b ]ᵗ Σ (σ ,, fcVar) : (⟦ bty ⟧ᵀ) Σ (σ ,, fcVar)).
         { eapply IHTy2 with (σ := σ,,fcVar) (Γ':=Γ'').
           change (of_global_context Σ ## Γ,, vass n relevance t =>
                   Γ' ,, vass n relevance (⟦t⟧! Σ σ) |= σ,, fcVar).
           eapply fctx_valid_cons_var;eauto. }
         unfold ft_term in H.
         erewrite <- unit_unique in H.
         eapply H.
    * (* NOTE: do something with names *)
      assert (Eq_names : n = n'). admit.
      rewrite Eq_names in Ty_bty. apply Ty_bty.
    * fold otranslate. instantiate (1:=n').
      change (Σ;;; Γ' |- tProd n' relevance (⟦t⟧! Σ σ)
       ((⟦ bty ⟧ᵀ) Σ (σ,, fcVar)) <= (⟦ tProd n' relevance t bty ⟧ᵀ) Σ σ).
      eapply cumul_red_r. Focus 2. unfold ft_type,mkOptApp,otranslate_type,snd. simpl.
      eapply red_beta. simpl.
      eapply cumul_red_r. Focus 2.
      eapply red_beta. simpl.
      apply congr_cumul_prod.
      ** apply congr_cumul_prod. eapply cumul_refl;auto.
         simpl. apply congr_cumul_prod.
         *** eapply cumul_refl;auto. simpl. rewrite Nat.eqb_refl. reflexivity.
         *** apply congr_cumul_app_l.
             change (Σ ;;; Γ' ,,, ext |-  ([t ]ᵗ Σ σ') <=
                                          (([t]ᵗ Σ (σ'∙[fcLift])){3 :=^σ.ₑ}{2 := # ^σ.ₑ})).
             assert (FcValid' : of_global_context Σ ## Γ => Γ' ,,, ext |= (σ ∙ [fcLift])) by
                  (repeat econstructor;eauto).
             now apply forcing_cond_subst_id with (ψ:=[fcLift]) (Γ:=Γ).
      ** unfold ft_type. simpl. unfold mkOptApp. simpl.
         unfold add_variable,extend_forcing_ctx. simpl.
         pose (vass n' relevance ((⟦ t ⟧!) Σ σ)) as v'.
         pose (vass n relevance t) as t'.
         assert (H : Σ;;; Γ',, v' |- tApp ([bty ]ᵗ Σ (σ∙[fcVar])) [^S σ.ₑ; # ^S σ.ₑ] <=
                                 tApp (([bty ]ᵗ Σ (σ∙[fcLift]∙[fcVar])){2:=^σ.ₑ}{1:=# ^σ.ₑ})
                                      [^S σ.ₑ; # (^S σ.ₑ)]).
         eapply congr_cumul_app_l.
         assert (FcValid' : of_global_context Σ ## Γ ,, t' => Γ' ,, v' |= (σ ∙ [fcVar]))
           by (repeat econstructor;eauto).
         now apply forcing_cond_subst_id with (Γ:=Γ,,t').
         unfold ft_term in H. erewrite <- unit_unique in H at 2.
         eapply H.
  - (* tLetIn *)
      admit.
Admitted.
