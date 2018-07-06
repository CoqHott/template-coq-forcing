Require Import Omega.
Require Import Forcing.TemplateForcing.
Require Import Template.Typing Template.Ast Template.WeakSubst Template.LiftSubst.
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


Definition leq_refl sigma t : leq_term sigma t t = true.
  induction t.
Admitted.

Definition cat_obj := tConst "Obj" [].
Definition cat_hom := tConst "Hom" [].
Definition id_hom := tConst "Id_hom" [].
Definition sort_set := tSort [Universe.Expr.set].

(** We assume the following sorts for the objects and morphisms of the base category *)
Axiom obj_sort : forall Σ Γ, Σ ;;; Γ |- cat_obj : sort_set.
Axiom hom_sort : forall Σ Γ t1 t2,
    Σ ;;; Γ |- t1 : cat_obj ->
    Σ ;;; Γ |- t2 : cat_obj ->
    Σ ;;; Γ |- tApp cat_hom [t1; t2] : sort_set.
Axiom id_hom_type : forall Σ Γ t,
    Σ ;;; Γ |- t : cat_obj ->
    Σ ;;; Γ |- tApp id_hom [t] : tApp cat_hom [t; t].

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
Admitted.

Lemma typed_empty_global_env :
  type_global_env init_graph [].
Proof.
  constructor. apply wf_init_graph.
Qed.

Ltac setctx na :=
  match goal with
    [ |- ?Σ ;;; ?Γ |- _ : _ ] => set(na := Γ)
  | [|- type_local_env ?Σ ?Γ ] => set(na := Γ)
  end.

Ltac setctx_2 na :=
  match goal with
    |- ?Σ ;;; ?Γ ,, ?v2 ,, ?v1 |- _ : _ => set(na := [v1;v2])
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

Reserved Notation "E ## Γ |= σ" (at level 40).

(* TODO: think about the empty context case *)
Inductive fctx_valid E : context -> list forcing_condition -> Type :=
| fctx_valid_nil : E ## vass (nNamed "p") Relevant (tConst "Obj" nil) :: nil |= nil
| fctx_valid_cons_var Γ σ T : E ## Γ |= σ ->
                            E ## (Γ ,, vass (nNamed "t") Relevant T) |= (σ ,, fcVar)
| fctx_valid_cons_lift Γ σ : E ## Γ |= σ ->
                        E ## (Γ ,,, get_ctx_lift cat E (last_condition σ)) |= (σ ,, fcLift)
where "E ## Γ |= σ" := (fctx_valid E Γ σ).


Lemma last_condition_sound σ Γ (Σ := ([], init_graph)) :
  type_local_env Σ Γ ->
  (of_global_context Σ) ## Γ |= σ ->
  Σ ;;; Γ |- tRel (last_condition σ) : cat_obj.
Proof.
  intros TyCtx FcValid.
  induction FcValid.
  - simpl. solve_rel.
  - simpl.
    pose [vass (nNamed "t") Relevant T] as Γ'.
    change (Σ;;; Γ ,,, Γ' |- lift0 #|Γ'| (tRel (last_condition σ)) : lift0 #|Γ'| (cat_obj)).
    assert (TyCtxΓ : type_local_env Σ Γ).
    { inversion TyCtx;subst;auto. }
    apply weakening.
    + apply typed_empty_global_env.
    + simpl.
      (* NOTE: here we do inversion again, because of some issues with [typing] being in [Type] *)
      inversion TyCtx;subst;auto.
    + apply IHFcValid; eauto.
  - solve_rel.
Qed.

Lemma lift_sound (Σ := (nil,init_graph)) Γ σ v :
  type_local_env Σ Γ ->
  (of_global_context Σ) ## Γ |= σ ->
  Σ;;; Γ,, vass v Relevant cat_obj |- tApp cat_hom [tRel (S (last_condition σ)); tRel 0] : sort_set.
Proof.
  intros TyCtx FcValid.
  eapply hom_sort.
  - pose ([vass v Relevant cat_obj]) as Γ'.
    change
      (Σ;;; Γ ,,, Γ' |- lift0 #|Γ'| (tRel (last_condition σ)) : lift0 #|Γ'| cat_obj).
    apply weakening with (Γ' := Γ').
    * apply typed_empty_global_env.
    * simpl. constructor. apply TyCtx. econstructor. simpl. apply obj_sort.
    * apply last_condition_sound;eauto.
  - solve_rel.
Qed.

Lemma lam_q_f_sound (Σ := (nil,init_graph)) Γ σ t T :
  let E := (of_global_context Σ) in
  let fctx := (mkFCtxt σ cat []) in
  let ext := get_ctx_lift cat E (last_condition σ) in
  type_local_env Σ Γ ->
  (of_global_context Σ) ## Γ |= σ ->
  Σ ;;; Γ ,,, ext |- t : T ->
  Σ ;;; Γ |- snd (λ_q_f E fctx) t : snd (Π_q_f E fctx) T.
Proof.
  simpl. intros TyCtx FcValid Ty.
  econstructor.
  + eapply obj_sort.
  + econstructor.
    * apply lift_sound;eauto.
    * eauto.
Qed.

Lemma Π_q_f_lift_sound (Σ := (nil,init_graph)) Γ σ T l :
  let σ_ext := σ ,, fcLift in
  let fctx_ext := (mkFCtxt σ_ext cat []) in
  let E := (of_global_context Σ) in
  let ext1 := get_ctx_lift cat E (last_condition σ) in
  let ext2 := get_ctx_lift cat E (last_condition σ_ext) in
  Σ ;;; Γ ,,, ext1 ,,, ext2  |- T : tSort l ->
  Σ ;;; Γ ,,, ext1 |- snd (Π_q_f E fctx_ext) T :
  tSort (Universe.sup [Universe.Expr.set]  (Universe.sup [Universe.Expr.set] l)).
Proof.
  simpl.
  intros H.
  apply type_Prod.
  ** apply obj_sort.
  ** apply type_Prod.
     *** apply hom_sort; solve_rel.
     *** eauto.
Qed.

Notation "'[' c ']ᵗ' " := (ft_term c) (at level 0).
Notation "⟦ Γ ⟧" := (ft_ctx Γ)  (at level 40).
Notation "'⟦' c '⟧ᵀ'" := (ft_type c) (at level 40).
Notation "'⟦' c '⟧!'" := (ft_type_boxed c) (at level 40).

Lemma context_traslation_valid E Γ σ :
  let Σ := to_global_context E in
  type_local_env Σ Γ ->
  E ## (⟦Γ⟧ Σ σ) |= σ.
Proof.
  intros ? TyCtx.
  Admitted.

Lemma forcing_context_soundness Σ Γ σ :
  type_local_env Σ Γ -> type_local_env Σ (⟦Γ⟧ Σ σ).
Admitted.


Tactic Notation "solve_last_cond" :=
  apply last_condition_sound;
  [apply forcing_context_soundness;assumption |
   apply context_traslation_valid;assumption].

Ltac type_spine_step :=
  match goal with
    | [  |- typing_spine _ _ _ (?t :: ?ts) _ ] =>
      econstructor;
      [eapply cumul_refl;apply leq_refl | | ]
  end.

Lemma sort_translation_prefix_sound (Σ := (nil,init_graph)) σ Γ T l:
  let E := (of_global_context Σ) in
  let fctx := (mkFCtxt σ cat []) in
  let srt := tSort (Universe.sup [Universe.Expr.set]  (Universe.sup [Universe.Expr.set] l)) in
  let ext1 := get_ctx_lift cat E (last_condition σ) in
  let ext2 := get_ctx_lift cat E (last_condition (σ ,, fcLift)) in
  type_local_env Σ Γ ->
  (of_global_context Σ) ## Γ |= σ ->
  Σ ;;; Γ ,,, ext1 ,,, ext2  |- T : tSort l ->
  Σ ;;; Γ |- snd (sort_translation_prefix E fctx tt) T
                      : snd (Π_q_f E fctx) srt.
Proof.
  intros ? ? ? ? ? TyCtx FcValid TyT.
  simpl.
  apply lam_q_f_sound;simpl;eauto.
  unfold sort_set.
  eapply Π_q_f_lift_sound. apply TyT.
Qed.

Lemma type_translation_sound (Σ := ([],init_graph)) Γ σ T :
  type_local_env Σ Γ ->
  (of_global_context Σ) ## Γ |= σ ->
  Σ;;; Γ |- [T ]ᵗ Σ σ : (⟦ tSort [Universe.Expr.set] ⟧ᵀ) Σ σ ->
  Σ ;;; Γ |- ⟦T⟧ᵀ Σ σ : tSort [Universe.Expr.set].
Proof.
  intros TyCtx FcValid TyT.
  unfold ft_type,otranslate_type. simpl. unfold mkOptApp.
  remember (tRel (last_condition σ)) as last_fcond.
  remember (tApp (tConst "Id_hom" []) [last_fcond]) as id_hom_lfc.
  change (Σ;;; Γ |- tApp ([T]ᵗ Σ σ) [last_fcond; id_hom_lfc] : tSort [Universe.Expr.set]).
  eapply type_App.
  - eapply TyT.
  - unfold ft_type. simpl. unfold mkOptApp. econstructor.
    * (* Abstract this reduction to a tactic *)
      eapply cumul_red_r. Focus 2.
      eapply red_beta. simpl.
      eapply cumul_red_r. Focus 2.
      eapply red_beta. simpl.
      eapply cumul_refl. apply leq_refl.
    * subst. apply last_condition_sound;eauto.
    * econstructor. Focus 2.
      subst. apply id_hom_type. apply last_condition_sound;eauto.
      econstructor. subst. eapply leq_refl.
      econstructor.
Qed.

Lemma ctx_with_lift_sound (Σ := ([],init_graph)) Γ σ:
  let ext := get_ctx_lift cat (of_global_context Σ) (last_condition σ) in
  type_local_env Σ Γ ->
  (of_global_context Σ) ## Γ |= σ ->
  type_local_env Σ (Γ ,,, ext).
Proof.
  simpl. intros TyCtx FcValid.
  constructor;eauto.
  constructor;eauto.
  econstructor; apply obj_sort.
  econstructor; apply lift_sound;eauto.
Qed.

Lemma boxed_type_translation_sound (Σ := ([],init_graph)) Γ σ A :
  let ext := get_ctx_lift cat (of_global_context Σ) (last_condition σ) in
  type_local_env Σ Γ ->
  (of_global_context Σ) ## Γ |= σ ->
  Σ ;;; Γ ,,, ext |- [A]ᵗ Σ (σ ,, fcLift) : (⟦ tSort [Universe.Expr.set] ⟧ᵀ) Σ (σ ,, fcLift) ->
  Σ ;;; Γ |- ⟦A⟧! Σ σ :  tSort (Universe.sup [Universe.Expr.set] [Universe.Expr.set]).
Proof.
  simpl.
  intros TyCtx FcValid H.
  unfold ft_type_boxed,otranslate_boxed_type. simpl.
  destruct (otranslate_type otranslate (of_global_context Σ)
            (extend_forcing_ctx {| f_context := σ; f_category := cat; f_translator := [] |} fcLift)
            tt A) eqn: HA.
  simpl. eapply type_Prod.
  - apply obj_sort.
  - replace ([Universe.Expr.set]) with
        (Universe.sup [Universe.Expr.set] [Universe.Expr.set]) by reflexivity.
    eapply type_Prod.
    pose ([vass pos_name Relevant (tConst "Obj" [])]) as Γ'.
    eapply hom_sort.
    + change (Σ;;; Γ ,,, Γ' |- lift0 #|Γ'| (tRel (last_condition σ)) : lift0 #|Γ'| (cat_obj)).
      subst Σ. eapply weakening.
      * apply typed_empty_global_env.
      * simpl. constructor;eauto.
        econstructor. apply obj_sort.
      * apply last_condition_sound;eauto.
    + solve_rel.
    + unfold mkOptApp. apply type_translation_sound.
      * apply  ctx_with_lift_sound;eauto.
      * constructor. assumption.
      * apply H.
Qed.

(* Lemma ctx_translation_extension (Σ := ([],init_graph)) σ Γ : *)
(*   let E := of_global_context Σ in *)
(*   ⟦ Γ ⟧ Σ (σ,, fcLift) = Γ ,,, (get_ctx_lift cat E (last_condition σ)). *)
(* Proof. *)
(*   simpl. destruct Γ. *)
(*   - unfold ft_ctx,otranslate_context_no_sigma. simpl. cbv. *)

Lemma forcing_typing_soundness (Σ := ([],init_graph)) Γ t T σ  :
  type_local_env Σ Γ ->
  Σ ;;; Γ |- t : T ->
  let Σ' := Σ in
  Σ' ;;; (⟦Γ⟧ Σ σ) |- ([t]ᵗ Σ σ) : (⟦T⟧ᵀ Σ σ).
Proof.
  intros TyCtx Ty.
  revert σ.
  induction Ty; intros; simpl.
  - (* -- Variables -- *)
    simpl. unfold translate_var.
    unshelve econstructor; simpl.
    Focus 2. constructor.  admit.
  - (* -- Sorts -- *)
    assert (FcValid : of_global_context Σ ## (⟦ Γ ⟧) Σ σ |= σ) by
        (apply context_traslation_valid;auto).
    (* Simplifying the applications in the type first*)
      unfold ft_term,otranslate,lambda_prefix,extend.
      eapply type_Conv;simpl.
      * apply lam_q_f_sound;simpl.
        ** apply forcing_context_soundness;assumption.
        ** apply FcValid.
        ** eapply Π_q_f_lift_sound; apply type_Sort.
      * unfold ft_type. simpl in *. unfold mkOptApp.
        eapply type_App.
        ** eapply lam_q_f_sound;simpl.
           *** apply forcing_context_soundness;assumption.
           *** apply FcValid.
           *** apply Π_q_f_lift_sound. unfold Universe.super. simpl.
               unfold Universe.type1,Universe.Expr.type1.
           (* TODO: show that [tSort [(Level.set, true)]] has type [tSort l] for some level l *)
           (* constructor [type_Sort] does not apply here. *)
               admit.
        ** simpl. (* typing_spine *)
           type_spine_step. solve_last_cond.
           type_spine_step. apply id_hom_type. solve_last_cond.
           apply type_spine_nil.
      * simpl. unfold ft_type. simpl. unfold mkOptApp.
        (* Abstract this reduction to a tactic *)
        eapply cumul_red_r. Focus 2.
        eapply red_beta. simpl.
        eapply cumul_red_r. Focus 2.
        eapply red_beta. simpl.
        eapply cumul_refl.
        simpl.
        (* NOTE: not sure how to prove this stuff about [leq_universe] *)
        assert (H : leq_universe
                      init_graph
                      (Universe.sup [Universe.Expr.set]
                                    (Universe.sup [Universe.Expr.set] (Universe.super l)))
                      (Universe.super l) = true). admit.
        rewrite H. rewrite Nat.eqb_refl. reflexivity.
  - admit.
  - (* -- Products -- *)
    assert (CtxSound : type_local_env Σ (⟦Γ⟧ Σ σ)) by (apply forcing_context_soundness;auto).
    assert (FcValid : of_global_context Σ ## (⟦ Γ ⟧) Σ σ |= σ) by
        (apply context_traslation_valid;auto).
    rename t into A. rename b into B.
    unfold ft_type, ft_term,snd. simpl.
    destruct (otranslate_boxed_type otranslate (of_global_context Σ)
            (extend_forcing_ctx {| f_context := σ; f_category := cat; f_translator := nil |} fcLift)
            tt A) as [sigma t_] eqn:Ht.
    destruct (otranslate_type otranslate (of_global_context Σ)
            (add_variable
               (extend_forcing_ctx {| f_context := σ; f_category := cat; f_translator := nil |}
                                   fcLift)) sigma B) as [sigma0 u_] eqn:Hu.
    unfold mkOptApp.
    eapply type_Conv;simpl.
    * eapply lam_q_f_sound;simpl.
      ** apply forcing_context_soundness;assumption.
      ** apply FcValid.
      ** eapply type_Prod.
         *** eapply Π_q_f_lift_sound.
             eapply type_translation_sound.
             **** simpl.
                  pose [vass hom_name Relevant (tApp cat_hom [tRel 2; tRel 0]);
                        vass pos_name Relevant cat_obj] as Γ'.
                  pose [vass hom_name Relevant (tApp cat_hom [tRel (S (last_condition σ)); tRel 0]);
                        vass pos_name Relevant (tConst "Obj" [])] as Γ''.
                  change (type_local_env ([], init_graph) (⟦ Γ ⟧ Σ σ ,,, Γ'' ,,, Γ')).
                  eapply ctx_with_lift_sound with (σ := σ ,, fcLift);eauto.
                  eapply ctx_with_lift_sound with (σ := σ);eauto.
                  constructor;eauto.
             **** repeat constructor;eauto.
             **** simpl.
                  pose [vass hom_name Relevant (tApp cat_hom [tRel 2; tRel 0]);
                        vass pos_name Relevant cat_obj] as Γ'.
                  pose [vass hom_name Relevant (tApp cat_hom [tRel (S (last_condition σ)); tRel 0]);
                        vass pos_name Relevant (tConst "Obj" [])] as Γ''.
                  assert (Hs1 :[Universe.Expr.set] = s1). admit.
                  rewrite Hs1. simpl in IHTy1.
                  change
  (Σ ;;; (⟦ Γ ⟧) Σ σ ,,, Γ'' ,,, Γ' |- [A ]ᵗ Σ (σ,, fcLift,, fcLift) : (⟦ tSort s1 ⟧ᵀ Σ  (σ,, fcLift,, fcLift))).
                  pose ((⟦ Γ ⟧) Σ ((σ,, fcLift),, fcLift)) as G.
                  unfold ft_ctx in G.
                  (* assert (Hfc : of_global_context Σ ## G |= (σ ,, fcLift ,, fcLift)). *)
                  (* { constructor. } *)
                  (* simpl in G. *)
                  (* eapply IHTy1 with (σ := σ ,,fcLift,,fcLift). *)
                  admit.

Admitted.