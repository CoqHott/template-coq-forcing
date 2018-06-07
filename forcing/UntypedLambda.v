Require Import GRTT_SProp.

Import Later.
Import Fix.
Import FoldUnfold.

Section UntypedLambda.

  Definition F := (fun T => T -> T).

  Definition 𝒟  := mu F.

  Definition fun_ {n} (f : ⊳[1+n]𝒟 -> ⊳[1+n]𝒟) : ⊳[n]𝒟
    := nfoldp (fun T : Type => T -> T) (fun A => later_unapp A A) f.

  Definition defun_ {n} (f : ⊳[n] 𝒟) : ⊳[1+n]𝒟 -> ⊳[1+n]𝒟
    := nunfoldp (fun T : Type => T -> T) (fun A => later_app A A) f.

  Definition switchD {n} : ⊳[1+n]𝒟 -> ⊳[n]𝒟 := fun t => fun_ (fun _ => t).

  Notation "↓ a" := (switchD a) (at level 40).

  Definition one_step {n} (x: ⊳[n]𝒟) := ↓ (nextp x).

  Notation "→ a" := (one_step a) (at level 40).

  Lemma switchD_nextp {n : nat} (t : ⊳[1+n] 𝒟) : (switchD (n:=1+n) (nextp t)) = nextp (↓t).
  Proof.
    unfold switchD,fun_.
    rewrite <- (nfold_next F (fun A : Type => later_app A A));
      try (intros ? ?; apply later_unapp_app).
    apply f_equal.
    apply functional_extensionality_dep. intros t'.
    symmetry. apply later_app_const_β.
    Qed.

  Definition applD {n} : ⊳[n]𝒟 -> ⊳[n]𝒟 -> ⊳[n]𝒟 := fun f s => ↓ ((defun_ f) (nextp s)).

  Notation "t1 @ t2" := (applD t1 t2) (at level 40).
  Notation "t1 '@[' n ']' t2" := (applD (n:=n) t1 t2) (at level 40).

  Lemma nextp_applD {n} (t t' : ⊳[n] 𝒟) : (nextp t) @[1+n] (nextp t') = nextp (t @ t').
  Proof.
    unfold applD. rewrite <- switchD_nextp. apply f_equal.
    unfold defun_.
    repeat rewrite nunfold_next.
    rewrite later_app_next_β. reflexivity.
  Qed.

  Lemma defun_fun_id {n} (f : ⊳[1+n]𝒟 -> ⊳[1+n]𝒟) : defun_ (fun_ f) = f.
  Proof.
    unfold fun_,defun_.
    rewrite nunfold_nfold_id; try (intros ? ?; apply later_app_unapp).
    reflexivity.
  Qed.

  Definition idD {n : nat} : ⊳[n]𝒟 := fun_ (fun x => x).

  Lemma idD_is_id {n} (t : ⊳[n]𝒟) : idD @ t = → t.
  Proof.
    unfold idD,applD,defun_,fun_. rewrite nunfold_nfold_id.
    reflexivity.  unfold TFUtils.sect. intros. apply later_app_unapp.
  Qed.

  Definition Ω {n} := fun_ (fun (x : ⊳[1+n]𝒟) => x @ x).

  Lemma Ω_unfold {n :nat} : Ω (n:=n) @ Ω = → (Ω @ Ω).
  Proof.
    unfold Ω at 1. unfold applD at 1.
    rewrite defun_fun_id. rewrite nextp_applD.
    reflexivity.
  Qed.

  Definition Y' {n} (f : ⊳[ 1 + n] 𝒟) : ⊳[ 1 + n] 𝒟
    := fun_ (fun (x : ⊳[2+n]𝒟) => applD (n:=2+n) (nextp f) (x @ x)).

  Definition Y {n} := fun_ (fun (f : ⊳[1+n]𝒟) => (Y' f) @ (Y' f)).

  Lemma Y_unfold : forall n (f : ⊳[1+n]𝒟),  (Y @ f) = → → (f @ ((Y' f) @ (Y' f))).
  Proof.
    intros.
    unfold Y'. unfold applD,switchD,defun_,fun_.
    unfold Y,fun_.
  Admitted.

End UntypedLambda.