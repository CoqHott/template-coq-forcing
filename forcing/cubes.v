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
        Forcing.Inductives.

Require Import FunctionalExtensionality.

Set Primitive Projections.

Notation "f 'o' g" := (Basics.compose f g) (at level 50, left associativity).

Definition funext {A B : Type} := @functional_extensionality A B.



(** SProp manipulation and notations *)

Inductive sBox (P : SProp) : Prop :=
| wrap : P -> sBox P.

Theorem unwrap (P : SProp) (b : sBox P) : P.
Proof.
  destruct b. exact H.
Qed.

Inductive eq_s {A : Type} : A -> A -> SProp :=
| refl_s : forall a : A, eq_s a a.

Notation "A '=s' B" := (eq_s A B) (at level 65, left associativity).

Theorem eqs_eq {A : Type} {a b : A} : a =s b -> a = b.
Proof.
  intro H. destruct H. reflexivity.
Qed.

Theorem eq_eqs {A : Type} {a b : A} : a = b -> a =s b.
Proof.
  intro H. apply unwrap. rewrite H. apply wrap. apply refl_s.
Qed.

Theorem ssym {A : Type} {a b : A} (p : eq_s a b) : eq_s b a.
Proof.
  destruct p. apply refl_s.
Qed.

Theorem srewrite {A : Type} {a b : A} (P : A -> SProp) (α : P a) (p : a =s b) : P b.
Proof.
  destruct p. exact α.
Qed.

Inductive sexists_s (A : Type) (B : A -> SProp) : SProp :=
| spair_s : forall a : A, B a -> sexists_s A B.

Record sexists {A : Type} (B : A -> SProp) : Type :=
  {
    spi1 : A ;
    spi2 : B spi1
  }.

Notation "x .1s" := x.(spi1 _) (at level 3).
Notation "x .2s" := x.(spi2 _) (at level 3).

Notation "( a ; b )s" := {| spi1 := a ; spi2 := b |}.






(** Redefinition of simple arithmetic *)

(* The definitions already present in the standard library are very complicated and take ages to quote *)

Theorem le_0_n : forall n, 0 <= n.
Proof.
  intro n. induction n.
  - apply le_n.
  - apply le_S. exact IHn.
Qed.

Theorem lt_0_succ : forall n, 0 < S n.
Proof.
  intro n. induction n.
  - now apply le_n.
  - apply le_S. exact IHn.
Qed.

Theorem pos_ge_0 : forall n, S n <= 0 -> False.
Proof.
  intros n H. inversion H.
Qed.

Theorem le_S_n : forall n m, S n <= S m -> n <= m.
Proof.
  intros n m. revert n. induction m.
  - intros n H. inversion H.
    + apply le_n.
    + apply pos_ge_0 in H1. destruct H1.
  - intros n H. inversion H.
    + apply le_n.
    + apply IHm in H1. apply le_S. exact H1.
Qed.

Theorem le_n_S : forall n m, n <= m -> S n <= S m.
Proof.
  intros n m. revert n. induction m.
  - intros n H. inversion H. apply le_n.
  - intros n H. inversion H.
    + apply le_n.
    + apply le_S. now apply IHm.
Qed.

Definition le_imp_eq_lt : forall n m : nat, n <= m -> {n = m} + {n < m}.
  intro n. induction n.
  - intros m H. destruct m.
    + left. reflexivity.
    + right. apply lt_0_succ.
  - intros m H. destruct m.
    + apply pos_ge_0 in H. destruct H.
    + destruct (IHn m).
      * now apply le_S_n.
      * rewrite e. left. reflexivity.
      * right. now apply le_n_S.
Defined.

Definition lt_eq_lt_dec :  forall n m : nat, {n < m} + {n = m} + {m < n}.
  intros n m. induction n.
  - assert (0 <= m). apply le_0_n. apply le_imp_eq_lt in H. destruct H.
    + left. now right.
    + left. now left.
  - destruct IHn as [[H | H] | H].
    + apply le_imp_eq_lt in H. destruct H.
      * left. right. exact e.
      * left. left. exact l.
    + rewrite H. right. now apply le_n.
    + right. now apply le_S.
Defined.

Definition lt_eq_eq_lt_dec (m n : nat) : {m < n} + {m = n} + {m = S n} + {m > S n}.
Proof.
  destruct (lt_eq_lt_dec m n) as [[H | H] | H].
  - left. left. now left.
  - left. left. now right.
  - apply le_imp_eq_lt in H. destruct H.
    + left. now right.
    + right. exact l.
Defined.

Theorem le_trans : forall n m p, n <= m -> m <= p -> n <= p.
Proof.
  intros n m p. revert n m. induction p.
  - destruct m.
    + trivial.
    + intros H H'. apply pos_ge_0 in H'. destruct H'.
  - intros n m H. destruct m, n.
    + intro H'. apply le_0_n.
    + apply pos_ge_0 in H. destruct H.
    + intro H'. apply le_0_n.
    + intro H'. apply le_S_n in H. apply le_S_n in H'. apply le_n_S.
      eapply IHp. apply H. exact H'.
Qed.






(** Definition of the cubes *)

Definition finset (n : nat) : Set :=
  {m : nat | m < n}.

(* 2 ^ n *)
Definition cube (n : nat) : Set := finset n -> bool.

Definition degen_c {n : nat} (m : finset (S n)) : cube (S n) -> cube n.
  destruct m as [m p]. intros x [i q].
  destruct (lt_eq_lt_dec i m) as [[H | H] | H].
  - apply x. exists i. now apply le_S.
  - apply x. exists (S i). now apply le_n_S.
  - apply x. exists (S i). now apply le_n_S.
Defined.

Definition face_c {n : nat} (m : finset (S n)) (d : bool) : cube n -> cube (S n).
  destruct m as [m p]. intros x [i q].
  destruct (lt_eq_lt_dec i m) as [[H | H] | H].
  - apply x. exists i. eapply le_trans. exact H. now apply le_S_n.
  - exact d.
  - apply x. destruct i.
    + apply pos_ge_0 in H. destruct H.
    + exists i. apply le_S_n. exact q.
Defined.

Definition meet_c {n : nat} (m : finset n) : cube (S n) -> cube n.
  destruct m as [m p]. intros x [i q].
  destruct (lt_eq_lt_dec i m) as [[H | H] | H].
  - apply x. exists i. now apply le_S.
  - apply andb.
    + apply x. exists i. now apply le_S.
    + apply x. exists (S i). now apply le_n_S.
  - apply x. exists (S i). now apply le_n_S.
Defined.

Definition join_c {n : nat} (m : finset n) : cube (S n) -> cube n.
  destruct m as [m p]. intros x [i q].
  destruct (lt_eq_lt_dec i m) as [[H | H] | H].
  - apply x. exists i. now apply le_S.
  - apply orb.
    + apply x. exists i. now apply le_S.
    + apply x. exists (S i). now apply le_n_S.
  - apply x. exists (S i). now apply le_n_S.
Defined.

Definition rev_c {n : nat} (m : finset n) : cube (S n) -> cube (S n).
  destruct m as [m p]. intros x [i q].
  destruct (lt_eq_eq_lt_dec i m) as [[[H | H] | H] | H].
  - apply x. exists i. exact q.
  - apply x. exists (S m). now apply le_n_S.
  - apply x. exists m. now apply le_S.
  - apply x. exists i. exact q.
Defined.

Inductive word : nat -> nat -> Type :=
| empty {a : nat} : word a a
| degen {a b : nat} : finset (S b) -> word a (S b) -> word a b
| face {a b : nat} : finset (S b) -> bool -> word a b -> word a (S b)
| meet {a b : nat} : finset b -> word a (S b) -> word a b
| join {a b : nat} : finset b -> word a (S b) -> word a b
| rev {a b : nat} : finset b -> word a (S b) -> word a (S b).

Fixpoint concat_word {a b c : nat} (w1 : word b c) (w2 : word a b) : word a c :=
  (match w1 in (word b c) return word a b -> word a c with
   | @empty x => (fun w : word a x => w)
   | @degen x y i w' => (fun w : word a x => degen i (concat_word w' w))
   | @face x y i d w' => (fun w : word a x => face i d (concat_word w' w))
   | @meet x y i w' => (fun w : word a x => meet i (concat_word w' w))
   | @join x y i w' => (fun w : word a x => join i (concat_word w' w))
   | @rev x y i w' => (fun w : word a x => rev i (concat_word w' w))
   end) w2.

Fixpoint comp_word {a b : nat} (w : word a b) : cube a -> cube b :=
  match w with
  | empty => (fun x => x)
  | degen i w' => (degen_c i) o (comp_word w')
  | face i d w' => (face_c i d) o (comp_word w')
  | meet i w' => (meet_c i) o (comp_word w')
  | join i w' => (join_c i) o (comp_word w')
  | rev i w' => (rev_c i) o (comp_word w')
  end.




(** Lemmas about cubes *)

Theorem concat_id_left {a b : nat} (w : word a b) : concat_word empty w = w.
Proof.
  now compute.
Qed.

Theorem concat_id_right {a b : nat} (w : word a b) : concat_word w empty = w.
Proof.
  induction w ; simpl ; try rewrite IHw ; reflexivity.
Qed.

Theorem concat_assoc {a b c d : nat} (w1 : word c d) (w2 : word b c) (w3 : word a b) :
  concat_word w1 (concat_word w2 w3) = concat_word (concat_word w1 w2) w3.
Proof.
  induction w1 ; simpl ; try rewrite IHw1 ; reflexivity.
Qed.

Theorem comp_id {a : nat} : comp_word (@empty a) = fun x => x.
Proof.
  easy.
Qed.

Theorem concat_sound {a b c : nat} (w1 : word b c) (w2 : word a b) :
  comp_word w1 o comp_word w2 =s comp_word (concat_word w1 w2).
Proof.
  induction w1 ;
    simpl ;
    try (match goal with
         | |- ?XX o ?YY o ?ZZ =s ?RR => change (XX o (YY o ZZ) =s RR)
         end) ;
    try (specialize IHw1 with (w2:=w2)) ;
    try (destruct IHw1) ;
    apply refl_s.
Qed.

Definition admissible {a b : nat} (f : cube a -> cube b) : SProp :=
  sexists_s (word a b) (fun w => (f =s comp_word w)).

Theorem adm_id {a : nat} : admissible (fun x : cube a => x).
Proof.
  apply spair_s with (a:=empty). simpl.
  apply refl_s.
Qed.

Theorem adm_comp {a b c : nat} (f : cube a -> cube b) (g : cube b -> cube c) :
  admissible f -> admissible g -> admissible (g o f).
Proof.
  intros [w p] [w' q]. apply ssym in q. apply ssym in p.
  assert (admissible ((comp_word w') o (comp_word w))).
  - apply spair_s with (a:=concat_word w' w). apply concat_sound.
  - assert (admissible (g o (comp_word w))).
    apply (srewrite (fun g => admissible (g o comp_word w)) H q).
    apply (srewrite (fun f => admissible (g o f)) H0 p).
Qed.

Definition arrow (a b : nat) : Type :=
  @sexists (cube a -> cube b) admissible.

Definition compose {A B C : nat} (g : arrow B C) (f : arrow A B) : arrow A C :=
  (
    g.1s o f.1s ;
    adm_comp f.1s g.1s f.2s g.2s
  )s.

Notation "A ~> B" := (arrow A B) (at level 90, left associativity).

Notation "f 'ô' g" := (compose f g) (at level 50, left associativity).

Definition id {A : nat} : A ~> A :=
  (
    fun x => x ;
    adm_id
  )s.




(** Check that category laws are definitional *)

Theorem compose_assoc {A B C D : nat}
           (f : A ~> B) (g : B ~> C) (h : C ~> D) :
  h ô (g ô f) = (h ô g) ô f.
Proof.
  reflexivity.
Qed.

Theorem compose_id_right {A B : nat} (f : A ~> B) :
  f ô id = f.
Proof.
  reflexivity.
Qed.

Theorem compose_id_left {A B : nat} (f : A ~> B) :
  id ô f = f.
Proof.
  reflexivity.
Qed.





(** Definition of the forcing machinery *)

Definition 𝐂_obj := nat.
Definition 𝐂_hom := arrow.
Definition 𝐂_id := @id.
Definition 𝐂_comp := @compose.

Quote Definition q_𝐂_obj := nat.
Quote Definition q_𝐂_hom := arrow.
Quote Definition q_𝐂_id := @id.
Quote Definition q_𝐂_comp := @compose.

Definition 𝐂 : category :=
  mkCat q_𝐂_obj q_𝐂_hom q_𝐂_id q_𝐂_comp.


Import MonadNotation.
Import ListNotations.

Definition ForcingTranslation (cat : category) : Translation :=
  {| tsl_id := tsl_ident;
     tsl_tm := f_translate cat;
     tsl_ty := f_translate_type cat;
     tsl_ind := f_translate_ind cat
     (* tsl_context -> kername -> kername -> mutual_inductive_body *)
     (*             -> tsl_result (tsl_table * list mutual_inductive_body) *)
  |}.

Definition add_translation (ctx : tsl_context) (e : global_reference * term): tsl_context :=
  let (Σ, E) := ctx in
  (Σ, e :: E).

Instance Cubical : Translation := ForcingTranslation 𝐂.

(* Define a type that, when recursively quoted, imports all we need *)
Definition pack := (arrow , @compose , @id).

Run TemplateProgram (prg <- tmQuoteRec pack ;;
                         tmDefinition "g_ctx" (fst prg)).
Definition ΣE : tsl_context := (reconstruct_global_context g_ctx,[]).




(** Definition of the interval *)

Run TemplateProgram (tImplementTC ΣE "I_TC" "I" Type).
Next Obligation.
  exact (p0 ~> 1).
Defined.

Definition terminal_word_aux (p : nat) (q : nat) : word (p+q) p.
  revert p. induction q.
  - intro p. rewrite <- (plus_n_O p). exact empty.
  - intro p. apply degen.
    + exists 0. easy.
    + rewrite <- plus_n_Sm.
      change (word (S (p + q)) (S p)) with (word (S p + q) (S p)).
      apply IHq.
Defined.

Definition terminal_word (p : nat) : word p 0.
  exact (terminal_word_aux 0 p).
Defined.

Definition terminal_map (p : nat) : cube p -> cube 0.
  intro c. intros [a H]. destruct (pos_ge_0 a H).
Defined.


(*
   this proof uses funext to show that any two arrows with terminal codomain must be
   equal. If necessary, it is possible to define a version that doesn't use it.
 *)
Theorem terminal_map_admissible (p : nat) :
  terminal_map p =s comp_word (terminal_word p).
Proof.
  apply eq_eqs.
  apply funext. intro a. apply funext. intros [b H]. destruct (pos_ge_0 b H).
Qed.

Definition terminal_arrow (p : nat) : p ~> 0.
  assert (admissible (terminal_map p)).
  - eapply spair_s. exact (terminal_map_admissible p).
  - exact (terminal_map p ; H)s.
Defined.

Theorem eq_sexist {A : Type} {P : A -> SProp} (a b : sexists P) (e : a.1s = b.1s) :
  a = b.
  destruct a, b. simpl in e. admit.
Admitted.

Theorem terminal_arrow_is_terminal (p : nat) (α : p ~> 0) :
  α = terminal_arrow p.
Proof.
  apply eq_sexist. apply funext. intro x. apply funext.
  intros [n H]. assert False. eapply pos_ge_0. exact H. inversion H0.
Qed.

Definition I_end_map (p : nat) (e : bool) : cube p -> cube 1 :=
  (fun (_ : cube p) (_ : finset 1) => e).

Definition I_end_word (p : nat) (e : bool) : word p 1.
  apply face.
  - exists 0. easy.
  - exact e.
  - exact (terminal_word p).
Defined.

Theorem I_end_admissible (p : nat) (e : bool) :
  I_end_map p e =s comp_word (I_end_word p e).
Proof.
  apply eq_eqs. simpl. rewrite <- (eqs_eq (terminal_map_admissible p)).
  apply funext. intro c. apply funext. intros [x H]. destruct x.
  - compute. reflexivity.
  - pose proof (le_S_n (S x) 0 H) as H'. apply pos_ge_0 in H'. destruct H'.
Qed.

Definition I_end (p : nat) (e : bool) : p ~> 1.
  assert (admissible (I_end_map p e)).
  - eapply spair_s. exact (I_end_admissible p e).
  - exact (I_end_map p e ; H)s.
Defined.

Run TemplateProgram (tImplementTC I_TC "I0_TC" "I0" I).
Next Obligation.
  exact (I_end p false).
Defined.

Run TemplateProgram (tImplementTC I0_TC "I1_TC" "I1" I).
Next Obligation.
  exact (I_end p true).
Defined.




(** Imported inductives *)

(* We copy translated definitions of [eq] generated by the OCaml
   forcing plugin, because inducives are not supported yet by the
   template-coq forcing translation *)
Inductive eqᵗ (p : 𝐂_obj) (A : forall p0 : 𝐂_obj, p ~> p0 -> forall p : 𝐂_obj, p0 ~> p -> Type)
(x : forall (p0 : 𝐂_obj) (α : p ~> p0), A p0 (α ô id) p0 id) :
  (forall (p0 : 𝐂_obj) (α : p ~> p0), A p0 (id ô (α ô id)) p0 id) -> Type :=
  eq_reflᵗ : eqᵗ p A x x.

(* This definition will fail if we leave the type of [A] implicit. *)
Definition eq_is_eq :
  forall p (A : forall x : 𝐂_obj, (p ~> x) -> forall x1 : 𝐂_obj, (x ~> x1) -> Type)
         (x y: forall p0 (f:p ~> p0), A p0 f p0 id),
    eq x y -> eqᵗ p A x y. (* it even fails if i don't mention A as an explicit argument
                             here b/c of some mysterious reason *)
Proof.
  intros. rewrite H. apply eq_reflᵗ.
Qed.

Run TemplateProgram (TC <- tAddExistingInd I1_TC "Coq.Init.Logic.eq" "eqᵗ" ;;
                          tmDefinition "eq_TC" TC).

Inductive Falseᵗ (p : 𝐂_obj) := .

Run TemplateProgram (TC <- tAddExistingInd eq_TC "Coq.Init.Logic.False" "Falseᵗ" ;;
                        tmDefinition "False_TC" TC).

Inductive orᵗ (p : 𝐂_obj) (A B : forall p0 : 𝐂_obj, p ~> p0 -> forall p1 : 𝐂_obj, p0 ~> p1 -> Prop) : Prop :=
    or_introlᵗ : (forall (p0 : 𝐂_obj) (α : p ~> p0), A p0 α p0 id) -> orᵗ p A B
  | or_introrᵗ : (forall (p0 : 𝐂_obj) (α : p ~> p0), B p0 α p0 id) -> orᵗ p A B.

Run TemplateProgram (TC <- tAddExistingInd False_TC "Coq.Init.Logic.or" "orᵗ" ;;
                        tmDefinition "or_TC" TC).

Definition complete_TC := or_TC.


(** Axiom 1 : connectedness *)

Definition unique : cube 0.
  unfold cube. unfold finset. intros [m H]. apply pos_ge_0 in H. inversion H.
Defined.

Definition zero_f1 : finset 1.
  exists 0. easy.
Defined.

Run TemplateProgram (tImplementTC complete_TC "sep_TC" "sep" (I -> Prop)).
Next Obligation.
  specialize (X 0 (terminal_arrow p)). unfold Iᵗ in X. unfold Iᵗ_obligation_1 in X.
  apply (fun x => x.1s) in X. specialize (X unique). unfold cube in X. specialize (X zero_f1).
  exact (if X then True else False).
Defined.

Run TemplateProgram (tImplementTC sep_TC "sep1_TC" "counter_ax1_pt1" (forall i : I, sep i \/ (sep i -> False))).
Next Obligation.
  assert (((i 0 (terminal_arrow p)).1s unique zero_f1 = true) \/ ((i 0 (terminal_arrow p)).1s unique zero_f1 = false)).
  - destruct ((i 0 (terminal_arrow p)).1s unique zero_f1).
    + now left.
    + now right.
  - destruct H.
    + apply or_introlᵗ. intros p0 α. unfold sepᵗ. unfold sepᵗ_obligation_1.
      change (id ô terminal_arrow p0 ô (id ô α ô id)) with (terminal_arrow p0 ô α).
      assert (terminal_arrow p0 ô α = terminal_arrow p).
      * apply terminal_arrow_is_terminal.
      * rewrite H0. rewrite H. exact Logic.I.
    + apply or_introrᵗ. intros p0 α H1. unfold sepᵗ in H1. unfold sepᵗ_obligation_1 in H1.
      specialize (H1 p0 id).
      assert (id ô terminal_arrow p0 ô id ô id ô (id ô α ô id) = terminal_arrow p).
      * apply terminal_arrow_is_terminal.
      * rewrite H0 in H1. rewrite H in H1. inversion H1.
Defined.

Run TemplateProgram (tImplementTC sep1_TC "sep2_TC" "counter_ax1_pt2" (sep I0 -> False)).
Next Obligation.
  specialize (H p id). compute in H. inversion H.
Defined.

Run TemplateProgram (tImplementTC sep2_TC "sep3_TC" "counter_ax1_pt3" (sep I1)).
Next Obligation.
  compute. exact Logic.I.
Defined.

Run TemplateProgram (tImplement sep3_TC "counter_ax1"
  ((forall (φ : I -> Prop), (forall i : I, φ i \/ (φ i -> False)) -> (forall i : I, φ i) \/ (forall i : I, φ i -> False)) -> False)).
Next Obligation.
  specialize (H p id). About sepᵗ. specialize (H (fun p α => sepᵗ p)). About counter_ax1_pt1ᵗ.
  specialize (H (fun p α => counter_ax1_pt1ᵗ p)). destruct H.
  - apply counter_ax1_pt2ᵗ. intros p0 α. specialize (H p0 α). specialize (H (fun p α => I0ᵗ p)). exact H.
  - specialize (H p id (fun p α => I1ᵗ p)). apply H. intros p0 α. exact (counter_ax1_pt3ᵗ p0).
Defined.


(** Axiom 2 : distinct end points *)

Definition zero_f1 : finset 1.
  exists 0. easy.
Defined.

Definition lowest_corner (p : nat) : cube p.
  intro. exact false.
Defined.

Run TemplateProgram (tImplement False_TC "ax2" (I0 = I1 -> False)).
Next Obligation.
  specialize (H p id). inversion H.
  assert (I0ᵗ p = I1ᵗ p).
  change (I0ᵗ p) with ((fun (p1 : nat) (_ : p ~> p1) => I0ᵗ p1) p id). rewrite H1. reflexivity.
  assert (I_end_map p false = I_end_map p true).
  change (I_end_map p false) with ((I0ᵗ p).1s). rewrite H0. reflexivity.
  assert (false = true).
  change false with (I_end_map p false (lowest_corner p) zero_f1). rewrite H2. reflexivity.
  inversion H3.
Defined.