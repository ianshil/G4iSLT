Require Import List.
Export ListNotations.
Require Import PeanoNat.
Require Import Lia.
Require Import Wellfounded.

Require Import general_export.

Require Import DiSL_calc.
Require Import DG4iSL_remove_list.
Require Import DG4iSL_list_lems.
Require Import DG4iSL_dec.
Require Import DLW_WO_list_nat.


Delimit Scope My_scope with M.
Open Scope My_scope.
Set Implicit Arguments.

Definition proj1_sigT2 {A : Type} (P : A -> Type) (e:sigT P) := match e with
                                    | existT _ a b => a
                                    end.

Definition proj2_sigT2 {A : Type} (P : A -> Type) (e : sigT P) :=
  match e return (P (proj1_sigT2 e)) with
  | existT _ a b => b
  end.

Lemma eq_dec_nat : forall (n m : nat), {n = m} + {n <> m}.
Proof.
decide equality.
Qed.

Lemma dec_le : forall (n m : nat), (n <= m) + (m <= n).
Proof.
induction n.
- destruct m ; auto. left. lia.
- destruct m ; auto. right ; lia. pose (IHn m). destruct s. left ; lia. right ; lia.
Qed.

(*------------------------------------------------------------------------------------------------------------------------------------------*)


(* Let us define our measure. It is the ordered list of numbers of occurrences
    of formulae of all complexity from the maximal complexity of a sequent to 0.
    The only trick is that we do unbox the left-hand side of the sequent as boxed
    formulas there are essentially dead-weights. *)

Inductive weight_test_ind (n : nat) (A : MPropF) (m : nat) : Type :=
  | testpos : (n = weight_form A) -> (m = 1) -> weight_test_ind n A m
  | testneg : (n <> weight_form A) -> (m = 0) -> weight_test_ind n A m.

Lemma dec_weight_test : forall n A,
  existsT2 m, (weight_test_ind n A m) * ((m = 1) + (m = 0)).
Proof.
intros. destruct (eq_dec_nat n (weight_form A)).
- subst. exists 1. split ; auto. apply testpos ; auto.
- exists 0 ; split ; auto. apply testneg ; auto.
Qed.

Definition weight_test n A : nat := proj1_sigT2 (dec_weight_test n A).

Lemma weight_test_0_or_1 : forall n A,
 (weight_test n A = 0) + (weight_test n A = 1).
Proof.
intros. unfold weight_test. destruct (dec_weight_test n A) ; destruct p ; destruct s ; auto.
Qed.

Fixpoint occ_weight_list (n : nat) (l : list MPropF) : nat :=
match l with
  | nil => 0
  | h :: t => (weight_test n h) + (occ_weight_list n t)
end.

Fixpoint list_occ_weight_list (n : nat) (l : list MPropF): list nat :=
match n with
  | 0 => nil
  | S m => (occ_weight_list (S m) l) :: (list_occ_weight_list m l)
end.

Lemma max_weight_list : forall l, existsT2 n, (forall B, InT B l -> weight_form B <= n) *
                (forall m, (forall B, InT B l -> weight_form B <= m) -> n <= m).
Proof.
induction l.
- simpl. exists 0. split ; auto. intros. inversion H. intros. lia.
- destruct IHl. destruct p. destruct (dec_le x (weight_form a)).
  * exists (weight_form a). split. intros. inversion H ; subst ; auto.
    pose (l0 B H1). lia. intros. apply H. apply InT_eq.
  * exists x. split. intros. inversion H ; subst ; auto. intros. apply l1. intros.
    apply H. apply InT_cons ; auto.
Qed.

Definition seq_list_occ_weight (s : list MPropF * (MPropF)) : list nat :=
          list_occ_weight_list (proj1_sigT2 (max_weight_list (unBoxed_list (fst s) ++ [snd s]))) (unBoxed_list (fst s) ++ [snd s]).


(*------------------------------------------------------------------------------------------------------------------------------------------*)


(* Use Dominique's work, which provides the correct induction principle (essentially formalises
    Shortlex). *)


(* We can thus define the triple which is the measure on sequents we were looking for. *)

Definition less_thanS (s0 s1 : list MPropF * (MPropF)) : Prop :=
     less_than lt (seq_list_occ_weight s0) (seq_list_occ_weight s1).

Notation "s0 '<<' s1" := (less_thanS s0 s1) (at level 70).

Fact less_thanS_inv l m : l << m -> (less_than lt (seq_list_occ_weight l) (seq_list_occ_weight m)).
Proof.
inversion 1; subst.
- left ; auto.
- right ; auto.
Qed.


Theorem less_thanS_wf : well_founded less_thanS.
Proof.
unfold less_thanS.
apply wf_inverse_image.
pose (@less_than_wf nat lt Nat.lt_wf_0).
pose (@lex_wf (list nat) (less_than lt) w).
auto.
Qed.

Fact lex_trans : forall l m n, (lex lt l m) -> (lex lt m n) -> (lex lt l n).
Proof.
intros l m n H. revert n. induction H.
- intros. inversion H0 ; subst. apply lex_skip ; auto. apply lex_cons ; auto. apply lex_length in H ; lia.
- intros. inversion H1 ; subst. apply lex_cons ; auto. apply lex_length in H5 ; lia.
  apply lex_cons ; lia.
Qed.

Fact less_thanS_trans l m n : l << m -> m << n -> l << n.
Proof.
inversion 1; subst.
- inversion 1 ; subst. 1-2: apply less_than_lt ; try lia. apply lex_length in H2 ; lia.
- inversion 1 ; subst. apply less_than_lt ; apply lex_length in H0 ; lia. apply less_than_eq.
  apply lex_trans with (m:=(seq_list_occ_weight m)) ; auto.
Qed.

Corollary less_thanS_rect (P : (list MPropF * (MPropF)) -> Type)
(HP : forall s, (forall s1, (less_than lt (seq_list_occ_weight s1) (seq_list_occ_weight s)) -> P s1) -> P s) s : P s.
Proof.
  induction s as [ s IHs ] using (well_founded_induction_type less_thanS_wf).
  apply HP; intros; apply IHs. unfold less_thanS ; auto.
Qed.

Lemma decT_lt : forall m n, (m < n) + ((m < n) -> False).
Proof.
induction m.
- destruct n. right. intro. inversion H. left. lia.
- destruct n. right. intro. inversion H. pose (IHm n). destruct s. left. lia. right. intro. apply f. lia.
Qed.

Lemma decT_less_than_lt : forall l0 l1, (less_than lt l0 l1) + ((less_than lt l0 l1) -> False).
Proof.
induction l0 ; intros.
- destruct l1. right. intro. apply less_than_inv in H. inversion H ; auto. simpl in H0 ; lia.
  inversion H0. simpl. left. apply less_than_lt ; simpl ; lia.
- destruct l1. right. intro. inversion H ; subst. simpl in H0 ; lia. inversion H0.
  destruct (IHl0 l1).
  + apply less_than_inv in l. destruct (decT_lt a n).
      * left. destruct l. apply less_than_lt. simpl ; lia. apply less_than_eq ; auto.
        apply lex_cons ; auto. simpl. apply lex_length in H ; auto.
      * destruct (eq_dec_nat (length l0) (length l1)). destruct (eq_dec_nat a n) ; subst.
        left. destruct l. exfalso ; lia. apply less_than_eq ; auto. apply lex_skip ; auto.
        right. intro. apply less_than_inv in H. destruct l ; try lia. destruct H. simpl in H. lia.
        inversion H ; subst ; auto. destruct (eq_dec_nat a n) ; subst. left. destruct l. apply less_than_lt ; auto.
        simpl ; lia. apply less_than_eq. apply lex_skip ; auto. left. destruct l. apply less_than_lt ; simpl ; lia.
        apply less_than_lt ; simpl. apply lex_length in H ; lia.
  + destruct (decT_lt a n).
      * destruct (eq_dec_nat (length l0) (length l1)). left. apply less_than_eq.
        apply lex_cons ; auto. right. intro. apply less_than_inv in H. destruct H. simpl in H.
        apply f. apply less_than_lt. lia. inversion H ; subst ; lia.
      * right. intro. apply less_than_inv in H. destruct H. simpl in H.
        apply f. apply less_than_lt. lia. inversion H ; subst. apply f. apply less_than_eq ; auto.
        lia.
Qed.


Theorem less_thanS_strong_inductionT:
forall P : (list MPropF * (MPropF)) -> Type,
(forall s0 : list MPropF * (MPropF), (forall s1 : list MPropF * (MPropF), ((s1 << s0) -> P s1)) -> P s0) ->
forall s : list MPropF * (MPropF), P s.
Proof.
intros P sIH.
assert (J: (forall s : list MPropF * (MPropF),
    (forall s1, (less_than lt (seq_list_occ_weight s1) (seq_list_occ_weight s)) -> P s1) -> P s)).
{ intros. apply sIH. intros. apply less_thanS_inv in H.
   destruct (decT_less_than_lt (seq_list_occ_weight s1) (seq_list_occ_weight s)). apply X ; auto.
   exfalso ; auto. }
pose (@less_thanS_rect P J) ; auto.
Qed.
