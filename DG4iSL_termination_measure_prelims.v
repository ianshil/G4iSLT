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
Require Import DG4iSL_termination_measure.
Require Import DLW_WO_list_nat.


(* Useful lemmas *)

Lemma length_max : forall n l, length (list_occ_weight_list n l) = n.
Proof.
induction n.
- intros. simpl ; auto.
- intros. simpl. pose (IHn l). lia.
Qed.

Lemma max_less_length : forall l1 l2 n m, n < m -> length (list_occ_weight_list n l1) < length (list_occ_weight_list m l2).
Proof.
intros. pose (length_max n l1). rewrite e. pose (length_max m l2). rewrite e0. auto.
Qed.

Lemma occ_weight_list_app_distrib : forall n l1 l2, occ_weight_list n (l1 ++ l2) = Nat.add (occ_weight_list n l1) (occ_weight_list n l2).
Proof.
intro n. induction l1.
- simpl. intros. auto.
- simpl. simpl in IHl1. intros. rewrite IHl1. lia.
Qed.

Lemma bigger_than_max_weight_0 : forall l n, ((proj1_sigT2 (max_weight_list l)) < n) -> (occ_weight_list n l = 0).
Proof.
induction l.
- intros. simpl. auto.
- intros. simpl. destruct (eq_dec_nat n (weight_form a)).
  + subst. exfalso. destruct (max_weight_list (a :: l)). simpl in H. destruct p.
     assert (InT a (a :: l)). apply InT_eq. pose (l0 a H0). lia.
  + assert (weight_test n a = 0). unfold weight_test. destruct (dec_weight_test n a). destruct p.
     destruct s. subst. inversion w. subst. exfalso. apply n0. auto. inversion H1. subst. inversion w. inversion H1.
     subst. simpl. auto. rewrite H0. simpl. apply IHl. destruct (max_weight_list (a :: l)). simpl in H.
     destruct p. destruct (max_weight_list l). destruct p. simpl in IHl. simpl.
     assert (x0 <= x). apply l3. intros. apply l0. apply InT_cons ; auto. lia.
Qed.

Lemma is_max_weight_bigger_0 : forall l, (0 < proj1_sigT2 (max_weight_list l)) -> (0 < occ_weight_list (proj1_sigT2 (max_weight_list l)) l).
Proof.
induction l.
- intros. exfalso. destruct (max_weight_list []). simpl in H. destruct p. assert (x <= 0).
  apply l0. intros. inversion H0. lia.
- intros. simpl. destruct (max_weight_list (a :: l)). simpl. simpl in H. destruct p.
  destruct (eq_dec_nat x (weight_form a)).
  + subst. unfold weight_test. destruct (dec_weight_test (weight_form a) a). destruct p.
     destruct s. subst. simpl. lia. subst. simpl. inversion w. inversion H1. exfalso. apply H0 ; auto.
  + assert (weight_test x a = 0). unfold weight_test. destruct (dec_weight_test x a). destruct p.
     destruct s. subst. inversion w. subst. exfalso. apply n. auto. inversion H1. subst. simpl. auto.
     rewrite H0. simpl.
     assert (x = (proj1_sigT2 (max_weight_list l))).
     { assert ((proj1_sigT2 (max_weight_list l)) <= x). destruct (max_weight_list l). simpl. simpl in IHl. destruct p.
       apply l3. intros. apply l0. apply InT_cons ; auto.
       assert (x <= (proj1_sigT2 (max_weight_list l))). assert (InT a (a :: l)). apply InT_eq. pose (l0 a H2).
       inversion l2. subst. exfalso. apply n ; auto. subst.
       assert (S m <= Nat.max (weight_form a) (proj1_sigT2 (max_weight_list l))). apply l1.
       intros. inversion H4. subst. lia. subst.
       assert (weight_form B <= (proj1_sigT2 (max_weight_list l))).
       destruct (max_weight_list l). subst. simpl. simpl in H1. simpl in IHl. destruct p. apply l3 ; auto.
       lia. lia. lia. }
     rewrite H1. apply IHl. lia.
Qed.

Lemma list_occ_weight_list_swap : forall l0 l1 l2 n, (list_occ_weight_list n (l0 ++ l1 ++ l2)) = (list_occ_weight_list n (l1 ++ l0 ++ l2)).
Proof.
induction n.
- intros. simpl ; auto.
- intros. simpl. rewrite IHn. repeat rewrite occ_weight_list_app_distrib.
  assert ((occ_weight_list (S n) l0 + (occ_weight_list (S n) l1 + occ_weight_list (S n) l2))%nat =
  (occ_weight_list (S n) l1 + (occ_weight_list (S n) l0 + occ_weight_list (S n) l2))%nat). lia. rewrite H. auto.
Qed.

Lemma list_occ_weight_list_headlist : forall  l0 l1 l2 x, (lex lt (list_occ_weight_list x l0) (list_occ_weight_list x l1)) ->
                                    (lex lt (list_occ_weight_list x (l0 ++ l2)) (list_occ_weight_list x (l1 ++ l2))).
Proof.
intros. generalize dependent l2. generalize dependent l1. generalize dependent l0.
induction x.
- simpl. intros. inversion H.
- intros. inversion H.
  * subst. apply IHx with (l2:=l2) in H1. simpl.
    destruct (dec_le (occ_weight_list (S x) (l0 ++ l2)) (occ_weight_list (S x) (l1 ++ l2))).
    + inversion l. rewrite H2. apply lex_skip ; auto. repeat rewrite occ_weight_list_app_distrib.
       rewrite occ_weight_list_app_distrib in H2. rewrite occ_weight_list_app_distrib in H0. apply lex_cons.
       repeat rewrite length_max ; auto. lia.
    + repeat rewrite occ_weight_list_app_distrib in l. repeat rewrite occ_weight_list_app_distrib. inversion l.
       rewrite H2. apply lex_skip ; auto. exfalso. lia.
  * subst. simpl. repeat rewrite occ_weight_list_app_distrib. apply lex_cons. repeat rewrite length_max ; auto. lia.
Qed.

Lemma lex_same_length : forall l0 l1, lex lt l0 l1 -> (length l0 = length l1).
Proof.
intros. induction H.
- simpl. rewrite IHlex. auto.
- simpl. auto.
Qed.

Lemma weight_form_more_one : forall A, 1 <= weight_form A.
Proof.
induction A ; simpl ; lia.
Qed.

Lemma list_occ_weight_list_relevant : forall  x l0 l1, (Nat.max (proj1_sigT2 (max_weight_list l0)) (proj1_sigT2 (max_weight_list l1)) <= x) ->
         (less_than lt (list_occ_weight_list (proj1_sigT2 (max_weight_list l0)) l0) (list_occ_weight_list (proj1_sigT2 (max_weight_list l1)) l1)) ->
         (lex lt (list_occ_weight_list x l0) (list_occ_weight_list x l1)).
Proof.
induction x.
- intros. simpl. exfalso. destruct l0. destruct l1. destruct (max_weight_list []). simpl in H. simpl in H0.
  destruct p. assert (x <= 0). lia. inversion H1. subst. simpl in H0. inversion H0.
  inversion H2. subst. inversion H2. destruct (max_weight_list []). simpl in H. simpl in H0.
  destruct p. assert (x <= 0). lia. inversion H1. subst. simpl in H0.
  destruct (max_weight_list (m :: l1)). simpl in H. simpl in H0. destruct p.
  assert (InT m (m :: l1)). apply InT_eq. pose (l2 m H2). destruct m ; simpl in l4 ; try lia.
  destruct (max_weight_list (m :: l0)). simpl in H. simpl in H0. destruct p.
  assert (InT m (m :: l0)). apply InT_eq. pose (l m H1). destruct m ; simpl in l3 ; try lia.
- intros. simpl. inversion H0.
  * subst. repeat rewrite length_max in H1. inversion H.
    + assert (proj1_sigT2 (max_weight_list l1) = S x). lia. rewrite H3. rewrite <- H2. apply lex_cons.
       repeat rewrite length_max ; auto.
       pose (bigger_than_max_weight_0 _ _ H1). rewrite e.
       apply is_max_weight_bigger_0. lia.
    + subst. pose (IHx _ _ H3 H0). assert (proj1_sigT2 (max_weight_list l0) < S x). lia.
       pose (bigger_than_max_weight_0 _ _ H2). rewrite e. assert (proj1_sigT2 (max_weight_list l1) < S x). lia.
       pose (bigger_than_max_weight_0 _ _ H4). rewrite e0. apply lex_skip ; auto.
  * subst. inversion H.
    + simpl. assert ((proj1_sigT2 (max_weight_list l1) = S x) * (proj1_sigT2 (max_weight_list l0) = S x)).
       { pose (lex_same_length _ _ H1). pose (length_max (proj1_sigT2 (max_weight_list l0)) l0). rewrite <- e0.
          pose (length_max (proj1_sigT2 (max_weight_list l1)) l1). rewrite <- e1. split ; lia. }
       destruct H2. inversion H1.
       { destruct (max_weight_list l0). simpl. simpl in H2. simpl in e0. rewrite e0 in H2. simpl in H2. inversion H2.
         simpl in H3.  rewrite H3. rewrite <- H7. destruct (max_weight_list l1). simpl. simpl in H4. simpl in e.
         rewrite e in H4. simpl in H4. inversion H4. simpl in H3. rewrite <- H9. apply lex_skip.
         rewrite <- H10. rewrite <- H8. auto. }
       { destruct (max_weight_list l0). simpl. simpl in H2. simpl in e0. rewrite e0 in H2. simpl in H2. inversion H2.
         simpl in H3.  rewrite H3. rewrite <- H8. destruct (max_weight_list l1). simpl. simpl in H4. simpl in e.
         rewrite e in H4. simpl in H4. inversion H4. simpl in H3. rewrite <- H10. apply lex_cons ; auto.
         repeat rewrite length_max ; auto. }
    + subst. pose (IHx _ _ H3 H0). assert (proj1_sigT2 (max_weight_list l0) < S x). lia.
       pose (bigger_than_max_weight_0 _ _ H2). rewrite e. assert (proj1_sigT2 (max_weight_list l1) < S x). lia.
       pose (bigger_than_max_weight_0 _ _ H4). rewrite e0. apply lex_skip ; auto.
Qed.

Lemma list_occ_weight_list_split : forall  l0 l1 l2 l3 x,
                                    (lex lt (list_occ_weight_list x l0) (list_occ_weight_list x l1)) ->
                                    (lex lt (list_occ_weight_list x l2) (list_occ_weight_list x l3)) ->
                                    (lex lt (list_occ_weight_list x (l0 ++ l2)) (list_occ_weight_list x (l1 ++ l3))).
Proof.
intros. generalize dependent l3. generalize dependent l2. generalize dependent l1. generalize dependent l0.
induction x.
- simpl. intros. inversion H.
- intros. inversion H ; subst.
  * simpl. inversion H0 ; subst.
    + pose (IHx _ _ H2 _ _ H3).
       destruct (dec_le (occ_weight_list (S x) (l0 ++ l2)) (occ_weight_list (S x) (l1 ++ l3))).
      -- inversion l4. rewrite H5. apply lex_skip ; auto. repeat rewrite occ_weight_list_app_distrib.
         rewrite occ_weight_list_app_distrib in H5. rewrite occ_weight_list_app_distrib in H1. apply lex_cons.
         repeat rewrite length_max ; auto. lia.
      -- repeat rewrite occ_weight_list_app_distrib in l4. repeat rewrite occ_weight_list_app_distrib. inversion l4.
          rewrite H5. apply lex_skip ; auto. exfalso. lia.
    + apply lex_cons. repeat rewrite length_max ; auto. repeat rewrite occ_weight_list_app_distrib. lia.
  * simpl. apply lex_cons. repeat rewrite length_max ; auto. repeat rewrite occ_weight_list_app_distrib. inversion H0 ; subst ; lia.
Qed.

Lemma list_occ_weight_cons : forall x l0 l1 (A : MPropF), (list_occ_weight_list x l0 = list_occ_weight_list x l1) ->
              (list_occ_weight_list x (A :: l0) = list_occ_weight_list x (A :: l1)).
Proof.
induction x ; simpl ; auto. intros. inversion H ; subst. rewrite IHx with (l1:=l1) ; auto.
Qed.

Lemma weight_test_refl_1 : forall B, weight_test (weight_form B) B = 1.
Proof.
intros. unfold weight_test. destruct (dec_weight_test (weight_form B) B) ; simpl.
destruct p. destruct s ; subst ; auto. inversion w. inversion H0. exfalso ; auto.
Qed.

Lemma list_occ_weight_lex : forall x l0 l1 (A B : MPropF), (list_occ_weight_list x l0 = list_occ_weight_list x l1) ->
              (weight_form B <= x) ->
              (weight_form A < weight_form B) ->
              (lex lt (list_occ_weight_list x (A :: l0)) (list_occ_weight_list x (B :: l1))).
Proof.
induction x ; simpl ; auto.
- intros. exfalso ; inversion H0 ; subst ; lia.
- intros. inversion H ; subst. inversion H0 ; subst.
  + rewrite weight_test_refl_1. apply lex_cons. repeat rewrite length_max ; auto.
     destruct (weight_test_0_or_1 (weight_form B) A) ; subst. rewrite e ; lia. exfalso.
     unfold weight_test in e. destruct (dec_weight_test (weight_form B) A). destruct p.
     simpl in e. destruct s ; subst. inversion w ; lia. inversion w ; lia.
  + pose (IHx l0 l1 A B H4 H5 H1).
     assert (weight_test (S x) B = 0). destruct (weight_test_0_or_1 (S x) B) ; subst ; auto. unfold weight_test in e.
     destruct (dec_weight_test (S x) B). simpl in e. destruct p. destruct s ; subst ; auto. inversion w ; lia. lia.
     assert (weight_test (S x) A = 0). destruct (weight_test_0_or_1 (S x) A) ; subst ; auto. unfold weight_test in e.
     destruct (dec_weight_test (S x) A). simpl in e. destruct p. destruct s ; subst ; auto. inversion w ; lia. lia.
     rewrite H2. rewrite H6. apply lex_skip. auto.
Qed.

Lemma list_occ_weight_lex_not_counted : forall x l (A : MPropF), (x < weight_form A) ->
              list_occ_weight_list x (A :: l) = list_occ_weight_list x l.
Proof.
induction x ; simpl ; auto. intros.
assert (weight_test (S x) A = 0). destruct (weight_test_0_or_1 (S x) A) ; subst ; auto. unfold weight_test in e.
destruct (dec_weight_test (S x) A). simpl in e. destruct p. destruct s ; subst ; auto. inversion w ; lia. lia.
rewrite H0 ; simpl. rewrite IHx ; auto. lia.
Qed.

Lemma list_occ_weight_lex_same_weight : forall x l0 l1 (A B : MPropF), (lex lt (list_occ_weight_list x l0) (list_occ_weight_list x l1)) ->
              (weight_form B <= x) ->
              (weight_form A <= weight_form B) ->
              (lex lt (list_occ_weight_list x (A :: l0)) (list_occ_weight_list x (B :: l1))).
Proof.
induction x ; simpl ; auto. intros. inversion H ; subst.
+ inversion H0 ; subst.
  - rewrite weight_test_refl_1. inversion H1 ; subst. rewrite weight_test_refl_1. apply lex_skip ; auto.
    repeat rewrite list_occ_weight_lex_not_counted ; auto ; try lia. simpl. apply lex_cons. repeat rewrite length_max ; auto.
    destruct (weight_test_0_or_1 (S m) A) ; subst ; simpl. rewrite e ; lia. exfalso.
    unfold weight_test in e. destruct (dec_weight_test (S m) A). destruct p.
    simpl in e. destruct s ; subst. inversion w ; lia. inversion w ; lia.
  - pose (IHx l0 l1 A B H3 H4 H1).
    assert (weight_test (S x) B = 0). destruct (weight_test_0_or_1 (S x) B) ; subst ; auto. unfold weight_test in e.
    destruct (dec_weight_test (S x) B). simpl in e. destruct p. destruct s ; subst ; auto. inversion w ; lia. lia.
    assert (weight_test (S x) A = 0). destruct (weight_test_0_or_1 (S x) A) ; subst ; auto. unfold weight_test in e.
    destruct (dec_weight_test (S x) A). simpl in e. destruct p. destruct s ; subst ; auto. inversion w ; lia. lia.
    rewrite H2. rewrite H6. apply lex_skip. auto.
+ apply lex_cons. repeat rewrite length_max ; auto.
   assert (weight_test (S x) A <= weight_test (S x) B). unfold weight_test. destruct (dec_weight_test (S x) A). destruct p.
   destruct (dec_weight_test (S x) B). destruct p. simpl. destruct s ; subst ; try lia. destruct s0 ; subst ; try lia.
   exfalso. inversion w ; subst ; try lia. inversion w0 ; subst ; lia.
   lia.
Qed.

Lemma unBoxed_list_stable_list_occ_weight : forall  l x,
      (proj1_sigT2 (max_weight_list l) <= x) ->
      ((list_occ_weight_list x l) = (list_occ_weight_list x (unBoxed_list l))) + (lex lt (list_occ_weight_list x (unBoxed_list l)) (list_occ_weight_list x l)).
Proof.
induction l ; intros ; simpl ; auto. destruct (max_weight_list (a :: l)). simpl in H. destruct p.
assert (proj1_sigT2 (max_weight_list l) <= x). destruct (max_weight_list l) ; simpl. simpl in IHl.
destruct p. apply l3 ; intros. assert (weight_form B <= x0). apply l0. apply InT_cons ;auto. lia.
apply IHl in H0. destruct H0 ; subst.
- destruct a ; simpl ; auto. 1-5: left ; apply list_occ_weight_cons ; auto.
  right. apply list_occ_weight_lex ; auto. assert (weight_form (Box a) <= x0). apply l0. apply InT_eq. lia.
- right. apply list_occ_weight_lex_same_weight ; auto. assert (weight_form a <= x0). apply l0. apply InT_eq. lia.
  destruct a ; simpl ; auto.
Qed.

Lemma unBoxed_list_weight_form : forall l n, (forall B, InT B l -> weight_form B <= n) ->  (forall B, InT B (unBoxed_list l) -> weight_form B <= n).
Proof.
induction l ; simpl ; intros ; auto. inversion H0 ; subst. assert (weight_form a <= n). apply H.
apply InT_eq. destruct a ; simpl in H1 ; simpl ; lia. apply IHl ; auto. intros. apply H. apply InT_cons ; auto.
Qed.

Lemma unBoxed_list_effective_or_not : forall l x, (proj1_sigT2 (max_weight_list l) <= x) ->
      (unBoxed_list l = l) + lex lt (list_occ_weight_list x (unBoxed_list l)) (list_occ_weight_list x l).
Proof.
induction l ; simpl ; auto ; intros. destruct (max_weight_list (a :: l)). simpl in H. destruct p.
destruct (dec_is_boxedT a).
- destruct a. 1-5: exfalso ; inversion i ; inversion H0. simpl. right.
  destruct (max_weight_list l). simpl in IHl. destruct p. assert (x1 <= x). apply l3. intros.
  assert (weight_form B <= x0). apply l0. simpl. apply InT_cons ; auto. lia.
  apply IHl in H0. destruct H0 ; subst.
  + rewrite e.
     epose (list_occ_weight_list_headlist [a] [Box a] _ x). simpl in l4. apply l4. clear l4.
     apply list_occ_weight_list_relevant.
     destruct (max_weight_list [a]). simpl. destruct p. assert (x2 <= x). apply l5. intros. inversion H0 ; subst.
     assert (weight_form (Box B) <= x0). apply l0. apply InT_eq. simpl in H1. lia. inversion H2.
     destruct (max_weight_list [Box a]). simpl. destruct p. assert (x3 <= x).
     apply l7. intros. assert (weight_form B <= x0). apply l0. inversion H1 ; subst. apply InT_eq.
     inversion H3. lia. lia.
     destruct (max_weight_list [a]). simpl. destruct p.
     destruct (max_weight_list [Box a]). simpl. destruct p. assert (x2 <= x3).
     apply l5. intros. assert (InT (Box a) [Box a]). apply InT_eq. apply l6 in H1. simpl in H1.
     inversion H0 ; subst. lia. inversion H3.
     apply less_than_lt. inversion H0 ; subst. 2: repeat rewrite length_max ; lia.
     exfalso. assert (weight_form (Box a) <= (weight_form a)).
     assert (weight_form (Box a) <= x3). apply l6. apply InT_eq.
     assert (x3 <= (weight_form a)). apply l5. intros.
     inversion H2 ; subst ; try lia. inversion H4. lia. simpl in H1 ; lia.
  + pose (list_occ_weight_list_split [a] [Box a] (unBoxed_list l) l).
     simpl in l5. apply l5 ; auto. clear l5.
     epose (list_occ_weight_list_headlist [a] [Box a] _ x). simpl in l5. apply l5. clear l5.
     apply list_occ_weight_list_relevant.
     destruct (max_weight_list [a]). simpl. destruct p. assert (x2 <= x). apply l6. intros. inversion H0 ; subst.
     assert (weight_form (Box B) <= x0). apply l0. apply InT_eq. simpl in H1. lia. inversion H2.
     destruct (max_weight_list [Box a]). simpl. destruct p. assert (x3 <= x).
     apply l8. intros. assert (weight_form B <= x0). apply l0. inversion H1 ; subst. apply InT_eq.
     inversion H3. lia. lia.
     destruct (max_weight_list [a]). simpl. destruct p.
     destruct (max_weight_list [Box a]). simpl. destruct p. assert (x2 <= x3).
     apply l6. intros. assert (InT (Box a) [Box a]). apply InT_eq. apply l7 in H1. simpl in H1.
     inversion H0 ; subst. lia. inversion H3.
     apply less_than_lt. inversion H0 ; subst. 2: repeat rewrite length_max ; lia.
     exfalso. assert (weight_form (Box a) <= (weight_form a)).
     assert (weight_form (Box a) <= x3). apply l7. apply InT_eq.
     assert (x3 <= (weight_form a)). apply l6. intros.
     inversion H2 ; subst ; try lia. inversion H4. lia. simpl in H1 ; lia.
- assert (unBox_formula a = a). destruct a ; auto. exfalso ; apply f ; eexists ;auto. rewrite H0.
  destruct (max_weight_list l). simpl in IHl. destruct p. assert (x1 <= x). apply l3. intros.
  assert (weight_form B <= x0). apply l0. apply InT_cons ; auto. lia.
  apply IHl in H1. destruct H1 ; subst.
  + left. rewrite e ; auto.
  + right.
     epose (list_occ_weight_list_swap [a] (unBoxed_list l) []). repeat rewrite <- app_nil_end in e. rewrite e.
     epose (list_occ_weight_list_swap [a] l []). repeat rewrite <- app_nil_end in e0. rewrite e0. clear e. clear e0.
     epose (list_occ_weight_list_headlist (unBoxed_list l) l _ x). simpl in l5. apply l5 ; auto.
Qed.
