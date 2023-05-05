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
Require Import DG4iSL_termination_measure_prelims.
Require Import DLW_WO_list_nat.


(* SLR rule *)


Lemma SLR_lt_counter : forall prem concl, SLRRule [prem] concl ->
                                    (less_than lt (seq_list_occ_weight prem) (seq_list_occ_weight concl)).
Proof.
intros prem concl RA. inversion RA. subst.
unfold seq_list_occ_weight ; simpl. repeat rewrite unBox_app_distrib ; simpl. repeat rewrite <- app_assoc ; simpl.
destruct (max_weight_list (unBoxed_list (unBoxed_list Γ) ++ [A; A])). simpl. destruct p.
destruct (max_weight_list (unBoxed_list Γ ++ [Box A])). simpl. destruct p.
assert (x <= x0). apply l0. intros. apply InT_app_or in H ; destruct H.
apply unBoxed_list_weight_form with (l:=(unBoxed_list Γ)) ; auto. intros. apply l1 ; apply InT_or_app ; auto.
assert (weight_form (Box A) <= x0). apply l1. apply InT_or_app ; right ; apply InT_eq. inversion i ; subst.
simpl in H ; lia. inversion H1 ; subst. simpl in H ; lia. inversion H2.
inversion H ; subst. 2: apply less_than_lt ; repeat rewrite length_max ; lia.
assert (proj1_sigT2 (max_weight_list (unBoxed_list Γ)) <= x0).
destruct (max_weight_list (unBoxed_list Γ)). simpl ; destruct p. apply l4. intros.
apply l1. apply InT_or_app ; auto.
pose (unBoxed_list_effective_or_not _ _ H0). destruct s.
- rewrite e.
  epose (list_occ_weight_list_swap (unBoxed_list Γ) [Box A] [] x0).
  simpl in e. repeat rewrite <- app_nil_end in e0. rewrite e0. clear e0.
  epose (list_occ_weight_list_swap (unBoxed_list Γ) [A;A] [] x0).
  simpl in e. repeat rewrite <- app_nil_end in e0. rewrite e0. clear e0. apply less_than_eq.
  epose (list_occ_weight_list_headlist [A;A] [Box A] _ x0). simpl in l3.
  repeat rewrite <- app_assoc in l3. apply l3. clear l3. apply list_occ_weight_list_relevant.
  destruct (max_weight_list [A; A]). simpl. destruct p. assert (x <= x0).
  apply l4. intros. apply l. apply InT_or_app ; right ; auto.
  destruct (max_weight_list [Box A]). simpl. destruct p. assert (x1 <= x0).
  apply l6. intros. apply l1. apply InT_or_app ; right. inversion H2 ; subst. apply InT_eq. inversion H4. lia.
  destruct (max_weight_list [A; A]). simpl. destruct p.
  destruct (max_weight_list [Box A]). simpl. destruct p. assert (x <= x1).
  apply l4. intros. assert (InT (Box A) [Box A]). apply InT_eq. apply l5 in H2. simpl in H2.
  inversion H1 ; subst. lia. inversion H4 ; subst. lia. inversion H5.
  apply less_than_lt. inversion H1 ; subst. 2: repeat rewrite length_max ; lia.
  exfalso. assert (weight_form (Box A) <= (weight_form A)).
  assert (weight_form (Box A) <= x1). apply l5. apply InT_eq.
  assert (x1 <= (weight_form A)). apply l4. intros.
  inversion H3 ; subst ; try lia. inversion H5 ; subst ; try lia. inversion H6. lia. simpl in H2 ; lia.
- apply less_than_eq.
  epose (list_occ_weight_list_split (unBoxed_list (unBoxed_list Γ)) (unBoxed_list Γ) [A;A] [Box A] x0). apply l4 ; auto.
  clear l4. apply list_occ_weight_list_relevant.
  destruct (max_weight_list [A; A]). simpl. destruct p. assert (x <= x0).
  apply l5. intros. apply l. apply InT_or_app ; right ; auto.
  destruct (max_weight_list [Box A]). simpl. destruct p. assert (x1 <= x0).
  apply l7. intros. apply l1. apply InT_or_app ; right. inversion H2 ; subst. apply InT_eq. inversion H4. lia.
  destruct (max_weight_list [A; A]). simpl. destruct p.
  destruct (max_weight_list [Box A]). simpl. destruct p. assert (x <= x1).
  apply l5. intros. assert (InT (Box A) [Box A]). apply InT_eq. apply l6 in H2. simpl in H2.
  inversion H1 ; subst. lia. inversion H4 ; subst. lia. inversion H5.
  apply less_than_lt. inversion H1 ; subst. 2: repeat rewrite length_max ; lia.
  exfalso. assert (weight_form (Box A) <= (weight_form A)).
  assert (weight_form (Box A) <= x1). apply l6. apply InT_eq.
  assert (x1 <= (weight_form A)). apply l5. intros.
  inversion H3 ; subst ; try lia. inversion H5 ; subst ; try lia. inversion H6. lia. simpl in H2 ; lia.
Qed.

Theorem SLR_less_thanS : forall prem concl, SLRRule [prem] concl ->
                                                          (prem << concl).
Proof.
intros. unfold less_thanS. apply SLR_lt_counter ; auto.
Qed.


