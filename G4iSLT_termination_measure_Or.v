Require Import List.
Export ListNotations.
Require Import PeanoNat.
Require Import Lia.
Require Import Wellfounded.

Require Import general_export.

Require Import G4iSLT_calc.
Require Import G4iSLT_remove_list.
Require Import G4iSLT_list_lems.
Require Import G4iSLT_dec.
Require Import G4iSLT_termination_measure.
Require Import G4iSLT_termination_measure_prelims.
Require Import DLW_WO_list_nat.


(* OrR1 rule *)

Lemma OrR1_le_counter : forall prem concl, OrR1Rule [prem] concl -> less_than lt (seq_list_occ_weight prem) (seq_list_occ_weight concl).
Proof.
intros. inversion H. subst. simpl. unfold seq_list_occ_weight ; simpl.
destruct (max_weight_list (unBoxed_list Γ ++ [A])). simpl. destruct p.
destruct (max_weight_list (unBoxed_list Γ ++ [A ∨ B])). simpl. destruct p.
assert (x <= x0). apply l0. intros. apply InT_app_or in H0 ; destruct H0. apply l1 ; apply InT_or_app ; auto.
assert (weight_form (A ∨ B) <= x0). apply l1. apply InT_or_app ; right ; apply InT_eq. inversion i ; subst.
simpl in H0. lia.  inversion H2 ; subst.
inversion H0 ; subst. 2: apply less_than_lt ; repeat rewrite length_max ; lia.
epose (list_occ_weight_list_swap (unBoxed_list Γ) [A] _ x0).
simpl in e. rewrite e. clear e.
epose (list_occ_weight_list_swap (unBoxed_list Γ) [A ∨ B] _ x0).
simpl in e. rewrite e. clear e. apply less_than_eq.
epose (list_occ_weight_list_headlist [A] [A ∨ B] _ x0). simpl in l3.
repeat rewrite <- app_assoc in l3. apply l3. clear l3. apply list_occ_weight_list_relevant.
destruct (max_weight_list [A]). simpl. destruct p. assert (x <= x0).
apply l4. intros. apply l. apply InT_or_app ; right ; auto.
destruct (max_weight_list [A ∨ B]). simpl. destruct p. assert (x1 <= x0).
apply l6. intros. apply l1. apply InT_or_app ; right ; auto. lia.
destruct (max_weight_list [A]). simpl. destruct p.
destruct (max_weight_list [A ∨ B]). simpl. destruct p. assert (x <= x1).
apply l4. intros. assert (InT (A ∨ B) [A ∨ B]). apply InT_eq. apply l5 in H2. simpl in H2.
inversion H1 ; subst. destruct B0 ; simpl in H2 ; simpl ; lia. inversion H4.
apply less_than_lt. inversion H1 ; subst. 2: repeat rewrite length_max ; lia.
exfalso. assert (weight_form (A ∨ B) <= (weight_form A)).
assert (weight_form (A ∨ B) <= x1). apply l5. apply InT_eq.
assert (x1 <= (weight_form A)). apply l4. intros. inversion H3 ; subst. lia. inversion H5. lia.
simpl in H2 ; lia.
Qed.

Theorem OrR1_less_thanS : forall prem concl, OrR1Rule [prem] concl ->
                                                          (prem << concl).
Proof.
intros. unfold less_thanS. pose (OrR1_le_counter _ _ H) ; auto.
Qed.






(*------------------------------------------------------------------------------------------------------------------------------------------*)






(* OrR2 rule *)

Lemma OrR2_le_counter : forall prem concl, OrR2Rule [prem] concl -> less_than lt (seq_list_occ_weight prem) (seq_list_occ_weight concl).
Proof.
intros. inversion H. subst. simpl. unfold seq_list_occ_weight ; simpl.
destruct (max_weight_list (unBoxed_list Γ ++ [B])). simpl. destruct p.
destruct (max_weight_list (unBoxed_list Γ ++ [A ∨ B])). simpl. destruct p.
assert (x <= x0). apply l0. intros. apply InT_app_or in H0 ; destruct H0. apply l1 ; apply InT_or_app ; auto.
assert (weight_form (A ∨ B) <= x0). apply l1. apply InT_or_app ; right ; apply InT_eq. inversion i ; subst.
simpl in H0. lia.  inversion H2 ; subst.
inversion H0 ; subst. 2: apply less_than_lt ; repeat rewrite length_max ; lia.
epose (list_occ_weight_list_swap (unBoxed_list Γ) [B] _ x0).
simpl in e. rewrite e. clear e.
epose (list_occ_weight_list_swap (unBoxed_list Γ) [A ∨ B] _ x0).
simpl in e. rewrite e. clear e. apply less_than_eq.
epose (list_occ_weight_list_headlist [B] [A ∨ B] _ x0). simpl in l3.
repeat rewrite <- app_assoc in l3. apply l3. clear l3. apply list_occ_weight_list_relevant.
destruct (max_weight_list [B]). simpl. destruct p. assert (x <= x0).
apply l4. intros. apply l. apply InT_or_app ; right ; auto.
destruct (max_weight_list [A ∨ B]). simpl. destruct p. assert (x1 <= x0).
apply l6. intros. apply l1. apply InT_or_app ; right ; auto. lia.
destruct (max_weight_list [B]). simpl. destruct p.
destruct (max_weight_list [A ∨ B]). simpl. destruct p. assert (x <= x1).
apply l4. intros. assert (InT (A ∨ B) [A ∨ B]). apply InT_eq. apply l5 in H2. simpl in H2.
inversion H1 ; subst. destruct B0 ; simpl in H2 ; simpl ; lia. inversion H4.
apply less_than_lt. inversion H1 ; subst. 2: repeat rewrite length_max ; lia.
exfalso. assert (weight_form (A ∨ B) <= (weight_form B)).
assert (weight_form (A ∨ B) <= x1). apply l5. apply InT_eq.
assert (x1 <= (weight_form B)). apply l4. intros. inversion H3 ; subst. lia. inversion H5. lia.
simpl in H2 ; lia.
Qed.

Theorem OrR2_less_thanS : forall prem concl, OrR2Rule [prem] concl ->
                                                          (prem << concl).
Proof.
intros. unfold less_thanS. pose (OrR2_le_counter _ _ H) ; auto.
Qed.




(*------------------------------------------------------------------------------------------------------------------------------------------*)






(* OrL rule *)

Lemma OrL_le_counter : forall prem1 prem2 concl, OrLRule [prem1; prem2] concl ->
                (less_than lt (seq_list_occ_weight prem1) (seq_list_occ_weight concl)) *
                (less_than lt (seq_list_occ_weight prem2) (seq_list_occ_weight concl)).
Proof.
intros. inversion H. subst. simpl. unfold seq_list_occ_weight ;simpl. repeat rewrite unBox_app_distrib. simpl.
repeat rewrite <- app_assoc. simpl.
destruct (max_weight_list (unBoxed_list Γ0 ++ unBox_formula A :: unBoxed_list Γ1 ++ [C])). simpl. destruct p.
destruct (max_weight_list (unBoxed_list Γ0 ++ A ∨ B :: unBoxed_list Γ1 ++ [C])). simpl. destruct p.
destruct (max_weight_list (unBoxed_list Γ0 ++ unBox_formula B :: unBoxed_list Γ1 ++ [C])). simpl ; destruct p.
split.
- assert (x <= x0). apply l0. intros. apply InT_app_or in H0. destruct H0. apply l1 ; apply InT_or_app ; auto.
  inversion i ; subst. assert (weight_form (A ∨ B) <= x0). apply l1. apply InT_or_app ; right ; apply InT_eq.
  simpl in H0. destruct A ; simpl ; simpl in H0 ; lia. apply l1. apply InT_or_app ; right ; apply InT_cons ; auto. destruct H0.
  2: apply less_than_lt ; repeat rewrite length_max ; lia.
  apply less_than_eq.
  epose (list_occ_weight_list_swap (unBoxed_list Γ0) [unBox_formula A] _ x).
  simpl in e. repeat rewrite <- app_assoc in e. rewrite e. clear e.
  epose (list_occ_weight_list_swap (unBoxed_list Γ0) [A ∨ B] _ x).
  simpl in e. repeat rewrite <- app_assoc in e. rewrite e. clear e.
  epose (list_occ_weight_list_headlist [unBox_formula A] [A ∨ B] _ x). simpl in l5. apply l5. clear l5.
  apply list_occ_weight_list_relevant.
  destruct (max_weight_list [unBox_formula A]). simpl. destruct p. assert (x0 <= x).
  apply l6. intros. apply l. inversion H0 ; subst. apply InT_or_app ; right ; apply InT_eq. inversion H2.
  destruct (max_weight_list [A ∨ B]). simpl. destruct p. assert (x2 <= x).
  apply l8. intros. apply l1. inversion H1 ; subst. apply InT_or_app ; right ; apply InT_eq. inversion H3. lia.
  destruct (max_weight_list [unBox_formula A]). simpl. destruct p.
  destruct (max_weight_list [A ∨ B]). simpl. destruct p. assert (x0 <= x2).
  apply l6. intros. inversion H0 ; subst. assert (weight_form (A ∨ B) <= x2). apply l7. apply InT_eq.
  simpl in H1. destruct A ; simpl ; simpl in H1 ; lia. inversion H2.
  apply less_than_lt. inversion H0 ; subst. 2: repeat rewrite length_max ; lia.
  exfalso. assert (weight_form (A ∨ B) <= weight_form A).
  assert (weight_form (A ∨ B) <= x2). apply l7. apply InT_eq.
  assert (x2 <= weight_form A). apply l6. intros. inversion H2 ; subst. destruct A ; simpl ; lia. inversion H4.
  lia. simpl in H1. lia.
- assert (x1 <= x0). apply l4. intros. apply InT_app_or in H0. destruct H0. apply l1 ; apply InT_or_app ; auto.
  inversion i ; subst. assert (weight_form (A ∨ B) <= x0). apply l1. apply InT_or_app ; right ; apply InT_eq.
  simpl in H0. destruct B ; simpl ; simpl in H0 ; lia. apply l1. apply InT_or_app ; right ; apply InT_cons ; auto. destruct H0.
  2: apply less_than_lt ; repeat rewrite length_max ; lia.
  apply less_than_eq.
  epose (list_occ_weight_list_swap (unBoxed_list Γ0) [unBox_formula B] _ x1).
  simpl in e. repeat rewrite <- app_assoc in e. rewrite e. clear e.
  epose (list_occ_weight_list_swap (unBoxed_list Γ0) [A ∨ B] _ x1).
  simpl in e. repeat rewrite <- app_assoc in e. rewrite e. clear e.
  epose (list_occ_weight_list_headlist [unBox_formula B] [A ∨ B] _ x1). simpl in l5. apply l5. clear l5.
  apply list_occ_weight_list_relevant.
  destruct (max_weight_list [unBox_formula B]). simpl. destruct p. assert (x0 <= x1).
  apply l6. intros. apply l3. inversion H0 ; subst. apply InT_or_app ; right ; apply InT_eq. inversion H2.
  destruct (max_weight_list [A ∨ B]). simpl. destruct p. assert (x2 <= x1).
  apply l8. intros. apply l1. inversion H1 ; subst. apply InT_or_app ; right ; apply InT_eq. inversion H3. lia.
  destruct (max_weight_list [unBox_formula B]). simpl. destruct p.
  destruct (max_weight_list [A ∨ B]). simpl. destruct p. assert (x0 <= x2).
  apply l6. intros. inversion H0 ; subst. assert (weight_form (A ∨ B) <= x2). apply l7. apply InT_eq.
  simpl in H1. destruct B ; simpl ; simpl in H1 ; lia. inversion H2.
  apply less_than_lt. inversion H0 ; subst. 2: repeat rewrite length_max ; lia.
  exfalso. assert (weight_form (A ∨ B) <= weight_form B).
  assert (weight_form (A ∨ B) <= x2). apply l7. apply InT_eq.
  assert (x2 <= weight_form B). apply l6. intros. inversion H2 ; subst. destruct B ; simpl ; lia. inversion H4.
  lia. simpl in H1. lia.
Qed.

Theorem OrL_less_thanS : forall prem1 prem2 concl, OrLRule [prem1;prem2] concl ->
                                                          (prem1 << concl) * (prem2 << concl).
Proof.
intros. split.
- unfold less_thanS. pose (OrL_le_counter _ _ _ H) ; destruct p ; auto.
- unfold less_thanS. pose (OrL_le_counter _ _ _ H) ; destruct p ; auto.
Qed.
