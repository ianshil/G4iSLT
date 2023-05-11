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

(* AndR rule *)

Lemma AndR_le_counter : forall prem1 prem2 concl, AndRRule [prem1; prem2] concl ->
                (less_than lt (seq_list_occ_weight prem1) (seq_list_occ_weight concl)) *
                (less_than lt (seq_list_occ_weight prem2) (seq_list_occ_weight concl)).
Proof.
intros. inversion H. subst. simpl. unfold seq_list_occ_weight ; simpl.
destruct (max_weight_list (unBoxed_list Γ ++ [A])). simpl. destruct p.
destruct (max_weight_list (unBoxed_list Γ ++ [A ∧ B])). simpl. destruct p.
assert (x <= x0). apply l0. intros. apply InT_app_or in H0. destruct H0. apply l1 ; apply InT_or_app ; auto.
inversion i ; subst. assert (InT (B0 ∧ B) (unBoxed_list Γ ++ [B0 ∧ B])). apply InT_or_app ; right ; apply InT_eq.
apply l1 in H0. simpl in H0. lia. inversion H1.
split.
- destruct H0.
  * apply less_than_eq. epose (list_occ_weight_list_swap (unBoxed_list Γ) [A] [] x).
    simpl in e. repeat rewrite <- app_nil_end in e. repeat rewrite <- app_assoc in e. rewrite e. clear e.
    epose (list_occ_weight_list_swap (unBoxed_list Γ) [A ∧ B] [] x).
    simpl in e. repeat rewrite <- app_nil_end in e. repeat rewrite <- app_assoc in e. rewrite e. clear e.
    epose (list_occ_weight_list_headlist [A] [A ∧ B] _ x). simpl in l3. apply l3. clear l3.
    apply list_occ_weight_list_relevant.
    destruct (max_weight_list [A]). simpl. destruct p. assert (x0 <= x).
    apply l4. intros. apply l. apply InT_or_app ; auto.
    destruct (max_weight_list [A ∧ B]). simpl. destruct p. assert (x1 <= x).
    apply l6. intros. apply l1. apply InT_or_app ; auto. lia.
    destruct (max_weight_list [A]). simpl. destruct p.
    destruct (max_weight_list [A ∧ B]). simpl. destruct p. assert (x0 <= x1).
    apply l4. intros. inversion H0 ; subst. assert (InT (B0 ∧ B) [B0 ∧ B]). apply InT_eq.
    apply l5 in H1. simpl in H1. lia. inversion H2.
    apply less_than_lt. inversion H0 ; subst.
    exfalso. assert (weight_form (A ∧ B) <= weight_form A).
    assert (weight_form (A ∧ B) <= x1). apply l5. apply InT_eq.
    assert (x1 <= weight_form A). apply l4. intros. inversion H2 ; subst ; auto. inversion H4.
    lia. simpl in H1. lia. repeat rewrite length_max ; lia.
  * apply less_than_lt. repeat rewrite length_max ; lia.
- destruct (max_weight_list (unBoxed_list Γ ++ [B])). simpl. destruct p.
  assert (x1 <= x0). apply l4. intros. apply InT_app_or in H1. destruct H1. apply l1 ; apply InT_or_app ; auto.
  inversion i ; subst. assert (InT (A ∧ B0) (unBoxed_list Γ ++ [A ∧ B0])). apply InT_or_app ; right ; apply InT_eq.
  apply l1 in H1. simpl in H1 ; lia. inversion H2.
 destruct H1.
  * apply less_than_eq. epose (list_occ_weight_list_swap (unBoxed_list Γ) [B] [] x1).
    simpl in e. repeat rewrite <- app_nil_end in e. repeat rewrite <- app_assoc in e. rewrite e. clear e.
    epose (list_occ_weight_list_swap (unBoxed_list Γ) [A ∧ B] [] x1).
    simpl in e. repeat rewrite <- app_nil_end in e. repeat rewrite <- app_assoc in e. rewrite e. clear e.
    epose (list_occ_weight_list_headlist [B] [A ∧ B] _ x1). simpl in l5. apply l5. clear l5.
    apply list_occ_weight_list_relevant.
    destruct (max_weight_list [B]). simpl. destruct p. assert (x0 <= x1).
    apply l6. intros. apply l3. apply InT_or_app ; auto.
    destruct (max_weight_list [A ∧ B]). simpl. destruct p. assert (x2 <= x1).
    apply l8. intros. apply l1. apply InT_or_app ; auto. lia.
    destruct (max_weight_list [B]). simpl. destruct p.
    destruct (max_weight_list [A ∧ B]). simpl. destruct p. assert (x0 <= x2).
    apply l6. intros. inversion H1 ; subst. assert (InT (A ∧ B0) [A ∧ B0]). apply InT_eq.
    apply l7 in H2. simpl in H2. lia. inversion H3.
    apply less_than_lt. inversion H1 ; subst.
    exfalso. assert (weight_form (A ∧ B) <= weight_form B).
    assert (weight_form (A ∧ B) <= x2). apply l7. apply InT_eq.
    assert (x2 <= weight_form B). apply l6. intros. inversion H3 ; subst ; auto. inversion H5.
    lia. simpl in H2. lia. repeat rewrite length_max ; lia.
  * apply less_than_lt. repeat rewrite length_max ; lia.
Qed.

Theorem AndR_less_thanS : forall prem1 prem2 concl, AndRRule [prem1;prem2] concl ->
                                                          (prem1 << concl) * (prem2 << concl).
Proof.
intros. split.
- unfold less_thanS. pose (AndR_le_counter _ _ _ H). destruct p ; auto.
- unfold less_thanS. pose (AndR_le_counter _ _ _ H). destruct p ; auto.
Qed.



(*------------------------------------------------------------------------------------------------------------------------------------------*)



(* AndL rule *)

Lemma AndL_le_counter : forall prem concl, AndLRule [prem] concl -> less_than lt (seq_list_occ_weight prem) (seq_list_occ_weight concl).
Proof.
intros. inversion H. subst. simpl. unfold seq_list_occ_weight ; simpl. repeat rewrite unBox_app_distrib ; simpl.
repeat rewrite <- app_assoc ; simpl.
destruct (max_weight_list (unBoxed_list Γ0 ++ unBox_formula A :: unBox_formula B :: unBoxed_list Γ1 ++ [C])). simpl. destruct p.
destruct (max_weight_list (unBoxed_list Γ0 ++ A ∧ B :: unBoxed_list Γ1 ++ [C])). simpl. destruct p.
assert (x <= x0). apply l0. intros. apply InT_app_or in H0 ; destruct H0. apply l1 ; apply InT_or_app ; auto.
inversion i ; subst. assert (weight_form (A ∧ B) <= x0). apply l1. apply InT_or_app ; right ; apply InT_eq.
simpl in H0. destruct A ; simpl ; simpl in H0 ; lia. inversion H1 ; subst. assert (weight_form (A ∧ B) <= x0).
apply l1. apply InT_or_app ; right ; apply InT_eq. simpl in H0. destruct B ; simpl ; simpl in H0 ; lia.
apply l1. apply InT_or_app ; right ; apply InT_cons ; auto.
inversion H0 ; subst. 2: apply less_than_lt ; repeat rewrite length_max ; lia.
epose (list_occ_weight_list_swap (unBoxed_list Γ0) (unBox_formula A :: [unBox_formula B]) _ x0).
simpl in e. rewrite e. clear e.
epose (list_occ_weight_list_swap (unBoxed_list Γ0) [A ∧ B] _ x0).
simpl in e. rewrite e. clear e. apply less_than_eq.
epose (list_occ_weight_list_headlist (unBox_formula A :: [unBox_formula B]) [A ∧ B] _ x0). simpl in l3.
repeat rewrite <- app_assoc in l3. apply l3. clear l3. apply list_occ_weight_list_relevant.
destruct (max_weight_list [unBox_formula A; unBox_formula B]). simpl. destruct p. assert (x <= x0).
apply l4. intros. apply l. apply InT_or_app ; right. inversion H1 ; subst. apply InT_eq. apply InT_cons.
inversion H3 ; subst. apply InT_eq. inversion H4.
destruct (max_weight_list [A ∧ B]). simpl. destruct p. assert (x1 <= x0).
apply l6. intros. apply l1. apply InT_or_app ; right. inversion H2 ; subst. apply InT_eq. inversion H4. lia.
destruct (max_weight_list [unBox_formula A; unBox_formula B]). simpl. destruct p.
destruct (max_weight_list [A ∧ B]). simpl. destruct p. assert (x <= x1).
apply l4. intros. assert (InT (A ∧ B) [A ∧ B]). apply InT_eq. apply l5 in H2. simpl in H2.
inversion H1 ; subst. destruct A ; simpl in H2 ; simpl ; lia.
inversion H4 ; subst. destruct B ; simpl in H2 ; simpl ; lia. inversion H5.
apply less_than_lt. inversion H1 ; subst. 2: repeat rewrite length_max ; lia.
exfalso. assert (weight_form (A ∧ B) <= Nat.max (weight_form B) (weight_form A)).
assert (weight_form (A ∧ B) <= x1). apply l5. apply InT_eq.
assert (x1 <= Nat.max (weight_form B) (weight_form A)). apply l4. intros.
inversion H3 ; subst ; try lia. destruct A ; simpl ; lia. inversion H5 ; subst.
rewrite Nat.max_comm. destruct B ; simpl ; lia. inversion H6. lia. simpl in H2 ; lia.
Qed.

Theorem AndL_less_thanS : forall prem concl, AndLRule [prem] concl ->
                                                          (prem << concl).
Proof.
intros. unfold less_thanS. pose (AndL_le_counter _ _ H) ; auto.
Qed.
