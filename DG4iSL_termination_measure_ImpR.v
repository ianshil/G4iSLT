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

(* ImpR rule *)

Lemma ImpR_le_counter : forall prem concl, ImpRRule [prem] concl -> less_than lt (seq_list_occ_weight prem) (seq_list_occ_weight concl).
Proof.
intros. inversion H. subst. simpl. unfold seq_list_occ_weight ; simpl. repeat rewrite unBox_app_distrib ; simpl.
repeat rewrite <- app_assoc ; simpl.
destruct (max_weight_list (unBoxed_list Γ0 ++ unBox_formula A :: unBoxed_list Γ1 ++ [B])). simpl. destruct p.
destruct (max_weight_list (unBoxed_list Γ0 ++ unBoxed_list Γ1 ++ [A → B])). simpl. destruct p.
assert (x <= x0). apply l0. intros. apply InT_app_or in H0 ; destruct H0. apply l1 ; apply InT_or_app ; auto.
inversion i ; subst. assert (weight_form (A → B) <= x0). apply l1. apply InT_or_app ; right ; apply InT_or_app ; right ; apply InT_eq.
simpl in H0. destruct A ; simpl ; simpl in H0 ; lia. apply InT_app_or in H1 ; destruct H1.
apply l1. apply InT_or_app ; right ; apply InT_or_app ; auto. inversion i0 ; subst.
assert (weight_form (A → B0) <= x0). apply l1. apply InT_or_app ; right ; apply InT_or_app ; right ; apply InT_eq.
simpl in H0. lia. inversion H1.
inversion H0 ; subst. 2: apply less_than_lt ; repeat rewrite length_max ; lia.
epose (list_occ_weight_list_swap (unBoxed_list Γ0) [unBox_formula A] _ x0).
simpl in e. rewrite e. clear e.
epose (list_occ_weight_list_swap (unBox_formula A :: unBoxed_list Γ0 ++ unBoxed_list Γ1) [B] [] x0).
simpl in e. repeat rewrite <- app_assoc in e. rewrite e. clear e.
epose (list_occ_weight_list_swap (unBoxed_list Γ0 ++ unBoxed_list Γ1) [A → B] [] x0).
simpl in e. repeat rewrite <- app_assoc in e. rewrite e. clear e.
apply less_than_eq.
epose (list_occ_weight_list_headlist (B :: [unBox_formula A]) [A → B] _ x0). simpl in l3.
repeat rewrite <- app_assoc in l3. apply l3. clear l3. apply list_occ_weight_list_relevant.
destruct (max_weight_list [B; unBox_formula A]). simpl. destruct p. assert (x <= x0).
apply l4. intros. apply l. apply InT_or_app ; right. inversion H1 ; subst.
apply InT_cons ; apply InT_or_app ; right ; apply InT_eq. inversion H3 ; subst.
apply InT_eq. inversion H4.
destruct (max_weight_list [A → B]). simpl. destruct p. assert (x1 <= x0).
apply l6. intros. apply l1. apply InT_or_app ; right. inversion H2 ; subst. apply InT_or_app ; right ; apply InT_eq. inversion H4. lia.
destruct (max_weight_list [B; unBox_formula A]). simpl. destruct p.
destruct (max_weight_list [A → B]). simpl. destruct p. assert (x <= x1).
apply l4. intros. assert (InT (A → B) [A → B]). apply InT_eq. apply l5 in H2. simpl in H2.
inversion H1 ; subst. simpl in H2 ; lia.
inversion H4 ; subst. destruct A ; simpl in H2 ; simpl ; lia. inversion H5.
apply less_than_lt. inversion H1 ; subst. 2: repeat rewrite length_max ; lia.
exfalso. assert (weight_form (A → B) <= Nat.max (weight_form B) (weight_form (unBox_formula A))).
assert (weight_form (A → B) <= x1). apply l5. apply InT_eq.
assert (x1 <= Nat.max (weight_form B) (weight_form (unBox_formula A))). apply l4. intros.
inversion H3 ; subst ; try lia. inversion H5 ; subst. destruct A ; simpl ; lia. inversion H6. lia.
destruct A ; simpl in H2 ; lia.
Qed.

Theorem ImpR_less_thanS : forall prem concl, ImpRRule [prem] concl ->
                                                          (prem << concl).
Proof.
intros. unfold less_thanS. pose (ImpR_le_counter _ _ H) ; auto.
Qed.

