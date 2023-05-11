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


(* AtomImpL1 rule *)

Lemma AtomImpL1_le_counter : forall prem concl, AtomImpL1Rule [prem] concl ->
        less_than lt (seq_list_occ_weight prem) (seq_list_occ_weight concl).
Proof.
intros. inversion H. subst. simpl. unfold seq_list_occ_weight ; simpl. repeat rewrite unBox_app_distrib ; simpl.
repeat rewrite <- app_assoc ; simpl.  repeat rewrite unBox_app_distrib ; simpl. repeat rewrite <- app_assoc ; simpl.
destruct (max_weight_list (unBoxed_list Γ0 ++ # P :: unBoxed_list Γ1 ++ unBox_formula A :: unBoxed_list Γ2 ++ [C])). simpl. destruct p.
destruct (max_weight_list (unBoxed_list Γ0 ++ # P :: unBoxed_list Γ1 ++ # P → A :: unBoxed_list Γ2 ++ [C])). simpl. destruct p.
assert (x <= x0). apply l0. intros. apply InT_app_or in H0 ; destruct H0. apply l1 ; apply InT_or_app ; auto.
inversion i ; subst. assert (weight_form (# P → A) <= x0). apply l1.
apply InT_or_app ; right ; apply InT_cons ; apply InT_or_app ; right ; apply InT_eq.
simpl in H0. simpl. lia. apply InT_app_or in H1. destruct H1. apply l1.
apply InT_or_app ; right ; apply InT_cons ; apply InT_or_app ; auto. inversion i0 ; subst.
assert (weight_form (# P → A) <= x0). apply l1.
apply InT_or_app ; right ; apply InT_cons ; apply InT_or_app ; right ; apply InT_eq.
simpl in H0. destruct A ; simpl ; simpl in H0 ; lia. apply InT_app_or in H1 ; destruct H1 ;
apply l1 ; apply InT_or_app ; right ; apply InT_cons ; apply InT_or_app ; right ; apply InT_cons ; apply InT_or_app ; auto.
inversion H0 ; subst. 2: apply less_than_lt ; repeat rewrite length_max ; lia.
epose (list_occ_weight_list_swap (unBoxed_list Γ0 ++ # P :: unBoxed_list Γ1) [unBox_formula A] _ x0).
simpl in e. repeat rewrite <- app_assoc in e. simpl in e. rewrite e. clear e.
epose (list_occ_weight_list_swap (unBoxed_list Γ0 ++ # P :: unBoxed_list Γ1) [# P → A] _ x0).
simpl in e. repeat rewrite <- app_assoc in e. simpl in e. rewrite e. clear e.
epose (list_occ_weight_list_headlist [unBox_formula A] [# P → A] _ x0). simpl in l3.
repeat rewrite <- app_assoc in l3. apply less_than_eq. apply l3. clear l3. apply list_occ_weight_list_relevant.
destruct (max_weight_list [unBox_formula A]). simpl. destruct p. assert (x <= x0).
apply l4. intros. apply l. inversion H1 ; subst. apply InT_or_app ; right ; apply InT_cons ; apply InT_or_app ; right ; apply InT_eq.
inversion H3.
destruct (max_weight_list [# P → A]). simpl. destruct p. assert (x1 <= x0).
apply l6. intros. apply l1. apply InT_or_app ; right. inversion H2 ; subst. apply InT_cons ; apply InT_or_app ; right ; apply InT_eq.
inversion H4. lia.
destruct (max_weight_list [unBox_formula A]). simpl. destruct p.
destruct (max_weight_list [# P → A]). simpl. destruct p. assert (x <= x1).
apply l4. intros. assert (InT (# P → A) [# P → A]). apply InT_eq. apply l5 in H2. simpl in H2.
inversion H1 ; subst. destruct A ; simpl in H2 ; simpl ; lia. inversion H4.
apply less_than_lt. inversion H1 ; subst. 2: repeat rewrite length_max ; lia.
exfalso. assert (weight_form (# P → A) <= (weight_form A)).
assert (weight_form (# P → A) <= x1). apply l5. apply InT_eq.
assert (x1 <= (weight_form A)). apply l4. intros.
inversion H3 ; subst ; try lia. destruct A ; simpl ; lia. inversion H5 ; subst.
lia. simpl in H2 ; lia.
Qed.

Theorem AtomImpL1_less_thanS : forall prem concl, AtomImpL1Rule [prem] concl ->
                                                          (prem << concl).
Proof.
intros. unfold less_thanS. pose (AtomImpL1_le_counter _ _ H) ; auto.
Qed.


(*------------------------------------------------------------------------------------------------------------------------------------------*)


(* AtomImpL2 rule *)


Lemma AtomImpL2_le_counter : forall prem concl, AtomImpL2Rule [prem] concl ->
         (less_than lt (seq_list_occ_weight prem) (seq_list_occ_weight concl)).
Proof.
intros. inversion H. subst. simpl. unfold seq_list_occ_weight ; simpl. repeat rewrite unBox_app_distrib ; simpl.
repeat rewrite <- app_assoc ; simpl.  repeat rewrite unBox_app_distrib ; simpl. repeat rewrite <- app_assoc ; simpl.
destruct (max_weight_list (unBoxed_list Γ0 ++ unBox_formula A :: unBoxed_list Γ1 ++ # P :: unBoxed_list Γ2 ++ [C])). simpl. destruct p.
destruct (max_weight_list (unBoxed_list Γ0 ++ # P → A :: unBoxed_list Γ1 ++ # P :: unBoxed_list Γ2 ++ [C])). simpl. destruct p.
assert (x <= x0). apply l0. intros. apply InT_app_or in H0 ; destruct H0. apply l1 ; apply InT_or_app ; auto.
inversion i ; subst. assert (weight_form (# P → A) <= x0). apply l1.
apply InT_or_app ; right ; apply InT_eq. simpl in H0. destruct A ; simpl ; simpl in H0 ; lia.
apply InT_app_or in H1. destruct H1. apply l1.
apply InT_or_app ; right ; apply InT_cons ; apply InT_or_app ; auto. inversion i0 ; subst.
assert (weight_form (# P → A) <= x0). apply l1. apply InT_or_app ; right ; apply InT_eq.
simpl in H0 ; simpl ; lia. apply InT_app_or in H1 ; destruct H1 ;
apply l1 ; apply InT_or_app ; right ; apply InT_cons ; apply InT_or_app ; right ; apply InT_cons ; apply InT_or_app ; auto.
inversion H0 ; subst. 2: apply less_than_lt ; repeat rewrite length_max ; lia.
epose (list_occ_weight_list_swap (unBoxed_list Γ0) [unBox_formula A] _ x0).
simpl in e. repeat rewrite <- app_assoc in e. simpl in e. rewrite e. clear e.
epose (list_occ_weight_list_swap (unBoxed_list Γ0) [# P → A] _ x0).
simpl in e. repeat rewrite <- app_assoc in e. simpl in e. rewrite e. clear e.
epose (list_occ_weight_list_headlist [unBox_formula A] [# P → A] _ x0). simpl in l3.
repeat rewrite <- app_assoc in l3. apply less_than_eq. apply l3. clear l3. apply list_occ_weight_list_relevant.
destruct (max_weight_list [unBox_formula A]). simpl. destruct p. assert (x <= x0).
apply l4. intros. apply l. inversion H1 ; subst. apply InT_or_app ; right ; apply InT_eq.
inversion H3.
destruct (max_weight_list [# P → A]). simpl. destruct p. assert (x1 <= x0).
apply l6. intros. apply l1. apply InT_or_app ; right. inversion H2 ; subst. apply InT_eq.
inversion H4. lia.
destruct (max_weight_list [unBox_formula A]). simpl. destruct p.
destruct (max_weight_list [# P → A]). simpl. destruct p. assert (x <= x1).
apply l4. intros. assert (InT (# P → A) [# P → A]). apply InT_eq. apply l5 in H2. simpl in H2.
inversion H1 ; subst. destruct A ; simpl in H2 ; simpl ; lia. inversion H4.
apply less_than_lt. inversion H1 ; subst. 2: repeat rewrite length_max ; lia.
exfalso. assert (weight_form (# P → A) <= (weight_form A)).
assert (weight_form (# P → A) <= x1). apply l5. apply InT_eq.
assert (x1 <= (weight_form A)). apply l4. intros.
inversion H3 ; subst ; try lia. destruct A ; simpl ; lia. inversion H5 ; subst.
lia. simpl in H2 ; lia.
Qed.

Theorem AtomImpL2_less_thanS : forall prem concl, AtomImpL2Rule [prem] concl ->
                                                          (prem << concl).
Proof.
intros. unfold less_thanS. pose (AtomImpL2_le_counter _ _ H) ; auto.
Qed.


(*------------------------------------------------------------------------------------------------------------------------------------------*)


(* AndImpL rule *)


Lemma AndImpL_le_counter : forall prem concl, AndImpLRule [prem] concl ->
         (less_than lt (seq_list_occ_weight prem) (seq_list_occ_weight concl)).
Proof.
intros. inversion H. subst. simpl. unfold seq_list_occ_weight ; simpl. repeat rewrite unBox_app_distrib ; simpl.
repeat rewrite <- app_assoc ; simpl.  repeat rewrite unBox_app_distrib ; simpl. repeat rewrite <- app_assoc ; simpl.
destruct (max_weight_list (unBoxed_list Γ0 ++ A → B → C :: unBoxed_list Γ1 ++ [D])). simpl. destruct p.
destruct (max_weight_list (unBoxed_list Γ0 ++ (A ∧ B) → C :: unBoxed_list Γ1 ++ [D])). simpl. destruct p.
assert (x <= x0). apply l0. intros. apply InT_app_or in H0 ; destruct H0. apply l1 ; apply InT_or_app ; auto.
inversion i ; subst. assert (weight_form ((A ∧ B) → C) <= x0). apply l1.
apply InT_or_app ; right ; apply InT_eq. simpl in H0. simpl. lia.
apply InT_app_or in H1. destruct H1. apply l1.
apply InT_or_app ; right ; apply InT_cons ; apply InT_or_app ; auto. inversion i0 ; subst.
apply l1. apply InT_or_app ; right ; apply InT_cons ; apply InT_or_app ; auto. inversion H1.
inversion H0 ; subst. 2: apply less_than_lt ; repeat rewrite length_max ; lia.
epose (list_occ_weight_list_swap (unBoxed_list Γ0) [A → B → C] _ x0).
simpl in e. repeat rewrite <- app_assoc in e. simpl in e. rewrite e. clear e.
epose (list_occ_weight_list_swap (unBoxed_list Γ0) [(A ∧ B) → C] _ x0).
simpl in e. repeat rewrite <- app_assoc in e. simpl in e. rewrite e. clear e.
epose (list_occ_weight_list_headlist [A → B → C] [(A ∧ B) → C] _ x0). simpl in l3.
repeat rewrite <- app_assoc in l3. apply less_than_eq. apply l3. clear l3. apply list_occ_weight_list_relevant.
destruct (max_weight_list [A → B → C]). simpl. destruct p. assert (x <= x0).
apply l4. intros. apply l. inversion H1 ; subst. apply InT_or_app ; right ; apply InT_eq.
inversion H3.
destruct (max_weight_list [(A ∧ B) → C]). simpl. destruct p. assert (x1 <= x0).
apply l6. intros. apply l1. apply InT_or_app ; right. inversion H2 ; subst. apply InT_eq.
inversion H4. lia.
destruct (max_weight_list [A → B → C]). simpl. destruct p.
destruct (max_weight_list [(A ∧ B) → C]). simpl. destruct p. assert (x <= x1).
apply l4. intros. assert (InT ((A ∧ B) → C) [(A ∧ B) → C]). apply InT_eq. apply l5 in H2. simpl in H2.
inversion H1 ; subst. simpl in H2 ; simpl ; lia. inversion H4.
apply less_than_lt. inversion H1 ; subst. 2: repeat rewrite length_max ; lia.
exfalso. assert (weight_form ((A ∧ B) → C) <= (weight_form (A → B → C))).
assert (weight_form ((A ∧ B) → C) <= x1). apply l5. apply InT_eq.
assert (x1 <= (weight_form (A → B → C))). apply l4. intros.
inversion H3 ; subst ; try lia. inversion H5 ; subst. lia. simpl in H2 ; lia.
Qed.

Theorem AndImpL_less_thanS : forall prem concl, AndImpLRule [prem] concl ->
                                                          (prem << concl).
Proof.
intros. unfold less_thanS. pose (AndImpL_le_counter _ _ H) ; auto.
Qed.


(*------------------------------------------------------------------------------------------------------------------------------------------*)



(* OrImpL rule *)

Lemma OrImpL_le_counter : forall prem concl, OrImpLRule [prem] concl ->
         (less_than lt (seq_list_occ_weight prem) (seq_list_occ_weight concl)).
Proof.
intros. inversion H. subst. simpl. unfold seq_list_occ_weight ; simpl. repeat rewrite unBox_app_distrib ; simpl.
repeat rewrite <- app_assoc ; simpl.  repeat rewrite unBox_app_distrib ; simpl. repeat rewrite <- app_assoc ; simpl.
destruct (max_weight_list (unBoxed_list Γ0 ++ A → C :: unBoxed_list Γ1 ++ B → C :: unBoxed_list Γ2 ++ [D])). simpl. destruct p.
destruct (max_weight_list (unBoxed_list Γ0 ++ (A ∨ B) → C :: unBoxed_list Γ1 ++ unBoxed_list Γ2 ++ [D])). simpl. destruct p.
assert (x <= x0). apply l0. intros. apply InT_app_or in H0 ; destruct H0. apply l1 ; apply InT_or_app ; auto.
inversion i ; subst. assert (weight_form ((A ∨ B) → C) <= x0). apply l1.
apply InT_or_app ; right ; apply InT_eq. simpl in H0. simpl. lia.
apply InT_app_or in H1. destruct H1. apply l1.
apply InT_or_app ; right ; apply InT_cons ; apply InT_or_app ; auto. inversion i0 ; subst.
assert (weight_form ((A ∨ B) → C) <= x0). apply l1.
apply InT_or_app ; right ; apply InT_eq. simpl in H0. simpl. lia.
apply l1. apply InT_or_app ; right ; apply InT_cons ; apply InT_or_app ; auto.
inversion H0 ; subst. 2: apply less_than_lt ; repeat rewrite length_max ; lia.
epose (list_occ_weight_list_swap (unBoxed_list Γ0) [A → C] _ x0).
simpl in e. repeat rewrite <- app_assoc in e. simpl in e. rewrite e. clear e.
epose (list_occ_weight_list_swap (A → C :: unBoxed_list Γ0 ++ unBoxed_list Γ1) [B → C] _ x0).
simpl in e. repeat rewrite <- app_assoc in e. simpl in e. rewrite e. clear e.
epose (list_occ_weight_list_swap (unBoxed_list Γ0) [(A ∨ B) → C] _ x0).
simpl in e. repeat rewrite <- app_assoc in e. simpl in e. rewrite e. clear e.
epose (list_occ_weight_list_headlist [B → C; A → C] [(A ∨ B) → C] _ x0). simpl in l3.
repeat rewrite <- app_assoc in l3. apply less_than_eq. apply l3. clear l3.
apply list_occ_weight_list_relevant.
destruct (max_weight_list [B → C; A → C]). simpl. destruct p. assert (x <= x0).
apply l4. intros. apply l. inversion H1 ; subst.
apply InT_or_app ; right ; apply InT_cons ; apply InT_or_app ; right ; apply InT_eq.
inversion H3 ; subst. apply InT_or_app ; right ; apply InT_eq. inversion H4.
destruct (max_weight_list [(A ∨ B) → C]). simpl. destruct p. assert (x1 <= x0).
apply l6. intros. apply l1. apply InT_or_app ; right. inversion H2 ; subst. apply InT_eq.
inversion H4. lia.
destruct (max_weight_list [B → C; A → C]). simpl. destruct p.
destruct (max_weight_list [(A ∨ B) → C]). simpl. destruct p. assert (x <= x1).
apply l4. intros. assert (InT ((A ∨ B) → C) [(A ∨ B) → C]). apply InT_eq. apply l5 in H2. simpl in H2.
inversion H1 ; subst. simpl in H2 ; simpl ; lia. inversion H4 ; subst. simpl in H2 ; simpl ; lia. inversion H5.
apply less_than_lt. inversion H1 ; subst. 2: repeat rewrite length_max ; lia.
exfalso. assert (weight_form ((A ∨ B) → C) <= Nat.max (weight_form (B → C)) (weight_form (A → C))).
assert (weight_form ((A ∨ B) → C) <= x1). apply l5. apply InT_eq.
assert (x1 <= Nat.max (weight_form (B → C)) (weight_form (A → C))). apply l4. intros.
inversion H3 ; subst ; try lia. inversion H5 ; subst ; try lia. inversion H6. lia. simpl in H2 ; lia.
Qed.

Theorem OrImpL_less_thanS : forall prem concl, OrImpLRule [prem] concl ->
                                                          (prem << concl).
Proof.
intros. unfold less_thanS. pose (OrImpL_le_counter _ _ H) ; auto.
Qed.


(*------------------------------------------------------------------------------------------------------------------------------------------*)


(* ImpImpL rule *)

Lemma ImpImpL_le_counter : forall prem1 prem2 concl, ImpImpLRule [prem1; prem2] concl ->
                (less_than lt (seq_list_occ_weight prem1) (seq_list_occ_weight concl)) *
                (less_than lt (seq_list_occ_weight prem2) (seq_list_occ_weight concl)).
Proof.
intros. inversion H. subst. simpl. unfold seq_list_occ_weight ; simpl. repeat rewrite unBox_app_distrib ; simpl.
repeat rewrite <- app_assoc ; simpl.
destruct (max_weight_list (unBoxed_list Γ0 ++ B → C :: unBoxed_list Γ1 ++ [A → B])). simpl. destruct p.
destruct (max_weight_list (unBoxed_list Γ0 ++ (A → B) → C :: unBoxed_list Γ1 ++ [D])). simpl. destruct p.
destruct (max_weight_list (unBoxed_list Γ0 ++ unBox_formula C :: unBoxed_list Γ1 ++ [D])). simpl. destruct p.
assert (x <= x0). apply l0. intros. apply InT_app_or in H0. destruct H0. apply l1 ; apply InT_or_app ; auto.
inversion i ; subst. assert (weight_form ((A → B) → C) <= x0). apply l1. apply InT_or_app ; right ; apply InT_eq.
simpl in H0. simpl. lia. apply InT_app_or in H1 ; destruct H1. apply l1.
apply InT_or_app ; right ; apply InT_cons ; apply InT_or_app ; auto. inversion i0 ; subst.  assert (weight_form ((A → B) → C) <= x0).
apply l1. apply InT_or_app ; right ; apply InT_eq. simpl in H0. simpl. lia. inversion H1.
assert (x1 <= x0). apply l4. intros. apply InT_app_or in H1. destruct H1. apply l1 ; apply InT_or_app ; auto.
inversion i ; subst. assert (weight_form ((A → B) → C) <= x0). apply l1. apply InT_or_app ; right ; apply InT_eq.
simpl in H1. destruct C ; simpl ; simpl in H1 ; lia. apply l1.  apply InT_or_app ; right ; apply InT_cons ; auto.
split.
- destruct H0. 2: apply less_than_lt ; repeat rewrite length_max ; lia.
  apply less_than_eq.
  epose (list_occ_weight_list_swap (unBoxed_list Γ0) [B → C] _ x).
  simpl in e. repeat rewrite <- app_assoc in e. rewrite e. clear e.
  epose (list_occ_weight_list_swap (B → C :: unBoxed_list Γ0 ++ unBoxed_list Γ1) [A → B] [] x).
  simpl in e. repeat rewrite <- app_nil_end in e. repeat rewrite <- app_assoc in e. rewrite e. clear e.
  epose (list_occ_weight_list_swap (unBoxed_list Γ0) [(A → B) → C] _ x).
  simpl in e. repeat rewrite <- app_assoc in e. rewrite e. clear e.
  epose (list_occ_weight_list_split (A → B :: [B → C]) [(A → B) → C] (unBoxed_list Γ0 ++ unBoxed_list Γ1) (unBoxed_list Γ0 ++ unBoxed_list Γ1 ++ [D]) x).
  simpl in l5. apply l5. clear l5.
  apply list_occ_weight_list_relevant.
  destruct (max_weight_list [A → B; B → C]). simpl. destruct p. assert (x0 <= x).
  apply l6. intros. apply l. inversion H0 ; subst.
  apply InT_or_app ; right ; apply InT_cons ; apply InT_or_app ; right ; apply InT_eq.
  inversion H3 ; subst. apply InT_or_app ; right ; apply InT_eq. inversion H4.
  destruct (max_weight_list [(A → B) → C]). simpl. destruct p. assert (x2 <= x).
  apply l8. intros. apply l1. apply InT_or_app ; right. inversion H2 ; subst. apply InT_eq.
  inversion H4. lia.
  destruct (max_weight_list [A → B; B → C]). simpl. destruct p.
  destruct (max_weight_list [(A → B) → C]). simpl. destruct p. assert (x0 <= x2).
  apply l6. intros. assert (InT ((A → B) → C) [(A → B) → C]). apply InT_eq. apply l7 in H2. simpl in H2.
  inversion H0 ; subst. simpl in H2 ; simpl ; lia. inversion H4 ; subst. simpl in H2 ; simpl ; lia. inversion H5.
  apply less_than_lt. inversion H0 ; subst. 2: repeat rewrite length_max ; lia.
  exfalso. assert (weight_form ((A → B) → C) <= Nat.max (weight_form (A → B)) (weight_form (B → C))).
  assert (weight_form ((A → B) → C) <= x2). apply l7. apply InT_eq.
  assert (x2 <= Nat.max (weight_form (A → B)) (weight_form (B → C))). apply l6. intros.
  inversion H3 ; subst ; try lia. inversion H5 ; subst ; try lia. inversion H6. lia. simpl in H2 ; lia.
  epose (list_occ_weight_list_swap (unBoxed_list Γ0 ++ unBoxed_list Γ1) [D] [] x).
  simpl in e. repeat rewrite <- app_assoc in e. rewrite e. clear e. clear l5. rewrite <- app_nil_end.
  epose (list_occ_weight_list_headlist [] [D] _ x).
  simpl in l5. apply l5. clear l5. apply list_occ_weight_list_relevant.
  destruct (max_weight_list []). simpl. destruct p. assert (x0 <= x).
  apply l6. intros. inversion H0.
  destruct (max_weight_list [D]). simpl. destruct p. assert (x2 <= x).
  apply l8. intros. apply l1. apply InT_or_app ; right. inversion H2 ; subst.
  apply InT_cons ; apply InT_or_app ; right ; apply InT_eq. inversion H4. lia.
  destruct (max_weight_list []). simpl. destruct p.
  destruct (max_weight_list [D]). simpl. destruct p. assert (x0 <= x2).
  apply l6. intros. assert (InT D [D]). apply InT_eq. apply l7 in H2. simpl in H2.
  inversion H0 ; subst. apply less_than_lt. inversion H0 ; subst. 2: repeat rewrite length_max ; lia.
  exfalso. assert (weight_form D <= 0). assert (weight_form D <= x2). apply l7. apply InT_eq.
  assert (x2 <= 0). apply l6. intros. inversion H3 ; subst ; try lia. simpl ; lia. destruct D ; simpl in H2 ; lia.
- destruct H1. 2: apply less_than_lt ; repeat rewrite length_max ; lia.
  apply less_than_eq.
  epose (list_occ_weight_list_swap (unBoxed_list Γ0) [unBox_formula C] _ x1).
  simpl in e. repeat rewrite <- app_assoc in e. rewrite e. clear e.
  epose (list_occ_weight_list_swap (unBoxed_list Γ0) [(A → B) → C] _ x1).
  simpl in e. repeat rewrite <- app_assoc in e. rewrite e. clear e.
  epose (list_occ_weight_list_headlist [unBox_formula C] [(A → B) → C] _ x1).
  simpl in l5. apply l5. clear l5. apply list_occ_weight_list_relevant.
  destruct (max_weight_list [unBox_formula C]). simpl. destruct p. assert (x0 <= x1).
  apply l6. intros. inversion H1 ; subst. assert (weight_form ((A → B) → C) <= x1). apply l1.
  apply InT_or_app ; right ; apply InT_eq. destruct C ; simpl in H2 ; simpl ; lia. inversion H3.
  destruct (max_weight_list [(A → B) → C]). simpl. destruct p. assert (x2 <= x1).
  apply l8. intros. apply l1. apply InT_or_app ; right. inversion H2 ; subst. apply InT_eq.
  inversion H4. lia.
  destruct (max_weight_list [unBox_formula C]). simpl. destruct p.
  destruct (max_weight_list [(A → B) → C]). simpl. destruct p. assert (x0 <= x2).
  apply l6. intros. assert (InT ((A → B) → C) [(A → B) → C]). apply InT_eq. apply l7 in H2. simpl in H2.
  inversion H1 ; subst. destruct C ; simpl in H2 ; simpl ; lia. inversion H4.
  apply less_than_lt. inversion H1 ; subst. 2: repeat rewrite length_max ; lia.
  exfalso. assert (weight_form ((A → B) → C) <= (weight_form (unBox_formula C))).
  assert (weight_form ((A → B) → C) <= x2). apply l7. apply InT_eq.
  assert (x2 <= (weight_form (unBox_formula C))). apply l6. intros.
  inversion H3 ; subst ; try lia. inversion H5 ; subst ; try lia. lia. destruct C ; simpl in H2 ; lia.
Qed.

Theorem ImpImpL_less_thanS : forall prem1 prem2 concl, ImpImpLRule [prem1;prem2] concl ->
                                                          ((prem1 << concl) * (prem2 << concl)).
Proof.
intros. unfold less_thanS. pose (ImpImpL_le_counter _ _ _ H). destruct p ; auto.
Qed.


(*------------------------------------------------------------------------------------------------------------------------------------------*)


(* BoxImpL rule *)

Lemma BoxImpL_le_counter : forall prem1 prem2 concl, BoxImpLRule [prem1; prem2] concl ->
                (less_than lt (seq_list_occ_weight prem1) (seq_list_occ_weight concl)) *
                (less_than lt (seq_list_occ_weight prem2) (seq_list_occ_weight concl)).
Proof.
intros. inversion H. subst. simpl. unfold seq_list_occ_weight ; simpl. repeat rewrite unBox_app_distrib ; simpl.
repeat rewrite <- app_assoc ; simpl. repeat rewrite unBox_app_distrib ; simpl. repeat rewrite <- app_assoc ; simpl.
destruct (max_weight_list (unBoxed_list (unBoxed_list Γ0) ++ unBox_formula B :: unBoxed_list (unBoxed_list Γ1) ++ [A; A])). simpl. destruct p.
destruct (max_weight_list (unBoxed_list Γ0 ++ Box A → B :: unBoxed_list Γ1 ++ [C])). simpl. destruct p.
destruct (max_weight_list (unBoxed_list Γ0 ++ unBox_formula B :: unBoxed_list Γ1 ++ [C])). simpl. destruct p.
assert (x <= x0).
{ apply l0. intros. apply InT_app_or in H0 ; destruct H0.
  apply unBoxed_list_weight_form with (l:=(unBoxed_list Γ0)) ; auto. intros.
  apply l1 ; apply InT_or_app ; auto.
  inversion i ; subst. assert (weight_form (Box A → B) <= x0). apply l1. apply InT_or_app ; right ; apply InT_eq.
  destruct B ; simpl in H0 ; simpl ; lia. apply InT_app_or in H1 ; destruct H1.
  apply unBoxed_list_weight_form with (l:=(unBoxed_list Γ1)) ; auto. intros.
  apply l1 ; apply InT_or_app ; right ; apply InT_cons ; apply InT_or_app ; auto.
  assert (weight_form (Box A → B) <= x0). apply l1. apply InT_or_app ; right ; apply InT_eq.
  simpl in H0. inversion i0 ; subst ; try lia. inversion H2 ; subst ; try lia. inversion H3. }
assert (x1 <= x0).
{ apply l4. intros. apply InT_app_or in H1. destruct H1. apply l1 ; apply InT_or_app ; auto.
  inversion i ; subst. assert (weight_form (Box A → B) <= x0). apply l1. apply InT_or_app ; right ; apply InT_eq.
  simpl in H0. destruct B ; simpl ; simpl in H1 ; lia. apply l1.  apply InT_or_app ; right ; apply InT_cons ; auto. }
split.
- destruct H0. 2: apply less_than_lt ; repeat rewrite length_max ; lia.
  apply less_than_eq.
  epose (list_occ_weight_list_swap (unBoxed_list Γ0 ++ Box A → B :: unBoxed_list Γ1) [C] [] x).
  simpl in e. repeat rewrite <- app_nil_end in e. repeat rewrite <- app_assoc in e. simpl in e. rewrite e. clear e.
  epose (list_occ_weight_list_swap (C :: unBoxed_list Γ0) [Box A → B] _ x).
  simpl in e. repeat rewrite <- app_assoc in e. simpl in e. rewrite e. clear e.
  epose (list_occ_weight_list_swap (unBoxed_list (unBoxed_list Γ0)) [unBox_formula B] _ x).
  simpl in e. repeat rewrite <- app_assoc in e. simpl in e. rewrite e. clear e.
  epose (list_occ_weight_list_swap (unBox_formula B :: (unBoxed_list (unBoxed_list Γ0)) ++ (unBoxed_list (unBoxed_list Γ1))) [A; A] [] x).
  simpl in e. repeat rewrite <- app_nil_end in e. repeat rewrite <- app_assoc in e. simpl in e. rewrite e. clear e.
  epose (list_occ_weight_list_split (A :: A :: [unBox_formula B]) [Box A → B] _ _). simpl in l5. apply l5. clear l5.
  + apply list_occ_weight_list_relevant.
    destruct (max_weight_list [A; A ; unBox_formula B]). simpl. destruct p. assert (x0 <= x).
    apply l6. intros. assert (weight_form (Box A → B) <= x). apply l1. apply InT_or_app ; right ; apply InT_eq.
    inversion H0 ; subst. simpl in H2 ; lia. inversion H4 ; subst ; simpl in H2 ; try lia. 
    inversion H5 ; subst. destruct B ; simpl ; simpl in H2 ; try lia. inversion H6.
    destruct (max_weight_list [Box A → B]). simpl. destruct p. assert (x2 <= x).
    apply l8. intros. apply l1. apply InT_or_app ; right. inversion H2 ; subst. apply InT_eq. inversion H4. lia.
    destruct (max_weight_list [A; A ; unBox_formula B]). simpl. destruct p.
    destruct (max_weight_list [Box A → B]). simpl. destruct p. assert (x0 <= x2).
    apply l6. intros. assert (weight_form (Box A → B) <= x2). apply l7. apply InT_eq.
    simpl in H2. inversion H0 ; subst. lia. inversion H4 ; subst. lia. inversion H5 ; subst.
    destruct B ; simpl ; simpl in H2 ; lia. inversion H6.
    apply less_than_lt. inversion H0 ; subst. 2: repeat rewrite length_max ; lia.
    exfalso. assert (weight_form (Box A → B) <= Nat.max (weight_form A) (weight_form (unBox_formula B))).
    assert (weight_form (Box A → B) <= x2). apply l7. apply InT_eq.
    assert (x2 <= Nat.max (weight_form A) (weight_form (unBox_formula B))). apply l6. intros.
    inversion H3 ; subst ; try lia. inversion H5 ; subst ; try lia. inversion H6 ; subst ; try lia. inversion H7.
    lia. destruct B ; simpl in H2 ; lia.
  + repeat rewrite <- unBox_app_distrib ; simpl.
     assert (proj1_sigT2 (max_weight_list (unBoxed_list (Γ0 ++ Γ1))) <= x).
     destruct (max_weight_list (unBoxed_list (Γ0 ++ Γ1))). simpl ; destruct p.
     apply l7. intros. apply l1. repeat rewrite unBox_app_distrib in H0. apply InT_app_or in H0.
     destruct H0. apply InT_or_app ; auto. apply InT_or_app ; right ; apply InT_cons ; apply InT_or_app ; auto.
     repeat rewrite unBox_app_distrib.
     pose (unBoxed_list_effective_or_not _ _ H0). destruct s.
    * repeat rewrite unBox_app_distrib in e. rewrite e.
      epose (list_occ_weight_list_headlist [] [C] _ x). simpl in l6. apply l6. clear l6. apply list_occ_weight_list_relevant.
      destruct (max_weight_list []). simpl. destruct p. assert (x0 <= x). apply l7. intros. inversion H2.
      destruct (max_weight_list [C]). simpl. destruct p. assert (x2 <= x).
      apply l9. intros. apply l1. apply InT_or_app ; right ; apply InT_cons ; apply InT_or_app. inversion H3 ; subst ; auto. lia.
      destruct (max_weight_list []). simpl. destruct p. apply less_than_lt.
      destruct (max_weight_list [C]). simpl. destruct p. assert (x0 <= x2).
      apply l7. intros. inversion H2. inversion H2 ; subst. 2: repeat rewrite length_max ; lia.
      exfalso. assert (weight_form C <= 0). assert (weight_form C <= x2). apply l8. apply InT_eq.
      assert (x2 <= 0). apply l7. intros. inversion H4 ; subst ; try lia. simpl ; lia. destruct C ; simpl in H3 ; lia.
   * epose (list_occ_weight_list_split [] [C] (unBoxed_list (unBoxed_list Γ0) ++ unBoxed_list (unBoxed_list Γ1))
     (unBoxed_list Γ0 ++ unBoxed_list Γ1) x). apply l7 ; auto.
     clear l7. apply list_occ_weight_list_relevant ; clear l5.
     destruct (max_weight_list []). simpl. destruct p. assert (x0 <= x). apply l7. intros. inversion H2.
     destruct (max_weight_list [C]). simpl. destruct p. assert (x2 <= x).
     apply l9. intros. apply l1. apply InT_or_app ; right ; apply InT_cons ; apply InT_or_app. inversion H3 ; subst ; auto. lia.
     destruct (max_weight_list []). simpl. destruct p. apply less_than_lt.
     destruct (max_weight_list [C]). simpl. destruct p. assert (x0 <= x2).
     apply l7. intros. inversion H2. inversion H2 ; subst. 2: repeat rewrite length_max ; lia.
     exfalso. assert (weight_form C <= 0). assert (weight_form C <= x2). apply l8. apply InT_eq.
     assert (x2 <= 0). apply l7. intros. inversion H4 ; subst ; try lia. simpl ; lia. destruct C ; simpl in H3 ; lia.
     repeat rewrite unBox_app_distrib in l6. auto.
- destruct H1. 2: apply less_than_lt ; repeat rewrite length_max ; lia.
  apply less_than_eq.
  epose (list_occ_weight_list_swap (unBoxed_list Γ0) [unBox_formula B] _ x1).
  simpl in e. repeat rewrite <- app_assoc in e. rewrite e. clear e.
  epose (list_occ_weight_list_swap (unBoxed_list Γ0) [Box A → B] _ x1).
  simpl in e. repeat rewrite <- app_assoc in e. rewrite e. clear e.
  epose (list_occ_weight_list_headlist [unBox_formula B] [Box A → B] _ x1).
  simpl in l5. apply l5. clear l5. apply list_occ_weight_list_relevant.
  destruct (max_weight_list [unBox_formula B]). simpl. destruct p. assert (x0 <= x1).
  apply l6. intros. inversion H1 ; subst. assert (weight_form (Box A → B) <= x1). apply l1.
  apply InT_or_app ; right ; apply InT_eq. destruct B ; simpl in H2 ; simpl ; lia. inversion H3.
  destruct (max_weight_list [Box A → B]). simpl. destruct p. assert (x2 <= x1).
  apply l8. intros. apply l1. apply InT_or_app ; right. inversion H2 ; subst. apply InT_eq.
  inversion H4. lia.
  destruct (max_weight_list [unBox_formula B]). simpl. destruct p.
  destruct (max_weight_list [Box A → B]). simpl. destruct p. assert (x0 <= x2).
  apply l6. intros. assert (InT (Box A → B) [Box A → B]). apply InT_eq. apply l7 in H2. simpl in H2.
  inversion H1 ; subst. destruct B ; simpl in H2 ; simpl ; lia. inversion H4.
  apply less_than_lt. inversion H1 ; subst. 2: repeat rewrite length_max ; lia.
  exfalso. assert (weight_form (Box A → B) <= (weight_form (unBox_formula B))).
  assert (weight_form (Box A → B) <= x2). apply l7. apply InT_eq.
  assert (x2 <= (weight_form (unBox_formula B))). apply l6. intros.
  inversion H3 ; subst ; try lia. inversion H5 ; subst ; try lia. lia. destruct B ; simpl in H2 ; lia.
Qed.

Theorem BoxImpL_less_thanS : forall prem1 prem2 concl, BoxImpLRule [prem1;prem2] concl ->
                                                          ((prem1 << concl) * (prem2 << concl)).
Proof.
intros. unfold less_thanS. pose (BoxImpL_le_counter _ _ _ H). destruct p ; auto.
Qed.





