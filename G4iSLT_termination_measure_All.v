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
Require Import G4iSLT_termination_measure_SLR.
Require Import G4iSLT_termination_measure_And.
Require Import G4iSLT_termination_measure_Or.
Require Import G4iSLT_termination_measure_ImpR.
Require Import G4iSLT_termination_measure_ImpL.
Require Import DLW_WO_list_nat.

(* All rules. *)



Theorem G4iSLT_less_thanS : forall prems concl, G4iSLT_rules prems concl ->
                                                    (forall prem, InT prem prems -> prem << concl).
Proof.
intros. inversion H ; subst.
1-2: inversion H1 ; subst ; inversion H0.
1-11: inversion H1 ; subst.
inversion H0 ; subst. apply AndR_less_thanS with (prem2:=(Γ, B)) ; auto.
inversion H3 ; subst. apply AndR_less_thanS with (prem1:=(Γ, A)) ; auto. inversion H4.
inversion H0 ; subst. apply AndL_less_thanS ; auto. inversion H3.
inversion H0 ; subst. apply OrR1_less_thanS ; auto. inversion H3.
inversion H0 ; subst. apply OrR2_less_thanS ; auto. inversion H3.
inversion H0 ; subst. apply OrL_less_thanS with (prem2:=(Γ0 ++ B :: Γ1, C)) ; auto.
inversion H3 ; subst. apply OrL_less_thanS with (prem1:=(Γ0 ++ A :: Γ1, C)) ; auto. inversion H4.
inversion H0 ; subst. apply ImpR_less_thanS ; auto. inversion H3.
inversion H0 ; subst. apply AtomImpL1_less_thanS ; auto. inversion H3.
inversion H0 ; subst. apply AtomImpL2_less_thanS ; auto. inversion H3.
inversion H0 ; subst. apply AndImpL_less_thanS ; auto. inversion H3.
inversion H0 ; subst. apply OrImpL_less_thanS ; auto. inversion H3.
inversion H0 ; subst. apply ImpImpL_less_thanS with (prem2:=(Γ0 ++ C :: Γ1, D)) ; auto.
inversion H3 ; subst. apply ImpImpL_less_thanS with (prem1:=(Γ0 ++ B → C :: Γ1, A → B)) ; auto. inversion H4.
1-2: inversion H1 ; subst.
inversion H0 ; subst. apply BoxImpL_less_thanS with (prem2:=(Γ0 ++ B :: Γ1, C)) ; auto.
inversion H3 ; subst. apply BoxImpL_less_thanS with (prem1:=(unBoxed_list Γ0 ++ B :: unBoxed_list Γ1 ++ [Box A], A)) ; auto. inversion H4.
inversion H0 ; subst. apply SLR_less_thanS ; auto. inversion H3.
Qed.