Require Import List.
Export ListNotations.
Require Import PeanoNat.
Require Import Lia.

Require Import general_export.

Require Import DiSL_calc.
Require Import DG4iSL_list_lems.
Require Import DG4iSL_dec.
Require Import DG4iSL_exch.
Require Import DG4iSL_wkn.
Require Import DG4iSL_inv_AndR_AndL.
Require Import DG4iSL_inv_OrL.
Require Import DG4iSL_inv_AtomImpL.
Require Import DG4iSL_inv_AndImpL.
Require Import DG4iSL_inv_OrImpL.
Require Import DG4iSL_inv_ImpImpL_R.
Require Import DG4iSL_inv_ImpImpL_L.
Require Import DG4iSL_inv_ImpR.
Require Import DG4iSL_inv_BoxImpL_R.
Require Import DG4iSL_ctr_prelims1.

Set Implicit Arguments.

(* Probably not useful as we do not have left invertibility for ImpImpL. *)

Lemma ImpImpL_app_ctr_L : forall s sc A ps1 ps2,
  (ctr_L A s sc) ->
  (ImpImpLRule [ps1;ps2] s) ->
  ((existsT2 psc1 psc2, (ImpImpLRule [psc1;psc2] sc) * (ctr_L A ps1 psc1) * (ctr_L A ps2 psc2))
  +
  (existsT2 B C D invps11 invps12 invpsc11 invps21 invps22 invpsc22,
                       (A = (B → C) → D) *
                       (ImpImpLRule [invps11;invps12] ps1) *
                       (ImpImpLRule [invps21;invps22] ps2) *
                       (@ctr_L (C → D) invps11 invpsc11) *
                       (@ctr_L D invps22 invpsc22) *
                       (ImpImpLRule [invpsc11;invpsc22] sc))).
Proof.
intros s sc A ps1 ps2 ctr RA. inversion RA. inversion ctr. subst.
inversion H. subst. apply app2_find_hole in H1. destruct H1.
repeat destruct s ; destruct p ; subst.
- inversion e0. subst. right. exists A0. exists B. exists C. exists (Γ2 ++ B → C :: Γ3 ++ B → C :: Γ4, A0 → B).
  exists (Γ2 ++ B → C :: Γ3 ++ C :: Γ4, A0 → B). exists (Γ2 ++ B → C :: Γ3 ++ Γ4, A0 → B).
  exists (Γ2 ++ C :: Γ3 ++ B → C :: Γ4, A0 → B). exists (Γ2 ++ C :: Γ3 ++ C :: Γ4, D). exists (Γ2 ++ C :: Γ3 ++ Γ4, D).
  repeat split ; auto.
  pose (ImpImpLRule_I A0 B  C (A0 → B) (Γ2 ++ B → C :: Γ3) Γ4). repeat rewrite <- app_assoc in i ; simpl in i ;  auto.
  pose (ImpImpLRule_I A0 B  C D (Γ2 ++ C :: Γ3) Γ4). repeat rewrite <- app_assoc in i ; simpl in i ;  auto.
- destruct x.
  * simpl in e0. inversion e0 ; subst. repeat rewrite <- app_assoc. simpl. right.
    exists A0. exists B. exists C. exists (Γ2 ++ B → C :: Γ3 ++ B → C :: Γ4, A0 → B).
    exists (Γ2 ++ B → C :: Γ3 ++ C :: Γ4, A0 → B). exists (Γ2 ++ B → C :: Γ3 ++ Γ4, A0 → B).
    exists (Γ2 ++ C :: Γ3 ++ B → C :: Γ4, A0 → B). exists (Γ2 ++ C :: Γ3 ++ C :: Γ4, D). exists (Γ2 ++ C :: Γ3 ++ Γ4, D).
    repeat split ; auto.
    pose (ImpImpLRule_I A0 B  C (A0 → B) (Γ2 ++ B → C :: Γ3) Γ4). repeat rewrite <- app_assoc in i ; simpl in i ;  auto.
    pose (ImpImpLRule_I A0 B  C D (Γ2 ++ C :: Γ3) Γ4). repeat rewrite <- app_assoc in i ; simpl in i ;  auto.
  * inversion e0. subst. apply app2_find_hole in H2. destruct H2. repeat destruct s ; destruct p ; subst.
    + inversion e1 ; subst. repeat rewrite <- app_assoc. simpl. right.
       exists A0. exists B. exists C. exists (Γ2 ++ B → C :: Γ3 ++ B → C :: Γ4, A0 → B).
       exists (Γ2 ++ C :: Γ3 ++ B → C :: Γ4, A0 → B). exists (Γ2 ++ B → C :: Γ3 ++ Γ4, A0 → B).
       exists (Γ2 ++ B → C :: Γ3 ++ C :: Γ4, A0 → B). exists (Γ2 ++ C :: Γ3 ++ C :: Γ4, D). exists (Γ2 ++ C :: Γ3 ++ Γ4, D).
       repeat split ; auto.
    + destruct x0.
      { simpl in e1. inversion e1. subst. right. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. simpl.
         exists A0. exists B. exists C. exists (Γ2 ++ B → C :: Γ3 ++ B → C :: Γ1, A0 → B).
         exists (Γ2 ++ C :: Γ3 ++ B → C :: Γ1, A0 → B). exists (Γ2 ++ B → C :: Γ3 ++ Γ1, A0 → B).
         exists (Γ2 ++ B → C :: Γ3 ++ C :: Γ1, A0 → B). exists (Γ2 ++ C :: Γ3 ++ C :: Γ1, D). exists (Γ2 ++ C :: Γ3 ++ Γ1, D).
         repeat split ; auto. }
      { simpl in e1. inversion e1. subst. left. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. simpl.
         exists (Γ2 ++ m0 :: Γ3 ++ x0 ++ B → C :: Γ1, A0 → B).  exists (Γ2 ++ m0 :: Γ3 ++ x0 ++ C :: Γ1, D). repeat split.
         pose (ImpImpLRule_I A0 B C D (Γ2 ++ m0 :: Γ3 ++ x0) Γ1). repeat rewrite <- app_assoc in i ; simpl in i ;
         repeat rewrite <- app_assoc in i ; simpl in i ; auto. }
    + destruct x0.
      { simpl in e1. inversion e1. subst. right. repeat rewrite <- app_assoc. simpl.
         exists A0. exists B. exists C. exists (Γ2 ++ B → C :: x ++ B → C :: Γ4, A0 → B).
         exists (Γ2 ++ C :: x ++ B → C :: Γ4, A0 → B). exists (Γ2 ++ B → C :: x ++ Γ4, A0 → B).
         exists (Γ2 ++ B → C :: x ++ C :: Γ4, A0 → B). exists (Γ2 ++ C :: x ++ C :: Γ4, D). exists (Γ2 ++ C :: x ++ Γ4, D). repeat split. }
      { simpl in e1. inversion e1. subst. left. repeat rewrite <- app_assoc. simpl.
         exists (Γ2 ++ m :: x ++ B → C :: x0 ++ Γ4, A0 → B).  exists (Γ2 ++ m :: x ++ C :: x0 ++ Γ4, D). repeat split.
         pose (ImpImpLRule_I A0 B C D (Γ2 ++ m :: x) (x0 ++ Γ4)). repeat rewrite <- app_assoc in i ; simpl in i ;  auto.
         pose (ctr_LI m Γ2 (x ++ B → C :: x0) Γ4 (A0 → B)). repeat rewrite <- app_assoc in c ; simpl in c ; auto.
         pose (ctr_LI m Γ2 (x ++ C :: x0) Γ4 D). repeat rewrite <- app_assoc in c ; simpl in c ; auto. }
- destruct x.
  * simpl in e0. inversion e0. subst. right. repeat rewrite <- app_assoc. simpl.
    exists A0. exists B. exists C. exists (Γ0 ++ B → C :: Γ3 ++ B → C :: Γ4, A0 → B).
    exists (Γ0 ++ B → C :: Γ3 ++ C :: Γ4, A0 → B). exists (Γ0 ++ B → C :: Γ3 ++ Γ4, A0 → B).
    exists (Γ0 ++ C :: Γ3 ++ B → C :: Γ4, A0 → B). exists (Γ0 ++ C :: Γ3 ++ C :: Γ4, D).
    exists (Γ0 ++ C :: Γ3 ++ Γ4, D). repeat split ; auto.
    pose (ImpImpLRule_I A0 B  C (A0 → B) (Γ0 ++ B → C :: Γ3) Γ4). repeat rewrite <- app_assoc in i ; simpl in i ;  auto.
    pose (ImpImpLRule_I A0 B  C D (Γ0 ++ C :: Γ3) Γ4). repeat rewrite <- app_assoc in i ; simpl in i ;  auto.
  * simpl in e0. inversion e0. subst. left. repeat rewrite <- app_assoc. simpl.
    exists (Γ0 ++ B → C :: x ++ A :: Γ3 ++ Γ4, A0 → B). exists (Γ0 ++ C :: x ++ A :: Γ3 ++ Γ4, D). repeat split.
    pose (ctr_LI A (Γ0 ++ B → C :: x) Γ3 Γ4 (A0 → B)). repeat rewrite <- app_assoc in c ; simpl in c ; auto.
    pose (ctr_LI A (Γ0 ++ C :: x) Γ3 Γ4 D). repeat rewrite <- app_assoc in c ; simpl in c ; auto.
Qed.

Lemma BoxImpL_app_ctr_L : forall s sc A ps1 ps2,
  (ctr_L A s sc) ->
  (BoxImpLRule [ps1;ps2] s) ->
  ((existsT2 psc2, (ctr_L A ps2 psc2) *
      (existsT2 psc1, (BoxImpLRule [psc1;psc2] sc) *  (ctr_L (unBox_formula A) ps1 psc1)))
  +
  (existsT2 B C invps11 invps12 invpsc12 invps21 invps22 invpsc22,
                       (A = (Box B) → C) *
                       (BoxImpLRule [invps11;invps12] ps1) *
                       (BoxImpLRule [invps21;invps22] ps2) *
                       (@ctr_L C invps12 invpsc12) *
                       (@ctr_L C invps22 invpsc22) *
                       (BoxImpLRule [invpsc12;invpsc22] sc))).
Proof.
intros s sc A ps1 ps2 ctr RA. inversion RA. inversion ctr. subst. inversion H. subst. apply app2_find_hole in H1. destruct H1.
repeat destruct s ; destruct p ; subst.
- inversion e0. subst. right. exists A0. exists B.
  exists (unBoxed_list (unBoxed_list Γ2) ++ unBox_formula B :: (unBoxed_list (unBoxed_list Γ3) ++ B :: unBoxed_list (unBoxed_list Γ4)) ++ [A0;Box A0], A0).
  exists (unBoxed_list Γ2 ++ B :: (unBoxed_list Γ3 ++ B :: unBoxed_list Γ4) ++ [Box A0], A0). exists(unBoxed_list Γ2 ++ B :: unBoxed_list Γ3 ++ unBoxed_list Γ4 ++ [Box A0], A0).
  exists (unBoxed_list Γ2 ++ unBox_formula B :: unBoxed_list Γ3 ++ B :: unBoxed_list Γ4 ++ [Box A0], A0). exists (Γ2 ++ B :: Γ3 ++ B :: Γ4, C). exists (Γ2 ++ B :: Γ3 ++ Γ4, C).
  repeat rewrite unBox_app_distrib ; simpl ; repeat rewrite <- app_assoc ; simpl ; repeat split ; auto.
  pose (@BoxImpLRule_I A0 B A0 ((unBoxed_list Γ2) ++ B :: (unBoxed_list Γ3)) ((unBoxed_list Γ4) ++ [Box A0])).
  repeat rewrite unBox_app_distrib in b ; simpl in b ; repeat rewrite <- app_assoc in b ; simpl in b ; apply b.
  pose (@BoxImpLRule_I A0 B C (Γ2 ++ B :: Γ3) Γ4).
  repeat rewrite unBox_app_distrib in b ; simpl in b ; repeat rewrite <- app_assoc in b ; simpl in b ; apply b.
  pose (@BoxImpLRule_I A0 B C Γ2 (Γ3 ++ Γ4)).
  repeat rewrite unBox_app_distrib in b ; simpl in b ; repeat rewrite <- app_assoc in b ; simpl in b ; apply b.
- destruct x.
  * simpl in e0. inversion e0 ; subst. repeat rewrite <- app_assoc. simpl. right. exists A0. exists B.
    exists (unBoxed_list (unBoxed_list Γ2) ++ unBox_formula B :: (unBoxed_list (unBoxed_list Γ3) ++ B :: unBoxed_list (unBoxed_list Γ4)) ++ [A0;Box A0], A0).
    exists (unBoxed_list Γ2 ++ B :: (unBoxed_list Γ3 ++ B :: unBoxed_list Γ4) ++ [Box A0], A0). exists(unBoxed_list Γ2 ++ B :: unBoxed_list Γ3 ++ unBoxed_list Γ4 ++ [Box A0], A0).
    exists (unBoxed_list Γ2 ++ unBox_formula B :: unBoxed_list Γ3 ++ B :: unBoxed_list Γ4 ++ [Box A0], A0). exists (Γ2 ++ B :: Γ3 ++ B :: Γ4, C). exists (Γ2 ++ B :: Γ3 ++ Γ4, C).
    repeat rewrite unBox_app_distrib ; simpl ; repeat rewrite <- app_assoc ; simpl ; repeat split ; auto.
    pose (@BoxImpLRule_I A0 B A0 ((unBoxed_list Γ2) ++ B :: (unBoxed_list Γ3)) ((unBoxed_list Γ4) ++ [Box A0])).
    repeat rewrite unBox_app_distrib in b ; simpl in b ; repeat rewrite <- app_assoc in b ; simpl in b ; apply b.
    pose (@BoxImpLRule_I A0 B C (Γ2 ++ B :: Γ3) Γ4).
    repeat rewrite unBox_app_distrib in b ; simpl in b ; repeat rewrite <- app_assoc in b ; simpl in b ; apply b.
    pose (@BoxImpLRule_I A0 B C Γ2 (Γ3 ++ Γ4)).
    repeat rewrite unBox_app_distrib in b ; simpl in b ; repeat rewrite <- app_assoc in b ; simpl in b ; apply b.
  * inversion e0. subst. apply app2_find_hole in H2. destruct H2. repeat destruct s ; destruct p ; subst.
    + inversion e1 ; subst. repeat rewrite <- app_assoc. simpl. right. exists A0. exists B.
       exists (unBoxed_list (unBoxed_list Γ2) ++ B :: unBoxed_list (unBoxed_list Γ3) ++ unBox_formula B :: unBoxed_list (unBoxed_list Γ4) ++ [A0;Box A0], A0).
       exists (unBoxed_list Γ2 ++ B :: unBoxed_list Γ3 ++ B :: unBoxed_list Γ4 ++ [Box A0], A0).
       exists (unBoxed_list Γ2 ++ B :: unBoxed_list Γ3 ++ unBoxed_list Γ4 ++ [Box A0], A0).
       exists (unBoxed_list Γ2 ++ B :: unBoxed_list Γ3 ++ unBox_formula B :: unBoxed_list Γ4 ++ [Box A0], A0).
       exists (Γ2 ++ B :: Γ3 ++ B :: Γ4, C). exists (Γ2 ++ B :: Γ3 ++ Γ4, C).
       repeat rewrite unBox_app_distrib ; simpl ; repeat rewrite <- app_assoc ; simpl ; repeat split ; auto.
       pose (@BoxImpLRule_I A0 B A0 (unBoxed_list Γ2) ((unBoxed_list Γ3) ++ B :: (unBoxed_list Γ4) ++ [Box A0])).
       repeat rewrite unBox_app_distrib in b ; simpl in b ; repeat rewrite <- app_assoc in b ; simpl in b ; repeat rewrite unBox_app_distrib in b ;
       simpl in b ; repeat rewrite <- app_assoc in b ; apply b.
       pose (@BoxImpLRule_I A0 B C Γ2 (Γ3 ++ B :: Γ4)).
       repeat rewrite unBox_app_distrib in b ; simpl in b ; repeat rewrite <- app_assoc in b ; simpl in b ; repeat rewrite unBox_app_distrib in b ;
       simpl in b ; repeat rewrite <- app_assoc in b ; apply b.
       pose (@BoxImpLRule_I A0 B C Γ2 (Γ3 ++ Γ4)).
       repeat rewrite unBox_app_distrib in b ; simpl in b ; repeat rewrite <- app_assoc in b ; simpl in b ; repeat rewrite unBox_app_distrib in b ;
       simpl in b ; repeat rewrite <- app_assoc in b ; apply b.
    + destruct x0.
      { simpl in e1. inversion e1. subst. right. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. simpl. rewrite <- app_nil_end.
         exists A0. exists B. exists (unBoxed_list (unBoxed_list Γ2) ++ B :: unBoxed_list (unBoxed_list Γ3) ++ unBox_formula B :: unBoxed_list (unBoxed_list Γ1) ++ [A0;Box A0], A0).
         exists (unBoxed_list Γ2 ++ B :: unBoxed_list Γ3 ++ B :: unBoxed_list Γ1 ++ [Box A0], A0). exists (unBoxed_list Γ2 ++ B :: unBoxed_list Γ3 ++ unBoxed_list Γ1 ++ [Box A0], A0).
         exists (unBoxed_list Γ2 ++ B :: unBoxed_list Γ3 ++ unBox_formula B :: unBoxed_list Γ1 ++ [Box A0], A0).
         exists (Γ2 ++ B :: Γ3 ++ B :: Γ1, C). exists (Γ2 ++ B :: Γ3 ++ Γ1, C).
         repeat rewrite unBox_app_distrib ; simpl ; repeat rewrite <- app_assoc ; simpl ; repeat split ; auto.
         pose (@BoxImpLRule_I A0 B A0 (unBoxed_list Γ2) (unBoxed_list Γ3 ++ B :: unBoxed_list Γ1 ++ [Box A0])).
         repeat rewrite unBox_app_distrib in b ; simpl in b ; repeat rewrite <- app_assoc in b ; simpl in b ; repeat rewrite unBox_app_distrib in b ;
         simpl in b ; repeat rewrite <- app_assoc in b ; apply b.
         pose (@BoxImpLRule_I A0 B C Γ2 (Γ3 ++ B :: Γ1)).
         repeat rewrite unBox_app_distrib in b ; simpl in b ; repeat rewrite <- app_assoc in b ; simpl in b ; repeat rewrite unBox_app_distrib in b ;
         simpl in b ; repeat rewrite <- app_assoc in b ; apply b.
         pose (@BoxImpLRule_I A0 B C Γ2 (Γ3 ++ Γ1)).
         repeat rewrite unBox_app_distrib in b ; simpl in b ; repeat rewrite <- app_assoc in b ; simpl in b ; repeat rewrite unBox_app_distrib in b ;
         simpl in b ; repeat rewrite <- app_assoc in b ; apply b. }
      { simpl in e1. inversion e1. subst. left. exists (Γ2 ++ m0 :: Γ3 ++ x0 ++ B :: Γ1, C). split.
        repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; simpl ; apply ctr_LI.
        exists (unBoxed_list Γ2 ++ unBox_formula m0 :: unBoxed_list Γ3 ++ unBoxed_list x0 ++ B :: unBoxed_list Γ1 ++ [Box A0], A0). repeat split ; auto.
        pose (@BoxImpLRule_I A0 B C (Γ2 ++ m0 :: Γ3 ++ x0) Γ1).
        repeat rewrite unBox_app_distrib in b ; simpl in b ; repeat rewrite <- app_assoc in b ; simpl in b ; repeat rewrite unBox_app_distrib in b ;
        simpl in b ; repeat rewrite <- app_assoc in b ; apply b.
        repeat rewrite unBox_app_distrib ; simpl ; repeat rewrite unBox_app_distrib ; simpl ; repeat rewrite <- app_assoc ; simpl ;
        repeat rewrite <- app_assoc ; simpl. pose (ctr_LI (unBox_formula m0) (unBoxed_list Γ2) (unBoxed_list Γ3) (unBoxed_list x0 ++ B :: unBoxed_list Γ1 ++ [Box A0]) A0).
        auto. }
    + destruct x0.
      { simpl in e1. inversion e1. subst. right. repeat rewrite <- app_assoc. simpl. exists A0. exists B.
         exists (unBoxed_list (unBoxed_list Γ2) ++  B :: unBoxed_list (unBoxed_list x) ++ unBox_formula B :: unBoxed_list (unBoxed_list Γ4) ++ [A0;Box A0], A0).
         exists ((unBoxed_list Γ2 ++ B :: unBoxed_list x) ++ B :: unBoxed_list Γ4 ++ [Box A0], A0).
         exists ((unBoxed_list Γ2 ++ B :: unBoxed_list x) ++ unBoxed_list Γ4 ++ [Box A0], A0).
         exists (unBoxed_list Γ2 ++ B :: unBoxed_list x ++ unBox_formula B :: unBoxed_list Γ4 ++ [Box A0], A0).
         exists (Γ2 ++ B :: x ++ B :: Γ4, C). exists (Γ2 ++ B :: x ++ Γ4, C).
         repeat rewrite unBox_app_distrib ; simpl ; repeat rewrite <- app_assoc ; simpl ; repeat split ; auto.
         pose (@BoxImpLRule_I A0 B A0 (unBoxed_list Γ2) ((unBoxed_list x) ++ B :: (unBoxed_list Γ4) ++ [Box A0])).
         repeat rewrite unBox_app_distrib in b ; simpl in b ; repeat rewrite <- app_assoc in b ; simpl in b ; repeat rewrite unBox_app_distrib in b ;
         simpl in b ; repeat rewrite <- app_assoc in b ; apply b.
         pose (@BoxImpLRule_I A0 B C Γ2 (x ++ B :: Γ4)).
         repeat rewrite unBox_app_distrib in b ; simpl in b ; repeat rewrite <- app_assoc in b ; simpl in b ; repeat rewrite unBox_app_distrib in b ;
         simpl in b ; repeat rewrite <- app_assoc in b ; apply b.
         pose (@BoxImpLRule_I A0 B C Γ2 (x ++ Γ4)).
         repeat rewrite unBox_app_distrib in b ; simpl in b ; repeat rewrite <- app_assoc in b ; simpl in b ; repeat rewrite unBox_app_distrib in b ;
         simpl in b ; repeat rewrite <- app_assoc in b ; apply b. }
      { simpl in e1. inversion e1. subst. left. exists (Γ2 ++ m :: x ++ B :: x0 ++ Γ4, C). split.
        pose (ctr_LI m Γ2 (x ++ B :: x0) Γ4 C). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in c ; simpl in c ; auto.
        exists (unBoxed_list Γ2 ++ unBox_formula m :: unBoxed_list x ++ B :: unBoxed_list x0 ++ unBoxed_list Γ4 ++ [Box A0], A0). repeat split ; auto.
        pose (@BoxImpLRule_I A0 B C (Γ2 ++ m :: x) (x0 ++ Γ4)).
        repeat rewrite unBox_app_distrib in b ; simpl in b ; repeat rewrite <- app_assoc in b ; simpl in b ; repeat rewrite unBox_app_distrib in b ;
        simpl in b ; repeat rewrite <- app_assoc in b ; repeat rewrite <- app_assoc ; apply b.
        repeat rewrite unBox_app_distrib ; simpl ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite unBox_app_distrib ;
        simpl ; repeat rewrite <- app_assoc.
        pose (ctr_LI (unBox_formula m) (unBoxed_list Γ2) (unBoxed_list x ++ B :: unBoxed_list x0) (unBoxed_list Γ4 ++ [Box A0]) A0).
        repeat rewrite <- app_assoc in c ; simpl in c ; auto. }
- destruct x.
  * simpl in e0. inversion e0 ; subst. repeat rewrite <- app_assoc. simpl. right. exists A0. exists B.
    exists (unBoxed_list (unBoxed_list Γ0) ++ unBox_formula B :: unBoxed_list (unBoxed_list Γ3) ++ B :: unBoxed_list (unBoxed_list Γ4) ++ [A0;Box A0], A0).
    exists (unBoxed_list Γ0 ++ B :: unBoxed_list Γ3 ++ B :: unBoxed_list Γ4 ++ [Box A0], A0).
    exists (unBoxed_list Γ0 ++ B :: unBoxed_list Γ3 ++ unBoxed_list Γ4 ++ [Box A0], A0).
    exists (unBoxed_list Γ0 ++ unBox_formula B :: unBoxed_list Γ3 ++ B :: unBoxed_list Γ4 ++ [Box A0], A0).
    exists (Γ0 ++ B :: Γ3 ++ B :: Γ4, C). exists (Γ0 ++ B :: Γ3 ++ Γ4, C).
    repeat rewrite unBox_app_distrib ; simpl ; repeat rewrite <- app_assoc ; simpl ; repeat split ; auto.
    pose (@BoxImpLRule_I A0 B A0 (unBoxed_list Γ0 ++ B :: unBoxed_list Γ3) (unBoxed_list Γ4 ++ [Box A0])).
    repeat rewrite unBox_app_distrib in b ; simpl in b ; repeat rewrite <- app_assoc in b ; simpl in b ; repeat rewrite unBox_app_distrib in b ;
    simpl in b ; repeat rewrite <- app_assoc in b ; repeat rewrite <- app_assoc ; apply b.
    pose (@BoxImpLRule_I A0 B C (Γ0 ++ B :: Γ3) Γ4).
    repeat rewrite unBox_app_distrib in b ; simpl in b ; repeat rewrite <- app_assoc in b ; simpl in b ; repeat rewrite unBox_app_distrib in b ;
    simpl in b ; repeat rewrite <- app_assoc in b ; repeat rewrite <- app_assoc ; apply b.
    pose (@BoxImpLRule_I A0 B C Γ0 (Γ3 ++ Γ4)).
    repeat rewrite unBox_app_distrib in b ; simpl in b ; repeat rewrite <- app_assoc in b ; simpl in b ; repeat rewrite unBox_app_distrib in b ;
    simpl in b ; repeat rewrite <- app_assoc in b ; repeat rewrite <- app_assoc ; apply b.
  * inversion e0. subst. left. exists (Γ0 ++ B :: x ++ A :: Γ3 ++ Γ4, C). repeat split ; auto.
    pose (ctr_LI A (Γ0 ++ B :: x) Γ3 Γ4 C). repeat rewrite <- app_assoc in c ; simpl in c ; auto.
    exists (unBoxed_list Γ0 ++ B :: unBoxed_list x ++ unBox_formula A :: unBoxed_list Γ3 ++ unBoxed_list Γ4 ++ [Box A0], A0).
    repeat rewrite unBox_app_distrib ; simpl ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite unBox_app_distrib ; simpl ;
    repeat rewrite <- app_assoc ; simpl ; repeat rewrite unBox_app_distrib ; simpl ; repeat split ; auto.
    pose (@BoxImpLRule_I A0 B C Γ0 (x ++ A :: Γ3 ++ Γ4)).
    repeat rewrite unBox_app_distrib in b ; simpl in b ; repeat rewrite <- app_assoc in b ; simpl in b ; repeat rewrite unBox_app_distrib in b ;
    simpl in b ; repeat rewrite <- app_assoc in b ; repeat rewrite <- app_assoc ; apply b.
    pose (ctr_LI (unBox_formula A) (unBoxed_list Γ0 ++ B :: unBoxed_list x) (unBoxed_list Γ3) (unBoxed_list Γ4 ++ [Box A0]) A0).
    repeat rewrite <- app_assoc in c ; simpl in c ; auto.
Qed.





