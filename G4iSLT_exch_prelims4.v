Require Import List.
Export ListNotations.
Require Import PeanoNat.
Require Import Lia.

Require Import general_export.

Require Import G4iSLT_calc.
Require Import G4iSLT_list_lems.
Require Import G4iSLT_exch_prelims1.

Lemma BoxImpL_app_list_exchL : forall s se ps1 ps2,
  (@list_exch_L s se) ->
  (BoxImpLRule [ps1;ps2] s) ->
  (existsT2 pse1 pse2,
    (BoxImpLRule [pse1;pse2] se) *
    (@list_exch_L ps1 pse1)  *
    (@list_exch_L ps2 pse2)).
Proof.
intros s se ps1 ps2 exch RA. inversion RA. subst. inversion exch. subst. symmetry in H0.
apply app2_find_hole in H0. destruct H0. repeat destruct s ; destruct p ; subst.
- destruct Γ3.
  + simpl in e0. subst. simpl. destruct Γ4.
      * simpl in e0. simpl. destruct Γ5.
        { simpl in e0. subst. simpl. exists (unBoxed_list Γ0 ++ B :: unBoxed_list Γ1 ++ [Box A], A). exists (Γ0 ++ B :: Γ1, C). repeat split ; try apply list_exch_L_id ; auto. }
        { simpl in e0. inversion e0. subst. simpl. exists (unBoxed_list Γ0 ++ B :: unBoxed_list (Γ5 ++ Γ6) ++ [Box A], A). exists (Γ0 ++ B :: Γ5 ++ Γ6, C). repeat split ; try apply list_exch_L_id ; auto. }
      * simpl in e0. inversion e0. subst.
        exists (unBoxed_list (Γ0 ++ Γ5) ++ B :: unBoxed_list (Γ4 ++ Γ6) ++ [Box A], A). exists (Γ0 ++ Γ5 ++ B :: Γ4 ++ Γ6, C). repeat split.
        pose (@BoxImpLRule_I A B C (Γ0 ++ Γ5) (Γ4 ++ Γ6)). repeat rewrite <- app_assoc in b ; simpl in b ; apply b.
        pose (list_exch_LI (unBoxed_list Γ0) [] (B :: (unBoxed_list Γ4)) (unBoxed_list Γ5) ((unBoxed_list Γ6) ++ [Box A]) A).
        repeat rewrite unBox_app_distrib in l ; repeat rewrite unBox_app_distrib ; simpl ; simpl in l ; repeat rewrite <- app_assoc in l ;  simpl ; repeat rewrite <- app_assoc ;  auto.
        pose (list_exch_LI Γ0 [] (B :: Γ4) Γ5 Γ6 C). simpl in l ; repeat rewrite <- app_assoc in l ;  simpl ; repeat rewrite <- app_assoc ;  auto.
  + simpl in e0. inversion e0. subst.
      exists (unBoxed_list Γ0 ++ unBoxed_list Γ5 ++ unBoxed_list Γ4 ++ B :: unBoxed_list Γ3 ++ unBoxed_list Γ6 ++ [Box A], A). exists (Γ0 ++ Γ5 ++ Γ4 ++ B :: Γ3 ++ Γ6, C). repeat split.
      pose (@BoxImpLRule_I A B C (Γ0 ++ Γ5 ++ Γ4) (Γ3 ++ Γ6)). repeat rewrite unBox_app_distrib in b ; simpl in b ; repeat repeat rewrite <- app_assoc in b ; simpl in b ; apply b.
      pose (list_exch_LI (unBoxed_list Γ0) (B :: unBoxed_list Γ3) (unBoxed_list Γ4) (unBoxed_list Γ5) (unBoxed_list Γ6 ++ [Box A]) A).
      repeat rewrite unBox_app_distrib in l ; repeat rewrite unBox_app_distrib ; simpl ; simpl in l ; repeat rewrite <- app_assoc in l ;  simpl ; repeat rewrite <- app_assoc ;  auto.
      pose (list_exch_LI Γ0 (B :: Γ3) Γ4 Γ5 Γ6 C). simpl in l ; repeat rewrite <- app_assoc in l ;  simpl ; repeat rewrite <- app_assoc ;  auto.
- destruct x.
  + simpl in e0. subst. simpl. destruct Γ3.
      * simpl in e0. simpl. destruct Γ4.
        { simpl in e0. subst. simpl. rewrite <- e0. repeat rewrite <- app_assoc ; simpl.  exists (unBoxed_list Γ0 ++ B :: unBoxed_list Γ1 ++ [Box A], A).
           exists (Γ0 ++ B :: Γ1, C). repeat split ; try apply list_exch_L_id ; try apply univ_gen_mod_combine ; auto. }
        { simpl in e0. inversion e0. subst. simpl. rewrite <- app_assoc ; simpl.
          exists (unBoxed_list Γ0 ++ unBoxed_list Γ5 ++ B :: unBoxed_list Γ4 ++ unBoxed_list Γ6 ++ [Box A], A). exists (Γ0 ++ Γ5 ++ B :: Γ4 ++ Γ6, C). repeat split.
          pose (@BoxImpLRule_I A B C (Γ0 ++ Γ5) (Γ4 ++ Γ6)).  repeat rewrite unBox_app_distrib in b ; repeat rewrite <- app_assoc in b ; simpl in b ; apply b.
          pose (list_exch_LI (unBoxed_list Γ0) [] (B :: (unBoxed_list Γ4)) (unBoxed_list Γ5) ((unBoxed_list Γ6) ++ [Box A]) A).
          repeat rewrite unBox_app_distrib in l ; repeat rewrite unBox_app_distrib ; simpl ; simpl in l ; repeat rewrite <- app_assoc in l ;  simpl ; repeat rewrite <- app_assoc ;  auto.
          pose (list_exch_LI Γ0 [] (B :: Γ4) Γ5 Γ6 C). simpl in l ; repeat rewrite <- app_assoc in l ;  simpl ; repeat rewrite <- app_assoc ;  auto. }
      * simpl in e0. inversion e0. subst. rewrite <- app_assoc ; simpl.
        exists (unBoxed_list Γ0 ++ unBoxed_list Γ5 ++ unBoxed_list Γ4 ++ B :: unBoxed_list Γ3 ++ unBoxed_list Γ6 ++ [Box A], A). exists (Γ0 ++ Γ5 ++ Γ4 ++ B :: Γ3 ++ Γ6, C). repeat split.
        pose (@BoxImpLRule_I A B C (Γ0 ++ Γ5 ++ Γ4) (Γ3 ++ Γ6)). repeat rewrite unBox_app_distrib in b ; repeat rewrite <- app_assoc in b ; simpl in b ; apply b.
        pose (list_exch_LI (unBoxed_list Γ0) (B :: unBoxed_list Γ3) (unBoxed_list Γ4) (unBoxed_list Γ5) (unBoxed_list Γ6 ++ [Box A]) A).
        repeat rewrite unBox_app_distrib in l ; repeat rewrite unBox_app_distrib ; simpl ; simpl in l ; repeat rewrite <- app_assoc in l ;  simpl ; repeat rewrite <- app_assoc ;  auto.
        pose (list_exch_LI Γ0 (B :: Γ3) Γ4 Γ5 Γ6 C). simpl in l ; repeat rewrite <- app_assoc in l ;  simpl ; repeat rewrite <- app_assoc ;  auto.
  + simpl in e0. inversion e0. subst.
      exists (unBoxed_list Γ0 ++ B :: unBoxed_list x ++ unBoxed_list Γ5 ++ unBoxed_list Γ4 ++ unBoxed_list Γ3 ++ unBoxed_list Γ6 ++ [Box A], A). exists ((Γ0 ++ B :: x) ++ Γ5 ++ Γ4 ++ Γ3 ++ Γ6, C). repeat split.
      pose (@BoxImpLRule_I A B C Γ0 (x ++ Γ5 ++ Γ4 ++ Γ3 ++ Γ6)). repeat rewrite unBox_app_distrib in b ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in b ; simpl in b ; apply b.
      pose (list_exch_LI (unBoxed_list Γ0 ++ B :: unBoxed_list x) (unBoxed_list Γ3) (unBoxed_list Γ4) (unBoxed_list Γ5) (unBoxed_list Γ6 ++ [Box A]) A).
      repeat rewrite unBox_app_distrib in l ; repeat rewrite unBox_app_distrib ; simpl ; simpl in l ; repeat rewrite <- app_assoc in l ;  simpl ; repeat rewrite <- app_assoc ;  auto.
      pose (list_exch_LI (Γ0 ++ B :: x) Γ3 Γ4 Γ5 Γ6 C). simpl in l ; repeat rewrite <- app_assoc in l ;  simpl ; repeat rewrite <- app_assoc ;  auto.
- apply app2_find_hole in e0. destruct e0. repeat destruct s ; destruct p ; subst.
  + simpl in e0. subst. simpl. destruct Γ4.
      * simpl in e0. simpl. destruct Γ5.
        { simpl in e0. subst. simpl. exists (unBoxed_list (Γ2 ++ Γ3) ++ B :: unBoxed_list Γ1 ++ [Box A], A). exists ((Γ2 ++ Γ3) ++ B :: Γ1, C).  repeat split ; try apply list_exch_L_id. rewrite app_assoc.
           apply BoxImpLRule_I. }
        { simpl in e0. inversion e0. subst. simpl. repeat rewrite unBox_app_distrib ; repeat rewrite <- app_assoc.
           exists (unBoxed_list Γ2 ++ B :: unBoxed_list Γ5 ++ unBoxed_list Γ3 ++ unBoxed_list Γ6 ++ [Box A], A). exists (Γ2 ++ B :: Γ5 ++ Γ3 ++ Γ6, C). repeat split.
           pose (@BoxImpLRule_I A B C Γ2 (Γ5 ++ Γ3 ++ Γ6)). repeat rewrite unBox_app_distrib in b ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in b ; simpl in b ; apply b.
           pose (list_exch_LI (unBoxed_list Γ2) (unBoxed_list Γ3) [] (B :: unBoxed_list Γ5) (unBoxed_list Γ6 ++ [Box A]) A). simpl in l ; repeat rewrite <- app_assoc in l ;  simpl ; repeat rewrite <- app_assoc ;  auto.
           pose (list_exch_LI Γ2 Γ3 [] (B :: Γ5) Γ6 C). simpl in l ; repeat rewrite <- app_assoc in l ;  simpl ; repeat rewrite <- app_assoc ;  auto. }
      * simpl in e0. inversion e0. subst.
         exists (unBoxed_list Γ2 ++ unBoxed_list Γ5 ++ B :: unBoxed_list Γ4 ++ unBoxed_list Γ3 ++ unBoxed_list Γ6 ++ [Box A], A). exists (Γ2 ++ Γ5 ++ B :: Γ4 ++ Γ3 ++ Γ6, C). simpl ; repeat split.
         pose (@BoxImpLRule_I A B C (Γ2 ++ Γ5) (Γ4 ++ Γ3 ++ Γ6)). repeat rewrite unBox_app_distrib in b ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in b ; simpl in b ; apply b.
         pose (list_exch_LI (unBoxed_list Γ2) (unBoxed_list Γ3) (B :: (unBoxed_list Γ4)) (unBoxed_list Γ5) ((unBoxed_list Γ6) ++ [Box A]) A).
         repeat rewrite unBox_app_distrib in l ; repeat rewrite unBox_app_distrib ; simpl ; simpl in l ; repeat rewrite <- app_assoc in l ;  simpl ; repeat rewrite <- app_assoc ;  auto.
         pose (list_exch_LI Γ2 Γ3 (B :: Γ4) Γ5 Γ6 C). simpl in l ; repeat rewrite <- app_assoc in l ;  simpl ; repeat rewrite <- app_assoc ;  auto.
  + apply app2_find_hole in e0. destruct e0. repeat destruct s ; destruct p ; subst.
      * simpl in e0. simpl. destruct Γ5.
        { simpl in e0. subst. simpl.
           exists (unBoxed_list Γ2 ++ unBoxed_list Γ4 ++ unBoxed_list Γ3 ++ B :: unBoxed_list Γ1 ++ [Box A], A). exists (Γ2 ++ Γ4 ++ Γ3 ++ B :: Γ1, C). simpl ; repeat split.
           pose (@BoxImpLRule_I A B C (Γ2 ++ Γ4 ++ Γ3) Γ1). repeat rewrite unBox_app_distrib in b ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in b ; simpl in b ; apply b.
           pose (list_exch_LI (unBoxed_list Γ2) (unBoxed_list Γ3) [] (unBoxed_list Γ4) (B :: unBoxed_list Γ1 ++ [Box A]) A).
           repeat rewrite unBox_app_distrib in l ; repeat rewrite unBox_app_distrib ; simpl ; simpl in l ; repeat rewrite <- app_assoc in l ;  simpl ; repeat rewrite <- app_assoc ;  auto.
           pose (list_exch_LI Γ2 Γ3 [] Γ4 (B :: Γ1) C). simpl in l ; repeat rewrite <- app_assoc in l ;  simpl ; repeat rewrite <- app_assoc ;  auto. }
        { simpl in e0. inversion e0. subst. simpl.
           exists (unBoxed_list Γ2 ++ B :: unBoxed_list Γ5 ++ unBoxed_list Γ4 ++ unBoxed_list Γ3 ++ unBoxed_list Γ6 ++ [Box A], A). exists (Γ2 ++ B :: Γ5 ++ Γ4 ++ Γ3 ++ Γ6, C). simpl ; repeat split.
           pose (@BoxImpLRule_I A B C Γ2 (Γ5 ++ Γ4 ++ Γ3 ++ Γ6)). repeat rewrite unBox_app_distrib in b ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in b ; simpl in b ; apply b.
           pose (list_exch_LI (unBoxed_list Γ2) (unBoxed_list Γ3) (unBoxed_list Γ4) (B :: (unBoxed_list Γ5)) ((unBoxed_list Γ6) ++ [Box A]) A).
           repeat rewrite unBox_app_distrib in l ; repeat rewrite unBox_app_distrib ; simpl ; simpl in l ; repeat rewrite <- app_assoc in l ;  simpl ; repeat rewrite <- app_assoc ;  auto.
           pose (list_exch_LI Γ2 Γ3 Γ4 (B :: Γ5) Γ6 C). simpl in l ; repeat rewrite <- app_assoc in l ;  simpl ; repeat rewrite <- app_assoc ;  auto. }
      * apply app2_find_hole in e0. destruct e0. repeat destruct s ; destruct p ; subst.
        {  repeat rewrite <- app_assoc.
           exists (unBoxed_list Γ2 ++ unBoxed_list Γ5 ++ unBoxed_list Γ4 ++ unBoxed_list Γ3 ++ B :: unBoxed_list Γ1 ++ [Box A], A). exists (Γ2 ++ Γ5 ++ Γ4 ++ Γ3 ++ B :: Γ1, C). simpl ; repeat split.
           pose (@BoxImpLRule_I A B C (Γ2 ++ Γ5 ++ Γ4 ++ Γ3) Γ1). repeat rewrite unBox_app_distrib in b ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in b ; simpl in b ; apply b.
           pose (list_exch_LI (unBoxed_list Γ2) (unBoxed_list Γ3) (unBoxed_list Γ4) (unBoxed_list Γ5) (B :: unBoxed_list Γ1 ++ [Box A]) A). repeat rewrite unBox_app_distrib ; simpl in l ; repeat rewrite <- app_assoc in l ;  simpl ; repeat rewrite <- app_assoc ;  auto. }
        {  repeat rewrite <- app_assoc.
           exists (unBoxed_list Γ2 ++ unBoxed_list Γ5 ++ unBoxed_list Γ4 ++ unBoxed_list Γ3 ++ unBoxed_list x0 ++ B :: unBoxed_list Γ1 ++ [Box A], A). exists (Γ2 ++ Γ5 ++ Γ4 ++ Γ3 ++ x0 ++ B :: Γ1, C). simpl ; repeat split.
           pose (@BoxImpLRule_I A B C (Γ2 ++ Γ5 ++ Γ4 ++ Γ3 ++ x0) Γ1). repeat rewrite unBox_app_distrib in b ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in b ; simpl in b ; apply b.
           pose (list_exch_LI (unBoxed_list Γ2) (unBoxed_list Γ3) (unBoxed_list Γ4) (unBoxed_list Γ5) (unBoxed_list x0 ++ B :: unBoxed_list Γ1 ++ [Box A]) A).
           repeat rewrite unBox_app_distrib ; simpl in l ; repeat rewrite <- app_assoc in l ;  simpl ; repeat rewrite <- app_assoc ;  auto. }
        { destruct x0.
            - simpl in e0. subst. repeat rewrite <- app_assoc. simpl.
              exists (unBoxed_list Γ2 ++ unBoxed_list x ++ unBoxed_list Γ4 ++ unBoxed_list Γ3 ++ B :: unBoxed_list Γ1 ++ [Box A], A). exists (Γ2 ++ x ++ Γ4 ++ Γ3 ++ B :: Γ1, C). simpl ; repeat split.
              pose (@BoxImpLRule_I A B C (Γ2 ++ x ++ Γ4 ++ Γ3) Γ1). repeat rewrite unBox_app_distrib in b ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in b ; simpl in b ; apply b.
              pose (list_exch_LI (unBoxed_list Γ2)  (unBoxed_list Γ3) (unBoxed_list Γ4) (unBoxed_list x) (B :: unBoxed_list Γ1 ++ [Box A]) A).
              repeat rewrite unBox_app_distrib ; simpl in l ; repeat rewrite <- app_assoc in l ;  simpl ; repeat rewrite <- app_assoc ;  auto.
            - simpl in e0. inversion e0. subst. repeat rewrite <- app_assoc. simpl.
              exists (unBoxed_list Γ2 ++ unBoxed_list x ++ B :: unBoxed_list x0 ++ unBoxed_list Γ4 ++ unBoxed_list Γ3 ++ unBoxed_list Γ6 ++ [Box A], A). exists (Γ2 ++ x ++ B :: x0 ++ Γ4 ++ Γ3 ++ Γ6, C). simpl ; repeat split.
              pose (@BoxImpLRule_I A B C (Γ2 ++ x) (x0 ++ Γ4 ++ Γ3 ++ Γ6)). repeat rewrite unBox_app_distrib in b ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in b ; simpl in b ; apply b.
              pose (list_exch_LI (unBoxed_list Γ2) (unBoxed_list Γ3) (unBoxed_list Γ4) ((unBoxed_list x) ++ B :: (unBoxed_list x0)) ((unBoxed_list Γ6) ++ [Box A]) A).
              repeat rewrite unBox_app_distrib ; simpl in l ; repeat rewrite <- app_assoc in l ;  simpl ; repeat rewrite <- app_assoc ;  auto.
              pose (list_exch_LI Γ2 Γ3 Γ4 (x ++ B :: x0) Γ6 C). simpl in l ; repeat rewrite <- app_assoc in l ;  simpl ; repeat rewrite <- app_assoc ;  auto. }
      * destruct x.
        { simpl in e0. destruct Γ5.
            - simpl in e0. subst. repeat rewrite <- app_assoc. simpl.
              exists (unBoxed_list Γ2 ++ unBoxed_list x0 ++ unBoxed_list Γ3 ++ B :: unBoxed_list Γ1 ++ [Box A], A). exists (Γ2 ++ x0 ++ Γ3 ++ B :: Γ1, C). simpl ; repeat split.
              pose (@BoxImpLRule_I A B C (Γ2 ++ x0 ++ Γ3) Γ1). repeat rewrite unBox_app_distrib in b ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in b ; simpl in b ; apply b.
              pose (list_exch_LI (unBoxed_list Γ2) (unBoxed_list Γ3) [] (unBoxed_list x0) (B :: unBoxed_list Γ1 ++ [Box A]) A).
              repeat rewrite unBox_app_distrib ; simpl in l ; repeat rewrite <- app_assoc in l ;  simpl ; repeat rewrite <- app_assoc ;  auto. 
              pose (list_exch_LI Γ2 Γ3 [] x0 (B :: Γ1) C). simpl in l ; repeat rewrite <- app_assoc in l ;  simpl ; repeat rewrite <- app_assoc ;  auto.
            - simpl in e0. inversion e0. subst. repeat rewrite <- app_assoc. simpl.
              exists (unBoxed_list Γ2 ++ B :: unBoxed_list Γ5 ++ unBoxed_list x0 ++ unBoxed_list Γ3 ++ unBoxed_list Γ6 ++ [Box A], A). exists (Γ2 ++ B :: Γ5 ++ x0 ++ Γ3 ++ Γ6, C). simpl ; repeat split.
              pose (@BoxImpLRule_I A B C Γ2 (Γ5 ++ x0 ++ Γ3 ++ Γ6)). repeat rewrite unBox_app_distrib in b ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in b ; simpl in b ; apply b.
              pose (list_exch_LI (unBoxed_list Γ2) (unBoxed_list Γ3) (unBoxed_list x0) (B :: (unBoxed_list Γ5)) ((unBoxed_list Γ6) ++ [Box A]) A).
              repeat rewrite unBox_app_distrib ; simpl in l ; repeat rewrite <- app_assoc in l ;  simpl ; repeat rewrite <- app_assoc ;  auto.
              pose (list_exch_LI Γ2 Γ3 x0 (B :: Γ5) Γ6 C). simpl in l ; repeat rewrite <- app_assoc in l ;  simpl ; repeat rewrite <- app_assoc ;  auto. }
        { simpl in e0. inversion e0. subst.
          exists (unBoxed_list Γ2 ++ unBoxed_list Γ5 ++ unBoxed_list x0 ++ B :: unBoxed_list x ++ unBoxed_list Γ3 ++ unBoxed_list Γ6 ++ [Box A], A). exists (Γ2 ++ Γ5 ++ x0 ++ B :: x ++ Γ3 ++ Γ6, C). simpl ; repeat split.
          pose (@BoxImpLRule_I A B C (Γ2 ++ Γ5 ++ x0) (x ++ Γ3 ++ Γ6)). repeat rewrite unBox_app_distrib in b ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in b ; simpl in b ; apply b.
          pose (list_exch_LI (unBoxed_list Γ2) (unBoxed_list Γ3) ((unBoxed_list x0) ++ B :: (unBoxed_list x)) (unBoxed_list Γ5) ((unBoxed_list Γ6) ++ [Box A]) A).
          repeat rewrite unBox_app_distrib ; simpl in l ; repeat rewrite <- app_assoc in l ;  simpl ; repeat rewrite <- app_assoc ;  auto.
          pose (list_exch_LI Γ2 Γ3 (x0 ++ B :: x) Γ5 Γ6 C). simpl in l ; repeat rewrite <- app_assoc in l ;  simpl ; repeat rewrite <- app_assoc ;  auto. }
  + destruct x0.
      * simpl in e0. simpl. destruct Γ4.
        { simpl in e0. destruct Γ5.
            - simpl in e0. subst. repeat rewrite <- app_assoc. simpl.
              exists (unBoxed_list Γ2 ++ unBoxed_list x ++ B ::unBoxed_list Γ1 ++ [Box A], A). exists (Γ2 ++ x ++ B :: Γ1, C). simpl ; repeat split.
              pose (@BoxImpLRule_I A B C (Γ2 ++ x) Γ1). repeat rewrite unBox_app_distrib in b ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in b ; simpl in b ; apply b.
              repeat rewrite unBox_app_distrib ; repeat rewrite <- app_assoc. 1-2: apply list_exch_L_id.
            - simpl in e0. inversion e0. subst. repeat rewrite <- app_assoc. simpl.
              exists (unBoxed_list Γ2 ++ B :: unBoxed_list Γ5 ++ unBoxed_list x ++ unBoxed_list Γ6 ++ [Box A], A). exists (Γ2 ++ B :: Γ5 ++ x ++ Γ6, C). repeat split.
              pose (@BoxImpLRule_I A B C Γ2 (Γ5 ++ x ++ Γ6)). repeat rewrite unBox_app_distrib in b ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in b ; simpl in b ; apply b.
              pose (list_exch_LI (unBoxed_list Γ2) (unBoxed_list x) [] (B :: (unBoxed_list Γ5)) ((unBoxed_list Γ6) ++ [Box A]) A).
              repeat rewrite unBox_app_distrib ; simpl in l ; repeat rewrite <- app_assoc in l ;  simpl ; repeat rewrite <- app_assoc ;  auto. 
              pose (list_exch_LI Γ2 x [] (B :: Γ5) Γ6 C). simpl in l ; repeat rewrite <- app_assoc in l ;  simpl ; repeat rewrite <- app_assoc ;  auto. }
        { simpl in e0. inversion e0. subst. repeat rewrite <- app_assoc. simpl.
          exists (unBoxed_list Γ2 ++ unBoxed_list Γ5 ++ B :: unBoxed_list Γ4 ++ unBoxed_list x ++ unBoxed_list Γ6 ++ [Box A], A). exists (Γ2 ++ Γ5 ++ B :: Γ4 ++ x ++ Γ6, C). repeat split.
          pose (@BoxImpLRule_I A B C (Γ2 ++ Γ5) (Γ4 ++ x ++ Γ6)). repeat rewrite unBox_app_distrib in b ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in b ; simpl in b ; apply b.
          pose (list_exch_LI (unBoxed_list Γ2) (unBoxed_list x) (B :: (unBoxed_list Γ4)) (unBoxed_list Γ5) ((unBoxed_list Γ6) ++ [Box A]) A).
          repeat rewrite unBox_app_distrib ; simpl in l ; repeat rewrite <- app_assoc in l ;  simpl ; repeat rewrite <- app_assoc ;  auto. 
          pose (list_exch_LI Γ2 x (B :: Γ4) Γ5 Γ6 C). simpl in l ; repeat rewrite <- app_assoc in l ;  simpl ; repeat rewrite <- app_assoc ;  auto. }
      * simpl in e0. inversion e0. subst. repeat rewrite <- app_assoc. simpl.
          exists (unBoxed_list Γ2 ++ unBoxed_list Γ5 ++ unBoxed_list Γ4 ++ unBoxed_list x ++ B :: unBoxed_list x0 ++ unBoxed_list Γ6 ++ [Box A], A). exists (Γ2 ++ Γ5 ++ Γ4 ++ x ++ B :: x0 ++ Γ6, C). repeat split.
          pose (@BoxImpLRule_I A B C (Γ2 ++ Γ5 ++ Γ4 ++ x) (x0 ++ Γ6)). repeat rewrite unBox_app_distrib in b ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in b ; simpl in b ; apply b.
          pose (list_exch_LI (unBoxed_list Γ2) ((unBoxed_list x) ++ B :: (unBoxed_list x0)) (unBoxed_list Γ4) (unBoxed_list Γ5) ((unBoxed_list Γ6) ++ [Box A]) A).
          repeat rewrite unBox_app_distrib ; simpl in l ; repeat rewrite <- app_assoc in l ;  simpl ; repeat rewrite <- app_assoc ;  auto. 
          pose (list_exch_LI Γ2 (x ++ B :: x0) Γ4 Γ5 Γ6 C). simpl in l ; repeat rewrite <- app_assoc in l ;  simpl ; repeat rewrite <- app_assoc ;  auto.
Qed.

Lemma ImpR_app_list_exchL : forall s se ps,
  (@list_exch_L s se) ->
  (ImpRRule [ps] s) ->
  (existsT2 pse,
    (ImpRRule [pse] se) *
    (@list_exch_L ps pse)).
Proof.
intros s se ps exch. intro RA. inversion RA. inversion exch. subst.
inversion H. apply app2_find_hole in H1. destruct H1. repeat destruct s ; destruct p ; subst.
- exists (Γ2 ++ A :: Γ5 ++ Γ4 ++ Γ3 ++ Γ6, B). split.
  apply ImpRRule_I. assert (Γ2 ++ A :: Γ3 ++ Γ4 ++ Γ5 ++ Γ6 = (Γ2 ++ [A]) ++ Γ3 ++ Γ4 ++ Γ5 ++ Γ6).
  rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
  assert (Γ2 ++ A :: Γ5 ++ Γ4 ++ Γ3 ++ Γ6 = (Γ2 ++ [A]) ++ Γ5 ++ Γ4 ++ Γ3 ++ Γ6).
  rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply list_exch_LI.
- apply app2_find_hole in e0. destruct e0. repeat destruct s ; destruct p ; subst.
  + exists ((Γ2 ++ Γ5) ++ A :: Γ4 ++ Γ3 ++ Γ6,  B). split.
    assert (Γ2 ++ Γ5 ++ Γ4 ++ Γ3 ++ Γ6 = (Γ2 ++ Γ5) ++ Γ4 ++ Γ3 ++ Γ6). rewrite app_assoc.
    reflexivity. rewrite H0. clear H0. apply ImpRRule_I. repeat rewrite <- app_assoc.
    assert (Γ2 ++ Γ3 ++ A :: Γ4 ++ Γ5 ++ Γ6 = Γ2 ++ Γ3 ++ (A :: Γ4) ++ Γ5 ++ Γ6).
    reflexivity. rewrite H0. clear H0.
    assert (Γ2 ++ Γ5 ++ A :: Γ4 ++ Γ3 ++ Γ6 = Γ2 ++ Γ5 ++ (A :: Γ4) ++ Γ3 ++ Γ6).
    reflexivity. rewrite H0. clear H0. apply list_exch_LI.
  + apply app2_find_hole in e0. destruct e0. repeat destruct s ; destruct p ; subst.
    * exists ((Γ2 ++ Γ5 ++ Γ4) ++ A :: Γ3 ++ Γ6, B). split.
      assert (Γ2 ++ Γ5 ++ Γ4 ++ Γ3 ++ Γ6 = (Γ2 ++ Γ5 ++ Γ4) ++ Γ3 ++ Γ6). repeat rewrite app_assoc.
      reflexivity. rewrite H0. clear H0. apply ImpRRule_I. repeat rewrite <- app_assoc.
      assert (Γ2 ++ Γ3 ++ Γ4 ++ A :: Γ5 ++ Γ6 = Γ2 ++ Γ3 ++ (Γ4 ++ [A]) ++ Γ5 ++ Γ6).
      repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
      assert (Γ2 ++ Γ5 ++ Γ4 ++ A :: Γ3 ++ Γ6 = Γ2 ++ Γ5 ++ (Γ4 ++ [A]) ++ Γ3 ++ Γ6).
      repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply list_exch_LI.
    * apply app2_find_hole in e0. destruct e0. repeat destruct s ; destruct p ; subst.
      { repeat rewrite <- app_assoc. exists (Γ2 ++ Γ5 ++ Γ4 ++ Γ3 ++ A :: Γ6, B).
        split. repeat rewrite app_assoc. apply ImpRRule_I. apply list_exch_LI. }
      { repeat rewrite <- app_assoc. exists (Γ2 ++ Γ5 ++ Γ4 ++ Γ3 ++ x0 ++ A :: Γ1, B).
        split. repeat rewrite app_assoc. apply ImpRRule_I. apply list_exch_LI. }
      { repeat rewrite <- app_assoc. exists (Γ2 ++ (x ++ A :: x0) ++ Γ4 ++ Γ3 ++ Γ6, B).
        split. assert (Γ2 ++ (x ++ A :: x0) ++ Γ4 ++ Γ3 ++ Γ6 = (Γ2 ++ x) ++ A :: x0 ++ Γ4 ++ Γ3 ++ Γ6).
        repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
        assert (Γ2 ++ x ++ x0 ++ Γ4 ++ Γ3 ++ Γ6 = (Γ2 ++ x) ++ x0 ++ Γ4 ++ Γ3 ++ Γ6).
        repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
        apply ImpRRule_I.
        assert (Γ2 ++ Γ3 ++ Γ4 ++ x ++ A :: x0 ++ Γ6 = Γ2 ++ Γ3 ++ Γ4 ++ (x ++ A :: x0) ++ Γ6).
        repeat rewrite <- app_assoc. reflexivity. rewrite H0. apply list_exch_LI. }
    * repeat rewrite <- app_assoc. exists (Γ2 ++ Γ5 ++ (x0 ++ A :: x) ++ Γ3 ++ Γ6, B).
      split. assert (Γ2 ++ Γ5 ++ (x0 ++ A :: x) ++ Γ3 ++ Γ6 = (Γ2 ++ Γ5 ++ x0) ++ A :: x ++ Γ3 ++ Γ6).
      repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
      assert (Γ2 ++ Γ5 ++ x0 ++ x ++ Γ3 ++ Γ6 = (Γ2 ++ Γ5 ++ x0) ++ x ++ Γ3 ++ Γ6).
      repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
      apply ImpRRule_I.
      assert (Γ2 ++ Γ3 ++ x0 ++ A :: x ++ Γ5 ++ Γ6 = Γ2 ++ Γ3 ++ (x0 ++ A :: x) ++ Γ5 ++ Γ6).
      repeat rewrite <- app_assoc. reflexivity. rewrite H0. apply list_exch_LI.
  + repeat rewrite <- app_assoc. exists (Γ2 ++ Γ5 ++ Γ4 ++ (x ++ A :: x0) ++ Γ6, B).
    split. assert (Γ2 ++ Γ5 ++ Γ4 ++ (x ++ A :: x0) ++ Γ6 = (Γ2 ++ Γ5 ++ Γ4 ++ x) ++ A :: x0 ++ Γ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
    assert (Γ2 ++ Γ5 ++ Γ4 ++ x ++ x0 ++ Γ6 = (Γ2 ++ Γ5 ++ Γ4 ++ x) ++ x0 ++ Γ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
    apply ImpRRule_I.
    assert (Γ2 ++ x ++ A :: x0 ++ Γ4 ++ Γ5 ++ Γ6 = Γ2 ++ (x ++ A :: x0) ++ Γ4 ++ Γ5 ++ Γ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. apply list_exch_LI.
- repeat rewrite <- app_assoc. exists (Γ0 ++ A :: x ++ Γ5 ++ Γ4 ++ Γ3 ++ Γ6, B).
  split. apply ImpRRule_I.
  assert (Γ0 ++ A :: x ++ Γ3 ++ Γ4 ++ Γ5 ++ Γ6 = (Γ0 ++ A :: x) ++ Γ3 ++ Γ4 ++ Γ5 ++ Γ6).
  repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
  assert (Γ0 ++ A :: x ++ Γ5 ++ Γ4 ++ Γ3 ++ Γ6 = (Γ0 ++ A :: x) ++ Γ5 ++ Γ4 ++ Γ3 ++ Γ6).
  repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply list_exch_LI.
Qed.