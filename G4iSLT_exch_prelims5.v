Require Import List.
Export ListNotations.
Require Import PeanoNat.
Require Import Lia.

Require Import general_export.

Require Import G4iSLT_calc.
Require Import G4iSLT_list_lems.
Require Import G4iSLT_exch_prelims1.

Lemma SLR_app_list_exchL : forall s se ps,
  (@list_exch_L s se) ->
  (SLRRule [ps] s) ->
  (existsT2 pse,
    (SLRRule [pse] se) *
    (@list_exch_L ps pse)).
Proof.
intros s se ps exch RA. inversion RA. inversion exch. subst. inversion H ; subst.
exists (unBoxed_list Γ0 ++ unBoxed_list Γ3 ++ unBoxed_list Γ2 ++ unBoxed_list Γ1 ++ unBoxed_list Γ4 ++ [Box A], A). split.
- pose (@SLRRule_I A (Γ0 ++ Γ3 ++ Γ2 ++ Γ1 ++ Γ4)). repeat rewrite unBox_app_distrib in s ; repeat rewrite <- app_assoc in s ; auto.
- repeat rewrite unBox_app_distrib ; repeat rewrite <- app_assoc. apply list_exch_LI.
Qed.

Lemma AndImpL_app_list_exchL : forall s se ps,
  (@list_exch_L s se) ->
  (AndImpLRule [ps] s) ->
   (existsT2 pse, (AndImpLRule [pse] se) *
    (@list_exch_L ps pse)).
Proof.
intros s se ps exch RA. inversion RA. subst. inversion exch. subst. symmetry in H0.
apply app2_find_hole in H0. destruct H0. repeat destruct s ; destruct p ; subst.
- destruct Γ3.
  + simpl in e0. subst. simpl. destruct Γ4.
      * simpl in e0. simpl. destruct Γ5.
        { simpl in e0. subst. simpl. exists (Γ0 ++ A → B → C :: Γ1, D). repeat split. apply list_exch_L_id. }
        { simpl in e0. inversion e0. subst. simpl. exists (Γ0 ++ A → B → C :: Γ5 ++ Γ6, D). repeat split. apply list_exch_L_id. }
      * simpl in e0. inversion e0. subst. exists (Γ0 ++ Γ5 ++ A → B → C :: Γ4 ++ Γ6, D). repeat split.
        pose (AndImpLRule_I A B C D (Γ0 ++ Γ5) (Γ4 ++ Γ6)). repeat rewrite <- app_assoc ; simpl ;  repeat rewrite <- app_assoc in a ; simpl in a ; auto.
        pose (list_exch_LI Γ0 (A → B → C :: Γ4) [] Γ5 Γ6 D). repeat rewrite <- app_assoc ; simpl ;  repeat rewrite <- app_assoc in l ; simpl in l ; auto.
  + simpl in e0. inversion e0. subst. exists (Γ0 ++ Γ5 ++ Γ4 ++ A → B → C :: Γ3 ++ Γ6, D). repeat split.
     pose (AndImpLRule_I A B C D (Γ0 ++ Γ5 ++ Γ4) (Γ3 ++ Γ6)). repeat rewrite <- app_assoc ; simpl ;  repeat rewrite <- app_assoc in a ; simpl in a ; auto.
     pose (list_exch_LI Γ0 (A → B → C :: Γ3) Γ4 Γ5 Γ6 D). repeat rewrite <- app_assoc ; simpl ;  repeat rewrite <- app_assoc in l ; simpl in l ; auto.
- destruct x.
  + simpl in e0. subst. simpl. destruct Γ3.
      * simpl in e0. simpl. destruct Γ4.
        { simpl in e0. subst. simpl. rewrite <- e0. exists ((Γ0 ++ []) ++ A → B → C :: Γ1, D). repeat split. rewrite <- app_assoc. apply list_exch_L_id. }
        { simpl in e0. inversion e0. subst. simpl. rewrite <- app_assoc ; simpl. exists (Γ0 ++ Γ5 ++ A → B → C :: Γ4 ++ Γ6, D). repeat split.
          pose (AndImpLRule_I A B C D (Γ0 ++ Γ5) (Γ4 ++ Γ6)). repeat rewrite <- app_assoc ; simpl ;  repeat rewrite <- app_assoc in a ; simpl in a ; auto.
          pose (list_exch_LI Γ0 (A → B → C :: Γ4) [] Γ5 Γ6 D). repeat rewrite <- app_assoc ; simpl ;  repeat rewrite <- app_assoc in l ; simpl in l ; auto. }
      * simpl in e0. inversion e0. subst. rewrite <- app_assoc ; simpl. exists (Γ0 ++ Γ5 ++ Γ4 ++ A → B → C :: Γ3 ++ Γ6, D). repeat split.
        pose (AndImpLRule_I A B C D (Γ0 ++ Γ5 ++ Γ4) (Γ3 ++ Γ6)). repeat rewrite <- app_assoc ; simpl ;  repeat rewrite <- app_assoc in a ; simpl in a ; auto.
        pose (list_exch_LI Γ0 (A → B → C :: Γ3) Γ4 Γ5 Γ6 D). repeat rewrite <- app_assoc ; simpl ;  repeat rewrite <- app_assoc in l ; simpl in l ; auto.
  + simpl in e0. inversion e0. subst. exists (Γ0 ++ A → B → C :: x ++ Γ5 ++ Γ4 ++ Γ3 ++ Γ6, D). repeat rewrite <- app_assoc. repeat split.
     pose (list_exch_LI (Γ0 ++ A → B → C :: x) Γ3 Γ4 Γ5 Γ6 D). repeat rewrite <- app_assoc ; simpl ;  repeat rewrite <- app_assoc in l ; simpl in l ; auto.
- apply app2_find_hole in e0. destruct e0. repeat destruct s ; destruct p ; subst.
  + simpl in e0. subst. simpl. destruct Γ4.
      * simpl in e0. simpl. destruct Γ5.
        { simpl in e0. subst. simpl. exists ((Γ2 ++ Γ3) ++ A → B → C :: Γ1, D). repeat split. 2: apply list_exch_L_id. rewrite app_assoc. apply AndImpLRule_I. }
        { simpl in e0. inversion e0. subst. simpl. exists (Γ2 ++ A → B → C :: Γ5 ++ Γ3 ++ Γ6, D). repeat split.
          pose (list_exch_LI Γ2 Γ3 [] (A → B → C :: Γ5) Γ6 D). repeat rewrite <- app_assoc ; simpl ;  repeat rewrite <- app_assoc in l ; simpl in l ; auto. }
      * simpl in e0. inversion e0. subst. exists ((Γ2 ++ Γ5) ++ A → B → C :: Γ4 ++ Γ3 ++ Γ6, D). repeat split.
        pose (AndImpLRule_I A B C D (Γ2 ++ Γ5) (Γ4 ++ Γ3 ++ Γ6)). repeat rewrite <- app_assoc ; simpl ;  repeat rewrite <- app_assoc in a ; simpl in a ; auto.
        pose (list_exch_LI Γ2 Γ3 (A → B → C :: Γ4) Γ5 Γ6 D). repeat rewrite <- app_assoc ; simpl ;  repeat rewrite <- app_assoc in l ; simpl in l ; auto.
  + apply app2_find_hole in e0. destruct e0. repeat destruct s ; destruct p ; subst.
      * simpl in e0. simpl. destruct Γ5.
        { simpl in e0. subst. simpl. exists ((Γ2 ++ Γ4 ++ Γ3) ++ A → B → C :: Γ1, D). repeat split.
          pose (AndImpLRule_I A B C D (Γ2 ++ Γ4 ++ Γ3) Γ1). repeat rewrite <- app_assoc ; simpl ;  repeat rewrite <- app_assoc in a ; simpl in a ; auto.
          pose (list_exch_LI Γ2 Γ3 [] Γ4 (A → B → C :: Γ1) D). repeat rewrite <- app_assoc ; simpl ;  repeat rewrite <- app_assoc in l ; simpl in l ; auto. }
        { simpl in e0. inversion e0. subst. simpl. exists (Γ2 ++ A → B → C :: Γ5 ++ Γ4 ++ Γ3 ++ Γ6, D). repeat split.
          pose (AndImpLRule_I A B C D (Γ2 ++ Γ3 ++ Γ4) (Γ5 ++ Γ6)). repeat rewrite <- app_assoc ; simpl ;  repeat rewrite <- app_assoc in a ; simpl in a ; auto.
          pose (list_exch_LI Γ2 Γ3 Γ4 (A → B → C :: Γ5) Γ6 D). repeat rewrite <- app_assoc ; simpl ;  repeat rewrite <- app_assoc in l ; simpl in l ; auto. }
      * apply app2_find_hole in e0. destruct e0. repeat destruct s ; destruct p ; subst.
        {  repeat rewrite <- app_assoc. exists (Γ2 ++ Γ5 ++ Γ4 ++ Γ3 ++ A → B → C :: Γ1, D). repeat split. repeat rewrite app_assoc. apply AndImpLRule_I. }
        {  repeat rewrite <- app_assoc. exists (Γ2 ++ Γ5 ++ Γ4 ++ Γ3 ++ x0 ++ A → B → C :: Γ1, D). repeat split. repeat rewrite app_assoc. apply AndImpLRule_I. }
        { destruct x0.
            - simpl in e0. subst. repeat rewrite <- app_assoc. simpl. exists (Γ2 ++ x ++ Γ4 ++ Γ3 ++ A → B → C :: Γ1, D). repeat split. repeat rewrite app_assoc. apply AndImpLRule_I.
            - simpl in e0. inversion e0. subst. repeat rewrite <- app_assoc. simpl. exists ((Γ2 ++ x) ++ A → B → C :: x0 ++ Γ4 ++ Γ3 ++ Γ6, D). repeat split.
              pose (AndImpLRule_I A B C D (Γ2 ++ x) (x0 ++ Γ4 ++ Γ3 ++ Γ6)). repeat rewrite <- app_assoc ; simpl ;  repeat rewrite <- app_assoc in a ; simpl in a ; auto.
              pose (list_exch_LI Γ2 Γ3 Γ4 (x ++ A → B → C :: x0) Γ6 D). repeat rewrite <- app_assoc ; simpl ;  repeat rewrite <- app_assoc in l ; simpl in l ; auto. }
      * destruct x.
        { simpl in e0. destruct Γ5.
            - simpl in e0. subst. repeat rewrite <- app_assoc. simpl. exists (Γ2 ++ x0 ++ Γ3 ++ A → B → C :: Γ1, D). repeat split.
              pose (AndImpLRule_I A B C D (Γ2 ++ x0 ++ Γ3) Γ1). repeat rewrite <- app_assoc ; simpl ;  repeat rewrite <- app_assoc in a ; simpl in a ; auto.
              pose (list_exch_LI Γ2 Γ3 [] x0 (A → B → C :: Γ1) D). repeat rewrite <- app_assoc ; simpl ;  repeat rewrite <- app_assoc in l ; simpl in l ; auto.
            - simpl in e0. inversion e0. subst. repeat rewrite <- app_assoc. simpl. exists (Γ2 ++ A → B → C :: Γ5 ++ x0 ++ Γ3 ++ Γ6, D). repeat split.
              pose (list_exch_LI Γ2 Γ3 x0 (A → B → C :: Γ5) Γ6 D). repeat rewrite <- app_assoc ; simpl ;  repeat rewrite <- app_assoc in l ; simpl in l ; auto. }
        { simpl in e0. inversion e0. subst. exists ((Γ2 ++ Γ5 ++ x0) ++ A → B → C :: x ++ Γ3 ++ Γ6, D). split.
           pose (AndImpLRule_I A B C D (Γ2 ++ Γ5 ++ x0) (x ++ Γ3 ++ Γ6)). repeat rewrite <- app_assoc ; simpl ;  repeat rewrite <- app_assoc in a ; simpl in a ; auto.
           pose (list_exch_LI Γ2 Γ3 (x0 ++ A → B → C :: x) Γ5 Γ6 D). repeat rewrite <- app_assoc ; simpl ;  repeat rewrite <- app_assoc in l ; simpl in l ; auto. }
  + destruct x0.
      * simpl in e0. simpl. destruct Γ4.
        { simpl in e0. destruct Γ5.
            - simpl in e0. subst. repeat rewrite <- app_assoc. simpl. exists (Γ2 ++ x ++ A → B → C :: Γ1, D). repeat split.
              repeat rewrite app_assoc. apply AndImpLRule_I. apply list_exch_L_id.
            - simpl in e0. inversion e0. subst. repeat rewrite <- app_assoc. simpl. exists (Γ2 ++ A → B → C :: Γ5 ++ x ++ Γ6, D). repeat split.
               pose (list_exch_LI Γ2 x [] (A → B → C :: Γ5) Γ6 D). repeat rewrite <- app_assoc ; simpl ;  repeat rewrite <- app_assoc in l ; simpl in l ; auto. }
        { simpl in e0. inversion e0. subst. repeat rewrite <- app_assoc. simpl. exists ((Γ2 ++ Γ5) ++ A → B → C :: Γ4 ++ x ++ Γ6, D). repeat split.
           pose (AndImpLRule_I A B C D (Γ2 ++ Γ5) (Γ4 ++ x ++ Γ6)). repeat rewrite <- app_assoc ; simpl ;  repeat rewrite <- app_assoc in a ; simpl in a ; auto.
           pose (list_exch_LI Γ2 x (A → B → C :: Γ4) Γ5 Γ6 D). repeat rewrite <- app_assoc ; simpl ;  repeat rewrite <- app_assoc in l ; simpl in l ; auto. }
      * simpl in e0. inversion e0. subst. repeat rewrite <- app_assoc. simpl. exists ((Γ2 ++ Γ5 ++ Γ4 ++ x) ++ A → B → C :: x0 ++ Γ6, D). repeat split.
         pose (AndImpLRule_I A B C D (Γ2 ++ Γ5 ++ Γ4 ++ x) (x0 ++ Γ6)). repeat rewrite <- app_assoc ; simpl ;  repeat rewrite <- app_assoc in a ; simpl in a ; auto.
         pose (list_exch_LI Γ2 (x ++ A → B → C :: x0) Γ4 Γ5 Γ6 D). repeat rewrite <- app_assoc ; simpl ;  repeat rewrite <- app_assoc in l ; simpl in l ; auto.
Qed. 

Lemma OrImpL_app_list_exchL : forall s se ps,
  (@list_exch_L s se) ->
  (OrImpLRule [ps] s) ->
   (existsT2 pse, (OrImpLRule [pse] se) *
   ((@list_exch_L ps pse) + (existsT2 pse1, (@list_exch_L ps pse1) * (@list_exch_L pse1 pse)))).
Proof.
intros s se ps exch RA. inversion RA. subst. inversion exch. subst. symmetry in H0.
apply app2_find_hole in H0. destruct H0. repeat destruct s ; destruct p ; subst.
- destruct Γ4.
  + simpl in e0. subst. simpl. destruct Γ5.
      * simpl in e0. simpl. destruct Γ6.
        { simpl in e0. subst. simpl. exists (Γ0 ++ A → C :: Γ1 ++ B → C :: Γ2, D). split ;auto. left. apply list_exch_L_id. }
        { simpl in e0. inversion e0. subst. simpl. apply app2_find_hole in H1. destruct H1. repeat destruct s ; destruct p ; subst.
          - exists (Γ0 ++ A → C :: Γ6 ++ B → C :: Γ7, D). repeat split. left. apply list_exch_L_id.
          - exists (Γ0 ++ A → C :: (Γ6 ++ x0) ++ B → C :: Γ2, D). repeat split. 2: left. 2: apply list_exch_L_id.
            assert (Γ0 ++ (A ∨ B) → C :: Γ6 ++ x0 ++ Γ2 =Γ0 ++ (A ∨ B) → C :: (Γ6 ++ x0) ++ Γ2). repeat rewrite <- app_assoc. auto.
            rewrite H. apply OrImpLRule_I.
          - exists (Γ0 ++ A → C :: Γ1 ++ B → C :: x0 ++ Γ7, D). repeat split. 2: left. 2: apply list_exch_L_id. repeat rewrite <- app_assoc.
            apply OrImpLRule_I. }
      * simpl in e0. inversion e0. subst. apply app2_find_hole in H1. destruct H1. repeat destruct s ; destruct p ; subst.
        { exists (Γ0 ++ Γ6 ++ (A→ C :: Γ5) ++ B→ C :: Γ7, D) . repeat split. 2: left.
          pose (OrImpLRule_I A B C D (Γ0 ++ Γ6) Γ5 Γ7). repeat rewrite <- app_assoc ; simpl ;  repeat rewrite <- app_assoc in o ; simpl in o ; auto.
          pose (list_exch_LI Γ0 (A → C :: Γ5 ++ [B → C]) [] Γ6 Γ7 D). repeat rewrite <- app_assoc ; simpl ; repeat (repeat rewrite <- app_assoc in l ; simpl in l) ; auto. }
        { apply app2_find_hole in e1. destruct e1. repeat destruct s ; destruct p ; subst.
          - exists ((Γ0 ++ Γ6) ++ A→ C :: Γ5 ++ B→ C :: Γ7, D). split. 2: left.
            pose (OrImpLRule_I A B C D (Γ0 ++ Γ6) Γ5 Γ7). repeat rewrite <- app_assoc ; simpl ;  repeat rewrite <- app_assoc in o ; simpl in o ; auto.
            pose (list_exch_LI Γ0 (A → C :: Γ5) [] Γ6 (B → C :: Γ7) D). repeat rewrite <- app_assoc ; simpl ; repeat (repeat rewrite <- app_assoc in l ; simpl in l) ; auto.
          - exists ((Γ0 ++ Γ6) ++ A → C :: (Γ5 ++ x1) ++ B → C :: Γ2, D). split. 2: left.
            pose (OrImpLRule_I A B C D (Γ0 ++ Γ6) (Γ5 ++ x1) Γ2). repeat rewrite <- app_assoc ; simpl ;  repeat rewrite <- app_assoc in o ; simpl in o ; auto.
            pose (list_exch_LI Γ0 (A → C :: Γ5) [] Γ6 (x1 ++ B → C :: Γ2) D). repeat rewrite <- app_assoc ; simpl ; repeat (repeat rewrite <- app_assoc in l ; simpl in l) ; auto.
          - exists ((Γ0 ++ x0 ++ x1) ++ A → C :: Γ5 ++ B → C :: Γ7, D). repeat split. 2: right.
            pose (OrImpLRule_I A B C D (Γ0 ++ x0 ++ x1) Γ5 Γ7). repeat rewrite <- app_assoc ; simpl ;  repeat rewrite <- app_assoc in o ; simpl in o ; auto.
            exists (Γ0 ++ x1++ A → C :: (Γ5 ++ x0) ++ B → C :: Γ7, D). repeat split.
            pose (list_exch_LI Γ0 [] (A → C :: Γ5 ++ x0 ++ [B → C]) x1 Γ7 D). repeat rewrite <- app_assoc ; simpl ; repeat (repeat rewrite <- app_assoc in l ; simpl in l) ; auto.
            pose (list_exch_LI Γ0 [] (x1 ++ A → C :: Γ5) x0 (B → C :: Γ7) D). repeat rewrite <- app_assoc ; simpl ; repeat (repeat rewrite <- app_assoc in l ; simpl in l) ; auto. }
        {  exists ((Γ0 ++ Γ6) ++ A → C :: Γ1 ++ B → C :: x0 ++ Γ7, D). repeat split. 2: left.
            pose (OrImpLRule_I A B C D (Γ0 ++ Γ6) Γ1 (x0 ++ Γ7)). repeat (simpl ; rewrite <- app_assoc ; simpl) ; repeat (simpl ; rewrite <- app_assoc in o ; simpl in o) ; auto.
            pose (list_exch_LI Γ0 (A → C :: Γ1 ++ B → C :: x0) [] Γ6 Γ7 D). repeat (simpl ; rewrite <- app_assoc ; simpl) ; repeat (simpl in l ; rewrite <- app_assoc in l ; simpl in l) ; auto. }
  + inversion e0. subst. symmetry in H1. apply app2_find_hole in H1. destruct H1. repeat destruct s ; destruct p ; subst.
     * exists ((Γ0 ++ Γ6 ++ Γ5) ++ A → C :: Γ1 ++ B → C :: Γ7, D). repeat split. 2: right.
        pose (OrImpLRule_I A B C D (Γ0 ++ Γ6 ++ Γ5) Γ1 Γ7). repeat rewrite <- app_assoc ; simpl ;  repeat rewrite <- app_assoc in o ; simpl in o ; auto.
        exists (Γ0 ++ Γ5 ++  A → C :: Γ1 ++ B → C :: Γ6 ++ Γ7, D). repeat split.
        pose (list_exch_LI Γ0 [] (A → C :: Γ1 ++ [B → C]) Γ5 (Γ6 ++ Γ7) D). repeat (simpl ; rewrite <- app_assoc ; simpl) ; repeat (simpl in l ; rewrite <- app_assoc in l ; simpl in l) ; auto.
        pose (list_exch_LI Γ0 [] (Γ5 ++ A → C :: Γ1 ++ [B → C]) Γ6 Γ7 D). repeat (simpl ; rewrite <- app_assoc ; simpl) ; repeat (simpl in l ; rewrite <- app_assoc in l ; simpl in l) ; auto.
     * exists ((Γ0 ++ Γ6 ++ Γ5) ++ A → C :: Γ1 ++ B → C :: x0 ++ Γ7, D). repeat split. 2: right.
        pose (OrImpLRule_I A B C D (Γ0 ++ Γ6 ++ Γ5) Γ1 (x0 ++ Γ7)). repeat (simpl ; rewrite <- app_assoc) ;  repeat (simpl in o ; rewrite <- app_assoc in o) ; auto.
        exists (Γ0 ++ Γ5 ++ A → C :: Γ1 ++ B → C :: x0 ++ Γ6 ++ Γ7, D). repeat split.
        pose (list_exch_LI Γ0 [] (A → C :: Γ1 ++ B → C :: x0) Γ5 (Γ6 ++ Γ7) D). repeat (simpl ; rewrite <- app_assoc ; simpl) ; repeat (simpl in l ; rewrite <- app_assoc in l ; simpl in l) ; auto.
        pose (list_exch_LI Γ0 [] (Γ5 ++ A → C :: Γ1 ++ B → C :: x0) Γ6 Γ7 D). repeat (simpl ; rewrite <- app_assoc ; simpl) ; repeat (simpl in l ; rewrite <- app_assoc in l ; simpl in l) ; auto.
     * symmetry in e1. apply app2_find_hole in e1. destruct e1. repeat destruct s ; destruct p ; subst.
       { exists ((Γ0 ++ Γ6 ++ x0) ++ A → C :: Γ4 ++ B → C :: Γ7, D). repeat split. 2: right.
         pose (OrImpLRule_I A B C D (Γ0 ++ Γ6 ++ x0) Γ4 Γ7). repeat (simpl ; rewrite <- app_assoc) ;  repeat (simpl in o ; rewrite <- app_assoc in o) ; auto.
         exists (Γ0 ++ x0 ++ A → C :: Γ4 ++ B → C :: Γ6 ++ Γ7, D). split.
         pose (list_exch_LI Γ0 [] (A → C :: Γ4) x0 (B → C :: Γ6 ++ Γ7) D). repeat (simpl ; rewrite <- app_assoc ; simpl) ; repeat (simpl in l ; rewrite <- app_assoc in l ; simpl in l) ; auto.
         pose (list_exch_LI Γ0 [] (x0 ++ A → C :: Γ4 ++ [B → C]) Γ6 Γ7 D). repeat (simpl ; rewrite <- app_assoc ; simpl) ; repeat (simpl in l ; rewrite <- app_assoc in l ; simpl in l) ; auto. }
       { exists ((Γ0 ++ Γ6 ++ x0 ++ x1) ++ A → C :: Γ4 ++ B → C :: Γ7, D). repeat split. 2: right.
         pose (OrImpLRule_I A B C D (Γ0 ++ Γ6 ++ x0 ++ x1) Γ4 Γ7). repeat (simpl ; rewrite <- app_assoc) ;  repeat (simpl in o ; rewrite <- app_assoc in o) ; auto.
          exists (Γ0 ++ A → C :: Γ4 ++ B → C :: x0 ++ x1 ++ Γ6 ++ Γ7, D). split.
         pose (list_exch_LI (Γ0 ++ A → C :: Γ4) x0 [B → C] [] (x1 ++ Γ6 ++ Γ7) D). repeat (simpl ; rewrite <- app_assoc ; simpl) ; repeat (simpl in l ; rewrite <- app_assoc in l ; simpl in l) ; auto.
         pose (list_exch_LI Γ0 (A → C :: Γ4 ++ [B → C]) (x0 ++ x1) Γ6 Γ7 D). repeat (simpl ; rewrite <- app_assoc ; simpl) ; repeat (simpl in l ; rewrite <- app_assoc in l ; simpl in l) ; auto. }
       { apply app2_find_hole in e1. destruct e1. repeat destruct s ; destruct p ; subst.
          - exists ((Γ0 ++ Γ6 ++ Γ5) ++ A→ C :: Γ4 ++ B→ C :: Γ7, D). repeat split. 2: left.
            pose (OrImpLRule_I A B C D (Γ0 ++ Γ6 ++ Γ5) Γ4 Γ7). repeat (simpl ; rewrite <- app_assoc) ; repeat (simpl in o ; repeat rewrite <- app_assoc in o) ; auto.
            pose (list_exch_LI Γ0 (A → C :: Γ4) Γ5 Γ6 (B → C :: Γ7) D). repeat rewrite <- app_assoc ; simpl ; repeat (repeat rewrite <- app_assoc in l ; simpl in l) ; auto.
          - exists ((Γ0 ++ Γ6 ++ Γ5) ++ A → C :: (Γ4 ++ x0) ++ B → C :: Γ2, D). repeat split. 2: left.
            pose (OrImpLRule_I A B C D (Γ0 ++ Γ6 ++ Γ5) (Γ4 ++ x0) Γ2). repeat (simpl ; rewrite <- app_assoc) ; repeat (simpl in o ; repeat rewrite <- app_assoc in o) ; auto.
            pose (list_exch_LI Γ0 (A → C :: Γ4) Γ5 Γ6 (x0 ++ B → C :: Γ2) D). repeat rewrite <- app_assoc ; simpl ; repeat (repeat rewrite <- app_assoc in l ; simpl in l) ; auto.
          - exists ((Γ0 ++ x1 ++ x0 ++ Γ5) ++ A → C :: Γ4 ++ B → C :: Γ7, D). repeat split. 2: right.
            pose (OrImpLRule_I A B C D (Γ0 ++ x1 ++ x0 ++ Γ5) Γ4 Γ7). repeat (simpl ; rewrite <- app_assoc) ;  repeat (simpl in o ; rewrite <- app_assoc in o) ; auto.
            exists ((Γ0 ++ A → C :: Γ4 ++ Γ5 ++ x1) ++ [] ++ x0 ++ [B → C] ++ Γ7, D). repeat split ; simpl.
            pose (list_exch_LI (Γ0 ++ A → C :: Γ4 ++ Γ5 ++ x1) [] [B → C] x0 Γ7 D). repeat (simpl ; rewrite <- app_assoc ; simpl) ; repeat (simpl in l ; rewrite <- app_assoc in l ; simpl in l) ; auto.
            pose (list_exch_LI Γ0 (A → C :: Γ4) Γ5 (x1 ++ x0) (B → C :: Γ7) D). repeat (simpl ; rewrite <- app_assoc ; simpl) ; repeat (simpl in l ; rewrite <- app_assoc in l ; simpl in l) ; auto. }
- destruct x ; simpl in e0 ; subst ; repeat rewrite <- app_assoc ; simpl.
  * destruct Γ4.
    + simpl in e0. subst. simpl. destruct Γ5.
        { simpl in e0. simpl. destruct Γ6.
          { simpl in e0. subst. simpl. exists (Γ0 ++ A → C :: Γ1 ++ B → C :: Γ2, D). split ;auto. left. apply list_exch_L_id. }
          { simpl in e0. inversion e0. subst. simpl. apply app2_find_hole in H1. destruct H1. repeat destruct s ; destruct p ; subst.
            - exists (Γ0 ++ A → C :: Γ1 ++ B → C :: Γ2, D). repeat split. left. apply list_exch_L_id.
            - exists (Γ0 ++ A → C :: Γ1 ++ B → C :: x ++ Γ7, D). repeat rewrite <- app_assoc. repeat split. left. apply list_exch_L_id.
            - exists (Γ0 ++ A → C :: (Γ6 ++ x) ++ B → C :: Γ2, D). repeat split. 2: left. 2: apply list_exch_L_id.
              assert (Γ0 ++ (A ∨ B) → C :: Γ6 ++ x ++ Γ2 =Γ0 ++ (A ∨ B) → C :: (Γ6 ++ x) ++ Γ2). repeat rewrite <- app_assoc. auto.
              rewrite H. apply OrImpLRule_I. } }
        { simpl in e0. inversion e0. subst. apply app2_find_hole in H1. destruct H1. repeat destruct s ; destruct p ; subst.
          { exists ((Γ0 ++ Γ6) ++ A→ C :: Γ1 ++ B→ C :: Γ7, D) . repeat split. 2: left.
            pose (OrImpLRule_I A B C D (Γ0 ++ Γ6) Γ1 Γ7). repeat (simpl ; rewrite <- app_assoc) ; repeat (simpl in o ; repeat rewrite <- app_assoc in o) ; auto.
            pose (list_exch_LI Γ0 [] (A → C :: Γ1 ++ [B → C]) Γ6 Γ7 D). repeat rewrite <- app_assoc ; simpl ; repeat (repeat rewrite <- app_assoc in l ; simpl in l) ; auto. }
          {  exists ((Γ0 ++  Γ6) ++ A→ C ::  Γ1 ++ B→ C :: x ++ Γ7, D). split. 2: left.
            pose (OrImpLRule_I A B C D (Γ0 ++ Γ6) Γ1 (x ++ Γ7)). repeat (simpl ; rewrite <- app_assoc) ; repeat (simpl in o ; repeat rewrite <- app_assoc in o) ; auto.
            pose (list_exch_LI Γ0 [] (A → C :: Γ1 ++ B → C :: x) Γ6 Γ7 D). repeat rewrite <- app_assoc ; simpl ; repeat (repeat rewrite <- app_assoc in l ; simpl in l) ; auto. }
          { apply app2_find_hole in e1. destruct e1. repeat destruct s ; destruct p ; subst.
            - exists ((Γ0 ++ Γ6) ++ A → C :: Γ5 ++ B → C :: Γ7, D). repeat split. 2: left.
              pose (OrImpLRule_I A B C D (Γ0 ++ Γ6) Γ5 Γ7). repeat (simpl ; rewrite <- app_assoc) ; repeat (simpl in o ; repeat rewrite <- app_assoc in o) ; auto.
              pose (list_exch_LI Γ0 [] (A → C :: Γ5) Γ6 (B → C :: Γ7) D). repeat rewrite <- app_assoc ; simpl ; repeat (repeat rewrite <- app_assoc in l ; simpl in l) ; auto.
            - exists ((Γ0 ++ Γ6) ++ A → C :: (Γ5 ++ x0) ++ B → C :: Γ2, D). repeat split. 2: left.
              pose (OrImpLRule_I A B C D (Γ0 ++ Γ6) (Γ5 ++ x0) Γ2). repeat (simpl ; rewrite <- app_assoc) ; repeat (simpl in o ; repeat rewrite <- app_assoc in o) ; auto.
              pose (list_exch_LI Γ0 [] (A → C :: Γ5) Γ6 (x0 ++ B → C :: Γ2) D). repeat rewrite <- app_assoc ; simpl ; repeat (repeat rewrite <- app_assoc in l ; simpl in l) ; auto.
            - exists ((Γ0 ++ x ++ x0) ++ A → C :: Γ5 ++ B → C :: Γ7, D). repeat split. 2: right.
              pose (OrImpLRule_I A B C D (Γ0 ++ x ++ x0) Γ5 Γ7). repeat (simpl ; rewrite <- app_assoc) ;  repeat (simpl in o ; rewrite <- app_assoc in o) ; auto.
              exists (Γ0 ++ x0 ++ A → C :: (Γ5 ++ x) ++ B → C :: Γ7, D). repeat split ; simpl.
              pose (list_exch_LI Γ0 (A → C :: Γ5 ++ x ++ [B → C]) [] x0 Γ7 D). repeat (simpl ; rewrite <- app_assoc ; simpl) ; repeat (simpl in l ; rewrite <- app_assoc in l ; simpl in l) ; auto.
              pose (list_exch_LI Γ0 (x0 ++ A → C :: Γ5) [] x (B → C :: Γ7) D). repeat (simpl ; rewrite <- app_assoc ; simpl) ; repeat (simpl in l ; rewrite <- app_assoc in l ; simpl in l) ; auto. } }
    + inversion e0. subst. apply app2_find_hole in H1. destruct H1. repeat destruct s ; destruct p ; subst.
      { exists ((Γ0 ++ Γ6 ++ Γ5) ++ A → C :: Γ1 ++ B → C :: Γ7, D). repeat split. 2: left.
        pose (OrImpLRule_I A B C D (Γ0 ++ Γ6 ++ Γ5) Γ1 Γ7). repeat (simpl ; rewrite <- app_assoc) ; repeat (simpl in o ; repeat rewrite <- app_assoc in o) ; auto.
        pose (list_exch_LI Γ0 (A → C :: Γ1 ++ [B → C]) Γ5 Γ6 Γ7 D). repeat rewrite <- app_assoc ; simpl ; repeat (repeat rewrite <- app_assoc in l ; simpl in l) ; auto. }
      { exists ((Γ0 ++ Γ6 ++ Γ5) ++ A → C :: Γ1 ++ B → C :: x ++ Γ7, D). repeat split. 2: left.
        pose (OrImpLRule_I A B C D (Γ0 ++ Γ6 ++ Γ5) Γ1 (x ++ Γ7)). repeat (simpl ; rewrite <- app_assoc) ; repeat (simpl in o ; repeat rewrite <- app_assoc in o) ; auto.
        pose (list_exch_LI Γ0 (A → C :: Γ1 ++ B → C :: x) Γ5 Γ6 Γ7 D). repeat rewrite <- app_assoc ; simpl ; repeat (repeat rewrite <- app_assoc in l ; simpl in l) ; auto. }
      {  apply app2_find_hole in e1. destruct e1. repeat destruct s ; destruct p ; subst.
        - exists ((Γ0 ++ Γ6 ++ Γ5) ++ A → C :: Γ4 ++ B → C :: Γ7, D). repeat split. 2: right.
          pose (OrImpLRule_I A B C D (Γ0 ++ Γ6 ++ Γ5) Γ4 Γ7). repeat (simpl ; rewrite <- app_assoc) ;  repeat (simpl in o ; rewrite <- app_assoc in o) ; auto.
          exists (Γ0 ++ [] ++ Γ5 ++ (A → C :: Γ4) ++ B → C :: Γ6 ++ Γ7, D). repeat split ; simpl.
          pose (list_exch_LI Γ0 (A → C :: Γ4) [] Γ5 (B → C :: Γ6 ++ Γ7) D). repeat (simpl ; rewrite <- app_assoc ; simpl) ; repeat (simpl in l ; rewrite <- app_assoc in l ; simpl in l) ; auto.
          pose (list_exch_LI Γ0 (Γ5 ++ A → C :: Γ4 ++ [B → C]) [] Γ6 Γ7 D). repeat (simpl ; rewrite <- app_assoc ; simpl) ; repeat (simpl in l ; rewrite <- app_assoc in l ; simpl in l) ; auto.
        - apply app2_find_hole in e1. destruct e1. repeat destruct s ; destruct p ; subst.
          * exists ((Γ0 ++ Γ6 ++ Γ5) ++ A → C :: Γ4 ++ B → C :: Γ7, D). repeat split. 2: left.
            pose (OrImpLRule_I A B C D (Γ0 ++ Γ6 ++ Γ5) Γ4 Γ7). repeat (simpl ; rewrite <- app_assoc) ; repeat (simpl in o ; repeat rewrite <- app_assoc in o) ; auto.
            pose (list_exch_LI Γ0 (A → C :: Γ4) Γ5 Γ6 (B → C :: Γ7) D). repeat rewrite <- app_assoc ; simpl ; repeat (repeat rewrite <- app_assoc in l ; simpl in l) ; auto.
          * exists ((Γ0 ++ Γ6 ++ Γ5) ++ A → C :: (Γ4 ++ x) ++ B → C :: Γ2, D). repeat split. 2: left.
            pose (OrImpLRule_I A B C D (Γ0 ++ Γ6 ++ Γ5) (Γ4 ++ x) Γ2). repeat (simpl ; rewrite <- app_assoc) ; repeat (simpl in o ; repeat rewrite <- app_assoc in o) ; auto.
            pose (list_exch_LI Γ0 (A → C :: Γ4) Γ5 Γ6 (x ++ B → C :: Γ2) D). repeat rewrite <- app_assoc ; simpl ; repeat (repeat rewrite <- app_assoc in l ; simpl in l) ; auto.
          * exists ((Γ0 ++ x0 ++ x ++ Γ5) ++ A → C :: Γ4 ++ B → C :: Γ7, D). repeat split. 2: right.
            pose (OrImpLRule_I A B C D (Γ0 ++ x0 ++ x ++ Γ5) Γ4 Γ7). repeat (simpl ; rewrite <- app_assoc) ;  repeat (simpl in o ; rewrite <- app_assoc in o) ; auto.
            exists (Γ0 ++ x0 ++ Γ5 ++ (A → C :: Γ4) ++ B → C :: x ++ Γ7, D). repeat split ; simpl.
            pose (list_exch_LI Γ0 (A → C :: Γ4) Γ5 x0 (B → C :: x ++ Γ7) D). repeat (simpl ; rewrite <- app_assoc ; simpl) ; repeat (simpl in l ; rewrite <- app_assoc in l ; simpl in l) ; auto.
            pose (list_exch_LI (Γ0 ++ x0) [] (Γ5 ++ A → C :: Γ4 ++ [B → C]) x Γ7 D). repeat (simpl ; rewrite <- app_assoc ; simpl) ; repeat (simpl in l ; rewrite <- app_assoc in l ; simpl in l) ; auto.
        - exists ((Γ0 ++ Γ6 ++ x ++ x0) ++ A → C :: Γ4 ++ B → C :: Γ7, D). repeat split. 2: right.
          pose (OrImpLRule_I A B C D (Γ0 ++ Γ6 ++ x ++ x0) Γ4 Γ7). repeat (simpl ; rewrite <- app_assoc) ;  repeat (simpl in o ; rewrite <- app_assoc in o) ; auto.
          exists (Γ0 ++ Γ6 ++ (x ++ B → C :: x0) ++ (A → C :: Γ4) ++ Γ7, D). repeat split ; simpl.
          pose (list_exch_LI Γ0 (A → C :: Γ4) (x ++ B → C :: x0) Γ6 Γ7 D). repeat (simpl ; rewrite <- app_assoc ; simpl) ; repeat (simpl in l ; rewrite <- app_assoc in l ; simpl in l) ; auto.
          pose (list_exch_LI (Γ0 ++ Γ6 ++ x) [B → C] (x0 ++ A → C :: Γ4) [] Γ7 D). repeat (simpl ; rewrite <- app_assoc ; simpl) ; repeat (simpl in l ; rewrite <- app_assoc in l ; simpl in l) ; auto. }
  * inversion e0 ; subst. apply app2_find_hole in H1. destruct H1. repeat destruct s ; destruct p ; subst.
    + exists (Γ0 ++ A → C :: (Γ1 ++ Γ6 ++ Γ5) ++ B → C :: Γ4 ++ Γ7, D). repeat split. 2: left.
        pose (OrImpLRule_I A B C D Γ0 (Γ1 ++ Γ6 ++ Γ5) (Γ4 ++ Γ7)). repeat (simpl ; rewrite <- app_assoc) ; repeat (simpl in o ; repeat rewrite <- app_assoc in o) ; auto.
        pose (list_exch_LI (Γ0 ++ A → C :: Γ1) (B → C :: Γ4) Γ5 Γ6 Γ7 D). repeat rewrite <- app_assoc ; simpl ; repeat (repeat rewrite <- app_assoc in l ; simpl in l) ; auto.
    + exists (Γ0 ++ A → C :: Γ1 ++ B → C :: x0 ++ Γ6 ++ Γ5 ++ Γ4 ++ Γ7, D). repeat split. repeat rewrite <- app_assoc. apply OrImpLRule_I. left.
        pose (list_exch_LI (Γ0 ++ A → C :: Γ1 ++ B → C :: x0) Γ4 Γ5 Γ6 Γ7 D). repeat rewrite <- app_assoc ; simpl ; repeat (repeat rewrite <- app_assoc in l ; simpl in l) ; auto.
    + apply app2_find_hole in e1. destruct e1. repeat destruct s ; destruct p ; subst.
      { exists (Γ0 ++ A → C :: (x ++ Γ6) ++ B → C :: Γ5 ++ Γ4 ++ Γ7, D). repeat split. 2: left.
        pose (OrImpLRule_I A B C D Γ0 (x ++ Γ6) (Γ5 ++ Γ4 ++ Γ7)). repeat (simpl ; rewrite <- app_assoc) ; repeat (simpl in o ; repeat rewrite <- app_assoc in o) ; auto.
        pose (list_exch_LI (Γ0 ++ A → C :: x) Γ4 (B → C :: Γ5) Γ6 Γ7 D). repeat rewrite <- app_assoc ; simpl ; repeat (repeat rewrite <- app_assoc in l ; simpl in l) ; auto. }
      { apply app2_find_hole in e1. destruct e1. repeat destruct s ; destruct p ; subst.
        - exists (Γ0 ++ A → C :: (x ++ Γ6 ++ Γ5) ++ B → C :: Γ4 ++ Γ7, D). repeat split. 2: left.
          pose (OrImpLRule_I A B C D Γ0 (x ++ Γ6 ++ Γ5) (Γ4 ++ Γ7)). repeat (simpl ; rewrite <- app_assoc) ; repeat (simpl in o ; repeat rewrite <- app_assoc in o) ; auto.
          pose (list_exch_LI (Γ0 ++ A → C :: x) Γ4 (Γ5 ++ [B → C]) Γ6 Γ7 D). repeat rewrite <- app_assoc ; simpl ; repeat (repeat rewrite <- app_assoc in l ; simpl in l) ; auto.
        - apply app2_find_hole in e1. destruct e1. repeat destruct s ; destruct p ; subst.
          + exists (Γ0 ++ A → C :: (x ++ Γ6 ++ Γ5 ++ Γ4) ++ B → C :: Γ7, D). repeat split. 2: left.
              pose (OrImpLRule_I A B C D Γ0 (x ++ Γ6 ++ Γ5 ++ Γ4) Γ7). repeat (simpl ; rewrite <- app_assoc) ; repeat (simpl in o ; repeat rewrite <- app_assoc in o) ; auto.
              pose (list_exch_LI (Γ0 ++ A → C :: x) Γ4 Γ5 Γ6 (B → C :: Γ7) D). repeat rewrite <- app_assoc ; simpl ; repeat (repeat rewrite <- app_assoc in l ; simpl in l) ; auto.
          + exists (Γ0 ++ A → C :: (x ++ Γ6 ++ Γ5 ++ Γ4 ++ x1) ++ B → C :: Γ2, D). repeat split. 2: left.
              pose (OrImpLRule_I A B C D Γ0 (x ++ Γ6 ++ Γ5 ++ Γ4 ++ x1) Γ2). repeat (simpl ; rewrite <- app_assoc) ; repeat (simpl in o ; repeat rewrite <- app_assoc in o) ; auto.
              pose (list_exch_LI (Γ0 ++ A → C :: x) Γ4 Γ5 Γ6 (x1 ++ B → C :: Γ2) D). repeat rewrite <- app_assoc ; simpl ; repeat (repeat rewrite <- app_assoc in l ; simpl in l) ; auto.
          + exists (Γ0 ++ A → C :: (x ++ x0) ++ B → C :: x1 ++ Γ5 ++ Γ4 ++ Γ7, D). repeat split. 2: left.
              pose (OrImpLRule_I A B C D Γ0 (x ++ x0) (x1 ++ Γ5 ++ Γ4 ++ Γ7)). repeat (simpl ; rewrite <- app_assoc) ; repeat (simpl in o ; repeat rewrite <- app_assoc in o) ; auto.
              pose (list_exch_LI (Γ0 ++ A → C :: x) Γ4 Γ5 (x0 ++ B → C :: x1) Γ7 D). repeat rewrite <- app_assoc ; simpl ; repeat (repeat rewrite <- app_assoc in l ; simpl in l) ; auto.
        - exists (Γ0 ++ A → C :: (x ++ Γ6 ++ x1) ++ B → C :: x0 ++ Γ4 ++ Γ7, D). repeat split. 2: left.
           pose (OrImpLRule_I A B C D Γ0 (x ++ Γ6 ++ x1) (x0 ++ Γ4 ++ Γ7)). repeat (simpl ; rewrite <- app_assoc) ; repeat (simpl in o ; repeat rewrite <- app_assoc in o) ; auto.
           pose (list_exch_LI (Γ0 ++ A → C :: x) Γ4 (x1 ++ B → C :: x0) Γ6 Γ7 D). repeat rewrite <- app_assoc ; simpl ; repeat (repeat rewrite <- app_assoc in l ; simpl in l) ; auto. }
      { exists (Γ0 ++ A → C :: (x ++ Γ6 ++ Γ5 ++ x0) ++ B → C :: x1 ++ Γ7, D). repeat split. 2: left.
         pose (OrImpLRule_I A B C D Γ0 (x ++ Γ6 ++ Γ5 ++ x0) (x1 ++ Γ7)). repeat (simpl ; rewrite <- app_assoc) ; repeat (simpl in o ; repeat rewrite <- app_assoc in o) ; auto.
         pose (list_exch_LI (Γ0 ++ A → C :: x) (x0 ++ B → C :: x1) Γ5 Γ6 Γ7 D). repeat rewrite <- app_assoc ; simpl ; repeat (repeat rewrite <- app_assoc in l ; simpl in l) ; auto. }
(* STOPPED CLEANING PROOF HERE. *)
- apply app2_find_hole in e0. destruct e0. repeat destruct s ; destruct p ; subst.
  * destruct Γ5.
      + simpl in e0. simpl. destruct Γ6.
        { simpl in e0. subst. simpl. exists ((Γ3 ++ Γ4) ++ A → C :: Γ1 ++ B → C :: Γ2, D). split ;auto.
           assert (Γ3 ++ Γ4 ++ (A ∨ B) → C :: Γ1 ++ Γ2 = (Γ3 ++ Γ4) ++ (A ∨ B) → C :: Γ1 ++ Γ2). repeat rewrite <- app_assoc ; auto.
           rewrite H. apply OrImpLRule_I. left. apply list_exch_L_id. }
        { simpl in e0. inversion e0. subst. simpl. apply app2_find_hole in H1. destruct H1. repeat destruct s ; destruct p ; subst.
          - exists (Γ3 ++ A → C :: (Γ1 ++ Γ4) ++ B → C :: Γ2, D). repeat split.
            assert (Γ3 ++ (A ∨ B) → C :: Γ1 ++ Γ4 ++ Γ2 = Γ3 ++ (A ∨ B) → C :: (Γ1 ++ Γ4) ++ Γ2). repeat rewrite <- app_assoc ; auto.
            rewrite H. apply OrImpLRule_I. left.
            assert ((Γ3 ++ Γ4) ++ A → C :: Γ1 ++ B → C :: Γ2 = Γ3 ++ Γ4 ++ (A → C :: Γ1) ++ [] ++ (B → C :: Γ2)). repeat rewrite <- app_assoc ; auto.
            rewrite H.
            assert (Γ3 ++ A → C :: (Γ1 ++ Γ4) ++ B → C :: Γ2 = Γ3 ++ [] ++ (A → C :: Γ1) ++ Γ4 ++ (B → C :: Γ2)). repeat rewrite <- app_assoc ; auto.
            rewrite H0. apply list_exch_LI.
          - exists (Γ3 ++ A → C :: Γ1 ++ B → C :: x ++ Γ4 ++ Γ7, D). repeat rewrite <- app_assoc. repeat split. left.
            assert (Γ3 ++ Γ4 ++ A → C :: Γ1 ++ B → C :: x ++ Γ7 = Γ3 ++ Γ4 ++ (A → C :: Γ1 ++ B → C :: x) ++ [] ++ Γ7). repeat rewrite <- app_assoc. simpl.
            repeat rewrite <- app_assoc ; auto. rewrite H.
            assert (Γ3 ++ A → C :: Γ1 ++ B → C :: x ++ Γ4 ++ Γ7 = Γ3 ++ [] ++ (A → C :: Γ1 ++ B → C :: x) ++ Γ4 ++ Γ7). repeat rewrite <- app_assoc. simpl.
            repeat rewrite <- app_assoc ; auto. rewrite H0. apply list_exch_LI.
          - exists (Γ3 ++ A → C :: (Γ6 ++ Γ4 ++ x) ++ B → C :: Γ2, D). repeat split.
            assert (Γ3 ++ (A ∨ B) → C :: Γ6 ++ Γ4 ++ x ++ Γ2 = Γ3 ++ (A ∨ B) → C :: (Γ6 ++ Γ4 ++ x) ++ Γ2). repeat rewrite <- app_assoc ; auto.
            rewrite H. apply OrImpLRule_I. left.
            assert ((Γ3 ++ Γ4) ++ A → C :: (Γ6 ++ x) ++ B → C :: Γ2 = Γ3 ++ Γ4 ++ (A → C :: Γ6) ++ [] ++ x ++ B → C :: Γ2). repeat rewrite <- app_assoc. simpl.
            repeat rewrite <- app_assoc ; auto. rewrite H.
            assert (Γ3 ++ A → C :: (Γ6 ++ Γ4 ++ x) ++ B → C :: Γ2 = Γ3 ++ [] ++ (A → C :: Γ6) ++ Γ4 ++ x ++ B → C :: Γ2). repeat rewrite <- app_assoc. simpl.
            repeat rewrite <- app_assoc ; auto. rewrite H0. apply list_exch_LI. }
      + simpl in e0. inversion e0. subst. apply app2_find_hole in H1. destruct H1. repeat destruct s ; destruct p ; subst.
        { exists ((Γ3 ++ Γ6) ++ A→ C :: Γ1 ++ B→ C :: Γ4 ++ Γ7, D) . repeat split. 2: left.
          assert (Γ3 ++ Γ6 ++ ((A ∨ B) → C :: Γ1) ++  Γ4 ++ Γ7 = (Γ3 ++ Γ6) ++ (A ∨ B) → C :: Γ1 ++  Γ4 ++ Γ7). repeat rewrite <- app_assoc. auto. rewrite H.
          apply OrImpLRule_I.
          assert ((Γ3 ++ Γ4) ++  A → C :: Γ1 ++ B → C :: Γ6 ++  Γ7 = Γ3 ++ Γ4 ++ (A → C :: Γ1 ++ [B → C]) ++ Γ6 ++  Γ7). repeat rewrite <- app_assoc.
          simpl. repeat rewrite <- app_assoc. auto. rewrite H.
          assert ((Γ3 ++ Γ6) ++ A → C :: Γ1 ++ B → C ::  Γ4 ++ Γ7 = Γ3 ++ Γ6 ++ (A → C :: Γ1 ++ [B → C]) ++ Γ4 ++  Γ7). repeat rewrite <- app_assoc.
          simpl. repeat rewrite <- app_assoc. auto. rewrite H0.
          apply list_exch_LI. }
        { exists ((Γ3 ++  Γ6) ++ A→ C ::  Γ1 ++ B→ C :: x ++ Γ4 ++ Γ7, D). split. 2: left.
          assert (Γ3 ++  Γ6 ++ ((A ∨ B) → C ::  Γ1 ++  x) ++ Γ4 ++ Γ7 = (Γ3 ++  Γ6) ++ (A ∨ B) → C ::  Γ1 ++ x ++ Γ4 ++ Γ7). repeat rewrite <- app_assoc. auto.
          simpl. repeat rewrite <- app_assoc. auto. rewrite H. apply OrImpLRule_I.
          assert ((Γ3 ++ Γ4) ++ A → C :: Γ1 ++ B → C :: x ++ Γ6 ++ Γ7 = Γ3 ++ Γ4 ++ (A → C ::  Γ1 ++  B → C :: x) ++  Γ6 ++ Γ7).
          repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
          assert ((Γ3 ++ Γ6) ++ A → C :: Γ1 ++ B → C :: x ++ Γ4 ++ Γ7 = Γ3 ++ Γ6 ++ (A → C ::  Γ1 ++  B → C :: x) ++ Γ4 ++ Γ7).
          repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI. }
        { apply app2_find_hole in e1. destruct e1. repeat destruct s ; destruct p ; subst.
          - exists ((Γ3 ++ Γ6) ++ A → C :: (Γ5 ++ Γ4) ++ B → C :: Γ7, D). repeat split.
            assert (Γ3 ++ Γ6 ++ ((A ∨ B) → C :: Γ5) ++ Γ4 ++ Γ7 = (Γ3 ++ Γ6) ++ (A ∨ B) → C :: (Γ5 ++ Γ4) ++ Γ7). repeat rewrite <- app_assoc. auto.
            rewrite H. apply OrImpLRule_I. left.
            assert ((Γ3 ++ Γ4) ++ A → C :: (Γ5 ++ Γ6) ++ B → C :: Γ7 = Γ3 ++ Γ4 ++ (A → C :: Γ5) ++ Γ6 ++ B → C :: Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert ((Γ3 ++ Γ6) ++ A → C :: (Γ5 ++ Γ4) ++ B → C :: Γ7 = Γ3 ++ Γ6 ++ (A → C :: Γ5) ++ Γ4 ++ B → C :: Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
          - exists ((Γ3 ++ Γ6) ++ A → C :: (Γ5 ++ Γ4 ++ x1) ++ B → C :: Γ2, D). repeat split.
            assert (Γ3 ++ Γ6 ++ ((A ∨ B) → C :: Γ5) ++ Γ4 ++ x1 ++ Γ2 = (Γ3 ++ Γ6) ++ (A ∨ B) → C :: (Γ5 ++ Γ4 ++ x1) ++ Γ2). repeat rewrite <- app_assoc. auto.
            rewrite H. apply OrImpLRule_I. left.
            assert ((Γ3 ++ Γ4) ++ A → C :: (Γ5 ++ Γ6 ++ x1) ++ B → C :: Γ2 = Γ3 ++ Γ4 ++ (A → C :: Γ5) ++ Γ6 ++ x1 ++ B → C :: Γ2).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert ((Γ3 ++ Γ6) ++ A → C :: (Γ5 ++ Γ4 ++ x1) ++ B → C :: Γ2 = Γ3 ++ Γ6 ++ (A → C :: Γ5) ++ Γ4 ++ x1 ++ B → C :: Γ2).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
          - exists ((Γ3 ++ x ++ x1) ++ A → C :: Γ5 ++ B → C :: Γ4 ++ Γ7, D). repeat split.
            assert (Γ3 ++ (x ++ x1) ++ ((A ∨ B) → C :: Γ5) ++ Γ4 ++ Γ7 = (Γ3 ++ x ++ x1) ++ (A ∨ B) → C :: Γ5 ++ Γ4 ++ Γ7). repeat rewrite <- app_assoc. auto.
            rewrite H. apply OrImpLRule_I. right. exists (Γ3 ++ (x ++ B → C :: x1) ++ (A → C :: Γ5) ++ Γ4 ++ Γ7, D). split.
            assert ((Γ3 ++ Γ4) ++ A → C :: (Γ5 ++ x) ++ B → C :: x1 ++ Γ7 = Γ3 ++ Γ4 ++ (A → C :: Γ5) ++ (x ++ B → C :: x1) ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H. apply list_exch_LI.
            assert (Γ3 ++ (x ++ B → C :: x1) ++ (A → C :: Γ5) ++ Γ4 ++ Γ7 = (Γ3 ++ x) ++ [B → C] ++ (x1 ++ A → C :: Γ5) ++ [] ++ Γ4 ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert ((Γ3 ++ x ++ x1) ++ A → C :: Γ5 ++ B → C :: Γ4 ++ Γ7 = (Γ3 ++ x) ++ [] ++ (x1 ++ A → C :: Γ5) ++ [B → C] ++ Γ4 ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0.  apply list_exch_LI. }
  * apply app2_find_hole in e0. destruct e0. repeat destruct s ; destruct p ; subst.
      + simpl in e0. simpl. destruct Γ6.
          { simpl in e0. subst. simpl. exists ((Γ3 ++ Γ5 ++ Γ4) ++ A → C :: Γ1 ++ B → C :: Γ2, D). split ;auto.
             assert (Γ3 ++ Γ5 ++ Γ4 ++ (A ∨ B) → C :: Γ1 ++ Γ2 = (Γ3 ++ Γ5 ++ Γ4) ++ (A ∨ B) → C :: Γ1 ++ Γ2). repeat rewrite <- app_assoc ; auto.
             rewrite H. apply OrImpLRule_I. left.
             assert ((Γ3 ++ Γ4 ++ Γ5) ++ A → C :: Γ1 ++ B → C :: Γ2 = Γ3 ++ Γ4 ++ [] ++ Γ5 ++ A → C :: Γ1 ++ B → C :: Γ2). repeat rewrite <- app_assoc ; auto.
             rewrite H.
             assert ((Γ3 ++ Γ5 ++ Γ4) ++ A → C :: Γ1 ++ B → C :: Γ2 = Γ3 ++ Γ5 ++ [] ++ Γ4 ++ A → C :: Γ1 ++ B → C :: Γ2). repeat rewrite <- app_assoc ; auto.
             rewrite H0. apply list_exch_LI. }
          { simpl in e0. inversion e0. subst. simpl. apply app2_find_hole in H1. destruct H1. repeat destruct s ; destruct p ; subst.
            - exists (Γ3 ++ A → C :: (Γ1 ++ Γ5 ++ Γ4) ++ B → C :: Γ2, D). repeat split.
              assert (Γ3 ++ (A ∨ B) → C :: Γ1 ++ Γ5 ++ Γ4 ++ Γ2 = Γ3 ++ (A ∨ B) → C :: (Γ1 ++ Γ5 ++ Γ4) ++ Γ2). repeat rewrite <- app_assoc ; auto.
              rewrite H. apply OrImpLRule_I. left.
              assert ((Γ3 ++ Γ4 ++ Γ5) ++ A → C :: Γ1 ++ B → C :: Γ2 = Γ3 ++ Γ4 ++ Γ5 ++ (A → C :: Γ1) ++ (B → C :: Γ2)). repeat rewrite <- app_assoc ; auto.
              rewrite H.
              assert (Γ3 ++ A → C :: (Γ1 ++ Γ5 ++ Γ4) ++ B → C :: Γ2 = Γ3 ++ (A → C :: Γ1) ++ Γ5 ++ Γ4 ++ (B → C :: Γ2)). repeat rewrite <- app_assoc ; auto.
              rewrite H0. apply list_exch_LI.
            - exists (Γ3 ++ A → C :: Γ1 ++ B → C :: x0 ++ Γ5 ++ Γ4 ++ Γ7, D). repeat rewrite <- app_assoc. repeat split. left.
              assert (Γ3 ++ Γ4 ++ Γ5 ++ A → C :: Γ1 ++ B → C :: x0 ++ Γ7 = Γ3 ++ Γ4 ++ Γ5 ++ (A → C :: Γ1 ++ B → C :: x0) ++ Γ7). repeat rewrite <- app_assoc. simpl.
              repeat rewrite <- app_assoc ; auto. rewrite H.
              assert (Γ3 ++ A → C :: Γ1 ++ B → C :: x0 ++ Γ5 ++ Γ4 ++ Γ7 = Γ3 ++ (A → C :: Γ1 ++ B → C :: x0) ++ Γ5 ++ Γ4 ++ Γ7). repeat rewrite <- app_assoc. simpl.
              repeat rewrite <- app_assoc ; auto. rewrite H0. apply list_exch_LI.
            - exists (Γ3 ++ A → C :: (Γ6 ++ Γ5 ++ Γ4 ++ x0) ++ B → C :: Γ2, D). repeat split.
              assert (Γ3 ++ (A ∨ B) → C :: Γ6 ++ Γ5 ++ Γ4 ++ x0 ++ Γ2 = Γ3 ++ (A ∨ B) → C :: (Γ6 ++ Γ5 ++ Γ4 ++ x0) ++ Γ2). repeat rewrite <- app_assoc ; auto.
              rewrite H. apply OrImpLRule_I. left.
              assert ((Γ3 ++ Γ4 ++ Γ5) ++ A → C :: (Γ6 ++ x0) ++ B → C :: Γ2 = Γ3 ++ Γ4 ++ Γ5 ++ (A → C :: Γ6) ++ x0 ++ B → C :: Γ2). repeat rewrite <- app_assoc. simpl.
              repeat rewrite <- app_assoc ; auto. rewrite H.
              assert (Γ3 ++ A → C :: (Γ6 ++ Γ5 ++ Γ4 ++ x0) ++ B → C :: Γ2 = Γ3 ++ (A → C :: Γ6) ++ Γ5 ++ Γ4 ++ x0 ++ B → C :: Γ2). repeat rewrite <- app_assoc. simpl.
              repeat rewrite <- app_assoc ; auto. rewrite H0. apply list_exch_LI. }
      + subst. apply app2_find_hole in e0. destruct e0. repeat destruct s ; destruct p ; subst.
          { exists ((Γ3 ++ Γ6 ++ Γ5 ++ Γ4) ++ A → C :: Γ1 ++ B → C :: Γ2, D) . repeat split. 2: left.
            assert (Γ3 ++ Γ6 ++ Γ5 ++ Γ4 ++ (A ∨ B) → C :: Γ1 ++ Γ2 = (Γ3 ++ Γ6 ++ Γ5 ++ Γ4) ++ (A ∨ B) → C :: Γ1 ++ Γ2). repeat rewrite <- app_assoc. auto. rewrite H.
            apply OrImpLRule_I. repeat rewrite <- app_assoc ; apply list_exch_LI. }
          { exists ((Γ3 ++ Γ6 ++ Γ5 ++ Γ4 ++ x0) ++ A → C :: Γ1 ++ B → C :: Γ2, D). split. 2: left.
            assert (Γ3 ++ Γ6 ++ Γ5 ++ Γ4 ++ x0 ++ (A ∨ B) → C :: Γ1 ++ Γ2 = (Γ3 ++ Γ6 ++ Γ5 ++ Γ4 ++ x0) ++ (A ∨ B) → C :: Γ1 ++ Γ2). repeat rewrite <- app_assoc. auto.
            rewrite H. apply OrImpLRule_I. repeat rewrite <- app_assoc ; apply list_exch_LI. }
          { destruct x0 ; simpl in e0 ; inversion e0 ; subst.
            - repeat rewrite <- app_assoc ; simpl. exists ((Γ3 ++ x ++ Γ5 ++ Γ4) ++ A → C :: Γ1 ++ B → C :: Γ2, D). repeat split.
              assert (Γ3 ++ x ++ Γ5 ++ Γ4 ++ (A ∨ B) → C :: Γ1 ++ Γ2 = (Γ3 ++ x ++ Γ5 ++ Γ4) ++ (A ∨ B) → C :: Γ1 ++ Γ2). repeat rewrite <- app_assoc. auto.
              rewrite H0. apply OrImpLRule_I. left. repeat rewrite <- app_assoc ; apply list_exch_LI.
            - apply app2_find_hole in H1. destruct H1. repeat destruct s ; destruct p ; subst.
              + exists((Γ3 ++ x) ++ A → C :: (Γ1 ++ Γ5 ++ Γ4) ++ B → C :: Γ2, D). repeat split.
                  assert (Γ3 ++ (x ++ (A ∨ B) → C :: Γ1) ++ Γ5 ++ Γ4 ++ Γ2 = (Γ3 ++ x) ++ (A ∨ B) → C :: (Γ1 ++ Γ5 ++ Γ4) ++ Γ2). repeat rewrite <- app_assoc. auto.
                  rewrite H. apply OrImpLRule_I. left.
                  assert ((Γ3 ++ Γ4 ++ Γ5 ++ x) ++ A → C :: Γ1 ++ B → C :: Γ2 = Γ3 ++ Γ4 ++ Γ5 ++ (x ++ A → C :: Γ1) ++ B → C :: Γ2).
                  repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                  assert ((Γ3 ++ x) ++ A → C :: (Γ1 ++ Γ5 ++ Γ4) ++ B → C :: Γ2 = Γ3 ++ (x ++ A → C :: Γ1) ++ Γ5 ++ Γ4 ++ B → C :: Γ2).
                  repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0.  apply list_exch_LI.
              + exists ((Γ3 ++ x) ++ A → C :: Γ1 ++ B → C :: x1 ++ Γ5 ++ Γ4 ++ Γ7, D). repeat split.
                  assert (Γ3 ++ (x ++ (A ∨ B) → C :: Γ1 ++ x1) ++ Γ5 ++ Γ4 ++ Γ7 = (Γ3 ++ x) ++ (A ∨ B) → C :: Γ1 ++ x1 ++ Γ5 ++ Γ4 ++ Γ7). repeat rewrite <- app_assoc. auto.
                  simpl. repeat rewrite <- app_assoc. auto. rewrite H. apply OrImpLRule_I. left.
                  assert ((Γ3 ++ Γ4 ++ Γ5 ++ x) ++ A → C :: Γ1 ++ B → C :: x1 ++ Γ7 = Γ3 ++ Γ4 ++ Γ5 ++ (x ++ A → C :: Γ1 ++ B → C :: x1) ++ Γ7).
                  repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                  assert ((Γ3 ++ x) ++ A → C :: Γ1 ++ B → C :: x1 ++ Γ5 ++ Γ4 ++ Γ7 = Γ3 ++ (x ++ A → C :: Γ1 ++ B → C :: x1) ++ Γ5 ++ Γ4 ++ Γ7).
                  repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0.  apply list_exch_LI.
              + exists ((Γ3 ++ x) ++ A → C :: (x0 ++ Γ5 ++ Γ4 ++ x1) ++ B → C :: Γ2, D). repeat split.
                  assert (Γ3 ++ (x ++ (A ∨ B) → C :: x0) ++ Γ5 ++ Γ4 ++ x1 ++ Γ2 = (Γ3 ++ x) ++ (A ∨ B) → C :: (x0 ++ Γ5 ++ Γ4 ++ x1) ++ Γ2). repeat rewrite <- app_assoc. auto.
                  rewrite H. apply OrImpLRule_I. left.
                  assert ((Γ3 ++ Γ4 ++ Γ5 ++ x) ++ A → C :: (x0 ++ x1) ++ B → C :: Γ2 = Γ3 ++ Γ4 ++ Γ5 ++ (x ++ A → C :: x0) ++ x1 ++ B → C :: Γ2).
                  repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                  assert ((Γ3 ++ x) ++ A → C :: (x0 ++ Γ5 ++ Γ4 ++ x1) ++ B → C :: Γ2 = Γ3 ++ (x ++ A → C :: x0) ++ Γ5 ++ Γ4 ++ x1 ++ B → C :: Γ2).
                  repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0.  apply list_exch_LI. }
      + destruct x ; simpl in e0 ; inversion e0 ; subst.
          { destruct Γ6.
            - simpl in e0. subst. simpl in H0. simpl. repeat rewrite <- app_assoc. simpl.
               exists ((Γ3 ++ x0 ++ Γ4) ++ A → C :: Γ1 ++ B → C :: Γ2, D). split ;auto.
               assert (Γ3 ++ x0 ++ Γ4 ++ (A ∨ B) → C :: Γ1 ++ Γ2 = (Γ3 ++ x0 ++ Γ4) ++ (A ∨ B) → C :: Γ1 ++ Γ2). repeat rewrite <- app_assoc ; auto.
               rewrite H. apply OrImpLRule_I. left.
               assert (Γ3 ++ Γ4 ++ x0 ++ A → C :: Γ1 ++ B → C :: Γ2 = Γ3 ++ Γ4 ++ [] ++ x0 ++ A → C :: Γ1 ++ B → C :: Γ2). repeat rewrite <- app_assoc ; auto.
               rewrite H.
               assert ((Γ3 ++ x0 ++ Γ4) ++ A → C :: Γ1 ++ B → C :: Γ2 = Γ3 ++ x0 ++ [] ++ Γ4 ++ A → C :: Γ1 ++ B → C :: Γ2). repeat rewrite <- app_assoc ; auto.
               rewrite H1. apply list_exch_LI.
            - simpl in e0. inversion e0. clear H0. subst. simpl. repeat rewrite <- app_assoc. simpl.
              apply app2_find_hole in H2. destruct H2. repeat destruct s ; destruct p ; subst.
              + exists (Γ3 ++ A → C :: (Γ1 ++ x0 ++ Γ4) ++ B → C :: Γ2, D). repeat split.
                assert (Γ3 ++ (A ∨ B) → C :: Γ1 ++ x0 ++ Γ4 ++ Γ2 = Γ3 ++ (A ∨ B) → C :: (Γ1 ++ x0 ++ Γ4) ++ Γ2). repeat rewrite <- app_assoc ; auto.
                rewrite H. apply OrImpLRule_I. left.
                assert (Γ3 ++ Γ4 ++ x0 ++ A → C :: Γ1 ++ B → C :: Γ2 = Γ3 ++ Γ4 ++ x0 ++ (A → C :: Γ1) ++ (B → C :: Γ2)). repeat rewrite <- app_assoc ; auto.
                rewrite H.
                assert (Γ3 ++ A → C :: (Γ1 ++ x0 ++ Γ4) ++ B → C :: Γ2 = Γ3 ++ (A → C :: Γ1) ++ x0 ++ Γ4 ++ (B → C :: Γ2)). repeat rewrite <- app_assoc ; auto.
                rewrite H0. apply list_exch_LI.
              + exists (Γ3 ++ A → C :: Γ1 ++ B → C :: x ++ x0 ++ Γ4 ++ Γ7, D). repeat rewrite <- app_assoc. repeat split. left.
                assert (Γ3 ++ Γ4 ++ x0 ++ A → C :: Γ1 ++ B → C :: x ++ Γ7 = Γ3 ++ Γ4 ++ x0 ++ (A → C :: Γ1 ++ B → C :: x) ++ Γ7). repeat rewrite <- app_assoc. simpl.
                repeat rewrite <- app_assoc ; auto. rewrite H.
                assert (Γ3 ++ A → C :: Γ1 ++ B → C :: x ++ x0 ++ Γ4 ++ Γ7 = Γ3 ++ (A → C :: Γ1 ++ B → C :: x) ++ x0 ++ Γ4 ++ Γ7). repeat rewrite <- app_assoc. simpl.
                repeat rewrite <- app_assoc ; auto. rewrite H0. apply list_exch_LI.
              + exists (Γ3 ++ A → C :: (Γ6 ++ x0 ++ Γ4 ++ x) ++ B → C :: Γ2, D). repeat split.
                assert (Γ3 ++ (A ∨ B) → C :: Γ6 ++ x0 ++ Γ4 ++ x ++ Γ2 = Γ3 ++ (A ∨ B) → C :: (Γ6 ++ x0 ++ Γ4 ++ x) ++ Γ2). repeat rewrite <- app_assoc ; auto.
                rewrite H. apply OrImpLRule_I. left.
                assert (Γ3 ++ Γ4 ++ x0 ++ A → C :: (Γ6 ++ x) ++ B → C :: Γ2 = Γ3 ++ Γ4 ++ x0 ++ (A → C :: Γ6) ++ x ++ B → C :: Γ2). repeat rewrite <- app_assoc. simpl.
                repeat rewrite <- app_assoc ; auto. rewrite H.
                assert (Γ3 ++ A → C :: (Γ6 ++ x0 ++ Γ4 ++ x) ++ B → C :: Γ2 = Γ3 ++ (A → C :: Γ6) ++ x0 ++ Γ4 ++ x ++ B → C :: Γ2). repeat rewrite <- app_assoc. simpl.
                repeat rewrite <- app_assoc ; auto. rewrite H0. apply list_exch_LI. }
        { apply app2_find_hole in H1. destruct H1. repeat destruct s ; destruct p ; subst.
          - exists ((Γ3 ++ Γ6 ++ x0) ++ A → C :: Γ1 ++ B → C :: Γ4 ++ Γ7, D). split ;auto.
             assert (Γ3 ++ Γ6 ++ (x0 ++ (A ∨ B) → C :: Γ1) ++ Γ4 ++ Γ7 = (Γ3 ++ Γ6 ++ x0) ++ (A ∨ B) → C :: Γ1 ++ Γ4 ++ Γ7). repeat rewrite <- app_assoc ; auto.
             rewrite H. apply OrImpLRule_I. left.
             assert ((Γ3 ++ Γ4 ++ x0) ++ A → C :: Γ1 ++ B → C :: Γ6 ++ Γ7 = Γ3 ++ Γ4 ++ (x0 ++ A → C :: Γ1 ++ [B → C]) ++ Γ6 ++ Γ7). repeat rewrite <- app_assoc ; simpl.
             repeat rewrite <- app_assoc ; auto. rewrite H.
             assert ((Γ3 ++ Γ6 ++ x0) ++ A → C :: Γ1 ++ B → C :: Γ4 ++ Γ7 = Γ3 ++ Γ6 ++ (x0 ++ A → C :: Γ1 ++ [B → C]) ++ Γ4 ++ Γ7). repeat rewrite <- app_assoc ; simpl.
             repeat rewrite <- app_assoc ; auto. rewrite H0. apply list_exch_LI.
          - exists ((Γ3 ++ Γ6 ++ x0) ++ A → C :: Γ1 ++ B → C :: x1 ++ Γ4 ++ Γ7, D). split ;auto.
             assert (Γ3 ++ Γ6 ++ (x0 ++ (A ∨ B) → C :: Γ1 ++ x1) ++ Γ4 ++ Γ7 = (Γ3 ++ Γ6 ++ x0) ++ (A ∨ B) → C :: Γ1 ++ x1 ++ Γ4 ++ Γ7). repeat rewrite <- app_assoc ; simpl.
             repeat rewrite <- app_assoc ; auto. rewrite H. apply OrImpLRule_I. left.
             assert ((Γ3 ++ Γ4 ++ x0) ++ A → C :: Γ1 ++ B → C :: x1 ++ Γ6 ++ Γ7 = Γ3 ++ Γ4 ++ (x0 ++ A → C :: Γ1 ++ B → C :: x1) ++ Γ6 ++ Γ7). repeat rewrite <- app_assoc ; simpl.
             repeat rewrite <- app_assoc ; auto. rewrite H.
             assert ((Γ3 ++ Γ6 ++ x0) ++ A → C :: Γ1 ++ B → C :: x1 ++ Γ4 ++ Γ7 = Γ3 ++ Γ6 ++ (x0 ++ A → C :: Γ1 ++ B → C :: x1) ++ Γ4 ++ Γ7). repeat rewrite <- app_assoc ; simpl.
             repeat rewrite <- app_assoc ; auto. rewrite H0. apply list_exch_LI.
          - apply app2_find_hole in e1. destruct e1. repeat destruct s ; destruct p ; subst.
            + exists ((Γ3 ++ Γ6 ++ x0) ++ A → C :: (x ++ Γ4) ++  B → C :: Γ7, D). split ;auto.
               assert (Γ3 ++ Γ6 ++ (x0 ++ (A ∨ B) → C :: x) ++ Γ4 ++ Γ7 = (Γ3 ++ Γ6 ++ x0) ++ (A ∨ B) → C :: (x ++ Γ4) ++ Γ7). repeat rewrite <- app_assoc ; simpl.
               repeat rewrite <- app_assoc ; auto. rewrite H. apply OrImpLRule_I. left.
               assert ((Γ3 ++ Γ4 ++ x0) ++ A → C :: (x ++ Γ6) ++ B → C :: Γ7 = Γ3 ++ Γ4 ++ (x0 ++ A → C :: x) ++ Γ6 ++ B → C :: Γ7). repeat rewrite <- app_assoc ; simpl.
               repeat rewrite <- app_assoc ; auto. rewrite H.
               assert ((Γ3 ++ Γ6 ++ x0) ++ A → C :: (x ++ Γ4) ++ B → C :: Γ7 = Γ3 ++ Γ6 ++ (x0 ++ A → C :: x) ++ Γ4 ++ B → C :: Γ7). repeat rewrite <- app_assoc ; simpl.
               repeat rewrite <- app_assoc ; auto. rewrite H0. apply list_exch_LI.
            + exists ((Γ3 ++ Γ6 ++ x0) ++ A → C :: (x ++ Γ4 ++ x2) ++  B → C :: Γ2, D). split ;auto.
               assert (Γ3 ++ Γ6 ++ (x0 ++ (A ∨ B) → C :: x) ++ Γ4 ++ x2 ++ Γ2 = (Γ3 ++ Γ6 ++ x0) ++ (A ∨ B) → C :: (x ++ Γ4 ++ x2) ++ Γ2). repeat rewrite <- app_assoc ; simpl.
               repeat rewrite <- app_assoc ; auto. rewrite H. apply OrImpLRule_I. left.
               assert ((Γ3 ++ Γ4 ++ x0) ++ A → C :: (x ++ Γ6 ++ x2) ++ B → C :: Γ2 = Γ3 ++ Γ4 ++ (x0 ++ A → C :: x) ++ Γ6 ++ x2 ++ B → C :: Γ2). repeat rewrite <- app_assoc ; simpl.
               repeat rewrite <- app_assoc ; auto. rewrite H.
               assert ((Γ3 ++ Γ6 ++ x0) ++ A → C :: (x ++ Γ4 ++ x2) ++ B → C :: Γ2 = Γ3 ++ Γ6 ++ (x0 ++ A → C :: x) ++ Γ4 ++ x2 ++ B → C :: Γ2). repeat rewrite <- app_assoc ; simpl.
               repeat rewrite <- app_assoc ; auto. rewrite H0. apply list_exch_LI.
            + exists ((Γ3 ++ x1 ++ x2 ++ x0) ++ A → C :: x ++ B → C :: Γ4 ++ Γ7, D). split ;auto.
               assert (Γ3 ++ (x1 ++ x2) ++ (x0 ++ (A ∨ B) → C :: x) ++ Γ4 ++ Γ7 = (Γ3 ++ x1 ++ x2 ++ x0) ++ (A ∨ B) → C :: x ++ Γ4 ++ Γ7). repeat rewrite <- app_assoc ; simpl.
               repeat rewrite <- app_assoc ; auto. rewrite H. apply OrImpLRule_I. right.
               exists (Γ3 ++ (x1 ++ B → C :: x2) ++ (x0 ++ A → C :: x) ++ Γ4 ++ Γ7, D). split.
               assert ((Γ3 ++ Γ4 ++ x0) ++ A → C :: (x ++ x1) ++ B → C :: x2 ++ Γ7 = Γ3 ++ Γ4 ++ (x0 ++ A → C :: x) ++ (x1 ++ B → C :: x2) ++ Γ7). repeat rewrite <- app_assoc ; simpl.
               repeat rewrite <- app_assoc ; auto. rewrite H. apply list_exch_LI.
               assert (Γ3 ++ (x1 ++ B → C :: x2) ++ (x0 ++ A → C :: x) ++ Γ4 ++ Γ7 = (Γ3 ++ x1) ++ [B → C] ++ (x2 ++ x0 ++ A → C :: x) ++ [] ++ Γ4 ++ Γ7). repeat rewrite <- app_assoc ; simpl.
               repeat rewrite <- app_assoc ; auto. rewrite H.
               assert ((Γ3 ++ x1 ++ x2 ++ x0) ++ A → C :: x ++ B → C :: Γ4 ++ Γ7 = (Γ3 ++ x1) ++ [] ++ (x2 ++ x0 ++ A → C :: x) ++ [B → C] ++ Γ4 ++ Γ7). repeat rewrite <- app_assoc ; simpl.
               repeat rewrite <- app_assoc ; auto. rewrite H0. apply list_exch_LI. }
  * destruct x0 ; simpl in e0 ; inversion e0 ; subst.
      + destruct Γ5 ; simpl in e0 ; inversion e0 ; subst.
          { destruct Γ6.
            - simpl in H1. subst. repeat rewrite <- app_assoc. simpl.
              exists ((Γ3 ++ x) ++ A → C :: Γ1 ++ B → C :: Γ2, D). repeat split.
              assert (Γ3 ++ x ++ (A ∨ B) → C :: Γ1 ++ Γ2 = (Γ3 ++ x) ++ (A ∨ B) → C :: Γ1 ++ Γ2). repeat rewrite <- app_assoc. auto.
              rewrite H. apply OrImpLRule_I. left. repeat rewrite <- app_assoc. apply list_exch_L_id.
            - simpl in H1. inversion H1. subst. apply app2_find_hole in H3. destruct H3. repeat destruct s ; destruct p ; subst.
              * repeat rewrite <- app_assoc. simpl. exists (Γ3 ++ A → C :: Γ1 ++ B → C :: x ++ Γ2, D). repeat split. left.
                assert (Γ3 ++ x ++ A → C :: Γ1 ++ B → C :: Γ2 = Γ3 ++ x ++ (A → C :: Γ1 ++ [B → C]) ++ [] ++ Γ2).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                assert (Γ3 ++ A → C :: Γ1 ++ B → C :: x ++ Γ2 = Γ3 ++ [] ++ (A → C :: Γ1 ++ [B → C]) ++ x ++ Γ2).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H2.  apply list_exch_LI.
              * repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc.
                exists (Γ3 ++ A → C :: Γ1 ++ B → C :: x0 ++ x ++ Γ7, D). repeat split. left.
                assert (Γ3 ++ x ++ A → C :: Γ1 ++ B → C :: x0 ++ Γ7 = Γ3 ++ x ++ (A → C :: Γ1 ++ B → C :: x0) ++ [] ++ Γ7).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                assert (Γ3 ++ A → C :: Γ1 ++ B → C :: x0 ++ x ++ Γ7 = Γ3 ++ [] ++ (A → C :: Γ1 ++ B → C :: x0) ++ x ++ Γ7).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H2.  apply list_exch_LI.
              * repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc.
                exists (Γ3 ++ A → C :: (Γ6 ++ x ++ x0) ++ B → C :: Γ2, D). repeat split.
                assert (Γ3 ++ (A ∨ B) → C :: Γ6 ++ x ++ x0 ++ Γ2 = Γ3 ++ (A ∨ B) → C :: (Γ6 ++ x ++ x0) ++ Γ2). repeat rewrite <- app_assoc ; simpl.
                repeat rewrite <- app_assoc ; auto. rewrite H. apply OrImpLRule_I. left.
                assert (Γ3 ++ x ++ A → C :: Γ6 ++ x0 ++ B → C :: Γ2 = Γ3 ++ x ++ (A → C :: Γ6) ++ [] ++ x0 ++ B → C :: Γ2).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                assert (Γ3 ++ A → C :: (Γ6 ++ x ++ x0) ++ B → C :: Γ2 = Γ3 ++ [] ++ (A → C :: Γ6) ++ x ++ x0 ++ B → C :: Γ2).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H2. apply list_exch_LI. }
          { apply app2_find_hole in H2. destruct H2. repeat destruct s ; destruct p ; subst.
            - repeat rewrite <- app_assoc. simpl. exists ((Γ3 ++ Γ6) ++ A → C :: Γ1 ++ B → C :: x ++ Γ7, D). repeat split.
              assert (Γ3 ++ Γ6 ++ (A ∨ B) → C :: Γ1 ++ x ++ Γ7 = (Γ3 ++ Γ6) ++ (A ∨ B) → C :: Γ1 ++ x ++ Γ7). repeat rewrite <- app_assoc ; simpl.
              repeat rewrite <- app_assoc ; auto. rewrite H. apply OrImpLRule_I. left.
              assert (Γ3 ++ x ++ A → C :: Γ1 ++ B → C :: Γ6 ++ Γ7 = Γ3 ++ x ++ (A → C :: Γ1 ++ [B → C]) ++ Γ6 ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert ((Γ3 ++ Γ6) ++ A → C :: Γ1 ++ B → C :: x ++ Γ7 = Γ3 ++ Γ6 ++ (A → C :: Γ1 ++ [B → C]) ++ x ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H1.  apply list_exch_LI.
            - repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc.
              exists ((Γ3 ++ Γ6) ++ A → C :: Γ1 ++ B → C :: x0 ++ x ++ Γ7, D). repeat split.
              assert (Γ3 ++ Γ6 ++ (A ∨ B) → C :: Γ1 ++ x0 ++ x ++ Γ7 = (Γ3 ++ Γ6) ++ (A ∨ B) → C :: Γ1 ++ x0 ++ x ++ Γ7). repeat rewrite <- app_assoc ; simpl.
              repeat rewrite <- app_assoc ; auto. rewrite H. apply OrImpLRule_I. left.
              assert (Γ3 ++ x ++ A → C :: Γ1 ++ B → C :: x0 ++ Γ6 ++ Γ7 = Γ3 ++ x ++(A → C :: Γ1 ++ B → C :: x0) ++ Γ6 ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert ((Γ3 ++ Γ6) ++ A → C :: Γ1 ++ B → C :: x0 ++ x ++ Γ7 = Γ3 ++ Γ6 ++ (A → C :: Γ1 ++ B → C :: x0) ++ x ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H1.  apply list_exch_LI.
            - repeat rewrite <- app_assoc. simpl. apply app2_find_hole in e1. destruct e1. repeat destruct s ; destruct p ; subst.
              * exists ((Γ3 ++ Γ6) ++ A → C :: (Γ5 ++ x) ++  B → C :: Γ7, D). repeat split.
                assert (Γ3 ++ Γ6 ++ (A ∨ B) → C :: Γ5 ++ x ++ Γ7 = (Γ3 ++ Γ6) ++ (A ∨ B) → C :: (Γ5 ++ x) ++ Γ7). repeat rewrite <- app_assoc ; simpl.
                repeat rewrite <- app_assoc ; auto. rewrite H. apply OrImpLRule_I. left.
                assert (Γ3 ++ x ++ A → C :: Γ5 ++ Γ6 ++ B → C :: Γ7 = Γ3 ++ x ++ (A → C :: Γ5) ++ Γ6 ++ B → C :: Γ7).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                assert ((Γ3 ++ Γ6) ++ A → C :: (Γ5 ++ x) ++ B → C :: Γ7 = Γ3 ++ Γ6 ++ (A → C :: Γ5) ++ x ++ B → C :: Γ7).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H1.  apply list_exch_LI.
              * exists ((Γ3 ++ Γ6) ++ A→ C :: (Γ5 ++ x ++ x1) ++ B→ C :: Γ2, D). repeat split.
                assert (Γ3 ++ Γ6 ++ (A ∨ B) → C :: Γ5 ++ x ++ x1 ++ Γ2 = (Γ3 ++ Γ6) ++ (A ∨ B) → C :: (Γ5 ++ x ++ x1) ++ Γ2). repeat rewrite <- app_assoc ; simpl.
                repeat rewrite <- app_assoc ; auto. rewrite H. apply OrImpLRule_I. left.
                assert (Γ3 ++ x ++ A → C :: Γ5 ++ (Γ6 ++ x1) ++ B → C :: Γ2 = Γ3 ++ x ++ (A → C :: Γ5) ++ Γ6 ++ x1 ++ B → C :: Γ2).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                assert ((Γ3 ++ Γ6) ++ A → C :: (Γ5 ++ x ++ x1) ++ B → C :: Γ2 = Γ3 ++ Γ6 ++ (A → C :: Γ5) ++ x ++ x1 ++ B → C :: Γ2).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H1. apply list_exch_LI.
              * exists ((Γ3 ++ x0 ++ x1) ++ A → C :: Γ5 ++ B → C :: x ++ Γ7, D). repeat split.
                assert (Γ3 ++ (x0 ++ x1) ++ (A ∨ B) → C :: Γ5 ++ x ++ Γ7 = (Γ3 ++ x0 ++ x1) ++ (A ∨ B) → C :: Γ5 ++ x ++ Γ7). repeat rewrite <- app_assoc ; simpl.
                repeat rewrite <- app_assoc ; auto. rewrite H. apply OrImpLRule_I. right.
                exists (Γ3 ++  (x0 ++ B → C :: x1) ++ (A → C :: Γ5) ++ x ++ Γ7, D). split.
                assert (Γ3 ++ x ++ A → C :: Γ5 ++ x0 ++ B → C :: x1 ++ Γ7 = Γ3 ++ x ++ (A → C :: Γ5) ++ (x0 ++ B → C :: x1) ++ Γ7).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H. apply list_exch_LI.
                assert (Γ3 ++ (x0 ++ B → C :: x1) ++ (A → C :: Γ5) ++ x ++ Γ7 = (Γ3 ++ x0) ++ [B → C] ++ (x1 ++ A → C :: Γ5) ++ [] ++ x ++ Γ7).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                assert ((Γ3 ++ x0 ++ x1) ++ A → C :: Γ5 ++ B → C :: x ++ Γ7 = (Γ3 ++ x0) ++ [] ++  (x1 ++ A → C :: Γ5) ++ [B → C] ++ x ++ Γ7).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H1. apply list_exch_LI. }
      + apply app2_find_hole in H1. destruct H1. repeat destruct s ; destruct p ; subst.
        {  exists ((Γ3 ++ Γ6 ++ Γ5 ++ x) ++ A → C :: Γ1 ++ B → C :: Γ7, D). repeat split.
            assert (Γ3 ++ Γ6 ++ Γ5 ++ (x ++ (A ∨ B) → C :: Γ1) ++ Γ7 = (Γ3 ++ Γ6 ++ Γ5 ++ x) ++ (A ∨ B) → C :: Γ1 ++ Γ7). repeat rewrite <- app_assoc. auto.
            rewrite H. apply OrImpLRule_I. left.
            assert ((Γ3 ++ x) ++ A → C :: Γ1 ++ B → C :: Γ5 ++ Γ6 ++ Γ7 = Γ3 ++ (x ++ A → C :: Γ1 ++ [B → C]) ++ Γ5 ++ Γ6 ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert ((Γ3 ++ Γ6 ++ Γ5 ++ x) ++ A → C :: Γ1 ++ B → C :: Γ7 = Γ3 ++ Γ6 ++ Γ5 ++ (x ++ A → C :: Γ1 ++ [B → C]) ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0.  apply list_exch_LI. }
        { exists ((Γ3 ++ Γ6 ++ Γ5 ++ x) ++ A → C :: Γ1 ++ B → C ::  x1 ++ Γ7, D). repeat split.
            assert (Γ3 ++ Γ6 ++ Γ5 ++ (x ++ (A ∨ B) → C :: Γ1 ++ x1) ++ Γ7 = (Γ3 ++ Γ6 ++ Γ5 ++ x) ++ (A ∨ B) → C :: Γ1 ++ x1 ++ Γ7). repeat rewrite <- app_assoc. auto.
            simpl. repeat rewrite <- app_assoc. auto. rewrite H. apply OrImpLRule_I. left.
            assert ((Γ3 ++ x) ++ A → C :: Γ1 ++ B → C :: x1 ++ Γ5 ++ Γ6 ++ Γ7 = Γ3 ++ (x ++ A → C :: Γ1 ++ B → C :: x1) ++ Γ5 ++ Γ6 ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
            assert ((Γ3 ++ Γ6 ++ Γ5 ++ x) ++ A → C :: Γ1 ++ B → C :: x1 ++ Γ7 = Γ3 ++ Γ6 ++ Γ5 ++ (x ++ A → C :: Γ1 ++ B → C :: x1) ++ Γ7).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI. }
        { apply app2_find_hole in e1. destruct e1. repeat destruct s ; destruct p ; subst.
            - exists ((Γ3 ++ Γ6 ++ Γ5 ++ x) ++ A → C :: x0 ++ B → C :: Γ7, D). repeat split.
              assert (Γ3 ++ Γ6 ++ Γ5 ++ (x ++ (A ∨ B) → C :: x0) ++ Γ7 = (Γ3 ++ Γ6 ++ Γ5 ++ x) ++ (A ∨ B) → C :: x0 ++ Γ7). repeat rewrite <- app_assoc ; simpl.
              repeat rewrite <- app_assoc ; auto. rewrite H. apply OrImpLRule_I. right.
              exists (Γ3 ++ Γ6 ++ (Γ5 ++ [B → C]) ++ (x ++ A → C :: x0) ++ Γ7, D). split.
              assert ((Γ3 ++ x) ++ A → C :: (x0 ++ Γ5) ++ B → C :: Γ6 ++ Γ7 = Γ3 ++ (x ++ A → C :: x0) ++ (Γ5 ++ [B → C]) ++ Γ6 ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H. apply list_exch_LI.
              assert (Γ3 ++ Γ6 ++ (Γ5 ++ [B → C]) ++ (x ++ A → C :: x0) ++ Γ7 = (Γ3 ++ Γ6 ++ Γ5) ++ [B → C] ++ (x ++ A → C :: x0) ++ [] ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert ((Γ3 ++ Γ6 ++ Γ5 ++ x) ++ A → C :: x0 ++ B → C :: Γ7 = (Γ3 ++ Γ6 ++ Γ5) ++ [] ++ (x ++ A → C :: x0) ++ [B → C] ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
            - apply app2_find_hole in e1. destruct e1. repeat destruct s ; destruct p ; subst.
              * exists ((Γ3 ++ Γ6 ++ Γ5 ++ x) ++ A → C :: x0 ++ B → C :: Γ7, D). repeat split.
                assert (Γ3 ++ Γ6 ++ Γ5 ++ (x ++ (A ∨ B) → C :: x0) ++ Γ7 = (Γ3 ++ Γ6 ++ Γ5 ++ x) ++ (A ∨ B) → C :: x0 ++ Γ7). repeat rewrite <- app_assoc ; simpl.
                repeat rewrite <- app_assoc ; auto. rewrite H. apply OrImpLRule_I. left.
                assert ((Γ3 ++ x) ++ A → C :: (x0 ++ Γ5 ++ Γ6) ++ B → C :: Γ7 = Γ3 ++ (x ++ A → C :: x0) ++ Γ5 ++ Γ6 ++ B → C :: Γ7).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                assert ((Γ3 ++ Γ6 ++ Γ5 ++ x) ++ A → C :: x0 ++ B → C :: Γ7 = Γ3 ++ Γ6 ++ Γ5 ++ (x ++ A → C :: x0) ++ B → C :: Γ7).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
              * exists ((Γ3 ++ Γ6 ++ Γ5 ++ x) ++ A → C :: (x0 ++ x1) ++ B → C :: Γ2, D). repeat split.
                assert (Γ3 ++ Γ6 ++ Γ5 ++ (x ++ (A ∨ B) → C :: x0) ++ x1 ++ Γ2 = (Γ3 ++ Γ6 ++ Γ5 ++ x) ++ (A ∨ B) → C :: (x0 ++ x1) ++ Γ2). repeat rewrite <- app_assoc ; simpl.
                repeat rewrite <- app_assoc ; auto. rewrite H. apply OrImpLRule_I. left.
                assert ((Γ3 ++ x) ++ A → C :: (x0 ++ Γ5 ++ Γ6 ++ x1) ++ B → C :: Γ2 = Γ3 ++ (x ++ A → C :: x0) ++ Γ5 ++ Γ6 ++ x1 ++ B → C :: Γ2).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                assert ((Γ3 ++ Γ6 ++ Γ5 ++ x) ++ A → C :: (x0 ++ x1) ++ B → C :: Γ2 = Γ3 ++ Γ6 ++ Γ5 ++ (x ++ A → C :: x0) ++ x1 ++ B → C :: Γ2).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
              * exists ((Γ3 ++ x2 ++ x1 ++ Γ5 ++ x) ++ A → C :: x0 ++ B → C :: Γ7, D). repeat split.
                assert (Γ3 ++ (x2 ++ x1) ++ Γ5 ++ (x ++ (A ∨ B) → C :: x0) ++ Γ7 = (Γ3 ++ x2 ++ x1 ++ Γ5 ++ x) ++ (A ∨ B) → C :: x0 ++ Γ7). repeat rewrite <- app_assoc ; simpl.
                repeat rewrite <- app_assoc ; auto. rewrite H. apply OrImpLRule_I. right.
                exists (Γ3 ++ (x2 ++ B → C :: x1) ++ Γ5 ++ (x ++ A → C :: x0) ++ Γ7, D). split.
                assert ((Γ3 ++ x) ++ A → C :: (x0 ++ Γ5 ++ x2) ++ B → C :: x1 ++ Γ7 = Γ3 ++ (x ++ A → C :: x0) ++ Γ5 ++ (x2 ++ B → C :: x1) ++ Γ7).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H. apply list_exch_LI.
                assert (Γ3 ++ (x2 ++ B → C :: x1) ++ Γ5 ++ (x ++ A → C :: x0) ++ Γ7 = (Γ3 ++ x2) ++ [B → C] ++ (x1 ++ Γ5 ++ x ++ A → C :: x0) ++ [] ++ Γ7).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
                assert ((Γ3 ++ x2 ++ x1 ++ Γ5 ++ x) ++ A → C :: x0 ++ B → C :: Γ7 = (Γ3 ++ x2) ++ [] ++ (x1 ++ Γ5 ++ x ++ A → C :: x0) ++ [B → C] ++ Γ7).
                repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI.
            - exists ((Γ3 ++ Γ6 ++ x1 ++ x2 ++ x) ++ A → C :: x0 ++ B → C :: Γ7, D). repeat split.
              assert (Γ3 ++ Γ6 ++ (x1 ++ x2) ++ (x ++ (A ∨ B) → C :: x0) ++ Γ7 = (Γ3 ++ Γ6 ++ x1 ++ x2 ++ x) ++ (A ∨ B) → C :: x0 ++ Γ7). repeat rewrite <- app_assoc ; simpl.
              repeat rewrite <- app_assoc ; auto. rewrite H. apply OrImpLRule_I. right.
              exists(Γ3 ++ Γ6 ++ (x1 ++ B → C :: x2) ++ (x ++ A → C :: x0) ++ Γ7, D). split.
              assert ((Γ3 ++ x) ++ A → C :: (x0 ++ x1) ++ B → C :: x2 ++ Γ6 ++ Γ7 = Γ3 ++ (x ++ A → C :: x0) ++ (x1 ++ B → C :: x2) ++ Γ6 ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H. apply list_exch_LI.
              assert (Γ3 ++ Γ6 ++ (x1 ++ B → C :: x2) ++ (x ++ A → C :: x0) ++ Γ7 = (Γ3 ++ Γ6 ++ x1) ++ [B → C] ++ (x2 ++ x ++ A → C :: x0) ++ [] ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H.
              assert ((Γ3 ++ Γ6 ++ x1 ++ x2 ++ x) ++ A → C :: x0 ++ B → C :: Γ7 = (Γ3 ++ Γ6 ++ x1) ++ [] ++ (x2 ++ x ++ A → C :: x0) ++ [B → C] ++ Γ7).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0. apply list_exch_LI. }
Qed.


Lemma ImpImpL_app_list_exchL : forall s se ps1 ps2,
  (@list_exch_L s se) ->
  (ImpImpLRule [ps1;ps2] s) ->
  (existsT2 pse1 pse2,
    (ImpImpLRule [pse1;pse2] se) *
    (@list_exch_L ps1 pse1)  *
    (@list_exch_L ps2 pse2)).
Proof.
intros s se ps1 ps2 exch RA. inversion RA. subst. inversion exch. subst. symmetry in H0.
apply app2_find_hole in H0. destruct H0. repeat destruct s ; destruct p ; subst.
- destruct Γ3.
  + simpl in e0. subst. simpl. destruct Γ4.
      * simpl in e0. simpl. destruct Γ5.
        { simpl in e0. subst. simpl. exists (Γ0 ++ B → C :: Γ1, A → B). exists (Γ0 ++ C :: Γ1, D). repeat split ; try apply list_exch_L_id. }
        { simpl in e0. inversion e0. subst. simpl. exists (Γ0 ++ B → C :: Γ5 ++ Γ6, A → B). exists (Γ0 ++ C :: Γ5 ++ Γ6, D). repeat split ; try apply list_exch_L_id. }
      * simpl in e0. inversion e0. subst. exists (Γ0 ++ Γ5 ++ B → C :: Γ4 ++ Γ6, A → B). exists (Γ0 ++ Γ5 ++ C :: Γ4 ++ Γ6, D). repeat split.
        assert (Γ0 ++ Γ5 ++ B → C :: Γ4 ++ Γ6 = (Γ0 ++ Γ5) ++ B → C :: Γ4 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
        assert (Γ0 ++ Γ5 ++ C :: Γ4 ++ Γ6 = (Γ0 ++ Γ5) ++ C :: Γ4 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
        assert (Γ0 ++ Γ5 ++ ((A → B) → C :: Γ4) ++ Γ6 = (Γ0 ++ Γ5) ++ (A → B) → C :: Γ4 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H1.
        apply ImpImpLRule_I.
        assert (Γ0 ++ B → C :: Γ4 ++ Γ5 ++ Γ6 = Γ0 ++ [] ++ (B → C :: Γ4) ++ Γ5 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
        assert (Γ0 ++ Γ5 ++ B → C :: Γ4 ++ Γ6 = Γ0 ++ Γ5 ++ (B → C :: Γ4) ++ [] ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
        apply list_exch_LI.
        assert (Γ0 ++ C :: Γ4 ++ Γ5 ++ Γ6 = Γ0 ++ [] ++ (C :: Γ4) ++ Γ5 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
        assert (Γ0 ++ Γ5 ++ C :: Γ4 ++ Γ6 = Γ0 ++ Γ5 ++ (C :: Γ4) ++ [] ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
        apply list_exch_LI.
  + simpl in e0. inversion e0. subst. exists (Γ0 ++ Γ5 ++ Γ4 ++ B → C :: Γ3 ++ Γ6, A → B). exists (Γ0 ++ Γ5 ++ Γ4 ++ C :: Γ3 ++ Γ6, D). repeat split.
      assert (Γ0 ++ Γ5 ++ Γ4 ++ B → C :: Γ3 ++ Γ6 = (Γ0 ++ Γ5 ++ Γ4) ++ B → C :: Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
      assert (Γ0 ++ Γ5 ++ Γ4 ++ C :: Γ3 ++ Γ6 = (Γ0 ++ Γ5 ++ Γ4) ++ C :: Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
      assert (Γ0 ++ Γ5 ++ Γ4 ++ ((A → B) → C :: Γ3) ++ Γ6 =( Γ0 ++ Γ5 ++ Γ4) ++ (A → B) → C :: Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H1.
      apply ImpImpLRule_I.
      assert (Γ0 ++ B → C :: Γ3 ++ Γ4 ++ Γ5 ++ Γ6 = Γ0 ++ (B → C :: Γ3) ++ Γ4 ++ Γ5 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
      assert (Γ0 ++ Γ5 ++ Γ4 ++ B → C :: Γ3 ++ Γ6 = Γ0 ++ Γ5 ++ Γ4 ++ (B → C :: Γ3) ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
      apply list_exch_LI.
      assert (Γ0 ++ C :: Γ3 ++ Γ4 ++ Γ5 ++ Γ6 = Γ0 ++ (C :: Γ3) ++ Γ4 ++ Γ5 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
      assert (Γ0 ++ Γ5 ++ Γ4 ++ C :: Γ3 ++ Γ6 = Γ0 ++ Γ5 ++ Γ4 ++ (C :: Γ3) ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
      apply list_exch_LI.
- destruct x.
  + simpl in e0. subst. simpl. destruct Γ3.
      * simpl in e0. simpl. destruct Γ4.
        { simpl in e0. subst. simpl. rewrite <- e0. exists ((Γ0 ++ []) ++ B → C :: Γ1, A → B). exists ((Γ0 ++ []) ++ C :: Γ1, D). repeat split ; rewrite <- app_assoc ; simpl ; try apply list_exch_L_id. }
        { simpl in e0. inversion e0. subst. simpl. rewrite <- app_assoc ; simpl. exists (Γ0 ++ Γ5 ++ B → C :: Γ4 ++ Γ6, A → B). exists (Γ0 ++ Γ5 ++ C :: Γ4 ++ Γ6, D). repeat split.
          assert (Γ0 ++ Γ5 ++ B → C :: Γ4 ++ Γ6 = (Γ0 ++ Γ5) ++ B → C :: Γ4 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
          assert (Γ0 ++ Γ5 ++ C :: Γ4 ++ Γ6 = (Γ0 ++ Γ5) ++ C :: Γ4 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
          assert (Γ0 ++ Γ5 ++ (A → B) → C :: Γ4 ++ Γ6 = (Γ0 ++ Γ5) ++ (A → B) → C :: Γ4 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H1.
          apply ImpImpLRule_I.
          assert (Γ0 ++ B → C :: Γ4 ++ Γ5 ++ Γ6 = Γ0 ++ [] ++ (B → C :: Γ4) ++ Γ5 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
          assert (Γ0 ++ Γ5 ++ B → C :: Γ4 ++ Γ6 = Γ0 ++ Γ5 ++ (B → C :: Γ4) ++ [] ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
          apply list_exch_LI.
          assert (Γ0 ++ C :: Γ4 ++ Γ5 ++ Γ6 = Γ0 ++ [] ++ (C :: Γ4) ++ Γ5 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
          assert (Γ0 ++ Γ5 ++ C :: Γ4 ++ Γ6 = Γ0 ++ Γ5 ++ (C :: Γ4) ++ [] ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
          apply list_exch_LI. }
      * simpl in e0. inversion e0. subst. rewrite <- app_assoc ; simpl. exists (Γ0 ++ Γ5 ++ Γ4 ++ B → C :: Γ3 ++ Γ6, A → B). exists (Γ0 ++ Γ5 ++ Γ4 ++ C :: Γ3 ++ Γ6, D). repeat split.
        assert (Γ0 ++ Γ5 ++ Γ4 ++ B → C :: Γ3 ++ Γ6 = (Γ0 ++ Γ5 ++ Γ4) ++ B → C :: Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
        assert (Γ0 ++ Γ5 ++ Γ4 ++ C :: Γ3 ++ Γ6 = (Γ0 ++ Γ5 ++ Γ4) ++ C :: Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
        assert (Γ0 ++ Γ5 ++ Γ4 ++ (A → B) → C :: Γ3 ++ Γ6 = (Γ0 ++ Γ5 ++ Γ4) ++ (A → B) → C :: Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H1.
        apply ImpImpLRule_I.
        assert (Γ0 ++ B → C :: Γ3 ++ Γ4 ++ Γ5 ++ Γ6 = Γ0 ++ (B → C :: Γ3) ++ Γ4 ++ Γ5 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
        assert (Γ0 ++ Γ5 ++ Γ4 ++ B → C :: Γ3 ++ Γ6 = Γ0 ++ Γ5 ++ Γ4 ++ (B → C :: Γ3) ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
        apply list_exch_LI.
        assert (Γ0 ++ C :: Γ3 ++ Γ4 ++ Γ5 ++ Γ6 = Γ0 ++ (C :: Γ3) ++ Γ4 ++ Γ5 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
        assert (Γ0 ++ Γ5 ++ Γ4 ++ C :: Γ3 ++ Γ6 = Γ0 ++ Γ5 ++ Γ4 ++ (C :: Γ3) ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
        apply list_exch_LI.
  + simpl in e0. inversion e0. subst. exists (Γ0 ++ B → C :: x ++ Γ5 ++ Γ4 ++ Γ3 ++ Γ6, A → B). exists (Γ0 ++ C :: x ++ Γ5 ++ Γ4 ++ Γ3 ++ Γ6, D). repeat rewrite <- app_assoc. repeat split.
      assert (Γ0 ++ B → C :: x ++ Γ3 ++ Γ4 ++ Γ5 ++ Γ6 = (Γ0 ++ B → C :: x) ++ Γ3 ++ Γ4 ++ Γ5 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
      assert (Γ0 ++ B → C :: x ++ Γ5 ++ Γ4 ++ Γ3 ++ Γ6 = (Γ0 ++ B → C :: x) ++ Γ5 ++ Γ4 ++ Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
      apply list_exch_LI.
      assert (Γ0 ++ C :: x ++ Γ3 ++ Γ4 ++ Γ5 ++ Γ6 = (Γ0 ++ C :: x) ++ Γ3 ++ Γ4 ++ Γ5 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
      assert (Γ0 ++ C :: x ++ Γ5 ++ Γ4 ++ Γ3 ++ Γ6 = (Γ0 ++ C :: x) ++ Γ5 ++ Γ4 ++ Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
      apply list_exch_LI.
- apply app2_find_hole in e0. destruct e0. repeat destruct s ; destruct p ; subst.
  + simpl in e0. subst. simpl. destruct Γ4.
      * simpl in e0. simpl. destruct Γ5.
        { simpl in e0. subst. simpl. exists ((Γ2 ++ Γ3) ++ B → C :: Γ1, A → B). exists ((Γ2 ++ Γ3) ++ C :: Γ1, D).  repeat split ; try apply list_exch_L_id. rewrite app_assoc.
           apply ImpImpLRule_I. }
        { simpl in e0. inversion e0. subst. simpl. exists (Γ2 ++ B → C :: Γ5 ++ Γ3 ++ Γ6, A → B). exists (Γ2 ++ C :: Γ5 ++ Γ3 ++ Γ6, D). repeat split.
           assert ((Γ2 ++ Γ3) ++ B → C :: Γ5 ++ Γ6 = Γ2 ++ Γ3 ++ [] ++ (B → C :: Γ5) ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
           assert (Γ2 ++ B → C :: Γ5 ++ Γ3 ++ Γ6 = Γ2 ++ (B → C :: Γ5) ++ [] ++ Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
           apply list_exch_LI.
           assert ((Γ2 ++ Γ3) ++ C :: Γ5 ++ Γ6 = Γ2 ++ Γ3 ++ [] ++ (C :: Γ5) ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
           assert (Γ2 ++ C :: Γ5 ++ Γ3 ++ Γ6 = Γ2 ++ (C :: Γ5) ++ [] ++ Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
           apply list_exch_LI. }
      * simpl in e0. inversion e0. subst. exists ((Γ2 ++ Γ5) ++ B → C :: Γ4 ++ Γ3 ++ Γ6, A → B). exists ((Γ2 ++ Γ5) ++ C :: Γ4 ++ Γ3 ++ Γ6, D). repeat split.
        assert (Γ2 ++ Γ5 ++ ((A → B) → C :: Γ4) ++ Γ3 ++ Γ6 = (Γ2 ++ Γ5) ++ (A → B) → C :: Γ4 ++ Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
        apply ImpImpLRule_I.
        assert ((Γ2 ++ Γ3) ++ B → C :: Γ4 ++ Γ5 ++ Γ6 = Γ2 ++ Γ3 ++ (B → C :: Γ4) ++ Γ5 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
        assert ((Γ2 ++ Γ5) ++ B → C :: Γ4 ++ Γ3 ++ Γ6 = Γ2 ++ Γ5 ++ (B → C :: Γ4) ++ Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
        apply list_exch_LI.
        assert ((Γ2 ++ Γ3) ++ C :: Γ4 ++ Γ5 ++ Γ6 = Γ2 ++ Γ3 ++ (C :: Γ4) ++ Γ5 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
        assert ((Γ2 ++ Γ5) ++ C :: Γ4 ++ Γ3 ++ Γ6 = Γ2 ++ Γ5 ++ (C :: Γ4) ++ Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
        apply list_exch_LI.
  + apply app2_find_hole in e0. destruct e0. repeat destruct s ; destruct p ; subst.
      * simpl in e0. simpl. destruct Γ5.
        { simpl in e0. subst. simpl. exists ((Γ2 ++ Γ4 ++ Γ3) ++ B → C :: Γ1, A → B). exists ((Γ2 ++ Γ4 ++ Γ3) ++ C :: Γ1, D). repeat split.
           assert (Γ2 ++ Γ4 ++ Γ3 ++ (A → B) → C :: Γ1 = (Γ2 ++ Γ4 ++ Γ3) ++ (A → B) → C :: Γ1). repeat rewrite <- app_assoc. auto. rewrite H.
           apply ImpImpLRule_I.
           assert ((Γ2 ++ Γ3 ++ Γ4) ++ B → C :: Γ1 = Γ2 ++ Γ3 ++ Γ4 ++ [] ++ B → C :: Γ1). repeat rewrite <- app_assoc. auto. rewrite H.
           assert ((Γ2 ++ Γ4 ++ Γ3) ++ B → C :: Γ1 = Γ2 ++ [] ++ Γ4 ++ Γ3 ++ B → C :: Γ1). repeat rewrite <- app_assoc. auto. rewrite H0.
           apply list_exch_LI.
           assert ((Γ2 ++ Γ3 ++ Γ4) ++ C :: Γ1 = Γ2 ++ Γ3 ++ Γ4 ++ [] ++ C :: Γ1). repeat rewrite <- app_assoc. auto. rewrite H.
           assert ((Γ2 ++ Γ4 ++ Γ3) ++ C :: Γ1 = Γ2 ++ [] ++ Γ4 ++ Γ3 ++ C :: Γ1). repeat rewrite <- app_assoc. auto. rewrite H0.
           apply list_exch_LI. }
        { simpl in e0. inversion e0. subst. simpl. exists (Γ2 ++ B → C :: Γ5 ++ Γ4 ++ Γ3 ++ Γ6, A → B). exists (Γ2 ++ C :: Γ5 ++ Γ4 ++ Γ3 ++ Γ6, D). repeat split.
           assert ((Γ2 ++ Γ3 ++ Γ4) ++ B → C :: Γ5 ++ Γ6 = Γ2 ++ Γ3 ++ Γ4 ++ (B → C :: Γ5) ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
           assert (Γ2 ++ B → C :: Γ5 ++ Γ4 ++ Γ3 ++ Γ6 = Γ2 ++ (B → C :: Γ5) ++ Γ4 ++ Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
           apply list_exch_LI.
           assert ((Γ2 ++ Γ3 ++ Γ4) ++ C :: Γ5 ++ Γ6 = Γ2 ++ Γ3 ++ Γ4 ++ (C :: Γ5) ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
           assert (Γ2 ++ C :: Γ5 ++ Γ4 ++ Γ3 ++ Γ6 = Γ2 ++ (C :: Γ5) ++ Γ4 ++ Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
           apply list_exch_LI. }
      * apply app2_find_hole in e0. destruct e0. repeat destruct s ; destruct p ; subst.
        {  repeat rewrite <- app_assoc. exists (Γ2 ++ Γ5 ++ Γ4 ++ Γ3 ++ B → C :: Γ1, A → B).  exists (Γ2 ++ Γ5 ++ Γ4 ++ Γ3 ++ C :: Γ1, D). repeat split. repeat rewrite app_assoc. apply ImpImpLRule_I. }
        {  repeat rewrite <- app_assoc. exists (Γ2 ++ Γ5 ++ Γ4 ++ Γ3 ++ x0 ++ B → C :: Γ1, A → B). exists (Γ2 ++ Γ5 ++ Γ4 ++ Γ3 ++ x0 ++ C :: Γ1, D). repeat split. repeat rewrite app_assoc. apply ImpImpLRule_I. }
        { destruct x0.
            - simpl in e0. subst. repeat rewrite <- app_assoc. simpl. exists (Γ2 ++ x ++ Γ4 ++ Γ3 ++ B → C :: Γ1, A → B). exists (Γ2 ++ x ++ Γ4 ++ Γ3 ++ C :: Γ1, D). repeat split.
              repeat rewrite app_assoc. apply ImpImpLRule_I.
            - simpl in e0. inversion e0. subst. repeat rewrite <- app_assoc. simpl. exists ((Γ2 ++ x) ++ B → C :: x0 ++ Γ4 ++ Γ3 ++ Γ6, A → B). exists ((Γ2 ++ x) ++ C :: x0 ++ Γ4 ++ Γ3 ++ Γ6, D). repeat split.
              assert (Γ2 ++ x ++ (A → B) → C :: x0 ++ Γ4 ++ Γ3 ++ Γ6 = (Γ2 ++ x) ++ (A → B) → C :: x0 ++ Γ4 ++ Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
              apply ImpImpLRule_I.
              assert (Γ2 ++ Γ3 ++ Γ4 ++ x ++ B → C :: x0 ++ Γ6 = Γ2 ++ Γ3 ++ Γ4 ++ (x ++ B → C :: x0) ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
              assert ((Γ2 ++ x) ++ B → C :: x0 ++ Γ4 ++ Γ3 ++ Γ6 = Γ2 ++ (x ++ B → C :: x0) ++ Γ4 ++ Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
              apply list_exch_LI.
              assert (Γ2 ++ Γ3 ++ Γ4 ++ x ++ C :: x0 ++ Γ6 = Γ2 ++ Γ3 ++ Γ4 ++ (x ++ C :: x0) ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
              assert ((Γ2 ++ x) ++ C :: x0 ++ Γ4 ++ Γ3 ++ Γ6 = Γ2 ++ (x ++ C :: x0) ++ Γ4 ++ Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
              apply list_exch_LI. }
      * destruct x.
        { simpl in e0. destruct Γ5.
            - simpl in e0. subst. repeat rewrite <- app_assoc. simpl. exists (Γ2 ++ x0 ++ Γ3 ++ B → C :: Γ1, A → B). exists (Γ2 ++ x0 ++ Γ3 ++ C :: Γ1, D). repeat split.
              repeat rewrite app_assoc. apply ImpImpLRule_I.
              assert (Γ2 ++ Γ3 ++ x0 ++ B → C :: Γ1 = Γ2 ++ Γ3 ++ [] ++ x0 ++ B → C :: Γ1). repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ2 ++ x0 ++ Γ3 ++ B → C :: Γ1 = Γ2 ++ x0 ++ [] ++ Γ3 ++ B → C :: Γ1). repeat rewrite <- app_assoc. auto. rewrite H0.
              apply list_exch_LI.
              assert (Γ2 ++ Γ3 ++ x0 ++ C :: Γ1 = Γ2 ++ Γ3 ++ [] ++ x0 ++ C :: Γ1). repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ2 ++ x0 ++ Γ3 ++ C :: Γ1 = Γ2 ++ x0 ++ [] ++ Γ3 ++ C :: Γ1). repeat rewrite <- app_assoc. auto. rewrite H0.
              apply list_exch_LI.
            - simpl in e0. inversion e0. subst. repeat rewrite <- app_assoc. simpl. exists (Γ2 ++ B → C :: Γ5 ++ x0 ++ Γ3 ++ Γ6, A → B). exists (Γ2 ++ C :: Γ5 ++ x0 ++ Γ3 ++ Γ6, D). repeat split.
              assert (Γ2 ++ Γ3 ++ x0 ++ B → C :: Γ5 ++ Γ6 = Γ2 ++ Γ3 ++ x0 ++ (B → C :: Γ5) ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ2 ++ B → C :: Γ5 ++ x0 ++ Γ3 ++ Γ6 = Γ2 ++ (B → C :: Γ5) ++ x0 ++ Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
              apply list_exch_LI.
              assert (Γ2 ++ Γ3 ++ x0 ++ C :: Γ5 ++ Γ6 = Γ2 ++ Γ3 ++ x0 ++ (C :: Γ5) ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ2 ++ C :: Γ5 ++ x0 ++ Γ3 ++ Γ6 = Γ2 ++ (C :: Γ5) ++ x0 ++ Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
              apply list_exch_LI. }
        { simpl in e0. inversion e0. subst. exists ((Γ2 ++ Γ5 ++ x0) ++ B → C :: x ++ Γ3 ++ Γ6, A → B). exists ((Γ2 ++ Γ5 ++ x0) ++ C :: x ++ Γ3 ++ Γ6, D). repeat split.
           assert (Γ2 ++ Γ5 ++ (x0 ++ (A → B) → C :: x) ++ Γ3 ++ Γ6 = (Γ2 ++ Γ5 ++ x0) ++ (A → B) → C :: x ++ Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
           apply ImpImpLRule_I.
           assert ((Γ2 ++ Γ3 ++ x0) ++ B → C :: x ++ Γ5 ++ Γ6 = Γ2 ++ Γ3 ++ (x0 ++ B → C :: x) ++ Γ5 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
           assert ((Γ2 ++ Γ5 ++ x0) ++ B → C :: x ++ Γ3 ++ Γ6 = Γ2 ++ Γ5 ++ (x0 ++ B → C :: x) ++ Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
           apply list_exch_LI.
           assert ((Γ2 ++ Γ3 ++ x0) ++ C :: x ++ Γ5 ++ Γ6 = Γ2 ++ Γ3 ++ (x0 ++ C :: x) ++ Γ5 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
           assert ((Γ2 ++ Γ5 ++ x0) ++ C :: x ++ Γ3 ++ Γ6 = Γ2 ++ Γ5 ++ (x0 ++ C :: x) ++ Γ3 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
           apply list_exch_LI. }
  + destruct x0.
      * simpl in e0. simpl. destruct Γ4.
        { simpl in e0. destruct Γ5.
            - simpl in e0. subst. repeat rewrite <- app_assoc. simpl. exists (Γ2 ++ x ++ B → C :: Γ1, A → B). exists (Γ2 ++ x ++ C :: Γ1, D). repeat split.
              repeat rewrite app_assoc. apply ImpImpLRule_I. apply list_exch_L_id. apply list_exch_L_id.
            - simpl in e0. inversion e0. subst. repeat rewrite <- app_assoc. simpl. exists (Γ2 ++ B → C :: Γ5 ++ x ++ Γ6, A → B). exists (Γ2 ++ C :: Γ5 ++ x ++ Γ6, D). repeat split.
              assert (Γ2 ++ x ++ B → C :: Γ5 ++ Γ6 = Γ2 ++ x ++ [] ++ (B → C :: Γ5) ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ2 ++ B → C :: Γ5 ++ x ++ Γ6 = Γ2 ++( B → C :: Γ5) ++ [] ++ x ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
              apply list_exch_LI.
              assert (Γ2 ++ x ++ C :: Γ5 ++ Γ6 = Γ2 ++ x ++ [] ++ (C :: Γ5) ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
              assert (Γ2 ++ C :: Γ5 ++ x ++ Γ6 = Γ2 ++(C :: Γ5) ++ [] ++ x ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
              apply list_exch_LI. }
        { simpl in e0. inversion e0. subst. repeat rewrite <- app_assoc. simpl. exists ((Γ2 ++ Γ5) ++ B → C :: Γ4 ++ x ++ Γ6, A → B). exists ((Γ2 ++ Γ5) ++ C :: Γ4 ++ x ++ Γ6, D). repeat split.
          assert (Γ2 ++ Γ5 ++ (A → B) → C :: Γ4 ++ x ++ Γ6 = (Γ2 ++ Γ5) ++ (A → B) → C :: Γ4 ++ x ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
          apply ImpImpLRule_I.
          assert (Γ2 ++ x ++ B → C :: Γ4 ++ Γ5 ++ Γ6 = Γ2 ++ x ++ (B → C :: Γ4) ++ Γ5 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
          assert ((Γ2 ++ Γ5) ++ B → C :: Γ4 ++ x ++ Γ6 = Γ2 ++ Γ5 ++ (B → C :: Γ4) ++ x ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
          apply list_exch_LI.
          assert (Γ2 ++ x ++ C :: Γ4 ++ Γ5 ++ Γ6 = Γ2 ++ x ++ (C :: Γ4) ++ Γ5 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
          assert ((Γ2 ++ Γ5) ++ C :: Γ4 ++ x ++ Γ6 = Γ2 ++ Γ5 ++ (C :: Γ4) ++ x ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
          apply list_exch_LI. }
      * simpl in e0. inversion e0. subst. repeat rewrite <- app_assoc. simpl. exists ((Γ2 ++ Γ5 ++ Γ4 ++ x) ++ B → C :: x0 ++ Γ6, A → B). exists ((Γ2 ++ Γ5 ++ Γ4 ++ x) ++ C :: x0 ++ Γ6, D). repeat split.
          assert (Γ2 ++ Γ5 ++ Γ4 ++ x ++ (A → B) → C :: x0 ++ Γ6 = (Γ2 ++ Γ5 ++ Γ4 ++ x) ++ (A → B) → C :: x0 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
          apply ImpImpLRule_I.
          assert (Γ2 ++ x ++ B → C :: x0 ++ Γ4 ++ Γ5 ++ Γ6 = Γ2 ++ (x ++ B → C :: x0) ++ Γ4 ++ Γ5 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
          assert ((Γ2 ++ Γ5 ++ Γ4 ++ x) ++ B → C :: x0 ++ Γ6 = Γ2 ++ Γ5 ++ Γ4 ++ (x ++ B → C :: x0) ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
          apply list_exch_LI.
          assert (Γ2 ++ x ++ C :: x0 ++ Γ4 ++ Γ5 ++ Γ6 = Γ2 ++ (x ++ C :: x0) ++ Γ4 ++ Γ5 ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H.
          assert ((Γ2 ++ Γ5 ++ Γ4 ++ x) ++ C :: x0 ++ Γ6 = Γ2 ++ Γ5 ++ Γ4 ++ (x ++ C :: x0) ++ Γ6). repeat rewrite <- app_assoc. auto. rewrite H0.
          apply list_exch_LI.
Qed.
