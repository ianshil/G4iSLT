Require Import List.
Export ListNotations.
Require Import PeanoNat.
Require Import Lia.

Require Import general_export.

Require Import DiSL_calc.
Require Import DG4iSL_list_lems.
Require Import DG4iSL_exch_prelims1.

Lemma AtomImpL2_app_list_exchL : forall s se ps,
  (@list_exch_L s se) ->
  (AtomImpL2Rule [ps] s) ->
   (existsT2 pse, (@list_exch_L ps pse) *
    ((AtomImpL2Rule [pse] se) + (AtomImpL1Rule [pse] se))).
Proof.
intros s se ps exch RA. inversion RA. subst. inversion exch. subst. symmetry in H0.
apply app2_find_hole in H0. destruct H0. repeat destruct s ; destruct p ; subst.
- destruct Γ4.
  + simpl in e0. subst. simpl. destruct Γ5.
      * simpl in e0. simpl. destruct Γ6.
        { simpl in e0. subst. simpl. exists (Γ0 ++ A :: Γ1 ++ # P :: Γ2, C). split ;auto. apply list_exch_L_id. }
        { simpl in e0. inversion e0. subst. simpl. apply app2_find_hole in H1. destruct H1. repeat destruct s ; destruct p ; subst.
          - exists (Γ0 ++ A :: Γ6 ++ # P :: Γ2, C). repeat split. apply list_exch_L_id. auto.
          - exists (Γ0 ++ A :: (Γ6 ++ x0) ++ # P :: Γ2, C). repeat split. repeat rewrite <- app_assoc. apply list_exch_L_id. left.
            pose (AtomImpL2Rule_I P A C Γ0 (Γ6 ++ x0) Γ2). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
          - destruct x0.
            * simpl in e1 ; subst. repeat rewrite <- app_assoc ; simpl. exists (Γ0 ++ A :: Γ1 ++ # P :: Γ2, C). repeat split. apply list_exch_L_id. auto.
            * inversion e1 ; subst. repeat rewrite <- app_assoc ; simpl. exists (Γ0 ++ A :: Γ1 ++ # P :: x0 ++ Γ7, C). repeat split. apply list_exch_L_id. auto. }
      * simpl in e0. inversion e0. subst. apply app2_find_hole in H1. destruct H1. repeat destruct s ; destruct p ; subst.
        { destruct Γ6.
          - simpl in e1 ; subst. simpl. exists (Γ0 ++ A :: Γ5 ++ # P :: Γ2, C) . repeat split ; auto. apply list_exch_L_id.
          - inversion e1 ; subst. exists (Γ0 ++ # P :: Γ6 ++ A :: Γ5 ++ Γ7, C) . split ; auto.
            pose (list_exch_LI Γ0 (A :: Γ5) [] (# P :: Γ6) Γ7 C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
            right. pose (AtomImpL1Rule_I P A C Γ0 Γ6 (Γ5 ++ Γ7)). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto. }
        { apply app2_find_hole in e1. destruct e1. repeat destruct s ; destruct p ; subst.
          - exists ((Γ0 ++ Γ6) ++ A :: Γ5 ++ # P :: Γ2, C). split. 2: left.
            pose (list_exch_LI Γ0 (A :: Γ5) [] Γ6 (# P :: Γ2) C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
            pose (AtomImpL2Rule_I P A C (Γ0 ++ Γ6) Γ5 Γ2). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
          - exists ((Γ0 ++ Γ6) ++ A :: (Γ5 ++ x1) ++ # P :: Γ2, C). split. 2: left.
            pose (list_exch_LI Γ0 (A :: Γ5) [] Γ6 (x1 ++ # P :: Γ2) C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
            pose (AtomImpL2Rule_I P A C (Γ0 ++ Γ6) (Γ5 ++ x1) Γ2). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
          - destruct x1.
            * simpl in e1 ; subst. repeat rewrite <- app_assoc ; simpl. exists ((Γ0 ++ x0) ++ A :: Γ5 ++ # P :: Γ2, C). repeat split. 2: left.
              pose (list_exch_LI Γ0 (A :: Γ5) [] x0 (# P :: Γ2) C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
              pose (AtomImpL2Rule_I P A C (Γ0 ++ x0) Γ5 Γ2). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
            * inversion e1 ; subst. repeat rewrite <- app_assoc ; simpl. exists ((Γ0 ++ x0) ++ # P :: x1 ++ A :: Γ5 ++  Γ7, C). repeat split. 2: right.
              pose (list_exch_LI Γ0 (A :: Γ5) [] (x0 ++ # P :: x1) Γ7 C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
              pose (AtomImpL1Rule_I P A C (Γ0 ++ x0) x1 (Γ5 ++ Γ7)). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto. }
        { destruct x0.
          - simpl in e1. destruct Γ6.
            + simpl in e1 ; subst. repeat rewrite <- app_assoc ; simpl. repeat rewrite <- app_assoc ; simpl.
                exists (Γ0 ++ A :: Γ1 ++ # P :: Γ2, C). repeat split. 2: left. apply list_exch_L_id. auto.
            + inversion e1. subst. repeat rewrite <- app_assoc ; simpl. rewrite app_nil_r. exists (Γ0 ++ # P :: Γ6 ++ A :: Γ1 ++ Γ7, C). repeat split. 2: right ; apply AtomImpL1Rule_I.
               pose (list_exch_LI Γ0 (A :: Γ1) [] (# P :: Γ6) Γ7 C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
          - inversion e1. subst. exists ((Γ0 ++ Γ6) ++ A :: Γ1 ++ # P :: x0 ++ Γ7, C). repeat split. 2: left.
            pose (list_exch_LI Γ0 [] (A :: Γ1 ++ # P :: x0) Γ6 Γ7 C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
            pose (AtomImpL2Rule_I P A C (Γ0 ++ Γ6) Γ1 (x0 ++ Γ7)). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; repeat rewrite <- app_assoc in a ; simpl in a ; auto. }
  + inversion e0. subst. apply app2_find_hole in H1. destruct H1. repeat destruct s ; destruct p ; subst.
     * destruct Γ5.
        { simpl in e1. destruct Γ6.
          - simpl in e1.  subst. simpl. exists (Γ0 ++ A :: Γ4 ++ # P :: Γ2, C). repeat split. 2: left. apply list_exch_L_id. apply AtomImpL2Rule_I.
          - inversion e1. subst. simpl. exists (Γ0 ++ # P :: Γ6 ++ A :: Γ4 ++ Γ7, C). repeat split. 2: right. 2: apply AtomImpL1Rule_I.
            pose (list_exch_LI Γ0 (A :: Γ4) [] (# P :: Γ6) Γ7 C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l. }
        { inversion e1. subst. simpl. exists (Γ0 ++ Γ6 ++ # P :: Γ5 ++ A :: Γ4 ++ Γ7, C). repeat split. 2: right.
          pose (list_exch_LI Γ0 (A :: Γ4) (# P :: Γ5) Γ6 Γ7 C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
          pose (AtomImpL1Rule_I P A C (Γ0 ++ Γ6) Γ5 (Γ4 ++ Γ7)). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto. }
     * apply app2_find_hole in e1. destruct e1. repeat destruct s ; destruct p ; subst.
       { destruct Γ6.
          - simpl in e1.  subst. simpl. exists (Γ0 ++ Γ5 ++ A :: Γ4 ++ # P :: Γ2, C). repeat split. 2: left.
            pose (list_exch_LI Γ0 (A :: Γ4) [] Γ5 (# P :: Γ2) C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
            pose (AtomImpL2Rule_I P A C (Γ0 ++ Γ5) Γ4 Γ2). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
          - inversion e1. subst. simpl. exists (Γ0 ++ # P :: Γ6 ++ Γ5 ++ A :: Γ4 ++ Γ7, C). repeat split. 2: right.
            pose (list_exch_LI Γ0 (A :: Γ4) Γ5 (# P :: Γ6) Γ7 C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
            pose (AtomImpL1Rule_I P A C Γ0 (Γ6 ++ Γ5) (Γ4 ++ Γ7)). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto. }
       { apply app2_find_hole in e1. destruct e1. repeat destruct s ; destruct p ; subst.
          - exists (Γ0 ++ Γ6 ++ Γ5 ++ A :: Γ4 ++ # P :: Γ2, C). repeat split. 2: left.
            pose (list_exch_LI Γ0 (A :: Γ4) Γ5 Γ6 (# P :: Γ2) C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
            pose (AtomImpL2Rule_I P A C (Γ0 ++ Γ6 ++ Γ5) Γ4 Γ2). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
          - exists (Γ0 ++ Γ6 ++ Γ5 ++ A :: Γ4 ++ x0 ++ # P :: Γ2, C). repeat split. 2: left.
            pose (list_exch_LI Γ0 (A :: Γ4) Γ5 Γ6 (x0 ++ # P :: Γ2) C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
            pose (AtomImpL2Rule_I P A C (Γ0 ++ Γ6 ++ Γ5) (Γ4 ++ x0) Γ2). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
          - destruct x0.
            * simpl in e1. subst. repeat rewrite <- app_assoc. simpl. exists (Γ0 ++ x1 ++ Γ5 ++ A :: Γ4 ++ # P :: Γ2, C). repeat split. 2: left.
              pose (list_exch_LI Γ0 (A :: Γ4) Γ5 x1 (# P :: Γ2) C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
              pose (AtomImpL2Rule_I P A C (Γ0 ++ x1 ++ Γ5) Γ4 Γ2). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
            * inversion e1. subst. repeat rewrite <- app_assoc. simpl. exists (Γ0 ++ x1 ++ # P :: x0 ++ Γ5 ++ A :: Γ4 ++ Γ7, C). repeat split. 2: right.
              pose (list_exch_LI Γ0 (A :: Γ4) Γ5 (x1 ++ # P :: x0) Γ7 C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
              pose (AtomImpL1Rule_I P A C (Γ0 ++ x1) (x0 ++ Γ5) (Γ4 ++ Γ7)). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto. }
       { destruct x1.
          - simpl in e1. subst. simpl. repeat rewrite <- app_assoc. simpl. destruct Γ6.
            + simpl in e1. subst. simpl. exists (Γ0 ++ x0 ++ A :: Γ4 ++ # P :: Γ2, C). repeat split. 2: left.
               pose (list_exch_LI Γ0 (A :: Γ4) [] x0 (# P :: Γ2) C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
               pose (AtomImpL2Rule_I P A C (Γ0 ++ x0) Γ4 Γ2). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
            + inversion e1. subst. simpl. exists (Γ0 ++ # P :: Γ6 ++ x0 ++ A :: Γ4 ++ Γ7, C). repeat split. 2: right.
               pose (list_exch_LI Γ0 (A :: Γ4) x0 (# P :: Γ6) Γ7 C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
               pose (AtomImpL1Rule_I P A C Γ0 (Γ6 ++ x0) (Γ4 ++ Γ7)). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
          - inversion e1. subst. simpl. repeat rewrite <- app_assoc. simpl. exists (Γ0 ++ Γ6 ++ x0 ++ # P :: x1 ++ A :: Γ4 ++ Γ7, C). repeat split. 2: right.
            pose (list_exch_LI Γ0 (A :: Γ4) (x0 ++ # P :: x1) Γ6 Γ7 C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
            pose (AtomImpL1Rule_I P A C (Γ0 ++ Γ6 ++ x0) x1 (Γ4 ++ Γ7)). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto. }
     * destruct x0.
       { simpl in e1. destruct Γ5.
          - simpl in e1. destruct Γ6.
            + simpl in e1. subst. simpl. repeat rewrite <- app_assoc. simpl. exists (Γ0 ++ A :: Γ1 ++  # P :: Γ2, C). repeat split. apply list_exch_L_id. auto.
            + inversion e1. subst. simpl. repeat rewrite <- app_assoc. simpl. exists (Γ0 ++ # P :: Γ6 ++ A :: Γ1 ++ Γ7, C). repeat split. 2: right.
               pose (list_exch_LI Γ0 (A :: Γ1) [] (# P :: Γ6) Γ7 C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
               pose (AtomImpL1Rule_I P A C Γ0 Γ6 (Γ1 ++ Γ7)). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
          - inversion e1. subst. simpl. repeat rewrite <- app_assoc. simpl. exists (Γ0 ++ Γ6 ++ # P :: Γ5 ++ A :: Γ1 ++ Γ7, C). repeat split. 2: right.
            pose (list_exch_LI Γ0 (A :: Γ1) (# P :: Γ5) Γ6 Γ7 C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
            pose (AtomImpL1Rule_I P A C (Γ0 ++ Γ6) Γ5 (Γ1 ++ Γ7)). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto. }
       { inversion e1. subst. simpl. repeat rewrite <- app_assoc. simpl. exists (Γ0 ++ Γ6 ++ Γ5 ++ A :: Γ1 ++ # P :: x0 ++ Γ7, C). repeat split. 2: left.
         pose (list_exch_LI Γ0 (A :: Γ1 ++ # P :: x0) Γ5 Γ6 Γ7 C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
         pose (AtomImpL2Rule_I P A C (Γ0 ++ Γ6 ++ Γ5) Γ1 (x0 ++ Γ7)). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto. }
- destruct x ; simpl in e0 ; subst ; repeat rewrite <- app_assoc ; simpl.
  * destruct Γ4.
    + simpl in e0. subst. simpl. destruct Γ5.
        { simpl in e0. simpl. destruct Γ6.
          { simpl in e0. subst. simpl. exists (Γ0 ++ A :: Γ1 ++ # P :: Γ2, C). split ;auto. apply list_exch_L_id. }
          { simpl in e0. inversion e0. subst. simpl. apply app2_find_hole in H1. destruct H1. repeat destruct s ; destruct p ; subst.
            - exists (Γ0 ++ A :: Γ1 ++ # P :: Γ2, C). repeat split ; auto. apply list_exch_L_id.
            - destruct x.
              * simpl in e1. subst. repeat rewrite <- app_assoc ; simpl. exists (Γ0 ++ A :: Γ1 ++ # P :: Γ2, C). repeat rewrite <- app_assoc. repeat split. apply list_exch_L_id. auto.
              * inversion e1. subst. repeat rewrite <- app_assoc ; simpl. exists (Γ0 ++ A :: Γ1 ++ # P :: x ++ Γ7, C). repeat split ; auto. apply list_exch_L_id.
            - exists (Γ0 ++ A :: Γ6 ++ x ++ # P :: Γ2, C). repeat split ; auto. repeat rewrite <- app_assoc; apply list_exch_L_id. repeat rewrite <- app_assoc in RA ; auto. } }
        { simpl in e0. inversion e0. subst. apply app2_find_hole in H1. destruct H1. repeat destruct s ; destruct p ; subst.
          { destruct Γ6.
            - simpl in e1. subst. simpl. exists (Γ0 ++ A :: Γ1 ++ # P :: Γ2, C) . repeat split ;auto. apply list_exch_L_id.
            - inversion e1. subst. simpl. exists (Γ0 ++ # P :: Γ6 ++ A :: Γ1 ++ Γ7, C) . repeat split ;auto. 2: right.
              pose (list_exch_LI Γ0 (A :: Γ1) [] (# P :: Γ6) Γ7 C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
              pose (AtomImpL1Rule_I P A C Γ0 Γ6 (Γ1 ++ Γ7)). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto. }
          { destruct x.
            - simpl in e1. subst. destruct Γ6.
              * simpl in e1. subst. simpl. repeat rewrite <- app_assoc. simpl. exists (Γ0 ++ A :: Γ1 ++ # P :: Γ2, C) . repeat split ;auto. apply list_exch_L_id.
              * inversion e1. subst. simpl. repeat rewrite <- app_assoc. simpl. exists (Γ0 ++ # P :: Γ6 ++ A :: Γ1 ++ Γ7, C) . repeat split ;auto. 2: right.
                pose (list_exch_LI Γ0 (A :: Γ1) [] (# P :: Γ6) Γ7 C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
                pose (AtomImpL1Rule_I P A C Γ0 Γ6 (Γ1 ++ Γ7)). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
            - inversion e1. subst. simpl. repeat rewrite <- app_assoc. simpl. exists (Γ0 ++ Γ6 ++ A :: Γ1 ++ # P :: x ++ Γ7, C). repeat split ;auto. 2: left.
              pose (list_exch_LI Γ0 [] (A :: Γ1 ++ # P :: x) Γ6 Γ7 C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
              pose (AtomImpL2Rule_I P A C (Γ0 ++ Γ6) Γ1 (x ++ Γ7)). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto. }
          { apply app2_find_hole in e1. destruct e1. repeat destruct s ; destruct p ; subst.
            - subst. simpl. repeat rewrite <- app_assoc. simpl. exists (Γ0 ++ Γ6 ++ A :: Γ5 ++ # P :: Γ2, C). repeat split ;auto. 2: left.
              pose (list_exch_LI Γ0 [] (A :: Γ5) Γ6 (# P :: Γ2) C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
              pose (AtomImpL2Rule_I P A C (Γ0 ++ Γ6) Γ5 Γ2). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
            - simpl. repeat rewrite <- app_assoc. simpl. exists (Γ0 ++ Γ6 ++ A :: Γ5 ++ x0 ++ # P :: Γ2, C). repeat split ;auto. 2: left.
              pose (list_exch_LI Γ0 [] (A :: Γ5) Γ6 (x0 ++ # P :: Γ2) C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
              pose (AtomImpL2Rule_I P A C (Γ0 ++ Γ6) (Γ5 ++ x0) Γ2). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
            - destruct x0.
              + simpl in e1. subst. simpl. repeat rewrite <- app_assoc. simpl. exists (Γ0 ++ x ++ A :: Γ5 ++ # P :: Γ2, C). repeat split ;auto. 2: left.
                 pose (list_exch_LI Γ0 [] (A :: Γ5) x (# P :: Γ2) C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
                 pose (AtomImpL2Rule_I P A C (Γ0 ++ x) Γ5 Γ2). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
              + inversion e1. subst. simpl. repeat rewrite <- app_assoc. simpl. exists (Γ0 ++ x ++ # P :: x0 ++ A :: Γ5 ++ Γ7, C). repeat split ;auto. 2: right.
                 pose (list_exch_LI Γ0 (A :: Γ5) [] (x ++ # P :: x0) Γ7 C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
                 pose (AtomImpL1Rule_I P A C (Γ0 ++ x) x0 (Γ5 ++ Γ7)). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto. } }
    + inversion e0. subst. apply app2_find_hole in H1. destruct H1. repeat destruct s ; destruct p ; subst.
      { destruct Γ5.
        - simpl in e1. destruct Γ6.
          + simpl in e1. subst. simpl. exists (Γ0 ++ A :: Γ1 ++ # P :: Γ2, C). repeat split ; auto. apply list_exch_L_id.
          + inversion e1. subst. simpl. exists (Γ0 ++ # P :: Γ6 ++ A :: Γ1 ++ Γ7, C). repeat split. 2: right.
             pose (list_exch_LI Γ0 (A :: Γ1) [] (# P :: Γ6) Γ7 C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
             pose (AtomImpL1Rule_I P A C Γ0 Γ6 (Γ1 ++ Γ7)). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
        - inversion e1. subst. simpl. exists (Γ0 ++ Γ6 ++ # P :: Γ5 ++ A :: Γ1 ++ Γ7, C). repeat split. 2: right.
          pose (list_exch_LI Γ0 (A :: Γ1) (# P :: Γ5) Γ6 Γ7 C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
          pose (AtomImpL1Rule_I P A C (Γ0 ++ Γ6) Γ5 (Γ1 ++ Γ7)). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto. }
      { destruct x.
          - simpl in e1. destruct Γ5.
            + simpl in e1. destruct Γ6.
              * simpl in e1. subst. simpl. repeat rewrite <- app_assoc ; simpl. exists (Γ0 ++ A :: Γ1 ++ # P :: Γ2, C). repeat split ; auto. apply list_exch_L_id.
              * inversion e1. subst. simpl. repeat rewrite <- app_assoc ; simpl. exists (Γ0 ++ # P :: Γ6 ++ A :: Γ1 ++ Γ7, C). repeat split. 2: right.
                pose (list_exch_LI Γ0 (A :: Γ1) [] (# P :: Γ6) Γ7 C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
                pose (AtomImpL1Rule_I P A C Γ0 Γ6 (Γ1 ++ Γ7)). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
            + inversion e1. subst. simpl. repeat rewrite <- app_assoc ; simpl. exists (Γ0 ++ Γ6 ++ # P :: Γ5 ++ A :: Γ1 ++ Γ7, C). repeat split. 2: right.
               pose (list_exch_LI Γ0 (A :: Γ1) (# P :: Γ5) Γ6 Γ7 C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
               pose (AtomImpL1Rule_I P A C (Γ0 ++ Γ6) Γ5 (Γ1 ++ Γ7)). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
          - inversion e1. subst. simpl. repeat rewrite <- app_assoc ; simpl. exists (Γ0 ++ Γ6 ++ Γ5 ++ A :: Γ1 ++ # P :: x ++ Γ7, C). repeat split. 2: left.
            pose (list_exch_LI Γ0 (A :: Γ1 ++ # P :: x) Γ5 Γ6 Γ7 C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
            pose (AtomImpL2Rule_I P A C (Γ0 ++ Γ6 ++ Γ5) Γ1 (x ++ Γ7)). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto. }
      {  apply app2_find_hole in e1. destruct e1. repeat destruct s ; destruct p ; subst.
        - destruct  Γ6.
          + simpl in e1. subst. simpl. repeat rewrite <- app_assoc ; simpl. exists (Γ0 ++ Γ5 ++ A :: Γ4 ++ # P :: Γ2, C). repeat split. 2: left.
             pose (list_exch_LI Γ0 (A :: Γ4) [] Γ5 (# P :: Γ2) C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
             pose (AtomImpL2Rule_I P A C (Γ0 ++ Γ5) Γ4 Γ2). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
          + inversion e1. subst. simpl. repeat rewrite <- app_assoc ; simpl. exists (Γ0 ++ # P :: Γ6 ++ Γ5 ++ A :: Γ4 ++ Γ7, C). repeat split. 2: right.
             pose (list_exch_LI Γ0 (A :: Γ4) Γ5 (# P :: Γ6) Γ7 C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
             pose (AtomImpL1Rule_I P A C Γ0 (Γ6 ++ Γ5) (Γ4 ++ Γ7)). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
        - apply app2_find_hole in e1. destruct e1. repeat destruct s ; destruct p ; subst.
          + simpl. repeat rewrite <- app_assoc ; simpl. exists (Γ0 ++ Γ6 ++ Γ5 ++ A :: Γ4 ++ # P :: Γ2, C). repeat split. 2: left.
             pose (list_exch_LI Γ0 (A :: Γ4) Γ5 Γ6 (# P :: Γ2) C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
             pose (AtomImpL2Rule_I P A C (Γ0 ++ Γ6 ++ Γ5) Γ4 Γ2). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
          + subst. simpl. repeat rewrite <- app_assoc ; simpl. exists (Γ0 ++ Γ6 ++ Γ5 ++ A :: Γ4 ++ x ++ # P :: Γ2, C). repeat split. 2: left.
             pose (list_exch_LI Γ0 (A :: Γ4) Γ5 Γ6 (x ++ # P :: Γ2) C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
             pose (AtomImpL2Rule_I P A C (Γ0 ++ Γ6 ++ Γ5) (Γ4 ++ x) Γ2). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
          + destruct x.
            * simpl in e1. subst. simpl. repeat rewrite <- app_assoc ; simpl. exists (Γ0 ++ x0 ++ Γ5 ++ A :: Γ4 ++ # P :: Γ2, C). repeat split. 2: left.
               pose (list_exch_LI Γ0 (A :: Γ4) Γ5 x0 (# P :: Γ2) C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
               pose (AtomImpL2Rule_I P A C (Γ0 ++ x0 ++ Γ5) Γ4 Γ2). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
            * inversion e1. subst. simpl. repeat rewrite <- app_assoc ; simpl. exists (Γ0 ++ x0 ++ # P :: x ++ Γ5 ++ A :: Γ4 ++ Γ7, C). repeat split. 2: right.
               pose (list_exch_LI Γ0 (A :: Γ4) Γ5 (x0 ++ # P :: x) Γ7 C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
               pose (AtomImpL1Rule_I P A C (Γ0 ++ x0) (x ++ Γ5) (Γ4 ++ Γ7)). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
        - destruct x0.
          + simpl in e1. destruct Γ6.
            * simpl in e1. subst. simpl. repeat rewrite <- app_assoc ; simpl. exists (Γ0 ++ x ++ A :: Γ4 ++ # P :: Γ2, C). repeat split. 2: left.
              pose (list_exch_LI Γ0 (A :: Γ4) [] x (# P :: Γ2) C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
              pose (AtomImpL2Rule_I P A C (Γ0 ++ x) Γ4 Γ2). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
            * inversion e1. subst. simpl. repeat rewrite <- app_assoc ; simpl. exists (Γ0 ++ # P :: Γ6 ++ x ++ A :: Γ4 ++ Γ7, C). repeat split. 2: right.
              pose (list_exch_LI Γ0 (A :: Γ4) x (# P :: Γ6) Γ7 C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
              pose (AtomImpL1Rule_I P A C Γ0 (Γ6 ++ x) (Γ4 ++ Γ7)). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
          + inversion e1. subst. simpl. repeat rewrite <- app_assoc ; simpl. exists (Γ0 ++ Γ6 ++ x ++ # P :: x0 ++ A :: Γ4 ++ Γ7, C). repeat split. 2: right.
              pose (list_exch_LI Γ0 (A :: Γ4) (x ++ # P :: x0) Γ6 Γ7 C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
              pose (AtomImpL1Rule_I P A C (Γ0 ++ Γ6 ++ x) x0 (Γ4 ++ Γ7)). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto. }
  * inversion e0 ; subst. apply app2_find_hole in H1. destruct H1. repeat destruct s ; destruct p ; subst.
    + destruct Γ4.
       { simpl in e1. destruct Γ5.
          - simpl in e1. destruct Γ6.
            * simpl in e1. subst. simpl. exists (Γ0 ++ A :: Γ1 ++ # P :: Γ2, C). repeat split ; auto. apply list_exch_L_id.
            * inversion e1. subst. simpl. exists (Γ0 ++ A :: Γ1 ++ # P :: Γ6 ++ Γ7, C). repeat split ; auto. apply list_exch_L_id.
          - inversion e1. subst. simpl. exists (Γ0 ++ A :: Γ1 ++ Γ6 ++ # P :: Γ5 ++ Γ7, C). repeat split ; auto. 2: left.
            pose (list_exch_LI (Γ0 ++ A :: Γ1) (# P :: Γ5) [] Γ6 Γ7 C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
            pose (AtomImpL2Rule_I P A C Γ0 (Γ1 ++ Γ6) (Γ5 ++ Γ7)). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto. }
       { inversion e1. subst. simpl. exists (Γ0 ++ A :: Γ1 ++ Γ6 ++ Γ5 ++ # P :: Γ4 ++ Γ7, C). repeat split ; auto. 2: left.
         pose (list_exch_LI (Γ0 ++ A :: Γ1) (# P :: Γ4) Γ5 Γ6 Γ7 C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
         pose (AtomImpL2Rule_I P A C Γ0 (Γ1 ++ Γ6 ++ Γ5) (Γ4 ++ Γ7)). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto. }
    + destruct x0.
      { destruct Γ4.
       { simpl in e1. destruct Γ5.
          - simpl in e1. destruct Γ6.
            * simpl in e1. subst. simpl. exists (Γ0 ++ A :: Γ1 ++ # P :: Γ2, C). repeat rewrite <- app_assoc; repeat split ; auto. apply list_exch_L_id.
            * inversion e1. subst. simpl. exists (Γ0 ++ A :: Γ1 ++ # P :: Γ6 ++ Γ7, C). repeat rewrite <- app_assoc ; repeat split ; auto. apply list_exch_L_id.
          - inversion e1. subst. simpl. repeat rewrite <- app_assoc ; simpl. exists (Γ0 ++ A :: Γ1 ++ Γ6 ++ # P :: Γ5 ++ Γ7, C). repeat split ; auto. 2: left.
            pose (list_exch_LI (Γ0 ++ A :: Γ1) (# P :: Γ5) [] Γ6 Γ7 C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
            pose (AtomImpL2Rule_I P A C Γ0 (Γ1 ++ Γ6) (Γ5 ++ Γ7)). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto. }
       { inversion e1. subst. simpl. repeat rewrite <- app_assoc ; simpl. exists (Γ0 ++ A :: Γ1 ++ Γ6 ++ Γ5 ++ # P :: Γ4 ++ Γ7, C). repeat split ; auto. 2: left.
         pose (list_exch_LI (Γ0 ++ A :: Γ1) (# P :: Γ4) Γ5 Γ6 Γ7 C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
         pose (AtomImpL2Rule_I P A C Γ0 (Γ1 ++ Γ6 ++ Γ5) (Γ4 ++ Γ7)). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto. } }
      { inversion e1. subst. simpl. repeat rewrite <- app_assoc ; simpl. exists (Γ0 ++ A :: Γ1 ++ # P :: x0 ++ Γ6 ++ Γ5 ++ Γ4 ++ Γ7, C). repeat split ; auto. 2: left. 2: apply AtomImpL2Rule_I.
        pose (list_exch_LI (Γ0 ++ A :: Γ1 ++ # P :: x0) Γ4 Γ5 Γ6 Γ7 C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l. }
    + apply app2_find_hole in e1. destruct e1. repeat destruct s ; destruct p ; subst.
       { destruct Γ5.
          - simpl in e1. destruct Γ6.
            * simpl in e1. subst. simpl. repeat rewrite <- app_assoc ; simpl. exists (Γ0 ++ A :: x ++ Γ4 ++ # P :: Γ2, C). repeat split ; auto. 2: left. apply list_exch_L_id.
              pose (AtomImpL2Rule_I P A C Γ0 (x ++ Γ4) Γ2). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
            * inversion e1. subst. simpl. repeat rewrite <- app_assoc ; simpl. exists (Γ0 ++ A :: x ++ # P :: Γ6 ++ Γ4 ++ Γ7, C). repeat split ; auto. 2: left. 2: apply AtomImpL2Rule_I.
              pose (list_exch_LI (Γ0 ++ A :: x) Γ4 [] (# P :: Γ6) Γ7 C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
          - inversion e1. subst. simpl. repeat rewrite <- app_assoc ; simpl. exists (Γ0 ++ A :: x ++ Γ6 ++ # P :: Γ5 ++ Γ4 ++ Γ7, C). repeat split ; auto. 2: left.
            pose (list_exch_LI (Γ0 ++ A :: x) Γ4 (# P :: Γ5) Γ6 Γ7 C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
            pose (AtomImpL2Rule_I P A C Γ0 (x ++ Γ6) (Γ5 ++ Γ4 ++ Γ7)). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto. }
       { apply app2_find_hole in e1. destruct e1. repeat destruct s ; destruct p ; subst.
          - destruct Γ6.
            * simpl in e1. subst. simpl. repeat rewrite <- app_assoc ; simpl. exists (Γ0 ++ A :: x ++ Γ5 ++ Γ4 ++ # P :: Γ2, C). repeat split ; auto. 2: left.
              pose (list_exch_LI (Γ0 ++ A :: x) Γ4 [] Γ5 (# P :: Γ2) C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
              pose (AtomImpL2Rule_I P A C Γ0 (x ++ Γ5 ++ Γ4) Γ2). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
            * inversion e1. subst. simpl. repeat rewrite <- app_assoc ; simpl. exists (Γ0 ++ A :: x ++  # P :: Γ6 ++ Γ5 ++ Γ4 ++ Γ7, C). repeat split ; auto. 2: left. 2: apply AtomImpL2Rule_I.
              pose (list_exch_LI (Γ0 ++ A :: x) Γ4 Γ5 (# P :: Γ6) Γ7 C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
          - apply app2_find_hole in e1. destruct e1. repeat destruct s ; destruct p ; subst.
            * simpl. repeat rewrite <- app_assoc ; simpl. exists (Γ0 ++ A :: x ++ Γ6 ++ Γ5 ++ Γ4 ++ # P :: Γ2, C). repeat split ; auto. 2: left.
              pose (list_exch_LI (Γ0 ++ A :: x) Γ4 Γ5 Γ6 (# P :: Γ2) C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
              pose (AtomImpL2Rule_I P A C Γ0 (x ++ Γ6 ++ Γ5 ++ Γ4) Γ2). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
            * simpl. repeat rewrite <- app_assoc ; simpl. exists (Γ0 ++ A :: x ++ Γ6 ++ Γ5 ++ Γ4 ++ x1 ++ # P :: Γ2, C). repeat split ; auto. 2: left.
              pose (list_exch_LI (Γ0 ++ A :: x) Γ4 Γ5 Γ6 (x1 ++ # P :: Γ2) C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
              pose (AtomImpL2Rule_I P A C Γ0 (x ++ Γ6 ++ Γ5 ++ Γ4 ++ x1) Γ2). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
            * destruct x1.
              + simpl in e1. subst. simpl. repeat rewrite <- app_assoc ; simpl. exists(Γ0 ++ A :: x ++ x0 ++ Γ5 ++ Γ4 ++ # P :: Γ2, C). repeat split ; auto. 2: left.
                 pose (list_exch_LI (Γ0 ++ A :: x) Γ4 Γ5 x0 (# P :: Γ2) C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
                 pose (AtomImpL2Rule_I P A C Γ0 (x ++ x0 ++ Γ5 ++ Γ4) Γ2). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
              + inversion e1. subst. simpl. repeat rewrite <- app_assoc ; simpl. exists (Γ0 ++ A :: x ++ x0 ++ # P :: x1 ++ Γ5 ++ Γ4 ++ Γ7, C). repeat split ; auto. 2: left.
                 pose (list_exch_LI (Γ0 ++ A :: x) Γ4 Γ5 (x0 ++ # P :: x1) Γ7 C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
                 pose (AtomImpL2Rule_I P A C Γ0 (x ++ x0) (x1 ++ Γ5 ++ Γ4 ++ Γ7)). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
          - destruct x0.
            * simpl in e1. destruct Γ6.
              + simpl in e1. subst. simpl. repeat rewrite <- app_assoc ; simpl. exists (Γ0 ++ A :: x ++ x1 ++ Γ4 ++ # P :: Γ2, C). repeat split ; auto. 2: left.
                 pose (list_exch_LI (Γ0 ++ A :: x) Γ4 [] x1 (# P :: Γ2) C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
                 pose (AtomImpL2Rule_I P A C Γ0 (x ++ x1 ++ Γ4) Γ2). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
              + inversion e1. subst. simpl. repeat rewrite <- app_assoc ; simpl. exists (Γ0 ++ A :: x ++ # P :: Γ6 ++ x1 ++ Γ4 ++ Γ7, C). repeat split ; auto. 2: left.
                 pose (list_exch_LI (Γ0 ++ A :: x) Γ4 x1 (# P :: Γ6) Γ7 C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
                 pose (AtomImpL2Rule_I P A C Γ0 x (Γ6 ++ x1 ++ Γ4 ++ Γ7)). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
            * inversion e1. subst. simpl. repeat rewrite <- app_assoc ; simpl. exists (Γ0 ++ A :: x ++ Γ6 ++ x1 ++ # P :: x0 ++ Γ4 ++ Γ7, C). repeat split ; auto. 2: left.
              pose (list_exch_LI (Γ0 ++ A :: x) Γ4 (x1 ++ # P :: x0) Γ6 Γ7 C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
              pose (AtomImpL2Rule_I P A C Γ0 (x ++ Γ6 ++ x1) (x0 ++ Γ4 ++ Γ7)). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto. }
       { destruct x1.
          - simpl in e1. destruct Γ5.
            * simpl in e1. destruct Γ6.
              + simpl in e1. subst. simpl. repeat rewrite <- app_assoc ; simpl. exists (Γ0 ++ A :: x ++ x0 ++ # P :: Γ2, C). repeat split ; auto. 2: left. apply list_exch_L_id.
                 pose (AtomImpL2Rule_I P A C Γ0 (x ++ x0) Γ2). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
              + inversion e1. subst. simpl. repeat rewrite <- app_assoc ; simpl. exists (Γ0 ++ A :: x ++ # P :: Γ6 ++ x0 ++ Γ7, C). repeat split ; auto. 2: left.
                 pose (list_exch_LI (Γ0 ++ A :: x) x0 [] (# P :: Γ6) Γ7 C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
                 pose (AtomImpL2Rule_I P A C Γ0 x (Γ6 ++ x0 ++ Γ7)). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
            * inversion e1. subst. simpl. repeat rewrite <- app_assoc ; simpl. exists (Γ0 ++ A :: x ++ Γ6 ++ # P :: Γ5 ++ x0 ++ Γ7, C) . repeat split ; auto. 2: left.
              pose (list_exch_LI (Γ0 ++ A :: x) x0 (# P :: Γ5) Γ6 Γ7 C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
              pose (AtomImpL2Rule_I P A C Γ0 (x ++ Γ6) (Γ5 ++ x0 ++ Γ7)). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
          - inversion e1. subst. simpl. repeat rewrite <- app_assoc ; simpl. exists (Γ0 ++ A :: x ++ Γ6 ++ Γ5 ++ x0 ++ # P :: x1 ++ Γ7, C). repeat split ; auto. 2: left.
            pose (list_exch_LI (Γ0 ++ A :: x) (x0 ++ # P :: x1) Γ5 Γ6 Γ7 C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
            pose (AtomImpL2Rule_I P A C Γ0 (x ++ Γ6 ++ Γ5 ++ x0) (x1 ++ Γ7)). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto. }
- apply app2_find_hole in e0. destruct e0. repeat destruct s ; destruct p ; subst.
  * destruct Γ5. 
      + simpl in e0. simpl. destruct Γ6.
        { simpl in e0. subst. simpl. exists (Γ3 ++ Γ4 ++ A :: Γ1 ++ # P :: Γ2, C). repeat rewrite <- app_assoc in RA. split ;auto. repeat rewrite <- app_assoc. apply list_exch_L_id. }
        { simpl in e0. inversion e0. subst. simpl. apply app2_find_hole in H1. destruct H1. repeat destruct s ; destruct p ; subst.
          - exists (Γ3 ++ A :: (Γ1 ++ Γ4) ++ # P :: Γ2, C). repeat split. 2: left.
            pose (list_exch_LI Γ3 Γ4 [] (A :: Γ1) (# P :: Γ2) C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
            pose (AtomImpL2Rule_I P A C Γ3 (Γ1 ++ Γ4) Γ2). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
          - destruct x.
            + simpl in e1. subst. repeat rewrite <- app_assoc. simpl. exists (Γ3 ++ A :: Γ1 ++ Γ4 ++ # P :: Γ2, C). repeat rewrite <- app_assoc. repeat split. 2: left.
               pose (list_exch_LI Γ3 Γ4 [] (A :: Γ1) (# P :: Γ2) C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
               pose (AtomImpL2Rule_I P A C Γ3 (Γ1 ++ Γ4) Γ2). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
            + inversion e1. subst. repeat rewrite <- app_assoc. simpl. exists (Γ3 ++ A :: Γ1 ++ # P :: x ++ Γ4 ++ Γ7, C). repeat rewrite <- app_assoc. repeat split. 2: left.
               pose (list_exch_LI Γ3 Γ4 [] (A :: Γ1++ # P :: x) Γ7 C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
               pose (AtomImpL2Rule_I P A C Γ3 Γ1 (x ++ Γ4 ++ Γ7)). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
          - exists (Γ3 ++ A :: Γ6 ++ Γ4 ++ x ++ # P :: Γ2, C). repeat split. 2: left.
            pose (list_exch_LI Γ3 Γ4 [] (A :: Γ6) (x ++ # P :: Γ2) C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
            pose (AtomImpL2Rule_I P A C Γ3 (Γ6 ++ Γ4 ++ x) Γ2). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto. }
      + simpl in e0. inversion e0. subst. apply app2_find_hole in H1. destruct H1. repeat destruct s ; destruct p ; subst.
        { destruct Γ6.
            - simpl in e1. subst. simpl. exists (Γ3 ++ A :: Γ1 ++ Γ4 ++ # P :: Γ2, C).  repeat split. 2: left.
              pose (list_exch_LI Γ3 Γ4 [] (A :: Γ1) (# P :: Γ2) C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
              pose (AtomImpL2Rule_I P A C Γ3 (Γ1 ++ Γ4) Γ2). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
            - inversion e1. subst. simpl. exists (Γ3 ++ # P :: Γ6 ++ A :: Γ1 ++ Γ4 ++ Γ7, C).  repeat split. 2: right.
              pose (list_exch_LI Γ3 Γ4 (A :: Γ1) (# P :: Γ6) Γ7 C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
              pose (AtomImpL1Rule_I P A C Γ3 Γ6 (Γ1 ++ Γ4 ++ Γ7)). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto. }
        { destruct x.
            - simpl in e1. destruct Γ6.
              * simpl in e1. subst. simpl. repeat rewrite <- app_assoc ; simpl. exists (Γ3 ++ A :: Γ1 ++ Γ4 ++ # P :: Γ2, C).  repeat split. 2: left.
                pose (list_exch_LI Γ3 Γ4 [] (A :: Γ1) (# P :: Γ2) C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
                pose (AtomImpL2Rule_I P A C Γ3 (Γ1 ++ Γ4) Γ2). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
              * inversion e1. subst. simpl. repeat rewrite <- app_assoc ; simpl. exists (Γ3 ++ # P :: Γ6 ++ A :: Γ1 ++ Γ4 ++ Γ7, C). repeat split. 2: right.
                pose (list_exch_LI Γ3 Γ4 (A :: Γ1) (# P :: Γ6) Γ7 C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
                pose (AtomImpL1Rule_I P A C Γ3 Γ6 (Γ1 ++ Γ4 ++ Γ7)). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
            - inversion e1. subst. simpl. repeat rewrite <- app_assoc ; simpl. exists (Γ3 ++ Γ6 ++ A :: Γ1 ++ # P :: x ++ Γ4 ++ Γ7, C).  repeat split. 2: left.
              pose (list_exch_LI Γ3 Γ4 (A :: Γ1 ++ # P :: x) Γ6 Γ7 C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
              pose (AtomImpL2Rule_I P A C (Γ3 ++ Γ6) Γ1 (x ++ Γ4 ++ Γ7)). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto. }
        { apply app2_find_hole in e1. destruct e1. repeat destruct s ; destruct p ; subst.
          - exists ((Γ3 ++ Γ6) ++ A :: (Γ5 ++ Γ4) ++ # P :: Γ2, C). repeat split. 2: left.
            pose (list_exch_LI Γ3 Γ4 (A :: Γ5) Γ6 (# P :: Γ2) C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
            pose (AtomImpL2Rule_I P A C (Γ3 ++ Γ6) (Γ5 ++ Γ4) Γ2). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
          - exists ((Γ3 ++ Γ6) ++ A :: (Γ5 ++ Γ4 ++ x1) ++ # P :: Γ2, C). repeat split. 2: left.
            pose (list_exch_LI Γ3 Γ4 (A :: Γ5) Γ6 (x1 ++ # P :: Γ2) C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
            pose (AtomImpL2Rule_I P A C (Γ3 ++ Γ6) (Γ5 ++ Γ4 ++ x1) Γ2). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
          - destruct x1.
              * simpl in e1. subst. simpl. repeat rewrite <- app_assoc ; simpl. exists (Γ3 ++ x ++ A :: Γ5 ++ Γ4 ++ # P :: Γ2, C).  repeat split. 2: left.
                pose (list_exch_LI Γ3 Γ4 (A :: Γ5) x (# P :: Γ2) C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
                pose (AtomImpL2Rule_I P A C (Γ3 ++ x) (Γ5 ++ Γ4) Γ2). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
              * inversion e1. subst. simpl. repeat rewrite <- app_assoc ; simpl. exists (Γ3 ++ x ++ # P :: x1 ++ A :: Γ5 ++ Γ4 ++ Γ7, C).  repeat split. 2: right.
                pose (list_exch_LI Γ3 Γ4 (A :: Γ5) (x ++ # P :: x1) Γ7 C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
                pose (AtomImpL1Rule_I P A C (Γ3 ++ x) x1 (Γ5 ++ Γ4 ++ Γ7)). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto. }
  * apply app2_find_hole in e0. destruct e0. repeat destruct s ; destruct p ; subst.
      + simpl in e0. simpl. destruct Γ6.
        {  simpl in e0. subst. simpl. exists (Γ3 ++ Γ5 ++ Γ4 ++ A :: Γ1 ++ # P :: Γ2, C).  repeat split. 2: left.
           pose (list_exch_LI Γ3 Γ4 [] Γ5 (A :: Γ1 ++ # P :: Γ2) C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
           pose (AtomImpL2Rule_I P A C (Γ3 ++ Γ5 ++ Γ4) Γ1 Γ2). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto. }
         { inversion e0. subst. apply app2_find_hole in H1. destruct H1. repeat destruct s ; destruct p ; subst.
            - simpl. exists (Γ3 ++ A :: Γ1 ++ Γ5 ++ Γ4 ++ # P :: Γ2, C).  repeat split. 2: left.
              pose (list_exch_LI Γ3 Γ4 Γ5 (A :: Γ1) (# P :: Γ2) C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
              pose (AtomImpL2Rule_I P A C Γ3 (Γ1 ++ Γ5 ++ Γ4) Γ2). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
            - destruct x0.
              * simpl in e1. subst. simpl. repeat rewrite <- app_assoc. simpl. exists (Γ3 ++ A :: Γ1 ++ Γ5 ++ Γ4 ++ # P :: Γ2, C). repeat split. 2: left.
                pose (list_exch_LI Γ3 Γ4 Γ5 (A :: Γ1) (# P :: Γ2) C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
                pose (AtomImpL2Rule_I P A C Γ3 (Γ1 ++ Γ5 ++ Γ4) Γ2). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
              * inversion e1. subst. simpl. repeat rewrite <- app_assoc. simpl. exists (Γ3 ++ A :: Γ1 ++ # P :: x0 ++ Γ5 ++ Γ4 ++ Γ7, C).  repeat split. 2: left.
                pose (list_exch_LI Γ3 Γ4 Γ5 (A :: Γ1 ++ # P :: x0) Γ7 C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
                pose (AtomImpL2Rule_I P A C Γ3 Γ1 (x0 ++ Γ5 ++ Γ4 ++ Γ7)). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
            - simpl. repeat rewrite <- app_assoc. simpl. exists (Γ3 ++ A :: Γ6 ++ Γ5 ++ Γ4 ++ x0 ++ # P :: Γ2, C).  repeat split. 2: left.
              pose (list_exch_LI Γ3 Γ4 Γ5 (A :: Γ6) (x0 ++ # P :: Γ2) C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
              pose (AtomImpL2Rule_I P A C Γ3 (Γ6 ++ Γ5 ++ Γ4 ++ x0) Γ2). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto. }
      + subst. apply app2_find_hole in e0. destruct e0. repeat destruct s ; destruct p ; subst.
          { exists ((Γ3 ++ Γ6 ++ Γ5 ++ Γ4) ++ A :: Γ1 ++ # P :: Γ2, C) . repeat split. 2: left. repeat rewrite <- app_assoc ; apply list_exch_LI.
            pose (AtomImpL2Rule_I P A C (Γ3 ++ Γ6 ++ Γ5 ++ Γ4) Γ1 Γ2). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto. }
          { exists ((Γ3 ++ Γ6 ++ Γ5 ++ Γ4 ++ x0) ++ A :: Γ1 ++ # P :: Γ2, C). split. 2: left. repeat rewrite <- app_assoc ; apply list_exch_LI. 
            pose (AtomImpL2Rule_I P A C (Γ3 ++ Γ6 ++ Γ5 ++ Γ4 ++ x0) Γ1 Γ2). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto. }
          { destruct x0 ; simpl in e0 ; inversion e0 ; subst.
            - repeat rewrite <- app_assoc ; simpl. exists ((Γ3 ++ x ++ Γ5 ++ Γ4) ++ A :: Γ1 ++ # P :: Γ2, C). repeat split. repeat rewrite <- app_assoc ; apply list_exch_LI.
              left. pose (AtomImpL2Rule_I P A C (Γ3 ++ x ++ Γ5 ++ Γ4) Γ1 Γ2). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
            - apply app2_find_hole in H1. destruct H1. repeat destruct s ; destruct p ; subst.
              + exists((Γ3 ++ x) ++ A :: (Γ1 ++ Γ5 ++ Γ4) ++ # P :: Γ2, C). repeat split. 2: left.
                 pose (list_exch_LI Γ3 Γ4 Γ5 (x ++ A :: Γ1) (# P :: Γ2) C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
                 pose (AtomImpL2Rule_I P A C (Γ3 ++ x) (Γ1 ++ Γ5 ++ Γ4) Γ2). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
              + destruct x1.
                 *  simpl in e1 ; subst. repeat rewrite <- app_assoc ; simpl. repeat rewrite <- app_assoc ; simpl.
                    exists (Γ3 ++ x ++ A :: Γ1 ++ Γ5 ++ Γ4 ++ # P :: Γ2, C). repeat split. 2: left.
                    pose (list_exch_LI Γ3 Γ4 Γ5 (x ++ A :: Γ1) (# P :: Γ2) C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
                    pose (AtomImpL2Rule_I P A C (Γ3 ++ x) (Γ1 ++ Γ5 ++ Γ4) Γ2). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
                 *  inversion e1 ; subst. repeat rewrite <- app_assoc ; simpl. repeat rewrite <- app_assoc ; simpl. exists (Γ3 ++ x ++ A :: Γ1 ++ # P :: x1 ++ Γ5 ++ Γ4 ++ Γ7, C). repeat split. 2: left.
                    pose (list_exch_LI Γ3 Γ4 Γ5 (x ++ A :: Γ1 ++ # P :: x1) Γ7 C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
                    pose (AtomImpL2Rule_I P A C (Γ3 ++ x) Γ1 (x1 ++ Γ5 ++ Γ4 ++ Γ7)). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
              + repeat rewrite <- app_assoc. simpl. exists (Γ3 ++ x ++ A :: x0 ++ Γ5 ++ Γ4 ++ x1 ++ # P :: Γ2, C). repeat split. 2: left.
                 pose (list_exch_LI Γ3 Γ4 Γ5 (x ++ A :: x0) (x1 ++ # P :: Γ2) C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
                 pose (AtomImpL2Rule_I P A C (Γ3 ++ x) (x0 ++ Γ5 ++ Γ4 ++ x1) Γ2). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto. }
      + destruct x ; simpl in e0 ; inversion e0 ; subst.
          { destruct Γ6.
            - simpl in e0. subst. simpl in H0. simpl. repeat rewrite <- app_assoc. simpl. exists ((Γ3 ++ x0 ++ Γ4) ++ A :: Γ1 ++ # P :: Γ2, C). split ;auto. 2: left.
              pose (list_exch_LI Γ3 Γ4 [] x0 (A :: Γ1 ++ # P :: Γ2) C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
              pose (AtomImpL2Rule_I P A C (Γ3 ++ x0 ++ Γ4) Γ1 Γ2). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
            - simpl in e0. inversion e0. clear H0. subst. simpl. repeat rewrite <- app_assoc. simpl.
              apply app2_find_hole in H2. destruct H2. repeat destruct s ; destruct p ; subst.
              + exists (Γ3 ++ A :: (Γ1 ++ x0 ++ Γ4) ++ # P :: Γ2, C). repeat split. 2: left.
                 pose (list_exch_LI Γ3 Γ4 x0 (A :: Γ1) (# P :: Γ2) C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
                 pose (AtomImpL2Rule_I P A C Γ3 (Γ1 ++ x0 ++ Γ4) Γ2). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
              + destruct x.
                 * simpl in e1 ; subst. repeat rewrite <- app_assoc ; simpl. exists (Γ3 ++ A :: Γ1 ++ x0 ++ Γ4 ++ # P :: Γ2, C). repeat split. 2: left.
                   pose (list_exch_LI Γ3 Γ4 x0 (A :: Γ1) (# P :: Γ2) C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
                   pose (AtomImpL2Rule_I P A C Γ3 (Γ1 ++ x0 ++ Γ4) Γ2). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
                 * inversion e1. subst. repeat rewrite <- app_assoc. simpl. exists (Γ3 ++ A :: Γ1 ++ # P :: x ++ x0 ++ Γ4 ++ Γ7, C). repeat split. 2: left. 2: apply AtomImpL2Rule_I.
                   pose (list_exch_LI Γ3 Γ4 x0 (A :: Γ1 ++ # P :: x) Γ7 C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
              + exists (Γ3 ++ A :: Γ6 ++ x0 ++ Γ4 ++ x ++ # P :: Γ2, C). repeat split. 2: left.
                 pose (list_exch_LI Γ3 Γ4 x0 (A :: Γ6) (x ++ # P :: Γ2) C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
                 pose (AtomImpL2Rule_I P A C Γ3 (Γ6 ++ x0 ++ Γ4 ++ x) Γ2). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto. }
        { apply app2_find_hole in H1. destruct H1. repeat destruct s ; destruct p ; subst.
          - destruct Γ6.
             * repeat rewrite <- app_assoc ; simpl. simpl in e1. subst. exists (Γ3 ++ x0 ++ A :: Γ1 ++ Γ4 ++ # P :: Γ2, C). split ;auto. 2: left.
               pose (list_exch_LI Γ3 Γ4 [] (x0 ++ A :: Γ1) (# P :: Γ2) C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
               pose (AtomImpL2Rule_I P A C (Γ3 ++ x0) (Γ1 ++ Γ4) Γ2). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
             * repeat rewrite <- app_assoc ; simpl. inversion e1. subst. exists (Γ3 ++ # P :: Γ6 ++ x0 ++ A :: Γ1 ++ Γ4 ++ Γ7, C). split ;auto. 2: right.
               pose (list_exch_LI Γ3 Γ4 (x0 ++ A :: Γ1) (# P :: Γ6) Γ7 C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
               pose (AtomImpL1Rule_I P A C Γ3 (Γ6 ++ x0) (Γ1 ++ Γ4 ++ Γ7)). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
          - destruct x1.
             * simpl in e1. destruct Γ6.
                + repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; simpl. simpl in e1. subst. exists (Γ3 ++ x0 ++ A :: Γ1 ++ Γ4 ++ # P :: Γ2, C). split ;auto. 2: left.
                   pose (list_exch_LI Γ3 Γ4 [] (x0 ++ A :: Γ1) (# P :: Γ2) C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
                   pose (AtomImpL2Rule_I P A C (Γ3 ++ x0) (Γ1 ++ Γ4) Γ2). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
                + repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; simpl. inversion e1. subst. exists (Γ3 ++ # P :: Γ6 ++ x0 ++ A :: Γ1 ++ Γ4 ++ Γ7, C). split ;auto. 2: right.
                   pose (list_exch_LI Γ3 Γ4 (x0 ++ A :: Γ1) (# P :: Γ6) Γ7 C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
                   pose (AtomImpL1Rule_I P A C Γ3 (Γ6 ++ x0) (Γ1 ++ Γ4 ++ Γ7)). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
             * repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; simpl. inversion e1. subst. exists (Γ3 ++ Γ6 ++ x0 ++ A :: Γ1 ++ # P :: x1 ++ Γ4 ++ Γ7, C). split ;auto. 2: left.
               pose (list_exch_LI Γ3 Γ4 (x0 ++ A :: Γ1 ++ # P :: x1) Γ6 Γ7 C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
               pose (AtomImpL2Rule_I P A C (Γ3 ++ Γ6 ++ x0) Γ1 (x1 ++ Γ4 ++ Γ7)). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
          - apply app2_find_hole in e1. destruct e1. repeat destruct s ; destruct p ; subst.
            + repeat rewrite <- app_assoc ; simpl. exists (Γ3 ++ Γ6 ++ x0 ++ A :: x ++ Γ4 ++ # P :: Γ2, C). split ;auto. 2: left.
               pose (list_exch_LI Γ3 Γ4 (x0 ++ A :: x) Γ6 (# P :: Γ2) C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
               pose (AtomImpL2Rule_I P A C (Γ3 ++ Γ6 ++ x0) (x ++ Γ4) Γ2). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
            + repeat rewrite <- app_assoc ; simpl. exists (Γ3 ++ Γ6 ++ x0 ++ A :: x ++ Γ4 ++ x2 ++ # P :: Γ2, C). split ;auto. 2: left.
               pose (list_exch_LI Γ3 Γ4 (x0 ++ A :: x) Γ6 (x2 ++ # P :: Γ2) C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
               pose (AtomImpL2Rule_I P A C (Γ3 ++ Γ6 ++ x0) (x ++ Γ4 ++ x2) Γ2). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
            + destruct x2.
              *  repeat rewrite <- app_assoc ; simpl. simpl in e1. subst. exists (Γ3 ++ x1 ++ x0 ++ A :: x ++ Γ4 ++ # P :: Γ2, C). split ;auto. 2: left.
                 pose (list_exch_LI Γ3 Γ4 (x0 ++ A :: x) x1 (# P :: Γ2) C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
                 pose (AtomImpL2Rule_I P A C (Γ3 ++ x1 ++ x0) (x ++ Γ4) Γ2). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
              *  repeat rewrite <- app_assoc ; simpl. inversion e1. subst. exists (Γ3 ++ x1 ++ # P :: x2 ++ x0 ++ A :: x ++ Γ4 ++ Γ7, C). split ;auto. 2: right.
                 pose (list_exch_LI Γ3 Γ4 (x0 ++ A :: x) (x1 ++ # P :: x2) Γ7 C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
                 pose (AtomImpL1Rule_I P A C (Γ3 ++ x1) (x2 ++ x0) (x ++ Γ4 ++ Γ7)). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto. }
  * destruct x0 ; simpl in e0 ; inversion e0 ; subst.
      + destruct Γ5 ; simpl in e0 ; inversion e0 ; subst.
          { destruct Γ6.
            - simpl in H1. subst. repeat rewrite <- app_assoc. simpl. exists ((Γ3 ++ x) ++ A :: Γ1 ++ # P :: Γ2, C). repeat split. 2: left. repeat rewrite <- app_assoc. apply list_exch_L_id.
              pose (AtomImpL2Rule_I P A C (Γ3 ++ x) Γ1 Γ2). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
            - simpl in H1. inversion H1. subst. apply app2_find_hole in H3. destruct H3. repeat destruct s ; destruct p ; subst.
              * repeat rewrite <- app_assoc. simpl. exists (Γ3 ++ A :: Γ1 ++ x ++ # P :: Γ2, C). repeat split. 2: left.
                pose (list_exch_LI Γ3 x [] (A :: Γ1) (# P :: Γ2) C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
                pose (AtomImpL2Rule_I P A C Γ3 (Γ1 ++ x) Γ2). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
              * destruct x0.
               + simpl in e1 ; subst. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. simpl. exists (Γ3 ++ A :: Γ1 ++ x ++ # P :: Γ2, C). repeat split. 2: left.
                  pose (list_exch_LI Γ3 x [] (A :: Γ1) (# P :: Γ2) C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
                  pose (AtomImpL2Rule_I P A C Γ3 (Γ1 ++ x) Γ2). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
               + inversion e1 ; subst. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. simpl. exists (Γ3 ++ A :: Γ1 ++ # P :: x0 ++ x ++ Γ7, C). repeat split. 2: left.
                  pose (list_exch_LI Γ3 x [] (A :: Γ1 ++ # P :: x0) Γ7 C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
                  pose (AtomImpL2Rule_I P A C Γ3 Γ1 (x0 ++ x ++ Γ7)). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
              * repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. exists (Γ3 ++ A :: (Γ6 ++ x ++ x0) ++ # P :: Γ2, C). repeat split. 2: left.
                pose (list_exch_LI Γ3 x [] (A :: Γ6) (x0 ++ # P :: Γ2) C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
                pose (AtomImpL2Rule_I P A C Γ3 (Γ6 ++ x ++ x0) Γ2). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto. }
          { apply app2_find_hole in H2. destruct H2. repeat destruct s ; destruct p ; subst.
            - destruct Γ6.
              * simpl in e1 ; subst. repeat rewrite <- app_assoc. simpl. exists (Γ3 ++ A :: Γ1 ++ x ++ # P :: Γ2, C). repeat split. 2: left.
                pose (list_exch_LI Γ3 x [] (A :: Γ1) (# P :: Γ2) C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
                pose (AtomImpL2Rule_I P A C Γ3 (Γ1 ++ x) Γ2). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
              * inversion e1 ; subst. repeat rewrite <- app_assoc. simpl. exists (Γ3 ++ # P :: Γ6 ++ A :: Γ1 ++ x ++ Γ7, C). repeat split. 2: right.
                pose (list_exch_LI Γ3 x (A :: Γ1) (# P :: Γ6) Γ7 C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
                pose (AtomImpL1Rule_I P A C Γ3 Γ6 (Γ1 ++ x ++ Γ7)). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
            - destruct x0.
              * simpl in e1. destruct Γ6.
                + simpl in e1 ; subst. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. simpl. exists (Γ3 ++ A :: (Γ1 ++ x) ++ # P :: Γ2, C). repeat split. 2: left.
                   pose (list_exch_LI Γ3 x [] (A :: Γ1) (# P :: Γ2) C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
                   pose (AtomImpL2Rule_I P A C Γ3 (Γ1 ++ x) Γ2). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
                + inversion e1 ; subst. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. simpl. exists (Γ3 ++ # P :: Γ6 ++ A :: Γ1 ++ x ++ Γ7, C). repeat split. 2: right.
                   pose (list_exch_LI Γ3 x (A :: Γ1) (# P :: Γ6) Γ7 C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
                   pose (AtomImpL1Rule_I P A C Γ3 Γ6 (Γ1 ++ x ++ Γ7)). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
              * inversion e1. subst. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. simpl. exists ((Γ3 ++ Γ6) ++ A :: Γ1 ++ # P :: x0 ++ x ++ Γ7, C). repeat split. 2: left.
                pose (list_exch_LI Γ3 x (A :: Γ1 ++ # P :: x0) Γ6 Γ7 C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
                pose (AtomImpL2Rule_I P A C (Γ3 ++ Γ6) Γ1 (x0 ++ x ++ Γ7)). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
            - repeat rewrite <- app_assoc. simpl. apply app2_find_hole in e1. destruct e1. repeat destruct s ; destruct p ; subst.
              * exists ((Γ3 ++ Γ6) ++ A :: (Γ5 ++ x) ++  # P :: Γ2, C). repeat split. 2: left.
                pose (list_exch_LI Γ3 x (A :: Γ5) Γ6 (# P :: Γ2) C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
                pose (AtomImpL2Rule_I P A C (Γ3 ++ Γ6) (Γ5 ++ x) Γ2). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
              * exists ((Γ3 ++ Γ6) ++ A :: (Γ5 ++ x ++ x1) ++ # P :: Γ2, C). repeat split. 2: left.
                pose (list_exch_LI Γ3 x (A :: Γ5) Γ6 (x1 ++ # P :: Γ2) C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
                pose (AtomImpL2Rule_I P A C (Γ3 ++ Γ6) (Γ5 ++ x ++ x1) Γ2). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
              * destruct x1.
                + simpl in e1. subst. repeat rewrite <- app_assoc. simpl. exists ((Γ3 ++ x0) ++ A :: (Γ5 ++ x) ++ # P :: Γ2, C). repeat split. 2: left.
                   pose (list_exch_LI Γ3 x (A :: Γ5) x0 (# P :: Γ2) C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
                   pose (AtomImpL2Rule_I P A C (Γ3 ++ x0) (Γ5 ++ x) Γ2). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
                + inversion e1. subst. repeat rewrite <- app_assoc. simpl. exists ((Γ3 ++ x0) ++ # P :: x1 ++ A :: Γ5 ++ x ++ Γ7, C). repeat split. 2: right.
                   pose (list_exch_LI Γ3 x (A :: Γ5) (x0 ++ # P :: x1) Γ7 C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
                   pose (AtomImpL1Rule_I P A C (Γ3 ++ x0) x1 (Γ5 ++ x ++ Γ7)). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto. }
      + apply app2_find_hole in H1. destruct H1. repeat destruct s ; destruct p ; subst.
        {  destruct Γ5.
            - simpl in e1. destruct Γ6.
              * simpl in e1.  subst. simpl. repeat rewrite <- app_assoc ; simpl. exists ((Γ3 ++ x) ++ A :: Γ1 ++ # P :: Γ2, C). repeat split. 2: left.
                repeat rewrite <- app_assoc. apply list_exch_L_id.
                pose (AtomImpL2Rule_I P A C (Γ3 ++ x) Γ1 Γ2). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
              * inversion e1 ; subst. simpl. repeat rewrite <- app_assoc ; simpl. exists (Γ3 ++ # P :: (Γ6 ++ x) ++ A :: Γ1 ++ Γ7, C). repeat split. 2: right.
                pose (list_exch_LI Γ3 [] (x ++ A :: Γ1) (# P :: Γ6) Γ7 C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
                pose (AtomImpL1Rule_I P A C Γ3 (Γ6 ++ x) (Γ1 ++ Γ7)). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
            - inversion e1 ; subst. simpl. repeat rewrite <- app_assoc ; simpl. exists ((Γ3 ++ Γ6) ++ # P :: (Γ5 ++ x) ++ A :: Γ1 ++ Γ7, C). repeat split. 2: right.
              pose (list_exch_LI Γ3 (x ++ A :: Γ1) (# P :: Γ5) Γ6 Γ7 C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
              pose (AtomImpL1Rule_I P A C (Γ3 ++ Γ6) (Γ5 ++ x) (Γ1 ++ Γ7)). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto. }
        { destruct x1.
            - simpl in e1. destruct Γ5.
              + simpl in e1. destruct Γ6.
                { simpl in e1.  subst. simpl. repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; simpl.
                  exists ((Γ3 ++ x) ++ A :: Γ1 ++ # P :: Γ2, C). repeat split. 2: left. repeat rewrite <- app_assoc. apply list_exch_L_id.
                  pose (AtomImpL2Rule_I P A C (Γ3 ++ x) Γ1 Γ2). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto. }
                { inversion e1 ; subst. simpl. repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; simpl. exists (Γ3 ++ # P :: (Γ6 ++ x) ++ A :: Γ1 ++ Γ7, C). repeat split. 2: right.
                  pose (list_exch_LI Γ3 (x ++ A :: Γ1) [] (# P :: Γ6) Γ7 C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
                  pose (AtomImpL1Rule_I P A C Γ3 (Γ6 ++ x) (Γ1 ++ Γ7)). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto. }
              + inversion e1 ; subst. simpl. repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; simpl. exists ((Γ3 ++ Γ6) ++ # P :: (Γ5 ++ x) ++ A :: Γ1 ++ Γ7, C). repeat split. 2: right.
                 pose (list_exch_LI Γ3 (x ++ A :: Γ1) (# P :: Γ5) Γ6 Γ7 C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
                 pose (AtomImpL1Rule_I P A C (Γ3 ++ Γ6) (Γ5 ++ x) (Γ1 ++ Γ7)). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
            - inversion e1 ; subst ; simpl. repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; simpl. exists ((Γ3 ++ Γ6 ++ Γ5 ++ x) ++ A :: Γ1 ++ # P :: x1 ++ Γ7, C). repeat split. 2: left.
              pose (list_exch_LI Γ3 (x ++ A :: Γ1 ++ # P :: x1) Γ5 Γ6 Γ7 C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
              pose (AtomImpL2Rule_I P A C (Γ3 ++ Γ6 ++ Γ5 ++ x) Γ1 (x1 ++ Γ7)). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto. }
        { apply app2_find_hole in e1. destruct e1. repeat destruct s ; destruct p ; subst.
            - destruct Γ6.
              * simpl in e1; subst. simpl ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; simpl. exists ((Γ3 ++ Γ5 ++ x) ++ A :: x0 ++ # P :: Γ2, C). repeat split. 2: left.
                pose (list_exch_LI Γ3 (x ++ A :: x0) [] Γ5 (# P :: Γ2) C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
                pose (AtomImpL2Rule_I P A C (Γ3 ++ Γ5 ++ x) x0 Γ2). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
              * inversion e1 ; subst. simpl. repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; simpl. exists (Γ3 ++ # P :: (Γ6 ++ Γ5 ++ x) ++ A :: x0 ++ Γ7, C). repeat split. 2: right.
                pose (list_exch_LI Γ3 (x ++ A :: x0) Γ5 (# P :: Γ6) Γ7 C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
                pose (AtomImpL1Rule_I P A C Γ3 (Γ6 ++ Γ5 ++ x) (x0 ++ Γ7)). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
            - apply app2_find_hole in e1. destruct e1. repeat destruct s ; destruct p ; subst.
              * repeat rewrite <- app_assoc ; simpl. exists ((Γ3 ++ Γ6 ++ Γ5 ++ x) ++ A :: x0 ++ # P :: Γ2, C). repeat split. 2: left.
                pose (list_exch_LI Γ3 (x ++ A :: x0) Γ5 Γ6 (# P :: Γ2) C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
                pose (AtomImpL2Rule_I P A C (Γ3 ++ Γ6 ++ Γ5 ++ x) x0 Γ2). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
              * exists ((Γ3 ++ Γ6 ++ Γ5 ++ x) ++ A :: (x0 ++ x1) ++ # P :: Γ2, C). repeat split. 2: left.
                pose (list_exch_LI Γ3 (x ++ A :: x0) Γ5 Γ6 (x1 ++ # P :: Γ2) C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
                pose (AtomImpL2Rule_I P A C (Γ3 ++ Γ6 ++ Γ5 ++ x) (x0 ++ x1) Γ2). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
              * repeat rewrite <- app_assoc ; simpl. destruct x1.
                + simpl in e1. subst. simpl. exists ((Γ3 ++ x2 ++ Γ5 ++ x) ++ A :: x0 ++ # P :: Γ2, C). repeat split. 2: left.
                  pose (list_exch_LI Γ3 (x ++ A :: x0) Γ5 x2 (# P :: Γ2) C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
                  pose (AtomImpL2Rule_I P A C (Γ3 ++ x2 ++ Γ5 ++ x) x0 Γ2). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
                + inversion e1 ; subst. simpl. exists ((Γ3 ++ x2) ++ # P :: (x1 ++ Γ5 ++ x) ++ A :: x0 ++ Γ7, C). repeat split. 2: right.
                  pose (list_exch_LI Γ3 (x ++ A :: x0) Γ5 (x2 ++ # P :: x1) Γ7 C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
                  pose (AtomImpL1Rule_I P A C (Γ3 ++ x2) (x1 ++ Γ5 ++ x) (x0 ++ Γ7)). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
            - destruct x2.
              * simpl in e1. destruct Γ6.
               + simpl in e1 ; subst. simpl ; repeat rewrite <- app_assoc ; simpl. exists ((Γ3 ++ x1 ++ x) ++ A :: x0 ++ # P :: Γ2, C). repeat split. 2: left.
                  pose (list_exch_LI Γ3 (x ++ A :: x0) [] x1 (# P :: Γ2) C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
                  pose (AtomImpL2Rule_I P A C (Γ3 ++ x1 ++ x) x0 Γ2). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
               + inversion e1 ; subst. simpl ; repeat rewrite <- app_assoc ; simpl. exists (Γ3 ++ # P :: (Γ6 ++ x1 ++ x) ++ A :: x0 ++ Γ7, C). repeat split. 2: right.
                  pose (list_exch_LI Γ3 (x ++ A :: x0) x1 (# P :: Γ6) Γ7 C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
                  pose (AtomImpL1Rule_I P A C Γ3 (Γ6 ++ x1 ++ x) (x0 ++ Γ7)). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
              * inversion e1 ; subst. simpl ; repeat rewrite <- app_assoc ; simpl. exists ((Γ3 ++ Γ6 ++ x1) ++ # P :: (x2 ++ x) ++ A :: x0 ++ Γ7, C). repeat split. 2: right.
                pose (list_exch_LI Γ3 (x ++ A :: x0) (x1 ++ # P :: x2) Γ6 Γ7 C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
                pose (AtomImpL1Rule_I P A C (Γ3 ++ Γ6 ++ x1) (x2 ++ x) (x0 ++ Γ7)). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto. }
Qed.