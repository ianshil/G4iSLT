Require Import List.
Export ListNotations.

Require Import general_export.

Require Import DiSL_calc.
Require Import DG4iSL_list_lems.
Require Import DG4iSL_remove_list.


Set Implicit Arguments.

(* In this file we show that the applicability of the rules in G4iSL is decidable. *)

Lemma dec_is_atomicT : forall (A : MPropF), (is_atomicT A) + ((is_atomicT A) -> False).
Proof.
induction A.
- left. left. exists n. reflexivity.
- left. right. reflexivity.
- right. intro. inversion X. inversion H. inversion H0. inversion H.
- right. intro. inversion X. inversion H. inversion H0. inversion H.
- right. intro. inversion X. inversion H. inversion H0. inversion H.
- right. intro. inversion X. inversion H. inversion H0. inversion H.
Qed.

Lemma dec_prop_var_in0 : forall l, (existsT2 P, In (# P) l) +
                                      ((existsT2 P, In (# P) l) -> False).
Proof.
intro. induction l.
- right. intro. destruct H. destruct i.
- destruct IHl.
  * destruct s. left. exists x. apply in_cons ; auto.
  * destruct (dec_is_atomicT a).
    +  inversion i. left. destruct H. exists x. simpl. auto. right. intro. destruct H0.
        inversion i0. subst. inversion H0. apply f. exists x. auto.
    + right. intro. simpl in H. destruct H. destruct o. subst.
      { subst. apply f0. left. exists x. reflexivity. }
      { apply f. firstorder. }
Qed.

Lemma dec_prop_var_in : forall s, (existsT2 P, (In (# P) (fst s)) /\ (# P = snd s)) +
                                      ((existsT2 P, (In (# P) (fst s)) /\ (# P = snd s)) -> False).
Proof.
intro. destruct s.
induction l.
- right. intro. destruct H. destruct a. simpl in H. inversion H.
- destruct IHl.
  * destruct s. simpl in a0. destruct a0. left. exists x. simpl. split. auto. assumption.
  * destruct (dec_is_atomicT a).
    + destruct (eq_dec_form m a).
      { inversion i. left. subst. destruct H. exists x. simpl. split. auto. subst. auto.
        subst. right. simpl. intro. destruct H. destruct a. destruct H. inversion H. apply f.
        exists x. auto. }
      { right. simpl. intro. destruct H. destruct a0. destruct H.
        - subst. apply n. subst. auto.
        - apply f. simpl. exists x. firstorder. }
    + right. intro. simpl in H. destruct H. destruct a0. destruct H.
      { subst. apply f0. left. exists x. reflexivity. }
      { apply f. firstorder. }
Qed.

Lemma dec_is_boxedT : forall (A : MPropF), (is_boxedT A) + ((is_boxedT A) -> False).
Proof.
induction A.
- right. intro. inversion X. inversion H.
- right. intro. inversion X. inversion H.
- right. intro. inversion X. inversion H.
- right. intro. inversion X. inversion H.
- right. intro. inversion X. inversion H.
- left. exists A. reflexivity.
Qed.

Lemma dec_is_box : forall (A : MPropF), (existsT2 B, A = Box B) + ((existsT2 B, A = Box B ) -> False).
Proof.
destruct A.
- right. intro. destruct H. inversion e.
- right. intro. destruct H. inversion e.
- right. intro. destruct H. inversion e.
- right. intro. destruct H. inversion e.
- right. intro. destruct H. inversion e.
- left. exists A. reflexivity.
Qed.

Lemma dec_box_in : forall s, (existsT2 (A : MPropF), (In (Box A) (fst s)) /\ (Box A = snd s)) +
                             ((existsT2 (A : MPropF), (In (Box A) (fst s)) /\ (Box A = snd s)) -> False).
Proof.
intro. destruct s.
induction l.
- right. intro. destruct H. destruct a. simpl in H. inversion H.
- destruct IHl.
  * destruct s. simpl in a0. destruct a0. left. exists x. simpl. split. auto. assumption.
  * destruct (dec_is_box a).
    + destruct (eq_dec_form m a).
      { left. destruct s. subst. simpl. exists x. auto. }
      { right. simpl. intro. destruct H. destruct a0. destruct H.
        - subst. apply n. auto.
        - apply f. simpl. exists x. firstorder. }
    + right. intro. simpl in H. destruct H. destruct a0. destruct H.
      { subst. apply f0. exists x. reflexivity. }
      { apply f. firstorder. }
Qed.

(* Initial rules *)

Lemma dec_G4iSL_init_rules : forall (s : Seq) ,
          ((IdPRule [] s) + (BotLRule [] s)) +
          (((IdPRule [] s) + (BotLRule [] s)) -> False).
Proof.
intro s. destruct s. destruct (dec_prop_var_in (pair l m)).
- destruct s. destruct a. left. left. simpl in H. simpl in H0.
  apply in_splitT in H. destruct H. destruct s. subst. apply IdPRule_I.
- destruct (In_dec l (⊥)).
  + left. apply in_splitT in i. destruct i. destruct s. subst. right. apply BotLRule_I.
  + right. intro. destruct H.
    * inversion i. subst. simpl in f. apply f. exists P. split. 2: auto. apply in_or_app. right. apply in_eq.
    * inversion b. subst. apply f0. apply in_or_app. right. apply in_eq.
Qed.

Lemma dec_IdP_rule : forall (s : Seq),
          (IdPRule [] s) +
          ((IdPRule [] s) -> False).
Proof.
intro s. destruct s. destruct (dec_prop_var_in (pair l m)).
- destruct s. destruct a. left. simpl in H. simpl in H0.
  apply in_splitT in H. destruct H. destruct s. subst. apply IdPRule_I.
- right. intro. destruct H. apply f. exists P. split ; auto ; apply in_or_app ; right ; apply in_eq.
Qed.

Lemma dec_BotL_rule : forall (s : Seq),
          (BotLRule [] s) +
          ((BotLRule [] s) -> False).
Proof.
intro s. destruct s. destruct (In_dec l (⊥)).
- left. apply in_splitT in i. destruct i. destruct s. subst. apply BotLRule_I.
- right. intro. inversion H. apply f. subst. apply in_or_app. right. apply in_eq.
Qed.

(* Conjunction rules *)

Lemma dec_is_and : forall (A : MPropF), (existsT2 B C, A = And B C) + ((existsT2 B C, A = And B C) -> False).
Proof.
destruct A.
- right. intro. destruct H. destruct s. inversion e.
- right. intro. destruct H. destruct s. inversion e.
- left. exists A1. exists A2. reflexivity.
- right. intro. destruct H. destruct s. inversion e.
- right. intro. destruct H. destruct s. inversion e.
- right. intro. destruct H. destruct s. inversion e.
Qed.

Lemma dec_and_in : forall (l : list MPropF), (existsT2 A B, In (And A B) l) + ((existsT2 A B, In (And A B) l) -> False).
Proof.
induction l.
- right. intro. destruct H. destruct s. inversion i.
- destruct IHl.
  * repeat destruct s. left. exists x. exists x0. apply in_cons. assumption.
  * destruct (dec_is_and a).
    + repeat destruct s. subst. left. exists x. exists x0. apply in_eq.
    + right. intro. destruct H. destruct s. inversion i.
      { subst. apply f0. exists x. exists x0. reflexivity. }
      { apply f. exists x. exists x0. assumption. }
Qed.

Lemma dec_AndR_rule : forall (concl : Seq),
          (existsT2 prem1 prem2, AndRRule [prem1;prem2] concl) + ((existsT2 prem1 prem2, AndRRule [prem1 ; prem2] concl) -> False).
Proof.
intros concl. destruct concl. destruct (dec_is_and m).
- left. repeat destruct s. subst. exists (l, x). exists (l, x0). apply AndRRule_I.
- right. intro. destruct H. destruct s. inversion a. subst. apply f. exists A. exists B. auto.
Qed.

Lemma dec_AndL_rule : forall (concl : Seq),
          (existsT2 prem, AndLRule [prem] concl) + ((existsT2 prem, AndLRule [prem] concl) -> False).
Proof.
intro concl. destruct concl. destruct (dec_and_in l).
- left. repeat destruct s. apply in_splitT in i. destruct i. destruct s. subst.
  exists (x1 ++ x :: x0 :: x2, m). apply AndLRule_I.
- right. intro. destruct H. inversion a. subst. apply f. exists A. exists B.
  apply in_or_app. right. apply in_eq.
Qed.

(* Disjunction rules *)

Lemma dec_is_or : forall (A : MPropF), (existsT2 B C, A = Or B C) + ((existsT2 B C, A = Or B C) -> False).
Proof.
destruct A.
- right. intro. destruct H. destruct s. inversion e.
- right. intro. destruct H. destruct s. inversion e.
- right. intro. destruct H. destruct s. inversion e.
- left. exists A1. exists A2. reflexivity.
- right. intro. destruct H. destruct s. inversion e.
- right. intro. destruct H. destruct s. inversion e.
Qed.

Lemma dec_or_in : forall (l : list MPropF), (existsT2 A B, In (Or A B) l) + ((existsT2 A B, In (Or A B) l) -> False).
Proof.
induction l.
- right. intro. destruct H. destruct s. inversion i.
- destruct IHl.
  * repeat destruct s. left. exists x. exists x0. apply in_cons. assumption.
  * destruct (dec_is_or a).
    + repeat destruct s. subst. left. exists x. exists x0. apply in_eq.
    + right. intro. destruct H. destruct s. inversion i.
      { subst. apply f0. exists x. exists x0. reflexivity. }
      { apply f. exists x. exists x0. assumption. }
Qed.

Lemma dec_OrR1_rule : forall (concl : Seq),
          (existsT2 prem, OrR1Rule [prem] concl) + ((existsT2 prem, OrR1Rule [prem] concl) -> False).
Proof.
intros concl. destruct concl. destruct (dec_is_or m).
- left. subst. destruct s. destruct s. subst. 
  exists (l, x). apply OrR1Rule_I.
- right. intro. destruct H. inversion o. subst. apply f. exists A. exists B. auto.
Qed.

Lemma dec_OrR2_rule : forall (concl : Seq),
          (existsT2 prem, OrR2Rule [prem] concl) + ((existsT2 prem, OrR2Rule [prem] concl) -> False).
Proof.
intros concl. destruct concl. destruct (dec_is_or m).
- left. subst. destruct s. destruct s. subst. 
  exists (l, x0). apply OrR2Rule_I.
- right. intro. destruct H. inversion o. subst. apply f. exists A. exists B. auto.
Qed.

Lemma dec_OrL_rule : forall (concl : Seq),
          (existsT2 prem1 prem2, OrLRule [prem1 ; prem2] concl) + ((existsT2 prem1 prem2, OrLRule [prem1 ; prem2] concl) -> False).
Proof.
intro concl. destruct concl. destruct (dec_or_in l).
- left. repeat destruct s. apply in_splitT in i. destruct i. destruct s. subst.
  exists (x1 ++ x :: x2, m). exists (x1 ++ x0 :: x2, m). apply OrLRule_I.
- right. intro. destruct H. destruct s. inversion o. subst. apply f. exists A. exists B.
  apply in_or_app. right. apply in_eq.
Qed.

(* Implication rules *)

Lemma dec_is_imp : forall (A : MPropF), (existsT2 B C, A = Imp B C) + ((existsT2 B C, A = Imp B C) -> False).
Proof.
destruct A.
- right. intro. destruct H. destruct s. inversion e.
- right. intro. destruct H. destruct s. inversion e.
- right. intro. destruct H. destruct s. inversion e.
- right. intro. destruct H. destruct s. inversion e.
- left. exists A1. exists A2. reflexivity.
- right. intro. destruct H. destruct s. inversion e.
Qed.

Lemma dec_imp_in : forall (l : list MPropF), (existsT2 A B, In (Imp A B) l) + ((existsT2 A B, In (Imp A B) l) -> False).
Proof.
induction l.
- right. intro. destruct H. destruct s. inversion i.
- destruct IHl.
  * repeat destruct s. left. exists x. exists x0. apply in_cons. assumption.
  * destruct (dec_is_imp a).
    + repeat destruct s. subst. left. exists x. exists x0. apply in_eq.
    + right. intro. destruct H. destruct s. inversion i.
      { subst. apply f0. exists x. exists x0. reflexivity. }
      { apply f. exists x. exists x0. assumption. }
Qed.

Lemma dec_ImpR_rule : forall (concl : Seq),
          (existsT2 prem, ImpRRule [prem] concl) + ((existsT2 prem, ImpRRule [prem] concl) -> False).
Proof.
intros concl. destruct concl. destruct (dec_is_imp m).
- left. repeat destruct s. subst. exists ([] ++ x :: l, x0). apply ImpRRule_I.
- right. intro. destruct H. inversion i. subst. apply f. exists A. exists B. auto.
Qed.

Lemma dec_is_atomimp : forall (A : MPropF), (existsT2 P C, A = Imp # P C) + ((existsT2 P C, A = Imp # P C) -> False).
Proof.
intro A. destruct (dec_is_imp A).
- destruct s. destruct s. subst. destruct (dec_is_atomicT x).
  + destruct i. destruct s. subst. left. exists x1. exists x0. auto. right. subst. intro. destruct H. destruct s. inversion e.
  + right. intro. destruct H. destruct s. inversion e. apply f. subst. left. exists x1. auto.
- right. intro. firstorder.
Qed.

Lemma dec_atomimp_in : forall (l : list MPropF) P, (existsT2 B, In (Imp # P B) l) + ((existsT2 B, In (Imp # P B) l) -> False).
Proof.
induction l.
- right. intro. destruct H. inversion i.
- intro. destruct (IHl P).
  * repeat destruct s. left. exists x. apply in_cons. assumption.
  * destruct (dec_is_atomimp a).
    + repeat destruct s. subst. destruct (eq_dec_form (# P) (# x)). left. exists x0. rewrite e. apply in_eq.
       right. intro. destruct H. inversion i.  inversion H ; auto. subst. apply f. exists x1. auto.
    + right. intro. destruct H. inversion i.
      { subst. apply f0. exists P. exists x. reflexivity. }
      { apply f. exists x. assumption. }
Qed.

Lemma dec_atom_atomimp1_in : forall (l : list MPropF), (existsT2 P B l0 l1, (In (# P) l0) * (In (Imp # P B) l1) * (l = l0 ++ l1)) +
                  ((existsT2 P B l0 l1, (In (# P) l0) * (In (Imp # P B) l1) * (l = l0 ++ l1)) -> False).
Proof.
induction l.
- right. intro. destruct H. destruct s. destruct s. destruct s. destruct p. destruct p. assert (x1 = []). symmetry in e. apply app_eq_nil in e.
  destruct e. auto. subst. inversion i.
- destruct IHl.
  * repeat destruct s. repeat destruct p. subst. left. exists x. exists x0. exists (a :: x1). exists x2. repeat split ; auto. apply in_cons. assumption.
  * destruct (dec_is_atomicT a).
    + destruct i.
      { destruct s. subst. destruct (dec_atomimp_in l x).
         - destruct s. left. exists x. exists x0.  exists [# x]. exists l. repeat split ; auto. apply in_eq. 
         - right. intro. destruct H. repeat destruct s. repeat destruct p. subst. destruct x2. simpl in e. subst. inversion i. inversion e.
           subst. inversion i. rewrite <- H in i0. apply f0. exists x1. apply in_or_app. auto. apply f. exists x0. exists x1. exists x2. exists x3.
           repeat split ; auto. }
      { subst. right. intro. destruct H. apply f. repeat destruct s. repeat destruct p. destruct x1. simpl in e. inversion i.
        inversion e. subst. exists x. exists x0. exists x1. exists x2. repeat split ; auto. inversion i ; auto. inversion H. }
    + right. intro. destruct H. repeat destruct s. repeat destruct p. apply f. exists x. exists x0. destruct x1. inversion i. inversion e. subst.
       exists x1. exists x2. repeat split ; auto. inversion i ; auto. subst. exfalso. apply f0. left. exists x. auto.
Qed.

Lemma dec_AtomImpL1_rule : forall (concl : Seq),
          (existsT2 prem, AtomImpL1Rule [prem] concl) + ((existsT2 prem, AtomImpL1Rule [prem] concl) -> False).
Proof.
intro concl. destruct concl. destruct (dec_atom_atomimp1_in l).
- repeat destruct s. repeat destruct p. subst. apply in_splitT in i. destruct i. destruct s. subst.
  apply in_splitT in i0. destruct i0. destruct s. subst. repeat rewrite <- app_assoc. simpl. left.
  exists (x3 ++ # x :: (x4 ++ x1) ++ x0 :: x5, m).
  assert ((x3 ++ # x :: x4 ++ x1 ++ (Imp (# x) x0) :: x5, m) =  (x3 ++ # x :: (x4 ++ x1) ++ Imp # x x0 :: x5, m)).
  repeat rewrite <- app_assoc. auto. rewrite H. apply AtomImpL1Rule_I.
- right. intro. destruct H. inversion a. subst. apply f. exists P. exists A. exists (Γ0 ++ # P :: Γ1).
  exists (Imp # P A :: Γ2). repeat split. apply in_or_app. right. apply in_eq. apply in_eq. repeat rewrite <- app_assoc. auto.
Qed.

Lemma dec_atom_atomimp2_in : forall (l : list MPropF), (existsT2 P B l0 l1, (In (# P) l1) * (In (Imp # P B) l0) * (l = l0 ++ l1)) +
                  ((existsT2 P B l0 l1, (In (# P) l1) * (In (Imp # P B) l0) * (l = l0 ++ l1)) -> False).
Proof.
induction l.
- right. intro. destruct H. destruct s. destruct s. destruct s. destruct p. destruct p. assert (x1 = []). symmetry in e. apply app_eq_nil in e.
  destruct e. auto. subst. inversion i0.
- destruct IHl.
  * repeat destruct s. repeat destruct p. subst. left. exists x. exists x0. exists (a :: x1). exists x2. repeat split ; auto. apply in_cons. assumption. 
  * destruct (dec_is_atomimp a).
    + destruct s. destruct s. subst. destruct (In_dec l (# x)).
       {  left. exists x. exists x0.  exists [# x → x0]. exists l. repeat split ; auto. apply in_eq. }
       { right. intro. destruct H. repeat destruct s. repeat destruct p. subst. destruct x3. simpl in e. subst. inversion i0. inversion e.
         subst. inversion i0. inversion H. subst. apply f0. apply in_or_app ; auto. apply f. exists x1. exists x2. exists x3. exists x4.
         repeat split ; auto. }
    + right. intro. destruct H. repeat destruct s. repeat destruct p. apply f. exists x. exists x0. destruct x1. inversion i0. inversion e. subst.
       exists x1. exists x2. repeat split ; auto. inversion i0 ; auto. subst. exfalso. apply f0. exists x. exists x0. auto.
Qed.

Lemma dec_AtomImpL2_rule : forall (concl : Seq),
          (existsT2 prem, AtomImpL2Rule [prem] concl) + ((existsT2 prem, AtomImpL2Rule [prem] concl) -> False).
Proof.
intro concl. destruct concl. destruct (dec_atom_atomimp2_in l).
- repeat destruct s. repeat destruct p. subst. apply in_splitT in i. destruct i. destruct s. subst.
  apply in_splitT in i0. destruct i0. destruct s. subst. repeat rewrite <- app_assoc. simpl. left.
  exists (x2 ++ x0 :: (x5 ++ x3) ++ # x :: x4, m).
  assert (x2 ++ # x → x0 :: x5 ++ x3 ++ # x :: x4 =  x2 ++ # x → x0 :: (x5 ++ x3) ++ # x :: x4).
  repeat rewrite <- app_assoc. auto. rewrite H. apply AtomImpL2Rule_I.
- right. intro. destruct H. inversion a. subst. apply f. exists P. exists A. exists (Γ0 ++ # P → A :: Γ1).
  exists (# P :: Γ2). repeat split. apply in_eq. apply in_or_app. right. apply in_eq. repeat rewrite <- app_assoc. auto.
Qed.

Lemma dec_is_andimp : forall (A : MPropF), (existsT2 B C D, A = Imp (And B C) D) + ((existsT2 B C D, A = Imp (And B C) D) -> False).
Proof.
intro A. destruct (dec_is_imp A).
- destruct s. destruct s. subst. destruct (dec_is_and x).
  + repeat destruct s. subst. left. exists x1. exists x2. exists x0. auto.
  + right. intro. destruct H. repeat destruct s. inversion e. apply f. subst. exists x1. exists x2. auto.
- right. intro. firstorder.
Qed.

Lemma dec_andimp_in : forall (l : list MPropF), (existsT2 A B C, In (Imp (And A B) C) l) + ((existsT2 A B C, In (Imp (And A B) C) l) -> False).
Proof.
induction l.
- right. intro. destruct H. repeat destruct s. inversion i.
- destruct IHl.
  * repeat destruct s. left. exists x. exists x0. exists x1. apply in_cons. assumption.
  * destruct (dec_is_andimp a).
    + repeat destruct s. subst. left. exists x. exists x0. exists x1. apply in_eq.
    + right. intro. destruct H. repeat destruct s. inversion i.
      { subst. apply f0. exists x. exists x0. exists x1. reflexivity. }
      { apply f. exists x. exists x0. exists x1. assumption. }
Qed.

Lemma dec_AndImpL_rule : forall (concl : Seq),
          (existsT2 prem, AndImpLRule [prem] concl) + ((existsT2 prem, AndImpLRule [prem] concl) -> False).
Proof.
intro concl. destruct concl. destruct (dec_andimp_in l).
- left. repeat destruct s. apply in_splitT in i. destruct i. destruct s. subst.
  exists (x2 ++ Imp x (Imp x0 x1) :: x3, m). apply AndImpLRule_I.
- right. intro. destruct H. inversion a. subst. apply f. exists A. exists B. exists C.
  apply in_or_app. right. apply in_eq.
Qed.

Lemma dec_is_orimp : forall (A : MPropF), (existsT2 B C D, A = Imp (Or B C) D) + ((existsT2 B C D, A = Imp (Or B C) D) -> False).
Proof.
intro A. destruct (dec_is_imp A).
- destruct s. destruct s. subst. destruct (dec_is_or x).
  + repeat destruct s. subst. left. exists x1. exists x2. exists x0. auto.
  + right. intro. destruct H. repeat destruct s. inversion e. apply f. subst. exists x1. exists x2. auto.
- right. intro. firstorder.
Qed.

Lemma dec_orimp_in : forall (l : list MPropF), (existsT2 A B C, In (Imp (Or A B) C) l) + ((existsT2 A B C, In (Imp (Or A B) C) l) -> False).
Proof.
induction l.
- right. intro. destruct H. repeat destruct s. inversion i.
- destruct IHl.
  * repeat destruct s. left. exists x. exists x0. exists x1. apply in_cons. assumption.
  * destruct (dec_is_orimp a).
    + repeat destruct s. subst. left. exists x. exists x0. exists x1. apply in_eq.
    + right. intro. destruct H. repeat destruct s. inversion i.
      { subst. apply f0. exists x. exists x0. exists x1. reflexivity. }
      { apply f. exists x. exists x0. exists x1. assumption. }
Qed.

Lemma dec_OrImpL_rule : forall (concl : Seq),
          (existsT2 prem, OrImpLRule [prem] concl) + ((existsT2 prem, OrImpLRule [prem] concl) -> False).
Proof.
intro concl. destruct concl. destruct (dec_orimp_in l).
- left. repeat destruct s. apply in_splitT in i. destruct i. destruct s. subst.
  exists (x2 ++ (Imp x x1) :: [] ++ Imp x0 x1 :: x3, m). apply OrImpLRule_I.
- right. intro. destruct H. inversion o. subst. apply f. exists A. exists B. exists C.
  apply in_or_app. right. apply in_eq.
Qed.

Lemma dec_is_impimp : forall (A : MPropF), (existsT2 B C D, A = Imp (Imp B C) D) + ((existsT2 B C D, A = Imp (Imp B C) D) -> False).
Proof.
intro A. destruct (dec_is_imp A).
- destruct s. destruct s. subst. destruct (dec_is_imp x).
  + repeat destruct s. subst. left. exists x1. exists x2. exists x0. auto.
  + right. intro. destruct H. repeat destruct s. inversion e. apply f. subst. exists x1. exists x2. auto.
- right. intro. firstorder.
Qed.

Lemma dec_impimp_in : forall (l : list MPropF), (existsT2 A B C, In (Imp (Imp A B) C) l) + ((existsT2 A B C, In (Imp (Imp A B) C) l) -> False).
Proof.
induction l.
- right. intro. destruct H. repeat destruct s. inversion i.
- destruct IHl.
  * repeat destruct s. left. exists x. exists x0. exists x1. apply in_cons. assumption.
  * destruct (dec_is_impimp a).
    + repeat destruct s. subst. left. exists x. exists x0. exists x1. apply in_eq.
    + right. intro. destruct H. repeat destruct s. inversion i.
      { subst. apply f0. exists x. exists x0. exists x1. reflexivity. }
      { apply f. exists x. exists x0. exists x1. assumption. }
Qed.

Lemma dec_ImpImpL_rule : forall (concl : Seq),
          (existsT2 prem1 prem2, ImpImpLRule [prem1 ; prem2] concl) + ((existsT2 prem1 prem2, ImpImpLRule [prem1 ; prem2] concl) -> False).
Proof.
intro concl. destruct concl. destruct (dec_impimp_in l).
- left. repeat destruct s. apply in_splitT in i. destruct i. destruct s. subst.
  exists (x2 ++ Imp x0 x1 :: x3, Imp x x0). exists (x2 ++ x1 :: x3, m). apply ImpImpLRule_I.
- right. intro. destruct H. destruct s. inversion i. subst. apply f. exists A. exists B. exists C.
  apply in_or_app. right. apply in_eq.
Qed.

Lemma dec_is_boximp : forall (A : MPropF), (existsT2 B C, A = Imp (Box B) C) + ((existsT2 B C, A = Imp (Box B)C) -> False).
Proof.
intro A. destruct (dec_is_imp A).
- destruct s. destruct s. subst. destruct (dec_is_box x).
  + repeat destruct s. subst. left. exists x1. exists x0. auto.
  + right. intro. destruct H. repeat destruct s. inversion e. apply f. subst. exists x1. auto.
- right. intro. firstorder.
Qed.

Lemma dec_boximp_in : forall (l : list MPropF), (existsT2 A B, In (Imp (Box A) B) l) + ((existsT2 A B, In (Imp (Box A) B) l) -> False).
Proof.
induction l.
- right. intro. destruct H. repeat destruct s. inversion i.
- destruct IHl.
  * repeat destruct s. left. exists x. exists x0. apply in_cons. assumption.
  * destruct (dec_is_boximp a).
    + repeat destruct s. subst. left. exists x. exists x0. apply in_eq.
    + right. intro. destruct H. repeat destruct s. inversion i.
      { subst. apply f0. exists x. exists x0. reflexivity. }
      { apply f. exists x. exists x0. assumption. }
Qed.

Lemma dec_BoxImpL_rule : forall (concl : Seq),
          (existsT2 prem1 prem2, BoxImpLRule [prem1 ; prem2] concl) + ((existsT2 prem1 prem2, BoxImpLRule [prem1 ; prem2] concl) -> False).
Proof.
intro concl. destruct concl. destruct (dec_boximp_in l).
- left. repeat destruct s. apply in_splitT in i. destruct i. destruct s. subst.
  exists (pair (unBoxed_list x1 ++ x0 :: unBoxed_list x2 ++ [Box x]) x). exists ((x1 ++ x0 :: x2), m). apply BoxImpLRule_I.
- right. intro. destruct H. destruct s. inversion b. subst. apply f. exists A. exists B.
  apply in_or_app. right. apply in_eq.
Qed.

Lemma dec_box_in_list : forall l, (existsT2 (A : MPropF), In (Box A) l) +
                             ((existsT2 (A : MPropF), In (Box A) l) -> False).
Proof.
induction l.
- simpl. right. intro. destruct H. assumption.
- destruct (dec_is_box a).
  * destruct s. subst. left. exists x. apply in_eq.
  * destruct IHl.
    + left. destruct s. exists x. apply in_cons. assumption.
    + right. intro. destruct H. inversion i. subst. apply f. exists x. reflexivity. apply f0.
      exists x. assumption.
Qed.

Lemma dec_SLR_rule : forall (concl : Seq),
          (existsT2 prem, SLRRule [prem] concl) + ((existsT2 prem, SLRRule [prem] concl) -> False).
Proof.
intro concl. destruct concl. destruct (dec_is_box m).
- left. destruct s. subst. exists (unBoxed_list l ++ [Box x], x).
  apply SLRRule_I.
- right. intro. destruct H. inversion s. subst. apply f. exists A. auto.
Qed.

Lemma dec_G4iSL_rules : forall (concl : Seq),
          ((existsT2 prems, G4iSL_rules prems concl) -> False) + (existsT2 prems, G4iSL_rules prems concl).
Proof.
intro concl. destruct (dec_G4iSL_init_rules concl).
- right. repeat destruct s.
  * exists nil. apply IdP. assumption.
  * exists nil. apply BotL. assumption.
- destruct (dec_ImpR_rule concl).
  * right. destruct s. exists [x]. apply ImpR. assumption.
  * destruct (dec_AtomImpL1_rule concl).
    + right. repeat destruct s. exists [x]. apply AtomImpL1. assumption.
    + destruct (dec_SLR_rule concl).
      { right. destruct s. exists [x]. apply SLR. assumption. }
      { destruct (dec_AndImpL_rule concl).
        - right. repeat destruct s. exists [x]. apply AndImpL. assumption.
        - destruct (dec_OrImpL_rule concl).
          + right. repeat destruct s. exists [x]. apply OrImpL. assumption.
          + destruct (dec_ImpImpL_rule concl).
            * right. repeat destruct s. exists [x;x0]. apply ImpImpL. assumption.
            * destruct (dec_BoxImpL_rule concl).
              { right. repeat destruct s. exists [x;x0]. apply BoxImpL. assumption. }
              { destruct (dec_AndR_rule concl).
                - right. repeat destruct s. exists [x; x0]. apply AndR. assumption.
                - destruct (dec_AndL_rule concl).
                  + right. repeat destruct s. exists [x]. apply AndL. assumption.
                  + destruct (dec_OrR1_rule concl).
                    * right. repeat destruct s. exists [x]. apply OrR1. assumption.
                    * destruct (dec_OrR2_rule concl).
                      { right. repeat destruct s. exists [x]. apply OrR2. assumption. }
                      { destruct (dec_OrL_rule concl).
                        - right. repeat destruct s. exists [x;x0]. apply OrL. assumption.
                        -  destruct (dec_AtomImpL2_rule concl).
                            + right. repeat destruct s. exists [x]. apply AtomImpL2. assumption.
                            + left. intro. destruct H. inversion g.
                              * inversion H. subst. apply f. auto.
                              * inversion H. subst. apply f. auto.
                              * inversion H. subst. apply f7. exists (Γ,A). exists (Γ, B). assumption.
                              * inversion H. subst. apply f8. exists (Γ0 ++ A :: B :: Γ1, C). assumption.
                              * inversion H. subst. apply f9. exists (Γ, A). assumption.
                              * inversion H. subst. apply f10. exists (Γ, B). assumption.
                              * inversion H. subst. apply f11. exists (Γ0 ++ A :: Γ1, C). exists (Γ0 ++ B :: Γ1, C). assumption.
                              * inversion H. subst. apply f0. exists (Γ0 ++ A :: Γ1, B). assumption.
                              * inversion H. subst. apply f1. exists (Γ0 ++ # P :: Γ1 ++ A :: Γ2, C). assumption.
                              * inversion H. subst. apply f12. exists (Γ0 ++ A :: Γ1 ++ # P :: Γ2, C). assumption.
                              * inversion H. subst. apply f3. exists (Γ0 ++ Imp A (Imp B C) :: Γ1, D). assumption.
                              * inversion H. subst. apply f4. exists (Γ0 ++ Imp A C :: Γ1 ++ Imp B C :: Γ2, D). assumption.
                              * inversion H. subst. apply f5. exists (Γ0 ++ Imp B C :: Γ1, Imp A B). exists (Γ0 ++ C :: Γ1, D). assumption.
                              * inversion H. subst. apply f6. exists (unBoxed_list Γ0 ++  B :: unBoxed_list Γ1 ++ [Box A], A). exists (Γ0 ++ B :: Γ1, C). assumption.
                              * inversion H. subst. apply f2. exists (unBoxed_list Γ ++ [Box A], A). assumption. } } }
Qed.




