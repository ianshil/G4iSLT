Require Import List.
Export ListNotations.
Require Import PeanoNat.
Require Import Ensembles.

Require Import general_export.

Require Import DG4iSL_export.

Require Import iSL_Kripke_sem.

Lemma In_unBoxed_list : forall A Γ, In A (unBoxed_list Γ) -> (In A Γ) + (In (Box A) Γ).
Proof.
Admitted.

Theorem G4iSL_sound : forall (Γ : list MPropF) A, G4iSL_prv (Γ,A) -> loc_conseq (fun B => In B Γ) A.
Proof.
intros. remember (Γ, A) as s. revert Heqs. revert A. revert Γ. revert X. revert s.
pose (@derrec_all_rect _ G4iSL_rules (fun _ => False)
(fun x => forall (Γ : list MPropF) (A : MPropF), x = (Γ, A) -> loc_conseq (fun B : MPropF => In B Γ) A)).
simpl in l. unfold G4iSL_prv. apply l.
intros ; subst. inversion H.
intros. clear l. inversion H1 ; subst. clear H2. pose (ForallTD_forall H0).
inversion H ; subst.

(* IdP *)
- inversion H1 ; subst. intros M w H2. apply H2. unfold Ensembles.In.
  apply in_or_app ; right ; apply in_eq.

(* BotL *)
- inversion H1 ; subst. intros M w H2.
  assert (Ensembles.In MPropF (fun B : MPropF => In B (Γ0 ++ ⊥ :: Γ1)) ⊥).
  unfold Ensembles.In. apply in_or_app ; right ; apply in_eq. apply H2 in H3. simpl in H3. inversion H3.

(* AndR *)
- inversion H1 ; subst. intros M w H2. simpl. split.
  assert (InT (Γ, A0) [(Γ, A0); (Γ, B)]). apply InT_eq.
  pose (l _ H3 Γ A0). apply l0 ; auto.
  assert (InT (Γ, B) [(Γ, A0); (Γ, B)]). apply InT_cons ; apply InT_eq.
  pose (l _ H3 Γ B). apply l0 ; auto.

(* AndL *)
- inversion H1 ; subst. intros M w H2.
  assert (InT (Γ0 ++ A0 :: B :: Γ1, A) [(Γ0 ++ A0 :: B :: Γ1, A)]). apply InT_eq.
  pose (l _ H3 (Γ0 ++ A0 :: B :: Γ1) A). apply l0 ; auto. unfold Ensembles.In in H2.
  intros. unfold Ensembles.In in H4. apply in_app_or in H4. destruct H4.
  apply H2. apply in_or_app ; auto.
  assert (In (A0 ∧ B) (Γ0 ++ A0 ∧ B :: Γ1)). apply in_or_app ; right ; apply in_eq.
  apply H2 in H5. simpl in H5 ; destruct H5 .
  inversion H4 ; subst ; auto. inversion H7 ; subst ; auto.
  apply H2. apply in_or_app ; right ; apply in_cons ; auto.

(* OrR1 *)
- inversion H1 ; subst. intros M w H2. simpl. left.
  assert (InT (Γ, A0) [(Γ, A0)]). apply InT_eq.
  pose (l _ H3 Γ A0). apply l0 ; auto.

(* OrR2 *)
- inversion H1 ; subst. intros M w H2. simpl. right.
  assert (InT (Γ, B) [(Γ, B)]). apply InT_eq.
  pose (l _ H3 Γ B). apply l0 ; auto.

(* OrL *)
- inversion H1 ; subst. intros M w H2. unfold Ensembles.In in H2.
  assert (In (A0 ∨ B) (Γ0 ++ A0 ∨ B :: Γ1)). apply in_or_app ; right ; apply in_eq.
  apply H2 in H3. simpl in H3 ; destruct H3 .
  assert (InT (Γ0 ++ A0 :: Γ1, A) [(Γ0 ++ A0 :: Γ1, A); (Γ0 ++ B :: Γ1, A)]). apply InT_eq.
  pose (l _ H4 (Γ0 ++ A0 :: Γ1) A). apply l0 ; auto.
  intros. unfold Ensembles.In in H5. apply in_app_or in H5. destruct H5.
  apply H2. apply in_or_app ; auto. inversion H5 ; subst ; auto.
  apply H2. apply in_or_app ; right ; apply in_cons ; auto.
  assert (InT (Γ0 ++ B :: Γ1, A) [(Γ0 ++ A0 :: Γ1, A); (Γ0 ++ B :: Γ1, A)]). apply InT_cons ; apply InT_eq.
  pose (l _ H4 (Γ0 ++ B :: Γ1) A). apply l0 ; auto.
  intros. unfold Ensembles.In in H5. apply in_app_or in H5. destruct H5.
  apply H2. apply in_or_app ; auto. inversion H5 ; subst ; auto.
  apply H2. apply in_or_app ; right ; apply in_cons ; auto.

(* ImpR *)
- inversion H1 ; subst. intros M w H2.
  assert (InT (Γ0 ++ A0 :: Γ1, B) [(Γ0 ++ A0 :: Γ1, B)]). apply InT_eq.
  pose (l _ H3 (Γ0 ++ A0 :: Γ1) B). simpl. intros. apply l0 ; auto.
  intros. unfold Ensembles.In in H2. unfold Ensembles.In in H6. apply in_app_or in H6. destruct H6.
  apply Persistence with (w:=w) ; auto. apply H2. apply in_or_app ; auto.
  inversion H6 ; subst ; auto.
  apply Persistence with (w:=w) ; auto. apply H2. apply in_or_app ; auto.

(* AtomImpL1 *)
- inversion H1 ; subst. intros M w H2. unfold Ensembles.In in H2.
  assert (In (# P) (Γ0 ++ # P :: Γ1 ++ # P → A0 :: Γ2)). apply in_or_app ; right ; apply in_eq.
  apply H2 in H3.
  assert (In (# P → A0) (Γ0 ++ # P :: Γ1 ++ # P → A0 :: Γ2)). apply in_or_app ; right ; apply in_cons ; apply in_or_app ; right ; apply in_eq.
  apply H2 in H4. simpl in H4.
  assert (InT (Γ0 ++ # P :: Γ1 ++ A0 :: Γ2, A) [(Γ0 ++ # P :: Γ1 ++ A0 :: Γ2, A)]). apply InT_eq.
  pose (l _ H5 (Γ0 ++ # P :: Γ1 ++ A0 :: Γ2) A). apply l0 ; auto.
  intros. unfold Ensembles.In in H6. apply in_app_or in H6. destruct H6.
  apply H2. apply in_or_app ; auto. inversion H6 ; subst ; auto.
  apply in_app_or in H7. destruct H7.
  apply H2. apply in_or_app ; right ; apply in_cons ; apply in_or_app ; auto.
  inversion H7 ; subst. apply H4. apply ireach_refl. auto.
  apply H2. apply in_or_app ; right ; apply in_cons ; apply in_or_app ; right ; apply in_cons ; auto.

(* AtomImpL2 *)
- inversion H1 ; subst. intros M w H2. unfold Ensembles.In in H2.
  assert (In (# P) (Γ0 ++ # P → A0 :: Γ1 ++ # P :: Γ2)). apply in_or_app ; right ; apply in_cons ; apply in_or_app ; right ; apply in_eq.
  apply H2 in H3.
  assert (In (# P → A0) (Γ0 ++ # P → A0 :: Γ1 ++ # P :: Γ2)). apply in_or_app ; right ; apply in_eq.
  apply H2 in H4. simpl in H4.
  assert (InT (Γ0 ++ A0 :: Γ1 ++ # P :: Γ2, A) [(Γ0 ++ A0 :: Γ1 ++ # P :: Γ2, A)]). apply InT_eq.
  pose (l _ H5 (Γ0 ++ A0 :: Γ1 ++ # P :: Γ2) A). apply l0 ; auto.
  intros. unfold Ensembles.In in H6. apply in_app_or in H6. destruct H6.
  apply H2. apply in_or_app ; auto. inversion H6 ; subst ; auto. apply H4. apply ireach_refl. auto.
  apply in_app_or in H7. destruct H7.
  apply H2. apply in_or_app ; right ; apply in_cons ; apply in_or_app ; auto.
  inversion H7 ; subst. auto.
  apply H2. apply in_or_app ; right ; apply in_cons ; apply in_or_app ; right ; apply in_cons ; auto.

(* AndImpL *)
- inversion H1 ; subst. intros M w H2. unfold Ensembles.In in H2.
  assert (In ((A0 ∧ B) → C) (Γ0 ++ (A0 ∧ B) → C :: Γ1)). apply in_or_app ; right ; apply in_eq.
  apply H2 in H3.
  assert (InT (Γ0 ++ A0 → B → C :: Γ1, A) [(Γ0 ++ A0 → B → C :: Γ1, A)]). apply InT_eq.
  pose (l _ H4 (Γ0 ++ A0 → B → C :: Γ1) A). apply l0 ; auto.
  intros. unfold Ensembles.In in H5. apply in_app_or in H5. destruct H5.
  apply H2. apply in_or_app ; auto. inversion H5 ; subst ; auto. simpl. intros.
  simpl in H3. apply H3 ; auto. apply ireach_tran with (v:=v) ; auto. split ; auto.
  apply Persistence with (w:=v) ; auto.
  apply H2. apply in_or_app ; right ; apply in_cons ; auto.

(* OrImpL *)
- inversion H1 ; subst. intros M w H2. unfold Ensembles.In in H2.
  assert (In ((A0 ∨ B) → C) (Γ0 ++ (A0 ∨ B) → C :: Γ1 ++ Γ2)). apply in_or_app ; right ; apply in_eq.
  apply H2 in H3.
  assert (InT (Γ0 ++ A0 → C :: Γ1 ++ B → C :: Γ2, A) [(Γ0 ++ A0 → C :: Γ1 ++ B → C :: Γ2, A)]). apply InT_eq.
  pose (l _ H4 (Γ0 ++ A0 → C :: Γ1 ++ B → C :: Γ2) A). apply l0 ; auto.
  intros. unfold Ensembles.In in H5. apply in_app_or in H5. destruct H5.
  apply H2. apply in_or_app ; auto. inversion H5 ; subst ; auto. simpl. intros.
  simpl in H3. apply H3 ; auto. apply in_app_or in H6. destruct H6.
  apply H2. apply in_or_app ; right ; apply in_cons ; apply in_or_app ; auto.
  inversion H6 ; subst ; auto. simpl. intros. simpl in H3. apply H3 ; auto.
  apply H2. apply in_or_app ; right ; apply in_cons ; apply in_or_app ; auto.

(* ImpImpL *)
- inversion H1 ; subst. intros M w H2. unfold Ensembles.In in H2.
  assert (In ((A0 → B) → C) (Γ0 ++ (A0 → B) → C :: Γ1)). apply in_or_app ; right ; apply in_eq.
  apply H2 in H3. simpl in H3.
  assert (InT (Γ0 ++ B → C :: Γ1, A0 → B) [(Γ0 ++ B → C :: Γ1, A0 → B); (Γ0 ++ C :: Γ1, A)]). apply InT_eq.
  pose (l _ H4 (Γ0 ++ B → C :: Γ1) (A0 → B)).
  assert (InT (Γ0 ++ C :: Γ1, A) [(Γ0 ++ B → C :: Γ1, A0 → B); (Γ0 ++ C :: Γ1, A)]). apply InT_cons ; apply InT_eq.
  pose (l _ H5 (Γ0 ++ C :: Γ1) A). apply l1 ; auto.
  intros. unfold Ensembles.In in H6. apply in_app_or in H6. destruct H6.
  apply H2. apply in_or_app ; auto. inversion H6 ; subst ; auto.
  apply H3. apply ireach_refl. intros. unfold loc_conseq in l0. simpl in l0. apply l0 with (w:=w) ; auto.
  intros. unfold Ensembles.In in H9. apply in_app_or in H9. destruct H9.
  apply H2. apply in_or_app ; auto. inversion H9 ; subst ; auto. simpl. intros. apply H3 ; auto.
  intros. apply Persistence with (w:=v0) ; auto.
  apply H2. apply in_or_app ; right ; apply in_cons ; auto.
  apply H2. apply in_or_app ; right ; apply in_cons ; auto.

(* BoxImpL *)
- inversion H1 ; subst. intros M w H2. unfold Ensembles.In in H2.
  assert (In (Box A0 → B) (Γ0 ++ Box A0 → B :: Γ1)). apply in_or_app ; right ; apply in_eq.
  apply H2 in H3. simpl in H3.
  assert (InT (unBoxed_list Γ0 ++ B :: unBoxed_list Γ1 ++ [Box A0], A0) [(unBoxed_list Γ0 ++ B :: unBoxed_list Γ1 ++ [Box A0], A0); (Γ0 ++ B :: Γ1, A)]). apply InT_eq.
  pose (l _ H4 (unBoxed_list Γ0 ++ B :: unBoxed_list Γ1 ++ [Box A0]) A0).
  assert (InT (Γ0 ++ B :: Γ1, A) [(unBoxed_list Γ0 ++ B :: unBoxed_list Γ1 ++ [Box A0], A0); (Γ0 ++ B :: Γ1, A)]). apply InT_cons ; apply InT_eq.
  pose (l _ H5 (Γ0 ++ B :: Γ1) A). apply l1 ; auto.
  intros. unfold Ensembles.In in H6. apply in_app_or in H6. destruct H6.
  apply H2. apply in_or_app ; auto. inversion H6 ; subst ; auto.
  apply H3. apply ireach_refl. intros.
  pose (@well_founded_ind _ (inverse mreachable) inv_mreach_wf
  (fun x => mreachable w x -> (wforces M x A0 /\ wforces M x ψ))).
  assert (wforces M v A0 /\ wforces M v ψ). apply a ; auto. clear a. intros.
  split.
  unfold loc_conseq in l0. simpl in l0. apply l0 ; auto. unfold Ensembles.In.
  intros. apply in_app_or in H10. destruct H10.
  destruct (In_unBoxed_list ψ0 Γ0) ; auto. apply Persistence with (w:=w) ; auto.
  apply H2 ; auto. apply in_or_app ; auto. apply imreach_subrel ; auto.
  pose (H2 (Box ψ0)). simpl in w0. apply w0 ; auto. apply in_or_app ; auto.
  inversion H10 ; subst ; auto. apply H3. apply imreach_subrel ; auto.
  intros ; auto. pose (H8 v0). destruct a ; auto. apply mreach_tran with (v:=x) ; auto.
  apply in_app_or in H11. destruct H11.
  destruct (In_unBoxed_list ψ0 Γ1) ; auto. apply Persistence with (w:=w) ; auto.
  apply H2 ; auto. apply in_or_app ; right ; apply in_cons ; auto. apply imreach_subrel ; auto.
  pose (H2 (Box ψ0)). simpl in w0. apply w0 ; auto. apply in_or_app ; right ; apply in_cons ; auto.
  inversion H11 ; subst. simpl. intros.
  pose (H8 v0). destruct a ; auto. apply mreach_tran with (v:=x) ; auto. inversion H12.
  apply H3. apply imreach_subrel ; auto.
  intros ; auto. pose (H8 v0). destruct a ; auto. apply mreach_tran with (v:=x) ; auto.
  destruct H8 ; auto.
  apply H2 ; auto. apply in_or_app ; right ; apply in_cons ; auto.

(* SLR *)
- inversion H1 ; subst. intros M w H2. unfold Ensembles.In in H2. simpl ; intros.
  assert (InT (unBoxed_list Γ ++ [Box A0], A0) [(unBoxed_list Γ ++ [Box A0], A0)]). apply InT_eq.
  pose (l _ H4 (unBoxed_list Γ ++ [Box A0]) A0).
  pose (@well_founded_ind _ (inverse mreachable) inv_mreach_wf
  (fun x => mreachable w x -> wforces M x A0)). apply w0 ; auto. clear w0.
  intros.
  apply l0 ; auto.
  intros. unfold Ensembles.In in H7. apply in_app_or in H7. destruct H7.
  destruct (In_unBoxed_list ψ Γ) ; auto. apply Persistence with (w:=w) ; auto.
  apply imreach_subrel ; auto. apply H2 in i. simpl in i. apply i ; auto.
  inversion H7 ; subst. 2: inversion H8. simpl. intros. apply H5. unfold inverse ; auto.
  apply mreach_tran with (v:=x) ; auto.
Qed.


