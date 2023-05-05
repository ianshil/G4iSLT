Require Import PeanoNat.
Require Import Lia.
Require Import Ensembles.
Require Import Init.Wf.

Require Import DiSL_calc.

Definition inverse {X : Type} (R : X -> X -> Prop) (x y : X) : Prop := R y x.

    Class model :=
      {
        nodes : Type ;

        (* Modal Relation *)
        mreachable : nodes -> nodes -> Prop ;
        mreach_tran u v w : mreachable u v -> mreachable v w -> mreachable u w ;
        inv_mreach_wf : well_founded (inverse mreachable) ;

        (* Intuitionistic Relation *)
        ireachable : nodes -> nodes -> Prop ;
        ireach_refl u : ireachable u u ;
        ireach_tran u v w : ireachable u v -> ireachable v w -> ireachable u w ;

        (* Interaction relations *)
        imreach_inter u v w : ireachable u v -> mreachable v w -> mreachable u w ;
        imreach_subrel u v : mreachable u v -> ireachable u v ;

        (* Valuation *)
        val : nodes -> nat -> Prop ;
        persist :  forall u v, ireachable u v -> forall p, val u p -> val v p
      }.

Fixpoint wforces (M: model) w (φ : MPropF) : Prop :=
match φ with
  | Var p => val w p
  | Bot => False
  | ψ ∧ χ => (wforces M w ψ) /\ (wforces M w χ)
  | ψ ∨ χ => (wforces M w ψ) \/ (wforces M w χ)
  | ψ → χ => forall v, ireachable w v -> wforces M v ψ -> wforces M v χ
  | Box ψ => forall v, mreachable w v -> wforces M v ψ
end.

Lemma Persistence : forall A M w, wforces M w A ->
            (forall v, ireachable w v -> wforces M v A).
Proof.
induction A ; intros ; try auto.
- simpl. pose ((@persist M) w v).
  pose (v0 H0 n). apply v1. auto.
- simpl. split. inversion H. apply IHA1 with (w:=w) ; auto.
  inversion H. apply IHA2 with (w:=w) ; auto.
- simpl. inversion H. left. apply IHA1 with (w:=w) ; auto.
  right. apply IHA2 with (w:=w) ; auto.
- simpl. intros. simpl in H. apply H with (v:=v0) ; auto.
  pose ((@ireach_tran) _ _ _ _ H0 H1). auto.
- simpl. intros. simpl in H. apply H. pose (@imreach_inter _ _ _ _ H0 H1) ; auto.
Qed.

Definition mforces M (φ : MPropF) : Prop := forall w , wforces M w φ.

Definition valid_form φ := forall M, mforces M φ.

Definition loc_conseq (Γ : Ensemble MPropF) (φ : MPropF) :=
  forall M w, (forall ψ, (In _ Γ ψ) -> wforces M w ψ) -> (wforces M w φ).

Definition glob_conseq (Γ : Ensemble MPropF) (φ : MPropF) :=
  forall M, (forall ψ, (In _ Γ ψ) -> mforces M ψ) -> (mforces M φ).