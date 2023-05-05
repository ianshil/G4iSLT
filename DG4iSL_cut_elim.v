Require Import List.
Export ListNotations.
Require Import Lia.

Require Import general_export.

Require Import DiSL_calc.
Require Import DG4iSL_adm_additive_cut.

Inductive CutRule : rlsT Seq :=
  | CutRule_I : forall A C Γ0 Γ1,
          CutRule [(pair (Γ0 ++ Γ1) A) ; (pair (Γ0 ++ A :: Γ1) C)]
                    (pair (Γ0 ++ Γ1) C)
.

Inductive G4iSL_cut_rules : rlsT  Seq :=
  | G4iSL_woc : forall ps c, G4iSL_rules ps c -> G4iSL_cut_rules ps c
  | G4iSL_cut : forall ps c, CutRule ps c -> G4iSL_cut_rules ps c
.

Definition G4iSL_cut_prv s := derrec G4iSL_cut_rules (fun _ => False) s.

Theorem G4iSL_cut_elimination : forall s, (G4iSL_cut_prv s) -> (G4iSL_prv s).
Proof.
intros s D.
apply derrec_all_rect with
(Q:= fun x => (derrec G4iSL_rules (fun _ => False) x))
in D ; auto.
- intros. inversion H.
- intros ps concl rule ders IH. inversion rule.
  * subst. apply derI with (ps:=ps) ; auto. apply dersrec_forall. intros.
    pose (ForallTD_forall IH H0) ;  auto.
  * subst. inversion H. subst. apply G4iSL_cut_adm with (A:=A). split.
    pose (ForallTD_forall IH). apply d. apply InT_eq.
    pose (ForallTD_forall IH). apply d. apply InT_cons ; apply InT_eq.
Defined.