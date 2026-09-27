/-
# Finite-volume coercivity on the original completed carrier

The dense coercivity coefficient passes to every completed vector orthogonal
to the original, unnormalized vacuum.  The coefficient remains dependent on
nome and extent.  This is a link-conditional Dirichlet estimate, not an
OS-time gap or a continuum scaling bound.
-/

import YMGap.Continuum.BF4ExactSlabFiniteVolumeCoercivity
import YMGap.Continuum.BF4ExactSlabConditionalCenteredCompletion
import YMGap.Continuum.GNSJointPairingContinuity
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz

namespace YMGap.Continuum.BF4ExactSlabCompletedFiniteVolumeCoercivity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSModulusCompletion
open YMGap.Continuum.GNSProjectionSweep
open YMGap.Continuum.GNSProjectionSweep.Family
open YMGap.Continuum.GNSDenseCompletionExtension
open YMGap.Continuum.GNSDenseCompletionLaws
open YMGap.Continuum.GNSJointPairingContinuity
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.BF4ExactSlabStarConditionalProjection
open YMGap.Continuum.BF4ExactSlabConditionalCovariance
open YMGap.Continuum.BF4ExactSlabConditionalCenteredCompletion
open YMGap.Continuum.BF4ExactSlabConditionalSweep
open YMGap.Continuum.BF4ExactSlabEightLayerCone
open YMGap.Continuum.BF4ExactSlabFiniteVolumeCoercivity
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

private def sumRep {A : Type} : List A → (A → CReal) → CReal
  | [], _ => CReal.czero
  | i :: rest, f => CReal.add (f i) (sumRep rest f)

private theorem sumRep_converges {A : Type} (xs : List A)
    (s : A → Nat → CReal) (lim : A → CReal)
    (h : ∀ i, i ∈ xs → CReal.ConvergesTo (s i) (lim i)) :
    CReal.ConvergesTo (fun n => sumRep xs (fun i => s i n)) (sumRep xs lim) := by
  induction xs with
  | nil => exact CReal.convergesTo_const CReal.czero
  | cons i rest ih =>
      exact CReal.convergesTo_add (h i List.mem_cons_self)
        (ih (fun j hj => h j (List.mem_cons_of_mem i hj)))

private theorem sumOn_rep {A : Type} (xs : List A) (f : A → CReal.RC)
    (g : A → CReal)
    (h : ∀ i, i ∈ xs → f i = Quotient.mk CReal.crealSetoid (g i)) :
    sumOn xs f = Quotient.mk CReal.crealSetoid (sumRep xs g) := by
  induction xs with
  | nil => rfl
  | cons i rest ih =>
      simp only [sumOn, sumRep, h i List.mem_cons_self,
        ih (fun j hj => h j (List.mem_cons_of_mem i hj)), CReal.RCadd_mk]

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (extent stage : Nat)

local notation "K" => headCutoff w + stage
local notation "hK" => Nat.le_add_right (headCutoff w) stage
local notation "F" => fullData hw0 hw1 K extent hK
local notation "P" => projections hw0 hw1 K extent hK
local notation "U" => unit hw0 hw1 extent stage

private def inputRep (X : CauchyGNS F) (n : Nat) : CReal :=
  (F).cinnerRep (constCauchy F (X.seq n)) (constCauchy F (X.seq n))

private def outputRep (i : PhysicalLink extent) (X : CauchyGNS F) (n : Nat) : CReal :=
  let T := conditionalDenseMap hw0 hw1 K extent hK i.val i.property
  (F).cinnerRep (T.toRep (X.seq n)) (T.toRep (X.seq n))

private def residualRep (i : PhysicalLink extent) (X : CauchyGNS F) (n : Nat) : CReal :=
  CReal.sub (inputRep hw0 hw1 extent stage X n)
    (outputRep hw0 hw1 extent stage i X n)

private def inputLimitRep (X : CauchyGNS F) : CReal := (F).cinnerRep X X

private def outputLimitRep (i : PhysicalLink extent) (X : CauchyGNS F) : CReal :=
  let T := conditionalDenseMap hw0 hw1 K extent hK i.val i.property
  (F).cinnerRep (T.mapRep X) (T.mapRep X)

private def residualLimitRep (i : PhysicalLink extent) (X : CauchyGNS F) : CReal :=
  CReal.sub (inputLimitRep hw0 hw1 extent stage X)
    (outputLimitRep hw0 hw1 extent stage i X)

private theorem inputRep_converges (X : CauchyGNS F) :
    CReal.ConvergesTo (inputRep hw0 hw1 extent stage X)
      (inputLimitRep hw0 hw1 extent stage X) := by
  have h := GNSJointPairingContinuity.pairing_converges
    (GNSDenseCompletionLaws.inputOuter X) (GNSDenseCompletionLaws.inputOuter X)
  have he : CReal.Equiv
      ((F).cinnerRep (GNSDenseCompletionLaws.inputOuter X).lim
        (GNSDenseCompletionLaws.inputOuter X).lim)
      ((F).cinnerRep X X) := by
    apply Quotient.exact (s := CReal.crealSetoid)
    change (F).cinnerCompl
      (Quotient.mk (cauchySetoid F) (GNSDenseCompletionLaws.inputOuter X).lim)
      (Quotient.mk (cauchySetoid F) (GNSDenseCompletionLaws.inputOuter X).lim) =
      (F).cinnerCompl (Quotient.mk (cauchySetoid F) X)
        (Quotient.mk (cauchySetoid F) X)
    rw [GNSDenseCompletionLaws.inputOuter_lim_class X]
  exact CReal.convergesTo_limit_congr h he

private theorem outputRep_converges (i : PhysicalLink extent) (X : CauchyGNS F) :
    CReal.ConvergesTo (outputRep hw0 hw1 extent stage i X)
      (outputLimitRep hw0 hw1 extent stage i X) := by
  let T := conditionalDenseMap hw0 hw1 K extent hK i.val i.property
  exact GNSJointPairingContinuity.pairing_converges (T.mapOuter X) (T.mapOuter X)

private theorem residualRep_converges (i : PhysicalLink extent) (X : CauchyGNS F) :
    CReal.ConvergesTo (residualRep hw0 hw1 extent stage i X)
      (residualLimitRep hw0 hw1 extent stage i X) :=
  CReal.convergesTo_add (inputRep_converges hw0 hw1 extent stage X)
    (CReal.convergesTo_neg (outputRep_converges hw0 hw1 extent stage i X))

private theorem residualRep_pin (i : PhysicalLink extent) (X : CauchyGNS F) (n : Nat) :
    normSq ((P).residual i (embedV F (X.seq n))) =
      Quotient.mk CReal.crealSetoid (residualRep hw0 hw1 extent stage i X n) := by
  let T := conditionalDenseMap hw0 hw1 K extent hK i.val i.property
  have ho : (P).op i (embedV F (X.seq n)) =
      Quotient.mk (cauchySetoid F) (T.toRep (X.seq n)) :=
    T.completionMap_embed (X.seq n)
  rw [(P).single_loss i (embedV F (X.seq n)), ho]
  rfl

private theorem residualLimitRep_pin (i : PhysicalLink extent) (X : CauchyGNS F) :
    normSq ((P).residual i (Quotient.mk (cauchySetoid F) X)) =
      Quotient.mk CReal.crealSetoid (residualLimitRep hw0 hw1 extent stage i X) := by
  let T := conditionalDenseMap hw0 hw1 K extent hK i.val i.property
  have ho : (P).op i (Quotient.mk (cauchySetoid F) X) =
      Quotient.mk (cauchySetoid F) (T.mapRep X) :=
    T.completionMap_mk X
  rw [(P).single_loss i (Quotient.mk (cauchySetoid F) X), ho]
  rfl

private theorem finalEnergyRep_pin (X : CauchyGNS F) :
    (P).finalEnergy (schedule extent) (Quotient.mk (cauchySetoid F) X) =
      Quotient.mk CReal.crealSetoid
        (sumRep (schedule extent) (fun i => residualLimitRep hw0 hw1 extent stage i X)) := by
  exact sumOn_rep (schedule extent) _ _ (fun i _ =>
    residualLimitRep_pin hw0 hw1 extent stage i X)

/-- Close any coefficient-parametric dense Dirichlet inequality along a
supplied Cauchy representative. No center or support property is inferred:
the caller supplies the SAME completed-carrier bound for every term. -/
theorem completed_of_termwise_bound (delta : Q') (X : CauchyGNS F)
    (hterms : ∀ n, CReal.RCle
      (CReal.RCscale delta (normSq (embedV F (X.seq n))))
      ((P).finalEnergy (schedule extent) (embedV F (X.seq n)))) :
    CReal.RCle
      (CReal.RCscale delta
        (normSq (Quotient.mk (cauchySetoid F) X)))
      ((P).finalEnergy (schedule extent) (Quotient.mk (cauchySetoid F) X)) := by
  let lhs : Nat → CReal := fun n =>
    CReal.mul (CReal.ofQ' delta) (inputRep hw0 hw1 extent stage X n)
  let rhs : Nat → CReal := fun n =>
    sumRep (schedule extent) (fun i => residualRep hw0 hw1 extent stage i X n)
  have hleft : CReal.ConvergesTo lhs
      (CReal.mul (CReal.ofQ' delta) (inputLimitRep hw0 hw1 extent stage X)) :=
    CReal.convergesTo_constMul delta
      (inputRep_converges hw0 hw1 extent stage X)
  have hright : CReal.ConvergesTo rhs
      (sumRep (schedule extent)
        (fun i => residualLimitRep hw0 hw1 extent stage i X)) :=
    sumRep_converges (schedule extent)
      (fun i n => residualRep hw0 hw1 extent stage i X n)
      (fun i => residualLimitRep hw0 hw1 extent stage i X)
      (fun i _ => residualRep_converges hw0 hw1 extent stage i X)
  have hterm (n : Nat) : CReal.leEv (lhs n) (rhs n) := by
    have h := hterms n
    have he : (P).finalEnergy (schedule extent) (embedV F (X.seq n)) =
        Quotient.mk CReal.crealSetoid (rhs n) := by
      exact sumOn_rep (schedule extent) _ _ (fun i _ =>
        residualRep_pin hw0 hw1 extent stage i X n)
    rw [he] at h
    change CReal.leEv (lhs n) (rhs n) at h
    exact h
  have hlim := CReal.leEv_of_convergesTo_le hleft hright hterm
  have hrc : CReal.RCle
      (Quotient.mk CReal.crealSetoid
        (CReal.mul (CReal.ofQ' delta) (inputLimitRep hw0 hw1 extent stage X)))
      (Quotient.mk CReal.crealSetoid
        (sumRep (schedule extent)
          (fun i => residualLimitRep hw0 hw1 extent stage i X))) := hlim
  rw [← finalEnergyRep_pin hw0 hw1 extent stage X] at hrc
  exact hrc

/-- Complete the already-proved dense inequality for a representative whose
terms are centered in the actual original full-action form. -/
private theorem completed_of_termwise_centered (X : CauchyGNS F)
    (hcenter : ∀ n, (F).B (X.seq n) U ≈ 0) :
    CReal.RCle
      (CReal.RCscale (coercivity hw0 hw1 extent)
        (normSq (Quotient.mk (cauchySetoid F) X)))
      ((P).finalEnergy (schedule extent) (Quotient.mk (cauchySetoid F) X)) :=
  completed_of_termwise_bound hw0 hw1 extent stage
    (coercivity hw0 hw1 extent) X
    (fun n => dense_centered_coercivity hw0 hw1 K extent hK (X.seq n) (hcenter n))

/-- The genuine original-action finite-volume Dirichlet lower bound on all
completed vectors orthogonal to the unnormalized original vacuum. -/
theorem completed_centered_coercivity (x : GNSCompletionSpace F)
    (hx : (F).cinnerCompl x (embedV F U) = CReal.RCzero) :
    CReal.RCle (CReal.RCscale (coercivity hw0 hw1 extent) (normSq x))
      ((P).finalEnergy (schedule extent) x) := by
  revert hx
  refine Quotient.inductionOn x ?_
  intro X hx
  let Y := centeredCauchy hw0 hw1 extent stage X
  have hY := completed_of_termwise_centered hw0 hw1 extent stage Y
    (centeredCauchy_term_centered hw0 hw1 extent stage X)
  have hsame := centeredCauchy_same_class hw0 hw1 extent stage X hx
  rw [hsame] at hY
  exact hY

end YMGap.Continuum.BF4ExactSlabCompletedFiniteVolumeCoercivity

#print axioms YMGap.Continuum.BF4ExactSlabCompletedFiniteVolumeCoercivity.completed_centered_coercivity
#print axioms YMGap.Continuum.BF4ExactSlabCompletedFiniteVolumeCoercivity.completed_of_termwise_bound
