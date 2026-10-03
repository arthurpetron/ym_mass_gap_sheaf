/-
# Original quadratic gain as a full-source finite heat defect

For the actual terminal g, A=Tg and b=T(g(f-c)), expose the uncentered
defect f(x)-a*f(y) under the COMPLETE original source V(x)*g(x) and upper
test V(y)*b(y). The difference from the accepted centered gain is exactly
(a-1)*c*ell(A*b). Neither this moving-mean residue nor any signed term is
silently discarded. This is the original-carrier consumer for finite heat
Stein or conditional covariance estimates, not a sign or uniform bound.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredCommutatorGain

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredGainSourcePair

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWeightedMass
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket (terminalMessage)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredCommutatorGain
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionHeadChainComposition (step_pairing)
open YMGap.Continuum.QuaternionHaarDensityVariance (shifted)
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
local notation:max "H" blocks:arg => quaternionHaar blocks
attribute [local irreducible] baseLinks spatialWeight kineticWeight terminalMessage

/-- Literal uncentered finite heat defect on the ORIGINAL doubled carrier. -/
def fullSourceDefectPair (w : Q') (K width n : Nat) (f : RatPoly) (c a : Q') : Q' :=
  let q := polyMul (spatialWeight w K width) (terminalMessage w K width n)
  let r := polyMul (spatialWeight w K width) (centeredMessage w K width n f c)
  H (N width+N width) (polyMul
    (polyMul (kineticWeight w K width)
      (polyMul q (polyAdd f (polySmul (-a) (liftBoundary (N width) f)))))
    (liftBoundary (N width) r))

/-- The SAME original weighted mean residue, before any normalization. -/
def centeredMeanPair (w : Q') (K width n : Nat) (f : RatPoly) (c : Q') : Q' :=
  weightedMass w K width (polyMul
    (transferStep w K width (terminalMessage w K width n))
    (centeredMessage w K width n f c))

private theorem weighted_product_add_smul (w : Q') (K width : Nat)
    (p q r : RatPoly) (d : Q') :
    weightedMass w K width (polyMul p (polyAdd q (polySmul d r))) ≈
      weightedMass w K width (polyMul p q) + d*weightedMass w K width (polyMul p r) :=
  Q'.eqv_trans _ _ _
    (weightedMass_congr w K width (RatPolyCoeffEqv.mul_add_right _ _ _))
    (Q'.eqv_trans _ _ _ (weightedMass_add w K width _ _)
      (Q'.add_eqv_congr' (Q'.eqv_refl _)
        (Q'.eqv_trans _ _ _
          (weightedMass_congr w K width (RatPolyCoeffEqv.polyMul_smul_right d p r))
          (weightedMass_smul w K width d _))))

private theorem weighted_centered_product (w : Q') (K width : Nat)
    (p A f : RatPoly) (c : Q') :
    weightedMass w K width (polyMul p (polyMul A (shifted f c))) ≈
      weightedMass w K width (polyMul p (polyMul A f)) +
        (-c)*weightedMass w K width (polyMul p A) := by
  have hs : RatPolyCoeffEqv (polyMul A (shifted f c))
      (polyAdd (polyMul A f) (polySmul (-c) A)) :=
    (RatPolyCoeffEqv.mul_add_right _ _ _).trans
      (((RatPolyCoeffEqv.polyMul_smul_right 1 A f).trans
        (RatPolyCoeffEqv.one_smul _)).add
        ((RatPolyCoeffEqv.polyMul_smul_right (-c) A polyOne).trans
          ((RatPolyCoeffEqv.mul_one A).smul (-c))))
  exact Q'.eqv_trans _ _ _ (weightedMass_congr w K width (hs.mul_left p))
    (weighted_product_add_smul w K width p _ A (-c))

/-- Exact folding into the original transfer; the entire source and both
endpoint spatial weights occur once. No source independence is assumed. -/
theorem fullSourceDefectPair_transfer (w : Q') (K width n : Nat)
    (f : RatPoly) (c a : Q') :
    fullSourceDefectPair w K width n f c a ≈
      weightedMass w K width (polyMul (centeredMessage w K width n f c)
        (transferStep w K width (polyMul (terminalMessage w K width n) f))) +
      (-a)*weightedMass w K width (polyMul (centeredMessage w K width n f c)
        (polyMul (transferStep w K width (terminalMessage w K width n)) f)) := by
  let V := spatialWeight w K width
  let g := terminalMessage w K width n
  let b := centeredMessage w K width n f c
  let k := kineticWeight w K width
  let L := polyMul (polyMul k (polyMul V (polyMul g f)))
    (liftBoundary (N width) (polyMul V b))
  let U := polyMul (polyMul k (polyMul V g))
    (liftBoundary (N width) (polyMul V (polyMul b f)))
  have he : RatPolyCoeffEqv
      (polyMul (polyMul k
        (polyMul (polyMul V g) (polyAdd f (polySmul (-a) (liftBoundary (N width) f)))))
        (liftBoundary (N width) (polyMul V b)))
      (polyAdd L (polySmul (-a) U)) := by
    have hs := (RatPolyCoeffEqv.polyMul_smul_right (-a) (polyMul V g)
      (liftBoundary (N width) f)).mul_left k
    have hs' := (hs.trans (RatPolyCoeffEqv.polyMul_smul_right (-a) k _)).mul_right
      (liftBoundary (N width) (polyMul V b))
    have hd := ((RatPolyCoeffEqv.mul_add_right (polyMul V g) f
      (polySmul (-a) (liftBoundary (N width) f))).mul_left k).mul_right
      (liftBoundary (N width) (polyMul V b))
    refine hd.trans (((RatPolyCoeffEqv.mul_add_right k _ _).mul_right _).trans ?_)
    rw [polyMul_add_left_exact]
    have hl : RatPolyCoeffEqv _ L :=
      ((RatPolyCoeffEqv.mul_assoc V g f).mul_left k).mul_right _
    have hu : RatPolyCoeffEqv
        (polyMul (polyMul k (polyMul (polyMul V g) (liftBoundary (N width) f)))
          (liftBoundary (N width) (polyMul V b))) U := by
      have hr : RatPolyCoeffEqv
          (polyMul (liftBoundary (N width) f) (liftBoundary (N width) (polyMul V b)))
          (liftBoundary (N width) (polyMul V (polyMul b f))) := by
        rw [← lift_product]
        exact lift_coeff (N width) (coeffEvalExpr_eqv_of_normalize_eq
          (.mul (.var 0) (.mul (.var 1) (.var 2)))
          (.mul (.var 1) (.mul (.var 2) (.var 0))) (by decide)
          (fun | 0 => f | 1 => V | _ => b))
      exact ((RatPolyCoeffEqv.mul_assoc k _ _).symm.mul_right _).trans
        ((RatPolyCoeffEqv.mul_assoc _ _ _).trans (hr.mul_left _))
    exact hl.add (hs'.trans ((RatPolyCoeffEqv.polyMul_smul_left (-a) _ _).trans (hu.smul (-a))))
  have hl := step_pairing (N width) (N width) k V (polyMul g f) (polyMul V b)
  have hu := step_pairing (N width) (N width) k V g (polyMul V (polyMul b f))
  have hl' : H (N width+N width) L ≈
      weightedMass w K width (polyMul b (transferStep w K width (polyMul g f))) :=
    Q'.eqv_trans _ _ _ hl (haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.mul (.var 1) (.mul (.var 2) (.var 0))) (by decide)
      (fun | 0 => transferStep w K width (polyMul g f) | 1 => V | _ => b)))
  have hu' : H (N width+N width) U ≈
      weightedMass w K width (polyMul b (polyMul (transferStep w K width g) f)) :=
    Q'.eqv_trans _ _ _ hu (haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.var 3))))
      (.mul (.var 1) (.mul (.var 2) (.mul (.var 0) (.var 3)))) (by decide)
      (fun | 0 => transferStep w K width g | 1 => V | 2 => b | _ => f)))
  exact Q'.eqv_trans _ _ _ (haar_of_coeff he)
    (Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _)
      (Q'.add_eqv_congr' hl' (Q'.eqv_trans _ _ _ (quaternionHaar_polySmul _ (-a) U)
        (Q'.mul_eqv_congr_left _ _ _ hu'))))

/-- Exact SAME-source gain consumer. The finite OWN center may be used,
but no stationarity or zero centered mean is asserted at finite depth. -/
theorem commutatorGain_source_pair (w : Q') (K width n : Nat)
    (f : RatPoly) (c a : Q') :
    commutatorGain w K width n f c a ≈
      fullSourceDefectPair w K width n f c a +
        (a-1)*c*centeredMeanPair w K width n f c := by
  let g := terminalMessage w K width n
  let A := transferStep w K width g
  let B := transferStep w K width (polyMul g f)
  let b := centeredMessage w K width n f c
  let X := weightedMass w K width (polyMul b B)
  let Y := weightedMass w K width (polyMul b (polyMul A f))
  let M := weightedMass w K width (polyMul b A)
  have hb : weightedMass w K width (polyMul b b) ≈ X+(-c)*M :=
    Q'.eqv_trans _ _ _
      (weightedMass_congr w K width ((centeredMessage_pin w K width n f c).mul_left b))
      (weighted_product_add_smul w K width b B A (-c))
  have hu := weighted_centered_product w K width b A f c
  have hg : commutatorGain w K width n f c a ≈ X+(-c)*M+(-a)*(Y+(-c)*M) :=
    Q'.eqv_trans _ _ _ (weighted_product_add_smul w K width b b (polyMul A (shifted f c)) (-a))
      (Q'.add_eqv_congr' hb (Q'.mul_eqv_congr_left _ _ _ hu))
  have hm : M ≈ centeredMeanPair w K width n f c :=
    weightedMass_congr w K width (RatPolyCoeffEqv.mul_comm b A)
  have hp := fullSourceDefectPair_transfer w K width n f c a
  exact Q'.eqv_trans _ _ _ hg (Q'.eqv_trans _ _ _
    (poly_identity_of_normal_eq
      (.add (.add (.var 0) (.mul (.neg (.var 3)) (.var 2)))
        (.mul (.neg (.var 4)) (.add (.var 1) (.mul (.neg (.var 3)) (.var 2)))))
      (.add (.add (.var 0) (.mul (.neg (.var 4)) (.var 1)))
        (.mul (.mul (.add (.var 4) (.neg (.const 1))) (.var 3)) (.var 2)))
      (by decide) (fun | 0 => X | 1 => Y | 2 => M | 3 => c | _ => a))
    (Q'.add_eqv_congr' hp.symm (Q'.mul_eqv_congr_left _ _ _ hm)))

end YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredGainSourcePair

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredGainSourcePair.fullSourceDefectPair
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredGainSourcePair.centeredMeanPair
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredGainSourcePair.fullSourceDefectPair_transfer
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredGainSourcePair.commutatorGain_source_pair
