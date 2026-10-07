/-
# Original last-step paired budget of a reconstruction error

For arbitrary signed supported a,e, let M=T1,A=Ta,U=T(a^2),E=T(e^2).
The actual paired budget J(a,e) has the constructed polynomial ceiling
  J(a,e) <= P(a)*E,  P(a)=2*M*(A^2+M*U).
The difference is the sum of a full original K*V plus-pair square and
2*M*U times the actual one-step Schur gap M*E-(Te)^2.

This controls an incoming reciprocal reconstruction error; it does not
bound the leading ratio-noise or complete signed cost by a surviving norm.
Every transfer and two-slice weight remains the original fixed-spatial one.
No positivity of the signed inputs, inverse, or family estimate is assumed.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepRegression
import YMGap.Continuum.BF4ExactSlabFixedSpatialTransferOrder
import YMGap.Continuum.SU2QuaternionHaarCertificateIntegration
import YMGap.Continuum.QuaternionHaarAngularCarrier

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepErrorBudget

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal (partialHaarHeads)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBound
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferOrder (transferStep_certificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepScoreVariance
  (lastStepScoreBudget lastStepPairedResidual_square_pin)
open YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepRegression
  (lastStepRegressionGram lastStepRegressionGram_certificate)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.SU2QuaternionHaarTailDerivative (partialHaarHeads_add)
open YMGap.Continuum.SU2QuaternionHaarKernelBound (kernelMap)
open YMGap.Continuum.SU2QuaternionHaarCertificateIntegration
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_add cap_mul cap_mul_left)

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv
attribute [local irreducible] baseLinks spatialWeight kineticWeight

/-- Computed positive multiplier; no amplitude or source norm is inverted. -/
def lastStepErrorBudgetMultiplier (w : Q') (K width : Nat) (a : RatPoly) : RatPoly :=
  let M := transferStep w K width polyOne
  let A := transferStep w K width a
  let U := transferStep w K width (polyMul a a)
  polyMul (cap 2) (polyMul M (polyAdd (polyMul A A) (polyMul M U)))

theorem lastStepErrorBudgetMultiplier_supported (w : Q') (K width : Nat)
    {a : RatPoly} (ha : SupportedQuaternionBlocks (N width) a) :
    SupportedQuaternionBlocks (N width) (lastStepErrorBudgetMultiplier w K width a) := by
  have hM := transferStep_supported w K width (supported_one (N width))
  have hA := transferStep_supported w K width ha
  have hU := transferStep_supported w K width (supported_polyMul ha ha)
  have htwo : SupportedQuaternionBlocks (N width) (cap 2) := by
    intro term ht
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
    exact supported_one (N width) s hs
  exact supported_polyMul htwo
    (supported_polyMul hM (supported_add (supported_polyMul hA hA)
      (supported_polyMul hM hU)))

/-- The multiplier is positive even when a is signed. -/
def lastStepErrorBudgetMultiplier_certificate {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) {a : RatPoly}
    (ha : SupportedQuaternionBlocks (N width) a) :
    Certificate (N width) (lastStepErrorBudgetMultiplier w K width a) := by
  let PM := transferStep_certificate hw0 hw1 K width hK
    (supported_one (N width)) (Certificate.one (N width))
  let PU := transferStep_certificate hw0 hw1 K width hK
    (supported_polyMul ha ha) (Certificate.square a ha)
  exact (Certificate.constant (N width) 2 (by decide)).mul
    (PM.mul ((Certificate.square (transferStep w K width a)
      (transferStep_supported w K width ha)).add (PM.mul PU)))

private theorem support_mono {small large : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks small p) (h : small ≤ large) :
    SupportedQuaternionBlocks large p :=
  fun term ht => Nat.le_trans (hp term ht) (Nat.mul_le_mul_left 4 h)

private theorem transfer_congr (w : Q') (K width : Nat) {p q : RatPoly}
    (h : RatPolyCoeffEqv p q) :
    RatPolyCoeffEqv (transferStep w K width p) (transferStep w K width q) :=
  partialHaarHeads_congr (N width)
    ((h.mul_left (spatialWeight w K width)).mul_left (kineticWeight w K width))

private theorem plus_pair_pin (w : Q') (K width : Nat) (a e : RatPoly) :
    let A := transferStep w K width a
    let b := transferStep w K width e
    let X := polyAdd (polyMul (liftBoundary (N width) A) e)
      (polyMul (liftBoundary (N width) b) a)
    let C := polyMul (polyMul A b) (transferStep w K width (polyMul a e))
    RatPolyCoeffEqv
      (partialHaarHeads (N width) (polyMul (stepWeight w K width) (polyMul X X)))
      (polyAdd (polyMul (polyMul A A) (transferStep w K width (polyMul e e)))
        (polyAdd (polyAdd C C)
          (polyMul (polyMul b b) (transferStep w K width (polyMul a a))))) := by
  dsimp only
  let W := stepWeight w K width
  let A := transferStep w K width a
  let b := transferStep w K width e
  let X := polyAdd (polyMul (liftBoundary (N width) A) e)
    (polyMul (liftBoundary (N width) b) a)
  let cross := polyMul (polyMul W (polyMul a e))
    (liftBoundary (N width) (polyMul A b))
  have he : RatPolyCoeffEqv (polyMul W (polyMul X X))
      (polyAdd
        (polyMul (polyMul W (polyMul e e)) (liftBoundary (N width) (polyMul A A)))
        (polyAdd (polyAdd cross cross)
          (polyMul (polyMul W (polyMul a a)) (liftBoundary (N width) (polyMul b b))))) := by
    dsimp only [X, cross]
    rw [lift_product, lift_product, lift_product]
    exact coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.mul (.add (.mul (.var 1) (.var 2)) (.mul (.var 3) (.var 4)))
        (.add (.mul (.var 1) (.var 2)) (.mul (.var 3) (.var 4)))))
      (.add (.mul (.mul (.var 0) (.mul (.var 2) (.var 2))) (.mul (.var 1) (.var 1)))
        (.add (.add
          (.mul (.mul (.var 0) (.mul (.var 4) (.var 2))) (.mul (.var 1) (.var 3)))
          (.mul (.mul (.var 0) (.mul (.var 4) (.var 2))) (.mul (.var 1) (.var 3))))
          (.mul (.mul (.var 0) (.mul (.var 4) (.var 4))) (.mul (.var 3) (.var 3)))))
      (by decide) (fun
        | 0 => W
        | 1 => liftBoundary (N width) A
        | 2 => e
        | 3 => liftBoundary (N width) b
        | _ => a)
  have pin (p R : RatPoly) : RatPolyCoeffEqv
      (partialHaarHeads (N width) (polyMul (polyMul W p) (liftBoundary (N width) R)))
      (polyMul R (transferStep w K width p)) :=
    (partialHaarHeads_mul_lift (N width) (polyMul W p) R).trans
      (((transferStep_kernelMap w K width p).symm.mul_right R).trans
        (RatPolyCoeffEqv.mul_comm _ R))
  have h := partialHaarHeads_congr (N width) he
  rw [partialHaarHeads_add, partialHaarHeads_add, partialHaarHeads_add] at h
  exact h.trans ((pin (polyMul e e) (polyMul A A)).add
    (((pin (polyMul a e) (polyMul A b)).add
      (pin (polyMul a e) (polyMul A b))).add
      (pin (polyMul a a) (polyMul b b))))

/-- Exact polynomial ceiling of the old paired-residual error budget.
The full original K*V weight is positive; a and e need not be positive. -/
def lastStepScoreBudget_error_certificate {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) {a e : RatPoly}
    (ha : SupportedQuaternionBlocks (N width) a)
    (he : SupportedQuaternionBlocks (N width) e) :
    Certificate (N width) (polyAdd
      (polyMul (lastStepErrorBudgetMultiplier w K width a)
        (transferStep w K width (polyMul e e)))
      (polyNeg (lastStepScoreBudget w K width a e))) := by
  let M := transferStep w K width polyOne
  let A := transferStep w K width a
  let b := transferStep w K width e
  let U := transferStep w K width (polyMul a a)
  let E := transferStep w K width (polyMul e e)
  let C := polyMul (polyMul A b) (transferStep w K width (polyMul a e))
  let X := polyAdd (polyMul (liftBoundary (N width) A) e)
    (polyMul (liftBoundary (N width) b) a)
  have hX : SupportedQuaternionBlocks (N width+N width) X :=
    supported_add
      (supported_polyMul (lift_supported (transferStep_supported w K width ha) (N width))
        (support_mono he (by omega)))
      (supported_polyMul (lift_supported (transferStep_supported w K width he) (N width))
        (support_mono ha (by omega)))
  let PM := transferStep_certificate hw0 hw1 K width hK
    (supported_one (N width)) (Certificate.one (N width))
  let PU := transferStep_certificate hw0 hw1 K width hK
    (supported_polyMul ha ha) (Certificate.square a ha)
  let Pplus := partialHaarHeads_certificate (N width) (N width)
    ((stepWeightCertificate hw0 hw1 K width hK).mul (Certificate.square X hX))
  have PN : Certificate (N width) (polyAdd (polyMul M E) (polyNeg (polyMul b b))) := by
    have hM := transfer_congr w K width (RatPolyCoeffEqv.one_mul polyOne)
    have hb := transfer_congr w K width (RatPolyCoeffEqv.one_mul e)
    exact Certificate.ofCoeff
      ((hM.mul (RatPolyCoeffEqv.refl E)).add (RatPolyCoeffEqv.neg (hb.mul hb))).symm
      (lastStepRegressionGram_certificate hw0 hw1 K width hK (supported_one (N width)) he)
  have PP : Certificate (N width)
      (polyMul M (polyAdd (polyMul (polyMul A A) E)
        (polyAdd (polyAdd C C) (polyMul (polyMul b b) U)))) :=
    PM.mul (Certificate.ofCoeff (plus_pair_pin w K width a e).symm Pplus)
  have PS := ((Certificate.constant (N width) 2 (by decide)).mul (PM.mul PU)).mul PN
  have hJ := (lastStepPairedResidual_square_pin w K width a e).mul_left M
  refine Certificate.ofCoeff
    (((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.neg hJ)).trans ?_) (PP.add PS)
  exact coeffEvalExpr_eqv_of_normalize_eq
    (.add (.mul (.mul (.const 2) (.mul (.var 0)
      (.add (.mul (.var 1) (.var 1)) (.mul (.var 0) (.var 2))))) (.var 3))
      (.neg (.mul (.var 0) (.add (.mul (.mul (.var 1) (.var 1)) (.var 3))
        (.add (.neg (.add (.var 5) (.var 5))) (.mul (.mul (.var 4) (.var 4)) (.var 2)))))))
    (.add (.mul (.var 0) (.add (.mul (.mul (.var 1) (.var 1)) (.var 3))
      (.add (.add (.var 5) (.var 5)) (.mul (.mul (.var 4) (.var 4)) (.var 2)))))
      (.mul (.mul (.const 2) (.mul (.var 0) (.var 2)))
        (.add (.mul (.var 0) (.var 3)) (.neg (.mul (.var 4) (.var 4))))))
    (by decide) (fun
      | 0 => M
      | 1 => A
      | 2 => U
      | 3 => E
      | 4 => b
      | _ => C)

private theorem support_cap (blocks : Nat) (c : Q') :
    SupportedQuaternionBlocks blocks (cap c) := by
  intro term ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact supported_one blocks s hs

private theorem support_neg {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) :
    SupportedQuaternionBlocks blocks (polyNeg p) := by
  intro term ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private theorem transfer_neg (w : Q') (K width : Nat) (p : RatPoly) :
    RatPolyCoeffEqv (transferStep w K width (polyNeg p))
      (polyNeg (transferStep w K width p)) :=
  (transfer_congr w K width (QuaternionHaarAngularCarrier.neg_smul p)).trans
    ((transferStep_smul w K width (-1) p).trans
      (QuaternionHaarAngularCarrier.neg_smul _).symm)

private def moment_window_certificate {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : headCutoff w ≤ K) {a : RatPoly}
    (ha : SupportedQuaternionBlocks (N width) a) (PA : Certificate (N width) a)
    (l u kappa : Q') (hkappa : (0 : Q') ≤ kappa) (hkl : kappa*l ≈ u)
    (L : Certificate (N width) (polyAdd a (polyNeg (cap l))))
    (U : Certificate (N width) (polyAdd (cap u) (polyNeg a))) :
    let M := transferStep w K width polyOne
    let A := transferStep w K width a
    let B := transferStep w K width (polyMul a a)
    Certificate (N width) (polyAdd
      (polyMul (cap kappa) (polyMul A A)) (polyNeg (polyMul M B))) := by
  let M := transferStep w K width polyOne
  let A := transferStep w K width a
  let B := transferStep w K width (polyMul a a)
  let PM := transferStep_certificate hw0 hw1 K width hK
    (supported_one (N width)) (Certificate.one (N width))
  let P := transferStep_certificate hw0 hw1 K width hK ha PA
  have hL : RatPolyCoeffEqv (transferStep w K width (polyAdd a (polyNeg (cap l))))
      (polyAdd A (polyNeg (polyMul (cap l) M))) :=
    (transferStep_add w K width _ _).trans
      ((RatPolyCoeffEqv.refl _).add ((transfer_neg w K width (cap l)).trans
        (RatPolyCoeffEqv.neg ((transferStep_smul w K width l polyOne).trans
          (cap_mul_left l M).symm))))
  let PL := Certificate.ofCoeff hL.symm
    (transferStep_certificate hw0 hw1 K width hK
      (supported_add ha (support_neg (support_cap (N width) l))) L)
  have huinput : RatPolyCoeffEqv (polyMul (polyAdd (cap u) (polyNeg a)) a)
      (polyAdd (polySmul u a) (polyNeg (polyMul a a))) :=
    (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.add (.var 0) (.neg (.var 1))) (.var 1))
      (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 1) (.var 1))))
      (by decide) (fun | 0 => cap u | _ => a)).trans
      ((cap_mul_left u a).add (RatPolyCoeffEqv.refl _))
  have hU : RatPolyCoeffEqv
      (transferStep w K width (polyMul (polyAdd (cap u) (polyNeg a)) a))
      (polyAdd (polyMul (cap u) A) (polyNeg B)) :=
    (transfer_congr w K width huinput).trans
      ((transferStep_add w K width _ _).trans
        (((transferStep_smul w K width u a).trans (cap_mul_left u A).symm).add
          (transfer_neg w K width (polyMul a a))))
  let PU := Certificate.ofCoeff hU.symm
    (transferStep_certificate hw0 hw1 K width hK
      (supported_polyMul (supported_add (support_cap (N width) u) (support_neg ha)) ha)
      (U.mul PA))
  have hcap : RatPolyCoeffEqv (polyMul (cap kappa) (cap l)) (cap u) :=
    (cap_mul kappa l).trans (RatPolyCoeffEqv.smul_coefficient hkl polyOne)
  let PU' : Certificate (N width) (polyAdd
      (polyMul (polyMul (cap kappa) (cap l)) A) (polyNeg B)) :=
    Certificate.ofCoeff ((hcap.mul_right A).add (RatPolyCoeffEqv.refl _)) PU
  let S := (((Certificate.constant (N width) kappa hkappa).mul P).mul PL).add
    (PM.mul PU')
  exact Certificate.ofCoeff (coeffEvalExpr_eqv_of_normalize_eq
    (.add (.mul (.var 0) (.mul (.var 1) (.var 1)))
      (.neg (.mul (.var 2) (.var 3))))
    (.add (.mul (.mul (.var 0) (.var 1))
      (.add (.var 1) (.neg (.mul (.var 4) (.var 2)))))
      (.mul (.var 2) (.add (.mul (.mul (.var 0) (.var 4)) (.var 1)) (.neg (.var 3)))))
    (by decide) (fun | 0 => cap kappa | 1 => A | 2 => M | 3 => B | _ => cap l)) S

/-- ORIGINAL cone refinement from a constructed scalar window on positive a.
The scalar kappa only satisfies kappa*l=u; neither a nor any source norm is
inverted. Both original transfer certificates are retained in the proof. -/
def lastStepErrorBudgetMultiplier_window_certificate {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : headCutoff w ≤ K) {a : RatPoly}
    (ha : SupportedQuaternionBlocks (N width) a) (PA : Certificate (N width) a)
    (l u kappa : Q') (hkappa : (0 : Q') ≤ kappa) (hkl : kappa*l ≈ u)
    (L : Certificate (N width) (polyAdd a (polyNeg (cap l))))
    (U : Certificate (N width) (polyAdd (cap u) (polyNeg a))) :
    let M := transferStep w K width polyOne
    let A := transferStep w K width a
    Certificate (N width) (polyAdd
      (polySmul (2*(1+kappa)) (polyMul M (polyMul A A)))
      (polyNeg (lastStepErrorBudgetMultiplier w K width a))) := by
  let M := transferStep w K width polyOne
  let A := transferStep w K width a
  let B := transferStep w K width (polyMul a a)
  let PM := transferStep_certificate hw0 hw1 K width hK
    (supported_one (N width)) (Certificate.one (N width))
  let S := (PM.mul (moment_window_certificate hw0 hw1 K width hK ha PA
    l u kappa hkappa hkl L U)).smul 2 (by decide)
  have hc : RatPolyCoeffEqv (cap (2*(1+kappa)))
      (polyMul (cap 2) (polyAdd (cap 1) (cap kappa))) :=
    (cap_mul 2 (1+kappa)).symm.trans
      ((RatPolyCoeffEqv.refl _).mul (cap_add 1 kappa).symm)
  have hfirst : RatPolyCoeffEqv
      (polySmul (2*(1+kappa)) (polyMul M (polyMul A A)))
      (polyMul (polyMul (cap 2) (polyAdd (cap 1) (cap kappa)))
        (polyMul M (polyMul A A))) :=
    (cap_mul_left (2*(1+kappa)) _).symm.trans (hc.mul_right _)
  exact Certificate.ofCoeff
    ((hfirst.add (RatPolyCoeffEqv.refl _)).trans
      ((coeffEvalExpr_eqv_of_normalize_eq
        (.add (.mul (.mul (.var 0) (.add (.const 1) (.var 1)))
          (.mul (.var 2) (.mul (.var 3) (.var 3))))
          (.neg (.mul (.var 0) (.mul (.var 2)
            (.add (.mul (.var 3) (.var 3)) (.mul (.var 2) (.var 4)))))))
        (.mul (.var 0) (.mul (.var 2)
          (.add (.mul (.var 1) (.mul (.var 3) (.var 3)))
            (.neg (.mul (.var 2) (.var 4))))))
        (by decide) (fun | 0 => cap 2 | 1 => cap kappa | 2 => M | 3 => A | _ => B)).trans
          (cap_mul_left 2 _))) S

/-- Cancel A squared only through a supplied ACTUAL finite multiplier-square
certificate. The scalar M ceiling is generic to avoid importing a downstream
original-step consumer; G need not be an inverse or a particular degree. -/
def lastStepErrorBudgetMultiplier_reciprocal_cap_certificate {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : headCutoff w ≤ K) {a G : RatPoly}
    (ha : SupportedQuaternionBlocks (N width) a)
    (hG : SupportedQuaternionBlocks (N width) G)
    (kappa m : Q') (hkappa : (0 : Q') ≤ kappa)
    (P : Certificate (N width) (polyAdd
      (polySmul (2*(1+kappa))
        (polyMul (transferStep w K width polyOne)
          (polyMul (transferStep w K width a) (transferStep w K width a))))
      (polyNeg (lastStepErrorBudgetMultiplier w K width a))))
    (CM : Certificate (N width) (polyAdd (cap m)
      (polyNeg (transferStep w K width polyOne))))
    (AG : Certificate (N width) (polyAdd polyOne
      (polyNeg (polyMul (polyMul (transferStep w K width a) G)
        (polyMul (transferStep w K width a) G))))) :
    Certificate (N width) (polyAdd (cap ((2*(1+kappa))*m))
      (polyNeg (polyMul (polyMul G G) (lastStepErrorBudgetMultiplier w K width a)))) := by
  let M := transferStep w K width polyOne
  let A := transferStep w K width a
  let B := lastStepErrorBudgetMultiplier w K width a
  let c := 2*(1+kappa)
  have hc : (0 : Q') ≤ c := Q'.mul_nonneg _ _ (by decide)
    (Q'.zero_le_add _ _ Q'.zero_le_one hkappa)
  let PM := transferStep_certificate hw0 hw1 K width hK
    (supported_one (N width)) (Certificate.one (N width))
  let S := ((CM.add (PM.mul AG)).smul c hc).add
    ((Certificate.square G hG).mul P)
  have hone : RatPolyCoeffEqv
      (polyAdd (cap 1) (polyNeg (polyMul (polyMul A G) (polyMul A G))))
      (polyAdd polyOne (polyNeg (polyMul (polyMul A G) (polyMul A G)))) :=
    (RatPolyCoeffEqv.one_smul polyOne).add (RatPolyCoeffEqv.refl _)
  have hfirst : RatPolyCoeffEqv
      (polyMul (cap c) (polyAdd (polyAdd (cap m) (polyNeg M))
        (polyMul M (polyAdd (cap 1)
          (polyNeg (polyMul (polyMul A G) (polyMul A G)))))))
      (polySmul c (polyAdd (polyAdd (cap m) (polyNeg M))
        (polyMul M (polyAdd polyOne
          (polyNeg (polyMul (polyMul A G) (polyMul A G))))))) :=
    (cap_mul_left c _).trans
      (((RatPolyCoeffEqv.refl _).add ((RatPolyCoeffEqv.refl M).mul hone)).smul c)
  exact Certificate.ofCoeff
    (((cap_mul c m).symm.add (RatPolyCoeffEqv.refl _)).trans
      ((coeffEvalExpr_eqv_of_normalize_eq
        (.add (.mul (.var 0) (.var 1))
          (.neg (.mul (.mul (.var 4) (.var 4)) (.var 5))))
        (.add (.mul (.var 0) (.add (.add (.var 1) (.neg (.var 2)))
          (.mul (.var 2) (.add (.const 1)
            (.neg (.mul (.mul (.var 3) (.var 4)) (.mul (.var 3) (.var 4))))))))
          (.mul (.mul (.var 4) (.var 4))
            (.add (.mul (.var 0) (.mul (.var 2) (.mul (.var 3) (.var 3))))
              (.neg (.var 5)))))
        (by decide) (fun | 0 => cap c | 1 => cap m | 2 => M | 3 => A | 4 => G | _ => B)).trans
          (hfirst.add
            ((RatPolyCoeffEqv.refl _).mul
              ((cap_mul_left c _).add (RatPolyCoeffEqv.refl _)))))) S

end YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepErrorBudget

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepErrorBudget.lastStepErrorBudgetMultiplier
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepErrorBudget.lastStepErrorBudgetMultiplier_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepErrorBudget.lastStepErrorBudgetMultiplier_certificate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepErrorBudget.lastStepScoreBudget_error_certificate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepErrorBudget.lastStepErrorBudgetMultiplier_window_certificate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepErrorBudget.lastStepErrorBudgetMultiplier_reciprocal_cap_certificate
