/-
# Nonunit innovation tower on the original finite BF4 action

The inner weight is the existing terminal-weighted half-open window. Its
mass and source moment are T^t g_n and T^t(g_n psi), rather than a unit
conditional mass. One further original K*V step gives a certificate for
  noise_(t+1)(g_n,psi) - noise_1(T^t g_n,phi) - 2 Cov,
where Cov = A*T(phi*e)-T(a*phi)*T(e), e=b-a*phi, A=T(a).
All spatial factors and chronological times remain literal. No inverse of
a, normalized kernel, stationarity, or quotient identification is used.

The supplied phi is any supported polynomial, including the existing
finite blockConditionalRatio. This supplies finite algebra and positivity;
useful bounds on the signed covariance and history contribution, the actual
changing-action comparison, survival and the continuum Clay target remain open.
-/

import YMGap.Continuum.SU2QuaternionUnnormalizedVarianceTower
import YMGap.Continuum.BF4ExactSlabFixedSpatialBlockScoreReplica
import YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalRatio

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialBlockInnovationTower

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal (partialHaarHeads)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.SU2QuaternionHaarTailDerivative
open YMGap.Continuum.SU2QuaternionHeadWindowContraction
open YMGap.Continuum.SU2QuaternionHeadWindowBounds (halfOpenAction_certificate)
open YMGap.Continuum.SU2QuaternionHaarCertificateExtension (certificate_extend)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.SU2QuaternionConditionalVarianceTower (mean towerWeight tower_mean_pin)
open YMGap.Continuum.SU2QuaternionMultiHeadVarianceReplica (determinant)
open YMGap.Continuum.SU2QuaternionUnnormalizedVarianceTower
  (innovationCovariance innovation_certificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight kineticWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBound (stepWeight stepWeightCertificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing (iterateStep_add)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage terminalMessage_supported terminalMessage_certificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockMultiplicationDefect (originalBlockTransfer)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalNoise (blockNoise)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockScoreReplica (blockWindowWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalRatio
  (blockConditionalRatio blockConditionalRatio_supported)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)

local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks kineticWeight spatialWeight

private theorem support_mono {small large : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks small p) (h : small ≤ large) :
    SupportedQuaternionBlocks large p :=
  fun term hterm => Nat.le_trans (hp term hterm) (Nat.mul_le_mul_left 4 h)

private theorem inner_moment (w : Q') (K width n t : Nat) (p : RatPoly) :
    RatPolyCoeffEqv (mean (t*(N width)) (blockWindowWeight w K width n t) p)
      (originalBlockTransfer w K width t (polyMul (terminalMessage w K width n) p)) := by
  unfold mean blockWindowWeight
  exact (partialHaarHeads_congr (t*(N width))
    (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.var 1)) (.var 2))
      (.mul (.mul (.var 0) (.var 2)) (.var 1)) (by decide)
      (fun | 0 => terminalMessage w K width n
           | 1 => halfOpenAction (N width) (kineticWeight w K width)
               (spatialWeight w K width) t
           | _ => p))).trans
    (windowMessage_iterate (N width) (kineticWeight w K width)
      (spatialWeight w K width) t (terminalMessage w K width n) p)

private theorem inner_mass (w : Q') (K width n t : Nat) :
    RatPolyCoeffEqv (partialHaarHeads (t*(N width)) (blockWindowWeight w K width n t))
      (originalBlockTransfer w K width t (terminalMessage w K width n)) := by
  unfold blockWindowWeight
  exact (partialHaarHeads_congr (t*(N width))
    ((RatPolyCoeffEqv.mul_one (terminalMessage w K width n)).symm.mul_right
      (halfOpenAction (N width) (kineticWeight w K width) (spatialWeight w K width) t))).trans
    (windowMessage_one (N width) (kineticWeight w K width)
      (spatialWeight w K width) t (terminalMessage w K width n))

private theorem outer_moment (w : Q') (K width : Nat) (p : RatPoly) :
    RatPolyCoeffEqv (mean (N width) (stepWeight w K width) p)
      (originalBlockTransfer w K width 1 p) := by
  exact partialHaarHeads_congr (N width)
    (RatPolyCoeffEqv.mul_assoc (kineticWeight w K width) (spatialWeight w K width) p)

private theorem block_succ (w : Q') (K width t : Nat) (p : RatPoly) :
    originalBlockTransfer w K width (t+1) p =
      originalBlockTransfer w K width 1 (originalBlockTransfer w K width t p) := by
  unfold originalBlockTransfer
  exact iterateStep_add (N width) (kineticWeight w K width) (spatialWeight w K width) t 1 p

private theorem outer_congr (w : Q') (K width : Nat) {p q : RatPoly}
    (h : RatPolyCoeffEqv p q) :
    RatPolyCoeffEqv (mean (N width) (stepWeight w K width) p)
      (originalBlockTransfer w K width 1 q) :=
  (partialHaarHeads_congr (N width) (h.mul_left (stepWeight w K width))).trans
    (outer_moment w K width q)

private theorem total_moment (w : Q') (K width n t : Nat) (p : RatPoly) :
    RatPolyCoeffEqv
      (mean (t*(N width)+N width)
        (towerWeight (t*(N width)) (blockWindowWeight w K width n t) (stepWeight w K width)) p)
      (originalBlockTransfer w K width (t+1) (polyMul (terminalMessage w K width n) p)) := by
  rw [block_succ]
  exact (tower_mean_pin (t*(N width)) (N width)
    (blockWindowWeight w K width n t) (stepWeight w K width) p).trans
    (outer_congr w K width (inner_moment w K width n t p))

private theorem total_mass (w : Q') (K width n t : Nat) :
    RatPolyCoeffEqv
      (partialHaarHeads (t*(N width)+N width)
        (towerWeight (t*(N width)) (blockWindowWeight w K width n t) (stepWeight w K width)))
      (originalBlockTransfer w K width (t+1) (terminalMessage w K width n)) := by
  rw [block_succ]
  unfold towerWeight
  rw [SU2QuaternionConditionalVarianceTower.heads_compose]
  exact (partialHaarHeads_congr (N width)
    ((partialHaarHeads_mul_lift (t*(N width))
      (blockWindowWeight w K width n t) (stepWeight w K width)).trans
      (((inner_mass w K width n t).mul_right (stepWeight w K width)).trans
        (RatPolyCoeffEqv.mul_comm _ _)))).trans
    (outer_moment w K width _)

/-- Signed covariance of the actual finite reconstruction defect. -/
def originalInnovationCovariance (w : Q') (K width n t : Nat) (psi phi : RatPoly) : RatPoly :=
  let a := originalBlockTransfer w K width t (terminalMessage w K width n)
  let b := originalBlockTransfer w K width t (polyMul (terminalMessage w K width n) psi)
  let e := polyAdd b (polyNeg (polyMul a phi))
  polyAdd
    (polyMul (originalBlockTransfer w K width 1 a)
      (originalBlockTransfer w K width 1 (polyMul phi e)))
    (polyNeg (polyMul (originalBlockTransfer w K width 1 (polyMul a phi))
      (originalBlockTransfer w K width 1 e)))

/-- On the actual vacuum input the signed covariance cancels the entire
last-prediction noise. Small reciprocal error is not a multiplicative
comparison to the zero full-window vacuum noise. No positivity is needed. -/
theorem originalInnovationCovariance_one (w : Q') (K width n t : Nat)
    (phi : RatPoly) :
    RatPolyCoeffEqv (originalInnovationCovariance w K width n t polyOne phi)
      (polyNeg (blockNoise w K width 1
        (originalBlockTransfer w K width t (terminalMessage w K width n)) phi)) := by
  let a := originalBlockTransfer w K width t (terminalMessage w K width n)
  let b := originalBlockTransfer w K width t
    (polyMul (terminalMessage w K width n) polyOne)
  let e := polyAdd b (polyNeg (polyMul a phi))
  let A := originalBlockTransfer w K width 1 a
  let v := originalBlockTransfer w K width 1 (polyMul a phi)
  let H := originalBlockTransfer w K width 1 (polyMul a (polyMul phi phi))
  have hb : RatPolyCoeffEqv b a :=
    (inner_moment w K width n t polyOne).symm.trans
      ((partialHaarHeads_congr (t*(N width))
        (RatPolyCoeffEqv.mul_one (blockWindowWeight w K width n t))).trans
        (inner_mass w K width n t))
  have he := hb.add (RatPolyCoeffEqv.refl (polyNeg (polyMul a phi)))
  have sub (p q : RatPoly) :
      RatPolyCoeffEqv (originalBlockTransfer w K width 1 (polyAdd p (polyNeg q)))
        (polyAdd (originalBlockTransfer w K width 1 p)
          (polyNeg (originalBlockTransfer w K width 1 q))) := by
    have hr := coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.add (.var 1) (.neg (.var 2))))
      (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 0) (.var 2))))
      (by decide) (fun | 0 => stepWeight w K width | 1 => p | _ => q)
    refine (outer_moment w K width _).symm.trans
      ((partialHaarHeads_congr (N width) hr).trans ?_)
    dsimp only [coeffEvalExpr]
    rw [partialHaarHeads_add]
    exact (outer_moment w K width p).add
      ((partialHaarHeads_neg (N width) _).trans
        (RatPolyCoeffEqv.neg (outer_moment w K width q)))
  have hz := (outer_moment w K width e).symm.trans
    ((outer_congr w K width he).trans (sub a (polyMul a phi)))
  have hc := (outer_moment w K width (polyMul phi e)).symm.trans
    ((outer_congr w K width ((he.mul_left phi).trans
    (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.add (.var 1) (.neg (.mul (.var 1) (.var 0)))))
      (.add (.mul (.var 1) (.var 0))
        (.neg (.mul (.var 1) (.mul (.var 0) (.var 0)))))
      (by decide) (fun | 0 => phi | _ => a)))).trans
    (sub (polyMul a phi) (polyMul a (polyMul phi phi))))
  exact (((RatPolyCoeffEqv.refl A).mul hc).add
    (RatPolyCoeffEqv.neg ((RatPolyCoeffEqv.refl v).mul hz))).trans
    (coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.var 0) (.add (.var 1) (.neg (.var 2))))
        (.neg (.mul (.var 1) (.add (.var 0) (.neg (.var 1))))))
      (.neg (.add (.mul (.var 0) (.var 2)) (.neg (.mul (.var 1) (.var 1)))))
      (by decide) (fun | 0 => A | 1 => v | _ => H))

private theorem covariance_pin (w : Q') (K width n t : Nat) (psi phi : RatPoly) :
    RatPolyCoeffEqv
      (innovationCovariance (t*(N width)) (N width)
        (blockWindowWeight w K width n t) (stepWeight w K width) psi phi)
      (originalInnovationCovariance w K width n t psi phi) := by
  have ha := inner_mass w K width n t
  have hb := inner_moment w K width n t psi
  have he := hb.add (RatPolyCoeffEqv.neg (ha.mul_right phi))
  exact ((outer_congr w K width ha).mul
    (outer_congr w K width (he.mul_left phi))).add
    (RatPolyCoeffEqv.neg ((outer_congr w K width (ha.mul_right phi)).mul
      (outer_congr w K width he)))

private theorem determinant_pin (w : Q') (K width n t : Nat) (psi : RatPoly) :
    RatPolyCoeffEqv
      (determinant (t*(N width)+N width)
        (towerWeight (t*(N width)) (blockWindowWeight w K width n t) (stepWeight w K width)) psi)
      (blockNoise w K width (t+1) (terminalMessage w K width n) psi) :=
  ((total_mass w K width n t).mul (total_moment w K width n t (polyMul psi psi))).add
    (RatPolyCoeffEqv.neg ((total_moment w K width n t psi).mul
      (total_moment w K width n t psi)))

private theorem outer_determinant_pin (w : Q') (K width n t : Nat) (phi : RatPoly) :
    RatPolyCoeffEqv
      (determinant (N width) (polyMul (stepWeight w K width)
        (partialHaarHeads (t*(N width)) (blockWindowWeight w K width n t))) phi)
      (blockNoise w K width 1
        (originalBlockTransfer w K width t (terminalMessage w K width n)) phi) := by
  let a := partialHaarHeads (t*(N width)) (blockWindowWeight w K width n t)
  have ha := inner_mass w K width n t
  have hm := outer_congr w K width ha
  have hq (q : RatPoly) : RatPolyCoeffEqv
      (mean (N width) (polyMul (stepWeight w K width) a) q)
      (originalBlockTransfer w K width 1
        (polyMul (originalBlockTransfer w K width t (terminalMessage w K width n)) q)) :=
    (partialHaarHeads_congr (N width)
      (RatPolyCoeffEqv.mul_assoc (stepWeight w K width) a q)).trans
      (outer_congr w K width (ha.mul_right q))
  exact (hm.mul (hq (polyMul phi phi))).add
    (RatPolyCoeffEqv.neg ((hq phi).mul (hq phi)))

/-- The actual nonunit block tower, with its signed covariance retained.
The square certificate is constructed from the original positive window,
for arbitrary supported psi and phi, including zero transitions. -/
def original_block_innovation_certificate {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n t : Nat) {psi phi : RatPoly}
    (hpsi : SupportedQuaternionBlocks (N width) psi)
    (hphi : SupportedQuaternionBlocks (N width) phi) :
    Certificate (N width)
      (polyAdd (blockNoise w K width (t+1) (terminalMessage w K width n) psi)
        (polyNeg (polyAdd
          (blockNoise w K width 1
            (originalBlockTransfer w K width t (terminalMessage w K width n)) phi)
          (polyAdd (originalInnovationCovariance w K width n t psi phi)
            (originalInnovationCovariance w K width n t psi phi))))) := by
  let W := blockWindowWeight w K width n t
  let R := stepWeight w K width
  have hs : (t+1)*(N width) = N width+t*(N width) := by rw [Nat.succ_mul]; omega
  have hsmall : N width ≤ (t+1)*(N width) := by rw [Nat.succ_mul]; omega
  have hbase : SupportedQuaternionBlocks (N width+t*(N width)) W := hs ▸
    supported_polyMul (support_mono (terminalMessage_supported w K width n) hsmall)
      (halfOpenAction_supported (kineticWeight_supported w K width)
        (spatialWeight_supported w K width) t)
  have Pbase : Certificate (N width+t*(N width)) W :=
    (certificate_extend (t*(N width)) (terminalMessage_supported w K width n)
      (terminalMessage_certificate hw0 hw1 K width hK n)).mul
      (hs ▸ halfOpenAction_certificate (kineticWeight_supported w K width)
        (spatialWeight_supported w K width) (stepWeightCertificate hw0 hw1 K width hK) t)
  have hW : SupportedQuaternionBlocks (N width+N width+t*(N width)) W :=
    support_mono hbase (by omega)
  have PW : Certificate (N width+N width+t*(N width)) W := by
    have he : N width+t*(N width)+N width = N width+N width+t*(N width) := by omega
    exact he ▸ certificate_extend (N width) hbase Pbase
  have hR : SupportedQuaternionBlocks (N width+N width) R :=
    supported_polyMul (kineticWeight_supported w K width)
      (support_mono (spatialWeight_supported w K width) (by omega))
  have P := innovation_certificate (N width) (t*(N width)) (N width) W R psi phi
    hW hR (support_mono hpsi (by omega)) (support_mono hphi (by omega))
    PW (stepWeightCertificate hw0 hw1 K width hK)
  have hC := covariance_pin w K width n t psi phi
  have hpin := (determinant_pin w K width n t psi).add
    (RatPolyCoeffEqv.neg ((outer_determinant_pin w K width n t phi).add (hC.add hC)))
  exact Certificate.ofCoeff hpin.symm P

/-- The existing finite reciprocal polynomial is an admissible actual phi.
This specializes support; it does not identify that polynomial with b/a. -/
def original_block_ratio_innovation_certificate {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n t k : Nat) {psi : RatPoly}
    (hpsi : SupportedQuaternionBlocks (N width) psi) :
    let phi := blockConditionalRatio hw0 hw1 K width hK n t psi k
    Certificate (N width)
      (polyAdd (blockNoise w K width (t+1) (terminalMessage w K width n) psi)
        (polyNeg (polyAdd
          (blockNoise w K width 1
            (originalBlockTransfer w K width t (terminalMessage w K width n)) phi)
          (polyAdd (originalInnovationCovariance w K width n t psi phi)
            (originalInnovationCovariance w K width n t psi phi))))) :=
  original_block_innovation_certificate hw0 hw1 K width hK n t hpsi
    (blockConditionalRatio_supported hw0 hw1 K width hK n t hpsi k)

#print axioms originalInnovationCovariance
#print axioms originalInnovationCovariance_one
#print axioms original_block_innovation_certificate
#print axioms original_block_ratio_innovation_certificate

end YMGap.Continuum.BF4ExactSlabFixedSpatialBlockInnovationTower
