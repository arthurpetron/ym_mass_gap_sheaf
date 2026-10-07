/-
# Original finite innovation covariance with a constructed geometric cap

For the existing finite reciprocal phi=G_k*b, the actual reconstruction
defect e=b-a*phi has two positive relative certificates
  c*mixRate^k*a plus/minus e.
The error multiplier and the original relative source bounds construct these
certificates; no division by a or reconstruction estimate is assumed.

Multiplication by the actual original K*V step and conditional Gruss give
  Cov^2 <= (L^2*A^2-(T e)^2)*noise_1(a,phi),
L=(1/2)^k+c*mixRate^k, A=T a. The strictly positive dyadic enlargement
also handles c=0 and mixRate=0. All shared output coordinates are retained.
Historical variance in the innovation tower is separate from this error;
its smallness, useful changing-family bounds, survival and Clay remain open.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialBlockInnovationTower
import YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjection
import YMGap.Continuum.SU2QuaternionConditionalGrussSquare
import YMGap.Continuum.QuaternionHaarRelativeIntervalProduct
import YMGap.Continuum.QuaternionHaarSignedInterval
import YMGap.Constructive.HalfPow
import YMGap.Constructive.Sqrt

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialBlockInnovationCovariance

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
open YMGap.Continuum.SU2QuaternionHaarCertificateExtension (certificate_extend)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap SquareBound)
open YMGap.Continuum.QuaternionHaarPolynomialInterval (Interval)
open YMGap.Continuum.QuaternionHaarRelativePolynomialInterval (RelativeInterval)
open YMGap.Continuum.QuaternionHaarPositiveWindowInverse
  (reciprocal multiplierErrorInterval)
open YMGap.Continuum.SU2QuaternionMultiHeadVarianceReplica (determinant)
open YMGap.Continuum.SU2QuaternionConditionalGrussSquare
  (centeredRelativeCoefficient conditionalGrussSquare_certificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight kineticWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBound (stepWeight stepWeightCertificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (kineticFloor kineticCap)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate
  (mixRate mixRate_nonnegative kineticFloor_le_cap)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing (iterateStep_add)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage terminalMessage_supported terminalMessage_certificate terminalMessage_mass_positive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockMultiplicationDefect (originalBlockTransfer)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalNoise (blockNoise)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalRatio
  (blockConditionalRatio blockConditionalRatio_supported blockReciprocal
   blockRelativeCertificates blockWindowLower blockWindowUpper
   blockWindowLower_positive blockWindowUpper_positive blockWindowCertificates blockWindow_radius_pin)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockInnovationTower (originalInnovationCovariance)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjection
  (spatialFringeMass spatialFringeMass_supported)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)

local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks kineticWeight spatialWeight

private theorem support_mono {small large : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks small p) (h : small ≤ large) :
    SupportedQuaternionBlocks large p :=
  fun term ht => Nat.le_trans (hp term ht) (Nat.mul_le_mul_left 4 h)

private theorem support_neg {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) : SupportedQuaternionBlocks blocks (polyNeg p) := by
  intro term ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private theorem block_terminal (w : Q') (K width n t : Nat) :
    originalBlockTransfer w K width t (terminalMessage w K width n) =
      terminalMessage w K width (n+t) := by
  unfold originalBlockTransfer terminalMessage
  exact (iterateStep_add (N width) (kineticWeight w K width)
    (spatialWeight w K width) n t polyOne).symm

private theorem window_order {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : headCutoff w ≤ K) (n t : Nat) :
    blockWindowLower w K width n t ≤ blockWindowUpper w K width n t :=
  Q'.mul_le_mul_of_nonneg_right _ _ _ (kineticFloor_le_cap hw0 hw1 width)
    (Q'.le_of_lt (terminalMessage_mass_positive hw0 hw1 K width hK (n+t-1)))

/-- Actual reconstruction defect on the original middle slice. -/
def blockReconstructionDefect {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : headCutoff w ≤ K) (n t : Nat) (psi : RatPoly) (k : Nat) : RatPoly :=
  polyAdd (originalBlockTransfer w K width t (polyMul (terminalMessage w K width n) psi))
    (polyNeg (polyMul (terminalMessage w K width (n+t))
      (blockConditionalRatio hw0 hw1 K width hK n t psi k)))

private theorem defect_supported {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : headCutoff w ≤ K) (n t k : Nat) {psi : RatPoly}
    (hpsi : SupportedQuaternionBlocks (N width) psi) :
    SupportedQuaternionBlocks (N width)
      (blockReconstructionDefect hw0 hw1 K width hK n t psi k) :=
  supported_add
    (iterateStep_supported (kineticWeight_supported w K width) (spatialWeight_supported w K width)
      t (supported_polyMul (terminalMessage_supported w K width n) hpsi))
    (support_neg (supported_polyMul (terminalMessage_supported w K width (n+t))
      (blockConditionalRatio_supported hw0 hw1 K width hK n t hpsi k)))

/-- The SAME original terminal message is the base of the geometric error
interval. Both endpoints are constructed from actual source and multiplier
certificates, with the exact existing mixRate retained. -/
def original_reconstruction_relativeInterval {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : headCutoff w ≤ K) (n t : Nat) (hdepth : 1 ≤ n+t)
    {psi : RatPoly} {c : Q'} (I : Interval (N width) psi c) (k : Nat) :
    RelativeInterval (N width) (terminalMessage w K width (n+t))
      (blockReconstructionDefect hw0 hw1 K width hK n t psi k)
      (c*(mixRate hw0 hw1 width)^k) := by
  let a := terminalMessage w K width (n+t)
  let b := originalBlockTransfer w K width t (polyMul (terminalMessage w K width n) psi)
  let u := blockWindowUpper w K width n t
  let hu := blockWindowUpper_positive hw0 hw1 K width hK n t
  let ell := blockWindowLower w K width n t
  let rho := QuaternionHaarPositiveWindowInverse.radius ell u hu
  let G := reciprocal a u hu k
  have B : RelativeInterval (N width) a b c :=
    ⟨(blockRelativeCertificates hw0 hw1 K width hK n t I).1,
     (blockRelativeCertificates hw0 hw1 K width hK n t I).2⟩
  have M := QuaternionHaarSignedInterval.Interval.neg
    (multiplierErrorInterval (terminalMessage_supported w K width (n+t)) hu
      (window_order hw0 hw1 K width hK n t)
      (blockWindowCertificates hw0 hw1 K width hK n t hdepth).1
      (blockWindowCertificates hw0 hw1 K width hK n t hdepth).2 k)
  have Q : RelativeInterval (N width) polyOne
      (polyNeg (polyAdd (polyMul a G) (polyNeg polyOne))) (rho^k) :=
    ⟨Certificate.ofCoeff
      ((RatPolyCoeffEqv.mul_one (cap (rho^k))).add (RatPolyCoeffEqv.refl _)) M.lower,
     Certificate.ofCoeff
      ((RatPolyCoeffEqv.mul_one (cap (rho^k))).add (RatPolyCoeffEqv.refl _)) M.upper⟩
  have J := RelativeInterval.baseOfCoeff (RatPolyCoeffEqv.mul_one a).symm (B.mul Q)
  have he : RatPolyCoeffEqv (blockReconstructionDefect hw0 hw1 K width hK n t psi k)
      (polyMul b (polyNeg (polyAdd (polyMul a G) (polyNeg polyOne)))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.add (.var 1) (.neg (.mul (.var 0) (.mul (.var 2) (.var 1)))))
      (.mul (.var 1) (.neg (.add (.mul (.var 0) (.var 2)) (.neg (.const 1)))))
      (by decide) (fun | 0 => a | 1 => b | _ => G)
  exact (RelativeInterval.ofCoeff he J).changeCap
    (Q'.mul_eqv_congr_left c _ _
      (Q'.pow_eqv_congr (blockWindow_radius_pin hw0 hw1 K width hK n t) k))

/-- Strict positive geometric enlargement needed by the Gruss compiler,
including a zero observable cap or a zero original mix rate. -/
def innovationRelativeCap {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (width : Nat) (c : Q') (k : Nat) : Q' :=
  HalfPow.half^k + c*(mixRate hw0 hw1 width)^k

private theorem half_power_positive : ∀ k : Nat, (0 : Q') < HalfPow.half^k
  | 0 => by decide
  | k+1 => Q'.mul_pos (by decide : (0 : Q') < HalfPow.half) (half_power_positive k)

private theorem cap_positive {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (width : Nat) {c : Q'} (hc : (0 : Q') ≤ c) (k : Nat) :
    (0 : Q') < innovationRelativeCap hw0 hw1 width c k :=
  Q'.pos_add_nonneg (half_power_positive k)
    (Q'.mul_nonneg _ _ hc (Q'.pow_nonneg _ (mixRate_nonnegative hw0 hw1 width) k))

private theorem cap_enlarges {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (width : Nat) (c : Q') (k : Nat) :
    c*(mixRate hw0 hw1 width)^k ≤ innovationRelativeCap hw0 hw1 width c k :=
  Q'.le_trans' _ _ _
    (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt (half_power_positive k)))
    (Q'.le_of_eqv (Q'.add_comm_eqv _ _))

private theorem moment_pin (w : Q') (K width : Nat) (p : RatPoly) :
    RatPolyCoeffEqv (partialHaarHeads (N width) (polyMul (stepWeight w K width) p))
      (originalBlockTransfer w K width 1 p) :=
  partialHaarHeads_congr (N width)
    (RatPolyCoeffEqv.mul_assoc (kineticWeight w K width) (spatialWeight w K width) p)

private theorem weighted_moment_pin (w : Q') (K width : Nat) (a p : RatPoly) :
    RatPolyCoeffEqv
      (partialHaarHeads (N width) (polyMul (polyMul (stepWeight w K width) a) p))
      (originalBlockTransfer w K width 1 (polyMul a p)) :=
  (partialHaarHeads_congr (N width) (RatPolyCoeffEqv.mul_assoc (stepWeight w K width) a p)).trans
    (moment_pin w K width (polyMul a p))

/-- Original covariance square controlled by its actual one-step noise.
The retained -(T e)^2 term comes from the two constructed positive laws;
no desired covariance inequality, inverse terminal message or history
estimate is assumed. -/
def original_innovationCovariance_gruss_certificate {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : headCutoff w ≤ K) (n t : Nat) (hdepth : 1 ≤ n+t)
    {psi : RatPoly} {c : Q'} (I : Interval (N width) psi c) (k : Nat) :
    let a := terminalMessage w K width (n+t)
    let phi := blockConditionalRatio hw0 hw1 K width hK n t psi k
    let e := blockReconstructionDefect hw0 hw1 K width hK n t psi k
    let A := originalBlockTransfer w K width 1 a
    let z := originalBlockTransfer w K width 1 e
    let L := innovationRelativeCap hw0 hw1 width c k
    let C := originalInnovationCovariance w K width n t psi phi
    Certificate (N width)
      (polyAdd (polyMul
        (polyAdd (polyMul (cap (L*L)) (polyMul A A)) (polyNeg (polyMul z z)))
        (blockNoise w K width 1 a phi)) (polyNeg (polyMul C C))) := by
  dsimp only
  let a := terminalMessage w K width (n+t)
  let phi := blockConditionalRatio hw0 hw1 K width hK n t psi k
  let e := blockReconstructionDefect hw0 hw1 K width hK n t psi k
  let R := stepWeight w K width
  let W := polyMul R a
  let d := polyMul R e
  let L := innovationRelativeCap hw0 hw1 width c k
  have ha := terminalMessage_supported w K width (n+t)
  have he := defect_supported hw0 hw1 K width hK n t k I.support
  have hf := blockConditionalRatio_supported hw0 hw1 K width hK n t I.support k
  have hR : SupportedQuaternionBlocks (N width+N width) R :=
    supported_polyMul (kineticWeight_supported w K width)
      (support_mono (spatialWeight_supported w K width) (by omega))
  have E := (original_reconstruction_relativeInterval hw0 hw1 K width hK n t hdepth I k).weaken
    (terminalMessage_certificate hw0 hw1 K width hK (n+t)) (cap_enlarges hw0 hw1 width c k)
  have hcap := (SquareBound.constant (N width) L).support
  have Ep := certificate_extend (N width)
    (supported_add (supported_polyMul hcap ha) he) E.lower
  have Em := certificate_extend (N width)
    (supported_add (supported_polyMul hcap ha) (support_neg he)) E.upper
  have Pplus : Certificate (N width+N width) (polyAdd (polyMul (cap L) W) d) :=
    Certificate.ofCoeff
      (coeffEvalExpr_eqv_of_normalize_eq
        (.add (.mul (.var 0) (.mul (.var 1) (.var 2))) (.mul (.var 1) (.var 3)))
        (.mul (.var 1) (.add (.mul (.var 0) (.var 2)) (.var 3)))
        (by decide) (fun | 0 => cap L | 1 => R | 2 => a | _ => e))
      ((stepWeightCertificate hw0 hw1 K width hK).mul Ep)
  have Pminus : Certificate (N width+N width) (polyAdd (polyMul (cap L) W) (polyNeg d)) :=
    Certificate.ofCoeff
      (coeffEvalExpr_eqv_of_normalize_eq
        (.add (.mul (.var 0) (.mul (.var 1) (.var 2))) (.neg (.mul (.var 1) (.var 3))))
        (.mul (.var 1) (.add (.mul (.var 0) (.var 2)) (.neg (.var 3))))
        (by decide) (fun | 0 => cap L | 1 => R | 2 => a | _ => e))
      ((stepWeightCertificate hw0 hw1 K width hK).mul Em)
  have P := conditionalGrussSquare_certificate (N width) (N width) W d phi L
    (cap_positive hw0 hw1 width I.nonnegative k)
    (supported_polyMul hR (support_mono ha (by omega)))
    (supported_polyMul hR (support_mono he (by omega)))
    (support_mono hf (by omega)) Pplus Pminus
  have hA := moment_pin w K width a
  have hz := moment_pin w K width e
  have hb := weighted_moment_pin w K width a phi
  have hs : RatPolyCoeffEqv
      (polyAdd (polyMul (partialHaarHeads (N width) W)
        (partialHaarHeads (N width) (polyMul d phi)))
        (polyNeg (polyMul (partialHaarHeads (N width) (polyMul W phi))
          (partialHaarHeads (N width) d))))
      (originalInnovationCovariance w K width n t psi phi) := by
    have hx : RatPolyCoeffEqv (partialHaarHeads (N width) (polyMul d phi))
        (originalBlockTransfer w K width 1 (polyMul phi e)) :=
      (partialHaarHeads_congr (N width)
        (coeffEvalExpr_eqv_of_normalize_eq
          (.mul (.mul (.var 0) (.var 1)) (.var 2))
          (.mul (.var 0) (.mul (.var 2) (.var 1)))
          (by decide) (fun | 0 => R | 1 => e | _ => phi))).trans
        (moment_pin w K width (polyMul phi e))
    unfold originalInnovationCovariance
    rw [block_terminal]
    exact (hA.mul hx).add (RatPolyCoeffEqv.neg (hb.mul hz))
  have hnoise : RatPolyCoeffEqv (determinant (N width) W phi)
      (blockNoise w K width 1 a phi) :=
    (hA.mul (weighted_moment_pin w K width a (polyMul phi phi))).add
      (RatPolyCoeffEqv.neg (hb.mul hb))
  have hcoefficient : RatPolyCoeffEqv (centeredRelativeCoefficient (N width) W d L)
      (polyAdd (polyMul (cap (L*L))
        (polyMul (originalBlockTransfer w K width 1 a) (originalBlockTransfer w K width 1 a)))
        (polyNeg (polyMul (originalBlockTransfer w K width 1 e) (originalBlockTransfer w K width 1 e)))) :=
    ((hA.mul hA).mul_left (cap (L*L))).add (RatPolyCoeffEqv.neg (hz.mul hz))
  exact Certificate.ofCoeff
    ((hcoefficient.mul hnoise).add (RatPolyCoeffEqv.neg (hs.mul hs))).symm P

/-- The covariance estimate reaches the literal spatial/reciprocal multiplier
of the direct-score consumer. Inner and output reciprocal degrees are
independent; no replacement of Vbar^2 by V or surviving-form estimate occurs. -/
theorem original_innovationCovariance_weighted_bound {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : headCutoff w ≤ K) (n t : Nat) (hdepth : 1 ≤ n+t)
    {psi : RatPoly} {c : Q'} (I : Interval (N width) psi c) (k kout : Nat) :
    let a := terminalMessage w K width (n+t)
    let phi := blockConditionalRatio hw0 hw1 K width hK n t psi k
    let e := blockReconstructionDefect hw0 hw1 K width hK n t psi k
    let A := originalBlockTransfer w K width 1 a
    let z := originalBlockTransfer w K width 1 e
    let L := innovationRelativeCap hw0 hw1 width c k
    let C := originalInnovationCovariance w K width n t psi phi
    let Vbar := spatialFringeMass w K width
    let Gout := blockReciprocal hw0 hw1 K width hK n (t+1) kout
    let Lambda := polyMul (polyMul Vbar Vbar) (polyMul Gout Gout)
    quaternionHaar (N width) (polyMul Lambda (polyMul C C)) ≤
      quaternionHaar (N width) (polyMul Lambda
        (polyMul (polyAdd (polyMul (cap (L*L)) (polyMul A A))
          (polyNeg (polyMul z z))) (blockNoise w K width 1 a phi))) := by
  dsimp only
  let a := terminalMessage w K width (n+t)
  let phi := blockConditionalRatio hw0 hw1 K width hK n t psi k
  let e := blockReconstructionDefect hw0 hw1 K width hK n t psi k
  let A := originalBlockTransfer w K width 1 a
  let z := originalBlockTransfer w K width 1 e
  let L := innovationRelativeCap hw0 hw1 width c k
  let C := originalInnovationCovariance w K width n t psi phi
  let Vbar := spatialFringeMass w K width
  let Gout := blockReciprocal hw0 hw1 K width hK n (t+1) kout
  let Lambda := polyMul (polyMul Vbar Vbar) (polyMul Gout Gout)
  let p := polyMul (polyAdd (polyMul (cap (L*L)) (polyMul A A))
    (polyNeg (polyMul z z))) (blockNoise w K width 1 a phi)
  let E := polyMul Lambda (polyAdd p (polyNeg (polyMul C C)))
  have P := original_innovationCovariance_gruss_certificate hw0 hw1 K width hK n t hdepth I k
  have PG : Certificate (N width) (polyMul Gout Gout) :=
    Certificate.square Gout
      (QuaternionHaarPositiveWindowInverse.reciprocal_supported
        (terminalMessage_supported w K width (n+(t+1))) _ _ kout)
  have hn : (0 : Q') ≤ quaternionHaar (N width) E :=
    (((Certificate.square Vbar (spatialFringeMass_supported w K width)).mul PG).mul P).haar_nonnegative
  have hid : RatPolyCoeffEqv
      (polyAdd (polyMul Lambda (polyMul C C)) E) (polyMul Lambda p) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.var 0) (.mul (.var 1) (.var 1)))
        (.mul (.var 0) (.add (.var 2) (.neg (.mul (.var 1) (.var 1))))))
      (.mul (.var 0) (.var 2))
      (by decide) (fun | 0 => Lambda | 1 => C | _ => p)
  have heq := Q'.eqv_trans _ _ _
    (Q'.eqv_symm (quaternionHaar_append (N width) _ _)) (haar_of_coeff hid)
  exact Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ _ hn) (Q'.le_of_eqv heq)

#print axioms blockReconstructionDefect
#print axioms original_reconstruction_relativeInterval
#print axioms innovationRelativeCap
#print axioms original_innovationCovariance_gruss_certificate
#print axioms original_innovationCovariance_weighted_bound

end YMGap.Continuum.BF4ExactSlabFixedSpatialBlockInnovationCovariance
