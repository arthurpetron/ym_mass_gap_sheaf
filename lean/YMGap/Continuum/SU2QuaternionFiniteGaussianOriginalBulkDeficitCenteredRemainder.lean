/-
# Centered lagged remainder for the bounded ORIGINAL bulk deficit

The bounded bulk deficit already splits globally on the unit-quaternion Haar
carrier into its vector-coordinate quadratic jet and a positive scalar-square
remainder.  Here the actual finite OWN mean is split at the same time, giving
an exact decomposition of the centered source.  Haar-carrier extension and
coordinate lifting then expand the actual finite chronological pair into the
jet--jet term and three explicit remainder terms.

The same normalized ORIGINAL window functional is positive on every supported
square.  A direct rational pre-inner-form argument therefore gives sharp
Cauchy--Schwarz bounds for each lagged cross term, without changing the action,
partition, center, heat cutoff, or time window.

This is a finite fixed-nome remainder identity and budget.  It does not bound
the diagonal remainder norms uniformly, compare with the FREE Gaussian law,
remove a cutoff, construct a continuum Hamiltonian, or prove a Clay mass gap.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitJetRemainder
import YMGap.Continuum.SU2QuaternionHaarCertificateExtension
import YMGap.Continuum.SU2QuaternionHaarCertificateLift
import YMGap.Continuum.BF4ExactSlabFixedSpatialWindowFunctionalLaws
import YMGap.Continuum.OSReconstructionProgress
import YMGap.Continuum.PositiveChannelTraceBound

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitCenteredRemainder

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation (finitePolySum)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMovingCenterLagDifference (centeredPair)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder (plaquette_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowFunctionalLaws
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPairing (windowRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.OSReconstructionProgress
open YMGap.Continuum.QuaternionHaarDensityVariance (shifted shifted_supported)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction (HaarCarrierEqv)
open YMGap.Continuum.SU2QuaternionHaarCertificateExtension (carrier_extend)
open YMGap.Continuum.SU2QuaternionHaarCertificateLift (lift_carrier)
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitCentering
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitJetRemainder

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] windowRatio

private theorem supported_smul_local {blocks : Nat} {polynomial : RatPoly}
    (hpolynomial : SupportedQuaternionBlocks blocks polynomial) (scale : Q') :
    SupportedQuaternionBlocks blocks (polySmul scale polynomial) := by
  intro term hterm
  obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hterm
  exact hpolynomial source hsource

private theorem supported_mono_local {small large : Nat} {polynomial : RatPoly}
    (hpolynomial : SupportedQuaternionBlocks small polynomial) (hsize : small ≤ large) :
    SupportedQuaternionBlocks large polynomial := by
  intro term hterm
  exact Nat.le_trans (hpolynomial term hterm) (Nat.mul_le_mul_left 4 hsize)

private theorem finitePolySum_supported_local {Index : Type} {blocks : Nat}
    (polynomial : Index → RatPoly)
    (hpolynomial : ∀ index, SupportedQuaternionBlocks blocks (polynomial index)) :
    ∀ items : List Index,
      SupportedQuaternionBlocks blocks (finitePolySum polynomial items)
  | [] => by
      intro term hterm
      cases hterm
  | index :: items =>
      supported_add (hpolynomial index)
        (finitePolySum_supported_local polynomial hpolynomial items)

/-- The global vector-coordinate jet uses only the original one-slice carrier. -/
theorem originalBulkVectorQuadraticJet_supported (s : Nat) (hs : 0 < s) :
    SupportedQuaternionBlocks (N (s * s))
      (originalBulkVectorQuadraticJet s hs) := by
  apply finitePolySum_supported_local
  intro face
  apply supported_smul_local
  have hface := plaquette_supported (s * s) (N (s * s)) (Nat.le_refl _) face
  exact supported_add (supported_polyMul hface.iPart hface.iPart)
    (supported_add (supported_polyMul hface.jPart hface.jPart)
      (supported_polyMul hface.kPart hface.kPart))

/-- The global scalar-square remainder uses only the original one-slice carrier. -/
theorem originalBulkScalarSquareRemainder_supported (s : Nat) (hs : 0 < s) :
    SupportedQuaternionBlocks (N (s * s))
      (originalBulkScalarSquareRemainder s hs) := by
  apply finitePolySum_supported_local
  intro face
  apply supported_smul_local
  exact supported_polyMul
    (plaquetteScalarDeficit_supported (s * s) (N (s * s)) (Nat.le_refl _) face)
    (plaquetteScalarDeficit_supported (s * s) (N (s * s)) (Nat.le_refl _) face)

/-- The actual bounded deficit source, after subtracting its finite OWN mean. -/
def originalBulkDeficitOwnShifted {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (s : Nat) (hs : 0 < s) (stage n : Nat) : RatPoly :=
  shifted (sourcePolynomial (originalBulkDeficitExpression s hs))
    (originalBulkDeficitOwnMean hw0 hw1 s hs stage n)

/-- The vector-coordinate jet after subtracting its part of the same OWN mean. -/
def originalBulkVectorQuadraticJetOwnShifted {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (s : Nat) (hs : 0 < s) (stage n : Nat) : RatPoly :=
  shifted (originalBulkVectorQuadraticJet s hs)
    (originalBulkVectorQuadraticJetOwnMean hw0 hw1 s hs stage n)

/-- The scalar-square remainder after subtracting its part of the same OWN mean. -/
def originalBulkScalarSquareRemainderOwnShifted {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (s : Nat) (hs : 0 < s) (stage n : Nat) : RatPoly :=
  shifted (originalBulkScalarSquareRemainder s hs)
    (originalBulkScalarSquareRemainderOwnMean hw0 hw1 s hs stage n)

theorem originalBulkDeficitOwnShifted_supported {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (s : Nat) (hs : 0 < s) (stage n : Nat) :
    SupportedQuaternionBlocks (N (s * s))
      (originalBulkDeficitOwnShifted hw0 hw1 s hs stage n) := by
  unfold originalBulkDeficitOwnShifted
  apply shifted_supported
  simpa only [Nat.zero_add, Nat.one_mul] using
    (source_supported 0 (originalBulkDeficitExpression s hs)
      (originalBulkDeficitExpression_within s hs))

theorem originalBulkVectorQuadraticJetOwnShifted_supported {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (s : Nat) (hs : 0 < s) (stage n : Nat) :
    SupportedQuaternionBlocks (N (s * s))
      (originalBulkVectorQuadraticJetOwnShifted hw0 hw1 s hs stage n) := by
  exact shifted_supported (originalBulkVectorQuadraticJet_supported s hs) _

theorem originalBulkScalarSquareRemainderOwnShifted_supported {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (s : Nat) (hs : 0 < s) (stage n : Nat) :
    SupportedQuaternionBlocks (N (s * s))
      (originalBulkScalarSquareRemainderOwnShifted hw0 hw1 s hs stage n) := by
  exact shifted_supported (originalBulkScalarSquareRemainder_supported s hs) _

private theorem neg_add_eqv_of_add_eqv {center leftCenter rightCenter : Q'}
    (hcenter : center ≈ leftCenter + rightCenter) :
    (-center) ≈ (-leftCenter) + (-rightCenter) := by
  exact Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ hcenter)
    (poly_identity_of_normal_eq
      (.neg (.add (.var 0) (.var 1)))
      (.add (.neg (.var 0)) (.neg (.var 1)))
      (by decide) (fun | 0 => leftCenter | _ => rightCenter))

private theorem shifted_carrier_add {blocks : Nat} {source left right : RatPoly}
    {center leftCenter rightCenter : Q'}
    (hsource : HaarCarrierEqv blocks source (polyAdd left right))
    (hcenter : center ≈ leftCenter + rightCenter) :
    HaarCarrierEqv blocks (shifted source center)
      (polyAdd (shifted left leftCenter) (shifted right rightCenter)) := by
  let centerPolynomial := polySmul (-center) polyOne
  let leftCenterPolynomial := polySmul (-leftCenter) polyOne
  let rightCenterPolynomial := polySmul (-rightCenter) polyOne
  have hsourceShift : RatPolyCoeffEqv
      (shifted source center) (polyAdd source centerPolynomial) := by
    unfold shifted centerPolynomial
    exact (RatPolyCoeffEqv.one_smul source).add (RatPolyCoeffEqv.refl _)
  have hleftShift : RatPolyCoeffEqv
      (shifted left leftCenter) (polyAdd left leftCenterPolynomial) := by
    unfold shifted leftCenterPolynomial
    exact (RatPolyCoeffEqv.one_smul left).add (RatPolyCoeffEqv.refl _)
  have hrightShift : RatPolyCoeffEqv
      (shifted right rightCenter) (polyAdd right rightCenterPolynomial) := by
    unfold shifted rightCenterPolynomial
    exact (RatPolyCoeffEqv.one_smul right).add (RatPolyCoeffEqv.refl _)
  have hcenterPolynomial : RatPolyCoeffEqv centerPolynomial
      (polyAdd leftCenterPolynomial rightCenterPolynomial) := by
    exact (RatPolyCoeffEqv.smul_coefficient
        (neg_add_eqv_of_add_eqv hcenter) polyOne).trans
      (RatPolyCoeffEqv.add_smul_same (-leftCenter) (-rightCenter) polyOne).symm
  exact (RatPolyCoeffEqv.haarCarrier hsourceShift).trans
    ((HaarCarrierEqv.add hsource
        (HaarCarrierEqv.refl blocks centerPolynomial)).trans
      ((RatPolyCoeffEqv.haarCarrier
          (((RatPolyCoeffEqv.refl (polyAdd left right)).add hcenterPolynomial).trans
            (RatPolyCoeffEqv.four_add_swap left right
              leftCenterPolynomial rightCenterPolynomial))).trans
        (RatPolyCoeffEqv.haarCarrier
          (hleftShift.symm.add hrightShift.symm))))

/-- Exact decomposition after subtracting the actual finite OWN center.  The
identity is on the SAME ORIGINAL one-slice Haar carrier. -/
theorem originalBulkDeficitOwnShifted_jet_remainder {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (s : Nat) (hs : 0 < s) (stage n : Nat) :
    HaarCarrierEqv (N (s * s))
      (originalBulkDeficitOwnShifted hw0 hw1 s hs stage n)
      (polyAdd
        (originalBulkVectorQuadraticJetOwnShifted hw0 hw1 s hs stage n)
        (originalBulkScalarSquareRemainderOwnShifted hw0 hw1 s hs stage n)) := by
  apply shifted_carrier_add
  · exact (RatPolyCoeffEqv.haarCarrier
      (originalBulkDeficitExpression_jet_source_pin s hs)).trans
      (originalBulkTraceDeficit_decomposition s hs)
  · exact originalBulkDeficitOwnMean_jet_remainder_split hw0 hw1 s hs stage n

/-- The actual normalized window functional evaluated on a chronological
left/right polynomial pair. -/
def laggedWindowPair {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : headCutoff w ≤ K) (n L : Nat)
    (left right : RatPoly) : Q' :=
  windowRatio hw0 hw1 K width hK n L n
    (polyMul left (liftBoundary (L * N width) right))

private def windowPairing {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : headCutoff w ≤ K) (m L n : Nat)
    (left right : RatPoly) : Q' :=
  windowRatio hw0 hw1 K width hK m L n (polyMul left right)

private theorem windowPairing_add_left {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : headCutoff w ≤ K) (m L n : Nat)
    (first second right : RatPoly) :
    windowPairing hw0 hw1 K width hK m L n (polyAdd first second) right ≈
      windowPairing hw0 hw1 K width hK m L n first right +
        windowPairing hw0 hw1 K width hK m L n second right := by
  unfold windowPairing
  rw [polyMul_add_left_exact]
  exact windowRatio_add hw0 hw1 K width hK m L n _ _

private theorem windowPairing_smul_left {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : headCutoff w ≤ K) (m L n : Nat)
    (scale : Q') (left right : RatPoly) :
    windowPairing hw0 hw1 K width hK m L n (polySmul scale left) right ≈
      scale * windowPairing hw0 hw1 K width hK m L n left right := by
  unfold windowPairing
  exact Q'.eqv_trans _ _ _
    (windowRatio_congr hw0 hw1 K width hK m L n
      (RatPolyCoeffEqv.polyMul_smul_left scale left right))
    (windowRatio_smul hw0 hw1 K width hK m L n scale _)

private theorem windowPairing_symm {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : headCutoff w ≤ K) (m L n : Nat)
    (left right : RatPoly) :
    windowPairing hw0 hw1 K width hK m L n left right ≈
      windowPairing hw0 hw1 K width hK m L n right left := by
  unfold windowPairing
  exact windowRatio_congr hw0 hw1 K width hK m L n
    (RatPolyCoeffEqv.mul_comm left right)

private def guardedWindowPolynomial (width L : Nat) :=
  {polynomial : RatPoly //
    SupportedQuaternionBlocks ((L + 1) * N width) polynomial}

private def windowPreInnerForm {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : headCutoff w ≤ K) (m L n : Nat) :
    PreInnerForm (guardedWindowPolynomial width L) where
  B := fun left right =>
    windowPairing hw0 hw1 K width hK m L n left.val right.val
  nonnegQuad := by
    intro firstScale secondScale first second
    let combination := polyAdd
      (polySmul firstScale first.val) (polySmul secondScale second.val)
    let B := windowPairing hw0 hw1 K width hK m L n
    have hcombination : SupportedQuaternionBlocks ((L + 1) * N width) combination :=
      supported_add (supported_smul_local first.property firstScale)
        (supported_smul_local second.property secondScale)
    have hnonnegative : (0 : Q') ≤ B combination combination := by
      exact windowRatio_square_nonnegative hw0 hw1 K width hK m L n hcombination
    have hfirst : B first.val combination ≈
        firstScale * B first.val first.val +
          secondScale * B first.val second.val := by
      exact Q'.eqv_trans _ _ _
        (windowPairing_symm hw0 hw1 K width hK m L n first.val combination)
        (Q'.eqv_trans _ _ _
          (windowPairing_add_left hw0 hw1 K width hK m L n
            (polySmul firstScale first.val) (polySmul secondScale second.val) first.val)
          (Q'.add_eqv_congr'
            (windowPairing_smul_left hw0 hw1 K width hK m L n
              firstScale first.val first.val)
            (Q'.eqv_trans _ _ _
              (windowPairing_smul_left hw0 hw1 K width hK m L n
                secondScale second.val first.val)
              (Q'.mul_eqv_congr_left _ _ _
                (windowPairing_symm hw0 hw1 K width hK m L n
                  second.val first.val)))))
    have hsecond : B second.val combination ≈
        firstScale * B first.val second.val +
          secondScale * B second.val second.val := by
      exact Q'.eqv_trans _ _ _
        (windowPairing_symm hw0 hw1 K width hK m L n second.val combination)
        (Q'.eqv_trans _ _ _
          (windowPairing_add_left hw0 hw1 K width hK m L n
            (polySmul firstScale first.val) (polySmul secondScale second.val) second.val)
          (Q'.add_eqv_congr'
            (windowPairing_smul_left hw0 hw1 K width hK m L n
              firstScale first.val second.val)
            (windowPairing_smul_left hw0 hw1 K width hK m L n
              secondScale second.val second.val)))
    have hfirstScaled : B (polySmul firstScale first.val) combination ≈
        firstScale *
          (firstScale * B first.val first.val +
            secondScale * B first.val second.val) :=
      Q'.eqv_trans _ _ _
        (windowPairing_smul_left hw0 hw1 K width hK m L n
          firstScale first.val combination)
        (Q'.mul_eqv_congr_left _ _ _ hfirst)
    have hsecondScaled : B (polySmul secondScale second.val) combination ≈
        secondScale *
          (firstScale * B first.val second.val +
            secondScale * B second.val second.val) :=
      Q'.eqv_trans _ _ _
        (windowPairing_smul_left hw0 hw1 K width hK m L n
          secondScale second.val combination)
        (Q'.mul_eqv_congr_left _ _ _ hsecond)
    have hexpand : B combination combination ≈
        firstScale *
            (firstScale * B first.val first.val +
              secondScale * B first.val second.val) +
          secondScale *
            (firstScale * B first.val second.val +
              secondScale * B second.val second.val) :=
      Q'.eqv_trans _ _ _
        (windowPairing_add_left hw0 hw1 K width hK m L n
          (polySmul firstScale first.val) (polySmul secondScale second.val) combination)
        (Q'.add_eqv_congr' hfirstScaled hsecondScaled)
    have hquad : B combination combination ≈
        firstScale * firstScale * B first.val first.val +
          2 * (firstScale * secondScale) * B first.val second.val +
            secondScale * secondScale * B second.val second.val :=
      Q'.eqv_trans _ _ _ hexpand
        (Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr'
            (Q'.mul_add_eqv firstScale
              (firstScale * B first.val first.val)
              (secondScale * B first.val second.val))
            (Q'.mul_add_eqv secondScale
              (firstScale * B first.val second.val)
              (secondScale * B second.val second.val)))
          (YMGap.Continuum.GNSQuotient.GNSData.quad_regroup
            firstScale secondScale
            (B first.val first.val) (B first.val second.val)
            (B second.val second.val)))
    exact Q'.le_trans' _ _ _ hnonnegative (Q'.le_of_eqv hquad)

/-- Sharp finite Cauchy--Schwarz for arbitrary supported polynomials in the
SAME normalized ORIGINAL window state. -/
theorem windowRatio_product_cauchySchwarz {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : headCutoff w ≤ K) (m L n : Nat)
    (left right : RatPoly)
    (hleft : SupportedQuaternionBlocks ((L + 1) * N width) left)
    (hright : SupportedQuaternionBlocks ((L + 1) * N width) right) :
    windowRatio hw0 hw1 K width hK m L n (polyMul left right) *
        windowRatio hw0 hw1 K width hK m L n (polyMul left right) ≤
      windowRatio hw0 hw1 K width hK m L n (polyMul left left) *
        windowRatio hw0 hw1 K width hK m L n (polyMul right right) :=
  (windowPreInnerForm hw0 hw1 K width hK m L n).cauchy_schwarz
    ⟨left, hleft⟩ ⟨right, hright⟩

/-- Square-root-free Young bound for arbitrary supported polynomials in the
SAME normalized ORIGINAL window state. -/
theorem windowRatio_product_two_abs_le_diagonal_sum {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : headCutoff w ≤ K) (m L n : Nat)
    (left right : RatPoly)
    (hleft : SupportedQuaternionBlocks ((L + 1) * N width) left)
    (hright : SupportedQuaternionBlocks ((L + 1) * N width) right) :
    2 * Q'.abs
        (windowRatio hw0 hw1 K width hK m L n (polyMul left right)) ≤
      windowRatio hw0 hw1 K width hK m L n (polyMul left left) +
        windowRatio hw0 hw1 K width hK m L n (polyMul right right) :=
  (windowPreInnerForm hw0 hw1 K width hK m L n).two_mul_abs_inner_le
    ⟨left, hleft⟩ ⟨right, hright⟩

/-- A chronological cross term is bounded by its two diagonal ORIGINAL window
norms.  The right diagonal retains the literal time lift. -/
theorem laggedWindowPair_cauchySchwarz {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : headCutoff w ≤ K) (n L : Nat)
    (left right : RatPoly)
    (hleft : SupportedQuaternionBlocks (N width) left)
    (hright : SupportedQuaternionBlocks (N width) right) :
    laggedWindowPair hw0 hw1 K width hK n L left right *
        laggedWindowPair hw0 hw1 K width hK n L left right ≤
      windowRatio hw0 hw1 K width hK n L n (polyMul left left) *
        windowRatio hw0 hw1 K width hK n L n
          (polyMul (liftBoundary (L * N width) right)
            (liftBoundary (L * N width) right)) := by
  have hsize : (L + 1) * N width = N width + L * N width := by
    rw [Nat.succ_mul]
    omega
  have hleftFull : SupportedQuaternionBlocks ((L + 1) * N width) left :=
    supported_mono_local hleft (by rw [hsize]; omega)
  have hrightFull : SupportedQuaternionBlocks ((L + 1) * N width)
      (liftBoundary (L * N width) right) := by
    rw [hsize]
    exact lift_supported hright (L * N width)
  exact windowRatio_product_cauchySchwarz hw0 hw1 K width hK n L n
    left (liftBoundary (L * N width) right) hleftFull hrightFull

/-- Square-root-free Young bound for a chronological cross term by its two
actual diagonal ORIGINAL window norms. -/
theorem laggedWindowPair_two_abs_le_diagonal_sum {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : headCutoff w ≤ K) (n L : Nat)
    (left right : RatPoly)
    (hleft : SupportedQuaternionBlocks (N width) left)
    (hright : SupportedQuaternionBlocks (N width) right) :
    2 * Q'.abs
        (laggedWindowPair hw0 hw1 K width hK n L left right) ≤
      windowRatio hw0 hw1 K width hK n L n (polyMul left left) +
        windowRatio hw0 hw1 K width hK n L n
          (polyMul (liftBoundary (L * N width) right)
            (liftBoundary (L * N width) right)) := by
  have hsize : (L + 1) * N width = N width + L * N width := by
    rw [Nat.succ_mul]
    omega
  have hleftFull : SupportedQuaternionBlocks ((L + 1) * N width) left :=
    supported_mono_local hleft (by rw [hsize]; omega)
  have hrightFull : SupportedQuaternionBlocks ((L + 1) * N width)
      (liftBoundary (L * N width) right) := by
    rw [hsize]
    exact lift_supported hright (L * N width)
  exact windowRatio_product_two_abs_le_diagonal_sum
    hw0 hw1 K width hK n L n left (liftBoundary (L * N width) right)
    hleftFull hrightFull

private theorem product_add_add_distribution
    (first second third fourth : RatPoly) :
    RatPolyCoeffEqv
      (polyMul (polyAdd first second) (polyAdd third fourth))
      (polyAdd (polyMul first third)
        (polyAdd (polyMul first fourth)
          (polyAdd (polyMul second third) (polyMul second fourth)))) := by
  exact coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.add (.var 0) (.var 1)) (.add (.var 2) (.var 3)))
    (.add (.mul (.var 0) (.var 2))
      (.add (.mul (.var 0) (.var 3))
        (.add (.mul (.var 1) (.var 2)) (.mul (.var 1) (.var 3)))))
    (by decide)
    (fun | 0 => first | 1 => second | 2 => third | _ => fourth)

/-- The actual finite centered deficit pair is the jet--jet pair plus the two
mixed terms and the remainder--remainder term, all in the SAME ORIGINAL
window state. -/
theorem originalBulkDeficitOwn_centeredPair_jet_remainder {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (s : Nat) (hs : 0 < s) (stage n L : Nat) :
    centeredPair hw0 hw1 (headCutoff w + stage) (s * s)
        (Nat.le_add_right _ _) n L
        (sourcePolynomial (originalBulkDeficitExpression s hs))
        (originalBulkDeficitOwnMean hw0 hw1 s hs stage n) ≈
      laggedWindowPair hw0 hw1 (headCutoff w + stage) (s * s)
          (Nat.le_add_right _ _) n L
          (originalBulkVectorQuadraticJetOwnShifted hw0 hw1 s hs stage n)
          (originalBulkVectorQuadraticJetOwnShifted hw0 hw1 s hs stage n) +
        (laggedWindowPair hw0 hw1 (headCutoff w + stage) (s * s)
            (Nat.le_add_right _ _) n L
            (originalBulkVectorQuadraticJetOwnShifted hw0 hw1 s hs stage n)
            (originalBulkScalarSquareRemainderOwnShifted hw0 hw1 s hs stage n) +
          (laggedWindowPair hw0 hw1 (headCutoff w + stage) (s * s)
              (Nat.le_add_right _ _) n L
              (originalBulkScalarSquareRemainderOwnShifted hw0 hw1 s hs stage n)
              (originalBulkVectorQuadraticJetOwnShifted hw0 hw1 s hs stage n) +
            laggedWindowPair hw0 hw1 (headCutoff w + stage) (s * s)
              (Nat.le_add_right _ _) n L
              (originalBulkScalarSquareRemainderOwnShifted hw0 hw1 s hs stage n)
              (originalBulkScalarSquareRemainderOwnShifted hw0 hw1 s hs stage n))) := by
  let blocks := N (s * s)
  let shift := L * blocks
  let deficit := originalBulkDeficitOwnShifted hw0 hw1 s hs stage n
  let jet := originalBulkVectorQuadraticJetOwnShifted hw0 hw1 s hs stage n
  let remainder := originalBulkScalarSquareRemainderOwnShifted hw0 hw1 s hs stage n
  let F := windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
    (Nat.le_add_right (headCutoff w) stage) n L n
  have hbase : HaarCarrierEqv blocks deficit (polyAdd jet remainder) := by
    exact originalBulkDeficitOwnShifted_jet_remainder hw0 hw1 s hs stage n
  have hdeficit : SupportedQuaternionBlocks blocks deficit := by
    exact originalBulkDeficitOwnShifted_supported hw0 hw1 s hs stage n
  have hjet : SupportedQuaternionBlocks blocks jet := by
    exact originalBulkVectorQuadraticJetOwnShifted_supported hw0 hw1 s hs stage n
  have hremainder : SupportedQuaternionBlocks blocks remainder := by
    exact originalBulkScalarSquareRemainderOwnShifted_supported hw0 hw1 s hs stage n
  have hsize : (L + 1) * blocks = blocks + shift := by
    unfold shift
    rw [Nat.succ_mul]
    omega
  have hleft : HaarCarrierEqv ((L + 1) * blocks)
      deficit (polyAdd jet remainder) := by
    rw [hsize]
    exact carrier_extend shift hdeficit (supported_add hjet hremainder) hbase
  have hright : HaarCarrierEqv ((L + 1) * blocks)
      (liftBoundary shift deficit)
      (polyAdd (liftBoundary shift jet) (liftBoundary shift remainder)) := by
    rw [hsize]
    simpa only [lift_add] using lift_carrier shift hbase
  have hproduct : HaarCarrierEqv ((L + 1) * blocks)
      (polyMul deficit (liftBoundary shift deficit))
      (polyAdd (polyMul jet (liftBoundary shift jet))
        (polyAdd (polyMul jet (liftBoundary shift remainder))
          (polyAdd (polyMul remainder (liftBoundary shift jet))
            (polyMul remainder (liftBoundary shift remainder))))) :=
    (HaarCarrierEqv.mul hleft hright).trans
      (RatPolyCoeffEqv.haarCarrier
        (product_add_add_distribution jet remainder
          (liftBoundary shift jet) (liftBoundary shift remainder)))
  have hratio : F (polyMul deficit (liftBoundary shift deficit)) ≈
      F (polyAdd (polyMul jet (liftBoundary shift jet))
        (polyAdd (polyMul jet (liftBoundary shift remainder))
          (polyAdd (polyMul remainder (liftBoundary shift jet))
            (polyMul remainder (liftBoundary shift remainder))))) := by
    exact windowRatio_carrier_congr hw0 hw1 (headCutoff w + stage) (s * s)
      (Nat.le_add_right _ _) n L n hproduct
  have hadd : F (polyAdd (polyMul jet (liftBoundary shift jet))
        (polyAdd (polyMul jet (liftBoundary shift remainder))
          (polyAdd (polyMul remainder (liftBoundary shift jet))
            (polyMul remainder (liftBoundary shift remainder))))) ≈
      F (polyMul jet (liftBoundary shift jet)) +
        (F (polyMul jet (liftBoundary shift remainder)) +
          (F (polyMul remainder (liftBoundary shift jet)) +
            F (polyMul remainder (liftBoundary shift remainder)))) := by
    exact Q'.eqv_trans _ _ _
      (windowRatio_add hw0 hw1 (headCutoff w + stage) (s * s)
        (Nat.le_add_right _ _) n L n _ _)
      (Q'.add_eqv_congr' (Q'.eqv_refl _)
        (Q'.eqv_trans _ _ _
          (windowRatio_add hw0 hw1 (headCutoff w + stage) (s * s)
            (Nat.le_add_right _ _) n L n _ _)
          (Q'.add_eqv_congr' (Q'.eqv_refl _)
            (windowRatio_add hw0 hw1 (headCutoff w + stage) (s * s)
              (Nat.le_add_right _ _) n L n _ _))))
  unfold centeredPair laggedWindowPair
  change F (polyMul deficit (liftBoundary shift deficit)) ≈ _
  exact Q'.eqv_trans _ _ _ hratio hadd

/-- The jet--remainder mixed term has a sharp square bound by its two actual
ORIGINAL diagonal window norms. -/
theorem originalBulkJetRemainderPair_cauchySchwarz {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (s : Nat) (hs : 0 < s) (stage n L : Nat) :
    let jet := originalBulkVectorQuadraticJetOwnShifted hw0 hw1 s hs stage n
    let remainder := originalBulkScalarSquareRemainderOwnShifted hw0 hw1 s hs stage n
    laggedWindowPair hw0 hw1 (headCutoff w + stage) (s * s)
        (Nat.le_add_right _ _) n L jet remainder *
        laggedWindowPair hw0 hw1 (headCutoff w + stage) (s * s)
          (Nat.le_add_right _ _) n L jet remainder ≤
      windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
          (Nat.le_add_right _ _) n L n (polyMul jet jet) *
        windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
          (Nat.le_add_right _ _) n L n
          (polyMul (liftBoundary (L * N (s * s)) remainder)
            (liftBoundary (L * N (s * s)) remainder)) := by
  dsimp only
  exact laggedWindowPair_cauchySchwarz hw0 hw1
    (headCutoff w + stage) (s * s) (Nat.le_add_right _ _) n L _ _
    (originalBulkVectorQuadraticJetOwnShifted_supported hw0 hw1 s hs stage n)
    (originalBulkScalarSquareRemainderOwnShifted_supported hw0 hw1 s hs stage n)

/-- The remainder--jet mixed term has the corresponding sharp square bound. -/
theorem originalBulkRemainderJetPair_cauchySchwarz {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (s : Nat) (hs : 0 < s) (stage n L : Nat) :
    let jet := originalBulkVectorQuadraticJetOwnShifted hw0 hw1 s hs stage n
    let remainder := originalBulkScalarSquareRemainderOwnShifted hw0 hw1 s hs stage n
    laggedWindowPair hw0 hw1 (headCutoff w + stage) (s * s)
        (Nat.le_add_right _ _) n L remainder jet *
        laggedWindowPair hw0 hw1 (headCutoff w + stage) (s * s)
          (Nat.le_add_right _ _) n L remainder jet ≤
      windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
          (Nat.le_add_right _ _) n L n (polyMul remainder remainder) *
        windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
          (Nat.le_add_right _ _) n L n
          (polyMul (liftBoundary (L * N (s * s)) jet)
            (liftBoundary (L * N (s * s)) jet)) := by
  dsimp only
  exact laggedWindowPair_cauchySchwarz hw0 hw1
    (headCutoff w + stage) (s * s) (Nat.le_add_right _ _) n L _ _
    (originalBulkScalarSquareRemainderOwnShifted_supported hw0 hw1 s hs stage n)
    (originalBulkVectorQuadraticJetOwnShifted_supported hw0 hw1 s hs stage n)

/-- The remainder--remainder lagged term is controlled by its two diagonal
remainder norms in the unchanged ORIGINAL window state. -/
theorem originalBulkRemainderPair_cauchySchwarz {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (s : Nat) (hs : 0 < s) (stage n L : Nat) :
    let remainder := originalBulkScalarSquareRemainderOwnShifted hw0 hw1 s hs stage n
    laggedWindowPair hw0 hw1 (headCutoff w + stage) (s * s)
        (Nat.le_add_right _ _) n L remainder remainder *
        laggedWindowPair hw0 hw1 (headCutoff w + stage) (s * s)
          (Nat.le_add_right _ _) n L remainder remainder ≤
      windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
          (Nat.le_add_right _ _) n L n (polyMul remainder remainder) *
        windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
          (Nat.le_add_right _ _) n L n
          (polyMul (liftBoundary (L * N (s * s)) remainder)
            (liftBoundary (L * N (s * s)) remainder)) := by
  dsimp only
  exact laggedWindowPair_cauchySchwarz hw0 hw1
    (headCutoff w + stage) (s * s) (Nat.le_add_right _ _) n L _ _
    (originalBulkScalarSquareRemainderOwnShifted_supported hw0 hw1 s hs stage n)
    (originalBulkScalarSquareRemainderOwnShifted_supported hw0 hw1 s hs stage n)

#print axioms originalBulkDeficitOwnShifted_jet_remainder
#print axioms windowRatio_product_cauchySchwarz
#print axioms windowRatio_product_two_abs_le_diagonal_sum
#print axioms laggedWindowPair_cauchySchwarz
#print axioms laggedWindowPair_two_abs_le_diagonal_sum
#print axioms originalBulkDeficitOwn_centeredPair_jet_remainder
#print axioms originalBulkJetRemainderPair_cauchySchwarz
#print axioms originalBulkRemainderJetPair_cauchySchwarz
#print axioms originalBulkRemainderPair_cauchySchwarz

end YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitCenteredRemainder
