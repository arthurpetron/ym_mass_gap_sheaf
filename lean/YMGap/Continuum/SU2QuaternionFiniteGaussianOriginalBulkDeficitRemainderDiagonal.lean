/-
# Diagonal ORIGINAL bounds for the centered bulk-deficit remainder

For one plaquette, the scalar deficit `1-r` has square cap four on the unit
quaternion carrier.  Summing with the positive bulk coefficients gives the
global scalar-square remainder the explicit cap

  B = 4 * sum(coefficients).

If `0 <= R, mu <= B`, the division-free identity

  B*(R+mu) - (R-mu)^2
    = R*(B-R) + mu*(B-mu) + 2*mu*R

is a sum of certified nonnegative terms.  This yields a diagonal bound for
the actual finite OWN-shifted remainder even when the surrounding lagged
window does not have `mu` as its own mean.  The global deficit decomposition
then replaces both remainder first moments by the corresponding bounded
deficit moments in the SAME ORIGINAL normalized window state.

The result is an explicit finite first-moment reduction.  It does not prove
that those deficit moments are cutoff- or volume-uniformly small, compare the
ORIGINAL jet with the FREE Gaussian law, remove a cutoff, or prove a continuum
Hamiltonian or Clay mass gap.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitCenteredRemainder
import YMGap.Continuum.BF4ExactSlabFixedSpatialWindowLagMeanControl
import YMGap.Continuum.QuaternionHaarPolynomialInterval
import YMGap.Continuum.SU2QuaternionTripleHeadPositiveWindow

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderDiagonal

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation (finitePolySum)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder
  (plaquette_supported plaquette_unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowFunctionalLaws
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowLagMeanControl
  (endpoint_means_eqv middleRatio_interval_bounds)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPairing (windowRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.OSReconstructionProgress
open YMGap.Continuum.QuaternionHaarDensityVariance (shifted shifted_supported)
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm (listQSum)
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction (HaarCarrierEqv)
open YMGap.Continuum.SU2QuaternionHaarCertificateExtension
  (carrier_extend certificate_extend)
open YMGap.Continuum.SU2QuaternionHaarCertificateLift (lift_certificate)
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionTripleHeadPositiveWindow
  (lift_cap_carrier liftUpperCertificate)
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitCentering
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitJetRemainder
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitCenteredRemainder
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] windowRatio

private theorem supported_smul_local {blocks : Nat} {polynomial : RatPoly}
    (hpolynomial : SupportedQuaternionBlocks blocks polynomial) (scale : Q') :
    SupportedQuaternionBlocks blocks (polySmul scale polynomial) := by
  intro term hterm
  obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hterm
  exact hpolynomial source hsource

private theorem supported_neg_local {blocks : Nat} {polynomial : RatPoly}
    (hpolynomial : SupportedQuaternionBlocks blocks polynomial) :
    SupportedQuaternionBlocks blocks (polyNeg polynomial) := by
  intro term hterm
  obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hterm
  exact hpolynomial source hsource

private theorem supported_mono_local {small large : Nat} {polynomial : RatPoly}
    (hpolynomial : SupportedQuaternionBlocks small polynomial) (hsize : small ≤ large) :
    SupportedQuaternionBlocks large polynomial := by
  intro term hterm
  exact Nat.le_trans (hpolynomial term hterm) (Nat.mul_le_mul_left 4 hsize)

private theorem cap_supported_local (blocks : Nat) (value : Q') :
    SupportedQuaternionBlocks blocks (cap value) :=
  supported_smul_local (supported_one blocks) value

/-- Explicit cap for the summed scalar-square remainder. -/
def originalBulkScalarSquareRemainderCap (s : Nat) (hs : 0 < s) : Q' :=
  4 * originalBulkCoefficientSum s hs

/-- The one-plaquette scalar deficit `1-r` has square cap four. -/
def plaquetteScalarDeficit_squareBound
    (width blocks : Nat) (hroom : N width ≤ blocks) (face : Z4Plaq) :
    SquareBound blocks (plaquetteScalarDeficit width face) 4 := by
  unfold plaquetteScalarDeficit
  exact SquareBound.changeCap (by decide : (sumBound 1 1) ≈ 4)
    ((SquareBound.one blocks).add
      (SquareBound.scalar (plaquette_supported width blocks hroom face)
        (plaquette_unit width blocks hroom face)).neg)

/-- Hence one scalar-square remainder lies constructively in `[0,4]`. -/
def plaquetteScalarSquareRemainder_interval
    (width blocks : Nat) (hroom : N width ≤ blocks) (face : Z4Plaq) :
    Interval blocks (plaquetteScalarSquareRemainder width face) 4 := by
  let deficit := plaquetteScalarDeficit width face
  let support := plaquetteScalarDeficit_supported width blocks hroom face
  let bound := plaquetteScalarDeficit_squareBound width blocks hroom face
  refine
    { support := ?_
      nonnegative := by decide
      upper := ?_
      lower := ?_ }
  · unfold plaquetteScalarSquareRemainder
    exact supported_polyMul support support
  · unfold plaquetteScalarSquareRemainder
    simpa only [gap] using bound.certificate
  · unfold plaquetteScalarSquareRemainder
    exact (Certificate.constant blocks 4 (by decide)).add
      (.square (plaquetteScalarDeficit width face) support)

private def weightedRemainderInterval
    (s : Nat) (hs : 0 < s) (face : Z4Plaq)
    (hface : face ∈ bulkSourceFaces s) :
    Interval (N (s * s))
      (polySmul (bulkSourceCoefficient s hs face)
        (plaquetteScalarSquareRemainder (s * s) face))
      (4 * bulkSourceCoefficient s hs face) := by
  exact Interval.changeCap
    (Q'.mul_comm_eqv (bulkSourceCoefficient s hs face) 4)
    (Interval.smul (bulkSourceCoefficient s hs face)
      (Q'.le_of_lt (bulkSourceCoefficient_pos hs hface))
      (plaquetteScalarSquareRemainder_interval
        (s * s) (N (s * s)) (Nat.le_refl _) face))

private def finiteRemainderInterval (s : Nat) (hs : 0 < s) :
    ∀ items : List Z4Plaq,
      (∀ face, face ∈ items → face ∈ bulkSourceFaces s) →
      Interval (N (s * s))
        (finitePolySum
          (fun face => polySmul (bulkSourceCoefficient s hs face)
            (plaquetteScalarSquareRemainder (s * s) face)) items)
        (listQSum (fun face => 4 * bulkSourceCoefficient s hs face) items)
  | [], _ => Interval.zero _
  | face :: items, hitems =>
      (weightedRemainderInterval s hs face (hitems face List.mem_cons_self)).add
        (finiteRemainderInterval s hs items
          (fun next hnext => hitems next (List.mem_cons_of_mem face hnext)))

private theorem listQSum_four {Index : Type} (coefficient : Index → Q')
    (items : List Index) :
    listQSum (fun index => 4 * coefficient index) items ≈
      4 * listQSum coefficient items := by
  induction items with
  | nil => exact Q'.eqv_symm (Q'.mul_zero_eqv 4)
  | cons index items induction =>
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (Q'.eqv_refl _)
          induction)
        (Q'.eqv_symm
          (Q'.mul_add_eqv 4 (coefficient index) (listQSum coefficient items)))

/-- The full summed scalar-square remainder lies in the explicit interval
`[0, 4*sum(coefficients)]` on the ORIGINAL one-slice carrier. -/
def originalBulkScalarSquareRemainder_interval (s : Nat) (hs : 0 < s) :
    Interval (N (s * s)) (originalBulkScalarSquareRemainder s hs)
      (originalBulkScalarSquareRemainderCap s hs) := by
  unfold originalBulkScalarSquareRemainder originalBulkScalarSquareRemainderCap
  exact Interval.changeCap
    (listQSum_four (bulkSourceCoefficient s hs) (bulkSourceFaces s))
    (finiteRemainderInterval s hs (bulkSourceFaces s)
      (fun _ hface => hface))

theorem originalBulkScalarSquareRemainderCap_nonnegative
    (s : Nat) (hs : 0 < s) :
    (0 : Q') ≤ originalBulkScalarSquareRemainderCap s hs :=
  (originalBulkScalarSquareRemainder_interval s hs).nonnegative

/-- The actual finite OWN remainder center lies below the same explicit cap. -/
theorem originalBulkScalarSquareRemainderOwnMean_le_cap {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (s : Nat) (hs : 0 < s) (stage n : Nat) :
    originalBulkScalarSquareRemainderOwnMean hw0 hw1 s hs stage n ≤
      originalBulkScalarSquareRemainderCap s hs := by
  unfold originalBulkScalarSquareRemainderOwnMean
  exact (middleRatio_interval_bounds hw0 hw1 _ _ _ _ _
    (originalBulkScalarSquareRemainder_interval s hs)).2

private def centeredSquareBudgetPolynomial
    (polynomial : RatPoly) (bound center : Q') : RatPoly :=
  polyAdd
    (polyMul (cap bound) (polyAdd polynomial (cap center)))
    (polyNeg
      (polyMul (polyAdd polynomial (polyNeg (cap center)))
        (polyAdd polynomial (polyNeg (cap center)))))

private theorem centeredSquareBudgetPolynomial_supported
    {blocks : Nat} {polynomial : RatPoly}
    (hpolynomial : SupportedQuaternionBlocks blocks polynomial)
    (bound center : Q') :
    SupportedQuaternionBlocks blocks
      (centeredSquareBudgetPolynomial polynomial bound center) := by
  unfold centeredSquareBudgetPolynomial
  have hbound := cap_supported_local blocks bound
  have hcenter := cap_supported_local blocks center
  have hcentered := supported_add hpolynomial (supported_neg_local hcenter)
  exact supported_add
    (supported_polyMul hbound (supported_add hpolynomial hcenter))
    (supported_neg_local (supported_polyMul hcentered hcentered))

private theorem neg_eq_negOne_mul (value : Q') :
    (-value) ≈ (-1 : Q') * value := by
  exact poly_identity_of_normal_eq
    (.neg (.var 0)) (.mul (.const (-1)) (.var 0))
    (by decide) (fun _ => value)

/-- Constructive form of
`B*(R+mu) - (R-mu)^2 = R*(B-R) + mu*(B-mu) + 2*mu*R`. -/
private def centeredSquareBudgetCertificate
    {blocks : Nat} {polynomial : RatPoly} {bound center : Q'}
    (positive : Certificate blocks polynomial)
    (upper : Certificate blocks (polyAdd (cap bound) (polyNeg polynomial)))
    (hcenter0 : (0 : Q') ≤ center) (hcenterBound : center ≤ bound) :
    Certificate blocks (centeredSquareBudgetPolynomial polynomial bound center) := by
  let centerGap := bound + (-center)
  have hcenterGap : (0 : Q') ≤ centerGap :=
    Q'.sub_nonneg_of_le hcenterBound
  have hnegCenter : RatPolyCoeffEqv
      (polyNeg (cap center)) (polySmul (-center) polyOne) :=
    (YMGap.Continuum.QuaternionHaarAngularCarrier.neg_smul (cap center)).trans
      ((RatPolyCoeffEqv.smul_assoc (-1) center polyOne).trans
        (RatPolyCoeffEqv.smul_coefficient
          (Q'.eqv_symm (neg_eq_negOne_mul center)) polyOne))
  have hcenterUpper : Certificate blocks
      (polyAdd (cap bound) (polyNeg (cap center))) := by
    apply Certificate.ofCoeff ?_
      (Certificate.constant blocks centerGap hcenterGap)
    unfold centerGap cap
    exact ((RatPolyCoeffEqv.refl _).add hnegCenter).trans
      (RatPolyCoeffEqv.add_smul_same bound (-center) polyOne)
  have hcenterCertificate := Certificate.constant blocks center hcenter0
  have hcenterProduct := hcenterCertificate.mul positive
  have hraw :=
    (positive.mul upper).add
      ((hcenterCertificate.mul hcenterUpper).add
        (hcenterProduct.add hcenterProduct))
  apply Certificate.ofCoeff ?_ hraw
  unfold centeredSquareBudgetPolynomial
  exact coeffEvalExpr_eqv_of_normalize_eq
    (.add
      (.mul (.var 1) (.add (.var 0) (.var 2)))
      (.neg
        (.mul (.add (.var 0) (.neg (.var 2)))
          (.add (.var 0) (.neg (.var 2))))))
    (.add
      (.mul (.var 0)
        (.add (.var 1) (.neg (.var 0))))
      (.add
        (.mul (.var 2) (.add (.var 1) (.neg (.var 2))))
        (.add (.mul (.var 2) (.var 0))
          (.mul (.var 2) (.var 0)))))
    (by decide)
    (fun | 0 => polynomial | 1 => cap bound | _ => cap center)

/-- Positivity of the unchanged finite window functional converts the
certificate into the diagonal first-moment bound. -/
theorem windowRatio_shifted_square_le_cap_mean {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : headCutoff w ≤ K) (m L n : Nat)
    (polynomial : RatPoly)
    (hpolynomial : SupportedQuaternionBlocks ((L + 1) * N width) polynomial)
    (positive : Certificate ((L + 1) * N width) polynomial)
    (bound center : Q')
    (upper : Certificate ((L + 1) * N width)
      (polyAdd (cap bound) (polyNeg polynomial)))
    (hcenter0 : (0 : Q') ≤ center) (hcenterBound : center ≤ bound) :
    windowRatio hw0 hw1 K width hK m L n
        (polyMul (shifted polynomial center) (shifted polynomial center)) ≤
      bound *
        (windowRatio hw0 hw1 K width hK m L n polynomial + center) := by
  let F := windowRatio hw0 hw1 K width hK m L n
  let square := polyMul (shifted polynomial center) (shifted polynomial center)
  let budget := centeredSquareBudgetPolynomial polynomial bound center
  have hnonnegative : (0 : Q') ≤ F budget := by
    exact windowRatio_certificate_nonnegative hw0 hw1 K width hK m L n
      (centeredSquareBudgetPolynomial_supported hpolynomial bound center)
      (centeredSquareBudgetCertificate positive upper hcenter0 hcenterBound)
  have hcenter : F (polySmul center polyOne) ≈ center := by
    exact Q'.eqv_trans _ _ _
      (windowRatio_smul hw0 hw1 K width hK m L n center polyOne)
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left center _ _
          (windowRatio_one hw0 hw1 K width hK m L n))
        (Q'.mul_one_eqv center))
  have hpositivePart :
      F (polyMul (cap bound) (polyAdd polynomial (cap center))) ≈
        bound * (F polynomial + center) := by
    exact Q'.eqv_trans _ _ _
      (windowRatio_congr hw0 hw1 K width hK m L n
        (cap_mul_left bound (polyAdd polynomial (cap center))))
      (Q'.eqv_trans _ _ _
        (windowRatio_smul hw0 hw1 K width hK m L n bound _)
        (Q'.mul_eqv_congr_left bound _ _
          (Q'.eqv_trans _ _ _
            (windowRatio_add hw0 hw1 K width hK m L n _ _)
            (Q'.add_eqv_congr' (Q'.eqv_refl _) hcenter))))
  have hnegCenter : RatPolyCoeffEqv
      (polyNeg (cap center)) (polySmul (-center) polyOne) :=
    (YMGap.Continuum.QuaternionHaarAngularCarrier.neg_smul (cap center)).trans
      ((RatPolyCoeffEqv.smul_assoc (-1) center polyOne).trans
        (RatPolyCoeffEqv.smul_coefficient
          (Q'.eqv_symm (neg_eq_negOne_mul center)) polyOne))
  have hcentered : RatPolyCoeffEqv
      (polyAdd polynomial (polyNeg (cap center)))
      (shifted polynomial center) := by
    unfold shifted
    exact (RatPolyCoeffEqv.one_smul polynomial).symm.add hnegCenter
  have hnegativePart : F
      (polyNeg
        (polyMul (polyAdd polynomial (polyNeg (cap center)))
          (polyAdd polynomial (polyNeg (cap center))))) ≈ -(F square) := by
    let centered := polyAdd polynomial (polyNeg (cap center))
    have hnegativeSquare : RatPolyCoeffEqv
        (polyNeg (polyMul centered centered)) (polySmul (-1) square) :=
      (YMGap.Continuum.QuaternionHaarAngularCarrier.neg_smul
        (polyMul centered centered)).trans ((hcentered.mul hcentered).smul (-1))
    exact Q'.eqv_trans _ _ _
      (windowRatio_congr hw0 hw1 K width hK m L n hnegativeSquare)
      (Q'.eqv_trans _ _ _
        (windowRatio_smul hw0 hw1 K width hK m L n (-1) square)
        (Q'.eqv_symm (neg_eq_negOne_mul (F square))))
  have hbudget : F budget ≈
      bound * (F polynomial + center) + -(F square) := by
    unfold budget centeredSquareBudgetPolynomial
    exact Q'.eqv_trans _ _ _
      (windowRatio_add hw0 hw1 K width hK m L n _ _)
      (Q'.add_eqv_congr' hpositivePart hnegativePart)
  exact q_le_of_sub_nonneg (le_of_le_eqv hnonnegative hbudget)

/-- At every finite lag, the scalar-square remainder first moment is below
the full bounded deficit first moment in the SAME ORIGINAL window state. -/
theorem originalBulkScalarSquareRemainder_windowRatio_le_deficit {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (s : Nat) (hs : 0 < s) (K : Nat) (hK : headCutoff w ≤ K)
    (n L : Nat) :
    windowRatio hw0 hw1 K (s * s) hK n L n
        (originalBulkScalarSquareRemainder s hs) ≤
      windowRatio hw0 hw1 K (s * s) hK n L n
        (sourcePolynomial (originalBulkDeficitExpression s hs)) := by
  let blocks := N (s * s)
  let shift := L * blocks
  let deficit := sourcePolynomial (originalBulkDeficitExpression s hs)
  let jet := originalBulkVectorQuadraticJet s hs
  let remainder := originalBulkScalarSquareRemainder s hs
  let F := windowRatio hw0 hw1 K (s * s) hK n L n
  have hdeficit : SupportedQuaternionBlocks blocks deficit := by
    simpa only [Nat.zero_add, Nat.one_mul] using
      (source_supported 0 (originalBulkDeficitExpression s hs)
        (originalBulkDeficitExpression_within s hs))
  have hjet : SupportedQuaternionBlocks blocks jet :=
    originalBulkVectorQuadraticJet_supported s hs
  have hremainder : SupportedQuaternionBlocks blocks remainder :=
    originalBulkScalarSquareRemainder_supported s hs
  have hbase : HaarCarrierEqv blocks deficit (polyAdd jet remainder) :=
    (RatPolyCoeffEqv.haarCarrier
      (originalBulkDeficitExpression_jet_source_pin s hs)).trans
      (originalBulkTraceDeficit_decomposition s hs)
  have hsize : (L + 1) * blocks = blocks + shift := by
    unfold shift
    rw [Nat.succ_mul]
    omega
  have hcarrier : HaarCarrierEqv ((L + 1) * blocks)
      deficit (polyAdd jet remainder) := by
    rw [hsize]
    exact carrier_extend shift hdeficit (supported_add hjet hremainder) hbase
  have hsplit : F deficit ≈ F jet + F remainder :=
    Q'.eqv_trans _ _ _
      (windowRatio_carrier_congr hw0 hw1 K (s * s) hK n L n hcarrier)
      (windowRatio_add hw0 hw1 K (s * s) hK n L n jet remainder)
  have hjetFull : SupportedQuaternionBlocks ((L + 1) * blocks) jet :=
    supported_mono_local hjet (by rw [hsize]; omega)
  have hjetCertificate : Certificate ((L + 1) * blocks) jet := by
    rw [hsize]
    exact certificate_extend shift hjet
      (originalBulkVectorQuadraticJet_certificate s hs)
  have hjetNonnegative : (0 : Q') ≤ F jet :=
    windowRatio_certificate_nonnegative hw0 hw1 K (s * s) hK n L n
      hjetFull hjetCertificate
  have hremainderLeSum : F remainder ≤ F jet + F remainder := by
    have h := Q'.add_le_add_right (0 : Q') (F jet) (F remainder)
      hjetNonnegative
    rwa [Q'.zero_add'] at h
  exact Q'.le_trans' _ _ _ hremainderLeSum
    (Q'.le_of_eqv (Q'.eqv_symm hsplit))

private theorem upper_supported_local {blocks : Nat} {polynomial : RatPoly}
    (hpolynomial : SupportedQuaternionBlocks blocks polynomial) (bound : Q') :
    SupportedQuaternionBlocks blocks (polyAdd (cap bound) (polyNeg polynomial)) :=
  supported_add (cap_supported_local blocks bound) (supported_neg_local hpolynomial)

/-- The lower chronological diagonal of the centered remainder is reduced to
first moments of the full bounded deficit. -/
theorem originalBulkScalarSquareRemainder_leftDiagonal_le_deficitMeans {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (s : Nat) (hs : 0 < s) (stage n L : Nat) :
    let remainder := originalBulkScalarSquareRemainder s hs
    let center := originalBulkScalarSquareRemainderOwnMean hw0 hw1 s hs stage n
    let bound := originalBulkScalarSquareRemainderCap s hs
    windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
        (Nat.le_add_right _ _) n L n
        (polyMul (shifted remainder center) (shifted remainder center)) ≤
      bound *
        (windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
            (Nat.le_add_right _ _) n L n
            (sourcePolynomial (originalBulkDeficitExpression s hs)) +
          originalBulkDeficitOwnMean hw0 hw1 s hs stage n) := by
  dsimp only
  let blocks := N (s * s)
  let shift := L * blocks
  let remainder := originalBulkScalarSquareRemainder s hs
  let center := originalBulkScalarSquareRemainderOwnMean hw0 hw1 s hs stage n
  let bound := originalBulkScalarSquareRemainderCap s hs
  let F := windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
    (Nat.le_add_right (headCutoff w) stage) n L n
  let I := originalBulkScalarSquareRemainder_interval s hs
  have hsize : (L + 1) * blocks = blocks + shift := by
    unfold shift
    rw [Nat.succ_mul]
    omega
  have hremainder : SupportedQuaternionBlocks blocks remainder := I.support
  have hremainderFull : SupportedQuaternionBlocks ((L + 1) * blocks) remainder :=
    supported_mono_local hremainder (by rw [hsize]; omega)
  have hpositive : Certificate ((L + 1) * blocks) remainder := by
    rw [hsize]
    exact certificate_extend shift hremainder
      (originalBulkScalarSquareRemainder_certificate s hs)
  have hupper : Certificate ((L + 1) * blocks)
      (polyAdd (cap bound) (polyNeg remainder)) := by
    rw [hsize]
    exact certificate_extend shift (upper_supported_local hremainder bound) I.upper
  have hcenter0 : (0 : Q') ≤ center :=
    originalBulkScalarSquareRemainderOwnMean_nonnegative hw0 hw1 s hs stage n
  have hcenterBound : center ≤ bound :=
    originalBulkScalarSquareRemainderOwnMean_le_cap hw0 hw1 s hs stage n
  have hdiagonal := windowRatio_shifted_square_le_cap_mean hw0 hw1
    (headCutoff w + stage) (s * s) (Nat.le_add_right _ _) n L n
    remainder hremainderFull hpositive bound center hupper hcenter0 hcenterBound
  have hremainderDeficit :=
    originalBulkScalarSquareRemainder_windowRatio_le_deficit hw0 hw1 s hs
      (headCutoff w + stage) (Nat.le_add_right _ _) n L
  have hcenterDeficit :=
    originalBulkScalarSquareRemainderOwnMean_le_deficit hw0 hw1 s hs stage n
  have hsum := Q'.add_le_add hremainderDeficit hcenterDeficit
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ bound hsum
    (originalBulkScalarSquareRemainderCap_nonnegative s hs)
  exact Q'.le_trans' _ _ _ hdiagonal hscaled

/-- The lifted upper chronological diagonal obeys the same first-deficit-
moment bound.  Constant padding is transported by Haar-carrier equality. -/
theorem originalBulkScalarSquareRemainder_rightDiagonal_le_deficitMeans {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (s : Nat) (hs : 0 < s) (stage n L : Nat) :
    let remainder := originalBulkScalarSquareRemainder s hs
    let center := originalBulkScalarSquareRemainderOwnMean hw0 hw1 s hs stage n
    let bound := originalBulkScalarSquareRemainderCap s hs
    let lifted := liftBoundary (L * N (s * s)) (shifted remainder center)
    windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
        (Nat.le_add_right _ _) n L n (polyMul lifted lifted) ≤
      bound *
        (windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
            (Nat.le_add_right _ _) n L n
            (sourcePolynomial (originalBulkDeficitExpression s hs)) +
          originalBulkDeficitOwnMean hw0 hw1 s hs stage n) := by
  dsimp only
  let blocks := N (s * s)
  let shift := L * blocks
  let remainder := originalBulkScalarSquareRemainder s hs
  let center := originalBulkScalarSquareRemainderOwnMean hw0 hw1 s hs stage n
  let bound := originalBulkScalarSquareRemainderCap s hs
  let liftedRemainder := liftBoundary shift remainder
  let F := windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
    (Nat.le_add_right (headCutoff w) stage) n L n
  let I := originalBulkScalarSquareRemainder_interval s hs
  have hsize : (L + 1) * blocks = blocks + shift := by
    unfold shift
    rw [Nat.succ_mul]
    omega
  have hremainder : SupportedQuaternionBlocks blocks remainder := I.support
  have hlifted : SupportedQuaternionBlocks ((L + 1) * blocks) liftedRemainder := by
    rw [hsize]
    exact lift_supported hremainder shift
  have hpositive : Certificate ((L + 1) * blocks) liftedRemainder := by
    rw [hsize]
    exact lift_certificate shift
      (originalBulkScalarSquareRemainder_certificate s hs)
  have hupper : Certificate ((L + 1) * blocks)
      (polyAdd (cap bound) (polyNeg liftedRemainder)) := by
    rw [hsize]
    exact liftUpperCertificate blocks shift I.upper
  have hcenter0 : (0 : Q') ≤ center :=
    originalBulkScalarSquareRemainderOwnMean_nonnegative hw0 hw1 s hs stage n
  have hcenterBound : center ≤ bound :=
    originalBulkScalarSquareRemainderOwnMean_le_cap hw0 hw1 s hs stage n
  have hdiagonal := windowRatio_shifted_square_le_cap_mean hw0 hw1
    (headCutoff w + stage) (s * s) (Nat.le_add_right _ _) n L n
    liftedRemainder hlifted hpositive bound center hupper hcenter0 hcenterBound
  have hshift : HaarCarrierEqv ((L + 1) * blocks)
      (liftBoundary shift (shifted remainder center))
      (shifted liftedRemainder center) := by
    unfold shifted liftedRemainder
    rw [lift_add, lift_smul]
    exact HaarCarrierEqv.add (HaarCarrierEqv.refl _ _)
      (by
        rw [hsize]
        simpa only [cap, lift_smul] using
          (lift_cap_carrier blocks shift (-center)))
  have hsquare : F
      (polyMul (liftBoundary shift (shifted remainder center))
        (liftBoundary shift (shifted remainder center))) ≈
      F (polyMul (shifted liftedRemainder center)
        (shifted liftedRemainder center)) :=
    windowRatio_carrier_congr hw0 hw1 (headCutoff w + stage) (s * s)
      (Nat.le_add_right _ _) n L n (HaarCarrierEqv.mul hshift hshift)
  have hliftedMean := endpoint_means_eqv hw0 hw1
    (headCutoff w + stage) (s * s) (Nat.le_add_right _ _) n L hremainder
  have hremainderDeficit :=
    originalBulkScalarSquareRemainder_windowRatio_le_deficit hw0 hw1 s hs
      (headCutoff w + stage) (Nat.le_add_right _ _) n L
  have hliftedDeficit : F liftedRemainder ≤
      F (sourcePolynomial (originalBulkDeficitExpression s hs)) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm hliftedMean))
      hremainderDeficit
  have hcenterDeficit :=
    originalBulkScalarSquareRemainderOwnMean_le_deficit hw0 hw1 s hs stage n
  have hsum := Q'.add_le_add hliftedDeficit hcenterDeficit
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ bound hsum
    (originalBulkScalarSquareRemainderCap_nonnegative s hs)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hsquare)
    (Q'.le_trans' _ _ _ hdiagonal hscaled)

#print axioms originalBulkScalarSquareRemainder_interval
#print axioms originalBulkScalarSquareRemainderOwnMean_le_cap
#print axioms windowRatio_shifted_square_le_cap_mean
#print axioms originalBulkScalarSquareRemainder_windowRatio_le_deficit
#print axioms originalBulkScalarSquareRemainder_leftDiagonal_le_deficitMeans
#print axioms originalBulkScalarSquareRemainder_rightDiagonal_le_deficitMeans

end YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderDiagonal
