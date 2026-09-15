/-
# Original-partition bounds for auxiliary dressed dual tests

A supported lower-local polynomial need not be a plaquette expression to
test the original finite OS form. Dress it with the FULL original lower
action. Pruning bounds its retained energy by its full interface energy;
ordinary positivity of the actual spatial-Gram background then bounds that
energy by its supplied polynomial cap times the SAME original partition.
Exact rational normalization cancels this partition, without a volume-sized
reciprocal ceiling. All small-nome guards and test caps remain explicit.

The original state input and OS form are unchanged. The tests descend to the
existing finite-cutoff GNS null quotient without choosing representatives.
No cutoff-limit/thermodynamic test construction, transfer preimage, decay,
or physical mass-gap theorem is supplied.
-/

import YMGap.Continuum.BF4ExactSlabPartialInterfaceHaarForm
import YMGap.Continuum.BF4ExactSlabBulkProbePositiveBackground
import YMGap.Continuum.BF4ExactSlabBulkProbeLocalIntervals
import YMGap.Constructive.Sqrt

namespace YMGap.Continuum.BF4ExactSlabDressedDualTestBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentObservableReflection
open YMGap.Continuum.BF4ExactSlabAllExtentTemporalHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentReflectionPositivity
open YMGap.Continuum.BF4ExactSlabAllExtentHeatUnit
open YMGap.Continuum.BF4ExactSlabAllExtentSpatialGramPositivity
open YMGap.Continuum.BF4ExactSlabLocalBilinearChannels
open YMGap.Continuum.BF4ExactSlabLowerHaarFactorization
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactSlabSpatialChannelReflection
open YMGap.Continuum.BF4ExactSlabSpatialHeatCertificate
open YMGap.Continuum.BF4ExactSlabSmallNomeHaarComparison
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquetteReflectionPositivity
open YMGap.Continuum.BF4ExactSlabPlaquetteFiniteGNS
open YMGap.Continuum.BF4ExactSlabPartialInterfaceRetention
open YMGap.Continuum.BF4ExactSlabPartialInterfaceTests
open YMGap.Continuum.ReflectedSquareTreeTestForm
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

local infix:50 " ≈ " => Q'.eqv
local notation "blocks" half => List.length (boundaryCompleteSlabLinks (centralExtent half))
private abbrev L (w : Q') (K half : Nat) := lowerObservable w K half (fun _ => 1)
private abbrev U (w : Q') (K half : Nat) := upperObservable w K half (fun _ => 1)
private abbrev G (w : Q') (K half : Nat) := interfacePolynomial w K half

def background (w : Q') (K half : Nat) : RatPoly :=
  polyMul (L w K half) (polyMul (G w K half) (U w K half))

def partition (w : Q') (K half : Nat) : Q' :=
  rawForm w K (.unit : PlaquetteExpression half) .unit

theorem background_partition (w : Q') (K half : Nat) :
    quaternionHaar (blocks half) (background w K half) ≈ partition w K half := by
  have h := upper_numerator_spatialGram w K (.unit : PlaquetteExpression half)
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (haar_of_coeff
    ((RatPolyCoeffEqv.one_mul (L w K half)).mul
      ((RatPolyCoeffEqv.refl (G w K half)).mul (RatPolyCoeffEqv.one_mul (U w K half))))))
    (Q'.eqv_symm h)

def dress (w : Q') (K half : Nat) (p : RatPoly) : RatPoly := polyMul p (L w K half)

theorem dress_supported (w : Q') (K half : Nat) {p : RatPoly}
    (hp : SupportedQuaternionBlocks (blocks half) p) :
    SupportedQuaternionBlocks (blocks half) (dress w K half p) :=
  supported_polyMul hp (lowerObservable_support w K half _)

theorem dress_lower (w : Q') (K half : Nat) {p : RatPoly} (hp : LowerLocal half p) :
    LowerLocal half (dress w K half p) := hp.mul (lowerObservable_local w K half _)

variable {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hdelta : heatRemainderBound w < 1)

include hw0 hw1 hsmall hdelta

/-- Constructed from all original lower/upper faces and ALL crossing heat modes. -/
def backgroundCertificate (K half : Nat) : Certificate (blocks half) (background w K half) :=
  (Certificate.ofCoeff (lowerObservable_one w K half)
    (faceProductCertificate hw0 hw1 hsmall (Q'.le_of_lt hdelta) K _ _
      (fun _ hi => (mem_centralLowerFaceIds.mp hi).1))).mul
    ((spatialProductCertificate hw0 hw1 hsmall (Q'.le_of_lt hdelta) K half (centralFixedFaceIds half)).mul
      (Certificate.ofCoeff (upperObservable_one w K half)
        (faceProductCertificate hw0 hw1 hsmall (Q'.le_of_lt hdelta) K _ _
          (fun _ hi => (mem_centralUpperFaceIds.mp hi).1))))

omit hw1 hsmall hdelta in
theorem full_energy_haar (K half : Nat) {p p' : RatPoly}
    (hp : SupportedQuaternionBlocks (blocks half) p)
    (hp' : SupportedQuaternionBlocks (blocks half) p') (hl : LowerLocal half p)
    (hr : ReflectionImage (centralExtent half) p p') :
    channelBilinearValue (blocks half) (dress w K half p) (dress w K half p)
      (interfaceExpansion hw0 K half).tree ≈
    quaternionHaar (blocks half) (polyMul (background w K half) (polyMul p' p)) := by
  have hd := dress_supported w K half hp
  have hd' := supported_polyMul hp' (upperObservable_support w K half (fun _ => 1))
  have hG := (interfaceExpansion hw0 K half).polynomialSupported
  have href := PaddedPolynomialCoeffEqv.mul
    (PaddedPolynomialCoeffEqv.mul (hr.mul (lowerObservable_reflection w K half (fun _ => 1)))
      (PaddedPolynomialCoeffEqv.refl (blocks half) (dress w K half p)))
    (PaddedPolynomialCoeffEqv.refl (blocks half) (G w K half))
  have hhaar := href.haar
    (supported_polyMul (supported_polyMul (reflectCorrectedSlabPolynomial_support _ _) hd) hG)
    (supported_polyMul (supported_polyMul hd' hd) hG)
  have hreorder := coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3))) (.var 4))
    (.mul (.mul (.var 3) (.mul (.var 4) (.var 1))) (.mul (.var 0) (.var 2)))
    (by decide) (fun | 0 => p' | 1 => U w K half | 2 => p | 3 => L w K half | _ => G w K half)
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm (expansion_mixed_pairing (interfaceExpansion hw0 K half) _ _ hd hd
      (dress_lower w K half hl) (dress_lower w K half hl)))
    (Q'.eqv_trans _ _ _ hhaar (haar_of_coeff hreorder))

omit hw1 hsmall hdelta in
theorem reference_le_full (K : Nat) (hK : 1 ≤ K) (half : Nat)
    (choice : Nat → PartialChoice) (q : RatPoly) :
    referenceEnergy hw0 K hK half choice q ≤
      channelBilinearValue (blocks half) q q (interfaceExpansion hw0 K half).tree :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv (diagonal_pin (blocks half) q _))
    (Q'.le_trans' _ _ _
      ((interfacePruning hw0 K hK half choice).dressed_value_le
        (interfaceExpansion hw0 K half).weightsNonnegative (blocks half) q)
      (Q'.ge_of_eqv (diagonal_pin (blocks half) q _)))

/-- The cap is independent of volume/cutoff WHEN the supplied test caps are. -/
theorem reference_partition_bound (K : Nat) (hK : 1 ≤ K) (half : Nat)
    (choice : Nat → PartialChoice) {p p' : RatPoly} {a b : Q'}
    (P : Interval (blocks half) p a) (P' : Interval (blocks half) p' b)
    (hl : LowerLocal half p) (hr : ReflectionImage (centralExtent half) p p') :
    referenceEnergy hw0 K hK half choice (dress w K half p) ≤
      (b*a)*partition w K half := by
  exact Q'.le_trans' _ _ _ (reference_le_full hw0 K hK half choice _)
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (full_energy_haar hw0 K half P.support P'.support hl hr))
      (Q'.le_trans' _ _ _ (Q'.le_abs_self _)
        (Q'.le_trans' _ _ _ ((P'.mul P).weighted_haar_bound (backgroundCertificate hw0 hw1 hsmall hdelta K half))
          (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ (background_partition w K half))))))

theorem amplitude_partition_bound (K : Nat) (hK : 1 ≤ K) (half : Nat)
    (choice : Nat → PartialChoice) {p p' : RatPoly} {a b : Q'}
    (P : Interval (blocks half) p a) (P' : Interval (blocks half) p' b)
    (hl : LowerLocal half p) (hr : ReflectionImage (centralExtent half) p p')
    (e : PlaquetteExpression half) :
    let A := testAmplitude hw0 K hK half choice (dress w K half p) e
    A*A ≤ rawForm w K e e * ((b*a)*partition w K half) :=
  Q'.le_trans' _ _ _ (testAmplitude_bound hw0 K hK half choice _ e)
    (Q'.mul_le_mul_of_nonneg_left _ _ _
      (reference_partition_bound hw0 hw1 hsmall hdelta K hK half choice P P' hl hr)
      (rawForm_nonnegative w hw0 K e))

omit hw0 hw1 hsmall hdelta in
private theorem power_pos {c : Q'} (hc : (0 : Q') < c) : ∀ n : Nat, (0 : Q') < c^n
  | 0 => by change (0 : Q') < 1; decide
  | n+1 => Q'.mul_pos hc (power_pos hc n)

theorem partition_positive (K half : Nat) : (0 : Q') < partition w K half :=
  Q'.pos_of_lt_of_le (power_pos (HKPos.one_sub_pos hdelta) _)
    (Q'.le_trans' _ _ _ (fullAction_floor hw0 hw1 hsmall (Q'.le_of_lt hdelta) K half)
      (Q'.ge_of_eqv (rawForm_unit w K half)))

def normalizer (K half : Nat) : Q' :=
  Q'.recipPos (partition w K half) (partition_positive hw0 hw1 hsmall hdelta K half)

theorem normalizer_positive (K half : Nat) : (0 : Q') < normalizer hw0 hw1 hsmall hdelta K half :=
  Q'.recipPos_pos _ _

theorem normalizer_partition (K half : Nat) :
    normalizer hw0 hw1 hsmall hdelta K half * partition w K half ≈ 1 :=
  Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.mul_recipPos_eqv _ _)

/-- Actual original rational OS normalization, not an ordinary L2 norm. -/
theorem normalized_amplitude_bound (K : Nat) (hK : 1 ≤ K) (half : Nat)
    (choice : Nat → PartialChoice) {p p' : RatPoly} {a b : Q'}
    (P : Interval (blocks half) p a) (P' : Interval (blocks half) p' b)
    (hl : LowerLocal half p) (hr : ReflectionImage (centralExtent half) p p')
    (e : PlaquetteExpression half) :
    let r := normalizer hw0 hw1 hsmall hdelta K half
    let A := testAmplitude hw0 K hK half choice (dress w K half p) e
    (r*A)*(r*A) ≤ (b*a)*(r*rawForm w K e e) := by
  dsimp only
  let r := normalizer hw0 hw1 hsmall hdelta K half
  let A := testAmplitude hw0 K hK half choice (dress w K half p) e
  have h := Q'.mul_le_mul_of_nonneg_left _ _ _
    (amplitude_partition_bound hw0 hw1 hsmall hdelta K hK half choice P P' hl hr e)
    (SumOfSquares.q_mul_self_nonneg r)
  have hleft : (r*A)*(r*A) ≈ (r*r)*(A*A) :=
    poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))
      (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (by decide)
      (fun | 0 => r | _ => A)
  have hright : (r*r)*(rawForm w K e e*((b*a)*partition w K half)) ≈
      ((b*a)*(r*rawForm w K e e))*(r*partition w K half) :=
    poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.mul (.var 2) (.var 3))))
      (.mul (.mul (.var 2) (.mul (.var 0) (.var 1))) (.mul (.var 0) (.var 3))) (by decide)
      (fun | 0 => r | 1 => rawForm w K e e | 2 => b*a | _ => partition w K half)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft) (Q'.le_trans' _ _ _ h
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _ hright (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _ (normalizer_partition hw0 hw1 hsmall hdelta K half)) (Q'.mul_one_eqv _)))))

/-- Concrete original spatial-coordinate product test; cap one at every slab
and cutoff. It is used as a dual polynomial, not asserted to be a state. -/
theorem normalized_bulkScalar_bound (K : Nat) (hK : 1 ≤ K) (half : Nat)
    (choice : Nat → PartialChoice) (e : PlaquetteExpression half) :
    let r := normalizer hw0 hw1 hsmall hdelta K half
    let A := testAmplitude hw0 K hK half choice
      (dress w K half (BF4ExactSlabBulkProbeHaarReference.bulkScalar half)) e
    (r*A)*(r*A) ≤ r*rawForm w K e e := by
  have h := normalized_amplitude_bound hw0 hw1 hsmall hdelta K hK half choice
    (BF4ExactSlabBulkProbeLocalIntervals.bulkScalarInterval half)
    (BF4ExactSlabBulkProbeLocalIntervals.upperScalarInterval half)
    (BF4ExactSlabBulkProbeInteractingAmplitudes.bulkScalar_lower half)
    (BF4ExactSlabBulkProbeLocalIntervals.upperScalar_image half) e
  exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.one_mul_eqv _))

/-- Nonzero normalization check on the SAME original unit, with no selection. -/
theorem normalized_unit_pin (K : Nat) (hK : 1 ≤ K) (half : Nat) :
    normalizer hw0 hw1 hsmall hdelta K half *
      testAmplitude hw0 K hK half (fun _ => none) (dress w K half polyOne)
        (.unit : PlaquetteExpression half) ≈ 1 := by
  unfold testAmplitude
  rw [retainedInterface_keepAll]
  have h := Q'.eqv_trans _ _ _ (diagonal_pin (blocks half) (dress w K half polyOne) _)
    (Q'.eqv_symm (BF4ExactSlabPlaquetteRetainedMinor.rawForm_eq_dressedSquareSum w hw0 K half .unit))
  exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ h)
    (normalizer_partition hw0 hw1 hsmall hdelta K half)

omit hw1 hsmall hdelta in
/-- Arbitrary auxiliary polynomials annihilate ORIGINAL finite-cutoff nulls.
This uses retained-tree positivity; no polynomial cap or small-nome guard. -/
theorem amplitude_null (K : Nat) (hK : 1 ≤ K) (half : Nat)
    (choice : Nat → PartialChoice) (q : RatPoly) (e : PlaquetteExpression half)
    (he : rawForm w K e e ≈ 0) : testAmplitude hw0 K hK half choice q e ≈ 0 := by
  let F := treeForm (blocks half) _ (retainedInterface_nonnegative hw0 K hK half choice)
  have hle : F.B (dressedLower w K e) (dressedLower w K e) ≤ 0 :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (diagonal_pin (blocks half) (dressedLower w K e) _))
      (Q'.le_trans' _ _ _ (retainedValue_le_rawForm hw0 K hK choice e) (Q'.le_of_eqv he))
  have hge := F.self_nonneg (dressedLower w K e)
  have hz : F.B (dressedLower w K e) (dressedLower w K e) ≈ 0 := Int.le_antisymm hle hge
  exact F.radical_form_zero (dressedLower w K e) q hz

omit hw1 hsmall hdelta in
theorem amplitude_rad_congr (K : Nat) (hK : 1 ≤ K) (half : Nat)
    (choice : Nat → PartialChoice) (q : RatPoly) {e f : PlaquetteExpression half}
    (h : (finiteGNSData w hw0 K half).rad e f) :
    testAmplitude hw0 K hK half choice q e ≈ testAmplitude hw0 K hK half choice q f := by
  have hz := amplitude_null hw0 K hK half choice q (.add e (.smul (-1) f)) h
  have hsub := Q'.eqv_trans _ _ _ (testAmplitude_add hw0 K hK half choice q e (.smul (-1) f))
    (Q'.add_eqv_congr_left _ _ _ (Q'.eqv_trans _ _ _ (testAmplitude_smul hw0 K hK half choice q (-1) f)
      (Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 _) (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv _)))))
  exact QPoly.q_eqv_of_sub_zero (Q'.eqv_trans _ _ _ (Q'.eqv_symm hsub) hz)

/-- A functional on the EXISTING original finite-cutoff quotient; no larger
observable algebra, second quotient, or selected representative is used. -/
def quotientAmplitude (K : Nat) (hK : 1 ≤ K) (half : Nat)
    (choice : Nat → PartialChoice) (q : RatPoly) :
    (finiteGNSData w hw0 K half).QuotSpace → GNSQuotient.QR :=
  Quotient.lift (fun e => Quotient.mk GNSQuotient.qSetoid
    (normalizer hw0 hw1 hsmall hdelta K half * testAmplitude hw0 K hK half choice q e))
    (fun _ _ h => Quotient.sound (Q'.mul_eqv_congr_left _ _ _
      (amplitude_rad_congr hw0 K hK half choice q h)))

theorem quotientAmplitude_mk (K : Nat) (hK : 1 ≤ K) (half : Nat)
    (choice : Nat → PartialChoice) (q : RatPoly) (e : PlaquetteExpression half) :
    quotientAmplitude hw0 hw1 hsmall hdelta K hK half choice q
      ((finiteGNSData w hw0 K half).qmk e) = Quotient.mk GNSQuotient.qSetoid
        (normalizer hw0 hw1 hsmall hdelta K half * testAmplitude hw0 K hK half choice q e) := rfl

theorem quotient_unit_pin (K : Nat) (hK : 1 ≤ K) (half : Nat) :
    quotientAmplitude hw0 hw1 hsmall hdelta K hK half (fun _ => none) (dress w K half polyOne)
      ((finiteGNSData w hw0 K half).qmk .unit) = Quotient.mk GNSQuotient.qSetoid 1 :=
  Quotient.sound (normalized_unit_pin hw0 hw1 hsmall hdelta K hK half)

end YMGap.Continuum.BF4ExactSlabDressedDualTestBound

#print axioms YMGap.Continuum.BF4ExactSlabDressedDualTestBound.background
#print axioms YMGap.Continuum.BF4ExactSlabDressedDualTestBound.partition
#print axioms YMGap.Continuum.BF4ExactSlabDressedDualTestBound.background_partition
#print axioms YMGap.Continuum.BF4ExactSlabDressedDualTestBound.dress
#print axioms YMGap.Continuum.BF4ExactSlabDressedDualTestBound.dress_supported
#print axioms YMGap.Continuum.BF4ExactSlabDressedDualTestBound.dress_lower
#print axioms YMGap.Continuum.BF4ExactSlabDressedDualTestBound.backgroundCertificate
#print axioms YMGap.Continuum.BF4ExactSlabDressedDualTestBound.full_energy_haar
#print axioms YMGap.Continuum.BF4ExactSlabDressedDualTestBound.reference_le_full
#print axioms YMGap.Continuum.BF4ExactSlabDressedDualTestBound.reference_partition_bound
#print axioms YMGap.Continuum.BF4ExactSlabDressedDualTestBound.amplitude_partition_bound
#print axioms YMGap.Continuum.BF4ExactSlabDressedDualTestBound.partition_positive
#print axioms YMGap.Continuum.BF4ExactSlabDressedDualTestBound.normalizer
#print axioms YMGap.Continuum.BF4ExactSlabDressedDualTestBound.normalizer_positive
#print axioms YMGap.Continuum.BF4ExactSlabDressedDualTestBound.normalizer_partition
#print axioms YMGap.Continuum.BF4ExactSlabDressedDualTestBound.normalized_amplitude_bound
#print axioms YMGap.Continuum.BF4ExactSlabDressedDualTestBound.normalized_bulkScalar_bound
#print axioms YMGap.Continuum.BF4ExactSlabDressedDualTestBound.normalized_unit_pin
#print axioms YMGap.Continuum.BF4ExactSlabDressedDualTestBound.amplitude_null
#print axioms YMGap.Continuum.BF4ExactSlabDressedDualTestBound.amplitude_rad_congr
#print axioms YMGap.Continuum.BF4ExactSlabDressedDualTestBound.quotientAmplitude
#print axioms YMGap.Continuum.BF4ExactSlabDressedDualTestBound.quotientAmplitude_mk
#print axioms YMGap.Continuum.BF4ExactSlabDressedDualTestBound.quotient_unit_pin
