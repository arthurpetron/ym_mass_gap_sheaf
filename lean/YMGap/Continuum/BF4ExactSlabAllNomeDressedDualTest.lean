/-
# Bounded ORIGINAL OS dual tests at every positive subunit nome

Late original heat prefixes supply the complete positive spatial-Gram
background. The existing retained-channel inequality therefore bounds
auxiliary lower-local polynomial tests without small-nome guards. Both
original partition factors are kept through cutoff removal and cancel
against the SAME original reciprocal. The coefficient is just the supplied
test caps; it pays no volume-dependent partition ceiling.

The concrete bulk scalar test has coefficient one and descends to the
EXISTING cutoff-removed finite-volume OS quotient. It is not asserted to be
an original state. Thermodynamic compatibility at varying nome, a separating
test family, centered decay, physical time/scale and Clay remain open.
-/

import YMGap.Continuum.BF4ExactSlabAllNomeSpatialHeatCertificate
import YMGap.Continuum.BF4ExactSlabDressedDualTestCutoffLimit

namespace YMGap.Continuum.BF4ExactSlabAllNomeDressedDualTest

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentHeatUnit
open YMGap.Continuum.BF4ExactSlabAllExtentSpatialGramPositivity
open YMGap.Continuum.BF4ExactSlabAllExtentTemporalImages
open YMGap.Continuum.BF4ExactSlabLowerHaarFactorization
open YMGap.Continuum.BF4ExactSlabSpatialChannelReflection
open YMGap.Continuum.BF4ExactSlabPartialInterfaceTests
open YMGap.Continuum.BF4ExactSlabPartialInterfaceRetention
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquetteReflectionPositivity
open YMGap.Continuum.BF4ExactSlabPlaquetteFiniteGNS
open YMGap.Continuum.BF4ExactSlabPlaquetteReflectedForm
open YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit
open YMGap.Continuum.BF4ExactSlabPolynomialExpectation (reciprocal_nonnegative)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabDressedDualTestBound
open YMGap.Continuum.BF4ExactSlabDressedDualTestCutoffLimit
open YMGap.Continuum.BF4ExactSlabBulkProbeHaarReference (bulkScalar)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal
  (convergesTo_mul_general)

local infix:50 " ≈ " => Q'.eqv
local notation "blocks" half => List.length (boundaryCompleteSlabLinks (centralExtent half))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))

/-- The SAME full background, not just the bulk-probe spectator background. -/
def backgroundCertificate (K half : Nat) (hK : headCutoff w ≤ K) :
    Certificate (blocks half) (background w K half) :=
  (Certificate.ofCoeff (lowerObservable_one w K half)
    (headProduct_certificate hw0 hw1 K _ hK _ (fun _ hi => (mem_centralLowerFaceIds.mp hi).1))).mul
    ((BF4ExactSlabAllNomeSpatialHeatCertificate.interfaceCertificate hw0 hw1 K half hK).mul
      (Certificate.ofCoeff (upperObservable_one w K half)
        (headProduct_certificate hw0 hw1 K _ hK _ (fun _ hi => (mem_centralUpperFaceIds.mp hi).1))))

include hw1 in
theorem reference_partition_bound (K : Nat) (hK : 1 ≤ K) (half : Nat)
    (hlate : headCutoff w ≤ K) (choice : Nat → PartialChoice) {p p' : RatPoly} {a b : Q'}
    (P : Interval (blocks half) p a) (P' : Interval (blocks half) p' b)
    (hl : LowerLocal half p) (hr : ReflectionImage (centralExtent half) p p') :
    referenceEnergy (Q'.le_of_lt hw0) K hK half choice (dress w K half p) ≤
      (b*a)*partition w K half :=
  Q'.le_trans' _ _ _ (reference_le_full (Q'.le_of_lt hw0) K hK half choice _)
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (full_energy_haar (Q'.le_of_lt hw0) K half P.support P'.support hl hr))
      (Q'.le_trans' _ _ _ (Q'.le_abs_self _)
        (Q'.le_trans' _ _ _ ((P'.mul P).weighted_haar_bound (backgroundCertificate hw0 hw1 K half hlate))
          (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ (background_partition w K half))))))

include hw1 in
theorem amplitude_partition_bound (K : Nat) (hK : 1 ≤ K) (half : Nat)
    (hlate : headCutoff w ≤ K) (choice : Nat → PartialChoice) {p p' : RatPoly} {a b : Q'}
    (P : Interval (blocks half) p a) (P' : Interval (blocks half) p' b)
    (hl : LowerLocal half p) (hr : ReflectionImage (centralExtent half) p p')
    (e : PlaquetteExpression half) :
    let A := testAmplitude (Q'.le_of_lt hw0) K hK half choice (dress w K half p) e
    A*A ≤ rawForm w K e e * ((b*a)*partition w K half) :=
  Q'.le_trans' _ _ _ (testAmplitude_bound (Q'.le_of_lt hw0) K hK half choice _ e)
    (Q'.mul_le_mul_of_nonneg_left _ _ _
      (reference_partition_bound hw0 hw1 K hK half hlate choice P P' hl hr)
      (rawForm_nonnegative w (Q'.le_of_lt hw0) K e))

variable (w) {half : Nat}

private theorem numerator_product_converges (p q : RatPoly) :
    CReal.ConvergesTo (fun K => CReal.ofQ'
      (numerator w (blocks half) (centralExtent half) (slabPhysicalFaceEdges (centralExtent half)) p K *
       numerator w (blocks half) (centralExtent half) (slabPhysicalFaceEdges (centralExtent half)) q K))
      (CReal.mul
        (numeratorLimit w hw0 hw1 (blocks half) (centralExtent half) (slabPhysicalFaceEdges (centralExtent half)) p)
        (numeratorLimit w hw0 hw1 (blocks half) (centralExtent half) (slabPhysicalFaceEdges (centralExtent half)) q)) :=
  fun epsilon he => (convergesTo_mul_general
    (numerator_converges w hw0 hw1 (blocks half) (centralExtent half) (slabPhysicalFaceEdges (centralExtent half)) p)
    (numerator_converges w hw0 hw1 (blocks half) (centralExtent half) (slabPhysicalFaceEdges (centralExtent half)) q)) epsilon he

/-- The cutoff-dependent dressed test stays inside the finite estimate;
only the fixed original insertion is passed through the cutoff limit. -/
theorem rawTestLimit_bound {p p' : RatPoly} {a b : Q'}
    (P : Interval (blocks half) p a) (P' : Interval (blocks half) p' b)
    (hl : LowerLocal half p) (hr : ReflectionImage (centralExtent half) p p')
    (htp : TemporalImage half p p) (e : PlaquetteExpression half) :
    CReal.leEv (CReal.mul (rawTestLimit w hw0 hw1 p e) (rawTestLimit w hw0 hw1 p e))
      (CReal.mul (CReal.ofQ' (b*a))
        (CReal.mul (rawLimit w hw0 hw1 e e) (rawLimit w hw0 hw1 (.unit : PlaquetteExpression half) .unit))) := by
  have hp := numerator_product_converges w hw0 hw1 (half := half)
    (polyMul (upper e) (lower e))
    (polyMul (upper (.unit : PlaquetteExpression half)) (lower (.unit : PlaquetteExpression half)))
  have hc : CReal.ConvergesTo
      (fun K => CReal.ofQ' ((b*a)*(rawForm w K e e * rawForm w K (.unit : PlaquetteExpression half) .unit)))
      (CReal.mul (CReal.ofQ' (b*a))
        (CReal.mul (rawLimit w hw0 hw1 e e) (rawLimit w hw0 hw1 (.unit : PlaquetteExpression half) .unit))) :=
    fun epsilon he => (CReal.convergesTo_const_mul (CReal.ofQ' (b*a)) hp) epsilon he
  apply CReal.leEv_of_ofQ'_limit_le
    (numerator_product_converges w hw0 hw1 (half := half) (polyMul (upper e) p) (polyMul (upper e) p)) hc
  intro epsilon he
  refine ⟨max 1 (headCutoff w), fun K hK => ?_⟩
  have hone := Nat.le_trans (Nat.le_max_left _ _) hK
  have hlate := Nat.le_trans (Nat.le_max_right _ _) hK
  have ha := full_amplitude_original w (Q'.le_of_lt hw0) K hone half p P.support hl htp e
  have hsq := Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha) (Q'.mul_eqv_congr_left _ _ _ ha)
  have h := amplitude_partition_bound hw0 hw1 K hone half hlate (fun _ => none) P P' hl hr e
  have horder : rawForm w K e e * ((b*a)*partition w K half) ≈
      (b*a)*(rawForm w K e e * partition w K half) :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv _ _)) (Q'.mul_assoc_eqv _ _ _))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hsq)
    (Q'.le_trans' _ _ _ h (Q'.le_trans' _ _ _ (Q'.le_of_eqv horder)
      (Q'.add_le_self_of_nonneg _ epsilon (Q'.le_of_lt he))))

private theorem normalization_square (A L : CReal) :
    CReal.Equiv (CReal.mul (CReal.mul A L) (CReal.mul A L))
      (CReal.mul (CReal.mul L L) (CReal.mul A A)) := by
  apply SumOfSquares.Equiv_of_approx_eqv
  intro n
  change Q'.eqv ((A.approx n * L.approx n) * (A.approx n * L.approx n))
    ((L.approx n * L.approx n) * (A.approx n * A.approx n))
  show _ * (_ : Int) = _ * (_ : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast]
  ac_rfl

private theorem normalization_product (B Z L : CReal) (c : Q') :
    CReal.Equiv (CReal.mul (CReal.mul L L) (CReal.mul (CReal.ofQ' c) (CReal.mul B Z)))
      (CReal.mul (CReal.ofQ' c) (CReal.mul (CReal.mul B L) (CReal.mul Z L))) := by
  apply SumOfSquares.Equiv_of_approx_eqv
  intro n
  change Q'.eqv ((L.approx n * L.approx n) * (c * (B.approx n * Z.approx n)))
    (c * ((B.approx n * L.approx n) * (Z.approx n * L.approx n)))
  show _ * (_ : Int) = _ * (_ : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast]
  ac_rfl

/-- Same original OS form and testLimit; no coupling guard or reciprocal
ceiling remains in the coefficient b*a. The test need not be a state. -/
theorem testLimit_bound {p p' : RatPoly} {a b : Q'}
    (P : Interval (blocks half) p a) (P' : Interval (blocks half) p' b)
    (hl : LowerLocal half p) (hr : ReflectionImage (centralExtent half) p p')
    (htp : TemporalImage half p p) (e : PlaquetteExpression half) :
    CReal.leEv (CReal.mul (testLimit w hw0 hw1 p e) (testLimit w hw0 hw1 p e))
      (CReal.mul (CReal.ofQ' (b*a)) (form w hw0 hw1 e e)) := by
  let L := BF4ExactSlabOriginalActionReciprocal.actionReciprocal w hw0 hw1 half
  have hL := reciprocal_nonnegative w hw0 hw1 half
  have h := CReal.leEv_mul_nonneg_left (CReal.mul_nonneg hL hL)
    (rawTestLimit_bound w hw0 hw1 P P' hl hr htp e)
  have hz := (normalization_product (rawLimit w hw0 hw1 e e)
    (rawLimit w hw0 hw1 (.unit : PlaquetteExpression half) .unit) L (b*a)).trans
      ((Pivot2.mul_congr_right (Pivot2.mul_congr_right (form_unit w hw0 hw1 half))).trans
        (Pivot2.mul_congr_right (CRealAlg.cmul_cone (form w hw0 hw1 e e))))
  exact CReal.leEv_trans (CReal.leEv_of_equiv (normalization_square (rawTestLimit w hw0 hw1 p e) L))
    (CReal.leEv_trans h (CReal.leEv_of_equiv hz))

/-- Nonzero normalization sanity check for the family, not a claim that
the particular bulk scalar test is nonzero or that the family separates. -/
theorem unit_test_pin :
    CReal.Equiv (testLimit w hw0 hw1 polyOne (.unit : PlaquetteExpression half)) CReal.cone :=
  (BF4ExactSlabPolynomialExpectation.expectation_congr w hw0 hw1 half
    (BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics.RatPolyCoeffEqv.one_mul polyOne)).trans
    (BF4ExactSlabPolynomialExpectation.expectation_one w hw0 hw1 half)

/-- Concrete cap-one test; all locality/reflection/temporal pins are proved. -/
theorem bulkScalar_limit_bound (e : PlaquetteExpression half) :
    CReal.leEv
      (CReal.mul (testLimit w hw0 hw1 (bulkScalar half) e) (testLimit w hw0 hw1 (bulkScalar half) e))
      (form w hw0 hw1 e e) := by
  have h := testLimit_bound w hw0 hw1
    (BF4ExactSlabBulkProbeLocalIntervals.bulkScalarInterval half)
    (BF4ExactSlabBulkProbeLocalIntervals.upperScalarInterval half)
    (BF4ExactSlabBulkProbeInteractingAmplitudes.bulkScalar_lower half)
    (BF4ExactSlabBulkProbeLocalIntervals.upperScalar_image half)
    (bulkScalar_temporal_fixed half) e
  exact CReal.leEv_trans h (CReal.leEv_of_equiv
    (SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.one_mul_eqv _)))

private theorem zero_of_square_le_zero (A : CReal)
    (h : CReal.leEv (CReal.mul A A) (CReal.ofQ' 0)) : CReal.Equiv A (CReal.ofQ' 0) := by
  intro epsilon he
  obtain ⟨N, hN⟩ := h (epsilon*epsilon) (Q'.mul_pos he he)
  refine ⟨N, fun n hn => ?_⟩
  have hs : A.approx n * A.approx n ≤ epsilon*epsilon := by
    have hs := hN n hn
    change A.approx n * A.approx n ≤ 0 + epsilon*epsilon at hs
    rwa [Q'.zero_add'] at hs
  have ha := Q'.abs_le_two_sided (Q'.abs_le_of_sq_le_sq he hs)
  constructor
  · exact Q'.le_trans' _ _ _ ha.1 (Q'.ge_of_eqv (Q'.eqv_of_eq (Q'.zero_add' _)))
  · apply Q'.le_add_of_sub_le
    change 0 + -A.approx n ≤ epsilon
    rw [Q'.zero_add']
    exact ha.2

theorem bulkScalar_limit_null (e : PlaquetteExpression half)
    (he : CReal.Equiv (form w hw0 hw1 e e) (CReal.ofQ' 0)) :
    CReal.Equiv (testLimit w hw0 hw1 (bulkScalar half) e) (CReal.ofQ' 0) :=
  zero_of_square_le_zero _ (CReal.leEv_trans (bulkScalar_limit_bound w hw0 hw1 e)
    (CReal.leEv_of_equiv he))

theorem bulkScalar_null_congr {e f : PlaquetteExpression half}
    (h : BF4ExactSlabPlaquetteNullQuotient.Null w hw0 hw1 e f) :
    CReal.Equiv (testLimit w hw0 hw1 (bulkScalar half) e) (testLimit w hw0 hw1 (bulkScalar half) f) :=
  CReal.Equiv_of_sub_eqv_zero ((testLimit_sub w hw0 hw1 (bulkScalar half) e f).symm.trans
    (bulkScalar_limit_null w hw0 hw1 _ (Quotient.exact h)))

/-- No representative selection and no replacement observable quotient. -/
def bulkScalarQuotientTest : BF4ExactSlabPlaquetteNullQuotient.Carrier w hw0 hw1 half → CReal.RC :=
  Quotient.lift (fun e => Quotient.mk CReal.crealSetoid (testLimit w hw0 hw1 (bulkScalar half) e))
    (fun _ _ h => Quotient.sound (bulkScalar_null_congr w hw0 hw1 h))

theorem bulkScalarQuotientTest_embed (e : PlaquetteExpression half) :
    bulkScalarQuotientTest w hw0 hw1 (BF4ExactSlabPlaquetteNullQuotient.embed w hw0 hw1 e) =
      Quotient.mk CReal.crealSetoid (testLimit w hw0 hw1 (bulkScalar half) e) := rfl

end YMGap.Continuum.BF4ExactSlabAllNomeDressedDualTest

#print axioms YMGap.Continuum.BF4ExactSlabAllNomeDressedDualTest.backgroundCertificate
#print axioms YMGap.Continuum.BF4ExactSlabAllNomeDressedDualTest.reference_partition_bound
#print axioms YMGap.Continuum.BF4ExactSlabAllNomeDressedDualTest.amplitude_partition_bound
#print axioms YMGap.Continuum.BF4ExactSlabAllNomeDressedDualTest.rawTestLimit_bound
#print axioms YMGap.Continuum.BF4ExactSlabAllNomeDressedDualTest.testLimit_bound
#print axioms YMGap.Continuum.BF4ExactSlabAllNomeDressedDualTest.unit_test_pin
#print axioms YMGap.Continuum.BF4ExactSlabAllNomeDressedDualTest.bulkScalar_limit_bound
#print axioms YMGap.Continuum.BF4ExactSlabAllNomeDressedDualTest.bulkScalar_limit_null
#print axioms YMGap.Continuum.BF4ExactSlabAllNomeDressedDualTest.bulkScalar_null_congr
#print axioms YMGap.Continuum.BF4ExactSlabAllNomeDressedDualTest.bulkScalarQuotientTest
#print axioms YMGap.Continuum.BF4ExactSlabAllNomeDressedDualTest.bulkScalarQuotientTest_embed
