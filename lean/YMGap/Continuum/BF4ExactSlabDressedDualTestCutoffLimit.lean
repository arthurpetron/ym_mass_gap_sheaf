/-
# Full-channel dual tests use the ORIGINAL cutoff limit

The actual temporal ledger fixes a lower-link scalar test. With an original
upper plaquette expression, the complete dressed test amplitude is therefore
the original full-action numerator of a FIXED polynomial insertion. Every
crossing channel and every bulk action factor remains. The pre-existing
numerator Cauchy modulus removes all heat cutoffs together; no new limiting
law or original-state realization of the auxiliary test is assumed.

This is fixed-volume cutoff control, not thermodynamic compatibility,
an actual time-transfer comparison, or a continuum/physical gap theorem.
-/

import YMGap.Continuum.BF4ExactSlabDressedDualTestBound
import YMGap.Continuum.BF4ExactSlabPlaquetteReflectedForm
import YMGap.Continuum.BF4ExactSlabPlaquetteNullQuotient

namespace YMGap.Continuum.BF4ExactSlabDressedDualTestCutoffLimit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentTemporalImages
open YMGap.Continuum.BF4ExactSlabAllExtentTemporalHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentSpatialGramPositivity
open YMGap.Continuum.BF4ExactSlabAllExtentObservableReflection
open YMGap.Continuum.BF4ExactSlabAllExtentHeatUnit
open YMGap.Continuum.BF4ExactSlabTemporalGaugeLedger
open YMGap.Continuum.BF4ExactSlabTemporalGaugeFaces
open YMGap.Continuum.BF4ExactSlabTemporalGaugeFixedCoordinates
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquetteReflectionPositivity
open YMGap.Continuum.BF4ExactSlabPlaquetteFiniteGNS
open YMGap.Continuum.BF4ExactSlabPlaquetteReflectedForm
open YMGap.Continuum.BF4ExactSlabPartialInterfaceTests
open YMGap.Continuum.BF4ExactSlabPartialInterfaceRetention
open YMGap.Continuum.BF4ExactSlabPartialInterfaceHaarForm
open YMGap.Continuum.BF4ExactSlabDressedDualTestBound
open YMGap.Continuum.BF4ExactSlabLowerHaarFactorization
open YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit
open YMGap.Continuum.BF4ExactSlabPolynomialExpectation
open YMGap.Continuum.BF4ExactSlabBulkProbeHaarReference
open YMGap.Continuum.BF4ExactSlabBulkProbeInterface
open YMGap.Continuum.BF4ExactSlabPlaquettePathGram
open YMGap.Continuum.BF4ExactSlabReflectedSquareGluing
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry

local infix:50 " ≈ " => Q'.eqv
local notation "blocks" half => List.length (boundaryCompleteSlabLinks (centralExtent half))

/-- The whole ledger fixes each actual non-upper scalar coordinate. -/
theorem scalar_temporal_fixed {half : Nat} {link : Z4Link}
    (hl : link ∈ boundaryCompleteSlabLinks (centralExtent half))
    (hn : linkHalfSide half link ≠ .upper) :
    TemporalImage half (correctedSlabLinkPolynomial (centralExtent half) link).scalar
      (correctedSlabLinkPolynomial (centralExtent half) link).scalar :=
  PaddedPolynomialCoeffEqv.of_prefix (temporalLedger_nonupper_link hl hn).scalar

theorem scalarProduct_temporal_fixed (half : Nat) : (links : List Z4Link) →
    (∀ link, link ∈ links → link ∈ boundaryCompleteSlabLinks (centralExtent half)) →
    (∀ link, link ∈ links → linkHalfSide half link ≠ .upper) →
    TemporalImage half (scalarProduct (centralExtent half) links) (scalarProduct (centralExtent half) links)
  | [], _, _ => TemporalImage.one half
  | link :: links, hp, hn =>
      (scalar_temporal_fixed (hp link List.mem_cons_self) (hn link List.mem_cons_self)).mul
        (scalarProduct_temporal_fixed half links
          (fun l hl => hp l (List.mem_cons_of_mem link hl))
          (fun l hl => hn l (List.mem_cons_of_mem link hl)))

theorem bulkScalar_temporal_fixed (half : Nat) :
    TemporalImage half (bulkScalar half) (bulkScalar half) := by
  rw [bulkScalar_coordinate_pin]
  have h := applySteps_fold_image (temporalTailBlocks_pos (centralExtent half))
    (temporalTranslationSteps (centralExtent half) half)
    (fun id => BF4ExactSlabFundamentalRetainedChannels.faceCoordinatePolynomial half id false false)
    (fun id => BF4ExactSlabFundamentalRetainedChannels.faceCoordinatePolynomial half id false false)
    (crossingIds half)
  rw [temporalTotalBlocks_eq] at h
  apply h
  intro id hi
  have hf := crossingIds_fixed hi
  exact scalar_temporal_fixed
    (faceLinkA_physical (slabPlaquetteAt_mem (mem_centralFixedFaceIds.mp hf).1))
    (by rw [(crossing_face_path_sides (mem_centralFixedFaceIds.mp hf).2).1]; decide)

private theorem haar_temporal {half : Nat} {p q : RatPoly} (h : TemporalImage half p q)
    (hp : SupportedQuaternionBlocks (blocks half) p) (hq : SupportedQuaternionBlocks (blocks half) q) :
    quaternionHaar (blocks half) p ≈ quaternionHaar (blocks half) q :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (applyTemporalTranslationLedger_haar _ _ _ hp))
    (h.haar (applyTemporalTranslationLedger_supported _ _ _ hp) hq)

/-- A test is an insertion, not asserted to belong to the state algebra.
The temporal image is an explicit algebraic pin, instantiated above. -/
theorem original_numerator_spatialGram (w : Q') (K half : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (blocks half) p) (htp : TemporalImage half p p)
    (e : PlaquetteExpression half) :
    numerator w (blocks half) (centralExtent half) (slabPhysicalFaceEdges (centralExtent half))
      (polyMul (upper e) p) K ≈
    quaternionHaar (blocks half)
      (polyMul (dress w K half p) (polyMul (interfacePolynomial w K half) (dressedUpper w K e))) := by
  let L := lowerObservable w K half (fun _ => 1)
  let U := upperObservable w K half (fun _ => 1)
  let I := interfaceHeatProduct w K half
  let base := polyMul L (polyMul I U)
  let target := temporalObservableIntegrand w K half (fun _ => 1) (fun _ => 1)
  have hb : SupportedQuaternionBlocks (blocks half) base :=
    supported_polyMul (lowerObservable_support w K half _)
      (supported_polyMul (interfaceHeatProduct_support w K half) (upperObservable_support w K half _))
  have hi : TemporalImage half base target := observableProduct_image w K half _ _
  have ht := haar_temporal (((upper_image e).mul htp).mul hi)
    (supported_polyMul (supported_polyMul (upper_supported e) hp) hb)
    (supported_polyMul (supported_polyMul (temporalUpper_supported e) hp)
      (temporalObservableIntegrand_support w K half _ _))
  have hpp : HaarCarrierEqv (blocks half) p p := fun _ => Q'.eqv_refl _
  have hg := HaarCarrierEqv.mul (HaarCarrierEqv.mul (temporalUpper_original e) hpp)
    (HaarCarrierEqv.mul (temporalLower_haar_original w K half (fun _ => 1))
      (HaarCarrierEqv.mul (temporalInterface_haar_gram w K half)
        (temporalUpper_haar_original w K half (fun _ => 1))))
  have hr := coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.mul (.var 3) (.var 4))))
    (.mul (.mul (.var 1) (.var 2)) (.mul (.var 3) (.mul (.var 0) (.var 4))))
    (by decide) (fun | 0 => upper e | 1 => p | 2 => L | 3 => interfacePolynomial w K half | _ => U)
  exact Q'.eqv_trans _ _ _ (haar_of_coeff_eqv _ ((unit_product w K (half := half)).symm.mul_left _))
    (Q'.eqv_trans _ _ _ ht (Q'.eqv_trans _ _ _ (QuaternionHaarSquareCertificate.haar_of_carrier hg)
      (haar_of_coeff_eqv _ hr)))

/-- ALL crossing modes, SAME action cutoff, fixed original insertion. -/
theorem full_amplitude_original (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) (hK : 1 ≤ K)
    (half : Nat) (p : RatPoly) (hp : SupportedQuaternionBlocks (blocks half) p)
    (hl : LowerLocal half p) (htp : TemporalImage half p p) (e : PlaquetteExpression half) :
    testAmplitude hw K hK half (fun _ => none) (dress w K half p) e ≈
      numerator w (blocks half) (centralExtent half) (slabPhysicalFaceEdges (centralExtent half))
        (polyMul (upper e) p) K := by
  have ht := testAmplitude_haar hw K hK half (fun _ => none) (dress w K half p)
    (dress_supported w K half hp) (dress_lower w K half hl) e
  have hg := (interfaceExpansion hw K half).polynomialSupported
  have hd := dress_supported w K half hp
  have hr := (PaddedPolynomialCoeffEqv.mul (PaddedPolynomialCoeffEqv.mul (dressed_reflection w K e)
    (PaddedPolynomialCoeffEqv.refl (blocks half) (dress w K half p)))
    (PaddedPolynomialCoeffEqv.refl (blocks half) (interfacePolynomial w K half))).haar
      (supported_polyMul (supported_polyMul
        (BF4ExactSlabVacuumReflection.reflectCorrectedSlabPolynomial_support _ _) hd) hg)
      (supported_polyMul (supported_polyMul (dressedUpper_supported w K e) hd) hg)
  have hreorder := coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.mul (.var 1) (.mul (.var 2) (.var 0)))
    (by decide) (fun | 0 => dressedUpper w K e | 1 => dress w K half p | _ => interfacePolynomial w K half)
  exact Q'.eqv_trans _ _ _ ht (Q'.eqv_trans _ _ _ hr
    (Q'.eqv_trans _ _ _ (haar_of_coeff_eqv _ hreorder)
      (Q'.eqv_symm (original_numerator_spatialGram w K half p hp htp e))))

variable (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {half : Nat}

/-- Reuse the actual original full-action CReal, not a new selected-channel limit. -/
def rawTestLimit (p : RatPoly) (e : PlaquetteExpression half) : CReal :=
  numeratorLimit w hw0 hw1 (blocks half) (centralExtent half)
    (slabPhysicalFaceEdges (centralExtent half)) (polyMul (upper e) p)

def testCutoff (p : RatPoly) (e : PlaquetteExpression half) (epsilon : Q') : Nat :=
  max 1 (numeratorCutoff w (centralExtent half) (slabPhysicalFaceEdges (centralExtent half))
    (polyMul (upper e) p) epsilon)

/-- Both all-later heat cutoff and numerical precision thresholds are data. -/
theorem full_amplitude_approx_close (p : RatPoly) (hp : SupportedQuaternionBlocks (blocks half) p)
    (hl : LowerLocal half p) (htp : TemporalImage half p p) (e : PlaquetteExpression half)
    (epsilon : Q') (he : (0 : Q') < epsilon) (K n : Nat)
    (hK : testCutoff w p e epsilon ≤ K) (hn : testCutoff w p e epsilon ≤ n) :
    let A := testAmplitude (Q'.le_of_lt hw0) K (Nat.le_trans (Nat.le_max_left _ _) hK)
      half (fun _ => none) (dress w K half p) e
    A ≤ (rawTestLimit w hw0 hw1 p e).approx n + epsilon ∧
    (rawTestLimit w hw0 hw1 p e).approx n ≤ A + epsilon := by
  have h := numerator_approx_close w hw0 hw1 (blocks half) (centralExtent half)
    (slabPhysicalFaceEdges (centralExtent half)) (polyMul (upper e) p) epsilon he K n
    (Nat.le_trans (Nat.le_max_right _ _) hK) (Nat.le_trans (Nat.le_max_right _ _) hn)
  have ha := full_amplitude_original w (Q'.le_of_lt hw0) K
    (Nat.le_trans (Nat.le_max_left _ _) hK) half p hp hl htp e
  exact ⟨Q'.le_trans' _ _ _ (Q'.le_of_eqv ha) h.1,
    Q'.le_trans' _ _ _ h.2 (Q'.add_le_add_right _ _ _ (Q'.ge_of_eqv ha))⟩

include hw0 hw1 in
private theorem numerator_abs_bound (p : RatPoly) (K : Nat) :
    Q'.abs (numerator w (blocks half) (centralExtent half)
      (slabPhysicalFaceEdges (centralExtent half)) p K) ≤ numeratorBound w half p :=
  Q'.le_trans' _ _ _ (quaternionHaar_abs_le_coefficientL1 _ _)
    (Q'.le_trans' _ _ _ (polynomialCoefficientL1_mul_le _ _)
      (Q'.mul_le_mul_of_nonneg_left _ _ _
        (BF4ExactSlabAllExtentHeatProductTail.heatProduct_coefficientL1_bound hw0 hw1 K _ _)
        (polynomialCoefficientL1_nonnegative p)))

private theorem numerator_product_converges (p q : RatPoly) :
    CReal.ConvergesTo (fun K => CReal.ofQ'
      (numerator w (blocks half) (centralExtent half) (slabPhysicalFaceEdges (centralExtent half)) p K *
       numerator w (blocks half) (centralExtent half) (slabPhysicalFaceEdges (centralExtent half)) q K))
      (CReal.mul
        (numeratorLimit w hw0 hw1 (blocks half) (centralExtent half) (slabPhysicalFaceEdges (centralExtent half)) p)
        (numeratorLimit w hw0 hw1 (blocks half) (centralExtent half) (slabPhysicalFaceEdges (centralExtent half)) q)) :=
  CReal.convergesTo_mul (B := Q'.max' (numeratorBound w half p) (numeratorBound w half q))
    (u := fun K => CReal.ofQ' (numerator w (blocks half) (centralExtent half)
      (slabPhysicalFaceEdges (centralExtent half)) p K))
    (v := fun K => CReal.ofQ' (numerator w (blocks half) (centralExtent half)
      (slabPhysicalFaceEdges (centralExtent half)) q K))
    (U := numeratorLimit w hw0 hw1 (blocks half) (centralExtent half) (slabPhysicalFaceEdges (centralExtent half)) p)
    (V := numeratorLimit w hw0 hw1 (blocks half) (centralExtent half) (slabPhysicalFaceEdges (centralExtent half)) q)
    (Q'.le_trans' _ _ _ (numeratorBound_nonnegative w hw0 half p) (Q'.le_max'_left _ _))
    (fun K _ => Q'.le_trans' _ _ _ (numerator_abs_bound w hw0 hw1 (half := half) p K) (Q'.le_max'_left _ _))
    (fun n => Q'.le_trans' _ _ _ (numerator_approx_abs_le w hw0 hw1 half q n) (Q'.le_max'_right _ _))
    (numerator_converges w hw0 hw1 (blocks half) (centralExtent half) (slabPhysicalFaceEdges (centralExtent half)) p)
    (numerator_converges w hw0 hw1 (blocks half) (centralExtent half) (slabPhysicalFaceEdges (centralExtent half)) q)

variable (hsmall : QuaternionHaarCharacterInterval.heatRatio w ≤ HalfPow.half)
  (hdelta : QuaternionHaarCharacterInterval.heatRemainderBound w < 1)

include hsmall hdelta in
/-- The finite estimate passes to the pre-existing original numerator limit. -/
theorem rawTestLimit_bound {p p' : RatPoly} {a b : Q'}
    (P : Interval (blocks half) p a) (P' : Interval (blocks half) p' b)
    (hl : LowerLocal half p) (hr : BF4ExactSlabSpatialChannelReflection.ReflectionImage (centralExtent half) p p')
    (htp : TemporalImage half p p) (e : PlaquetteExpression half) :
    CReal.leEv (CReal.mul (rawTestLimit w hw0 hw1 p e) (rawTestLimit w hw0 hw1 p e))
      (CReal.mul (CReal.ofQ' (b*a))
        (CReal.mul (rawLimit w hw0 hw1 e e) (rawLimit w hw0 hw1 (.unit : PlaquetteExpression half) .unit))) := by
  have hp : CReal.ConvergesTo
      (fun K => CReal.ofQ' (rawForm w K e e * rawForm w K (.unit : PlaquetteExpression half) .unit))
      (CReal.mul (rawLimit w hw0 hw1 e e) (rawLimit w hw0 hw1 (.unit : PlaquetteExpression half) .unit)) :=
    numerator_product_converges w hw0 hw1 (half := half)
      (polyMul (upper e) (lower e))
      (polyMul (upper (.unit : PlaquetteExpression half)) (lower (.unit : PlaquetteExpression half)))
  have hc : CReal.ConvergesTo
      (fun K => CReal.ofQ' ((b*a)*(rawForm w K e e * rawForm w K (.unit : PlaquetteExpression half) .unit)))
      (CReal.mul (CReal.ofQ' (b*a))
        (CReal.mul (rawLimit w hw0 hw1 e e) (rawLimit w hw0 hw1 (.unit : PlaquetteExpression half) .unit))) :=
    fun epsilon he => (CReal.convergesTo_const_mul (CReal.ofQ' (b*a)) hp) epsilon he
  apply CReal.leEv_of_ofQ'_limit_le
    (r := fun K => numerator w (blocks half) (centralExtent half) (slabPhysicalFaceEdges (centralExtent half))
      (polyMul (upper e) p) K * numerator w (blocks half) (centralExtent half)
        (slabPhysicalFaceEdges (centralExtent half)) (polyMul (upper e) p) K)
    (r' := fun K => (b*a)*(rawForm w K e e * rawForm w K (.unit : PlaquetteExpression half) .unit))
    (numerator_product_converges w hw0 hw1 (half := half) (polyMul (upper e) p) (polyMul (upper e) p))
    hc
  intro epsilon he
  refine ⟨1, fun K hK => ?_⟩
  have ha := full_amplitude_original w (Q'.le_of_lt hw0) K hK half p P.support hl htp e
  have hsq := Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha) (Q'.mul_eqv_congr_left _ _ _ ha)
  have h := amplitude_partition_bound (Q'.le_of_lt hw0) (Q'.le_of_lt hw1) hsmall hdelta
    K hK half (fun _ => none) P P' hl hr e
  have horder : rawForm w K e e * ((b*a)*partition w K half) ≈
      (b*a)*(rawForm w K e e * partition w K half) :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv _ _)) (Q'.mul_assoc_eqv _ _ _))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hsq)
    (Q'.le_trans' _ _ _ h (Q'.le_trans' _ _ _ (Q'.le_of_eqv horder)
      (Q'.add_le_self_of_nonneg _ epsilon (Q'.le_of_lt he))))

/-- Normalization uses the original action reciprocal and its existing modulus. -/
def testLimit (p : RatPoly) (e : PlaquetteExpression half) : CReal :=
  expectation w hw0 hw1 half (polyMul (upper e) p)

def testLimitCauchy (p : RatPoly) (e : PlaquetteExpression half) :
    CReal.QCauchy (testLimit w hw0 hw1 p e).approx :=
  expectationCauchy w hw0 hw1 half (polyMul (upper e) p)

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

include hsmall hdelta in
/-- The ORIGINAL cutoff-removed reflected norm, with the SAME cap and no
partition ceiling in its coefficient. This is not a time-transfer bound. -/
theorem testLimit_bound {p p' : RatPoly} {a b : Q'}
    (P : Interval (blocks half) p a) (P' : Interval (blocks half) p' b)
    (hl : LowerLocal half p) (hr : BF4ExactSlabSpatialChannelReflection.ReflectionImage (centralExtent half) p p')
    (htp : TemporalImage half p p) (e : PlaquetteExpression half) :
    CReal.leEv (CReal.mul (testLimit w hw0 hw1 p e) (testLimit w hw0 hw1 p e))
      (CReal.mul (CReal.ofQ' (b*a)) (form w hw0 hw1 e e)) := by
  let L := BF4ExactSlabOriginalActionReciprocal.actionReciprocal w hw0 hw1 half
  have hL := reciprocal_nonnegative w hw0 hw1 half
  have h := CReal.leEv_mul_nonneg_left (CReal.mul_nonneg hL hL)
    (rawTestLimit_bound w hw0 hw1 hsmall hdelta P P' hl hr htp e)
  have hz := (normalization_product (rawLimit w hw0 hw1 e e)
    (rawLimit w hw0 hw1 (.unit : PlaquetteExpression half) .unit) L (b*a)).trans
      ((Pivot2.mul_congr_right (Pivot2.mul_congr_right (form_unit w hw0 hw1 half))).trans
        (Pivot2.mul_congr_right (CRealAlg.cmul_cone (form w hw0 hw1 e e))))
  exact CReal.leEv_trans (CReal.leEv_of_equiv (normalization_square (rawTestLimit w hw0 hw1 p e) L))
    (CReal.leEv_trans h (CReal.leEv_of_equiv hz))

include hsmall hdelta in
/-- Concrete lower-link product: no temporal-invariance premise is left. -/
theorem bulkScalar_limit_bound (e : PlaquetteExpression half) :
    CReal.leEv
      (CReal.mul (testLimit w hw0 hw1 (bulkScalar half) e) (testLimit w hw0 hw1 (bulkScalar half) e))
      (form w hw0 hw1 e e) := by
  have h := testLimit_bound w hw0 hw1 hsmall hdelta
    (BF4ExactSlabBulkProbeLocalIntervals.bulkScalarInterval half)
    (BF4ExactSlabBulkProbeLocalIntervals.upperScalarInterval half)
    (BF4ExactSlabBulkProbeInteractingAmplitudes.bulkScalar_lower half)
    (BF4ExactSlabBulkProbeLocalIntervals.upperScalar_image half)
    (bulkScalar_temporal_fixed half) e
  exact CReal.leEv_trans h (CReal.leEv_of_equiv
    (SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.one_mul_eqv _)))

theorem testLimit_add (p : RatPoly) (e f : PlaquetteExpression half) :
    CReal.Equiv (testLimit w hw0 hw1 p (.add e f))
      (CReal.add (testLimit w hw0 hw1 p e) (testLimit w hw0 hw1 p f)) := by
  change CReal.Equiv (expectation w hw0 hw1 half (polyMul (polyAdd (upper e) (upper f)) p)) _
  rw [polyMul_add_left_exact]
  exact expectation_add w hw0 hw1 half _ _

theorem testLimit_smul (p : RatPoly) (c : Q') (e : PlaquetteExpression half) :
    CReal.Equiv (testLimit w hw0 hw1 p (.smul c e))
      (CReal.mul (CReal.ofQ' c) (testLimit w hw0 hw1 p e)) :=
  (expectation_congr w hw0 hw1 half (RatPolyCoeffEqv.polyMul_smul_left c (upper e) p)).trans
    (expectation_smul w hw0 hw1 half c _)

theorem testLimit_sub (p : RatPoly) (e f : PlaquetteExpression half) :
    CReal.Equiv (testLimit w hw0 hw1 p (BF4ExactSlabPlaquetteNullQuotient.subtract e f))
      (CReal.sub (testLimit w hw0 hw1 p e) (testLimit w hw0 hw1 p f)) :=
  (testLimit_add w hw0 hw1 p e (.smul (-1) f)).trans
    (Pivot2.add_congr (CReal.Equiv.refl _)
      ((testLimit_smul w hw0 hw1 p (-1) f).trans
        (SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 _)
          (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv _))))))

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

include hsmall hdelta in
/-- Nullity is for the cutoff-REMOVED original form, not a finite-cutoff radical. -/
theorem bulkScalar_limit_null (e : PlaquetteExpression half)
    (he : CReal.Equiv (form w hw0 hw1 e e) (CReal.ofQ' 0)) :
    CReal.Equiv (testLimit w hw0 hw1 (bulkScalar half) e) (CReal.ofQ' 0) :=
  zero_of_square_le_zero _ (CReal.leEv_trans (bulkScalar_limit_bound w hw0 hw1 hsmall hdelta e)
    (CReal.leEv_of_equiv he))

include hsmall hdelta in
theorem bulkScalar_null_congr {e f : PlaquetteExpression half}
    (h : BF4ExactSlabPlaquetteNullQuotient.Null w hw0 hw1 e f) :
    CReal.Equiv (testLimit w hw0 hw1 (bulkScalar half) e) (testLimit w hw0 hw1 (bulkScalar half) f) :=
  CReal.Equiv_of_sub_eqv_zero ((testLimit_sub w hw0 hw1 (bulkScalar half) e f).symm.trans
    (bulkScalar_limit_null w hw0 hw1 hsmall hdelta _ (Quotient.exact h)))

/-- The test now acts on the EXISTING cutoff-removed finite-volume OS quotient. -/
def bulkScalarQuotientTest : BF4ExactSlabPlaquetteNullQuotient.Carrier w hw0 hw1 half → CReal.RC :=
  Quotient.lift (fun e => Quotient.mk CReal.crealSetoid (testLimit w hw0 hw1 (bulkScalar half) e))
    (fun _ _ h => Quotient.sound (bulkScalar_null_congr w hw0 hw1 hsmall hdelta h))

theorem bulkScalarQuotientTest_embed (e : PlaquetteExpression half) :
    bulkScalarQuotientTest w hw0 hw1 hsmall hdelta (BF4ExactSlabPlaquetteNullQuotient.embed w hw0 hw1 e) =
      Quotient.mk CReal.crealSetoid (testLimit w hw0 hw1 (bulkScalar half) e) := rfl

end YMGap.Continuum.BF4ExactSlabDressedDualTestCutoffLimit

#print axioms YMGap.Continuum.BF4ExactSlabDressedDualTestCutoffLimit.scalar_temporal_fixed
#print axioms YMGap.Continuum.BF4ExactSlabDressedDualTestCutoffLimit.scalarProduct_temporal_fixed
#print axioms YMGap.Continuum.BF4ExactSlabDressedDualTestCutoffLimit.bulkScalar_temporal_fixed
#print axioms YMGap.Continuum.BF4ExactSlabDressedDualTestCutoffLimit.original_numerator_spatialGram
#print axioms YMGap.Continuum.BF4ExactSlabDressedDualTestCutoffLimit.full_amplitude_original
#print axioms YMGap.Continuum.BF4ExactSlabDressedDualTestCutoffLimit.rawTestLimit
#print axioms YMGap.Continuum.BF4ExactSlabDressedDualTestCutoffLimit.testCutoff
#print axioms YMGap.Continuum.BF4ExactSlabDressedDualTestCutoffLimit.full_amplitude_approx_close
#print axioms YMGap.Continuum.BF4ExactSlabDressedDualTestCutoffLimit.rawTestLimit_bound
#print axioms YMGap.Continuum.BF4ExactSlabDressedDualTestCutoffLimit.testLimit
#print axioms YMGap.Continuum.BF4ExactSlabDressedDualTestCutoffLimit.testLimitCauchy
#print axioms YMGap.Continuum.BF4ExactSlabDressedDualTestCutoffLimit.testLimit_bound
#print axioms YMGap.Continuum.BF4ExactSlabDressedDualTestCutoffLimit.bulkScalar_limit_bound
#print axioms YMGap.Continuum.BF4ExactSlabDressedDualTestCutoffLimit.testLimit_add
#print axioms YMGap.Continuum.BF4ExactSlabDressedDualTestCutoffLimit.testLimit_smul
#print axioms YMGap.Continuum.BF4ExactSlabDressedDualTestCutoffLimit.testLimit_sub
#print axioms YMGap.Continuum.BF4ExactSlabDressedDualTestCutoffLimit.bulkScalar_limit_null
#print axioms YMGap.Continuum.BF4ExactSlabDressedDualTestCutoffLimit.bulkScalar_null_congr
#print axioms YMGap.Continuum.BF4ExactSlabDressedDualTestCutoffLimit.bulkScalarQuotientTest
#print axioms YMGap.Continuum.BF4ExactSlabDressedDualTestCutoffLimit.bulkScalarQuotientTest_embed
