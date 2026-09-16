/-
# Normalized intermediate original actions at every rational nome

Every physical face list has an original normalized cutoff limit for
0<w<1. Only the explicitly computed initial cutoffs are discarded. The
actual normalized rational stream and its CReal limit retain their Cauchy
moduli; the limit is pinned to the original numerator and partition.

This removes the small-nome restriction on intermediate face-set laws,
not on any spatial estimate. Floors depend on the nome and face count.
No decimation closure, uniform spatial bound, physical gap or continuum
construction is inferred from normalization.
-/

import YMGap.Continuum.BF4ExactSlabAllNomeFaceSetReciprocal
import YMGap.Continuum.BF4ExactSlabFaceSetExpectation
import YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarAlgebra
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz

namespace YMGap.Continuum.BF4ExactSlabAllNomeFaceSetExpectation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabAllExtentActionLimit
open YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetReciprocal
open YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarAlgebra
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.BoundedRationalCauchyProduct
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

private def streamReal (r : Nat → Q') (c : QCauchy r) : CReal where
  approx := r
  cauchy := fun epsilon he => ⟨c.M epsilon, c.bound epsilon he⟩

variable (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (extent : Nat) (ids : List Nat)
  (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent)

local notation "blocks" => List.length (boundaryCompleteSlabLinks extent)
local notation "N" => numerator w blocks extent ids
local notation "Nlim" => numeratorLimit w hw0 hw1 blocks extent ids
local notation "Zlim" => heatProductHaarLimit w hw0 hw1 blocks extent ids
local notation "R" => reciprocal w hw0 hw1 extent ids hids
local notation "r" => reciprocalTerm w hw0 hw1 extent ids hids

private def numeratorSampleCauchy (p : RatPoly) :
    QCauchy (fun n => N p (headCutoff w+n)) where
  M := (numeratorCauchy w hw0 hw1 blocks extent ids p).M
  bound := fun epsilon he _ _ hi hj =>
    (numeratorCauchy w hw0 hw1 blocks extent ids p).bound epsilon he _ _
      (Nat.le_trans hi (Nat.le_add_left _ _)) (Nat.le_trans hj (Nat.le_add_left _ _))

/-- Index n uses the SAME numerator and denominator at cutoff headCutoff(w)+n. -/
def finiteValue (p : RatPoly) (n : Nat) : Q' := N p (headCutoff w+n) * r n

/-- The returned modulus controls the actual normalized rational values. -/
def finiteCauchy (p : RatPoly) : QCauchy (finiteValue w hw0 hw1 extent ids hids p) :=
  scalarMulCauchy
    (streamReal _ (numeratorSampleCauchy w hw0 hw1 extent ids p))
    (streamReal _ (reciprocalStreamCauchy w hw0 hw1 extent ids hids))
    (numeratorSampleCauchy w hw0 hw1 extent ids p)
    (reciprocalStreamCauchy w hw0 hw1 extent ids hids)

def expectation (p : RatPoly) : CReal :=
  ofQ'CauchySeq _ (finiteCauchy w hw0 hw1 extent ids hids p)

def expectationCauchy (p : RatPoly) : QCauchy (expectation w hw0 hw1 extent ids hids p).approx :=
  representativeCauchy _ (finiteCauchy w hw0 hw1 extent ids hids p)

theorem finite_converges (p : RatPoly) :
    ConvergesTo (fun n => ofQ' (finiteValue w hw0 hw1 extent ids hids p n))
      (expectation w hw0 hw1 extent ids hids p) := convergesTo_ofQ'CauchySeq _ _

/-- Both raw cutoff-offset and representative thresholds are explicit data. -/
theorem approx_close (p : RatPoly) (epsilon : Q') (he : (0 : Q') < epsilon)
    (K n : Nat) (hK : (finiteCauchy w hw0 hw1 extent ids hids p).M epsilon ≤ K)
    (hn : (finiteCauchy w hw0 hw1 extent ids hids p).M epsilon ≤ n) :
    finiteValue w hw0 hw1 extent ids hids p K ≤
        (expectation w hw0 hw1 extent ids hids p).approx n + epsilon ∧
      (expectation w hw0 hw1 extent ids hids p).approx n ≤
        finiteValue w hw0 hw1 extent ids hids p K + epsilon :=
  (finiteCauchy w hw0 hw1 extent ids hids p).bound epsilon he K _ hK
    (Nat.le_trans hn (self_le_QMhat _ _ n))

/-- Pin to the two ORIGINAL cutoff limits; no replacement action or partition. -/
theorem expectation_formula (p : RatPoly) :
    Equiv (expectation w hw0 hw1 extent ids hids p) (CReal.mul (Nlim p) R) := by
  have hN : ConvergesTo (fun n => ofQ' (N p (headCutoff w+n))) (Nlim p) := by
    intro epsilon he
    obtain ⟨M,hM⟩ := numerator_converges w hw0 hw1 blocks extent ids p epsilon he
    exact ⟨M, fun n hn => hM _ (Nat.le_trans hn (Nat.le_add_left _ _))⟩
  have hR : ConvergesTo (fun n => ofQ' (r n)) R :=
    PositiveRationalCauchyReciprocal.converges _ _ _ _
  have hmul :=
    Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general hN hR
  refine Equiv_of_limit_of_equal ?_
    (finite_converges w hw0 hw1 extent ids hids p) hmul
  intro n
  exact SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_refl _)

theorem expectation_one : Equiv (expectation w hw0 hw1 extent ids hids polyOne) cone :=
  (expectation_formula w hw0 hw1 extent ids hids polyOne).trans
    ((Pivot2.mul_congr_left (numeratorLimit_one w hw0 hw1 blocks extent ids)).trans
      (partition_cancellation w hw0 hw1 extent ids hids))

theorem expectation_recover (p : RatPoly) :
    Equiv (CReal.mul (expectation w hw0 hw1 extent ids hids p) Zlim) (Nlim p) :=
  (Pivot2.mul_congr_left (expectation_formula w hw0 hw1 extent ids hids p)).trans
    ((CRealAlg.cmul_assoc _ _ _).trans
      ((Pivot2.mul_congr_right ((CRealAlg.cmul_comm _ _).trans
        (partition_cancellation w hw0 hw1 extent ids hids))).trans (CRealAlg.cmul_cone _)))

theorem expectation_certificate_nonnegative (p : RatPoly) (P : Certificate blocks p) :
    leEv (ofQ' 0) (expectation w hw0 hw1 extent ids hids p) :=
  leEv_trans
    (CReal.mul_nonneg (numeratorLimit_certificate_nonnegative w hw0 hw1 extent ids hids p P)
      (leEv_ofQ'_of_approx_ge (fun n => Q'.le_of_lt (reciprocal_approx_pos w hw0 hw1 extent ids hids n))))
    (leEv_of_equiv (expectation_formula w hw0 hw1 extent ids hids p).symm)

/-- Where the old guards hold, this is exactly the old face-set state. -/
theorem legacy_expectation_pin (hsmall : heatRatio w ≤ HalfPow.half)
    (hd : heatRemainderBound w < 1) (p : RatPoly) :
    Equiv (expectation w hw0 hw1 extent ids hids p)
      (BF4ExactSlabFaceSetExpectation.expectation w hw0 hw1 hsmall hd extent ids hids p) := by
  let e := expectation w hw0 hw1 extent ids hids p
  have hc := BF4ExactSlabFaceSetExpectation.partition_cancellation w hw0 hw1 hsmall hd extent ids hids
  exact (CRealAlg.cmul_cone e).symm.trans
    ((Pivot2.mul_congr_right hc.symm).trans
      ((CRealAlg.cmul_assoc _ _ _).symm.trans
        (Pivot2.mul_congr_left (expectation_recover w hw0 hw1 extent ids hids p))))

/-- The full odd-slab specialization is the pre-existing all-nome original law. -/
theorem odd_expectation_pin (half : Nat) (p : RatPoly) :
    Equiv (expectation w hw0 hw1 (centralExtent half) (slabPhysicalFaceEdges (centralExtent half))
      (fun _ h => h) p) (BF4ExactSlabPolynomialExpectation.expectation w hw0 hw1 half p) := by
  let e := expectation w hw0 hw1 (centralExtent half) (slabPhysicalFaceEdges (centralExtent half))
    (fun _ h => h) p
  have hc := BF4ExactSlabOriginalActionReciprocal.action_mul_reciprocal w hw0 hw1 half
  exact (CRealAlg.cmul_cone e).symm.trans
    ((Pivot2.mul_congr_right hc.symm).trans
      ((CRealAlg.cmul_assoc _ _ _).symm.trans
        (Pivot2.mul_congr_left (expectation_recover w hw0 hw1
          (centralExtent half) (slabPhysicalFaceEdges (centralExtent half)) (fun _ h => h) p))))

end YMGap.Continuum.BF4ExactSlabAllNomeFaceSetExpectation

#print axioms YMGap.Continuum.BF4ExactSlabAllNomeFaceSetExpectation.finiteValue
#print axioms YMGap.Continuum.BF4ExactSlabAllNomeFaceSetExpectation.finiteCauchy
#print axioms YMGap.Continuum.BF4ExactSlabAllNomeFaceSetExpectation.expectation
#print axioms YMGap.Continuum.BF4ExactSlabAllNomeFaceSetExpectation.expectationCauchy
#print axioms YMGap.Continuum.BF4ExactSlabAllNomeFaceSetExpectation.finite_converges
#print axioms YMGap.Continuum.BF4ExactSlabAllNomeFaceSetExpectation.approx_close
#print axioms YMGap.Continuum.BF4ExactSlabAllNomeFaceSetExpectation.expectation_formula
#print axioms YMGap.Continuum.BF4ExactSlabAllNomeFaceSetExpectation.expectation_one
#print axioms YMGap.Continuum.BF4ExactSlabAllNomeFaceSetExpectation.expectation_recover
#print axioms YMGap.Continuum.BF4ExactSlabAllNomeFaceSetExpectation.expectation_certificate_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabAllNomeFaceSetExpectation.legacy_expectation_pin
#print axioms YMGap.Continuum.BF4ExactSlabAllNomeFaceSetExpectation.odd_expectation_pin
