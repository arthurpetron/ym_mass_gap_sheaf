/-
# Finite exact certificates for a positive ORIGINAL action-integral limit

The original product-tail modulus makes a finite rational test sufficient:
choose epsilon > 0, b > 0 and K beyond that modulus, then check
                         b + epsilon <= fullActionValue w K half.
The SAME limit has an eventual approximation floor b at an explicit index.
The checker returns the finite data and its proofs, or none. Failure means
only that these proposed data did not certify a floor; it is not a zero test.

This supplies no universal successful certificate, no lower bound uniform
in w/extent/spacing, and no replacement of the interacting Haar law. The
remaining analytic task is to produce successful data throughout the required
parameter family. No pointwise heat-positivity or JTP premise is introduced.
Conversely, a supplied positive geRat floor yields such finite data with a
computed cutoff and quarter-floor budget. Thus the finite criterion adds no
extra analytic assumption; the converse is not an unconditional producer.
-/

import YMGap.Continuum.BF4ExactSlabAllExtentHeatUnitNormAction

namespace YMGap.Continuum.BF4ExactSlabAllExtentActionFloorCertificate

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4ExactSlabAllExtentActionLimit
open YMGap.Continuum.BF4ExactSlabAllExtentHeatProductTail
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

/-- Both the finite anchor and eventual representative index use this explicit threshold. -/
def actionCutoff (w : Q') (half : Nat) (epsilon : Q') : Nat :=
  heatProductCutoff w (centralExtent half) (slabPhysicalFaceEdges (centralExtent half)) epsilon

theorem fullActionLimit_approx_close (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (epsilon : Q') (hepsilon : (0 : Q') < epsilon) (K n : Nat)
    (hK : actionCutoff w half epsilon ≤ K) (hn : actionCutoff w half epsilon ≤ n) :
    fullActionValue w K half ≤ (fullActionLimit w hw0 hw1 half).approx n + epsilon ∧
      (fullActionLimit w hw0 hw1 half).approx n ≤ fullActionValue w K half + epsilon := by
  unfold fullActionLimit
  rw [heatProductHaarLimit_approx]
  exact (heatProductHaarCauchy w hw0 hw1
    (boundaryCompleteSlabLinks (centralExtent half)).length
    (centralExtent half) (slabPhysicalFaceEdges (centralExtent half))).bound
      epsilon hepsilon K _ hK (Nat.le_trans hn (CReal.self_le_QMhat _ _ n))

private theorem add_cancel_right {a b c : Q'} (h : a + c ≤ b + c) : a ≤ b := by
  have hc (x : Q') : (x + c) + (-c) ≈ x :=
    Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv x c (-c))
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left x _ _ (Q'.add_neg_self_eqv c))
        (Q'.eqv_of_eq (Q'.add_zero' x)))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (hc a))
    (Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ (-c) h) (Q'.le_of_eqv (hc b)))

/-- The floor and its full eventual-index guarantee, before a legacy geRat wrapper. -/
theorem fullActionLimit_finite_floor (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (epsilon b : Q') (hepsilon : (0 : Q') < epsilon) (K : Nat)
    (hK : actionCutoff w half epsilon ≤ K) (hb : b + epsilon ≤ fullActionValue w K half)
    (n : Nat) (hn : actionCutoff w half epsilon ≤ n) :
    b ≤ (fullActionLimit w hw0 hw1 half).approx n :=
  add_cancel_right (Q'.le_trans' _ _ _ hb
    (fullActionLimit_approx_close w hw0 hw1 half epsilon hepsilon K n hK hn).1)

/-- Only finite, decidable inequalities on the ORIGINAL action data. -/
structure FiniteActionFloor (w : Q') (half : Nat) where
  epsilon : Q'
  floor : Q'
  cutoff : Nat
  epsilon_pos : (0 : Q') < epsilon
  floor_pos : (0 : Q') < floor
  tail_cutoff : actionCutoff w half epsilon ≤ cutoff
  finite_floor : floor + epsilon ≤ fullActionValue w cutoff half

/-- Executable proof-producing check; none is NOT a proof of vanishing. -/
def checkActionFloor (w : Q') (half : Nat) (epsilon b : Q') (K : Nat) :
    Option (FiniteActionFloor w half) :=
  if he : (0 : Q') < epsilon then
    if hb : (0 : Q') < b then
      if hK : actionCutoff w half epsilon ≤ K then
        if hf : b + epsilon ≤ fullActionValue w K half then
          some ⟨epsilon, b, K, he, hb, hK, hf⟩
        else none
      else none
    else none
  else none

theorem checkActionFloor_accepts (w : Q') (half : Nat) (epsilon b : Q') (K : Nat)
    (he : (0 : Q') < epsilon) (hb : (0 : Q') < b)
    (hK : actionCutoff w half epsilon ≤ K) (hf : b + epsilon ≤ fullActionValue w K half) :
    checkActionFloor w half epsilon b K = some ⟨epsilon, b, K, he, hb, hK, hf⟩ := by
  simp [checkActionFloor, he, hb, hK, hf]

namespace FiniteActionFloor

/-- Computable representative-index bound accompanying the rational floor. -/
def index {w : Q'} {half : Nat} (C : FiniteActionFloor w half) : Nat :=
  actionCutoff w half C.epsilon

theorem approx_ge {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {half : Nat} (C : FiniteActionFloor w half) (n : Nat) (hn : C.index ≤ n) :
    C.floor ≤ (fullActionLimit w hw0 hw1 half).approx n :=
  fullActionLimit_finite_floor w hw0 hw1 half C.epsilon C.floor C.epsilon_pos
    C.cutoff C.tail_cutoff C.finite_floor n hn

theorem limit_ge {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {half : Nat} (C : FiniteActionFloor w half) :
    ExpPos.geRat (fullActionLimit w hw0 hw1 half) C.floor :=
  ExpPos.geRat_of_eventually ⟨C.index, C.approx_ge hw0 hw1⟩

/-- Completeness of the finite criterion, GIVEN a positive floor for the same limit.
All returned data depend only on w, half and b, not on an extracted Prop witness. -/
def ofLimitFloor (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (half : Nat)
    (b : Q') (hb : (0 : Q') < b) (hfloor : ExpPos.geRat (fullActionLimit w hw0 hw1 half) b) :
    FiniteActionFloor w half where
  epsilon := HalfPow.half * (HalfPow.half * b)
  floor := HalfPow.half * (HalfPow.half * b)
  cutoff := actionCutoff w half (HalfPow.half * (HalfPow.half * b))
  epsilon_pos := ExpNeg.half_mul_pos _ (ExpNeg.half_mul_pos _ hb)
  floor_pos := ExpNeg.half_mul_pos _ (ExpNeg.half_mul_pos _ hb)
  tail_cutoff := Nat.le_refl _
  finite_floor := by
    let delta := HalfPow.half * (HalfPow.half * b)
    let K := actionCutoff w half delta
    have hd : (0 : Q') < delta := ExpNeg.half_mul_pos _ (ExpNeg.half_mul_pos _ hb)
    obtain ⟨N, hN⟩ := hfloor delta hd
    have hsample := (fullActionLimit_approx_close w hw0 hw1 half delta hd K (max K N)
      (Nat.le_refl _) (Nat.le_max_left _ _)).2
    have hle := Q'.le_trans' _ _ _ (hN (max K N) (Nat.le_max_right _ _))
      (Q'.add_le_add_right _ _ delta hsample)
    have hfour : (delta + delta) + (delta + delta) ≈ b :=
      Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (ExpNeg.two_halves (HalfPow.half * b))
          (ExpNeg.two_halves (HalfPow.half * b))) (ExpNeg.two_halves b)
    exact add_cancel_right (Q'.le_trans' _ _ _ (Q'.le_of_eqv hfour)
      (Q'.le_trans' _ _ _ hle (Q'.le_of_eqv (Q'.add_assoc_eqv _ delta delta))))

theorem ofLimitFloor_epsilon (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (half : Nat)
    (b : Q') (hb : (0 : Q') < b) (hfloor : ExpPos.geRat (fullActionLimit w hw0 hw1 half) b) :
    (ofLimitFloor w hw0 hw1 half b hb hfloor).epsilon = HalfPow.half * (HalfPow.half * b) := rfl

theorem ofLimitFloor_floor (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (half : Nat)
    (b : Q') (hb : (0 : Q') < b) (hfloor : ExpPos.geRat (fullActionLimit w hw0 hw1 half) b) :
    (ofLimitFloor w hw0 hw1 half b hb hfloor).floor = HalfPow.half * (HalfPow.half * b) := rfl

theorem ofLimitFloor_cutoff (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (half : Nat)
    (b : Q') (hb : (0 : Q') < b) (hfloor : ExpPos.geRat (fullActionLimit w hw0 hw1 half) b) :
    (ofLimitFloor w hw0 hw1 half b hb hfloor).cutoff =
      actionCutoff w half (HalfPow.half * (HalfPow.half * b)) := rfl

end FiniteActionFloor

end YMGap.Continuum.BF4ExactSlabAllExtentActionFloorCertificate

#print axioms YMGap.Continuum.BF4ExactSlabAllExtentActionFloorCertificate.actionCutoff
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentActionFloorCertificate.fullActionLimit_approx_close
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentActionFloorCertificate.fullActionLimit_finite_floor
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentActionFloorCertificate.FiniteActionFloor
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentActionFloorCertificate.checkActionFloor
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentActionFloorCertificate.checkActionFloor_accepts
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentActionFloorCertificate.FiniteActionFloor.index
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentActionFloorCertificate.FiniteActionFloor.approx_ge
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentActionFloorCertificate.FiniteActionFloor.limit_ge
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentActionFloorCertificate.FiniteActionFloor.ofLimitFloor
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentActionFloorCertificate.FiniteActionFloor.ofLimitFloor_epsilon
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentActionFloorCertificate.FiniteActionFloor.ofLimitFloor_floor
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentActionFloorCertificate.FiniteActionFloor.ofLimitFloor_cutoff
