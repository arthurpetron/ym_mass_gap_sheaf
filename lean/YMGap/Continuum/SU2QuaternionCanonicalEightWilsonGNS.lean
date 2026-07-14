/-
# Interacting Wilson GNS datum on the canonical quaternion carrier

The exact Haar-test quotient makes every missing state law constructive: the
interacting expectation is congruent by testing with the Wilson weight,
additive and homogeneous by the derived Haar pairing identities, and
conjugate-symmetric because the polynomial involution is real and the exact
Haar triple pairing is commutative.
-/

import YMGap.Continuum.SU2QuaternionCanonicalEightHaarPairModule

namespace YMGap.Continuum.SU2QuaternionCanonicalEightWilsonGNS

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.FiniteVolume
open YMGap.Continuum.ReferenceWeightTimeGeometry
open YMGap.Continuum.SU2QuaternionCanonicalEightCarrier
open YMGap.Continuum.SU2QuaternionCanonicalEightHaar
open YMGap.Continuum.SU2QuaternionCanonicalEightHaarLinearity
open YMGap.Continuum.SU2QuaternionCanonicalEightHaarPairModule
open YMGap.Continuum.SU2QuaternionCanonicalEightHaarSymmetry
open YMGap.Continuum.SU2QuaternionCanonicalEightTimeAction
open YMGap.Continuum.SU2QuaternionCanonicalEightWilsonPositivity
open YMGap.Continuum.SU2QuaternionCanonicalEightWilsonWeight

local infix:50 " ≈ " => Q'.eqv

theorem canonicalProductHaar_pair_swap (r p : Poly8) :
    canonicalProductHaar (polyMul8 r (swapPoly8 p)) ≈
      canonicalProductHaar (polyMul8 (swapPoly8 r) p) := by
  refine Q'.eqv_trans _
    (canonicalProductHaar
      (swapPoly8 (polyMul8 r (swapPoly8 p)))) _
    (Q'.eqv_symm
      (canonicalProductHaar_swap_invariant
        (polyMul8 r (swapPoly8 p)))) ?_
  rw [swapPoly8_mul, swapPoly8_involutive]
  exact Q'.eqv_refl _

/-- The same strict period-two action descends through the Haar-test quotient,
which is the quotient directly suited to the interacting expectation. -/
def canonicalRetainedBoundarySwapHaarPairGeometry :
    GeometryEnrichedReferenceWeight canonicalRetainedReferenceWeight
      canonicalHaarPairModule where
  timeExtent := 2
  timeExtent_pos := by decide
  action := canonicalRetainedBoundarySwapAction
  periodic := canonicalRetainedBoundarySwapAction_period_two
  map_veq := by
    intro a b h r
    refine Q'.eqv_trans _
      (canonicalProductHaar (polyMul8 (swapPoly8 r) a)) _
      (canonicalProductHaar_pair_swap r a) ?_
    refine Q'.eqv_trans _
      (canonicalProductHaar (polyMul8 (swapPoly8 r) b)) _
      (h (swapPoly8 r)) ?_
    exact Q'.eqv_symm (canonicalProductHaar_pair_swap r b)
  map_add := by
    intro a b r
    change canonicalProductHaar
        (polyMul8 r (swapPoly8 (polyAdd8 a b))) ≈
      canonicalProductHaar
        (polyMul8 r (polyAdd8 (swapPoly8 a) (swapPoly8 b)))
    rw [swapPoly8_add]
    exact Q'.eqv_refl _
  map_neg := by
    intro a r
    change canonicalProductHaar
        (polyMul8 r (swapPoly8 (polySmul8 (-(1 : Q')) a))) ≈
      canonicalProductHaar
        (polyMul8 r (polySmul8 (-(1 : Q')) (swapPoly8 a)))
    rw [swapPoly8_smul]
    exact Q'.eqv_refl _
  map_smul := by
    intro s a r
    change canonicalProductHaar
        (polyMul8 r (swapPoly8 (polySmul8 s a))) ≈
      canonicalProductHaar
        (polyMul8 r (polySmul8 s (swapPoly8 a)))
    rw [swapPoly8_smul]
    exact Q'.eqv_refl _

theorem canonicalRetained_E_congr {a b : Poly8}
    (h : CanonicalHaarPairEqv a b) :
    (canonicalRetainedReferenceWeight.E_Λ a).eqv
      (canonicalRetainedReferenceWeight.E_Λ b) := by
  change
    (canonicalProductHaar (polyMul8 retainedRelativeWeight8 a) *
        PlaquetteReweight.recip 1) ≈
      (canonicalProductHaar (polyMul8 retainedRelativeWeight8 b) *
        PlaquetteReweight.recip 1)
  exact Q'.mul_eqv_congr_right _ _ _ (h retainedRelativeWeight8)

theorem canonicalRetained_E_add (a b : Poly8) :
    (canonicalRetainedReferenceWeight.E_Λ (polyAdd8 a b)).eqv
      (canonicalRetainedReferenceWeight.E_Λ a +
        canonicalRetainedReferenceWeight.E_Λ b) := by
  change
    (canonicalProductHaar
        (polyMul8 retainedRelativeWeight8 (polyAdd8 a b)) *
      PlaquetteReweight.recip 1) ≈
    canonicalProductHaar (polyMul8 retainedRelativeWeight8 a) *
        PlaquetteReweight.recip 1 +
      canonicalProductHaar (polyMul8 retainedRelativeWeight8 b) *
        PlaquetteReweight.recip 1
  refine Q'.eqv_trans _
    ((canonicalProductHaar (polyMul8 retainedRelativeWeight8 a) +
      canonicalProductHaar (polyMul8 retainedRelativeWeight8 b)) *
        PlaquetteReweight.recip 1) _
    (Q'.mul_eqv_congr_right _ _ _
      (canonicalProductHaar_mul_add_right retainedRelativeWeight8 a b)) ?_
  exact Q'.add_mul_eqv _ _ _

theorem canonicalRetained_E_smul (s : Q') (a : Poly8) :
    (canonicalRetainedReferenceWeight.E_Λ (polySmul8 s a)).eqv
      (s * canonicalRetainedReferenceWeight.E_Λ a) := by
  change
    (canonicalProductHaar
        (polyMul8 retainedRelativeWeight8 (polySmul8 s a)) *
      PlaquetteReweight.recip 1) ≈
    s * (canonicalProductHaar
      (polyMul8 retainedRelativeWeight8 a) * PlaquetteReweight.recip 1)
  refine Q'.eqv_trans _
    ((s * canonicalProductHaar
      (polyMul8 retainedRelativeWeight8 a)) *
        PlaquetteReweight.recip 1) _
    (Q'.mul_eqv_congr_right _ _ _
      (canonicalProductHaar_mul_smul_right s retainedRelativeWeight8 a)) ?_
  exact Q'.mul_assoc_eqv _ _ _

theorem canonicalRetained_E_hconj (a b : Poly8) :
    (canonicalRetainedReferenceWeight.E_Λ (polyMul8 a b)).eqv
      (canonicalRetainedReferenceWeight.E_Λ (polyMul8 b a)) := by
  change
    (canonicalProductHaar
        (polyMul8 retainedRelativeWeight8 (polyMul8 a b)) *
      PlaquetteReweight.recip 1) ≈
    (canonicalProductHaar
        (polyMul8 retainedRelativeWeight8 (polyMul8 b a)) *
      PlaquetteReweight.recip 1)
  exact Q'.mul_eqv_congr_right _ _ _
    (canonicalProductHaar_mul_middle_comm retainedRelativeWeight8 a b)

/-- Unconditional interacting Wilson GNS data on the full canonical
polynomial algebra.  Its positivity comes from the exact Wilson SOS theorem;
none of its linearity or symmetry fields is assumed. -/
def canonicalRetainedWilsonGNSData : WilsonGNS.WilsonGNSData
    canonicalQuaternionPairAlg :=
  canonicalRetainedBoundarySwapHaarPairGeometry.toWilsonGNSData
    canonicalRetained_E_congr canonicalRetained_E_add
    canonicalRetained_E_smul canonicalRetained_E_hconj

end YMGap.Continuum.SU2QuaternionCanonicalEightWilsonGNS

#print axioms YMGap.Continuum.SU2QuaternionCanonicalEightWilsonGNS.canonicalRetainedBoundarySwapHaarPairGeometry
#print axioms YMGap.Continuum.SU2QuaternionCanonicalEightWilsonGNS.canonicalRetained_E_congr
#print axioms YMGap.Continuum.SU2QuaternionCanonicalEightWilsonGNS.canonicalRetainedWilsonGNSData
