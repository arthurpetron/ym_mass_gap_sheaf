/-
# Strict ORIGINAL action-limit floor and non-null completed heat unit

For every rational 0<w<1 and every odd slab, the ORIGINAL interacting
action limit is at least c(w)^F>0. The same-object Jacobi product comparison
provides an explicit approximation index at each requested error; the
original CReal cofinal reindex preserves that threshold.

This constructs the existing FiniteActionFloor without a positive-floor
premise and proves the ACTUAL completed full heat unit nonzero. The floor
depends on w and the finite face count. Normalization, compatible slabs,
physical stationary vacuum/time transfer, strict vacuum-complement gap,
volume/spacing control and continuum/QFT/all-group Clay remain separate.
-/

import YMGap.Continuum.BF4ExactSlabJacobiProductComparison
import YMGap.Continuum.BF4ExactSlabAllExtentHeatUnitCertifiedNonzero

namespace YMGap.Continuum.BF4ExactSlabOriginalActionStrictFloor

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4ExactSlabAllExtentFiniteBoundaryObservable
open YMGap.Continuum.BF4ExactSlabAllExtentCutoffLimitGNS
open YMGap.Continuum.BF4ExactSlabAllExtentHeatUnitCauchy
open YMGap.Continuum.BF4ExactSlabAllExtentActionLimit
open YMGap.Continuum.BF4ExactSlabAllExtentActionFloorCertificate
open YMGap.Continuum.BF4ExactSlabJacobiProductComparison
open YMGap.Continuum.BF4ExactSlabJacobiHaarFloor
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

/-- Explicit all-later approximation bound on the EXISTING original CReal.
comparisonCutoff is the Type-level index; it is not extracted from geRat. -/
theorem productLimit_approx_floor (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (extent : Nat) (ids : List Nat) (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent)
    (ε : Q') (hε : (0 : Q') < ε) (n : Nat) (hn : comparisonCutoff w extent ids ε ≤ n) :
    productFloor w ids ≤
      (heatProductHaarLimit w hw0 hw1 (boundaryCompleteSlabLinks extent).length extent ids).approx n + ε := by
  rw [heatProductHaarLimit_approx]
  exact productFloor_le_original_add hw0 hw1 extent ids hids ε hε _
    (Nat.le_trans hn (CReal.self_le_QMhat _ _ n))

theorem productLimit_ge_floor (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (extent : Nat) (ids : List Nat) (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent) :
    ExpPos.geRat (heatProductHaarLimit w hw0 hw1 (boundaryCompleteSlabLinks extent).length extent ids)
      (productFloor w ids) :=
  fun ε hε => ⟨comparisonCutoff w extent ids ε, productLimit_approx_floor w hw0 hw1 extent ids hids ε hε⟩

/-- Computed nome- and slab-dependent strict original-action floor. -/
def fullActionFloor (w : Q') (half : Nat) : Q' :=
  productFloor w (slabPhysicalFaceEdges (centralExtent half))

theorem fullActionFloor_pos {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (half : Nat) :
    (0 : Q') < fullActionFloor w half := productFloor_pos hw0 hw1 _

/-- Unconditional within the stated rational nome range, on the original
interacting action; no auxiliary positive-law identity is used. -/
theorem fullActionLimit_ge_floor (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (half : Nat) :
    ExpPos.geRat (fullActionLimit w hw0 hw1 half) (fullActionFloor w half) :=
  productLimit_ge_floor w hw0 hw1 _ _ (fun _ h => h)

/-- Actual successful finite certificate for EVERY supplied w and odd slab.
The pre-existing criterion is unchanged, including its original tail cutoff. -/
def fullActionFloorCertificate (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (half : Nat) :
    FiniteActionFloor w half :=
  FiniteActionFloor.ofLimitFloor w hw0 hw1 half (fullActionFloor w half)
    (fullActionFloor_pos hw0 hw1 half) (fullActionLimit_ge_floor w hw0 hw1 half)

theorem fullActionFloorCertificate_floor (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (half : Nat) :
    (fullActionFloorCertificate w hw0 hw1 half).floor = HalfPow.half * (HalfPow.half * fullActionFloor w half) := rfl

theorem fullActionFloorCertificate_cutoff (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (half : Nat) :
    (fullActionFloorCertificate w hw0 hw1 half).cutoff =
      actionCutoff w half (HalfPow.half * (HalfPow.half * fullActionFloor w half)) := rfl

theorem fullActionLimit_not_equiv_zero (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (half : Nat) :
    ¬ CReal.Equiv (fullActionLimit w hw0 hw1 half) (CReal.ofQ' 0) :=
  BF4ExactSlabAllExtentHeatUnitCertifiedNonzero.actionLimit_not_equiv_zero hw0 hw1
    (fullActionFloorCertificate w hw0 hw1 half)

/-- The actual original slab completion, not a surrogate Hilbert space. -/
theorem completedHeatUnit_norm_ne_zero (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (half : Nat) :
    (cutoffLimitCompletion w (Q'.le_of_lt hw0) half).hilbert.cinner
      (completedHeatUnit w hw0 hw1 half) (completedHeatUnit w hw0 hw1 half) ≠
      Quotient.mk CReal.crealSetoid (CReal.ofQ' 0) :=
  BF4ExactSlabAllExtentHeatUnitCertifiedNonzero.completedHeatUnit_norm_ne_zero hw0 hw1
    (fullActionFloorCertificate w hw0 hw1 half)

/-- The completed full heat unit is NON-NULL for every 0<w<1 and odd slab.
This does not identify it with a normalized or stationary physical vacuum. -/
theorem completedHeatUnit_ne_zero (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (half : Nat) :
    completedHeatUnit w hw0 hw1 half ≠
      cutoffLimitEmbed w (Q'.le_of_lt hw0) (BoundaryObservable.zero half) :=
  BF4ExactSlabAllExtentHeatUnitCertifiedNonzero.completedHeatUnit_ne_zero hw0 hw1
    (fullActionFloorCertificate w hw0 hw1 half)

end YMGap.Continuum.BF4ExactSlabOriginalActionStrictFloor

#print axioms YMGap.Continuum.BF4ExactSlabOriginalActionStrictFloor.productLimit_approx_floor
#print axioms YMGap.Continuum.BF4ExactSlabOriginalActionStrictFloor.productLimit_ge_floor
#print axioms YMGap.Continuum.BF4ExactSlabOriginalActionStrictFloor.fullActionFloor
#print axioms YMGap.Continuum.BF4ExactSlabOriginalActionStrictFloor.fullActionFloor_pos
#print axioms YMGap.Continuum.BF4ExactSlabOriginalActionStrictFloor.fullActionLimit_ge_floor
#print axioms YMGap.Continuum.BF4ExactSlabOriginalActionStrictFloor.fullActionFloorCertificate
#print axioms YMGap.Continuum.BF4ExactSlabOriginalActionStrictFloor.fullActionFloorCertificate_floor
#print axioms YMGap.Continuum.BF4ExactSlabOriginalActionStrictFloor.fullActionFloorCertificate_cutoff
#print axioms YMGap.Continuum.BF4ExactSlabOriginalActionStrictFloor.fullActionLimit_not_equiv_zero
#print axioms YMGap.Continuum.BF4ExactSlabOriginalActionStrictFloor.completedHeatUnit_norm_ne_zero
#print axioms YMGap.Continuum.BF4ExactSlabOriginalActionStrictFloor.completedHeatUnit_ne_zero
