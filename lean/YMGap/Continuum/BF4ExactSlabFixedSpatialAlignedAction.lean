/-
# The aligned interior mask has exactly the smaller original chart law

Filter the larger selected chain by membership in the translated smaller
chain. Physical injectivity and the no-repetition properties prove that
this filtered order is a permutation of the literal translated list.
The exact numerator and partition permutation identities then transport
the SAME normalized finite values and all-cutoff expectations back to the
source chart, for every supported insertion with its explicit prefix pin.

The translation is spatial d and temporal 2*d, with source margin r and
target margin r+d at the same chart radius and time buffer. Only the
filtered target action is identified with the smaller chart. No equality
with the whole larger selected action, boundary-response estimate, or
cross-width limiting state is asserted.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialAlignedBoxes
import YMGap.Continuum.BF4ExactSlabTranslatedSelectedAction
import YMGap.Continuum.BF4ExactSlabMixedAction

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialAlignedAction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabFixedSpatialAlignedBoxes
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetReciprocal
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetExpectation
open YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit (eqv_close)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection

local infix:50 " ≈ " => Q'.eqv
local notation:max "blocks" extent:arg => List.length (boundaryCompleteSlabLinks extent)

/-- The actual membership mask shared with the mixed-action comparison. -/
def keep (base r d H t id : Nat) : Bool :=
  decide (id ∈ translatedChartIds base r d H t)

/-- The larger selected chain filtered by the translated smaller selection. -/
def insideIds (base r d H t : Nat) : List Nat :=
  BF4ExactSlabMixedAction.inside (keep base r d H t) (chartIds base (r+d) H t)

theorem keep_eq_true (base r d H t id : Nat) :
    keep base r d H t id = true ↔ id ∈ translatedChartIds base r d H t := by
  simp only [keep, decide_eq_true_eq]

theorem keep_eq_false (base r d H t id : Nat) :
    keep base r d H t id = false ↔ id ∉ translatedChartIds base r d H t := by
  simp only [keep, decide_eq_false_iff_not]

theorem translatedChartIds_nodup (base r d H t : Nat) :
    (translatedChartIds base r d H t).Nodup :=
  nodup_map_of_injOn _ _ (chartIds_nodup base r H t)
    (fun _ hi _ hj he => (placement base r d H t).faceId_injective
      (chartIds_physical hi) (chartIds_physical hj) he)

theorem insideIds_nodup (base r d H t : Nat) : (insideIds base r d H t).Nodup :=
  List.filter_sublist.nodup (chartIds_nodup base (r+d) H t)

/-- The target-chain membership condition follows from actual geometric inclusion. -/
theorem insideIds_mem_iff (base r d H t id : Nat) :
    id ∈ insideIds base r d H t ↔ id ∈ translatedChartIds base r d H t := by
  constructor
  · intro hi
    exact (keep_eq_true base r d H t id).mp (List.mem_filter.mp hi).2
  · intro hi
    exact List.mem_filter.mpr ⟨translatedChartIds_subset base r d H t hi,
      (keep_eq_true base r d H t id).mpr hi⟩

/-- Filtering changes only the order, not the actual selected face list. -/
theorem insideIds_perm (base r d H t : Nat) :
    (insideIds base r d H t).Perm (translatedChartIds base r d H t) :=
  perm_of_nodup_mem_iff _ _ (insideIds_nodup base r d H t)
    (translatedChartIds_nodup base r d H t) (insideIds_mem_iff base r d H t)

theorem insideIds_physical (base r d H t id : Nat)
    (hi : id ∈ insideIds base r d H t) :
    id ∈ slabPhysicalFaceEdges (chartExtent base (r+d) H t) :=
  chartIds_physical (List.mem_filter.mp hi).1

private theorem qmul {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h)
    (Q'.mul_eqv_congr_left _ _ _ k)

private theorem finiteValue_perm {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (extent : Nat)
    (xs ys : List Nat)
    (hx : ∀ id, id ∈ xs → id ∈ slabPhysicalFaceEdges extent)
    (hy : ∀ id, id ∈ ys → id ∈ slabPhysicalFaceEdges extent)
    (hperm : xs.Perm ys) (p : RatPoly) (stage : Nat) :
    finiteValue w hw0 hw1 extent xs hx p stage ≈
      finiteValue w hw0 hw1 extent ys hy p stage := by
  unfold finiteValue
  apply qmul (BF4ExactSlabMixedAction.moment_perm w _ extent p hperm)
  unfold reciprocalTerm PositiveRationalCauchyReciprocal.term partitionSample
  exact Q'.recipPos_eqv_congr _ _ _ _
    (BF4ExactSlabMixedAction.partition_perm w _ extent hperm)

/-- Exact normalized smaller-chart pin for the shared filtered target action.
Both sides use cutoff headCutoff(w)+stage and their actual same-action reciprocal. -/
theorem finiteValue_pin {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (base r d H t : Nat)
    (p : RatPoly) (hp : SupportedQuaternionBlocks (blocks (chartExtent base r H t)) p)
    (q : RatPoly) (hq : SupportedQuaternionBlocks (blocks (chartExtent base (r+d) H t)) q)
    (he : QuaternionPrefixPolynomialEqv (blocks (chartExtent base (r+d) H t))
      ((placement base r d H t).embedding.polynomial p) q) (stage : Nat) :
    finiteValue w hw0 hw1 (chartExtent base (r+d) H t) (insideIds base r d H t)
      (insideIds_physical base r d H t) q stage ≈
      finiteValue w hw0 hw1 (chartExtent base r H t) (chartIds base r H t)
        (fun _ hi => chartIds_physical hi) p stage := by
  exact Q'.eqv_trans _ _ _
    (finiteValue_perm hw0 hw1 (chartExtent base (r+d) H t)
      (insideIds base r d H t) (translatedChartIds base r d H t)
      (insideIds_physical base r d H t)
      (BF4ExactSlabTranslatedSelectedAction.selectedIds_physical
        (placement base r d H t) (chartIds base r H t) (fun _ hi => chartIds_physical hi))
      (insideIds_perm base r d H t) q stage)
    (BF4ExactSlabTranslatedSelectedAction.finiteValue_pin_of_prefix
      (placement base r d H t) hw0 hw1 (chartIds base r H t)
      (fun _ hi => chartIds_physical hi) p hp q hq he stage)

/-- All-cutoff equality of the actual filtered target expectation and source chart.
The existing explicit Cauchy data are retained on each side. -/
theorem expectation_pin {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (base r d H t : Nat)
    (p : RatPoly) (hp : SupportedQuaternionBlocks (blocks (chartExtent base r H t)) p)
    (q : RatPoly) (hq : SupportedQuaternionBlocks (blocks (chartExtent base (r+d) H t)) q)
    (he : QuaternionPrefixPolynomialEqv (blocks (chartExtent base (r+d) H t))
      ((placement base r d H t).embedding.polynomial p) q) :
    Equiv (expectation w hw0 hw1 (chartExtent base (r+d) H t) (insideIds base r d H t)
      (insideIds_physical base r d H t) q)
      (expectation w hw0 hw1 (chartExtent base r H t) (chartIds base r H t)
        (fun _ hi => chartIds_physical hi) p) :=
  Equiv_of_ofQ'_limit_close (finite_converges w hw0 hw1 _ _ _ _)
    (finite_converges w hw0 hw1 _ _ _ _)
    (fun epsilon hepsilon => ⟨0, fun stage _ => eqv_close
      (finiteValue_pin hw0 hw1 base r d H t p hp q hq he stage) epsilon hepsilon⟩)

end YMGap.Continuum.BF4ExactSlabFixedSpatialAlignedAction

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialAlignedAction.keep
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialAlignedAction.insideIds
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialAlignedAction.keep_eq_true
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialAlignedAction.keep_eq_false
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialAlignedAction.translatedChartIds_nodup
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialAlignedAction.insideIds_nodup
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialAlignedAction.insideIds_mem_iff
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialAlignedAction.insideIds_perm
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialAlignedAction.insideIds_physical
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialAlignedAction.finiteValue_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialAlignedAction.expectation_pin
