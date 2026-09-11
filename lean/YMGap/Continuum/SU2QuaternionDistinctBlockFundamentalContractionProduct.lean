/-
# Distinct-block products of oriented fundamental contractions

The generic-block Schur theorem contracts one oppositely oriented
fundamental coefficient pair in the presence of a complex spectator which is
independent of that link.  This leaf iterates that theorem over a finite list
of pairwise distinct link blocks.

The raw product is deliberately parenthesized so that the list head is the
literal right factor

    productOver base (step :: steps)
      = productOver base steps * contraction(step).

Thus `step` is the next block contracted and the tail product is its
spectator.  The rational-complex Schur fold mirrors this parenthesization
exactly.  No raw associativity, commutativity, reordering, or unit law is
used.

An arbitrary `base` is retained.  For one elementary cube it may be the
canonical complex polynomial one.  For a two-cube network it can instead
carry the unresolved four-valent shared-link factor while all distinct
bivalent links are contracted around it.

## Representation fences

* `RatPoly` is a duplicate-preserving raw list carrier.  This file never
  transports a pointwise `RatPolyEqv` through `finiteProductHaar`.
* A face-ordered product is not silently reordered into the paired product
  below.  The Haar-facing trace summand must be defined in this canonical
  paired order, with physical pointwise evaluation proved separately.
* Repeated blocks are excluded.  A second factor on the selected block is not
  an independent spectator; such a four-valent block belongs to the later
  Racah calculation.
* The result is for one fixed Boolean-index summand.  It does not enumerate a
  trace-index family or unfold a global face product.
* All conclusions remain in `RationalComplexEqv`; the nested Schur-delta fold
  is not replaced by raw equality or a scalar power.

# Axiom gate

No `Classical`, choice, `sorry`/`admit`, `native_decide`, or custom axiom.
-/

import YMGap.Continuum.SU2QuaternionComplexRatPolyAlgebra

namespace YMGap.Continuum.SU2QuaternionDistinctBlockFundamentalContractionProduct

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFiniteProductHaarCarrier
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchur
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionGenericBlockPartialFundamentalSchur
open YMGap.Continuum.SU2QuaternionFundamentalMatrixSemantics
open YMGap.Continuum.SU2QuaternionComplexRatPolyAlgebra

/-! ## 1. One contraction step and exact schedule predicates -/

/-- One oppositely oriented fundamental coefficient pair on one quaternion
link block.  Link identifiers remain plain naturals; range and distinctness
proofs are schedule hypotheses rather than proof fields. -/
structure OrientedFundamentalContraction where
  block : Nat
  forwardRow : Bool
  forwardColumn : Bool
  reverseRow : Bool
  reverseColumn : Bool

/-- The honest complex polynomial carried by one contraction step. -/
def OrientedFundamentalContraction.polynomial
    (step : OrientedFundamentalContraction) : ComplexRatPoly :=
  orientedFundamentalLinkContraction step.block
    step.forwardRow step.forwardColumn step.reverseRow step.reverseColumn

/-- The exact crossed `1/2` Schur delta carried by one contraction step. -/
def OrientedFundamentalContraction.delta
    (step : OrientedFundamentalContraction) : RationalComplex :=
  orientedFundamentalSchurDelta
    step.forwardRow step.forwardColumn step.reverseRow step.reverseColumn

/-- Every scheduled physical link block belongs to the finite-product Haar
carrier. -/
def ContractionBlocksInRange
    (blockCount : Nat)
    (schedule : List OrientedFundamentalContraction) : Prop :=
  ∀ step, step ∈ schedule → step.block < blockCount

/-- No physical link block occurs twice in the bivalent contraction
schedule. -/
def ContractionBlocksNodup
    (schedule : List OrientedFundamentalContraction) : Prop :=
  (schedule.map fun step => step.block).Nodup

/-- The external base spectator is independent of every block which the
schedule will contract. -/
def ComplexBaseIndependentOfSchedule
    (base : ComplexRatPoly)
    (schedule : List OrientedFundamentalContraction) : Prop :=
  ∀ step, step ∈ schedule →
    ComplexQuaternionBlockIndependent step.block base

/-! ## 2. Right-local raw product and matching Schur-delta fold -/

/-- Right-local contraction product over an arbitrary external base.  The
head is intentionally multiplied on the right of the recursively built tail
spectator. -/
def contractionProductOver
    (base : ComplexRatPoly) :
    List OrientedFundamentalContraction → ComplexRatPoly
  | [] => base
  | step :: steps =>
      complexRatPolyMul (contractionProductOver base steps) step.polynomial

/-- Matching right-local fold of exact Schur deltas, using the canonical
rational-complex multiplication exported through the complex-algebra
facade. -/
def schurDeltaProductFrom
    (initial : RationalComplex) :
    List OrientedFundamentalContraction → RationalComplex
  | [] => initial
  | step :: steps =>
      YMGap.Continuum.SU2QuaternionFundamentalMatrixSemantics.rationalComplexMul
        (schurDeltaProductFrom initial steps) step.delta

/-- Pure contraction product based at the canonical complex polynomial one. -/
def fundamentalContractionProduct
    (schedule : List OrientedFundamentalContraction) : ComplexRatPoly :=
  contractionProductOver complexRatPolyOne schedule

/-- Pure exact delta product based at the canonical rational-complex one. -/
def schurDeltaProduct
    (schedule : List OrientedFundamentalContraction) : RationalComplex :=
  schurDeltaProductFrom rationalComplexOne schedule

/-! ## 3. Spectator independence invariant -/

/-- The canonical complex polynomial one is independent of every quaternion
block. -/
theorem complexRatPolyOne_blockIndependent (block : Nat) :
    ComplexQuaternionBlockIndependent block complexRatPolyOne := by
  exact ⟨quaternionBlockIndependent_polyOne block,
    quaternionBlockIndependent_polyZero block⟩

/-- A right-local product remains independent of `target` when its external
base is independent and every scheduled source block differs from `target`.

This is the exact induction invariant needed when the schedule head is
contracted: the tail product is a legal spectator for the head block. -/
theorem contractionProductOver_blockIndependent
    (target : Nat) (base : ComplexRatPoly) :
    ∀ schedule : List OrientedFundamentalContraction,
    ComplexQuaternionBlockIndependent target base →
    (∀ step, step ∈ schedule → step.block ≠ target) →
      ComplexQuaternionBlockIndependent target
        (contractionProductOver base schedule)
  | [], hbase, _ => hbase
  | step :: steps, hbase, havoid => by
      have htailAvoid :
          ∀ item, item ∈ steps → item.block ≠ target := by
        intro item hitem
        exact havoid item (List.mem_cons_of_mem step hitem)
      have hstepAvoid : step.block ≠ target :=
        havoid step List.mem_cons_self
      exact complexQuaternionBlockIndependent_mul
        (contractionProductOver_blockIndependent
          target base steps hbase htailAvoid)
        (complexQuaternionBlockIndependent_orientedFundamentalLinkContraction
          (source := step.block) (target := target) hstepAvoid
          step.forwardRow step.forwardColumn
          step.reverseRow step.reverseColumn)

/-! ## 4. Constructive value-level transport -/

/-- Changing the initial rational-complex value by componentwise equivalence
changes the entire mirrored Schur fold by componentwise equivalence. -/
theorem schurDeltaProductFrom_congr_initial
    {initial initial' : RationalComplex}
    (hinitial : RationalComplexEqv initial initial') :
    ∀ schedule : List OrientedFundamentalContraction,
      RationalComplexEqv
        (schurDeltaProductFrom initial schedule)
        (schurDeltaProductFrom initial' schedule)
  | [] => hinitial
  | step :: steps =>
      rationalComplexMul_congr
        (schurDeltaProductFrom_congr_initial hinitial steps)
        (rationalComplexEqv_refl step.delta)

/-! ## 5. Distinct-block contraction theorem -/

/-- **Finite distinct-block fundamental contraction with an arbitrary
base.**  Each schedule head is contracted against the recursively built tail
spectator.  Block distinctness supplies syntactic independence, while the
generic/canonical multiplication bridge transports the one-link theorem into
the public rational-complex algebra.

No associativity or commutativity of either raw polynomial multiplication or
rational-complex multiplication is needed: both sides use the same recursive
parenthesization. -/
theorem finiteProductHaarComplex_distinctFundamentalContractionProduct
    (blockCount : Nat) (base : ComplexRatPoly) :
    ∀ schedule : List OrientedFundamentalContraction,
    ContractionBlocksInRange blockCount schedule →
    ContractionBlocksNodup schedule →
    ComplexBaseIndependentOfSchedule base schedule →
      RationalComplexEqv
        (finiteProductHaarComplex blockCount
          (contractionProductOver base schedule))
        (schurDeltaProductFrom
          (finiteProductHaarComplex blockCount base) schedule)
  | [], _, _, _ =>
      rationalComplexEqv_refl
        (finiteProductHaarComplex blockCount base)
  | step :: steps, hrange, hnodup, hbase => by
      have hstepRange : step.block < blockCount :=
        hrange step List.mem_cons_self
      have htailRange : ContractionBlocksInRange blockCount steps := by
        intro item hitem
        exact hrange item (List.mem_cons_of_mem step hitem)
      have hnodupRaw := hnodup
      unfold ContractionBlocksNodup at hnodupRaw
      change
        (step.block ::
          List.map (fun item : OrientedFundamentalContraction =>
            item.block) steps).Nodup at hnodupRaw
      have hnodupParts := List.nodup_cons.mp hnodupRaw
      have htailNodup : ContractionBlocksNodup steps := by
        unfold ContractionBlocksNodup
        exact hnodupParts.2
      have hbaseStep :
          ComplexQuaternionBlockIndependent step.block base :=
        hbase step List.mem_cons_self
      have hbaseTail : ComplexBaseIndependentOfSchedule base steps := by
        intro item hitem
        exact hbase item (List.mem_cons_of_mem step hitem)
      have htailAvoid :
          ∀ item, item ∈ steps → item.block ≠ step.block := by
        intro item hitem heq
        apply hnodupParts.1
        rw [List.mem_map]
        exact ⟨item, hitem, heq⟩
      have hspectator :
          ComplexQuaternionBlockIndependent step.block
            (contractionProductOver base steps) :=
        contractionProductOver_blockIndependent
          step.block base steps hbaseStep htailAvoid
      have hhead :=
        YMGap.Continuum.SU2QuaternionGenericBlockPartialFundamentalSchur.genericBlock_oriented_fundamental_schur_with_complex_spectator
          blockCount step.block hstepRange
          (contractionProductOver base steps) hspectator
          step.forwardRow step.forwardColumn
          step.reverseRow step.reverseColumn
      have hbridge := generic_rationalComplexMul_eqv
        (finiteProductHaarComplex blockCount
          (contractionProductOver base steps))
        step.delta
      have htail :=
        finiteProductHaarComplex_distinctFundamentalContractionProduct
          blockCount base steps htailRange htailNodup hbaseTail
      have htransport := rationalComplexMul_congr htail
        (rationalComplexEqv_refl step.delta)
      exact rationalComplexEqv_trans hhead
        (rationalComplexEqv_trans hbridge htransport)

/-- **Pure distinct-block delta product.**  With canonical polynomial one as
the external base, the exact finite-product Haar value is the mirrored nested
product of the crossed one-link Schur deltas. -/
theorem finiteProductHaarComplex_fundamentalContractionProduct
    (blockCount : Nat)
    (schedule : List OrientedFundamentalContraction)
    (hrange : ContractionBlocksInRange blockCount schedule)
    (hnodup : ContractionBlocksNodup schedule) :
    RationalComplexEqv
      (finiteProductHaarComplex blockCount
        (fundamentalContractionProduct schedule))
      (schurDeltaProduct schedule) := by
  have hbase : ComplexBaseIndependentOfSchedule
      complexRatPolyOne schedule := by
    intro step _
    exact complexRatPolyOne_blockIndependent step.block
  have hproduct :=
    finiteProductHaarComplex_distinctFundamentalContractionProduct
      blockCount complexRatPolyOne schedule hrange hnodup hbase
  have hinitial := schurDeltaProductFrom_congr_initial
    (finiteProductHaarComplex_one blockCount) schedule
  exact rationalComplexEqv_trans hproduct hinitial

#print axioms complexRatPolyOne_blockIndependent
#print axioms contractionProductOver_blockIndependent
#print axioms schurDeltaProductFrom_congr_initial
#print axioms finiteProductHaarComplex_distinctFundamentalContractionProduct
#print axioms finiteProductHaarComplex_fundamentalContractionProduct

end YMGap.Continuum.SU2QuaternionDistinctBlockFundamentalContractionProduct
