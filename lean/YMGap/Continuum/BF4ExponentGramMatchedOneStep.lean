/-
# Exponent-grouped reflected-Gram matching for one BF4 block

`BF4ObservableMatchedOneStep` matches expectations of pointwise functions on
full slab labellings.  A reflection Gram entry is not such an expectation:
it couples the lower restriction of a full labelling to its reflected upper
restriction.  This module supplies the missing common analytic carrier.

For an arbitrary finite rational law on the corrected-slab Cartesian state
space it defines:

* the reflected bilinear form of two lower-half coefficient functions;
* the heat/Casimir exponent of a lower-half SU(2) labelling;
* exact Gram entries obtained by grouping lower states by that exponent;
* a finite all-coordinate `L¹` discrepancy between the pushed cutoff-one law
  and a candidate normalized cutoff-four Gibbs law.

A constructive finite argmin then selects the candidate coupling minimizing
that genuine Gram discrepancy.  The coarse diagonal and every finite linear
combination of exponent profiles inherit the already-proved normalized
Osterwalder--Schrader positivity theorem.

The finite coordinate list is explicit data.  Increasing it is therefore an
honest spacing/cutoff approximation, rather than an implicit classical sum
over all labels.

## Axiom gate

Finite lists and exact `Q'` arithmetic only.  No `Classical.*`,
`native_decide`, custom axiom, noncomputable declaration, or placeholder.
-/

import YMGap.Continuum.BF4ObservableMatchedOneStep
import YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex

namespace YMGap.Continuum.BF4ExponentGramMatchedOneStep

set_option maxRecDepth 40000
set_option maxHeartbeats 8000000

open YMGap.Constructive
open YMGap.Continuum.BF4ObservableMatchedOneStep
open YMGap.Continuum.CompactDualCutoffOnePhysicalPushforward
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex

local infix:50 " ≈ " => Q'.eqv

abbrev SlabLabelling := EdgeLabelling

/-! ## 1. A reflected bilinear form for any finite law -/

/-- The reflected bilinear form carried by an arbitrary finite rational mass
on full corrected-slab labellings.  No positivity is assumed here. -/
def reflectedLawBilinear
    (half : Nat)
    (states : List SlabLabelling)
    (mass : SlabLabelling → Q')
    (leftCoefficient rightCoefficient : SlabLabelling → Q') : Q' :=
  listQSum
    (fun physical =>
      (leftCoefficient (centralLowerRestriction half physical) *
        rightCoefficient
          (centralReflectedUpperRestriction half physical)) *
        mass physical)
    states

/-- The quadratic specialization of `reflectedLawBilinear`. -/
def reflectedLawQuadratic
    (half : Nat)
    (states : List SlabLabelling)
    (mass : SlabLabelling → Q')
    (coefficient : SlabLabelling → Q') : Q' :=
  reflectedLawBilinear half states mass coefficient coefficient

/-! ## 2. Exact exponent grouping -/

/-- A constructive sum of the SU(2) heat exponents `c4(spin)` over a named
finite list of face identifiers. -/
def heatExponentOn
    (ids : List Nat) (state : SlabLabelling) : Nat :=
  match ids with
  | [] => 0
  | id :: tail => c4 (state id) + heatExponentOn tail state

/-- The total Casimir exponent on the lower half of a corrected slab. -/
def lowerHeatExponent (half : Nat) (state : SlabLabelling) : Nat :=
  heatExponentOn (centralLowerFaceIds half) state

/-- Characteristic coefficient of one exact lower-half exponent group. -/
def exponentCoefficient
    (half exponent : Nat) (state : SlabLabelling) : Q' :=
  if lowerHeatExponent half state = exponent then 1 else 0

/-- One coordinate of the exponent-grouped reflected Gram matrix. -/
structure ExponentGramCoordinate : Type where
  leftExponent : Nat
  rightExponent : Nat
  deriving DecidableEq

/-- One exponent-grouped Gram entry of an arbitrary finite law. -/
def exponentGramEntry
    (half : Nat)
    (states : List SlabLabelling)
    (mass : SlabLabelling → Q')
    (coordinate : ExponentGramCoordinate) : Q' :=
  reflectedLawBilinear half states mass
    (exponentCoefficient half coordinate.leftExponent)
    (exponentCoefficient half coordinate.rightExponent)

/-- Exact finite sum of rational coefficients indexed by heat exponent. -/
def exponentLinearCoefficient
    (half : Nat) (coefficients : List (Nat × Q'))
    (state : SlabLabelling) : Q' :=
  listQSum
    (fun entry =>
      entry.2 * exponentCoefficient half entry.1 state)
    coefficients

/-- Cartesian exponent coordinates through an inclusive exponent ceiling. -/
def exponentCoordinatesThrough
    (maximum : Nat) : List ExponentGramCoordinate :=
  (List.range (maximum + 1)).flatMap (fun left =>
    (List.range (maximum + 1)).map (fun right =>
      { leftExponent := left, rightExponent := right }))

/-- The largest possible lower-half heat exponent at spin cutoff `K`. -/
def lowerHeatExponentCeiling (K half : Nat) : Nat :=
  (centralLowerFaceIds half).length * c4 K

/-- The complete exponent-Gram coordinate list at a fixed physical cutoff.
This is the direct all-label regrouping: every bounded lower-half labelling
belongs to one of these exponent groups. -/
def completeExponentCoordinates
    (K half : Nat) : List ExponentGramCoordinate :=
  exponentCoordinatesThrough (lowerHeatExponentCeiling K half)

private theorem c4_mono_local {left right : Nat}
    (h : left ≤ right) : c4 left ≤ c4 right := by
  unfold c4
  exact Nat.mul_le_mul h (Nat.add_le_add_right h 2)

private theorem heatExponentOn_le
    (K : Nat) (state : SlabLabelling) :
    ∀ ids : List Nat,
      (∀ id, id ∈ ids → state id < K + 1) →
      heatExponentOn ids state ≤ ids.length * c4 K
  | [], _ => by simp [heatExponentOn]
  | id :: tail, hbounded => by
      have hid : state id ≤ K :=
        Nat.le_of_lt_succ (by
          simpa only [Nat.add_comm] using
            hbounded id List.mem_cons_self)
      have hhead : c4 (state id) ≤ c4 K :=
        c4_mono_local hid
      have htail : heatExponentOn tail state ≤ tail.length * c4 K :=
        heatExponentOn_le K state tail
          (fun item hitem =>
            hbounded item (List.mem_cons_of_mem id hitem))
      simp only [heatExponentOn, List.length_cons]
      calc
        c4 (state id) + heatExponentOn tail state
            ≤ c4 K + tail.length * c4 K :=
          Nat.add_le_add hhead htail
        _ = tail.length * c4 K + c4 K := Nat.add_comm _ _
        _ = (tail.length + 1) * c4 K := by
          rw [Nat.add_mul]
          simp

/-- Every cutoff-bounded lower state lands below the advertised complete
exponent ceiling. -/
theorem lowerHeatExponent_le_ceiling
    {K half : Nat} {state : SlabLabelling}
    (hstate : state ∈ boundedEdgeLabellings K
      (centralLowerFaceIds half)) :
    lowerHeatExponent half state ≤ lowerHeatExponentCeiling K half := by
  unfold lowerHeatExponent lowerHeatExponentCeiling
  exact heatExponentOn_le K state (centralLowerFaceIds half)
    (boundedEdgeLabellings_sound K
      (centralLowerFaceIds half) state hstate).1

/-- Hence the exponent label of every bounded lower state occurs in the
complete coordinate range. -/
theorem lowerHeatExponent_mem_completeRange
    {K half : Nat} {state : SlabLabelling}
    (hstate : state ∈ boundedEdgeLabellings K
      (centralLowerFaceIds half)) :
    lowerHeatExponent half state ∈
      List.range (lowerHeatExponentCeiling K half + 1) := by
  exact List.mem_range.mpr
    (Nat.lt_succ_of_le (lowerHeatExponent_le_ceiling hstate))

/-! ## 3. The pushed and coarse Gram entries on the same carrier -/

/-- Exponent-Gram entry of the actual globally link-glued cutoff-one
pushforward law at a candidate coarse coupling. -/
def blockedExponentGramEntry
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (candidate : Q') (hcandidate : (0 : Q') < candidate)
    (coordinate : ExponentGramCoordinate) : Q' :=
  let S := G.candidateScalePair g hg candidate hcandidate
  let K := physicalKernel S rfl hcandidate
  exponentGramEntry G.coarseHalf
    S.coarse.physicalLabellings K.blockedMass coordinate

/-- Exponent-Gram entry of the normalized cutoff-four coarse Gibbs law at
the same candidate coupling. -/
def coarseExponentGramEntry
    (G : CutoffOneGeometry)
    (candidate : Q') (hcandidate : (0 : Q') < candidate)
    (coordinate : ExponentGramCoordinate) : Q' :=
  let coarse := G.coarseData candidate hcandidate
  exponentGramEntry G.coarseHalf
    coarse.physicalLabellings coarse.normalizedMass coordinate

/-- Finite all-coordinate `L¹` distance between the pushed and coarse
exponent-Gram matrices.  Repetitions in `coordinates` are deliberately
counted, so a caller may attach integer multiplicities without extra scalar
machinery. -/
def exponentGramDistance
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (candidate : Q') (hcandidate : (0 : Q') < candidate)
    (coordinates : List ExponentGramCoordinate) : Q' :=
  listQSum
    (fun coordinate =>
      Q'.abs
        (blockedExponentGramEntry G g hg candidate hcandidate coordinate +
          -(coarseExponentGramEntry G candidate hcandidate coordinate)))
    coordinates

/-! ## 4. Constructive finite Gram-matched selection -/

def atlasExponentGramScore
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (atlas : PositiveCouplingAtlas)
    (coordinates : List ExponentGramCoordinate)
    (candidate : Q') : Q' :=
  if hcandidate : candidate ∈ atlas.candidates then
    exponentGramDistance G g hg candidate
      (atlas.candidate_pos hcandidate) coordinates
  else 0

theorem atlasExponentGramScore_of_mem
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (atlas : PositiveCouplingAtlas)
    (coordinates : List ExponentGramCoordinate)
    (candidate : Q') (hcandidate : candidate ∈ atlas.candidates) :
    atlasExponentGramScore G g hg atlas coordinates candidate =
      exponentGramDistance G g hg candidate
        (atlas.candidate_pos hcandidate) coordinates := by
  unfold atlasExponentGramScore
  rw [dif_pos hcandidate]

/-- The exact candidate minimizing the finite exponent-Gram discrepancy. -/
def exponentGramMatchedCoupling
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (atlas : PositiveCouplingAtlas)
    (coordinates : List ExponentGramCoordinate) : Q' :=
  (finiteArgmin
    (atlasExponentGramScore G g hg atlas coordinates)
    atlas.head atlas.tail).choice

theorem exponentGramMatchedCoupling_mem
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (atlas : PositiveCouplingAtlas)
    (coordinates : List ExponentGramCoordinate) :
    exponentGramMatchedCoupling G g hg atlas coordinates ∈
      atlas.candidates := by
  exact finiteArgmin_choice_mem
    (atlasExponentGramScore G g hg atlas coordinates)
    atlas.head atlas.tail

theorem exponentGramMatchedCoupling_pos
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (atlas : PositiveCouplingAtlas)
    (coordinates : List ExponentGramCoordinate) :
    (0 : Q') <
      exponentGramMatchedCoupling G g hg atlas coordinates :=
  atlas.candidate_pos
    (exponentGramMatchedCoupling_mem G g hg atlas coordinates)

theorem exponentGramMatchedCoupling_minimizes
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (atlas : PositiveCouplingAtlas)
    (coordinates : List ExponentGramCoordinate)
    (candidate : Q') (hcandidate : candidate ∈ atlas.candidates) :
    exponentGramDistance G g hg
        (exponentGramMatchedCoupling G g hg atlas coordinates)
        (exponentGramMatchedCoupling_pos G g hg atlas coordinates)
        coordinates ≤
      exponentGramDistance G g hg candidate
        (atlas.candidate_pos hcandidate) coordinates := by
  have hminimal :=
    finiteArgmin_minimal
      (atlasExponentGramScore G g hg atlas coordinates)
      atlas.head atlas.tail candidate hcandidate
  change
    atlasExponentGramScore G g hg atlas coordinates
        (exponentGramMatchedCoupling G g hg atlas coordinates) ≤
      atlasExponentGramScore G g hg atlas coordinates candidate at hminimal
  rw [
    atlasExponentGramScore_of_mem G g hg atlas coordinates
      (exponentGramMatchedCoupling G g hg atlas coordinates)
      (exponentGramMatchedCoupling_mem G g hg atlas coordinates),
    atlasExponentGramScore_of_mem G g hg atlas coordinates
      candidate hcandidate
  ] at hminimal
  exact hminimal

/-- The physical scale pair rebuilt from the exponent-Gram matched coupling. -/
def exponentGramMatchedScalePair
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (atlas : PositiveCouplingAtlas)
    (coordinates : List ExponentGramCoordinate) :
    CompactDualFiniteBlockRemainder.SlabScalePair :=
  G.candidateScalePair g hg
    (exponentGramMatchedCoupling G g hg atlas coordinates)
    (exponentGramMatchedCoupling_pos G g hg atlas coordinates)

@[simp] theorem exponentGramMatchedScalePair_coupling
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (atlas : PositiveCouplingAtlas)
    (coordinates : List ExponentGramCoordinate) :
    (exponentGramMatchedScalePair G g hg atlas coordinates).coarse.coupling =
      exponentGramMatchedCoupling G g hg atlas coordinates :=
  rfl

/-! ## 5. Coarse reflection positivity for exponent packets -/

/-- The generic reflected quadratic evaluated with the normalized physical
mass is exactly the pre-existing normalized full OS quadratic.  This is the
bridge that puts the matching entries and the reflection-positivity theorem
on one analytic carrier. -/
theorem reflectedNormalizedMassQuadratic_eq_OS
    (D : SlabPhysicalData)
    (coefficient : SlabLabelling → Q') :
    reflectedLawQuadratic D.half D.physicalLabellings
        D.normalizedMass coefficient ≈
      centralNormalizedFullPhysicalReflectionQuadratic
        D.coupling D.coupling_nonnegative D.cutoff D.half coefficient := by
  let reciprocal :=
    Q'.recipPos D.physicalPartition
      (slabParametricKPhysicalPartition_pos
        D.coupling_nonnegative D.cutoff D.extent)
  refine Q'.eqv_trans _
    (listQSum
      (fun physical =>
        ((coefficient (centralLowerRestriction D.half physical) *
            coefficient
              (centralReflectedUpperRestriction D.half physical)) *
          D.physicalTerm physical) * reciprocal)
      D.physicalLabellings) _ ?_ ?_
  · unfold reflectedLawQuadratic reflectedLawBilinear
      SlabPhysicalData.normalizedMass Q'.divPos
    apply listQSum_congr_on
    intro physical _
    exact Q'.eqv_symm
      (Q'.mul_assoc_eqv
        (coefficient (centralLowerRestriction D.half physical) *
          coefficient
            (centralReflectedUpperRestriction D.half physical))
        (D.physicalTerm physical) reciprocal)
  · refine Q'.eqv_trans _
      (D.fullReflectionQuadratic coefficient * reciprocal) _
      (listQSum_mul_right
        (fun physical =>
          (coefficient (centralLowerRestriction D.half physical) *
            coefficient
              (centralReflectedUpperRestriction D.half physical)) *
            D.physicalTerm physical)
        reciprocal D.physicalLabellings) ?_
    exact Q'.eqv_refl _

/-- The normalized coarse OS quadratic of an arbitrary finite linear
combination of exact heat-exponent groups. -/
def coarseExponentPacketQuadratic
    (G : CutoffOneGeometry)
    (candidate : Q') (hcandidate : (0 : Q') < candidate)
    (coefficients : List (Nat × Q')) : Q' :=
  let coarse := G.coarseData candidate hcandidate
  centralNormalizedFullPhysicalReflectionQuadratic
    coarse.coupling coarse.coupling_nonnegative
    coarse.cutoff coarse.half
    (exponentLinearCoefficient coarse.half coefficients)

/-- Every finite exponent packet is reflection positive in the exact
normalized coarse SU(2) Gibbs law. -/
theorem coarseExponentPacketQuadratic_nonnegative
    (G : CutoffOneGeometry)
    (candidate : Q') (hcandidate : (0 : Q') < candidate)
    (coefficients : List (Nat × Q')) :
    (0 : Q') ≤
      coarseExponentPacketQuadratic G candidate hcandidate coefficients := by
  exact centralNormalizedFullPhysicalReflectionQuadratic_nonnegative
    candidate (Q'.le_of_lt hcandidate) 4 G.coarseHalf
    (exponentLinearCoefficient G.coarseHalf coefficients)

/-- In particular, every diagonal exponent-grouped Gram entry of the coarse
law is nonnegative. -/
theorem coarseExponentGramDiagonal_nonnegative
    (G : CutoffOneGeometry)
    (candidate : Q') (hcandidate : (0 : Q') < candidate)
    (exponent : Nat) :
    (0 : Q') ≤
      coarseExponentPacketQuadratic G candidate hcandidate
        [(exponent, 1)] :=
  coarseExponentPacketQuadratic_nonnegative
    G candidate hcandidate [(exponent, 1)]

/-- The actual diagonal entry used by `exponentGramDistance` is
nonnegative—not merely an isomorphic auxiliary packet quadratic. -/
theorem coarseExponentGramEntry_diagonal_nonnegative
    (G : CutoffOneGeometry)
    (candidate : Q') (hcandidate : (0 : Q') < candidate)
    (exponent : Nat) :
    (0 : Q') ≤
      coarseExponentGramEntry G candidate hcandidate
        { leftExponent := exponent, rightExponent := exponent } := by
  let coarse := G.coarseData candidate hcandidate
  let coefficient := exponentCoefficient G.coarseHalf exponent
  have hOS :
      (0 : Q') ≤
        centralNormalizedFullPhysicalReflectionQuadratic
          coarse.coupling coarse.coupling_nonnegative
          coarse.cutoff coarse.half coefficient :=
    centralNormalizedFullPhysicalReflectionQuadratic_nonnegative
      coarse.coupling coarse.coupling_nonnegative
      coarse.cutoff coarse.half coefficient
  have heq :
      coarseExponentGramEntry G candidate hcandidate
          { leftExponent := exponent, rightExponent := exponent } ≈
        centralNormalizedFullPhysicalReflectionQuadratic
          coarse.coupling coarse.coupling_nonnegative
          coarse.cutoff coarse.half coefficient := by
    exact reflectedNormalizedMassQuadratic_eq_OS coarse coefficient
  exact Q'.le_trans' _ _ _ hOS (Q'.ge_of_eqv heq)

end YMGap.Continuum.BF4ExponentGramMatchedOneStep

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.BF4ExponentGramMatchedOneStep.reflectedLawBilinear
#print axioms YMGap.Continuum.BF4ExponentGramMatchedOneStep.exponentGramDistance
#print axioms YMGap.Continuum.BF4ExponentGramMatchedOneStep.exponentGramMatchedCoupling_mem
#print axioms YMGap.Continuum.BF4ExponentGramMatchedOneStep.exponentGramMatchedCoupling_pos
#print axioms YMGap.Continuum.BF4ExponentGramMatchedOneStep.exponentGramMatchedCoupling_minimizes
#print axioms YMGap.Continuum.BF4ExponentGramMatchedOneStep.exponentGramMatchedScalePair_coupling
#print axioms YMGap.Continuum.BF4ExponentGramMatchedOneStep.lowerHeatExponent_mem_completeRange
#print axioms YMGap.Continuum.BF4ExponentGramMatchedOneStep.reflectedNormalizedMassQuadratic_eq_OS
#print axioms YMGap.Continuum.BF4ExponentGramMatchedOneStep.coarseExponentPacketQuadratic_nonnegative
#print axioms YMGap.Continuum.BF4ExponentGramMatchedOneStep.coarseExponentGramDiagonal_nonnegative
#print axioms YMGap.Continuum.BF4ExponentGramMatchedOneStep.coarseExponentGramEntry_diagonal_nonnegative
