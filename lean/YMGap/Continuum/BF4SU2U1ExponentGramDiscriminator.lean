/-
# Exact SU(2)/U(1) exponent-Gram discriminator

This module places the non-abelian and abelian BF4 block laws in one finite,
constructive comparison harness.

The SU(2) side uses the corrected-slab exponent-Gram entries and globally
link-glued physical pushforward from
`BF4ExponentGramMatchedOneStep`.  The U(1) side uses the identical slab
geometry, its signed-charge Haar law, and its direct four-face charge
pushforward from `BF4U1SameCarrierPushforward`.

For U(1), exponent groups are sums of `|q|^2` over lower-half faces.  Thus the
same list of pairs of natural exponents addresses Gram coordinates on both
sides, while each group retains the physically correct heat exponent.

Each side independently minimizes its exact pushed-versus-coarse finite Gram
distance over the same positive rational coupling atlas.  The result is a
`Type`-valued exact comparison certificate between the selected SU(2) and
U(1) couplings.

This decides every finite instance.  It does not assert the weak-coupling
sign uniformly in cutoff or spacing; that remains an analytic convergence
and separation theorem.

## Axiom gate

Finite lists and exact `Q'` arithmetic only.  No `Classical.*`,
`native_decide`, custom axiom, noncomputable declaration, or placeholder.
-/

import YMGap.Continuum.BF4ExponentGramMatchedOneStep
import YMGap.Continuum.BF4U1SameCarrierPushforward

namespace YMGap.Continuum.BF4SU2U1ExponentGramDiscriminator

set_option maxRecDepth 40000
set_option maxHeartbeats 8000000

open YMGap.Constructive
open YMGap.Continuum.BF4ExponentGramMatchedOneStep
open YMGap.Continuum.BF4ObservableMatchedOneStep
open YMGap.Continuum.BF4U1SameCarrierPushforward
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. U(1) exponent-grouped Gram on the shared carrier -/

def u1HeatExponentOn
    (ids : List Nat) (state : ChargeLabelling) : Nat :=
  match ids with
  | [] => 0
  | id :: tail =>
      chargeMagnitude (state id) * chargeMagnitude (state id) +
        u1HeatExponentOn tail state

def u1LowerHeatExponent
    (half : Nat) (state : ChargeLabelling) : Nat :=
  u1HeatExponentOn (centralLowerFaceIds half) state

def u1ExponentCoefficient
    (half exponent : Nat) (state : ChargeLabelling) : Q' :=
  if u1LowerHeatExponent half state = exponent then 1 else 0

def u1ExponentGramEntry
    (half : Nat)
    (states : List ChargeLabelling)
    (mass : ChargeLabelling → Q')
    (coordinate : ExponentGramCoordinate) : Q' :=
  reflectedLawBilinear half states mass
    (u1ExponentCoefficient half coordinate.leftExponent)
    (u1ExponentCoefficient half coordinate.rightExponent)

def u1BlockedExponentGramEntry
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (candidate : Q') (hcandidate : (0 : Q') < candidate)
    (fineChargeCutoff : Nat)
    (coordinate : ExponentGramCoordinate) : Q' :=
  let coarse :=
    coarseU1Data G candidate hcandidate fineChargeCutoff
  u1ExponentGramEntry G.coarseHalf coarse.states
    (u1BlockedMass G g hg candidate hcandidate fineChargeCutoff)
    coordinate

def u1CoarseExponentGramEntry
    (G : CutoffOneGeometry)
    (candidate : Q') (hcandidate : (0 : Q') < candidate)
    (fineChargeCutoff : Nat)
    (coordinate : ExponentGramCoordinate) : Q' :=
  let coarse :=
    coarseU1Data G candidate hcandidate fineChargeCutoff
  u1ExponentGramEntry G.coarseHalf coarse.states
    coarse.normalizedMass coordinate

def u1ExponentGramDistance
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (candidate : Q') (hcandidate : (0 : Q') < candidate)
    (fineChargeCutoff : Nat)
    (coordinates : List ExponentGramCoordinate) : Q' :=
  listQSum
    (fun coordinate =>
      Q'.abs
        (u1BlockedExponentGramEntry G g hg candidate hcandidate
            fineChargeCutoff coordinate +
          -(u1CoarseExponentGramEntry G candidate hcandidate
            fineChargeCutoff coordinate)))
    coordinates

/-! ## 2. U(1) finite Gram-matched selection -/

def atlasU1ExponentGramScore
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (atlas : PositiveCouplingAtlas)
    (fineChargeCutoff : Nat)
    (coordinates : List ExponentGramCoordinate)
    (candidate : Q') : Q' :=
  if hcandidate : candidate ∈ atlas.candidates then
    u1ExponentGramDistance G g hg candidate
      (atlas.candidate_pos hcandidate)
      fineChargeCutoff coordinates
  else 0

theorem atlasU1ExponentGramScore_of_mem
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (atlas : PositiveCouplingAtlas)
    (fineChargeCutoff : Nat)
    (coordinates : List ExponentGramCoordinate)
    (candidate : Q') (hcandidate : candidate ∈ atlas.candidates) :
    atlasU1ExponentGramScore G g hg atlas fineChargeCutoff
        coordinates candidate =
      u1ExponentGramDistance G g hg candidate
        (atlas.candidate_pos hcandidate)
        fineChargeCutoff coordinates := by
  unfold atlasU1ExponentGramScore
  rw [dif_pos hcandidate]

def u1ExponentGramMatchedCoupling
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (atlas : PositiveCouplingAtlas)
    (fineChargeCutoff : Nat)
    (coordinates : List ExponentGramCoordinate) : Q' :=
  (finiteArgmin
    (atlasU1ExponentGramScore G g hg atlas
      fineChargeCutoff coordinates)
    atlas.head atlas.tail).choice

theorem u1ExponentGramMatchedCoupling_mem
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (atlas : PositiveCouplingAtlas)
    (fineChargeCutoff : Nat)
    (coordinates : List ExponentGramCoordinate) :
    u1ExponentGramMatchedCoupling G g hg atlas
        fineChargeCutoff coordinates ∈ atlas.candidates := by
  exact finiteArgmin_choice_mem
    (atlasU1ExponentGramScore G g hg atlas
      fineChargeCutoff coordinates)
    atlas.head atlas.tail

theorem u1ExponentGramMatchedCoupling_pos
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (atlas : PositiveCouplingAtlas)
    (fineChargeCutoff : Nat)
    (coordinates : List ExponentGramCoordinate) :
    (0 : Q') <
      u1ExponentGramMatchedCoupling G g hg atlas
        fineChargeCutoff coordinates :=
  atlas.candidate_pos
    (u1ExponentGramMatchedCoupling_mem G g hg atlas
      fineChargeCutoff coordinates)

theorem u1ExponentGramMatchedCoupling_minimizes
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (atlas : PositiveCouplingAtlas)
    (fineChargeCutoff : Nat)
    (coordinates : List ExponentGramCoordinate)
    (candidate : Q') (hcandidate : candidate ∈ atlas.candidates) :
    u1ExponentGramDistance G g hg
        (u1ExponentGramMatchedCoupling G g hg atlas
          fineChargeCutoff coordinates)
        (u1ExponentGramMatchedCoupling_pos G g hg atlas
          fineChargeCutoff coordinates)
        fineChargeCutoff coordinates ≤
      u1ExponentGramDistance G g hg candidate
        (atlas.candidate_pos hcandidate)
        fineChargeCutoff coordinates := by
  have hminimal :=
    finiteArgmin_minimal
      (atlasU1ExponentGramScore G g hg atlas
        fineChargeCutoff coordinates)
      atlas.head atlas.tail candidate hcandidate
  change
    atlasU1ExponentGramScore G g hg atlas fineChargeCutoff coordinates
        (u1ExponentGramMatchedCoupling G g hg atlas
          fineChargeCutoff coordinates) ≤
      atlasU1ExponentGramScore G g hg atlas fineChargeCutoff coordinates
        candidate at hminimal
  rw [
    atlasU1ExponentGramScore_of_mem G g hg atlas fineChargeCutoff
      coordinates
      (u1ExponentGramMatchedCoupling G g hg atlas
        fineChargeCutoff coordinates)
      (u1ExponentGramMatchedCoupling_mem G g hg atlas
        fineChargeCutoff coordinates),
    atlasU1ExponentGramScore_of_mem G g hg atlas fineChargeCutoff
      coordinates candidate hcandidate
  ] at hminimal
  exact hminimal

/-! ## 3. Exact finite SU(2)/U(1) comparison -/

inductive SU2U1Comparison (su2 u1 : Q') : Type where
  | su2Below : su2 < u1 → SU2U1Comparison su2 u1
  | matched : su2 ≈ u1 → SU2U1Comparison su2 u1
  | su2Above : u1 < su2 → SU2U1Comparison su2 u1

private theorem q_eqv_of_neither_lt {left right : Q'}
    (hleft : ¬ left < right) (hright : ¬ right < left) :
    left ≈ right := by
  show
    left.num * (right.den : Int) =
      right.num * (left.den : Int)
  exact Int.le_antisymm (Int.not_lt.mp hright) (Int.not_lt.mp hleft)

/-- The exact finite discriminator.  Both couplings are derived from their
respective pushed physical laws by minimizing the same list of exponent-Gram
coordinates over the same atlas. -/
def su2U1ExponentGramComparison
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (atlas : PositiveCouplingAtlas)
    (fineChargeCutoff : Nat)
    (coordinates : List ExponentGramCoordinate) :
    SU2U1Comparison
      (exponentGramMatchedCoupling G g hg atlas coordinates)
      (u1ExponentGramMatchedCoupling G g hg atlas
        fineChargeCutoff coordinates) :=
  if hbelow :
      exponentGramMatchedCoupling G g hg atlas coordinates <
        u1ExponentGramMatchedCoupling G g hg atlas
          fineChargeCutoff coordinates then
    SU2U1Comparison.su2Below hbelow
  else if habove :
      u1ExponentGramMatchedCoupling G g hg atlas
          fineChargeCutoff coordinates <
        exponentGramMatchedCoupling G g hg atlas coordinates then
    SU2U1Comparison.su2Above habove
  else
    SU2U1Comparison.matched
      (q_eqv_of_neither_lt hbelow habove)

theorem su2U1ExponentGram_trichotomy
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (atlas : PositiveCouplingAtlas)
    (fineChargeCutoff : Nat)
    (coordinates : List ExponentGramCoordinate) :
    exponentGramMatchedCoupling G g hg atlas coordinates <
        u1ExponentGramMatchedCoupling G g hg atlas
          fineChargeCutoff coordinates ∨
      exponentGramMatchedCoupling G g hg atlas coordinates ≈
        u1ExponentGramMatchedCoupling G g hg atlas
          fineChargeCutoff coordinates ∨
      u1ExponentGramMatchedCoupling G g hg atlas
          fineChargeCutoff coordinates <
        exponentGramMatchedCoupling G g hg atlas coordinates := by
  cases su2U1ExponentGramComparison G g hg atlas
      fineChargeCutoff coordinates with
  | su2Below h => exact Or.inl h
  | matched h => exact Or.inr (Or.inl h)
  | su2Above h => exact Or.inr (Or.inr h)

end YMGap.Continuum.BF4SU2U1ExponentGramDiscriminator

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.BF4SU2U1ExponentGramDiscriminator.u1ExponentGramDistance
#print axioms YMGap.Continuum.BF4SU2U1ExponentGramDiscriminator.u1ExponentGramMatchedCoupling_mem
#print axioms YMGap.Continuum.BF4SU2U1ExponentGramDiscriminator.u1ExponentGramMatchedCoupling_pos
#print axioms YMGap.Continuum.BF4SU2U1ExponentGramDiscriminator.u1ExponentGramMatchedCoupling_minimizes
#print axioms YMGap.Continuum.BF4SU2U1ExponentGramDiscriminator.su2U1ExponentGramComparison
#print axioms YMGap.Continuum.BF4SU2U1ExponentGramDiscriminator.su2U1ExponentGram_trichotomy
