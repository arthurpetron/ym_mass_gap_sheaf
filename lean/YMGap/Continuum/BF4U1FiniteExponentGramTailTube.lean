/-
# Finite-coordinate U(1) exponent-Gram tail tubes

`BF4U1SignedChargeTailInstantiation` gives an explicit charge cutoff for a
single diagonal exponent-Gram entry.  This module extends the same fixed-slab
argument to every `ExponentGramCoordinate`, sums the absolute errors over an
arbitrary finite coordinate list, and pays the coordinate cardinality inside
the cutoff.

The last section treats a finite positive coupling atlas.  The normalized
U(1) slab may vary with the atlas candidate.  A recursive natural-number
maximum combines the candidate-wise cutoffs into one common cutoff, producing
an actual `AtlasScoreTube` for the finite-coordinate distance from a fixed
reference Gram vector.

## Honest scope

The reference vector is fixed across the atlas.  Applying this tube directly
to `atlasU1ExponentGramScore` still requires an identification of its blocked
entry with a candidate-independent reference entry (or a second tail tube for
that changing entry).  No such block-independence statement, weak-coupling
separator, spacing-uniform estimate, or physical AF trajectory is asserted
here.

All constructions use finite lists, exact `Q'` order, and explicit recursive
cutoffs.  There is no `Classical.*`, `Real`, `native_decide`, custom axiom,
noncomputable declaration, or placeholder.
-/

import YMGap.Continuum.BF4U1SignedChargeTailInstantiation
import YMGap.Continuum.BF4ExponentGramLocatedStability
import YMGap.Continuum.Z4FiniteCylinderQuadraticStability

namespace YMGap.Continuum.BF4U1FiniteExponentGramTailTube

set_option maxRecDepth 50000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Constructive.ExpNeg
open YMGap.Continuum.BF4ExponentGramLocatedStability
open YMGap.Continuum.BF4ExponentGramMatchedOneStep
open YMGap.Continuum.BF4ObservableMatchedOneStep
open YMGap.Continuum.BF4SU2U1ExponentGramDiscriminator
open YMGap.Continuum.BF4U1ExponentGramCutoffTailBridge
open YMGap.Continuum.BF4U1SameCarrierPushforward
open YMGap.Continuum.BF4U1SignedChargeTailInstantiation
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Finite-sum and absolute-value helpers -/

private theorem listQSum_le_length_mul_local
    {A : Type} (value : A → Q')
    {bound : Q'} (hbound0 : (0 : Q') ≤ bound) :
    ∀ items : List A,
      (∀ item, item ∈ items → value item ≤ bound) →
      listQSum value items ≤ Q'.ofNat items.length * bound
  | [], _ => by
      exact Q'.le_of_eqv
        (Q'.eqv_symm (Q'.zero_mul_eqv bound))
  | head :: rest, hbound => by
      have hhead := hbound head List.mem_cons_self
      have hrest :=
        listQSum_le_length_mul_local value hbound0 rest
          (fun item hitem =>
            hbound item (List.mem_cons_of_mem head hitem))
      have hsum :
          value head + listQSum value rest ≤
            bound + Q'.ofNat rest.length * bound :=
        Q'.add_le_add hhead hrest
      have htarget :
          bound + Q'.ofNat rest.length * bound ≈
            Q'.ofNat (head :: rest).length * bound := by
        refine Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_right
            bound ((1 : Q') * bound)
            (Q'.ofNat rest.length * bound)
            (Q'.eqv_symm (Q'.one_mul_eqv bound))) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.eqv_symm
            (Q'.add_mul_eqv 1 (Q'.ofNat rest.length) bound)) ?_
        apply Q'.mul_eqv_congr_right
        exact Q'.eqv_trans _ _ _
          (Q'.add_comm_eqv 1 (Q'.ofNat rest.length))
          (Q'.eqv_symm
            (YMGap.Continuum.HKConvGen.ofNat_succ_eqv rest.length))
      exact Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv htarget)

private theorem sub_add_rearrange
    (a a' b b' : Q') :
    ((a + a') + (-(b + b'))) ≈
      ((a + (-b)) + (a' + (-b'))) := by
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left
      (a + a') _ _ (Q'.neg_add_eqv b b')) ?_
  exact Q'.add_swap_inner a a' (-b) (-b')

private theorem same_reference_sub_eqv
    (a b reference : Q') :
    ((a + (-reference)) + (-(b + (-reference)))) ≈
      a + (-b) := by
  refine Q'.eqv_trans _ _ _
    (sub_add_rearrange a (-reference) b (-reference)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (a + (-b))
      ((-reference) + (-(-reference))) 0 ?_) ?_
  · refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (-reference)
        (-(-reference)) reference
        (Q'.neg_neg_eqv reference)) ?_
    exact Q'.neg_add_self_eqv reference
  · exact Q'.eqv_of_eq (Q'.add_zero' (a + (-b)))

/-- Taking the distance to a fixed rational reference is one-Lipschitz. -/
theorem abs_distance_to_reference_lipschitz
    (a b reference : Q') :
    Q'.abs
        (Q'.abs (a + (-reference)) +
          (-Q'.abs (b + (-reference)))) ≤
      Q'.abs (a + (-b)) := by
  have hab :
      Q'.abs (a + (-reference)) ≤
        Q'.abs (b + (-reference)) +
          Q'.abs (a + (-b)) := by
    have htriangle :=
      Q'.abs_le_abs_add_abs_sub
        (a + (-reference)) (b + (-reference))
    exact Q'.le_trans' _ _ _ htriangle
      (Q'.add_le_add_left
        (Q'.abs (b + (-reference))) _ _
        (Q'.le_of_eqv
          (Q'.abs_eqv_congr
            (same_reference_sub_eqv a b reference))))
  have hba :
      Q'.abs (b + (-reference)) ≤
        Q'.abs (a + (-reference)) +
          Q'.abs (a + (-b)) := by
    have htriangle :=
      Q'.abs_le_abs_add_abs_sub
        (b + (-reference)) (a + (-reference))
    have hsame :
        Q'.abs
            ((b + (-reference)) +
              (-(a + (-reference)))) ≤
          Q'.abs (a + (-b)) := by
      refine Q'.le_trans' _ _ _
        (Q'.le_of_eqv
          (Q'.abs_eqv_congr
            (same_reference_sub_eqv b a reference))) ?_
      exact Q'.le_of_eqv
        (YMGap.Constructive.ExpNeg.abs_sub_comm b a)
    exact Q'.le_trans' _ _ _ htriangle
      (Q'.add_le_add_left
        (Q'.abs (a + (-reference))) _ _ hsame)
  exact CReal.abs_sub_le_of_bounds hab hba

/-! ## 2. Arbitrary-coordinate fixed-slab cutoff -/

/-- Same-carrier charge cutoff for one arbitrary exponent-Gram coordinate. -/
def u1ExponentGramCoordinateChargeCutoff
    (D : U1SlabData)
    (coordinate : ExponentGramCoordinate)
    (cutoff : Nat) : Q' :=
  listQSum
    (fun physical =>
      if u1StateWithinChargeCutoff D cutoff physical then
        (u1ExponentCoefficient D.half coordinate.leftExponent
              (centralLowerRestriction D.half physical) *
            u1ExponentCoefficient D.half coordinate.rightExponent
              (centralReflectedUpperRestriction D.half physical)) *
          D.normalizedMass physical
      else 0)
    D.states

/-- The complementary omitted part of one arbitrary coordinate. -/
def u1ExponentGramCoordinateOmitted
    (D : U1SlabData)
    (coordinate : ExponentGramCoordinate)
    (cutoff : Nat) : Q' :=
  listQSum
    (fun physical =>
      if u1StateWithinChargeCutoff D cutoff physical then 0
      else
        (u1ExponentCoefficient D.half coordinate.leftExponent
              (centralLowerRestriction D.half physical) *
            u1ExponentCoefficient D.half coordinate.rightExponent
              (centralReflectedUpperRestriction D.half physical)) *
          D.normalizedMass physical)
    D.states

theorem coordinateCutoff_add_omitted_eqv_entry
    (D : U1SlabData)
    (coordinate : ExponentGramCoordinate)
    (cutoff : Nat) :
    u1ExponentGramCoordinateChargeCutoff D coordinate cutoff +
        u1ExponentGramCoordinateOmitted D coordinate cutoff ≈
      u1ExponentGramEntry
        D.half D.states D.normalizedMass coordinate := by
  unfold u1ExponentGramCoordinateChargeCutoff
    u1ExponentGramCoordinateOmitted
    u1ExponentGramEntry reflectedLawBilinear
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (listQSum_add
        (fun physical =>
          if u1StateWithinChargeCutoff D cutoff physical then
            (u1ExponentCoefficient D.half coordinate.leftExponent
                  (centralLowerRestriction D.half physical) *
                u1ExponentCoefficient D.half coordinate.rightExponent
                  (centralReflectedUpperRestriction D.half physical)) *
              D.normalizedMass physical
          else 0)
        (fun physical =>
          if u1StateWithinChargeCutoff D cutoff physical then 0
          else
            (u1ExponentCoefficient D.half coordinate.leftExponent
                  (centralLowerRestriction D.half physical) *
                u1ExponentCoefficient D.half coordinate.rightExponent
                  (centralReflectedUpperRestriction D.half physical)) *
              D.normalizedMass physical)
        D.states)) ?_
  apply listQSum_congr_on
  intro physical _
  cases hwithin :
      u1StateWithinChargeCutoff D cutoff physical
  · exact Q'.eqv_of_eq (Q'.zero_add' _)
  · exact Q'.eqv_of_eq (Q'.add_zero' _)

theorem u1ExponentGramCoordinateOmitted_nonnegative
    (D : U1SlabData)
    (coordinate : ExponentGramCoordinate)
    (cutoff : Nat) :
    (0 : Q') ≤
      u1ExponentGramCoordinateOmitted D coordinate cutoff := by
  unfold u1ExponentGramCoordinateOmitted
  apply listQSum_nonnegative_on
  intro physical _
  cases hwithin :
      u1StateWithinChargeCutoff D cutoff physical
  · exact Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _
        (u1ExponentCoefficient_nonnegative
          D.half coordinate.leftExponent _)
        (u1ExponentCoefficient_nonnegative
          D.half coordinate.rightExponent _))
      (D.normalizedMass_nonnegative physical)
  · exact Q'.le_refl' 0

private theorem exponentCoefficient_product_le_one
    (D : U1SlabData)
    (coordinate : ExponentGramCoordinate)
    (physical : ChargeLabelling) :
    u1ExponentCoefficient D.half coordinate.leftExponent
          (centralLowerRestriction D.half physical) *
        u1ExponentCoefficient D.half coordinate.rightExponent
          (centralReflectedUpperRestriction D.half physical) ≤
      (1 : Q') := by
  have hright0 :=
    u1ExponentCoefficient_nonnegative
      D.half coordinate.rightExponent
      (centralReflectedUpperRestriction D.half physical)
  have hleft1 :=
    u1ExponentCoefficient_le_one
      D.half coordinate.leftExponent
      (centralLowerRestriction D.half physical)
  have hright1 :=
    u1ExponentCoefficient_le_one
      D.half coordinate.rightExponent
      (centralReflectedUpperRestriction D.half physical)
  have hscaled :
      u1ExponentCoefficient D.half coordinate.leftExponent
            (centralLowerRestriction D.half physical) *
          u1ExponentCoefficient D.half coordinate.rightExponent
            (centralReflectedUpperRestriction D.half physical) ≤
        (1 : Q') *
          u1ExponentCoefficient D.half coordinate.rightExponent
            (centralReflectedUpperRestriction D.half physical) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hleft1 hright0
  exact Q'.le_trans' _ _ _ hscaled
    (Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.one_mul_eqv _)) hright1)

/-- The omitted mass of every arbitrary coordinate obeys the same
carrier-amplified one-charge tail as a diagonal coordinate. -/
theorem u1ExponentGramCoordinateOmitted_le
    (D : U1SlabData)
    (hcoupling : D.coupling ≤ (1 : Q'))
    (tailData : OneChargeTail D)
    (coordinate : ExponentGramCoordinate)
    (cutoff : Nat) :
    u1ExponentGramCoordinateOmitted D coordinate cutoff ≤
      Q'.ofNat D.states.length * tailData.tail cutoff := by
  unfold u1ExponentGramCoordinateOmitted
  apply listQSum_le_length_mul_local
    _ (tailData.tail_nonnegative cutoff)
  intro physical _
  cases hwithin :
      u1StateWithinChargeCutoff D cutoff physical
  · have hmass0 := D.normalizedMass_nonnegative physical
    have hscaled :
        (u1ExponentCoefficient D.half coordinate.leftExponent
              (centralLowerRestriction D.half physical) *
            u1ExponentCoefficient D.half coordinate.rightExponent
              (centralReflectedUpperRestriction D.half physical)) *
            D.normalizedMass physical ≤
          (1 : Q') * D.normalizedMass physical :=
      Q'.mul_le_mul_of_nonneg_right _ _ _
        (exponentCoefficient_product_le_one D coordinate physical)
        hmass0
    have hmassTail :=
      u1NormalizedMass_le_oneChargeTail_of_outside
        D hcoupling tailData cutoff physical hwithin
    exact Q'.le_trans' _ _ _ hscaled
      (Q'.le_trans' _ _ _
        (Q'.le_of_eqv
          (Q'.one_mul_eqv (D.normalizedMass physical)))
        hmassTail)
  · exact Q'.le_trans' _ _ _
      (Q'.le_refl' 0)
      (tailData.tail_nonnegative cutoff)

/-- Absolute arbitrary-coordinate error for a supplied one-charge tail. -/
theorem u1ExponentGramCoordinateChargeCutoff_abs_tail
    (D : U1SlabData)
    (hcoupling : D.coupling ≤ (1 : Q'))
    (tailData : OneChargeTail D)
    (coordinate : ExponentGramCoordinate)
    (cutoff : Nat) :
    Q'.abs
        (u1ExponentGramCoordinateChargeCutoff D coordinate cutoff +
          (-u1ExponentGramEntry
            D.half D.states D.normalizedMass coordinate)) ≤
      Q'.ofNat D.states.length * tailData.tail cutoff := by
  let error :=
    Q'.ofNat D.states.length * tailData.tail cutoff
  have hsplit :=
    coordinateCutoff_add_omitted_eqv_entry
      D coordinate cutoff
  have homitted0 :=
    u1ExponentGramCoordinateOmitted_nonnegative
      D coordinate cutoff
  have homitted :=
    u1ExponentGramCoordinateOmitted_le
      D hcoupling tailData coordinate cutoff
  have hcutoff_le_entry :
      u1ExponentGramCoordinateChargeCutoff D coordinate cutoff ≤
        u1ExponentGramEntry
          D.half D.states D.normalizedMass coordinate := by
    exact Q'.le_trans' _ _ _
      (Q'.add_le_self_of_nonneg
        (u1ExponentGramCoordinateChargeCutoff D coordinate cutoff)
        (u1ExponentGramCoordinateOmitted D coordinate cutoff)
        homitted0)
      (Q'.le_of_eqv hsplit)
  have hentry_le_cutoff_error :
      u1ExponentGramEntry
          D.half D.states D.normalizedMass coordinate ≤
        u1ExponentGramCoordinateChargeCutoff D coordinate cutoff +
          error := by
    exact Q'.le_trans' _ _ _
      (Q'.ge_of_eqv hsplit)
      (Q'.add_le_add_left
        (u1ExponentGramCoordinateChargeCutoff D coordinate cutoff)
        _ _ homitted)
  have herror0 : (0 : Q') ≤ error :=
    Q'.mul_nonneg _ _
      (Q'.le_of_lt
        (u1StateCarrierScale_pos D))
      (tailData.tail_nonnegative cutoff)
  apply CReal.abs_sub_le_of_bounds
  · exact Q'.le_trans' _ _ _ hcutoff_le_entry
      (Q'.add_le_self_of_nonneg
        (u1ExponentGramEntry
          D.half D.states D.normalizedMass coordinate)
        error herror0)
  · exact hentry_le_cutoff_error

/-- The explicit signed-charge modulus for every exponent-Gram coordinate,
not only diagonal entries. -/
theorem u1ExponentGramCoordinateSignedChargeCutoff_abs_modulus
    (D : U1SlabData)
    (hw0 : (0 : Q') < D.coupling)
    (hw1 : D.coupling < (1 : Q'))
    (coordinate : ExponentGramCoordinate)
    (ε : Q') (hε : (0 : Q') < ε)
    (M : Nat)
    (hM : signedChargeCarrierCutoff D ε ≤ M) :
    Q'.abs
        (u1ExponentGramCoordinateChargeCutoff D coordinate M +
          (-u1ExponentGramEntry
            D.half D.states D.normalizedMass coordinate)) ≤
      ε := by
  let tailData :=
    signedChargeOneChargeTailModulus D hw0 hw1
  exact Q'.le_trans' _ _ _
    (u1ExponentGramCoordinateChargeCutoff_abs_tail
      D (Q'.le_of_lt hw1) tailData.toOneChargeTail coordinate M)
    (tailData.scaled_tail ε hε M hM)

/-! ## 3. Finite-coordinate total L1 error -/

/-- Sum of the absolute arbitrary-coordinate cutoff errors. -/
def u1ExponentGramFiniteCoordinateL1Error
    (D : U1SlabData)
    (coordinates : List ExponentGramCoordinate)
    (cutoff : Nat) : Q' :=
  listQSum
    (fun coordinate =>
      Q'.abs
        (u1ExponentGramCoordinateChargeCutoff D coordinate cutoff +
          (-u1ExponentGramEntry
            D.half D.states D.normalizedMass coordinate)))
    coordinates

/-- Per-coordinate tolerance after reserving one extra positive unit.  The
extra unit makes the denominator positive even for the empty list. -/
def finiteCoordinateTolerance
    (coordinates : List ExponentGramCoordinate)
    (ε : Q') : Q' :=
  YMGap.Continuum.HKConv.divPos ε
    (Q'.ofNat (coordinates.length + 1))

/-- One explicit charge cutoff paying both the slab-state and coordinate
cardinalities. -/
def finiteCoordinateSignedChargeCutoff
    (D : U1SlabData)
    (coordinates : List ExponentGramCoordinate)
    (ε : Q') : Nat :=
  signedChargeCarrierCutoff D
    (finiteCoordinateTolerance coordinates ε)

theorem finiteCoordinateTolerance_pos
    (coordinates : List ExponentGramCoordinate)
    {ε : Q'} (hε : (0 : Q') < ε) :
    (0 : Q') < finiteCoordinateTolerance coordinates ε :=
  YMGap.Continuum.HKConv.divPos_pos
    (CReal.num_pos_of_pos hε)

theorem coordinateScale_mul_tolerance_eqv
    (coordinates : List ExponentGramCoordinate)
    (ε : Q') :
    Q'.ofNat (coordinates.length + 1) *
        finiteCoordinateTolerance coordinates ε ≈
      ε := by
  unfold finiteCoordinateTolerance
  refine Q'.eqv_trans _ _ _
    (Q'.mul_comm_eqv
      (Q'.ofNat (coordinates.length + 1))
      (YMGap.Continuum.HKConv.divPos ε
        (Q'.ofNat (coordinates.length + 1)))) ?_
  exact YMGap.Continuum.HKConv.divPos_mul_eqv
    (CReal.num_pos_of_pos
      (Q'.ofNat_succ_pos coordinates.length))

/-- The explicit combined cutoff makes the complete finite-coordinate L1
error at most the requested positive tolerance. -/
theorem u1ExponentGramFiniteCoordinateL1Error_le
    (D : U1SlabData)
    (hw0 : (0 : Q') < D.coupling)
    (hw1 : D.coupling < (1 : Q'))
    (coordinates : List ExponentGramCoordinate)
    (ε : Q') (hε : (0 : Q') < ε)
    (M : Nat)
    (hM :
      finiteCoordinateSignedChargeCutoff D coordinates ε ≤ M) :
    u1ExponentGramFiniteCoordinateL1Error D coordinates M ≤ ε := by
  let δ := finiteCoordinateTolerance coordinates ε
  have hδpos : (0 : Q') < δ :=
    finiteCoordinateTolerance_pos coordinates hε
  have hper :
      ∀ coordinate,
        coordinate ∈ coordinates →
        Q'.abs
            (u1ExponentGramCoordinateChargeCutoff D coordinate M +
              (-u1ExponentGramEntry
                D.half D.states D.normalizedMass coordinate)) ≤
          δ := by
    intro coordinate _
    exact
      u1ExponentGramCoordinateSignedChargeCutoff_abs_modulus
        D hw0 hw1 coordinate δ hδpos M hM
  have hsum :
      u1ExponentGramFiniteCoordinateL1Error D coordinates M ≤
        Q'.ofNat coordinates.length * δ := by
    unfold u1ExponentGramFiniteCoordinateL1Error
    exact listQSum_le_length_mul_local
      _ (Q'.le_of_lt hδpos) coordinates hper
  have hscale :
      Q'.ofNat coordinates.length * δ ≤
        Q'.ofNat (coordinates.length + 1) * δ :=
    Q'.mul_le_mul_of_nonneg_right _ _ _
      (CReal.ofNat_le_ofNat (by omega))
      (Q'.le_of_lt hδpos)
  exact Q'.le_trans' _ _ _ hsum
    (Q'.le_trans' _ _ _ hscale
      (Q'.le_of_eqv
        (coordinateScale_mul_tolerance_eqv coordinates ε)))

/-! ## 4. Fixed-reference finite-coordinate score -/

def fixedReferenceExponentGramScore
    (D : U1SlabData)
    (reference : ExponentGramCoordinate → Q')
    (coordinates : List ExponentGramCoordinate) : Q' :=
  listQSum
    (fun coordinate =>
      Q'.abs
        (u1ExponentGramEntry
            D.half D.states D.normalizedMass coordinate +
          (-reference coordinate)))
    coordinates

def fixedReferenceExponentGramCutoffScore
    (D : U1SlabData)
    (reference : ExponentGramCoordinate → Q')
    (coordinates : List ExponentGramCoordinate)
    (cutoff : Nat) : Q' :=
  listQSum
    (fun coordinate =>
      Q'.abs
        (u1ExponentGramCoordinateChargeCutoff D coordinate cutoff +
          (-reference coordinate)))
    coordinates

theorem fixedReferenceExponentGramScore_abs_error
    (D : U1SlabData)
    (reference : ExponentGramCoordinate → Q')
    (coordinates : List ExponentGramCoordinate)
    (cutoff : Nat) :
    Q'.abs
        (fixedReferenceExponentGramCutoffScore
            D reference coordinates cutoff +
          (-fixedReferenceExponentGramScore
            D reference coordinates)) ≤
      u1ExponentGramFiniteCoordinateL1Error
        D coordinates cutoff := by
  have hsum :=
    abs_listQSum_sub_le
      (fun coordinate =>
        Q'.abs
          (u1ExponentGramCoordinateChargeCutoff
              D coordinate cutoff +
            (-reference coordinate)))
      (fun coordinate =>
        Q'.abs
          (u1ExponentGramEntry
              D.half D.states D.normalizedMass coordinate +
            (-reference coordinate)))
      coordinates
  refine Q'.le_trans' _ _ _ hsum ?_
  unfold u1ExponentGramFiniteCoordinateL1Error
  apply listQSum_mono
  intro coordinate _
  exact abs_distance_to_reference_lipschitz
    (u1ExponentGramCoordinateChargeCutoff D coordinate cutoff)
    (u1ExponentGramEntry
      D.half D.states D.normalizedMass coordinate)
    (reference coordinate)

theorem fixedReferenceExponentGramScore_abs_modulus
    (D : U1SlabData)
    (hw0 : (0 : Q') < D.coupling)
    (hw1 : D.coupling < (1 : Q'))
    (reference : ExponentGramCoordinate → Q')
    (coordinates : List ExponentGramCoordinate)
    (ε : Q') (hε : (0 : Q') < ε)
    (M : Nat)
    (hM :
      finiteCoordinateSignedChargeCutoff D coordinates ε ≤ M) :
    Q'.abs
        (fixedReferenceExponentGramCutoffScore
            D reference coordinates M +
          (-fixedReferenceExponentGramScore
            D reference coordinates)) ≤
      ε :=
  Q'.le_trans' _ _ _
    (fixedReferenceExponentGramScore_abs_error
      D reference coordinates M)
    (u1ExponentGramFiniteCoordinateL1Error_le
      D hw0 hw1 coordinates ε hε M hM)

/-! ## 5. A common finite-atlas cutoff and `AtlasScoreTube` -/

/-- A candidate-indexed family of genuine finite normalized U(1) slabs. -/
structure FixedSlabAtlasFamily
    (atlas : PositiveCouplingAtlas) : Type where
  slab : Q' → U1SlabData
  coupling_pos :
    ∀ candidate, candidate ∈ atlas.candidates →
      (0 : Q') < (slab candidate).coupling
  coupling_lt_one :
    ∀ candidate, candidate ∈ atlas.candidates →
      (slab candidate).coupling < (1 : Q')

/-- Constructive maximum of a finite natural-number list. -/
def listNatMax : List Nat → Nat
  | [] => 0
  | head :: rest => max head (listNatMax rest)

theorem le_listNatMax_of_mem :
    ∀ {value : Nat} {values : List Nat},
      value ∈ values → value ≤ listNatMax values
  | _, [], hmem => by simp at hmem
  | value, head :: rest, hmem => by
      rcases List.mem_cons.mp hmem with hhead | hrest
      · subst head
        exact Nat.le_max_left _ _
      · exact Nat.le_trans
          (le_listNatMax_of_mem hrest)
          (Nat.le_max_right _ _)

/-- One common cutoff dominating the explicit total-L1 cutoff of every atlas
candidate. -/
def atlasFiniteCoordinateSignedChargeCutoff
    (atlas : PositiveCouplingAtlas)
    (family : FixedSlabAtlasFamily atlas)
    (coordinates : List ExponentGramCoordinate)
    (ε : Q') : Nat :=
  listNatMax
    (atlas.candidates.map (fun candidate =>
      finiteCoordinateSignedChargeCutoff
        (family.slab candidate) coordinates ε))

theorem candidateCutoff_le_atlasCutoff
    (atlas : PositiveCouplingAtlas)
    (family : FixedSlabAtlasFamily atlas)
    (coordinates : List ExponentGramCoordinate)
    (ε : Q')
    (candidate : Q')
    (hcandidate : candidate ∈ atlas.candidates) :
    finiteCoordinateSignedChargeCutoff
        (family.slab candidate) coordinates ε ≤
      atlasFiniteCoordinateSignedChargeCutoff
        atlas family coordinates ε := by
  apply le_listNatMax_of_mem
  exact List.mem_map.mpr
    ⟨candidate, hcandidate, rfl⟩

def atlasFixedSlabExponentGramScore
    (atlas : PositiveCouplingAtlas)
    (family : FixedSlabAtlasFamily atlas)
    (reference : ExponentGramCoordinate → Q')
    (coordinates : List ExponentGramCoordinate)
    (candidate : Q') : Q' :=
  if candidate ∈ atlas.candidates then
    fixedReferenceExponentGramScore
      (family.slab candidate) reference coordinates
  else 0

def atlasFixedSlabExponentGramCutoffScore
    (atlas : PositiveCouplingAtlas)
    (family : FixedSlabAtlasFamily atlas)
    (reference : ExponentGramCoordinate → Q')
    (coordinates : List ExponentGramCoordinate)
    (ε : Q')
    (candidate : Q') : Q' :=
  if candidate ∈ atlas.candidates then
    fixedReferenceExponentGramCutoffScore
      (family.slab candidate) reference coordinates
      (atlasFiniteCoordinateSignedChargeCutoff
        atlas family coordinates ε)
  else 0

/-- The finite maximum of candidate-wise signed-charge cutoffs constructs a
uniform two-sided score tube on the whole supplied atlas. -/
def fixedSlabAtlasScoreTube
    (atlas : PositiveCouplingAtlas)
    (family : FixedSlabAtlasFamily atlas)
    (reference : ExponentGramCoordinate → Q')
    (coordinates : List ExponentGramCoordinate)
    (ε : Q') (hε : (0 : Q') < ε) :
    AtlasScoreTube atlas
      (atlasFixedSlabExponentGramCutoffScore
        atlas family reference coordinates ε)
      (atlasFixedSlabExponentGramScore
        atlas family reference coordinates)
      ε :=
  atlasScoreTubeOfAbs
    atlas
    (atlasFixedSlabExponentGramCutoffScore
      atlas family reference coordinates ε)
    (atlasFixedSlabExponentGramScore
      atlas family reference coordinates)
    ε (Q'.le_of_lt hε) (by
      intro candidate hcandidate
      unfold atlasFixedSlabExponentGramCutoffScore
        atlasFixedSlabExponentGramScore
      simp only [if_pos hcandidate]
      exact fixedReferenceExponentGramScore_abs_modulus
        (family.slab candidate)
        (family.coupling_pos candidate hcandidate)
        (family.coupling_lt_one candidate hcandidate)
        reference coordinates ε hε
        (atlasFiniteCoordinateSignedChargeCutoff
          atlas family coordinates ε)
        (candidateCutoff_le_atlasCutoff
          atlas family coordinates ε candidate hcandidate))

end YMGap.Continuum.BF4U1FiniteExponentGramTailTube

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.BF4U1FiniteExponentGramTailTube.abs_distance_to_reference_lipschitz
#print axioms YMGap.Continuum.BF4U1FiniteExponentGramTailTube.u1ExponentGramCoordinateChargeCutoff_abs_tail
#print axioms YMGap.Continuum.BF4U1FiniteExponentGramTailTube.u1ExponentGramCoordinateSignedChargeCutoff_abs_modulus
#print axioms YMGap.Continuum.BF4U1FiniteExponentGramTailTube.u1ExponentGramFiniteCoordinateL1Error_le
#print axioms YMGap.Continuum.BF4U1FiniteExponentGramTailTube.fixedReferenceExponentGramScore_abs_modulus
#print axioms YMGap.Continuum.BF4U1FiniteExponentGramTailTube.fixedSlabAtlasScoreTube
