/-
# Two-sided charge-cutoff control for the full U(1) exponent Gram

This module upgrades the one-sided diagonal cutoff estimate to a two-sided
absolute estimate for a reflected bilinear form.  The two half-observables
may differ, which is exactly what is required by an arbitrary off-diagonal
`ExponentGramCoordinate`.

All estimates stay on the genuine normalized finite U(1) slab carrier.  The
same bilinear form is then transported through the existing deterministic
BF4 pushforward by pulling the two half-observables back separately.
-/

import YMGap.Continuum.BF4U1SignedChargeTailInstantiation

namespace YMGap.Continuum.BF4U1ExponentGramOffDiagonalCutoff

set_option maxRecDepth 50000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4ExponentGramMatchedOneStep
open YMGap.Continuum.BF4ObservableMatchedOneStep
open YMGap.Continuum.BF4SU2U1ExponentGramDiscriminator
open YMGap.Continuum.BF4U1BlockReflectionCP
open YMGap.Continuum.BF4U1ExponentGramCutoffTailBridge
open YMGap.Continuum.BF4U1ExponentGramPositivity
open YMGap.Continuum.BF4U1SameCarrierPushforward
open YMGap.Continuum.BF4U1SignedChargeTailInstantiation
open YMGap.Continuum.BF4U1TwistedPhysicalReindex
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex

local infix:50 " ≈ " => Q'.eqv

private theorem listQSum_le_length_mul_local
    {A : Type} (value : A → Q')
    {bound : Q'} (hbound0 : (0 : Q') ≤ bound) :
    ∀ items : List A,
      (∀ item, item ∈ items → value item ≤ bound) →
      listQSum value items ≤
        Q'.ofNat items.length * bound
  | [], _ => by
      exact Q'.le_of_eqv
        (Q'.eqv_symm
          (Q'.zero_mul_eqv bound))
  | head :: rest, hbound => by
      have hhead :=
        hbound head List.mem_cons_self
      have hrest :=
        listQSum_le_length_mul_local
          value hbound0 rest
          (fun item hitem =>
            hbound item
              (List.mem_cons_of_mem head hitem))
      have hsum :
          value head + listQSum value rest ≤
            bound +
              Q'.ofNat rest.length * bound :=
        Q'.add_le_add hhead hrest
      have htarget :
          bound +
              Q'.ofNat rest.length * bound ≈
            Q'.ofNat (head :: rest).length *
              bound := by
        refine Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_right
            bound
            ((1 : Q') * bound)
            (Q'.ofNat rest.length * bound)
            (Q'.eqv_symm
              (Q'.one_mul_eqv bound))) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.eqv_symm
            (Q'.add_mul_eqv
              1 (Q'.ofNat rest.length) bound)) ?_
        apply Q'.mul_eqv_congr_right
        exact Q'.eqv_trans _ _ _
          (Q'.add_comm_eqv
            1 (Q'.ofNat rest.length))
          (Q'.eqv_symm
            (YMGap.Continuum.HKConvGen.ofNat_succ_eqv
              rest.length))
      exact Q'.le_trans' _ _ _ hsum
        (Q'.le_of_eqv htarget)

/-! ## 1. A genuine orientation-correct bilinear cutoff -/

def u1FullNormalizedMassReflectionBilinear
    (D : U1SlabData)
    (leftCoefficient rightCoefficient :
      ChargeLabelling → Q') : Q' :=
  listQSum
    (fun physical =>
      (leftCoefficient
          (centralLowerRestriction D.half physical) *
        rightCoefficient
          (u1ReflectedUpperRestriction
            D.half physical)) *
      D.normalizedMass physical)
    D.states

def u1FullNormalizedReflectionBilinearChargeCutoff
    (D : U1SlabData)
    (leftCoefficient rightCoefficient :
      ChargeLabelling → Q')
    (cutoff : Nat) : Q' :=
  listQSum
    (fun physical =>
      if u1StateWithinChargeCutoff
          D cutoff physical then
        (leftCoefficient
            (centralLowerRestriction D.half physical) *
          rightCoefficient
            (u1ReflectedUpperRestriction
              D.half physical)) *
        D.normalizedMass physical
      else 0)
    D.states

def u1FullNormalizedReflectionBilinearOmitted
    (D : U1SlabData)
    (leftCoefficient rightCoefficient :
      ChargeLabelling → Q')
    (cutoff : Nat) : Q' :=
  listQSum
    (fun physical =>
      if u1StateWithinChargeCutoff
          D cutoff physical then 0
      else
        (leftCoefficient
            (centralLowerRestriction D.half physical) *
          rightCoefficient
            (u1ReflectedUpperRestriction
              D.half physical)) *
        D.normalizedMass physical)
    D.states

theorem bilinearCutoff_add_omitted_eqv_full
    (D : U1SlabData)
    (leftCoefficient rightCoefficient :
      ChargeLabelling → Q')
    (cutoff : Nat) :
    u1FullNormalizedReflectionBilinearChargeCutoff
          D leftCoefficient rightCoefficient cutoff +
        u1FullNormalizedReflectionBilinearOmitted
          D leftCoefficient rightCoefficient cutoff ≈
      u1FullNormalizedMassReflectionBilinear
        D leftCoefficient rightCoefficient := by
  unfold u1FullNormalizedReflectionBilinearChargeCutoff
    u1FullNormalizedReflectionBilinearOmitted
    u1FullNormalizedMassReflectionBilinear
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (listQSum_add
        (fun physical =>
          if u1StateWithinChargeCutoff
              D cutoff physical then
            (leftCoefficient
                (centralLowerRestriction D.half physical) *
              rightCoefficient
                (u1ReflectedUpperRestriction
                  D.half physical)) *
            D.normalizedMass physical
          else 0)
        (fun physical =>
          if u1StateWithinChargeCutoff
              D cutoff physical then 0
          else
            (leftCoefficient
                (centralLowerRestriction D.half physical) *
              rightCoefficient
                (u1ReflectedUpperRestriction
                  D.half physical)) *
            D.normalizedMass physical)
        D.states)) ?_
  apply listQSum_congr_on
  intro physical _
  cases hwithin :
      u1StateWithinChargeCutoff D cutoff physical
  · exact Q'.eqv_of_eq
      (Q'.zero_add' _)
  · exact Q'.eqv_of_eq
      (Q'.add_zero' _)

private theorem coefficientProduct_nonnegative
    (leftCoefficient rightCoefficient :
      ChargeLabelling → Q')
    (left_nonnegative :
      ∀ state, (0 : Q') ≤ leftCoefficient state)
    (right_nonnegative :
      ∀ state, (0 : Q') ≤ rightCoefficient state)
    (leftState rightState : ChargeLabelling) :
    (0 : Q') ≤
      leftCoefficient leftState *
        rightCoefficient rightState :=
  Q'.mul_nonneg _ _
    (left_nonnegative leftState)
    (right_nonnegative rightState)

private theorem coefficientProduct_le_one
    (leftCoefficient rightCoefficient :
      ChargeLabelling → Q')
    (left_le_one :
      ∀ state, leftCoefficient state ≤ (1 : Q'))
    (right_nonnegative :
      ∀ state, (0 : Q') ≤ rightCoefficient state)
    (right_le_one :
      ∀ state, rightCoefficient state ≤ (1 : Q'))
    (leftState rightState : ChargeLabelling) :
    leftCoefficient leftState *
        rightCoefficient rightState ≤
      (1 : Q') := by
  have hscale :
      leftCoefficient leftState *
          rightCoefficient rightState ≤
        (1 : Q') * rightCoefficient rightState :=
    Q'.mul_le_mul_of_nonneg_right
      _ _ _
      (left_le_one leftState)
      (right_nonnegative rightState)
  exact Q'.le_trans' _ _ _ hscale
    (Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.one_mul_eqv
          (rightCoefficient rightState)))
      (right_le_one rightState))

theorem u1FullNormalizedReflectionBilinearOmitted_nonnegative
    (D : U1SlabData)
    (leftCoefficient rightCoefficient :
      ChargeLabelling → Q')
    (left_nonnegative :
      ∀ state, (0 : Q') ≤ leftCoefficient state)
    (right_nonnegative :
      ∀ state, (0 : Q') ≤ rightCoefficient state)
    (cutoff : Nat) :
    (0 : Q') ≤
      u1FullNormalizedReflectionBilinearOmitted
        D leftCoefficient rightCoefficient cutoff := by
  unfold u1FullNormalizedReflectionBilinearOmitted
  apply listQSum_nonnegative_on
  intro physical _
  cases hwithin :
      u1StateWithinChargeCutoff D cutoff physical
  · exact Q'.mul_nonneg _ _
      (coefficientProduct_nonnegative
        leftCoefficient rightCoefficient
        left_nonnegative right_nonnegative _ _)
      (D.normalizedMass_nonnegative physical)
  · exact Q'.le_refl' 0

theorem u1FullNormalizedReflectionBilinearOmitted_le
    (D : U1SlabData)
    (hcoupling : D.coupling ≤ (1 : Q'))
    (tailData : OneChargeTail D)
    (leftCoefficient rightCoefficient :
      ChargeLabelling → Q')
    (left_le_one :
      ∀ state, leftCoefficient state ≤ (1 : Q'))
    (right_nonnegative :
      ∀ state, (0 : Q') ≤ rightCoefficient state)
    (right_le_one :
      ∀ state, rightCoefficient state ≤ (1 : Q'))
    (cutoff : Nat) :
    u1FullNormalizedReflectionBilinearOmitted
        D leftCoefficient rightCoefficient cutoff ≤
      Q'.ofNat D.states.length *
        tailData.tail cutoff := by
  unfold u1FullNormalizedReflectionBilinearOmitted
  apply listQSum_le_length_mul_local
    _ (tailData.tail_nonnegative cutoff)
  intro physical _
  cases hwithin :
      u1StateWithinChargeCutoff D cutoff physical
  · have hproduct1 :=
      coefficientProduct_le_one
        leftCoefficient rightCoefficient
        left_le_one
        right_nonnegative right_le_one
        (centralLowerRestriction D.half physical)
        (u1ReflectedUpperRestriction
          D.half physical)
    have hmass0 :=
      D.normalizedMass_nonnegative physical
    have hscaled :
        (leftCoefficient
              (centralLowerRestriction
                D.half physical) *
            rightCoefficient
              (u1ReflectedUpperRestriction
                D.half physical)) *
            D.normalizedMass physical ≤
          (1 : Q') *
            D.normalizedMass physical :=
      Q'.mul_le_mul_of_nonneg_right
        _ _ _ hproduct1 hmass0
    have hmassTail :=
      u1NormalizedMass_le_oneChargeTail_of_outside
        D hcoupling tailData cutoff physical hwithin
    exact Q'.le_trans' _ _ _ hscaled
      (Q'.le_trans' _ _ _
        (Q'.le_of_eqv
          (Q'.one_mul_eqv
            (D.normalizedMass physical)))
        hmassTail)
  · exact tailData.tail_nonnegative cutoff

/-! ## 2. Two-sided and absolute error -/

theorem u1FullNormalizedReflectionBilinearChargeCutoff_le
    (D : U1SlabData)
    (leftCoefficient rightCoefficient :
      ChargeLabelling → Q')
    (left_nonnegative :
      ∀ state, (0 : Q') ≤ leftCoefficient state)
    (right_nonnegative :
      ∀ state, (0 : Q') ≤ rightCoefficient state)
    (cutoff : Nat) :
    u1FullNormalizedReflectionBilinearChargeCutoff
        D leftCoefficient rightCoefficient cutoff ≤
      u1FullNormalizedMassReflectionBilinear
        D leftCoefficient rightCoefficient := by
  have homitted0 :=
    u1FullNormalizedReflectionBilinearOmitted_nonnegative
      D leftCoefficient rightCoefficient
      left_nonnegative right_nonnegative cutoff
  have hadd :
      u1FullNormalizedReflectionBilinearChargeCutoff
          D leftCoefficient rightCoefficient cutoff ≤
        u1FullNormalizedReflectionBilinearChargeCutoff
            D leftCoefficient rightCoefficient cutoff +
          u1FullNormalizedReflectionBilinearOmitted
            D leftCoefficient rightCoefficient cutoff :=
    Q'.add_le_self_of_nonneg _ _ homitted0
  exact Q'.le_trans' _ _ _ hadd
    (Q'.le_of_eqv
      (bilinearCutoff_add_omitted_eqv_full
        D leftCoefficient rightCoefficient cutoff))

theorem u1FullNormalizedReflectionBilinear_twoSided
    (D : U1SlabData)
    (hcoupling : D.coupling ≤ (1 : Q'))
    (tailData : OneChargeTail D)
    (leftCoefficient rightCoefficient :
      ChargeLabelling → Q')
    (left_nonnegative :
      ∀ state, (0 : Q') ≤ leftCoefficient state)
    (left_le_one :
      ∀ state, leftCoefficient state ≤ (1 : Q'))
    (right_nonnegative :
      ∀ state, (0 : Q') ≤ rightCoefficient state)
    (right_le_one :
      ∀ state, rightCoefficient state ≤ (1 : Q'))
    (cutoff : Nat) :
    u1FullNormalizedMassReflectionBilinear
          D leftCoefficient rightCoefficient ≤
        u1FullNormalizedReflectionBilinearChargeCutoff
            D leftCoefficient rightCoefficient cutoff +
          Q'.ofNat D.states.length *
            tailData.tail cutoff ∧
      u1FullNormalizedReflectionBilinearChargeCutoff
            D leftCoefficient rightCoefficient cutoff ≤
        u1FullNormalizedMassReflectionBilinear
            D leftCoefficient rightCoefficient +
          Q'.ofNat D.states.length *
            tailData.tail cutoff := by
  have hsplit :=
    bilinearCutoff_add_omitted_eqv_full
      D leftCoefficient rightCoefficient cutoff
  have homitted :=
    u1FullNormalizedReflectionBilinearOmitted_le
      D hcoupling tailData
      leftCoefficient rightCoefficient
      left_le_one
      right_nonnegative right_le_one cutoff
  have hforward :
      u1FullNormalizedMassReflectionBilinear
          D leftCoefficient rightCoefficient ≤
        u1FullNormalizedReflectionBilinearChargeCutoff
            D leftCoefficient rightCoefficient cutoff +
          Q'.ofNat D.states.length *
            tailData.tail cutoff :=
    Q'.le_trans' _ _ _
      (Q'.ge_of_eqv hsplit)
      (Q'.add_le_add_left _ _ _ homitted)
  have hcut :=
    u1FullNormalizedReflectionBilinearChargeCutoff_le
      D leftCoefficient rightCoefficient
      left_nonnegative right_nonnegative cutoff
  have hbound0 :
      (0 : Q') ≤
        Q'.ofNat D.states.length *
          tailData.tail cutoff :=
    Q'.mul_nonneg _ _
      (Q'.le_of_lt
        (u1StateCarrierScale_pos D))
      (tailData.tail_nonnegative cutoff)
  exact
    ⟨hforward,
      Q'.le_trans' _ _ _ hcut
        (Q'.add_le_self_of_nonneg _ _ hbound0)⟩

theorem u1FullNormalizedReflectionBilinear_abs_error
    (D : U1SlabData)
    (hcoupling : D.coupling ≤ (1 : Q'))
    (tailData : OneChargeTail D)
    (leftCoefficient rightCoefficient :
      ChargeLabelling → Q')
    (left_nonnegative :
      ∀ state, (0 : Q') ≤ leftCoefficient state)
    (left_le_one :
      ∀ state, leftCoefficient state ≤ (1 : Q'))
    (right_nonnegative :
      ∀ state, (0 : Q') ≤ rightCoefficient state)
    (right_le_one :
      ∀ state, rightCoefficient state ≤ (1 : Q'))
    (cutoff : Nat) :
    Q'.abs
        (u1FullNormalizedMassReflectionBilinear
            D leftCoefficient rightCoefficient +
          -u1FullNormalizedReflectionBilinearChargeCutoff
            D leftCoefficient rightCoefficient cutoff) ≤
      Q'.ofNat D.states.length *
        tailData.tail cutoff := by
  have htwo :=
    u1FullNormalizedReflectionBilinear_twoSided
      D hcoupling tailData
      leftCoefficient rightCoefficient
      left_nonnegative left_le_one
      right_nonnegative right_le_one cutoff
  exact CReal.abs_sub_le_of_bounds htwo.1 htwo.2

/-! ## 3. Recovery of the existing one-observable cutoff -/

theorem u1FullNormalizedReflectionChargeCutoff_twoSided
    (D : U1SlabData)
    (hcoupling : D.coupling ≤ (1 : Q'))
    (tailData : OneChargeTail D)
    (coefficient : ChargeLabelling → Q')
    (coefficient_nonnegative :
      ∀ state, (0 : Q') ≤ coefficient state)
    (coefficient_le_one :
      ∀ state, coefficient state ≤ (1 : Q'))
    (cutoff : Nat) :
    u1FullNormalizedMassReflectionQuadratic
          D coefficient ≤
        u1FullNormalizedReflectionChargeCutoff
            D coefficient cutoff +
          Q'.ofNat D.states.length *
            tailData.tail cutoff ∧
      u1FullNormalizedReflectionChargeCutoff
            D coefficient cutoff ≤
        u1FullNormalizedMassReflectionQuadratic
            D coefficient +
          Q'.ofNat D.states.length *
            tailData.tail cutoff :=
  u1FullNormalizedReflectionBilinear_twoSided
    D hcoupling tailData coefficient coefficient
    coefficient_nonnegative coefficient_le_one
    coefficient_nonnegative coefficient_le_one cutoff

theorem u1FullNormalizedReflectionChargeCutoff_abs_error
    (D : U1SlabData)
    (hcoupling : D.coupling ≤ (1 : Q'))
    (tailData : OneChargeTail D)
    (coefficient : ChargeLabelling → Q')
    (coefficient_nonnegative :
      ∀ state, (0 : Q') ≤ coefficient state)
    (coefficient_le_one :
      ∀ state, coefficient state ≤ (1 : Q'))
    (cutoff : Nat) :
    Q'.abs
        (u1FullNormalizedMassReflectionQuadratic
            D coefficient +
          -u1FullNormalizedReflectionChargeCutoff
            D coefficient cutoff) ≤
      Q'.ofNat D.states.length *
        tailData.tail cutoff := by
  exact
    u1FullNormalizedReflectionBilinear_abs_error
      D hcoupling tailData coefficient coefficient
      coefficient_nonnegative coefficient_le_one
      coefficient_nonnegative coefficient_le_one cutoff

/-! ## 4. Arbitrary exponent-Gram coordinates -/

def u1ExponentGramCoordinateChargeCutoff
    (D : U1SlabData)
    (coordinate : ExponentGramCoordinate)
    (cutoff : Nat) : Q' :=
  u1FullNormalizedReflectionBilinearChargeCutoff D
    (u1ExponentCoefficient
      D.half coordinate.leftExponent)
    (u1ExponentCoefficient
      D.half coordinate.rightExponent)
    cutoff

theorem u1ExponentGramEntry_eq_fullBilinear
    (D : U1SlabData)
    (coordinate : ExponentGramCoordinate) :
    u1ExponentGramEntry
        D.half D.states D.normalizedMass coordinate ≈
      u1FullNormalizedMassReflectionBilinear D
        (u1ExponentCoefficient
          D.half coordinate.leftExponent)
        (u1ExponentCoefficient
          D.half coordinate.rightExponent) := by
  unfold u1ExponentGramEntry reflectedLawBilinear
    u1FullNormalizedMassReflectionBilinear
  apply listQSum_congr_on
  intro physical _
  rw [u1ExponentCoefficient_reflectedRestrictions]
  exact Q'.eqv_refl _

theorem u1ExponentGramCoordinateChargeCutoff_abs_error
    (D : U1SlabData)
    (hcoupling : D.coupling ≤ (1 : Q'))
    (tailData : OneChargeTail D)
    (coordinate : ExponentGramCoordinate)
    (cutoff : Nat) :
    Q'.abs
        (u1ExponentGramEntry
            D.half D.states D.normalizedMass coordinate +
          -u1ExponentGramCoordinateChargeCutoff
            D coordinate cutoff) ≤
      Q'.ofNat D.states.length *
        tailData.tail cutoff := by
  have hfull :=
    u1ExponentGramEntry_eq_fullBilinear
      D coordinate
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.abs_eqv_congr
        (Q'.add_eqv_congr_right _ _ _
          hfull))) ?_
  exact u1FullNormalizedReflectionBilinear_abs_error
    D hcoupling tailData
    (u1ExponentCoefficient
      D.half coordinate.leftExponent)
    (u1ExponentCoefficient
      D.half coordinate.rightExponent)
    (u1ExponentCoefficient_nonnegative
      D.half coordinate.leftExponent)
    (u1ExponentCoefficient_le_one
      D.half coordinate.leftExponent)
    (u1ExponentCoefficient_nonnegative
      D.half coordinate.rightExponent)
    (u1ExponentCoefficient_le_one
      D.half coordinate.rightExponent)
    cutoff

theorem u1ExponentGramCoordinateChargeCutoff_twoSided
    (D : U1SlabData)
    (hcoupling : D.coupling ≤ (1 : Q'))
    (tailData : OneChargeTail D)
    (coordinate : ExponentGramCoordinate)
    (cutoff : Nat) :
    u1ExponentGramEntry
          D.half D.states D.normalizedMass coordinate ≤
        u1ExponentGramCoordinateChargeCutoff
            D coordinate cutoff +
          Q'.ofNat D.states.length *
            tailData.tail cutoff ∧
      u1ExponentGramCoordinateChargeCutoff
            D coordinate cutoff ≤
        u1ExponentGramEntry
            D.half D.states D.normalizedMass coordinate +
          Q'.ofNat D.states.length *
            tailData.tail cutoff := by
  have hentry :=
    u1ExponentGramEntry_eq_fullBilinear
      D coordinate
  have htwo :=
    u1FullNormalizedReflectionBilinear_twoSided
      D hcoupling tailData
      (u1ExponentCoefficient
        D.half coordinate.leftExponent)
      (u1ExponentCoefficient
        D.half coordinate.rightExponent)
      (u1ExponentCoefficient_nonnegative
        D.half coordinate.leftExponent)
      (u1ExponentCoefficient_le_one
        D.half coordinate.leftExponent)
      (u1ExponentCoefficient_nonnegative
        D.half coordinate.rightExponent)
      (u1ExponentCoefficient_le_one
        D.half coordinate.rightExponent)
      cutoff
  exact
    ⟨Q'.le_trans' _ _ _
        (Q'.le_of_eqv hentry) htwo.1,
      Q'.le_trans' _ _ _ htwo.2
        (Q'.add_le_add_right _ _ _
          (Q'.ge_of_eqv hentry))⟩

theorem u1ExponentGramCoordinateSignedChargeCutoff_modulus
    (D : U1SlabData)
    (hw0 : (0 : Q') < D.coupling)
    (hw1 : D.coupling < (1 : Q'))
    (coordinate : ExponentGramCoordinate)
    (ε : Q') (hε : (0 : Q') < ε)
    (M : Nat)
    (hM : signedChargeCarrierCutoff D ε ≤ M) :
    Q'.abs
        (u1ExponentGramEntry
            D.half D.states D.normalizedMass coordinate +
          -u1ExponentGramCoordinateChargeCutoff
            D coordinate M) ≤
      ε := by
  exact Q'.le_trans' _ _ _
    (u1ExponentGramCoordinateChargeCutoff_abs_error
      D (Q'.le_of_lt hw1)
      (signedChargeOneChargeTail
        D hw0 hw1)
      coordinate M)
    ((signedChargeOneChargeTailModulus
      D hw0 hw1).scaled_tail ε hε M hM)

/-! ## 5. Deterministic BF4 pullback -/

def u1BlockedFullReflectionBilinear
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (candidate : Q') (hcandidate : (0 : Q') < candidate)
    (fineChargeCutoff : Nat)
    (leftCoefficient rightCoefficient :
      ChargeLabelling → Q') : Q' :=
  listQSum
    (fun coarseState =>
      (leftCoefficient
          (centralLowerRestriction
            G.coarseHalf coarseState) *
        rightCoefficient
          (u1ReflectedUpperRestriction
            G.coarseHalf coarseState)) *
      u1BlockedMass G g hg candidate hcandidate
        fineChargeCutoff coarseState)
    (coarseU1Data G candidate hcandidate
      fineChargeCutoff).states

private theorem u1BlockPullbackCoefficient_lower_local
    (G : CutoffOneGeometry) (fineChargeCutoff : Nat)
    (coefficient : ChargeLabelling → Q')
    (fineState : ChargeLabelling) :
    u1BlockPullbackCoefficient G fineChargeCutoff coefficient
        (centralLowerRestriction G.fineHalf fineState) =
      coefficient
        (centralLowerRestriction G.coarseHalf
          (u1BlockState G fineChargeCutoff fineState)) := by
  unfold u1BlockPullbackCoefficient
  rw [← centralLowerRestriction_u1BlockState
    G fineChargeCutoff fineState]

private theorem u1BlockPullbackCoefficient_upper_local
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (fineChargeCutoff : Nat)
    (coefficient : ChargeLabelling → Q')
    {fineState : ChargeLabelling}
    (hfine :
      fineState ∈
        (fineU1Data G g hg fineChargeCutoff).states) :
    u1BlockPullbackCoefficient G fineChargeCutoff coefficient
        (u1ReflectedUpperRestriction
          G.fineHalf fineState) =
      coefficient
        (u1ReflectedUpperRestriction G.coarseHalf
          (u1BlockState G fineChargeCutoff fineState)) := by
  unfold u1BlockPullbackCoefficient
  rw [u1ReflectedUpperRestriction_u1BlockState
    G g hg fineChargeCutoff hfine]

theorem u1BlockedFullReflectionBilinear_eq_finePullback
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (candidate : Q') (hcandidate : (0 : Q') < candidate)
    (fineChargeCutoff : Nat)
    (leftCoefficient rightCoefficient :
      ChargeLabelling → Q') :
    u1BlockedFullReflectionBilinear
        G g hg candidate hcandidate fineChargeCutoff
        leftCoefficient rightCoefficient ≈
      u1FullNormalizedMassReflectionBilinear
        (fineU1Data G g hg fineChargeCutoff)
        (u1BlockPullbackCoefficient
          G fineChargeCutoff leftCoefficient)
        (u1BlockPullbackCoefficient
          G fineChargeCutoff rightCoefficient) := by
  let coarseObservable : ChargeLabelling → Q' :=
    fun coarseState =>
      leftCoefficient
          (centralLowerRestriction
            G.coarseHalf coarseState) *
        rightCoefficient
          (u1ReflectedUpperRestriction
            G.coarseHalf coarseState)
  refine Q'.eqv_trans _
    (listQSum
      (fun fineState =>
        (fineU1Data G g hg fineChargeCutoff).normalizedMass
            fineState *
          coarseObservable
            (u1BlockState G fineChargeCutoff fineState))
      (fineU1Data G g hg fineChargeCutoff).states) _ ?_ ?_
  · exact u1BlockedObservableExpectation_eq_pullback
      G g hg candidate hcandidate fineChargeCutoff
      coarseObservable
  · unfold u1FullNormalizedMassReflectionBilinear
    apply listQSum_congr_on
    intro fineState hfine
    unfold coarseObservable
    change
      (fineU1Data G g hg fineChargeCutoff).normalizedMass fineState *
          (leftCoefficient
              (centralLowerRestriction G.coarseHalf
                (u1BlockState G fineChargeCutoff fineState)) *
            rightCoefficient
              (u1ReflectedUpperRestriction G.coarseHalf
                (u1BlockState G fineChargeCutoff fineState))) ≈
        (u1BlockPullbackCoefficient G fineChargeCutoff leftCoefficient
              (centralLowerRestriction G.fineHalf fineState) *
            u1BlockPullbackCoefficient G fineChargeCutoff rightCoefficient
              (u1ReflectedUpperRestriction G.fineHalf fineState)) *
          (fineU1Data G g hg fineChargeCutoff).normalizedMass fineState
    rw [u1BlockPullbackCoefficient_lower_local,
      u1BlockPullbackCoefficient_upper_local
        G g hg fineChargeCutoff
        rightCoefficient hfine]
    exact Q'.mul_comm_eqv _ _

theorem u1BlockedExponentGramEntry_eq_fineBilinear
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (candidate : Q') (hcandidate : (0 : Q') < candidate)
    (fineChargeCutoff : Nat)
    (coordinate : ExponentGramCoordinate) :
    u1BlockedExponentGramEntry
        G g hg candidate hcandidate fineChargeCutoff coordinate ≈
      u1FullNormalizedMassReflectionBilinear
        (fineU1Data G g hg fineChargeCutoff)
        (u1BlockPullbackCoefficient G fineChargeCutoff
          (u1ExponentCoefficient
            G.coarseHalf coordinate.leftExponent))
        (u1BlockPullbackCoefficient G fineChargeCutoff
          (u1ExponentCoefficient
            G.coarseHalf coordinate.rightExponent)) := by
  refine Q'.eqv_trans _ _ _
    ?_ (u1BlockedFullReflectionBilinear_eq_finePullback
      G g hg candidate hcandidate fineChargeCutoff
      (u1ExponentCoefficient
        G.coarseHalf coordinate.leftExponent)
      (u1ExponentCoefficient
        G.coarseHalf coordinate.rightExponent))
  unfold u1BlockedExponentGramEntry u1ExponentGramEntry
    reflectedLawBilinear u1BlockedFullReflectionBilinear
  apply listQSum_congr_on
  intro coarseState _
  rw [u1ExponentCoefficient_reflectedRestrictions]
  exact Q'.eqv_refl _

def u1BlockedExponentGramCoordinateChargeCutoff
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (fineChargeCutoff : Nat)
    (coordinate : ExponentGramCoordinate)
    (retainedCharge : Nat) : Q' :=
  u1FullNormalizedReflectionBilinearChargeCutoff
    (fineU1Data G g hg fineChargeCutoff)
    (u1BlockPullbackCoefficient G fineChargeCutoff
      (u1ExponentCoefficient
        G.coarseHalf coordinate.leftExponent))
    (u1BlockPullbackCoefficient G fineChargeCutoff
      (u1ExponentCoefficient
        G.coarseHalf coordinate.rightExponent))
    retainedCharge

private theorem u1BlockExponentPullback_nonnegative_local
    (G : CutoffOneGeometry)
    (fineChargeCutoff exponent : Nat)
    (state : ChargeLabelling) :
    (0 : Q') ≤
      u1BlockPullbackCoefficient G fineChargeCutoff
        (u1ExponentCoefficient G.coarseHalf exponent)
        state := by
  unfold u1BlockPullbackCoefficient
  exact u1ExponentCoefficient_nonnegative
    G.coarseHalf exponent _

private theorem u1BlockExponentPullback_le_one_local
    (G : CutoffOneGeometry)
    (fineChargeCutoff exponent : Nat)
    (state : ChargeLabelling) :
    u1BlockPullbackCoefficient G fineChargeCutoff
        (u1ExponentCoefficient G.coarseHalf exponent)
        state ≤ (1 : Q') := by
  unfold u1BlockPullbackCoefficient
  exact u1ExponentCoefficient_le_one
    G.coarseHalf exponent _

theorem u1BlockedExponentGramCoordinateChargeCutoff_abs_error
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (hg1 : g ≤ (1 : Q'))
    (candidate : Q') (hcandidate : (0 : Q') < candidate)
    (fineChargeCutoff : Nat)
    (tailData :
      OneChargeTail
        (fineU1Data G g hg fineChargeCutoff))
    (coordinate : ExponentGramCoordinate)
    (retainedCharge : Nat) :
    Q'.abs
        (u1BlockedExponentGramEntry
            G g hg candidate hcandidate fineChargeCutoff coordinate +
          -u1BlockedExponentGramCoordinateChargeCutoff
            G g hg fineChargeCutoff coordinate retainedCharge) ≤
      Q'.ofNat
          (fineU1Data G g hg
            fineChargeCutoff).states.length *
        tailData.tail retainedCharge := by
  have hentry :=
    u1BlockedExponentGramEntry_eq_fineBilinear
      G g hg candidate hcandidate
      fineChargeCutoff coordinate
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.abs_eqv_congr
        (Q'.add_eqv_congr_right _ _ _
          hentry))) ?_
  exact u1FullNormalizedReflectionBilinear_abs_error
    (fineU1Data G g hg fineChargeCutoff)
    hg1 tailData
    (u1BlockPullbackCoefficient G fineChargeCutoff
      (u1ExponentCoefficient
        G.coarseHalf coordinate.leftExponent))
    (u1BlockPullbackCoefficient G fineChargeCutoff
      (u1ExponentCoefficient
        G.coarseHalf coordinate.rightExponent))
    (u1BlockExponentPullback_nonnegative_local
      G fineChargeCutoff coordinate.leftExponent)
    (u1BlockExponentPullback_le_one_local
      G fineChargeCutoff coordinate.leftExponent)
    (u1BlockExponentPullback_nonnegative_local
      G fineChargeCutoff coordinate.rightExponent)
    (u1BlockExponentPullback_le_one_local
      G fineChargeCutoff coordinate.rightExponent)
    retainedCharge

theorem u1BlockedExponentGramCoordinateSignedChargeCutoff_modulus
    (G : CutoffOneGeometry)
    (g : Q') (hg0 : (0 : Q') < g)
    (hg1 : g < (1 : Q'))
    (candidate : Q') (hcandidate : (0 : Q') < candidate)
    (fineChargeCutoff : Nat)
    (coordinate : ExponentGramCoordinate)
    (ε : Q') (hε : (0 : Q') < ε)
    (M : Nat)
    (hM :
      signedChargeCarrierCutoff
          (fineU1Data G g (Q'.le_of_lt hg0)
            fineChargeCutoff) ε ≤
        M) :
    Q'.abs
        (u1BlockedExponentGramEntry
            G g (Q'.le_of_lt hg0)
            candidate hcandidate fineChargeCutoff coordinate +
          -u1BlockedExponentGramCoordinateChargeCutoff
            G g (Q'.le_of_lt hg0)
            fineChargeCutoff coordinate M) ≤
      ε := by
  let D :=
    fineU1Data G g (Q'.le_of_lt hg0)
      fineChargeCutoff
  exact Q'.le_trans' _ _ _
    (u1BlockedExponentGramCoordinateChargeCutoff_abs_error
      G g (Q'.le_of_lt hg0) (Q'.le_of_lt hg1)
      candidate hcandidate fineChargeCutoff
      (signedChargeOneChargeTail D hg0 hg1)
      coordinate M)
    ((signedChargeOneChargeTailModulus
      D hg0 hg1).scaled_tail ε hε M hM)

#print axioms bilinearCutoff_add_omitted_eqv_full
#print axioms u1FullNormalizedReflectionBilinear_abs_error
#print axioms u1FullNormalizedReflectionChargeCutoff_twoSided
#print axioms u1FullNormalizedReflectionChargeCutoff_abs_error
#print axioms u1ExponentGramCoordinateChargeCutoff_twoSided
#print axioms u1ExponentGramCoordinateChargeCutoff_abs_error
#print axioms u1ExponentGramCoordinateSignedChargeCutoff_modulus
#print axioms u1BlockedFullReflectionBilinear_eq_finePullback
#print axioms u1BlockedExponentGramCoordinateChargeCutoff_abs_error
#print axioms u1BlockedExponentGramCoordinateSignedChargeCutoff_modulus

end YMGap.Continuum.BF4U1ExponentGramOffDiagonalCutoff
