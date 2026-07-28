/-
# Quantitative entrywise-to-Hilbert--Schmidt BF4 convergence

The normalized same-carrier BF4/Mehler layer previously asked directly for
one squared Hilbert--Schmidt estimate.  For an explicit kernel construction,
the estimates naturally arrive entry by entry.  On an `N × N` carrier,

    |Eᵢⱼ| ≤ δ

implies

    ||E||²_HS ≤ N · (N · δ²).

This file proves that finite estimate over the project's exact rational
arithmetic and packages a cutoff-indexed entrywise convergence datum.  The
only growth condition it requires is the explicit balance

    N(cutoff)² δ(cutoff)² ≤ ε(cutoff)².

It then constructs the existing `NormalizedSameCarrierMehlerHSConvergence`
object and inherits the eventual nonlinear Perron-ratio bound.

## Axiom gate

Finite rational sums and intuitionistic, Type-valued moduli only.  No
`Classical.*`, `sorry`, `native_decide`, custom axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4NormalizedSameCarrierPerron

namespace YMGap.Continuum.BF4EntrywiseSameCarrierHSConvergence

set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

open YMGap.Constructive
open YMGap.Continuum.BF4GaussianPerronRatio
open YMGap.Continuum.BF4NormalizedSameCarrierPerron
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.CubeRatioBounds
open YMGap.Continuum.FiniteCarrierHSPerronPerturbation

local infix:50 " ≈ " => Q'.eqv

private theorem fsum_mono_lt_local
    {lower upper : Nat → Q'} :
    ∀ N,
      (∀ index, index < N → lower index ≤ upper index) →
        fsum lower N ≤ fsum upper N
  | 0, _ => Q'.le_refl' 0
  | N + 1, termwise =>
      Q'.add_le_add
        (fsum_mono_lt_local N
          (fun index hindex =>
            termwise index (Nat.lt_trans hindex (by omega))))
        (termwise N (by omega))

private theorem fsum_const_local
    (constant : Q') :
    ∀ N : Nat,
      fsum (fun _ => constant) N ≈
        Q'.ofNat N * constant
  | 0 => by
      exact Q'.eqv_symm
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right
            (Q'.ofNat 0) 0 constant
            Q'.ofNat_zero_eqv)
          (Q'.zero_mul_eqv constant))
  | N + 1 => by
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ constant
          (fsum_const_local constant N)) ?_
      refine Q'.eqv_symm
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right
            (Q'.ofNat (N + 1))
            (Q'.ofNat N + Q'.ofNat 1)
            constant
            (Q'.ofNat_add_eqv N 1)) ?_)
      refine Q'.eqv_trans _ _ _
        (Q'.add_mul_eqv
          (Q'.ofNat N) (Q'.ofNat 1) constant) ?_
      exact Q'.add_eqv_congr_left _ _ _
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right
            (Q'.ofNat 1) 1 constant
            (by decide))
          (Q'.one_mul_eqv constant))

/-! ## 1. The finite entrywise-to-HS estimate -/

private theorem square_le_of_abs_le
    {entry error : Q'}
    (herror0 : (0 : Q') ≤ error)
    (hentry : Q'.abs entry ≤ error) :
    entry * entry ≤ error * error := by
  refine Q'.le_trans' _ _ _
    (Q'.le_abs_self (entry * entry)) ?_
  refine Q'.le_trans' _ _ _
    (ExpNeg.abs_mul_le entry entry) ?_
  exact Q'.mul_le_mul_of_nonneg
    hentry hentry herror0 (Q'.abs_nonneg entry)

theorem rowHSSq_le_of_entrywise_abs
    (matrix : RationalMatrix) (N row : Nat)
    (error : Q') (herror0 : (0 : Q') ≤ error)
    (hentry :
      ∀ column, column < N →
        Q'.abs (matrix row column) ≤ error) :
    rowHSSq matrix N row ≤
      Q'.ofNat N * (error * error) := by
  have hsum :
      rowHSSq matrix N row ≤
        fsum (fun _ => error * error) N := by
    unfold rowHSSq
    apply fsum_mono_lt_local
    intro column hcolumn
    exact square_le_of_abs_le
      herror0 (hentry column hcolumn)
  exact Q'.le_trans' _ _ _ hsum
    (Q'.le_of_eqv
      (fsum_const_local (error * error) N))

/-- **Quantitative finite entrywise-to-Hilbert--Schmidt estimate.**

The explicit carrier-dimension loss is exactly the iterated factor
`N · (N · δ²)`. -/
theorem matrixHSSq_le_of_entrywise_abs
    (matrix : RationalMatrix) (N : Nat)
    (error : Q') (herror0 : (0 : Q') ≤ error)
    (hentry :
      ∀ row, row < N →
        ∀ column, column < N →
          Q'.abs (matrix row column) ≤ error) :
    matrixHSSq matrix N ≤
      Q'.ofNat N *
        (Q'.ofNat N * (error * error)) := by
  have hsum :
      matrixHSSq matrix N ≤
        fsum
          (fun _ =>
            Q'.ofNat N * (error * error)) N := by
    unfold matrixHSSq
    apply fsum_mono_lt_local
    intro row hrow
    exact rowHSSq_le_of_entrywise_abs
      matrix N row error herror0
      (hentry row hrow)
  exact Q'.le_trans' _ _ _ hsum
    (Q'.le_of_eqv
      (fsum_const_local
        (Q'.ofNat N * (error * error)) N))

/-! ## 2. Cutoff-indexed entrywise convergence package -/

/-- A same-carrier nonlinear/Mehler comparison whose analytic estimate is
given entry by entry.  The dimension/error balance is displayed explicitly
rather than hidden inside an HS hypothesis. -/
structure EntrywiseNormalizedSameCarrierMehlerConvergence : Type where
  predecessor : Nat → Nat
  nonlinear : Nat → RationalMatrix
  mehler : Nat → RationalMatrix
  approximation : Nat → Nat
  nonlinear_normalized :
    ∀ cutoff,
      UniformNormalizedMatrix
        (nonlinear cutoff) (predecessor cutoff)
  mehler_normalized :
    ∀ cutoff,
      UniformNormalizedMatrix
        (mehler cutoff) (predecessor cutoff)
  mehler_quadratic :
    ∀ cutoff vector,
      Q'.abs
          (matrixQuadratic
            (vacuumRemovedMatrix
              (mehler cutoff) (predecessor cutoff))
            vector (predecessor cutoff + 1)) ≤
        gaussianPerronRatio.approx (approximation cutoff) *
          vectorNormSq vector (predecessor cutoff + 1)
  entry_error : Nat → Q'
  entry_error_nonnegative :
    ∀ cutoff, (0 : Q') ≤ entry_error cutoff
  entrywise_error :
    ∀ cutoff row, row < predecessor cutoff + 1 →
      ∀ column, column < predecessor cutoff + 1 →
        Q'.abs
            (matrixDifference
              (vacuumRemovedMatrix
                (nonlinear cutoff) (predecessor cutoff))
              (vacuumRemovedMatrix
                (mehler cutoff) (predecessor cutoff))
              row column) ≤
          entry_error cutoff
  epsilon : Nat → Q'
  epsilon_nonnegative :
    ∀ cutoff, (0 : Q') ≤ epsilon cutoff
  dimension_error_balance :
    ∀ cutoff,
      let carrierSize := predecessor cutoff + 1
      Q'.ofNat carrierSize *
          (Q'.ofNat carrierSize *
            (entry_error cutoff * entry_error cutoff)) ≤
        epsilon cutoff * epsilon cutoff
  epsilon_tends_zero :
    ∀ tolerance : Q', (0 : Q') < tolerance →
      { threshold : Nat //
        ∀ cutoff, threshold ≤ cutoff →
          epsilon cutoff ≤ tolerance }

namespace EntrywiseNormalizedSameCarrierMehlerConvergence

variable
  (convergence :
    EntrywiseNormalizedSameCarrierMehlerConvergence)

/-- Promote the entrywise estimate to the already-verified nonlinear
same-carrier Hilbert--Schmidt convergence layer. -/
def toHSConvergence :
    NormalizedSameCarrierMehlerHSConvergence where
  predecessor := convergence.predecessor
  nonlinear := convergence.nonlinear
  mehler := convergence.mehler
  approximation := convergence.approximation
  nonlinear_normalized :=
    convergence.nonlinear_normalized
  mehler_normalized :=
    convergence.mehler_normalized
  mehler_quadratic :=
    convergence.mehler_quadratic
  epsilon := convergence.epsilon
  epsilon_nonnegative :=
    convergence.epsilon_nonnegative
  hs_error := by
    intro cutoff
    exact Q'.le_trans' _ _ _
      (matrixHSSq_le_of_entrywise_abs
        (matrixDifference
          (vacuumRemovedMatrix
            (convergence.nonlinear cutoff)
            (convergence.predecessor cutoff))
          (vacuumRemovedMatrix
            (convergence.mehler cutoff)
            (convergence.predecessor cutoff)))
        (convergence.predecessor cutoff + 1)
        (convergence.entry_error cutoff)
        (convergence.entry_error_nonnegative cutoff)
        (convergence.entrywise_error cutoff))
      (convergence.dimension_error_balance cutoff)
  epsilon_tends_zero :=
    convergence.epsilon_tends_zero

/-- The entrywise formulation reaches the same eventual normalized
nonlinear Perron-ratio theorem. -/
def eventually_perronRatio_le_quarter :
    { threshold : Nat //
      ∀ cutoff, threshold ≤ cutoff →
        ∀ identification :
          NormalizedSameCarrierMehlerHSConvergence.PerronIdentification
            (vacuumRemovedMatrix
              (convergence.nonlinear cutoff)
              (convergence.predecessor cutoff))
            (convergence.predecessor cutoff + 1),
          identification.qS ≤ oneQuarter } := by
  obtain ⟨threshold, hthreshold⟩ :=
    convergence.toHSConvergence.eventually_perronRatio_le_quarter
  exact ⟨threshold, fun cutoff hcutoff identification =>
    hthreshold cutoff hcutoff identification⟩

end EntrywiseNormalizedSameCarrierMehlerConvergence

/-! ## 3. Literal matched-physical fixed-scale specialization -/

/-- Entrywise comparison data on the literal matched BF4 square section.
This is the fixed-scale form expected from a direct estimate on the grouped
Feynman--Kac entries. -/
structure MatchedEntrywiseCenteredMehlerComparison
    {family :
      BF4MatchedPhysicalAFBridge.MatchedBlockFamily}
    {g : Q'}
    (physical :
      MatchedUniformNormalizedSameCarrier
        (family := family) (g := g))
    (approximation : Nat) : Type 1 where
  mehler : RationalMatrix
  mehler_normalized :
    UniformNormalizedMatrix mehler physical.predecessor
  mehler_quadratic :
    ∀ vector,
      Q'.abs
          (matrixQuadratic
            (vacuumRemovedMatrix mehler physical.predecessor)
            vector (physical.predecessor + 1)) ≤
        gaussianPerronRatio.approx approximation *
          vectorNormSq vector (physical.predecessor + 1)
  entry_error : Q'
  entry_error_nonnegative : (0 : Q') ≤ entry_error
  entrywise_error :
    ∀ row, row < physical.predecessor + 1 →
      ∀ column, column < physical.predecessor + 1 →
        Q'.abs
            (matrixDifference
              physical.centeredPhysicalMatrix
              (vacuumRemovedMatrix mehler physical.predecessor)
              row column) ≤
          entry_error
  dimension_buffer :
    let carrierSize := physical.predecessor + 1
    Q'.ofNat carrierSize *
        (Q'.ofNat carrierSize *
          (entry_error * entry_error)) ≤
      sevenHundredths * sevenHundredths

namespace MatchedEntrywiseCenteredMehlerComparison

variable
    {family :
      BF4MatchedPhysicalAFBridge.MatchedBlockFamily}
    {g : Q'}
    {physical :
      MatchedUniformNormalizedSameCarrier
        (family := family) (g := g)}
    {approximation : Nat}
    (comparison :
      MatchedEntrywiseCenteredMehlerComparison
        physical approximation)

/-- Promote literal physical entry bounds to the existing fixed-scale
centered Mehler comparison. -/
def toCenteredComparison :
    MatchedCenteredMehlerComparison physical approximation where
  mehler := comparison.mehler
  mehler_normalized := comparison.mehler_normalized
  perturbation := {
    gaussianRate_nonnegative :=
      Q'.le_trans' _ _ _
        (by decide : (0 : Q') ≤ oneTwentieth)
        (oneTwentieth_le_ratio_approx approximation)
    epsilon_pos := by decide
    gaussian_quadratic :=
      comparison.mehler_quadratic
    nonlinear_gaussian_hs :=
      Q'.le_trans' _ _ _
        (matrixHSSq_le_of_entrywise_abs
          (matrixDifference
            physical.centeredPhysicalMatrix
            (vacuumRemovedMatrix
              comparison.mehler physical.predecessor))
          (physical.predecessor + 1)
          comparison.entry_error
          comparison.entry_error_nonnegative
          comparison.entrywise_error)
        comparison.dimension_buffer
  }

/-- Direct physical quarter theorem from entrywise grouped-kernel bounds. -/
theorem perronRatio_le_quarter
    (entryComparison :
      MatchedEntrywiseCenteredMehlerComparison
        physical approximation)
    (identification :
      NormalizedSameCarrierMehlerHSConvergence.PerronIdentification
        physical.centeredPhysicalMatrix
        (physical.predecessor + 1)) :
    identification.qS ≤ oneQuarter :=
  matchedCentered_perronRatio_le_quarter
    (toCenteredComparison entryComparison) identification

end MatchedEntrywiseCenteredMehlerComparison

#print axioms rowHSSq_le_of_entrywise_abs
#print axioms matrixHSSq_le_of_entrywise_abs
#print axioms EntrywiseNormalizedSameCarrierMehlerConvergence.toHSConvergence
#print axioms EntrywiseNormalizedSameCarrierMehlerConvergence.eventually_perronRatio_le_quarter
#print axioms MatchedEntrywiseCenteredMehlerComparison.toCenteredComparison
#print axioms MatchedEntrywiseCenteredMehlerComparison.perronRatio_le_quarter

end YMGap.Continuum.BF4EntrywiseSameCarrierHSConvergence
