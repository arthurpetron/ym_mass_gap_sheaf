/-
# Cofinal removal of the physical spin cutoff in one finite Z4 box

At the repository's exact heat-kernel coupling `1/2`, the adjacent interacting
cutoff increment has a dyadic bound along the volume-dependent schedule from
`Z4AdjacentCutoffDyadicSchedule`.  Here adjacent increments are shown to add
exactly, are summed by a finite geometric series, and yield a depth-uniform
cutoff-extension modulus.

For each fixed finite box this constructs a genuine `CReal` limit of the
fusion-complete partition as the representation cutoff tends to infinity.
This is cutoff removal at fixed lattice spacing and fixed finite volume; it is
not an infinite-volume or continuum Yang--Mills construction.
-/

import YMGap.Continuum.KPLimit
import YMGap.Continuum.Z4AdjacentCutoffDyadicSchedule

namespace YMGap.Continuum.Z4InteractingCutoffCofinal

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.Z4AdjacentCutoffDyadicSchedule
open YMGap.Continuum.Z4FiniteGraphVacuumFloor
open YMGap.Continuum.Z4PhysicalCutoffPartitionMonotonicity

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Exact additivity of the interacting new-label sector -/

theorem fusionCompleteCutoffIncrement_additive
    {K M L n : Nat} (hKM : K ≤ M) (hML : M ≤ L) :
    fusionCompleteCutoffIncrement K L n ≈
      fusionCompleteCutoffIncrement K M n +
        fusionCompleteCutoffIncrement M L n := by
  let ZK := fusionCompleteVertexPartition K n
  let ZM := fusionCompleteVertexPartition M n
  let ZL := fusionCompleteVertexPartition L n
  have hKL : K ≤ L := Nat.le_trans hKM hML
  have hwhole : ZL + -ZK ≈ fusionCompleteCutoffIncrement K L n :=
    fusionCompleteVertexPartition_difference_eq_increment hKL
  have hleft : ZM + -ZK ≈ fusionCompleteCutoffIncrement K M n :=
    fusionCompleteVertexPartition_difference_eq_increment hKM
  have hright : ZL + -ZM ≈ fusionCompleteCutoffIncrement M L n :=
    fusionCompleteVertexPartition_difference_eq_increment hML
  have hmiddle :
      (ZM + -ZK) + (ZL + -ZM) ≈ ZL + -ZK := by
    refine Q'.eqv_trans _ ((ZM + -ZK) + (-ZM + ZL)) _ ?_ ?_
    · exact Q'.add_eqv_congr_left _ _ _ (Q'.add_comm_eqv ZL (-ZM))
    refine Q'.eqv_trans _ ((ZM + -ZM) + (-ZK + ZL)) _
      (Q'.add_swap_inner ZM (-ZK) (-ZM) ZL) ?_
    refine Q'.eqv_trans _ ((0 : Q') + (-ZK + ZL)) _
      (Q'.add_eqv_congr_right _ _ _ (Q'.add_neg_self_eqv ZM)) ?_
    refine Q'.eqv_trans _ (-ZK + ZL) _
      (Q'.eqv_of_eq (Q'.zero_add' (-ZK + ZL))) ?_
    exact Q'.add_comm_eqv _ _
  refine Q'.eqv_trans _ (ZL + -ZK) _ (Q'.eqv_symm hwhole) ?_
  refine Q'.eqv_trans _ ((ZM + -ZK) + (ZL + -ZM)) _ ?_ ?_
  · exact Q'.eqv_symm hmiddle
  · exact Q'.add_eqv_congr' hleft hright

def adjacentCutoffIncrementSum (K depth n : Nat) : Q' :=
  finSum
    (fun offset =>
      fusionCompleteCutoffIncrement (K + offset) (K + offset + 1) n)
    depth

/-- A finite extension is exactly the sum of its adjacent new-label sectors. -/
theorem fusionCompleteCutoffIncrement_eqv_adjacentSum (K n : Nat) :
    ∀ depth : Nat,
      fusionCompleteCutoffIncrement K (K + depth) n ≈
        adjacentCutoffIncrementSum K depth n
  | 0 => by
      unfold adjacentCutoffIncrementSum
      rw [finSum_zero, Nat.add_zero]
      have hdiff := fusionCompleteVertexPartition_difference_eq_increment
        (K := K) (L := K) (n := n) (Nat.le_refl K)
      exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hdiff)
        (Q'.add_neg_self_eqv (fusionCompleteVertexPartition K n))
  | depth + 1 => by
      unfold adjacentCutoffIncrementSum
      rw [finSum_succ]
      have hindex : K + (depth + 1) = K + depth + 1 := by omega
      rw [hindex]
      have hadd := fusionCompleteCutoffIncrement_additive
        (K := K) (M := K + depth) (L := K + depth + 1) (n := n)
        (by omega) (by omega)
      exact Q'.eqv_trans _ _ _ hadd
        (Q'.add_eqv_congr'
          (fusionCompleteCutoffIncrement_eqv_adjacentSum K n depth)
          (Q'.eqv_refl _))

/-! ## 2. Geometric resummation along the derived schedule -/

private theorem interactingAdjacentCutoff_add (stage offset n : Nat) :
    interactingAdjacentCutoff stage n + offset =
      interactingAdjacentCutoff (stage + offset) n := by
  unfold interactingAdjacentCutoff
  omega

theorem scheduledAdjacentCutoffIncrementSum_le_two_halfPow
    (stage depth n : Nat) :
    adjacentCutoffIncrementSum (interactingAdjacentCutoff stage n) depth n ≤
      Q'.ofNat 2 * (HalfPow.half ^ stage) := by
  have hterm : ∀ offset,
      fusionCompleteCutoffIncrement
          (interactingAdjacentCutoff stage n + offset)
          (interactingAdjacentCutoff stage n + offset + 1) n ≤
        (HalfPow.half ^ stage) * (HalfPow.half ^ offset) := by
    intro offset
    rw [interactingAdjacentCutoff_add stage offset n]
    have hinc := interactingAdjacentCutoff_increment_le_halfPow
      (stage + offset) n
    exact Q'.le_trans' _ _ _ hinc
      (Q'.le_of_eqv (Q'.pow_add_eqv HalfPow.half stage offset))
  unfold adjacentCutoffIncrementSum
  have hsum := ExpNeg.finSum_le_finSum_of_termwise
    (fun offset =>
      fusionCompleteCutoffIncrement
        (interactingAdjacentCutoff stage n + offset)
        (interactingAdjacentCutoff stage n + offset + 1) n)
    (fun offset => (HalfPow.half ^ stage) * (HalfPow.half ^ offset))
    hterm depth
  exact Q'.le_trans' _ _ _ hsum
    (geom_half_series_le (HalfPow.half ^ stage)
      (Q'.pow_nonneg _ HalfPow.half_nonneg stage) depth)

/-- Every finite extension above a scheduled cutoff has one depth-independent
dyadic bound. -/
theorem scheduledCutoffIncrement_le_two_halfPow
    (stage depth n : Nat) :
    fusionCompleteCutoffIncrement
        (interactingAdjacentCutoff stage n)
        (interactingAdjacentCutoff stage n + depth) n ≤
      Q'.ofNat 2 * (HalfPow.half ^ stage) := by
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (fusionCompleteCutoffIncrement_eqv_adjacentSum
        (interactingAdjacentCutoff stage n) n depth))
    (scheduledAdjacentCutoffIncrementSum_le_two_halfPow stage depth n)

theorem scheduledPartition_abs_cutoff_difference_le_two_halfPow
    (stage depth n : Nat) :
    absQ
        (fusionCompleteVertexPartition
            (interactingAdjacentCutoff stage n + depth) n +
          -fusionCompleteVertexPartition
            (interactingAdjacentCutoff stage n) n) ≤
      Q'.ofNat 2 * (HalfPow.half ^ stage) := by
  have habs := fusionCompleteVertexPartition_abs_difference_eq_increment
    (K := interactingAdjacentCutoff stage n)
    (L := interactingAdjacentCutoff stage n + depth)
    (n := n) (by omega)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv habs)
    (scheduledCutoffIncrement_le_two_halfPow stage depth n)

theorem scheduledPartition_relative_cutoff_le_two_halfPow
    (stage depth n : Nat) :
    absQ
        (Q'.divPos
            (fusionCompleteVertexPartition
              (interactingAdjacentCutoff stage n + depth) n)
            (fusionCompleteVertexPartition
              (interactingAdjacentCutoff stage n) n)
            (fusionCompleteVertexPartition_pos
              (interactingAdjacentCutoff stage n) n) +
          -(1 : Q')) ≤
      Q'.ofNat 2 * (HalfPow.half ^ stage) := by
  have hrelative := fusionCompleteVertexPartition_relative_cutoff_increment
    (K := interactingAdjacentCutoff stage n)
    (L := interactingAdjacentCutoff stage n + depth)
    (n := n) (by omega)
  exact Q'.le_trans' _ _ _ hrelative
    (scheduledCutoffIncrement_le_two_halfPow stage depth n)

/-! ## 3. The fixed-box constructive cutoff limit -/

def interactingCutoffPartitionSequence (n stage : Nat) : Q' :=
  fusionCompleteVertexPartition (interactingAdjacentCutoff stage n) n

theorem interactingCutoffPartitionSequence_step_eqv (n stage : Nat) :
    interactingCutoffPartitionSequence n (stage + 1) ≈
      interactingCutoffPartitionSequence n stage +
        fusionCompleteCutoffIncrement
          (interactingAdjacentCutoff stage n)
          (interactingAdjacentCutoff stage n + 1) n := by
  have hcutoff : interactingAdjacentCutoff (stage + 1) n =
      interactingAdjacentCutoff stage n + 1 := by
    unfold interactingAdjacentCutoff
    omega
  unfold interactingCutoffPartitionSequence
  rw [hcutoff]
  exact fusionCompleteVertexPartition_eq_base_add_increment (by omega)

theorem interactingCutoffPartitionSequence_step_upper (n stage : Nat) :
    interactingCutoffPartitionSequence n (stage + 1) ≤
      interactingCutoffPartitionSequence n stage +
        geoIncr 1 stage := by
  have heq := interactingCutoffPartitionSequence_step_eqv n stage
  have hinc := interactingAdjacentCutoff_increment_le_halfPow stage n
  have hgeo : HalfPow.half ^ stage ≤ geoIncr 1 stage :=
    Q'.le_of_eqv (Q'.eqv_symm (Q'.one_mul_eqv _))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv heq)
    (Q'.add_le_add_left _ _ _ (Q'.le_trans' _ _ _ hinc hgeo))

theorem interactingCutoffPartitionSequence_step_lower (n stage : Nat) :
    interactingCutoffPartitionSequence n stage ≤
      interactingCutoffPartitionSequence n (stage + 1) +
        geoIncr 1 stage := by
  have hcutoff : interactingAdjacentCutoff stage n ≤
      interactingAdjacentCutoff (stage + 1) n := by
    unfold interactingAdjacentCutoff
    omega
  have hmono : interactingCutoffPartitionSequence n stage ≤
      interactingCutoffPartitionSequence n (stage + 1) := by
    unfold interactingCutoffPartitionSequence
    exact fusionCompleteVertexPartition_mono hcutoff
  exact Q'.le_trans' _ _ _ hmono
    (Q'.add_le_self_of_nonneg _ _ (geoIncr_nonneg 1 Q'.zero_le_one stage))

/-- The fusion-complete finite-box partition has a constructive representation-
cutoff limit at the exact coupling used by this spin-foam development. -/
def interactingCutoffPartitionLimit (n : Nat) : CReal :=
  crealOfGeoIncrement (interactingCutoffPartitionSequence n)
    1 Q'.zero_le_one
    (interactingCutoffPartitionSequence_step_upper n)
    (interactingCutoffPartitionSequence_step_lower n)
    (fun ε hε => by
      refine ⟨HalfPow.half * ε, ExpNeg.half_mul_pos ε hε, ?_⟩
      show (Q'.ofNat 2 * 1) * (HalfPow.half * ε) ≤ ε
      refine Q'.le_of_eqv ?_
      refine Q'.eqv_trans _
        (Q'.ofNat 2 * (HalfPow.half * ε)) _
        (Q'.mul_eqv_congr_right _ _ _
          (Q'.mul_one_eqv (Q'.ofNat 2))) ?_
      refine Q'.eqv_trans _
        ((Q'.ofNat 2 * HalfPow.half) * ε) _
        (Q'.eqv_symm
          (Q'.mul_assoc_eqv (Q'.ofNat 2) HalfPow.half ε)) ?_
      refine Q'.eqv_trans _ ((1 : Q') * ε) _
        (Q'.mul_eqv_congr_right _ _ _ (by decide)) ?_
      exact Q'.one_mul_eqv ε)

@[simp] theorem interactingCutoffPartitionLimit_approx (n stage : Nat) :
    (interactingCutoffPartitionLimit n).approx stage =
      interactingCutoffPartitionSequence n stage := rfl

end YMGap.Continuum.Z4InteractingCutoffCofinal

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4InteractingCutoffCofinal.fusionCompleteCutoffIncrement_additive
#print axioms YMGap.Continuum.Z4InteractingCutoffCofinal.fusionCompleteCutoffIncrement_eqv_adjacentSum
#print axioms YMGap.Continuum.Z4InteractingCutoffCofinal.scheduledCutoffIncrement_le_two_halfPow
#print axioms YMGap.Continuum.Z4InteractingCutoffCofinal.scheduledPartition_relative_cutoff_le_two_halfPow
#print axioms YMGap.Continuum.Z4InteractingCutoffCofinal.interactingCutoffPartitionLimit
#print axioms YMGap.Continuum.Z4InteractingCutoffCofinal.interactingCutoffPartitionLimit_approx
