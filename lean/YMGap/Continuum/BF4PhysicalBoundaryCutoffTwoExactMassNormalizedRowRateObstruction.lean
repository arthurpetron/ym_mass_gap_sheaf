/-
# The cutoff-two row-rate obstruction survives physical normalization

The production-kernel row-ten obstruction is first transported through the
common positive partition normalization.  Both the cleared centered row
distance and the product of component mass with row mass acquire the same
positive square of the normalization scale, so their strict inequality is
preserved exactly.

This is a finite diagnostic theorem.  It shows that row total variation is
too strong at cutoff two; it does not contradict the cancellation-preserving
`49/50` signed-form gap.  The subsequent canonical-state transport to the
named exact maximum `h_2` is deliberately left to a separate bridge module.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoExactRowRateObstruction
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalVacuumNormalizedGap

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoExactMassNormalizedRowRateObstruction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

open YMGap.Constructive
open YMGap.Continuum.BF4FiveHolonomyNormalizedKernel
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalVacuumNormalizedGap
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoExactRowRateObstruction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorPhysicalUpperGap
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelCertificate
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPartition

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num (q : Q') : (-q).num = -q.num := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num, Int.add_mul, Int.mul_add,
               Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one, Int.zero_mul, Int.mul_zero, Int.add_zero,
               Int.zero_add]; ac_rfl))

private theorem mul_eqv_congr_local {a b c d : Q'}
    (hac : a ≈ c) (hbd : b ≈ d) : a * b ≈ c * d :=
  Q'.eqv_trans _ (c * b) _
    (Q'.mul_eqv_congr_right _ _ b hac)
    (Q'.mul_eqv_congr_left c _ _ hbd)

/-! ## 1. Common normalization of the table data -/

theorem cutoffTwoSectorNormalizedKernel_eqv_physical_mul_rowRateReciprocal
    (row column : Nat) :
    cutoffTwoSectorNormalizedKernel row column ≈
      cutoffTwoSectorPhysicalKernel row column *
        cutoffTwoPartitionReciprocalSealed :=
  cutoffTwoSectorNormalizedKernel_eqv_scaledSealed

theorem cutoffTwoSectorNormalizedRowSum_eqv_physical_mul_rowRateReciprocal
    (row : Nat) :
    cutoffTwoSectorNormalizedRowSum row ≈
      cutoffTwoSectorPhysicalRowSum row *
        cutoffTwoPartitionReciprocalSealed :=
  cutoffTwoSectorNormalizedRowSum_eqv_scaledSealed row

def cutoffTwoSectorNormalizedMass : Q' :=
  listQSum cutoffTwoSectorNormalizedRowSum (List.range 65)

theorem cutoffTwoSectorNormalizedMass_eqv_physical_mul_rowRateReciprocal :
    cutoffTwoSectorNormalizedMass ≈
      cutoffTwoSectorPhysicalMass * cutoffTwoPartitionReciprocalSealed := by
  unfold cutoffTwoSectorNormalizedMass cutoffTwoSectorPhysicalMass
  refine Q'.eqv_trans _
    (listQSum
      (fun row => cutoffTwoSectorPhysicalRowSum row *
        cutoffTwoPartitionReciprocalSealed)
      (List.range 65)) _ ?_ ?_
  · apply listQSum_congr_on
    intro row _
    exact
      cutoffTwoSectorNormalizedRowSum_eqv_physical_mul_rowRateReciprocal
        row
  · exact listQSum_mul_right _ _ _

theorem cutoffTwoSectorPhysicalMass_pos :
    (0 : Q') < cutoffTwoSectorPhysicalMass := by
  have hmass : cutoffTwoSectorPhysicalMass ≈
      cutoffTwoSectorRawMassValue :=
    Q'.eqv_trans _ _ _ cutoffTwoSectorPhysicalMass_eqv_rawMass
      cutoffTwoSectorRawMass_eqv_value
  exact Q'.pos_of_lt_of_le cutoffTwoSectorRawMassValue_pos
    (Q'.ge_of_eqv hmass)

theorem cutoffTwoSectorNormalizedMass_pos :
    (0 : Q') < cutoffTwoSectorNormalizedMass := by
  exact Q'.pos_of_lt_of_le
    (Q'.mul_pos cutoffTwoSectorPhysicalMass_pos
      cutoffTwoPartitionReciprocalSealed_pos)
    (Q'.ge_of_eqv
      cutoffTwoSectorNormalizedMass_eqv_physical_mul_rowRateReciprocal)

def cutoffTwoSectorNormalizedClearedMassNormalizedRowDistance
    (mass : Q') (row : Nat) : Q' :=
  listQSum
    (fun column =>
      Q'.abs
        (mass * cutoffTwoSectorNormalizedKernel row column +
          (-(cutoffTwoSectorNormalizedRowSum row *
            cutoffTwoSectorNormalizedRowSum column))))
    (List.range 65)

private theorem clearedMassNormalizedRowDistance_eqv_scaled_generic
    (normalizedKernel physicalKernel : Nat → Nat → Q')
    (normalizedRowSum physicalRowSum : Nat → Q')
    (normalizedMass physicalMass scale : Q')
    (hmass : normalizedMass ≈ physicalMass * scale)
    (hkernel : ∀ row column : Nat,
      normalizedKernel row column ≈ physicalKernel row column * scale)
    (hrowSum : ∀ row : Nat,
      normalizedRowSum row ≈ physicalRowSum row * scale)
    (hscaleSqNonnegative : (0 : Q') ≤ scale * scale)
    (row : Nat) :
    listQSum
        (fun column =>
          Q'.abs
            (normalizedMass * normalizedKernel row column +
              (-(normalizedRowSum row * normalizedRowSum column))))
        (List.range 65) ≈
      listQSum
          (fun column =>
            Q'.abs
              (physicalMass * physicalKernel row column +
                (-(physicalRowSum row * physicalRowSum column))))
          (List.range 65) *
        (scale * scale) := by
  let scaleSq := scale * scale
  refine Q'.eqv_trans _
    (listQSum
      (fun column =>
        Q'.abs
          ((physicalMass * physicalKernel row column +
            (-(physicalRowSum row * physicalRowSum column))) * scaleSq))
      (List.range 65)) _ ?_ ?_
  · apply listQSum_congr_on
    intro column _
    apply Q'.abs_eqv_congr
    refine Q'.eqv_trans _
      ((physicalMass * scale) *
            (physicalKernel row column * scale) +
        (-((physicalRowSum row * scale) *
          (physicalRowSum column * scale)))) _ ?_ ?_
    · apply Q'.add_eqv_congr'
      · exact mul_eqv_congr_local hmass (hkernel row column)
      · exact Q'.neg_eqv_congr _ _
          (mul_eqv_congr_local (hrowSum row) (hrowSum column))
    · change
        (physicalMass * scale) *
              (physicalKernel row column * scale) +
            -((physicalRowSum row * scale) *
              (physicalRowSum column * scale)) ≈
          (physicalMass * physicalKernel row column +
            -(physicalRowSum row * physicalRowSum column)) * scaleSq
      dsimp [scaleSq]
      ring_qeqv
  · refine Q'.eqv_trans _
      (listQSum
        (fun column =>
          Q'.abs
            (physicalMass * physicalKernel row column +
              -(physicalRowSum row * physicalRowSum column)) * scaleSq)
        (List.range 65)) _ ?_ ?_
    · apply listQSum_congr_on
      intro column _
      exact YMGap.Continuum.TsumDeriv.abs_mul_nonneg_right _
        hscaleSqNonnegative
    · exact listQSum_mul_right _ _ _

theorem cutoffTwoSectorNormalizedClearedMassNormalizedRowDistance_eqv_scaled
    (row : Nat) :
    cutoffTwoSectorNormalizedClearedMassNormalizedRowDistance
        cutoffTwoSectorNormalizedMass row ≈
      cutoffTwoSectorPhysicalClearedMassNormalizedRowDistance
          cutoffTwoSectorPhysicalMass row *
        (cutoffTwoPartitionReciprocalSealed *
          cutoffTwoPartitionReciprocalSealed) := by
  let scale := cutoffTwoPartitionReciprocalSealed
  have hscaleSqNonnegative : (0 : Q') ≤ scale * scale :=
    Q'.mul_nonneg _ _
      (Q'.le_of_lt cutoffTwoPartitionReciprocalSealed_pos)
      (Q'.le_of_lt cutoffTwoPartitionReciprocalSealed_pos)
  unfold cutoffTwoSectorNormalizedClearedMassNormalizedRowDistance
    cutoffTwoSectorPhysicalClearedMassNormalizedRowDistance
  exact clearedMassNormalizedRowDistance_eqv_scaled_generic
    cutoffTwoSectorNormalizedKernel
    cutoffTwoSectorPhysicalKernel
    cutoffTwoSectorNormalizedRowSum
    cutoffTwoSectorPhysicalRowSum
    cutoffTwoSectorNormalizedMass
    cutoffTwoSectorPhysicalMass
    scale
    cutoffTwoSectorNormalizedMass_eqv_physical_mul_rowRateReciprocal
    cutoffTwoSectorNormalizedKernel_eqv_physical_mul_rowRateReciprocal
    cutoffTwoSectorNormalizedRowSum_eqv_physical_mul_rowRateReciprocal
    hscaleSqNonnegative row

private theorem strictRowObstruction_of_commonPositiveScale
    (normalizedMass normalizedRowSum normalizedCleared : Q')
    (physicalMass physicalRowSum physicalCleared scale : Q')
    (hmass : normalizedMass ≈ physicalMass * scale)
    (hrowSum : normalizedRowSum ≈ physicalRowSum * scale)
    (hcleared : normalizedCleared ≈
      physicalCleared * (scale * scale))
    (hphysical : physicalMass * physicalRowSum < physicalCleared)
    (hscalePos : (0 : Q') < scale) :
    normalizedMass * normalizedRowSum < normalizedCleared := by
  let scaleSq := scale * scale
  have hscaleSqPos : (0 : Q') < scaleSq :=
    Q'.mul_pos hscalePos hscalePos
  have hscaled :=
    YMGap.Continuum.ClusteringImpliesGap.mul_lt_mul_of_pos_right
      hscaleSqPos hphysical
  have hleft :
      normalizedMass * normalizedRowSum ≈
        (physicalMass * physicalRowSum) * scaleSq := by
    refine Q'.eqv_trans _
      ((physicalMass * scale) * (physicalRowSum * scale)) _ ?_ ?_
    · exact mul_eqv_congr_local hmass hrowSum
    · change
        (physicalMass * scale) * (physicalRowSum * scale) ≈
          (physicalMass * physicalRowSum) * scaleSq
      dsimp [scaleSq]
      ring_qeqv
  exact YMGap.Continuum.ClusteringImpliesGap.lt_of_lt_of_le
    (Q'.lt_of_le_of_lt (Q'.le_of_eqv hleft) hscaled)
    (Q'.ge_of_eqv hcleared)

theorem cutoffTwoSectorNormalizedClearedRowTen_gt_mass_mul_rowSum :
    cutoffTwoSectorNormalizedMass * cutoffTwoSectorNormalizedRowSum 10 <
      cutoffTwoSectorNormalizedClearedMassNormalizedRowDistance
        cutoffTwoSectorNormalizedMass 10 := by
  let scale := cutoffTwoPartitionReciprocalSealed
  exact strictRowObstruction_of_commonPositiveScale
    cutoffTwoSectorNormalizedMass
    (cutoffTwoSectorNormalizedRowSum 10)
    (cutoffTwoSectorNormalizedClearedMassNormalizedRowDistance
      cutoffTwoSectorNormalizedMass 10)
    cutoffTwoSectorPhysicalMass
    (cutoffTwoSectorPhysicalRowSum 10)
    (cutoffTwoSectorPhysicalClearedMassNormalizedRowDistance
      cutoffTwoSectorPhysicalMass 10)
    scale
    cutoffTwoSectorNormalizedMass_eqv_physical_mul_rowRateReciprocal
    (cutoffTwoSectorNormalizedRowSum_eqv_physical_mul_rowRateReciprocal 10)
    (cutoffTwoSectorNormalizedClearedMassNormalizedRowDistance_eqv_scaled 10)
    cutoffTwoSectorPhysicalClearedRowTen_gt_mass_mul_rowSum
    cutoffTwoPartitionReciprocalSealed_pos

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoExactMassNormalizedRowRateObstruction

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoExactMassNormalizedRowRateObstruction.cutoffTwoSectorNormalizedMass_eqv_physical_mul_rowRateReciprocal
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoExactMassNormalizedRowRateObstruction.cutoffTwoSectorNormalizedClearedMassNormalizedRowDistance_eqv_scaled
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoExactMassNormalizedRowRateObstruction.cutoffTwoSectorNormalizedClearedRowTen_gt_mass_mul_rowSum
