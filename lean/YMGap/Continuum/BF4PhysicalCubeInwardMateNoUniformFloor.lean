/-
# No cutoff-uniform direct inward-mate transition floor

At every fixed `0 < w <= 1/2`, including the physical anchor `w=1/400`,
an explicit cofinal family in the actual vacuum component has direct-mate
conditional probability at most `w^(4k+2)`. All probabilities use the original
partition-normalized reflected joint kernel and its own row marginal.

This refutes a state/cutoff-uniform lower bound for that SINGLE selected
transition. It does not refute a spectral gap, a weighted family of moves,
an averaged traffic bound, or any existing conditional proof compiler.
-/

import YMGap.Continuum.BF4PhysicalCubeInwardMateCompetitor
import YMGap.Constructive.HalfPow

namespace YMGap.Continuum.BF4PhysicalCubeInwardMateNoUniformFloor

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4PhysicalCubeInwardMateCompetitor
open YMGap.Continuum.BF4PhysicalCubeDifferenceBoundaryKernel
open YMGap.Continuum.BF4PhysicalVacuumSectorCubeClassification
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateOrbits
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalSpinCubeRawReturnRatio
open YMGap.Continuum.BF4PhysicalCutoffKernelSupportPersistence
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram

local infix:50 " ≈ " => Q'.eqv

theorem source_common_parity (k : Nat) : CubeSupportedCommonParity (source k) := by
  refine ⟨profile_zero_off _ _, ?_⟩
  intro face hf
  by_cases hz : face = 0 <;> simp [source, profile, hz, hf]

/-- The counterexample sources lie in the actual root vacuum component,
not merely in the larger positive carrier. -/
theorem source_in_vacuum_sector {w : Q'} (hw : (0 : Q') < w) (K k : Nat)
    (hK : 2 * k + 14 ≤ K) :
    source k ∈ centralPhysicalFiniteVacuumSectorStates w (Q'.le_of_lt hw) K 0 :=
  cubeSupportedCommonParity_mem_sector hw K (by omega) (source k)
    (fun face _ => profile_bounded _ _ K hK (by omega) face) (source_common_parity k)

theorem source_retained {w : Q'} (hw : (0 : Q') < w) (K k : Nat) (hK : 2 * k + 14 ≤ K) :
    source k ∈ centralPositiveHalfStates w (Q'.le_of_lt hw) K 0 :=
  cubeSupported_mem_positiveHalfStates hw K (by omega) (source k)
    (fun face _ => profile_bounded _ _ K hK (by omega) face) (profile_zero_off _ _)

theorem competitor_retained {w : Q'} (hw : (0 : Q') < w) (K k : Nat) (hK : 2 * k + 14 ≤ K) :
    competitor k ∈ centralPositiveHalfStates w (Q'.le_of_lt hw) K 0 :=
  cubeSupported_mem_positiveHalfStates hw K (by omega) (competitor k)
    (fun face _ => profile_bounded _ _ K (by omega) (by omega) face) (profile_zero_off _ _)

/-- Conditional probability from the actual normalized joint and its own
stationary marginal; the target is the literal mate by `source_mate`. -/
def mateProbability {w : Q'} (hw : (0 : Q') < w) (K k : Nat) (hK : 2 * k + 14 ≤ K) : Q' :=
  Q'.divPos
    (centralNormalizedPhysicalReflectedKernel w (Q'.le_of_lt hw) K 0 (source k) (mate k))
    (centralPhysicalRowMarginal w (Q'.le_of_lt hw) K 0 (source k))
    (mem_centralPositiveHalfStates_iff.mp (source_retained hw K k hK)).2

private theorem member_le_sum {A : Type} (value : A → Q')
    (hn : ∀ x, (0 : Q') ≤ value x) :
    ∀ (xs : List A) {x : A}, x ∈ xs → value x ≤ listQSum value xs
  | [], _, h => by cases h
  | y :: ys, x, h => by
      rcases List.mem_cons.mp h with he | ht
      · subst x
        exact Q'.add_le_self_of_nonneg _ _ (listQSum_nonnegative_on _ _ (fun z _ => hn z))
      · have hmono := Q'.add_le_add_right (0 : Q') (value y) (listQSum value ys) (hn y)
        rw [Q'.zero_add'] at hmono
        exact Q'.le_trans' _ _ _ (member_le_sum value hn ys ht) hmono

/-- For all admitted cutoffs, the selected direct transition is geometrically
small along the explicit family. The common partition factor cancels. -/
theorem probability_upper {w : Q'} (hw : (0 : Q') < w) (K k : Nat) (hK : 2 * k + 14 ≤ K) :
    mateProbability hw K k hK ≤ qpow w (4 * k + 2) := by
  have hb := member_le_sum (centralPhysicalReflectedKernel w K 0 (source k))
    (fun target => centralPhysicalReflectedKernel_nonnegative (Q'.le_of_lt hw) K 0 (source k) target)
    (centralPositiveHalfStates w (Q'.le_of_lt hw) K 0) (competitor_retained hw K k hK)
  have he := centralNormalizedPhysicalReturn_eqv_rawRatio (source_retained hw K k hK) (mate k)
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv he) ?_
  apply Q'.divPos_le_of_le_mul
  exact Q'.le_trans' _ _ _ (kernel_comparison (Q'.le_of_lt hw) K k hK)
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hb (qpow_nonneg w (Q'.le_of_lt hw) _))

private theorem half_fold : ∀ n : Nat, qpow HalfPow.half n ≈ HalfPow.half ^ n
  | 0 => Q'.eqv_refl _
  | n + 1 => Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (half_fold n))
      (Q'.mul_comm_eqv _ _)

/-- Explicit index attaining tolerance beyond any requested cutoff threshold.
This is data, not an existentially hidden modulus. -/
def smallIndex (epsilon : Q') (start : Nat) : Nat := epsilon.den + start

def smallCutoff (epsilon : Q') (start : Nat) : Nat := 2 * smallIndex epsilon start + 14

theorem smallCutoff_cofinal (epsilon : Q') (start : Nat) : start ≤ smallCutoff epsilon start := by
  unfold smallCutoff smallIndex
  omega

/-- Uniform in all cutoffs admitting the displayed source, at a FIXED nome
in `(0,1/2]`. Dependence on tolerance and the cofinal threshold is explicit. -/
theorem probability_small {w : Q'} (hw : (0 : Q') < w) (hwHalf : w ≤ HalfPow.half)
    (epsilon : Q') (he : (0 : Q') < epsilon) (start K : Nat)
    (hK : smallCutoff epsilon start ≤ K) :
    mateProbability hw K (smallIndex epsilon start) hK ≤ epsilon := by
  refine Q'.le_trans' _ _ _ (probability_upper hw K _ hK) ?_
  refine Q'.le_trans' _ _ _ (HeatKernelGap.qpow_mono (Q'.le_of_lt hw) hwHalf _) ?_
  refine Q'.le_trans' _ _ _ (qpow_antitone (by decide) (by decide) epsilon.den _
    (by unfold smallIndex; omega)) ?_
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (half_fold _)) (HalfPow.pow_half_le epsilon he)

/-- No positive direct-mate floor even on this root-sector family, even
after discarding an arbitrary initial range of spin cutoffs. -/
theorem no_cofinal_uniform_direct_mate_floor {w : Q'} (hw : (0 : Q') < w)
    (hwHalf : w ≤ HalfPow.half) (delta : Q') (hd : (0 : Q') < delta) (start : Nat) :
    ¬ (∀ K, start ≤ K → ∀ k (hK : 2 * k + 14 ≤ K), delta ≤ mateProbability hw K k hK) := by
  intro floor
  let epsilon := delta * HalfPow.half
  have he : (0 : Q') < epsilon := Q'.mul_pos hd (by decide)
  have hu := probability_small hw hwHalf epsilon he start (smallCutoff epsilon start) (Nat.le_refl _)
  have hl := floor (smallCutoff epsilon start) (smallCutoff_cofinal epsilon start)
    (smallIndex epsilon start) (Nat.le_refl _)
  have hbad : delta * 1 ≤ delta * HalfPow.half := Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.mul_one_eqv delta)) (Q'.le_trans' _ _ _ hl hu)
  have h := Q'.le_of_mul_le_mul_left hbad hd
  exact (by decide : ¬ ((1 : Q') ≤ HalfPow.half)) h

end YMGap.Continuum.BF4PhysicalCubeInwardMateNoUniformFloor

#print axioms YMGap.Continuum.BF4PhysicalCubeInwardMateNoUniformFloor.source_common_parity
#print axioms YMGap.Continuum.BF4PhysicalCubeInwardMateNoUniformFloor.source_in_vacuum_sector
#print axioms YMGap.Continuum.BF4PhysicalCubeInwardMateNoUniformFloor.source_retained
#print axioms YMGap.Continuum.BF4PhysicalCubeInwardMateNoUniformFloor.competitor_retained
#print axioms YMGap.Continuum.BF4PhysicalCubeInwardMateNoUniformFloor.mateProbability
#print axioms YMGap.Continuum.BF4PhysicalCubeInwardMateNoUniformFloor.probability_upper
#print axioms YMGap.Continuum.BF4PhysicalCubeInwardMateNoUniformFloor.smallIndex
#print axioms YMGap.Continuum.BF4PhysicalCubeInwardMateNoUniformFloor.smallCutoff
#print axioms YMGap.Continuum.BF4PhysicalCubeInwardMateNoUniformFloor.smallCutoff_cofinal
#print axioms YMGap.Continuum.BF4PhysicalCubeInwardMateNoUniformFloor.probability_small
#print axioms YMGap.Continuum.BF4PhysicalCubeInwardMateNoUniformFloor.no_cofinal_uniform_direct_mate_floor
