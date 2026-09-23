/-
# High-label trace at every positive subunit nome

This is the same literal high-label trace as the existing small-nome route.
Only the shell estimate and its radial tail are replaced by the explicit
nome-dependent subunit envelopes.
-/

import YMGap.Continuum.BF4PhysicalCubeSubunitBoundarySumBound
import YMGap.Continuum.BF4PhysicalCubeSubunitRadialTail
import YMGap.Continuum.BF4PhysicalCubeHighLabelTrace
import YMGap.Continuum.BF4PhysicalCubeNewTailTraceBound

namespace YMGap.Continuum.BF4PhysicalCubeSubunitHighLabelTrace

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.BF4PhysicalCubeBalancedDescent
open YMGap.Continuum.BF4PhysicalCubeGaussianReturn
open YMGap.Continuum.BF4PhysicalCubeSubunitBoundarySumBound
open YMGap.Continuum.BF4PhysicalCubeSubunitRadialTail
open YMGap.Continuum.BF4PhysicalCubeHighLabelTrace
open YMGap.Continuum.BF4PhysicalCubeNewTailTraceBound
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorBlockDecomposition
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGram
open YMGap.Continuum.BF4PhysicalVacuumSectorCenteredHeadTailTraceGap
open YMGap.Continuum.BF4PhysicalVacuumSectorCenteredTailTrace
open YMGap.Continuum.BF4PhysicalVacuumSectorHeadTailGramGap
open YMGap.Continuum.BF4PhysicalVacuumSectorCubeClassification
open YMGap.Continuum.BF4PhysicalVacuumSectorCubeContainment
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.GenuineResidualDefect
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

local macro "q_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.mul_num_cast, Q'.mul_den_cast];
             try ac_rfl))

private theorem count_regroup (n c p : Q') :
    n * ((c * n) * p) ≈ (c * (n * n)) * p := by q_ring

private theorem sum_le {A : Type} (f g : A → Q') : ∀ xs,
    (∀ x, x ∈ xs → f x ≤ g x) → listQSum f xs ≤ listQSum g xs
  | [], _ => Q'.le_refl' 0
  | x :: xs, h => Q'.add_le_add (h x List.mem_cons_self)
      (sum_le f g xs (fun y hy => h y (List.mem_cons_of_mem x hy)))

private theorem sum_le_length {A : Type} (value : A → Q') (bound : Q') : ∀ xs,
    (∀ x, x ∈ xs → value x ≤ bound) → listQSum value xs ≤ Q'.ofNat xs.length * bound
  | [], _ => Q'.ge_of_eqv (Q'.zero_mul_eqv bound)
  | x :: xs, h => by
      refine Q'.le_trans' _ _ _ (Q'.add_le_add (h x List.mem_cons_self)
        (sum_le_length value bound xs (fun y hy => h y (List.mem_cons_of_mem x hy)))) ?_
      apply Q'.ge_of_eqv
      refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ bound (Q'.ofNat_add_eqv xs.length 1)) ?_
      refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv _ _ _) ?_
      exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ (Q'.one_mul_eqv bound)) (Q'.add_comm_eqv _ _)

private theorem fsum_mask (f : Nat → Q') (N : Nat) : ∀ L,
    fsum (fun M => if N ≤ M then f M else 0) L =
      fsum (fun k => f (N + k)) (L - N)
  | 0 => by rw [Nat.zero_sub]; rfl
  | L + 1 => by
      rw [fsum_succ, fsum_mask f N L]
      by_cases h : N ≤ L
      · rw [if_pos h, show L + 1 - N = (L - N) + 1 by omega, fsum_succ]
        rw [show N + (L - N) = L by omega]
      · rw [if_neg h, show L - N = 0 by omega, show L + 1 - N = 0 by omega]
        exact Q'.zero_add' 0

private theorem subunitReturnEnvelope_nonneg {w : Q'} (hw0 : (0 : Q') < w) (M : Nat) :
    (0 : Q') ≤ subunitReturnEnvelope w M := by
  exact Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _ (subunitBoundaryFactor_nonnegative hw0) (zero_le_ofNat _))
    (qpow_nonneg w (Q'.le_of_lt hw0) _)

private theorem count_times_subunitReturn (w : Q') (M : Nat) :
    Q'.ofNat ((M + 1) ^ 6) * subunitReturnEnvelope w M ≈
      subunitRadialEnvelope w M := by
  have he : Q'.ofNat ((M + 1) ^ 6) * Q'.ofNat ((M + 1) ^ 6) ≈
      Q'.ofNat ((M + 1) ^ 12) := by
    rw [show (12 : Nat) = 6 + 6 from rfl, Nat.pow_add]
    show (Int.ofNat ((M + 1) ^ 6) * Int.ofNat ((M + 1) ^ 6)) * (1 : Int) =
      Int.ofNat ((M + 1) ^ 6 * (M + 1) ^ 6) * (1 : Int)
    rfl
  unfold subunitReturnEnvelope subunitRadialEnvelope
  refine Q'.eqv_trans _
    ((subunitBoundaryFactor w *
      (Q'.ofNat ((M + 1) ^ 6) * Q'.ofNat ((M + 1) ^ 6))) *
        qpow w (gaussianExponent M)) _ (count_regroup _ _ _) ?_
  exact Q'.mul_eqv_congr_right _ _ _
    (Q'.mul_eqv_congr_left _ _ _ he)

/-- One literal radius shell is bounded using the all-subunit physical return
bound, with no replacement trace or kernel. -/
theorem radiusShell_selfReturn_le_subunit {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (K M : Nat) (hM : 1400 ≤ M) :
    listQSum (fun state => centralPhysicalConditionalKernel w (Q'.le_of_lt hw0) K 0 state state)
      (radiusShell w (Q'.le_of_lt hw0) K M) ≤ subunitRadialEnvelope w M := by
  have hterm : ∀ state, state ∈ radiusShell w (Q'.le_of_lt hw0) K M →
      centralPhysicalConditionalKernel w (Q'.le_of_lt hw0) K 0 state state ≤
        subunitReturnEnvelope w M := by
    intro state hs
    have hmem := List.mem_filter.mp hs
    have he : M = radius state := of_decide_eq_true hmem.2
    rw [he]
    exact vacuumSector_selfReturn_le_subunit_gaussian hw0 hw1 K hmem.1 (he ▸ hM)
  exact Q'.le_trans' _ _ _ (sum_le_length _ _ _ hterm)
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _
        (CReal.ofNat_le_ofNat (radiusShell_length_le w (Q'.le_of_lt hw0) K M))
        (subunitReturnEnvelope_nonneg hw0 M))
      (Q'.le_of_eqv (count_times_subunitReturn w M)))

/-- The actual high-label trace, pushed through the existing radius shells,
has the new nome-dependent radial envelope. -/
theorem highLabelTrace_le_subunitRadial {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (K N : Nat)
    (hN : subunitRadialOnset w ≤ N) :
    highLabelTrace w (Q'.le_of_lt hw0) K N ≤
      Q'.ofNat 2 * subunitRadialEnvelope w N := by
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (highLabelTrace_eq_shells w (Q'.le_of_lt hw0) K N)) ?_
  refine Q'.le_trans' _
    (listQSum (fun M => if N ≤ M then subunitRadialEnvelope w M else 0)
      (List.range (K + 1))) _ ?_ ?_
  · apply sum_le
    intro M _
    split
    · exact radiusShell_selfReturn_le_subunit hw0 hw1 K M (by
        have h1400 : 1400 ≤ N := Nat.le_trans (Nat.le_max_left _ _) hN
        omega)
    · exact Q'.le_refl' 0
  · have he := listQSum_range_eq_fsum
      (fun M => if N ≤ M then subunitRadialEnvelope w M else 0) (K + 1)
    rw [fsum_mask, fsum_eq_finSum] at he
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
      (subunitRadialEnvelope_tail_le hw0 hw1 N hN _)

/-- Explicit all-subunit cutoff for the literal high-label trace. -/
theorem highLabelTrace_small_subunit {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (epsilon : Q') (he : (0 : Q') < epsilon) (K : Nat) :
    highLabelTrace w (Q'.le_of_lt hw0) K (subunitRadialTailCutoff w epsilon) ≤ epsilon := by
  have hOnset := subunitRadialOnset_le_tailCutoff w epsilon
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (highLabelTrace_eq_shells w (Q'.le_of_lt hw0) K
      (subunitRadialTailCutoff w epsilon))) ?_
  refine Q'.le_trans' _
    (listQSum (fun M => if subunitRadialTailCutoff w epsilon ≤ M then
      subunitRadialEnvelope w M else 0) (List.range (K + 1))) _ ?_ ?_
  · apply sum_le
    intro M _
    split
    · exact radiusShell_selfReturn_le_subunit hw0 hw1 K M (by
        have h1400 : 1400 ≤ subunitRadialOnset w := Nat.le_max_left _ _
        omega)
    · exact Q'.le_refl' 0
  · have hh := listQSum_range_eq_fsum
      (fun M => if subunitRadialTailCutoff w epsilon ≤ M then
        subunitRadialEnvelope w M else 0) (K + 1)
    rw [fsum_mask, fsum_eq_finSum] at hh
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hh)
      (subunitRadialTailCutoff_bound hw0 hw1 epsilon he _)

/-- Raising the radius threshold only removes nonnegative diagonal terms
from the same physical trace. -/
theorem highLabelTrace_antitone_threshold (w : Q') (hw : (0 : Q') ≤ w)
    (K low high : Nat) (h : low ≤ high) :
    highLabelTrace w hw K high ≤ highLabelTrace w hw K low := by
  apply sum_le
  intro state _
  by_cases hh : high ≤ radius state
  · rw [if_pos hh, if_pos (Nat.le_trans h hh)]
    exact Q'.le_refl' _
  · rw [if_neg hh]
    split
    · exact centralPhysicalConditionalKernel_nonnegative hw K 0 state state
    · exact Q'.le_refl' 0

/-- The actual raw new-block trace is small at a computed fixed base,
uniformly over every later admitting representation cutoff. -/
theorem newTailSelfReturnTrace_small_subunit {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (epsilon : Q') (he : (0 : Q') < epsilon)
    (later : Nat) (hlater : subunitRadialTailCutoff w epsilon ≤ later) :
    centralPhysicalFiniteVacuumSectorExactNewTailSelfReturnTrace
      w (Q'.le_of_lt hw0) (subunitRadialTailCutoff w epsilon) later 0 ≤ epsilon := by
  have hbase : 1 ≤ subunitRadialTailCutoff w epsilon :=
    Nat.le_trans (by decide : 1 ≤ 1400)
      (Nat.le_trans (Nat.le_max_left _ _) (subunitRadialOnset_le_tailCutoff w epsilon))
  exact Q'.le_trans' _ _ _
    (newTailSelfReturnTrace_le_highLabel hw0 _ later hbase hlater)
    (Q'.le_trans' _ _ _
      (highLabelTrace_antitone_threshold w (Q'.le_of_lt hw0) later _ _ (Nat.le_succ _))
      (highLabelTrace_small_subunit hw0 hw1 epsilon he later))

/-- The favorable stationary subtraction also bounds the existing centered
trace rate, without changing its normalization. -/
theorem newTailTraceRate_small_subunit {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (epsilon : Q') (he : (0 : Q') < epsilon)
    (later : Nat) (hlater : subunitRadialTailCutoff w epsilon ≤ later) :
    centralPhysicalFiniteVacuumSectorExactNewTailTraceRate
      w (Q'.le_of_lt hw0) (subunitRadialTailCutoff w epsilon) later 0 ≤ epsilon :=
  Q'.le_trans' _ _ _
    (centralPhysicalFiniteVacuumSectorExactNewTailTraceRate_le_selfReturnTrace _ _ _ _ _)
    (newTailSelfReturnTrace_small_subunit hw0 hw1 epsilon he later hlater)

/-- Every literal new-tail vector is controlled in its own later-cutoff
stationary norm; no head rate or full gap is assumed. -/
theorem centered_newTail_le_subunit {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (epsilon : Q') (he : (0 : Q') < epsilon)
    (later : Nat) (hlater : subunitRadialTailCutoff w epsilon ≤ later)
    (coefficient : Nat → Q') :
    let D := centralPhysicalFiniteVacuumSectorCenteredGramGNSData w (Q'.le_of_lt hw0) later 0
    let tail := centralPhysicalFiniteVacuumSectorNewTailCoefficient
      w (Q'.le_of_lt hw0) (subunitRadialTailCutoff w epsilon) later 0 coefficient
    D.B tail tail ≤ epsilon * centralPhysicalFiniteVacuumSectorDiagonalQuadratic
      w (Q'.le_of_lt hw0) later 0 tail :=
  centralPhysicalFiniteVacuumSectorCenteredNewTailCoefficient_le_of_traceBound _ _ _ _ _ _ _
    (newTailTraceRate_small_subunit hw0 hw1 epsilon he later hlater)

end YMGap.Continuum.BF4PhysicalCubeSubunitHighLabelTrace

#print axioms YMGap.Continuum.BF4PhysicalCubeSubunitHighLabelTrace.radiusShell_selfReturn_le_subunit
#print axioms YMGap.Continuum.BF4PhysicalCubeSubunitHighLabelTrace.highLabelTrace_le_subunitRadial
#print axioms YMGap.Continuum.BF4PhysicalCubeSubunitHighLabelTrace.highLabelTrace_small_subunit
#print axioms YMGap.Continuum.BF4PhysicalCubeSubunitHighLabelTrace.highLabelTrace_antitone_threshold
#print axioms YMGap.Continuum.BF4PhysicalCubeSubunitHighLabelTrace.newTailSelfReturnTrace_small_subunit
#print axioms YMGap.Continuum.BF4PhysicalCubeSubunitHighLabelTrace.newTailTraceRate_small_subunit
#print axioms YMGap.Continuum.BF4PhysicalCubeSubunitHighLabelTrace.centered_newTail_le_subunit
