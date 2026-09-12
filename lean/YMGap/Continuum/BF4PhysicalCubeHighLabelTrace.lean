/-
# Uniform high-label trace of the original vacuum-sector conditional kernel

The actual sector states have unique six-label codes. Radius-M shells
therefore have at most (M+1)^6 entries. Exact deterministic pushforward by
radius, together with the physical Gaussian diagonal bound, contracts the
entire high-label trace into the proved degree-12 radial envelope.

Extent one and the nome interval are explicit. This is a tail estimate,
not a centered head estimate, an all-vector gap or a continuum theorem.
Exact untrusted pilot: computations/bf4_cube_high_label_trace.py.
-/

import YMGap.Continuum.BF4PhysicalCubeGaussianReturn
import YMGap.Continuum.BF4PhysicalVacuumSectorZeroExtensionDirichlet

namespace YMGap.Continuum.BF4PhysicalCubeHighLabelTrace

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4PhysicalCubeBalancedDescent
open YMGap.Continuum.BF4PhysicalCubeGaussianReturn
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalVacuumSectorCubeClassification
open YMGap.Continuum.BF4PhysicalVacuumSectorCubeContainment
open YMGap.Continuum.BF4PhysicalVacuumSectorZeroExtensionDirichlet
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.GenuineResidualDefect
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

local infix:50 " ≈ " => Q'.eqv

local macro "q_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.mul_num_cast, Q'.mul_den_cast];
             try ac_rfl))

private theorem map_values {A B : Type} (f g : A → B) : ∀ ids : List A,
    ids.map f = ids.map g → ∀ i, i ∈ ids → f i = g i
  | [], _, _, h => by cases h
  | j :: ids, he, i, hi => by
      have hh := List.cons.inj he
      rcases List.mem_cons.mp hi with rfl | ht
      · exact hh.1
      · exact map_values f g ids hh.2 i ht

/-- No decidable equality on infinite functions is assumed: finite cube
codes are injective on the proved support. -/
theorem cubeLabels_injective (left right : EdgeLabelling)
    (hl : ∀ face, face ∉ centralLowerCubeFaceIds → left face = 0)
    (hr : ∀ face, face ∉ centralLowerCubeFaceIds → right face = 0)
    (he : cubeLabels left = cubeLabels right) : left = right := by
  funext face
  by_cases hf : face ∈ centralLowerCubeFaceIds
  · exact map_values left right centralLowerCubeFaceIds he face hf
  · rw [hl face hf, hr face hf]

/-- A duplicate-free collection of supported states of radius at most M
injects into the explicit finite code space of size (M+1)^6. -/
theorem cubeSupported_list_length_le (M : Nat) (states : List EdgeLabelling)
    (hn : states.Nodup)
    (hz : ∀ state, state ∈ states → ∀ face, face ∉ centralLowerCubeFaceIds → state face = 0)
    (hb : ∀ state, state ∈ states → radius state ≤ M) : states.length ≤ (M + 1) ^ 6 := by
  have hi := nodup_map_of_injOn cubeLabels states hn
    (fun left hl right hr he => cubeLabels_injective left right (hz left hl) (hz right hr) he)
  have hc : ∀ code, code ∈ states.map cubeLabels → code ∈ allSeqs (M + 1) 6 := by
    intro code hcode
    obtain ⟨state, hs, rfl⟩ := List.mem_map.mp hcode
    apply mem_allSeqs
    · simp [cubeLabels, centralLowerCubeFaceIds]
    · intro s hmem
      have h := member_le_maxLabel (cubeLabels state) hmem
      exact Nat.lt_succ_of_le (Nat.le_trans h (hb state hs))
  have h := nodup_subset_length_le (states.map cubeLabels) (allSeqs (M + 1) 6) hi hc
  simpa only [List.length_map, length_allSeqs] using h

def radiusShell (w : Q') (hw : (0 : Q') ≤ w) (K M : Nat) : List EdgeLabelling :=
  (centralPhysicalFiniteVacuumSectorStates w hw K 0).filter (fun state => decide (M = radius state))

theorem radiusShell_length_le (w : Q') (hw : (0 : Q') ≤ w) (K M : Nat) :
    (radiusShell w hw K M).length ≤ (M + 1) ^ 6 := by
  apply cubeSupported_list_length_le M
  · exact (vacuumSectorStates_nodup w hw K 0).filter _
  · intro state hs
    exact (vacuumSector_cubeSupportedCommonParity w hw K (List.mem_filter.mp hs).1).1
  · intro state hs
    have he := of_decide_eq_true (List.mem_filter.mp hs).2
    exact Nat.le_of_eq he.symm

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

private theorem returnEnvelope_nonneg {w : Q'} (hw : (0 : Q') ≤ w) (M : Nat) :
    (0 : Q') ≤ returnEnvelope w M :=
  Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (zero_le_ofNat _) (zero_le_ofNat _)) (qpow_nonneg w hw _)

private theorem count_times_return (w : Q') (M : Nat) :
    Q'.ofNat ((M + 1) ^ 6) * returnEnvelope w M ≈ radialEnvelope w M := by
  have he : Q'.ofNat ((M + 1) ^ 6) * Q'.ofNat ((M + 1) ^ 6) ≈ Q'.ofNat ((M + 1) ^ 12) := by
    rw [show (12 : Nat) = 6 + 6 from rfl, Nat.pow_add]
    show (Int.ofNat ((M + 1) ^ 6) * Int.ofNat ((M + 1) ^ 6)) * (1 : Int) =
      Int.ofNat ((M + 1) ^ 6 * (M + 1) ^ 6) * (1 : Int)
    rfl
  unfold returnEnvelope radialEnvelope
  refine Q'.eqv_trans _
    ((Q'.ofNat 4096 * (Q'.ofNat ((M + 1) ^ 6) * Q'.ofNat ((M + 1) ^ 6))) *
      qpow w (gaussianExponent M)) _ (by q_ring) ?_
  exact Q'.mul_eqv_congr_right _ _ _ (Q'.mul_eqv_congr_left _ _ _ he)

/-- The radial envelope bounds the actual sum of physical conditional
self-returns on one complete radius shell. -/
theorem radiusShell_selfReturn_le {w : Q'} (hw0 : (0 : Q') < w) (hw : w ≤ HalfPow.half)
    (K M : Nat) (hM : 1400 ≤ M) :
    listQSum (fun state => centralPhysicalConditionalKernel w (Q'.le_of_lt hw0) K 0 state state)
      (radiusShell w (Q'.le_of_lt hw0) K M) ≤ radialEnvelope w M := by
  have hterm : ∀ state, state ∈ radiusShell w (Q'.le_of_lt hw0) K M →
      centralPhysicalConditionalKernel w (Q'.le_of_lt hw0) K 0 state state ≤ returnEnvelope w M := by
    intro state hs
    have hmem := List.mem_filter.mp hs
    have he : M = radius state := of_decide_eq_true hmem.2
    rw [he]
    exact vacuumSector_selfReturn_le_gaussian hw0 hw K hmem.1 (he ▸ hM)
  exact Q'.le_trans' _ _ _ (sum_le_length _ _ _ hterm) (Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _ (CReal.ofNat_le_ofNat (radiusShell_length_le w (Q'.le_of_lt hw0) K M))
      (returnEnvelope_nonneg (Q'.le_of_lt hw0) M)) (Q'.le_of_eqv (count_times_return w M)))

/-- Literal positive conditional diagonal trace on the high-label portion
of the original canonical vacuum sector. -/
def highLabelTrace (w : Q') (hw : (0 : Q') ≤ w) (K N : Nat) : Q' :=
  listQSum (fun state => if N ≤ radius state then
    centralPhysicalConditionalKernel w hw K 0 state state else 0)
    (centralPhysicalFiniteVacuumSectorStates w hw K 0)

theorem highLabelTrace_nonneg (w : Q') (hw : (0 : Q') ≤ w) (K N : Nat) :
    (0 : Q') ≤ highLabelTrace w hw K N := by
  apply listQSum_nonnegative_on
  intro state _
  split
  · exact centralPhysicalConditionalKernel_nonnegative hw K 0 state state
  · exact Q'.le_refl' 0

private theorem range_nodup (N : Nat) : (List.range N).Nodup := by
  induction N with
  | zero => exact List.nodup_nil
  | succ N ih =>
      rw [List.range_succ]
      refine List.nodup_append.mpr
        ⟨ih, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
      intro x hx y hy hxy
      have hyN : y = N := List.mem_singleton.mp hy
      rw [hxy, hyN] at hx
      exact absurd (List.mem_range.mp hx) (Nat.lt_irrefl N)

/-- Exact deterministic pushforward by the maximum label. No duplicate
states, enlarged carrier or independent replacement kernel is introduced. -/
theorem highLabelTrace_eq_shells (w : Q') (hw : (0 : Q') ≤ w) (K N : Nat) :
    highLabelTrace w hw K N ≈
      listQSum (fun M => if N ≤ M then
        listQSum (fun state => centralPhysicalConditionalKernel w hw K 0 state state)
          (radiusShell w hw K M) else 0) (List.range (K + 1)) := by
  have hpart := fiberWeight_total (centralPhysicalFiniteVacuumSectorStates w hw K 0)
    (fun state => if N ≤ radius state then centralPhysicalConditionalKernel w hw K 0 state state else 0)
    radius (List.range (K + 1)) (range_nodup (K + 1))
    (fun state hs => List.mem_range.mpr (Nat.lt_succ_of_le
      (radius_le state K (vacuumSector_cubeBounded w hw K hs))))
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm hpart) ?_
  apply listQSum_congr_on
  intro M _
  by_cases h : N ≤ M
  · rw [if_pos h]
    apply listQSum_congr_on
    intro state hs
    have he : M = radius state := of_decide_eq_true (List.mem_filter.mp hs).2
    rw [if_pos (he ▸ h)]
    exact Q'.eqv_refl _
  · rw [if_neg h]
    refine Q'.eqv_trans _ _ _ (listQSum_congr_on _ (fun _ => (0 : Q')) _ ?_) (listQSum_zero _)
    intro state hs
    have he : M = radius state := of_decide_eq_true (List.mem_filter.mp hs).2
    rw [if_neg (he ▸ h)]
    exact Q'.eqv_refl _

private theorem fsum_mask (f : Nat → Q') (N : Nat) : ∀ L,
    fsum (fun M => if N ≤ M then f M else 0) L = fsum (fun k => f (N + k)) (L - N)
  | 0 => by rw [Nat.zero_sub]; rfl
  | L + 1 => by
      rw [fsum_succ, fsum_mask f N L]
      by_cases h : N ≤ L
      · rw [if_pos h, show L + 1 - N = (L - N) + 1 by omega, fsum_succ]
        rw [show N + (L - N) = L by omega]
      · rw [if_neg h, show L - N = 0 by omega, show L + 1 - N = 0 by omega]
        exact Q'.zero_add' 0

/-- **Actual high-label trace bound**, all representation cutoffs K. -/
theorem highLabelTrace_le_radial {w : Q'} (hw0 : (0 : Q') < w) (hw : w ≤ HalfPow.half)
    (K N : Nat) (hN : 1400 ≤ N) :
    highLabelTrace w (Q'.le_of_lt hw0) K N ≤ Q'.ofNat 2 * radialEnvelope w N := by
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (highLabelTrace_eq_shells w (Q'.le_of_lt hw0) K N)) ?_
  refine Q'.le_trans' _ (listQSum (fun M => if N ≤ M then radialEnvelope w M else 0) (List.range (K + 1))) _ ?_ ?_
  · apply sum_le
    intro M _
    split
    · exact radiusShell_selfReturn_le hw0 hw K M (by omega)
    · exact Q'.le_refl' 0
  · have he := listQSum_range_eq_fsum (fun M => if N ≤ M then radialEnvelope w M else 0) (K + 1)
    rw [fsum_mask, fsum_eq_finSum] at he
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv he) (radialEnvelope_tail_le (Q'.le_of_lt hw0) hw N hN _)

/-- Explicit high-label trace cutoff, independent of the outer representation
cutoff and uniform on the displayed coupling interval. -/
theorem highLabelTrace_small {w : Q'} (hw0 : (0 : Q') < w) (hw : w ≤ HalfPow.half)
    (epsilon : Q') (he : (0 : Q') < epsilon) (K : Nat) :
    highLabelTrace w (Q'.le_of_lt hw0) K (radialTailCutoff epsilon) ≤ epsilon := by
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (highLabelTrace_eq_shells w (Q'.le_of_lt hw0) K (radialTailCutoff epsilon))) ?_
  refine Q'.le_trans' _
    (listQSum (fun M => if radialTailCutoff epsilon ≤ M then radialEnvelope w M else 0) (List.range (K + 1))) _ ?_ ?_
  · apply sum_le
    intro M _
    split
    · exact radiusShell_selfReturn_le hw0 hw K M (by unfold radialTailCutoff at *; omega)
    · exact Q'.le_refl' 0
  · have hh := listQSum_range_eq_fsum (fun M => if radialTailCutoff epsilon ≤ M then radialEnvelope w M else 0) (K + 1)
    rw [fsum_mask, fsum_eq_finSum] at hh
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hh) (radialTailCutoff_bound (Q'.le_of_lt hw0) hw epsilon he _)

end YMGap.Continuum.BF4PhysicalCubeHighLabelTrace

#print axioms YMGap.Continuum.BF4PhysicalCubeHighLabelTrace.cubeLabels_injective
#print axioms YMGap.Continuum.BF4PhysicalCubeHighLabelTrace.cubeSupported_list_length_le
#print axioms YMGap.Continuum.BF4PhysicalCubeHighLabelTrace.radiusShell
#print axioms YMGap.Continuum.BF4PhysicalCubeHighLabelTrace.radiusShell_length_le
#print axioms YMGap.Continuum.BF4PhysicalCubeHighLabelTrace.radiusShell_selfReturn_le
#print axioms YMGap.Continuum.BF4PhysicalCubeHighLabelTrace.highLabelTrace
#print axioms YMGap.Continuum.BF4PhysicalCubeHighLabelTrace.highLabelTrace_nonneg
#print axioms YMGap.Continuum.BF4PhysicalCubeHighLabelTrace.highLabelTrace_eq_shells
#print axioms YMGap.Continuum.BF4PhysicalCubeHighLabelTrace.highLabelTrace_le_radial
#print axioms YMGap.Continuum.BF4PhysicalCubeHighLabelTrace.highLabelTrace_small
