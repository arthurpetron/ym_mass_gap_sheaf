/-
# Full cube boundary summation relative to the difference boundary

For the explicitly restricted coupling interval 0 <= w <= 1/2, sum the
original bounded boundary enumeration, not just a selected summand.
Each active coordinate has a geometric heat tail above its minimal source
difference; inactive coordinates are forced zero. The resulting constant
is independent of the representation cutoff, not of arbitrary coupling.

Exact untrusted pilot: computations/bf4_cube_boundary_sum_bound.py.
No spectral gap or continuum theorem is asserted.
-/

import YMGap.Continuum.BF4PhysicalCubeBalancedDescent
import YMGap.Continuum.BF4PhysicalSpinCubeRawReturnRatio
import YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
import YMGap.Continuum.PlaquetteActivity

namespace YMGap.Continuum.BF4PhysicalCubeBoundarySumBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4PhysicalCubeBalancedDescent
open YMGap.Continuum.BF4PhysicalCubeBoundaryMask
open YMGap.Continuum.BF4PhysicalCubeDifferenceBoundary
open YMGap.Continuum.BF4PhysicalCubeDifferenceBoundaryKernel
open YMGap.Continuum.BF4PhysicalCubeDifferenceBoundaryMultiplicity
open YMGap.Continuum.BF4PhysicalCubeKernelFactorization
open YMGap.Continuum.BF4PhysicalCutoffKernelSupportPersistence
open YMGap.Continuum.BF4PhysicalSpinCubeRawReturnRatio
open YMGap.Continuum.BF4PhysicalVacuumSectorCubeClassification
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateOrbits
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FusedChannelOne
open YMGap.Continuum.FusionQuotientCollapse
open YMGap.Continuum.FusionResidualBound
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.PlaquetteActivity
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4ExplicitValenceFusionMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram

local infix:50 " ≈ " => Q'.eqv

local macro "q_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.mkPos_num, Q'.mkPos_den, Q'.ofNat,
               Int.add_mul, Int.mul_add, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.add_zero, Int.zero_add];
             try ac_rfl))

/-- Includes the vacuum-to-fundamental step. The nome restriction is explicit. -/
theorem coeffW_succ_le_half {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw : w ≤ Q'.mkPos 1 2 (by decide)) (s : Nat) :
    coeffW w (s + 1) ≤ Q'.mkPos 1 2 (by decide) * coeffW w s := by
  cases s with
  | zero =>
      have hmono := qpow_mono hw0 hw 3
      have hh := Q'.mul_le_mul_of_nonneg_left _ _ _ hmono (zero_le_ofNat 2)
      have hz : coeffW w 0 ≈ 1 := Q'.eqv_of_eq (coeffW_zero w)
      have he : coeffW w 1 = Q'.ofNat 2 * qpow w 3 := rfl
      rw [he]
      refine Q'.le_trans' _ _ _ hh ?_
      exact Q'.le_trans' _ (Q'.mkPos 1 2 (by decide) * 1) _ (by decide)
        (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hz)))
  | succ s =>
      have hw1 := Q'.le_trans' _ _ (1 : Q') hw (by decide)
      exact Q'.le_trans' _ _ _ (coeffW_succ_ratio hw0 hw1 (s + 1) (by omega))
        (Q'.mul_le_mul_of_nonneg_right _ _ _ (ratio_le_half hw0 hw)
          (coeffW_nonneg hw0 _))

private theorem double_step {a b : Q'} (h : b ≤ Q'.mkPos 1 2 (by decide) * a) :
    a + Q'.ofNat 2 * b ≤ Q'.ofNat 2 * a := by
  have hh := Q'.mul_le_mul_of_nonneg_left _ _ _ h (zero_le_ofNat 2)
  have he : Q'.ofNat 2 * (Q'.mkPos 1 2 (by decide) * a) ≈ a := by
    exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ a (by decide)) (Q'.one_mul_eqv a))
  have hd : a + a ≈ Q'.ofNat 2 * a := by
    exact Q'.eqv_trans _ ((1 : Q') * a + 1 * a) _
      (Q'.add_eqv_congr' (Q'.eqv_symm (Q'.one_mul_eqv a)) (Q'.eqv_symm (Q'.one_mul_eqv a)))
      (Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_mul_eqv 1 1 a))
        (Q'.mul_eqv_congr_right _ _ a (by decide)))
  exact Q'.le_trans' _ _ _ (Q'.add_le_add_left a _ _ hh)
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.eqv_refl a) he) hd))

private theorem tail_budget (a : Nat → Q')
    (hs : ∀ n, a n + Q'.ofNat 2 * a (n + 1) ≤ Q'.ofNat 2 * a n) (d : Nat) :
    ∀ n, fsum (fun s => if d ≤ s then a s else 0) n +
      Q'.ofNat 2 * a (max d n) ≤ Q'.ofNat 2 * a d
  | 0 => by simp only [fsum_zero, Nat.max_zero, Q'.zero_add']; exact Q'.le_refl' _
  | n + 1 => by
      by_cases h : d ≤ n
      · have ih := tail_budget a hs d n
        rw [Nat.max_eq_right h] at ih
        rw [fsum_succ, if_pos h, Nat.max_eq_right (by omega : d ≤ n + 1)]
        exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.add_assoc_eqv _ _ _))
          (Q'.le_trans' _ _ _ (Q'.add_le_add_left _ _ _ (hs n)) ih)
      · have ih := tail_budget a hs d n
        rw [Nat.max_eq_left (by omega : n ≤ d)] at ih
        rw [fsum_succ, if_neg h, Nat.max_eq_left (by omega : n + 1 ≤ d), Q'.add_zero']
        exact ih

/-- Every finite heat tail is bounded relative to its own first coefficient,
uniformly in the truncation n, for the stated strong-coupling interval. -/
theorem coeffW_tail_le_twice {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw : w ≤ Q'.mkPos 1 2 (by decide)) (d n : Nat) :
    fsum (fun s => if d ≤ s then coeffW w s else 0) n ≤ Q'.ofNat 2 * coeffW w d := by
  exact Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ _
    (Q'.mul_nonneg _ _ (zero_le_ofNat 2) (coeffW_nonneg hw0 _)))
    (tail_budget (coeffW w) (fun s => double_step (coeffW_succ_le_half hw0 hw s)) d n)

private theorem product_congr (f g : Nat → Q') : ∀ ids : List Nat,
    (∀ i, i ∈ ids → f i = g i) → eliminateLinks f ids = eliminateLinks g ids
  | [], _ => rfl
  | i :: ids, h => by
      simp only [eliminateLinks, h i List.mem_cons_self,
        product_congr f g ids (fun j hj => h j (List.mem_cons_of_mem i hj))]

/-- Exact finite Fubini for independent coordinate weights on the original
Cartesian enumeration. Distinct coordinate identifiers are required. -/
theorem bounded_product_sum (w : Nat → Nat → Q') (K : Nat) : ∀ ids : List Nat,
    ids.Nodup →
    listQSum (fun b => eliminateLinks (fun i => w i (b i)) ids)
      (boundedEdgeLabellings K ids) ≈
    eliminateLinks (fun i => fsum (w i) (K + 1)) ids
  | [], _ => by exact Q'.eqv_of_eq (Q'.add_zero' 1)
  | i :: ids, hn => by
      have hh := List.nodup_cons.mp hn
      refine Q'.eqv_trans _ _ _ (listQSum_bounded_cons K i ids _) ?_
      refine Q'.eqv_trans _
        (fsum (fun s => w i s * listQSum
          (fun b => eliminateLinks (fun j => w j (b j)) ids)
          (boundedEdgeLabellings K ids)) (K + 1)) _ ?_ ?_
      · apply fsum_eqv_congr'
        intro s
        refine Q'.eqv_trans _ _ _ (listQSum_congr_on _ _ _ (fun b _ => ?_))
          (listQSum_mul_left (w i s) _ _)
        apply Q'.eqv_of_eq
        simp only [eliminateLinks, setEdgeLabel, ↓reduceIte]
        congr 1
        apply product_congr
        intro j hj
        have hji : j ≠ i := fun he => hh.1 (he ▸ hj)
        rw [if_neg hji]
      · exact Q'.eqv_trans _ _ _ (fsum_factor _ _ (K + 1))
          (Q'.mul_eqv_congr_left _ _ _ (bounded_product_sum w K ids hh.2))

private theorem product_nonneg (f : Nat → Q') (h : ∀ i, (0 : Q') ≤ f i) :
    ∀ ids, (0 : Q') ≤ eliminateLinks f ids
  | [] => by exact Q'.zero_le_one
  | i :: ids => Q'.mul_nonneg _ _ (h i) (product_nonneg f h ids)

private theorem product_le (f g : Nat → Q') (h0 : ∀ i, (0 : Q') ≤ f i)
    (h : ∀ i, f i ≤ g i) : ∀ ids, eliminateLinks f ids ≤ eliminateLinks g ids
  | [] => Q'.le_refl' 1
  | i :: ids => Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ (h i) (product_nonneg f h0 ids))
      (Q'.mul_le_mul_of_nonneg_left _ _ _ (product_le f g h0 h ids)
        (Q'.le_trans' _ _ _ (h0 i) (h i)))

private theorem product_mul (f g : Nat → Q') : ∀ ids,
    eliminateLinks (fun i => f i * g i) ids ≈ eliminateLinks f ids * eliminateLinks g ids
  | [] => Q'.eqv_symm (Q'.one_mul_eqv 1)
  | i :: ids => by
      refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (product_mul f g ids)) ?_
      simp only [eliminateLinks]
      q_ring

private theorem sum_le {A : Type} (f g : A → Q') : ∀ xs,
    (∀ x, x ∈ xs → f x ≤ g x) → listQSum f xs ≤ listQSum g xs
  | [], _ => Q'.le_refl' 0
  | x :: xs, h => Q'.add_le_add (h x List.mem_cons_self)
      (sum_le f g xs (fun y hy => h y (List.mem_cons_of_mem x hy)))

/-- Necessary lower bound from the actual SU(2) edge tests. -/
theorem admissible_boundary_ge_difference (state boundary : EdgeLabelling)
    (ha : cubeEdgeAdmissibleB state boundary = true) (face : Nat)
    (hf : face ∈ cubeDifferenceBoundaryIds) : cubeDifferenceBoundary state face ≤ boundary face := by
  have hcover : face ∈ cubeDifferenceEdges.map (fun e => e.2.2) := by
    simp only [cubeDifferenceBoundaryIds, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hcover
  rw [cubeDifferenceBoundary_on_edge state e he]
  have htri := (fusionOK_eq_true_iff _ _ _).mp (List.all_eq_true.mp ha e he)
  unfold spinDistance
  have hd : (state e.1 - state e.2.1) + (state e.2.1 - state e.1) =
      max (state e.1) (state e.2.1) - min (state e.1) (state e.2.1) := by omega
  rw [hd]
  exact htri.1

/-- Independent one-coordinate majorant; inactive faces retain only zero. -/
def boundaryTailFactor (w : Q') (state : EdgeLabelling) (face spin : Nat) : Q' :=
  if face ∈ cubeDifferenceBoundaryIds then
    if cubeDifferenceBoundary state face ≤ spin then coeffW w spin else 0
  else if spin = 0 then 1 else 0

theorem boundaryTailFactor_nonneg {w : Q'} (hw : (0 : Q') ≤ w)
    (state : EdgeLabelling) (face spin : Nat) : (0 : Q') ≤ boundaryTailFactor w state face spin := by
  unfold boundaryTailFactor
  split
  · split
    · exact coeffW_nonneg hw _
    · exact Q'.le_refl' 0
  · split
    · exact Q'.zero_le_one
    · exact Q'.le_refl' 0

theorem boundaryTailFactor_sum_le {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw : w ≤ Q'.mkPos 1 2 (by decide)) (K : Nat) (state : EdgeLabelling) (face : Nat) :
    fsum (boundaryTailFactor w state face) (K + 1) ≤
      (if face ∈ cubeDifferenceBoundaryIds then Q'.ofNat 2 else 1) *
        coeffW w (cubeDifferenceBoundary state face) := by
  by_cases hf : face ∈ cubeDifferenceBoundaryIds
  · unfold boundaryTailFactor
    simp only [if_pos hf]
    exact coeffW_tail_le_twice hw0 hw _ _
  · unfold boundaryTailFactor
    simp only [if_neg hf, cubeDifferenceBoundary_zero_off state hf, coeffW_zero]
    have hc := fsum_collapse (g := fun s => if s = 0 then (1 : Q') else 0)
      (fun s hs => by simp only [if_neg hs]; exact Q'.eqv_refl 0) (K + 1) (Nat.zero_lt_succ K)
    exact Q'.le_of_eqv (Q'.eqv_trans _ 1 _ hc (Q'.eqv_symm (Q'.one_mul_eqv 1)))

/-- The complete production mask is dominated by independent heat tails.
No corner or upper-triangle constraint is asserted in the majorant. -/
theorem boundary_integrand_le_product {w : Q'} (hw : (0 : Q') ≤ w) (K : Nat)
    (left right boundary : EdgeLabelling) (hb : boundary ∈ centralBoundaryChannels K 0) :
    boundaryHeat w boundary * Q'.ofNat (boolMultiplicity (cubeKernelAllowedB left right boundary)) ≤
      eliminateLinks (fun face => boundaryTailFactor w left face (boundary face)) (centralFixedFaceIds 0) := by
  cases hmask : cubeKernelAllowedB left right boundary with
  | false =>
      simp only [boolMultiplicity, Bool.false_eq_true, ↓reduceIte]
      exact Q'.le_trans' _ 0 _ (Q'.le_of_eqv (Q'.mul_zero_eqv _))
        (product_nonneg _ (fun face => boundaryTailFactor_nonneg hw left face _) _)
  | true =>
      simp only [boolMultiplicity, ↓reduceIte]
      have hm : cubeBoundaryZeroB boundary = true ∧ (cubeCornerAdmissibleB boundary = true ∧
          (cubeEdgeAdmissibleB left boundary = true ∧ cubeEdgeAdmissibleB right boundary = true)) := by
        simpa only [cubeKernelAllowedB, Bool.and_eq_true] using hmask
      have he := hm.2.2.1
      have hp : boundaryHeat w boundary =
          eliminateLinks (fun face => boundaryTailFactor w left face (boundary face)) (centralFixedFaceIds 0) := by
        apply product_congr
        intro face _
        by_cases hf : face ∈ cubeDifferenceBoundaryIds
        · simp only [boundaryTailFactor, if_pos hf,
            if_pos (admissible_boundary_ge_difference left boundary he face hf)]
        · rw [boundary_zero_off_active hb hm.1 face hf]
          simp only [boundaryTailFactor, if_neg hf, ↓reduceIte, coeffW_zero]
      exact Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.mul_one_eqv _) (Q'.eqv_of_eq hp))

/-- **Full boundary sum:** all cutoffs K and all source/target labels, on
0 <= w <= 1/2. The explicit loss 4096 = 2^12 counts active boundary faces.
This is an upper estimate, not a transition floor or spectral-gap rate. -/
theorem cubeBoundaryOverlap_le_difference {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw : w ≤ Q'.mkPos 1 2 (by decide)) (K : Nat) (left right : EdgeLabelling) :
    cubeBoundaryOverlap w K left right ≤ Q'.ofNat 4096 * boundaryHeat w (cubeDifferenceBoundary left) := by
  have hsum := sum_le _ _ (centralBoundaryChannels K 0)
    (fun boundary hb => boundary_integrand_le_product hw0 K left right boundary hb)
  have hF := bounded_product_sum (boundaryTailFactor w left) K (centralFixedFaceIds 0) (by decide +kernel)
  have hprod := product_le (fun face => fsum (boundaryTailFactor w left face) (K + 1))
    (fun face => (if face ∈ cubeDifferenceBoundaryIds then Q'.ofNat 2 else 1) *
      coeffW w (cubeDifferenceBoundary left face))
    (fun face => fsum_nonneg (fun spin => boundaryTailFactor_nonneg hw0 left face spin) _)
    (boundaryTailFactor_sum_le hw0 hw K left) (centralFixedFaceIds 0)
  have hsplit := product_mul (fun face => if face ∈ cubeDifferenceBoundaryIds then Q'.ofNat 2 else 1)
    (fun face => coeffW w (cubeDifferenceBoundary left face)) (centralFixedFaceIds 0)
  have hcount : eliminateLinks (fun face => if face ∈ cubeDifferenceBoundaryIds then Q'.ofNat 2 else 1)
      (centralFixedFaceIds 0) ≈ Q'.ofNat 4096 := by decide +kernel
  exact Q'.le_trans' _ _ _ hsum (Q'.le_trans' _ _ _ (Q'.le_of_eqv hF)
    (Q'.le_trans' _ _ _ hprod (Q'.le_of_eqv (Q'.eqv_trans _ _ _ hsplit
      (Q'.mul_eqv_congr_right _ _ _ hcount)))))

/-- Upper bound on the original raw diagonal, including its complete
boundary sum. No source parity assumption is needed. -/
theorem cubePhysicalKernel_diagonal_le {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw : w ≤ Q'.mkPos 1 2 (by decide)) (K : Nat) (state : EdgeLabelling)
    (hb : ∀ face, face ∈ centralLowerCubeFaceIds → state face ≤ K)
    (hz : ∀ face, face ∉ centralLowerCubeFaceIds → state face = 0) :
    centralPhysicalReflectedKernel w K 0 state state ≤
      Q'.ofNat 4096 * ((halfHeat w state * halfHeat w state) *
        boundaryHeat w (cubeDifferenceBoundary state)) := by
  have hn : (0 : Q') ≤ halfHeat w state := product_nonneg _ (fun _ => coeffW_nonneg hw0 _) _
  have hf := cubePhysicalKernel_eq_heat_overlap w K state state
    (cubeSupported_bounded K state hb hz) (cubeSupported_bounded K state hb hz) hz hz
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hf) (Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ (cubeBoundaryOverlap_le_difference hw0 hw K state state)
      (Q'.mul_nonneg _ _ hn hn)) (Q'.le_of_eqv (by q_ring)))

/-- The full diagonal is paid by an actual off-diagonal balanced transition,
with source/target heat factors explicit. This is not a common transition floor. -/
theorem cube_diagonal_balanced_comparison {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw : w ≤ Q'.mkPos 1 2 (by decide)) (K : Nat) (hK : 2 ≤ K) (state : EdgeLabelling)
    (hb : ∀ face, face ∈ centralLowerCubeFaceIds → state face ≤ K)
    (hp : CubeSupportedCommonParity state) :
    halfHeat w (balancedState state) * centralPhysicalReflectedKernel w K 0 state state ≤
      (Q'.ofNat 4096 * halfHeat w state) *
        centralPhysicalReflectedKernel w K 0 state (balancedState state) := by
  have hn : (0 : Q') ≤ halfHeat w (balancedState state) :=
    product_nonneg _ (fun _ => coeffW_nonneg hw0 _) _
  have hd := Q'.mul_le_mul_of_nonneg_left _ _ _ (cubePhysicalKernel_diagonal_le hw0 hw K state hb hp.1) hn
  refine Q'.le_trans' _ _ _ hd (Q'.le_trans' _
    ((Q'.ofNat 4096 * halfHeat w state) * balancedPhysicalWeight w state) _ ?_ ?_)
  · apply Q'.le_of_eqv
    unfold balancedPhysicalWeight
    q_ring
  · exact Q'.mul_le_mul_of_nonneg_left _ _ _ (balancedPhysicalWeight_le_kernel hw0 K hK state hb hp)
      (Q'.mul_nonneg _ _ (zero_le_ofNat 4096) (product_nonneg _ (fun _ => coeffW_nonneg hw0 _) _))

private theorem member_le_sum {A : Type} (value : A → Q') (hn : ∀ x, (0 : Q') ≤ value x) :
    ∀ (xs : List A) {x : A}, x ∈ xs → value x ≤ listQSum value xs
  | [], _, h => by cases h
  | y :: ys, x, h => by
      rcases List.mem_cons.mp h with he | ht
      · subst x
        exact Q'.add_le_self_of_nonneg _ _ (listQSum_nonnegative_on _ _ (fun z _ => hn z))
      · have hh := Q'.add_le_add_right (0 : Q') (value y) (listQSum value ys) (hn y)
        rw [Q'.zero_add'] at hh
        exact Q'.le_trans' _ _ _ (member_le_sum value hn ys ht) hh

/-- Comparison with the row over the original positive physical carrier,
not a row of a newly introduced dynamics. -/
theorem cube_diagonal_rawRow_comparison {w : Q'} (hw0 : (0 : Q') < w)
    (hw : w ≤ Q'.mkPos 1 2 (by decide)) (K : Nat) (hK : 2 ≤ K) (state : EdgeLabelling)
    (hb : ∀ face, face ∈ centralLowerCubeFaceIds → state face ≤ K)
    (hp : CubeSupportedCommonParity state) :
    halfHeat w (balancedState state) * centralPhysicalReflectedKernel w K 0 state state ≤
      (Q'.ofNat 4096 * halfHeat w state) *
        centralPhysicalPositiveRawRowMass w (Q'.le_of_lt hw0) K 0 state := by
  have hm := cubeSupported_mem_positiveHalfStates hw0 K (by omega) (balancedState state)
    (fun face _ => balancedState_bounded state K hK hb face) (balancedState_off state)
  have hr := member_le_sum (centralPhysicalReflectedKernel w K 0 state)
    (fun target => centralPhysicalReflectedKernel_nonnegative (Q'.le_of_lt hw0) K 0 state target)
    (centralPositiveHalfStates w (Q'.le_of_lt hw0) K 0) hm
  exact Q'.le_trans' _ _ _ (cube_diagonal_balanced_comparison (Q'.le_of_lt hw0) hw K hK state hb hp)
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hr (Q'.mul_nonneg _ _ (zero_le_ofNat 4096)
      (product_nonneg _ (fun _ => coeffW_nonneg (Q'.le_of_lt hw0) _) _)))

/-- Actual conditional self-return, formed from the normalized joint kernel
and its own marginal. The common partition cancels exactly. What remains
is the state-dependent source/target heat ratio, not an assumed uniform gap. -/
theorem cube_selfReturn_scaled_le {w : Q'} (hw0 : (0 : Q') < w)
    (hw : w ≤ Q'.mkPos 1 2 (by decide)) (K : Nat) (hK : 2 ≤ K) (state : EdgeLabelling)
    (hb : ∀ face, face ∈ centralLowerCubeFaceIds → state face ≤ K)
    (hp : CubeSupportedCommonParity state) :
    halfHeat w (balancedState state) *
      Q'.divPos (centralNormalizedPhysicalReflectedKernel w (Q'.le_of_lt hw0) K 0 state state)
        (centralPhysicalRowMarginal w (Q'.le_of_lt hw0) K 0 state)
        (mem_centralPositiveHalfStates_iff.mp
          (cubeSupported_mem_positiveHalfStates hw0 K (by omega) state hb hp.1)).2 ≤
      Q'.ofNat 4096 * halfHeat w state := by
  have hs := cubeSupported_mem_positiveHalfStates hw0 K (by omega) state hb hp.1
  have he := centralNormalizedPhysicalReturn_eqv_rawRatio hs state
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ he)) ?_
  refine Q'.le_trans' _
    (Q'.divPos (halfHeat w (balancedState state) * centralPhysicalReflectedKernel w K 0 state state)
      (centralPhysicalPositiveRawRowMass w (Q'.le_of_lt hw0) K 0 state)
      (centralPhysicalPositiveRawRowMass_pos hs)) _ ?_ ?_
  · exact Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
  · exact Q'.divPos_le_of_le_mul _ _ _ (cube_diagonal_rawRow_comparison hw0 hw K hK state hb hp)

end YMGap.Continuum.BF4PhysicalCubeBoundarySumBound

#print axioms YMGap.Continuum.BF4PhysicalCubeBoundarySumBound.coeffW_succ_le_half
#print axioms YMGap.Continuum.BF4PhysicalCubeBoundarySumBound.coeffW_tail_le_twice
#print axioms YMGap.Continuum.BF4PhysicalCubeBoundarySumBound.bounded_product_sum
#print axioms YMGap.Continuum.BF4PhysicalCubeBoundarySumBound.admissible_boundary_ge_difference
#print axioms YMGap.Continuum.BF4PhysicalCubeBoundarySumBound.boundaryTailFactor
#print axioms YMGap.Continuum.BF4PhysicalCubeBoundarySumBound.boundaryTailFactor_nonneg
#print axioms YMGap.Continuum.BF4PhysicalCubeBoundarySumBound.boundaryTailFactor_sum_le
#print axioms YMGap.Continuum.BF4PhysicalCubeBoundarySumBound.boundary_integrand_le_product
#print axioms YMGap.Continuum.BF4PhysicalCubeBoundarySumBound.cubeBoundaryOverlap_le_difference
#print axioms YMGap.Continuum.BF4PhysicalCubeBoundarySumBound.cubePhysicalKernel_diagonal_le
#print axioms YMGap.Continuum.BF4PhysicalCubeBoundarySumBound.cube_diagonal_balanced_comparison
#print axioms YMGap.Continuum.BF4PhysicalCubeBoundarySumBound.cube_diagonal_rawRow_comparison
#print axioms YMGap.Continuum.BF4PhysicalCubeBoundarySumBound.cube_selfReturn_scaled_le
