/-
# All-state balanced descent through the physical difference boundary

For a cube-supported common-parity source with largest label M, replace s by
`2 * (floor(2*floor(s/2)/3) + ceil(M/12))` on each cube face.
Every source difference channel remains admissible. The resulting all-even
cube fits every original cutoff K>=2 and strictly lowers M when M>=12.
The selected production summand is pinned to the original physical kernel.
No uniform transition probability, congestion or spectral gap is inferred.

Exact untrusted pilot: computations/bf4_cube_balanced_descent.py.
-/

import YMGap.Continuum.BF4PhysicalCubeKernelFactorization
import YMGap.Continuum.BF4PhysicalVacuumSectorCubeClassification

namespace YMGap.Continuum.BF4PhysicalCubeBalancedDescent

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4PhysicalCubeBoundaryMask
open YMGap.Continuum.BF4PhysicalCubeDifferenceBoundary
open YMGap.Continuum.BF4PhysicalCubeDifferenceBoundaryKernel
open YMGap.Continuum.BF4PhysicalCubeDifferenceBoundaryMultiplicity
open YMGap.Continuum.BF4PhysicalCubeKernelFactorization
open YMGap.Continuum.BF4PhysicalVacuumSectorCubeClassification
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateOrbits
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FusionQuotientCollapse
open YMGap.Continuum.FusionResidualBound
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4ExplicitValenceFusionMultiplicity
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

def maxLabel : List Nat → Nat
  | [] => 0
  | s :: ss => max s (maxLabel ss)

theorem member_le_maxLabel {s : Nat} : ∀ ss : List Nat, s ∈ ss → s ≤ maxLabel ss
  | [], h => by cases h
  | t :: ts, h => by
      rcases List.mem_cons.mp h with rfl | ht
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (member_le_maxLabel ts ht) (Nat.le_max_right _ _)

theorem maxLabel_le (K : Nat) : ∀ ss : List Nat,
    (∀ s, s ∈ ss → s ≤ K) → maxLabel ss ≤ K
  | [], _ => Nat.zero_le K
  | s :: ss, h => Nat.max_le.mpr ⟨h s List.mem_cons_self,
      maxLabel_le K ss (fun t ht => h t (List.mem_cons_of_mem s ht))⟩

theorem maxLabel_mem : ∀ ss : List Nat, ss ≠ [] → maxLabel ss ∈ ss
  | [], h => False.elim (h rfl)
  | [s], _ => by simp [maxLabel]
  | s :: t :: ts, _ => by
      by_cases h : s ≤ maxLabel (t :: ts)
      · rw [maxLabel, Nat.max_eq_right h]
        exact List.mem_cons_of_mem s (maxLabel_mem (t :: ts) (by simp))
      · rw [maxLabel, Nat.max_eq_left (by omega)]
        exact List.mem_cons_self

def cubeLabels (state : EdgeLabelling) : List Nat := centralLowerCubeFaceIds.map state
def radius (state : EdgeLabelling) : Nat := maxLabel (cubeLabels state)

theorem label_le_radius (state : EdgeLabelling) (face : Nat) (hf : face ∈ centralLowerCubeFaceIds) :
    state face ≤ radius state := member_le_maxLabel _ (List.mem_map.mpr ⟨face, hf, rfl⟩)

theorem radius_le (state : EdgeLabelling) (K : Nat)
    (hb : ∀ face, face ∈ centralLowerCubeFaceIds → state face ≤ K) : radius state ≤ K := by
  apply maxLabel_le
  intro s hs
  obtain ⟨face, hf, rfl⟩ := List.mem_map.mp hs
  exact hb face hf

def balancedLabel (M s : Nat) : Nat := 2 * ((2 * (s / 2)) / 3 + (M + 11) / 12)

theorem balancedLabel_even (M s : Nat) : balancedLabel M s % 2 = 0 := by
  unfold balancedLabel
  omega

/-- Rounding costs less than two label units. -/
theorem balancedLabel_affine_bound (M s : Nat) : 6 * balancedLabel M s ≤ 4 * s + M + 11 := by
  unfold balancedLabel
  omega

theorem balancedLabel_bounded (M s : Nat) (hs : s ≤ M) : balancedLabel M s ≤ max M 2 := by
  unfold balancedLabel
  have h0 := Nat.le_max_left M 2
  have h2 := Nat.le_max_right M 2
  omega

theorem balancedLabel_strict (M s : Nat) (hs : s ≤ M) (hM : 12 ≤ M) : balancedLabel M s < M := by
  have h := balancedLabel_affine_bound M s
  omega

/-- Simultaneous balancing preserves every MINIMAL source edge channel.
Common source parity is explicit and load-bearing for fusion parity. -/
theorem balancedLabel_fusion (M a b : Nat) (ha : a ≤ M) (hb : b ≤ M)
    (hp : a % 2 = b % 2) :
    fusionOK (balancedLabel M a) (balancedLabel M b) (spinDistance a b) = true := by
  rw [fusionOK_eq_true_iff]
  unfold balancedLabel spinDistance
  simp only [Nat.max_def, Nat.min_def]
  split <;> refine ⟨?_, ?_, ?_⟩ <;> omega

def balancedState (state : EdgeLabelling) : EdgeLabelling := fun face =>
  if face ∈ centralLowerCubeFaceIds then balancedLabel (radius state) (state face) else 0

theorem balancedState_on (state : EdgeLabelling) (face : Nat) (hf : face ∈ centralLowerCubeFaceIds) :
    balancedState state face = balancedLabel (radius state) (state face) := if_pos hf

theorem balancedState_off (state : EdgeLabelling) (face : Nat) (hf : face ∉ centralLowerCubeFaceIds) :
    balancedState state face = 0 := if_neg hf

theorem balancedState_common_parity (state : EdgeLabelling) : CubeSupportedCommonParity (balancedState state) := by
  refine ⟨balancedState_off state, ?_⟩
  intro face hf
  rw [balancedState_on state face hf, balancedState_on state 0 (by decide),
    balancedLabel_even, balancedLabel_even]

theorem balancedState_bounded (state : EdgeLabelling) (K : Nat) (hK : 2 ≤ K)
    (hb : ∀ face, face ∈ centralLowerCubeFaceIds → state face ≤ K) :
    ∀ face, balancedState state face ≤ K := by
  intro face
  by_cases hf : face ∈ centralLowerCubeFaceIds
  · rw [balancedState_on state face hf]
    exact Nat.le_trans (balancedLabel_bounded _ _ (label_le_radius state face hf))
      (Nat.max_le.mpr ⟨radius_le state K hb, hK⟩)
  · rw [balancedState_off state face hf]; exact Nat.zero_le K

theorem balancedState_radius_strict (state : EdgeLabelling) (hM : 12 ≤ radius state) :
    radius (balancedState state) < radius state := by
  have hb : ∀ face, face ∈ centralLowerCubeFaceIds → balancedState state face ≤ radius state - 1 := by
    intro face hf
    rw [balancedState_on state face hf]
    have h := balancedLabel_strict _ _ (label_le_radius state face hf) hM
    omega
  have h := radius_le _ _ hb
  omega

theorem balancedState_radius_affine (state : EdgeLabelling) :
    6 * radius (balancedState state) ≤ 5 * radius state + 11 := by
  have hb : ∀ face, face ∈ centralLowerCubeFaceIds →
      balancedState state face ≤ (5 * radius state + 11) / 6 := by
    intro face hf
    rw [balancedState_on state face hf]
    have h := balancedLabel_affine_bound (radius state) (state face)
    have hs := label_le_radius state face hf
    omega
  have h := radius_le _ _ hb
  omega

/-- The excess above radius eleven contracts by the explicit factor 5/6.
This is geometric label descent, NOT an operator-norm contraction. -/
theorem balancedState_excess_contraction (state : EdgeLabelling) :
    6 * (radius (balancedState state) - 11) ≤ 5 * (radius state - 11) := by
  have h := balancedState_radius_affine state
  omega

theorem balancedState_in_sector {w : Q'} (hw : (0 : Q') < w) (K : Nat) (hK : 2 ≤ K)
    (state : EdgeLabelling) (hb : ∀ face, face ∈ centralLowerCubeFaceIds → state face ≤ K) :
    balancedState state ∈ centralPhysicalFiniteVacuumSectorStates w (Q'.le_of_lt hw) K 0 :=
  cubeSupportedCommonParity_mem_sector hw K (by omega) _
    (fun face _ => balancedState_bounded state K hK hb face) (balancedState_common_parity state)

theorem difference_source_admissible (state : EdgeLabelling) :
    cubeEdgeAdmissibleB state (cubeDifferenceBoundary state) = true := by
  apply List.all_eq_true.mpr
  intro e he
  rw [cubeDifferenceBoundary_on_edge state e he]
  exact spinDistance_fusion _ _

theorem difference_balanced_admissible (state : EdgeLabelling) (hp : CubeSupportedCommonParity state) :
    cubeEdgeAdmissibleB (balancedState state) (cubeDifferenceBoundary state) = true := by
  apply List.all_eq_true.mpr
  intro e he
  have hf := cubeDifferenceEdge_faces e he
  rw [cubeDifferenceBoundary_on_edge state e he,
    balancedState_on state e.1 hf.1, balancedState_on state e.2.1 hf.2.1]
  exact balancedLabel_fusion _ _ _ (label_le_radius state _ hf.1)
    (label_le_radius state _ hf.2.1) ((hp.2 _ hf.1).trans (hp.2 _ hf.2.1).symm)

theorem difference_balanced_mask (state : EdgeLabelling) (hp : CubeSupportedCommonParity state) :
    cubeKernelAllowedB state (balancedState state) (cubeDifferenceBoundary state) = true := by
  simp only [cubeKernelAllowedB, Bool.and_eq_true]
  refine ⟨?_, ?_, difference_source_admissible state, difference_balanced_admissible state hp⟩
  · apply List.all_eq_true.mpr
    intro face hf
    apply decide_eq_true
    apply cubeDifferenceBoundary_zero_off
    have hd : cubeInactiveBoundaryIds.all (fun f => decide (f ∉ cubeDifferenceBoundaryIds)) = true := by decide
    exact of_decide_eq_true (List.all_eq_true.mp hd face hf)
  · apply List.all_eq_true.mpr
    intro corner hc
    exact cubeDifferenceBoundary_corner_fusion state corner hc

/-- One complete physical production summand, not a proposed new dynamics. -/
def balancedPhysicalWeight (w : Q') (state : EdgeLabelling) : Q' :=
  (halfHeat w state * halfHeat w (balancedState state)) * boundaryHeat w (cubeDifferenceBoundary state)

private theorem heat_product_pos {w : Q'} (hw : (0 : Q') < w) (state : EdgeLabelling) :
    ∀ ids : List Nat, (0 : Q') < eliminateLinks (fun face => coeffW w (state face)) ids
  | [] => by change (0 : Q') < 1; decide
  | face :: ids => Q'.mul_pos (coeffW_pos hw _) (heat_product_pos hw state ids)

theorem balancedPhysicalWeight_pos {w : Q'} (hw : (0 : Q') < w) (state : EdgeLabelling) :
    (0 : Q') < balancedPhysicalWeight w state :=
  Q'.mul_pos (Q'.mul_pos (heat_product_pos hw state _) (heat_product_pos hw _ _))
    (heat_product_pos hw _ _)

theorem balancedPhysicalTerm_eq_weight (w : Q') (K : Nat) (hK : 2 ≤ K) (state : EdgeLabelling)
    (hb : ∀ face, face ∈ centralLowerCubeFaceIds → state face ≤ K)
    (hp : CubeSupportedCommonParity state) :
    slabParametricKPhysicalTerm w K 1
      (assembleReflectedSlabLabelling 0 state (cubeDifferenceBoundary state) (balancedState state)) ≈
        balancedPhysicalWeight w state := by
  have h := cubePhysicalTerm_eq_mask w K state (balancedState state) (cubeDifferenceBoundary state)
    (cubeSupported_bounded K state hb hp.1) (balancedState_bounded state K hK hb)
    hp.1 (balancedState_off state) (cubeDifferenceBoundary_mem K state hb)
  rw [difference_balanced_mask state hp] at h
  exact Q'.eqv_trans _ _ _ h (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_one_eqv _))

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

theorem balancedPhysicalWeight_le_kernel {w : Q'} (hw : (0 : Q') ≤ w) (K : Nat)
    (hK : 2 ≤ K) (state : EdgeLabelling)
    (hb : ∀ face, face ∈ centralLowerCubeFaceIds → state face ≤ K)
    (hp : CubeSupportedCommonParity state) :
    balancedPhysicalWeight w state ≤ centralPhysicalReflectedKernel w K 0 state (balancedState state) := by
  have h := member_le_sum
    (fun boundary => slabParametricKPhysicalTerm w K 1
      (assembleReflectedSlabLabelling 0 state boundary (balancedState state)))
    (fun _ => slabParametricKPhysicalTerm_nonnegative hw K 1 _)
    (centralBoundaryChannels K 0) (cubeDifferenceBoundary_mem K state hb)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (balancedPhysicalTerm_eq_weight w K hK state hb hp)) h

theorem balanced_kernel_pos {w : Q'} (hw : (0 : Q') < w) (K : Nat) (hK : 2 ≤ K)
    (state : EdgeLabelling) (hb : ∀ face, face ∈ centralLowerCubeFaceIds → state face ≤ K)
    (hp : CubeSupportedCommonParity state) :
    (0 : Q') < centralPhysicalReflectedKernel w K 0 state (balancedState state) :=
  Q'.pos_of_lt_of_le (balancedPhysicalWeight_pos hw state)
    (balancedPhysicalWeight_le_kernel (Q'.le_of_lt hw) K hK state hb hp)

end YMGap.Continuum.BF4PhysicalCubeBalancedDescent

#print axioms YMGap.Continuum.BF4PhysicalCubeBalancedDescent.maxLabel
#print axioms YMGap.Continuum.BF4PhysicalCubeBalancedDescent.member_le_maxLabel
#print axioms YMGap.Continuum.BF4PhysicalCubeBalancedDescent.maxLabel_le
#print axioms YMGap.Continuum.BF4PhysicalCubeBalancedDescent.maxLabel_mem
#print axioms YMGap.Continuum.BF4PhysicalCubeBalancedDescent.cubeLabels
#print axioms YMGap.Continuum.BF4PhysicalCubeBalancedDescent.radius
#print axioms YMGap.Continuum.BF4PhysicalCubeBalancedDescent.label_le_radius
#print axioms YMGap.Continuum.BF4PhysicalCubeBalancedDescent.radius_le
#print axioms YMGap.Continuum.BF4PhysicalCubeBalancedDescent.balancedLabel
#print axioms YMGap.Continuum.BF4PhysicalCubeBalancedDescent.balancedLabel_even
#print axioms YMGap.Continuum.BF4PhysicalCubeBalancedDescent.balancedLabel_affine_bound
#print axioms YMGap.Continuum.BF4PhysicalCubeBalancedDescent.balancedLabel_bounded
#print axioms YMGap.Continuum.BF4PhysicalCubeBalancedDescent.balancedLabel_strict
#print axioms YMGap.Continuum.BF4PhysicalCubeBalancedDescent.balancedLabel_fusion
#print axioms YMGap.Continuum.BF4PhysicalCubeBalancedDescent.balancedState
#print axioms YMGap.Continuum.BF4PhysicalCubeBalancedDescent.balancedState_on
#print axioms YMGap.Continuum.BF4PhysicalCubeBalancedDescent.balancedState_off
#print axioms YMGap.Continuum.BF4PhysicalCubeBalancedDescent.balancedState_common_parity
#print axioms YMGap.Continuum.BF4PhysicalCubeBalancedDescent.balancedState_bounded
#print axioms YMGap.Continuum.BF4PhysicalCubeBalancedDescent.balancedState_radius_strict
#print axioms YMGap.Continuum.BF4PhysicalCubeBalancedDescent.balancedState_radius_affine
#print axioms YMGap.Continuum.BF4PhysicalCubeBalancedDescent.balancedState_excess_contraction
#print axioms YMGap.Continuum.BF4PhysicalCubeBalancedDescent.balancedState_in_sector
#print axioms YMGap.Continuum.BF4PhysicalCubeBalancedDescent.difference_source_admissible
#print axioms YMGap.Continuum.BF4PhysicalCubeBalancedDescent.difference_balanced_admissible
#print axioms YMGap.Continuum.BF4PhysicalCubeBalancedDescent.difference_balanced_mask
#print axioms YMGap.Continuum.BF4PhysicalCubeBalancedDescent.balancedPhysicalWeight
#print axioms YMGap.Continuum.BF4PhysicalCubeBalancedDescent.balancedPhysicalWeight_pos
#print axioms YMGap.Continuum.BF4PhysicalCubeBalancedDescent.balancedPhysicalTerm_eq_weight
#print axioms YMGap.Continuum.BF4PhysicalCubeBalancedDescent.balancedPhysicalWeight_le_kernel
#print axioms YMGap.Continuum.BF4PhysicalCubeBalancedDescent.balanced_kernel_pos
