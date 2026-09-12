/-
# Exact eventual cutoff stability of the physical cube kernel

The edge triangle upper bounds force every contributing interface label
below twice a bound on either endpoint. Thus the raw kernel at fixed cube
states stops changing exactly once the cutoff includes both states and that
boundary range. This is a raw-kernel identity, not invariance of partition
normalization, row sums, Hilbert norms or transfer operators.

The finite saturation cutoff and stable rational entry are explicit data.
There is no limiting choice and no unknown analytic certificate here.
-/

import YMGap.Continuum.BF4PhysicalCubeKernelFactorization

namespace YMGap.Continuum.BF4PhysicalCubeKernelSaturation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4PhysicalCubeBoundaryMask
open YMGap.Continuum.BF4PhysicalCubeDifferenceBoundary
open YMGap.Continuum.BF4PhysicalCubeDifferenceBoundaryMultiplicity
open YMGap.Continuum.BF4PhysicalCubeKernelFactorization
open YMGap.Continuum.FusionQuotientCollapse
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphCutoffCoherence
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4ExplicitValenceFusionMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

/-- The original fusion upper bounds constrain every active boundary face. -/
theorem cubeKernelAllowedB_boundary_bound (R : Nat) (left right boundary : EdgeLabelling)
    (hl : ∀ face, face ∈ centralLowerCubeFaceIds → left face ≤ R)
    (ha : cubeKernelAllowedB left right boundary = true) :
    labelWithinB (2 * R) (centralFixedFaceIds 0) boundary = true := by
  have hp : cubeBoundaryZeroB boundary = true ∧ cubeCornerAdmissibleB boundary = true ∧
      cubeEdgeAdmissibleB left boundary = true ∧ cubeEdgeAdmissibleB right boundary = true := by
    simpa only [cubeKernelAllowedB, Bool.and_eq_true] using ha
  apply (labelWithinB_true_iff _ _ _).mpr
  intro face hf
  rcases fixed_faces_active_or_inactive hf with hactive | hinactive
  · have hcatalog : cubeDifferenceBoundaryIds.all (fun face => cubeDifferenceEdges.any
        (fun edge => decide (edge.2.2 = face))) = true := by decide +kernel
    obtain ⟨edge, he, hface⟩ := List.any_eq_true.mp (List.all_eq_true.mp hcatalog face hactive)
    have hfaceEq := of_decide_eq_true hface
    have htriangle := List.all_eq_true.mp hp.2.2.1 edge he
    have hupper := (fusionOK_eq_true_iff _ _ _).mp htriangle
    have hg := cubeDifferenceEdge_faces edge he
    have hleft := hl edge.1 hg.1
    have hright := hl edge.2.1 hg.2.1
    rw [← hfaceEq]
    omega
  · have hz := of_decide_eq_true (List.all_eq_true.mp hp.1 face hinactive)
    rw [hz]; exact Nat.succ_pos _

private theorem sum_eq_filter {A : Type} (value : A → Q') (test : A → Bool) :
    ∀ items : List A, (∀ item, item ∈ items → test item = false → value item ≈ 0) →
      listQSum value items ≈ listQSum value (items.filter test)
  | [], _ => Q'.eqv_refl _
  | head :: tail, hz => by
      have ih := sum_eq_filter value test tail (fun x hx => hz x (List.mem_cons_of_mem head hx))
      cases ht : test head with
      | false =>
          simp only [List.filter_cons, ht, Bool.false_eq_true, ↓reduceIte, listQSum]
          exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (hz head List.mem_cons_self ht) ih)
            (Q'.eqv_of_eq (Q'.zero_add' _))
      | true =>
          simp only [List.filter_cons, ht, ↓reduceIte, listQSum]
          exact Q'.add_eqv_congr' (Q'.eqv_refl _) ih

/-- The boundary overlap has finite support independent of the ambient cutoff. -/
theorem cubeBoundaryOverlap_cutoff_stable (w : Q') (R K L : Nat)
    (hRK : 2 * R ≤ K) (hKL : K ≤ L) (left right : EdgeLabelling)
    (hl : ∀ face, face ∈ centralLowerCubeFaceIds → left face ≤ R) :
    cubeBoundaryOverlap w L left right ≈ cubeBoundaryOverlap w K left right := by
  have hfilter : (centralBoundaryChannels L 0).filter (labelWithinB K (centralFixedFaceIds 0)) =
      centralBoundaryChannels K 0 :=
    boundedEdgeLabellings_filter_cutoff hKL _ (by decide +kernel)
  unfold cubeBoundaryOverlap
  rw [← hfilter]
  apply sum_eq_filter
  intro boundary _ hlarge
  cases ha : cubeKernelAllowedB left right boundary with
  | false =>
      exact Q'.mul_zero_eqv _
  | true =>
      have hsmall := cubeKernelAllowedB_boundary_bound R left right boundary hl ha
      have hk : labelWithinB K (centralFixedFaceIds 0) boundary = true := by
        apply (labelWithinB_true_iff _ _ _).mpr
        intro face hf
        have hv := (labelWithinB_true_iff _ _ _).mp hsmall face hf
        omega
      rw [hlarge] at hk
      cases hk

/-- Fixed-entry stability concerns the original unnormalized OS kernel. -/
theorem cubePhysicalKernel_cutoff_stable (w : Q') (R K L : Nat)
    (hRK : 2 * R ≤ K) (hKL : K ≤ L) (left right : EdgeLabelling)
    (hl : ∀ face, left face ≤ R) (hr : ∀ face, right face ≤ K)
    (hlz : ∀ face, face ∉ centralLowerCubeFaceIds → left face = 0)
    (hrz : ∀ face, face ∉ centralLowerCubeFaceIds → right face = 0) :
    centralPhysicalReflectedKernel w L 0 left right ≈ centralPhysicalReflectedKernel w K 0 left right := by
  have hRleK : R ≤ K := by omega
  refine Q'.eqv_trans _ _ _ (cubePhysicalKernel_eq_heat_overlap w L left right
    (fun face => Nat.le_trans (hl face) (Nat.le_trans hRleK hKL))
    (fun face => Nat.le_trans (hr face) hKL) hlz hrz) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _
    (cubeBoundaryOverlap_cutoff_stable w R K L hRK hKL left right (fun face _ => hl face))) ?_
  exact Q'.eqv_symm (cubePhysicalKernel_eq_heat_overlap w K left right
    (fun face => Nat.le_trans (hl face) hRleK) hr hlz hrz)

def cubeSpinSum (state : EdgeLabelling) : Nat :=
  state 0 + state 1 + state 3 + state 9 + state 19 + state 39

theorem cubeSpinSum_bounds (state : EdgeLabelling) (face : Nat)
    (hf : face ∈ centralLowerCubeFaceIds) : state face ≤ cubeSpinSum state := by
  simp only [centralLowerCubeFaceIds, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl <;> unfold cubeSpinSum <;> omega

/-- Computed finite support modulus. It is conservative and needs no search. -/
def cubeKernelSaturationCutoff (left right : EdgeLabelling) : Nat :=
  2 * (cubeSpinSum left + cubeSpinSum right)

def cubeStableRawKernel (w : Q') (left right : EdgeLabelling) : Q' :=
  centralPhysicalReflectedKernel w (cubeKernelSaturationCutoff left right) 0 left right

/-- The eventual raw entry is an explicit rational with zero error past its
computed cutoff, not merely a Cauchy limit with an unspecified modulus. -/
theorem cubeStableRawKernel_eventual (w : Q') (left right : EdgeLabelling)
    (hlz : ∀ face, face ∉ centralLowerCubeFaceIds → left face = 0)
    (hrz : ∀ face, face ∉ centralLowerCubeFaceIds → right face = 0)
    (L : Nat) (hL : cubeKernelSaturationCutoff left right ≤ L) :
    centralPhysicalReflectedKernel w L 0 left right ≈ cubeStableRawKernel w left right := by
  apply cubePhysicalKernel_cutoff_stable w (cubeSpinSum left + cubeSpinSum right)
    (cubeKernelSaturationCutoff left right) L (Nat.le_refl _) hL left right _ _ hlz hrz
  · apply cubeSupported_bounded _ left _ hlz
    intro face hf
    have hb := cubeSpinSum_bounds left face hf
    omega
  · apply cubeSupported_bounded _ right _ hrz
    intro face hf
    have hb := cubeSpinSum_bounds right face hf
    unfold cubeKernelSaturationCutoff
    omega

end YMGap.Continuum.BF4PhysicalCubeKernelSaturation

#print axioms YMGap.Continuum.BF4PhysicalCubeKernelSaturation.cubeKernelAllowedB_boundary_bound
#print axioms YMGap.Continuum.BF4PhysicalCubeKernelSaturation.cubeBoundaryOverlap_cutoff_stable
#print axioms YMGap.Continuum.BF4PhysicalCubeKernelSaturation.cubePhysicalKernel_cutoff_stable
#print axioms YMGap.Continuum.BF4PhysicalCubeKernelSaturation.cubeSpinSum_bounds
#print axioms YMGap.Continuum.BF4PhysicalCubeKernelSaturation.cubeKernelSaturationCutoff
#print axioms YMGap.Continuum.BF4PhysicalCubeKernelSaturation.cubeStableRawKernel
#print axioms YMGap.Continuum.BF4PhysicalCubeKernelSaturation.cubeStableRawKernel_eventual
