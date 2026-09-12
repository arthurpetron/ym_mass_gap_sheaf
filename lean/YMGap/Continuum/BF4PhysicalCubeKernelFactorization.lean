/-
# The actual cube OS kernel is heat times a Boolean boundary overlap

This exact formula holds for any two cube-supported bounded states and every
bounded interface boundary, not just a selected move. Twelve interface labels
are forced zero; twelve edge triangles on each half and eight corner triangles
determine the entire production multiplicity. All auxiliary fusion sums are
eliminated. The original boundary enumeration and heat weights are retained.

No uniform transition, Poincare, completed-gap or continuum claim is made.
-/

import YMGap.Continuum.BF4PhysicalCubeBoundaryMask

namespace YMGap.Continuum.BF4PhysicalCubeKernelFactorization

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCubeBoundaryMask
open YMGap.Continuum.BF4PhysicalCubeDifferenceBoundaryKernel
open YMGap.Continuum.BF4PhysicalHalfCubeSupport
open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FusionResidualBound
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4ExplicitValenceFusionMultiplicity
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

def cubeKernelAllowedB (left right boundary : EdgeLabelling) : Bool :=
  cubeBoundaryZeroB boundary && (cubeCornerAdmissibleB boundary &&
    (cubeEdgeAdmissibleB left boundary && cubeEdgeAdmissibleB right boundary))

/-- Original 24-coordinate boundary enumeration; twelve coordinates are
forced zero by cubeKernelAllowedB. There is no hidden auxiliary multiplicity. -/
def cubeBoundaryOverlap (w : Q') (K : Nat) (left right : EdgeLabelling) : Q' :=
  listQSum (fun boundary => boundaryHeat w boundary *
    Q'.ofNat (boolMultiplicity (cubeKernelAllowedB left right boundary))) (centralBoundaryChannels K 0)

private theorem product_congr (left right : Nat → Q') :
    ∀ ids : List Nat, (∀ face, face ∈ ids → left face = right face) →
      eliminateLinks left ids = eliminateLinks right ids
  | [], _ => rfl
  | face :: ids, h => by
      simp only [eliminateLinks, h face List.mem_cons_self,
        product_congr left right ids (fun f hf => h f (List.mem_cons_of_mem face hf))]

private theorem faceFactor_eq_heat (w : Q') (K : Nat)
    (physical state : EdgeLabelling) (ids : List Nat)
    (hb : ∀ face, state face ≤ K)
    (heq : ∀ face, face ∈ ids → physical face = state face) :
    slabFaceFactorOn w K physical ids = eliminateLinks (fun face => coeffW w (state face)) ids := by
  apply product_congr
  intro face hf
  rw [heq face hf, coeffAt_heatKernelPacket (Nat.lt_succ_of_le (hb face))]

/-- Exact amplitude, including all zero cases. -/
theorem halfAmplitude_eq_heat_mask (w : Q') (K : Nat) (state boundary : EdgeLabelling)
    (hs : ∀ face, state face ≤ K)
    (hz : ∀ face, face ∉ centralLowerCubeFaceIds → state face = 0)
    (hb : boundary ∈ centralBoundaryChannels K 0) :
    centralHalfAmplitude w K 0 state boundary = halfHeat w state *
      Q'.ofNat (boolMultiplicity (cubeEdgeAdmissibleB state boundary && cubeBoundaryZeroB boundary)) := by
  change slabFaceFactorOn w K (assembleReflectedSlabLabelling 0 state boundary zeroEdgeLabelling)
    (centralLowerFaceIds 0) * Q'.ofNat (slabLinkMultiplicityProductOn K 1
      (assembleReflectedSlabLabelling 0 state boundary zeroEdgeLabelling) (centralLowerLinks 0)) = _
  rw [lower_product_eq_mask K state boundary hs hz hb,
    faceFactor_eq_heat w K _ state _ hs (fun _ hf => assembled_lower state boundary hf)]
  rfl

theorem boundaryWeight_eq_heat_mask (w : Q') (K : Nat) (boundary : EdgeLabelling)
    (hb : boundary ∈ centralBoundaryChannels K 0) (hz : cubeBoundaryZeroB boundary = true) :
    centralBoundaryWeight w K 0 boundary = boundaryHeat w boundary *
      Q'.ofNat (boolMultiplicity (cubeCornerAdmissibleB boundary)) := by
  change slabFaceFactorOn w K (assembleReflectedSlabLabelling 0 zeroEdgeLabelling boundary zeroEdgeLabelling)
    (centralFixedFaceIds 0) * Q'.ofNat (slabLinkMultiplicityProductOn K 1
      (assembleReflectedSlabLabelling 0 zeroEdgeLabelling boundary zeroEdgeLabelling) (centralFixedLinks 0)) = _
  rw [fixed_product_eq_mask K boundary hb hz,
    faceFactor_eq_heat w K _ boundary _ (boundary_bounded hb)
      (fun _ hf => assembled_fixed zeroEdgeLabelling boundary hf)]
  rfl

private theorem qmul_congr {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a * c ≈ b * d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h) (Q'.mul_eqv_congr_left _ _ _ k)

private theorem qmul_right_zero (a b : Q') (hb : b ≈ 0) : a * b ≈ 0 :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hb) (Q'.mul_zero_eqv _)

private theorem heat_mask_reorder (B L R : Q') (c l r : Nat) :
    (B * Q'.ofNat c) * ((L * Q'.ofNat l) * (R * Q'.ofNat r)) ≈
      (L * R) * (B * Q'.ofNat (c * (l * r))) := by
  show ((B * Q'.ofNat c) * ((L * Q'.ofNat l) * (R * Q'.ofNat r))).num *
      (((L * R) * (B * Q'.ofNat (c * (l * r)))).den : Int) =
    ((L * R) * (B * Q'.ofNat (c * (l * r)))).num *
      (((B * Q'.ofNat c) * ((L * Q'.ofNat l) * (R * Q'.ofNat r))).den : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast]
  simp only [Q'.ofNat, Q'.den]
  rw [show Int.ofNat (c * (l * r)) = Int.ofNat c * (Int.ofNat l * Int.ofNat r) from rfl]
  push_cast
  ac_rfl

/-- Exact summand of the original production kernel, including inadmissible
boundaries. Both halves refer to the same boundary and the same action. -/
theorem cubePhysicalTerm_eq_mask (w : Q') (K : Nat) (left right boundary : EdgeLabelling)
    (hl : ∀ face, left face ≤ K) (hr : ∀ face, right face ≤ K)
    (hlz : ∀ face, face ∉ centralLowerCubeFaceIds → left face = 0)
    (hrz : ∀ face, face ∉ centralLowerCubeFaceIds → right face = 0)
    (hb : boundary ∈ centralBoundaryChannels K 0) :
    slabParametricKPhysicalTerm w K 1 (assembleReflectedSlabLabelling 0 left boundary right) ≈
      (halfHeat w left * halfHeat w right) *
        (boundaryHeat w boundary * Q'.ofNat (boolMultiplicity (cubeKernelAllowedB left right boundary))) := by
  refine Q'.eqv_trans _ _ _ (centralPhysicalTerm_eq_gram_integrand w
    (cubeSupported_mem_halfStates K left hl hlz) hb (cubeSupported_mem_halfStates K right hr hrz)) ?_
  rw [halfAmplitude_eq_heat_mask w K left boundary hl hlz hb,
    halfAmplitude_eq_heat_mask w K right boundary hr hrz hb]
  cases hz : cubeBoundaryZeroB boundary with
  | false =>
      simp only [hz, Bool.and_false, cubeKernelAllowedB, Bool.false_and, boolMultiplicity,
        Bool.false_eq_true, ↓reduceIte]
      refine Q'.eqv_trans _ 0 _ ?_ (Q'.eqv_symm (qmul_right_zero _ _ (Q'.mul_zero_eqv _)))
      exact qmul_right_zero _ _ (qmul_right_zero _ _ (Q'.mul_zero_eqv _))
  | true =>
      rw [boundaryWeight_eq_heat_mask w K boundary hb hz]
      simp only [hz, Bool.and_true, cubeKernelAllowedB, Bool.true_and]
      rw [boolMultiplicity_and, boolMultiplicity_and]
      exact heat_mask_reorder _ _ _ _ _ _

/-- **Exact six-face-state / boundary-overlap factorization of the OS kernel.** -/
theorem cubePhysicalKernel_eq_heat_overlap (w : Q') (K : Nat) (left right : EdgeLabelling)
    (hl : ∀ face, left face ≤ K) (hr : ∀ face, right face ≤ K)
    (hlz : ∀ face, face ∉ centralLowerCubeFaceIds → left face = 0)
    (hrz : ∀ face, face ∉ centralLowerCubeFaceIds → right face = 0) :
    centralPhysicalReflectedKernel w K 0 left right ≈
      (halfHeat w left * halfHeat w right) * cubeBoundaryOverlap w K left right := by
  refine Q'.eqv_trans _ _ _ ?_ (listQSum_mul_left _ _ _)
  apply listQSum_congr_on
  intro boundary hb
  exact cubePhysicalTerm_eq_mask w K left right boundary hl hr hlz hrz hb

end YMGap.Continuum.BF4PhysicalCubeKernelFactorization

#print axioms YMGap.Continuum.BF4PhysicalCubeKernelFactorization.cubeKernelAllowedB
#print axioms YMGap.Continuum.BF4PhysicalCubeKernelFactorization.cubeBoundaryOverlap
#print axioms YMGap.Continuum.BF4PhysicalCubeKernelFactorization.halfAmplitude_eq_heat_mask
#print axioms YMGap.Continuum.BF4PhysicalCubeKernelFactorization.boundaryWeight_eq_heat_mask
#print axioms YMGap.Continuum.BF4PhysicalCubeKernelFactorization.cubePhysicalTerm_eq_mask
#print axioms YMGap.Continuum.BF4PhysicalCubeKernelFactorization.cubePhysicalKernel_eq_heat_overlap
