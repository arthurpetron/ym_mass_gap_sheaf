/-
# Exact face-weight factorization for insertion into a cleared support

Let a background physical field vanish wherever an inserted pattern is
positive.  Replacing the background by the pattern on that positive support
then factors the exact corrected-slab heat face product into the pattern factor
times the background factor.

The statement is uniform in cutoff, coupling, extent, pattern, and background.
It is the analytic compiler needed by guarded non-abelian channel insertion;
all geometry is isolated in the single pointwise clearing hypothesis.

Constructive contract: finite product recursion and exact `Q'` equalities only;
no `Classical`, choice, `native_decide`, `sorry`, new axiom, noncomputable
declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

namespace YMGap.Continuum.CompactDualSlabPhysicalInsertionFactorization

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

/-- Insert `pattern` exactly on its positive support and retain `background`
elsewhere. -/
def positiveSupportInsert
    (pattern background : EdgeLabelling) : EdgeLabelling :=
  fun faceId =>
    if 0 < pattern faceId then pattern faceId else background faceId

private theorem qmul_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem mul_four_regroup (A B C D : Q') :
    (A * B) * (C * D) ≈ (A * C) * (B * D) := by
  refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv A B (C * D)) ?_
  refine Q'.eqv_trans _ _ _ ?_
    (Q'.eqv_symm (Q'.mul_assoc_eqv A C (B * D)))
  refine Q'.mul_eqv_congr_left A _ _ ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv B C D)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ D (Q'.mul_comm_eqv B C)) ?_
  exact Q'.mul_assoc_eqv C B D

private theorem eliminateLinks_positiveSupportInsert_factor
    (w : Q') (K : Nat) (pattern background : EdgeLabelling) :
    ∀ faces : List Nat,
      (∀ faceId, faceId ∈ faces → 0 < pattern faceId →
        background faceId = 0) →
      eliminateLinks
          (fun faceId => coeffAt (heatKernelPacket K w)
            (positiveSupportInsert pattern background faceId)) faces ≈
        eliminateLinks
            (fun faceId => coeffAt (heatKernelPacket K w)
              (pattern faceId)) faces *
          eliminateLinks
            (fun faceId => coeffAt (heatKernelPacket K w)
              (background faceId)) faces
  | [], _ => Q'.eqv_symm (Q'.one_mul_eqv 1)
  | faceId :: rest, hzero => by
      have htail := eliminateLinks_positiveSupportInsert_factor
        w K pattern background rest
        (fun query hquery hpositive =>
          hzero query (List.mem_cons_of_mem faceId hquery) hpositive)
      have hhead : coeffAt (heatKernelPacket K w)
            (positiveSupportInsert pattern background faceId) ≈
          coeffAt (heatKernelPacket K w) (pattern faceId) *
            coeffAt (heatKernelPacket K w) (background faceId) := by
        by_cases hpositive : 0 < pattern faceId
        · have hbackground := hzero faceId List.mem_cons_self hpositive
          unfold positiveSupportInsert
          rw [if_pos hpositive, hbackground,
            coeffAt_heatKernelPacket (Nat.succ_pos K), coeffW_zero]
          exact Q'.eqv_symm (Q'.mul_one_eqv _)
        · have hpattern : pattern faceId = 0 := by omega
          unfold positiveSupportInsert
          rw [if_neg hpositive, hpattern,
            coeffAt_heatKernelPacket (Nat.succ_pos K), coeffW_zero]
          exact Q'.eqv_symm (Q'.one_mul_eqv _)
      exact Q'.eqv_trans _ _ _
        (qmul_congr hhead htail)
        (mul_four_regroup _ _ _ _)

/-- **Cleared-support insertion factorization.**  The full exact slab face
product of an inserted pattern is the product of its isolated face factor and
the cleared background factor. -/
theorem slabParametricKPhysicalFaceFactor_positiveSupportInsert_eqv_mul
    (w : Q') (K extent : Nat) (pattern background : EdgeLabelling)
    (hzero : ∀ faceId, faceId ∈ slabPhysicalFaceEdges extent →
      0 < pattern faceId → background faceId = 0) :
    slabParametricKPhysicalFaceFactor w K extent
        (positiveSupportInsert pattern background) ≈
      slabParametricKPhysicalFaceFactor w K extent pattern *
        slabParametricKPhysicalFaceFactor w K extent background := by
  unfold slabParametricKPhysicalFaceFactor
  exact eliminateLinks_positiveSupportInsert_factor
    w K pattern background (slabPhysicalFaceEdges extent) hzero

#print axioms positiveSupportInsert
#print axioms slabParametricKPhysicalFaceFactor_positiveSupportInsert_eqv_mul

end YMGap.Continuum.CompactDualSlabPhysicalInsertionFactorization
