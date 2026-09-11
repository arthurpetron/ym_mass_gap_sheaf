/-
# Weighted capacity of one exact global inward-mate target fiber

Equality of the finite target key is exactly equality of the realized target
atom.  Hence every source in one exact key fiber has the same target weight.
Combining this fact with the six-face pointwise heat comparison and the exact
fiber capacity `64` gives

  sum(source weights in one target fiber)
    <= 64 * (32,000,000^6 * representative target weight).

This is the local weighted transport certificate needed before exact Fubini
summation over realized target keys.  It does not yet bound the sum of distinct
target atoms by the physical partition, derive a posterior-variance fraction,
identify the OS transfer form, or assert a spectral or continuum gap.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, enlarged heartbeat budget, or trusted external
computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetFiberCapacity
import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetWeightComparison
import YMGap.Continuum.CompactDualSlabFaceStrandComponentHighSpinAdaptiveFiberWeight

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetFiberWeight

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetFiberCapacity
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetPhysical
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetPreimageInjectivity
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetWeight
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetWeightComparison
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalSourceNormalization
open YMGap.Continuum.CompactDualSlabFaceStrandComponentHighSpinAdaptiveFiberWeight
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Exact target-key fibers have one common target weight -/

/-- The realized target weight is nonnegative. -/
theorem GlobalCubeInwardMateCertifiedTargetFullSource.targetWeight_nonnegative
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    (0 : Q') ≤
      GlobalCubeInwardMateCertifiedTargetFullSource.targetWeight source := by
  unfold GlobalCubeInwardMateCertifiedTargetFullSource.targetWeight
  exact retainedFineIntertwinerPhysicalFiberWeight_nonnegative
    (by decide) K 0
    (GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical source)
    (GlobalCubeInwardMateCertifiedTargetFullSource.targetRaw source)

/-- Equal exact target keys force equal target weights. -/
private theorem prod_fst_eq_of_eq
    {A B : Type} {leftA rightA : A} {leftB rightB : B}
    (hpair : (leftA, leftB) = (rightA, rightB)) :
    leftA = rightA := by
  injection hpair

theorem GlobalCubeInwardMateCertifiedTargetFullSource.targetWeight_eqv_of_key_eq
    {K : Nat} {hK : 1 ≤ K}
    (left right : GlobalCubeInwardMateCertifiedTargetFullSource K hK)
    (hkey : globalInwardMateTargetKey left =
      globalInwardMateTargetKey right) :
    GlobalCubeInwardMateCertifiedTargetFullSource.targetWeight left ≈
      GlobalCubeInwardMateCertifiedTargetFullSource.targetWeight right := by
  have hatom := globalTargetAtom_eq_of_targetKey_eq left right hkey
  have hpair :
      (GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical left,
          GlobalCubeInwardMateCertifiedTargetFullSource.targetRaw left) =
        (GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical right,
          GlobalCubeInwardMateCertifiedTargetFullSource.targetRaw right) := by
    calc
      _ = GlobalCubeInwardMateCertifiedTargetFullSource.targetAtom left :=
        (globalTargetAtom_eq left).symm
      _ = GlobalCubeInwardMateCertifiedTargetFullSource.targetAtom right := hatom
      _ = _ := globalTargetAtom_eq right
  have hphysical :
      GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical left =
        GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical right :=
    prod_fst_eq_of_eq hpair
  refine Q'.eqv_trans _
    (slabParametricKPhysicalFaceFactor anchorCoupling K 1
      (GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical left)) _
    (GlobalCubeInwardMateCertifiedTargetFullSource.targetWeight_eqv_faceFactor
      left) ?_
  rw [hphysical]
  exact Q'.eqv_symm
    (GlobalCubeInwardMateCertifiedTargetFullSource.targetWeight_eqv_faceFactor
      right)

/-! ## 2. Sum the pointwise comparison inside one exact target fiber -/

private theorem listQSum_le_length_mul_local {A : Type}
    (value : A → Q') (bound : Q') : ∀ items : List A,
    (0 : Q') ≤ bound →
    (∀ item, item ∈ items → value item ≤ bound) →
      listQSum value items ≤ Q'.ofNat items.length * bound
  | [], _, _ =>
      Q'.le_of_eqv (Q'.eqv_symm (Q'.zero_mul_eqv bound))
  | head :: tail, hbound0, hvalue => by
      have htail := listQSum_le_length_mul_local value bound tail hbound0
        (fun item hitem => hvalue item (List.mem_cons_of_mem head hitem))
      have hadd := Q'.add_le_add
        (hvalue head List.mem_cons_self) htail
      exact Q'.le_trans' _ _ _ hadd
        (Q'.le_of_eqv (by
          refine Q'.eqv_symm ?_
          refine Q'.eqv_trans _
            ((Q'.ofNat tail.length + 1) * bound) _ ?_ ?_
          · exact Q'.mul_eqv_congr_right _ _ bound
              (Q'.ofNat_add_eqv tail.length 1)
          refine Q'.eqv_trans _
            (Q'.ofNat tail.length * bound + (1 : Q') * bound) _
            (Q'.add_mul_eqv (Q'.ofNat tail.length) 1 bound) ?_
          exact Q'.eqv_trans _
            (Q'.ofNat tail.length * bound + bound) _
            (Q'.add_eqv_congr_left _ _ _ (Q'.one_mul_eqv bound))
            (Q'.add_comm_eqv
              (Q'.ofNat tail.length * bound) bound)))

/-- **Weighted exact target-column capacity.**  The complete source mass over
one realized target atom costs at most `64` copies of the six-face anchor
comparison against that target atom. -/
theorem globalInwardMateTargetFiber_weight_le_sixtyFour_mateCost
    {K : Nat} {hK : 1 ≤ K}
    (representative : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    listQSum
        GlobalCubeInwardMateCertifiedTargetFullSource.weight
        (globalInwardMateTargetFiber representative) ≤
      Q'.ofNat 64 *
        (anchorInwardMateCost ^ 6 *
          GlobalCubeInwardMateCertifiedTargetFullSource.targetWeight
            representative) := by
  let fiber := globalInwardMateTargetFiber representative
  let bound := anchorInwardMateCost ^ 6 *
    GlobalCubeInwardMateCertifiedTargetFullSource.targetWeight representative
  have hcost0 : (0 : Q') ≤ anchorInwardMateCost := by
    unfold anchorInwardMateCost
    decide
  have hbound0 : (0 : Q') ≤ bound :=
    Q'.mul_nonneg _ _
      (Q'.pow_nonneg anchorInwardMateCost hcost0 6)
      (GlobalCubeInwardMateCertifiedTargetFullSource.targetWeight_nonnegative
        representative)
  have hsum :
      listQSum
          GlobalCubeInwardMateCertifiedTargetFullSource.weight fiber ≤
        Q'.ofNat fiber.length * bound := by
    apply listQSum_le_length_mul_local
    · exact hbound0
    · intro source hsource
      have hkey := globalInwardMateTargetFiber_key_eq
        representative source hsource
      have htargetWeight :=
        GlobalCubeInwardMateCertifiedTargetFullSource.targetWeight_eqv_of_key_eq
          source representative hkey
      exact Q'.le_trans' _ _ _
        (GlobalCubeInwardMateCertifiedTargetFullSource.weight_le_six_mate_cost_mul_targetWeight
          source)
        (Q'.le_of_eqv
          (Q'.mul_eqv_congr_left (anchorInwardMateCost ^ 6) _ _
            htargetWeight))
  have hlength :=
    globalInwardMateTargetFiber_length_le_sixtyFour representative
  have hlengthQ : Q'.ofNat fiber.length ≤ Q'.ofNat 64 :=
    CReal.ofNat_le_ofNat hlength
  have hscaled := Q'.mul_le_mul_of_nonneg_right _ _ bound hlengthQ hbound0
  exact Q'.le_trans' _ _ _ hsum hscaled

#print axioms GlobalCubeInwardMateCertifiedTargetFullSource.targetWeight_nonnegative
#print axioms GlobalCubeInwardMateCertifiedTargetFullSource.targetWeight_eqv_of_key_eq
#print axioms globalInwardMateTargetFiber_weight_le_sixtyFour_mateCost

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetFiberWeight
