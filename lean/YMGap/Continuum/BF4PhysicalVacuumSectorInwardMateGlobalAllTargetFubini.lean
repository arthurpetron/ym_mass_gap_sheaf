/-
# Exact Fubini sum over realized global inward-mate targets

The exact finite target key selects one actual successful source for every
realized target atom.  Its representative fibers partition the complete
successful-source carrier without loss.  Summing the weighted target-column
capacity therefore gives

  total successful source mass
    <= 64 * (32,000,000^6 * sum(distinct realized target weights)).

This is the exact source-side Fubini transport.  The remaining target-side
step is to inject the distinct fixed-order target presentations into the
genuine BF4 target-tuple carrier and thereby bound their weight sum by the
physical partition.  No posterior-variance, OS form, spectral-gap, or
continuum claim is made here.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, enlarged heartbeat budget, or trusted external
computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetFiberWeight
import YMGap.Continuum.FiniteKeyRepresentativePartition

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetFubini

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetFiberCapacity
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetFiberWeight
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetWeight
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalSourceNormalization
open YMGap.Continuum.FiniteKeyRepresentativePartition
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Actual representatives and their exact fibers -/

/-- One actual successful source for each distinct realized target atom. -/
def globalInwardMateTargetRepresentatives
    (K : Nat) (hK : 1 ≤ K) :
    List (GlobalCubeInwardMateCertifiedTargetFullSource K hK) :=
  keyRepresentatives globalInwardMateTargetKey
    (globalCubeInwardMateCertifiedTargetFullSources K hK)

/-- Every chosen target representative belongs to the successful-source
carrier. -/
theorem globalInwardMateTargetRepresentatives_mem_source
    {K : Nat} {hK : 1 ≤ K}
    (representative : GlobalCubeInwardMateCertifiedTargetFullSource K hK)
    (hrepresentative : representative ∈
      globalInwardMateTargetRepresentatives K hK) :
    representative ∈ globalCubeInwardMateCertifiedTargetFullSources K hK := by
  exact keyRepresentatives_mem_source globalInwardMateTargetKey
    (globalCubeInwardMateCertifiedTargetFullSources K hK)
    representative hrepresentative

/-- The generic representative fiber and the literal exact target fiber agree;
their Boolean equality tests differ only by symmetry. -/
theorem globalInwardMateRepresentativeFiber_eq_targetFiber
    {K : Nat} {hK : 1 ≤ K}
    (representative : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    representativeFiber
        (globalCubeInwardMateCertifiedTargetFullSources K hK)
        globalInwardMateTargetKey representative =
      globalInwardMateTargetFiber representative := by
  unfold representativeFiber globalInwardMateTargetFiber
  apply List.filter_congr
  intro source _
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hkey
    apply decide_eq_true
    exact (of_decide_eq_true hkey).symm
  · intro hkey
    apply decide_eq_true
    exact (of_decide_eq_true hkey).symm

private theorem listQSum_congr_mem_local
    {A : Type} {left right : A → Q'} :
    ∀ items : List A,
      (∀ item, item ∈ items → left item ≈ right item) →
      listQSum left items ≈ listQSum right items
  | [], _ => Q'.eqv_refl 0
  | head :: tail, hagree =>
      Q'.add_eqv_congr'
        (hagree head List.mem_cons_self)
        (listQSum_congr_mem_local tail
          (fun item hitem =>
            hagree item (List.mem_cons_of_mem head hitem)))

/-- **Exact realized-target Fubini identity.**  Summing the literal target
fibers over the selected distinct representatives recovers all successful
source weight. -/
theorem globalInwardMateTargetRepresentativeFibers_weight_total
    (K : Nat) (hK : 1 ≤ K) :
    listQSum
        (fun representative =>
          listQSum
            GlobalCubeInwardMateCertifiedTargetFullSource.weight
            (globalInwardMateTargetFiber representative))
        (globalInwardMateTargetRepresentatives K hK) ≈
      listQSum
        GlobalCubeInwardMateCertifiedTargetFullSource.weight
        (globalCubeInwardMateCertifiedTargetFullSources K hK) := by
  unfold globalInwardMateTargetRepresentatives
  refine Q'.eqv_trans _
    (listQSum
      (fun representative =>
        listQSum
          GlobalCubeInwardMateCertifiedTargetFullSource.weight
          (representativeFiber
            (globalCubeInwardMateCertifiedTargetFullSources K hK)
            globalInwardMateTargetKey representative))
      (keyRepresentatives globalInwardMateTargetKey
        (globalCubeInwardMateCertifiedTargetFullSources K hK))) _ ?_ ?_
  · apply listQSum_congr_mem_local
    intro representative _
    rw [globalInwardMateRepresentativeFiber_eq_targetFiber]
    exact Q'.eqv_refl _
  · exact keyRepresentativeFibers_weight_total
      (globalCubeInwardMateCertifiedTargetFullSources K hK)
      GlobalCubeInwardMateCertifiedTargetFullSource.weight
      globalInwardMateTargetKey

/-! ## 2. Sum the weighted capacity over every realized target -/

private theorem listQSum_le_termwise_local
    {A : Type} (left right : A → Q') : ∀ items : List A,
    (∀ item, item ∈ items → left item ≤ right item) →
      listQSum left items ≤ listQSum right items
  | [], _ => Q'.le_refl' 0
  | head :: tail, hpoint =>
      Q'.add_le_add
        (hpoint head List.mem_cons_self)
        (listQSum_le_termwise_local left right tail
          (fun item hitem =>
            hpoint item (List.mem_cons_of_mem head hitem)))

private theorem representativeTargetBounds_factor
    {K : Nat} {hK : 1 ≤ K} :
    listQSum
        (fun representative :
            GlobalCubeInwardMateCertifiedTargetFullSource K hK =>
          Q'.ofNat 64 *
            (anchorInwardMateCost ^ 6 *
              GlobalCubeInwardMateCertifiedTargetFullSource.targetWeight
                representative))
        (globalInwardMateTargetRepresentatives K hK) ≈
      Q'.ofNat 64 *
        (anchorInwardMateCost ^ 6 *
          listQSum
            GlobalCubeInwardMateCertifiedTargetFullSource.targetWeight
            (globalInwardMateTargetRepresentatives K hK)) := by
  refine Q'.eqv_trans _
    (Q'.ofNat 64 *
      listQSum
        (fun representative =>
          anchorInwardMateCost ^ 6 *
            GlobalCubeInwardMateCertifiedTargetFullSource.targetWeight
              representative)
        (globalInwardMateTargetRepresentatives K hK)) _ ?_ ?_
  · exact listQSum_mul_left (Q'.ofNat 64)
      (fun representative =>
        anchorInwardMateCost ^ 6 *
          GlobalCubeInwardMateCertifiedTargetFullSource.targetWeight
            representative)
      (globalInwardMateTargetRepresentatives K hK)
  · exact Q'.mul_eqv_congr_left (Q'.ofNat 64) _ _
      (listQSum_mul_left (anchorInwardMateCost ^ 6)
        GlobalCubeInwardMateCertifiedTargetFullSource.targetWeight
        (globalInwardMateTargetRepresentatives K hK))

/-- **Summed exact-key transport.**  The complete successful-source mass is
bounded by the explicit six-bit congestion and six-face heat cost times the
sum of one target weight for each distinct realized target atom. -/
theorem globalInwardMateSuccessfulSourceWeight_le_representativeTargets
    (K : Nat) (hK : 1 ≤ K) :
    listQSum
        GlobalCubeInwardMateCertifiedTargetFullSource.weight
        (globalCubeInwardMateCertifiedTargetFullSources K hK) ≤
      Q'.ofNat 64 *
        (anchorInwardMateCost ^ 6 *
          listQSum
            GlobalCubeInwardMateCertifiedTargetFullSource.targetWeight
            (globalInwardMateTargetRepresentatives K hK)) := by
  have htotal :=
    globalInwardMateTargetRepresentativeFibers_weight_total K hK
  have hcolumns :
      listQSum
          (fun representative =>
            listQSum
              GlobalCubeInwardMateCertifiedTargetFullSource.weight
              (globalInwardMateTargetFiber representative))
          (globalInwardMateTargetRepresentatives K hK) ≤
        listQSum
          (fun representative =>
            Q'.ofNat 64 *
              (anchorInwardMateCost ^ 6 *
                GlobalCubeInwardMateCertifiedTargetFullSource.targetWeight
                  representative))
          (globalInwardMateTargetRepresentatives K hK) := by
    apply listQSum_le_termwise_local
    intro representative _
    exact globalInwardMateTargetFiber_weight_le_sixtyFour_mateCost
      representative
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_symm htotal))
    (Q'.le_trans' _ _ _ hcolumns
      (Q'.le_of_eqv representativeTargetBounds_factor))

#print axioms globalInwardMateTargetRepresentatives
#print axioms globalInwardMateTargetRepresentatives_mem_source
#print axioms globalInwardMateRepresentativeFiber_eq_targetFiber
#print axioms globalInwardMateTargetRepresentativeFibers_weight_total
#print axioms globalInwardMateSuccessfulSourceWeight_le_representativeTargets

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetFubini
