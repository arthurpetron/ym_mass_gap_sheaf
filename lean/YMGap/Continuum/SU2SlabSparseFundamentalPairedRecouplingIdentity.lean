/-
# Sparse fundamental higher-valence slab links have unit paired weight

Bundle a local external-spin word by the two geometric properties supplied
by a closed binary surface away from a switch: every label is at most one and
the total incident spin is zero or two.  The sparse theorem makes each
valence-four, valence-five, or valence-six one-replica recoupling entry exactly
one; lower valences already carry the one-point identity matrix.
Tensoring the two physical replicas therefore leaves every such production
slab-link coordinate exactly one as well.

This is the desired non-pivot identity: ordinary surface links do not
accumulate a volume-dependent loss.  The separate four-fundamental pivot
theorem supplies the only nontrivial local factor.

Constructive contract: finite words, exact `Q'` normalization, and
definitional specialization of the production slab packages only; no
`Classical`, choice, `native_decide`, `sorry`, new axiom, noncomputable
declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.SU2SlabPhysicalPairRecouplingKernel
import YMGap.Continuum.SU2SparseFundamentalHigherValenceKernel

namespace YMGap.Continuum.SU2SlabSparseFundamentalPairedRecouplingIdentity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.FiniteBistochasticQKernelComposition
open YMGap.Continuum.SU2DirectRightFixedOutputSections
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FixedLeftTransvectantEvaluation
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2PhysicalSchurBistochasticKernel
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingKernel
open YMGap.Continuum.SU2SparseFundamentalHigherValenceKernel
open YMGap.Continuum.SU2ValenceFiveCommonAssociatorCarrier
open YMGap.Continuum.SU2ValenceFiveSecondBistochasticBlock
open YMGap.Continuum.SU2ValenceSixPrefixBistochasticBlock
open YMGap.Continuum.SU2ValenceSixThirdBistochasticBlock
open YMGap.Continuum.Z4CanonicalLinkUsedCoordinates
open YMGap.Continuum.Z4ExplicitCutoffOneSurfaceSelection
open YMGap.Continuum.Z4ValenceFusionCutoffIndependence

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The sparse local-word certificate -/

structure SparseFundamentalWord (degree : Nat) (external : EdgeLabelling) :
    Prop where
  label_le_one : ∀ position, position < degree → external position ≤ 1
  total_eq_zero_or_two : localExternalSpinSum degree external = 0 ∨
    localExternalSpinSum degree external = 2

private theorem range_four_local : List.range 4 = [0, 1, 2, 3] := rfl

private theorem range_five_local : List.range 5 = [0, 1, 2, 3, 4] := rfl

private theorem range_six_local : List.range 6 = [0, 1, 2, 3, 4, 5] := rfl

private theorem sparseFourTotal
    (external : EdgeLabelling) (h : SparseFundamentalWord 4 external) :
    external 0 + external 1 + external 2 + external 3 = 0 ∨
      external 0 + external 1 + external 2 + external 3 = 2 := by
  have htotal := h.total_eq_zero_or_two
  unfold localExternalSpinSum at htotal
  rw [range_four_local] at htotal
  simp only [List.map, natListSum] at htotal
  rcases htotal with hzero | htwo
  · left
    omega
  · right
    omega

private theorem sparseFiveTotal
    (external : EdgeLabelling) (h : SparseFundamentalWord 5 external) :
    external 0 + external 1 + external 2 + external 3 + external 4 = 0 ∨
      external 0 + external 1 + external 2 + external 3 + external 4 = 2 := by
  have htotal := h.total_eq_zero_or_two
  unfold localExternalSpinSum at htotal
  rw [range_five_local] at htotal
  simp only [List.map, natListSum] at htotal
  rcases htotal with hzero | htwo
  · left
    omega
  · right
    omega

private theorem sparseSixTotal
    (external : EdgeLabelling) (h : SparseFundamentalWord 6 external) :
    external 0 + external 1 + external 2 + external 3 + external 4 +
        external 5 = 0 ∨
      external 0 + external 1 + external 2 + external 3 + external 4 +
        external 5 = 2 := by
  have htotal := h.total_eq_zero_or_two
  unfold localExternalSpinSum at htotal
  rw [range_six_local] at htotal
  simp only [List.map, natListSum] at htotal
  rcases htotal with hzero | htwo
  · left
    omega
  · right
    omega

/-! ## 2. One-replica higher-valence identities -/

theorem sparseFundamentalWord_valenceFourKernel_eqv_one
    (external : EdgeLabelling) (h : SparseFundamentalWord 4 external)
    (source : FixedLeftCGChannel
      (external 0) (external 1) (external 2) (external 3))
    (target : FixedRightCGChannel
      (external 0) (external 1) (external 2) (external 3)) :
    (physicalSchurBistochasticKernel
      (external 0) (external 1) (external 2) (external 3)).weight
        source target ≈ 1 :=
  evenSparsePhysicalSchurKernel_eqv_one
    (external 0) (external 1) (external 2) (external 3)
    (h.label_le_one 1 (by decide))
    (h.label_le_one 2 (by decide))
    (sparseFourTotal external h) source target

theorem sparseFundamentalWord_valenceFiveKernel_eqv_one
    (external : EdgeLabelling) (h : SparseFundamentalWord 5 external)
    (source : ValenceFiveLeftCarrier
      (external 0) (external 1) (external 2) (external 3) (external 4))
    (target : ValenceFiveRightCarrier
      (external 0) (external 1) (external 2) (external 3) (external 4)) :
    (valenceFiveBistochasticKernel
      (external 0) (external 1) (external 2) (external 3) (external 4)).weight
        source target ≈ 1 :=
  evenSparseValenceFiveKernel_eqv_one
    (external 0) (external 1) (external 2) (external 3) (external 4)
    (h.label_le_one 1 (by decide))
    (h.label_le_one 2 (by decide))
    (h.label_le_one 3 (by decide))
    (sparseFiveTotal external h) source target

theorem sparseFundamentalWord_valenceSixKernel_eqv_one
    (external : EdgeLabelling) (h : SparseFundamentalWord 6 external)
    (source : ValenceSixLeftCarrier
      (external 0) (external 1) (external 2) (external 3)
      (external 4) (external 5))
    (target : ValenceSixRightCarrier
      (external 0) (external 1) (external 2) (external 3)
      (external 4) (external 5)) :
    (valenceSixBistochasticKernel
      (external 0) (external 1) (external 2) (external 3)
      (external 4) (external 5)).weight source target ≈ 1 :=
  evenSparseValenceSixKernel_eqv_one
    (external 0) (external 1) (external 2) (external 3)
    (external 4) (external 5)
    (h.label_le_one 0 (by decide))
    (h.label_le_one 1 (by decide))
    (h.label_le_one 2 (by decide))
    (h.label_le_one 3 (by decide))
    (h.label_le_one 4 (by decide))
    (h.label_le_one 5 (by decide))
    (sparseSixTotal external h) source target

/-! ## 3. Tensor the two physical replicas -/

private theorem mul_eqv_one_of_eqv_one {left right : Q'}
    (hleft : left ≈ 1) (hright : right ≈ 1) :
    left * right ≈ 1 :=
  Q'.eqv_trans _ (1 * right) _
    (Q'.mul_eqv_congr_right left 1 right hleft)
    (Q'.eqv_trans _ (1 * 1) _
      (Q'.mul_eqv_congr_left 1 right 1 hright)
      (Q'.one_mul_eqv 1))

theorem slabPhysicalPairRecouplingKernelPackageFour_sparse_eqv_one
    {extent : Nat} (D : SlabPhysicalPairRecouplingData extent 4)
    (hleft : SparseFundamentalWord 4
      (slabLinkExternalSpins extent D.leftPhysical D.link))
    (hright : SparseFundamentalWord 4
      (slabLinkExternalSpins extent D.rightPhysical D.link))
    (source : (slabPhysicalPairRecouplingKernelPackageFour D).Source)
    (target : (slabPhysicalPairRecouplingKernelPackageFour D).Target) :
    (slabPhysicalPairRecouplingKernelPackageFour D).kernel.weight
        source target ≈ 1 := by
  change
    tensorWeight
      (physicalSchurBistochasticKernel
        ((slabLinkExternalSpins extent D.leftPhysical D.link) 0)
        ((slabLinkExternalSpins extent D.leftPhysical D.link) 1)
        ((slabLinkExternalSpins extent D.leftPhysical D.link) 2)
        ((slabLinkExternalSpins extent D.leftPhysical D.link) 3))
      (physicalSchurBistochasticKernel
        ((slabLinkExternalSpins extent D.rightPhysical D.link) 0)
        ((slabLinkExternalSpins extent D.rightPhysical D.link) 1)
        ((slabLinkExternalSpins extent D.rightPhysical D.link) 2)
        ((slabLinkExternalSpins extent D.rightPhysical D.link) 3))
      source target ≈ 1
  unfold tensorWeight
  exact mul_eqv_one_of_eqv_one
    (sparseFundamentalWord_valenceFourKernel_eqv_one
      (slabLinkExternalSpins extent D.leftPhysical D.link)
      hleft source.1 target.1)
    (sparseFundamentalWord_valenceFourKernel_eqv_one
      (slabLinkExternalSpins extent D.rightPhysical D.link)
      hright source.2 target.2)

theorem slabPhysicalPairRecouplingKernelPackageFour_sparse_pos
    {extent : Nat} (D : SlabPhysicalPairRecouplingData extent 4)
    (hleft : SparseFundamentalWord 4
      (slabLinkExternalSpins extent D.leftPhysical D.link))
    (hright : SparseFundamentalWord 4
      (slabLinkExternalSpins extent D.rightPhysical D.link))
    (source : (slabPhysicalPairRecouplingKernelPackageFour D).Source)
    (target : (slabPhysicalPairRecouplingKernelPackageFour D).Target) :
    (0 : Q') <
      (slabPhysicalPairRecouplingKernelPackageFour D).kernel.weight
        source target :=
  Q'.pos_of_lt_of_le (by decide : (0 : Q') < 1)
    (Q'.ge_of_eqv
      (slabPhysicalPairRecouplingKernelPackageFour_sparse_eqv_one
        D hleft hright source target))

theorem slabPhysicalPairRecouplingKernelPackageFive_sparse_eqv_one
    {extent : Nat} (D : SlabPhysicalPairRecouplingData extent 5)
    (hleft : SparseFundamentalWord 5
      (slabLinkExternalSpins extent D.leftPhysical D.link))
    (hright : SparseFundamentalWord 5
      (slabLinkExternalSpins extent D.rightPhysical D.link))
    (source : (slabPhysicalPairRecouplingKernelPackageFive D).Source)
    (target : (slabPhysicalPairRecouplingKernelPackageFive D).Target) :
    (slabPhysicalPairRecouplingKernelPackageFive D).kernel.weight
        source target ≈ 1 := by
  change
    tensorWeight
      (valenceFiveBistochasticKernel
        ((slabLinkExternalSpins extent D.leftPhysical D.link) 0)
        ((slabLinkExternalSpins extent D.leftPhysical D.link) 1)
        ((slabLinkExternalSpins extent D.leftPhysical D.link) 2)
        ((slabLinkExternalSpins extent D.leftPhysical D.link) 3)
        ((slabLinkExternalSpins extent D.leftPhysical D.link) 4))
      (valenceFiveBistochasticKernel
        ((slabLinkExternalSpins extent D.rightPhysical D.link) 0)
        ((slabLinkExternalSpins extent D.rightPhysical D.link) 1)
        ((slabLinkExternalSpins extent D.rightPhysical D.link) 2)
        ((slabLinkExternalSpins extent D.rightPhysical D.link) 3)
        ((slabLinkExternalSpins extent D.rightPhysical D.link) 4))
      source target ≈ 1
  unfold tensorWeight
  exact mul_eqv_one_of_eqv_one
    (sparseFundamentalWord_valenceFiveKernel_eqv_one
      (slabLinkExternalSpins extent D.leftPhysical D.link)
      hleft source.1 target.1)
    (sparseFundamentalWord_valenceFiveKernel_eqv_one
      (slabLinkExternalSpins extent D.rightPhysical D.link)
      hright source.2 target.2)

theorem slabPhysicalPairRecouplingKernelPackageFive_sparse_pos
    {extent : Nat} (D : SlabPhysicalPairRecouplingData extent 5)
    (hleft : SparseFundamentalWord 5
      (slabLinkExternalSpins extent D.leftPhysical D.link))
    (hright : SparseFundamentalWord 5
      (slabLinkExternalSpins extent D.rightPhysical D.link))
    (source : (slabPhysicalPairRecouplingKernelPackageFive D).Source)
    (target : (slabPhysicalPairRecouplingKernelPackageFive D).Target) :
    (0 : Q') <
      (slabPhysicalPairRecouplingKernelPackageFive D).kernel.weight
        source target :=
  Q'.pos_of_lt_of_le (by decide : (0 : Q') < 1)
    (Q'.ge_of_eqv
      (slabPhysicalPairRecouplingKernelPackageFive_sparse_eqv_one
        D hleft hright source target))

theorem slabPhysicalPairRecouplingKernelPackageSix_sparse_eqv_one
    {extent : Nat} (D : SlabPhysicalPairRecouplingData extent 6)
    (hleft : SparseFundamentalWord 6
      (slabLinkExternalSpins extent D.leftPhysical D.link))
    (hright : SparseFundamentalWord 6
      (slabLinkExternalSpins extent D.rightPhysical D.link))
    (source : (slabPhysicalPairRecouplingKernelPackageSix D).Source)
    (target : (slabPhysicalPairRecouplingKernelPackageSix D).Target) :
    (slabPhysicalPairRecouplingKernelPackageSix D).kernel.weight
        source target ≈ 1 := by
  change
    tensorWeight
      (valenceSixBistochasticKernel
        ((slabLinkExternalSpins extent D.leftPhysical D.link) 0)
        ((slabLinkExternalSpins extent D.leftPhysical D.link) 1)
        ((slabLinkExternalSpins extent D.leftPhysical D.link) 2)
        ((slabLinkExternalSpins extent D.leftPhysical D.link) 3)
        ((slabLinkExternalSpins extent D.leftPhysical D.link) 4)
        ((slabLinkExternalSpins extent D.leftPhysical D.link) 5))
      (valenceSixBistochasticKernel
        ((slabLinkExternalSpins extent D.rightPhysical D.link) 0)
        ((slabLinkExternalSpins extent D.rightPhysical D.link) 1)
        ((slabLinkExternalSpins extent D.rightPhysical D.link) 2)
        ((slabLinkExternalSpins extent D.rightPhysical D.link) 3)
        ((slabLinkExternalSpins extent D.rightPhysical D.link) 4)
        ((slabLinkExternalSpins extent D.rightPhysical D.link) 5))
      source target ≈ 1
  unfold tensorWeight
  exact mul_eqv_one_of_eqv_one
    (sparseFundamentalWord_valenceSixKernel_eqv_one
      (slabLinkExternalSpins extent D.leftPhysical D.link)
      hleft source.1 target.1)
    (sparseFundamentalWord_valenceSixKernel_eqv_one
      (slabLinkExternalSpins extent D.rightPhysical D.link)
      hright source.2 target.2)

theorem slabPhysicalPairRecouplingKernelPackageSix_sparse_pos
    {extent : Nat} (D : SlabPhysicalPairRecouplingData extent 6)
    (hleft : SparseFundamentalWord 6
      (slabLinkExternalSpins extent D.leftPhysical D.link))
    (hright : SparseFundamentalWord 6
      (slabLinkExternalSpins extent D.rightPhysical D.link))
    (source : (slabPhysicalPairRecouplingKernelPackageSix D).Source)
    (target : (slabPhysicalPairRecouplingKernelPackageSix D).Target) :
    (0 : Q') <
      (slabPhysicalPairRecouplingKernelPackageSix D).kernel.weight
        source target :=
  Q'.pos_of_lt_of_le (by decide : (0 : Q') < 1)
    (Q'.ge_of_eqv
      (slabPhysicalPairRecouplingKernelPackageSix_sparse_eqv_one
        D hleft hright source target))

/-! ## 4. One all-valence non-pivot compiler -/

/-- Every entry of the paired production recoupling matrix is exactly one when
both physical words are sparse.  This single statement contracts the complete
ambient slab valence split: degrees below four are the one-point matrix,
degrees four through six are the singleton-carrier theorems above, and larger
degrees contradict the geometric degree bound carried by `D`. -/
theorem slabPhysicalPairRecouplingKernelPackage_sparse_eqv_one
    {extent degree : Nat}
    (D : SlabPhysicalPairRecouplingData extent degree)
    (hleft : SparseFundamentalWord degree
      (slabLinkExternalSpins extent D.leftPhysical D.link))
    (hright : SparseFundamentalWord degree
      (slabLinkExternalSpins extent D.rightPhysical D.link))
    (source : (slabPhysicalPairRecouplingKernelPackage degree D).Source)
    (target : (slabPhysicalPairRecouplingKernelPackage degree D).Target) :
    (slabPhysicalPairRecouplingKernelPackage degree D).kernel.weight
        source target ≈ 1 := by
  cases degree with
  | zero => exact Q'.eqv_refl 1
  | succ degree =>
      cases degree with
      | zero => exact Q'.eqv_refl 1
      | succ degree =>
          cases degree with
          | zero => exact Q'.eqv_refl 1
          | succ degree =>
              cases degree with
              | zero => exact Q'.eqv_refl 1
              | succ degree =>
                  cases degree with
                  | zero =>
                      exact
                        slabPhysicalPairRecouplingKernelPackageFour_sparse_eqv_one
                          D hleft hright source target
                  | succ degree =>
                      cases degree with
                      | zero =>
                          exact
                            slabPhysicalPairRecouplingKernelPackageFive_sparse_eqv_one
                              D hleft hright source target
                      | succ degree =>
                          cases degree with
                          | zero =>
                              exact
                                slabPhysicalPairRecouplingKernelPackageSix_sparse_eqv_one
                                  D hleft hright source target
                          | succ degree =>
                              exact False.elim (by
                                have hdegree := D.degree_le_six
                                omega)

theorem slabPhysicalPairRecouplingKernelPackage_sparse_pos
    {extent degree : Nat}
    (D : SlabPhysicalPairRecouplingData extent degree)
    (hleft : SparseFundamentalWord degree
      (slabLinkExternalSpins extent D.leftPhysical D.link))
    (hright : SparseFundamentalWord degree
      (slabLinkExternalSpins extent D.rightPhysical D.link))
    (source : (slabPhysicalPairRecouplingKernelPackage degree D).Source)
    (target : (slabPhysicalPairRecouplingKernelPackage degree D).Target) :
    (0 : Q') <
      (slabPhysicalPairRecouplingKernelPackage degree D).kernel.weight
        source target :=
  Q'.pos_of_lt_of_le (by decide : (0 : Q') < 1)
    (Q'.ge_of_eqv
      (slabPhysicalPairRecouplingKernelPackage_sparse_eqv_one
        D hleft hright source target))

end YMGap.Continuum.SU2SlabSparseFundamentalPairedRecouplingIdentity

#print axioms YMGap.Continuum.SU2SlabSparseFundamentalPairedRecouplingIdentity.sparseFundamentalWord_valenceFiveKernel_eqv_one
#print axioms YMGap.Continuum.SU2SlabSparseFundamentalPairedRecouplingIdentity.sparseFundamentalWord_valenceFourKernel_eqv_one
#print axioms YMGap.Continuum.SU2SlabSparseFundamentalPairedRecouplingIdentity.slabPhysicalPairRecouplingKernelPackageFour_sparse_eqv_one
#print axioms YMGap.Continuum.SU2SlabSparseFundamentalPairedRecouplingIdentity.slabPhysicalPairRecouplingKernelPackageFour_sparse_pos
#print axioms YMGap.Continuum.SU2SlabSparseFundamentalPairedRecouplingIdentity.sparseFundamentalWord_valenceSixKernel_eqv_one
#print axioms YMGap.Continuum.SU2SlabSparseFundamentalPairedRecouplingIdentity.slabPhysicalPairRecouplingKernelPackageFive_sparse_eqv_one
#print axioms YMGap.Continuum.SU2SlabSparseFundamentalPairedRecouplingIdentity.slabPhysicalPairRecouplingKernelPackageFive_sparse_pos
#print axioms YMGap.Continuum.SU2SlabSparseFundamentalPairedRecouplingIdentity.slabPhysicalPairRecouplingKernelPackageSix_sparse_eqv_one
#print axioms YMGap.Continuum.SU2SlabSparseFundamentalPairedRecouplingIdentity.slabPhysicalPairRecouplingKernelPackageSix_sparse_pos
#print axioms YMGap.Continuum.SU2SlabSparseFundamentalPairedRecouplingIdentity.slabPhysicalPairRecouplingKernelPackage_sparse_eqv_one
#print axioms YMGap.Continuum.SU2SlabSparseFundamentalPairedRecouplingIdentity.slabPhysicalPairRecouplingKernelPackage_sparse_pos
