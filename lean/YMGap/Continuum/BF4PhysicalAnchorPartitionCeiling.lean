/-
# A sharp physical partition ceiling at the fixed BF4 anchor

The actual SU(2) incidence bound gives the one-face majorant
`(s+1)^13 * (1/400)^(s*(s+2))`. Its successive ratio is at most
`2/15625`, including the step from spin zero. Geometric summation bounds
every cutoff by `15625/15623` per face. Exact finite Fubini transfers this
to the interacting physical partition, not an independent-face replacement.

The corrected extent-one slab embeds in the ambient corner box of side two,
which has exactly 96 plaquettes. Its partition is at most `65/64`.
Constants were checked first in computations/bf4_anchor_sector_escape_budget.py;
every arithmetic comparison below is independently kernel checked.

Only the spin cutoff is uniform. Coupling is fixed at 1/400, and the last
bound has fixed slab extent one. No volume, spacing, or spectral gap claim.
-/

import YMGap.Continuum.SU2PhysicalOuterCutoffFiniteFubiniTail
import YMGap.Continuum.Z4HalfTimeReflectionSlabAmbientComplement
import YMGap.Continuum.FiniteDeterministicKernelPushforward

namespace YMGap.Continuum.BF4PhysicalAnchorPartitionCeiling

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2PhysicalOuterCutoffTensorTail
open YMGap.Continuum.SU2PhysicalOuterCutoffFiniteFubiniTail
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4HalfTimeReflectionPartition
open YMGap.Continuum.Z4HalfTimeReflectionSlabAmbientComplement
open YMGap.Continuum.Z4ParametricPhysicalCutoffPartition
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-- Explicit all-spin ratio at the fixed SU(2) anchor. -/
def anchorFaceRatio : Q' := Q'.mkPos 2 15625 (by decide)

/-- Explicit geometric ceiling, retaining the near-vacuum normalization. -/
def anchorFaceCeiling : Q' := Q'.mkPos 15625 15623 (by decide)

theorem anchorFaceRatio_bound (spin : Nat) :
    tailTerm anchorCoupling physicalFacePolynomialDegree (spin + 1) ≤
      anchorFaceRatio * tailTerm anchorCoupling physicalFacePolynomialDegree spin := by
  have hratio : tailTerm anchorCoupling physicalFacePolynomialDegree (spin + 1) ≤
      (Q'.ofNat (2 ^ physicalFacePolynomialDegree) * qpow anchorCoupling 3) *
        tailTerm anchorCoupling physicalFacePolynomialDegree spin := by
    simpa only [Nat.zero_add] using tailTerm_ratio (w := anchorCoupling)
      (by decide) (by decide) physicalFacePolynomialDegree 0 spin
  have hconstant : Q'.ofNat (2 ^ physicalFacePolynomialDegree) *
      qpow anchorCoupling (2 * 0 + 3) ≈ anchorFaceRatio := by decide
  exact Q'.le_trans' _ _ _ hratio
    (Q'.le_of_eqv (Q'.mul_eqv_congr_right _ _ _ hconstant))

theorem anchorPhysicalLabelPartial_le (K : Nat) :
    su2PhysicalLabelPartial anchorCoupling K ≤ anchorFaceCeiling := by
  exact CharacterTail.geom_series_le
    (tailTerm anchorCoupling physicalFacePolynomialDegree)
    1 anchorFaceRatio anchorFaceCeiling
    (by decide) (by decide) (by decide) anchorFaceRatio_bound (by decide) (K + 1)

theorem anchorPhysicalTensorMass_le (K : Nat) : ∀ dimension : Nat,
    su2PhysicalTensorMass anchorCoupling K dimension ≤ anchorFaceCeiling ^ dimension
  | 0 => Q'.le_refl' 1
  | dimension + 1 =>
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ (anchorPhysicalLabelPartial_le K)
        (su2PhysicalTensorMass_nonnegative (by decide) K dimension))
      (Q'.mul_le_mul_of_nonneg_left _ _ _
        (anchorPhysicalTensorMass_le K dimension) (by decide))

private theorem sum_mono {A : Type} (f g : A → Q') : ∀ items : List A,
    (∀ item, item ∈ items → f item ≤ g item) →
    listQSum f items ≤ listQSum g items
  | [], _ => Q'.le_refl' 0
  | head :: tail, h => Q'.add_le_add (h head List.mem_cons_self)
      (sum_mono f g tail (fun item hi => h item (List.mem_cons_of_mem head hi)))

private theorem range_nodup_local : ∀ count : Nat, (List.range count).Nodup
  | 0 => List.nodup_nil
  | count + 1 => by
    rw [List.range_succ]
    exact List.nodup_append.mpr
      ⟨range_nodup_local count,
        List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩,
        fun item hitem member hmember => by
          have hlt := List.mem_range.mp hitem
          have heq : member = count := List.mem_singleton.mp hmember
          subst member
          omega⟩

/-- The majorant dominates the actual interacting ambient partition. -/
theorem anchorPhysicalPartition_le (K n : Nat) :
    parametricKPhysicalPartition anchorCoupling K n ≤
      anchorFaceCeiling ^ plaquetteEdgeCount n := by
  have hpointwise := sum_mono
    (parametricKPhysicalTerm anchorCoupling K n)
    (su2PhysicalFaceProduct anchorCoupling (List.range (plaquetteEdgeCount n)))
    (boundedEdgeLabellings K (List.range (plaquetteEdgeCount n)))
    (fun _ hphysical => anchorPhysicalTerm_le_degreeThirteenFaceProduct hphysical)
  have hfubini := boundedSU2PhysicalFaceMass_eq_tensorMass anchorCoupling K
    (List.range (plaquetteEdgeCount n)) (range_nodup_local _)
  rw [List.length_range] at hfubini
  exact Q'.le_trans' _ _ _ hpointwise
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hfubini)
      (anchorPhysicalTensorMass_le K (plaquetteEdgeCount n)))

/-- Source geometry: this ambient corner box has 6 * 2^4 faces. -/
theorem ambientTwo_plaquetteCount : plaquetteEdgeCount 2 = 96 := by
  unfold plaquetteEdgeCount
  rw [boxPlaquettes_length]

private theorem pow_add_eqv (q : Q') : ∀ n m : Nat,
    q ^ (n + m) ≈ q ^ n * q ^ m
  | 0, m => by
    rw [Nat.zero_add]
    exact Q'.eqv_symm (Q'.one_mul_eqv (q ^ m))
  | n + 1, m => by
    rw [Nat.succ_add]
    exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _ (pow_add_eqv q n m))
      (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))

private theorem pow_blocks_le (q r : Q') (hq : (0 : Q') ≤ q)
    (hr : (0 : Q') ≤ r) (block : Nat) (hblock : q ^ block ≤ r) :
    ∀ n : Nat, q ^ (block * n) ≤ r ^ n
  | 0 => Q'.le_refl' 1
  | n + 1 => by
    rw [Nat.mul_succ, Nat.add_comm (block * n) block]
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (pow_add_eqv q block (block * n)))
      (Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right _ _ _ hblock (Q'.pow_nonneg q hq _))
        (Q'.mul_le_mul_of_nonneg_left _ _ _ (pow_blocks_le q r hq hr block hblock n) hr))

theorem anchorFaceCeiling_pow_96_le :
    anchorFaceCeiling ^ 96 ≤ Q'.mkPos 65 64 (by decide) := by
  let blockCeiling : Q' := Q'.mkPos 10021 10000 (by decide)
  have hblock : anchorFaceCeiling ^ 16 ≤ blockCeiling := by decide
  have hblocks := pow_blocks_le anchorFaceCeiling blockCeiling
    (by decide) (by decide) 16 hblock 6
  exact Q'.le_trans' _ _ _ hblocks
    (by decide : blockCeiling ^ 6 ≤ Q'.mkPos 65 64 (by decide))

/-- Cutoff-uniform partition ceiling at fixed coupling and slab extent one. -/
theorem anchorSlabPartition_one_le_ceiling (K : Nat) :
    slabParametricKPhysicalPartition anchorCoupling K 1 ≤
      Q'.mkPos 65 64 (by decide) := by
  have hcomplement : (0 : Q') ≤
      ambientSlabComplementPhysicalPartition anchorCoupling K 1 :=
    listQSum_nonnegative_on _ _ (fun physical _ =>
      parametricKPhysicalTerm_nonnegative (by decide) K 2 physical)
  have hembed := Q'.le_trans' _ _ _
    (Q'.add_le_self_of_nonneg _ _ hcomplement)
    (Q'.le_of_eqv (slabPartition_add_complement_eq_ambientFull anchorCoupling K 1))
  have hambient := anchorPhysicalPartition_le K 2
  rw [ambientTwo_plaquetteCount] at hambient
  exact Q'.le_trans' _ _ _ hembed
    (Q'.le_trans' _ _ _ hambient anchorFaceCeiling_pow_96_le)

end YMGap.Continuum.BF4PhysicalAnchorPartitionCeiling

#print axioms YMGap.Continuum.BF4PhysicalAnchorPartitionCeiling.anchorFaceRatio_bound
#print axioms YMGap.Continuum.BF4PhysicalAnchorPartitionCeiling.anchorPhysicalLabelPartial_le
#print axioms YMGap.Continuum.BF4PhysicalAnchorPartitionCeiling.anchorPhysicalTensorMass_le
#print axioms YMGap.Continuum.BF4PhysicalAnchorPartitionCeiling.anchorPhysicalPartition_le
#print axioms YMGap.Continuum.BF4PhysicalAnchorPartitionCeiling.ambientTwo_plaquetteCount
#print axioms YMGap.Continuum.BF4PhysicalAnchorPartitionCeiling.anchorFaceCeiling_pow_96_le
#print axioms YMGap.Continuum.BF4PhysicalAnchorPartitionCeiling.anchorSlabPartition_one_le_ceiling
