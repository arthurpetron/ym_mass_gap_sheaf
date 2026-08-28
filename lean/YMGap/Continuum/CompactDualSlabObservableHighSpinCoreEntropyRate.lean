/-
# Strict effective rate of every entropy-paid rich fiber

For an entropy-paid representative write

```text
paid = 15 * residual + extra.
```

The counted fixed-fiber coefficient then factors exactly as

```text
((8/25)^15 * 20480000)^residual * (8/25)^extra.
```

Both bases are at most `4/5`.  Hence the coefficient is bounded by
`(4/5)^(residual+extra)`, whose exponent is exactly
`paid - 14 * residual`.  The existing far geometry simultaneously proves

```text
radius + 2 <= 16 * (paid - 14 * residual).
```

This module applies that algebra to the literal accepted-target rich fiber.
It does not yet sum distinct effective exponents within one target fiber.

Constructive contract: exact natural arithmetic, rational power identities,
and finite weighted inequalities only.  No `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, noncomputable declaration, or enlarged
heartbeat budget.
-/

import YMGap.Continuum.CompactDualSlabObservableHighSpinCoreEntropyFiber

namespace YMGap.Continuum.CompactDualSlabObservableHighSpinCoreEntropyRate

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4SU2FineIntertwinerPhysicalDisintegration
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveEntropyCarrier
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveFiberWeight
open YMGap.Continuum.CompactDualSlabHighSpinFacePeelWeight
open YMGap.Continuum.CompactDualSlabObservableHighSpinCoreCarrier
open YMGap.Continuum.CompactDualSlabObservableHighSpinCoreEntropyFiber
open YMGap.Continuum.CompactDualSlabObservableHighSpinCoreEntropySplit
open YMGap.Continuum.CompactDualSlabObservableHighSpinCoreGeometry
open YMGap.Continuum.CompactDualSlabObservableHighSpinExteriorContraction
open YMGap.Continuum.CompactDualSlabObservableHighSpinExteriorPartition
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteKeyRepresentativePartition
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Exact power algebra -/

/-- The convenient strict rate used for both entropy blocks and extra paid
strands. -/
def componentCoreCompletionEntropyCeiling : Q' :=
  Q'.mkPos 4 5 (by decide)

private theorem pow_eqv_congr_local {left right : Q'}
    (h : left ≈ right) : forall exponent : Nat,
    left ^ exponent ≈ right ^ exponent
  | 0 => Q'.eqv_refl 1
  | exponent + 1 =>
      Q'.eqv_trans _ (right * left ^ exponent) _
        (Q'.mul_eqv_congr_right left right (left ^ exponent) h)
        (Q'.mul_eqv_congr_left right (left ^ exponent)
          (right ^ exponent) (pow_eqv_congr_local h exponent))

private theorem pow_mul_eqv_local (base : Q') (block : Nat) :
    forall count : Nat,
    base ^ (block * count) ≈ (base ^ block) ^ count
  | 0 => Q'.eqv_refl 1
  | count + 1 => by
      rw [Nat.mul_succ]
      refine Q'.eqv_trans _
        (base ^ (block * count) * base ^ block) _
        (Q'.pow_add_eqv base (block * count) block) ?_
      refine Q'.eqv_trans _
        ((base ^ block) ^ count * base ^ block) _
        (Q'.mul_eqv_congr_right _ _ _
          (pow_mul_eqv_local base block count)) ?_
      exact Q'.mul_comm_eqv _ _

private theorem mul_pow_eqv_local (left right : Q') : forall exponent : Nat,
    left ^ exponent * right ^ exponent ≈ (left * right) ^ exponent
  | 0 => Q'.one_mul_eqv 1
  | exponent + 1 => by
      refine Q'.eqv_trans _
        ((left * right) *
          (left ^ exponent * right ^ exponent)) _ ?_ ?_
      · exact YMGap.Continuum.PartitionUpperBound.mul_four_mid'
          left (left ^ exponent) right (right ^ exponent)
      · exact Q'.mul_eqv_congr_left (left * right) _ _
          (mul_pow_eqv_local left right exponent)

private theorem mul_reorder_three (left middle right : Q') :
    (left * middle) * right ≈ (left * right) * middle := by
  refine Q'.eqv_trans _ (left * (middle * right)) _
    (Q'.mul_assoc_eqv left middle right) ?_
  refine Q'.eqv_trans _ (left * (right * middle)) _
    (Q'.mul_eqv_congr_left left _ _ (Q'.mul_comm_eqv middle right)) ?_
  exact Q'.eqv_symm (Q'.mul_assoc_eqv left right middle)

private theorem pow_le_pow_local {left right : Q'}
    (hleft : (0 : Q') <= left) (hle : left <= right) :
    forall exponent : Nat, left ^ exponent <= right ^ exponent
  | 0 => Q'.le_refl' 1
  | exponent + 1 => by
      have hright : (0 : Q') <= right :=
        Q'.le_trans' _ _ _ hleft hle
      have hpower := pow_le_pow_local hleft hle exponent
      exact Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right _ _ _ hle
          (Q'.pow_nonneg left hleft exponent))
        (Q'.mul_le_mul_of_nonneg_left _ _ _ hpower hright)

/-- The entropy-paid two-rate coefficient contracts at the exact effective
exponent `paid - 14 * residual`. -/
theorem componentCoreCompletionEntropyPaidRate_le
    (paid residual : Nat) (hbalance : 15 * residual <= paid) :
    componentAdaptiveEntropyAnchorRatio ^ paid *
        componentCoreCompletionResidualEntropyFactor ^ residual <=
      componentCoreCompletionEntropyCeiling ^
        (paid - 14 * residual) := by
  let extra := paid - 15 * residual
  have hpaid : paid = 15 * residual + extra := by
    dsimp only [extra]
    omega
  have heffective : paid - 14 * residual = residual + extra := by
    dsimp only [extra]
    omega
  have hfactor :
      componentAdaptiveEntropyAnchorRatio ^ paid *
          componentCoreCompletionResidualEntropyFactor ^ residual ≈
        componentCoreCompletionEntropyBlockRate ^ residual *
          componentAdaptiveEntropyAnchorRatio ^ extra := by
    rw [hpaid]
    refine Q'.eqv_trans _
      ((componentAdaptiveEntropyAnchorRatio ^ (15 * residual) *
          componentAdaptiveEntropyAnchorRatio ^ extra) *
        componentCoreCompletionResidualEntropyFactor ^ residual) _ ?_ ?_
    · exact Q'.mul_eqv_congr_right _ _ _
        (Q'.pow_add_eqv componentAdaptiveEntropyAnchorRatio
          (15 * residual) extra)
    refine Q'.eqv_trans _
      ((componentAdaptiveEntropyAnchorRatio ^ (15 * residual) *
          componentCoreCompletionResidualEntropyFactor ^ residual) *
        componentAdaptiveEntropyAnchorRatio ^ extra) _ ?_ ?_
    · exact mul_reorder_three _ _ _
    refine Q'.eqv_trans _
      (((componentAdaptiveEntropyAnchorRatio ^ 15) ^ residual *
          componentCoreCompletionResidualEntropyFactor ^ residual) *
        componentAdaptiveEntropyAnchorRatio ^ extra) _ ?_ ?_
    · exact Q'.mul_eqv_congr_right _ _ _
        (Q'.mul_eqv_congr_right _ _ _
          (pow_mul_eqv_local componentAdaptiveEntropyAnchorRatio 15 residual))
    refine Q'.eqv_trans _
      (((componentAdaptiveEntropyAnchorRatio ^ 15 *
          componentCoreCompletionResidualEntropyFactor) ^ residual) *
        componentAdaptiveEntropyAnchorRatio ^ extra) _ ?_ ?_
    · exact Q'.mul_eqv_congr_right _ _ _
        (mul_pow_eqv_local
          (componentAdaptiveEntropyAnchorRatio ^ 15)
          componentCoreCompletionResidualEntropyFactor residual)
    exact Q'.mul_eqv_congr_right _ _ _
      (pow_eqv_congr_local
        (Q'.eqv_of_eq rfl) residual)
  have hblockPower := pow_le_pow_local
    (Q'.mul_nonneg _ _
      (Q'.pow_nonneg componentAdaptiveEntropyAnchorRatio (by decide) 15)
      (by decide))
    componentCoreCompletionEntropyBlockRate_le_fourFifths residual
  have hextraPower := pow_le_pow_local
    (by decide : (0 : Q') <= componentAdaptiveEntropyAnchorRatio)
    componentAdaptiveEntropyAnchorRatio_le_fourFifths extra
  have hleft :
      componentCoreCompletionEntropyBlockRate ^ residual *
          componentAdaptiveEntropyAnchorRatio ^ extra <=
        componentCoreCompletionEntropyCeiling ^ residual *
          componentAdaptiveEntropyAnchorRatio ^ extra :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hblockPower
      (Q'.pow_nonneg componentAdaptiveEntropyAnchorRatio (by decide) extra)
  have hright :
      componentCoreCompletionEntropyCeiling ^ residual *
          componentAdaptiveEntropyAnchorRatio ^ extra <=
        componentCoreCompletionEntropyCeiling ^ residual *
          componentCoreCompletionEntropyCeiling ^ extra :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hextraPower
      (Q'.pow_nonneg componentCoreCompletionEntropyCeiling (by decide)
        residual)
  rw [heffective]
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hfactor)
    (Q'.le_trans' _ _ _ hleft
      (Q'.le_trans' _ _ _ hright
        (Q'.le_of_eqv
          (Q'.eqv_symm
            (Q'.pow_add_eqv componentCoreCompletionEntropyCeiling
              residual extra)))))

/-! ## 2. Apply the effective rate to realized rich fibers -/

/-- Every selected rich-key representative is an actual member of the
entropy-paid far list. -/
theorem slabObservableHighSpinFarCoreEntropyPaidRepresentative_mem
    {D : SlabPhysicalData} {faceId : Nat}
    {hface : faceId ∈ slabPhysicalFaceEdges D.extent}
    {threshold radius : Nat}
    (representative : SlabObservableHighSpinCoreCertificate
      D faceId hface threshold)
    (hrepresentative : representative ∈
      slabObservableHighSpinFarCoreEntropyPaidRepresentatives
        D faceId hface threshold radius) :
    representative ∈
      slabObservableHighSpinFarCoreEntropyPaidCertificates
        D faceId hface threshold radius :=
  keyRepresentatives_mem_source
    slabObservableHighSpinCoreEntropyKey
    (slabObservableHighSpinFarCoreEntropyPaidCertificates
      D faceId hface threshold radius)
    representative hrepresentative

/-- A selected representative inherits the exact entropy balance and
volume-free effective-exponent distance floor. -/
theorem slabObservableHighSpinFarCoreEntropyPaidRepresentative_bounds
    {D : SlabPhysicalData} {faceId : Nat}
    {hface : faceId ∈ slabPhysicalFaceEdges D.extent}
    {threshold radius : Nat}
    (representative : SlabObservableHighSpinCoreCertificate
      D faceId hface threshold)
    (hrepresentative : representative ∈
      slabObservableHighSpinFarCoreEntropyPaidRepresentatives
        D faceId hface threshold radius) :
    15 * slabObservableHighSpinCoreCertificateResidualLength representative <=
        slabObservableHighSpinCoreCertificatePaidLength representative ∧
      radius + 2 <= 16 *
        (slabObservableHighSpinCoreCertificatePaidLength representative -
          14 * slabObservableHighSpinCoreCertificateResidualLength
            representative) := by
  have hmem :=
    slabObservableHighSpinFarCoreEntropyPaidRepresentative_mem
      representative hrepresentative
  exact ⟨slabObservableHighSpinFarCoreEntropyPaid_balance
      representative hmem,
    slabObservableHighSpinFarCoreEntropyPaid_exponent_floor
      representative hmem⟩

/-- **Strict effective-rate fixed-fiber bound.**  Every realized entropy-paid
rich fiber contracts against its accepted target at rate
`(4/5)^(paid-14*residual)`. -/
theorem slabObservableHighSpinFarCoreEntropyPaidRepresentativeFiber_effective_weight_le
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (cutoff half : Nat) (D : SlabPhysicalData)
    (hD : D = observableCouplingSlabPhysicalData
      w (Q'.le_of_lt hw0) cutoff half)
    (faceId : Nat) (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (radius : Nat)
    (representative : SlabObservableHighSpinCoreCertificate
      D faceId hface (anchorPaidExteriorThreshold w))
    (hrepresentative : representative ∈
      slabObservableHighSpinFarCoreEntropyPaidRepresentatives
        D faceId hface (anchorPaidExteriorThreshold w) radius) :
    listQSum slabObservableHighSpinCoreCertificateWeight
        (slabObservableHighSpinFarCoreEntropyPaidRepresentativeFiber
          (hface := hface) (radius := radius) representative) <=
      componentCoreCompletionEntropyCeiling ^
          (slabObservableHighSpinCoreCertificatePaidLength representative -
            14 * slabObservableHighSpinCoreCertificateResidualLength
              representative) *
        slabExpandedFineSourceWeight D
          (slabObservableHighSpinCoreEntropyTarget representative) := by
  have hraw :=
    slabObservableHighSpinFarCoreEntropyPaidRepresentativeFiber_weight_le
      hw0 hw1 cutoff half D hD faceId hface radius representative
  have hbounds :=
    slabObservableHighSpinFarCoreEntropyPaidRepresentative_bounds
      representative hrepresentative
  have hrate := componentCoreCompletionEntropyPaidRate_le
    (slabObservableHighSpinCoreCertificatePaidLength representative)
    (slabObservableHighSpinCoreCertificateResidualLength representative)
    hbounds.1
  have htarget := slabObservableExpandedFineSourceWeight_nonnegative D
    (slabObservableHighSpinCoreEntropyTarget representative)
  have hscaled := Q'.mul_le_mul_of_nonneg_right _ _ _ hrate htarget
  exact Q'.le_trans' _ _ _ hraw hscaled

#print axioms componentCoreCompletionEntropyCeiling
#print axioms componentCoreCompletionEntropyPaidRate_le
#print axioms slabObservableHighSpinFarCoreEntropyPaidRepresentative_mem
#print axioms slabObservableHighSpinFarCoreEntropyPaidRepresentative_bounds
#print axioms slabObservableHighSpinFarCoreEntropyPaidRepresentativeFiber_effective_weight_le

end YMGap.Continuum.CompactDualSlabObservableHighSpinCoreEntropyRate
