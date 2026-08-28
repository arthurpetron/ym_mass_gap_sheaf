/-
# Double geometric tail of the entropy-paid far core

Inside one accepted-target fiber, rich representatives have injective
coordinates

```text
(residual, extra := paid - 15 * residual)
```

and their already-summed inverse fibers cost at most
`(4/5)^(residual+extra)` times the accepted-target weight.  At radius
`32 * floor`, the far geometry forces one coordinate to be at least
`floor + 1`.  Splitting on that coordinate embeds each branch into a shifted
finite Cartesian square.  Two elementary geometric sums therefore close the
entire entropy-paid far branch with a volume-free tail.

Constructive contract: finite Boolean filters, injective natural-coordinate
maps, and rational geometric summation only.  No `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, noncomputable declaration, or enlarged
heartbeat budget.
-/

import YMGap.Constructive.CharacterTail
import YMGap.Continuum.CompactDualSlabObservableHighSpinCoreEntropyTargetPartition

namespace YMGap.Continuum.CompactDualSlabObservableHighSpinCoreEntropyTargetTail

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CharacterTail
open YMGap.Constructive.RationalTail
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabHighSpinFacePeelWeight
open YMGap.Continuum.CompactDualSlabObservableHighSpinCoreCarrier
open YMGap.Continuum.CompactDualSlabObservableHighSpinCoreEntropyFiber
open YMGap.Continuum.CompactDualSlabObservableHighSpinCoreEntropyRate
open YMGap.Continuum.CompactDualSlabObservableHighSpinCoreEntropySplit
open YMGap.Continuum.CompactDualSlabObservableHighSpinCoreEntropyTargetPartition
open YMGap.Continuum.CompactDualSlabObservableHighSpinCoreGeometry
open YMGap.Continuum.CompactDualSlabObservableHighSpinExteriorContraction
open YMGap.Continuum.CompactDualSlabObservableHighSpinExteriorPartition
open YMGap.Continuum.CompactDualSlabObservableRemovalPartition
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteKeyRepresentativePartition
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Exact finite double geometric sum -/

private theorem listQSum_range_eqv_finSum_local (value : Nat -> Q') :
    forall count : Nat,
      listQSum value (List.range count) ≈ finSum value count
  | 0 => Q'.eqv_refl 0
  | count + 1 => by
      rw [List.range_succ, finSum_succ]
      exact Q'.eqv_trans _
        (listQSum value (List.range count) + listQSum value [count]) _
        (listQSum_append value (List.range count) [count])
        (Q'.add_eqv_congr'
          (listQSum_range_eqv_finSum_local value count)
          (Q'.eqv_of_eq (Q'.add_zero' (value count))))

private theorem listQSum_mul_left_local {A : Type}
    (factor : Q') (value : A -> Q') :
    forall items : List A,
      listQSum (fun item => factor * value item) items ≈
        factor * listQSum value items
  | [] => Q'.eqv_symm (Q'.mul_zero_eqv factor)
  | item :: items => by
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (Q'.eqv_refl _)
          (listQSum_mul_left_local factor value items))
        (Q'.eqv_symm
          (Q'.mul_add_eqv factor (value item) (listQSum value items)))

private theorem listQSum_mul_right_local {A : Type}
    (value : A -> Q') (factor : Q') :
    forall items : List A,
      listQSum (fun item => value item * factor) items ≈
        listQSum value items * factor
  | [] => Q'.eqv_symm (Q'.zero_mul_eqv factor)
  | item :: items => by
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (Q'.eqv_refl _)
          (listQSum_mul_right_local value factor items))
        (Q'.eqv_symm
          (Q'.add_mul_eqv (value item) (listQSum value items) factor))

private theorem range_nodup_local :
    forall count : Nat, (List.range count).Nodup
  | 0 => List.nodup_nil
  | count + 1 => by
      rw [List.range_succ]
      exact List.nodup_append.mpr
        ⟨range_nodup_local count,
          List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩,
          fun item hitem member hmember => by
            have hmemberEq : member = count := List.mem_singleton.mp hmember
            subst member
            exact Nat.ne_of_lt (List.mem_range.mp hitem)⟩

/-- Every finite partial sum of `(4/5)^n` is at most `5`. -/
theorem componentCoreCompletionEntropyCeiling_fullTail_le (count : Nat) :
    listQSum
        (fun index => componentCoreCompletionEntropyCeiling ^ index)
        (List.range count) <= 5 := by
  have hfinite : finSum
      (fun index => componentCoreCompletionEntropyCeiling ^ index) count <=
        5 := by
    apply geom_series_le
      (fun index => componentCoreCompletionEntropyCeiling ^ index)
      1 componentCoreCompletionEntropyCeiling 5
    · decide
    · decide
    · rw [Q'.pow_zero]
      exact Q'.le_refl' 1
    · intro index
      rw [show index + 1 = index + 1 by rfl, Q'.pow_succ]
      exact Q'.le_refl' _
    · decide
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (listQSum_range_eqv_finSum_local
        (fun index => componentCoreCompletionEntropyCeiling ^ index) count))
    hfinite

/-- A shifted Cartesian square of effective exponents costs at most two
geometric factors `5`, hence `25`, times its common target charge. -/
theorem componentCoreCompletionEntropyCeiling_shiftedSquare_le
    (floor count : Nat) (targetWeight : Q')
    (htargetWeight : (0 : Q') <= targetWeight) :
    listQSum
        (fun pair =>
          ((componentCoreCompletionEntropyCeiling ^ floor *
              componentCoreCompletionEntropyCeiling ^ pair.1) *
            componentCoreCompletionEntropyCeiling ^ pair.2) * targetWeight)
        (cartesian (List.range count) (List.range count)) <=
      (25 * componentCoreCompletionEntropyCeiling ^ floor) * targetWeight := by
  have hright := listQSum_mul_right_local
    (fun pair : Nat × Nat =>
      (componentCoreCompletionEntropyCeiling ^ floor *
          componentCoreCompletionEntropyCeiling ^ pair.1) *
        componentCoreCompletionEntropyCeiling ^ pair.2)
    targetWeight (cartesian (List.range count) (List.range count))
  have hcartesian := listQSum_cartesian_product
    (fun left => componentCoreCompletionEntropyCeiling ^ floor *
      componentCoreCompletionEntropyCeiling ^ left)
    (fun right => componentCoreCompletionEntropyCeiling ^ right)
    (List.range count) (List.range count)
  have hleftFactor := listQSum_mul_left_local
    (componentCoreCompletionEntropyCeiling ^ floor)
    (fun left => componentCoreCompletionEntropyCeiling ^ left)
    (List.range count)
  have htail := componentCoreCompletionEntropyCeiling_fullTail_le count
  have hpow0 : (0 : Q') <=
      componentCoreCompletionEntropyCeiling ^ floor :=
    Q'.pow_nonneg componentCoreCompletionEntropyCeiling (by decide) floor
  have hleftScaled := Q'.mul_le_mul_of_nonneg_left _ _ _ htail hpow0
  have htailNonnegative : (0 : Q') <=
      listQSum
        (fun index => componentCoreCompletionEntropyCeiling ^ index)
        (List.range count) :=
    listQSum_nonnegative_on _ _ (fun index _ =>
      Q'.pow_nonneg componentCoreCompletionEntropyCeiling (by decide) index)
  have hfiveNonnegative : (0 : Q') <=
      componentCoreCompletionEntropyCeiling ^ floor * 5 :=
    Q'.mul_nonneg _ _ hpow0 (by decide)
  have hfirst := Q'.mul_le_mul_of_nonneg_right _ _ _
    hleftScaled htailNonnegative
  have hsecond := Q'.mul_le_mul_of_nonneg_left _ _ _ htail hfiveNonnegative
  have hdouble :
      (componentCoreCompletionEntropyCeiling ^ floor *
          listQSum
            (fun left => componentCoreCompletionEntropyCeiling ^ left)
            (List.range count)) *
        listQSum
          (fun right => componentCoreCompletionEntropyCeiling ^ right)
          (List.range count) <=
        (componentCoreCompletionEntropyCeiling ^ floor * 5) * 5 :=
    Q'.le_trans' _ _ _ hfirst hsecond
  have hscale := Q'.mul_le_mul_of_nonneg_right _ _ _ hdouble htargetWeight
  have htwentyFive : (5 : Q') * 5 ≈ 25 := by decide
  have hcoefficient :
      (componentCoreCompletionEntropyCeiling ^ floor * 5) * 5 ≈
        25 * componentCoreCompletionEntropyCeiling ^ floor := by
    refine Q'.eqv_trans _
      (componentCoreCompletionEntropyCeiling ^ floor * (5 * 5)) _
      (Q'.mul_assoc_eqv _ _ _) ?_
    refine Q'.eqv_trans _
      (componentCoreCompletionEntropyCeiling ^ floor * 25) _
      (Q'.mul_eqv_congr_left _ _ _ htwentyFive) ?_
    exact Q'.mul_comm_eqv _ _
  have hsumEqv :
      listQSum
          (fun pair =>
            ((componentCoreCompletionEntropyCeiling ^ floor *
                componentCoreCompletionEntropyCeiling ^ pair.1) *
              componentCoreCompletionEntropyCeiling ^ pair.2) * targetWeight)
          (cartesian (List.range count) (List.range count)) ≈
        ((componentCoreCompletionEntropyCeiling ^ floor *
            listQSum
              (fun left => componentCoreCompletionEntropyCeiling ^ left)
              (List.range count)) *
          listQSum
            (fun right => componentCoreCompletionEntropyCeiling ^ right)
            (List.range count)) * targetWeight :=
    Q'.eqv_trans _ _ _ hright
      (Q'.mul_eqv_congr_right _ _ _
        (Q'.eqv_trans _ _ _ hcartesian
          (Q'.mul_eqv_congr_right _ _ _ hleftFactor)))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hsumEqv)
    (Q'.le_trans' _ _ _ hscale
      (Q'.le_of_eqv
        (Q'.mul_eqv_congr_right _ _ targetWeight hcoefficient)))

/-! ## 2. The far floor forces one long effective coordinate -/

/-- At spatial radius `32 * floor`, every selected rich representative has
either residual coordinate or extra coordinate at least `floor + 1`. -/
theorem slabObservableHighSpinFarCoreEntropyPaidRepresentative_effectivePair_floor
    {D : SlabPhysicalData} {faceId : Nat}
    {hface : faceId ∈ slabPhysicalFaceEdges D.extent}
    {threshold floor : Nat}
    (representative : SlabObservableHighSpinCoreCertificate
      D faceId hface threshold)
    (hrepresentative : representative ∈
      slabObservableHighSpinFarCoreEntropyPaidRepresentatives
        D faceId hface threshold (32 * floor)) :
    floor + 1 <=
        (slabObservableHighSpinCoreEntropyEffectivePair representative).1 ∨
      floor + 1 <=
        (slabObservableHighSpinCoreEntropyEffectivePair representative).2 := by
  have hbounds :=
    slabObservableHighSpinFarCoreEntropyPaidRepresentative_bounds
      representative hrepresentative
  change
    floor + 1 <=
        slabObservableHighSpinCoreCertificateResidualLength representative ∨
      floor + 1 <=
        slabObservableHighSpinCoreCertificatePaidLength representative -
          15 *
            slabObservableHighSpinCoreCertificateResidualLength representative
  omega

/-! ## 3. Shifted coordinate branches inside one accepted target -/

/-- Executable test for the residual-long half of the effective pair. -/
def slabObservableHighSpinCoreEntropyResidualLongTest
    {D : SlabPhysicalData} {faceId : Nat}
    {hface : faceId ∈ slabPhysicalFaceEdges D.extent}
    {threshold : Nat} (floor : Nat)
    (representative : SlabObservableHighSpinCoreCertificate
      D faceId hface threshold) : Bool :=
  decide (floor + 1 <=
    (slabObservableHighSpinCoreEntropyEffectivePair representative).1)

/-- Representatives in one target fiber whose residual coordinate is long. -/
def slabObservableHighSpinFarCoreEntropyPaidTargetResidualLongFiber
    {D : SlabPhysicalData} {faceId : Nat}
    {hface : faceId ∈ slabPhysicalFaceEdges D.extent}
    {threshold : Nat} (floor : Nat)
    (targetRepresentative : SlabObservableHighSpinCoreCertificate
      D faceId hface threshold) :
    List (SlabObservableHighSpinCoreCertificate
      D faceId hface threshold) :=
  (slabObservableHighSpinFarCoreEntropyPaidTargetFiber
    (hface := hface) (radius := 32 * floor) targetRepresentative).filter
      (slabObservableHighSpinCoreEntropyResidualLongTest floor)

/-- Complementary representatives; the far floor will force their extra
coordinate to be long. -/
def slabObservableHighSpinFarCoreEntropyPaidTargetExtraLongFiber
    {D : SlabPhysicalData} {faceId : Nat}
    {hface : faceId ∈ slabPhysicalFaceEdges D.extent}
    {threshold : Nat} (floor : Nat)
    (targetRepresentative : SlabObservableHighSpinCoreCertificate
      D faceId hface threshold) :
    List (SlabObservableHighSpinCoreCertificate
      D faceId hface threshold) :=
  (slabObservableHighSpinFarCoreEntropyPaidTargetFiber
    (hface := hface) (radius := 32 * floor) targetRepresentative).filter
      (fun representative =>
        !(slabObservableHighSpinCoreEntropyResidualLongTest
          floor representative))

/-- Shift the known-long residual coordinate down by `floor + 1`. -/
def slabObservableHighSpinCoreEntropyResidualShiftEncode
    {D : SlabPhysicalData} {faceId : Nat}
    {hface : faceId ∈ slabPhysicalFaceEdges D.extent}
    {threshold : Nat} (floor : Nat)
    (representative : SlabObservableHighSpinCoreCertificate
      D faceId hface threshold) : Nat × Nat :=
  ((slabObservableHighSpinCoreEntropyEffectivePair representative).1 -
      (floor + 1),
    (slabObservableHighSpinCoreEntropyEffectivePair representative).2)

/-- Shift the known-long extra coordinate down by `floor + 1`. -/
def slabObservableHighSpinCoreEntropyExtraShiftEncode
    {D : SlabPhysicalData} {faceId : Nat}
    {hface : faceId ∈ slabPhysicalFaceEdges D.extent}
    {threshold : Nat} (floor : Nat)
    (representative : SlabObservableHighSpinCoreCertificate
      D faceId hface threshold) : Nat × Nat :=
  ((slabObservableHighSpinCoreEntropyEffectivePair representative).1,
    (slabObservableHighSpinCoreEntropyEffectivePair representative).2 -
      (floor + 1))

private theorem nodup_of_map_nodup_local {A B : Type} (map : A -> B) :
    forall items : List A, (items.map map).Nodup -> items.Nodup
  | [], _ => List.nodup_nil
  | head :: tail, hnodup => by
      have hparts := List.nodup_cons.mp hnodup
      apply List.nodup_cons.mpr
      refine ⟨?_, nodup_of_map_nodup_local map tail hparts.2⟩
      intro hmem
      exact hparts.1 (List.mem_map.mpr ⟨head, hmem, rfl⟩)

private theorem slabObservableHighSpinFarCoreEntropyPaidTargetFiber_nodup
    {D : SlabPhysicalData} {faceId : Nat}
    {hface : faceId ∈ slabPhysicalFaceEdges D.extent}
    {threshold radius : Nat}
    (targetRepresentative : SlabObservableHighSpinCoreCertificate
      D faceId hface threshold) :
    (slabObservableHighSpinFarCoreEntropyPaidTargetFiber
      (hface := hface) (radius := radius) targetRepresentative).Nodup := by
  unfold slabObservableHighSpinFarCoreEntropyPaidTargetFiber
    representativeFiber
  apply List.filter_sublist.nodup
  exact nodup_of_map_nodup_local
    slabObservableHighSpinCoreEntropyKey _
    (slabObservableHighSpinFarCoreEntropyPaidRepresentatives_keys_nodup
      D faceId hface threshold radius)

private theorem slabObservableHighSpinFarCoreEntropyPaidTargetResidualLongFiber_nodup
    {D : SlabPhysicalData} {faceId : Nat}
    {hface : faceId ∈ slabPhysicalFaceEdges D.extent}
    {threshold floor : Nat}
    (targetRepresentative : SlabObservableHighSpinCoreCertificate
      D faceId hface threshold) :
    (slabObservableHighSpinFarCoreEntropyPaidTargetResidualLongFiber
      floor targetRepresentative).Nodup := by
  unfold slabObservableHighSpinFarCoreEntropyPaidTargetResidualLongFiber
  exact List.filter_sublist.nodup
    (slabObservableHighSpinFarCoreEntropyPaidTargetFiber_nodup
      targetRepresentative)

private theorem slabObservableHighSpinFarCoreEntropyPaidTargetExtraLongFiber_nodup
    {D : SlabPhysicalData} {faceId : Nat}
    {hface : faceId ∈ slabPhysicalFaceEdges D.extent}
    {threshold floor : Nat}
    (targetRepresentative : SlabObservableHighSpinCoreCertificate
      D faceId hface threshold) :
    (slabObservableHighSpinFarCoreEntropyPaidTargetExtraLongFiber
      floor targetRepresentative).Nodup := by
  unfold slabObservableHighSpinFarCoreEntropyPaidTargetExtraLongFiber
  exact List.filter_sublist.nodup
    (slabObservableHighSpinFarCoreEntropyPaidTargetFiber_nodup
      targetRepresentative)

private theorem slabObservableHighSpinFarCoreEntropyPaidTargetResidualLongFiber_encode_mem
    {D : SlabPhysicalData} {faceId : Nat}
    {hface : faceId ∈ slabPhysicalFaceEdges D.extent}
    {threshold floor : Nat}
    (targetRepresentative representative :
      SlabObservableHighSpinCoreCertificate D faceId hface threshold)
    (_hrepresentative : representative ∈
      slabObservableHighSpinFarCoreEntropyPaidTargetResidualLongFiber
        floor targetRepresentative) :
    slabObservableHighSpinCoreEntropyResidualShiftEncode floor representative ∈
      cartesian
        (List.range (slabObservableRemovalMaxSize D + 1))
        (List.range (slabObservableRemovalMaxSize D + 1)) := by
  apply (mem_cartesian_iff _ _ _).2
  have hbounds :=
    slabObservableHighSpinFarCoreEntropyPaidRepresentative_pair_bounds
      representative
  constructor
  · apply List.mem_range.mpr
    change
      (slabObservableHighSpinCoreEntropyEffectivePair representative).1 -
          (floor + 1) < slabObservableRemovalMaxSize D + 1
    omega
  · apply List.mem_range.mpr
    change
      (slabObservableHighSpinCoreEntropyEffectivePair representative).2 <
        slabObservableRemovalMaxSize D + 1
    omega

private theorem slabObservableHighSpinFarCoreEntropyPaidTargetExtraLongFiber_encode_mem
    {D : SlabPhysicalData} {faceId : Nat}
    {hface : faceId ∈ slabPhysicalFaceEdges D.extent}
    {threshold floor : Nat}
    (targetRepresentative representative :
      SlabObservableHighSpinCoreCertificate D faceId hface threshold)
    (_hrepresentative : representative ∈
      slabObservableHighSpinFarCoreEntropyPaidTargetExtraLongFiber
        floor targetRepresentative) :
    slabObservableHighSpinCoreEntropyExtraShiftEncode floor representative ∈
      cartesian
        (List.range (slabObservableRemovalMaxSize D + 1))
        (List.range (slabObservableRemovalMaxSize D + 1)) := by
  apply (mem_cartesian_iff _ _ _).2
  have hbounds :=
    slabObservableHighSpinFarCoreEntropyPaidRepresentative_pair_bounds
      representative
  constructor
  · apply List.mem_range.mpr
    change
      (slabObservableHighSpinCoreEntropyEffectivePair representative).1 <
        slabObservableRemovalMaxSize D + 1
    omega
  · apply List.mem_range.mpr
    change
      (slabObservableHighSpinCoreEntropyEffectivePair representative).2 -
          (floor + 1) < slabObservableRemovalMaxSize D + 1
    omega

private theorem slabObservableHighSpinFarCoreEntropyPaidTargetResidualLongFiber_encode_injective
    {D : SlabPhysicalData} {faceId : Nat}
    {hface : faceId ∈ slabPhysicalFaceEdges D.extent}
    {threshold floor : Nat}
    (targetRepresentative left :
      SlabObservableHighSpinCoreCertificate D faceId hface threshold)
    (hleft : left ∈
      slabObservableHighSpinFarCoreEntropyPaidTargetResidualLongFiber
        floor targetRepresentative)
    (right : SlabObservableHighSpinCoreCertificate
      D faceId hface threshold)
    (hright : right ∈
      slabObservableHighSpinFarCoreEntropyPaidTargetResidualLongFiber
        floor targetRepresentative)
    (hencode :
      slabObservableHighSpinCoreEntropyResidualShiftEncode floor left =
        slabObservableHighSpinCoreEntropyResidualShiftEncode floor right) :
    left = right := by
  have hleftFiber := (List.mem_filter.mp hleft).1
  have hrightFiber := (List.mem_filter.mp hright).1
  have hleftLong := of_decide_eq_true (List.mem_filter.mp hleft).2
  have hrightLong := of_decide_eq_true (List.mem_filter.mp hright).2
  apply slabObservableHighSpinFarCoreEntropyPaidTargetFiber_pair_injective
    targetRepresentative left hleftFiber right hrightFiber
  apply Prod.ext
  · have hfirst := congrArg Prod.fst hencode
    change
      (slabObservableHighSpinCoreEntropyEffectivePair left).1 - (floor + 1) =
        (slabObservableHighSpinCoreEntropyEffectivePair right).1 - (floor + 1)
      at hfirst
    change floor + 1 <=
      (slabObservableHighSpinCoreEntropyEffectivePair left).1 at hleftLong
    change floor + 1 <=
      (slabObservableHighSpinCoreEntropyEffectivePair right).1 at hrightLong
    omega
  · have hsecond := congrArg Prod.snd hencode
    change
      (slabObservableHighSpinCoreEntropyEffectivePair left).2 =
        (slabObservableHighSpinCoreEntropyEffectivePair right).2 at hsecond
    exact hsecond

private theorem slabObservableHighSpinFarCoreEntropyPaidTargetExtraLongFiber_extra_floor
    {D : SlabPhysicalData} {faceId : Nat}
    {hface : faceId ∈ slabPhysicalFaceEdges D.extent}
    {threshold floor : Nat}
    (targetRepresentative representative :
      SlabObservableHighSpinCoreCertificate D faceId hface threshold)
    (hrepresentative : representative ∈
      slabObservableHighSpinFarCoreEntropyPaidTargetExtraLongFiber
        floor targetRepresentative) :
    floor + 1 <=
      (slabObservableHighSpinCoreEntropyEffectivePair representative).2 := by
  have hfiber := (List.mem_filter.mp hrepresentative).1
  have hrich := (List.mem_filter.mp hfiber).1
  have hfloor :=
    slabObservableHighSpinFarCoreEntropyPaidRepresentative_effectivePair_floor
      representative hrich
  by_cases hresidual : floor + 1 <=
      (slabObservableHighSpinCoreEntropyEffectivePair representative).1
  · have htest :
        slabObservableHighSpinCoreEntropyResidualLongTest
          floor representative = true := decide_eq_true hresidual
    have hcomplement := (List.mem_filter.mp hrepresentative).2
    simp only [htest, Bool.not_true, Bool.false_eq_true] at hcomplement
  · exact hfloor.resolve_left hresidual

private theorem slabObservableHighSpinFarCoreEntropyPaidTargetExtraLongFiber_encode_injective
    {D : SlabPhysicalData} {faceId : Nat}
    {hface : faceId ∈ slabPhysicalFaceEdges D.extent}
    {threshold floor : Nat}
    (targetRepresentative left :
      SlabObservableHighSpinCoreCertificate D faceId hface threshold)
    (hleft : left ∈
      slabObservableHighSpinFarCoreEntropyPaidTargetExtraLongFiber
        floor targetRepresentative)
    (right : SlabObservableHighSpinCoreCertificate
      D faceId hface threshold)
    (hright : right ∈
      slabObservableHighSpinFarCoreEntropyPaidTargetExtraLongFiber
        floor targetRepresentative)
    (hencode : slabObservableHighSpinCoreEntropyExtraShiftEncode floor left =
      slabObservableHighSpinCoreEntropyExtraShiftEncode floor right) :
    left = right := by
  have hleftFiber := (List.mem_filter.mp hleft).1
  have hrightFiber := (List.mem_filter.mp hright).1
  have hleftLong :=
    slabObservableHighSpinFarCoreEntropyPaidTargetExtraLongFiber_extra_floor
      targetRepresentative left hleft
  have hrightLong :=
    slabObservableHighSpinFarCoreEntropyPaidTargetExtraLongFiber_extra_floor
      targetRepresentative right hright
  apply slabObservableHighSpinFarCoreEntropyPaidTargetFiber_pair_injective
    targetRepresentative left hleftFiber right hrightFiber
  apply Prod.ext
  · have hfirst := congrArg Prod.fst hencode
    change
      (slabObservableHighSpinCoreEntropyEffectivePair left).1 =
        (slabObservableHighSpinCoreEntropyEffectivePair right).1 at hfirst
    exact hfirst
  · have hsecond := congrArg Prod.snd hencode
    change
      (slabObservableHighSpinCoreEntropyEffectivePair left).2 - (floor + 1) =
        (slabObservableHighSpinCoreEntropyEffectivePair right).2 - (floor + 1)
      at hsecond
    omega

/-! ## 4. Sum each shifted branch -/

private theorem slabObservableHighSpinFarCoreEntropyPaidTargetResidualLongFiber_term_le
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (cutoff half : Nat) (D : SlabPhysicalData)
    (hD : D = observableCouplingSlabPhysicalData
      w (Q'.le_of_lt hw0) cutoff half)
    (faceId : Nat) (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (floor : Nat)
    (targetRepresentative representative :
      SlabObservableHighSpinCoreCertificate
        D faceId hface (anchorPaidExteriorThreshold w))
    (hrepresentative : representative ∈
      slabObservableHighSpinFarCoreEntropyPaidTargetResidualLongFiber
        floor targetRepresentative) :
    listQSum slabObservableHighSpinCoreCertificateWeight
        (slabObservableHighSpinFarCoreEntropyPaidRepresentativeFiber
          (hface := hface) (radius := 32 * floor) representative) <=
      ((componentCoreCompletionEntropyCeiling ^ (floor + 1) *
          componentCoreCompletionEntropyCeiling ^
            (slabObservableHighSpinCoreEntropyResidualShiftEncode
              floor representative).1) *
        componentCoreCompletionEntropyCeiling ^
          (slabObservableHighSpinCoreEntropyResidualShiftEncode
            floor representative).2) *
        slabExpandedFineSourceWeight D
          (slabObservableHighSpinCoreEntropyTarget targetRepresentative) := by
  have htargetFiber := (List.mem_filter.mp hrepresentative).1
  have hrich := (List.mem_filter.mp htargetFiber).1
  have hlong := of_decide_eq_true (List.mem_filter.mp hrepresentative).2
  have hbounds :=
    slabObservableHighSpinFarCoreEntropyPaidRepresentative_bounds
      representative hrich
  have hraw :=
    slabObservableHighSpinFarCoreEntropyPaidRepresentativeFiber_effective_weight_le
      hw0 hw1 cutoff half D hD faceId hface (32 * floor)
      representative hrich
  have htarget :=
    slabObservableHighSpinCoreEntropyTarget_eq_of_targetKey_eq
      targetRepresentative representative
      (slabObservableHighSpinFarCoreEntropyPaidTargetFiber_key_eq
        targetRepresentative representative htargetFiber)
  rw [← htarget] at hraw
  let residual :=
    slabObservableHighSpinCoreCertificateResidualLength representative
  let paid := slabObservableHighSpinCoreCertificatePaidLength representative
  let extra := paid - 15 * residual
  have heffective : paid - 14 * residual = residual + extra := by
    dsimp only [paid, residual, extra]
    omega
  have hlong' : floor + 1 <= residual := by
    change floor + 1 <=
      slabObservableHighSpinCoreCertificateResidualLength representative
    exact hlong
  have hdecompose :
      residual + extra = (floor + 1 + (residual - (floor + 1))) + extra := by
    omega
  have hpow :
      componentCoreCompletionEntropyCeiling ^ (residual + extra) ≈
        (componentCoreCompletionEntropyCeiling ^ (floor + 1) *
            componentCoreCompletionEntropyCeiling ^
              (residual - (floor + 1))) *
          componentCoreCompletionEntropyCeiling ^ extra := by
    rw [hdecompose]
    refine Q'.eqv_trans _
      (componentCoreCompletionEntropyCeiling ^
          (floor + 1 + (residual - (floor + 1))) *
        componentCoreCompletionEntropyCeiling ^ extra) _
      (Q'.pow_add_eqv _ _ _) ?_
    exact Q'.mul_eqv_congr_right _ _ _
      (Q'.pow_add_eqv _ _ _)
  rw [show
      slabObservableHighSpinCoreCertificatePaidLength representative -
          14 * slabObservableHighSpinCoreCertificateResidualLength
            representative = paid - 14 * residual by rfl,
    heffective] at hraw
  change
    listQSum slabObservableHighSpinCoreCertificateWeight
        (slabObservableHighSpinFarCoreEntropyPaidRepresentativeFiber
          (hface := hface) (radius := 32 * floor) representative) <=
      ((componentCoreCompletionEntropyCeiling ^ (floor + 1) *
          componentCoreCompletionEntropyCeiling ^
            (residual - (floor + 1))) *
        componentCoreCompletionEntropyCeiling ^ extra) *
        slabExpandedFineSourceWeight D
          (slabObservableHighSpinCoreEntropyTarget targetRepresentative)
  exact Q'.le_trans' _ _ _ hraw
    (Q'.le_of_eqv
      (Q'.mul_eqv_congr_right _ _ _ hpow))

private theorem slabObservableHighSpinFarCoreEntropyPaidTargetExtraLongFiber_term_le
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (cutoff half : Nat) (D : SlabPhysicalData)
    (hD : D = observableCouplingSlabPhysicalData
      w (Q'.le_of_lt hw0) cutoff half)
    (faceId : Nat) (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (floor : Nat)
    (targetRepresentative representative :
      SlabObservableHighSpinCoreCertificate
        D faceId hface (anchorPaidExteriorThreshold w))
    (hrepresentative : representative ∈
      slabObservableHighSpinFarCoreEntropyPaidTargetExtraLongFiber
        floor targetRepresentative) :
    listQSum slabObservableHighSpinCoreCertificateWeight
        (slabObservableHighSpinFarCoreEntropyPaidRepresentativeFiber
          (hface := hface) (radius := 32 * floor) representative) <=
      ((componentCoreCompletionEntropyCeiling ^ (floor + 1) *
          componentCoreCompletionEntropyCeiling ^
            (slabObservableHighSpinCoreEntropyExtraShiftEncode
              floor representative).1) *
        componentCoreCompletionEntropyCeiling ^
          (slabObservableHighSpinCoreEntropyExtraShiftEncode
            floor representative).2) *
        slabExpandedFineSourceWeight D
          (slabObservableHighSpinCoreEntropyTarget targetRepresentative) := by
  have htargetFiber := (List.mem_filter.mp hrepresentative).1
  have hrich := (List.mem_filter.mp htargetFiber).1
  have hlong :=
    slabObservableHighSpinFarCoreEntropyPaidTargetExtraLongFiber_extra_floor
      targetRepresentative representative hrepresentative
  have hbounds :=
    slabObservableHighSpinFarCoreEntropyPaidRepresentative_bounds
      representative hrich
  have hraw :=
    slabObservableHighSpinFarCoreEntropyPaidRepresentativeFiber_effective_weight_le
      hw0 hw1 cutoff half D hD faceId hface (32 * floor)
      representative hrich
  have htarget :=
    slabObservableHighSpinCoreEntropyTarget_eq_of_targetKey_eq
      targetRepresentative representative
      (slabObservableHighSpinFarCoreEntropyPaidTargetFiber_key_eq
        targetRepresentative representative htargetFiber)
  rw [← htarget] at hraw
  let residual :=
    slabObservableHighSpinCoreCertificateResidualLength representative
  let paid := slabObservableHighSpinCoreCertificatePaidLength representative
  let extra := paid - 15 * residual
  have heffective : paid - 14 * residual = residual + extra := by
    dsimp only [paid, residual, extra]
    omega
  have hlong' : floor + 1 <= extra := by
    dsimp only [extra, paid, residual]
    exact hlong
  have hdecompose :
      residual + extra = (floor + 1 + residual) + (extra - (floor + 1)) := by
    omega
  have hpow :
      componentCoreCompletionEntropyCeiling ^ (residual + extra) ≈
        (componentCoreCompletionEntropyCeiling ^ (floor + 1) *
            componentCoreCompletionEntropyCeiling ^ residual) *
          componentCoreCompletionEntropyCeiling ^
            (extra - (floor + 1)) := by
    rw [hdecompose]
    refine Q'.eqv_trans _
      (componentCoreCompletionEntropyCeiling ^
          (floor + 1 + residual) *
        componentCoreCompletionEntropyCeiling ^ (extra - (floor + 1))) _
      (Q'.pow_add_eqv _ _ _) ?_
    exact Q'.mul_eqv_congr_right _ _ _
      (Q'.pow_add_eqv _ _ _)
  rw [show
      slabObservableHighSpinCoreCertificatePaidLength representative -
          14 * slabObservableHighSpinCoreCertificateResidualLength
            representative = paid - 14 * residual by rfl,
    heffective] at hraw
  change
    listQSum slabObservableHighSpinCoreCertificateWeight
        (slabObservableHighSpinFarCoreEntropyPaidRepresentativeFiber
          (hface := hface) (radius := 32 * floor) representative) <=
      ((componentCoreCompletionEntropyCeiling ^ (floor + 1) *
          componentCoreCompletionEntropyCeiling ^ residual) *
        componentCoreCompletionEntropyCeiling ^ (extra - (floor + 1))) *
        slabExpandedFineSourceWeight D
          (slabObservableHighSpinCoreEntropyTarget targetRepresentative)
  exact Q'.le_trans' _ _ _ hraw
    (Q'.le_of_eqv
      (Q'.mul_eqv_congr_right _ _ _ hpow))

/-- The residual-long half of one accepted-target fiber costs at most one
shifted Cartesian square. -/
theorem slabObservableHighSpinFarCoreEntropyPaidTargetResidualLongFiber_weight_le
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (cutoff half : Nat) (D : SlabPhysicalData)
    (hD : D = observableCouplingSlabPhysicalData
      w (Q'.le_of_lt hw0) cutoff half)
    (faceId : Nat) (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (floor : Nat)
    (targetRepresentative : SlabObservableHighSpinCoreCertificate
      D faceId hface (anchorPaidExteriorThreshold w)) :
    listQSum
        (fun representative =>
          listQSum slabObservableHighSpinCoreCertificateWeight
            (slabObservableHighSpinFarCoreEntropyPaidRepresentativeFiber
              (hface := hface) (radius := 32 * floor) representative))
        (slabObservableHighSpinFarCoreEntropyPaidTargetResidualLongFiber
          floor targetRepresentative) <=
      (25 * componentCoreCompletionEntropyCeiling ^ (floor + 1)) *
        slabExpandedFineSourceWeight D
          (slabObservableHighSpinCoreEntropyTarget targetRepresentative) := by
  let source :=
    slabObservableHighSpinFarCoreEntropyPaidTargetResidualLongFiber
      floor targetRepresentative
  let target := cartesian
    (List.range (slabObservableRemovalMaxSize D + 1))
    (List.range (slabObservableRemovalMaxSize D + 1))
  let sourceWeight := fun representative :
      SlabObservableHighSpinCoreCertificate
        D faceId hface (anchorPaidExteriorThreshold w) =>
    listQSum slabObservableHighSpinCoreCertificateWeight
      (slabObservableHighSpinFarCoreEntropyPaidRepresentativeFiber
        (hface := hface) (radius := 32 * floor) representative)
  let acceptedWeight := slabExpandedFineSourceWeight D
    (slabObservableHighSpinCoreEntropyTarget targetRepresentative)
  let targetWeight := fun pair : Nat × Nat =>
    ((componentCoreCompletionEntropyCeiling ^ (floor + 1) *
        componentCoreCompletionEntropyCeiling ^ pair.1) *
      componentCoreCompletionEntropyCeiling ^ pair.2) * acceptedWeight
  have haccepted : (0 : Q') <= acceptedWeight :=
    slabObservableExpandedFineSourceWeight_nonnegative D _
  have hinjection : listQSum sourceWeight source <=
      listQSum targetWeight target := by
    apply listQSum_le_of_injective source target sourceWeight targetWeight
      (slabObservableHighSpinCoreEntropyResidualShiftEncode floor)
    · exact
        slabObservableHighSpinFarCoreEntropyPaidTargetResidualLongFiber_nodup
          targetRepresentative
    · intro representative hrepresentative
      exact
        slabObservableHighSpinFarCoreEntropyPaidTargetResidualLongFiber_encode_mem
          targetRepresentative representative hrepresentative
    · intro left hleft right hright hencode
      exact
        slabObservableHighSpinFarCoreEntropyPaidTargetResidualLongFiber_encode_injective
          targetRepresentative left hleft right hright hencode
    · intro representative hrepresentative
      exact
        slabObservableHighSpinFarCoreEntropyPaidTargetResidualLongFiber_term_le
          hw0 hw1 cutoff half D hD faceId hface floor targetRepresentative
          representative hrepresentative
    · intro pair _
      exact Q'.mul_nonneg _ _
        (Q'.mul_nonneg _ _
          (Q'.mul_nonneg _ _
            (Q'.pow_nonneg componentCoreCompletionEntropyCeiling
              (by decide) (floor + 1))
            (Q'.pow_nonneg componentCoreCompletionEntropyCeiling
              (by decide) pair.1))
          (Q'.pow_nonneg componentCoreCompletionEntropyCeiling
            (by decide) pair.2))
        haccepted
  exact Q'.le_trans' _ _ _ hinjection
    (componentCoreCompletionEntropyCeiling_shiftedSquare_le
      (floor + 1) (slabObservableRemovalMaxSize D + 1)
      acceptedWeight haccepted)

/-- The complementary extra-long half obeys the same shifted-square bound. -/
theorem slabObservableHighSpinFarCoreEntropyPaidTargetExtraLongFiber_weight_le
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (cutoff half : Nat) (D : SlabPhysicalData)
    (hD : D = observableCouplingSlabPhysicalData
      w (Q'.le_of_lt hw0) cutoff half)
    (faceId : Nat) (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (floor : Nat)
    (targetRepresentative : SlabObservableHighSpinCoreCertificate
      D faceId hface (anchorPaidExteriorThreshold w)) :
    listQSum
        (fun representative =>
          listQSum slabObservableHighSpinCoreCertificateWeight
            (slabObservableHighSpinFarCoreEntropyPaidRepresentativeFiber
              (hface := hface) (radius := 32 * floor) representative))
        (slabObservableHighSpinFarCoreEntropyPaidTargetExtraLongFiber
          floor targetRepresentative) <=
      (25 * componentCoreCompletionEntropyCeiling ^ (floor + 1)) *
        slabExpandedFineSourceWeight D
          (slabObservableHighSpinCoreEntropyTarget targetRepresentative) := by
  let source := slabObservableHighSpinFarCoreEntropyPaidTargetExtraLongFiber
    floor targetRepresentative
  let target := cartesian
    (List.range (slabObservableRemovalMaxSize D + 1))
    (List.range (slabObservableRemovalMaxSize D + 1))
  let sourceWeight := fun representative :
      SlabObservableHighSpinCoreCertificate
        D faceId hface (anchorPaidExteriorThreshold w) =>
    listQSum slabObservableHighSpinCoreCertificateWeight
      (slabObservableHighSpinFarCoreEntropyPaidRepresentativeFiber
        (hface := hface) (radius := 32 * floor) representative)
  let acceptedWeight := slabExpandedFineSourceWeight D
    (slabObservableHighSpinCoreEntropyTarget targetRepresentative)
  let targetWeight := fun pair : Nat × Nat =>
    ((componentCoreCompletionEntropyCeiling ^ (floor + 1) *
        componentCoreCompletionEntropyCeiling ^ pair.1) *
      componentCoreCompletionEntropyCeiling ^ pair.2) * acceptedWeight
  have haccepted : (0 : Q') <= acceptedWeight :=
    slabObservableExpandedFineSourceWeight_nonnegative D _
  have hinjection : listQSum sourceWeight source <=
      listQSum targetWeight target := by
    apply listQSum_le_of_injective source target sourceWeight targetWeight
      (slabObservableHighSpinCoreEntropyExtraShiftEncode floor)
    · exact
        slabObservableHighSpinFarCoreEntropyPaidTargetExtraLongFiber_nodup
          targetRepresentative
    · intro representative hrepresentative
      exact
        slabObservableHighSpinFarCoreEntropyPaidTargetExtraLongFiber_encode_mem
          targetRepresentative representative hrepresentative
    · intro left hleft right hright hencode
      exact
        slabObservableHighSpinFarCoreEntropyPaidTargetExtraLongFiber_encode_injective
          targetRepresentative left hleft right hright hencode
    · intro representative hrepresentative
      exact
        slabObservableHighSpinFarCoreEntropyPaidTargetExtraLongFiber_term_le
          hw0 hw1 cutoff half D hD faceId hface floor targetRepresentative
          representative hrepresentative
    · intro pair _
      exact Q'.mul_nonneg _ _
        (Q'.mul_nonneg _ _
          (Q'.mul_nonneg _ _
            (Q'.pow_nonneg componentCoreCompletionEntropyCeiling
              (by decide) (floor + 1))
            (Q'.pow_nonneg componentCoreCompletionEntropyCeiling
              (by decide) pair.1))
          (Q'.pow_nonneg componentCoreCompletionEntropyCeiling
            (by decide) pair.2))
        haccepted
  exact Q'.le_trans' _ _ _ hinjection
    (componentCoreCompletionEntropyCeiling_shiftedSquare_le
      (floor + 1) (slabObservableRemovalMaxSize D + 1)
      acceptedWeight haccepted)

/-! ## 5. Close one target, then the whole entropy-paid far branch -/

/-- The two Boolean branches exactly partition one accepted-target fiber. -/
theorem slabObservableHighSpinFarCoreEntropyPaidTargetFiber_effective_split
    {D : SlabPhysicalData} {faceId : Nat}
    {hface : faceId ∈ slabPhysicalFaceEdges D.extent}
    {threshold : Nat} (floor : Nat)
    (targetRepresentative : SlabObservableHighSpinCoreCertificate
      D faceId hface threshold) :
    listQSum
        (fun representative =>
          listQSum slabObservableHighSpinCoreCertificateWeight
            (slabObservableHighSpinFarCoreEntropyPaidRepresentativeFiber
              (hface := hface) (radius := 32 * floor) representative))
        (slabObservableHighSpinFarCoreEntropyPaidTargetFiber
          (hface := hface) (radius := 32 * floor) targetRepresentative) ≈
      listQSum
          (fun representative =>
            listQSum slabObservableHighSpinCoreCertificateWeight
              (slabObservableHighSpinFarCoreEntropyPaidRepresentativeFiber
                (hface := hface) (radius := 32 * floor) representative))
          (slabObservableHighSpinFarCoreEntropyPaidTargetResidualLongFiber
            floor targetRepresentative) +
        listQSum
          (fun representative =>
            listQSum slabObservableHighSpinCoreCertificateWeight
              (slabObservableHighSpinFarCoreEntropyPaidRepresentativeFiber
                (hface := hface) (radius := 32 * floor) representative))
          (slabObservableHighSpinFarCoreEntropyPaidTargetExtraLongFiber
            floor targetRepresentative) := by
  unfold slabObservableHighSpinFarCoreEntropyPaidTargetResidualLongFiber
    slabObservableHighSpinFarCoreEntropyPaidTargetExtraLongFiber
  exact listQSum_filter_partition _
    (slabObservableHighSpinCoreEntropyResidualLongTest floor) _

/-- One accepted target absorbs every entropy-paid rich representative above
radius `32 * floor`, with the explicit two-branch constant `50`. -/
theorem slabObservableHighSpinFarCoreEntropyPaidTargetFiber_weight_le
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (cutoff half : Nat) (D : SlabPhysicalData)
    (hD : D = observableCouplingSlabPhysicalData
      w (Q'.le_of_lt hw0) cutoff half)
    (faceId : Nat) (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (floor : Nat)
    (targetRepresentative : SlabObservableHighSpinCoreCertificate
      D faceId hface (anchorPaidExteriorThreshold w)) :
    listQSum
        (fun representative =>
          listQSum slabObservableHighSpinCoreCertificateWeight
            (slabObservableHighSpinFarCoreEntropyPaidRepresentativeFiber
              (hface := hface) (radius := 32 * floor) representative))
        (slabObservableHighSpinFarCoreEntropyPaidTargetFiber
          (hface := hface) (radius := 32 * floor) targetRepresentative) <=
      (50 * componentCoreCompletionEntropyCeiling ^ (floor + 1)) *
        slabExpandedFineSourceWeight D
          (slabObservableHighSpinCoreEntropyTarget targetRepresentative) := by
  have hsplit :=
    slabObservableHighSpinFarCoreEntropyPaidTargetFiber_effective_split
      floor targetRepresentative
  have hresidual :=
    slabObservableHighSpinFarCoreEntropyPaidTargetResidualLongFiber_weight_le
      hw0 hw1 cutoff half D hD faceId hface floor targetRepresentative
  have hextra :=
    slabObservableHighSpinFarCoreEntropyPaidTargetExtraLongFiber_weight_le
      hw0 hw1 cutoff half D hD faceId hface floor targetRepresentative
  have hadd := Q'.add_le_add hresidual hextra
  have htwice :
      (25 * componentCoreCompletionEntropyCeiling ^ (floor + 1)) *
            slabExpandedFineSourceWeight D
              (slabObservableHighSpinCoreEntropyTarget targetRepresentative) +
          (25 * componentCoreCompletionEntropyCeiling ^ (floor + 1)) *
            slabExpandedFineSourceWeight D
              (slabObservableHighSpinCoreEntropyTarget targetRepresentative) ≈
        (50 * componentCoreCompletionEntropyCeiling ^ (floor + 1)) *
          slabExpandedFineSourceWeight D
            (slabObservableHighSpinCoreEntropyTarget targetRepresentative) := by
    refine Q'.eqv_trans _
      ((25 * componentCoreCompletionEntropyCeiling ^ (floor + 1) +
          25 * componentCoreCompletionEntropyCeiling ^ (floor + 1)) *
        slabExpandedFineSourceWeight D
          (slabObservableHighSpinCoreEntropyTarget targetRepresentative)) _
      (Q'.eqv_symm (Q'.add_mul_eqv _ _ _)) ?_
    refine Q'.mul_eqv_congr_right _ _ _ ?_
    refine Q'.eqv_trans _
      ((25 + 25) * componentCoreCompletionEntropyCeiling ^ (floor + 1)) _
      (Q'.eqv_symm (Q'.add_mul_eqv _ _ _)) ?_
    exact Q'.mul_eqv_congr_right _ _ _ (by decide)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hsplit)
    (Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv htwice))

private theorem listQSum_mono_local {A : Type} (lower upper : A -> Q') :
    forall (items : List A),
      (forall item, item ∈ items -> lower item <= upper item) ->
      listQSum lower items <= listQSum upper items
  | [], _ => Q'.le_refl' 0
  | head :: tail, hterm => by
      exact Q'.add_le_add
        (hterm head List.mem_cons_self)
        (listQSum_mono_local lower upper tail
          (fun item hitem => hterm item (List.mem_cons_of_mem head hitem)))

/-- **Volume-free entropy-paid far-core tail.**  After all inverse codes,
rich keys, effective coordinate pairs, and accepted targets have been summed,
the complete entropy-paid branch at radius `32 * floor` costs at most
`50 * (4/5)^(floor+1)` times the physical partition. -/
theorem slabObservableHighSpinFarCoreEntropyPaidCertificates_weight_le_partition
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (cutoff half : Nat) (D : SlabPhysicalData)
    (hD : D = observableCouplingSlabPhysicalData
      w (Q'.le_of_lt hw0) cutoff half)
    (faceId : Nat) (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (floor : Nat) :
    listQSum slabObservableHighSpinCoreCertificateWeight
        (slabObservableHighSpinFarCoreEntropyPaidCertificates
          D faceId hface (anchorPaidExteriorThreshold w) (32 * floor)) <=
      (50 * componentCoreCompletionEntropyCeiling ^ (floor + 1)) *
        D.physicalPartition := by
  let representatives :=
    slabObservableHighSpinFarCoreEntropyPaidTargetRepresentatives
      D faceId hface (anchorPaidExteriorThreshold w) (32 * floor)
  let sourceWeight := fun targetRepresentative :
      SlabObservableHighSpinCoreCertificate
        D faceId hface (anchorPaidExteriorThreshold w) =>
    listQSum
      (fun representative =>
        listQSum slabObservableHighSpinCoreCertificateWeight
          (slabObservableHighSpinFarCoreEntropyPaidRepresentativeFiber
            (hface := hface) (radius := 32 * floor) representative))
      (slabObservableHighSpinFarCoreEntropyPaidTargetFiber
        (hface := hface) (radius := 32 * floor) targetRepresentative)
  let factor := 50 *
    componentCoreCompletionEntropyCeiling ^ (floor + 1)
  let targetWeight := fun targetRepresentative :
      SlabObservableHighSpinCoreCertificate
        D faceId hface (anchorPaidExteriorThreshold w) =>
    slabExpandedFineSourceWeight D
      (slabObservableHighSpinCoreEntropyTarget targetRepresentative)
  have htotal :=
    slabObservableHighSpinFarCoreEntropyPaidTargetFibers_weight_total
      D faceId hface (anchorPaidExteriorThreshold w) (32 * floor)
  have hpoint : forall targetRepresentative,
      targetRepresentative ∈ representatives ->
      sourceWeight targetRepresentative <= factor *
        targetWeight targetRepresentative := by
    intro targetRepresentative _
    exact
      slabObservableHighSpinFarCoreEntropyPaidTargetFiber_weight_le
        hw0 hw1 cutoff half D hD faceId hface floor targetRepresentative
  have hmono : listQSum sourceWeight representatives <=
      listQSum (fun targetRepresentative =>
        factor * targetWeight targetRepresentative) representatives :=
    listQSum_mono_local _ _ _ hpoint
  have hfactor := listQSum_mul_left_local
    factor targetWeight representatives
  have htargets :=
    slabObservableHighSpinFarCoreEntropyPaidTargetRepresentatives_weight_le_partition
      D faceId hface (anchorPaidExteriorThreshold w) (32 * floor)
  have hfactorNonnegative : (0 : Q') <= factor :=
    Q'.mul_nonneg _ _ (by decide)
      (Q'.pow_nonneg componentCoreCompletionEntropyCeiling
        (by decide) (floor + 1))
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ _
    htargets hfactorNonnegative
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_symm htotal))
    (Q'.le_trans' _ _ _ hmono
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hfactor) hscaled))

#print axioms componentCoreCompletionEntropyCeiling_fullTail_le
#print axioms componentCoreCompletionEntropyCeiling_shiftedSquare_le
#print axioms slabObservableHighSpinFarCoreEntropyPaidRepresentative_effectivePair_floor
#print axioms slabObservableHighSpinCoreEntropyResidualLongTest
#print axioms slabObservableHighSpinFarCoreEntropyPaidTargetResidualLongFiber
#print axioms slabObservableHighSpinFarCoreEntropyPaidTargetExtraLongFiber
#print axioms slabObservableHighSpinCoreEntropyResidualShiftEncode
#print axioms slabObservableHighSpinCoreEntropyExtraShiftEncode
#print axioms slabObservableHighSpinFarCoreEntropyPaidTargetResidualLongFiber_weight_le
#print axioms slabObservableHighSpinFarCoreEntropyPaidTargetExtraLongFiber_weight_le
#print axioms slabObservableHighSpinFarCoreEntropyPaidTargetFiber_effective_split
#print axioms slabObservableHighSpinFarCoreEntropyPaidTargetFiber_weight_le
#print axioms slabObservableHighSpinFarCoreEntropyPaidCertificates_weight_le_partition

end YMGap.Continuum.CompactDualSlabObservableHighSpinCoreEntropyTargetTail
