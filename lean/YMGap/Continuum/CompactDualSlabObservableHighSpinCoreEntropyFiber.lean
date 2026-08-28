/-
# Fixed accepted-target fibers of the entropy-paid far core

The pointwise core-completion theorem lands every source on its actual
accepted complete-removal target with coefficient

```text
anchorFaceCoefficient ^ paid * 2 ^ residual.
```

To sum this estimate without losing either rate, this module groups the
literal entropy-paid far certificates by the exact finite key

```text
(accepted target, paid length, residual length).
```

Within one such fiber the existing adaptive entropy code is injective on
source entries and lies in the carrier of size
`componentAdaptiveEntropyBase ^ (paid + residual)`.  The resulting exact
fixed-fiber estimate is

```text
fiber weight
  <= (8/25)^paid * 20480000^residual * accepted target weight.
```

This is the fixed-target summation compiler.  Summing its strict rates over
the distinct realized length pairs is a subsequent theorem.

Constructive contract: realized finite keys, explicit list injections, and
exact rational algebra only.  No `Classical.*`, choice, `native_decide`,
`sorry`, custom axiom, noncomputable declaration, or enlarged heartbeat
budget.
-/

import YMGap.Continuum.CompactDualSlabObservableHighSpinCoreEntropySplit
import YMGap.Continuum.FiniteKeyRepresentativePartition

namespace YMGap.Continuum.CompactDualSlabObservableHighSpinCoreEntropyFiber

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.SU3CharFactor
open YMGap.Continuum.BF4SU2FineIntertwinerPhysicalDisintegration
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabExpandedTargetKey
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveEntropyCarrier
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveFiberWeight
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveInverseFiber
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAssignment
open YMGap.Continuum.CompactDualSlabFaceStrandComponentCoreCompletionWeight
open YMGap.Continuum.CompactDualSlabFaceStrandComponentHighSpinCoreSplitWeight
open YMGap.Continuum.CompactDualSlabFaceStrandComponentWeight
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabHighSpinFacePeelWeight
open YMGap.Continuum.CompactDualSlabObservableHighSpinCoreCarrier
open YMGap.Continuum.CompactDualSlabObservableHighSpinCoreEntropySplit
open YMGap.Continuum.CompactDualSlabObservableHighSpinCoreFarSplit
open YMGap.Continuum.CompactDualSlabObservableHighSpinCoreGeometry
open YMGap.Continuum.CompactDualSlabObservableHighSpinExteriorContraction
open YMGap.Continuum.CompactDualSlabObservableHighSpinExteriorPartition
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteKeyRepresentativePartition
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.PartitionUpperBound
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The exact target/two-length key -/

/-- Actual accepted complete-removal target of one core certificate. -/
def slabObservableHighSpinCoreEntropyTarget
    {D : SlabPhysicalData} {faceId : Nat}
    {hface : faceId ∈ slabPhysicalFaceEdges D.extent}
    {threshold : Nat}
    (certificate : SlabObservableHighSpinCoreCertificate
      D faceId hface threshold) :
    SlabLabelling × SlabFusionWitnessAssignment :=
  slabObservableHighSpinExteriorTarget hface certificate.sourceEntry

/-- Decidable data on which both the accepted target and pointwise two-rate
coefficient are constant. -/
structure SlabObservableHighSpinCoreEntropyKey : Type where
  targetKey : SlabExpandedFineTargetKey
  paidLength : Nat
  residualLength : Nat
  deriving DecidableEq

/-- Rich entropy key of a positive observable source entry. -/
def slabObservableHighSpinCoreEntropySourceKey
    {D : SlabPhysicalData} {faceId : Nat}
    (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (threshold : Nat)
    (entry : SlabObservablePositiveSourceEntry D faceId) :
    SlabObservableHighSpinCoreEntropyKey :=
  { targetKey := slabExpandedFineTargetKey D
      (slabObservableHighSpinExteriorTarget hface entry).1
      (slabObservableHighSpinExteriorTarget hface entry).2
    paidLength :=
      (SlabFusionWitnessFaceStrandSeed.exteriorPeelFaces
        (entry.seed D faceId hface) threshold).length
    residualLength :=
      (SlabFusionWitnessFaceStrandSeed.coreResidualFaces
        (entry.seed D faceId hface) threshold).length }

/-- Rich entropy key specialized to a decoded core certificate. -/
def slabObservableHighSpinCoreEntropyKey
    {D : SlabPhysicalData} {faceId : Nat}
    {hface : faceId ∈ slabPhysicalFaceEdges D.extent}
    {threshold : Nat}
    (certificate : SlabObservableHighSpinCoreCertificate
      D faceId hface threshold) :
    SlabObservableHighSpinCoreEntropyKey :=
  slabObservableHighSpinCoreEntropySourceKey
    hface threshold certificate.sourceEntry

/-- One realized rich-key representative of every entropy-paid far source. -/
def slabObservableHighSpinFarCoreEntropyPaidRepresentatives
    (D : SlabPhysicalData) (faceId : Nat)
    (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (threshold radius : Nat) :
    List (SlabObservableHighSpinCoreCertificate
      D faceId hface threshold) :=
  keyRepresentatives slabObservableHighSpinCoreEntropyKey
    (slabObservableHighSpinFarCoreEntropyPaidCertificates
      D faceId hface threshold radius)

/-- Literal entropy-paid certificates with the same accepted target and the
same two lengths as one realized representative. -/
def slabObservableHighSpinFarCoreEntropyPaidRepresentativeFiber
    {D : SlabPhysicalData} {faceId : Nat}
    {hface : faceId ∈ slabPhysicalFaceEdges D.extent}
    {threshold radius : Nat}
    (representative : SlabObservableHighSpinCoreCertificate
      D faceId hface threshold) :
    List (SlabObservableHighSpinCoreCertificate
      D faceId hface threshold) :=
  representativeFiber
    (slabObservableHighSpinFarCoreEntropyPaidCertificates
      D faceId hface threshold radius)
    slabObservableHighSpinCoreEntropyKey representative

/-- Membership in one rich-key fiber gives exact equality of all its key
data. -/
theorem slabObservableHighSpinFarCoreEntropyPaidRepresentativeFiber_key_eq
    {D : SlabPhysicalData} {faceId : Nat}
    {hface : faceId ∈ slabPhysicalFaceEdges D.extent}
    {threshold radius : Nat}
    (representative certificate : SlabObservableHighSpinCoreCertificate
      D faceId hface threshold)
    (hcertificate : certificate ∈
      slabObservableHighSpinFarCoreEntropyPaidRepresentativeFiber
        (hface := hface) (radius := radius) representative) :
    slabObservableHighSpinCoreEntropyKey representative =
      slabObservableHighSpinCoreEntropyKey certificate :=
  of_decide_eq_true (List.mem_filter.mp hcertificate).2

/-- Equality of rich keys recovers equality of the actual accepted targets. -/
theorem slabObservableHighSpinCoreEntropyTarget_eq_of_key_eq
    {D : SlabPhysicalData} {faceId : Nat}
    {hface : faceId ∈ slabPhysicalFaceEdges D.extent}
    {threshold : Nat}
    (left right : SlabObservableHighSpinCoreCertificate
      D faceId hface threshold)
    (hkey : slabObservableHighSpinCoreEntropyKey left =
      slabObservableHighSpinCoreEntropyKey right) :
    slabObservableHighSpinCoreEntropyTarget left =
      slabObservableHighSpinCoreEntropyTarget right := by
  apply slabExpandedFineTargetKey_eq_source_eq D
  · exact slabObservableHighSpinExteriorTarget_mem left.sourceEntry
  · exact slabObservableHighSpinExteriorTarget_mem right.sourceEntry
  · exact congrArg SlabObservableHighSpinCoreEntropyKey.targetKey hkey

/-! ## 2. The adaptive code counts every rich-key fiber -/

private theorem nodup_of_map_nodup {A B : Type} (map : A -> B) :
    forall {items : List A}, (items.map map).Nodup -> items.Nodup
  | [], _ => List.nodup_nil
  | head :: tail, hnodup => by
      have hparts := List.nodup_cons.mp hnodup
      apply List.nodup_cons.mpr
      refine ⟨?_, nodup_of_map_nodup map hparts.2⟩
      intro hmem
      exact hparts.1 (List.mem_map.mpr ⟨head, hmem, rfl⟩)

/-- The full canonical core-certificate presentation has no duplicate source
entries. -/
theorem slabObservableHighSpinCoreCertificates_sourceEntries_nodup
    (D : SlabPhysicalData) (faceId : Nat)
    (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (threshold : Nat) :
    ((slabObservableHighSpinCoreCertificates
        D faceId hface threshold).map
      (fun certificate => certificate.sourceEntry)).Nodup := by
  rw [slabObservableHighSpinCoreCertificates_sourceEntries_eq]
  unfold slabObservableHighSpinCoreEntries
  exact (attach_nodup_of_nodup _
    (slabObservablePositiveExpandedSources_nodup D faceId)).filter _

/-- Source entries in one rich-key fiber remain duplicate-free. -/
theorem slabObservableHighSpinFarCoreEntropyPaidRepresentativeFiber_sourceEntries_nodup
    {D : SlabPhysicalData} {faceId : Nat}
    {hface : faceId ∈ slabPhysicalFaceEdges D.extent}
    {threshold radius : Nat}
    (representative : SlabObservableHighSpinCoreCertificate
      D faceId hface threshold) :
    ((slabObservableHighSpinFarCoreEntropyPaidRepresentativeFiber
        (hface := hface) (radius := radius) representative).map
      (fun certificate => certificate.sourceEntry)).Nodup := by
  have hfiber :
      List.Sublist
        (slabObservableHighSpinFarCoreEntropyPaidRepresentativeFiber
          (hface := hface) (radius := radius) representative)
        (slabObservableHighSpinFarCoreEntropyPaidCertificates
          D faceId hface threshold radius) :=
    List.filter_sublist
  have hpaid :
      List.Sublist
        (slabObservableHighSpinFarCoreEntropyPaidCertificates
          D faceId hface threshold radius)
        (slabObservableHighSpinFarCoreCertificates
          D faceId hface threshold radius) :=
    List.filter_sublist
  have hfar :
      List.Sublist
        (slabObservableHighSpinFarCoreCertificates
          D faceId hface threshold radius)
        (slabObservableHighSpinCoreCertificates
          D faceId hface threshold) :=
    List.filter_sublist
  have hpaidFar := hpaid.trans hfar
  have hall := hfiber.trans hpaidFar
  have hmapped := hall.map
    (fun certificate => certificate.sourceEntry)
  exact hmapped.nodup
    (slabObservableHighSpinCoreCertificates_sourceEntries_nodup
      D faceId hface threshold)

/-- Adaptive entropy code of one literal positive source entry. -/
def slabObservableHighSpinCoreEntropySourceCode
    {D : SlabPhysicalData} {faceId : Nat}
    (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (entry : SlabObservablePositiveSourceEntry D faceId) :
    ComponentAdaptiveEntropyCode :=
  componentAdaptiveEntropyCode (entry.seed D faceId hface)

/-- Equal adaptive codes on one rich-key fiber recover equal source entries. -/
theorem slabObservableHighSpinCoreEntropySourceEntry_eq_of_code_eq
    {D : SlabPhysicalData} {faceId : Nat}
    {hface : faceId ∈ slabPhysicalFaceEdges D.extent}
    {threshold radius : Nat}
    (representative left right : SlabObservableHighSpinCoreCertificate
      D faceId hface threshold)
    (hleft : left ∈
      slabObservableHighSpinFarCoreEntropyPaidRepresentativeFiber
        (hface := hface) (radius := radius) representative)
    (hright : right ∈
      slabObservableHighSpinFarCoreEntropyPaidRepresentativeFiber
        (hface := hface) (radius := radius) representative)
    (hcode : slabObservableHighSpinCoreEntropySourceCode
        hface left.sourceEntry =
      slabObservableHighSpinCoreEntropySourceCode
        hface right.sourceEntry) :
    left.sourceEntry = right.sourceEntry := by
  have hleftKey :=
    slabObservableHighSpinFarCoreEntropyPaidRepresentativeFiber_key_eq
      representative left hleft
  have hrightKey :=
    slabObservableHighSpinFarCoreEntropyPaidRepresentativeFiber_key_eq
      representative right hright
  have hkey : slabObservableHighSpinCoreEntropyKey left =
      slabObservableHighSpinCoreEntropyKey right :=
    hleftKey.symm.trans hrightKey
  have htarget := slabObservableHighSpinCoreEntropyTarget_eq_of_key_eq
    left right hkey
  have hsourceData := componentAdaptiveEntropyCode_eq_sourceData_eq
    (left.sourceEntry.seed D faceId hface)
    (right.sourceEntry.seed D faceId hface)
    (by simp [SlabObservablePositiveSourceEntry.seed])
    (congrArg Prod.fst htarget) (congrArg Prod.snd htarget) hcode
  exact Subtype.ext (Prod.ext hsourceData.1 hsourceData.2)

/-- The source-entry adaptive codes in one rich-key fiber are duplicate-free. -/
theorem slabObservableHighSpinFarCoreEntropyPaidRepresentativeFiber_codes_nodup
    {D : SlabPhysicalData} {faceId : Nat}
    {hface : faceId ∈ slabPhysicalFaceEdges D.extent}
    {threshold radius : Nat}
    (representative : SlabObservableHighSpinCoreCertificate
      D faceId hface threshold) :
    (((slabObservableHighSpinFarCoreEntropyPaidRepresentativeFiber
          (hface := hface) (radius := radius) representative).map
        (fun certificate => certificate.sourceEntry)).map
      (slabObservableHighSpinCoreEntropySourceCode hface)).Nodup := by
  let certificates :=
    slabObservableHighSpinFarCoreEntropyPaidRepresentativeFiber
      (hface := hface) (radius := radius) representative
  let entries := certificates.map
    (fun certificate => certificate.sourceEntry)
  apply nodup_map_of_injOn
    (slabObservableHighSpinCoreEntropySourceCode hface) entries
    (slabObservableHighSpinFarCoreEntropyPaidRepresentativeFiber_sourceEntries_nodup
      representative)
  intro leftEntry hleftEntry rightEntry hrightEntry hcode
  obtain ⟨left, hleft, rfl⟩ := List.mem_map.mp hleftEntry
  obtain ⟨right, hright, rfl⟩ := List.mem_map.mp hrightEntry
  exact slabObservableHighSpinCoreEntropySourceEntry_eq_of_code_eq
    representative left right hleft hright hcode

/-- One rich-key fiber has at most one adaptive entropy carrier at the sum of
its two representative lengths. -/
theorem slabObservableHighSpinFarCoreEntropyPaidRepresentativeFiber_length_le
    {D : SlabPhysicalData} {faceId : Nat}
    {hface : faceId ∈ slabPhysicalFaceEdges D.extent}
    {threshold radius : Nat}
    (representative : SlabObservableHighSpinCoreCertificate
      D faceId hface threshold) :
    (slabObservableHighSpinFarCoreEntropyPaidRepresentativeFiber
        (hface := hface) (radius := radius) representative).length <=
      componentAdaptiveEntropyBase ^
        (slabObservableHighSpinCoreCertificatePaidLength representative +
          slabObservableHighSpinCoreCertificateResidualLength
            representative) := by
  let certificates :=
    slabObservableHighSpinFarCoreEntropyPaidRepresentativeFiber
      (hface := hface) (radius := radius) representative
  let entries := certificates.map
    (fun certificate => certificate.sourceEntry)
  let codes := entries.map
    (slabObservableHighSpinCoreEntropySourceCode hface)
  have hsubset : forall code, code ∈ codes ->
      code ∈ componentAdaptiveEntropyCarrier D.extent faceId
        (slabObservableHighSpinCoreCertificatePaidLength representative +
          slabObservableHighSpinCoreCertificateResidualLength
            representative) := by
    intro code hcode
    obtain ⟨entry, hentry, rfl⟩ := List.mem_map.mp hcode
    obtain ⟨certificate, hcertificate, rfl⟩ := List.mem_map.mp hentry
    have hkey :=
      slabObservableHighSpinFarCoreEntropyPaidRepresentativeFiber_key_eq
        representative certificate hcertificate
    have hpaid := congrArg
      SlabObservableHighSpinCoreEntropyKey.paidLength hkey
    have hresidual := congrArg
      SlabObservableHighSpinCoreEntropyKey.residualLength hkey
    change
      (SlabFusionWitnessFaceStrandSeed.exteriorPeelFaces
          (representative.sourceEntry.seed D faceId hface)
          threshold).length =
        (SlabFusionWitnessFaceStrandSeed.exteriorPeelFaces
          (certificate.sourceEntry.seed D faceId hface)
          threshold).length at hpaid
    change
      (SlabFusionWitnessFaceStrandSeed.coreResidualFaces
          (representative.sourceEntry.seed D faceId hface)
          threshold).length =
        (SlabFusionWitnessFaceStrandSeed.coreResidualFaces
          (certificate.sourceEntry.seed D faceId hface)
          threshold).length at hresidual
    have hmem := componentAdaptiveEntropyCode_mem_carrier
      (certificate.sourceEntry.seed D faceId hface)
    have hsplit :=
      slabObservableHighSpinCoreCertificate_peel_length_split certificate
    change slabObservableHighSpinCoreEntropySourceCode
        hface certificate.sourceEntry ∈
      componentAdaptiveEntropyCarrier D.extent faceId
        (SlabFusionWitnessFaceStrandSeed.peelFaces
          (certificate.sourceEntry.seed D faceId hface)).length at hmem
    rw [hsplit, ← hpaid, ← hresidual] at hmem
    exact hmem
  have hbound := nodup_subset_length_le codes
    (componentAdaptiveEntropyCarrier D.extent faceId
      (slabObservableHighSpinCoreCertificatePaidLength representative +
        slabObservableHighSpinCoreCertificateResidualLength representative))
    (slabObservableHighSpinFarCoreEntropyPaidRepresentativeFiber_codes_nodup
      representative) hsubset
  calc
    certificates.length = entries.length := (List.length_map _).symm
    _ = codes.length := (List.length_map _).symm
    _ <= (componentAdaptiveEntropyCarrier D.extent faceId
          (slabObservableHighSpinCoreCertificatePaidLength representative +
            slabObservableHighSpinCoreCertificateResidualLength
              representative)).length := hbound
    _ <= componentAdaptiveEntropyBase ^
          (slabObservableHighSpinCoreCertificatePaidLength representative +
            slabObservableHighSpinCoreCertificateResidualLength
              representative) :=
      componentAdaptiveEntropyCarrier_length_le _ _ _

/-! ## 3. Counted two-rate fixed-fiber weight -/

/-- The raw coefficient after applying the exact inverse-fiber cardinality
to the two-rate pointwise estimate. -/
def componentCoreCompletionCountedRate (paid residual : Nat) : Q' :=
  Q'.ofNat (componentAdaptiveEntropyBase ^ (paid + residual)) *
    (anchorFaceCoefficient ^ paid * (Q'.ofNat 2) ^ residual)

private theorem pow_eqv_congr_local {left right : Q'}
    (h : left ≈ right) : forall exponent : Nat,
    left ^ exponent ≈ right ^ exponent
  | 0 => Q'.eqv_refl 1
  | exponent + 1 =>
      Q'.eqv_trans _ (right * left ^ exponent) _
        (Q'.mul_eqv_congr_right left right (left ^ exponent) h)
        (Q'.mul_eqv_congr_left right (left ^ exponent)
          (right ^ exponent) (pow_eqv_congr_local h exponent))

/-- Exact normalization of the counted coefficient into its paid and
residual entropy rates. -/
theorem componentCoreCompletionCountedRate_eqv
    (paid residual : Nat) :
    componentCoreCompletionCountedRate paid residual ≈
      componentAdaptiveEntropyAnchorRatio ^ paid *
        componentCoreCompletionResidualEntropyFactor ^ residual := by
  unfold componentCoreCompletionCountedRate
    componentAdaptiveEntropyAnchorRatio
    componentCoreCompletionResidualEntropyFactor
  rw [Nat.pow_add]
  refine Q'.eqv_trans _
    ((Q'.ofNat (componentAdaptiveEntropyBase ^ paid) *
        Q'.ofNat (componentAdaptiveEntropyBase ^ residual)) *
      (anchorFaceCoefficient ^ paid * (Q'.ofNat 2) ^ residual)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _
      (ofNat_mul_eqv
        (componentAdaptiveEntropyBase ^ paid)
        (componentAdaptiveEntropyBase ^ residual))
  refine Q'.eqv_trans _
    ((Q'.ofNat (componentAdaptiveEntropyBase ^ paid) *
        anchorFaceCoefficient ^ paid) *
      (Q'.ofNat (componentAdaptiveEntropyBase ^ residual) *
        (Q'.ofNat 2) ^ residual)) _ ?_ ?_
  · exact mul_four_mid'
      (Q'.ofNat (componentAdaptiveEntropyBase ^ paid))
      (Q'.ofNat (componentAdaptiveEntropyBase ^ residual))
      (anchorFaceCoefficient ^ paid) ((Q'.ofNat 2) ^ residual)
  refine Q'.eqv_trans _
    (componentAdaptiveEntropyAnchorRatio ^ paid *
      (Q'.ofNat (componentAdaptiveEntropyBase ^ residual) *
        (Q'.ofNat 2) ^ residual)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _
      (ofNat_pow_mul componentAdaptiveEntropyBase
        anchorFaceCoefficient paid)
  refine Q'.eqv_trans _
    (componentAdaptiveEntropyAnchorRatio ^ paid *
      (Q'.ofNat componentAdaptiveEntropyBase * Q'.ofNat 2) ^ residual) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left _ _ _
      (ofNat_pow_mul componentAdaptiveEntropyBase (Q'.ofNat 2) residual)
  · exact Q'.mul_eqv_congr_left _ _ _
      (pow_eqv_congr_local
        (Q'.eqv_trans _
          (Q'.ofNat (componentAdaptiveEntropyBase * 2)) _
          (Q'.eqv_symm
            (ofNat_mul_eqv componentAdaptiveEntropyBase 2))
          (Q'.eqv_of_eq (congrArg Q'.ofNat (Nat.mul_comm _ _))))
        residual)

private theorem listQSum_le_fixed_cardinality_coefficient
    {A : Type} (items : List A) (weight : A -> Q')
    (cardinality : Nat) (coefficient targetWeight : Q')
    (hcardinality : items.length <= cardinality)
    (hcoefficient : (0 : Q') <= coefficient)
    (htarget : (0 : Q') <= targetWeight)
    (hpointwise : forall item, item ∈ items ->
      weight item <= coefficient * targetWeight) :
    listQSum weight items <=
      (Q'.ofNat cardinality * coefficient) * targetWeight := by
  have hbound : (0 : Q') <= coefficient * targetWeight :=
    Q'.mul_nonneg _ _ hcoefficient htarget
  have hsum := listQSum_le_length_mul weight hbound items hpointwise
  have hcardinalityQ :
      Q'.ofNat items.length <= Q'.ofNat cardinality :=
    Q'.ofNat_le_ofNat hcardinality
  have hscale := Q'.mul_le_mul_of_nonneg_right _ _ _
    hcardinalityQ hbound
  exact Q'.le_trans' _ _ _ hsum
    (Q'.le_trans' _ _ _ hscale
      (Q'.le_of_eqv
        (Q'.eqv_symm
          (Q'.mul_assoc_eqv
            (Q'.ofNat cardinality) coefficient targetWeight))))

/-- **Fixed accepted-target entropy-paid fiber estimate.**  The literal
source mass in one rich-key fiber is bounded by the exact entropy-adjusted
two-rate coefficient times the representative's accepted target weight. -/
theorem slabObservableHighSpinFarCoreEntropyPaidRepresentativeFiber_weight_le
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (cutoff half : Nat) (D : SlabPhysicalData)
    (hD : D = observableCouplingSlabPhysicalData
      w (Q'.le_of_lt hw0) cutoff half)
    (faceId : Nat) (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (radius : Nat)
    (representative : SlabObservableHighSpinCoreCertificate
      D faceId hface (anchorPaidExteriorThreshold w)) :
    listQSum slabObservableHighSpinCoreCertificateWeight
        (slabObservableHighSpinFarCoreEntropyPaidRepresentativeFiber
          (hface := hface) (radius := radius) representative) <=
      (componentAdaptiveEntropyAnchorRatio ^
          slabObservableHighSpinCoreCertificatePaidLength representative *
        componentCoreCompletionResidualEntropyFactor ^
          slabObservableHighSpinCoreCertificateResidualLength
            representative) *
        slabExpandedFineSourceWeight D
          (slabObservableHighSpinCoreEntropyTarget representative) := by
  subst D
  let certificates :=
    slabObservableHighSpinFarCoreEntropyPaidRepresentativeFiber
      (hface := hface) (radius := radius) representative
  let paid := slabObservableHighSpinCoreCertificatePaidLength representative
  let residual :=
    slabObservableHighSpinCoreCertificateResidualLength representative
  let targetWeight := slabExpandedFineSourceWeight
    (observableCouplingSlabPhysicalData
      w (Q'.le_of_lt hw0) cutoff half)
    (slabObservableHighSpinCoreEntropyTarget representative)
  have hraw := listQSum_le_fixed_cardinality_coefficient
    certificates slabObservableHighSpinCoreCertificateWeight
    (componentAdaptiveEntropyBase ^ (paid + residual))
    (anchorFaceCoefficient ^ paid * (Q'.ofNat 2) ^ residual)
    targetWeight
    (slabObservableHighSpinFarCoreEntropyPaidRepresentativeFiber_length_le
      representative)
    (Q'.mul_nonneg _ _
      (Q'.pow_nonneg anchorFaceCoefficient (by decide) paid)
      (Q'.pow_nonneg (Q'.ofNat 2) (by decide) residual))
    (slabObservableExpandedFineSourceWeight_nonnegative
      (observableCouplingSlabPhysicalData
        w (Q'.le_of_lt hw0) cutoff half)
      (slabObservableHighSpinCoreEntropyTarget representative))
    (fun certificate hcertificate => by
      have hkey :=
        slabObservableHighSpinFarCoreEntropyPaidRepresentativeFiber_key_eq
          representative certificate hcertificate
      have hpaid := congrArg
        SlabObservableHighSpinCoreEntropyKey.paidLength hkey
      have hresidual := congrArg
        SlabObservableHighSpinCoreEntropyKey.residualLength hkey
      have htarget :=
        slabObservableHighSpinCoreEntropyTarget_eq_of_key_eq
          representative certificate hkey
      have hweight := expandedFiberWeight_coreCompleted_le
        hw0 hw1 cutoff half
        (certificate.sourceEntry.seed
          (observableCouplingSlabPhysicalData
            w (Q'.le_of_lt hw0) cutoff half)
          faceId hface)
        (slabObservableHighSpinExteriorEntry_bounded
          certificate.sourceEntry)
      dsimp only at hweight
      change
        slabObservableHighSpinCoreCertificatePaidLength representative =
          slabObservableHighSpinCoreCertificatePaidLength certificate at hpaid
      change
        slabObservableHighSpinCoreCertificateResidualLength representative =
          slabObservableHighSpinCoreCertificateResidualLength certificate
        at hresidual
      change
        slabExpandedFineSourceWeight
            (observableCouplingSlabPhysicalData
              w (Q'.le_of_lt hw0) cutoff half)
            certificate.sourceEntry.1 <=
          (anchorFaceCoefficient ^
              slabObservableHighSpinCoreCertificatePaidLength certificate *
            (Q'.ofNat 2) ^
              slabObservableHighSpinCoreCertificateResidualLength
                certificate) *
            slabExpandedFineSourceWeight
              (observableCouplingSlabPhysicalData
                w (Q'.le_of_lt hw0) cutoff half)
              (slabObservableHighSpinCoreEntropyTarget certificate) at hweight
      rw [← hpaid, ← hresidual, ← htarget] at hweight
      simpa only [slabObservableHighSpinCoreCertificateWeight,
        paid, residual, targetWeight] using hweight)
  have hrate := componentCoreCompletionCountedRate_eqv paid residual
  exact Q'.le_trans' _ _ _ hraw
    (Q'.le_of_eqv
      (Q'.mul_eqv_congr_right _ _ targetWeight hrate))

/-! ## 4. Exact rich-fiber partition -/

/-- Rich-key representative fibers recover the complete entropy-paid far
mass exactly. -/
theorem slabObservableHighSpinFarCoreEntropyPaidRepresentativeFibers_weight_total
    (D : SlabPhysicalData) (faceId : Nat)
    (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (threshold radius : Nat) :
    listQSum
        (fun representative =>
          listQSum slabObservableHighSpinCoreCertificateWeight
            (slabObservableHighSpinFarCoreEntropyPaidRepresentativeFiber
              (hface := hface) (radius := radius) representative))
        (slabObservableHighSpinFarCoreEntropyPaidRepresentatives
          D faceId hface threshold radius) ≈
      listQSum slabObservableHighSpinCoreCertificateWeight
        (slabObservableHighSpinFarCoreEntropyPaidCertificates
          D faceId hface threshold radius) := by
  exact keyRepresentativeFibers_weight_total
    (slabObservableHighSpinFarCoreEntropyPaidCertificates
      D faceId hface threshold radius)
    slabObservableHighSpinCoreCertificateWeight
    slabObservableHighSpinCoreEntropyKey

#print axioms slabObservableHighSpinCoreEntropyTarget
#print axioms SlabObservableHighSpinCoreEntropyKey
#print axioms slabObservableHighSpinCoreEntropySourceKey
#print axioms slabObservableHighSpinCoreEntropyKey
#print axioms slabObservableHighSpinFarCoreEntropyPaidRepresentatives
#print axioms slabObservableHighSpinFarCoreEntropyPaidRepresentativeFiber
#print axioms slabObservableHighSpinFarCoreEntropyPaidRepresentativeFiber_key_eq
#print axioms slabObservableHighSpinCoreEntropyTarget_eq_of_key_eq
#print axioms slabObservableHighSpinCoreCertificates_sourceEntries_nodup
#print axioms slabObservableHighSpinFarCoreEntropyPaidRepresentativeFiber_sourceEntries_nodup
#print axioms slabObservableHighSpinCoreEntropySourceCode
#print axioms slabObservableHighSpinCoreEntropySourceEntry_eq_of_code_eq
#print axioms slabObservableHighSpinFarCoreEntropyPaidRepresentativeFiber_codes_nodup
#print axioms slabObservableHighSpinFarCoreEntropyPaidRepresentativeFiber_length_le
#print axioms componentCoreCompletionCountedRate
#print axioms componentCoreCompletionCountedRate_eqv
#print axioms slabObservableHighSpinFarCoreEntropyPaidRepresentativeFiber_weight_le
#print axioms slabObservableHighSpinFarCoreEntropyPaidRepresentativeFibers_weight_total

end YMGap.Continuum.CompactDualSlabObservableHighSpinCoreEntropyFiber
