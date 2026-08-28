/-
# Split a far core component into paid and genuinely low-spin length

The complete selected-copy profile of a reserve-failing rooted component is
the pointwise sum of its high-spin exterior drop and finite-core residual
drop.  Serialization preserves that sum exactly at the level of list lengths.

Consequently, a far certificate whose complete component has size at least
`radius + 2` satisfies one of two executable alternatives:

```text
radius + 2 <= 2 * paid exterior length,
radius + 2 <= 2 * finite-core residual length.
```

The first branch already carries the arbitrary-coupling high-spin path
payment.  Only the second branch is a genuinely long low-spin connected
object.  The Boolean split below preserves the far-core mass exactly.

Constructive contract: exact `List.flatMap` length arithmetic and Boolean
finite partition only.  No `Classical.*`, choice, `native_decide`, `sorry`,
custom axiom, noncomputable declaration, or enlarged heartbeat budget.
-/

import YMGap.Continuum.CompactDualSlabObservableHighSpinCoreGeometry
import YMGap.Continuum.CompactDualSlabFaceStrandComponentHighSpinCoreSplitWeight

namespace YMGap.Continuum.CompactDualSlabObservableHighSpinCoreFarSplit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.CompactDualSlabFaceStrandComponentDrop
open YMGap.Continuum.CompactDualSlabFaceStrandComponentHighSpinCoreSplitWeight
open YMGap.Continuum.CompactDualSlabFaceStrandComponentWeight
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabObservableHighSpinCoreCarrier
open YMGap.Continuum.CompactDualSlabObservableHighSpinCoreGeometry
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Serialization preserves a pointwise drop split -/

private theorem flatMap_replicate_length_split
    {A B : Type} (whole left right : A -> Nat)
    (value : A -> B)
    (hsplit : forall item, left item + right item = whole item) :
    forall items : List A,
      (items.flatMap fun item =>
          List.replicate (whole item) (value item)).length =
        (items.flatMap fun item =>
            List.replicate (left item) (value item)).length +
          (items.flatMap fun item =>
            List.replicate (right item) (value item)).length
  | [] => rfl
  | head :: tail => by
      simp only [List.flatMap_cons, List.length_append,
        List.length_replicate]
      rw [flatMap_replicate_length_split whole left right value hsplit tail]
      have hhead := hsplit head
      omega

/-- For every physical drop profile, the complete serialized word length is
the sum of its paid exterior and finite-core residual word lengths. -/
theorem highSpinDropFaces_length_split
    (extent : Nat) (physical : SlabLabelling) (threshold : Nat)
    (drop : Nat -> Nat) :
    (slabFaceDropList extent drop).length =
      (highSpinExteriorDropFaces
          extent physical threshold drop).length +
        (highSpinCoreResidualFaces
          extent physical threshold drop).length := by
  unfold slabFaceDropList highSpinExteriorDropFaces
    highSpinCoreResidualFaces
  exact flatMap_replicate_length_split
    drop
    (exteriorDropCount physical threshold drop)
    (coreResidualDropCount physical threshold drop)
    (fun faceId => faceId)
    (fun faceId =>
      exteriorDropCount_add_coreResidualDropCount
        physical threshold drop faceId)
    (slabPhysicalFaceEdges extent)

/-- Specialization to the actual observable-rooted strand component. -/
theorem slabObservableHighSpinCoreCertificate_peel_length_split
    {D : SlabPhysicalData} {faceId : Nat}
    {hface : faceId ∈ slabPhysicalFaceEdges D.extent}
    {threshold : Nat}
    (certificate : SlabObservableHighSpinCoreCertificate
      D faceId hface threshold) :
    (SlabFusionWitnessFaceStrandSeed.peelFaces
        (certificate.sourceEntry.seed D faceId hface)).length =
      (SlabFusionWitnessFaceStrandSeed.exteriorPeelFaces
          (certificate.sourceEntry.seed D faceId hface) threshold).length +
        (SlabFusionWitnessFaceStrandSeed.coreResidualFaces
          (certificate.sourceEntry.seed D faceId hface) threshold).length := by
  exact highSpinDropFaces_length_split
    D.extent certificate.sourceEntry.1.1 threshold
    (slabFaceStrandSelectionCount
      (certificate.sourceEntry.seed D faceId hface).selected)

/-! ## 2. Executable paid/residual split of the far carrier -/

/-- Whether at least half of the far size floor is paid by the exterior word,
written without division. -/
def slabObservableHighSpinFarCoreExteriorLongTest
    {D : SlabPhysicalData} {faceId : Nat}
    {hface : faceId ∈ slabPhysicalFaceEdges D.extent}
    {threshold : Nat} (radius : Nat)
    (certificate : SlabObservableHighSpinCoreCertificate
      D faceId hface threshold) : Bool :=
  decide
    (radius + 2 <=
      2 * (SlabFusionWitnessFaceStrandSeed.exteriorPeelFaces
        (certificate.sourceEntry.seed D faceId hface) threshold).length)

/-- Far certificates with a long paid exterior word. -/
def slabObservableHighSpinFarCoreExteriorLongCertificates
    (D : SlabPhysicalData) (faceId : Nat)
    (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (threshold radius : Nat) :
    List (SlabObservableHighSpinCoreCertificate
      D faceId hface threshold) :=
  (slabObservableHighSpinFarCoreCertificates
      D faceId hface threshold radius).filter
    (slabObservableHighSpinFarCoreExteriorLongTest radius)

/-- Far certificates for which the paid exterior is not long enough; their
finite-core residual word must be long. -/
def slabObservableHighSpinFarCoreResidualLongCertificates
    (D : SlabPhysicalData) (faceId : Nat)
    (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (threshold radius : Nat) :
    List (SlabObservableHighSpinCoreCertificate
      D faceId hface threshold) :=
  (slabObservableHighSpinFarCoreCertificates
      D faceId hface threshold radius).filter fun certificate =>
    !(slabObservableHighSpinFarCoreExteriorLongTest radius certificate)

/-- The far-core certificate weight is exactly the long-paid mass plus the
long-residual mass. -/
theorem slabObservableHighSpinFarCoreCertificates_weight_split
    (D : SlabPhysicalData) (faceId : Nat)
    (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (threshold radius : Nat) :
    listQSum slabObservableHighSpinCoreCertificateWeight
        (slabObservableHighSpinFarCoreCertificates
          D faceId hface threshold radius) ≈
      listQSum slabObservableHighSpinCoreCertificateWeight
          (slabObservableHighSpinFarCoreExteriorLongCertificates
            D faceId hface threshold radius) +
        listQSum slabObservableHighSpinCoreCertificateWeight
          (slabObservableHighSpinFarCoreResidualLongCertificates
            D faceId hface threshold radius) := by
  unfold slabObservableHighSpinFarCoreExteriorLongCertificates
    slabObservableHighSpinFarCoreResidualLongCertificates
  exact listQSum_filter_partition
    slabObservableHighSpinCoreCertificateWeight
    (slabObservableHighSpinFarCoreExteriorLongTest radius)
    (slabObservableHighSpinFarCoreCertificates
      D faceId hface threshold radius)

/-- Membership in the paid branch exposes its exact doubled length floor. -/
theorem slabObservableHighSpinFarCoreExteriorLong_length_floor
    {D : SlabPhysicalData} {faceId : Nat}
    {hface : faceId ∈ slabPhysicalFaceEdges D.extent}
    {threshold radius : Nat}
    (certificate : SlabObservableHighSpinCoreCertificate
      D faceId hface threshold)
    (hcertificate : certificate ∈
      slabObservableHighSpinFarCoreExteriorLongCertificates
        D faceId hface threshold radius) :
    radius + 2 <=
      2 * (SlabFusionWitnessFaceStrandSeed.exteriorPeelFaces
        (certificate.sourceEntry.seed D faceId hface) threshold).length := by
  exact of_decide_eq_true (List.mem_filter.mp hcertificate).2

/-- If the paid half fails, the exact complete-length split forces the
finite-core residual half to be long. -/
theorem slabObservableHighSpinFarCoreResidualLong_length_floor
    {D : SlabPhysicalData} {faceId : Nat}
    {hface : faceId ∈ slabPhysicalFaceEdges D.extent}
    {threshold radius : Nat}
    (certificate : SlabObservableHighSpinCoreCertificate
      D faceId hface threshold)
    (hcertificate : certificate ∈
      slabObservableHighSpinFarCoreResidualLongCertificates
        D faceId hface threshold radius) :
    radius + 2 <=
      2 * (SlabFusionWitnessFaceStrandSeed.coreResidualFaces
        (certificate.sourceEntry.seed D faceId hface) threshold).length := by
  have hparts := List.mem_filter.mp hcertificate
  have hfar : certificate ∈
      slabObservableHighSpinFarCoreCertificates
        D faceId hface threshold radius := hparts.1
  have hnotPaid := hparts.2
  have hcomplete :=
    slabObservableHighSpinFarCoreCertificate_peel_floor certificate hfar
  have hsplit :=
    slabObservableHighSpinCoreCertificate_peel_length_split certificate
  by_cases hpaid : radius + 2 <=
      2 * (SlabFusionWitnessFaceStrandSeed.exteriorPeelFaces
        (certificate.sourceEntry.seed D faceId hface) threshold).length
  · simp [slabObservableHighSpinFarCoreExteriorLongTest, hpaid] at hnotPaid
  · omega

#print axioms highSpinDropFaces_length_split
#print axioms slabObservableHighSpinCoreCertificate_peel_length_split
#print axioms slabObservableHighSpinFarCoreExteriorLongTest
#print axioms slabObservableHighSpinFarCoreExteriorLongCertificates
#print axioms slabObservableHighSpinFarCoreResidualLongCertificates
#print axioms slabObservableHighSpinFarCoreCertificates_weight_split
#print axioms slabObservableHighSpinFarCoreExteriorLong_length_floor
#print axioms slabObservableHighSpinFarCoreResidualLong_length_floor

end YMGap.Continuum.CompactDualSlabObservableHighSpinCoreFarSplit
