/-
# Entropy-balanced split of the far observable core

The accepted-target comparison for one component has the two-rate form

```text
anchorFaceCoefficient ^ paid * 2 ^ residual.
```

The adaptive inverse fiber contributes `componentAdaptiveEntropyBase` for
every complete component strand.  Since `complete = paid + residual`, the
combined rate is

```text
(8/25)^paid * (2 * 10240000)^residual.
```

Fifteen paid strands absorb one residual strand:

```text
(8/25)^15 * 20480000 < 4/5.
```

This module therefore replaces the preliminary half-length split by the
load-bearing executable dichotomy `15 * residual <= paid`.  In the paid
branch the strict entropy block rate is exposed.  In the complementary branch
a far component satisfies `radius + 2 <= 16 * residual`, so only a genuinely
long low-spin residual remains.

Constructive contract: Boolean finite partition, exact `Nat` arithmetic, and
closed rational arithmetic only.  No `Classical.*`, choice, `native_decide`,
`sorry`, custom axiom, noncomputable declaration, or enlarged heartbeat
budget.
-/

import YMGap.Continuum.CompactDualSlabObservableHighSpinCoreFarSplit
import YMGap.Continuum.CompactDualSlabFaceStrandComponentCoreCompletionWeight
import YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveEntropyCarrier

namespace YMGap.Continuum.CompactDualSlabObservableHighSpinCoreEntropySplit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveEntropyCarrier
open YMGap.Continuum.CompactDualSlabFaceStrandComponentWeight
open YMGap.Continuum.CompactDualSlabFaceStrandComponentHighSpinCoreSplitWeight
open YMGap.Continuum.CompactDualSlabObservableHighSpinCoreCarrier
open YMGap.Continuum.CompactDualSlabObservableHighSpinCoreFarSplit
open YMGap.Continuum.CompactDualSlabObservableHighSpinCoreGeometry
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The exact entropy threshold -/

/-- The low-spin factor after accounting for one residual strand's ordinary
peel cost and its one full-strand adaptive entropy factor. -/
def componentCoreCompletionResidualEntropyFactor : Q' :=
  Q'.ofNat (2 * componentAdaptiveEntropyBase)

/-- Fifteen paid high-spin entropy rates assigned to one residual factor. -/
def componentCoreCompletionEntropyBlockRate : Q' :=
  componentAdaptiveEntropyAnchorRatio ^ 15 *
    componentCoreCompletionResidualEntropyFactor

/-- The entropy-balanced block is strictly below the convenient rational
ceiling `4/5`. -/
theorem componentCoreCompletionEntropyBlockRate_le_fourFifths :
    componentCoreCompletionEntropyBlockRate <=
      Q'.mkPos 4 5 (by decide) := by
  unfold componentCoreCompletionEntropyBlockRate
    componentCoreCompletionResidualEntropyFactor
    componentAdaptiveEntropyAnchorRatio componentAdaptiveEntropyBase
    anchorFaceCoefficient
  decide

/-- One unpaired paid strand also fits under the same `4/5` ceiling. -/
theorem componentAdaptiveEntropyAnchorRatio_le_fourFifths :
    componentAdaptiveEntropyAnchorRatio <=
      Q'.mkPos 4 5 (by decide) := by
  unfold componentAdaptiveEntropyAnchorRatio componentAdaptiveEntropyBase
    anchorFaceCoefficient
  decide

/-! ## 2. Paid and residual lengths of the literal certificates -/

def slabObservableHighSpinCoreCertificatePaidLength
    {D : SlabPhysicalData} {faceId : Nat}
    {hface : faceId ∈ slabPhysicalFaceEdges D.extent}
    {threshold : Nat}
    (certificate : SlabObservableHighSpinCoreCertificate
      D faceId hface threshold) : Nat :=
  (SlabFusionWitnessFaceStrandSeed.exteriorPeelFaces
    (certificate.sourceEntry.seed D faceId hface) threshold).length

def slabObservableHighSpinCoreCertificateResidualLength
    {D : SlabPhysicalData} {faceId : Nat}
    {hface : faceId ∈ slabPhysicalFaceEdges D.extent}
    {threshold : Nat}
    (certificate : SlabObservableHighSpinCoreCertificate
      D faceId hface threshold) : Nat :=
  (SlabFusionWitnessFaceStrandSeed.coreResidualFaces
    (certificate.sourceEntry.seed D faceId hface) threshold).length

/-- Executable entropy-dominance test. -/
def slabObservableHighSpinFarCoreEntropyPaidTest
    {D : SlabPhysicalData} {faceId : Nat}
    {hface : faceId ∈ slabPhysicalFaceEdges D.extent}
    {threshold : Nat}
    (certificate : SlabObservableHighSpinCoreCertificate
      D faceId hface threshold) : Bool :=
  decide
    (15 * slabObservableHighSpinCoreCertificateResidualLength certificate <=
      slabObservableHighSpinCoreCertificatePaidLength certificate)

/-- Far certificates whose high-spin payment absorbs the full adaptive
entropy and coarse low-spin completion price. -/
def slabObservableHighSpinFarCoreEntropyPaidCertificates
    (D : SlabPhysicalData) (faceId : Nat)
    (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (threshold radius : Nat) :
    List (SlabObservableHighSpinCoreCertificate
      D faceId hface threshold) :=
  (slabObservableHighSpinFarCoreCertificates
    D faceId hface threshold radius).filter
      slabObservableHighSpinFarCoreEntropyPaidTest

/-- Complementary far certificates; these carry a quantitatively long
low-spin residual word. -/
def slabObservableHighSpinFarCoreEntropyResidualCertificates
    (D : SlabPhysicalData) (faceId : Nat)
    (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (threshold radius : Nat) :
    List (SlabObservableHighSpinCoreCertificate
      D faceId hface threshold) :=
  (slabObservableHighSpinFarCoreCertificates
    D faceId hface threshold radius).filter fun certificate =>
      !(slabObservableHighSpinFarCoreEntropyPaidTest certificate)

/-- The entropy-balanced Boolean split preserves the far-core weight
exactly. -/
theorem slabObservableHighSpinFarCoreCertificates_entropy_weight_split
    (D : SlabPhysicalData) (faceId : Nat)
    (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (threshold radius : Nat) :
    listQSum slabObservableHighSpinCoreCertificateWeight
        (slabObservableHighSpinFarCoreCertificates
          D faceId hface threshold radius) ≈
      listQSum slabObservableHighSpinCoreCertificateWeight
          (slabObservableHighSpinFarCoreEntropyPaidCertificates
            D faceId hface threshold radius) +
        listQSum slabObservableHighSpinCoreCertificateWeight
          (slabObservableHighSpinFarCoreEntropyResidualCertificates
            D faceId hface threshold radius) := by
  unfold slabObservableHighSpinFarCoreEntropyPaidCertificates
    slabObservableHighSpinFarCoreEntropyResidualCertificates
  exact listQSum_filter_partition
    slabObservableHighSpinCoreCertificateWeight
    slabObservableHighSpinFarCoreEntropyPaidTest
    (slabObservableHighSpinFarCoreCertificates
      D faceId hface threshold radius)

/-! ## 3. Quantitative consequences of the split -/

/-- Membership in the paid branch exposes the exact entropy balance. -/
theorem slabObservableHighSpinFarCoreEntropyPaid_balance
    {D : SlabPhysicalData} {faceId : Nat}
    {hface : faceId ∈ slabPhysicalFaceEdges D.extent}
    {threshold radius : Nat}
    (certificate : SlabObservableHighSpinCoreCertificate
      D faceId hface threshold)
    (hcertificate : certificate ∈
      slabObservableHighSpinFarCoreEntropyPaidCertificates
        D faceId hface threshold radius) :
    15 * slabObservableHighSpinCoreCertificateResidualLength certificate <=
      slabObservableHighSpinCoreCertificatePaidLength certificate := by
  exact of_decide_eq_true (List.mem_filter.mp hcertificate).2

/-- In the paid branch, the far distance floor is carried by a volume-free
strict-rate exponent. -/
theorem slabObservableHighSpinFarCoreEntropyPaid_exponent_floor
    {D : SlabPhysicalData} {faceId : Nat}
    {hface : faceId ∈ slabPhysicalFaceEdges D.extent}
    {threshold radius : Nat}
    (certificate : SlabObservableHighSpinCoreCertificate
      D faceId hface threshold)
    (hcertificate : certificate ∈
      slabObservableHighSpinFarCoreEntropyPaidCertificates
        D faceId hface threshold radius) :
    radius + 2 <=
      16 * (slabObservableHighSpinCoreCertificatePaidLength certificate -
        14 * slabObservableHighSpinCoreCertificateResidualLength
          certificate) := by
  have hparts := List.mem_filter.mp hcertificate
  have hfar := slabObservableHighSpinFarCoreCertificate_peel_floor
    certificate hparts.1
  have hsplit :=
    slabObservableHighSpinCoreCertificate_peel_length_split certificate
  have hbalance := of_decide_eq_true hparts.2
  change
    (SlabFusionWitnessFaceStrandSeed.peelFaces
      (certificate.sourceEntry.seed D faceId hface)).length =
      slabObservableHighSpinCoreCertificatePaidLength certificate +
        slabObservableHighSpinCoreCertificateResidualLength certificate
    at hsplit
  omega

/-- Failure of the entropy balance makes the low-spin residual itself long.
This is the only genuinely unsuppressed far branch left by the two-rate
calculation. -/
theorem slabObservableHighSpinFarCoreEntropyResidual_length_floor
    {D : SlabPhysicalData} {faceId : Nat}
    {hface : faceId ∈ slabPhysicalFaceEdges D.extent}
    {threshold radius : Nat}
    (certificate : SlabObservableHighSpinCoreCertificate
      D faceId hface threshold)
    (hcertificate : certificate ∈
      slabObservableHighSpinFarCoreEntropyResidualCertificates
        D faceId hface threshold radius) :
    radius + 2 <=
      16 * slabObservableHighSpinCoreCertificateResidualLength certificate := by
  have hparts := List.mem_filter.mp hcertificate
  have hfar := slabObservableHighSpinFarCoreCertificate_peel_floor
    certificate hparts.1
  have hsplit :=
    slabObservableHighSpinCoreCertificate_peel_length_split certificate
  have hnotPaid := hparts.2
  by_cases hpaid :
      15 * slabObservableHighSpinCoreCertificateResidualLength certificate <=
        slabObservableHighSpinCoreCertificatePaidLength certificate
  · simp [slabObservableHighSpinFarCoreEntropyPaidTest, hpaid] at hnotPaid
  · change
      (SlabFusionWitnessFaceStrandSeed.peelFaces
        (certificate.sourceEntry.seed D faceId hface)).length =
        slabObservableHighSpinCoreCertificatePaidLength certificate +
          slabObservableHighSpinCoreCertificateResidualLength certificate
      at hsplit
    omega

#print axioms componentCoreCompletionResidualEntropyFactor
#print axioms componentCoreCompletionEntropyBlockRate
#print axioms componentCoreCompletionEntropyBlockRate_le_fourFifths
#print axioms componentAdaptiveEntropyAnchorRatio_le_fourFifths
#print axioms slabObservableHighSpinCoreCertificatePaidLength
#print axioms slabObservableHighSpinCoreCertificateResidualLength
#print axioms slabObservableHighSpinFarCoreEntropyPaidTest
#print axioms slabObservableHighSpinFarCoreEntropyPaidCertificates
#print axioms slabObservableHighSpinFarCoreEntropyResidualCertificates
#print axioms slabObservableHighSpinFarCoreCertificates_entropy_weight_split
#print axioms slabObservableHighSpinFarCoreEntropyPaid_balance
#print axioms slabObservableHighSpinFarCoreEntropyPaid_exponent_floor
#print axioms slabObservableHighSpinFarCoreEntropyResidual_length_floor

end YMGap.Continuum.CompactDualSlabObservableHighSpinCoreEntropySplit
