/-
# Unchanged physical presentations in a larger base box

The inclusion retains every signed coefficient, distance label, and original
spatial face word literally. It commutes with physical time, rational linear
operations, and recentering. These are presentation and geometry statements;
they do not identify finite-width interacting pairings or their norms.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialRecenter
import YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicLinear

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialBaseInclusion

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement
open YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicReflectedForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicSeminorm
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicLinear (addSpan smulSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime (physicalTime unit zero)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialRecenter

/-- Only the physical-face guard is enlarged, not the original face. -/
theorem spatialFaces_mono {base larger : Nat} (h : base ≤ larger)
    {p : Z4Plaq} (hp : p ∈ spatialFaces base) : p ∈ spatialFaces larger := by
  obtain ⟨⟨a,b,c,z⟩, plane⟩ := p
  have hf := (spatialFaces_mem_iff base ((a,b,c,z),plane)).mp hp
  change a < base ∧ b < base ∧ c < base ∧ z = 0 ∧
    (dirsOf plane).2 ≠ Dir4.x3 at hf
  apply (spatialFaces_mem_iff larger _).mpr
  exact ⟨Nat.lt_of_lt_of_le hf.1 h, Nat.lt_of_lt_of_le hf.2.1 h,
    Nat.lt_of_lt_of_le hf.2.2.1 h, hf.2.2.2.1, hf.2.2.2.2⟩

theorem physical_mono {base larger : Nat} (h : base ≤ larger)
    (xs : DistanceSpan) (hx : Physical base xs) : Physical larger xs := by
  intro x hm e he f hf
  exact spatialFaces_mono h (hx x hm e he f hf)

/-- The same signed original face words, with the larger physical guard. -/
def inclusion {base larger : Nat} (h : base ≤ larger)
    (x : PhysicalSpan base) : PhysicalSpan larger :=
  ⟨x.val, physical_mono h x.val x.property⟩

theorem inclusion_val {base larger : Nat} (h : base ≤ larger)
    (x : PhysicalSpan base) : (inclusion h x).val = x.val := rfl

theorem inclusion_radius {base larger : Nat} (h : base ≤ larger)
    (x : PhysicalSpan base) : radius (inclusion h x).val = radius x.val := rfl

theorem inclusion_encodeChart {base larger : Nat} (h : base ≤ larger)
    (H : Nat) (x : PhysicalSpan base) :
    encodeChart H (inclusion h x).val = encodeChart H x.val := rfl

theorem inclusion_refl {base : Nat} (x : PhysicalSpan base) :
    inclusion (Nat.le_refl base) x = x := Subtype.ext rfl

theorem inclusion_trans {base middle larger : Nat}
    (h : base ≤ middle) (k : middle ≤ larger) (x : PhysicalSpan base) :
    inclusion k (inclusion h x) = inclusion (Nat.le_trans h k) x := Subtype.ext rfl

theorem inclusion_time {base larger : Nat} (h : base ≤ larger)
    (n : Nat) (x : PhysicalSpan base) :
    inclusion h (physicalTime n x) = physicalTime n (inclusion h x) := Subtype.ext rfl

theorem inclusion_add {base larger : Nat} (h : base ≤ larger)
    (x y : PhysicalSpan base) :
    inclusion h (addSpan x y) = addSpan (inclusion h x) (inclusion h y) := Subtype.ext rfl

theorem inclusion_smul {base larger : Nat} (h : base ≤ larger)
    (c : Q') (x : PhysicalSpan base) :
    inclusion h (smulSpan c x) = smulSpan c (inclusion h x) := Subtype.ext rfl

theorem inclusion_unit {base larger : Nat} (h : base ≤ larger) :
    inclusion h (unit base) = unit larger := Subtype.ext rfl

theorem inclusion_zero {base larger : Nat} (h : base ≤ larger) :
    inclusion h (zero base) = zero larger := Subtype.ext rfl

theorem paddedWidth_mono {base larger : Nat} (h : base ≤ larger) (r : Nat) :
    paddedWidth base r ≤ paddedWidth larger r := by
  unfold paddedWidth
  omega

/-- Inclusion and recentering give literally the same target presentation. -/
theorem inclusion_recenter {base larger : Nat} (h : base ≤ larger)
    (r : Nat) (x : PhysicalSpan base) :
    inclusion (paddedWidth_mono h r) (recenter r x) = recenter r (inclusion h x) :=
  Subtype.ext rfl

#print axioms spatialFaces_mono
#print axioms physical_mono
#print axioms inclusion
#print axioms inclusion_val
#print axioms inclusion_radius
#print axioms inclusion_encodeChart
#print axioms inclusion_refl
#print axioms inclusion_trans
#print axioms inclusion_time
#print axioms inclusion_add
#print axioms inclusion_smul
#print axioms inclusion_unit
#print axioms inclusion_zero
#print axioms paddedWidth_mono
#print axioms inclusion_recenter

end YMGap.Continuum.BF4ExactSlabFixedSpatialBaseInclusion
