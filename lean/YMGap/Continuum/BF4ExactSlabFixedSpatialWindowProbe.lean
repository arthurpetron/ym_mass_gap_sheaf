/-
# Ordered signed spatial probes throughout a fixed time window

A schedule is a list of time offsets and lists of signed face-character
factors. Its source polynomial uses the existing slice probe on each
specified slice of the chronological carrier. The literal original probe
list shifts only faces, retaining every coefficient, spin, repeated factor
and list order. No sorting or merging of scheduled times is performed.

The existing middle-slice placement and ordered source-probe pin give the
whole-window coefficient-sensitive pin. This supplies original physical
observables for the finite window pairing and its time limit. It does not
identify arbitrary coordinate polynomials with gauge-invariant observables,
or assert a stationary cylinder law, OS positivity or a physical gap.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalMiddle

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialWindowProbe

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialChainCarrier (embedding)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialProbe
open YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalMiddle (middle_polynomial_pin)
open YMGap.Continuum.BF4ExactSlabTemporalSweep
open YMGap.Continuum.BF4ExactSlabTemporalSweepCharacters (sweptCharacter)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHaarBlockEmbedding
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra (lift_supported)
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate (supported_one)
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local notation:max "N" width:arg => List.length (baseLinks width)
local notation:max "B" extent:arg => List.length (boundaryCompleteSlabLinks extent)

/-- The ordered signed schedule on its chronological source coordinates. -/
def windowProbe (width : Nat) (fs : List (Nat × List FaceFactor)) : RatPoly :=
  polynomialProduct (fun e => liftBoundary (e.1*(N width)) (sourceProbe width e.2)) fs

/-- Produce the literal original factors, changing only each face's time. -/
def placeWindowProbes (start : Nat) (fs : List (Nat × List FaceFactor)) : List FaceFactor :=
  fs.flatMap (fun e => placeProbes (start+e.1) e.2)

private theorem support_mono {small large : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks small p) (hle : small ≤ large) :
    SupportedQuaternionBlocks large p :=
  fun term hm => Nat.le_trans (hp term hm) (Nat.mul_le_mul_left 4 hle)

/-- Syntactic support needs only the scheduled offsets, not physical faces. -/
theorem windowProbe_supported (width L : Nat) :
    (fs : List (Nat × List FaceFactor)) →
    (hwithin : ∀ e, e ∈ fs → e.1 ≤ L) →
    SupportedQuaternionBlocks ((L+1)*(N width)) (windowProbe width fs)
  | [], _ => supported_one _
  | e::es, hwithin => by
      have he : e.1 ≤ L := hwithin e List.mem_cons_self
      have hle : N width + e.1*(N width) ≤ (L+1)*(N width) := by
        have hm := Nat.mul_le_mul_right (N width) he
        rw [Nat.succ_mul]
        omega
      exact supported_polyMul
        (support_mono (lift_supported (sourceProbe_supported width e.2) (e.1*(N width))) hle)
        (windowProbe_supported width L es (fun a ha => hwithin a (List.mem_cons_of_mem e ha)))

/-- Every emitted factor is a physical face of the same original slab. -/
theorem placeWindowProbes_physical {width start L extent : Nat}
    (hw : width ≤ extent) (ht : start+L ≤ extent)
    (fs : List (Nat × List FaceFactor))
    (hwithin : ∀ e, e ∈ fs → e.1 ≤ L)
    (hfaces : ∀ e, e ∈ fs → ∀ f, f ∈ e.2 → f.1 ∈ spatialFaces width) :
    ∀ f, f ∈ placeWindowProbes start fs → f.1 ∈ boundaryCompleteSlabPlaquettes extent := by
  intro f hf
  obtain ⟨e, he, hfe⟩ := List.mem_flatMap.mp hf
  have hoffset := hwithin e he
  exact placeProbes_physical hw (show start+e.1 ≤ extent by omega) e.2 (hfaces e he) f hfe

/-- All emitted factors remain spatial, at any start time. -/
theorem placeWindowProbes_spatial {width : Nat} (start : Nat)
    (fs : List (Nat × List FaceFactor))
    (hfaces : ∀ e, e ∈ fs → ∀ f, f ∈ e.2 → f.1 ∈ spatialFaces width) :
    ∀ f, f ∈ placeWindowProbes start fs → (dirsOf f.1.2).2 ≠ Dir4.x3 := by
  intro f hf
  obtain ⟨e, he, hfe⟩ := List.mem_flatMap.mp hf
  exact placeProbes_spatial (start+e.1) e.2 (hfaces e he) f hfe

private theorem scheduledProbe_pin {width start L extent : Nat}
    (hw : width ≤ extent) (ht : start+L ≤ extent)
    (e : Nat × List FaceFactor) (he : e.1 ≤ L)
    (hfaces : ∀ f, f ∈ e.2 → f.1 ∈ spatialFaces width) :
    PaddedPolynomialCoeffEqv (B extent)
      ((embedding L hw ht).polynomial (liftBoundary (e.1*(N width)) (sourceProbe width e.2)))
      (sweptProduct extent 0 (placeProbes (start+e.1) e.2)) := by
  have hcount : e.1+(L-e.1) = L := by omega
  have htime : start+e.1 ≤ extent := by omega
  have hplace :
      (embedding L hw ht).polynomial (liftBoundary (e.1*(N width)) (sourceProbe width e.2)) =
        (BF4ExactSlabFixedSpatialSliceCarrier.embedding hw htime).polynomial (sourceProbe width e.2) := by
    have h := middle_polynomial_pin (m := e.1) (n := L-e.1) hw
      (show start+(e.1+(L-e.1)) ≤ extent by omega)
      (sourceProbe width e.2) (sourceProbe_supported width e.2)
    simpa only [BlockEmbedding.polynomial, BlockEmbedding.exponents,
      BlockEmbedding.index, embedding, hcount] using h
  rw [hplace]
  exact sourceProbe_pin hw htime e.2 hfaces

/-- Exact scheduled-probe pin in the original chronological carrier. Every
signed character list and the entire flattened schedule order are retained. -/
theorem windowProbe_pin {width start L extent : Nat}
    (hw : width ≤ extent) (ht : start+L ≤ extent) :
    (fs : List (Nat × List FaceFactor)) →
    (hwithin : ∀ e, e ∈ fs → e.1 ≤ L) →
    (hfaces : ∀ e, e ∈ fs → ∀ f, f ∈ e.2 → f.1 ∈ spatialFaces width) →
    PaddedPolynomialCoeffEqv (B extent)
      ((embedding L hw ht).polynomial (windowProbe width fs))
      (sweptProduct extent 0 (placeWindowProbes start fs))
  | [], _, _ => .of_prefix (embedding L hw ht).polynomial_one_prefix
  | e::es, hwithin, hfaces => by
      have hhead := scheduledProbe_pin hw ht e
        (hwithin e List.mem_cons_self) (hfaces e List.mem_cons_self)
      have htail := windowProbe_pin hw ht es
        (fun a ha => hwithin a (List.mem_cons_of_mem e ha))
        (fun a ha => hfaces a (List.mem_cons_of_mem e ha))
      change PaddedPolynomialCoeffEqv (B extent)
        ((embedding L hw ht).polynomial
          (polyMul (liftBoundary (e.1*(N width)) (sourceProbe width e.2)) (windowProbe width es)))
        (sweptProduct extent 0 (placeProbes (start+e.1) e.2 ++ placeWindowProbes start es))
      rw [BlockEmbedding.polynomial_mul]
      exact (hhead.mul htail).trans
        (.of_coeff (polynomialProduct_append (factor (sweptCharacter extent 0))
          (placeProbes (start+e.1) e.2) (placeWindowProbes start es)).symm)

end YMGap.Continuum.BF4ExactSlabFixedSpatialWindowProbe

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowProbe.windowProbe
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowProbe.placeWindowProbes
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowProbe.windowProbe_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowProbe.placeWindowProbes_physical
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowProbe.placeWindowProbes_spatial
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowProbe.windowProbe_pin
