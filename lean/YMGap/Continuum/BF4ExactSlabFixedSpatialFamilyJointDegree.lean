/-
# Depth-independent degree of the ORIGINAL conditioned joint law

The original finite-cutoff kinetic kernel resets each retained output block
to degree at most K, regardless of the degree of the integrated input.
Consequently every actual terminal message has this ceiling at every depth.
The complete central edge and its family projection inherit the ceiling 8*K:
one kinetic factor, at most six incident spatial faces, one terminal message.
Compression reads the same surviving exponents, so the finite-margin backend
retains these ceilings on its computed smaller carrier. Its signed-family
numerators live in a fixed finite exponent universe depending on K and family
length, not on nome, width, terminal depth or the signed coefficients.

This bounds degree independently of width and terminal depth at FIXED cutoff.
No coefficient-size, term-count, construction-cost, runtime, useful signed
margin, scaling-family or continuum conclusion is asserted.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyJointDensity
import YMGap.Continuum.BF4ExactSlabFixedSpatialKineticDegree
import YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialDegree
import YMGap.Continuum.SU2QuaternionBoundedMonomials

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyJointDegree

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder (supported_polyMul)
open YMGap.Continuum.BF4GeometricSpinNetworkMehler (characterPolynomial)
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation (finitePolySum)
open YMGap.Continuum.ClusterCount4DProgress (Z4Plaq)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
  (quaternionBlockDegree SupportedQuaternionBlocks)
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection (exponentAt_drop)
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal (partialHaarHeads)
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionBlockDegreeBound
open YMGap.Continuum.QuaternionHaarSquareCertificate (supported_one)
open YMGap.Continuum.SU2QuaternionBoundedMonomials
open YMGap.Continuum.SU2QuaternionHaarBlockEmbedding
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection (familyProject)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight kineticWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticDegree
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialDegree
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (plaquette)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamilySchedule
  (spatialSpan spatialSpan_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage terminalMessage_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (edgeDensity jump)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyJointDensity
  (density observableCopies observableCopies_length footprintEmbedding)

local notation:max "N" width:arg => List.length (baseLinks width)

/-- Integrating a head shifts a surviving degree ceiling by one block. -/
theorem partialHaarHead_degree {i d : Nat} {p : RatPoly}
    (hp : DegreeLE (i+1) d p) : DegreeLE i d (partialHaarHead p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  change quaternionBlockDegree (s.1.drop 4) i ≤ d
  simpa only [quaternionBlockDegree, exponentAt_drop,
    show 4+4*i = 4*(i+1) by omega,
    show 4+(4*i+1) = 4*(i+1)+1 by omega,
    show 4+(4*i+2) = 4*(i+1)+2 by omega,
    show 4+(4*i+3) = 4*(i+1)+3 by omega] using hp s hs

theorem partialHaarHeads_degree (n i d : Nat) {p : RatPoly}
    (hp : DegreeLE (n+i) d p) : DegreeLE i d (partialHaarHeads n p) := by
  induction n generalizing p with
  | zero => simpa only [Nat.zero_add] using hp
  | succ n ih =>
      apply ih
      apply partialHaarHead_degree (i := n+i)
      simpa only [Nat.succ_add, Nat.add_succ] using hp

/-- The output ceiling comes from the kernel only, not the input degree. -/
theorem step_degree_reset {n i d : Nat} {kernel weight input : RatPoly}
    (hk : DegreeLE (n+i) d kernel)
    (hw : SupportedQuaternionBlocks n weight)
    (hi : SupportedQuaternionBlocks n input) :
    DegreeLE i d (step n kernel weight input) := by
  apply partialHaarHeads_degree n i d
  simpa only [Nat.add_zero] using hk.mul
    ((DegreeLE.of_independent (supported_upper_independent hw i)).mul
      (DegreeLE.of_independent (supported_upper_independent hi i)))

theorem iterateStep_degree {n i d : Nat} {kernel weight : RatPoly}
    (hk : SupportedQuaternionBlocks (n+n) kernel)
    (hw : SupportedQuaternionBlocks n weight)
    (hd : DegreeLE (n+i) d kernel) (count : Nat) {input : RatPoly}
    (hi : SupportedQuaternionBlocks n input) (hdi : DegreeLE i d input) :
    DegreeLE i d (iterateStep n kernel weight count input) := by
  induction count generalizing input with
  | zero => exact hdi
  | succ count ih =>
      exact ih (step_supported hk hw hi) (step_degree_reset hd hw hi)

/-- Every actual original terminal depth uses the SAME cutoff-only ceiling. -/
theorem terminalMessage_degree (w : Q') (K width depth i : Nat)
    (hi : i < N width) : DegreeLE i K (terminalMessage w K width depth) := by
  unfold terminalMessage
  exact iterateStep_degree (kineticWeight_supported w K width)
    (spatialWeight_supported w K width) (kineticWeight_upper_degree w K width i hi)
    depth (supported_one _) (DegreeLE.one i K)

private theorem liftHead_degree {i d : Nat} {p : RatPoly}
    (hp : DegreeLE i d p) : DegreeLE (i+1) d (liftHead p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  have he (r : Nat) : exponentAt (0::0::0::0::s.1) (4*(i+1)+r) =
      exponentAt s.1 (4*i+r) := by
    rw [show 4*(i+1)+r = (4*i+r)+4 by omega]
    rfl
  change exponentAt (0::0::0::0::s.1) (4*(i+1)+0) +
    exponentAt (0::0::0::0::s.1) (4*(i+1)+1) +
    exponentAt (0::0::0::0::s.1) (4*(i+1)+2) +
    exponentAt (0::0::0::0::s.1) (4*(i+1)+3) ≤ d
  rw [he 0, he 1, he 2, he 3]
  exact hp s hs

theorem liftBoundary_degree (n i d : Nat) {p : RatPoly}
    (hp : DegreeLE i d p) : DegreeLE (n+i) d (liftBoundary n p) := by
  induction n with
  | zero => simpa only [Nat.zero_add] using hp
  | succ n ih =>
      simpa only [Nat.succ_add, Nat.add_succ] using liftHead_degree ih

theorem edgeDensity_lower_degree (w : Q') (K width depth i : Nat)
    (hi : i < N width) :
    DegreeLE i (8*K)
      (edgeDensity w K width (terminalMessage w K width depth)) := by
  have hl := (kineticWeight_lower_degree w K width i hi).mul
    ((spatialWeight_degree w K width i hi).mul
      (terminalMessage_degree w K width depth i hi))
  have hu := DegreeLE.of_independent
    (lift_lower_independent (N width)
      (polyMul (spatialWeight w K width) (terminalMessage w K width depth)) i hi)
  have h := hl.mul hu
  simpa only [edgeDensity, Nat.add_zero, show K+(6*K+K) = 8*K by omega] using h

theorem edgeDensity_upper_degree (w : Q') (K width depth i : Nat)
    (hi : i < N width) :
    DegreeLE (N width+i) (8*K)
      (edgeDensity w K width (terminalMessage w K width depth)) := by
  have hvg := supported_polyMul (spatialWeight_supported w K width)
    (terminalMessage_supported w K width depth)
  have hl := (kineticWeight_upper_degree w K width i hi).mul
    (DegreeLE.of_independent (supported_upper_independent hvg i))
  have hu := liftBoundary_degree (N width) i _
    ((spatialWeight_degree w K width i hi).mul
      (terminalMessage_degree w K width depth i hi))
  simpa only [edgeDensity, Nat.add_zero, show K+(6*K+K) = 8*K by omega] using hl.mul hu

theorem density_degree (w : Q') (K width depth : Nat) (qs : List Z4Plaq)
    (block : Nat) (hb : block < N width+N width) :
    DegreeLE block (8*K) (density w K width depth qs) := by
  unfold density
  apply familyProject_degree
  by_cases h : block < N width
  · exact edgeDensity_lower_degree w K width depth block h
  · have hi : block-N width < N width := by omega
    have he : N width+(block-N width) = block := by omega
    simpa only [he] using
      edgeDensity_upper_degree w K width depth (block-N width) hi

/-- Compression reads exactly the original degree at the selected block. -/
theorem compress_degree {source target : Nat} (E : BlockEmbedding source target)
    (i : Nat) (hi : i < source) (d : Nat) {p : RatPoly}
    (hp : DegreeLE (E.block i) d p) : DegreeLE i d (E.compress p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  have he (r : Nat) (hr : r < 4) :
      exponentAt (E.compressExponents s.1) (4*i+r) =
        exponentAt s.1 (4*E.block i+r) := by
    rw [E.compress_exponent_pin s.1 (by omega),
      show (4*i+r)/4 = i by omega, show (4*i+r)%4 = r by omega]
  change quaternionBlockDegree (E.compressExponents s.1) i ≤ d
  unfold quaternionBlockDegree
  rw [show 4*i = 4*i+0 by omega, he 0 (by decide), he 1 (by decide),
    he 2 (by decide), he 3 (by decide)]
  exact hp s hs

/-- The actual compact density inherits the depth-independent ORIGINAL ceiling. -/
theorem compressed_density_degree (w : Q') (K width depth : Nat) (qs : List Z4Plaq)
    (i : Nat) (hi : i < (observableCopies width qs).length) :
    DegreeLE i (8*K)
      ((footprintEmbedding width qs).compress (density w K width depth qs)) :=
  compress_degree _ i hi _
    (density_degree w K width depth qs _ ((footprintEmbedding width qs).block_lt hi))

/-- Each actual compressed insertion pays its OWN added degree, preserving signs. -/
theorem compressed_insertion_degree (w : Q') (K width depth : Nat) (qs : List Z4Plaq)
    (i d : Nat) (hi : i < (observableCopies width qs).length) {p : RatPoly}
    (hp : DegreeLE ((footprintEmbedding width qs).block i) d p) :
    DegreeLE i (8*K+d)
      ((footprintEmbedding width qs).compress (polyMul (density w K width depth qs) p)) :=
  compress_degree _ i hi _
    ((density_degree w K width depth qs _
      ((footprintEmbedding width qs).block_lt hi)).mul hp)

private theorem neg_degree {i d : Nat} {p : RatPoly}
    (hp : DegreeLE i d p) : DegreeLE i d (polyNeg p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

/-- A complete signed family is degree at most one in every physical block;
overlap and signs do not enlarge the ceiling. -/
theorem spatialSpan_degree (width : Nat) (coeff : Z4Plaq → Q')
    (qs : List Z4Plaq) (hqs : ∀ q, q ∈ qs → q ∈ spatialFaces width)
    (i : Nat) (hi : i < N width) : DegreeLE i 1 (spatialSpan width coeff qs) := by
  induction qs with
  | nil => intro t ht; exact False.elim (List.not_mem_nil ht)
  | cons q qs ih =>
      change DegreeLE i 1 (polyAdd
        (polySmul (coeff q) (characterPolynomial (plaquette width q).scalar 1))
        (spatialSpan width coeff qs))
      have hq := characterPolynomial_degree_le i (plaquette width q).scalar
        (plaquetteScalar_degree width q i hi (hqs q List.mem_cons_self)) 1
      exact (hq.smul (coeff q)).add
        (ih (fun r hr => hqs r (List.mem_cons_of_mem q hr)))

theorem family_lower_degree (width : Nat) (coeff : Z4Plaq → Q')
    (qs : List Z4Plaq) (hqs : ∀ q, q ∈ qs → q ∈ spatialFaces width)
    (i : Nat) (_hi : i < N width+N width) :
    DegreeLE i 1 (spatialSpan width coeff qs) := by
  by_cases h : i < N width
  · exact spatialSpan_degree width coeff qs hqs i h
  · have he : N width+(i-N width) = i := by omega
    have hz := DegreeLE.of_independent
      (supported_upper_independent (spatialSpan_supported width coeff qs) (i-N width))
    have hz' : DegreeLE i 0 (spatialSpan width coeff qs) := by simpa only [he] using hz
    exact hz'.mono (by decide : 0 ≤ 1)

theorem family_upper_degree (width : Nat) (coeff : Z4Plaq → Q')
    (qs : List Z4Plaq) (hqs : ∀ q, q ∈ qs → q ∈ spatialFaces width)
    (i : Nat) (hi : i < N width+N width) :
    DegreeLE i 1 (liftBoundary (N width) (spatialSpan width coeff qs)) := by
  by_cases h : i < N width
  · exact (DegreeLE.of_independent
      (lift_lower_independent (N width) (spatialSpan width coeff qs) i h)).mono
      (by decide : 0 ≤ 1)
  · have hj : i-N width < N width := by omega
    have he : N width+(i-N width) = i := by omega
    simpa only [he] using liftBoundary_degree (N width) (i-N width) 1
      (spatialSpan_degree width coeff qs hqs (i-N width) hj)

/-- The complete signed jump, not a sum of facewise squared costs. -/
theorem family_jump_degree (width : Nat) (coeff : Z4Plaq → Q')
    (qs : List Z4Plaq) (hqs : ∀ q, q ∈ qs → q ∈ spatialFaces width)
    (i : Nat) (hi : i < N width+N width) :
    DegreeLE i 1 (jump width (spatialSpan width coeff qs)) :=
  (family_lower_degree width coeff qs hqs i hi).add
    (neg_degree (family_upper_degree width coeff qs hqs i hi))

/-- Actual partition, BOTH means, second moment, mixed moment and whole jump.
Every cross term of the original signed family remains present. -/
def marginInsertions (width : Nat) (coeff : Z4Plaq → Q') (qs : List Z4Plaq) :
    List RatPoly :=
  let f := spatialSpan width coeff qs
  let u := liftBoundary (N width) f
  let j := jump width f
  [polyOne, f, u, polyMul f f, polyMul f u, polyMul j j]

theorem marginInsertions_degree (width : Nat) (coeff : Z4Plaq → Q')
    (qs : List Z4Plaq) (hqs : ∀ q, q ∈ qs → q ∈ spatialFaces width)
    (p : RatPoly) (hp : p ∈ marginInsertions width coeff qs)
    (i : Nat) (hi : i < N width+N width) : DegreeLE i 2 p := by
  have hl := family_lower_degree width coeff qs hqs i hi
  have hu := family_upper_degree width coeff qs hqs i hi
  have hj := family_jump_degree width coeff qs hqs i hi
  simp only [marginInsertions, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  · exact DegreeLE.one i 2
  · exact hl.mono (by decide)
  · exact hu.mono (by decide)
  · exact hl.mul hl
  · exact hl.mul hu
  · exact hj.mul hj

/-- One computable finite exponent universe for all these ORIGINAL numerators.
Only cutoff and face count enter; no division or choice is involved. -/
def marginMonomials (K faces : Nat) : List (List Nat) :=
  monomials (8*faces) (fun _ => 8*K+2)

private theorem compressed_monomial {source target blocks d : Nat}
    (E : BlockEmbedding source target) (hsize : source ≤ blocks) (p : RatPoly)
    (hd : ∀ i, i < source → DegreeLE i d (E.compress p))
    (t : RatTerm) (ht : t ∈ E.compress p) :
    t.1 ∈ monomials blocks (fun _ => d) := by
  have hs := E.compress_supported p
  apply mem_monomials_of_degree blocks (fun _ => d) t.1
    (Nat.le_trans (hs t ht) (Nat.mul_le_mul_left 4 hsize))
  intro i _hi
  by_cases h : i < source
  · exact hd i h t ht
  · have he : source+(i-source) = i := by omega
    have hz := DegreeLE.of_independent (supported_upper_independent hs (i-source))
    have hz' : DegreeLE i 0 (E.compress p) := by simpa only [he] using hz
    exact Nat.le_trans (hz' t ht) (Nat.zero_le d)

/-- ALL actual margin numerators have terms in the SAME finite list at every
nome, spatial width and terminal depth, retaining BOTH means and signed mixes. -/
theorem margin_numerators_monomials (w : Q') (K width depth : Nat)
    (coeff : Z4Plaq → Q') (qs : List Z4Plaq)
    (hqs : ∀ q, q ∈ qs → q ∈ spatialFaces width)
    (p : RatPoly) (hp : p ∈ marginInsertions width coeff qs)
    (t : RatTerm) (ht : t ∈ (footprintEmbedding width qs).compress
      (polyMul (density w K width depth qs) p)) :
    t.1 ∈ marginMonomials K qs.length := by
  apply compressed_monomial (footprintEmbedding width qs)
    (observableCopies_length width qs) (polyMul (density w K width depth qs) p)
    (fun i hi => compressed_insertion_degree w K width depth qs i 2 hi
      (marginInsertions_degree width coeff qs hqs p hp _
        ((footprintEmbedding width qs).block_lt hi))) t ht

#print axioms partialHaarHead_degree
#print axioms partialHaarHeads_degree
#print axioms step_degree_reset
#print axioms iterateStep_degree
#print axioms terminalMessage_degree
#print axioms liftBoundary_degree
#print axioms edgeDensity_lower_degree
#print axioms edgeDensity_upper_degree
#print axioms density_degree
#print axioms compress_degree
#print axioms compressed_density_degree
#print axioms compressed_insertion_degree
#print axioms spatialSpan_degree
#print axioms family_lower_degree
#print axioms family_upper_degree
#print axioms family_jump_degree
#print axioms marginInsertions
#print axioms marginInsertions_degree
#print axioms marginMonomials
#print axioms margin_numerators_monomials

end YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyJointDegree
