/-
# Actual symmetric-power traces on the original slab Haar carrier

Hamilton norms multiply coefficientwise. Each literal slab link has unit
norm in the arbitrary-insertion Haar carrier, so the ordered plaquette
product does too. The actual all-degree matrix trace can therefore replace
the original character factor under every spectator insertion, at every
slab extent. No pointwise unit-norm hypothesis is assumed under Haar.

This is a signed-Haar identity, not positivity, link gluing, a transfer
operator construction, or a spectral gap.
-/

import YMGap.Continuum.SU2QuaternionSymmetricPowerHaarTrace

namespace YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.RationalQuaternionRatPoly
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionSymmetricPowerPolynomial
open YMGap.Continuum.SU2QuaternionSymmetricPowerHaarTrace
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugePolynomialSemantics
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

private def normEnvironment (p q : PolyQuaternion) : Nat → RatPoly
  | 0 => p.scalar | 1 => p.iPart | 2 => p.jPart | 3 => p.kPart
  | 4 => q.scalar | 5 => q.iPart | 6 => q.jPart | 7 => q.kPart
  | _ => polyZero

/-- Norm multiplicativity before any Haar integration or sphere relation. -/
theorem polyQuaternionNorm_mul (p q : PolyQuaternion) :
    RatPolyCoeffEqv (polyQuaternionNorm (PolyQuaternion.mul p q))
      (polyMul (polyQuaternionNorm p) (polyQuaternionNorm q)) := by
  exact coeffEvalExpr_eqv_of_normalize_eq
    (PolyQuaternionExpr.norm (PolyQuaternionExpr.mul
      (PolyQuaternionExpr.coordinate 0) (PolyQuaternionExpr.coordinate 4)))
    (.mul (PolyQuaternionExpr.norm (PolyQuaternionExpr.coordinate 0))
      (PolyQuaternionExpr.norm (PolyQuaternionExpr.coordinate 4)))
    (by decide) (normEnvironment p q)

theorem polyQuaternionNorm_conj (q : PolyQuaternion) :
    RatPolyCoeffEqv (polyQuaternionNorm (PolyQuaternion.conj q))
      (polyQuaternionNorm q) := by
  exact coeffEvalExpr_eqv_of_normalize_eq
    (PolyQuaternionExpr.norm (PolyQuaternionExpr.conj (PolyQuaternionExpr.coordinate 0)))
    (PolyQuaternionExpr.norm (PolyQuaternionExpr.coordinate 0))
    (by decide) (normEnvironment q q)

theorem polyQuaternionNorm_one :
    RatPolyCoeffEqv (polyQuaternionNorm PolyQuaternion.one) polyOne := by
  exact ((RatPolyCoeffEqv.mul_one _).add
    ((RatPolyCoeffEqv.mul_zero_left _).add
      ((RatPolyCoeffEqv.mul_zero_left _).add (RatPolyCoeffEqv.mul_zero_left _)))).trans
    (RatPolyCoeffEqv.add_zero _)

/-- Unit norms compose on the SAME product-Haar carrier with arbitrary
insertions, without requiring the two factors to use disjoint links. -/
theorem haarNorm_mul {blocks : Nat} {p q : PolyQuaternion}
    (hp : QuaternionHaarCarrierEqv blocks (polyQuaternionNorm p) polyOne)
    (hq : QuaternionHaarCarrierEqv blocks (polyQuaternionNorm q) polyOne) :
    QuaternionHaarCarrierEqv blocks (polyQuaternionNorm (PolyQuaternion.mul p q)) polyOne :=
  QuaternionHaarCarrierEqv.trans (RatPolyCoeffEqv.haarCarrier (polyQuaternionNorm_mul p q))
    (QuaternionHaarCarrierEqv.trans (QuaternionHaarCarrierEqv.mul hp hq)
      (RatPolyCoeffEqv.haarCarrier (RatPolyCoeffEqv.mul_one polyOne)))

theorem haarNorm_fold {α : Type} {blocks : Nat} (factor : α → PolyQuaternion)
    (entries : List α) (hentries : ∀ entry ∈ entries,
      QuaternionHaarCarrierEqv blocks (polyQuaternionNorm (factor entry)) polyOne)
    (initial : PolyQuaternion)
    (hinitial : QuaternionHaarCarrierEqv blocks (polyQuaternionNorm initial) polyOne) :
    QuaternionHaarCarrierEqv blocks
      (polyQuaternionNorm (entries.foldl (fun total entry => PolyQuaternion.mul total (factor entry)) initial))
      polyOne := by
  induction entries generalizing initial with
  | nil => exact hinitial
  | cons entry entries ih =>
    exact ih (fun e he => hentries e (List.mem_cons_of_mem entry he))
      (PolyQuaternion.mul initial (factor entry))
      (haarNorm_mul hinitial (hentries entry (List.mem_cons_self)))

theorem haarNorm_coordinate {blocks block : Nat} (hblock : block < blocks) :
    QuaternionHaarCarrierEqv blocks
      (polyQuaternionNorm (PolyQuaternion.coordinateVariable block)) polyOne :=
  QuaternionHaarCarrierEqv.trans
    (RatPolyCoeffEqv.haarCarrier (polyQuaternionNorm_coordinateVariable block))
    (quaternionRadiusPolynomial_carrier_one hblock)

/-- Every original slab link has Haar-unit norm, including its reversed
orientation. Membership ensures the identity fallback is not used. -/
theorem haarNorm_orientedSlabLink {extent : Nat} (entry : OrientedBF4Link)
    (hlink : entry.link ∈ boundaryCompleteSlabLinks extent) :
    QuaternionHaarCarrierEqv (boundaryCompleteSlabLinks extent).length
      (polyQuaternionNorm (orientedCorrectedSlabLinkPolynomial extent entry)) polyOne := by
  have hc := haarNorm_coordinate (List.idxOf_lt_length_of_mem hlink)
  unfold orientedCorrectedSlabLinkPolynomial
  rw [correctedSlabLinkPolynomial_of_mem hlink]
  split
  · exact QuaternionHaarCarrierEqv.trans
      (RatPolyCoeffEqv.haarCarrier (polyQuaternionNorm_conj _)) hc
  · exact hc

/-- The literal noncommutative plaquette word has Haar-unit norm for every
extent. All spectator polynomials are retained by the carrier relation. -/
theorem haarNorm_slabPlaquette {extent : Nat} {face : Z4Plaq}
    (hface : face ∈ boundaryCompleteSlabPlaquettes extent) :
    QuaternionHaarCarrierEqv (boundaryCompleteSlabLinks extent).length
      (polyQuaternionNorm (correctedSlabPlaquettePolynomial extent face)) polyOne := by
  exact haarNorm_fold (orientedCorrectedSlabLinkPolynomial extent)
    (orientedPlaquetteBoundary face)
    (fun entry hentry => haarNorm_orientedSlabLink entry
      (orientedPlaquetteBoundary_link_mem_slab hface hentry))
    PolyQuaternion.one (RatPolyCoeffEqv.haarCarrier polyQuaternionNorm_one)

/-- A field-preserving recoding of the ORIGINAL slab plaquette, not a new
holonomy or a commuting replacement of its ordered link word. -/
def slabPlaquetteRepresentationQuaternion (extent : Nat) (face : Z4Plaq) : RatPolyQuaternion :=
  let q := correctedSlabPlaquettePolynomial extent face
  ⟨q.scalar, q.iPart, q.jPart, q.kPart⟩

/-- At every extent and spin, the actual symmetric-power trace equals the
original plaquette character under EVERY polynomial Haar insertion. The
imaginary trace component vanishes in that same carrier. -/
theorem slabPlaquette_trace_haar_character {extent : Nat} {face : Z4Plaq}
    (hface : face ∈ boundaryCompleteSlabPlaquettes extent) (spin : Nat) :
    QuaternionHaarCarrierEqv (boundaryCompleteSlabLinks extent).length
      (polynomialTrace (slabPlaquetteRepresentationQuaternion extent face) spin).1
      (characterPolynomial (correctedSlabPlaquettePolynomial extent face).scalar spin) ∧
    QuaternionHaarCarrierEqv (boundaryCompleteSlabLinks extent).length
      (polynomialTrace (slabPlaquetteRepresentationQuaternion extent face) spin).2 polyZero :=
  polynomialTrace_haar_character (slabPlaquetteRepresentationQuaternion extent face)
    (haarNorm_slabPlaquette hface) spin

end YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace

#print axioms YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace.polyQuaternionNorm_mul
#print axioms YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace.polyQuaternionNorm_conj
#print axioms YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace.polyQuaternionNorm_one
#print axioms YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace.haarNorm_mul
#print axioms YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace.haarNorm_fold
#print axioms YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace.haarNorm_coordinate
#print axioms YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace.haarNorm_orientedSlabLink
#print axioms YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace.haarNorm_slabPlaquette
#print axioms YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace.slabPlaquetteRepresentationQuaternion
#print axioms YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace.slabPlaquette_trace_haar_character
