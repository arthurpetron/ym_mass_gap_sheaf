/-
# The four-square certificate for 1 + the ORIGINAL scalar holonomy

Unit norm is used as an arbitrary-insertion Haar relation, not as a
pointwise substitution. Thus the certificate remains valid with every
other face polynomial present. The actual slab plaquette support and
Haar-unit norm discharge its hypotheses at every physical face and extent.
-/

import YMGap.Continuum.QuaternionHaarSquareCertificate
import YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace

namespace YMGap.Continuum.QuaternionHaarUnitScalarSquare

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.ClusterCount4DProgress

/-- Syntactic coordinate support, not an analytic positivity hypothesis. -/
structure Supported (blocks : Nat) (p : PolyQuaternion) : Prop where
  scalar : SupportedQuaternionBlocks blocks p.scalar
  iPart : SupportedQuaternionBlocks blocks p.iPart
  jPart : SupportedQuaternionBlocks blocks p.jPart
  kPart : SupportedQuaternionBlocks blocks p.kPart

private theorem supported_zero (blocks : Nat) : SupportedQuaternionBlocks blocks polyZero := by
  intro t ht
  exact False.elim (List.not_mem_nil ht)

private theorem supported_neg {blocks : Nat} {p : RatPoly} (hp : SupportedQuaternionBlocks blocks p) :
    SupportedQuaternionBlocks blocks (polyNeg p) := by
  intro t ht
  obtain ⟨s, hs, he⟩ := List.mem_map.mp ht
  rw [← he]
  exact hp s hs

private theorem supported_var {blocks coordinate : Nat} (h : coordinate < 4 * blocks) :
    SupportedQuaternionBlocks blocks (polyVar coordinate) := by
  intro t ht
  have he := List.mem_singleton.mp ht
  subst t
  simp only [varMono, List.length_append, List.length_replicate, List.length_singleton]
  omega

theorem Supported.one (blocks : Nat) : Supported blocks PolyQuaternion.one :=
  ⟨supported_one blocks, supported_zero blocks, supported_zero blocks, supported_zero blocks⟩

theorem Supported.coordinate {blocks block : Nat} (h : block < blocks) :
    Supported blocks (PolyQuaternion.coordinateVariable block) := by
  constructor <;> apply supported_var <;> omega

theorem Supported.conj {blocks : Nat} {p : PolyQuaternion} (hp : Supported blocks p) :
    Supported blocks (PolyQuaternion.conj p) :=
  ⟨hp.scalar, supported_neg hp.iPart, supported_neg hp.jPart, supported_neg hp.kPart⟩

theorem Supported.mul {blocks : Nat} {p q : PolyQuaternion} (hp : Supported blocks p) (hq : Supported blocks q) :
    Supported blocks (PolyQuaternion.mul p q) := by
  constructor <;> simp only [PolyQuaternion.mul]
  all_goals repeat' first
    | exact hp.scalar | exact hp.iPart | exact hp.jPart | exact hp.kPart
    | exact hq.scalar | exact hq.iPart | exact hq.jPart | exact hq.kPart
    | apply supported_add | apply supported_neg | apply supported_polyMul

theorem supported_slabLink (extent : Nat) (link : Z4Link) :
    Supported (boundaryCompleteSlabLinks extent).length (correctedSlabLinkPolynomial extent link) := by
  by_cases h : link ∈ boundaryCompleteSlabLinks extent
  · rw [correctedSlabLinkPolynomial_of_mem h]
    exact Supported.coordinate (List.idxOf_lt_length_of_mem h)
  · rw [correctedSlabLinkPolynomial_of_not_mem h]
    exact Supported.one _

private theorem supported_orientedLink (extent : Nat) (entry : OrientedBF4Link) :
    Supported (boundaryCompleteSlabLinks extent).length (orientedCorrectedSlabLinkPolynomial extent entry) := by
  unfold orientedCorrectedSlabLinkPolynomial
  split
  · exact (supported_slabLink extent entry.link).conj
  · exact supported_slabLink extent entry.link

private theorem supported_fold (extent : Nat) : ∀ (entries : List OrientedBF4Link) (total : PolyQuaternion),
    Supported (boundaryCompleteSlabLinks extent).length total →
    Supported (boundaryCompleteSlabLinks extent).length
      (entries.foldl (fun p entry => PolyQuaternion.mul p (orientedCorrectedSlabLinkPolynomial extent entry)) total)
  | [], _, h => h
  | e :: es, _, h => supported_fold extent es _ (h.mul (supported_orientedLink extent e))

/-- Actual ordered slab plaquette; all quaternion components are supported. -/
theorem supported_slabPlaquette (extent : Nat) (face : Z4Plaq) :
    Supported (boundaryCompleteSlabLinks extent).length (correctedSlabPlaquettePolynomial extent face) :=
  supported_fold extent (orientedPlaquetteBoundary face) PolyQuaternion.one (Supported.one _)

def oneAddScalar (p : PolyQuaternion) : RatPoly := polyAdd polyOne p.scalar

/-- The four literal square channels, with their original shared variables. -/
def squareSum (p : PolyQuaternion) : RatPoly :=
  polyAdd (polyMul (oneAddScalar p) (oneAddScalar p))
    (polyAdd (polyMul p.iPart p.iPart) (polyAdd (polyMul p.jPart p.jPart) (polyMul p.kPart p.kPart)))

private def sq (p : PolyExpr) : PolyExpr := .mul p p
private def normExpr : PolyExpr := .add (sq (.var 1))
  (.add (sq (.var 2)) (.add (sq (.var 3)) (sq (.var 4))))
private def sumExpr : PolyExpr := .add (sq (.add (.var 0) (.var 1)))
  (.add (sq (.var 2)) (.add (sq (.var 3)) (sq (.var 4))))
private def expandedExpr : PolyExpr := .add
  (.add (sq (.var 0)) (.add (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))) normExpr
private def env (p : PolyQuaternion) : Nat → RatPoly
  | 0 => polyOne | 1 => p.scalar | 2 => p.iPart | 3 => p.jPart | 4 => p.kPart | _ => polyZero

/-- Coefficientwise ring expansion, before the Haar-unit norm is used. -/
theorem squareSum_expansion (p : PolyQuaternion) :
    RatPolyCoeffEqv (squareSum p)
      (polyAdd (polyAdd polyOne (polyAdd p.scalar p.scalar)) (polyQuaternionNorm p)) := by
  have h := coeffEvalExpr_eqv_of_normalize_eq sumExpr expandedExpr (by decide) (env p)
  exact h.trans (((RatPolyCoeffEqv.one_mul polyOne).add
    ((RatPolyCoeffEqv.one_mul p.scalar).add (RatPolyCoeffEqv.one_mul p.scalar))).add
      (RatPolyCoeffEqv.refl (polyQuaternionNorm p)))

/-- Two copies of 1+scalar equal the four squares under EVERY insertion. -/
theorem twice_oneAddScalar_haar {blocks : Nat} {p : PolyQuaternion}
    (hnorm : HaarCarrierEqv blocks (polyQuaternionNorm p) polyOne) :
    HaarCarrierEqv blocks (polyAdd (oneAddScalar p) (oneAddScalar p)) (squareSum p) := by
  have h1 := HaarCarrierEqv.trans (RatPolyCoeffEqv.haarCarrier (squareSum_expansion p))
    (HaarCarrierEqv.add (HaarCarrierEqv.refl blocks _) hnorm)
  have h2 : RatPolyCoeffEqv
      (polyAdd (polyAdd polyOne (polyAdd p.scalar p.scalar)) polyOne)
      (polyAdd (oneAddScalar p) (oneAddScalar p)) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.add (.add (.var 0) (.add (.var 1) (.var 1))) (.var 0))
      (.add (.add (.var 0) (.var 1)) (.add (.var 0) (.var 1))) (by decide) (env p)
  exact (HaarCarrierEqv.trans h1 (RatPolyCoeffEqv.haarCarrier h2)).symm

/-- The explicit square certificate for 1+scalar uses positive rational
weights half; no square root or pointwise-to-Haar principle is assumed. -/
def oneAddScalar_certificate {blocks : Nat} {p : PolyQuaternion}
    (hp : Supported blocks p) (hnorm : HaarCarrierEqv blocks (polyQuaternionNorm p) polyOne) :
    Certificate blocks (oneAddScalar p) := by
  let C : Certificate blocks (squareSum p) :=
    .add (.square (oneAddScalar p) (supported_add (supported_one blocks) hp.scalar))
      (.add (.square p.iPart hp.iPart) (.add (.square p.jPart hp.jPart) (.square p.kPart hp.kPart)))
  have he : RatPolyCoeffEqv
      (polySmul HalfPow.half (polyAdd (oneAddScalar p) (oneAddScalar p))) (oneAddScalar p) :=
    (RatPolyCoeffEqv.smul_add _ _ _).trans
      ((RatPolyCoeffEqv.add_smul_same _ _ _).trans
        ((RatPolyCoeffEqv.smul_coefficient (by decide) _).trans (RatPolyCoeffEqv.one_smul _)))
  exact .transport
    (HaarCarrierEqv.trans (RatPolyCoeffEqv.haarCarrier he.symm)
      (HaarCarrierEqv.smul HalfPow.half (twice_oneAddScalar_haar hnorm)))
    (.smul HalfPow.half HalfPow.half_nonneg C)

/-- An unconditional certificate for EVERY physical original slab face. -/
def slab_oneAddScalar_certificate {extent : Nat} {face : Z4Plaq}
    (hface : face ∈ boundaryCompleteSlabPlaquettes extent) :
    Certificate (boundaryCompleteSlabLinks extent).length
      (oneAddScalar (correctedSlabPlaquettePolynomial extent face)) :=
  oneAddScalar_certificate (supported_slabPlaquette extent face) (haarNorm_slabPlaquette hface)

/-- The original scalar shift remains positive under an arbitrary supported
square insertion. This is an actual Haar inequality, not an evaluation bound. -/
theorem slab_oneAddScalar_square_insertion_nonnegative {extent : Nat} {face : Z4Plaq}
    (hface : face ∈ boundaryCompleteSlabPlaquettes extent) (r : RatPoly)
    (hr : SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length r) :
    (0 : Q') ≤ BF4GeometricHaarMehlerProjection.quaternionHaar (boundaryCompleteSlabLinks extent).length
      (polyMul (polyMul r r) (oneAddScalar (correctedSlabPlaquettePolynomial extent face))) :=
  (slab_oneAddScalar_certificate hface).square_insertion_nonnegative r hr

end YMGap.Continuum.QuaternionHaarUnitScalarSquare

#print axioms YMGap.Continuum.QuaternionHaarUnitScalarSquare.Supported.one
#print axioms YMGap.Continuum.QuaternionHaarUnitScalarSquare.Supported.coordinate
#print axioms YMGap.Continuum.QuaternionHaarUnitScalarSquare.Supported.conj
#print axioms YMGap.Continuum.QuaternionHaarUnitScalarSquare.Supported.mul
#print axioms YMGap.Continuum.QuaternionHaarUnitScalarSquare.supported_slabLink
#print axioms YMGap.Continuum.QuaternionHaarUnitScalarSquare.supported_slabPlaquette
#print axioms YMGap.Continuum.QuaternionHaarUnitScalarSquare.squareSum_expansion
#print axioms YMGap.Continuum.QuaternionHaarUnitScalarSquare.twice_oneAddScalar_haar
#print axioms YMGap.Continuum.QuaternionHaarUnitScalarSquare.oneAddScalar_certificate
#print axioms YMGap.Continuum.QuaternionHaarUnitScalarSquare.slab_oneAddScalar_certificate
#print axioms YMGap.Continuum.QuaternionHaarUnitScalarSquare.slab_oneAddScalar_square_insertion_nonnegative
