/-
# Constructed conditional square for every one-sided polynomial on the even slab

Split each original monomial into its strict-lower and fixed-slice exponents.
The split is computed, preserves the original coefficients and reproduces the
original polynomial on the declared quaternion carrier. Applying the proved
site factorization returns a boundary-local polynomial C(p) with

    H(theta(p) * p) = H(C(p) * C(p)) >= 0.

This covers arbitrary signed polynomial dependence on both the lower and
shared spatial links; no separated-expansion or boundary-reflection witness
is supplied by the caller. Support outside the declared finite slab is never
silently discarded. The finite product Haar and literal slab reflection are
the existing ones.

This is the unweighted conditional-square calculation. It does not yet
identify the full heat-weighted site form with the existing thermodynamic
geometric T1 pairing. It supplies no actual T2 range approximation, time-zero
modulus, spacing-uniform mass or continuum/Clay closure.
-/

import YMGap.Continuum.BF4ExactSlabSiteBoundaryReflection

namespace YMGap.Continuum.BF4ExactSlabSiteConditionalSquare

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactSlabSelectedFaceCanonicalWord
open YMGap.Continuum.BF4ExactSlabSiteHaarFactorization
open YMGap.Continuum.BF4ExactSlabSiteBoundaryReflection
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarPolynomialPositivity
open YMGap.Continuum.SU2QuaternionBlockLocality
open YMGap.Continuum.SU2QuaternionHeadSubstitutionPrefix
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenCrossPlaneGeometry

local infix:50 " ≈ " => Q'.eqv

/-- Allows the shared slice, but no strict-upper coordinates. -/
def OneSided (radius : Nat) (p : RatPoly) : Prop :=
  BlockLocal (blockCount radius) (fun b => blockSide radius b ≠ .upper) p

def mask (radius : Nat) (side : CrossPlaneSide) (m : List Nat) : List Nat :=
  List.ofFn (fun i : Fin (4 * blockCount radius) =>
    if blockSide radius (i.val/4) = side then exponentAt m i.val else 0)

theorem mask_length (radius : Nat) (side : CrossPlaneSide) (m : List Nat) :
    (mask radius side m).length = 4 * blockCount radius := List.length_ofFn

theorem mask_exponent (radius : Nat) (side : CrossPlaneSide) (m : List Nat)
    {i : Nat} (hi : i < 4 * blockCount radius) :
    exponentAt (mask radius side m) i =
      if blockSide radius (i/4) = side then exponentAt m i else 0 := by
  unfold exponentAt
  rw [← List.getElem_eq_getD (l := mask radius side m) (i := i)
    (h := by rw [mask_length]; exact hi) 0]
  exact List.getElem_ofFn (h := by rw [List.length_ofFn]; exact hi)

theorem masked_supported (radius : Nat) (side : CrossPlaneSide) (m : List Nat) (c : Q') :
    SupportedQuaternionBlocks (blockCount radius) [(mask radius side m,c)] := by
  intro t ht
  have he := List.mem_singleton.mp ht
  subst t
  exact Nat.le_of_eq (mask_length radius side m)

theorem masked_local (radius : Nat) (side : CrossPlaneSide) (m : List Nat) (c : Q') :
    Local radius side [(mask radius side m,c)] := by
  intro t ht b hb hn i hi
  have he := List.mem_singleton.mp ht
  subst t
  rw [mask_exponent radius side m (by omega), show (4*b+i)/4=b by omega, if_neg hn]

/-- The term is data; only its upper-block vanishing is a proof field. -/
structure OneSidedTerm (radius : Nat) where
  term : RatTerm
  upper_zero : ∀ b, b < blockCount radius → blockSide radius b = .upper → BlockZero term.1 b

def lowerFactor {radius : Nat} (t : OneSidedTerm radius) : RatPoly :=
  [(mask radius .lower t.term.1,t.term.2)]

def boundaryFactor {radius : Nat} (t : OneSidedTerm radius) : RatPoly :=
  [(mask radius .fixed t.term.1,1)]

theorem term_split {radius : Nat} (t : OneSidedTerm radius) :
    QuaternionPrefixPolynomialEqv (blockCount radius)
      (polyMul (lowerFactor t) (boundaryFactor t)) [t.term] := by
  apply QuaternionPrefixPolynomialEqv.cons
  · constructor
    · exact Q'.mul_one_eqv _
    · intro i hi
      change exponentAt (monoMul (mask radius .lower t.term.1) (mask radius .fixed t.term.1)) i = _
      rw [exponentAt_monoMul, mask_exponent radius .lower t.term.1 hi, mask_exponent radius .fixed t.term.1 hi]
      cases hs : blockSide radius (i/4) <;>
        simp only [reduceCtorEq, ↓reduceIte, Nat.zero_add, Nat.add_zero]
      have hz := t.upper_zero (i/4) (by omega) hs (i%4) (Nat.mod_lt _ (by decide))
      rw [show 4*(i/4)+i%4=i by omega] at hz
      exact hz.symm
  · exact .nil

/-- Finite source-derived pieces, with no search or selected representatives. -/
def pieces (radius : Nat) : (p : RatPoly) → OneSided radius p → List (OneSidedTerm radius)
  | [], _ => []
  | t :: p, hp => ⟨t, fun b hb hu => hp t List.mem_cons_self b hb (fun hn => hn hu)⟩ ::
      pieces radius p (fun s hs => hp s (List.mem_cons_of_mem t hs))

theorem pieces_pin (radius : Nat) : ∀ (p : RatPoly) (hp : OneSided radius p),
    QuaternionPrefixPolynomialEqv (blockCount radius)
      (lowerSum lowerFactor boundaryFactor (pieces radius p hp)) p
  | [], _ => .nil
  | t :: p, hp => (term_split ⟨t, fun b hb hu => hp t List.mem_cons_self b hb (fun hn => hn hu)⟩).append
      (pieces_pin radius p (fun s hs => hp s (List.mem_cons_of_mem t hs)))

/-- The computed boundary polynomial is the witness square, not just a number. -/
def conditionalPolynomial (radius : Nat) (p : RatPoly) (hp : OneSided radius p) : RatPoly :=
  boundarySum radius lowerFactor boundaryFactor (pieces radius p hp)

theorem conditional_supported (radius : Nat) (p : RatPoly) (hp : OneSided radius p) :
    SupportedQuaternionBlocks (blockCount radius) (conditionalPolynomial radius p hp) :=
  boundarySum_supported radius lowerFactor boundaryFactor
    (fun t => masked_supported radius .fixed t.term.1 1) _

theorem conditional_local (radius : Nat) (p : RatPoly) (hp : OneSided radius p) :
    Local radius .fixed (conditionalPolynomial radius p hp) :=
  boundarySum_local radius lowerFactor boundaryFactor
    (fun t => masked_local radius .fixed t.term.1 1) _

/-- Exact identity for every ORIGINAL supported one-sided polynomial. -/
theorem conditional_square (radius : Nat) (p : RatPoly) (hp : OneSided radius p)
    (hs : SupportedQuaternionBlocks (blockCount radius) p) :
    quaternionHaar (blockCount radius)
      (polyMul (reflectCorrectedSlabPolynomial (adjacentEvenExtent radius) p) p) ≈
      quaternionHaar (blockCount radius)
        (polyMul (conditionalPolynomial radius p hp) (conditionalPolynomial radius p hp)) := by
  let xs := pieces radius p hp
  let P := lowerSum lowerFactor boundaryFactor xs
  have hP : SupportedQuaternionBlocks (blockCount radius) P :=
    lowerSum_supported radius lowerFactor boundaryFactor
      (fun t => masked_supported radius .lower t.term.1 t.term.2)
      (fun t => masked_supported radius .fixed t.term.1 1) xs
  have hi := prefix_symm (pieces_pin radius p hp)
  have hr := (QuaternionPrefixPolynomialEqv.reindex
    (correctedSlabQuaternionBlockInvolution (adjacentEvenExtent radius)) hi).signSelected
    (correctedSlabTimeVectorCoordinate (adjacentEvenExtent radius))
  have he : quaternionHaar (blockCount radius)
      (polyMul (reflectCorrectedSlabPolynomial (adjacentEvenExtent radius) p) p) ≈
      quaternionHaar (blockCount radius)
        (polyMul (reflectCorrectedSlabPolynomial (adjacentEvenExtent radius) P) P) :=
    (PaddedPolynomialCoeffEqv.of_prefix (hr.mul hi)).haar
      (supported_polyMul (reflectCorrectedSlabPolynomial_support _ _) hs)
      (supported_polyMul (reflectCorrectedSlabPolynomial_support _ _) hP)
  exact Q'.eqv_trans _ _ _ he (site_reflected_square radius lowerFactor boundaryFactor
    (fun t => masked_supported radius .lower t.term.1 t.term.2)
    (fun t => masked_supported radius .fixed t.term.1 1)
    (fun t => masked_local radius .lower t.term.1 t.term.2)
    (fun t => masked_local radius .fixed t.term.1 1) xs)

theorem one_sided_reflection_nonnegative (radius : Nat) (p : RatPoly) (hp : OneSided radius p)
    (hs : SupportedQuaternionBlocks (blockCount radius) p) :
    (0 : Q') ≤ quaternionHaar (blockCount radius)
      (polyMul (reflectCorrectedSlabPolynomial (adjacentEvenExtent radius) p) p) :=
  Q'.le_trans' _ _ _ (quaternionHaar_square_nonnegative _ _ (conditional_supported radius p hp))
    (Q'.ge_of_eqv (conditional_square radius p hp hs))

end YMGap.Continuum.BF4ExactSlabSiteConditionalSquare

#print axioms YMGap.Continuum.BF4ExactSlabSiteConditionalSquare.OneSided
#print axioms YMGap.Continuum.BF4ExactSlabSiteConditionalSquare.mask
#print axioms YMGap.Continuum.BF4ExactSlabSiteConditionalSquare.mask_length
#print axioms YMGap.Continuum.BF4ExactSlabSiteConditionalSquare.mask_exponent
#print axioms YMGap.Continuum.BF4ExactSlabSiteConditionalSquare.masked_supported
#print axioms YMGap.Continuum.BF4ExactSlabSiteConditionalSquare.masked_local
#print axioms YMGap.Continuum.BF4ExactSlabSiteConditionalSquare.lowerFactor
#print axioms YMGap.Continuum.BF4ExactSlabSiteConditionalSquare.boundaryFactor
#print axioms YMGap.Continuum.BF4ExactSlabSiteConditionalSquare.term_split
#print axioms YMGap.Continuum.BF4ExactSlabSiteConditionalSquare.pieces
#print axioms YMGap.Continuum.BF4ExactSlabSiteConditionalSquare.pieces_pin
#print axioms YMGap.Continuum.BF4ExactSlabSiteConditionalSquare.conditionalPolynomial
#print axioms YMGap.Continuum.BF4ExactSlabSiteConditionalSquare.conditional_supported
#print axioms YMGap.Continuum.BF4ExactSlabSiteConditionalSquare.conditional_local
#print axioms YMGap.Continuum.BF4ExactSlabSiteConditionalSquare.conditional_square
#print axioms YMGap.Continuum.BF4ExactSlabSiteConditionalSquare.one_sided_reflection_nonnegative
