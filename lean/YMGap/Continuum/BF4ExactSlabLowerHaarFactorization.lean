/-
# Reflected Haar pairings of literal lower-half polynomials

The physical odd slab reflection sends lower link blocks to upper link
blocks. A lower-local polynomial and its literal reflected polynomial
therefore have disjoint quaternion-block dependence. The original product
Haar law factors, and reflection invariance identifies both integrals.

This proves a reflected pairing is an explicit rational square, at every
odd extent. It does not identify arbitrary input polynomials as lower-local.
That geometric obligation for the actual global channels is kept separate.
-/

import YMGap.Continuum.SU2QuaternionDisjointBlockHaarFactorization

namespace YMGap.Continuum.BF4ExactSlabLowerHaarFactorization

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionBlockLocality
open YMGap.Continuum.SU2QuaternionDisjointBlockHaarFactorization

def LowerBlock (half block : Nat) : Prop :=
  linkHalfSide half (correctedSlabLinkAt (centralExtent half) block) = .lower

def UpperBlock (half block : Nat) : Prop :=
  linkHalfSide half (correctedSlabLinkAt (centralExtent half) block) = .upper

def LowerLocal (half : Nat) (p : RatPoly) : Prop :=
  BlockLocal (boundaryCompleteSlabLinks (centralExtent half)).length (LowerBlock half) p

theorem blockSide_reflection (half : Nat) {block : Nat}
    (hb : block < (boundaryCompleteSlabLinks (centralExtent half)).length) :
    linkHalfSide half (correctedSlabLinkAt (centralExtent half)
      (correctedSlabLinkReflectBlock (centralExtent half) block)) =
      flipSide (linkHalfSide half (correctedSlabLinkAt (centralExtent half) block)) := by
  have hm : block ∈ correctedSlabLinkBlocks (centralExtent half) := List.mem_range.mpr hb
  rw [correctedSlabLinkAt_reflectBlock hm]
  exact centralSlabLink_reflection_side (correctedSlabLinkAt_mem hm)

theorem lower_reflection_upper {half : Nat} {p : RatPoly} (h : LowerLocal half p) :
    BlockLocal (boundaryCompleteSlabLinks (centralExtent half)).length (UpperBlock half)
      (reflectCorrectedSlabPolynomial (centralExtent half) p) := by
  apply BlockLocal.signSelected
  apply h.reindex (correctedSlabQuaternionBlockInvolution (centralExtent half))
  intro block hb hl
  have hs := blockSide_reflection half hb
  change linkHalfSide half (correctedSlabLinkAt (centralExtent half)
    (correctedSlabLinkReflectBlock (centralExtent half) block)) = .lower at hl
  rw [hl] at hs
  unfold UpperBlock
  cases he : linkHalfSide half (correctedSlabLinkAt (centralExtent half) block) <;>
    rw [he] at hs
  · cases hs
  · cases hs

theorem lower_reflection_disjoint {half : Nat} {p : RatPoly} (h : LowerLocal half p) :
    BlockDisjoint (boundaryCompleteSlabLinks (centralExtent half)).length
      (reflectCorrectedSlabPolynomial (centralExtent half) p) p := by
  have hu := lower_reflection_upper h
  intro s hs t ht block hb
  haveI : Decidable (LowerBlock half block) := inferInstanceAs
    (Decidable (linkHalfSide half (correctedSlabLinkAt (centralExtent half) block) = .lower))
  by_cases hl : LowerBlock half block
  · apply Or.inl
    apply hu s hs block hb
    intro hup
    change linkHalfSide half (correctedSlabLinkAt (centralExtent half) block) = .upper at hup
    change linkHalfSide half (correctedSlabLinkAt (centralExtent half) block) = .lower at hl
    rw [hl] at hup
    cases hup
  · exact Or.inr (h t ht block hb hl)

/-- SAME original Haar law and literal reflection, with the witness square
given by the polynomial's own rational Haar integral. -/
theorem lower_reflected_haar_square {half : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks (centralExtent half)).length p)
    (hl : LowerLocal half p) :
    (quaternionHaar (boundaryCompleteSlabLinks (centralExtent half)).length
      (polyMul (reflectCorrectedSlabPolynomial (centralExtent half) p) p)).eqv
      (quaternionHaar (boundaryCompleteSlabLinks (centralExtent half)).length p *
        quaternionHaar (boundaryCompleteSlabLinks (centralExtent half)).length p) :=
  Q'.eqv_trans _ _ _
    (haar_product (reflectCorrectedSlabPolynomial_support (centralExtent half) p) hp (lower_reflection_disjoint hl))
    (Q'.mul_eqv_congr_right _ _ _ (quaternionHaar_reflectCorrectedSlabPolynomial (centralExtent half) p hp))

theorem lower_reflected_haar_nonnegative {half : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks (centralExtent half)).length p)
    (hl : LowerLocal half p) :
    (0 : Q') ≤ quaternionHaar (boundaryCompleteSlabLinks (centralExtent half)).length
      (polyMul (reflectCorrectedSlabPolynomial (centralExtent half) p) p) :=
  Q'.le_trans' _ _ _ (SumOfSquares.q_mul_self_nonneg _)
    (Q'.le_of_eqv (Q'.eqv_symm (lower_reflected_haar_square hp hl)))

end YMGap.Continuum.BF4ExactSlabLowerHaarFactorization

#print axioms YMGap.Continuum.BF4ExactSlabLowerHaarFactorization.LowerBlock
#print axioms YMGap.Continuum.BF4ExactSlabLowerHaarFactorization.UpperBlock
#print axioms YMGap.Continuum.BF4ExactSlabLowerHaarFactorization.LowerLocal
#print axioms YMGap.Continuum.BF4ExactSlabLowerHaarFactorization.blockSide_reflection
#print axioms YMGap.Continuum.BF4ExactSlabLowerHaarFactorization.lower_reflection_upper
#print axioms YMGap.Continuum.BF4ExactSlabLowerHaarFactorization.lower_reflection_disjoint
#print axioms YMGap.Continuum.BF4ExactSlabLowerHaarFactorization.lower_reflected_haar_square
#print axioms YMGap.Continuum.BF4ExactSlabLowerHaarFactorization.lower_reflected_haar_nonnegative
