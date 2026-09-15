/-
# Conditional Haar factorization at the actual integer reflection slice

The strict lower and upper link sets are disjoint, but both halves can share
the fixed spatial links. Those fixed links must remain unintegrated. For a
finite separated polynomial sum P = sum_i L_i B_i, integrate only L_i and
retain B_i. The literal reflected Haar quadratic of P is the Haar square of
the resulting boundary polynomial, provided the displayed finite locality
and reflection certificates hold. Signed coefficients are allowed in L_i.

All geometry uses the existing boundary-complete even slab and its actual
orientation-correct reflection. This is an unweighted finite Haar identity,
not a replacement action or an OS norm comparison. Decomposing the original
heat-dressed observables into these pieces, retaining the fixed-slice heat
weight, and passing to the existing thermodynamic pairing remain separate.
Geometric T1 positivity, range density, time zero and Clay remain open.
-/

import YMGap.Continuum.BF4ExactSlabLowerHaarFactorization
import YMGap.Continuum.BF4ExactSlabAllExtentObservableReflection
import YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenCrossPlaneGeometry
import YMGap.Continuum.QuaternionHaarSquareCertificate

namespace YMGap.Continuum.BF4ExactSlabSiteHaarFactorization

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactSlabAllExtentObservableReflection
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabSpatialChannelReflection
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionArbitraryHaarPolynomialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarHomogenization
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.SU2QuaternionBlockLocality
open YMGap.Continuum.SU2QuaternionDisjointBlockHaarFactorization
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenCrossPlaneGeometry

local infix:50 " ≈ " => Q'.eqv

def blockCount (radius : Nat) : Nat :=
  (boundaryCompleteSlabLinks (adjacentEvenExtent radius)).length

def blockSide (radius block : Nat) : CrossPlaneSide :=
  adjacentEvenLinkSide radius (correctedSlabLinkAt (adjacentEvenExtent radius) block)

def Local (radius : Nat) (side : CrossPlaneSide) (p : RatPoly) : Prop :=
  BlockLocal (blockCount radius) (fun b => blockSide radius b = side) p

theorem blockSide_reflection (radius : Nat) {b : Nat} (hb : b < blockCount radius) :
    blockSide radius (correctedSlabLinkReflectBlock (adjacentEvenExtent radius) b) =
      flipSide (blockSide radius b) := by
  have hm := List.mem_range.mpr hb
  unfold blockSide
  rw [correctedSlabLinkAt_reflectBlock hm]
  exact adjacentEvenSlabLink_reflection_side (correctedSlabLinkAt_mem hm)

theorem lower_reflection_upper {radius : Nat} {p : RatPoly} (hp : Local radius .lower p) :
    Local radius .upper (reflectCorrectedSlabPolynomial (adjacentEvenExtent radius) p) := by
  apply BlockLocal.signSelected
  apply hp.reindex (correctedSlabQuaternionBlockInvolution (adjacentEvenExtent radius))
  intro b hb hl
  have hs := blockSide_reflection radius hb
  change blockSide radius (correctedSlabLinkReflectBlock (adjacentEvenExtent radius) b) = .lower at hl
  rw [hl] at hs
  cases he : blockSide radius b <;> rw [he] at hs
  · cases hs
  · cases hs

theorem local_disjoint {radius : Nat} {a b : CrossPlaneSide} (hab : a ≠ b)
    {p q : RatPoly} (hp : Local radius a p) (hq : Local radius b q) :
    BlockDisjoint (blockCount radius) p q := by
  intro s hs t ht k hk
  by_cases h : blockSide radius k = a
  · exact Or.inr (hq t ht k hk (fun he => hab (h.symm.trans he)))
  · exact Or.inl (hp s hs k hk h)

private theorem upper_disjoint_lower_fixed {radius : Nat} {u p b : RatPoly}
    (hu : Local radius .upper u) (hp : Local radius .lower p) (hb : Local radius .fixed b) :
    BlockDisjoint (blockCount radius) u (polyMul p b) := by
  intro s hs t ht k hk
  by_cases h : blockSide radius k = .upper
  · apply Or.inr
    obtain ⟨v, hv, ht⟩ := List.mem_flatMap.mp ht
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp ht
    intro c hc
    rw [SU2QuaternionRatPolyDifferential.exponentAt_monoMul,
      hp v hv k hk (by intro he; have hbad := h.symm.trans he; cases hbad) c hc,
      hb w hw k hk (by intro he; have hbad := h.symm.trans he; cases hbad) c hc]
  · exact Or.inl (hu s hs k hk h)

/-- Both strict halves are integrated; the shared slice is kept inside Haar. -/
theorem pairing_factor {radius : Nat} {p q b : RatPoly}
    (hp : SupportedQuaternionBlocks (blockCount radius) p)
    (hq : SupportedQuaternionBlocks (blockCount radius) q)
    (hb : SupportedQuaternionBlocks (blockCount radius) b)
    (lp : Local radius .lower p) (lq : Local radius .lower q) (lb : Local radius .fixed b) :
    quaternionHaar (blockCount radius)
      (polyMul (reflectCorrectedSlabPolynomial (adjacentEvenExtent radius) p) (polyMul q b)) ≈
      quaternionHaar (blockCount radius) p *
        (quaternionHaar (blockCount radius) q * quaternionHaar (blockCount radius) b) :=
  Q'.eqv_trans _ _ _
    (haar_product (reflectCorrectedSlabPolynomial_support _ _) (supported_polyMul hq hb)
      (upper_disjoint_lower_fixed (lower_reflection_upper lp) lq lb))
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (quaternionHaar_reflectCorrectedSlabPolynomial _ p hp))
      (Q'.mul_eqv_congr_left _ _ _ (haar_product hq hb (local_disjoint (by intro h; cases h) lq lb))))

def lowerSum {A : Type} (lower boundary : A → RatPoly) : List A → RatPoly
  | [] => polyZero
  | a :: xs => polyAdd (polyMul (lower a) (boundary a)) (lowerSum lower boundary xs)

def upperSum {A : Type} (radius : Nat) (lower boundary : A → RatPoly) : List A → RatPoly
  | [] => polyZero
  | a :: xs => polyAdd (polyMul (reflectCorrectedSlabPolynomial (adjacentEvenExtent radius) (lower a))
      (boundary a)) (upperSum radius lower boundary xs)

/-- Explicit boundary polynomial; no limit or representative choice. -/
def boundarySum {A : Type} (radius : Nat) (lower boundary : A → RatPoly) : List A → RatPoly
  | [] => polyZero
  | a :: xs => polyAdd (polySmul (quaternionHaar (blockCount radius) (lower a)) (boundary a))
      (boundarySum radius lower boundary xs)

private theorem haar_add_left (blocks : Nat) (a b c : RatPoly) :
    quaternionHaar blocks (polyMul (polyAdd a b) c) ≈
      quaternionHaar blocks (polyMul a c) + quaternionHaar blocks (polyMul b c) := by
  rw [polyMul_add_left_exact]
  exact quaternionHaar_append blocks _ _

private theorem haar_zero_left (blocks : Nat) (p : RatPoly) :
    quaternionHaar blocks (polyMul polyZero p) ≈ 0 := Q'.eqv_refl _

private theorem haar_zero_right (blocks : Nat) (p : RatPoly) :
    quaternionHaar blocks (polyMul p polyZero) ≈ 0 := by
  have h : polyMul p polyZero = polyZero := by
    induction p with
    | nil => rfl
    | cons s p ih => exact ih
  rw [h]
  exact Q'.eqv_refl _

private theorem factor_reorder (a b c d : RatPoly) :
    RatPolyCoeffEqv (polyMul (polyMul a b) (polyMul c d)) (polyMul a (polyMul c (polyMul b d))) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
    (.mul (.var 0) (.mul (.var 2) (.mul (.var 1) (.var 3)))) (by decide)
    (fun | 0 => a | 1 => b | 2 => c | _ => d)

private theorem scaled_pair (blocks : Nat) (a b : Q') (p q : RatPoly) :
    quaternionHaar blocks (polyMul (polySmul a p) (polySmul b q)) ≈
      a * (b * quaternionHaar blocks (polyMul p q)) := by
  exact Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_comm blocks _ _)
    (Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_smul_right blocks a _ _)
      (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_trans _ _ _
        (quaternionHaar_polyMul_comm blocks _ _) (quaternionHaar_polyMul_smul_right blocks b _ _))))

theorem separated_pair {radius : Nat} {p q b c : RatPoly}
    (hp : SupportedQuaternionBlocks (blockCount radius) p)
    (hq : SupportedQuaternionBlocks (blockCount radius) q)
    (hb : SupportedQuaternionBlocks (blockCount radius) b)
    (hc : SupportedQuaternionBlocks (blockCount radius) c)
    (lp : Local radius .lower p) (lq : Local radius .lower q)
    (lb : Local radius .fixed b) (lc : Local radius .fixed c) :
    quaternionHaar (blockCount radius)
      (polyMul (polyMul (reflectCorrectedSlabPolynomial (adjacentEvenExtent radius) p) b) (polyMul q c)) ≈
      quaternionHaar (blockCount radius)
        (polyMul (polySmul (quaternionHaar (blockCount radius) p) b)
          (polySmul (quaternionHaar (blockCount radius) q) c)) :=
  Q'.eqv_trans _ _ _ (haar_of_coeff_eqv _ (factor_reorder _ _ _ _))
    (Q'.eqv_trans _ _ _ (pairing_factor hp hq (supported_polyMul hb hc) lp lq (lb.mul lc))
      (Q'.eqv_symm (scaled_pair _ _ _ _ _)))

section FiniteSum

variable {A : Type} (radius : Nat) (lower boundary : A → RatPoly)
  (hl : ∀ a, SupportedQuaternionBlocks (blockCount radius) (lower a))
  (hb : ∀ a, SupportedQuaternionBlocks (blockCount radius) (boundary a))
  (ll : ∀ a, Local radius .lower (lower a))
  (lb : ∀ a, Local radius .fixed (boundary a))

include hl hb ll lb in
private theorem row_pair (a : A) : ∀ ys : List A,
    quaternionHaar (blockCount radius)
      (polyMul (polyMul (reflectCorrectedSlabPolynomial (adjacentEvenExtent radius) (lower a)) (boundary a))
        (lowerSum lower boundary ys)) ≈
      quaternionHaar (blockCount radius)
        (polyMul (polySmul (quaternionHaar (blockCount radius) (lower a)) (boundary a))
          (boundarySum radius lower boundary ys))
  | [] => Q'.eqv_trans _ _ _ (haar_zero_right _ _) (Q'.eqv_symm (haar_zero_right _ _))
  | b :: ys => Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_add_right _ _ _ _)
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
        (separated_pair (hl a) (hl b) (hb a) (hb b) (ll a) (ll b) (lb a) (lb b))
        (row_pair a ys)) (Q'.eqv_symm (quaternionHaar_polyMul_add_right _ _ _ _)))

include hl hb ll lb in
/-- The remaining boundary integral retains all mixed terms of a signed sum. -/
theorem sum_pairing : ∀ xs ys : List A,
    quaternionHaar (blockCount radius)
      (polyMul (upperSum radius lower boundary xs) (lowerSum lower boundary ys)) ≈
      quaternionHaar (blockCount radius)
        (polyMul (boundarySum radius lower boundary xs) (boundarySum radius lower boundary ys))
  | [], _ => Q'.eqv_refl _
  | a :: xs, ys => Q'.eqv_trans _ _ _ (haar_add_left _ _ _ _)
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
        (row_pair radius lower boundary hl hb ll lb a ys) (sum_pairing xs ys))
        (Q'.eqv_symm (haar_add_left _ _ _ _)))

include hl hb in
theorem lowerSum_supported : ∀ xs : List A,
    SupportedQuaternionBlocks (blockCount radius) (lowerSum lower boundary xs)
  | [] => fun _ h => False.elim (List.not_mem_nil h)
  | a :: xs => supported_add (supported_polyMul (hl a) (hb a)) (lowerSum_supported xs)

include hb in
theorem upperSum_supported : ∀ xs : List A,
    SupportedQuaternionBlocks (blockCount radius) (upperSum radius lower boundary xs)
  | [] => fun _ h => False.elim (List.not_mem_nil h)
  | a :: xs => supported_add (supported_polyMul (reflectCorrectedSlabPolynomial_support _ _) (hb a))
      (upperSum_supported xs)

include hb in
theorem boundarySum_supported : ∀ xs : List A,
    SupportedQuaternionBlocks (blockCount radius) (boundarySum radius lower boundary xs)
  | [] => fun _ h => False.elim (List.not_mem_nil h)
  | a :: xs => supported_add (by
      intro t ht
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
      exact hb a s hs) (boundarySum_supported xs)

include lb in
theorem boundarySum_local : ∀ xs : List A,
    Local radius .fixed (boundarySum radius lower boundary xs)
  | [] => BlockLocal.zero _ _
  | a :: xs => (lb a).smul _ |>.add (boundarySum_local xs)

/-- A finite reflection certificate on each shared-slice factor, not a
positivity or transfer hypothesis. -/
theorem lowerSum_reflection
    (br : ∀ a, ReflectionImage (adjacentEvenExtent radius) (boundary a) (boundary a)) :
    ∀ xs : List A, ReflectionImage (adjacentEvenExtent radius) (lowerSum lower boundary xs)
      (upperSum radius lower boundary xs)
  | [] => ReflectionImage.zero _
  | a :: xs => ((show ReflectionImage (adjacentEvenExtent radius) (lower a)
      (reflectCorrectedSlabPolynomial (adjacentEvenExtent radius) (lower a)) from .refl _ _).mul (br a)).add
        (lowerSum_reflection br xs)

include hl hb ll lb in
/-- SAME finite Haar law and literal orientation-correct slab reflection.
The witnessing square polynomial lives on the shared spatial slice. -/
theorem reflected_square
    (br : ∀ a, ReflectionImage (adjacentEvenExtent radius) (boundary a) (boundary a)) (xs : List A) :
    quaternionHaar (blockCount radius)
      (polyMul (reflectCorrectedSlabPolynomial (adjacentEvenExtent radius) (lowerSum lower boundary xs))
        (lowerSum lower boundary xs)) ≈
      quaternionHaar (blockCount radius)
        (polyMul (boundarySum radius lower boundary xs) (boundarySum radius lower boundary xs)) :=
  Q'.eqv_trans _ _ _
    ((PaddedPolynomialCoeffEqv.mul (lowerSum_reflection radius lower boundary br xs) (.refl _ _)).haar
      (supported_polyMul (reflectCorrectedSlabPolynomial_support _ _) (lowerSum_supported radius lower boundary hl hb xs))
      (supported_polyMul (upperSum_supported radius lower boundary hb xs) (lowerSum_supported radius lower boundary hl hb xs)))
    (sum_pairing radius lower boundary hl hb ll lb xs xs)

include hl hb ll lb in
theorem reflected_nonnegative
    (br : ∀ a, ReflectionImage (adjacentEvenExtent radius) (boundary a) (boundary a)) (xs : List A) :
    (0 : Q') ≤ quaternionHaar (blockCount radius)
      (polyMul (reflectCorrectedSlabPolynomial (adjacentEvenExtent radius) (lowerSum lower boundary xs))
        (lowerSum lower boundary xs)) :=
  Q'.le_trans' _ _ _
    (quaternionHaar_square_nonnegative _ _ (boundarySum_supported radius lower boundary hb xs))
    (Q'.ge_of_eqv (reflected_square radius lower boundary hl hb ll lb br xs))

end FiniteSum

end YMGap.Continuum.BF4ExactSlabSiteHaarFactorization

#print axioms YMGap.Continuum.BF4ExactSlabSiteHaarFactorization.blockCount
#print axioms YMGap.Continuum.BF4ExactSlabSiteHaarFactorization.blockSide
#print axioms YMGap.Continuum.BF4ExactSlabSiteHaarFactorization.Local
#print axioms YMGap.Continuum.BF4ExactSlabSiteHaarFactorization.blockSide_reflection
#print axioms YMGap.Continuum.BF4ExactSlabSiteHaarFactorization.lower_reflection_upper
#print axioms YMGap.Continuum.BF4ExactSlabSiteHaarFactorization.local_disjoint
#print axioms YMGap.Continuum.BF4ExactSlabSiteHaarFactorization.pairing_factor
#print axioms YMGap.Continuum.BF4ExactSlabSiteHaarFactorization.lowerSum
#print axioms YMGap.Continuum.BF4ExactSlabSiteHaarFactorization.upperSum
#print axioms YMGap.Continuum.BF4ExactSlabSiteHaarFactorization.boundarySum
#print axioms YMGap.Continuum.BF4ExactSlabSiteHaarFactorization.separated_pair
#print axioms YMGap.Continuum.BF4ExactSlabSiteHaarFactorization.sum_pairing
#print axioms YMGap.Continuum.BF4ExactSlabSiteHaarFactorization.lowerSum_supported
#print axioms YMGap.Continuum.BF4ExactSlabSiteHaarFactorization.upperSum_supported
#print axioms YMGap.Continuum.BF4ExactSlabSiteHaarFactorization.boundarySum_supported
#print axioms YMGap.Continuum.BF4ExactSlabSiteHaarFactorization.boundarySum_local
#print axioms YMGap.Continuum.BF4ExactSlabSiteHaarFactorization.lowerSum_reflection
#print axioms YMGap.Continuum.BF4ExactSlabSiteHaarFactorization.reflected_square
#print axioms YMGap.Continuum.BF4ExactSlabSiteHaarFactorization.reflected_nonnegative
