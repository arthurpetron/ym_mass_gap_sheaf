/-
# Faraut image pairing gives a constructive interior SU(2) Harnack window

Jacques Faraut, *Analysis on Lie Groups: An Introduction* (Cambridge
University Press, 2008), Proposition 8.6.6, p. 181, gives the displayed
SU(2) heat-kernel image formula

    H₀(t,θ) =
      (√π / 4) (eᵗ / (t√t))
        Σ_{k∈ℤ} ((θ - 2kπ) / sin θ)
          exp (-(θ - 2kπ)² / (4t)).

On an interior class-angle window `0 < δ ≤ θ ≤ π-δ`, split the integer
sum into the pairs `k = -n` and `k = n+1`.  The `n`th pair has the form

    positiveImage n - negativeImage n,

where both image magnitudes are nonnegative.  Gaussian decay is then used
twice:

* `negativeImage n ≤ positiveImage n`, so every paired contribution is
  nonnegative;
* a summable positive majorant gives a uniform upper bound.

This module formalizes exactly that order argument over the project's
constructive rationals and reals.  It does **not** assert Faraut's analytic
identity, define the exponential image terms, or silently identify a
normalization convention.  Those facts are carried by the explicit
`FarautInteriorImageCertificate`.  The certificate is strictly more
structured than a heat-kernel window: it exposes the positive and negative
images, their pairwise domination, a summable majorant, and the two
factorization identities.  Given it, the module constructs a positive
completed-kernel window and a terminal-independent projective comparison.

This is useful for the AF/small-time branch because the missing analytic work
is now localized to constructive Gaussian enclosures on an interior angle
window.  It does not by itself control the removable singularities at
`θ = 0,π`, nor identify the resulting class kernel with the interacting BF4
retained carrier.

## Constructivity

Only structural recursion, exact `Q'` order, and the explicit approximants of
`CReal` are used.  There is no `Classical.*`, `Real`, `native_decide`, `sorry`,
custom axiom, or noncomputable declaration.
-/

import YMGap.Constructive.CRealComplete
import YMGap.Constructive.CRealMul
import YMGap.Constructive.ExpPos
import YMGap.Constructive.RationalTail
import YMGap.Constructive.Sqrt

namespace YMGap.Continuum.SU2FarautInteriorImageHarnack

open YMGap.Constructive
open YMGap.Constructive.RationalTail

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Paired image prefixes -/

/-- The signed contribution obtained by pairing the Faraut images
`k = -n` and `k = n+1`.  The inputs are their nonnegative magnitudes. -/
def farautImagePair
    (positiveImage negativeImage : Nat → Q') (n : Nat) : Q' :=
  positiveImage n + (-(negativeImage n))

/-- The first `N+1` paired Faraut images.  Including the zeroth pair at every
approximation lets a strict lower floor survive the constructive limit. -/
def farautImagePrefix
    (positiveImage negativeImage : Nat → Q') (N : Nat) : Q' :=
  finSum
    (farautImagePair positiveImage negativeImage)
    (N + 1)

/-- Pairwise domination of the negative image by the positive image is
equivalent to nonnegativity of the signed pair, in the direction needed
below. -/
theorem farautImagePair_nonnegative
    {positiveImage negativeImage : Nat → Q'}
    (pair_domination :
      ∀ n, negativeImage n ≤ positiveImage n)
    (n : Nat) :
    (0 : Q') ≤
      farautImagePair positiveImage negativeImage n := by
  unfold farautImagePair
  exact Q'.sub_nonneg_of_le (pair_domination n)

/-- A floor on the zeroth pair and nonnegativity of every later pair give the
same floor for every paired prefix. -/
theorem farautImagePrefix_lower
    {positiveImage negativeImage : Nat → Q'}
    {imageFloor : Q'}
    (zero_pair_floor :
      imageFloor ≤
        farautImagePair positiveImage negativeImage 0)
    (pair_nonnegative :
      ∀ n, (0 : Q') ≤
        farautImagePair positiveImage negativeImage n) :
    ∀ N,
      imageFloor ≤
        farautImagePrefix positiveImage negativeImage N
  | 0 => by
      unfold farautImagePrefix
      simpa only [finSum_succ, finSum_zero,
        Q'.zero_add'] using zero_pair_floor
  | N + 1 => by
      unfold farautImagePrefix
      rw [show N + 1 + 1 = (N + 1) + 1 by omega,
        finSum_succ]
      exact Q'.le_trans' _ _ _
        (farautImagePrefix_lower
          zero_pair_floor pair_nonnegative N)
        (Q'.add_le_self_of_nonneg
          (finSum
            (farautImagePair positiveImage negativeImage)
            (N + 1))
          (farautImagePair
            positiveImage negativeImage (N + 1))
          (pair_nonnegative (N + 1)))

/-- Finite sums preserve pointwise rational order. -/
theorem finSum_mono
    {lower upper : Nat → Q'}
    (term_order : ∀ n, lower n ≤ upper n) :
    ∀ N, finSum lower N ≤ finSum upper N
  | 0 => Q'.le_refl' 0
  | N + 1 =>
      Q'.add_le_add
        (finSum_mono term_order N)
        (term_order N)

/-- If every signed pair is bounded by a nonnegative summable majorant, a
uniform majorant-prefix ceiling bounds every paired image prefix. -/
theorem farautImagePrefix_upper
    {positiveImage negativeImage majorant : Nat → Q'}
    {imageCeiling : Q'}
    (pair_le_majorant :
      ∀ n,
        farautImagePair positiveImage negativeImage n ≤
          majorant n)
    (majorant_prefix_ceiling :
      ∀ N, finSum majorant (N + 1) ≤ imageCeiling)
    (N : Nat) :
    farautImagePrefix positiveImage negativeImage N ≤
      imageCeiling := by
  exact Q'.le_trans' _ _ _
    (finSum_mono pair_le_majorant (N + 1))
    (majorant_prefix_ceiling N)

/-! ## 2. The explicit analytic certificate -/

/-- Constructive certificate for applying Faraut's image formula on one
interior class-angle window.

The two identities are stated approximation-by-approximation:

* `image_formula` identifies the completed image sum with paired integer-image
  prefixes;
* `kernel_formula` identifies the completed heat kernel with the product of
  the positive prefactor and that image sum.

This is the honest interface for the cited analytic formula.  In particular,
neither identity is manufactured in this module.  The remaining fields are
Gaussian inequalities and a summable tail majorant, not the desired kernel
window itself. -/
structure FarautInteriorImageCertificate
    (kernel : CReal)
    (prefactorFloor prefactorCeiling
      imageFloor imageCeiling : Q') : Type where
  prefactor : CReal
  imageSum : CReal
  positiveImage : Nat → Q'
  negativeImage : Nat → Q'
  majorant : Nat → Q'
  prefactor_floor_pos : (0 : Q') < prefactorFloor
  image_floor_pos : (0 : Q') < imageFloor
  prefactor_ceiling_nonnegative :
    (0 : Q') ≤ prefactorCeiling
  image_ceiling_nonnegative :
    (0 : Q') ≤ imageCeiling
  prefactor_lower :
    ∀ N, prefactorFloor ≤ prefactor.approx N
  prefactor_upper :
    ∀ N, prefactor.approx N ≤ prefactorCeiling
  positive_image_nonnegative :
    ∀ n, (0 : Q') ≤ positiveImage n
  negative_image_nonnegative :
    ∀ n, (0 : Q') ≤ negativeImage n
  pair_domination :
    ∀ n, negativeImage n ≤ positiveImage n
  zero_pair_floor :
    imageFloor ≤
      farautImagePair positiveImage negativeImage 0
  pair_le_majorant :
    ∀ n,
      farautImagePair positiveImage negativeImage n ≤
        majorant n
  majorant_nonnegative :
    ∀ n, (0 : Q') ≤ majorant n
  majorant_prefix_ceiling :
    ∀ N, finSum majorant (N + 1) ≤ imageCeiling
  image_formula :
    ∀ N,
      imageSum.approx N ≈
        farautImagePrefix positiveImage negativeImage N
  kernel_formula :
    ∀ N,
      kernel.approx N ≈
        prefactor.approx N * imageSum.approx N

namespace FarautInteriorImageCertificate

variable
    {kernel : CReal}
    {prefactorFloor prefactorCeiling
      imageFloor imageCeiling : Q'}
    (certificate :
      FarautInteriorImageCertificate
        kernel prefactorFloor prefactorCeiling
        imageFloor imageCeiling)

include certificate

/-- Every completed image-sum approximant retains the strict zeroth-pair
floor. -/
theorem image_lower (N : Nat) :
    imageFloor ≤ certificate.imageSum.approx N := by
  have hprefix :
      imageFloor ≤
        farautImagePrefix
          certificate.positiveImage
          certificate.negativeImage N :=
    farautImagePrefix_lower
      certificate.zero_pair_floor
      (fun n =>
        farautImagePair_nonnegative
          certificate.pair_domination n)
      N
  exact Q'.le_trans' _ _ _
    hprefix
    (Q'.ge_of_eqv (certificate.image_formula N))

/-- The supplied Gaussian majorant bounds every completed image-sum
approximant. -/
theorem image_upper (N : Nat) :
    certificate.imageSum.approx N ≤ imageCeiling := by
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (certificate.image_formula N))
    (farautImagePrefix_upper
      certificate.pair_le_majorant
      certificate.majorant_prefix_ceiling N)

/-- The completed kernel has the explicit positive rational floor obtained
by multiplying the prefactor and zeroth-pair floors. -/
theorem kernel_approx_lower (N : Nat) :
    prefactorFloor * imageFloor ≤ kernel.approx N := by
  have hprefactor_nonnegative :
      (0 : Q') ≤ (certificate.prefactor).approx N :=
    Q'.le_trans' _ _ _
      (Q'.le_of_lt certificate.prefactor_floor_pos)
      (certificate.prefactor_lower N)
  have hproduct :
      prefactorFloor * imageFloor ≤
        (certificate.prefactor).approx N *
          (certificate.imageSum).approx N :=
    Q'.mul_le_mul_of_nonneg
      (certificate.prefactor_lower N)
      (certificate.image_lower N)
      hprefactor_nonnegative
      (Q'.le_of_lt certificate.image_floor_pos)
  exact Q'.le_trans' _ _ _
    hproduct
    (Q'.ge_of_eqv (certificate.kernel_formula N))

/-- The completed kernel has the explicit rational ceiling obtained by
multiplying the prefactor and image-sum ceilings. -/
theorem kernel_approx_upper (N : Nat) :
    kernel.approx N ≤
      prefactorCeiling * imageCeiling := by
  have himage_nonnegative :
      (0 : Q') ≤ (certificate.imageSum).approx N :=
    Q'.le_trans' _ _ _
      (Q'.le_of_lt certificate.image_floor_pos)
      (certificate.image_lower N)
  have hproduct :
      (certificate.prefactor).approx N *
          (certificate.imageSum).approx N ≤
        prefactorCeiling * imageCeiling :=
    Q'.mul_le_mul_of_nonneg
      (certificate.prefactor_upper N)
      (certificate.image_upper N)
      certificate.prefactor_ceiling_nonnegative
      himage_nonnegative
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (certificate.kernel_formula N))
    hproduct

/-- Semantic constructive-real lower bound supplied by the Faraut image
certificate. -/
theorem kernel_ge_floor :
    ExpPos.geRat kernel
      (prefactorFloor * imageFloor) :=
  ExpPos.geRat_of_eventually
    ⟨0, fun N _ => certificate.kernel_approx_lower N⟩

/-- Semantic constructive-real upper bound supplied by the Faraut image
certificate. -/
theorem kernel_le_ceiling :
    CReal.leRat kernel
      (prefactorCeiling * imageCeiling) :=
  CReal.leRat_of_eventually
    ⟨0, fun N _ => certificate.kernel_approx_upper N⟩

/-- The resulting kernel floor is strictly positive, with an explicit
rational witness. -/
theorem kernel_floor_pos :
    (0 : Q') < prefactorFloor * imageFloor :=
  Q'.mul_pos
    certificate.prefactor_floor_pos
    certificate.image_floor_pos

end FarautInteriorImageCertificate

/-! ## 3. Interior projective/Harnack order -/

/-- Two kernels carrying the same uniform Faraut image window obey a
terminal-independent projective comparison.  This is the form consumed by
backward-message and retained-path Harnack arguments.

The proof is approximation-wise, so no spectral theorem or classical extrema
argument enters. -/
theorem farautInterior_projective_order
    {first second : CReal}
    {prefactorFloor prefactorCeiling
      imageFloor imageCeiling spread : Q'}
    (firstCertificate :
      FarautInteriorImageCertificate
        first prefactorFloor prefactorCeiling
        imageFloor imageCeiling)
    (secondCertificate :
      FarautInteriorImageCertificate
        second prefactorFloor prefactorCeiling
        imageFloor imageCeiling)
    (spread_nonnegative : (0 : Q') ≤ spread)
    (window_order :
      prefactorCeiling * imageCeiling ≤
        spread * (prefactorFloor * imageFloor)) :
    CReal.leEv first
      (CReal.mul (CReal.ofQ' spread) second) := by
  intro ε hε
  refine ⟨0, fun N _ => ?_⟩
  have hsecond_floor :
      prefactorFloor * imageFloor ≤ second.approx N :=
    secondCertificate.kernel_approx_lower N
  have hscaled :
      spread * (prefactorFloor * imageFloor) ≤
        spread * second.approx N :=
    Q'.mul_le_mul_of_nonneg_left _ _ _
      hsecond_floor spread_nonnegative
  have hraw :
      first.approx N ≤
        spread * second.approx N :=
    Q'.le_trans' _ _ _
      (firstCertificate.kernel_approx_upper N)
      (Q'.le_trans' _ _ _ window_order hscaled)
  exact Q'.le_trans' _ _ _
    hraw
    (Q'.add_le_self_of_nonneg
      (spread * second.approx N)
      ε (Q'.le_of_lt hε))

end YMGap.Continuum.SU2FarautInteriorImageHarnack

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.SU2FarautInteriorImageHarnack.farautImagePair_nonnegative
#print axioms YMGap.Continuum.SU2FarautInteriorImageHarnack.farautImagePrefix_lower
#print axioms YMGap.Continuum.SU2FarautInteriorImageHarnack.finSum_mono
#print axioms YMGap.Continuum.SU2FarautInteriorImageHarnack.farautImagePrefix_upper
#print axioms YMGap.Continuum.SU2FarautInteriorImageHarnack.FarautInteriorImageCertificate.image_lower
#print axioms YMGap.Continuum.SU2FarautInteriorImageHarnack.FarautInteriorImageCertificate.image_upper
#print axioms YMGap.Continuum.SU2FarautInteriorImageHarnack.FarautInteriorImageCertificate.kernel_approx_lower
#print axioms YMGap.Continuum.SU2FarautInteriorImageHarnack.FarautInteriorImageCertificate.kernel_approx_upper
#print axioms YMGap.Continuum.SU2FarautInteriorImageHarnack.FarautInteriorImageCertificate.kernel_ge_floor
#print axioms YMGap.Continuum.SU2FarautInteriorImageHarnack.FarautInteriorImageCertificate.kernel_le_ceiling
#print axioms YMGap.Continuum.SU2FarautInteriorImageHarnack.FarautInteriorImageCertificate.kernel_floor_pos
#print axioms YMGap.Continuum.SU2FarautInteriorImageHarnack.farautInterior_projective_order
