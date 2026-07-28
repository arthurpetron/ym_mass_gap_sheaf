/-
# Constructive completion of geometrically dominated Faraut image pairs

`SU2FarautInteriorImageHarnack` isolates the analytic content of Faraut's
SU(2) image formula in a `FarautInteriorImageCertificate`.  That certificate
still accepts a completed `imageSum : CReal` and an `image_formula` identifying
its approximants with paired integer-image prefixes.

This module removes both assumed fields for the important case in which the
paired images have an explicit geometric majorant

    0 ≤ pair(n) ≤ C r^n,        0 < r < 1.

The general-base geometric increment engine
`HKConvGen.crealOfGeoIncrementBase` constructs the image sum directly from
the shifted prefixes

    S_N = Σ_{n < N+1} pair(n).

The shift keeps the strictly positive zeroth-pair floor visible in every
approximant.  Since

    S_{N+1} - S_N = pair(N+1) ≤ C r^(N+1) ≤ C r^N,

the prefixes fit the engine without changing the supplied constant `C`.
The same geometric estimate proves the uniform image ceiling

    S_N ≤ C / (1-r).

Finally a positive rational prefactor is embedded into `CReal`, multiplied
by the constructed image sum, and packaged as a genuine
`FarautInteriorImageCertificate`.  Thus the earlier certificate's
`imageSum`, `image_formula`, majorant-prefix ceiling, prefactor bounds, and
kernel factorization are all constructed here.

Honest remaining inputs are exactly the image data: rational enclosures for
the positive and negative Gaussian images, pair domination, a strict zeroth
pair floor, and the common geometric bound.  This module does not prove
Faraut's Poisson/image identity for the repository's character heat kernel,
the `t`-to-nome normalization, endpoint removal at `θ=0,π`, or identification
with the interacting BF4 retained carrier.

## Constructivity

There is no `Classical.*`, `Real`, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration.
-/

import YMGap.Continuum.SU2FarautInteriorImageHarnack
import YMGap.Continuum.HeatKernelConvGen

namespace YMGap.Continuum.SU2FarautGeometricImageCompletion

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.SU2FarautInteriorImageHarnack

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Geometrically dominated paired-image data -/

/-- The remaining rational Gaussian input for completing the paired Faraut
image series.

`positiveImage n` and `negativeImage n` are the magnitudes of the
`k=-n` and `k=n+1` terms after the common angle denominator has been
included.  The signed contribution is their difference. -/
structure FarautGeometricImageData : Type where
  positiveImage : Nat → Q'
  negativeImage : Nat → Q'
  imageFloor : Q'
  constant : Q'
  ratio : Q'
  image_floor_pos : (0 : Q') < imageFloor
  ratio_pos : (0 : Q') < ratio
  ratio_lt_one : ratio < (1 : Q')
  positive_image_nonnegative :
    ∀ n, (0 : Q') ≤ positiveImage n
  negative_image_nonnegative :
    ∀ n, (0 : Q') ≤ negativeImage n
  pair_domination :
    ∀ n, negativeImage n ≤ positiveImage n
  zero_pair_floor :
    imageFloor ≤
      farautImagePair positiveImage negativeImage 0
  pair_geometric_upper :
    ∀ n,
      farautImagePair positiveImage negativeImage n ≤
        HKConvGen.geoIncrBase constant ratio n

namespace FarautGeometricImageData

variable (data : FarautGeometricImageData)

/-- Every paired image is nonnegative. -/
theorem pair_nonnegative (n : Nat) :
    (0 : Q') ≤
      farautImagePair
        data.positiveImage data.negativeImage n :=
  farautImagePair_nonnegative data.pair_domination n

/-- The geometric constant is automatically positive: the positive zeroth
floor lies below the zeroth pair, which lies below `C r^0 = C`. -/
theorem constant_pos :
    (0 : Q') < data.constant := by
  have hfloor_to_majorant :
      data.imageFloor ≤
        HKConvGen.geoIncrBase
          data.constant data.ratio 0 :=
    Q'.le_trans' _ _ _
      data.zero_pair_floor
      (data.pair_geometric_upper 0)
  have hmajorant_to_constant :
      HKConvGen.geoIncrBase
          data.constant data.ratio 0 ≤
        data.constant := by
    unfold HKConvGen.geoIncrBase
    exact Q'.le_of_eqv
      (Q'.mul_one_eqv data.constant)
  exact Q'.pos_of_lt_of_le
    data.image_floor_pos
    (Q'.le_trans' _ _ _
      hfloor_to_majorant hmajorant_to_constant)

/-- The derived geometric constant positivity gives nonnegativity. -/
theorem constant_nonnegative :
    (0 : Q') ≤ data.constant :=
  Q'.le_of_lt data.constant_pos

/-- The geometric ratio is nonnegative. -/
theorem ratio_nonnegative :
    (0 : Q') ≤ data.ratio :=
  Q'.le_of_lt data.ratio_pos

/-- The geometric majorant is nonnegative term by term. -/
theorem majorant_nonnegative (n : Nat) :
    (0 : Q') ≤
      HKConvGen.geoIncrBase data.constant data.ratio n :=
  HKConvGen.geoIncrBase_nonneg
    data.constant_nonnegative
    data.ratio_nonnegative n

end FarautGeometricImageData

/-! ## 2. Increment control for shifted paired prefixes -/

@[simp] theorem farautImagePrefix_succ
    (positiveImage negativeImage : Nat → Q') (N : Nat) :
    farautImagePrefix positiveImage negativeImage (N + 1) =
      farautImagePrefix positiveImage negativeImage N +
        farautImagePair positiveImage negativeImage (N + 1) := by
  unfold farautImagePrefix
  rw [show N + 1 + 1 = (N + 1) + 1 by omega,
    finSum_succ]

/-- The newly added pair at step `N+1` is bounded by the increment envelope
`C r^N` consumed by `crealOfGeoIncrementBase`. -/
theorem shifted_pair_le_increment
    (data : FarautGeometricImageData) (N : Nat) :
    farautImagePair
        data.positiveImage data.negativeImage (N + 1) ≤
      HKConvGen.geoIncrBase
        data.constant data.ratio N := by
  have hpower :
      data.ratio ^ (N + 1) ≤ data.ratio ^ N :=
    HKConvGen.pow_base_le_succ
      data.ratio_nonnegative
      (Q'.le_of_lt data.ratio_lt_one) N
  have hscaled :
      data.constant * data.ratio ^ (N + 1) ≤
        data.constant * data.ratio ^ N :=
    Q'.mul_le_mul_of_nonneg_left _ _ _
      hpower data.constant_nonnegative
  exact Q'.le_trans' _ _ _
    (data.pair_geometric_upper (N + 1))
    hscaled

/-- Upper one-step increment inequality for the shifted prefixes. -/
theorem farautImagePrefix_increment_upper
    (data : FarautGeometricImageData) (N : Nat) :
    farautImagePrefix
        data.positiveImage data.negativeImage (N + 1) ≤
      farautImagePrefix
          data.positiveImage data.negativeImage N +
        HKConvGen.geoIncrBase
          data.constant data.ratio N := by
  rw [farautImagePrefix_succ]
  exact Q'.add_le_add_left
    (farautImagePrefix
      data.positiveImage data.negativeImage N)
    (farautImagePair
      data.positiveImage data.negativeImage (N + 1))
    (HKConvGen.geoIncrBase
      data.constant data.ratio N)
    (shifted_pair_le_increment data N)

/-- Lower one-step increment inequality.  Since every paired contribution
is nonnegative, the prefix is monotone; adding the nonnegative geometric
slack preserves the required reverse estimate. -/
theorem farautImagePrefix_increment_lower
    (data : FarautGeometricImageData) (N : Nat) :
    farautImagePrefix
        data.positiveImage data.negativeImage N ≤
      farautImagePrefix
          data.positiveImage data.negativeImage (N + 1) +
        HKConvGen.geoIncrBase
          data.constant data.ratio N := by
  have hmono :
      farautImagePrefix
          data.positiveImage data.negativeImage N ≤
        farautImagePrefix
          data.positiveImage data.negativeImage (N + 1) := by
    rw [farautImagePrefix_succ]
    exact Q'.add_le_self_of_nonneg
      (farautImagePrefix
        data.positiveImage data.negativeImage N)
      (farautImagePair
        data.positiveImage data.negativeImage (N + 1))
      (data.pair_nonnegative (N + 1))
  exact Q'.le_trans' _ _ _
    hmono
    (Q'.add_le_self_of_nonneg
      (farautImagePrefix
        data.positiveImage data.negativeImage (N + 1))
      (HKConvGen.geoIncrBase
        data.constant data.ratio N)
      (data.majorant_nonnegative N))

/-! ## 3. Explicit modulus and constructive image completion -/

/-- Type-level modulus input required by the general-base geometric
completion.  It is constructed by dividing the requested tolerance by the
positive total geometric scale `C/(1-r)`. -/
theorem farautGeometricIncrementModulus
    (data : FarautGeometricImageData) :
    ∀ ε : Q', (0 : Q') < ε →
      ∃ δ : Q', (0 : Q') < δ ∧
        (data.constant *
          HKConv.divPos 1 (1 + (-data.ratio))) *
          δ ≤ ε := by
  intro ε hε
  let scale :=
    data.constant *
      HKConv.divPos 1 (1 + (-data.ratio))
  have hscale_pos : (0 : Q') < scale :=
    Q'.mul_pos
      data.constant_pos
      (HKConv.divPos_pos (by decide))
  have hscale_num : 0 < scale.num :=
    CReal.num_pos_of_pos hscale_pos
  refine
    ⟨HKConv.divPos ε scale,
      HKConv.divPos_pos
        (CReal.num_pos_of_pos hε), ?_⟩
  refine Q'.le_of_eqv ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_comm_eqv scale
      (HKConv.divPos ε scale)) ?_
  exact HKConv.divPos_mul_eqv hscale_num

/-- The paired Faraut image sum constructed from its actual rational
prefixes and geometric increment modulus. -/
def farautGeometricImageSum
    (data : FarautGeometricImageData) : CReal :=
  HKConvGen.crealOfGeoIncrementBase
    (farautImagePrefix
      data.positiveImage data.negativeImage)
    data.constant data.ratio
    data.constant_nonnegative
    data.ratio_pos data.ratio_lt_one
    (farautImagePrefix_increment_upper data)
    (farautImagePrefix_increment_lower data)
    (farautGeometricIncrementModulus data)

/-- The constructed real's approximants are definitionally the paired image
prefixes; no separate `image_formula` hypothesis remains. -/
@[simp] theorem farautGeometricImageSum_approx
    (data : FarautGeometricImageData) (N : Nat) :
    (farautGeometricImageSum data).approx N =
      farautImagePrefix
        data.positiveImage data.negativeImage N :=
  rfl

/-- The rational paired-image prefixes converge constructively to the image
sum just built.  The convergence modulus is the one carried by
`crealOfGeoIncrementBase`, not an erased compactness argument. -/
theorem farautImagePrefix_converges
    (data : FarautGeometricImageData) :
    CReal.ConvergesTo
      (fun N =>
        CReal.ofQ'
          (farautImagePrefix
            data.positiveImage data.negativeImage N))
      (farautGeometricImageSum data) := by
  simpa [farautGeometricImageSum] using
    (CReal.convergesTo_self
      (farautGeometricImageSum data))

/-! ## 4. Constructed geometric ceiling -/

/-- The exact rational geometric-series ceiling used by the completed image
sum. -/
def farautGeometricImageCeiling
    (data : FarautGeometricImageData) : Q' :=
  HKConvGen.geoTailBase
    data.constant data.ratio 0

/-- Every finite geometric majorant prefix is below the constructed
`C/(1-r)` ceiling. -/
theorem farautGeometricMajorant_prefix_ceiling
    (data : FarautGeometricImageData) (N : Nat) :
    finSum
        (fun n =>
          HKConvGen.geoIncrBase
            data.constant data.ratio n)
        (N + 1) ≤
      farautGeometricImageCeiling data := by
  simpa only [Nat.zero_add] using
    (HKConvGen.geoTailBase_series_le
      data.constant_nonnegative
      data.ratio_pos data.ratio_lt_one
      0 (N + 1))

/-- The geometric image ceiling is nonnegative. -/
theorem farautGeometricImageCeiling_nonnegative
    (data : FarautGeometricImageData) :
    (0 : Q') ≤ farautGeometricImageCeiling data := by
  unfold farautGeometricImageCeiling
  exact Q'.mul_nonneg _ _
    (HKConvGen.geoIncrBase_nonneg
      data.constant_nonnegative
      data.ratio_nonnegative 0)
    (HKConv.divPos_nonneg (by decide))

/-! ## 5. Genuine Faraut certificate and positive kernel -/

/-- The completed rational-prefactor Faraut kernel. -/
def farautGeometricKernel
    (prefactor : Q')
    (data : FarautGeometricImageData) : CReal :=
  CReal.mul
    (CReal.ofQ' prefactor)
    (farautGeometricImageSum data)

/-- A positive rational prefactor and geometrically dominated image data
construct a complete `FarautInteriorImageCertificate`.  In particular, its
`imageSum`, image formula, majorant ceiling, prefactor corridor, and kernel
factorization are outputs, not assumptions. -/
def farautGeometricInteriorCertificate
    (prefactor : Q') (prefactor_pos : (0 : Q') < prefactor)
    (data : FarautGeometricImageData) :
    FarautInteriorImageCertificate
      (farautGeometricKernel prefactor data)
      prefactor prefactor
      data.imageFloor
      (farautGeometricImageCeiling data) where
  prefactor := CReal.ofQ' prefactor
  imageSum := farautGeometricImageSum data
  positiveImage := data.positiveImage
  negativeImage := data.negativeImage
  majorant := fun n =>
    HKConvGen.geoIncrBase
      data.constant data.ratio n
  prefactor_floor_pos := prefactor_pos
  image_floor_pos := data.image_floor_pos
  prefactor_ceiling_nonnegative :=
    Q'.le_of_lt prefactor_pos
  image_ceiling_nonnegative :=
    farautGeometricImageCeiling_nonnegative data
  prefactor_lower := fun _ =>
    Q'.le_refl' prefactor
  prefactor_upper := fun _ =>
    Q'.le_refl' prefactor
  positive_image_nonnegative :=
    data.positive_image_nonnegative
  negative_image_nonnegative :=
    data.negative_image_nonnegative
  pair_domination :=
    data.pair_domination
  zero_pair_floor :=
    data.zero_pair_floor
  pair_le_majorant :=
    data.pair_geometric_upper
  majorant_nonnegative :=
    data.majorant_nonnegative
  majorant_prefix_ceiling :=
    farautGeometricMajorant_prefix_ceiling data
  image_formula := fun _ =>
    Q'.eqv_refl _
  kernel_formula := fun _ =>
    Q'.eqv_refl _

/-- The constructed kernel has an explicit positive rational floor. -/
theorem farautGeometricKernel_ge_floor
    (prefactor : Q') (prefactor_pos : (0 : Q') < prefactor)
    (data : FarautGeometricImageData) :
    ExpPos.geRat
      (farautGeometricKernel prefactor data)
      (prefactor * data.imageFloor) :=
  (farautGeometricInteriorCertificate
    prefactor prefactor_pos data).kernel_ge_floor

/-- The constructed kernel has the explicit geometric rational ceiling. -/
theorem farautGeometricKernel_le_ceiling
    (prefactor : Q') (prefactor_pos : (0 : Q') < prefactor)
    (data : FarautGeometricImageData) :
    CReal.leRat
      (farautGeometricKernel prefactor data)
      (prefactor * farautGeometricImageCeiling data) :=
  (farautGeometricInteriorCertificate
    prefactor prefactor_pos data).kernel_le_ceiling

/-- The constructed kernel floor is strictly positive. -/
theorem farautGeometricKernel_floor_pos
    (prefactor : Q') (prefactor_pos : (0 : Q') < prefactor)
    (data : FarautGeometricImageData) :
    (0 : Q') < prefactor * data.imageFloor :=
  Q'.mul_pos prefactor_pos data.image_floor_pos

end YMGap.Continuum.SU2FarautGeometricImageCompletion

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.SU2FarautGeometricImageCompletion.FarautGeometricImageData.pair_nonnegative
#print axioms YMGap.Continuum.SU2FarautGeometricImageCompletion.FarautGeometricImageData.constant_pos
#print axioms YMGap.Continuum.SU2FarautGeometricImageCompletion.shifted_pair_le_increment
#print axioms YMGap.Continuum.SU2FarautGeometricImageCompletion.farautImagePrefix_increment_upper
#print axioms YMGap.Continuum.SU2FarautGeometricImageCompletion.farautImagePrefix_increment_lower
#print axioms YMGap.Continuum.SU2FarautGeometricImageCompletion.farautGeometricIncrementModulus
#print axioms YMGap.Continuum.SU2FarautGeometricImageCompletion.farautGeometricImageSum
#print axioms YMGap.Continuum.SU2FarautGeometricImageCompletion.farautGeometricImageSum_approx
#print axioms YMGap.Continuum.SU2FarautGeometricImageCompletion.farautImagePrefix_converges
#print axioms YMGap.Continuum.SU2FarautGeometricImageCompletion.farautGeometricMajorant_prefix_ceiling
#print axioms YMGap.Continuum.SU2FarautGeometricImageCompletion.farautGeometricInteriorCertificate
#print axioms YMGap.Continuum.SU2FarautGeometricImageCompletion.farautGeometricKernel_ge_floor
#print axioms YMGap.Continuum.SU2FarautGeometricImageCompletion.farautGeometricKernel_le_ceiling
#print axioms YMGap.Continuum.SU2FarautGeometricImageCompletion.farautGeometricKernel_floor_pos
