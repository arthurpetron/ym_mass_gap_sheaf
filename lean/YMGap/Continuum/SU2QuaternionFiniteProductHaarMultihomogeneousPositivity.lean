/-
# Finite-product Haar positivity on multihomogeneous parity sectors

The exact radial transfer for finitely many quaternion blocks is termwise.
To turn it into polynomial positivity, its radial denominator must be common
to every monomial pair in the square.  This leaf isolates precisely that
condition without materializing a parity vector or a degree vector:

* `AllFiniteQuaternionBlockDegrees` fixes one degree in each carried block;
* `AllFiniteQuaternionCoordinateParity` fixes coordinatewise parity through
  a lazy function `Nat → Nat`;
* `SupportedQuaternionBlocks` confines every exponent list to the carried
  base-four coordinate prefix.

On two polynomials in the same sector, raw finite-product Haar integration of
their product, multiplied by the common positive radial factor, equals the
corresponding finite product-Gaussian integral.  The proof uses literal row
and bilinear folds, so it neither expands a polynomial square nor enumerates
coordinates, terms, parity assignments, or degree assignments.

Specializing the rectangular transfer to a square and using the constructive
finite-dimensional Gaussian Gram theorem gives nonnegativity of every square
inside every arbitrary-block common-degree/common-parity sector.

# Axiom gate

No `Classical`, choice, `sorry`/`admit`, `native_decide`, or custom axiom.
-/

import YMGap.Continuum.SU2QuaternionFiniteProductHaarGaussianRadialFactor
import YMGap.Continuum.SU2QuaternionFiniteProductGaussianPositivity
import YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini

namespace YMGap.Continuum.SU2QuaternionFiniteProductHaarMultihomogeneousPositivity

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFiniteProductHaarCarrier
open YMGap.Continuum.SU2QuaternionFiniteProductHaarSphereIdeal
open YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini
open YMGap.Continuum.SU2QuaternionFiniteProductGaussianPositivity
open YMGap.Continuum.SU2QuaternionFiniteProductHaarGaussianRadialFactor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Lazy arbitrary-block sector predicates -/

/-- Every monomial has the prescribed total degree in each carried
quaternion block.  The degree assignment is a function and is never
enumerated. -/
def AllFiniteQuaternionBlockDegrees
    (blockCount : Nat) (degrees : Nat → Nat) (polynomial : RatPoly) : Prop :=
  ∀ term, term ∈ polynomial → ∀ block, block < blockCount →
    quaternionBlockDegree block term.1 = degrees block

/-- Every monomial has the prescribed parity in each carried scalar
coordinate.  Only the prefix below `4 * blockCount` is constrained, and the
parity assignment remains a lazy function. -/
def AllFiniteQuaternionCoordinateParity
    (blockCount : Nat) (parities : Nat → Nat)
    (polynomial : RatPoly) : Prop :=
  ∀ term, term ∈ polynomial → ∀ coordinate,
    coordinate < 4 * blockCount →
      exponentAt term.1 coordinate % 2 = parities coordinate

/-- Two monomials drawn from one common coordinate-parity sector have the
same four parities in every carried quaternion block. -/
theorem sameQuaternionBlockParity_of_commonParity
    {blockCount : Nat} {parities : Nat → Nat}
    {left right : RatTerm}
    (hleft : ∀ coordinate, coordinate < 4 * blockCount →
      exponentAt left.1 coordinate % 2 = parities coordinate)
    (hright : ∀ coordinate, coordinate < 4 * blockCount →
      exponentAt right.1 coordinate % 2 = parities coordinate)
    (block : Nat) (hblock : block < blockCount) :
    SameQuaternionBlockParity block left.1 right.1 := by
  constructor
  · exact (hleft (4 * block) (by omega)).trans
      (hright (4 * block) (by omega)).symm
  constructor
  · exact (hleft (4 * block + 1) (by omega)).trans
      (hright (4 * block + 1) (by omega)).symm
  constructor
  · exact (hleft (4 * block + 2) (by omega)).trans
      (hright (4 * block + 2) (by omega)).symm
  · exact (hleft (4 * block + 3) (by omega)).trans
      (hright (4 * block + 3) (by omega)).symm

/-- A product of two structurally supported monomials has a literally zero
exponent tail beyond the finite quaternion-block carrier. -/
theorem allZero_drop_monoMul_of_supported
    {blockCount : Nat} {left right : List Nat}
    (hleft : left.length ≤ 4 * blockCount)
    (hright : right.length ≤ 4 * blockCount) :
    allZero ((monoMul left right).drop (4 * blockCount)) = true := by
  rw [monoMul_drop_of_right_length_le
    left right (4 * blockCount) hright]
  rw [List.drop_eq_nil_of_le hleft]
  rfl

/-! ## 2. Termwise common-radial-factor transfer -/

/-- The monomial radial identity lifted through the product of the two raw
coefficients. -/
theorem finiteHaarPair_mul_degreeRadialFactor
    (blockCount : Nat) (degrees parities : Nat → Nat)
    (left right : RatTerm)
    (hleftSupport : left.1.length ≤ 4 * blockCount)
    (hrightSupport : right.1.length ≤ 4 * blockCount)
    (hleftParity : ∀ coordinate, coordinate < 4 * blockCount →
      exponentAt left.1 coordinate % 2 = parities coordinate)
    (hrightParity : ∀ coordinate, coordinate < 4 * blockCount →
      exponentAt right.1 coordinate % 2 = parities coordinate)
    (hleftDegree : ∀ block, block < blockCount →
      quaternionBlockDegree block left.1 = degrees block)
    (hrightDegree : ∀ block, block < blockCount →
      quaternionBlockDegree block right.1 = degrees block) :
    ((left.2 * right.2) *
        finiteProductHaarMono blockCount (monoMul left.1 right.1)) *
          finiteBlockDegreeRadialFactor blockCount degrees ≈
      (left.2 * right.2) *
        quaternionProductGaussianMono blockCount
          (monoMul left.1 right.1) := by
  refine Q'.eqv_trans _
    ((left.2 * right.2) *
      (finiteProductHaarMono blockCount (monoMul left.1 right.1) *
        finiteBlockDegreeRadialFactor blockCount degrees)) _
    (Q'.mul_assoc_eqv _ _ _) ?_
  exact Q'.mul_eqv_congr_left _ _ _
    (finiteProductHaarMono_pair_mul_degreeRadialFactor
      blockCount left.1 right.1 degrees
      (allZero_drop_monoMul_of_supported hleftSupport hrightSupport)
      (fun block hblock =>
        sameQuaternionBlockParity_of_commonParity
          hleftParity hrightParity block hblock)
      hleftDegree hrightDegree)

/-! ## 3. Finite-product Haar row and bilinear folds -/

/-- One row of the arbitrary-block raw Haar monomial-pair expansion. -/
def finiteHaarRow (blockCount : Nat) (left : RatTerm) : RatPoly → Q'
  | [] => 0
  | right :: polynomial =>
      (left.2 * right.2) *
          finiteProductHaarMono blockCount
            (monoMul left.1 right.1) +
        finiteHaarRow blockCount left polynomial

/-- The arbitrary-block raw Haar bilinear form. -/
def finiteHaarBilinear (blockCount : Nat) : RatPoly → RatPoly → Q'
  | [], _ => 0
  | left :: polynomial, right =>
      finiteHaarRow blockCount left right +
        finiteHaarBilinear blockCount polynomial right

private theorem finiteProductHaar_map_row
    (blockCount : Nat) (left : RatTerm) : ∀ right : RatPoly,
    finiteProductHaar blockCount
        (right.map fun term =>
          (monoMul left.1 term.1, left.2 * term.2)) ≈
      finiteHaarRow blockCount left right
  | [] => Q'.eqv_refl 0
  | term :: polynomial => by
      change
        (left.2 * term.2) *
              finiteProductHaarMono blockCount
                (monoMul left.1 term.1) +
            finiteProductHaar blockCount
              (polynomial.map fun other =>
                (monoMul left.1 other.1, left.2 * other.2)) ≈
          (left.2 * term.2) *
              finiteProductHaarMono blockCount
                (monoMul left.1 term.1) +
            finiteHaarRow blockCount left polynomial
      exact Q'.add_eqv_congr_left _ _ _
        (finiteProductHaar_map_row blockCount left polynomial)

/-- Raw finite-product Haar integration of a literal polynomial product is
exactly the corresponding finite Haar bilinear fold. -/
theorem finiteProductHaar_polyMul_eq_bilinear
    (blockCount : Nat) : ∀ left right : RatPoly,
    finiteProductHaar blockCount (polyMul left right) ≈
      finiteHaarBilinear blockCount left right
  | [], _ => Q'.eqv_refl 0
  | term :: polynomial, right => by
      unfold polyMul List.flatMap
      refine Q'.eqv_trans _
        (finiteProductHaar blockCount
            (right.map fun other =>
              (monoMul term.1 other.1, term.2 * other.2)) +
          finiteProductHaar blockCount
            (polyMul polynomial right)) _
        (finiteProductHaar_append blockCount _ _) ?_
      exact QPoly.q_add_congr
        (finiteProductHaar_map_row blockCount term right)
        (finiteProductHaar_polyMul_eq_bilinear
          blockCount polynomial right)

/-! ## 4. Row and rectangular bilinear radial transfer -/

private theorem finiteHaarRow_mul_degreeRadialFactor
    (blockCount : Nat) (degrees parities : Nat → Nat)
    (left : RatTerm)
    (hleftSupport : left.1.length ≤ 4 * blockCount)
    (hleftParity : ∀ coordinate, coordinate < 4 * blockCount →
      exponentAt left.1 coordinate % 2 = parities coordinate)
    (hleftDegree : ∀ block, block < blockCount →
      quaternionBlockDegree block left.1 = degrees block) :
    ∀ right : RatPoly,
      SupportedQuaternionBlocks blockCount right →
      AllFiniteQuaternionCoordinateParity blockCount parities right →
      AllFiniteQuaternionBlockDegrees blockCount degrees right →
      finiteHaarRow blockCount left right *
          finiteBlockDegreeRadialFactor blockCount degrees ≈
        finiteGaussianRow (4 * blockCount) left right
  | [], _, _, _ => QPoly.q_zero_mul _
  | right :: polynomial, hsupport, hparity, hdegree => by
      have hrightSupport := hsupport right (by simp)
      have hrightParity := hparity right (by simp)
      have hrightDegree := hdegree right (by simp)
      refine Q'.eqv_trans _
        (((left.2 * right.2) *
              finiteProductHaarMono blockCount
                (monoMul left.1 right.1)) *
            finiteBlockDegreeRadialFactor blockCount degrees +
          finiteHaarRow blockCount left polynomial *
            finiteBlockDegreeRadialFactor blockCount degrees) _
        (Q'.add_mul_eqv _ _ _) ?_
      exact QPoly.q_add_congr
        (finiteHaarPair_mul_degreeRadialFactor
          blockCount degrees parities left right
          hleftSupport hrightSupport
          hleftParity hrightParity hleftDegree hrightDegree)
        (finiteHaarRow_mul_degreeRadialFactor
          blockCount degrees parities left
          hleftSupport hleftParity hleftDegree polynomial
          (fun term hterm => hsupport term (by simp [hterm]))
          (fun term hterm => hparity term (by simp [hterm]))
          (fun term hterm => hdegree term (by simp [hterm])))

/-- Exact common-radial-factor transfer for a rectangular pair of
polynomials in the same arbitrary-block degree/parity sector. -/
theorem finiteHaarBilinear_mul_degreeRadialFactor
    (blockCount : Nat) (degrees parities : Nat → Nat) :
    ∀ left right : RatPoly,
      SupportedQuaternionBlocks blockCount left →
      SupportedQuaternionBlocks blockCount right →
      AllFiniteQuaternionCoordinateParity blockCount parities left →
      AllFiniteQuaternionCoordinateParity blockCount parities right →
      AllFiniteQuaternionBlockDegrees blockCount degrees left →
      AllFiniteQuaternionBlockDegrees blockCount degrees right →
      finiteHaarBilinear blockCount left right *
          finiteBlockDegreeRadialFactor blockCount degrees ≈
        finiteGaussianBilinear (4 * blockCount) left right
  | [], right, _, _, _, _, _, _ => QPoly.q_zero_mul _
  | left :: polynomial, right,
      hleftSupport, hrightSupport,
      hleftParity, hrightParity,
      hleftDegree, hrightDegree => by
      have htermSupport := hleftSupport left (by simp)
      have htermParity := hleftParity left (by simp)
      have htermDegree := hleftDegree left (by simp)
      refine Q'.eqv_trans _
        (finiteHaarRow blockCount left right *
            finiteBlockDegreeRadialFactor blockCount degrees +
          finiteHaarBilinear blockCount polynomial right *
            finiteBlockDegreeRadialFactor blockCount degrees) _
        (Q'.add_mul_eqv _ _ _) ?_
      exact QPoly.q_add_congr
        (finiteHaarRow_mul_degreeRadialFactor
          blockCount degrees parities left
          htermSupport htermParity htermDegree right
          hrightSupport hrightParity hrightDegree)
        (finiteHaarBilinear_mul_degreeRadialFactor
          blockCount degrees parities polynomial right
          (fun term hterm => hleftSupport term (by simp [hterm]))
          hrightSupport
          (fun term hterm => hleftParity term (by simp [hterm]))
          hrightParity
          (fun term hterm => hleftDegree term (by simp [hterm]))
          hrightDegree)

/-! ## 5. Polynomial transfer and square positivity -/

/-- **Exact rectangular polynomial transfer.**  On a common finite-block
degree/parity sector, scaled product Haar equals the dimension-matched
product Gaussian functional. -/
theorem finiteProductHaar_polyMul_mul_degreeRadialFactor
    (blockCount : Nat) (degrees parities : Nat → Nat)
    (left right : RatPoly)
    (hleftSupport : SupportedQuaternionBlocks blockCount left)
    (hrightSupport : SupportedQuaternionBlocks blockCount right)
    (hleftParity :
      AllFiniteQuaternionCoordinateParity blockCount parities left)
    (hrightParity :
      AllFiniteQuaternionCoordinateParity blockCount parities right)
    (hleftDegree :
      AllFiniteQuaternionBlockDegrees blockCount degrees left)
    (hrightDegree :
      AllFiniteQuaternionBlockDegrees blockCount degrees right) :
    finiteProductHaar blockCount (polyMul left right) *
        finiteBlockDegreeRadialFactor blockCount degrees ≈
      quaternionProductGaussian blockCount (polyMul left right) := by
  refine Q'.eqv_trans _
    (finiteHaarBilinear blockCount left right *
      finiteBlockDegreeRadialFactor blockCount degrees) _
    (Q'.mul_eqv_congr_right _ _ _
      (finiteProductHaar_polyMul_eq_bilinear
        blockCount left right)) ?_
  refine Q'.eqv_trans _
    (finiteGaussianBilinear (4 * blockCount) left right) _
    (finiteHaarBilinear_mul_degreeRadialFactor
      blockCount degrees parities left right
      hleftSupport hrightSupport
      hleftParity hrightParity hleftDegree hrightDegree) ?_
  unfold quaternionProductGaussian
  exact Q'.eqv_symm
    (finiteProductGaussian_polyMul (4 * blockCount) left right)

/-- Exact scaled-Haar-square identity on an arbitrary finite quaternion-block
common-degree/common-parity sector. -/
theorem finiteProductHaar_square_mul_degreeRadialFactor
    (blockCount : Nat) (degrees parities : Nat → Nat)
    (polynomial : RatPoly)
    (hsupport : SupportedQuaternionBlocks blockCount polynomial)
    (hparity :
      AllFiniteQuaternionCoordinateParity blockCount parities polynomial)
    (hdegree :
      AllFiniteQuaternionBlockDegrees blockCount degrees polynomial) :
    finiteProductHaar blockCount (polyMul polynomial polynomial) *
        finiteBlockDegreeRadialFactor blockCount degrees ≈
      quaternionProductGaussian blockCount
        (polyMul polynomial polynomial) :=
  finiteProductHaar_polyMul_mul_degreeRadialFactor
    blockCount degrees parities polynomial polynomial
    hsupport hsupport hparity hparity hdegree hdegree

/-- **Arbitrary-block common-sector square positivity.**  Every raw
polynomial square is nonnegative under finite product Haar once its monomials
share one coordinate-parity assignment and one degree in every carried
quaternion block. -/
theorem finiteProductHaar_square_nonneg_of_multihomogeneous_parity
    (blockCount : Nat) (degrees parities : Nat → Nat)
    (polynomial : RatPoly)
    (hsupport : SupportedQuaternionBlocks blockCount polynomial)
    (hparity :
      AllFiniteQuaternionCoordinateParity blockCount parities polynomial)
    (hdegree :
      AllFiniteQuaternionBlockDegrees blockCount degrees polynomial) :
    (0 : Q') ≤
      finiteProductHaar blockCount
        (polyMul polynomial polynomial) := by
  have hGaussian :=
    quaternionProductGaussian_square_nonneg blockCount polynomial
  have heq := finiteProductHaar_square_mul_degreeRadialFactor
    blockCount degrees parities polynomial hsupport hparity hdegree
  have hscaled :
      (0 : Q') ≤
        finiteProductHaar blockCount (polyMul polynomial polynomial) *
          finiteBlockDegreeRadialFactor blockCount degrees :=
    Q'.le_trans' _ _ _ hGaussian
      (Q'.le_of_eqv (Q'.eqv_symm heq))
  have hleft :
      (0 : Q') ≤
        finiteBlockDegreeRadialFactor blockCount degrees *
          finiteProductHaar blockCount
            (polyMul polynomial polynomial) :=
    Q'.le_trans' _ _ _ hscaled
      (Q'.le_of_eqv (Q'.eqv_symm
        (Q'.mul_comm_eqv
          (finiteBlockDegreeRadialFactor blockCount degrees)
          (finiteProductHaar blockCount
            (polyMul polynomial polynomial)))))
  exact Q'.nonneg_of_mul_pos
    (finiteBlockDegreeRadialFactor_pos blockCount degrees) hleft

#print axioms sameQuaternionBlockParity_of_commonParity
#print axioms allZero_drop_monoMul_of_supported
#print axioms finiteHaarPair_mul_degreeRadialFactor
#print axioms finiteProductHaar_polyMul_eq_bilinear
#print axioms finiteHaarBilinear_mul_degreeRadialFactor
#print axioms finiteProductHaar_polyMul_mul_degreeRadialFactor
#print axioms finiteProductHaar_square_mul_degreeRadialFactor
#print axioms finiteProductHaar_square_nonneg_of_multihomogeneous_parity

end YMGap.Continuum.SU2QuaternionFiniteProductHaarMultihomogeneousPositivity
