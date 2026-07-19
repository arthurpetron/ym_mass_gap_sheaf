/-
# Exact radial transfer for any finite product of quaternion spheres

The historical sphere-to-Gaussian radial identity was stated for the two
quaternion blocks of a single reflected boundary pair.  A finite lattice
gauge field instead has one four-coordinate quaternion block for every
active link.  This leaf proves the dimension-uniform monomial identity.

For each block, its exact normalized `S^3` moment multiplied by the positive
radial denominator is the corresponding four-coordinate product-Gaussian
moment.  Multiplying these identities over an arbitrary finite block list
gives a Fubini-compatible radial transfer.  On `List.range blockCount`, the
Gaussian block product is then identified with the existing lazy
`finiteGaussianMono (4 * blockCount)` carrier.  Consequently every supported
monomial satisfies

  finiteProductHaarMono blockCount m * finiteRadialFactor blockCount m
    = quaternionProductGaussianMono blockCount m

up to the constructive rational setoid.  The radial factor is proved
strictly positive.  These are precisely the monomial and cancellation atoms
needed by a later block-multihomogeneous square-positivity leaf.

No polynomial product, feature matrix, exponent family, or bounded labelling
space is materialized.

# Axiom gate

No `Classical`, choice, `sorry`/`admit`, `native_decide`, or custom axiom.
-/

import YMGap.Continuum.SU2QuaternionFiniteProductGaussianPositivity
import YMGap.Continuum.SU2QuaternionFiniteProductHaarSphereIdeal

namespace YMGap.Continuum.SU2QuaternionFiniteProductHaarGaussianRadialFactor

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarSphereIdeal
open YMGap.Continuum.SU2QuaternionHaarGaussianRadialFactor
open YMGap.Continuum.SU2QuaternionGaussianPolynomialIBP
open YMGap.Continuum.SU2QuaternionFiniteProductHaarCarrier
open YMGap.Continuum.SU2QuaternionFiniteProductHaarSphereIdeal
open YMGap.Continuum.SU2QuaternionFiniteProductGaussianPositivity

local infix:50 " ≈ " => Q'.eqv

private theorem q_mul_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right a a' b ha)
    (Q'.mul_eqv_congr_left a' b b' hb)

private theorem q_swap_adjacent (a b tail : Q') :
    a * (b * tail) ≈ b * (a * tail) := by
  refine Q'.eqv_trans _ ((a * b) * tail) _
    (Q'.eqv_symm (Q'.mul_assoc_eqv a b tail)) ?_
  refine Q'.eqv_trans _ ((b * a) * tail) _
    (Q'.mul_eqv_congr_right _ _ tail (Q'.mul_comm_eqv a b)) ?_
  exact Q'.mul_assoc_eqv b a tail

/-- Explicit commutative-semigroup bookkeeping for the four newly appended
Gaussian coordinates.  Keeping this at the rational setoid level avoids a
large quotient-unfolded commutative-ring normalization goal. -/
private theorem q_reverse_four_with_tail (a b c d tail : Q') :
    d * (c * (b * (a * tail))) ≈
      (a * (b * (c * d))) * tail := by
  refine Q'.eqv_trans _ (d * (c * (a * (b * tail)))) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left d _ _
      (Q'.mul_eqv_congr_left c _ _ (q_swap_adjacent b a tail))
  refine Q'.eqv_trans _ (d * (a * (c * (b * tail)))) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left d _ _
      (q_swap_adjacent c a (b * tail))
  refine Q'.eqv_trans _ (a * (d * (c * (b * tail)))) _
    (q_swap_adjacent d a (c * (b * tail))) ?_
  refine Q'.eqv_trans _ (a * (d * (b * (c * tail)))) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left a _ _
      (Q'.mul_eqv_congr_left d _ _ (q_swap_adjacent c b tail))
  refine Q'.eqv_trans _ (a * (b * (d * (c * tail)))) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left a _ _
      (q_swap_adjacent d b (c * tail))
  refine Q'.eqv_trans _ (a * (b * (c * (d * tail)))) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left a _ _
      (Q'.mul_eqv_congr_left b _ _ (q_swap_adjacent d c tail))
  refine Q'.eqv_trans _ (a * (b * ((c * d) * tail))) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left a _ _
      (Q'.mul_eqv_congr_left b _ _
        (Q'.eqv_symm (Q'.mul_assoc_eqv c d tail)))
  refine Q'.eqv_trans _ (a * ((b * (c * d)) * tail)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left a _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv b (c * d) tail))
  exact Q'.eqv_symm (Q'.mul_assoc_eqv a (b * (c * d)) tail)

/-! ## 1. Blockwise radial and Gaussian factors -/

/-- Half of the total exponent in one quaternion block, on an even monomial. -/
def quaternionBlockHalfDegree (block : Nat) (monomial : List Nat) : Nat :=
  halfDegree4
    (exponentAt monomial (4 * block))
    (exponentAt monomial (4 * block + 1))
    (exponentAt monomial (4 * block + 2))
    (exponentAt monomial (4 * block + 3))

/-- The positive radial denominator belonging to one quaternion block. -/
def quaternionBlockRadialDenominator
    (block : Nat) (monomial : List Nat) : Q' :=
  Q'.ofNat
    (sphereFourDenominator (quaternionBlockHalfDegree block monomial))

/-- The four-coordinate standard product-Gaussian moment in one block. -/
def quaternionBlockGaussianMoment
    (block : Nat) (monomial : List Nat) : Q' :=
  gaussianMoment4
    (exponentAt monomial (4 * block))
    (exponentAt monomial (4 * block + 1))
    (exponentAt monomial (4 * block + 2))
    (exponentAt monomial (4 * block + 3))

/-- Product of the selected block radial denominators, in finite Fubini
order. -/
def quaternionBlockRadialDenominatorProduct
    (monomial : List Nat) : List Nat → Q'
  | [] => 1
  | block :: blocks =>
      quaternionBlockRadialDenominator block monomial *
        quaternionBlockRadialDenominatorProduct monomial blocks

/-- Product of the selected four-coordinate Gaussian block moments. -/
def quaternionBlockGaussianMomentProduct
    (monomial : List Nat) : List Nat → Q'
  | [] => 1
  | block :: blocks =>
      quaternionBlockGaussianMoment block monomial *
        quaternionBlockGaussianMomentProduct monomial blocks

/-- Product of the radial denominators of the first `blockCount` carried
quaternion blocks.  This is lazy in `blockCount`. -/
def finiteRadialFactor (blockCount : Nat) (monomial : List Nat) : Q' :=
  quaternionBlockRadialDenominatorProduct monomial
    (List.range blockCount)

/-- The exact one-block radial identity at an arbitrary block offset. -/
theorem quaternionBlockMoment_mul_radialDenominator
    (block : Nat) (monomial : List Nat) :
    quaternionBlockMoment block monomial *
        quaternionBlockRadialDenominator block monomial ≈
      quaternionBlockGaussianMoment block monomial := by
  exact sphereMoment4_mul_radialDenominator
    (exponentAt monomial (4 * block))
    (exponentAt monomial (4 * block + 1))
    (exponentAt monomial (4 * block + 2))
    (exponentAt monomial (4 * block + 3))

/-- Multiplying the one-block identities gives exact radial transfer over
every finite block list.  Repeated blocks are permitted; no distinctness
hypothesis is needed for this purely multiplicative statement. -/
theorem quaternionBlockMomentProduct_mul_radialDenominatorProduct
    (monomial : List Nat) : ∀ blocks : List Nat,
    quaternionBlockMomentProduct monomial blocks *
        quaternionBlockRadialDenominatorProduct monomial blocks ≈
      quaternionBlockGaussianMomentProduct monomial blocks
  | [] => Q'.mul_one_eqv 1
  | block :: blocks => by
      change
        (quaternionBlockMoment block monomial *
            quaternionBlockMomentProduct monomial blocks) *
          (quaternionBlockRadialDenominator block monomial *
            quaternionBlockRadialDenominatorProduct monomial blocks) ≈
        quaternionBlockGaussianMoment block monomial *
          quaternionBlockGaussianMomentProduct monomial blocks
      refine Q'.eqv_trans _
        ((quaternionBlockMoment block monomial *
            quaternionBlockRadialDenominator block monomial) *
          (quaternionBlockMomentProduct monomial blocks *
            quaternionBlockRadialDenominatorProduct monomial blocks)) _
        (q_mul4_swap _ _ _ _) ?_
      exact q_mul_congr
        (quaternionBlockMoment_mul_radialDenominator block monomial)
        (quaternionBlockMomentProduct_mul_radialDenominatorProduct
          monomial blocks)

theorem quaternionBlockRadialDenominatorProduct_append
    (monomial : List Nat) : ∀ left right : List Nat,
    quaternionBlockRadialDenominatorProduct monomial (left ++ right) ≈
      quaternionBlockRadialDenominatorProduct monomial left *
        quaternionBlockRadialDenominatorProduct monomial right
  | [], right => Q'.eqv_symm
      (Q'.one_mul_eqv
        (quaternionBlockRadialDenominatorProduct monomial right))
  | block :: blocks, right => by
      change
        quaternionBlockRadialDenominator block monomial *
            quaternionBlockRadialDenominatorProduct monomial
              (blocks ++ right) ≈
          (quaternionBlockRadialDenominator block monomial *
              quaternionBlockRadialDenominatorProduct monomial blocks) *
            quaternionBlockRadialDenominatorProduct monomial right
      refine Q'.eqv_trans _
        (quaternionBlockRadialDenominator block monomial *
          (quaternionBlockRadialDenominatorProduct monomial blocks *
            quaternionBlockRadialDenominatorProduct monomial right)) _ ?_ ?_
      · exact Q'.mul_eqv_congr_left _ _ _
          (quaternionBlockRadialDenominatorProduct_append
            monomial blocks right)
      · exact Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)

theorem quaternionBlockGaussianMomentProduct_append
    (monomial : List Nat) : ∀ left right : List Nat,
    quaternionBlockGaussianMomentProduct monomial (left ++ right) ≈
      quaternionBlockGaussianMomentProduct monomial left *
        quaternionBlockGaussianMomentProduct monomial right
  | [], right => Q'.eqv_symm
      (Q'.one_mul_eqv
        (quaternionBlockGaussianMomentProduct monomial right))
  | block :: blocks, right => by
      change
        quaternionBlockGaussianMoment block monomial *
            quaternionBlockGaussianMomentProduct monomial
              (blocks ++ right) ≈
          (quaternionBlockGaussianMoment block monomial *
              quaternionBlockGaussianMomentProduct monomial blocks) *
            quaternionBlockGaussianMomentProduct monomial right
      refine Q'.eqv_trans _
        (quaternionBlockGaussianMoment block monomial *
          (quaternionBlockGaussianMomentProduct monomial blocks *
            quaternionBlockGaussianMomentProduct monomial right)) _ ?_ ?_
      · exact Q'.mul_eqv_congr_left _ _ _
          (quaternionBlockGaussianMomentProduct_append monomial blocks right)
      · exact Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)

/-! ## 2. Strict positivity of every finite radial factor -/

private theorem ofNat_pos_of_pos {n : Nat} (hn : 0 < n) :
    (0 : Q') < Q'.ofNat n := by
  cases n with
  | zero => omega
  | succ n => exact Q'.ofNat_succ_pos n

theorem quaternionBlockRadialDenominator_pos
    (block : Nat) (monomial : List Nat) :
    (0 : Q') < quaternionBlockRadialDenominator block monomial := by
  exact ofNat_pos_of_pos
    (sphereFourDenominator_pos
      (quaternionBlockHalfDegree block monomial))

theorem quaternionBlockRadialDenominatorProduct_pos
    (monomial : List Nat) : ∀ blocks : List Nat,
    (0 : Q') < quaternionBlockRadialDenominatorProduct monomial blocks
  | [] => by
      change (0 : Q') < (1 : Q')
      decide
  | block :: blocks =>
      Q'.mul_pos
        (quaternionBlockRadialDenominator_pos block monomial)
        (quaternionBlockRadialDenominatorProduct_pos monomial blocks)

/-! ## 3. Common factors on block-degree/parity sectors -/

/-- Total polynomial degree in one quaternion block. -/
def quaternionBlockDegree (block : Nat) (monomial : List Nat) : Nat :=
  exponentAt monomial (4 * block) +
    exponentAt monomial (4 * block + 1) +
    exponentAt monomial (4 * block + 2) +
    exponentAt monomial (4 * block + 3)

/-- Coordinatewise parity agreement in one quaternion block.  It is stated
as four propositions rather than as a materialized parity vector. -/
def SameQuaternionBlockParity
    (block : Nat) (left right : List Nat) : Prop :=
  exponentAt left (4 * block) % 2 =
      exponentAt right (4 * block) % 2 ∧
    exponentAt left (4 * block + 1) % 2 =
      exponentAt right (4 * block + 1) % 2 ∧
    exponentAt left (4 * block + 2) % 2 =
      exponentAt right (4 * block + 2) % 2 ∧
    exponentAt left (4 * block + 3) % 2 =
      exponentAt right (4 * block + 3) % 2

/-- In one fixed block-degree/parity sector, the half-degree of every
monomial pairing is the common degree. -/
theorem quaternionBlockHalfDegree_monoMul_eq
    (block : Nat) (left right : List Nat) (degree : Nat)
    (hparity : SameQuaternionBlockParity block left right)
    (hleft : quaternionBlockDegree block left = degree)
    (hright : quaternionBlockDegree block right = degree) :
    quaternionBlockHalfDegree block (monoMul left right) = degree := by
  rcases hparity with ⟨h0, h1, h2, h3⟩
  unfold quaternionBlockHalfDegree halfDegree4
  simp only [exponentAt_monoMul]
  unfold quaternionBlockDegree at hleft hright
  omega

/-- Radial denominator prescribed by a common block degree, independently
of either monomial in the pairing. -/
def blockDegreeRadialDenominator (degree : Nat) : Q' :=
  Q'.ofNat (sphereFourDenominator degree)

/-- Product of prescribed degree denominators over a supplied block order. -/
def blockDegreeRadialDenominatorProduct
    (degrees : Nat → Nat) : List Nat → Q'
  | [] => 1
  | block :: blocks =>
      blockDegreeRadialDenominator (degrees block) *
        blockDegreeRadialDenominatorProduct degrees blocks

/-- The common positive radial factor for the first `blockCount` blocks of a
block-multihomogeneous sector. -/
def finiteBlockDegreeRadialFactor
    (blockCount : Nat) (degrees : Nat → Nat) : Q' :=
  blockDegreeRadialDenominatorProduct degrees (List.range blockCount)

theorem blockDegreeRadialDenominator_pos (degree : Nat) :
    (0 : Q') < blockDegreeRadialDenominator degree := by
  exact ofNat_pos_of_pos (sphereFourDenominator_pos degree)

theorem blockDegreeRadialDenominatorProduct_pos
    (degrees : Nat → Nat) : ∀ blocks : List Nat,
    (0 : Q') < blockDegreeRadialDenominatorProduct degrees blocks
  | [] => by
      change (0 : Q') < (1 : Q')
      decide
  | block :: blocks =>
      Q'.mul_pos
        (blockDegreeRadialDenominator_pos (degrees block))
        (blockDegreeRadialDenominatorProduct_pos degrees blocks)

theorem finiteBlockDegreeRadialFactor_pos
    (blockCount : Nat) (degrees : Nat → Nat) :
    (0 : Q') < finiteBlockDegreeRadialFactor blockCount degrees := by
  exact blockDegreeRadialDenominatorProduct_pos degrees
    (List.range blockCount)

theorem quaternionBlockRadialDenominatorProduct_eq_degreeProduct
    (monomial : List Nat) (degrees : Nat → Nat) :
    ∀ blocks : List Nat,
      (∀ block, block ∈ blocks →
        quaternionBlockHalfDegree block monomial = degrees block) →
      quaternionBlockRadialDenominatorProduct monomial blocks =
        blockDegreeRadialDenominatorProduct degrees blocks
  | [], _ => rfl
  | block :: blocks, hdegrees => by
      have hhead := hdegrees block (by simp)
      have htail : ∀ other, other ∈ blocks →
          quaternionBlockHalfDegree other monomial = degrees other := by
        intro other hmem
        exact hdegrees other (by simp [hmem])
      simp only [quaternionBlockRadialDenominatorProduct,
        blockDegreeRadialDenominatorProduct,
        quaternionBlockRadialDenominator,
        blockDegreeRadialDenominator, hhead,
        quaternionBlockRadialDenominatorProduct_eq_degreeProduct
          monomial degrees blocks htail]

theorem finiteRadialFactor_monoMul_eq_degreeFactor
    (blockCount : Nat) (left right : List Nat) (degrees : Nat → Nat)
    (hparity : ∀ block, block < blockCount →
      SameQuaternionBlockParity block left right)
    (hleft : ∀ block, block < blockCount →
      quaternionBlockDegree block left = degrees block)
    (hright : ∀ block, block < blockCount →
      quaternionBlockDegree block right = degrees block) :
    finiteRadialFactor blockCount (monoMul left right) =
      finiteBlockDegreeRadialFactor blockCount degrees := by
  unfold finiteRadialFactor finiteBlockDegreeRadialFactor
  apply quaternionBlockRadialDenominatorProduct_eq_degreeProduct
  intro block hmem
  have hblock : block < blockCount := List.mem_range.mp hmem
  exact quaternionBlockHalfDegree_monoMul_eq block left right
    (degrees block) (hparity block hblock)
    (hleft block hblock) (hright block hblock)

/-! ## 4. Identification with the dimension-uniform Gaussian carrier -/

private theorem zero_num_cast : (0 : Q').num = 0 := rfl
private theorem zero_den_cast : ((0 : Q').den : Int) = 1 := rfl
private theorem one_num_cast : (1 : Q').num = 1 := rfl
private theorem one_den_cast : ((1 : Q').den : Int) = 1 := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.ofNat_num_cast, Q'.ofNat_den_cast,
               zero_num_cast, zero_den_cast, one_num_cast, one_den_cast,
               Int.add_mul, Int.mul_add, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.zero_add, Int.add_zero];
             try ac_rfl))

/-- A four-coordinate Gaussian block is the tensor product of its four
univariate exact Gaussian moments.  This public offset-free form is included
here because the corresponding lemma in the historical eight-coordinate
bridge was intentionally private. -/
theorem gaussianMoment4_eq_fourfold (e0 e1 e2 e3 : Nat) :
    gaussianMoment4 e0 e1 e2 e3 ≈
      gaussianMoment1 e0 * (gaussianMoment1 e1 *
        (gaussianMoment1 e2 * gaussianMoment1 e3)) := by
  unfold gaussianMoment1
  by_cases h0 : e0 % 2 = 0
  · by_cases h1 : e1 % 2 = 0
    · by_cases h2 : e2 % 2 = 0
      · by_cases h3 : e3 % 2 = 0
        · simp only [gaussianMoment4, h0, h1, h2, h3, Nat.zero_mod,
            and_self, ↓reduceDIte, oddDoubleFactorial]
          let a := oddDoubleFactorial (e0 / 2)
          let b := oddDoubleFactorial (e1 / 2)
          let c := oddDoubleFactorial (e2 / 2)
          let d := oddDoubleFactorial (e3 / 2)
          refine Q'.eqv_trans _
            (Q'.ofNat ((a * b) * c) * Q'.ofNat d) _
            (YMGap.Constructive.SU3CharFactor.ofNat_mul_eqv
              ((a * b) * c) d) ?_
          refine Q'.eqv_trans _
            ((Q'.ofNat (a * b) * Q'.ofNat c) * Q'.ofNat d) _
            (Q'.mul_eqv_congr_right _ _
              (Q'.ofNat d)
              (YMGap.Constructive.SU3CharFactor.ofNat_mul_eqv
                (a * b) c)) ?_
          refine Q'.eqv_trans _
            (((Q'.ofNat a * Q'.ofNat b) * Q'.ofNat c) * Q'.ofNat d) _
            (Q'.mul_eqv_congr_right _ _ (Q'.ofNat d)
              (Q'.mul_eqv_congr_right _ _ (Q'.ofNat c)
                (YMGap.Constructive.SU3CharFactor.ofNat_mul_eqv a b))) ?_
          ring_qeqv
        · simp only [gaussianMoment4, h0, h1, h2, h3, Nat.zero_mod,
            and_self, and_true, true_and, ↓reduceDIte]
          ring_qeqv
      · simp only [gaussianMoment4, h0, h1, h2, Nat.zero_mod,
          and_self, and_true, true_and, false_and, ↓reduceDIte]
        ring_qeqv
    · simp only [gaussianMoment4, h0, h1, Nat.zero_mod,
        and_self, and_true, true_and, false_and, ↓reduceDIte]
      ring_qeqv
  · simp only [gaussianMoment4, h0, Nat.zero_mod,
      and_self, and_true, false_and, ↓reduceDIte]
    ring_qeqv

/-- Adding one quaternion block to the finite coordinate Gaussian carrier
adds exactly the corresponding four-coordinate Gaussian moment.  The
apparently reversed recursion order is harmless by commutativity. -/
theorem finiteGaussianMono_four_step
    (block : Nat) (monomial : List Nat) :
    finiteGaussianMono (4 * (block + 1)) monomial ≈
      quaternionBlockGaussianMoment block monomial *
        finiteGaussianMono (4 * block) monomial := by
  simp only [finiteGaussianMono]
  unfold quaternionBlockGaussianMoment
  refine Q'.eqv_trans _
    ((gaussianMoment1 (exponentAt monomial (4 * block)) *
        (gaussianMoment1 (exponentAt monomial (4 * block + 1)) *
          (gaussianMoment1 (exponentAt monomial (4 * block + 2)) *
            gaussianMoment1 (exponentAt monomial (4 * block + 3)))) *
      finiteGaussianMono (4 * block) monomial)) _ ?_ ?_
  · exact q_reverse_four_with_tail
      (gaussianMoment1 (exponentAt monomial (4 * block)))
      (gaussianMoment1 (exponentAt monomial (4 * block + 1)))
      (gaussianMoment1 (exponentAt monomial (4 * block + 2)))
      (gaussianMoment1 (exponentAt monomial (4 * block + 3)))
      (finiteGaussianMono (4 * block) monomial)
  · exact Q'.mul_eqv_congr_right _ _ _
      (Q'.eqv_symm
        (gaussianMoment4_eq_fourfold
          (exponentAt monomial (4 * block))
          (exponentAt monomial (4 * block + 1))
          (exponentAt monomial (4 * block + 2))
          (exponentAt monomial (4 * block + 3))))

/-- The blockwise Gaussian product over the prefix of quaternion blocks is
exactly the existing dimension-uniform coordinate Gaussian monomial moment. -/
theorem quaternionBlockGaussianMomentProduct_range
    (monomial : List Nat) : ∀ blockCount : Nat,
    quaternionBlockGaussianMomentProduct monomial
        (List.range blockCount) ≈
      finiteGaussianMono (4 * blockCount) monomial
  | 0 => Q'.eqv_refl 1
  | blockCount + 1 => by
      rw [List.range_succ]
      refine Q'.eqv_trans _
        (quaternionBlockGaussianMomentProduct monomial
            (List.range blockCount) *
          quaternionBlockGaussianMomentProduct monomial [blockCount]) _
        (quaternionBlockGaussianMomentProduct_append monomial
          (List.range blockCount) [blockCount]) ?_
      change
        quaternionBlockGaussianMomentProduct monomial
              (List.range blockCount) *
            (quaternionBlockGaussianMoment blockCount monomial * 1) ≈
          finiteGaussianMono (4 * (blockCount + 1)) monomial
      refine Q'.eqv_trans _
        (quaternionBlockGaussianMomentProduct monomial
            (List.range blockCount) *
          quaternionBlockGaussianMoment blockCount monomial) _
        (Q'.mul_eqv_congr_left _ _ _
          (Q'.mul_one_eqv
            (quaternionBlockGaussianMoment blockCount monomial))) ?_
      refine Q'.eqv_trans _
        (finiteGaussianMono (4 * blockCount) monomial *
          quaternionBlockGaussianMoment blockCount monomial) _
        (Q'.mul_eqv_congr_right _ _ _
          (quaternionBlockGaussianMomentProduct_range monomial blockCount)) ?_
      refine Q'.eqv_trans _
        (quaternionBlockGaussianMoment blockCount monomial *
          finiteGaussianMono (4 * blockCount) monomial) _
        (Q'.mul_comm_eqv _ _) ?_
      exact Q'.eqv_symm
        (finiteGaussianMono_four_step blockCount monomial)

/-! ## 5. The finite-product radial factor and the main transfer -/

theorem finiteRadialFactor_pos
    (blockCount : Nat) (monomial : List Nat) :
    (0 : Q') < finiteRadialFactor blockCount monomial := by
  exact quaternionBlockRadialDenominatorProduct_pos monomial
    (List.range blockCount)

/-- **Exact finite-product sphere-to-Gaussian monomial transfer.**  A
monomial supported in the first `4 * blockCount` coordinates has finite
product-Haar moment times its positive radial factor equal to the exact
`4 * blockCount`-coordinate Gaussian moment. -/
theorem finiteProductHaarMono_mul_finiteRadialFactor
    (blockCount : Nat) (monomial : List Nat)
    (htail : allZero (monomial.drop (4 * blockCount)) = true) :
    finiteProductHaarMono blockCount monomial *
        finiteRadialFactor blockCount monomial ≈
      quaternionProductGaussianMono blockCount monomial := by
  unfold finiteProductHaarMono finiteRadialFactor
  rw [if_pos htail]
  refine Q'.eqv_trans _
    (quaternionBlockGaussianMomentProduct monomial
      (List.range blockCount)) _
    (quaternionBlockMomentProduct_mul_radialDenominatorProduct
      monomial (List.range blockCount)) ?_
  exact quaternionBlockGaussianMomentProduct_range monomial blockCount

/-- Pairwise form of the main transfer on a block-multihomogeneous parity
sector.  Its radial factor depends only on the sector degrees, not on the
chosen pair of monomials. -/
theorem finiteProductHaarMono_pair_mul_degreeRadialFactor
    (blockCount : Nat) (left right : List Nat) (degrees : Nat → Nat)
    (htail : allZero
      ((monoMul left right).drop (4 * blockCount)) = true)
    (hparity : ∀ block, block < blockCount →
      SameQuaternionBlockParity block left right)
    (hleft : ∀ block, block < blockCount →
      quaternionBlockDegree block left = degrees block)
    (hright : ∀ block, block < blockCount →
      quaternionBlockDegree block right = degrees block) :
    finiteProductHaarMono blockCount (monoMul left right) *
        finiteBlockDegreeRadialFactor blockCount degrees ≈
      quaternionProductGaussianMono blockCount (monoMul left right) := by
  rw [← finiteRadialFactor_monoMul_eq_degreeFactor
    blockCount left right degrees hparity hleft hright]
  exact finiteProductHaarMono_mul_finiteRadialFactor
    blockCount (monoMul left right) htail

#print axioms quaternionBlockMoment_mul_radialDenominator
#print axioms quaternionBlockMomentProduct_mul_radialDenominatorProduct
#print axioms quaternionBlockRadialDenominatorProduct_pos
#print axioms quaternionBlockHalfDegree_monoMul_eq
#print axioms finiteBlockDegreeRadialFactor_pos
#print axioms finiteRadialFactor_monoMul_eq_degreeFactor
#print axioms gaussianMoment4_eq_fourfold
#print axioms finiteGaussianMono_four_step
#print axioms quaternionBlockGaussianMomentProduct_range
#print axioms finiteRadialFactor_pos
#print axioms finiteProductHaarMono_mul_finiteRadialFactor
#print axioms finiteProductHaarMono_pair_mul_degreeRadialFactor

end YMGap.Continuum.SU2QuaternionFiniteProductHaarGaussianRadialFactor
