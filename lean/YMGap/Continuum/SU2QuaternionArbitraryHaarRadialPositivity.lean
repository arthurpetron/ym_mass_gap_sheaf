/-
# Arbitrary-product quaternion Haar positivity on one radial/parity sector

This module is the sphere-radial companion to
`SU2QuaternionArbitraryGaussianPositivity`.  For any finite number of
quaternion blocks it proves positivity of the exact product-Haar functional
on a polynomial square whenever:

* all monomials are supported in those blocks;
* every pair of monomials has the same coordinate parities; and
* every monomial has one common total degree on each quaternion block.

Under these hypotheses every monomial pair has the same positive radial
denominator.  Multiplying by that denominator identifies the Haar square with
the already-proved arbitrary-coordinate Gaussian square.

This is the load-bearing fixed-sector theorem.  The subsequent
homogenization layer removes the common-degree restriction by multiplying
individual terms with unit sphere-radius polynomials.
-/

import YMGap.Continuum.BF4GeometricHaarMehlerProjection
import YMGap.Continuum.SU2QuaternionArbitraryGaussianPositivity

namespace YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity

set_option maxRecDepth 30000
set_option maxHeartbeats 8000000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarGaussianRadialFactor
open YMGap.Continuum.SU2QuaternionGaussianPolynomialIBP
open YMGap.Continuum.SU2QuaternionProductGaussianHermiteGram
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2QuaternionArbitraryGaussianPositivity

local infix:50 " ≈ " => Q'.eqv

private theorem exponentAt_monoMul
    (left right : List Nat) (index : Nat) :
    exponentAt (monoMul left right) index =
      exponentAt left index + exponentAt right index := by
  induction left generalizing right index with
  | nil => simp [monoMul, exponentAt]
  | cons x xs ih =>
      cases right with
      | nil => simp [monoMul, exponentAt]
      | cons y ys =>
          cases index with
          | zero => simp [monoMul, exponentAt]
          | succ index =>
              change exponentAt (monoMul xs ys) index =
                exponentAt xs index + exponentAt ys index
              exact ih ys index

private theorem exponentAt_drop
    (monomial : List Nat) :
    ∀ (offset index : Nat),
      exponentAt (monomial.drop offset) index =
        exponentAt monomial (offset + index)
  | 0, index => by
      simp [exponentAt]
  | offset + 1, index => by
      cases monomial with
      | nil => simp [exponentAt]
      | cons exponent rest =>
          have hindex :
              offset + 1 + index =
                (offset + index) + 1 := by
            omega
          rw [hindex]
          simp only [List.drop_succ_cons]
          unfold exponentAt
          simp only [List.getD_cons_succ]
          exact exponentAt_drop rest offset index

private theorem monoMul_drop_of_length_le
    (left right : List Nat) (coordinates : Nat)
    (hright : right.length ≤ coordinates) :
    (monoMul left right).drop coordinates =
      left.drop coordinates := by
  induction coordinates generalizing left right with
  | zero =>
      cases right with
      | nil => cases left <;> rfl
      | cons y ys => simp at hright
  | succ coordinates ih =>
      cases left with
      | nil =>
          simp only [monoMul]
          exact List.drop_eq_nil_of_le hright
      | cons x xs =>
          cases right with
          | nil => simp [monoMul]
          | cons y ys =>
              simp only [List.length_cons] at hright
              simp [monoMul, ih xs ys (by omega)]

private theorem monoMul_length_le
    {left right : List Nat} {coordinates : Nat}
    (hleft : left.length ≤ coordinates)
    (hright : right.length ≤ coordinates) :
    (monoMul left right).length ≤ coordinates := by
  apply List.drop_eq_nil_iff.mp
  rw [monoMul_drop_of_length_le left right coordinates hright]
  exact List.drop_eq_nil_of_le hleft

private theorem allZero_of_drop_nil
    (values : List Nat) (hvalues : values = []) :
    allZero values = true := by
  rw [hvalues]
  rfl

/-- The total polynomial degree in the four coordinates of one quaternion
block. -/
def quaternionBlockDegree
    (monomial : List Nat) (block : Nat) : Nat :=
  exponentAt monomial (4 * block) +
    exponentAt monomial (4 * block + 1) +
    exponentAt monomial (4 * block + 2) +
    exponentAt monomial (4 * block + 3)

/-- Coordinate-parity equality on the declared quaternion prefix. -/
def SameQuaternionParity
    (blocks : Nat) (left right : List Nat) : Prop :=
  ∀ index, index < 4 * blocks →
    exponentAt left index % 2 =
      exponentAt right index % 2

/-- Common block degree data for one monomial. -/
def HasQuaternionBlockDegrees
    (blocks : Nat) (degrees : Nat → Nat)
    (monomial : List Nat) : Prop :=
  ∀ block, block < blocks →
    quaternionBlockDegree monomial block =
      degrees block

/-- Syntactic support in the first `4 * blocks` coordinates. -/
def SupportedQuaternionBlocks
    (blocks : Nat) (polynomial : RatPoly) : Prop :=
  ∀ term, term ∈ polynomial →
    term.1.length ≤ 4 * blocks

/-- Product of the radial denominators attached to the declared block
degrees. -/
def quaternionRadialFactor
    (degrees : Nat → Nat) (startBlock : Nat) :
    Nat → Q'
  | 0 => 1
  | blocks + 1 =>
      Q'.ofNat
          (sphereFourDenominator
            (degrees startBlock)) *
        quaternionRadialFactor degrees
          (startBlock + 1) blocks

private theorem ofNat_pos_of_pos
    {value : Nat} (hvalue : 0 < value) :
    (0 : Q') < Q'.ofNat value := by
  cases value with
  | zero => omega
  | succ value => exact Q'.ofNat_succ_pos value

theorem quaternionRadialFactor_positive
    (degrees : Nat → Nat) (startBlock blocks : Nat) :
      (0 : Q') <
        quaternionRadialFactor degrees startBlock blocks := by
  induction blocks generalizing startBlock with
  | zero =>
      change (0 : Q') < 1
      exact CReal.pos_of_num_pos (by decide)
  | succ blocks induction =>
      exact Q'.mul_pos
        (ofNat_pos_of_pos
          (sphereFourDenominator_pos
            (degrees startBlock)))
        (induction (startBlock + 1))

/-- The same product Haar prefix written with global coordinate offsets. -/
def quaternionHaarRange
    (start : Nat) : Nat → List Nat → Q'
  | 0, _ => 1
  | blocks + 1, monomial =>
      sphereMoment4
          (exponentAt monomial start)
          (exponentAt monomial (start + 1))
          (exponentAt monomial (start + 2))
          (exponentAt monomial (start + 3)) *
        quaternionHaarRange
          (start + 4) blocks monomial

private theorem quaternionHaarPrefix_drop_eq_range
    (monomial : List Nat) :
    ∀ (start blocks : Nat),
      quaternionHaarPrefix blocks
          (monomial.drop start) ≈
        quaternionHaarRange
          start blocks monomial
  | _, 0 => Q'.eqv_refl 1
  | start, blocks + 1 => by
      unfold quaternionHaarPrefix quaternionHaarRange
      rw [exponentAt_drop monomial start 0,
        exponentAt_drop monomial start 1,
        exponentAt_drop monomial start 2,
        exponentAt_drop monomial start 3]
      simp only [Nat.add_zero]
      refine Q'.mul_eqv_congr_left _ _ _ ?_
      have induction :=
        quaternionHaarPrefix_drop_eq_range
          monomial (start + 4) blocks
      simpa [List.drop_drop, Nat.add_assoc] using induction

private theorem gaussianMomentRange_four
    (start coordinates : Nat) (monomial : List Nat) :
    gaussianMomentRange start (4 + coordinates) monomial ≈
      gaussianMoment4
          (exponentAt monomial start)
          (exponentAt monomial (start + 1))
          (exponentAt monomial (start + 2))
          (exponentAt monomial (start + 3)) *
        gaussianMomentRange
          (start + 4) coordinates monomial := by
  rw [Nat.add_comm 4 coordinates]
  change
    gaussianMoment1 (exponentAt monomial start) *
        (gaussianMoment1
            (exponentAt monomial (start + 1)) *
          (gaussianMoment1
              (exponentAt monomial (start + 1 + 1)) *
            (gaussianMoment1
                (exponentAt monomial
                  (start + 1 + 1 + 1)) *
              gaussianMomentRange
                (start + 1 + 1 + 1 + 1)
                coordinates monomial))) ≈
      gaussianMoment4
          (exponentAt monomial start)
          (exponentAt monomial (start + 1))
          (exponentAt monomial (start + 2))
          (exponentAt monomial (start + 3)) *
        gaussianMomentRange
          (start + 4) coordinates monomial
  let g0 := gaussianMoment1 (exponentAt monomial start)
  let g1 := gaussianMoment1 (exponentAt monomial (start + 1))
  let g2 := gaussianMoment1 (exponentAt monomial (start + 2))
  let g3 := gaussianMoment1 (exponentAt monomial (start + 3))
  let tail :=
    gaussianMomentRange (start + 4) coordinates monomial
  have hstart1 : start + 1 + 1 = start + 2 := by omega
  have hstart2 : start + 2 + 1 = start + 3 := by omega
  have hstart3 : start + 3 + 1 = start + 4 := by omega
  rw [hstart1, hstart2, hstart3]
  refine Q'.eqv_trans _
    ((g0 * (g1 * (g2 * g3))) * tail) _ ?_ ?_
  · refine Q'.eqv_trans _
      (g0 * (g1 * ((g2 * g3) * tail))) _
      (Q'.mul_eqv_congr_left g0 _ _
        (Q'.mul_eqv_congr_left g1 _ _
          (Q'.eqv_symm
            (Q'.mul_assoc_eqv g2 g3 tail)))) ?_
    refine Q'.eqv_trans _
      (g0 * ((g1 * (g2 * g3)) * tail)) _
      (Q'.mul_eqv_congr_left g0 _ _
        (Q'.eqv_symm
          (Q'.mul_assoc_eqv
            g1 (g2 * g3) tail))) ?_
    exact Q'.eqv_symm
      (Q'.mul_assoc_eqv
        g0 (g1 * (g2 * g3)) tail)
  · exact Q'.mul_eqv_congr_right _ _ tail
      (Q'.eqv_symm
        (gaussianMoment4_eq_tensor
          (exponentAt monomial start)
          (exponentAt monomial (start + 1))
          (exponentAt monomial (start + 2))
          (exponentAt monomial (start + 3))))

private theorem pair_halfDegree_eq
    {blocks : Nat} {degrees : Nat → Nat}
    {left right : List Nat}
    (hparity :
      SameQuaternionParity blocks left right)
    (hleft :
      HasQuaternionBlockDegrees
        blocks degrees left)
    (hright :
      HasQuaternionBlockDegrees
        blocks degrees right) :
    ∀ block, block < blocks →
      halfDegree4
          (exponentAt (monoMul left right)
            (4 * block))
          (exponentAt (monoMul left right)
            (4 * block + 1))
          (exponentAt (monoMul left right)
            (4 * block + 2))
          (exponentAt (monoMul left right)
            (4 * block + 3)) =
        degrees block := by
  intro block hblock
  have hp0 := hparity (4 * block) (by omega)
  have hp1 := hparity (4 * block + 1) (by omega)
  have hp2 := hparity (4 * block + 2) (by omega)
  have hp3 := hparity (4 * block + 3) (by omega)
  have hdleft := hleft block hblock
  have hdright := hright block hblock
  unfold quaternionBlockDegree at hdleft hdright
  unfold halfDegree4
  simp only [exponentAt_monoMul]
  omega

private theorem haarRange_mul_radial_eq_gaussian
    (monomial : List Nat)
    (degrees : Nat → Nat) :
    ∀ (start startBlock blocks : Nat),
      (∀ offset, offset < blocks →
        halfDegree4
            (exponentAt monomial
              (start + 4 * offset))
            (exponentAt monomial
              (start + 4 * offset + 1))
            (exponentAt monomial
              (start + 4 * offset + 2))
            (exponentAt monomial
              (start + 4 * offset + 3)) =
          degrees (startBlock + offset)) →
      quaternionHaarRange start blocks monomial *
          quaternionRadialFactor
            degrees startBlock blocks ≈
        gaussianMomentRange
          start (4 * blocks) monomial
  | _, _, 0, _ => Q'.mul_one_eqv 1
  | start, startBlock, blocks + 1, hdegree => by
      unfold quaternionHaarRange quaternionRadialFactor
      let sphere :=
        sphereMoment4
          (exponentAt monomial start)
          (exponentAt monomial (start + 1))
          (exponentAt monomial (start + 2))
          (exponentAt monomial (start + 3))
      let denominator :=
        Q'.ofNat
          (sphereFourDenominator
            (degrees startBlock))
      let haarTail :=
        quaternionHaarRange
          (start + 4) blocks monomial
      let radialTail :=
        quaternionRadialFactor
          degrees (startBlock + 1) blocks
      have hhead :
          halfDegree4
              (exponentAt monomial start)
              (exponentAt monomial (start + 1))
              (exponentAt monomial (start + 2))
              (exponentAt monomial (start + 3)) =
            degrees startBlock := by
        simpa using hdegree 0 (by omega)
      have htailDegree :
          ∀ offset, offset < blocks →
            halfDegree4
                (exponentAt monomial
                  (start + 4 + 4 * offset))
                (exponentAt monomial
                  (start + 4 + 4 * offset + 1))
                (exponentAt monomial
                  (start + 4 + 4 * offset + 2))
                (exponentAt monomial
                  (start + 4 + 4 * offset + 3)) =
              degrees (startBlock + 1 + offset) := by
        intro offset hoffset
        have h := hdegree (offset + 1) (by omega)
        have hcoordinate :
            start + 4 * (offset + 1) =
              start + 4 + 4 * offset := by
          omega
        have hblock :
            startBlock + (offset + 1) =
              startBlock + 1 + offset := by
          omega
        rw [hcoordinate, hblock] at h
        exact h
      have htail :=
        haarRange_mul_radial_eq_gaussian
          monomial degrees
          (start + 4) (startBlock + 1)
          blocks htailDegree
      have hradial :
          sphere * denominator ≈
            gaussianMoment4
              (exponentAt monomial start)
              (exponentAt monomial (start + 1))
              (exponentAt monomial (start + 2))
              (exponentAt monomial (start + 3)) := by
        unfold sphere denominator
        rw [← hhead]
        exact sphereMoment4_mul_radialDenominator _ _ _ _
      refine Q'.eqv_trans _
        ((sphere * denominator) *
          (haarTail * radialTail)) _
        (q_mul4_swap sphere haarTail
          denominator radialTail) ?_
      refine Q'.eqv_trans _
        (gaussianMoment4
            (exponentAt monomial start)
            (exponentAt monomial (start + 1))
            (exponentAt monomial (start + 2))
            (exponentAt monomial (start + 3)) *
          gaussianMomentRange
            (start + 4) (4 * blocks) monomial) _
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right _ _ _
            hradial)
          (Q'.mul_eqv_congr_left _ _ _
            htail)) ?_
      have hcount :
          4 * (blocks + 1) = 4 + 4 * blocks := by
        omega
      rw [hcount]
      exact Q'.eqv_symm
        (gaussianMomentRange_four
          start (4 * blocks) monomial)

private theorem quaternionHaar_monomialPair_radial
    {blocks : Nat} {degrees : Nat → Nat}
    {left right : RatTerm}
    (hleftSupport : left.1.length ≤ 4 * blocks)
    (hrightSupport : right.1.length ≤ 4 * blocks)
    (hparity :
      SameQuaternionParity
        blocks left.1 right.1)
    (hleftDegree :
      HasQuaternionBlockDegrees
        blocks degrees left.1)
    (hrightDegree :
      HasQuaternionBlockDegrees
        blocks degrees right.1) :
    ((left.2 * right.2) *
        quaternionHaarMono blocks
          (monoMul left.1 right.1)) *
        quaternionRadialFactor degrees 0 blocks ≈
      (left.2 * right.2) *
        arbitraryGaussianMono (4 * blocks)
          (monoMul left.1 right.1) := by
  let monomial := monoMul left.1 right.1
  have hsupport :
      monomial.length ≤ 4 * blocks :=
    monoMul_length_le
      hleftSupport hrightSupport
  have htail :
      allZero
          (monomial.drop (4 * blocks)) =
        true :=
    allZero_of_drop_nil _
      (List.drop_eq_nil_of_le hsupport)
  have hprefix :
      quaternionHaarPrefix blocks monomial ≈
        quaternionHaarRange 0 blocks monomial := by
    simpa using
      quaternionHaarPrefix_drop_eq_range
        monomial 0 blocks
  have hdegrees :
      ∀ offset, offset < blocks →
        halfDegree4
            (exponentAt monomial (4 * offset))
            (exponentAt monomial (4 * offset + 1))
            (exponentAt monomial (4 * offset + 2))
            (exponentAt monomial (4 * offset + 3)) =
          degrees offset := by
    intro offset hoffset
    simpa [monomial] using
      pair_halfDegree_eq hparity
        hleftDegree hrightDegree
        offset hoffset
  have hradial :=
    haarRange_mul_radial_eq_gaussian
      monomial degrees 0 0 blocks
      (by simpa using hdegrees)
  unfold quaternionHaarMono
  rw [if_pos htail]
  unfold arbitraryGaussianMono
  refine Q'.eqv_trans _
    ((left.2 * right.2) *
      (quaternionHaarPrefix blocks monomial *
        quaternionRadialFactor degrees 0 blocks)) _
    (Q'.mul_assoc_eqv _ _ _) ?_
  exact Q'.mul_eqv_congr_left
    (left.2 * right.2) _ _
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _
        hprefix)
      hradial)

/-- Raw Haar row and bilinear folds for an arbitrary number of quaternion
blocks. -/
def quaternionHaarRow
    (blocks : Nat) (source : RatTerm) :
    RatPoly → Q'
  | [] => 0
  | target :: rest =>
      (source.2 * target.2) *
          quaternionHaarMono blocks
            (monoMul source.1 target.1) +
        quaternionHaarRow blocks source rest

def quaternionHaarBilinear
    (blocks : Nat) :
    RatPoly → RatPoly → Q'
  | [], _ => 0
  | source :: rest, target =>
      quaternionHaarRow blocks source target +
        quaternionHaarBilinear blocks rest target

private theorem quaternionHaar_append
    (blocks : Nat) :
    ∀ left right : RatPoly,
      quaternionHaar blocks (left ++ right) ≈
        quaternionHaar blocks left +
          quaternionHaar blocks right
  | [], right =>
      Q'.eqv_symm
        (QPoly.q_zero_add_eqv
          (quaternionHaar blocks right))
  | term :: rest, right => by
      change
        term.2 * quaternionHaarMono blocks term.1 +
            quaternionHaar blocks (rest ++ right) ≈
          (term.2 * quaternionHaarMono blocks term.1 +
              quaternionHaar blocks rest) +
            quaternionHaar blocks right
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left _ _ _
          (quaternionHaar_append blocks rest right)) ?_
      exact Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)

private theorem quaternionHaar_map_row
    (blocks : Nat) (source : RatTerm) :
    ∀ target : RatPoly,
      quaternionHaar blocks
          (target.map fun term =>
            (monoMul source.1 term.1,
              source.2 * term.2)) ≈
        quaternionHaarRow blocks source target
  | [] => Q'.eqv_refl 0
  | term :: rest => by
      exact Q'.add_eqv_congr_left _ _ _
        (quaternionHaar_map_row
          blocks source rest)

theorem quaternionHaar_polyMul
    (blocks : Nat) :
    ∀ left right : RatPoly,
      quaternionHaar blocks (polyMul left right) ≈
        quaternionHaarBilinear blocks left right
  | [], _ => Q'.eqv_refl 0
  | source :: rest, right => by
      unfold polyMul List.flatMap
      refine Q'.eqv_trans _
        (quaternionHaar blocks
            (right.map fun target =>
              (monoMul source.1 target.1,
                source.2 * target.2)) +
          quaternionHaar blocks
            (polyMul rest right)) _
        (quaternionHaar_append blocks _ _) ?_
      exact QPoly.q_add_congr
        (quaternionHaar_map_row
          blocks source right)
        (quaternionHaar_polyMul
          blocks rest right)

private theorem quaternionHaarRow_mul_radial
    (blocks : Nat) (degrees : Nat → Nat)
    (source : RatTerm)
    (hsourceSupport :
      source.1.length ≤ 4 * blocks)
    (hsourceDegree :
      HasQuaternionBlockDegrees
        blocks degrees source.1) :
    ∀ target : RatPoly,
      SupportedQuaternionBlocks blocks target →
      (∀ term, term ∈ target →
        SameQuaternionParity
          blocks source.1 term.1) →
      (∀ term, term ∈ target →
        HasQuaternionBlockDegrees
          blocks degrees term.1) →
      quaternionHaarRow blocks source target *
          quaternionRadialFactor degrees 0 blocks ≈
        arbitraryGaussianRow
          (4 * blocks) source target
  | [], _, _, _ => Q'.zero_mul_eqv _
  | term :: rest, hsupport, hparity, hdegree => by
      change
        (((source.2 * term.2) *
              quaternionHaarMono blocks
                (monoMul source.1 term.1)) +
            quaternionHaarRow blocks source rest) *
            quaternionRadialFactor degrees 0 blocks ≈
          (source.2 * term.2) *
              arbitraryGaussianMono (4 * blocks)
                (monoMul source.1 term.1) +
            arbitraryGaussianRow
              (4 * blocks) source rest
      refine Q'.eqv_trans _
        (((source.2 * term.2) *
              quaternionHaarMono blocks
                (monoMul source.1 term.1)) *
            quaternionRadialFactor degrees 0 blocks +
          quaternionHaarRow blocks source rest *
            quaternionRadialFactor degrees 0 blocks) _
        (Q'.add_mul_eqv _ _ _) ?_
      exact QPoly.q_add_congr
        (quaternionHaar_monomialPair_radial
          hsourceSupport
          (hsupport term (by simp))
          (hparity term (by simp))
          hsourceDegree
          (hdegree term (by simp)))
        (quaternionHaarRow_mul_radial
          blocks degrees source
          hsourceSupport hsourceDegree rest
          (fun other hother =>
            hsupport other (by simp [hother]))
          (fun other hother =>
            hparity other (by simp [hother]))
          (fun other hother =>
            hdegree other (by simp [hother])))

private theorem quaternionHaarBilinear_mul_radial
    (blocks : Nat) (degrees : Nat → Nat) :
    ∀ leftPolynomial rightPolynomial : RatPoly,
      SupportedQuaternionBlocks blocks leftPolynomial →
      SupportedQuaternionBlocks blocks rightPolynomial →
      (∀ left, left ∈ leftPolynomial →
        ∀ right, right ∈ rightPolynomial →
          SameQuaternionParity
            blocks left.1 right.1) →
      (∀ term, term ∈ leftPolynomial →
        HasQuaternionBlockDegrees
          blocks degrees term.1) →
      (∀ term, term ∈ rightPolynomial →
        HasQuaternionBlockDegrees
          blocks degrees term.1) →
      quaternionHaarBilinear
          blocks leftPolynomial rightPolynomial *
          quaternionRadialFactor degrees 0 blocks ≈
        arbitraryGaussianBilinear
          (4 * blocks) leftPolynomial rightPolynomial
  | [], _, _, _, _, _, _ => Q'.zero_mul_eqv _
  | source :: rest, rightPolynomial,
      hleftSupport, hrightSupport, hparity,
      hleftDegree, hrightDegree => by
      change
        (quaternionHaarRow
              blocks source rightPolynomial +
            quaternionHaarBilinear
              blocks rest rightPolynomial) *
            quaternionRadialFactor degrees 0 blocks ≈
          arbitraryGaussianRow
              (4 * blocks) source rightPolynomial +
            arbitraryGaussianBilinear
              (4 * blocks) rest rightPolynomial
      refine Q'.eqv_trans _
        (quaternionHaarRow
              blocks source rightPolynomial *
              quaternionRadialFactor degrees 0 blocks +
          quaternionHaarBilinear
              blocks rest rightPolynomial *
              quaternionRadialFactor degrees 0 blocks) _
        (Q'.add_mul_eqv _ _ _) ?_
      exact QPoly.q_add_congr
        (quaternionHaarRow_mul_radial
          blocks degrees source
          (hleftSupport source (by simp))
          (hleftDegree source (by simp))
          rightPolynomial
          hrightSupport
          (fun term hterm =>
            hparity source (by simp)
              term hterm)
          hrightDegree)
        (quaternionHaarBilinear_mul_radial
          blocks degrees rest rightPolynomial
          (fun term hterm =>
            hleftSupport term (by simp [hterm]))
          hrightSupport
          (fun left hleft right hright =>
            hparity left (by simp [hleft])
              right hright)
          (fun term hterm =>
            hleftDegree term (by simp [hterm]))
          hrightDegree)

/-- Exact radial transfer for a fixed arbitrary-product parity/degree
sector. -/
theorem quaternionHaar_square_mul_radial_eq_gaussian
    (blocks : Nat) (degrees : Nat → Nat)
    (polynomial : RatPoly)
    (hsupport :
      SupportedQuaternionBlocks blocks polynomial)
    (hparity :
      ∀ left, left ∈ polynomial →
        ∀ right, right ∈ polynomial →
          SameQuaternionParity
            blocks left.1 right.1)
    (hdegree :
      ∀ term, term ∈ polynomial →
        HasQuaternionBlockDegrees
          blocks degrees term.1) :
    quaternionHaar blocks
          (polyMul polynomial polynomial) *
        quaternionRadialFactor degrees 0 blocks ≈
      arbitraryGaussian (4 * blocks)
        (polyMul polynomial polynomial) := by
  refine Q'.eqv_trans _
    (quaternionHaarBilinear
        blocks polynomial polynomial *
      quaternionRadialFactor degrees 0 blocks) _
    (Q'.mul_eqv_congr_right _ _ _
      (quaternionHaar_polyMul
        blocks polynomial polynomial)) ?_
  refine Q'.eqv_trans _
    (arbitraryGaussianBilinear
        (4 * blocks) polynomial polynomial) _
    (quaternionHaarBilinear_mul_radial
      blocks degrees polynomial polynomial
      hsupport hsupport hparity hdegree hdegree) ?_
  exact Q'.eqv_symm
    (arbitraryGaussian_polyMul
      (4 * blocks) polynomial polynomial)

/-- **Arbitrary-product Haar positivity on every fixed radial/parity
sector.** -/
theorem quaternionHaar_square_nonnegative_of_fixed_sector
    (blocks : Nat) (degrees : Nat → Nat)
    (polynomial : RatPoly)
    (hsupport :
      SupportedQuaternionBlocks blocks polynomial)
    (hparity :
      ∀ left, left ∈ polynomial →
        ∀ right, right ∈ polynomial →
          SameQuaternionParity
            blocks left.1 right.1)
    (hdegree :
      ∀ term, term ∈ polynomial →
        HasQuaternionBlockDegrees
          blocks degrees term.1) :
    (0 : Q') ≤
      quaternionHaar blocks
        (polyMul polynomial polynomial) := by
  have hgaussian :=
    arbitraryGaussian_square_nonnegative
      (4 * blocks) polynomial
  have htransfer :=
    quaternionHaar_square_mul_radial_eq_gaussian
      blocks degrees polynomial
      hsupport hparity hdegree
  have hscaled :
      (0 : Q') ≤
        quaternionHaar blocks
            (polyMul polynomial polynomial) *
          quaternionRadialFactor
            degrees 0 blocks :=
    Q'.le_trans' _ _ _ hgaussian
      (Q'.le_of_eqv
        (Q'.eqv_symm htransfer))
  have hcommuted :
      (0 : Q') ≤
        quaternionRadialFactor
            degrees 0 blocks *
          quaternionHaar blocks
            (polyMul polynomial polynomial) :=
    Q'.le_trans' _ _ _ hscaled
      (Q'.le_of_eqv
        (Q'.eqv_symm
          (Q'.mul_comm_eqv
            (quaternionRadialFactor
              degrees 0 blocks)
            (quaternionHaar blocks
              (polyMul polynomial polynomial)))))
  exact Q'.nonneg_of_mul_pos
    (quaternionRadialFactor_positive
      degrees 0 blocks)
    hcommuted

end YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity

#print axioms YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity.quaternionRadialFactor_positive
#print axioms YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity.quaternionHaar_polyMul
#print axioms YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity.quaternionHaar_square_mul_radial_eq_gaussian
#print axioms YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity.quaternionHaar_square_nonnegative_of_fixed_sector
