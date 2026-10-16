/-
# Exact Cayley spatial-cubic rows and their half-square

For one directed Cayley plaquette, the cubic spatial heat-action coefficient
is `V3 = H3/4`, hence four times the sum of the four ordered triple
determinants.  This leaf expands that coefficient into its twenty-four signed
ordered three-row words.  It then expands the ordered product of any two such
finite cubic block lists into weighted six-row words, retaining the exact
factor `1/2` required by `V3^2/2`.

The coefficient certificate is purely finite polynomial algebra.  It does
not select an open-cube face family, take a Gaussian expectation, discard
cross-face or cross-time pairs, prove a sign or uniform estimate, compare the
ORIGINAL law, or establish a physical mass gap.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianTwoTwoSixCumulant
import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSpatialHeatActionCumulant

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianCayleyCubicPairTerms

set_option autoImplicit false

open YMGap.Constructive
open YMGap.RepTheory.RationalQuaternionSphereNets
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4ExactSlabPlaquetteCayleyExpansion
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFiniteGaussianRowWordWick
open YMGap.Continuum.SU2QuaternionFiniteGaussianNormalizedCayleyQuarticTerms
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSpatialHeatActionCumulant

local infix:50 " ≈ " => Q'.eqv

/-- Exact coefficient `1/2` in the cubic half-square. -/
def cubicPairHalf : Q' := Q'.mkPos 1 2 (by decide)

/-- Rational value of one spatial heat-action cubic coefficient. -/
def cayleySpatialCubicValue (a b c d : Triple) : Q' :=
  4 * ((det3 a b c + det3 a b d) +
    (det3 a c d + det3 b c d))

/-- The displayed cubic value is exactly `H3/4`, with no denominator or
continuum-vertex substitution. -/
theorem cayleySpatialCubicValue_eq_H3_quarter (a b c d : Triple) :
    cayleySpatialCubicValue a b c d ≈ spatialHeatQuarter * H3 a b c d := by
  unfold cayleySpatialCubicValue spatialHeatQuarter H3
  let value := (det3 a b c + det3 a b d) +
    (det3 a c d + det3 b c d)
  have hconstant : (4 : Q') ≈ Q'.mkPos 1 4 (by decide) * 16 := by
    decide
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right 4
      (Q'.mkPos 1 4 (by decide) * 16) value hconstant)
    (Q'.mul_assoc_eqv (Q'.mkPos 1 4 (by decide)) 16 value)

/-- A rationally weighted ordered cubic row word. -/
structure WeightedCubicRowBlock where
  weight : Q'
  first : Nat → Q'
  second : Nat → Q'
  third : Nat → Q'

/-- A rationally weighted ordered sextic row word. -/
structure WeightedSexticRowBlock where
  weight : Q'
  first : Nat → Q'
  second : Nat → Q'
  third : Nat → Q'
  fourth : Nat → Q'
  fifth : Nat → Q'
  sixth : Nat → Q'

def weightedCubicRowBlockTerm (N : Nat)
    (term : WeightedCubicRowBlock) : Q' × RatPoly :=
  (term.weight,
    finiteGaussianRowWord N [term.first, term.second, term.third])

def weightedSexticRowBlockTerm (N : Nat)
    (term : WeightedSexticRowBlock) : Q' × RatPoly :=
  (term.weight,
    finiteGaussianRowWord N
      [term.first, term.second, term.third,
        term.fourth, term.fifth, term.sixth])

/-- The six signed coordinate words of `weight * det(x,y,z)`. -/
def finiteGaussianDeterminantCubicRowBlocks (weight : Q')
    (x y z : Nat → Nat → Q') : List WeightedCubicRowBlock :=
  [ { weight := weight
      first := x 1, second := y 2, third := z 0 },
    { weight := -weight
      first := x 2, second := y 1, third := z 0 },
    { weight := weight
      first := x 2, second := y 0, third := z 1 },
    { weight := -weight
      first := x 0, second := y 2, third := z 1 },
    { weight := weight
      first := x 0, second := y 1, third := z 2 },
    { weight := -weight
      first := x 1, second := y 0, third := z 2 } ]

/-- The twenty-four signed row words of the literal `H3/4` coefficient. -/
def finiteGaussianCayleySpatialCubicRowBlocks
    (a b c d : Nat → Nat → Q') : List WeightedCubicRowBlock :=
  finiteGaussianDeterminantCubicRowBlocks 4 a b c ++
    (finiteGaussianDeterminantCubicRowBlocks 4 a b d ++
      (finiteGaussianDeterminantCubicRowBlocks 4 a c d ++
        finiteGaussianDeterminantCubicRowBlocks 4 b c d))

/-- Literal finite polynomial of the exact spatial cubic coefficient. -/
def finiteGaussianCayleySpatialCubicPolynomial (N : Nat)
    (a b c d : Nat → Nat → Q') : RatPoly :=
  weightedTermPolynomial
    ((finiteGaussianCayleySpatialCubicRowBlocks a b c d).map
      (weightedCubicRowBlockTerm N))

/-- Full ordered Cartesian product of two cubic block lists. -/
def finiteGaussianOrderedCubicBlockPairs
    (left right : List WeightedCubicRowBlock) :
    List (WeightedCubicRowBlock × WeightedCubicRowBlock) :=
  left.flatMap fun leftTerm =>
    right.map fun rightTerm => (leftTerm, rightTerm)

/-- One ordered cubic-block pair, retaining the exact half-square weight. -/
def finiteGaussianCubicBlockPairSexticRowBlock
    (pair : WeightedCubicRowBlock × WeightedCubicRowBlock) :
    WeightedSexticRowBlock :=
  { weight := cubicPairHalf * (pair.1.weight * pair.2.weight)
    first := pair.1.first
    second := pair.1.second
    third := pair.1.third
    fourth := pair.2.first
    fifth := pair.2.second
    sixth := pair.2.third }

/-- Full ordered cubic-block pair list with the exact half-square weight.
No symmetry quotient is taken, so every off-diagonal pair occurs twice. -/
def finiteGaussianCubicPairSexticRowBlocks
    (left right : List WeightedCubicRowBlock) :
    List WeightedSexticRowBlock :=
  (finiteGaussianOrderedCubicBlockPairs left right).map
    finiteGaussianCubicBlockPairSexticRowBlock

/-- Literal weighted six-row polynomial of the cubic half-product. -/
def finiteGaussianCubicPairPolynomial (N : Nat)
    (left right : List WeightedCubicRowBlock) : RatPoly :=
  weightedTermPolynomial
    ((finiteGaussianCubicPairSexticRowBlocks left right).map
      (weightedSexticRowBlockTerm N))

private theorem polySum_congr {A : Type} (f g : A → RatPoly) :
    ∀ items : List A,
      (∀ item, item ∈ items → RatPolyCoeffEqv (f item) (g item)) →
      RatPolyCoeffEqv (polySum (items.map f)) (polySum (items.map g))
  | [], _ => RatPolyCoeffEqv.refl _
  | item :: items, h => RatPolyCoeffEqv.add
      (h item List.mem_cons_self)
      (polySum_congr f g items
        (fun other hother => h other (List.mem_cons_of_mem item hother)))

private theorem polySum_map_polySum_flatMap {A : Type}
    (block : A → List RatPoly) : ∀ items : List A,
    RatPolyCoeffEqv
      (polySum (items.map fun item => polySum (block item)))
      (polySum (items.flatMap block))
  | [] => RatPolyCoeffEqv.refl _
  | item :: items =>
      RatPolyCoeffEqv.trans
        (RatPolyCoeffEqv.add (RatPolyCoeffEqv.refl _)
          (polySum_map_polySum_flatMap block items))
        (RatPolyCoeffEqv.polySum_append (block item)
          (items.flatMap block))

private theorem polySmul_polySum (weight : Q') : ∀ polynomials : List RatPoly,
    RatPolyCoeffEqv (polySmul weight (polySum polynomials))
      (polySum (polynomials.map fun polynomial =>
        polySmul weight polynomial))
  | [] => RatPolyCoeffEqv.zero_smul polyZero
  | polynomial :: polynomials =>
      RatPolyCoeffEqv.trans
        (RatPolyCoeffEqv.smul_add weight polynomial (polySum polynomials))
        (RatPolyCoeffEqv.add (RatPolyCoeffEqv.refl _)
          (polySmul_polySum weight polynomials))

private theorem scaled_cubic_terms_mul
    (N : Nat) (leftTerm rightTerm : WeightedCubicRowBlock) :
    RatPolyCoeffEqv
      (polyMul
        (polySmul leftTerm.weight
          (finiteGaussianRowWord N
            [leftTerm.first, leftTerm.second, leftTerm.third]))
        (polySmul rightTerm.weight
          (finiteGaussianRowWord N
            [rightTerm.first, rightTerm.second, rightTerm.third])))
      (polySmul (leftTerm.weight * rightTerm.weight)
        (finiteGaussianRowWord N
          [leftTerm.first, leftTerm.second, leftTerm.third,
            rightTerm.first, rightTerm.second, rightTerm.third])) := by
  have hscale : RatPolyCoeffEqv
      (polyMul
        (polySmul leftTerm.weight
          (finiteGaussianRowWord N
            [leftTerm.first, leftTerm.second, leftTerm.third]))
        (polySmul rightTerm.weight
          (finiteGaussianRowWord N
            [rightTerm.first, rightTerm.second, rightTerm.third])))
      (polySmul (leftTerm.weight * rightTerm.weight)
        (polyMul
          (finiteGaussianRowWord N
            [leftTerm.first, leftTerm.second, leftTerm.third])
          (finiteGaussianRowWord N
            [rightTerm.first, rightTerm.second, rightTerm.third]))) :=
    (RatPolyCoeffEqv.polyMul_smul_left leftTerm.weight _ _).trans
      (((RatPolyCoeffEqv.polyMul_smul_right rightTerm.weight _ _).smul
        leftTerm.weight).trans
        (RatPolyCoeffEqv.smul_assoc leftTerm.weight rightTerm.weight _))
  exact hscale.trans
    ((finiteGaussianRowWord_append_nonempty N
      leftTerm.first rightTerm.first
      [leftTerm.second, leftTerm.third]
      [rightTerm.second, rightTerm.third]).smul
        (leftTerm.weight * rightTerm.weight))

private theorem cubic_polynomials_mul
    (N : Nat) (left right : List WeightedCubicRowBlock) :
    RatPolyCoeffEqv
      (polyMul
        (weightedTermPolynomial
          (left.map (weightedCubicRowBlockTerm N)))
        (weightedTermPolynomial
          (right.map (weightedCubicRowBlockTerm N))))
      (polySum (left.flatMap fun leftTerm =>
        right.map fun rightTerm =>
          polySmul (leftTerm.weight * rightTerm.weight)
            (finiteGaussianRowWord N
              [leftTerm.first, leftTerm.second, leftTerm.third,
                rightTerm.first, rightTerm.second, rightTerm.third]))) := by
  have hflat := polySum_map_polySum_flatMap
    (fun leftTerm => right.map fun rightTerm =>
      polySmul (leftTerm.weight * rightTerm.weight)
        (finiteGaussianRowWord N
          [leftTerm.first, leftTerm.second, leftTerm.third,
            rightTerm.first, rightTerm.second, rightTerm.third]))
    left
  have houter := RatPolyCoeffEqv.polySum_mul_right
    (left.map fun term : WeightedCubicRowBlock =>
      polySmul term.weight
        (finiteGaussianRowWord N
          [term.first, term.second, term.third]))
    (polySum (right.map fun term : WeightedCubicRowBlock =>
      polySmul term.weight
        (finiteGaussianRowWord N
          [term.first, term.second, term.third])))
  have hrows : RatPolyCoeffEqv
      (polySum (left.map fun leftTerm =>
        polyMul
          (polySmul leftTerm.weight
            (finiteGaussianRowWord N
              [leftTerm.first, leftTerm.second, leftTerm.third]))
          (polySum (right.map fun rightTerm =>
            polySmul rightTerm.weight
              (finiteGaussianRowWord N
                [rightTerm.first, rightTerm.second, rightTerm.third])))))
      (polySum (left.map fun leftTerm =>
        polySum (right.map fun rightTerm =>
          polySmul (leftTerm.weight * rightTerm.weight)
            (finiteGaussianRowWord N
              [leftTerm.first, leftTerm.second, leftTerm.third,
                rightTerm.first, rightTerm.second, rightTerm.third])))) :=
    polySum_congr _ _ left (fun leftTerm _ =>
      RatPolyCoeffEqv.trans
        (RatPolyCoeffEqv.mul_polySum_right
          (polySmul leftTerm.weight
            (finiteGaussianRowWord N
              [leftTerm.first, leftTerm.second, leftTerm.third]))
          (right.map fun rightTerm =>
            polySmul rightTerm.weight
              (finiteGaussianRowWord N
                [rightTerm.first, rightTerm.second, rightTerm.third])))
        (by
          simp only [List.map_map]
          exact polySum_congr _ _ right (fun rightTerm _ =>
            scaled_cubic_terms_mul N leftTerm rightTerm)))
  unfold weightedTermPolynomial weightedCubicRowBlockTerm
  simp only [List.map_map]
  exact RatPolyCoeffEqv.trans houter
    (RatPolyCoeffEqv.trans (by simpa only [List.map_map] using hrows) hflat)

/-- The explicit ordered sextic list is coefficientwise equal to one half of
the product of the two corresponding cubic polynomials. -/
theorem finiteGaussianCubicPairPolynomial_coeffEqv
    (N : Nat) (left right : List WeightedCubicRowBlock) :
    RatPolyCoeffEqv
      (polySmul cubicPairHalf
        (polyMul
          (weightedTermPolynomial
            (left.map (weightedCubicRowBlockTerm N)))
          (weightedTermPolynomial
            (right.map (weightedCubicRowBlockTerm N)))))
      (finiteGaussianCubicPairPolynomial N left right) := by
  have hproduct := cubic_polynomials_mul N left right
  have hdistribute := polySmul_polySum cubicPairHalf
    (left.flatMap fun leftTerm =>
      right.map fun rightTerm =>
        polySmul (leftTerm.weight * rightTerm.weight)
          (finiteGaussianRowWord N
            [leftTerm.first, leftTerm.second, leftTerm.third,
              rightTerm.first, rightTerm.second, rightTerm.third]))
  have hleftList :
      ((left.flatMap fun leftTerm =>
        right.map fun rightTerm =>
          polySmul (leftTerm.weight * rightTerm.weight)
            (finiteGaussianRowWord N
              [leftTerm.first, leftTerm.second, leftTerm.third,
                rightTerm.first, rightTerm.second, rightTerm.third])).map
        (fun polynomial => polySmul cubicPairHalf polynomial)) =
      (finiteGaussianOrderedCubicBlockPairs left right).map fun pair =>
        polySmul cubicPairHalf
          (polySmul (pair.1.weight * pair.2.weight)
            (finiteGaussianRowWord N
              [pair.1.first, pair.1.second, pair.1.third,
                pair.2.first, pair.2.second, pair.2.third])) := by
    unfold finiteGaussianOrderedCubicBlockPairs
    simp only [List.map_flatMap, List.map_map]
    rfl
  have hrightList :
      (((finiteGaussianCubicPairSexticRowBlocks left right).map
        (weightedSexticRowBlockTerm N)).map
          (fun term => polySmul term.1 term.2)) =
      (finiteGaussianOrderedCubicBlockPairs left right).map fun pair =>
        polySmul (cubicPairHalf *
          (pair.1.weight * pair.2.weight))
          (finiteGaussianRowWord N
            [pair.1.first, pair.1.second, pair.1.third,
              pair.2.first, pair.2.second, pair.2.third]) := by
    unfold finiteGaussianCubicPairSexticRowBlocks
      finiteGaussianCubicBlockPairSexticRowBlock
      weightedSexticRowBlockTerm
    simp only [List.map_map]
    rfl
  exact (hproduct.smul cubicPairHalf).trans
    (hdistribute.trans (by
      unfold finiteGaussianCubicPairPolynomial weightedTermPolynomial
      rw [hleftList, hrightList]
      exact polySum_congr _ _
        (finiteGaussianOrderedCubicBlockPairs left right)
        (fun pair _ =>
          RatPolyCoeffEqv.smul_assoc cubicPairHalf
            (pair.1.weight * pair.2.weight) _)))

end YMGap.Continuum.SU2QuaternionFiniteGaussianCayleyCubicPairTerms

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianCayleyCubicPairTerms.cayleySpatialCubicValue_eq_H3_quarter
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianCayleyCubicPairTerms.finiteGaussianCubicPairPolynomial_coeffEqv
