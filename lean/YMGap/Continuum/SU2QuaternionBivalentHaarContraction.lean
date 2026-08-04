/-
# Fused bivalent quaternion Haar contraction

For a bivalent link the factorized contractor sees exactly two incident
polynomials.  A generic implementation first constructs their full product,
then applies the head `S^3` moment, then deletes all zero-moment terms.  This
module fuses those operations: it drops the integrated block while forming
each product term and filters exact rational zeros immediately.

The filtered direct product is proved to have the same rational canonical
form as the original partial Haar product.  Consequently the complete fused
recursion is definitionally equal to the audited compact factorized Haar
recursion.  This is an optimization theorem, not an additional evaluator
assumption.

## Axiom gate

Finite lists, exact rational arithmetic, and the existing factorized Haar
theorem only.  No Classical.*, native_decide, sorry, custom axiom, choice,
or noncomputable declaration.
-/

import YMGap.Continuum.SU2QuaternionFactorizedHaarContraction

namespace YMGap.Continuum.SU2QuaternionBivalentHaarContraction

set_option maxRecDepth 200000
set_option maxHeartbeats 12000000

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionHaarHeadConditionalProduct
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier

local infix:50 " ≈ " => Q'.eqv

private theorem drop_monoMul_local :
    ∀ (count : Nat) (left right : List Nat),
      (monoMul left right).drop count =
        monoMul (left.drop count) (right.drop count)
  | 0, left, right => by simp
  | count + 1, [], right => by simp [monoMul]
  | count + 1, left, [] => by
      rw [monoMul_right_nil_local, List.drop_nil,
        monoMul_right_nil_local]
  | count + 1, _ :: left, _ :: right => by
      simp only [monoMul, List.drop_succ_cons]
      exact drop_monoMul_local count left right
where
  monoMul_right_nil_local : ∀ monomial : List Nat,
      monoMul monomial [] = monomial
    | [] => rfl
    | _ :: _ => by simp only [monoMul]

/-- One product term with its head moment already applied and its four head
coordinates already removed. -/
def directPartialHaarProductTerm
    (source target : RatTerm) : RatTerm :=
  (monoMul (source.1.drop 4) (target.1.drop 4),
    (source.2 * target.2) *
      headQuaternionMoment (monoMul source.1 target.1))

/-- Unfiltered fused multiplication and one-block Haar integration. -/
def directPartialHaarProductRaw
    (left right : RatPoly) : RatPoly :=
  left.flatMap fun source =>
    right.map fun target => directPartialHaarProductTerm source target

/-- The fused raw operation is literally the ordinary product followed by
`partialHaarHead`; only the construction order differs. -/
theorem partialHaarHead_polyMul_eq_directRaw :
    ∀ left right : RatPoly,
      partialHaarHead (polyMul left right) =
        directPartialHaarProductRaw left right
  | [], _ => rfl
  | source :: rest, right => by
      simp only [polyMul, partialHaarHead, List.flatMap_cons,
        List.map_append, List.map_map, directPartialHaarProductRaw]
      congr 1
      · apply List.map_congr_left
        intro target _
        simp only [Function.comp_apply, partialHaarHeadTerm,
          directPartialHaarProductTerm]
        congr 2
        exact drop_monoMul_local 4 source.1 target.1
      · exact partialHaarHead_polyMul_eq_directRaw rest right

def nonzeroCoeffTerms (polynomial : RatPoly) : RatPoly :=
  polynomial.filter fun term => decide (term.2.num ≠ 0)

/-- Deleting exact rational-zero coefficients before canonicalization changes
nothing. -/
theorem canonRat_nonzeroCoeffTerms : ∀ polynomial : RatPoly,
    canonRat (nonzeroCoeffTerms polynomial) = canonRat polynomial
  | [] => rfl
  | term :: rest => by
      by_cases hzero : term.2.num = 0
      · have hdrop : decide (term.2.num ≠ 0) = false :=
          decide_eq_false (fun hne => hne hzero)
        rw [show nonzeroCoeffTerms (term :: rest) =
            nonzeroCoeffTerms rest by
          simp only [nonzeroCoeffTerms, List.filter_cons, hdrop,
            Bool.false_eq_true, if_false]]
        change canonRat (nonzeroCoeffTerms rest) =
          insertRatTerm term.1 term.2 (canonRat rest)
        rw [canonRat_nonzeroCoeffTerms rest]
        cases hrest : canonRat rest with
        | nil => simp [insertRatTerm, hzero]
        | cons _ _ => simp [insertRatTerm, hzero]
      · have hkeep : decide (term.2.num ≠ 0) = true :=
          decide_eq_true hzero
        rw [show nonzeroCoeffTerms (term :: rest) =
            term :: nonzeroCoeffTerms rest by
          simp only [nonzeroCoeffTerms, List.filter_cons, hkeep, if_true]]
        change insertRatTerm term.1 term.2
            (canonRat (nonzeroCoeffTerms rest)) =
          insertRatTerm term.1 term.2 (canonRat rest)
        rw [canonRat_nonzeroCoeffTerms rest]

/-- Production fused operation: zero-moment terms are discarded as soon as
they are formed. -/
def directPartialHaarProduct
    (left right : RatPoly) : RatPoly :=
  left.flatMap fun source =>
    (right.map fun target =>
      directPartialHaarProductTerm source target).filter fun term =>
        decide (term.2.num ≠ 0)

theorem directPartialHaarProduct_eq_filter
    (left right : RatPoly) :
    directPartialHaarProduct left right =
      nonzeroCoeffTerms (directPartialHaarProductRaw left right) := by
  induction left with
  | nil => rfl
  | cons source rest induction =>
      simp only [directPartialHaarProduct,
        directPartialHaarProductRaw, nonzeroCoeffTerms,
        List.flatMap_cons, List.filter_append]
      congr 1

/-- The fused filtered operation has exactly the ordinary partial product's
canonical rational form. -/
theorem canonRat_directPartialHaarProduct
    (left right : RatPoly) :
    canonRat (directPartialHaarProduct left right) =
      canonRat (partialHaarHead (polyMul left right)) := by
  rw [directPartialHaarProduct_eq_filter,
    canonRat_nonzeroCoeffTerms,
    partialHaarHead_polyMul_eq_directRaw]

/-- Use the fused path precisely when two factors meet the head block; retain
the generic audited path at all other valences. -/
def bivalentFactorizedHeadStep (factors : List RatPoly) : List RatPoly :=
  let incident := headIncidentFactors factors
  let integrated :=
    match incident with
    | [left, right] =>
        canonRat
          (directPartialHaarProduct left (polyMul right polyOne))
    | _ => canonRat (partialHaarHead (factorProduct incident))
  integrated ::
    (headIndependentFactors factors).map dropHeadPolynomial

/-- The fused bivalent head step is literally the original factorized step
after rational canonicalization. -/
theorem bivalentFactorizedHeadStep_eq (factors : List RatPoly) :
    bivalentFactorizedHeadStep factors = factorizedHeadStep factors := by
  unfold bivalentFactorizedHeadStep factorizedHeadStep
  cases headIncidentFactors factors with
  | nil => rfl
  | cons left rest =>
      cases rest with
      | nil => rfl
      | cons right tail =>
          cases tail with
          | nil =>
              simp only [factorProduct]
              rw [canonRat_directPartialHaarProduct]
          | cons _ _ => rfl

def compactBivalentFactorizedHeadStep
    (factors : List RatPoly) : List RatPoly :=
  nonUnitFactors (bivalentFactorizedHeadStep factors)

theorem compactBivalentFactorizedHeadStep_eq (factors : List RatPoly) :
    compactBivalentFactorizedHeadStep factors =
      compactFactorizedHeadStep factors := by
  unfold compactBivalentFactorizedHeadStep compactFactorizedHeadStep
  rw [bivalentFactorizedHeadStep_eq]

def compactBivalentFactorizedHaarContract :
    Nat → List RatPoly → RatPoly
  | 0, factors => factorProduct (nonUnitFactors factors)
  | blocks + 1, factors =>
      compactBivalentFactorizedHaarContract blocks
        (compactBivalentFactorizedHeadStep factors)

def compactBivalentFactorizedHaar
    (blocks : Nat) (factors : List RatPoly) : Q' :=
  quaternionHaar 0
    (compactBivalentFactorizedHaarContract blocks factors)

theorem compactBivalentFactorizedHaarContract_eq :
    ∀ (blocks : Nat) (factors : List RatPoly),
      compactBivalentFactorizedHaarContract blocks factors =
        compactFactorizedHaarContract blocks factors
  | 0, _ => rfl
  | blocks + 1, factors => by
      simp only [compactBivalentFactorizedHaarContract,
        compactFactorizedHaarContract]
      rw [compactBivalentFactorizedHeadStep_eq,
        compactBivalentFactorizedHaarContract_eq]

/-- Exactness of the complete optimized recursion. -/
theorem quaternionHaar_eq_compactBivalentFactorizedHaar
    (blocks : Nat) (factors : List RatPoly) :
    quaternionHaar blocks (factorProduct factors) ≈
      compactBivalentFactorizedHaar blocks factors := by
  unfold compactBivalentFactorizedHaar
  rw [compactBivalentFactorizedHaarContract_eq]
  exact quaternionHaar_eq_compactFactorizedHaar blocks factors

end YMGap.Continuum.SU2QuaternionBivalentHaarContraction

#print axioms YMGap.Continuum.SU2QuaternionBivalentHaarContraction.partialHaarHead_polyMul_eq_directRaw
#print axioms YMGap.Continuum.SU2QuaternionBivalentHaarContraction.canonRat_directPartialHaarProduct
#print axioms YMGap.Continuum.SU2QuaternionBivalentHaarContraction.bivalentFactorizedHeadStep_eq
#print axioms YMGap.Continuum.SU2QuaternionBivalentHaarContraction.quaternionHaar_eq_compactBivalentFactorizedHaar
