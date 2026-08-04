/-
# Exact factorized quaternion Haar contraction

This module gives a constructive variable-elimination algorithm for a product
of finite rational quaternion polynomials.  At each head block it multiplies
only incident factors, performs the exact normalized S^3 moment, canonicalizes
the small result, and carries independent factors forward.  The final theorem
proves that this factorized contraction is exactly the original product Haar
functional; it is an evaluator certificate, not a new axiom or semantic
shortcut.

## Axiom gate

Finite lists, exact rational polynomial algebra, and previously proved Haar
Fubini/permutation identities only.  No Classical.*, native_decide, sorry,
custom axiom, choice, or noncomputable declaration.
-/

import YMGap.Continuum.SU2QuaternionHaarHeadConditionalProduct
import YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
import YMGap.Continuum.BF4QuaternionHaarFactorFoldPerm
import YMGap.Continuum.BF4CompactActionCPOrder

namespace YMGap.Continuum.SU2QuaternionFactorizedHaarContraction

set_option maxRecDepth 200000
set_option maxHeartbeats 12000000

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionArbitraryHaarHomogenization
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHaarHeadConditionalProduct
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4QuaternionHaarFactorFoldPerm
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.SU2QuaternionArbitraryHaarFourSwap

local infix:50 " ≈ " => Q'.eqv

def factorProduct : List RatPoly -> RatPoly
  | [] => polyOne
  | factor :: rest => polyMul factor (factorProduct rest)

theorem factorProduct_eq_foldr (factors : List RatPoly) :
    factorProduct factors = factors.foldr polyMul polyOne := by
  induction factors with
  | nil => rfl
  | cons factor rest induction =>
      simp only [factorProduct, List.foldr]
      rw [induction]

def headIndependentCheck (polynomial : RatPoly) : Bool :=
  polynomial.all fun term => decide (headQuaternionDegree term.1 = 0)

theorem headIndependentCheck_sound {polynomial : RatPoly}
    (hcheck : headIndependentCheck polynomial = true) :
    HeadQuaternionIndependent polynomial := by
  intro term hterm
  exact of_decide_eq_true
    (List.all_eq_true.mp hcheck term hterm)

private theorem exponentAt_monoMul_local
    (left right : List Nat) (index : Nat) :
    exponentAt (monoMul left right) index =
      exponentAt left index + exponentAt right index := by
  induction left generalizing right index with
  | nil => simp [monoMul, exponentAt]
  | cons x xs induction =>
      cases right with
      | nil => simp [monoMul, exponentAt]
      | cons y ys =>
          cases index with
          | zero => simp [monoMul, exponentAt]
          | succ index =>
              change exponentAt (monoMul xs ys) index =
                exponentAt xs index + exponentAt ys index
              exact induction ys index

private theorem headQuaternionDegree_monoMul
    (left right : List Nat) :
    headQuaternionDegree (monoMul left right) =
      headQuaternionDegree left + headQuaternionDegree right := by
  unfold headQuaternionDegree
  rw [exponentAt_monoMul_local, exponentAt_monoMul_local,
    exponentAt_monoMul_local, exponentAt_monoMul_local]
  omega

theorem HeadQuaternionIndependent.polyMul
    {left right : RatPoly}
    (hleft : HeadQuaternionIndependent left)
    (hright : HeadQuaternionIndependent right) :
    HeadQuaternionIndependent (polyMul left right) := by
  intro term hterm
  unfold YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier.polyMul at hterm
  obtain ⟨source, hsource, hrow⟩ := List.mem_flatMap.mp hterm
  obtain ⟨target, htarget, heq⟩ := List.mem_map.mp hrow
  rw [← heq, headQuaternionDegree_monoMul,
    hleft source hsource, hright target htarget]

theorem factorProduct_headIndependent : forall factors : List RatPoly,
    (forall factor, factor ∈ factors -> HeadQuaternionIndependent factor) ->
      HeadQuaternionIndependent (factorProduct factors)
  | [], _ => by
      intro term hterm
      simp [factorProduct, polyOne] at hterm
      subst term
      rfl
  | factor :: rest, hall =>
      HeadQuaternionIndependent.polyMul
        (hall factor List.mem_cons_self)
        (factorProduct_headIndependent rest fun item hitem =>
          hall item (List.mem_cons_of_mem factor hitem))

private theorem drop_monoMul_local :
    forall (count : Nat) (left right : List Nat),
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
  monoMul_right_nil_local : forall monomial : List Nat,
      monoMul monomial [] = monomial
    | [] => rfl
    | _ :: _ => by simp only [monoMul]

theorem dropHeadPolynomial_polyMul (left right : RatPoly) :
    dropHeadPolynomial (polyMul left right) =
      polyMul (dropHeadPolynomial left) (dropHeadPolynomial right) := by
  induction left with
  | nil => rfl
  | cons source rest induction =>
      unfold dropHeadPolynomial at induction ⊢
      simp only [polyMul, List.flatMap_cons, List.map_append,
        List.map_cons, List.map_map]
      congr 1
      · apply List.map_congr_left
        intro target htarget
        simp [drop_monoMul_local]
      · simpa only [polyMul, List.map_map] using induction

theorem dropHeadPolynomial_factorProduct : forall factors : List RatPoly,
    dropHeadPolynomial (factorProduct factors) =
      factorProduct (factors.map dropHeadPolynomial)
  | [] => by rfl
  | factor :: rest => by
      simp only [factorProduct, List.map_cons]
      rw [dropHeadPolynomial_polyMul,
        dropHeadPolynomial_factorProduct rest]

def headIncidentFactors (factors : List RatPoly) : List RatPoly :=
  factors.filter fun factor => !headIndependentCheck factor

def headIndependentFactors (factors : List RatPoly) : List RatPoly :=
  factors.filter headIndependentCheck

theorem headFactor_partition_perm : forall factors : List RatPoly,
    (headIncidentFactors factors ++ headIndependentFactors factors).Perm
      factors
  | [] => List.Perm.nil
  | factor :: rest => by
      unfold headIncidentFactors headIndependentFactors
      simp only [List.filter_cons]
      cases hcheck : headIndependentCheck factor
      · simp only [Bool.not_false, if_true]
        exact List.Perm.cons factor (headFactor_partition_perm rest)
      · simp only [Bool.not_true, if_true]
        exact List.perm_middle.trans
          (List.Perm.cons factor (headFactor_partition_perm rest))

theorem independentFactors_sound (factors : List RatPoly) :
    forall factor, factor ∈ headIndependentFactors factors ->
      HeadQuaternionIndependent factor := by
  intro factor hfactor
  have hparts := List.mem_filter.mp hfactor
  exact headIndependentCheck_sound hparts.2

/-- Equality after exact Haar even in the presence of an arbitrary factor on
the left.  This is the congruence strength needed to reassociate a factor
network without asserting literal associativity of the list representation. -/
def HaarCarrierEqv (blocks : Nat) (left right : RatPoly) : Prop :=
  ∀ insertion : RatPoly,
    quaternionHaar blocks (polyMul insertion left) ≈
      quaternionHaar blocks (polyMul insertion right)

theorem HaarCarrierEqv.refl (blocks : Nat) (polynomial : RatPoly) :
    HaarCarrierEqv blocks polynomial polynomial := by
  intro insertion
  exact Q'.eqv_refl _

theorem HaarCarrierEqv.trans {blocks : Nat} {left middle right : RatPoly}
    (hleft : HaarCarrierEqv blocks left middle)
    (hright : HaarCarrierEqv blocks middle right) :
    HaarCarrierEqv blocks left right := by
  intro insertion
  exact Q'.eqv_trans _ _ _ (hleft insertion) (hright insertion)

theorem HaarCarrierEqv.symm {blocks : Nat} {left right : RatPoly}
    (h : HaarCarrierEqv blocks left right) :
    HaarCarrierEqv blocks right left := by
  intro insertion
  exact Q'.eqv_symm (h insertion)

theorem HaarCarrierEqv.mul_left {blocks : Nat} (factor : RatPoly)
    {left right : RatPoly} (h : HaarCarrierEqv blocks left right) :
    HaarCarrierEqv blocks (polyMul factor left) (polyMul factor right) := by
  intro insertion
  refine Q'.eqv_trans _
    (quaternionHaar blocks (polyMul (polyMul insertion factor) left)) _
    (Q'.eqv_symm
      (quaternionHaar_polyMul_assoc blocks insertion factor left)) ?_
  exact Q'.eqv_trans _ _ _
    (h (polyMul insertion factor))
    (quaternionHaar_polyMul_assoc blocks insertion factor right)

theorem haarCarrier_assoc (blocks : Nat) (first second third : RatPoly) :
    HaarCarrierEqv blocks
      (polyMul (polyMul first second) third)
      (polyMul first (polyMul second third)) := by
  intro insertion
  refine Q'.eqv_trans _
    (quaternionHaar blocks
      (polyMul insertion (polyMul third (polyMul first second)))) _
    (quaternionHaar_polyMul_middle_comm blocks insertion
      (polyMul first second) third) ?_
  refine Q'.eqv_trans _
    (quaternionHaar blocks
      (polyMul (polyMul insertion third) (polyMul first second))) _
    (Q'.eqv_symm
      (quaternionHaar_polyMul_assoc blocks insertion third
        (polyMul first second))) ?_
  refine Q'.eqv_trans _
    (quaternionHaar blocks
      (polyMul (polyMul insertion first) (polyMul third second))) _
    (quaternionHaar_polyMul_four_swap blocks insertion third first second) ?_
  refine Q'.eqv_trans _
    (quaternionHaar blocks
      (polyMul (polyMul insertion first) (polyMul second third))) _
    (quaternionHaar_polyMul_middle_comm blocks
      (polyMul insertion first) third second) ?_
  exact quaternionHaar_polyMul_assoc blocks insertion first
    (polyMul second third)

theorem haarCarrier_polyOne_left (blocks : Nat) (polynomial : RatPoly) :
    HaarCarrierEqv blocks (polyMul polyOne polynomial) polynomial := by
  intro insertion
  refine Q'.eqv_trans _
    (quaternionHaar blocks
      (polyMul insertion (polyMul polynomial polyOne))) _
    (quaternionHaar_polyMul_middle_comm blocks insertion
      polyOne polynomial) ?_
  refine Q'.eqv_trans _
    (quaternionHaar blocks
      (polyMul (polyMul insertion polynomial) polyOne)) _
    (Q'.eqv_symm
      (quaternionHaar_polyMul_assoc blocks insertion polynomial polyOne)) ?_
  exact quaternionHaar_polyMul_one_right blocks
    (polyMul insertion polynomial)

theorem factorProduct_append_carrier (blocks : Nat) :
    ∀ left right : List RatPoly,
      HaarCarrierEqv blocks (factorProduct (left ++ right))
        (polyMul (factorProduct left) (factorProduct right))
  | [], right => HaarCarrierEqv.symm
      (haarCarrier_polyOne_left blocks (factorProduct right))
  | factor :: rest, right => by
      simp only [List.cons_append, factorProduct]
      exact HaarCarrierEqv.trans
        (HaarCarrierEqv.mul_left factor
          (factorProduct_append_carrier blocks rest right))
        (HaarCarrierEqv.symm
          (haarCarrier_assoc blocks factor (factorProduct rest)
            (factorProduct right)))

private theorem quaternionHaar_polyOne_left
    (blocks : Nat) (polynomial : RatPoly) :
    quaternionHaar blocks (polyMul polyOne polynomial) ≈
      quaternionHaar blocks polynomial := by
  exact Q'.eqv_trans _
    (quaternionHaar blocks (polyMul polynomial polyOne)) _
    (quaternionHaar_polyMul_comm blocks polyOne polynomial)
    (quaternionHaar_polyMul_one_right blocks polynomial)

theorem quaternionHaar_factorProduct_perm
    (blocks : Nat) {left right : List RatPoly}
    (hperm : left.Perm right) :
    quaternionHaar blocks (factorProduct left) ≈
      quaternionHaar blocks (factorProduct right) := by
  refine Q'.eqv_trans _
    (quaternionHaar blocks (polyMul polyOne (factorProduct left))) _
    (Q'.eqv_symm
      (quaternionHaar_polyOne_left blocks (factorProduct left))) ?_
  refine Q'.eqv_trans _
    (quaternionHaar blocks (polyMul polyOne (factorProduct right))) _ ?_ ?_
  · rw [factorProduct_eq_foldr, factorProduct_eq_foldr]
    exact
      (quaternionHaar_factorFold_perm blocks (fun factor : RatPoly => factor)
        hperm polyOne)
  · exact quaternionHaar_polyOne_left blocks (factorProduct right)

def factorizedHeadStep (factors : List RatPoly) : List RatPoly :=
  canonRat (partialHaarHead (factorProduct (headIncidentFactors factors))) ::
    (headIndependentFactors factors).map dropHeadPolynomial

/-- One exact factorized elimination step: collect precisely the factors
incident on the head quaternion, integrate their small product, canonicalize
it, and carry every independent factor to the next block. -/
theorem quaternionHaar_factorizedHeadStep (blocks : Nat)
    (factors : List RatPoly) :
    quaternionHaar (blocks + 1) (factorProduct factors) ≈
      quaternionHaar blocks (factorProduct (factorizedHeadStep factors)) := by
  let incident := headIncidentFactors factors
  let independent := headIndependentFactors factors
  have hperm : (incident ++ independent).Perm factors :=
    headFactor_partition_perm factors
  have hindependent : HeadQuaternionIndependent (factorProduct independent) :=
    factorProduct_headIndependent independent
      (independentFactors_sound factors)
  refine Q'.eqv_trans _
    (quaternionHaar (blocks + 1)
      (factorProduct (incident ++ independent))) _
    (Q'.eqv_symm
      (quaternionHaar_factorProduct_perm (blocks + 1) hperm)) ?_
  refine Q'.eqv_trans _
    (quaternionHaar (blocks + 1)
      (polyMul (factorProduct incident) (factorProduct independent))) _
    ((factorProduct_append_carrier (blocks + 1) incident independent)
      polyOne |> fun h => Q'.eqv_trans _ _ _
        (Q'.eqv_symm (quaternionHaar_polyOne_left (blocks + 1) _))
        (Q'.eqv_trans _ _ _ h
          (quaternionHaar_polyOne_left (blocks + 1) _))) ?_
  refine Q'.eqv_trans _
    (quaternionHaar blocks
      (polyMul (partialHaarHead (factorProduct incident))
        (dropHeadPolynomial (factorProduct independent)))) _
    (quaternionHaar_polyMul_headIndependent blocks
      (factorProduct incident) (factorProduct independent) hindependent) ?_
  rw [dropHeadPolynomial_factorProduct]
  change quaternionHaar blocks
      (polyMul (partialHaarHead (factorProduct incident))
        (factorProduct (independent.map dropHeadPolynomial))) ≈
    quaternionHaar blocks
      (polyMul (canonRat (partialHaarHead (factorProduct incident)))
        (factorProduct (independent.map dropHeadPolynomial)))
  exact Q'.eqv_symm
    (quaternionHaar_canonRat_mul blocks
      (partialHaarHead (factorProduct incident))
      (factorProduct (independent.map dropHeadPolynomial)))

def factorizedHaarContract : Nat → List RatPoly → RatPoly
  | 0, factors => factorProduct factors
  | blocks + 1, factors =>
      factorizedHaarContract blocks (factorizedHeadStep factors)

def factorizedHaar (blocks : Nat) (factors : List RatPoly) : Q' :=
  quaternionHaar 0 (factorizedHaarContract blocks factors)

theorem quaternionHaar_eq_factorizedHaar :
    ∀ (blocks : Nat) (factors : List RatPoly),
      quaternionHaar blocks (factorProduct factors) ≈
        factorizedHaar blocks factors
  | 0, factors => Q'.eqv_refl _
  | blocks + 1, factors => by
      exact Q'.eqv_trans _ _ _
        (quaternionHaar_factorizedHeadStep blocks factors)
        (quaternionHaar_eq_factorizedHaar blocks
          (factorizedHeadStep factors))

def nonUnitFactors (factors : List RatPoly) : List RatPoly :=
  factors.filter fun factor => decide (factor ≠ polyOne)

theorem factorProduct_nonUnit_carrier (blocks : Nat) :
    ∀ factors : List RatPoly,
      HaarCarrierEqv blocks (factorProduct factors)
        (factorProduct (nonUnitFactors factors))
  | [] => HaarCarrierEqv.refl blocks polyOne
  | factor :: rest => by
      by_cases hunit : factor = polyOne
      · subst factor
        have hdrop : decide (polyOne ≠ polyOne) = false := by decide
        simp only [factorProduct, nonUnitFactors, List.filter_cons,
          hdrop, Bool.false_eq_true, if_false]
        exact HaarCarrierEqv.trans
          (haarCarrier_polyOne_left blocks (factorProduct rest))
          (factorProduct_nonUnit_carrier blocks rest)
      · have hkeep : decide (factor ≠ polyOne) = true := by
          exact decide_eq_true hunit
        simp only [factorProduct, nonUnitFactors, List.filter_cons,
          hkeep, if_true]
        exact HaarCarrierEqv.mul_left factor
          (factorProduct_nonUnit_carrier blocks rest)

theorem quaternionHaar_nonUnitFactors (blocks : Nat)
    (factors : List RatPoly) :
    quaternionHaar blocks (factorProduct factors) ≈
      quaternionHaar blocks (factorProduct (nonUnitFactors factors)) := by
  refine Q'.eqv_trans _
    (quaternionHaar blocks (polyMul polyOne (factorProduct factors))) _
    (Q'.eqv_symm
      (quaternionHaar_polyOne_left blocks (factorProduct factors))) ?_
  exact Q'.eqv_trans _ _ _
    ((factorProduct_nonUnit_carrier blocks factors) polyOne)
    (quaternionHaar_polyOne_left blocks
      (factorProduct (nonUnitFactors factors)))

def compactFactorizedHeadStep (factors : List RatPoly) : List RatPoly :=
  nonUnitFactors (factorizedHeadStep factors)

theorem quaternionHaar_compactFactorizedHeadStep (blocks : Nat)
    (factors : List RatPoly) :
    quaternionHaar (blocks + 1) (factorProduct factors) ≈
      quaternionHaar blocks
        (factorProduct (compactFactorizedHeadStep factors)) := by
  exact Q'.eqv_trans _ _ _
    (quaternionHaar_factorizedHeadStep blocks factors)
    (quaternionHaar_nonUnitFactors blocks
      (factorizedHeadStep factors))

def compactFactorizedHaarContract : Nat → List RatPoly → RatPoly
  | 0, factors => factorProduct (nonUnitFactors factors)
  | blocks + 1, factors =>
      compactFactorizedHaarContract blocks
        (compactFactorizedHeadStep factors)

def compactFactorizedHaar (blocks : Nat) (factors : List RatPoly) : Q' :=
  quaternionHaar 0 (compactFactorizedHaarContract blocks factors)

theorem quaternionHaar_eq_compactFactorizedHaar :
    ∀ (blocks : Nat) (factors : List RatPoly),
      quaternionHaar blocks (factorProduct factors) ≈
        compactFactorizedHaar blocks factors
  | 0, factors => quaternionHaar_nonUnitFactors 0 factors
  | blocks + 1, factors => by
      exact Q'.eqv_trans _ _ _
        (quaternionHaar_compactFactorizedHeadStep blocks factors)
        (quaternionHaar_eq_compactFactorizedHaar blocks
          (compactFactorizedHeadStep factors))


end YMGap.Continuum.SU2QuaternionFactorizedHaarContraction

#print axioms YMGap.Continuum.SU2QuaternionFactorizedHaarContraction.dropHeadPolynomial_polyMul
#print axioms YMGap.Continuum.SU2QuaternionFactorizedHaarContraction.quaternionHaar_factorizedHeadStep
#print axioms YMGap.Continuum.SU2QuaternionFactorizedHaarContraction.quaternionHaar_eq_compactFactorizedHaar
