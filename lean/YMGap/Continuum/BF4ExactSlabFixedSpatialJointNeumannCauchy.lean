/-
# Represented Cauchy convergence of the finite even Neumann orbit

The finite even-orbit representatives of a supplied unit-complement source
form a norm-Cauchy family on the SAME fixed-nome, fixed-width joint reflected
completion.  The modulus is explicit and depends only on the supplied
representative's computed norm ceiling and the finite geometric-series bound.

No representative is selected from a quotient, and no inverse, continuous
time generator, changing-spacing statement, or continuum claim is made.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialJointOrbitTailBound
import YMGap.Continuum.BF4ExactSlabFixedSpatialJointPresentedCompleteness

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialJointNeumannCauchy

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.CRealSeminormCompletion
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.LargeFieldSuppression
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointSeminorm
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPhysicalTime
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointLinear
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointCompletedInner
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointGeometry
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPairingBounds
  (normCeiling normCeiling_nonnegative)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDenseCenteredGap
  (twoStepRate twoStepRate_nonnegative twoStepRate_lt_one)
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointOrbitCauchy
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointOrbitTailBound
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPresentedCompleteness
open YMGap.Continuum.PositiveContractionResidual (geometricCutoff geometric_bound)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width : Nat)

local notation "D" => jointSeminorm hw0 hw1 width
local notation "V" => JointCompletion hw0 hw1 width
local notation "B" => completedInner hw0 hw1 width
local notation "U" => jointCompletedUnit hw0 hw1 width
local notation "q" => twoStepRate hw0 hw1 width
local notation "Rq" a:arg => Quotient.mk crealSetoid (ofQ' a)

/-- Symmetry of the actual completed squared distance. -/
theorem completedDistSq_symm (x y : V) :
    completedDistSq hw0 hw1 width x y = completedDistSq hw0 hw1 width y x := by
  refine Quotient.inductionOn₂ x y ?_
  intro X Y
  rw [completedDistSq_mk, completedDistSq_mk]
  exact Quotient.sound (Equiv_of_limit_of_equal
    (fun n => (D).distSq_symm (X.seq n) (Y.seq n))
    (representativeDistSq_converges hw0 hw1 width X Y)
    (representativeDistSq_converges hw0 hw1 width Y X))

private theorem square_le_square {a b : Q'} (ha : (0 : Q') ≤ a) (hab : a ≤ b) :
    a*a ≤ b*b := by
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right a b a hab ha)
    (Q'.mul_le_mul_of_nonneg_left a b b hab
      (Q'.le_trans' _ _ _ ha hab))

/-- The rational coefficient multiplying `q^p` in the uniform tail bound. -/
def orbitNormConstant (X : (D).Cauchy) : Q' :=
  let gap : (0 : Q') < 1 - q := HKPos.one_sub_pos (twoStepRate_lt_one hw0 hw1 width)
  let geometricCap := Q'.divPos 1 (1-q) gap
  normCeiling hw0 hw1 width X * (geometricCap * geometricCap)

theorem orbitNormConstant_nonnegative (X : (D).Cauchy) :
    (0 : Q') ≤ orbitNormConstant hw0 hw1 width X := by
  let gap : (0 : Q') < 1-q := HKPos.one_sub_pos (twoStepRate_lt_one hw0 hw1 width)
  let g := Q'.divPos 1 (1-q) gap
  have hg : (0 : Q') ≤ g := Q'.le_of_lt (Q'.divPos_pos 1 (1-q) gap (by decide))
  change (0 : Q') ≤ normCeiling hw0 hw1 width X * (g*g)
  exact Q'.mul_nonneg _ _ (normCeiling_nonnegative hw0 hw1 width X)
    (Q'.mul_nonneg _ _ hg hg)

private theorem tailScalar_le (X : (D).Cauchy) (p l : Nat) :
    ((q^p * geomSum q l) * (q^p * geomSum q l)) * normCeiling hw0 hw1 width X ≤
      q^p * orbitNormConstant hw0 hw1 width X := by
  dsimp only [orbitNormConstant]
  let a := q^p
  let s := geomSum q l
  let gap : (0 : Q') < 1-q := HKPos.one_sub_pos (twoStepRate_lt_one hw0 hw1 width)
  let g := Q'.divPos 1 (1-q) gap
  have hq0 : (0 : Q') ≤ q := twoStepRate_nonnegative hw0 hw1 width
  have ha0 : (0 : Q') ≤ a := Q'.pow_nonneg q hq0 p
  have ha1 : a ≤ (1 : Q') :=
    HKPos.pow_le_one hq0 (Q'.le_of_lt (twoStepRate_lt_one hw0 hw1 width)) p
  have hs0 : (0 : Q') ≤ s := geomSum_nonneg hq0 l
  have hsg : s ≤ g := geomSum_le_recip hq0 gap l
  have hg0 : (0 : Q') ≤ g := Q'.le_trans' _ _ _ hs0 hsg
  have haa : a*a ≤ a := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left a 1 a ha1 ha0)
    (Q'.le_of_eqv (Q'.mul_one_eqv a))
  have hss : s*s ≤ g*g := square_le_square hs0 hsg
  have hprod : (a*a)*(s*s) ≤ a*(g*g) := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right (a*a) a (s*s) haa
      (Q'.mul_nonneg _ _ hs0 hs0))
    (Q'.mul_le_mul_of_nonneg_left (s*s) (g*g) a hss ha0)
  have hcoeff : (a*s)*(a*s) ≤ a*(g*g) := Q'.le_trans' _ _ _
    (Q'.le_of_eqv (RingNormaliser.poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))
      (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (by decide)
      (fun | 0 => a | _ => s))) hprod
  have hN := normCeiling_nonnegative hw0 hw1 width X
  refine Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hcoeff hN) ?_
  exact Q'.le_of_eqv (RingNormaliser.poly_identity_of_normal_eq
    (.mul (.mul (.var 0) (.mul (.var 1) (.var 1))) (.var 2))
    (.mul (.var 0) (.mul (.var 2) (.mul (.var 1) (.var 1)))) (by decide)
    (fun | 0 => a | 1 => g | _ => normCeiling hw0 hw1 width X))

private theorem ordered_orbit_dist_le (X : (D).Cauchy)
    (hX : B (Quotient.mk (D).completionSetoid X) U = RCzero)
    (p r : Nat) (hpr : p ≤ r) :
    RCle (completedDistSq hw0 hw1 width
        (Quotient.mk (D).completionSetoid (evenOrbitRep hw0 hw1 width X p))
        (Quotient.mk (D).completionSetoid (evenOrbitRep hw0 hw1 width X r)))
      (Rq (q^p * orbitNormConstant hw0 hw1 width X)) := by
  rw [completedDistSq_symm, mk_evenOrbitRep, mk_evenOrbitRep,
    show r = p + (r-p) by omega, completedDistSq, evenOrbitSum_sub_eq_tail]
  have ht := evenOrbitTail_geometric_norm_le hw0 hw1 width
    (Quotient.mk (D).completionSetoid X) hX p (r-p)
  have hc : RCle (B (evenOrbitTail hw0 hw1 width
      (Quotient.mk (D).completionSetoid X) p (r-p))
      (evenOrbitTail hw0 hw1 width
        (Quotient.mk (D).completionSetoid X) p (r-p)))
      (RCscale ((q^p * geomSum q (r-p)) * (q^p * geomSum q (r-p)))
        (Rq (normCeiling hw0 hw1 width X))) :=
    RCle_trans ht (RCscale_mono
      (Q'.mul_nonneg _ _
        (Q'.mul_nonneg _ _ (Q'.pow_nonneg q (twoStepRate_nonnegative hw0 hw1 width) p)
          (geomSum_nonneg (twoStepRate_nonnegative hw0 hw1 width) (r-p)))
        (Q'.mul_nonneg _ _ (Q'.pow_nonneg q (twoStepRate_nonnegative hw0 hw1 width) p)
          (geomSum_nonneg (twoStepRate_nonnegative hw0 hw1 width) (r-p))))
      (representativeInner_le_normCeiling hw0 hw1 width X))
  refine RCle_trans hc ?_
  rw [RCscale_mk, RCle_mk]
  exact leEv_trans (leEv_of_equiv (CReal.Equiv.symm (CRealAlg.ofQ'_mul _ _)))
    (leEv_of_le (ofQ'_le_ofQ' (tailScalar_le hw0 hw1 width X p (r-p))))

/-- Supplied representatives of the finite even Neumann orbit, with their
explicit actual-norm Cauchy modulus. -/
def orbitNormCauchy (X : (D).Cauchy)
    (hX : B (Quotient.mk (D).completionSetoid X) U = RCzero) :
    PresentedNormCauchy hw0 hw1 width where
  pt := evenOrbitRep hw0 hw1 width X
  modulus epsilon := geometricCutoff q (orbitNormConstant hw0 hw1 width X) epsilon
  cauchy := by
    intro epsilon he p r hp hr
    cases Nat.le_total p r with
    | inl hpr =>
        exact RCle_trans (ordered_orbit_dist_le hw0 hw1 width X hX p r hpr)
          (leEv_of_le (ofQ'_le_ofQ' (geometric_bound
            (twoStepRate_nonnegative hw0 hw1 width)
            (twoStepRate_lt_one hw0 hw1 width)
            (orbitNormConstant_nonnegative hw0 hw1 width X) he p hp)))
    | inr hrp =>
        rw [completedDistSq_symm]
        exact RCle_trans (ordered_orbit_dist_le hw0 hw1 width X hX r p hrp)
          (leEv_of_le (ofQ'_le_ofQ' (geometric_bound
            (twoStepRate_nonnegative hw0 hw1 width)
            (twoStepRate_lt_one hw0 hw1 width)
            (orbitNormConstant_nonnegative hw0 hw1 width X) he r hr)))

/-- The represented-completeness limit of the finite even orbit. -/
def orbitLimit (X : (D).Cauchy)
    (hX : B (Quotient.mk (D).completionSetoid X) U = RCzero) : V :=
  (orbitNormCauchy hw0 hw1 width X hX).limit hw0 hw1 width

theorem orbitLimit_converges (X : (D).Cauchy)
    (hX : B (Quotient.mk (D).completionSetoid X) U = RCzero)
    (epsilon : Q') (he : (0 : Q') < epsilon) (p : Nat)
    (hp : (orbitNormCauchy hw0 hw1 width X hX).limitRate hw0 hw1 width epsilon ≤ p) :
    RCle (completedDistSq hw0 hw1 width
        (Quotient.mk (D).completionSetoid (evenOrbitRep hw0 hw1 width X p))
        (orbitLimit hw0 hw1 width X hX)) (Rq epsilon) :=
  (orbitNormCauchy hw0 hw1 width X hX).limit_converges hw0 hw1 width epsilon he p hp

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointNeumannCauchy.orbitNormCauchy
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointNeumannCauchy.completedDistSq_symm
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointNeumannCauchy.orbitLimit
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointNeumannCauchy.orbitLimit_converges

end YMGap.Continuum.BF4ExactSlabFixedSpatialJointNeumannCauchy
