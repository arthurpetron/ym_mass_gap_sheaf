/-
# Joint time and heat-cutoff removal for actual Wilson-window expressions

The source expression and window stay fixed. Every scalar is the original
finiteValue with its full selected chain action and partition, not a product
state or an auxiliary expectation. Its time modulus is independent of heat
stage; at one computed time pivot the existing arbitrary-polynomial cutoff
modulus supplies the other comparison. Three comparisons give a rectangular
bound in independent cutoff and time indices, then an explicit CReal limit.

Actual finite reflected-square positivity survives this joint limit through
the exact centered-placement pin. Spatial width and nome remain fixed. No
spatial/spacing passage, full gauge-observable coverage, enlarged completion
or extension of the old completed-carrier strict bound is asserted.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowReflectionPositive

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowJointCauchy

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialChainGeometry (chainIds chainIds_physical)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowTimeLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowReflectionPositive
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowTimeLimit (windowTimeModulus)
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetExpectation (finiteCauchy)
open YMGap.Continuum.QuaternionHaarSupportedPolynomialInterval (polynomialCap)

local infix:50 " ≈ " => Q'.eqv

/-- Cutoff Cauchy data at ONE fixed original ambient and time placement. -/
def windowCutoffCauchy {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (L : Nat) (e : WindowExpression width) (t : Nat) :
    QCauchy (fun stage => originalWindowScalar hw0 hw1 L e stage t t) :=
  finiteCauchy w hw0 hw1 (width+(t+(L+t)))
    (chainIds (width+(t+(L+t))) width 0 (t+(L+t)))
    (fun _ hi => chainIds_physical hi) (placedPolynomial (width+(t+(L+t))) t e)

attribute [local irreducible] originalWindowScalar

/-- One common time pivot at one quarter of the error budget. -/
def jointTimeThreshold {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (e : WindowExpression width) (epsilon : Q') : Nat :=
  windowTimeModulus hw0 hw1 width (polynomialCap (sourcePolynomial e))
    (HalfPow.half * (HalfPow.half * epsilon))

/-- Cutoff control at the computed pivot, not uniformly over every chain. -/
def jointCutoffThreshold {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (L : Nat) (e : WindowExpression width) (epsilon : Q') : Nat :=
  (windowCutoffCauchy hw0 hw1 L e (jointTimeThreshold hw0 hw1 e epsilon)).M
    (HalfPow.half * (HalfPow.half * epsilon))

def jointModulus {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (L : Nat) (e : WindowExpression width) (epsilon : Q') : Nat :=
  max (jointTimeThreshold hw0 hw1 e epsilon) (jointCutoffThreshold hw0 hw1 L e epsilon)

attribute [local irreducible] windowCutoffCauchy

private theorem three_quarter_chain (epsilon : Q') (he : (0 : Q') < epsilon)
    (u v x z : Q')
    (hu : u ≤ v + HalfPow.half * (HalfPow.half * epsilon))
    (hv : v ≤ x + HalfPow.half * (HalfPow.half * epsilon))
    (hx : x ≤ z + HalfPow.half * (HalfPow.half * epsilon)) : u ≤ z + epsilon := by
  let q := HalfPow.half * (HalfPow.half * epsilon)
  have hq : (0 : Q') ≤ q := Q'.le_of_lt
    (ExpNeg.half_mul_pos _ (ExpNeg.half_mul_pos epsilon he))
  have h1 := Q'.le_trans' _ _ _ hu (Q'.add_le_add_right _ _ q hv)
  have h2 := Q'.le_trans' _ _ _ h1
    (Q'.add_le_add_right _ _ q (Q'.add_le_add_right _ _ q hx))
  have h3 := Q'.le_trans' _ _ _ h2 (Q'.add_le_self_of_nonneg _ q hq)
  have hfour : (((z+q)+q)+q)+q ≈ z+epsilon := by
    have hqq : q+q ≈ HalfPow.half*epsilon := ExpNeg.two_halves (HalfPow.half*epsilon)
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv ((z+q)+q) q q) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ (q+q) (Q'.add_assoc_eqv z q q)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv z (q+q) (q+q)) ?_
    exact Q'.add_eqv_congr_left z _ _
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hqq hqq) (ExpNeg.two_halves epsilon))
  exact Q'.le_trans' _ _ _ h3 (Q'.le_of_eqv hfour)

/-- Heat stage and symmetric exterior-time depth vary independently. The
compact Wilson expression, original action convention and nome do not change. -/
theorem originalJoint_rectangle {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (L : Nat) (e : WindowExpression width) (he : Within L e)
    (epsilon : Q') (heps : (0 : Q') < epsilon) (k t j u : Nat)
    (hk : jointCutoffThreshold hw0 hw1 L e epsilon ≤ k)
    (ht : jointTimeThreshold hw0 hw1 e epsilon ≤ t)
    (hj : jointCutoffThreshold hw0 hw1 L e epsilon ≤ j)
    (hu : jointTimeThreshold hw0 hw1 e epsilon ≤ u) :
    originalWindowScalar hw0 hw1 L e k t t ≤ originalWindowScalar hw0 hw1 L e j u u + epsilon ∧
      originalWindowScalar hw0 hw1 L e j u u ≤ originalWindowScalar hw0 hw1 L e k t t + epsilon := by
  let delta := HalfPow.half * (HalfPow.half * epsilon)
  have hd : (0 : Q') < delta := ExpNeg.half_mul_pos _ (ExpNeg.half_mul_pos epsilon heps)
  let a := jointTimeThreshold hw0 hw1 e epsilon
  have hleft := (originalWindowCauchy hw0 hw1 L e he k).bound
    delta hd t a ht (Nat.le_refl _)
  have hmiddle := (windowCutoffCauchy hw0 hw1 L e a).bound delta hd k j hk hj
  have hright := (originalWindowCauchy hw0 hw1 L e he j).bound
    delta hd a u (Nat.le_refl _) hu
  exact ⟨three_quarter_chain epsilon heps _ _ _ _ hleft.1 hmiddle.1 hright.1,
    three_quarter_chain epsilon heps _ _ _ _ hright.2 hmiddle.2 hleft.2⟩

/-- Witnessed diagonal Cauchy data retains both independent thresholds. -/
def originalJointCauchy {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (L : Nat) (e : WindowExpression width) (he : Within L e) :
    QCauchy (fun s => originalWindowScalar hw0 hw1 L e s s s) where
  M := jointModulus hw0 hw1 L e
  bound := fun epsilon heps i j hi hj =>
    originalJoint_rectangle hw0 hw1 L e he epsilon heps i i j j
      (Nat.le_trans (Nat.le_max_right _ _) hi) (Nat.le_trans (Nat.le_max_left _ _) hi)
      (Nat.le_trans (Nat.le_max_right _ _) hj) (Nat.le_trans (Nat.le_max_left _ _) hj)

/-- Joint time/cutoff CReal for the SAME original finite expectation. -/
def originalJointLimit {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (L : Nat) (e : WindowExpression width) (he : Within L e) : CReal :=
  ofQ'CauchySeq _ (originalJointCauchy hw0 hw1 L e he)

theorem originalJoint_diagonal_converges {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (L : Nat) (e : WindowExpression width) (he : Within L e) :
    ConvergesTo (fun s => ofQ' (originalWindowScalar hw0 hw1 L e s s s))
      (originalJointLimit hw0 hw1 L e he) :=
  convergesTo_ofQ'CauchySeq _ (originalJointCauchy hw0 hw1 L e he)

/-- The returned limit controls the whole late heat/time rectangle, not
only the diagonal; all raw and representative thresholds are displayed. -/
theorem originalJoint_approx {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (L : Nat) (e : WindowExpression width) (he : Within L e)
    (epsilon : Q') (heps : (0 : Q') < epsilon) (k t p : Nat)
    (hk : jointCutoffThreshold hw0 hw1 L e epsilon ≤ k)
    (ht : jointTimeThreshold hw0 hw1 e epsilon ≤ t)
    (hp : jointModulus hw0 hw1 L e epsilon ≤ p) :
    originalWindowScalar hw0 hw1 L e k t t ≤
        (originalJointLimit hw0 hw1 L e he).approx p + epsilon ∧
      (originalJointLimit hw0 hw1 L e he).approx p ≤
        originalWindowScalar hw0 hw1 L e k t t + epsilon := by
  let c := originalJointCauchy hw0 hw1 L e he
  let s := QMhat _ c p
  have hs : jointModulus hw0 hw1 L e epsilon ≤ s := Nat.le_trans hp (self_le_QMhat _ c p)
  exact originalJoint_rectangle hw0 hw1 L e he epsilon heps k t s s hk ht
    (Nat.le_trans (Nat.le_max_right _ _) hs) (Nat.le_trans (Nat.le_max_left _ _) hs)

/-- Exact centered reflection pins imply positivity of the actual original
scalar, whose raw ambient need not itself be reflection centered. -/
theorem originalReflectedScalar_nonnegative {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (h : Nat) (e : WindowExpression width) (he : Within h e)
    (stage t : Nat) :
    (0 : Q') ≤ originalWindowScalar hw0 hw1 (2*h) (.mul (mirror h e) e) stage t t :=
  Q'.le_trans' _ _ _ (reflectedWindowRatio_nonnegative hw0 hw1 h e he stage t)
    (Q'.ge_of_eqv (originalWindowScalar_pin hw0 hw1 (2*h) (.mul (mirror h e) e)
      ⟨mirror_within h e, within_mono (by omega : h ≤ 2*h) e he⟩ stage t t))

/-- Reflected positivity after BOTH the heat cutoff and the external time
boundaries have been removed. Width, nome and the complete expression stay fixed. -/
theorem originalJoint_reflected_nonnegative {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (h : Nat) (e : WindowExpression width) (he : Within h e) :
    leEv (ofQ' 0) (originalJointLimit hw0 hw1 (2*h) (.mul (mirror h e) e)
      ⟨mirror_within h e, within_mono (by omega : h ≤ 2*h) e he⟩) := by
  let c := originalJointCauchy hw0 hw1 (2*h) (.mul (mirror h e) e)
    ⟨mirror_within h e, within_mono (by omega : h ≤ 2*h) e he⟩
  exact leEv_ofQ'_of_approx_ge (fun k => originalReflectedScalar_nonnegative hw0 hw1 h e he
    (QMhat _ c k) (QMhat _ c k))

end YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowJointCauchy

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowJointCauchy.windowCutoffCauchy
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowJointCauchy.jointTimeThreshold
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowJointCauchy.jointCutoffThreshold
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowJointCauchy.jointModulus
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowJointCauchy.originalJoint_rectangle
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowJointCauchy.originalJointCauchy
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowJointCauchy.originalJointLimit
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowJointCauchy.originalJoint_diagonal_converges
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowJointCauchy.originalJoint_approx
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowJointCauchy.originalReflectedScalar_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowJointCauchy.originalJoint_reflected_nonnegative
