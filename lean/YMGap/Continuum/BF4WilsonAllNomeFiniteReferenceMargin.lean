/-
# A finite signed margin certifies the original completed reference ratio

At ONE fixed terminal depth, the original signed margin c*OWNVar-E is a
combination of four actual window moments. Their constructed cutoff moduli
and the original endpoint-mean caps give its own explicit cutoff modulus.
No epsilon-dependent time threshold or convergence premise is introduced.

The executable checker accepts ONLY finite rational/natural data: c>=0,
epsilon>0, a pivot past that modulus, and margin(pivot)>=2*epsilon.
Acceptance proves margin>=epsilon at every later cutoff, then feeds the
existing terminal-depth and SAME completed-carrier ratio transport.

This is a certificate reduction, not a successful certificate for a changing
Wilson family. No useful small coefficient, scaling trajectory, continuum
survival, physical mass, QFT axiom or every-group realization is supplied.
-/

import YMGap.Continuum.BF4WilsonAllNomeTerminalReferenceEnergyRatio

namespace YMGap.Continuum.BF4WilsonAllNomeFiniteReferenceMargin

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowTimeLimit
  (originalWindowScalar originalWindowScalar_pin)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowJointCauchy
  (windowCutoffCauchy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialUniformProbeCap (windowRatio_bounds)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4WilsonAllNomeBondReflectedForm (crossOdd crossOdd_within)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm (unit)
open YMGap.Continuum.BF4WilsonAllNomeCenteredTransferBondLimit
  (singleSlice finiteScalar finiteScalar_connected_pin)
open YMGap.Continuum.BF4WilsonAllNomeTemporalEnergyLimit
  (finiteEnergy finiteEnergy_half_pin finiteEnergy_nonnegative)
open YMGap.Continuum.BF4WilsonAllNomeMarginalVarianceLimit
  (finiteVariance finiteVariance_budget_pin)
open YMGap.Continuum.BF4WilsonAllNomeTerminalReferenceEnergyRatio
  (referenceCoefficient finite_reference_ratio completed_reference_ratio)
open YMGap.Continuum.BF4WilsonAllNomeZeroRadiusIncrement (state squareAt)
open YMGap.Continuum.BF4WilsonAllNomeCenteredVector (centeredVector)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner (completedInner)
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime (completedTime)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.QuaternionHaarSupportedPolynomialInterval (polynomialCap)

local infix:50 " ≈ " => Q'.eqv

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  {width : Nat} (e : WindowExpression width) (he : Within 0 e)

local notation "x" => singleSlice e he
local notation "u" => unit width
local notation "P" => crossOdd x x
local notation "U" => crossOdd x u
local notation "L" => crossOdd u x
local notation "S" => squareAt e 1
local notation "J" k:arg t:arg f:arg => originalWindowScalar hw0 hw1 1 f k t t

attribute [local irreducible] originalWindowScalar finiteEnergy finiteVariance finiteScalar

/-- The actual finite quantities, not an angular or bare-Haar surrogate. -/
def referenceMargin (c : Q') (k t : Nat) : Q' :=
  c*finiteVariance hw0 hw1 e k t + -(finiteEnergy hw0 hw1 e k t)

private def alpha (c : Q') : Q' := (c-1)*HalfPow.half

/-- BOTH endpoint means remain inside the signed joint margin. -/
theorem referenceMargin_pin (c : Q') (k t : Nat) :
    referenceMargin hw0 hw1 e c k t ≈
      alpha c * J k t S + c*(J k t P + -(J k t U * J k t L)) := by
  have hb := finiteScalar_connected_pin hw0 hw1 e he k t
  change finiteScalar hw0 hw1 e k t ≈ J k t P + -(J k t U * J k t L) at hb
  have hE := finiteEnergy_half_pin hw0 hw1 e he k t
  have hV := Q'.eqv_trans _ _ _ (finiteVariance_budget_pin hw0 hw1 e he k t)
    (Q'.add_eqv_congr' hE hb)
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (Q'.mul_eqv_congr_left c _ _ hV) (Q'.neg_eqv_congr _ _ hE))
    (poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.add (.mul (.var 5) (.var 1))
        (.add (.var 2) (.neg (.mul (.var 3) (.var 4))))))
        (.neg (.mul (.var 5) (.var 1))))
      (.add (.mul (.mul (.add (.var 0) (.neg (.const 1))) (.var 5))
        (.var 1)) (.mul (.var 0) (.add (.var 2) (.neg (.mul (.var 3) (.var 4))))))
      (by decide) (fun
        | 0 => c
        | 1 => J k t S
        | 2 => J k t P
        | 3 => J k t U
        | 4 => J k t L
        | _ => HalfPow.half))

private def meanCap : Q' := Q'.max' 1
  (Q'.max' (polynomialCap (sourcePolynomial U)) (polynomialCap (sourcePolynomial L)))

private theorem meanCap_positive : (0 : Q') < meanCap e he :=
  Q'.pos_of_lt_of_le (by decide : (0 : Q') < 1) (Q'.le_max'_left _ _)

private theorem window_abs (f : WindowExpression width) (hf : Within 1 f) (k t : Nat) :
    Q'.abs (J k t f) ≤ polynomialCap (sourcePolynomial f) := by
  have hb := windowRatio_bounds hw0 hw1 (headCutoff w+k) width (Nat.le_add_right _ _)
    t 1 t (sourcePolynomial f) (source_supported 1 f hf)
  have hp := originalWindowScalar_pin hw0 hw1 1 f hf k t t
  exact Q'.abs_le
    (Q'.le_trans' _ _ _ hb.1 (Q'.ge_of_eqv hp))
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hp) hb.2)

private theorem upper_abs (k t : Nat) : Q'.abs (J k t U) ≤ meanCap e he :=
  Q'.le_trans' _ _ _ (window_abs hw0 hw1 U (crossOdd_within x u) k t)
    (Q'.le_trans' _ _ _ (Q'.le_max'_left _ _) (Q'.le_max'_right _ _))

private theorem lower_abs (k t : Nat) : Q'.abs (J k t L) ≤ meanCap e he :=
  Q'.le_trans' _ _ _ (window_abs hw0 hw1 L (crossOdd_within u x) k t)
    (Q'.le_trans' _ _ _ (Q'.le_max'_right _ _) (Q'.le_max'_right _ _))

private def amplitude (c : Q') : Q' :=
  Q'.abs (alpha c) + Q'.abs c * ((1+meanCap e he)+meanCap e he)

private theorem amplitude_nonnegative (c : Q') : (0 : Q') ≤ amplitude e he c :=
  Q'.zero_le_add _ _ (Q'.abs_nonneg _)
    (Q'.mul_nonneg _ _ (Q'.abs_nonneg _)
      (Q'.zero_le_add _ _
        (Q'.zero_le_add _ _ (by decide) (Q'.le_of_lt (meanCap_positive e he)))
        (Q'.le_of_lt (meanCap_positive e he))))

private theorem denominator_positive (c : Q') : (0 : Q') < 1+amplitude e he c :=
  Q'.pos_of_lt_of_le (by decide : (0 : Q') < 1)
    (Q'.add_le_self_of_nonneg _ _ (amplitude_nonnegative e he c))

/-- A positive denominator even at c=0; no division by c or variance. -/
def cutoffTolerance (c epsilon : Q') : Q' :=
  Q'.divPos epsilon (1+amplitude e he c) (denominator_positive e he c)

private theorem cutoffTolerance_positive (c : Q') {epsilon : Q'} (hp : (0 : Q') < epsilon) :
    (0 : Q') < cutoffTolerance e he c epsilon := Q'.divPos_pos _ _ _ hp

/-- FOUR fixed-depth original cutoff moduli; reference depth need not be late. -/
def referenceCutoff (c : Q') (t : Nat) (epsilon : Q') : Nat :=
  let d := cutoffTolerance e he c epsilon
  max ((windowCutoffCauchy hw0 hw1 1 S t).M d)
    (max ((windowCutoffCauchy hw0 hw1 1 P t).M d)
      (max ((windowCutoffCauchy hw0 hw1 1 U t).M d)
        ((windowCutoffCauchy hw0 hw1 1 L t).M d)))

private theorem margin_close (c epsilon : Q') (hp : (0 : Q') < epsilon)
    (a b p q v z l m : Q')
    (hv : Q'.abs v ≤ meanCap e he) (hzcap : Q'.abs z ≤ meanCap e he)
    (hlcap : Q'.abs l ≤ meanCap e he) (hm : Q'.abs m ≤ meanCap e he)
    (ha : a ≤ b+cutoffTolerance e he c epsilon ∧ b ≤ a+cutoffTolerance e he c epsilon)
    (hq : p ≤ q+cutoffTolerance e he c epsilon ∧ q ≤ p+cutoffTolerance e he c epsilon)
    (hz : v ≤ z+cutoffTolerance e he c epsilon ∧ z ≤ v+cutoffTolerance e he c epsilon)
    (hl : l ≤ m+cutoffTolerance e he c epsilon ∧ m ≤ l+cutoffTolerance e he c epsilon) :
    alpha c*a+c*(p+-(v*l)) ≤ alpha c*b+c*(q+-(z*m))+epsilon := by
  let d := cutoffTolerance e he c epsilon
  let B := meanCap e he
  have hd : (0 : Q') ≤ d := Q'.le_of_lt (cutoffTolerance_positive e he c hp)
  have hproduct : z*m ≤ v*l+(B*d+B*d) :=
    BoundedRationalCauchyProduct.product_close z v m l B d
      (Q'.le_of_lt (meanCap_positive e he)) hd
      hzcap hlcap hz.symm hl.symm
  have hcov : p+-(v*l) ≤ (q+-(z*m))+(d+(B*d+B*d)) := by
    have h := Q'.add_le_add hq.1 (Q'.neg_le_neg_add hproduct)
    exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv
      (poly_identity_of_normal_eq
        (.add (.add (.var 0) (.var 1)) (.add (.var 2) (.var 3)))
        (.add (.add (.var 0) (.var 2)) (.add (.var 1) (.var 3)))
        (by decide) (fun | 0 => q | 1 => d | 2 => -(z*m) | _ => B*d+B*d)))
  have halpha := Q'.mul_close_of_two_sided (alpha c) a b (Q'.abs (alpha c)) d
    (Q'.abs_nonneg _) hd (ExpNeg.neg_abs_le _) (Q'.le_abs_self _) ha.1 ha.2
  have hcovback : q+-(z*m) ≤ (p+-(v*l))+(d+(B*d+B*d)) := by
    have hproduct' := BoundedRationalCauchyProduct.product_close v z l m B d
      (Q'.le_of_lt (meanCap_positive e he)) hd hv hm hz hl
    have h := Q'.add_le_add hq.2 (Q'.neg_le_neg_add hproduct')
    exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv
      (poly_identity_of_normal_eq
        (.add (.add (.var 0) (.var 1)) (.add (.var 2) (.var 3)))
        (.add (.add (.var 0) (.var 2)) (.add (.var 1) (.var 3)))
        (by decide) (fun | 0 => p | 1 => d | 2 => -(v*l) | _ => B*d+B*d)))
  have hscaled := Q'.mul_close_of_two_sided c (p+-(v*l)) (q+-(z*m)) (Q'.abs c)
    (d+(B*d+B*d)) (Q'.abs_nonneg _)
    (Q'.zero_le_add _ _ hd (Q'.zero_le_add _ _ (Q'.mul_nonneg _ _
      (Q'.le_of_lt (meanCap_positive e he)) hd) (Q'.mul_nonneg _ _
      (Q'.le_of_lt (meanCap_positive e he)) hd)))
    (ExpNeg.neg_abs_le _) (Q'.le_abs_self _) hcov hcovback
  have h := Q'.add_le_add halpha hscaled
  have heq : (alpha c*b+Q'.abs (alpha c)*d)+
      (c*(q+-(z*m))+Q'.abs c*(d+(B*d+B*d))) ≈
      (alpha c*b+c*(q+-(z*m)))+amplitude e he c*d :=
    poly_identity_of_normal_eq
      (.add (.add (.var 0) (.mul (.var 2) (.var 4)))
        (.add (.var 1) (.mul (.var 3) (.add (.var 4)
          (.add (.mul (.var 5) (.var 4)) (.mul (.var 5) (.var 4)))))))
      (.add (.add (.var 0) (.var 1)) (.mul
        (.add (.var 2) (.mul (.var 3) (.add (.add (.const 1) (.var 5)) (.var 5))))
        (.var 4))) (by decide)
      (fun
        | 0 => alpha c*b
        | 1 => c*(q+-(z*m))
        | 2 => Q'.abs (alpha c)
        | 3 => Q'.abs c
        | 4 => d
        | _ => B)
  have hbudget : amplitude e he c*d ≤ epsilon := by
    have h := Q'.add_le_self_of_nonneg (amplitude e he c*d) d hd
    have hid : amplitude e he c*d+d ≈ epsilon :=
      Q'.eqv_trans _ _ _
        (poly_identity_of_normal_eq
          (.add (.mul (.var 0) (.var 1)) (.var 1))
          (.mul (.var 1) (.add (.const 1) (.var 0)))
          (by decide) (fun | 0 => amplitude e he c | _ => d))
        (Q'.divPos_mul_eqv _ _ _)
    exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv hid)
  exact Q'.le_trans' _ _ _ h (Q'.le_trans' _ _ _ (Q'.le_of_eqv heq)
    (Q'.add_le_add_left _ _ _ hbudget))

/-- Cutoff Cauchy data for c*OWNVar-E at an ARBITRARY fixed original depth. -/
def referenceMarginCauchy (c : Q') (t : Nat) :
    QCauchy (fun k => referenceMargin hw0 hw1 e c k t) where
  M epsilon := referenceCutoff hw0 hw1 e he c t epsilon
  bound := by
    intro epsilon hp i j hi hj
    let d := cutoffTolerance e he c epsilon
    have hd : (0 : Q') < d := cutoffTolerance_positive e he c hp
    have hs : (windowCutoffCauchy hw0 hw1 1 S t).M d ≤
        referenceCutoff hw0 hw1 e he c t epsilon := Nat.le_max_left _ _
    have hpair : (windowCutoffCauchy hw0 hw1 1 P t).M d ≤
        referenceCutoff hw0 hw1 e he c t epsilon :=
      Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
    have hu : (windowCutoffCauchy hw0 hw1 1 U t).M d ≤
        referenceCutoff hw0 hw1 e he c t epsilon :=
      Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))
        (Nat.le_max_right _ _)
    have hl : (windowCutoffCauchy hw0 hw1 1 L t).M d ≤
        referenceCutoff hw0 hw1 e he c t epsilon :=
      Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
        (Nat.le_max_right _ _)
    have bs := (windowCutoffCauchy hw0 hw1 1 S t).bound d hd i j
      (Nat.le_trans hs hi) (Nat.le_trans hs hj)
    have bp := (windowCutoffCauchy hw0 hw1 1 P t).bound d hd i j
      (Nat.le_trans hpair hi) (Nat.le_trans hpair hj)
    have bu := (windowCutoffCauchy hw0 hw1 1 U t).bound d hd i j
      (Nat.le_trans hu hi) (Nat.le_trans hu hj)
    have bl := (windowCutoffCauchy hw0 hw1 1 L t).bound d hd i j
      (Nat.le_trans hl hi) (Nat.le_trans hl hj)
    have forward := margin_close e he c epsilon hp _ _ _ _ _ _ _ _
      (upper_abs hw0 hw1 e he i t) (upper_abs hw0 hw1 e he j t)
      (lower_abs hw0 hw1 e he i t) (lower_abs hw0 hw1 e he j t) bs bp bu bl
    have backward := margin_close e he c epsilon hp _ _ _ _ _ _ _ _
      (upper_abs hw0 hw1 e he j t) (upper_abs hw0 hw1 e he i t)
      (lower_abs hw0 hw1 e he j t) (lower_abs hw0 hw1 e he i t)
      bs.symm bp.symm bu.symm bl.symm
    have pin_i := referenceMargin_pin hw0 hw1 e he c i t
    have pin_j := referenceMargin_pin hw0 hw1 e he c j t
    exact ⟨Q'.le_trans' _ _ _ (Q'.le_of_eqv pin_i)
      (Q'.le_trans' _ _ _ forward (Q'.ge_of_eqv
        (Q'.add_eqv_congr_right _ _ epsilon pin_j))),
      Q'.le_trans' _ _ _ (Q'.le_of_eqv pin_j)
        (Q'.le_trans' _ _ _ backward (Q'.ge_of_eqv
          (Q'.add_eqv_congr_right _ _ epsilon pin_i)))⟩

/-- A decidable finite test on the ORIGINAL rational margin. No oracle input. -/
def check (s : Nat) (c epsilon : Q') (pivot : Nat) : Bool :=
  decide ((0 : Q') ≤ c ∧ (0 : Q') < epsilon ∧
    referenceCutoff hw0 hw1 e he c (s+1) epsilon ≤ pivot ∧
    epsilon+epsilon ≤ referenceMargin hw0 hw1 e c pivot (s+1))

/-- Finite certificate data, not an additional analytic frontier bundle. -/
structure Certificate (s : Nat) (c : Q') where
  tolerance : Q'
  pivot : Nat
  accepted : check hw0 hw1 e he s c tolerance pivot = true

private theorem cancel_right {a b d : Q'} (h : a+d ≤ b+d) : a ≤ b := by
  have h' := Q'.add_le_add_right _ _ (-d) h
  have hc (zeta : Q') : (zeta+d)+(-d) ≈ zeta :=
    Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv _ _ _)
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ (Q'.add_neg_self_eqv _))
        (Q'.eqv_of_eq (Q'.add_zero' _)))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (hc a))
    (Q'.le_trans' _ _ _ h' (Q'.le_of_eqv (hc b)))

namespace Certificate

variable {s : Nat} {c : Q'} (C : Certificate hw0 hw1 e he s c)

private theorem conditions : (0 : Q') ≤ c ∧ (0 : Q') < C.tolerance ∧
    referenceCutoff hw0 hw1 e he c (s+1) C.tolerance ≤ C.pivot ∧
    C.tolerance+C.tolerance ≤ referenceMargin hw0 hw1 e c C.pivot (s+1) :=
  of_decide_eq_true C.accepted

/-- The cutoff is COMPUTED from the certificate's tolerance, not assumed. -/
def cutoff : Nat := referenceCutoff hw0 hw1 e he c (s+1) C.tolerance

/-- A positive absolute margin survives every later heat cutoff. -/
theorem margin_floor (k : Nat) (hk : C.cutoff hw0 hw1 e he ≤ k) :
    C.tolerance ≤ referenceMargin hw0 hw1 e c k (s+1) := by
  have h := C.conditions hw0 hw1 e he
  have hb := (referenceMarginCauchy hw0 hw1 e he c (s+1)).bound
    C.tolerance h.2.1 C.pivot k h.2.2.1 hk
  exact cancel_right (Q'.le_trans' _ _ _ h.2.2.2 hb.1)

/-- Strict finite energy/OWN-variance inequality, retaining the margin. -/
theorem reference_strict_ratio (k : Nat) (hk : C.cutoff hw0 hw1 e he ≤ k) :
    finiteEnergy hw0 hw1 e k (s+1)+C.tolerance ≤
      c*finiteVariance hw0 hw1 e k (s+1) := by
  have h := Q'.add_le_add_right _ _ (finiteEnergy hw0 hw1 e k (s+1))
    (C.margin_floor hw0 hw1 e he k hk)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.add_comm_eqv _ _))
    (Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.sub_add_cancel_eqv _ _)))

/-- This fills the old all-late-cutoff premise using only accepted finite data. -/
theorem reference_ratio (k : Nat) (hk : C.cutoff hw0 hw1 e he ≤ k) :
    finiteEnergy hw0 hw1 e k (s+1) ≤ c*finiteVariance hw0 hw1 e k (s+1) :=
  Q'.le_trans' _ _ _
    (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt (C.conditions hw0 hw1 e he).2.1))
    (C.reference_strict_ratio hw0 hw1 e he k hk)

/-- Every later terminal depth uses the SAME original energy and variance. -/
theorem all_later_ratio (k r : Nat) (hk : C.cutoff hw0 hw1 e he ≤ k) :
    finiteEnergy hw0 hw1 e k (s+1+r) ≤
      referenceCoefficient hw0 hw1 width s c * finiteVariance hw0 hw1 e k (s+1+r) :=
  finite_reference_ratio hw0 hw1 e he s (C.cutoff hw0 hw1 e he)
    (C.conditions hw0 hw1 e he).1 (C.reference_ratio hw0 hw1 e he) k r hk

include C in
/-- The existing completed carrier consumes the FINITE certificate directly. -/
theorem completed_ratio :
    RCle
      (RCsub
        (completedInner hw0 hw1 (centeredVector hw0 hw1 (state e he))
          (centeredVector hw0 hw1 (state e he)))
        (completedInner hw0 hw1 (centeredVector hw0 hw1 (state e he))
          (completedTime hw0 hw1 1 (centeredVector hw0 hw1 (state e he)))))
      (RCscale (referenceCoefficient hw0 hw1 width s c)
        (completedInner hw0 hw1 (centeredVector hw0 hw1 (state e he))
          (centeredVector hw0 hw1 (state e he)))) :=
  completed_reference_ratio hw0 hw1 e he s (C.cutoff hw0 hw1 e he)
    (C.conditions hw0 hw1 e he).1 (C.reference_ratio hw0 hw1 e he)

/-- Acceptance cannot be supplied by a zero-variance or zero-coefficient test. -/
theorem product_ne_zero (k : Nat) (hk : C.cutoff hw0 hw1 e he ≤ k) :
    ¬ (c*finiteVariance hw0 hw1 e k (s+1) ≈ 0) := by
  intro hz
  have hE := finiteEnergy_nonnegative hw0 hw1 e he k (s+1)
  have hslack : C.tolerance ≤ finiteEnergy hw0 hw1 e k (s+1)+C.tolerance := by
    simpa only [Q'.zero_add'] using Q'.add_le_add_right _ _ C.tolerance hE
  have hbad : C.tolerance ≤ 0 := Q'.le_trans' _ _ _ hslack
    (Q'.le_trans' _ _ _ (C.reference_strict_ratio hw0 hw1 e he k hk) (Q'.le_of_eqv hz))
  exact (by decide : ¬ (0 : Q') < (0 : Q'))
    (Q'.pos_of_lt_of_le (C.conditions hw0 hw1 e he).2.1 hbad)

/-- A successful finite certificate has a genuinely nonzero original variance. -/
theorem variance_ne_zero (k : Nat) (hk : C.cutoff hw0 hw1 e he ≤ k) :
    ¬ (finiteVariance hw0 hw1 e k (s+1) ≈ 0) := by
  intro hz
  exact C.product_ne_zero hw0 hw1 e he k hk (Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left c _ _ hz) (Q'.mul_zero_eqv c))

end Certificate

#print axioms referenceMargin_pin
#print axioms cutoffTolerance
#print axioms referenceCutoff
#print axioms referenceMarginCauchy
#print axioms check
#print axioms Certificate.margin_floor
#print axioms Certificate.reference_strict_ratio
#print axioms Certificate.all_later_ratio
#print axioms Certificate.completed_ratio
#print axioms Certificate.product_ne_zero
#print axioms Certificate.variance_ne_zero

end YMGap.Continuum.BF4WilsonAllNomeFiniteReferenceMargin
