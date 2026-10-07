/-
# A relative dissipation budget feeds the existing computed RG margin

Keep kappa identically one and the existing computed-rate consumer unchanged.
An external nonnegative epsilon with epsilon(n) <= delta(n)*(1-r(n)^2)
is paid by an ORDINARY finite-prefix delta budget. The computed upper margin
supplies the missing dyadic factor: 2^n*epsilon(n) <= 2*(1-seed)*delta(n).
Consequently the existing weighted effective-defect budget has the explicit
bound S=2*(1-seed)*D, and its existing seed floor is (1-seed)*(seed-D).
The relative rate and its error are also constructed recursively from delta;
their bounds and equality with the existing computed sequence are proved.
No numerical self-consistency premise is needed for this specialization.

This proves numerical implications, not an action-specific RG comparison.
The actual completed-form relative dissipation estimate and a useful ordinary
prefix budget remain analytic inputs. No canonical field is changed, no
coercive comparison is imposed, and no infinite convergence without a modulus
or continuum/Clay conclusion is asserted.
-/

import YMGap.Continuum.BF4WilsonAllNomeRGComputedMargin
import YMGap.Continuum.BF4WilsonAllNomeRGRelativeDissipation
import YMGap.Constructive.FinSumAlg

namespace YMGap.Continuum.BF4WilsonAllNomeRGDissipationBudget

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.HalfPow
open YMGap.Constructive.RationalTail (finSum)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4WilsonAllNomeRGStepComposition
open YMGap.Continuum.BF4WilsonAllNomeRGComputedMargin
open YMGap.Continuum.RGExplicitRationalRate (explicitRate rate_nonnegative rate_le_one)
open YMGap.Continuum.BF4WilsonAllNomeRGRelativeDissipation
  (relativeFactor_error relativeFactor_nonnegative relativeFactor_le_one)

local infix:50 " ≈ " => Q'.eqv

private theorem unitDefect_eqv (epsilon r : Q') :
    effectiveRgDefect 1 epsilon r ≈ epsilon :=
  poly_identity_of_normal_eq
    (.add (.mul (.add (.const 1) (.neg (.const 1))) (.mul (.var 0) (.var 0)))
      (.mul (.const 1) (.var 1)))
    (.var 1) (by decide) (fun | 0 => r | _ => epsilon)

private theorem squareLoss_le_twice_margin (r : Q') :
    (1 : Q') - r*r ≤ 2*((1 : Q') - r) := by
  have hid : (1 : Q') - r*r ≈
      2*((1 : Q') - r) + -(((1 : Q') - r)*((1 : Q') - r)) :=
    poly_identity_of_normal_eq
      (.add (.const 1) (.neg (.mul (.var 0) (.var 0))))
      (.add (.mul (.const 2) (.add (.const 1) (.neg (.var 0))))
        (.neg (.mul (.add (.const 1) (.neg (.var 0)))
          (.add (.const 1) (.neg (.var 0))))))
      (by decide) (fun _ => r)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hid)
    (Q'.le_trans' _ _ _
      (Q'.add_le_add_left _ _ _
        (Q'.neg_le_neg (SumOfSquares.q_mul_self_nonneg ((1 : Q') - r))))
      (Q'.le_of_eqv (Q'.eqv_of_eq (Q'.add_zero' _))))

/-- The existing computed upper margin cancels the exponential error weight.
No all-scale contraction, rate cap or positive margin is a premise. -/
theorem weightedEffectiveDefect_le_relative (seed : Q') (epsilon delta : Nat → Q')
    (he : ∀ n, (0 : Q') ≤ epsilon n) (hd : ∀ n, (0 : Q') ≤ delta n)
    (hrelative : ∀ n, epsilon n ≤ delta n * ((1 : Q') -
      computedRate seed epsilon (fun _ => 1) n * computedRate seed epsilon (fun _ => 1) n))
    (n : Nat) :
    Q'.ofNat (2 ^ n) *
      effectiveDefectSeq (fun _ => 1) epsilon (computedRate seed epsilon (fun _ => 1)) n ≤
        (2*((1 : Q') - seed))*delta n := by
  let r := computedRate seed epsilon (fun _ => 1) n
  let m := (1 : Q') - seed
  let p := half ^ n
  let a := Q'.ofNat (2 ^ n)
  have hup := computedMargin_upper seed epsilon (fun _ => 1)
    (fun _ => Q'.le_refl' 1) he n
  change (1 : Q') - r ≤ m*p at hup
  have htwice := Q'.mul_le_mul_of_nonneg_left _ _ (2 : Q') hup (by decide)
  have heps : epsilon n ≤ delta n * (2*(m*p)) :=
    Q'.le_trans' _ _ _ (hrelative n)
      (Q'.mul_le_mul_of_nonneg_left _ _ (delta n)
        (Q'.le_trans' _ _ _ (squareLoss_le_twice_margin r) htwice) (hd n))
  have hweight := Q'.mul_le_mul_of_nonneg_left _ _ a heps (ofNat_nonneg_rg _)
  have hid : a*(delta n*(2*(m*p))) ≈ ((2*m)*delta n)*(a*p) :=
    poly_identity_of_normal_eq
      (.mul (.var 0) (.mul (.var 1) (.mul (.const 2) (.mul (.var 2) (.var 3)))))
      (.mul (.mul (.mul (.const 2) (.var 2)) (.var 1)) (.mul (.var 0) (.var 3)))
      (by decide) (fun | 0 => a | 1 => delta n | 2 => m | _ => p)
  have hcancel : a*(delta n*(2*(m*p))) ≈ (2*m)*delta n :=
    Q'.eqv_trans _ _ _ hid
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left _ _ _ (ofNat_two_pow_mul_half_pow n))
        (Q'.mul_one_eqv _))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.mul_eqv_congr_left a _ _ (unitDefect_eqv (epsilon n) r)))
    (Q'.le_trans' _ _ _ hweight (Q'.le_of_eqv hcancel))

/-- An ordinary, supplied finite-prefix delta budget gives the EXISTING
weighted effective-defect budget at kappa=1. -/
theorem relativeError_summable (seed D : Q') (epsilon delta : Nat → Q')
    (hseed : seed ≤ (1 : Q')) (hD : (0 : Q') ≤ D)
    (he : ∀ n, (0 : Q') ≤ epsilon n) (hd : ∀ n, (0 : Q') ≤ delta n)
    (hrelative : ∀ n, epsilon n ≤ delta n * ((1 : Q') -
      computedRate seed epsilon (fun _ => 1) n * computedRate seed epsilon (fun _ => 1) n))
    (hprefix : ∀ n, finSum delta n ≤ D) :
    RgErrorSummable
      (effectiveDefectSeq (fun _ => 1) epsilon (computedRate seed epsilon (fun _ => 1)))
      0 (2*((1 : Q') - seed)*D) := by
  let E := effectiveDefectSeq (fun _ => 1) epsilon (computedRate seed epsilon (fun _ => 1))
  let c := 2*((1 : Q') - seed)
  have hc : (0 : Q') ≤ c :=
    Q'.mul_nonneg _ _ (by decide) (Q'.sub_nonneg_of_le hseed)
  have hsum : ∀ n, weightedErrorSum E 0 n ≤ c*finSum delta n := by
    intro n
    induction n with
    | zero => exact Q'.ge_of_eqv (Q'.mul_zero_eqv c)
    | succ n ih =>
      change weightedErrorSum E 0 n + Q'.ofNat (2 ^ n)*E (0+n) ≤
        c*(finSum delta n + delta n)
      rw [Nat.zero_add]
      exact Q'.le_trans' _ _ _
        (Q'.add_le_add ih (weightedEffectiveDefect_le_relative seed epsilon delta he hd hrelative n))
        (Q'.ge_of_eqv (Q'.mul_add_eqv c (finSum delta n) (delta n)))
  exact ⟨Q'.mul_nonneg _ _ hc hD, fun n =>
    Q'.le_trans' _ _ _ (hsum n)
      (Q'.mul_le_mul_of_nonneg_left _ _ c (hprefix n) hc)⟩

/-- The existing sufficient seed floor has this exact relative-budget form. -/
theorem seedFloor_relativeBudget_eqv (seed D : Q') :
    seedFloor seed (2*((1 : Q') - seed)*D) ≈ ((1 : Q') - seed)*(seed-D) := by
  let m := (1 : Q') - seed
  have he : half*((2*m)*D) ≈ m*D :=
    Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq
        (.mul (.var 0) (.mul (.mul (.const 2) (.var 1)) (.var 2)))
        (.mul (.mul (.const 2) (.var 0)) (.mul (.var 1) (.var 2)))
        (by decide) (fun | 0 => half | 1 => m | _ => D))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ two_mul_half_eqv)
        (Q'.one_mul_eqv _))
  exact Q'.eqv_trans _ _ _ (seedFloor_eqv seed (2*m*D))
    (Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left _ _ _ (Q'.neg_eqv_congr _ _ he))
      (poly_identity_of_normal_eq
        (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 1) (.var 2))))
        (.mul (.var 1) (.add (.var 0) (.neg (.var 2))))
        (by decide) (fun | 0 => seed | 1 => m | _ => D)))

/-- Strict seed and budget inequalities make the EXISTING floor positive. -/
theorem seedFloor_relativeBudget_positive (seed D : Q')
    (hseed : seed < (1 : Q')) (hD : D < seed) :
    (0 : Q') < seedFloor seed (2*((1 : Q') - seed)*D) :=
  Q'.pos_of_lt_of_le
    (Q'.mul_pos (HKPos.one_sub_pos hseed) (ClusteringImpliesGap.sub_pos_of_lt hD))
    (Q'.ge_of_eqv (seedFloor_relativeBudget_eqv seed D))

/-- Direct join to the existing dyadic lower-margin theorem; its floor is
(1-seed)*(seed-D), and the delta budget is unweighted. -/
theorem computedMargin_lower_of_relativeBudget (seed D : Q') (epsilon delta : Nat → Q')
    (hseed : seed < (1 : Q')) (hD0 : (0 : Q') ≤ D) (hD : D < seed)
    (he : ∀ n, (0 : Q') ≤ epsilon n) (hd : ∀ n, (0 : Q') ≤ delta n)
    (hrelative : ∀ n, epsilon n ≤ delta n * ((1 : Q') -
      computedRate seed epsilon (fun _ => 1) n * computedRate seed epsilon (fun _ => 1) n))
    (hprefix : ∀ n, finSum delta n ≤ D) (n : Nat) :
    half ^ n * (((1 : Q') - seed)*(seed-D)) ≤
      latticeMarginOf (computedRate seed epsilon (fun _ => 1)) n := by
  have hs := relativeError_summable seed D epsilon delta (Q'.le_of_lt hseed) hD0
    he hd hrelative hprefix
  have hl := computedMargin_lower seed (2*((1 : Q') - seed)*D) epsilon (fun _ => 1)
    (fun _ => Q'.le_refl' 1) he (Q'.sub_nonneg_of_le (Q'.le_of_lt hseed)) hs
    (seedFloor_relativeBudget_positive seed D hseed hD) n
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (Q'.mul_eqv_congr_left _ _ _ (seedFloor_relativeBudget_eqv seed D))) hl

/-- Explicit relative recovery rates, with the original seed as data. -/
def relativeRate (seed : Q') (delta : Nat → Q') : Nat → Q'
  | 0 => seed
  | n+1 => explicitRate ((1 : Q') *
      (relativeRate seed delta n * relativeRate seed delta n +
        delta n * ((1 : Q') - relativeRate seed delta n * relativeRate seed delta n)))

/-- The relative error is computed from those same rates, not independently
supplied and later assumed to satisfy a self-consistency law. -/
def relativeError (seed : Q') (delta : Nat → Q') (n : Nat) : Q' :=
  delta n * ((1 : Q') - relativeRate seed delta n * relativeRate seed delta n)

/-- Literal equality with the existing computed-rate data at kappa=1. -/
theorem computedRate_relativeError (seed : Q') (delta : Nat → Q') (n : Nat) :
    computedRate seed (relativeError seed delta) (fun _ => 1) n = relativeRate seed delta n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change explicitRate ((1 : Q') *
      (computedRate seed (relativeError seed delta) (fun _ => 1) n *
        computedRate seed (relativeError seed delta) (fun _ => 1) n + relativeError seed delta n)) = _
    rw [ih]
    rfl

/-- Relative factors keep every constructed rate in [0,1], before any
contraction or all-scale margin is supplied. -/
theorem relativeRate_bounds (seed : Q') (delta : Nat → Q')
    (hs0 : (0 : Q') ≤ seed) (hs1 : seed ≤ (1 : Q'))
    (hd0 : ∀ n, (0 : Q') ≤ delta n) (hd1 : ∀ n, delta n ≤ (1 : Q')) :
    ∀ n, (0 : Q') ≤ relativeRate seed delta n ∧ relativeRate seed delta n ≤ (1 : Q') := by
  intro n
  induction n with
  | zero => exact ⟨hs0, hs1⟩
  | succ n ih =>
    have heq := relativeFactor_error (delta n) (relativeRate seed delta n)
    have h0 := Q'.le_trans' _ _ _
      (relativeFactor_nonnegative (delta n) (relativeRate seed delta n) (hd0 n) (hd1 n))
      (Q'.le_of_eqv heq)
    have h1 := Q'.le_trans' _ _ _ (Q'.ge_of_eqv heq)
      (relativeFactor_le_one (delta n) (relativeRate seed delta n) (hd1 n) ih.1 ih.2)
    exact ⟨rate_nonnegative _ h0, rate_le_one _ h1⟩

/-- The error of the constructed relative rates is nonnegative. -/
theorem relativeError_nonnegative (seed : Q') (delta : Nat → Q')
    (hs0 : (0 : Q') ≤ seed) (hs1 : seed ≤ (1 : Q'))
    (hd0 : ∀ n, (0 : Q') ≤ delta n) (hd1 : ∀ n, delta n ≤ (1 : Q'))
    (n : Nat) : (0 : Q') ≤ relativeError seed delta n := by
  have hr := relativeRate_bounds seed delta hs0 hs1 hd0 hd1 n
  have hsq : relativeRate seed delta n * relativeRate seed delta n ≤ (1 : Q') :=
    Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg hr.2 hr.2 (by decide) hr.1) (by decide)
  exact Q'.mul_nonneg _ _ (hd0 n) (Q'.sub_nonneg_of_le hsq)

/-- The explicitly constructed rates have the dyadic floor from the
ordinary delta prefix budget. No external error sequence or numerical
self-consistency hypothesis appears. Actual form comparisons remain open. -/
theorem relativeRate_margin_lower (seed D : Q') (delta : Nat → Q')
    (hs0 : (0 : Q') ≤ seed) (hs1 : seed < (1 : Q'))
    (hD0 : (0 : Q') ≤ D) (hD : D < seed)
    (hd0 : ∀ n, (0 : Q') ≤ delta n) (hd1 : ∀ n, delta n ≤ (1 : Q'))
    (hprefix : ∀ n, finSum delta n ≤ D) (n : Nat) :
    half ^ n * (((1 : Q') - seed)*(seed-D)) ≤ latticeMarginOf (relativeRate seed delta) n := by
  have he := relativeError_nonnegative seed delta hs0 (Q'.le_of_lt hs1) hd0 hd1
  have hrelative : ∀ n, relativeError seed delta n ≤ delta n * ((1 : Q') -
      computedRate seed (relativeError seed delta) (fun _ => 1) n *
        computedRate seed (relativeError seed delta) (fun _ => 1) n) := by
    intro i
    rw [computedRate_relativeError seed delta i]
    exact Q'.le_refl' _
  have h := computedMargin_lower_of_relativeBudget seed D (relativeError seed delta) delta
    hs1 hD0 hD he hd0 hrelative hprefix n
  change half ^ n * (((1 : Q') - seed)*(seed-D)) ≤
    (1 : Q') - computedRate seed (relativeError seed delta) (fun _ => 1) n at h
  rw [computedRate_relativeError seed delta n] at h
  exact h

end YMGap.Continuum.BF4WilsonAllNomeRGDissipationBudget

#print axioms YMGap.Continuum.BF4WilsonAllNomeRGDissipationBudget.weightedEffectiveDefect_le_relative
#print axioms YMGap.Continuum.BF4WilsonAllNomeRGDissipationBudget.relativeError_summable
#print axioms YMGap.Continuum.BF4WilsonAllNomeRGDissipationBudget.seedFloor_relativeBudget_eqv
#print axioms YMGap.Continuum.BF4WilsonAllNomeRGDissipationBudget.seedFloor_relativeBudget_positive
#print axioms YMGap.Continuum.BF4WilsonAllNomeRGDissipationBudget.computedMargin_lower_of_relativeBudget
#print axioms YMGap.Continuum.BF4WilsonAllNomeRGDissipationBudget.computedRate_relativeError
#print axioms YMGap.Continuum.BF4WilsonAllNomeRGDissipationBudget.relativeRate_bounds
#print axioms YMGap.Continuum.BF4WilsonAllNomeRGDissipationBudget.relativeError_nonnegative
#print axioms YMGap.Continuum.BF4WilsonAllNomeRGDissipationBudget.relativeRate_margin_lower
