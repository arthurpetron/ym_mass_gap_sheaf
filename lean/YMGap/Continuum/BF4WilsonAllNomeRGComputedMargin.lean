/-
# Computed RG rates: a proved dyadic margin, not an assumed rate chain

The supplied quadratic RG comparisons produce a TWO-step norm factor. Use
the rational recovery rate `(3+alpha)/4` at every step. Its margins obey
`m(n+1) = (2*m(n)-m(n)^2-E(n))/4`, where E is the actual effective defect.

For kappa >= 1 and epsilon >= 0, the computed margins have their OWN upper
bound `m(n) <= m(0)*2^-n`. A finite weighted defect budget S and positive
`floor = m(0)-m(0)^2-S/2` then give `floor*2^-n <= m(n)`. Joint induction
proves positivity before recovering each next contraction: neither global
factor caps, a B04 upper ceiling nor the opposite-direction RgRateChainκ is
assumed. All rates and the floor are explicit Q' data.

This is a conditional analytic consumer on the SAME original Wilson family.
Actual comparison functions and a useful weighted distortion/error budget
remain OPEN. The existing finite all-nome contraction can supply a seed at its
own rate, but not that budget. No survival, physical trajectory, OS scaling
limit, continuum theory or Clay theorem is constructed here.
-/

import YMGap.Continuum.BF4WilsonAllNomeRGTwoStepRecovery
import YMGap.Continuum.BF4WilsonAllNomeRGTimeSmoothingObstruction

namespace YMGap.Continuum.BF4WilsonAllNomeRGComputedMargin

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal (RCle RCscale RCadd)
open YMGap.Constructive.HalfPow
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4WilsonAllNomeRGStepComposition
open YMGap.Continuum.BF4WilsonAllNomeRGTwoStepRecovery
open YMGap.Continuum.RGExplicitRationalRate
open YMGap.Continuum.BF4WilsonAllNomeExprAnchorTrajectory (ExprAnchorTrajectory)
open YMGap.Continuum.BF4WilsonAllNomeExprMixRateContraction (WilsonVacuumSqContraction)
open YMGap.Continuum.BF4WilsonAllNomeWilsonDynamicFamily
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner (completedInner)
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime (VacuumComplement completedTime)
open YMGap.Continuum.BF4WilsonAllNomeRGTimeSmoothingObstruction
  (twoStepFactor_of_upper_comparison)

local infix:50 " ≈ " => Q'.eqv

/-- The actual rate computation, with the seed retained as data. -/
def computedRate (seed : Q') (epsilon kappa : Nat → Q') : Nat → Q'
  | 0 => seed
  | n + 1 => explicitRate
      (kappa n * (computedRate seed epsilon kappa n * computedRate seed epsilon kappa n + epsilon n))

/-- The explicit sufficient floor after quadratic and defect losses. -/
def seedFloor (seed S : Q') : Q' :=
  ((1 : Q') - seed) + -(((1 : Q') - seed) * ((1 : Q') - seed)) + -(half * S)

theorem seedFloor_eqv (seed S : Q') : seedFloor seed S ≈ seed * ((1 : Q') - seed) + -(half * S) :=
  poly_identity_of_normal_eq
    (.add (.add (.add (.const 1) (.neg (.var 0)))
      (.neg (.mul (.add (.const 1) (.neg (.var 0))) (.add (.const 1) (.neg (.var 0))))))
      (.neg (.mul (.var 2) (.var 1))))
    (.add (.mul (.var 0) (.add (.const 1) (.neg (.var 0)))) (.neg (.mul (.var 2) (.var 1))))
    (by decide) (fun | 0 => seed | 1 => S | _ => half)

/-- Every computed successor rate is at least 3/4. This records why the
effective defect must pay RG distortion as well as additive error. -/
theorem computedRate_succ_lower (seed : Q') (epsilon kappa : Nat → Q')
    (hk : ∀ n, (1 : Q') ≤ kappa n) (he : ∀ n, (0 : Q') ≤ epsilon n) (n : Nat) :
    (⟨3, 3⟩ : Q') ≤ computedRate seed epsilon kappa (n+1) := by
  have h0 : (0 : Q') ≤ kappa n * (computedRate seed epsilon kappa n * computedRate seed epsilon kappa n + epsilon n) :=
    Q'.mul_nonneg _ _ (Q'.le_trans' _ _ _ (by decide : (0 : Q') ≤ (1 : Q')) (hk n))
      (Q'.zero_le_add _ _ (SumOfSquares.q_mul_self_nonneg _) (he n))
  have hs := Q'.add_le_add_left (3 : Q') _ _ h0
  exact Q'.le_trans' _ _ _ (by decide : (⟨3, 3⟩ : Q') ≤ quarter * ((3 : Q') + 0))
    (Q'.mul_le_mul_of_nonneg_left _ _ quarter hs quarter_nonnegative)

/-- At rates at least 3/4, each effective defect pays at least 9/16 of the
norm distortion. A weighted budget cannot hide nondecaying distortion. -/
theorem effectiveDefect_distortion_lower (r kappa epsilon : Q')
    (hk : (1 : Q') ≤ kappa) (he : (0 : Q') ≤ epsilon) (hr : (⟨3, 3⟩ : Q') ≤ r) :
    (kappa + -(1 : Q')) * (⟨9, 15⟩ : Q') ≤ effectiveRgDefect kappa epsilon r := by
  have hr0 : (0 : Q') ≤ r := Q'.le_trans' _ _ _ (by decide) hr
  have hsq : (⟨9, 15⟩ : Q') ≤ r*r :=
    Q'.le_trans' _ _ _ (by decide : (⟨9, 15⟩ : Q') ≤ (⟨3, 3⟩ : Q') * (⟨3, 3⟩ : Q'))
      (Q'.mul_le_mul_of_nonneg hr hr hr0 (by decide))
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ (kappa + -(1 : Q')) hsq (Q'.sub_nonneg_of_le hk))
    (Q'.add_le_self_of_nonneg _ _ (Q'.mul_nonneg _ _
      (Q'.le_trans' _ _ _ (by decide : (0 : Q') ≤ (1 : Q')) hk) he))

theorem computedDefect_distortion_lower (seed : Q') (epsilon kappa : Nat → Q')
    (hk : ∀ n, (1 : Q') ≤ kappa n) (he : ∀ n, (0 : Q') ≤ epsilon n) (n : Nat) :
    (kappa (n+1) + -(1 : Q')) * (⟨9, 15⟩ : Q') ≤
      effectiveDefectSeq kappa epsilon (computedRate seed epsilon kappa) (n+1) :=
  effectiveDefect_distortion_lower _ _ _ (hk _) (he _) (computedRate_succ_lower seed epsilon kappa hk he n)

/-- Nonnegative effective defect makes the computed margin at most half the
previous margin. No sign on the previous rate is needed for this inequality. -/
theorem explicitRate_margin_upper (rC kappa epsilon : Q')
    (hk : (1 : Q') ≤ kappa) (he : (0 : Q') ≤ epsilon) :
    (1 : Q') - explicitRate (kappa * (rC*rC + epsilon)) ≤
      half * ((1 : Q') - rC) := by
  have hcost : (0 : Q') ≤ (((1 : Q') - rC) * ((1 : Q') - rC)) +
      effectiveRgDefect kappa epsilon rC :=
    Q'.zero_le_add _ _ (SumOfSquares.q_mul_self_nonneg _)
      (effectiveRgDefect_nonneg kappa epsilon rC hk he)
  have hid : (1 : Q') - kappa * (rC*rC + epsilon) ≈
      (((1 : Q') - rC) + ((1 : Q') - rC)) +
        -((((1 : Q') - rC) * ((1 : Q') - rC)) + effectiveRgDefect kappa epsilon rC) :=
    poly_identity_of_normal_eq
      (.add (.const 1) (.neg (.mul (.var 1) (.add (.mul (.var 0) (.var 0)) (.var 2)))))
      (.add (.add (.add (.const 1) (.neg (.var 0))) (.add (.const 1) (.neg (.var 0))))
        (.neg (.add (.mul (.add (.const 1) (.neg (.var 0))) (.add (.const 1) (.neg (.var 0))))
          (.add (.mul (.add (.var 1) (.neg (.const 1))) (.mul (.var 0) (.var 0)))
            (.mul (.var 1) (.var 2))))))
      (by decide) (fun | 0 => rC | 1 => kappa | _ => epsilon)
  have hb : (1 : Q') - kappa * (rC*rC + epsilon) ≤ ((1 : Q') - rC) + ((1 : Q') - rC) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hid)
      (Q'.le_trans' _ _ _ (Q'.add_le_add_left _ _ _ (Q'.neg_le_neg hcost))
        (Q'.le_of_eqv (Q'.eqv_of_eq (Q'.add_zero' _))))
  have hsum : quarter * (((1 : Q') - rC) + ((1 : Q') - rC)) ≈
      (quarter + quarter) * ((1 : Q') - rC) :=
    poly_identity_of_normal_eq
      (.mul (.var 0) (.add (.var 1) (.var 1)))
      (.mul (.add (.var 0) (.var 0)) (.var 1))
      (by decide) (fun | 0 => quarter | _ => (1 : Q') - rC)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (rate_margin (kappa * (rC*rC + epsilon))))
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ quarter hb quarter_nonnegative)
      (Q'.le_of_eqv (Q'.eqv_trans _ _ _ hsum
        (Q'.mul_eqv_congr_right _ _ _ (by decide : quarter + quarter ≈ half)))))

theorem computedMargin_upper (seed : Q') (epsilon kappa : Nat → Q')
    (hk : ∀ n, (1 : Q') ≤ kappa n) (he : ∀ n, (0 : Q') ≤ epsilon n) :
    ∀ n, latticeMarginOf (computedRate seed epsilon kappa) n ≤ ((1 : Q') - seed) * half ^ n := by
  intro n
  induction n with
  | zero => exact Q'.ge_of_eqv (Q'.mul_one_eqv _)
  | succ n ih =>
    have h := explicitRate_margin_upper (computedRate seed epsilon kappa n) (kappa n) (epsilon n)
      (hk n) (he n)
    have hm := Q'.mul_le_mul_of_nonneg_left _ _ half ih half_nonneg
    have hid : half * (((1 : Q') - seed) * half ^ n) ≈ ((1 : Q') - seed) * half ^ (n + 1) :=
      poly_identity_of_normal_eq
        (.mul (.var 0) (.mul (.var 1) (.var 2)))
        (.mul (.var 1) (.mul (.var 0) (.var 2)))
        (by decide) (fun | 0 => half | 1 => (1 : Q') - seed | _ => half ^ n)
    exact Q'.le_trans' _ _ _ h (Q'.le_trans' _ _ _ hm (Q'.le_of_eqv hid))

private theorem scaled_to_margin (L m : Q') (n : Nat)
    (h : L ≤ Q'.ofNat (2 ^ n) * m) : half ^ n * L ≤ m := by
  have hm := Q'.mul_le_mul_of_nonneg_left _ _ _ h (Q'.pow_nonneg half half_nonneg n)
  have hid : half ^ n * (Q'.ofNat (2 ^ n) * m) ≈ m :=
    Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
      (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.mul (.mul (.var 1) (.var 0)) (.var 2)) (by decide)
      (fun | 0 => half ^ n | 1 => Q'.ofNat (2 ^ n) | _ => m))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (ofNat_two_pow_mul_half_pow n))
        (Q'.one_mul_eqv m))
  exact Q'.le_trans' _ _ _ hm (Q'.le_of_eqv hid)

private theorem floor_le_partial (m S : Q') (E : Nat → Q')
    (hS : RgErrorSummable E 0 S) (n : Nat) :
    m + -(m*m) + -(half*S) ≤ m + -(m*m*halfGeomSum n) + -(half*weightedErrorSum E 0 n) := by
  have hG : m*m*halfGeomSum n ≤ m*m :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ (halfGeomSum_le_one n) (SumOfSquares.q_mul_self_nonneg m))
      (Q'.le_of_eqv (Q'.mul_one_eqv _))
  have hW := Q'.mul_le_mul_of_nonneg_left _ _ half (hS.2 n) half_nonneg
  exact Q'.add_le_add (Q'.add_le_add_left _ _ _ (Q'.neg_le_neg hG)) (Q'.neg_le_neg hW)

/-- Finite telescoping with positivity proved inductively, not assumed at all
scales. No fourth-power rate-chain hypothesis occurs. -/
theorem computedMargin_invariant (seed S : Q') (epsilon kappa : Nat → Q')
    (hk : ∀ n, (1 : Q') ≤ kappa n) (he : ∀ n, (0 : Q') ≤ epsilon n)
    (hm0 : (0 : Q') ≤ (1 : Q') - seed)
    (hS : RgErrorSummable (effectiveDefectSeq kappa epsilon (computedRate seed epsilon kappa)) 0 S)
    (hfloor : (0 : Q') < seedFloor seed S) :
    ∀ n, ((1 : Q') - seed) + -(((1 : Q') - seed)*((1 : Q') - seed)*halfGeomSum n) +
        -(half*weightedErrorSum (effectiveDefectSeq kappa epsilon (computedRate seed epsilon kappa)) 0 n) ≤
      Q'.ofNat (2 ^ n) * latticeMarginOf (computedRate seed epsilon kappa) n := by
  let r := computedRate seed epsilon kappa
  let m := (1 : Q') - seed
  let E := effectiveDefectSeq kappa epsilon r
  have hup := computedMargin_upper seed epsilon kappa hk he
  intro n
  induction n with
  | zero =>
    exact Q'.le_of_eqv (poly_identity_of_normal_eq
      (.add (.add (.var 0) (.neg (.mul (.mul (.var 0) (.var 0)) (.const 0))))
        (.neg (.mul (.var 1) (.const 0)))) (.mul (.const 1) (.var 0))
      (by decide) (fun | 0 => m | _ => half))
  | succ n ih =>
    have hlo : half ^ n * seedFloor seed S ≤ latticeMarginOf r n :=
      scaled_to_margin _ _ n (Q'.le_trans' _ _ _ (floor_le_partial m S E hS n) ih)
    have hmn : (0 : Q') ≤ latticeMarginOf r n :=
      Q'.le_trans' _ _ _ (Q'.mul_nonneg _ _ (Q'.pow_nonneg half half_nonneg n) (Q'.le_of_lt hfloor)) hlo
    have hs := scaled_step_core (Q'.ofNat (2 ^ n)) (latticeMarginOf r n) (latticeMarginOf r (n+1))
      (E n) m (half ^ n)
      (explicitRate_margin_step (r n) (kappa n) (epsilon n))
      (ofNat_nonneg_rg _) hmn hm0 (hup n) (ofNat_two_pow_mul_half_pow n)
    have hs' : Q'.ofNat (2 ^ n)*latticeMarginOf r n + -(m*m*half ^ (n+1)) +
        -(half*(Q'.ofNat (2 ^ n)*E n)) ≤ Q'.ofNat (2 ^ (n+1))*latticeMarginOf r (n+1) :=
      Q'.le_trans' _ _ _ hs (Q'.le_of_eqv (Q'.eqv_symm
        (Q'.mul_eqv_congr_right _ _ _ (ofNat_two_pow_succ_eqv n))))
    have hmono := Q'.add_le_add_right _ _ (-(half*(Q'.ofNat (2 ^ n)*E n)))
      (Q'.add_le_add_right _ _ (-(m*m*half ^ (n+1))) ih)
    have hre : m + -(m*m*halfGeomSum (n+1)) + -(half*weightedErrorSum E 0 (n+1)) ≈
        m + -(m*m*halfGeomSum n) + -(half*weightedErrorSum E 0 n) +
          -(m*m*half ^ (n+1)) + -(half*(Q'.ofNat (2 ^ n)*E n)) := by
      change m + -(m*m*(halfGeomSum n + half ^ (n+1))) +
        -(half*(weightedErrorSum E 0 n + Q'.ofNat (2 ^ n)*E (0+n))) ≈ _
      rw [Nat.zero_add]
      exact poly_identity_of_normal_eq
        (.add (.add (.var 0) (.neg (.mul (.mul (.var 0) (.var 0)) (.add (.var 1) (.var 2)))))
          (.neg (.mul (.var 3) (.add (.var 4) (.var 5)))))
        (.add (.add (.add (.add (.var 0) (.neg (.mul (.mul (.var 0) (.var 0)) (.var 1))))
          (.neg (.mul (.var 3) (.var 4)))) (.neg (.mul (.mul (.var 0) (.var 0)) (.var 2))))
          (.neg (.mul (.var 3) (.var 5))))
        (by decide) (fun
          | 0 => m
          | 1 => halfGeomSum n
          | 2 => half ^ (n+1)
          | 3 => half
          | 4 => weightedErrorSum E 0 n
          | _ => Q'.ofNat (2 ^ n)*E n)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hre) (Q'.le_trans' _ _ _ hmono hs')

/-- An explicit positive dyadic floor for the computed margins. -/
theorem computedMargin_lower (seed S : Q') (epsilon kappa : Nat → Q')
    (hk : ∀ n, (1 : Q') ≤ kappa n) (he : ∀ n, (0 : Q') ≤ epsilon n)
    (hm0 : (0 : Q') ≤ (1 : Q') - seed)
    (hS : RgErrorSummable (effectiveDefectSeq kappa epsilon (computedRate seed epsilon kappa)) 0 S)
    (hfloor : (0 : Q') < seedFloor seed S) (n : Nat) :
    half ^ n * seedFloor seed S ≤ latticeMarginOf (computedRate seed epsilon kappa) n :=
  scaled_to_margin _ _ n (Q'.le_trans' _ _ _
    (floor_le_partial ((1 : Q') - seed) S _ hS n)
    (computedMargin_invariant seed S epsilon kappa hk he hm0 hS hfloor n))

theorem computedRate_nonnegative (seed : Q') (epsilon kappa : Nat → Q')
    (hseed : (0 : Q') ≤ seed) (hk : ∀ n, (1 : Q') ≤ kappa n)
    (he : ∀ n, (0 : Q') ≤ epsilon n) : ∀ n, (0 : Q') ≤ computedRate seed epsilon kappa n := by
  intro n
  cases n with
  | zero => exact hseed
  | succ n =>
    exact rate_nonnegative _ (Q'.mul_nonneg _ _
      (Q'.le_trans' _ _ _ (by decide : (0 : Q') ≤ (1 : Q')) (hk n))
      (Q'.zero_le_add _ _ (SumOfSquares.q_mul_self_nonneg _) (he n)))

private theorem rate_lt_one_of_margin_pos (r : Q') (h : (0 : Q') < (1 : Q') - r) :
    r < (1 : Q') := by
  have hn := Q'.num_pos_of_pos h
  change (0 : Int) < 1 * (r.den : Int) + -r.num * 1 at hn
  change r.num * 1 < 1 * (r.den : Int)
  simp only [Int.one_mul, Int.mul_one] at *
  omega

/-- Strictness follows from the proved floor, rather than supplied global caps. -/
theorem computedRate_lt_one (seed S : Q') (epsilon kappa : Nat → Q')
    (hk : ∀ n, (1 : Q') ≤ kappa n) (he : ∀ n, (0 : Q') ≤ epsilon n)
    (hm0 : (0 : Q') ≤ (1 : Q') - seed)
    (hS : RgErrorSummable (effectiveDefectSeq kappa epsilon (computedRate seed epsilon kappa)) 0 S)
    (hfloor : (0 : Q') < seedFloor seed S) (n : Nat) : computedRate seed epsilon kappa n < (1 : Q') :=
  rate_lt_one_of_margin_pos _ (Q'.pos_of_lt_of_le
    (Q'.mul_pos (ClusteringImpliesGap.pow_pos (by decide : (0 : Q') < half) n) hfloor)
    (computedMargin_lower seed S epsilon kappa hk he hm0 hS hfloor n))

private theorem factor_le_one_of_rate_le_one (alpha : Q')
    (h : explicitRate alpha ≤ (1 : Q')) : alpha ≤ (1 : Q') := by
  have h4 := Q'.mul_le_mul_of_nonneg_left _ _ (4 : Q') h (by decide)
  have hsum : (3 : Q') + alpha ≤ (4 : Q') :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv (four_mul_rate alpha))
      (Q'.le_trans' _ _ _ h4 (by decide))
  have hc := Q'.add_le_add_right _ _ (-(3 : Q')) hsum
  have hid : ((3 : Q') + alpha) + -(3 : Q') ≈ alpha :=
    poly_identity_of_normal_eq (.add (.add (.const 3) (.var 0)) (.neg (.const 3)))
      (.var 0) (by decide) (fun _ => alpha)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hid) (Q'.le_trans' _ _ _ hc (by decide))

/-- Supplied actual comparisons and ONE seed contraction give every next
contraction at the computed rate. Neither all-scale contractions nor factor
caps are premises. The comparisons and useful budget remain analytic inputs. -/
theorem computedRate_contraction (tr : ExprAnchorTrajectory) (seed S : Q')
    (epsilon kappa : Nat → Q')
    (hk : ∀ n, (1 : Q') ≤ kappa n) (he : ∀ n, (0 : Q') ≤ epsilon n)
    (hm0 : (0 : Q') ≤ (1 : Q') - seed)
    (hS : RgErrorSummable (effectiveDefectSeq kappa epsilon (computedRate seed epsilon kappa)) 0 S)
    (hfloor : (0 : Q') < seedFloor seed S)
    (hseed : WilsonVacuumSqContraction (tr.schedule.nome_pos 0) (tr.schedule.nome_lt_one 0) (tr.width 0) seed)
    (H : ∀ n, ApproxRgIntertwiner
      (tr.schedule.nome_pos (n+1)) (tr.schedule.nome_lt_one (n+1))
      (tr.schedule.nome_pos n) (tr.schedule.nome_lt_one n)
      (tr.width (n+1)) (tr.width n) (epsilon n) (kappa n)) :
    ∀ n, WilsonVacuumSqContraction (tr.schedule.nome_pos n) (tr.schedule.nome_lt_one n)
      (tr.width n) (computedRate seed epsilon kappa n) := by
  intro n
  induction n with
  | zero => exact hseed
  | succ n ih =>
    have hcap : kappa n * (computedRate seed epsilon kappa n * computedRate seed epsilon kappa n + epsilon n) ≤ 1 :=
      factor_le_one_of_rate_le_one _
        (Q'.le_of_lt (computedRate_lt_one seed S epsilon kappa hk he hm0 hS hfloor (n+1)))
    exact approxRg_transfers_explicitRate (H n) _ ih hcap

/-- The SAME computed-rate induction needs only upper norm comparisons and
the actual two-step comparison. No coercive lower comparison is assumed or
constructed; maps losing fringe norms are not excluded by this consumer.
The action-specific comparisons and weighted defect budget remain OPEN. -/
theorem computedRate_contraction_of_upperComparisons (tr : ExprAnchorTrajectory) (seed S : Q')
    (epsilon kappa : Nat → Q')
    (hk : ∀ n, (1 : Q') ≤ kappa n) (he : ∀ n, (0 : Q') ≤ epsilon n)
    (hm0 : (0 : Q') ≤ (1 : Q') - seed)
    (hS : RgErrorSummable (effectiveDefectSeq kappa epsilon (computedRate seed epsilon kappa)) 0 S)
    (hfloor : (0 : Q') < seedFloor seed S)
    (hseed : WilsonVacuumSqContraction (tr.schedule.nome_pos 0) (tr.schedule.nome_lt_one 0) (tr.width 0) seed)
    (Phi : ∀ n, VacuumComplement (tr.schedule.nome_pos (n+1)) (tr.schedule.nome_lt_one (n+1))
      (width := tr.width (n+1)) →
        VacuumComplement (tr.schedule.nome_pos n) (tr.schedule.nome_lt_one n) (width := tr.width n))
    (hupper : ∀ n x, RCle
      (completedInner (tr.schedule.nome_pos n) (tr.schedule.nome_lt_one n) (Phi n x).val (Phi n x).val)
      (completedInner (tr.schedule.nome_pos (n+1)) (tr.schedule.nome_lt_one (n+1)) x.val x.val))
    (htwo : ∀ n x, RCle
      (completedInner (tr.schedule.nome_pos (n+1)) (tr.schedule.nome_lt_one (n+1))
        (completedTime (tr.schedule.nome_pos (n+1)) (tr.schedule.nome_lt_one (n+1)) 2 x.val)
        (completedTime (tr.schedule.nome_pos (n+1)) (tr.schedule.nome_lt_one (n+1)) 2 x.val))
      (RCadd (RCscale (kappa n)
        (completedInner (tr.schedule.nome_pos n) (tr.schedule.nome_lt_one n)
          (completedTime (tr.schedule.nome_pos n) (tr.schedule.nome_lt_one n) 1 (Phi n x).val)
          (completedTime (tr.schedule.nome_pos n) (tr.schedule.nome_lt_one n) 1 (Phi n x).val)))
        (RCscale (kappa n * epsilon n)
          (completedInner (tr.schedule.nome_pos (n+1)) (tr.schedule.nome_lt_one (n+1)) x.val x.val)))) :
    ∀ n, WilsonVacuumSqContraction (tr.schedule.nome_pos n) (tr.schedule.nome_lt_one n)
      (tr.width n) (computedRate seed epsilon kappa n) := by
  intro n
  induction n with
  | zero => exact hseed
  | succ n ih =>
    have hk0 : (0 : Q') ≤ kappa n :=
      Q'.le_trans' _ _ _ (by decide : (0 : Q') ≤ (1 : Q')) (hk n)
    have h0 : (0 : Q') ≤ kappa n *
        (computedRate seed epsilon kappa n * computedRate seed epsilon kappa n + epsilon n) :=
      Q'.mul_nonneg _ _ hk0
        (Q'.zero_le_add _ _ (SumOfSquares.q_mul_self_nonneg _) (he n))
    have hcap := factor_le_one_of_rate_le_one _
      (Q'.le_of_lt (computedRate_lt_one seed S epsilon kappa hk he hm0 hS hfloor (n+1)))
    exact vacuumSq_explicitRate_of_twoStepFactor _ h0 hcap
      (twoStepFactor_of_upper_comparison
        (tr.schedule.nome_pos (n+1)) (tr.schedule.nome_lt_one (n+1))
        (tr.schedule.nome_pos n) (tr.schedule.nome_lt_one n)
        (tr.width (n+1)) (tr.width n) (epsilon n) (kappa n)
        (computedRate seed epsilon kappa n) (Phi n) hk0 (hupper n) (htwo n) ih)

/-- Actual family witness produced from the named analytic inputs above. -/
def computedWilsonFamily (tr : ExprAnchorTrajectory) (seed S : Q')
    (epsilon kappa : Nat → Q') (hseed0 : (0 : Q') ≤ seed)
    (hk : ∀ n, (1 : Q') ≤ kappa n) (he : ∀ n, (0 : Q') ≤ epsilon n)
    (hm0 : (0 : Q') ≤ (1 : Q') - seed)
    (hS : RgErrorSummable (effectiveDefectSeq kappa epsilon (computedRate seed epsilon kappa)) 0 S)
    (hfloor : (0 : Q') < seedFloor seed S)
    (hseed : WilsonVacuumSqContraction (tr.schedule.nome_pos 0) (tr.schedule.nome_lt_one 0) (tr.width 0) seed)
    (H : ∀ n, ApproxRgIntertwiner
      (tr.schedule.nome_pos (n+1)) (tr.schedule.nome_lt_one (n+1))
      (tr.schedule.nome_pos n) (tr.schedule.nome_lt_one n)
      (tr.width (n+1)) (tr.width n) (epsilon n) (kappa n)) : WilsonDynamicFamily :=
  exprWilsonFamily tr (computedRate seed epsilon kappa)
    (computedRate_nonnegative seed epsilon kappa hseed0 hk he)
    (computedRate_lt_one seed S epsilon kappa hk he hm0 hS hfloor)
    (computedRate_contraction tr seed S epsilon kappa hk he hm0 hS hfloor hseed H)

/-- The computed family meets the EXISTING WilsonLowerMargin consumer, with
an explicit floor and its actual dyadic spacing. Physical spacing calibration
and survival are not consequences of this numerical spacing declaration. -/
theorem computedWilsonFamily_lowerMargin (tr : ExprAnchorTrajectory) (seed S : Q')
    (epsilon kappa : Nat → Q') (hseed0 : (0 : Q') ≤ seed)
    (hk : ∀ n, (1 : Q') ≤ kappa n) (he : ∀ n, (0 : Q') ≤ epsilon n)
    (hm0 : (0 : Q') ≤ (1 : Q') - seed)
    (hS : RgErrorSummable (effectiveDefectSeq kappa epsilon (computedRate seed epsilon kappa)) 0 S)
    (hfloor : (0 : Q') < seedFloor seed S)
    (hseed : WilsonVacuumSqContraction (tr.schedule.nome_pos 0) (tr.schedule.nome_lt_one 0) (tr.width 0) seed)
    (H : ∀ n, ApproxRgIntertwiner
      (tr.schedule.nome_pos (n+1)) (tr.schedule.nome_lt_one (n+1))
      (tr.schedule.nome_pos n) (tr.schedule.nome_lt_one n)
      (tr.width (n+1)) (tr.width n) (epsilon n) (kappa n)) :
    WilsonLowerMargin (computedWilsonFamily tr seed S epsilon kappa hseed0 hk he hm0 hS hfloor hseed H)
      (seedFloor seed S) := by
  refine ⟨hfloor, fun n => ?_⟩
  have h := computedMargin_lower seed S epsilon kappa hk he hm0 hS hfloor n
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv _ _)) h

end YMGap.Continuum.BF4WilsonAllNomeRGComputedMargin

#print axioms YMGap.Continuum.BF4WilsonAllNomeRGComputedMargin.explicitRate_margin_upper
#print axioms YMGap.Continuum.BF4WilsonAllNomeRGComputedMargin.seedFloor_eqv
#print axioms YMGap.Continuum.BF4WilsonAllNomeRGComputedMargin.computedRate_succ_lower
#print axioms YMGap.Continuum.BF4WilsonAllNomeRGComputedMargin.effectiveDefect_distortion_lower
#print axioms YMGap.Continuum.BF4WilsonAllNomeRGComputedMargin.computedDefect_distortion_lower
#print axioms YMGap.Continuum.BF4WilsonAllNomeRGComputedMargin.computedMargin_upper
#print axioms YMGap.Continuum.BF4WilsonAllNomeRGComputedMargin.computedMargin_invariant
#print axioms YMGap.Continuum.BF4WilsonAllNomeRGComputedMargin.computedMargin_lower
#print axioms YMGap.Continuum.BF4WilsonAllNomeRGComputedMargin.computedRate_nonnegative
#print axioms YMGap.Continuum.BF4WilsonAllNomeRGComputedMargin.computedRate_lt_one
#print axioms YMGap.Continuum.BF4WilsonAllNomeRGComputedMargin.computedRate_contraction
#print axioms YMGap.Continuum.BF4WilsonAllNomeRGComputedMargin.computedRate_contraction_of_upperComparisons
#print axioms YMGap.Continuum.BF4WilsonAllNomeRGComputedMargin.computedWilsonFamily
#print axioms YMGap.Continuum.BF4WilsonAllNomeRGComputedMargin.computedWilsonFamily_lowerMargin
