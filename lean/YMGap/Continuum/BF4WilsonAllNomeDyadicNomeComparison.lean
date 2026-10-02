/-
# Constructed two-nome comparison of the SAME normalized dyadic response

The existing ORIGINAL joint-coupling producer truncates both exterior time
tails at its computed finite pivot and compares the actual finite-chain
expectations. Three such computed costs control the joint lag moment, the
zero-lag moment and the singleton mean. Exact normalization cancels the
shared mean correction only once:

 V_u*(R_v-R_u) = dJ_lag - R_v*dJ_zero - (1-R_v)*d(mean^2).

Both nomes retain their OWN original means, partitions and completions.
Only pinned CReal scalars are compared. The existing coarse singleton cap
32 and original positive norm floor give the explicit response cost below.
Every nome, width, loop scale, lag and finite pivot dependence is retained.
There is no cross-scale tail, carrier map, continuum limit or survival claim.
-/

import YMGap.Continuum.BF4WilsonAllNomeTimeCoupling
import YMGap.Continuum.BF4WilsonAllNomeDyadicUnitExcitation
import YMGap.Continuum.BF4WilsonAllNomeTimeDefectMoments
import YMGap.Continuum.RcQuadResidualClose

namespace YMGap.Continuum.BF4WilsonAllNomeDyadicNomeComparison

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.CRealAlg
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.RcQuadResidualClose (abs_mul_equiv geRat_abs leRat_abs_add)
open YMGap.Continuum.BF4WilsonAllNomeTimeCoupling
  (comparisonDepth joint_coupling_tolerance_bound)
open YMGap.Continuum.BF4ExactSlabWilsonFiniteWindowCoupling (finiteWindowCap)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowJointCauchy (originalJointLimit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm (unit)
open YMGap.Continuum.BF4WilsonAllNomeReflectedForm (intrinsicForm intrinsicForm_symm)
open YMGap.Continuum.BF4WilsonAllNomeLoopTimePin (loopState pairing_lag)
open YMGap.Continuum.BF4WilsonAllNomeMomentConvexity (lagExpression lagMoment lag_within)
open YMGap.Continuum.BF4WilsonAllNomeCenteredMoments (centeredTimeMoment)
open YMGap.Continuum.BF4WilsonAllNomeDyadicVariance (literal_mean_pin)
open YMGap.Continuum.BF4WilsonAllNomeDyadicUnitExcitation
open YMGap.Continuum.BF4WilsonAllNomeTimeContraction (originalJointLimit_approx_abs_bound)
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeTimeDefectMoments
  (mixedMoment_nonnegative completedTime_form_le)
open YMGap.Continuum.BF4ExactSlabLocalStarComparison (starRatio starRatio_positive)
open YMGap.Continuum.BF4WilsonJointFunctionalLaws (equiv_sub)
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDenseDyadicGap
  (leEv_cancel_mul_right_posEv)
open YMGap.Continuum.BF4DyadicWilsonSquare

private theorem order_of_approx {a b : CReal} (h : ∀ n, a.approx n ≤ b.approx n) :
    leEv a b := by
  intro epsilon he
  exact ⟨0,fun n _ => Q'.le_trans' _ _ _ (h n)
    (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt he))⟩

private theorem budget_nonnegative {x : CReal} {b : Q'}
    (h : leEv (CReal.abs x) (ofQ' b)) : (0 : Q') ≤ b := by
  apply Q'.le_of_forall_pos_add
  intro epsilon he
  obtain ⟨N,hN⟩ := h epsilon he
  exact Q'.le_trans' _ _ _ (Q'.abs_nonneg (x.approx N)) (hN N (Nat.le_refl _))

private theorem abs_neg (x : CReal) : Equiv (CReal.abs (neg x)) (CReal.abs x) :=
  SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.abs_neg' (x.approx n))

private theorem abs_product_bound {x y : CReal} {a b : Q'}
    (hx : leEv (CReal.abs x) (ofQ' a)) (hy : leEv (CReal.abs y) (ofQ' b)) :
    leEv (CReal.abs (mul x y)) (ofQ' (a*b)) :=
  leRat_of_equiv (abs_mul_equiv x y)
    (leRat_mul hx hy (geRat_abs x) (geRat_abs y)
      (budget_nonnegative hx) (budget_nonnegative hy))

private theorem abs_sub_bound {x y : CReal} {a b : Q'}
    (hx : leEv (CReal.abs x) (ofQ' a)) (hy : leEv (CReal.abs y) (ofQ' b)) :
    leEv (CReal.abs (sub x y)) (ofQ' (a+b)) :=
  leRat_abs_add hx (leRat_of_equiv (abs_neg y) hy)

private theorem abs_unit_interval (r : CReal)
    (h0 : leEv czero r) (h1 : leEv r cone) :
    leEv (CReal.abs r) cone ∧ leEv (CReal.abs (sub cone r)) cone := by
  constructor <;> intro epsilon he
  all_goals
    obtain ⟨N0,hN0⟩ := h0 epsilon he
    obtain ⟨N1,hN1⟩ := h1 epsilon he
    refine ⟨max N0 N1, fun n hn => ?_⟩
    have hl : -epsilon ≤ r.approx n := Q'.neg_le_of_zero_le_add
      (hN0 n (Nat.le_trans (Nat.le_max_left _ _) hn))
    have hu : r.approx n ≤ 1+epsilon :=
      hN1 n (Nat.le_trans (Nat.le_max_right _ _) hn)
    have heb : epsilon ≤ 1+epsilon := Q'.le_trans' _ _ _
      (Q'.add_le_self_of_nonneg epsilon 1 Q'.zero_le_one)
      (Q'.le_of_eqv (Q'.add_comm_eqv _ _))
  · exact Q'.abs_le_of_bounds
      (Q'.le_trans' _ _ _ (Q'.neg_le_neg heb) hl) hu
  · have hnr : -(r.approx n) ≤ epsilon := Q'.le_trans' _ _ _
      (Q'.neg_le_neg hl) (Q'.le_of_eqv (Q'.neg_neg_eqv epsilon))
    have hl' : -(1+epsilon) ≤ 1 + -(r.approx n) :=
      Q'.le_trans' _ _ _ (Q'.neg_le_neg hu)
        (Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg (-(r.approx n)) 1 Q'.zero_le_one)
          (Q'.le_of_eqv (Q'.add_comm_eqv _ _)))
    exact Q'.abs_le_of_bounds hl' (Q'.add_le_add_left _ _ _ hnr)

private theorem clear_abs_bound (V d : CReal) (c b : Q')
    (hc : (0 : Q') < c) (hV : leEv (ofQ' c) V)
    (h : leEv (CReal.abs (mul V d)) (ofQ' b)) :
    leEv (CReal.abs d) (ofQ' (b*Q'.recipPos c hc)) := by
  apply leEv_cancel_mul_right_posEv (F := ofQ' c) ⟨c,hc,leEv_refl _⟩
  have hVa : leEv (ofQ' c) (CReal.abs V) := leEv_trans hV
    (order_of_approx (fun n => Q'.le_abs_self (V.approx n)))
  have hmul := leEv_mul_nonneg_left (geRat_abs d) hVa
  have hcomm : Equiv (mul (CReal.abs d) (CReal.abs V)) (CReal.abs (mul V d)) :=
    (cmul_comm _ _).trans (abs_mul_equiv V d).symm
  have hleft := leEv_trans hmul (leEv_trans (leEv_of_equiv hcomm) h)
  have hright : Equiv (mul (ofQ' (b*Q'.recipPos c hc)) (ofQ' c)) (ofQ' b) :=
    SumOfSquares.Equiv_of_approx_eqv (fun _ =>
      Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _)
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _
          (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.mul_recipPos_eqv c hc)))
          (Q'.mul_one_eqv _)))
  exact leEv_trans hleft (leEv_of_equiv hright.symm)

private def comparisonPairing (r ju jv zu zv muu muv : CReal) : CReal :=
  sub (sub (sub jv ju) (mul r (sub zv zu)))
    (mul (sub cone r) (sub (mul muv muv) (mul muu muu)))

private theorem comparison_pairing_bound (r ju jv zu zv muu muv : CReal)
    (dj dz dm : Q') (hr0 : leEv czero r) (hr1 : leEv r cone)
    (hj : leEv (CReal.abs (sub jv ju)) (ofQ' dj))
    (hz : leEv (CReal.abs (sub zv zu)) (ofQ' dz))
    (hm : leEv (CReal.abs (sub muv muu)) (ofQ' dm))
    (hmu : leEv (CReal.abs muu) (ofQ' 32))
    (hmv : leEv (CReal.abs muv) (ofQ' 32)) :
    leEv (CReal.abs (comparisonPairing r ju jv zu zv muu muv))
      (ofQ' (dj+dz+64*dm)) := by
  have hr := abs_unit_interval r hr0 hr1
  have hsum : leEv (CReal.abs (add muv muu)) (ofQ' 64) := leRat_abs_add hmv hmu
  have hfactor := abs_product_bound hsum hm
  have hsq : Equiv (sub (mul muv muv) (mul muu muu))
      (mul (add muv muu) (sub muv muu)) :=
    SumOfSquares.Equiv_of_approx_eqv (fun n => poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.var 0)) (.neg (.mul (.var 1) (.var 1))))
      (.mul (.add (.var 0) (.var 1)) (.add (.var 0) (.neg (.var 1))))
      (by decide) (fun | 0 => muv.approx n | _ => muu.approx n))
  have hmean := leRat_of_equiv (abs_equiv_congr hsq) hfactor
  have hzero := leRat_mono (abs_product_bound hr.1 hz)
    (Q'.le_of_eqv (Q'.one_mul_eqv dz))
  have hmean' := leRat_mono (abs_product_bound hr.2 hmean)
    (Q'.le_of_eqv (Q'.one_mul_eqv (64*dm)))
  exact abs_sub_bound (abs_sub_bound hj hzero) hmean'

private theorem normalized_pairing_cancellation (ru rv ju jv zu zv muu muv : CReal)
    (hU : Equiv (mul ru (sub zu (mul muu muu))) (sub ju (mul muu muu)))
    (hV : Equiv (mul rv (sub zv (mul muv muv))) (sub jv (mul muv muv))) :
    Equiv (mul (sub zu (mul muu muu)) (sub rv ru))
      (comparisonPairing rv ju jv zu zv muu muv) := by
  let muU2 : YMGap.Continuum.RingNormaliser.PolyExpr := .mul (.var 5) (.var 5)
  let muV2 : YMGap.Continuum.RingNormaliser.PolyExpr := .mul (.var 6) (.var 6)
  let zUe : YMGap.Continuum.RingNormaliser.PolyExpr := .add (.var 3) (.neg muU2)
  let zVe : YMGap.Continuum.RingNormaliser.PolyExpr := .add (.var 4) (.neg muV2)
  let gUe : YMGap.Continuum.RingNormaliser.PolyExpr := .add (.var 1) (.neg muU2)
  let gVe : YMGap.Continuum.RingNormaliser.PolyExpr := .add (.var 2) (.neg muV2)
  let phiE : YMGap.Continuum.RingNormaliser.PolyExpr :=
    .add (.add (.add (.var 2) (.neg (.var 1)))
      (.neg (.mul (.var 0) (.add (.var 4) (.neg (.var 3))))))
      (.neg (.mul (.add (.const 1) (.neg (.var 0))) (.add muV2 (.neg muU2))))
  have hl := (CReal.mul_sub (sub zu (mul muu muu)) rv ru).trans
    (equiv_sub (cmul_comm _ _) ((cmul_comm _ _).trans hU))
  have he : Equiv (sub (mul rv (sub zu (mul muu muu))) (sub ju (mul muu muu)))
      (add (comparisonPairing rv ju jv zu zv muu muv)
        (sub (mul rv (sub zv (mul muv muv))) (sub jv (mul muv muv)))) :=
    SumOfSquares.Equiv_of_approx_eqv (fun n => poly_identity_of_normal_eq
      (.add (.mul (.var 0) zUe) (.neg gUe))
      (.add phiE (.add (.mul (.var 0) zVe) (.neg gVe)))
      (by decide) (fun
        | 0 => rv.approx n
        | 1 => ju.approx n
        | 2 => jv.approx n
        | 3 => zu.approx n
        | 4 => zv.approx n
        | 5 => muu.approx n
        | _ => muv.approx n))
  have hz := (equiv_sub hV (Equiv.refl _)).trans (sub_self_eqv_zero _)
  exact hl.trans (he.trans ((Equiv_add (Equiv.refl _) hz).trans
    (SumOfSquares.Equiv_of_approx_eqv (fun n => QPoly.q_add_zero_eqv _))))

variable {u v W : Q'} (hu0 : (0 : Q') < u) (huv : u ≤ v)
  (hvW : v ≤ W) (hW1 : W < (1 : Q'))

local notation "hv0" => Q'.pos_of_lt_of_le hu0 huv
local notation "hv1" => Q'.lt_of_le_of_lt hvW hW1
local notation "hu1" => Q'.lt_of_le_of_lt huv hv1

/-- Computed original finite-pivot cost, including BOTH constructed time tails. -/
def momentCost {width : Nat} (L : Nat) (e : WindowExpression width) (tau : Q') : Q' :=
  (tau + finiteWindowCap W u v L e
    (comparisonDepth hu0 huv hvW hW1 e tau+1)) + tau

/-- The raw moment cost is produced by the existing ORIGINAL coupling path,
not supplied as a comparison hypothesis. -/
theorem momentCost_bound {width : Nat} (L : Nat) (e : WindowExpression width)
    (he : Within L e) (tau : Q') (htau : (0 : Q') < tau) :
    leEv (CReal.abs (sub (originalJointLimit hv0 hv1 L e he)
      (originalJointLimit hu0 hu1 L e he)))
      (ofQ' (momentCost hu0 huv hvW hW1 L e tau)) :=
  joint_coupling_tolerance_bound hu0 huv hvW hW1 L e he tau htau

private def dyadicMean {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (scale width : Nat) (hwidth : side scale < width) : CReal :=
  originalJointLimit hw0 hw1 0 (.loop 0 (paddedSquare scale width hwidth) 1) (Nat.le_refl 0)

private theorem centered_pin {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (scale width : Nat) (hwidth : side scale < width) (lag : Nat) :
    Equiv (centeredTimeMoment hw0 hw1 lag
      (loopState (paddedSquare scale width hwidth)) (loopState (paddedSquare scale width hwidth)))
      (sub (lagMoment hw0 hw1 (paddedSquare scale width hwidth) lag)
        (mul (dyadicMean hw0 hw1 scale width hwidth) (dyadicMean hw0 hw1 scale width hwidth))) := by
  have hmu := literal_mean_pin hw0 hw1 scale width hwidth
  have hmv := (intrinsicForm_symm hw0 hw1 (unit width)
    (loopState (paddedSquare scale width hwidth))).trans hmu
  exact equiv_sub (pairing_lag hw0 hw1 (paddedSquare scale width hwidth) lag)
    ((Pivot2.mul_congr_left hmu).trans (Pivot2.mul_congr_right hmv))

private theorem response_times_norm {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (scale width : Nat) (hwidth : side scale < width) (lag : Nat) :
    Equiv (mul (dyadicUnitResponse hw0 hw1 scale width hwidth lag)
      (dyadicOriginalNorm hw0 hw1 scale width hwidth))
      (centeredTimeMoment hw0 hw1 lag (loopState (paddedSquare scale width hwidth))
        (loopState (paddedSquare scale width hwidth))) := by
  let s := dyadicNormalizer hw0 hw1 scale width hwidth
  let A := dyadicOriginalNorm hw0 hw1 scale width hwidth
  let G := centeredTimeMoment hw0 hw1 lag (loopState (paddedSquare scale width hwidth))
    (loopState (paddedSquare scale width hwidth))
  have he : Equiv (mul (mul s (mul s G)) A) (mul (mul s (mul s A)) G) :=
    SumOfSquares.Equiv_of_approx_eqv (fun n => poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.mul (.var 0) (.var 1))) (.var 2))
      (.mul (.mul (.var 0) (.mul (.var 0) (.var 2))) (.var 1))
      (by decide) (fun | 0 => s.approx n | 1 => G.approx n | _ => A.approx n))
  exact he.trans ((Pivot2.mul_congr_left
    (dyadicNormalizer_normalizes hw0 hw1 scale width hwidth)).trans (cone_mul G))

private theorem raw_response_pin {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (scale width : Nat) (hwidth : side scale < width) (lag : Nat) :
    Equiv (mul (dyadicUnitResponse hw0 hw1 scale width hwidth lag)
      (sub (lagMoment hw0 hw1 (paddedSquare scale width hwidth) 0)
        (mul (dyadicMean hw0 hw1 scale width hwidth) (dyadicMean hw0 hw1 scale width hwidth))))
      (sub (lagMoment hw0 hw1 (paddedSquare scale width hwidth) lag)
        (mul (dyadicMean hw0 hw1 scale width hwidth) (dyadicMean hw0 hw1 scale width hwidth))) :=
  (Pivot2.mul_congr_right (centered_pin hw0 hw1 scale width hwidth 0).symm).trans
    ((response_times_norm hw0 hw1 scale width hwidth lag).trans
      (centered_pin hw0 hw1 scale width hwidth lag))

private theorem response_unit_bounds {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (scale width : Nat) (hwidth : side scale < width) (lag : Nat) :
    leEv czero (dyadicUnitResponse hw0 hw1 scale width hwidth lag) ∧
      leEv (dyadicUnitResponse hw0 hw1 scale width hwidth lag) cone := by
  let x := Subtype.val (dyadicUnitExcitation hw0 hw1 scale width hwidth)
  have h0 := mixedMoment_nonnegative hw0 hw1 x lag 0
  change RCnonneg (completedInner hw0 hw1 x (completedTime hw0 hw1 lag x)) at h0
  rw [dyadicUnitResponse_pin] at h0
  have h1 := completedTime_form_le hw0 hw1 lag x
  rw [dyadicUnitResponse_pin, dyadicUnitExcitation_norm] at h1
  exact ⟨h0,h1⟩

private theorem mean_abs_bound {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (scale width : Nat) (hwidth : side scale < width) :
    leEv (CReal.abs (dyadicMean hw0 hw1 scale width hwidth)) (ofQ' 32) :=
  leEv_le_ofQ'_of_approx_le (fun n => originalJointLimit_approx_abs_bound hw0 hw1 0
    (.loop 0 (paddedSquare scale width hwidth) 1) (Nat.le_refl 0) n)

/-- Actual signed three-moment difference; both OWN means occur explicitly. -/
def dyadicNomeSignedPairing (scale width : Nat) (hwidth : side scale < width)
    (lag : Nat) : CReal :=
  comparisonPairing (dyadicUnitResponse hv0 hv1 scale width hwidth lag)
    (lagMoment hu0 hu1 (paddedSquare scale width hwidth) lag)
    (lagMoment hv0 hv1 (paddedSquare scale width hwidth) lag)
    (lagMoment hu0 hu1 (paddedSquare scale width hwidth) 0)
    (lagMoment hv0 hv1 (paddedSquare scale width hwidth) 0)
    (dyadicMean hu0 hu1 scale width hwidth) (dyadicMean hv0 hv1 scale width hwidth)

/-- Exact normalization cancels the shared mean correction ONCE, rather than
separately estimating two centered moments. No cross-carrier map is used. -/
theorem dyadicUnitResponse_nome_cancellation (scale width : Nat)
    (hwidth : side scale < width) (lag : Nat) :
    Equiv (mul (dyadicOriginalNorm hu0 hu1 scale width hwidth)
      (sub (dyadicUnitResponse hv0 hv1 scale width hwidth lag)
        (dyadicUnitResponse hu0 hu1 scale width hwidth lag)))
      (dyadicNomeSignedPairing hu0 huv hvW hW1 scale width hwidth lag) :=
  (Pivot2.mul_congr_left (centered_pin hu0 hu1 scale width hwidth 0)).trans
    (normalized_pairing_cancellation _ _ _ _ _ _ _ _
      (raw_response_pin hu0 hu1 scale width hwidth lag)
      (raw_response_pin hv0 hv1 scale width hwidth lag))

/-- The explicit finite-pivot response cost. Scale, width, integer lag, both
nomes, coupling cap, tolerance and every selected face count remain visible. -/
def dyadicNomeResponseCost (scale width : Nat) (hwidth : side scale < width)
    (lag : Nat) (tau : Q') : Q' :=
  ((momentCost hu0 huv hvW hW1 lag (lagExpression (paddedSquare scale width hwidth) lag) tau +
    momentCost hu0 huv hvW hW1 0 (lagExpression (paddedSquare scale width hwidth) 0) tau) +
    64*momentCost hu0 huv hvW hW1 0 (.loop 0 (paddedSquare scale width hwidth) 1) tau) *
      Q'.recipPos (starRatio u) (starRatio_positive hu0 hu1)

/-- Constructed comparison at fixed loop scale, width and lag. The only
inputs are actual nomes and positive tolerance; no scalar comparison or
uniform scaling hypothesis is supplied. -/
theorem dyadicUnitResponse_nome_difference_bound (scale width : Nat)
    (hwidth : side scale < width) (lag : Nat) (tau : Q') (htau : (0 : Q') < tau) :
    leEv (CReal.abs (sub (dyadicUnitResponse hv0 hv1 scale width hwidth lag)
      (dyadicUnitResponse hu0 hu1 scale width hwidth lag)))
      (ofQ' (dyadicNomeResponseCost hu0 huv hvW hW1 scale width hwidth lag tau)) := by
  have hj := momentCost_bound hu0 huv hvW hW1 lag
    (lagExpression (paddedSquare scale width hwidth) lag)
    (lag_within (paddedSquare scale width hwidth) lag) tau htau
  have hz := momentCost_bound hu0 huv hvW hW1 0
    (lagExpression (paddedSquare scale width hwidth) 0)
    (lag_within (paddedSquare scale width hwidth) 0) tau htau
  have hm := momentCost_bound hu0 huv hvW hW1 0
    (.loop 0 (paddedSquare scale width hwidth) 1) (Nat.le_refl 0) tau htau
  have hr := response_unit_bounds hv0 hv1 scale width hwidth lag
  have hp := comparison_pairing_bound _ _ _ _ _ _ _ _ _ _ hr.1 hr.2 hj hz hm
    (mean_abs_bound hu0 hu1 scale width hwidth) (mean_abs_bound hv0 hv1 scale width hwidth)
  have hclear := leEv_trans (leEv_of_equiv (abs_equiv_congr
    (dyadicUnitResponse_nome_cancellation hu0 huv hvW hW1 scale width hwidth lag))) hp
  exact clear_abs_bound _ _ (starRatio u) _ (starRatio_positive hu0 hu1)
    (dyadicOriginalNorm_floor hu0 hu1 scale width hwidth) hclear

#print axioms momentCost
#print axioms momentCost_bound
#print axioms dyadicNomeSignedPairing
#print axioms dyadicUnitResponse_nome_cancellation
#print axioms dyadicNomeResponseCost
#print axioms dyadicUnitResponse_nome_difference_bound

end YMGap.Continuum.BF4WilsonAllNomeDyadicNomeComparison
