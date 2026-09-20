/-
# Original face heat variation with no representation-cutoff loss

For 0 <= u <= v <= W < 1, construct an ORIGINAL Haar square-certificate
interval for the change in one face heat prefix. The cap is
prefixBudget(W) * (1/W) * |v-u| and is independent of cutoff, face and extent.
All coupling dependence is explicit. No spatial or continuum estimate follows
from this local estimate alone.
-/
import YMGap.Continuum.BoundedNomePowerDifference
import YMGap.Continuum.SU2HeatQuarticPrefixBound
import YMGap.Continuum.BF4ExactSlabAllNomeTailInterval

namespace YMGap.Continuum.BF4ExactSlabCouplingVariationInterval

set_option autoImplicit false
open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.HeatKernelGap (qpow_mono)
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation (finitePolySum)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace
open YMGap.Continuum.BF4ExactSlabAllExtentFaceHeatTail
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm (faceHeatPolynomial)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarUnitScalarSquare
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarSharpCharacterInterval
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num (a : Q') : (-a).num = -(a.num) := rfl
local macro "ring_qeqv" : tactic =>
  `(tactic| (try unfold Q'.sub;
             show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast, Q'.mul_den_cast,
               Q'.neg_den, neg_num, Q'.ofNat_num_cast, Q'.ofNat_den_cast,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg,
               Int.one_mul, Int.mul_one, Int.zero_mul, Int.mul_zero, Int.zero_add, Int.add_zero];
             try ac_rfl))

def couplingScale (W u v : Q') : Q' := HKConv.divPos 1 W * Q'.abs (v + -u)
def variationCap (W u v : Q') : Q' := SU2HeatQuarticPrefixBound.prefixBudget W * couplingScale W u v

theorem couplingScale_nonnegative (W u v : Q') : (0 : Q') ≤ couplingScale W u v :=
  Q'.mul_nonneg _ _ (HKConv.divPos_nonneg Q'.zero_le_one) (Q'.abs_nonneg _)

theorem variationCap_nonnegative {W : Q'} (hW0 : (0 : Q') < W) (u v : Q') :
    (0 : Q') ≤ variationCap W u v :=
  Q'.mul_nonneg _ _ (SU2HeatQuarticPrefixBound.prefixBudget_nonnegative hW0)
    (couplingScale_nonnegative W u v)

theorem coefficient_difference_nonnegative {u v : Q'} (hu : (0 : Q') ≤ u) (huv : u ≤ v) (n : Nat) :
    (0 : Q') ≤ coeffW v n + -coeffW u n :=
  Q'.sub_nonneg_of_le (Q'.mul_le_mul_of_nonneg_left _ _ _ (qpow_mono hu huv (c4 n)) (zero_le_ofNat _))

private theorem casimir_le_square (n : Nat) : c4 n ≤ (n+1)^2 := by
  unfold c4
  simp only [Nat.pow_two, Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
  omega

/-- The damping survives differentiation of the ACTUAL SU(2) heat coefficient. -/
theorem coefficient_dimension_difference_bound {u v W : Q'}
    (hu0 : (0 : Q') ≤ u) (huv : u ≤ v) (hvW : v ≤ W) (hW0 : (0 : Q') < W) (n : Nat) :
    (coeffW v n + -coeffW u n) * dimQ n ≤ tailTerm W 4 n * couplingScale W u v := by
  have hv0 := Q'.le_trans' _ _ _ hu0 huv
  have hpow0 := Q'.sub_nonneg_of_le (qpow_mono hu0 huv (c4 n))
  have hp := BoundedNomePowerDifference.weighted_qpow_difference hv0 hu0 hvW
    (Q'.le_trans' _ _ _ huv hvW) hW0 (c4 n)
  have hd0 : (0 : Q') ≤ dimQ n * dimQ n := Q'.mul_nonneg _ _ (zero_le_ofNat _) (zero_le_ofNat _)
  have hp' := Q'.mul_le_mul_of_nonneg_left _ _ (dimQ n * dimQ n) hp hd0
  have hleft : W*((coeffW v n + -coeffW u n)*dimQ n) ≈
      (dimQ n*dimQ n)*(W*Q'.abs (qpow v (c4 n) + -qpow u (c4 n))) := by
    refine Q'.eqv_trans _ _ _ ?_
      (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_eqv_congr_left _ _ _
        (by rw [TrigAdd.abs_of_nonneg hpow0]; exact Q'.eqv_refl _)))
    unfold coeffW
    ring_qeqv
  have hdim : dimQ n * dimQ n * Q'.ofNat (c4 n) ≤ Q'.ofNat ((n+1)^4) := by
    have h := Q'.mul_le_mul_of_nonneg_left _ _ (dimQ n*dimQ n)
      (CReal.ofNat_le_ofNat (casimir_le_square n)) hd0
    refine Q'.le_trans' _ _ _ h (Q'.le_of_eqv ?_)
    have hn : ((n+1)*(n+1))*((n+1)^2) = (n+1)^4 := by
      simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
      ac_rfl
    exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (SU3CharFactor.ofNat_mul_eqv _ _))
      (Q'.eqv_trans _ _ _ (Q'.eqv_symm (SU3CharFactor.ofNat_mul_eqv _ _))
        (by rw [hn]; exact Q'.eqv_refl _))
  have hright : (dimQ n*dimQ n)*((Q'.ofNat (c4 n)*qpow W (c4 n))*Q'.abs (v + -u)) ≈
      (dimQ n*dimQ n*Q'.ofNat (c4 n))*(qpow W (c4 n)*Q'.abs (v + -u)) := by ring_qeqv
  have hb := Q'.mul_le_mul_of_nonneg_right _ _ (qpow W (c4 n)*Q'.abs (v + -u)) hdim
    (Q'.mul_nonneg _ _ (qpow_nonneg W (Q'.le_of_lt hW0) (c4 n)) (Q'.abs_nonneg (v + -u)))
  have hcancel : W*(tailTerm W 4 n*couplingScale W u v) ≈
      Q'.ofNat ((n+1)^4)*(qpow W (c4 n)*Q'.abs (v + -u)) := by
    have he : W*(tailTerm W 4 n*couplingScale W u v) ≈
        (HKConv.divPos 1 W*W)*(Q'.ofNat ((n+1)^4)*(qpow W (c4 n)*Q'.abs (v + -u))) := by
      unfold tailTerm couplingScale
      ring_qeqv
    exact Q'.eqv_trans _ _ _ he (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (HKConv.divPos_mul_eqv (CReal.num_pos_of_pos hW0)))
      (Q'.one_mul_eqv _))
  apply HKConvGen.mul_le_mul_left_cancel hW0
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _ hp' (Q'.le_trans' _ _ _ (Q'.le_of_eqv hright)
      (Q'.le_trans' _ _ _ hb (Q'.ge_of_eqv hcancel))))

def differenceTerm (u v : Q') (extent id n : Nat) : RatPoly :=
  polySmul (coeffW v n + -coeffW u n) (characterPolynomial (faceScalar extent id) n)

def faceDifference (u v : Q') (K extent id : Nat) : RatPoly :=
  finitePolySum (differenceTerm u v extent id) (List.range (K+1))

def differenceTermInterval {u v W : Q'} (hu0 : (0 : Q') ≤ u) (huv : u ≤ v)
    (hvW : v ≤ W) (hW0 : (0 : Q') < W) (extent id : Nat)
    (hi : id ∈ slabPhysicalFaceEdges extent) (n : Nat) :
    Interval (boundaryCompleteSlabLinks extent).length (differenceTerm u v extent id n)
      (tailTerm W 4 n*couplingScale W u v) :=
  ((sharpCharacterInterval (.scalar (supported_slabPlaquette _ _)
    (haarNorm_slabPlaquette (slabPlaquetteAt_mem hi))) n).smul
      (coeffW v n + -coeffW u n) (coefficient_difference_nonnegative hu0 huv n)).weaken
        (coefficient_dimension_difference_bound hu0 huv hvW hW0 n)

def faceDifferenceInterval {u v W : Q'} (hu0 : (0 : Q') ≤ u) (huv : u ≤ v)
    (hvW : v ≤ W) (hW0 : (0 : Q') < W) (hW1 : W < (1 : Q'))
    (K extent id : Nat) (hi : id ∈ slabPhysicalFaceEdges extent) :
    Interval (boundaryCompleteSlabLinks extent).length (faceDifference u v K extent id)
      (variationCap W u v) :=
  ((Interval.finiteRange (differenceTerm u v extent id) (fun n => tailTerm W 4 n*couplingScale W u v)
    (differenceTermInterval hu0 huv hvW hW0 extent id hi) (K+1)).changeCap
      (Q'.eqv_symm (finSum_mul_const (tailTerm W 4) (couplingScale W u v) (K+1)))).weaken
    (Q'.mul_le_mul_of_nonneg_right _ _ _ (SU2HeatQuarticPrefixBound.prefix_bound hW0 hW1 _)
      (couplingScale_nonnegative W u v))

private theorem term_pin (u v : Q') (extent id n : Nat) : RatPolyCoeffEqv
    (faceHeatTerm v extent id n) (polyAdd (faceHeatTerm u extent id n) (differenceTerm u v extent id n)) := by
  exact ((RatPolyCoeffEqv.add_smul_same _ _ _).trans
    (RatPolyCoeffEqv.smul_coefficient (poly_identity_of_normal_eq
      (.add (.var 0) (.add (.var 1) (.neg (.var 0)))) (.var 1) (by decide)
      (fun | 0 => coeffW u n | _ => coeffW v n)) _)).symm

private theorem sum_pin (f g h : Nat → RatPoly) (hp : ∀ n, RatPolyCoeffEqv (f n) (polyAdd (g n) (h n))) :
    ∀ xs, RatPolyCoeffEqv (finitePolySum f xs) (polyAdd (finitePolySum g xs) (finitePolySum h xs))
  | [] => RatPolyCoeffEqv.refl _
  | n::xs => ((hp n).add (sum_pin f g h hp xs)).trans
      (coeffEvalExpr_eqv_of_normalize_eq
        (.add (.add (.var 0) (.var 1)) (.add (.var 2) (.var 3)))
        (.add (.add (.var 0) (.var 2)) (.add (.var 1) (.var 3))) (by decide)
        (fun | 0 => g n | 1 => h n | 2 => finitePolySum g xs | _ => finitePolySum h xs))

/-- Exact original-polynomial identity, including all signed cancellation. -/
theorem faceDifference_pin (u v : Q') (K extent id : Nat) : RatPolyCoeffEqv
    (faceHeatPolynomial v K extent id)
    (polyAdd (faceHeatPolynomial u K extent id) (faceDifference u v K extent id)) := by
  rw [faceHeatPolynomial_eq_sum, faceHeatPolynomial_eq_sum]
  exact sum_pin _ _ _ (term_pin u v extent id) _

end YMGap.Continuum.BF4ExactSlabCouplingVariationInterval

#print axioms YMGap.Continuum.BF4ExactSlabCouplingVariationInterval.couplingScale
#print axioms YMGap.Continuum.BF4ExactSlabCouplingVariationInterval.variationCap
#print axioms YMGap.Continuum.BF4ExactSlabCouplingVariationInterval.couplingScale_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabCouplingVariationInterval.variationCap_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabCouplingVariationInterval.coefficient_difference_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabCouplingVariationInterval.coefficient_dimension_difference_bound
#print axioms YMGap.Continuum.BF4ExactSlabCouplingVariationInterval.differenceTerm
#print axioms YMGap.Continuum.BF4ExactSlabCouplingVariationInterval.faceDifference
#print axioms YMGap.Continuum.BF4ExactSlabCouplingVariationInterval.differenceTermInterval
#print axioms YMGap.Continuum.BF4ExactSlabCouplingVariationInterval.faceDifferenceInterval
#print axioms YMGap.Continuum.BF4ExactSlabCouplingVariationInterval.faceDifference_pin
