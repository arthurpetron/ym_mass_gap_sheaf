/-
# Original Euclidean/Cayley infinitesimal normalization

Both remainders below use the SAME represented original complex Wilson bond
graph point.  The Euclidean term uses the original positive-time action; the
Cayley term uses the constructed signed group's positive rational pin.  The
factor two is dimensionless lattice-time normalization, not a physical clock,
spacing conversion, continuum theory or mass-gap estimate.
-/

import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyMaximalTangent
import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSDerivative
import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSTime
import YMGap.Continuum.BF4WilsonAllNomePositiveTimePins
import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyRefinement

namespace YMGap.Continuum.BF4WilsonAllNomeComplexBondOSWickSlopeComparison

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.PositiveRealDyadicTimeData (rational)
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimePins
  (timeValue realValue realValue_pin dyadicTime)
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime (completedTime)
open YMGap.Continuum.BF4WilsonAllNomeBondOSTime
  (bondValue bondValue_injective)
open YMGap.Continuum.BF4WilsonAllNomeBondOSLinear
  (bondValue_add bondValue_negate bondValue_smul bondValue_realSmul)
open YMGap.Continuum.BF4WilsonAllNomeCompletedRealScalar
  (completedRealSmul_ofQ')
open YMGap.Continuum.BF4WilsonAllNomeLinear
  (completedAdd completedSmul completedNeg)
open YMGap.Continuum.BF4WilsonAllNomeLinearLaws
  (completedSmul_add completedSmul_mul completedSmul_congr completedSmul_one
    completedAdd_smul)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSCompletion
  (ComplexBondCompletion value)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSDerivative
  (Point ofPoint input output remainder realTaylorCertificate)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyGraphTangentComparison
  (tangentError)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyMaximalTangent
  (tangentRadius tangentRadius_positive physicalPoint_tangent_bound)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyConsistency
  (imagScale realScale cneg)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyDoubledIdentity
  (diff)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyLimitMap
  (limitMap)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyRefinement
  (normSq_imagScale add_assoc add_comm add_zero add_neg)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyErrorBound
  (normSq normSq_add_le)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "H" => ComplexBondCompletion hw0 hw1 (width := width)
local notation "P" => Point hw0 hw1 (width := width)
local notation "N" => normSq hw0 hw1
local notation "A" => BF4WilsonAllNomeComplexBondOSTime.add hw0 hw1
local notation "S" => BF4WilsonAllNomeBondOSLinear.smul hw0 hw1
local notation "RA" => BF4WilsonAllNomeBondOSLinear.add hw0 hw1
local notation "RN" => BF4WilsonAllNomeBondOSLinear.negate hw0 hw1
local notation "CNeg" => cneg hw0 hw1
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)

private def oneTenth : Q' := Q'.mkPos 1 10 (by decide)
private def eta (e : Q') : Q' := oneTenth*e

private theorem eta_positive (e : Q') (he : (0 : Q') < e) :
    (0 : Q') < eta e := Q'.mul_pos (by decide) he

private theorem rat_mul (a b : Q') :
    RCmul (rat a) (rat b) = rat (a*b) :=
  (Quotient.sound (CRealAlg.ofQ'_mul a b)).symm

private theorem scale_rat (a b : Q') : RCscale a (rat b) = rat (a*b) :=
  (Quotient.sound (CRealAlg.ofQ'_mul a b)).symm

/-- The real-valued positive rational datum has its exact rational clock. -/
theorem rational_time_value (t : Q') (ht : (0 : Q') < t) :
    realValue (timeValue (rational t ht)) = rat t := by
  rw [realValue_pin]
  rfl

/-- Actual Euclidean first-order remainder, on the original physical graph. -/
def euclideanRemainder (p : P) (t : Q') (ht : (0 : Q') < t) : H :=
  remainder hw0 hw1 (rational t ht)
    (input hw0 hw1 (ofPoint hw0 hw1 p))
    (output hw0 hw1 (ofPoint hw0 hw1 p))

/-- Combining the actual Cayley error with twice the original Euclidean
remainder cancels the common derivative output at first order. -/
def wickRemainder (p : P) (t : Q') (ht : (0 : Q') < t) : H :=
  A (tangentError hw0 hw1 t ht (ofPoint hw0 hw1 p))
    (imagScale hw0 hw1 2 (euclideanRemainder hw0 hw1 p t ht))

private theorem realSmul_rational (t : Q')
    (ct : QCauchy (ofQ' t).approx)
    (x : BF4WilsonAllNomeBondOSCompletion.BondCompletion hw0 hw1
      (width := width)) :
    BF4WilsonAllNomeBondOSLinear.realSmul hw0 hw1 (ofQ' t) ct x = S t x := by
  apply bondValue_injective hw0 hw1
  rw [bondValue_realSmul,bondValue_smul,completedRealSmul_ofQ']

/-- The original real-time remainder equals the actual Euclidean increment
minus its graph-linear term at the SAME rational time. -/
theorem euclideanRemainder_eq (p : P) (t : Q') (ht : (0 : Q') < t) :
    euclideanRemainder hw0 hw1 p t ht =
      diff hw0 hw1
        (diff hw0 hw1 (input hw0 hw1 (ofPoint hw0 hw1 p))
          (BF4WilsonAllNomeComplexBondOSTime.action hw0 hw1
            (timeValue (rational t ht)) (input hw0 hw1 (ofPoint hw0 hw1 p))))
        (realScale hw0 hw1 t (output hw0 hw1 (ofPoint hw0 hw1 p))) := by
  apply Prod.ext
  · change BF4WilsonAllNomeBondOSDerivative.bondRemainder hw0 hw1
        (rational t ht) (input hw0 hw1 (ofPoint hw0 hw1 p)).1
        (output hw0 hw1 (ofPoint hw0 hw1 p)).1 =
      BF4WilsonAllNomeBondOSLinear.sub hw0 hw1
        (BF4WilsonAllNomeBondOSLinear.sub hw0 hw1
          (input hw0 hw1 (ofPoint hw0 hw1 p)).1
          (BF4WilsonAllNomeBondOSRealTime.action hw0 hw1
            (timeValue (rational t ht)) (input hw0 hw1 (ofPoint hw0 hw1 p)).1))
        (S t (output hw0 hw1 (ofPoint hw0 hw1 p)).1)
    unfold BF4WilsonAllNomeBondOSDerivative.bondRemainder
    rw [BF4WilsonAllNomeBondOSRealTime.action_pin]
    exact congrArg (BF4WilsonAllNomeBondOSLinear.sub hw0 hw1
      (BF4WilsonAllNomeBondOSLinear.sub hw0 hw1
        (input hw0 hw1 (ofPoint hw0 hw1 p)).1
        (BF4WilsonAllNomeBondOSTime.bondAction hw0 hw1 (rational t ht)
          (input hw0 hw1 (ofPoint hw0 hw1 p)).1)))
      (realSmul_rational hw0 hw1 t (rational t ht).cauchy _)
  · change BF4WilsonAllNomeBondOSDerivative.bondRemainder hw0 hw1
        (rational t ht) (input hw0 hw1 (ofPoint hw0 hw1 p)).2
        (output hw0 hw1 (ofPoint hw0 hw1 p)).2 =
      BF4WilsonAllNomeBondOSLinear.sub hw0 hw1
        (BF4WilsonAllNomeBondOSLinear.sub hw0 hw1
          (input hw0 hw1 (ofPoint hw0 hw1 p)).2
          (BF4WilsonAllNomeBondOSRealTime.action hw0 hw1
            (timeValue (rational t ht)) (input hw0 hw1 (ofPoint hw0 hw1 p)).2))
        (S t (output hw0 hw1 (ofPoint hw0 hw1 p)).2)
    unfold BF4WilsonAllNomeBondOSDerivative.bondRemainder
    rw [BF4WilsonAllNomeBondOSRealTime.action_pin]
    exact congrArg (BF4WilsonAllNomeBondOSLinear.sub hw0 hw1
      (BF4WilsonAllNomeBondOSLinear.sub hw0 hw1
        (input hw0 hw1 (ofPoint hw0 hw1 p)).2
        (BF4WilsonAllNomeBondOSTime.bondAction hw0 hw1 (rational t ht)
          (input hw0 hw1 (ofPoint hw0 hw1 p)).2)))
      (realSmul_rational hw0 hw1 t (rational t ht).cauchy _)

private theorem scale_add (c : Q')
    (x y : BF4WilsonAllNomeBondOSCompletion.BondCompletion hw0 hw1
      (width := width)) : S c (RA x y) = RA (S c x) (S c y) := by
  apply bondValue_injective hw0 hw1
  simp only [bondValue_smul,bondValue_add]
  exact completedSmul_add hw0 hw1 c _ _

private theorem scale_mul (a b : Q')
    (x : BF4WilsonAllNomeBondOSCompletion.BondCompletion hw0 hw1
      (width := width)) : S a (S b x) = S (a*b) x := by
  apply bondValue_injective hw0 hw1
  simp only [bondValue_smul]
  exact completedSmul_mul hw0 hw1 a b _

private theorem scale_congr {a b : Q'} (h : Q'.eqv a b)
    (x : BF4WilsonAllNomeBondOSCompletion.BondCompletion hw0 hw1
      (width := width)) : S a x = S b x := by
  apply bondValue_injective hw0 hw1
  simp only [bondValue_smul]
  exact completedSmul_congr hw0 hw1 h _

private theorem scale_double (c : Q')
    (x : BF4WilsonAllNomeBondOSCompletion.BondCompletion hw0 hw1
      (width := width)) : S c (RA x x) = S (2*c) x := by
  apply bondValue_injective hw0 hw1
  simp only [bondValue_smul,bondValue_add]
  rw [completedSmul_add,completedAdd_smul]
  apply completedSmul_congr hw0 hw1
  exact poly_identity_of_normal_eq
    (.add (.var 0) (.var 0)) (.mul (.const 2) (.var 0))
    (by decide) (fun _ => c)

private theorem scale_neg (c : Q')
    (x : BF4WilsonAllNomeBondOSCompletion.BondCompletion hw0 hw1
      (width := width)) : S c (RN x) = RN (S c x) := by
  apply bondValue_injective hw0 hw1
  simp only [bondValue_smul,bondValue_negate]
  change completedSmul hw0 hw1 c (completedSmul hw0 hw1 (-1) (bondValue hw0 hw1 x)) =
    completedSmul hw0 hw1 (-1) (completedSmul hw0 hw1 c (bondValue hw0 hw1 x))
  rw [completedSmul_mul,completedSmul_mul]
  exact completedSmul_congr hw0 hw1 (Q'.mul_comm_eqv c (-1)) _

private theorem neg_additive
    (x y : BF4WilsonAllNomeBondOSCompletion.BondCompletion hw0 hw1
      (width := width)) : RN (RA x y) = RA (RN x) (RN y) := by
  apply bondValue_injective hw0 hw1
  simp only [bondValue_negate,bondValue_add]
  exact completedSmul_add hw0 hw1 (-1) _ _

private theorem imag_add (c : Q') (x y : H) :
    imagScale hw0 hw1 c (A x y) =
      A (imagScale hw0 hw1 c x) (imagScale hw0 hw1 c y) := by
  apply Prod.ext
  · exact (congrArg RN (scale_add hw0 hw1 c x.2 y.2)).trans
      (neg_additive hw0 hw1 _ _)
  · exact scale_add hw0 hw1 c x.1 y.1

private theorem imag_neg (c : Q') (x : H) :
    imagScale hw0 hw1 c (CNeg x) = CNeg (imagScale hw0 hw1 c x) :=
  Prod.ext (congrArg RN (scale_neg hw0 hw1 c x.2))
    (scale_neg hw0 hw1 c x.1)

private theorem imag_diff (c : Q') (x y : H) :
    imagScale hw0 hw1 c (diff hw0 hw1 x y) =
      diff hw0 hw1 (imagScale hw0 hw1 c x) (imagScale hw0 hw1 c y) := by
  unfold diff
  rw [imag_add,imag_neg]

private theorem imag_double_scale (t : Q') (x : H) :
    imagScale hw0 hw1 t (A x x) =
      imagScale hw0 hw1 2 (realScale hw0 hw1 t x) := by
  apply Prod.ext
  · change RN (S t (RA x.2 x.2)) = RN (S 2 (S t x.2))
    rw [scale_double,scale_mul]
  · change S t (RA x.1 x.1) = S 2 (S t x.1)
    rw [scale_double,scale_mul]

private theorem cancel_middle (a b c : H) :
    A (A a c) (diff hw0 hw1 b c) = A a b := by
  unfold diff
  calc
    A (A a c) (A b (CNeg c)) = A a (A c (A b (CNeg c))) :=
      add_assoc hw0 hw1 a c _
    _ = A a (A (A c b) (CNeg c)) := by
      rw [← add_assoc hw0 hw1 c b (CNeg c)]
    _ = A a (A (A b c) (CNeg c)) := by rw [add_comm hw0 hw1 c b]
    _ = A a (A b (A c (CNeg c))) := by
      rw [add_assoc hw0 hw1 b c (CNeg c)]
    _ = A a b := by rw [add_neg hw0 hw1 c,add_zero hw0 hw1 b]

/-- Exact SAME-action normalization: its two graph terms cancel, leaving
the Cayley increment plus twice the imaginary Euclidean increment.  This is
an algebraic tangent comparison, NOT Wick analytic continuation. -/
theorem wickRemainder_pin (p : P) (t : Q') (ht : (0 : Q') < t) :
    wickRemainder hw0 hw1 p t ht =
      A (diff hw0 hw1
          (limitMap hw0 hw1 t ht (input hw0 hw1 (ofPoint hw0 hw1 p)))
          (input hw0 hw1 (ofPoint hw0 hw1 p)))
        (imagScale hw0 hw1 2
          (diff hw0 hw1 (input hw0 hw1 (ofPoint hw0 hw1 p))
            (BF4WilsonAllNomeComplexBondOSTime.action hw0 hw1
              (timeValue (rational t ht))
              (input hw0 hw1 (ofPoint hw0 hw1 p))))) := by
  unfold wickRemainder tangentError
  rw [euclideanRemainder_eq,imag_diff,imag_double_scale]
  exact cancel_middle hw0 hw1 _ _ _

/-- BOTH represented rates are computed from one supplied graph point. -/
def wickRadius (p : P) (e : Q') (he : (0 : Q') < e) : Q' :=
  Q'.min' (tangentRadius hw0 hw1 p (eta e) (eta_positive e he))
    (realTaylorCertificate hw0 hw1 p (eta e) (eta_positive e he)).1

theorem wickRadius_positive (p : P) (e : Q') (he : (0 : Q') < e) :
    (0 : Q') < wickRadius hw0 hw1 p e he :=
  CReal.min_pos (tangentRadius_positive hw0 hw1 p (eta e) (eta_positive e he))
    (realTaylorCertificate hw0 hw1 p (eta e) (eta_positive e he)).2.1

/-- Rational time specializes the existing ORIGINAL real-Taylor certificate. -/
theorem euclidean_remainder_bound (p : P) (e : Q') (he : (0 : Q') < e)
    (t : Q') (ht : (0 : Q') < t)
    (htr : t ≤ wickRadius hw0 hw1 p e he) :
    RCle (N (euclideanRemainder hw0 hw1 p t ht))
      (rat ((t*t)*eta e)) := by
  let C := realTaylorCertificate hw0 hw1 p (eta e) (eta_positive e he)
  have hr : t ≤ C.1 :=
    Q'.le_trans' _ _ _ htr (Q'.min_le_right' _ _)
  have hclock : RCle (realValue (timeValue (rational t ht))) (rat C.1) := by
    rw [rational_time_value]
    exact leEv_le_ofQ'_of_approx_le (fun _ => hr)
  have h := C.2.2 (rational t ht) hclock
  simp only [rational_time_value] at h
  change RCle (N (euclideanRemainder hw0 hw1 p t ht))
    (RCmul (RCmul (rat t) (rat t)) (rat (eta e))) at h
  rwa [rat_mul,rat_mul] at h

private theorem wick_budget (t e : Q') :
    RCadd
      (RCadd (rat ((t*t)*eta e)) (rat ((t*t)*eta e)))
      (RCadd (rat ((2*2)*((t*t)*eta e)))
        (rat ((2*2)*((t*t)*eta e)))) = rat ((t*t)*e) := by
  let z := (t*t)*eta e
  have hpoly : Q'.eqv ((z+z)+((2*2)*z+(2*2)*z)) (10*z) :=
    poly_identity_of_normal_eq
      (.add (.add (.var 0) (.var 0))
        (.add (.mul (.mul (.const 2) (.const 2)) (.var 0))
          (.mul (.mul (.const 2) (.const 2)) (.var 0))))
      (.mul (.const 10) (.var 0)) (by decide) (fun _ => z)
  have hten : Q'.eqv (10*oneTenth) 1 := by decide
  have hfactor : Q'.eqv (10*((t*t)*(oneTenth*e))) (((10*oneTenth)*(t*t))*e) :=
    poly_identity_of_normal_eq
      (.mul (.const 10) (.mul (.mul (.var 0) (.var 0))
        (.mul (.var 1) (.var 2))))
      (.mul (.mul (.mul (.const 10) (.var 1))
        (.mul (.var 0) (.var 0))) (.var 2))
      (by decide) (fun | 0 => t | 1 => oneTenth | _ => e)
  have hinner : Q'.eqv ((10*oneTenth)*(t*t)) (t*t) :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hten)
      (Q'.one_mul_eqv _)
  have hfinal : Q'.eqv (10*z) ((t*t)*e) :=
    Q'.eqv_trans _ _ _ hfactor (Q'.mul_eqv_congr_right _ _ e hinner)
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun _ => Q'.eqv_trans _ _ _ hpoly hfinal))

/-- Computed, source-dependent dimensionless factor-two slope comparison.
No input floor, transfer logarithm or physical spacing is assumed. -/
theorem wick_remainder_bound (p : P) (e : Q') (he : (0 : Q') < e)
    (t : Q') (ht : (0 : Q') < t)
    (htr : t ≤ wickRadius hw0 hw1 p e he) :
    RCle (N (wickRemainder hw0 hw1 p t ht)) (rat ((t*t)*e)) := by
  let q := (t*t)*eta e
  have hc : RCle
      (N (tangentError hw0 hw1 t ht (ofPoint hw0 hw1 p))) (rat q) :=
    physicalPoint_tangent_bound hw0 hw1 p (eta e) (eta_positive e he)
      t ht (Q'.le_trans' _ _ _ htr (Q'.min_le_left' _ _))
  have heuc := euclidean_remainder_bound hw0 hw1 p e he t ht htr
  have hi : RCle
      (N (imagScale hw0 hw1 2 (euclideanRemainder hw0 hw1 p t ht)))
      (rat ((2*2)*q)) := by
    rw [normSq_imagScale]
    have h := RCscale_mono (by decide : (0 : Q') ≤ (2 : Q')*2) heuc
    rwa [scale_rat] at h
  unfold wickRemainder
  have hsum := normSq_add_le hw0 hw1
    (tangentError hw0 hw1 t ht (ofPoint hw0 hw1 p))
    (imagScale hw0 hw1 2 (euclideanRemainder hw0 hw1 p t ht))
  have hfour := RCadd_le_add (RCadd_le_add hc hc) (RCadd_le_add hi hi)
  change RCle _
    (RCadd
      (RCadd (rat ((t*t)*eta e)) (rat ((t*t)*eta e)))
      (RCadd (rat ((2*2)*((t*t)*eta e)))
        (rat ((2*2)*((t*t)*eta e))))) at hfour
  rw [wick_budget] at hfour
  exact RCle_trans hsum hfour

/-- The same complex physical carrier samples the ORIGINAL Euclidean
completed transfer at every strictly positive integer time. -/
theorem euclidean_integer_original (n : Nat) (hn : 0 < n) (x : H) :
    value hw0 hw1
      (BF4WilsonAllNomeComplexBondOSTime.action hw0 hw1
        (timeValue (dyadicTime ⟨0,n⟩ hn)) x) =
      (completedTime hw0 hw1 n (value hw0 hw1 x).1,
       completedTime hw0 hw1 n (value hw0 hw1 x).2) := by
  rw [BF4WilsonAllNomeComplexBondOSTime.action_value]
  change
    (BF4WilsonAllNomePositiveTimePins.realTimeAction hw0 hw1
      (timeValue (dyadicTime ⟨0,n⟩ hn)) (value hw0 hw1 x).1,
     BF4WilsonAllNomePositiveTimePins.realTimeAction hw0 hw1
      (timeValue (dyadicTime ⟨0,n⟩ hn)) (value hw0 hw1 x).2) = _
  simp only [BF4WilsonAllNomePositiveTimePins.realTimeAction_pin,
    BF4WilsonAllNomePositiveTimePins.positiveAction_original]

#print axioms rational_time_value
#print axioms euclideanRemainder
#print axioms euclideanRemainder_eq
#print axioms wickRemainder
#print axioms wickRemainder_pin
#print axioms wickRadius
#print axioms wickRadius_positive
#print axioms euclidean_remainder_bound
#print axioms wick_remainder_bound
#print axioms euclidean_integer_original

end YMGap.Continuum.BF4WilsonAllNomeComplexBondOSWickSlopeComparison
