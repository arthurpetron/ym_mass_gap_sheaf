/-
# Computed rational tangent on supplied ORIGINAL maximal graph points

Simultaneous graph approximation now controls the ORIGINAL output error,
not an input error divided by time squared. The actual graph tangent
comparison and the source's second-output norm ceiling compute a positive
rational radius with squared tangent error <= t^2*epsilon. Scaling by the
computed reciprocal gives a vanishing normalized residual on the SAME carrier.

The exact phase is -2i times the ORIGINAL derivative output. Rates belong
to supplied represented physical Points; no quotient representative is chosen.
The signed action is pinned at positive rational times. This does not assert
the converse infinitesimal-domain characterization, full-real differentiability,
physical-clock/spacing calibration, continuum survival or a physical mass gap.
-/

import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyGraphTangentComparison
import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSSecondCoreGraphDensity
import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyDyadicLimit
import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleySignedTime
import YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialContinuity

namespace YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyMaximalTangent

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSDerivative
  (Point Domain ofPoint input output)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSCompletion (ComplexBondCompletion)
open YMGap.Continuum.BF4WilsonAllNomeBondOSCompletion
  (BondCompletion bondCompletedInner)
open YMGap.Continuum.BF4WilsonAllNomeBondOSTime (bondValue_inner)
open YMGap.Continuum.BF4WilsonAllNomeBondOSLinear (bondValue_smul)
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
  (completedInner_smul_left completedInner_smul_right)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSSecondCore (first second second_output_norm_le)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSSecondCoreGraphDensity
  (physicalSecondSource physical_second_output_bound)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyGraphTangentComparison
  (tangentError graph_tangent_comparison)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyErrorBound
  (normSq preimageNorm)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyDyadicLimit
  (preimageCeiling preimageCeiling_nonnegative preimageNorm_le_ceiling)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyConsistency
  (realScale imagScale)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyDoubledIdentity (diff)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSGeometricRowsLimit (distance_symm)
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialContinuity
  (linearTolerance linearTolerance_pos linearTolerance_budget positiveBudget)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "H" => ComplexBondCompletion hw0 hw1 (width := width)
local notation "P" => Point hw0 hw1 (width := width)
local notation "D" => Domain hw0 hw1 (width := width)
local notation "N" => normSq hw0 hw1
local notation "In" => input hw0 hw1
local notation "Out" => output hw0 hw1
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)

private def one128 : Q' := Q'.mkPos 1 128 (by decide)

def graphTolerance (e : Q') : Q' := one128*e

theorem graphTolerance_positive (e : Q') (he : (0 : Q') < e) :
    (0 : Q') < graphTolerance e := Q'.mul_pos (by decide) he

/-- All approximants are computed from the SUPPLIED original graph point. -/
def approximation (p : P) (e : Q') :=
  physicalSecondSource hw0 hw1 p (graphTolerance e)

def outputCeiling (p : P) (e : Q') : Q' :=
  preimageCeiling hw0 hw1 (approximation hw0 hw1 p e)

theorem outputCeiling_nonnegative (p : P) (e : Q') :
    (0 : Q') ≤ outputCeiling hw0 hw1 p e :=
  preimageCeiling_nonnegative hw0 hw1 _

theorem secondOutput_ceiling (p : P) (e : Q') :
    RCle (N (Out (second hw0 hw1 (approximation hw0 hw1 p e))))
      (rat (outputCeiling hw0 hw1 p e)) :=
  RCle_trans (second_output_norm_le hw0 hw1 _)
    (preimageNorm_le_ceiling hw0 hw1 _)

def radiusBudget (p : P) (e : Q') : Q' :=
  736*outputCeiling hw0 hw1 p e + HalfPow.half*e

theorem radiusBudget_nonnegative (p : P) (e : Q') (he : (0 : Q') < e) :
    (0 : Q') ≤ radiusBudget hw0 hw1 p e :=
  Q'.zero_le_add _ _
    (Q'.mul_nonneg _ _ (by decide) (outputCeiling_nonnegative hw0 hw1 p e))
    (Q'.le_of_lt (ExpNeg.half_mul_pos e he))

/-- Positive radius computed from one actual graph approximation and its norm. -/
def tangentRadius (p : P) (e : Q') (he : (0 : Q') < e) : Q' :=
  linearTolerance (radiusBudget hw0 hw1 p e)
    (radiusBudget_nonnegative hw0 hw1 p e he) (HalfPow.half*e)

theorem tangentRadius_positive (p : P) (e : Q') (he : (0 : Q') < e) :
    (0 : Q') < tangentRadius hw0 hw1 p e he :=
  linearTolerance_pos _ _ (ExpNeg.half_mul_pos e he)

private theorem graphTolerance_budget (e : Q') (he : (0 : Q') < e) :
    48*graphTolerance e ≤ HalfPow.half*e := by
  have hc : 48*one128 ≤ HalfPow.half := by decide
  have h := Q'.mul_le_mul_of_nonneg_right _ _ e hc (Q'.le_of_lt he)
  have hp : Q'.eqv (48*graphTolerance e) ((48*one128)*e) :=
    Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hp) h

private theorem radius_square_budget (p : P) (e : Q') (he : (0 : Q') < e)
    (t : Q') (ht : (0 : Q') < t) (htr : t ≤ tangentRadius hw0 hw1 p e he) :
    (736*(t*t))*outputCeiling hw0 hw1 p e ≤ HalfPow.half*e := by
  let c := outputCeiling hw0 hw1 p e
  let q := HalfPow.half*e
  let B := radiusBudget hw0 hw1 p e
  have hc : (0 : Q') ≤ c := outputCeiling_nonnegative hw0 hw1 p e
  have hq : (0 : Q') ≤ q := Q'.le_of_lt (ExpNeg.half_mul_pos e he)
  have hB : (0 : Q') ≤ B := radiusBudget_nonnegative hw0 hw1 p e he
  have hB0 : 736*c ≤ B := Q'.add_le_self_of_nonneg _ _ hq
  have hqB : q ≤ B+1 := by
    have h := Q'.add_le_self_of_nonneg q (736*c)
      (Q'.mul_nonneg _ _ (by decide) hc)
    exact Q'.le_trans' _ _ _
      (Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.add_comm_eqv _ _)))
      (Q'.add_le_self_of_nonneg B 1 Q'.zero_le_one)
  have hr1 : tangentRadius hw0 hw1 p e he ≤ 1 :=
    Q'.divPos_le_of_le_mul q (B+1) (positiveBudget B hB)
      (Q'.le_trans' _ _ _ hqB (Q'.le_of_eqv (Q'.eqv_symm (Q'.one_mul_eqv _))))
  have ht1 : t ≤ 1 := Q'.le_trans' _ _ _ htr hr1
  have ht0 : (0 : Q') ≤ t := Q'.le_of_lt ht
  have htt : t*t ≤ t := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ t ht1 ht0)
    (Q'.le_of_eqv (Q'.one_mul_eqv t))
  have hs := Q'.mul_le_mul_of_nonneg_left _ _ (736*c) htt
    (Q'.mul_nonneg _ _ (by decide) hc)
  have hcB := Q'.mul_le_mul_of_nonneg_right _ _ t hB0 ht0
  have hBt := Q'.mul_le_mul_of_nonneg_left _ _ B htr hB
  have hb : B*tangentRadius hw0 hw1 p e he ≤ q :=
    linearTolerance_budget B hB (ExpNeg.half_mul_pos e he)
  have hp : Q'.eqv ((736*(t*t))*c) ((736*c)*(t*t)) :=
    poly_identity_of_normal_eq
      (.mul (.mul (.const 736) (.mul (.var 0) (.var 0))) (.var 1))
      (.mul (.mul (.const 736) (.var 1)) (.mul (.var 0) (.var 0)))
      (by decide) (fun | 0 => t | _ => c)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hp)
    (Q'.le_trans' _ _ _ hs (Q'.le_trans' _ _ _ hcB (Q'.le_trans' _ _ _ hBt hb)))

private theorem rat_le {a b : Q'} (h : a ≤ b) : RCle (rat a) (rat b) := by
  intro e he
  exact ⟨0,fun _ _ => Q'.le_trans' _ _ _ h
    (Q'.add_le_self_of_nonneg b e (Q'.le_of_lt he))⟩

private theorem scale_rat (c q : Q') : RCscale c (rat q) = rat (c*q) :=
  Quotient.sound (CRealAlg.ofQ'_mul _ _).symm

private theorem add_rat (a b : Q') : RCadd (rat a) (rat b) = rat (a+b) :=
  Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun _ => Q'.eqv_refl (a+b)))

/-- The maximal represented graph has its exact -2i rational right tangent.
The modulus is supplied as data below, not extracted from a bare quotient. -/
theorem physicalPoint_tangent_bound (p : P) (e : Q') (he : (0 : Q') < e)
    (t : Q') (ht : (0 : Q') < t) (htr : t ≤ tangentRadius hw0 hw1 p e he) :
    RCle (N (tangentError hw0 hw1 t ht (ofPoint hw0 hw1 p))) (rat ((t*t)*e)) := by
  let Y := approximation hw0 hw1 p e
  let c := outputCeiling hw0 hw1 p e
  let eta := graphTolerance e
  have hnear : RCle
      (BF4WilsonAllNomeComplexBondOSCompletion.distance hw0 hw1
        (Out (ofPoint hw0 hw1 p)) (Out (first hw0 hw1 Y))) (rat eta) := by
    rw [distance_symm]
    exact physical_second_output_bound hw0 hw1 p eta (graphTolerance_positive e he)
  have ht2 : (0 : Q') ≤ t*t := Q'.mul_nonneg _ _ (Q'.le_of_lt ht) (Q'.le_of_lt ht)
  have h4 : (0 : Q') ≤ (t*t)*(t*t) := Q'.mul_nonneg _ _ ht2 ht2
  have h := RCle_trans (graph_tangent_comparison hw0 hw1 t ht (ofPoint hw0 hw1 p) Y)
    (RCadd_le_add
      (RCscale_mono (Q'.mul_nonneg _ _ (by decide : (0 : Q') ≤ 736) h4)
        (secondOutput_ceiling hw0 hw1 p e))
      (RCscale_mono (Q'.mul_nonneg _ _ (by decide : (0 : Q') ≤ 48) ht2) hnear))
  rw [scale_rat,scale_rat,add_rat] at h
  have hinner : ((736*(t*t))*c)+48*eta ≤ e :=
    Q'.le_trans' _ _ _
      (Q'.add_le_add (radius_square_budget hw0 hw1 p e he t ht htr)
        (graphTolerance_budget e he))
      (Q'.le_of_eqv (ExpNeg.two_halves e))
  have hbudget := Q'.mul_le_mul_of_nonneg_left _ _ (t*t) hinner ht2
  have hp : Q'.eqv
      ((736*((t*t)*(t*t)))*c+(48*(t*t))*eta)
      ((t*t)*(((736*(t*t))*c)+48*eta)) :=
    poly_identity_of_normal_eq
      (.add
        (.mul (.mul (.const 736) (.mul (.mul (.var 0) (.var 0))
          (.mul (.var 0) (.var 0)))) (.var 1))
        (.mul (.mul (.const 48) (.mul (.var 0) (.var 0))) (.var 2)))
      (.mul (.mul (.var 0) (.var 0))
        (.add (.mul (.mul (.const 736) (.mul (.var 0) (.var 0))) (.var 1))
          (.mul (.const 48) (.var 2))))
      (by decide) (fun | 0 => t | 1 => c | _ => eta)
  exact RCle_trans h (rat_le (Q'.le_trans' _ _ _ (Q'.le_of_eqv hp) hbudget))

/-- Original Point and tolerance compute the whole rational tangent modulus. -/
def tangentCertificate (p : P) (e : Q') (he : (0 : Q') < e) :
    Σ' r : Q', ((0 : Q') < r) ×'
      (∀ t : Q', ∀ ht : (0 : Q') < t, t ≤ r →
        RCle (N (tangentError hw0 hw1 t ht (ofPoint hw0 hw1 p))) (rat ((t*t)*e))) :=
  ⟨tangentRadius hw0 hw1 p e he,tangentRadius_positive hw0 hw1 p e he,
    physicalPoint_tangent_bound hw0 hw1 p e he⟩

private theorem bond_norm_smul (c : Q')
    (x : BondCompletion hw0 hw1 (width := width)) :
    bondCompletedInner hw0 hw1 (BF4WilsonAllNomeBondOSLinear.smul hw0 hw1 c x)
      (BF4WilsonAllNomeBondOSLinear.smul hw0 hw1 c x) =
      RCscale (c*c) (bondCompletedInner hw0 hw1 x x) := by
  rw [bondValue_inner,bondValue_smul,bondValue_inner,
    completedInner_smul_left,completedInner_smul_right,RCscale_RCscale]

theorem normSq_realScale (c : Q') (x : H) :
    N (realScale hw0 hw1 c x) = RCscale (c*c) (N x) := by
  change RCadd
    (bondCompletedInner hw0 hw1 (BF4WilsonAllNomeBondOSLinear.smul hw0 hw1 c x.1)
      (BF4WilsonAllNomeBondOSLinear.smul hw0 hw1 c x.1))
    (bondCompletedInner hw0 hw1 (BF4WilsonAllNomeBondOSLinear.smul hw0 hw1 c x.2)
      (BF4WilsonAllNomeBondOSLinear.smul hw0 hw1 c x.2)) =
    RCscale (c*c) (RCadd (bondCompletedInner hw0 hw1 x.1 x.1)
      (bondCompletedInner hw0 hw1 x.2 x.2))
  rw [bond_norm_smul,bond_norm_smul,RCscale_RCadd]

/-- The actual tangent residual scaled by the computed positive rational
reciprocal. Its vanishing is measured by the ORIGINAL physical norm. -/
def normalizedResidual (t : Q') (ht : (0 : Q') < t) (d : D) : H :=
  realScale hw0 hw1 (Q'.recipPos t ht) (tangentError hw0 hw1 t ht d)

private theorem reciprocal_square_cancel (t : Q') (ht : (0 : Q') < t)
    (e : Q') :
    Q'.eqv ((Q'.recipPos t ht*Q'.recipPos t ht)*((t*t)*e)) e := by
  let r := Q'.recipPos t ht
  have htr : Q'.eqv (t*r) 1 := Q'.mul_recipPos_eqv t ht
  have hpoly : Q'.eqv ((r*r)*((t*t)*e)) (((t*r)*(t*r))*e) :=
    poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 0))
        (.mul (.mul (.var 1) (.var 1)) (.var 2)))
      (.mul (.mul (.mul (.var 1) (.var 0)) (.mul (.var 1) (.var 0))) (.var 2))
      (by decide) (fun | 0 => r | 1 => t | _ => e)
  have hsq : Q'.eqv ((t*r)*(t*r)) 1 :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ htr)
      (Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _) htr)
  exact Q'.eqv_trans _ _ _ hpoly
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ e hsq) (Q'.one_mul_eqv e))

theorem physicalPoint_normalized_bound (p : P) (e : Q') (he : (0 : Q') < e)
    (t : Q') (ht : (0 : Q') < t) (htr : t ≤ tangentRadius hw0 hw1 p e he) :
    RCle (N (normalizedResidual hw0 hw1 t ht (ofPoint hw0 hw1 p))) (rat e) := by
  have hr : (0 : Q') ≤ Q'.recipPos t ht := Q'.le_of_lt (Q'.recipPos_pos t ht)
  have h := RCscale_mono (Q'.mul_nonneg _ _ hr hr)
    (physicalPoint_tangent_bound hw0 hw1 p e he t ht htr)
  rw [scale_rat] at h
  have hrat : rat ((Q'.recipPos t ht*Q'.recipPos t ht)*((t*t)*e)) = rat e :=
    Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
      (fun _ => reciprocal_square_cancel t ht e))
  rw [hrat] at h
  change RCle (N (realScale hw0 hw1 (Q'.recipPos t ht)
    (tangentError hw0 hw1 t ht (ofPoint hw0 hw1 p)))) (rat e)
  rw [normSq_realScale]
  exact h

/-- The original Point computes a positive radius for its normalized residual. -/
def normalizedTangentCertificate (p : P) (e : Q') (he : (0 : Q') < e) :
    Σ' r : Q', ((0 : Q') < r) ×'
      (∀ t : Q', ∀ ht : (0 : Q') < t, t ≤ r →
        RCle (N (normalizedResidual hw0 hw1 t ht (ofPoint hw0 hw1 p))) (rat e)) :=
  ⟨tangentRadius hw0 hw1 p e he,tangentRadius_positive hw0 hw1 p e he,
    physicalPoint_normalized_bound hw0 hw1 p e he⟩

/-- The rational parameter is pinned to the constructed SIGNED group's action,
not merely an unrelated finite-product family. -/
theorem signedAction_positive_rational (t : Q') (ht : (0 : Q') < t) (x : H) :
    BF4WilsonAllNomeComplexBondOSScaledCayleySignedTime.signedAction hw0 hw1
      (SignedRealTimeData.positiveTime
        (BF4ExactSlabThermodynamicPositiveTimePins.timeValue
          (PositiveRealDyadicTimeData.rational t ht))) x =
      BF4WilsonAllNomeComplexBondOSScaledCayleyLimitMap.limitMap hw0 hw1 t ht x := by
  rw [BF4WilsonAllNomeComplexBondOSScaledCayleySignedTime.signedAction_positiveTime]
  exact BF4WilsonAllNomeComplexBondOSScaledCayleyPositiveTimePins.positiveRealAction_rational
    hw0 hw1 t ht x

#print axioms graphTolerance_positive
#print axioms approximation
#print axioms outputCeiling_nonnegative
#print axioms secondOutput_ceiling
#print axioms radiusBudget_nonnegative
#print axioms tangentRadius
#print axioms tangentRadius_positive
#print axioms physicalPoint_tangent_bound
#print axioms tangentCertificate
#print axioms normSq_realScale
#print axioms normalizedResidual
#print axioms physicalPoint_normalized_bound
#print axioms normalizedTangentCertificate
#print axioms signedAction_positive_rational

end YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyMaximalTangent
