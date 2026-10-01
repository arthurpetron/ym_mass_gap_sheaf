/-
# Positive-rational scaled resolvent on the original physical bond carrier

For t>0, this is (I+tA)^(-1), constructed from the EXISTING positive
resolvent at lambda=1/t. Its derivative-domain point is obtained by scaling
the original witnessed graph point; no new denominator inverse, source
selection, analytic hypothesis, or logarithm identification is introduced.

This is the real fixed-nome/width input for scaled imaginary shifts and a
later scaled-Cayley consistency proof, not a physical-time unitary group.
-/

import YMGap.Continuum.BF4WilsonAllNomeBondOSResolvent
import YMGap.Continuum.BF4WilsonAllNomeCompletedRealScalar
import YMGap.Continuum.BF4WilsonAllNomeResolventEquation
import YMGap.Continuum.RCSignedPairBudget

namespace YMGap.Continuum.BF4WilsonAllNomeBondOSScaledResolvent

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner (completedInner)
open YMGap.Continuum.BF4WilsonAllNomeLinear
  (completedAdd completedSmul completedSub completedNeg)
open YMGap.Continuum.BF4WilsonAllNomeLinearLaws
  (completedSmul_one completedSmul_mul completedSmul_add completedSmul_congr)
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
  (completedInner_smul_left completedInner_smul_right)
open YMGap.Continuum.BF4WilsonAllNomeCompletedRealScalar
  (rationalCauchy completedRealSmul_ofQ')
open YMGap.Continuum.BF4WilsonAllNomeBondOSCompletion
  (BondCompletion bondCompletedInner)
open YMGap.Continuum.BF4WilsonAllNomeBondOSTime
  (bondValue bondValue_injective bondValue_inner)
open YMGap.Continuum.BF4WilsonAllNomeBondOSLinear
  (bondValue_add bondValue_sub bondValue_smul bondValue_ofState)
open YMGap.Continuum.BF4WilsonAllNomeBondOSDerivative
  (Domain input output input_mk output_mk bondValue_input_mk bondValue_output_mk)
open YMGap.Continuum.BF4WilsonAllNomeBondOSResolvent
  (bondValue_resolvent input_resolventDomain inverse_right)
open YMGap.Continuum.RCSignedPairBudget (scale_congr)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "H" => BondCompletion hw0 hw1 (width := width)
local notation "D" => Domain hw0 hw1 (width := width)
local notation "B" => bondCompletedInner hw0 hw1
local notation "V" => completedInner hw0 hw1
local notation "Value" => bondValue hw0 hw1
local notation "Add" => BF4WilsonAllNomeBondOSLinear.add hw0 hw1
local notation "Sub" => BF4WilsonAllNomeBondOSLinear.sub hw0 hw1
local notation "Scale" => BF4WilsonAllNomeBondOSLinear.smul hw0 hw1
local notation "In" => input hw0 hw1
local notation "Out" => output hw0 hw1

def reciprocal (t : Q') (ht : (0 : Q') < t) : Q' := Q'.recipPos t ht

theorem reciprocal_pos (t : Q') (ht : (0 : Q') < t) :
    (0 : Q') < reciprocal t ht := Q'.recipPos_pos t ht

/-- The exact rational cancellation used by the normalized graph sum. -/
theorem time_reciprocal (t : Q') (ht : (0 : Q') < t) :
    (t * reciprocal t ht).eqv 1 := Q'.mul_recipPos_eqv t ht

/-- Rational scaling of the ACTUAL physical domain quotient. The source
point's two original range witnesses are scaled before quotienting. -/
def scaleDomain (c : Q') : D → D :=
  Quotient.lift
    (fun p => Quotient.mk (BF4WilsonAllNomeSectorDerivative.domainSetoid hw0 hw1)
      (BF4WilsonAllNomeSectorDerivative.realSmul hw0 hw1 (ofQ' c)
        (rationalCauchy c) p))
    (fun p q h => Quotient.sound (by
      change BF4WilsonAllNomeCompletedRealScalar.completedRealSmul hw0 hw1
        (ofQ' c) (rationalCauchy c) p.input.val =
        BF4WilsonAllNomeCompletedRealScalar.completedRealSmul hw0 hw1
          (ofQ' c) (rationalCauchy c) q.input.val
      rw [completedRealSmul_ofQ', completedRealSmul_ofQ', h]))

theorem input_scaleDomain (c : Q') (d : D) :
    In (scaleDomain hw0 hw1 c d) = Scale c (In d) := by
  refine Quotient.inductionOn d ?_
  intro p
  apply bondValue_injective hw0 hw1
  change Value (In (Quotient.mk _
    (BF4WilsonAllNomeSectorDerivative.realSmul hw0 hw1 (ofQ' c)
      (rationalCauchy c) p))) = _
  rw [bondValue_input_mk,bondValue_smul,bondValue_input_mk]
  change BF4WilsonAllNomeCompletedRealScalar.completedRealSmul hw0 hw1
    (ofQ' c) (rationalCauchy c) p.input.val = completedSmul hw0 hw1 c p.input.val
  exact completedRealSmul_ofQ' hw0 hw1 c (rationalCauchy c) p.input.val

theorem output_scaleDomain (c : Q') (d : D) :
    Out (scaleDomain hw0 hw1 c d) = Scale c (Out d) := by
  refine Quotient.inductionOn d ?_
  intro p
  apply bondValue_injective hw0 hw1
  change Value (Out (Quotient.mk _
    (BF4WilsonAllNomeSectorDerivative.realSmul hw0 hw1 (ofQ' c)
      (rationalCauchy c) p))) = _
  rw [bondValue_output_mk,bondValue_smul,bondValue_output_mk]
  change BF4WilsonAllNomeCompletedRealScalar.completedRealSmul hw0 hw1
    (ofQ' c) (rationalCauchy c) p.output.val = completedSmul hw0 hw1 c p.output.val
  exact completedRealSmul_ofQ' hw0 hw1 c (rationalCauchy c) p.output.val

/-- The represented graph point for `(I+tA)^(-1)x`. -/
def resolventDomain (t : Q') (ht : (0 : Q') < t) (x : H) : D :=
  scaleDomain hw0 hw1 (reciprocal t ht)
    (BF4WilsonAllNomeBondOSResolvent.resolventDomain hw0 hw1
      (reciprocal t ht) (reciprocal_pos t ht) x)

def resolvent (t : Q') (ht : (0 : Q') < t) (x : H) : H :=
  In (resolventDomain hw0 hw1 t ht x)

theorem input_resolventDomain (t : Q') (ht : (0 : Q') < t) (x : H) :
    In (resolventDomain hw0 hw1 t ht x) = resolvent hw0 hw1 t ht x := rfl

theorem resolvent_value (t : Q') (ht : (0 : Q') < t) (x : H) :
    resolvent hw0 hw1 t ht x =
      Scale (reciprocal t ht)
        (BF4WilsonAllNomeBondOSResolvent.resolvent hw0 hw1
          (reciprocal t ht) (reciprocal_pos t ht) x) := by
  unfold resolvent resolventDomain
  rw [input_scaleDomain,
    BF4WilsonAllNomeBondOSResolvent.input_resolventDomain]

theorem output_resolventDomain (t : Q') (ht : (0 : Q') < t) (x : H) :
    Out (resolventDomain hw0 hw1 t ht x) =
      Scale (reciprocal t ht)
        (Out (BF4WilsonAllNomeBondOSResolvent.resolventDomain hw0 hw1
          (reciprocal t ht) (reciprocal_pos t ht) x)) := by
  unfold resolventDomain
  rw [output_scaleDomain]

private theorem scale_time_reciprocal (t : Q') (ht : (0 : Q') < t) (y : H) :
    Scale t (Scale (reciprocal t ht) y) = y := by
  apply bondValue_injective hw0 hw1
  rw [bondValue_smul,bondValue_smul,completedSmul_mul,
    completedSmul_congr hw0 hw1 (time_reciprocal t ht) (Value y),
    completedSmul_one]

/-- Exact graph equation on the same original completed bond class. -/
theorem graph_sum (t : Q') (ht : (0 : Q') < t) (x : H) :
    Add (resolvent hw0 hw1 t ht x)
      (Scale t (Out (resolventDomain hw0 hw1 t ht x))) = x := by
  rw [resolvent_value,output_resolventDomain,scale_time_reciprocal]
  have h := BF4WilsonAllNomeBondOSResolvent.inverse_right hw0 hw1
    (reciprocal t ht) (reciprocal_pos t ht) x
  change Add
    (Scale (reciprocal t ht)
      (In (BF4WilsonAllNomeBondOSResolvent.resolventDomain hw0 hw1
        (reciprocal t ht) (reciprocal_pos t ht) x)))
    (Out (BF4WilsonAllNomeBondOSResolvent.resolventDomain hw0 hw1
      (reciprocal t ht) (reciprocal_pos t ht) x)) = x at h
  rw [BF4WilsonAllNomeBondOSResolvent.input_resolventDomain] at h
  exact h

private theorem scale_add (c : Q') (x y : H) :
    Scale c (Add x y) = Add (Scale c x) (Scale c y) := by
  apply bondValue_injective hw0 hw1
  rw [bondValue_smul,bondValue_add,bondValue_add,bondValue_smul,bondValue_smul]
  exact completedSmul_add hw0 hw1 c (Value x) (Value y)

private theorem scale_comm (a c : Q') (x : H) :
    Scale a (Scale c x) = Scale c (Scale a x) := by
  apply bondValue_injective hw0 hw1
  rw [bondValue_smul,bondValue_smul,bondValue_smul,bondValue_smul,
    completedSmul_mul,completedSmul_mul]
  exact completedSmul_congr hw0 hw1 (Q'.mul_comm_eqv a c) (Value x)

private theorem scale_sub (c : Q') (x y : H) :
    Scale c (Sub x y) = Sub (Scale c x) (Scale c y) := by
  apply bondValue_injective hw0 hw1
  rw [bondValue_smul,bondValue_sub,bondValue_sub,bondValue_smul,bondValue_smul]
  unfold completedSub completedNeg
  rw [completedSmul_add,completedSmul_mul,completedSmul_mul]
  exact congrArg (completedAdd hw0 hw1 (completedSmul hw0 hw1 c (Value x)))
    (completedSmul_congr hw0 hw1 (Q'.mul_comm_eqv c (-1)) (Value y))

private theorem old_add (lambda : Q') (hl : (0 : Q') < lambda) (x y : H) :
    BF4WilsonAllNomeBondOSResolvent.resolvent hw0 hw1 lambda hl (Add x y) =
      Add (BF4WilsonAllNomeBondOSResolvent.resolvent hw0 hw1 lambda hl x)
        (BF4WilsonAllNomeBondOSResolvent.resolvent hw0 hw1 lambda hl y) := by
  apply bondValue_injective hw0 hw1
  rw [bondValue_resolvent,bondValue_add,bondValue_add,
    bondValue_resolvent,bondValue_resolvent]
  exact BF4WilsonAllNomeResolventEquation.resolvent_add hw0 hw1 lambda hl _ _

private theorem old_smul (lambda : Q') (hl : (0 : Q') < lambda)
    (a : Q') (x : H) :
    BF4WilsonAllNomeBondOSResolvent.resolvent hw0 hw1 lambda hl (Scale a x) =
      Scale a (BF4WilsonAllNomeBondOSResolvent.resolvent hw0 hw1 lambda hl x) := by
  apply bondValue_injective hw0 hw1
  rw [bondValue_resolvent,bondValue_smul,bondValue_smul,bondValue_resolvent]
  exact BF4WilsonAllNomeResolventEquation.resolvent_smul hw0 hw1 lambda hl a _

private theorem old_sub (lambda : Q') (hl : (0 : Q') < lambda) (x y : H) :
    BF4WilsonAllNomeBondOSResolvent.resolvent hw0 hw1 lambda hl (Sub x y) =
      Sub (BF4WilsonAllNomeBondOSResolvent.resolvent hw0 hw1 lambda hl x)
        (BF4WilsonAllNomeBondOSResolvent.resolvent hw0 hw1 lambda hl y) := by
  apply bondValue_injective hw0 hw1
  rw [bondValue_resolvent,bondValue_sub,bondValue_sub,
    bondValue_resolvent,bondValue_resolvent]
  exact BF4WilsonAllNomeResolventEquation.resolvent_sub hw0 hw1 lambda hl _ _

theorem resolvent_add (t : Q') (ht : (0 : Q') < t) (x y : H) :
    resolvent hw0 hw1 t ht (Add x y) =
      Add (resolvent hw0 hw1 t ht x) (resolvent hw0 hw1 t ht y) := by
  rw [resolvent_value,resolvent_value,resolvent_value,old_add,scale_add]

theorem resolvent_smul (t : Q') (ht : (0 : Q') < t) (a : Q') (x : H) :
    resolvent hw0 hw1 t ht (Scale a x) = Scale a (resolvent hw0 hw1 t ht x) := by
  rw [resolvent_value,resolvent_value,old_smul,scale_comm]

theorem resolvent_sub (t : Q') (ht : (0 : Q') < t) (x y : H) :
    resolvent hw0 hw1 t ht (Sub x y) =
      Sub (resolvent hw0 hw1 t ht x) (resolvent hw0 hw1 t ht y) := by
  rw [resolvent_value,resolvent_value,resolvent_value,old_sub,scale_sub]

/-- The ORIGINAL graph action I+t*A, not a supplied shifted operator. -/
def shifted (t : Q') (d : D) : H := Add (In d) (Scale t (Out d))

private theorem shifted_scaled_old (t : Q') (ht : (0 : Q') < t) (d : D) :
    shifted hw0 hw1 t d = Scale t
      (BF4WilsonAllNomeBondOSResolvent.shifted hw0 hw1 (reciprocal t ht) d) := by
  apply bondValue_injective hw0 hw1
  simp only [shifted, BF4WilsonAllNomeBondOSResolvent.shifted,
    bondValue_add, bondValue_smul]
  rw [completedSmul_add, completedSmul_mul,
    completedSmul_congr hw0 hw1 (time_reciprocal t ht), completedSmul_one]

theorem inverse_right (t : Q') (ht : (0 : Q') < t) (x : H) :
    shifted hw0 hw1 t (resolventDomain hw0 hw1 t ht x) = x := by
  unfold shifted
  rw [input_resolventDomain]
  exact graph_sum hw0 hw1 t ht x

/-- Both inverse laws retain the ACTUAL original domain quotient. -/
theorem inverse_left (t : Q') (ht : (0 : Q') < t) (d : D) :
    resolventDomain hw0 hw1 t ht (shifted hw0 hw1 t d) = d := by
  apply BF4WilsonAllNomeBondOSDerivative.input_injective hw0 hw1
  rw [input_resolventDomain, shifted_scaled_old hw0 hw1 t ht d,
    resolvent_smul, resolvent_value]
  have h := congrArg (input hw0 hw1)
    (BF4WilsonAllNomeBondOSResolvent.inverse_left hw0 hw1
      (reciprocal t ht) (reciprocal_pos t ht) d)
  rw [BF4WilsonAllNomeBondOSResolvent.input_resolventDomain] at h
  rw [h, scale_time_reciprocal]

theorem resolvent_symmetric (t : Q') (ht : (0 : Q') < t) (x y : H) :
    B (resolvent hw0 hw1 t ht x) y = B x (resolvent hw0 hw1 t ht y) := by
  rw [resolvent_value,resolvent_value,bondValue_inner,bondValue_inner,
    bondValue_smul,bondValue_smul,completedInner_smul_left,
    completedInner_smul_right,bondValue_resolvent,bondValue_resolvent]
  rw [BF4WilsonAllNomeResolventEquation.resolvent_symmetric]

private theorem norm_coefficient (lambda : Q') (hl : (0 : Q') < lambda) :
    ((lambda * lambda) *
      (Q'.recipPos lambda hl * Q'.recipPos lambda hl)).eqv 1 := by
  let r := Q'.recipPos lambda hl
  show (((lambda * lambda) * (r * r)).num * ((1 : Q').den : Int)) =
    ((1 : Q').num * (((lambda * lambda) * (r * r)).den : Int))
  change ((lambda.num * lambda.num) * (r.num * r.num)) * 1 =
    1 * (((lambda * lambda) * (r * r)).den : Int)
  rw [Int.mul_one,Int.one_mul,Q'.mul_den_cast,Q'.mul_den_cast,Q'.mul_den_cast,
    Q'.recipPos_num,Q'.recipPos_den]
  simp only [Int.mul_assoc,Int.mul_comm]

/-- A uniform contraction of the ACTUAL scaled resolvent, independent of
the positive rational t. -/
theorem norm_bound (t : Q') (ht : (0 : Q') < t) (x : H) :
    RCle (B (resolvent hw0 hw1 t ht x) (resolvent hw0 hw1 t ht x)) (B x x) := by
  let lambda := reciprocal t ht
  have hl : (0 : Q') < lambda := reciprocal_pos t ht
  have hbase := BF4WilsonAllNomeBondOSResolvent.norm_bound hw0 hw1 lambda hl x
  have hscaled := RCscale_mono (Q'.le_of_lt (Q'.mul_pos hl hl)) hbase
  rw [RCscale_RCscale,scale_congr (norm_coefficient lambda hl),RCscale_one] at hscaled
  rw [resolvent_value,bondValue_inner,bondValue_smul,
    completedInner_smul_left,completedInner_smul_right,RCscale_RCscale,
    ← bondValue_inner]
  exact hscaled

#print axioms reciprocal
#print axioms reciprocal_pos
#print axioms time_reciprocal
#print axioms scaleDomain
#print axioms input_scaleDomain
#print axioms output_scaleDomain
#print axioms resolventDomain
#print axioms resolvent
#print axioms input_resolventDomain
#print axioms resolvent_value
#print axioms output_resolventDomain
#print axioms graph_sum
#print axioms resolvent_add
#print axioms resolvent_smul
#print axioms resolvent_sub
#print axioms shifted
#print axioms inverse_right
#print axioms inverse_left
#print axioms resolvent_symmetric
#print axioms norm_bound

end YMGap.Continuum.BF4WilsonAllNomeBondOSScaledResolvent
