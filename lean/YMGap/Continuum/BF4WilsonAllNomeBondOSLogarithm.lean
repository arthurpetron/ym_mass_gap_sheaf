/-
The ordinary logarithm of ORIGINAL time one on the existing bond completion.

These are literal powers of I-P and their positive logarithm partial sums,
where P is the already constructed real-time action at numerical time one.
The original derivative graph supplies the tail bound on every quotient
domain point. Convergence data are computed only for a supplied represented
DomainPoint, using its original output-range modulus: no representative of
a quotient domain is selected. This is a fixed-nome, fixed-width bond-sector
identification, not a continuum Hamiltonian or physical-spacing calibration.
-/

import YMGap.Continuum.BF4WilsonAllNomeBondOSDerivative
import YMGap.Continuum.BF4WilsonAllNomeDomainLogarithm

namespace YMGap.Continuum.BF4WilsonAllNomeBondOSLogarithm

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimePins
  (timeValue dyadicTime)
open YMGap.Continuum.BF4WilsonAllNomeBondOSCompletion
  (BondCompletion bondCompletedDistance bondCompletedInner)
open YMGap.Continuum.BF4WilsonAllNomeBondOSTime
  (bondValue bondValue_distance bondValue_inner)
open YMGap.Continuum.BF4WilsonAllNomeBondOSLinear
  (bondValue_zero bondValue_add bondValue_sub bondValue_smul)
open YMGap.Continuum.BF4WilsonAllNomeBondOSRealTime (action_value)
open YMGap.Continuum.BF4WilsonAllNomePositiveRealSemigroup (realTimeAction_original)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner (completedInner)
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime (completedTime)
open YMGap.Continuum.BF4WilsonAllNomeLinear
  (completedZero completedAdd completedSub completedSmul)
open YMGap.Continuum.BF4WilsonAllNomeSectorDerivative (DomainPoint domainSetoid graph)
open YMGap.Continuum.BF4WilsonAllNomeBondOSDerivative
  (Domain input output bondValue_input_mk bondValue_output_mk)
open YMGap.Continuum.BF4WilsonAllNomeDomainLogarithm
  (domainLogModulus domainLogarithm_bound graph_logarithm_tail_bound)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "H" => BondCompletion hw0 hw1 (width := width)
local notation "Class" => Quotient.mk (domainSetoid hw0 hw1 (width := width))
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)

/-- The existing bond real-time action at actual numerical time one. -/
def transfer (x : H) : H :=
  BF4WilsonAllNomeBondOSRealTime.action hw0 hw1
    (timeValue (dyadicTime ⟨0,1⟩ (Nat.succ_pos 0))) x

theorem bondValue_transfer (x : H) :
    bondValue hw0 hw1 (transfer hw0 hw1 x) =
      completedTime hw0 hw1 1 (bondValue hw0 hw1 x) := by
  unfold transfer
  rw [action_value, realTimeAction_original]

/-- I-P on the SAME existing bond completion. -/
def defect (x : H) : H :=
  BF4WilsonAllNomeBondOSLinear.sub hw0 hw1 x (transfer hw0 hw1 x)

theorem bondValue_defect (x : H) :
    bondValue hw0 hw1 (defect hw0 hw1 x) =
      BF4WilsonAllNomeTimeDefectMoments.defect hw0 hw1 (bondValue hw0 hw1 x) := by
  unfold defect BF4WilsonAllNomeTimeDefectMoments.defect
  rw [bondValue_sub, bondValue_transfer]

/-- Literal iterates of I-P, without an inverse or a new carrier. -/
def defectPower : Nat → H → H
  | 0, x => x
  | n+1, x => defect hw0 hw1 (defectPower n x)

theorem bondValue_defectPower (n : Nat) (x : H) :
    bondValue hw0 hw1 (defectPower hw0 hw1 n x) =
      BF4WilsonAllNomeTimeDefectMoments.defectPower hw0 hw1 n
        (bondValue hw0 hw1 x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [defectPower, BF4WilsonAllNomeTimeDefectMoments.defectPower,
        bondValue_defect, ih]

/-- The literal sum of D^(j+1)x/(j+1), with the original addition order. -/
def logPartial : Nat → H → H
  | 0, _ => BF4WilsonAllNomeBondOSLinear.zero hw0 hw1
  | n+1, x => BF4WilsonAllNomeBondOSLinear.add hw0 hw1 (logPartial n x)
      (BF4WilsonAllNomeBondOSLinear.smul hw0 hw1 (Q'.invSucc n)
        (defectPower hw0 hw1 (n+1) x))

theorem bondValue_logPartial (m : Nat) (x : H) :
    bondValue hw0 hw1 (logPartial hw0 hw1 m x) =
      BF4WilsonAllNomeUnregularizedLogPartial.unregularizedLogPartial hw0 hw1 m
        (bondValue hw0 hw1 x) := by
  induction m with
  | zero => exact bondValue_zero hw0 hw1
  | succ m ih =>
      change bondValue hw0 hw1
        (BF4WilsonAllNomeBondOSLinear.add hw0 hw1 (logPartial hw0 hw1 m x)
          (BF4WilsonAllNomeBondOSLinear.smul hw0 hw1 (Q'.invSucc m)
            (defectPower hw0 hw1 (m+1) x))) =
        completedAdd hw0 hw1
          (BF4WilsonAllNomeUnregularizedLogPartial.unregularizedLogPartial hw0 hw1 m
            (bondValue hw0 hw1 x))
          (completedSmul hw0 hw1 (Q'.invSucc m)
            (BF4WilsonAllNomeTimeDefectMoments.defectPower hw0 hw1 (m+1)
              (bondValue hw0 hw1 x)))
      rw [bondValue_add, bondValue_smul, bondValue_defectPower, ih]

/-- Every existing quotient-domain point has the original logarithm tail
bound. Quotient elimination is into Prop and produces no chosen modulus. -/
theorem domain_logarithm_tail_bound (d : Domain hw0 hw1 (width := width)) (m : Nat) :
    RCle (bondCompletedDistance hw0 hw1
      (logPartial hw0 hw1 m (input hw0 hw1 d)) (output hw0 hw1 d))
      (bondCompletedInner hw0 hw1 (defectPower hw0 hw1 m (output hw0 hw1 d))
        (defectPower hw0 hw1 m (output hw0 hw1 d))) := by
  refine Quotient.inductionOn d ?_
  intro p
  simp only [bondValue_distance, bondValue_inner, bondValue_logPartial,
    bondValue_defectPower, bondValue_input_mk, bondValue_output_mk]
  exact graph_logarithm_tail_bound hw0 hw1 (graph hw0 hw1 p) m

/-- For a supplied original point, use exactly its produced output modulus. -/
theorem represented_logarithm_bound (p : DomainPoint hw0 hw1 (width := width))
    (e : Q') (he : (0 : Q') < e) (m : Nat)
    (hm : domainLogModulus hw0 hw1 p e ≤ m) :
    RCle (bondCompletedDistance hw0 hw1
      (logPartial hw0 hw1 m (input hw0 hw1 (Class p)))
      (output hw0 hw1 (Class p))) (rat e) := by
  simp only [bondValue_distance, bondValue_logPartial,
    bondValue_input_mk, bondValue_output_mk]
  exact domainLogarithm_bound hw0 hw1 p e he m hm

/-- SAME input/output and explicit convergence data for a supplied original
domain point. There is deliberately no data extraction from quotient Domain. -/
def representedLogarithmCertificate (p : DomainPoint hw0 hw1 (width := width)) :
    Σ' y : H, Σ' modulus : Q' → Nat,
      (y = output hw0 hw1 (Class p)) ×'
      (∀ e : Q', (0 : Q') < e → ∀ m, modulus e ≤ m →
        RCle (bondCompletedDistance hw0 hw1
          (logPartial hw0 hw1 m (input hw0 hw1 (Class p))) y) (rat e)) :=
  ⟨output hw0 hw1 (Class p), domainLogModulus hw0 hw1 p, rfl,
    represented_logarithm_bound hw0 hw1 p⟩

#print axioms transfer
#print axioms bondValue_transfer
#print axioms defect
#print axioms bondValue_defect
#print axioms defectPower
#print axioms bondValue_defectPower
#print axioms logPartial
#print axioms bondValue_logPartial
#print axioms domain_logarithm_tail_bound
#print axioms represented_logarithm_bound
#print axioms representedLogarithmCertificate

end YMGap.Continuum.BF4WilsonAllNomeBondOSLogarithm
