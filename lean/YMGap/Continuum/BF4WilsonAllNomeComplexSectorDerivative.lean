/-
# Intrinsic complex derivative graph on the original witnessed time sector

The domain consists of two explicit real derivative-domain points. Complex
adjoint tests reduce to their real and imaginary component tests against the
same witnessed graph. This is a direct complexification of that graph, not
an identification with an OS Hilbert space or a physical Hamiltonian.
-/

import YMGap.Continuum.BF4WilsonAllNomeComplexification
import YMGap.Continuum.BF4WilsonAllNomeComplexTimeSector
import YMGap.Continuum.BF4WilsonAllNomeSectorDerivative
import YMGap.Continuum.BF4WilsonAllNomeComplexGap

namespace YMGap.Continuum.BF4WilsonAllNomeComplexSectorDerivative

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeComplexification

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "Z" => completedZero hw0 hw1 width
local notation "T" => completedTime hw0 hw1
local notation "A" => BF4WilsonAllNomeDyadicDerivative.derivativeAction hw0 hw1
local notation "I" => inner hw0 hw1 width
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)

/-- Use the already constructed complex sector, with both original range
witnesses and its computed Cauchy modulus. -/
abbrev State := BF4WilsonAllNomeComplexTimeSector.State hw0 hw1 (width := width)

def stateValue (x : State hw0 hw1 (width := width)) :
    ComplexCarrier hw0 hw1 width := BF4WilsonAllNomeComplexTimeSector.val hw0 hw1 x

/-- Two original real domain points, not a new abstract graph relation. -/
abbrev DomainPoint := BF4WilsonAllNomeSectorDerivative.DomainPoint hw0 hw1 (width := width) ×
  BF4WilsonAllNomeSectorDerivative.DomainPoint hw0 hw1 (width := width)

def input (p : DomainPoint hw0 hw1 (width := width)) : State hw0 hw1 (width := width) :=
  (p.1.input,p.2.input)

def output (p : DomainPoint hw0 hw1 (width := width)) : State hw0 hw1 (width := width) :=
  (p.1.output,p.2.output)

/-- The action is single-valued for the ORIGINAL complex input equality. -/
theorem output_congr (p q : DomainPoint hw0 hw1 (width := width))
    (h : stateValue hw0 hw1 (input hw0 hw1 p) = stateValue hw0 hw1 (input hw0 hw1 q)) :
    stateValue hw0 hw1 (output hw0 hw1 p) = stateValue hw0 hw1 (output hw0 hw1 q) :=
  Prod.ext (BF4WilsonAllNomeSectorDerivative.output_congr hw0 hw1 p.1 q.1 (congrArg Prod.fst h))
    (BF4WilsonAllNomeSectorDerivative.output_congr hw0 hw1 p.2 q.2 (congrArg Prod.snd h))

def add (p q : DomainPoint hw0 hw1 (width := width)) :
    DomainPoint hw0 hw1 (width := width) :=
  (BF4WilsonAllNomeSectorDerivative.add hw0 hw1 p.1 q.1,
    BF4WilsonAllNomeSectorDerivative.add hw0 hw1 p.2 q.2)

def realSmul (s : CReal) (cs : QCauchy s.approx)
    (p : DomainPoint hw0 hw1 (width := width)) :
    DomainPoint hw0 hw1 (width := width) :=
  (BF4WilsonAllNomeSectorDerivative.realSmul hw0 hw1 s cs p.1,
    BF4WilsonAllNomeSectorDerivative.realSmul hw0 hw1 s cs p.2)

def negateReal (p : BF4WilsonAllNomeSectorDerivative.DomainPoint hw0 hw1 (width := width)) :
    BF4WilsonAllNomeSectorDerivative.DomainPoint hw0 hw1 (width := width) where
  input := BF4WilsonAllNomeTimeSector.negate hw0 hw1 p.input
  output := BF4WilsonAllNomeTimeSector.negate hw0 hw1 p.output
  equation := by
    change A (completedNeg hw0 hw1 p.input.val) =
      T 1 (completedNeg hw0 hw1 p.output.val)
    unfold completedNeg
    rw [BF4WilsonAllNomeDyadicDerivativeLaws.derivativeAction_smul,
      completedTime_smul,p.equation]

/-- The complex scalar is the two real graph operations in precisely the
same order as the existing witnessed complex-sector scalar action. -/
def smul (s t : CReal) (cs : QCauchy s.approx) (ct : QCauchy t.approx)
    (p : DomainPoint hw0 hw1 (width := width)) :
    DomainPoint hw0 hw1 (width := width) :=
  (BF4WilsonAllNomeSectorDerivative.add hw0 hw1
      (BF4WilsonAllNomeSectorDerivative.realSmul hw0 hw1 s cs p.1)
      (negateReal hw0 hw1
        (BF4WilsonAllNomeSectorDerivative.realSmul hw0 hw1 t ct p.2)),
   BF4WilsonAllNomeSectorDerivative.add hw0 hw1
      (BF4WilsonAllNomeSectorDerivative.realSmul hw0 hw1 t ct p.1)
      (BF4WilsonAllNomeSectorDerivative.realSmul hw0 hw1 s cs p.2))

theorem smul_input (s t : CReal) (cs : QCauchy s.approx) (ct : QCauchy t.approx)
    (p : DomainPoint hw0 hw1 (width := width)) :
    stateValue hw0 hw1 (input hw0 hw1 (smul hw0 hw1 s t cs ct p)) =
      stateValue hw0 hw1
        (BF4WilsonAllNomeComplexTimeSector.smul hw0 hw1 s t cs ct (input hw0 hw1 p)) := rfl

theorem smul_output (s t : CReal) (cs : QCauchy s.approx) (ct : QCauchy t.approx)
    (p : DomainPoint hw0 hw1 (width := width)) :
    stateValue hw0 hw1 (output hw0 hw1 (smul hw0 hw1 s t cs ct p)) =
      stateValue hw0 hw1
        (BF4WilsonAllNomeComplexTimeSector.smul hw0 hw1 s t cs ct (output hw0 hw1 p)) := rfl

/-- The zero test is an actual represented graph point. -/
def zeroDomain : BF4WilsonAllNomeSectorDerivative.DomainPoint hw0 hw1 (width := width) where
  input := BF4WilsonAllNomeTimeSector.zero hw0 hw1
  output := BF4WilsonAllNomeTimeSector.zero hw0 hw1
  equation := by
    change A Z = T 1 Z
    rw [BF4WilsonAllNomeDerivativeCore.derivativeAction_zero,
      BF4WilsonAllNomeBilinearTime.completedTime_zero_element]

private theorem rc_add_zero (a : RC) : RCadd a RCzero = a := by
  refine Quotient.inductionOn a ?_
  exact fun X => Quotient.sound
    (SumOfSquares.Equiv_of_approx_eqv (fun n => QPoly.q_add_zero_eqv (X.approx n)))

private theorem rc_zero_add (a : RC) : RCadd RCzero a = a := by
  refine Quotient.inductionOn a ?_
  exact fun X => Quotient.sound
    (SumOfSquares.Equiv_of_approx_eqv (fun n => QPoly.q_zero_add_eqv (X.approx n)))

/-- Complex adjoint tests use the existing ambient complex pairing, but only
against the concretely represented complex derivative domain. -/
def AdjointPair (u v : State hw0 hw1 (width := width)) : Prop :=
  ∀ p : DomainPoint hw0 hw1 (width := width),
    I (stateValue hw0 hw1 u) (stateValue hw0 hw1 (output hw0 hw1 p)) =
      I (stateValue hw0 hw1 v) (stateValue hw0 hw1 (input hw0 hw1 p))

/-- The real component of tests `(q,0)` and `(0,q)` recovers both actual
real adjoint laws. No choice of representatives or complex spectrum enters. -/
theorem adjoint_components (u v : State hw0 hw1 (width := width))
    (h : AdjointPair hw0 hw1 u v) :
    BF4WilsonAllNomeSectorDerivative.AdjointPair hw0 hw1 u.1 v.1 ∧
      BF4WilsonAllNomeSectorDerivative.AdjointPair hw0 hw1 u.2 v.2 := by
  constructor
  · intro q
    have hq := congrArg Prod.fst (h (q,zeroDomain hw0 hw1))
    change RCadd (B u.1.val q.output.val) (B u.2.val Z) =
      RCadd (B v.1.val q.input.val) (B v.2.val Z) at hq
    rw [completedInner_zero_right,completedInner_zero_right,rc_add_zero,rc_add_zero] at hq
    exact hq
  · intro q
    have hq := congrArg Prod.fst (h (zeroDomain hw0 hw1,q))
    change RCadd (B u.1.val Z) (B u.2.val q.output.val) =
      RCadd (B v.1.val Z) (B v.2.val q.input.val) at hq
    rw [completedInner_zero_right,completedInner_zero_right,rc_zero_add,rc_zero_add] at hq
    exact hq

theorem components_adjoint (u v : State hw0 hw1 (width := width))
    (h₁ : BF4WilsonAllNomeSectorDerivative.AdjointPair hw0 hw1 u.1 v.1)
    (h₂ : BF4WilsonAllNomeSectorDerivative.AdjointPair hw0 hw1 u.2 v.2) :
    AdjointPair hw0 hw1 u v := by
  intro p
  apply Prod.ext
  · change RCadd (B u.1.val p.1.output.val) (B u.2.val p.2.output.val) =
      RCadd (B v.1.val p.1.input.val) (B v.2.val p.2.input.val)
    rw [h₁ p.1,h₂ p.2]
  · change RCsub (B u.1.val p.2.output.val) (B u.2.val p.1.output.val) =
      RCsub (B v.1.val p.2.input.val) (B v.2.val p.1.input.val)
    rw [h₁ p.2,h₂ p.1]

/-- Complex graph equality with its intrinsic adjoint is exactly the two
checked real graph equalities, on the same witnessed carrier. -/
theorem equation_iff_adjoint (u v : State hw0 hw1 (width := width)) :
    (A u.1.val = T 1 v.1.val ∧ A u.2.val = T 1 v.2.val) ↔
      AdjointPair hw0 hw1 u v := by
  constructor
  · intro h
    exact components_adjoint hw0 hw1 u v
      ((BF4WilsonAllNomeSectorDerivative.equation_iff_adjoint hw0 hw1 u.1 v.1).mp h.1)
      ((BF4WilsonAllNomeSectorDerivative.equation_iff_adjoint hw0 hw1 u.2 v.2).mp h.2)
  · intro h
    obtain ⟨h₁,h₂⟩ := adjoint_components hw0 hw1 u v h
    exact ⟨(BF4WilsonAllNomeSectorDerivative.equation_iff_adjoint hw0 hw1 u.1 v.1).mpr h₁,
      (BF4WilsonAllNomeSectorDerivative.equation_iff_adjoint hw0 hw1 u.2 v.2).mpr h₂⟩

def ofAdjoint (u v : State hw0 hw1 (width := width))
    (h : AdjointPair hw0 hw1 u v) : DomainPoint hw0 hw1 (width := width) := by
  obtain ⟨h₁,h₂⟩ := adjoint_components hw0 hw1 u v h
  exact (BF4WilsonAllNomeSectorDerivative.ofAdjoint hw0 hw1 u.1 v.1 h₁,
    BF4WilsonAllNomeSectorDerivative.ofAdjoint hw0 hw1 u.2 v.2 h₂)

theorem domain_adjoint (p : DomainPoint hw0 hw1 (width := width)) :
    AdjointPair hw0 hw1 (input hw0 hw1 p) (output hw0 hw1 p) :=
  components_adjoint hw0 hw1 _ _
    (BF4WilsonAllNomeSectorDerivative.domain_adjoint hw0 hw1 p.1)
    (BF4WilsonAllNomeSectorDerivative.domain_adjoint hw0 hw1 p.2)

/-- Every complex sector state has a computed pair of core approximants;
the component moduli are combined without a representative choice. -/
def coreDensityCertificate (x : State hw0 hw1 (width := width)) :
    Σ' points : Nat → DomainPoint hw0 hw1 (width := width), Σ' modulus : Q' → Nat,
      ∀ e : Q', (0 : Q') < e → ∀ n, modulus e ≤ n →
        RCle
          (BF4WilsonAllNomeComplexTimeSector.distance hw0 hw1
            (input hw0 hw1 (points n)) x)
          (Quotient.mk crealSetoid (ofQ' e)) := by
  let points n :=
    (BF4WilsonAllNomeSectorDerivative.coreApproximation hw0 hw1 x.1 n,
      BF4WilsonAllNomeSectorDerivative.coreApproximation hw0 hw1 x.2 n)
  let modulus (e : Q') := max (x.1.range.modulus (HalfPow.half*e))
    (x.2.range.modulus (HalfPow.half*e))
  refine ⟨points,modulus,?_⟩
  intro e he n hn
  have hh : (0 : Q') < HalfPow.half*e := ExpNeg.half_mul_pos _ he
  have h₁ := BF4WilsonAllNomeSectorDerivative.coreApproximation_bound hw0 hw1 x.1
    (HalfPow.half*e) hh n (Nat.le_trans (Nat.le_max_left _ _) hn)
  have h₂ := BF4WilsonAllNomeSectorDerivative.coreApproximation_bound hw0 hw1 x.2
    (HalfPow.half*e) hh n (Nat.le_trans (Nat.le_max_right _ _) hn)
  have h := RCadd_le_add h₁ h₂
  have hp : RCadd (Quotient.mk crealSetoid (ofQ' (HalfPow.half*e)))
      (Quotient.mk crealSetoid (ofQ' (HalfPow.half*e))) =
      Quotient.mk crealSetoid (ofQ' e) :=
    Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun _ => ExpNeg.two_halves e))
  simpa only [points,input,BF4WilsonAllNomeComplexTimeSector.distance,hp] using h

/-- Positivity is the sum of the two original nonnegative domain forms. -/
theorem domain_nonnegative (p : DomainPoint hw0 hw1 (width := width)) :
    RCnonneg (I (stateValue hw0 hw1 (input hw0 hw1 p))
      (stateValue hw0 hw1 (output hw0 hw1 p))).1 := by
  have h := RCadd_le_add
    (BF4WilsonAllNomeSectorDerivative.domain_nonnegative hw0 hw1 p.1)
    (BF4WilsonAllNomeSectorDerivative.domain_nonnegative hw0 hw1 p.2)
  rw [rc_add_zero] at h
  exact h

/-- The strict ORIGINAL fixed-nome/width form margin survives complexification.
This uses the same vacuum as the pre-existing complex transfer. -/
theorem domain_form_gap (p : DomainPoint hw0 hw1 (width := width))
    (h : I (BF4WilsonAllNomeComplexGap.complexUnit hw0 hw1 width)
      (stateValue hw0 hw1 (input hw0 hw1 p)) = (RCzero,RCzero)) :
    RCle (RCscale (BF4WilsonAllNomeLogCoreGap.coreMargin hw0 hw1 width)
      (I (stateValue hw0 hw1 (input hw0 hw1 p)) (stateValue hw0 hw1 (input hw0 hw1 p))).1)
      (I (stateValue hw0 hw1 (input hw0 hw1 p)) (stateValue hw0 hw1 (output hw0 hw1 p))).1 := by
  obtain ⟨hr,hi⟩ := (BF4WilsonAllNomeComplexGap.complex_orthogonal_iff hw0 hw1 width _).mp h
  have h1 : B (unitState hw0 hw1 width) p.1.input.val = RCzero :=
    (completedInner_symm hw0 hw1 _ _).trans hr
  have h2 : B (unitState hw0 hw1 width) p.2.input.val = RCzero :=
    (completedInner_symm hw0 hw1 _ _).trans hi
  have hs := RCadd_le_add (BF4WilsonAllNomeSectorDerivative.domain_form_gap hw0 hw1 p.1 h1)
    (BF4WilsonAllNomeSectorDerivative.domain_form_gap hw0 hw1 p.2 h2)
  rw [← RCscale_RCadd] at hs
  exact hs

/-- Graph limits retain BOTH original complex sector witnesses. -/
def closedLimit (inputs outputs : BF4WilsonAllNomeComplexTimeSector.CauchySequence hw0 hw1 (width := width))
    (equations : ∀ n, A (inputs.seq n).1.val = T 1 (outputs.seq n).1.val ∧
      A (inputs.seq n).2.val = T 1 (outputs.seq n).2.val) :
    DomainPoint hw0 hw1 (width := width) :=
  (BF4WilsonAllNomeSectorDerivative.closedLimit hw0 hw1
    (BF4WilsonAllNomeComplexTimeSector.realSequence hw0 hw1 inputs)
    (BF4WilsonAllNomeComplexTimeSector.realSequence hw0 hw1 outputs) (fun n => (equations n).1),
   BF4WilsonAllNomeSectorDerivative.closedLimit hw0 hw1
    (BF4WilsonAllNomeComplexTimeSector.imagSequence hw0 hw1 inputs)
    (BF4WilsonAllNomeComplexTimeSector.imagSequence hw0 hw1 outputs) (fun n => (equations n).2))

theorem closedLimit_input (inputs outputs : BF4WilsonAllNomeComplexTimeSector.CauchySequence hw0 hw1 (width := width))
    (equations : ∀ n, A (inputs.seq n).1.val = T 1 (outputs.seq n).1.val ∧
      A (inputs.seq n).2.val = T 1 (outputs.seq n).2.val) :
    stateValue hw0 hw1 (input hw0 hw1 (closedLimit hw0 hw1 inputs outputs equations)) =
      stateValue hw0 hw1 (BF4WilsonAllNomeComplexTimeSector.limit hw0 hw1 inputs) := rfl

theorem closedLimit_output (inputs outputs : BF4WilsonAllNomeComplexTimeSector.CauchySequence hw0 hw1 (width := width))
    (equations : ∀ n, A (inputs.seq n).1.val = T 1 (outputs.seq n).1.val ∧
      A (inputs.seq n).2.val = T 1 (outputs.seq n).2.val) :
    stateValue hw0 hw1 (output hw0 hw1 (closedLimit hw0 hw1 inputs outputs equations)) =
      stateValue hw0 hw1 (BF4WilsonAllNomeComplexTimeSector.limit hw0 hw1 outputs) := rfl

/-- Original complex Taylor remainder: input minus its ACTUAL time image
minus time times the actual domain output. -/
def remainder (t : PositiveRealDyadicTimeData.PositiveTime)
    (p : DomainPoint hw0 hw1 (width := width)) : ComplexCarrier hw0 hw1 width :=
  (BF4WilsonAllNomeDerivativeGraphReal.realRemainder hw0 hw1 t p.1.input.val p.1.output.val,
   BF4WilsonAllNomeDerivativeGraphReal.realRemainder hw0 hw1 t p.2.input.val p.2.output.val)

theorem remainder_pin (t : PositiveRealDyadicTimeData.PositiveTime)
    (p : DomainPoint hw0 hw1 (width := width)) :
    remainder hw0 hw1 t p =
      (completedSub hw0 hw1 (completedSub hw0 hw1 p.1.input.val
        (stateValue hw0 hw1 (BF4WilsonAllNomeComplexTimeSector.action hw0 hw1 t (input hw0 hw1 p))).1)
        (BF4WilsonAllNomeCompletedRealScalar.completedRealSmul hw0 hw1 t.real t.cauchy p.1.output.val),
       completedSub hw0 hw1 (completedSub hw0 hw1 p.2.input.val
        (stateValue hw0 hw1 (BF4WilsonAllNomeComplexTimeSector.action hw0 hw1 t (input hw0 hw1 p))).2)
        (BF4WilsonAllNomeCompletedRealScalar.completedRealSmul hw0 hw1 t.real t.cauchy p.2.output.val)) := by
  simp only [remainder,BF4WilsonAllNomeDerivativeGraphReal.realRemainder,
    BF4WilsonAllNomePositiveTimePins.realTimeAction_pin]
  rfl

private theorem half_product_budget (a : RC) (e : Q') :
    RCadd (RCmul a (rat (HalfPow.half*e))) (RCmul a (rat (HalfPow.half*e))) =
      RCmul a (rat e) := by
  refine Quotient.inductionOn a ?_
  intro X
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_add_eqv _ _ _))
      (Q'.mul_eqv_congr_left (X.approx n) _ _ (ExpNeg.two_halves e))))

/-- EVERY domain point is the derivative of the same complex real-time
action, with an explicitly returned radius in ORIGINAL lattice time units. -/
def realTaylorCertificate (p : DomainPoint hw0 hw1 (width := width))
    (e : Q') (he : (0 : Q') < e) :
    Σ' r : Q', ((0 : Q') < r) ×'
      (∀ t : PositiveRealDyadicTimeData.PositiveTime,
        RCle (BF4ExactSlabThermodynamicPositiveTimePins.realValue
          (BF4ExactSlabThermodynamicPositiveTimePins.timeValue t)) (rat r) →
        RCle (I (remainder hw0 hw1 t p) (remainder hw0 hw1 t p)).1
          (RCmul
            (RCmul (BF4ExactSlabThermodynamicPositiveTimePins.realValue
              (BF4ExactSlabThermodynamicPositiveTimePins.timeValue t))
              (BF4ExactSlabThermodynamicPositiveTimePins.realValue
                (BF4ExactSlabThermodynamicPositiveTimePins.timeValue t))) (rat e))) := by
  let realData := BF4WilsonAllNomeSectorDerivative.realTaylorCertificate hw0 hw1 p.1
    (HalfPow.half*e) (ExpNeg.half_mul_pos _ he)
  let imagData := BF4WilsonAllNomeSectorDerivative.realTaylorCertificate hw0 hw1 p.2
    (HalfPow.half*e) (ExpNeg.half_mul_pos _ he)
  refine ⟨Q'.min' realData.1 imagData.1,?_,?_⟩
  · unfold Q'.min'
    split
    · exact realData.2.1
    · exact imagData.2.1
  · intro t ht
    have h1 := realData.2.2 t (RCle_trans ht
      (leEv_le_ofQ'_of_approx_le (fun _ => Q'.min_le_left' _ _)))
    have h2 := imagData.2.2 t (RCle_trans ht
      (leEv_le_ofQ'_of_approx_le (fun _ => Q'.min_le_right' _ _)))
    have h := RCadd_le_add h1 h2
    rw [half_product_budget] at h
    exact h

#print axioms stateValue
#print axioms input
#print axioms output
#print axioms output_congr
#print axioms add
#print axioms realSmul
#print axioms negateReal
#print axioms smul
#print axioms smul_input
#print axioms smul_output
#print axioms zeroDomain
#print axioms AdjointPair
#print axioms adjoint_components
#print axioms components_adjoint
#print axioms equation_iff_adjoint
#print axioms ofAdjoint
#print axioms domain_adjoint
#print axioms coreDensityCertificate
#print axioms domain_nonnegative
#print axioms domain_form_gap
#print axioms closedLimit
#print axioms closedLimit_input
#print axioms closedLimit_output
#print axioms remainder_pin
#print axioms realTaylorCertificate

end YMGap.Continuum.BF4WilsonAllNomeComplexSectorDerivative
