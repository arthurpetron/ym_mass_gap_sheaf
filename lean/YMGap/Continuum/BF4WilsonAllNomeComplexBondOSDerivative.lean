/-
# Actual complex derivative and intrinsic adjoint on physical bond classes

The domain is the pair of EXISTING real physical derivative-domain quotients.
Both its input and output lie in the existing complex BondCompletion; its
Hermitian tests retain all four original pairings. The actual resolvent-based
real reconstruction supplies a unique complex domain class for every intrinsic
adjoint pair, without selecting any quotient representatives.

Supplied original graph points and physical rows give Taylor radii and dense
domain approximants with explicit moduli. All statements are fixed nome/width
in original lattice time, not continuum QFT or physical mass calibration.
-/

import YMGap.Continuum.BF4WilsonAllNomeBondOSAdjoint
import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSTime
import YMGap.Continuum.BF4WilsonAllNomeComplexSectorDerivative

namespace YMGap.Continuum.BF4WilsonAllNomeComplexBondOSDerivative

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.PositiveRealDyadicTimeData (PositiveTime)
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimePins (timeValue realValue)
open YMGap.Continuum.BF4WilsonAllNomeBondOSCompletion
  (BondCompletion bondCompletedInner)
open YMGap.Continuum.BF4WilsonAllNomeBondOSTime
  (bondValue bondValue_injective bondValue_inner)
open YMGap.Continuum.BF4WilsonAllNomeBondOSLinear (bondValue_zero)
open YMGap.Continuum.BF4WilsonAllNomeBondOSDerivative
  (bondValue_input_mk bondValue_output_mk)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSCompletion
  (ComplexBondCompletion Rows value inner inner_value distance distance_value
    ofRows value_ofRows rowState)
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime (completedInner_zero_right)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "H" => ComplexBondCompletion hw0 hw1 (width := width)
local notation "RH" => BondCompletion hw0 hw1 (width := width)
local notation "RD" => BF4WilsonAllNomeBondOSDerivative.Domain hw0 hw1 (width := width)
local notation "RIn" => BF4WilsonAllNomeBondOSDerivative.input hw0 hw1
local notation "ROut" => BF4WilsonAllNomeBondOSDerivative.output hw0 hw1
local notation "B" => bondCompletedInner hw0 hw1
local notation "I" => inner hw0 hw1
local notation "RAdj" => BF4WilsonAllNomeBondOSAdjoint.AdjointPair hw0 hw1
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)

/-- Two actual real physical-domain classes, not a supplied abstract graph. -/
abbrev Domain := RD × RD

abbrev Point := BF4WilsonAllNomeComplexSectorDerivative.DomainPoint hw0 hw1 (width := width)

def input (d : Domain hw0 hw1 (width := width)) : H := (RIn d.1,RIn d.2)

def output (d : Domain hw0 hw1 (width := width)) : H := (ROut d.1,ROut d.2)

def ofPoint (p : Point hw0 hw1 (width := width)) : Domain hw0 hw1 (width := width) :=
  (Quotient.mk (BF4WilsonAllNomeSectorDerivative.domainSetoid hw0 hw1) p.1,
   Quotient.mk (BF4WilsonAllNomeSectorDerivative.domainSetoid hw0 hw1) p.2)

theorem value_input_ofPoint (p : Point hw0 hw1 (width := width)) :
    value hw0 hw1 (input hw0 hw1 (ofPoint hw0 hw1 p)) =
      BF4WilsonAllNomeComplexSectorDerivative.stateValue hw0 hw1
        (BF4WilsonAllNomeComplexSectorDerivative.input hw0 hw1 p) := by
  apply Prod.ext <;> exact bondValue_input_mk hw0 hw1 _

theorem value_output_ofPoint (p : Point hw0 hw1 (width := width)) :
    value hw0 hw1 (output hw0 hw1 (ofPoint hw0 hw1 p)) =
      BF4WilsonAllNomeComplexSectorDerivative.stateValue hw0 hw1
        (BF4WilsonAllNomeComplexSectorDerivative.output hw0 hw1 p) := by
  apply Prod.ext <;> exact bondValue_output_mk hw0 hw1 _

theorem input_injective {d e : Domain hw0 hw1 (width := width)}
    (h : input hw0 hw1 d = input hw0 hw1 e) : d = e :=
  Prod.ext
    (BF4WilsonAllNomeBondOSDerivative.input_injective hw0 hw1 (congrArg Prod.fst h))
    (BF4WilsonAllNomeBondOSDerivative.input_injective hw0 hw1 (congrArg Prod.snd h))

private def zeroRealDomain : RD :=
  Quotient.mk (BF4WilsonAllNomeSectorDerivative.domainSetoid hw0 hw1)
    (BF4WilsonAllNomeComplexSectorDerivative.zeroDomain hw0 hw1)

private theorem zeroReal_input :
    RIn (zeroRealDomain hw0 hw1 (width := width)) = BF4WilsonAllNomeBondOSLinear.zero hw0 hw1 := by
  apply bondValue_injective hw0 hw1
  unfold zeroRealDomain
  rw [bondValue_input_mk, bondValue_zero]
  rfl

private theorem zeroReal_output :
    ROut (zeroRealDomain hw0 hw1 (width := width)) = BF4WilsonAllNomeBondOSLinear.zero hw0 hw1 := by
  apply bondValue_injective hw0 hw1
  unfold zeroRealDomain
  rw [bondValue_output_mk, bondValue_zero]
  rfl

private theorem real_inner_zero_right (x : RH) :
    B x (BF4WilsonAllNomeBondOSLinear.zero hw0 hw1) = RCzero := by
  rw [bondValue_inner, bondValue_zero, completedInner_zero_right]

private theorem rc_add_zero (a : RC) : RCadd a RCzero = a := by
  refine Quotient.inductionOn a ?_
  exact fun X => Quotient.sound
    (SumOfSquares.Equiv_of_approx_eqv (fun n => QPoly.q_add_zero_eqv (X.approx n)))

private theorem rc_zero_add (a : RC) : RCadd RCzero a = a := by
  refine Quotient.inductionOn a ?_
  exact fun X => Quotient.sound
    (SumOfSquares.Equiv_of_approx_eqv (fun n => QPoly.q_zero_add_eqv (X.approx n)))

/-- Full Hermitian adjoint tests on EVERY completed physical complex class. -/
def AdjointPair (u v : H) : Prop :=
  ∀ d : Domain hw0 hw1 (width := width),
    I u (output hw0 hw1 d) = I v (input hw0 hw1 d)

theorem adjoint_components (u v : H) (h : AdjointPair hw0 hw1 u v) :
    RAdj u.1 v.1 ∧ RAdj u.2 v.2 := by
  constructor
  · intro d
    have hd := congrArg Prod.fst (h (d,zeroRealDomain hw0 hw1))
    change RCadd (B u.1 (ROut d)) (B u.2 (ROut (zeroRealDomain hw0 hw1))) =
      RCadd (B v.1 (RIn d)) (B v.2 (RIn (zeroRealDomain hw0 hw1))) at hd
    rw [zeroReal_output,zeroReal_input,real_inner_zero_right,real_inner_zero_right,
      rc_add_zero,rc_add_zero] at hd
    exact hd
  · intro d
    have hd := congrArg Prod.fst (h (zeroRealDomain hw0 hw1,d))
    change RCadd (B u.1 (ROut (zeroRealDomain hw0 hw1))) (B u.2 (ROut d)) =
      RCadd (B v.1 (RIn (zeroRealDomain hw0 hw1))) (B v.2 (RIn d)) at hd
    rw [zeroReal_output,zeroReal_input,real_inner_zero_right,real_inner_zero_right,
      rc_zero_add,rc_zero_add] at hd
    exact hd

/-- Both cross pairings in the imaginary part use the same real graph tests. -/
theorem components_adjoint (u v : H) (h₁ : RAdj u.1 v.1) (h₂ : RAdj u.2 v.2) :
    AdjointPair hw0 hw1 u v := by
  intro d
  apply Prod.ext
  · change RCadd (B u.1 (ROut d.1)) (B u.2 (ROut d.2)) =
      RCadd (B v.1 (RIn d.1)) (B v.2 (RIn d.2))
    rw [h₁ d.1,h₂ d.2]
  · change RCsub (B u.1 (ROut d.2)) (B u.2 (ROut d.1)) =
      RCsub (B v.1 (RIn d.2)) (B v.2 (RIn d.1))
    rw [h₁ d.2,h₂ d.1]

theorem domain_adjoint (d : Domain hw0 hw1 (width := width)) :
    AdjointPair hw0 hw1 (input hw0 hw1 d) (output hw0 hw1 d) :=
  components_adjoint hw0 hw1 _ _
    (BF4WilsonAllNomeBondOSAdjoint.domain_adjoint hw0 hw1 d.1)
    (BF4WilsonAllNomeBondOSAdjoint.domain_adjoint hw0 hw1 d.2)

/-- Both classes are computed by the ORIGINAL positive real resolvent. -/
def adjointDomain (u v : H) : Domain hw0 hw1 (width := width) :=
  (BF4WilsonAllNomeBondOSAdjoint.adjointDomain hw0 hw1 u.1 v.1,
   BF4WilsonAllNomeBondOSAdjoint.adjointDomain hw0 hw1 u.2 v.2)

theorem adjointDomain_input (u v : H) (h : AdjointPair hw0 hw1 u v) :
    input hw0 hw1 (adjointDomain hw0 hw1 u v) = u :=
  Prod.ext
    (BF4WilsonAllNomeBondOSAdjoint.adjointDomain_input hw0 hw1 u.1 v.1
      (adjoint_components hw0 hw1 u v h).1)
    (BF4WilsonAllNomeBondOSAdjoint.adjointDomain_input hw0 hw1 u.2 v.2
      (adjoint_components hw0 hw1 u v h).2)

theorem adjointDomain_output (u v : H) (h : AdjointPair hw0 hw1 u v) :
    output hw0 hw1 (adjointDomain hw0 hw1 u v) = v :=
  Prod.ext
    (BF4WilsonAllNomeBondOSAdjoint.adjointDomain_output hw0 hw1 u.1 v.1
      (adjoint_components hw0 hw1 u v h).1)
    (BF4WilsonAllNomeBondOSAdjoint.adjointDomain_output hw0 hw1 u.2 v.2
      (adjoint_components hw0 hw1 u v h).2)

/-- Type-valued graph reconstruction; no physical quotient representatives. -/
def ofAdjoint (u v : H) (h : AdjointPair hw0 hw1 u v) :
    Σ' d : Domain hw0 hw1 (width := width),
      (input hw0 hw1 d = u) ×' (output hw0 hw1 d = v) :=
  ⟨adjointDomain hw0 hw1 u v,
    adjointDomain_input hw0 hw1 u v h,adjointDomain_output hw0 hw1 u v h⟩

theorem adjointDomain_unique (u v : H) (h : AdjointPair hw0 hw1 u v)
    (d : Domain hw0 hw1 (width := width)) (hd : input hw0 hw1 d = u) :
    d = adjointDomain hw0 hw1 u v :=
  input_injective hw0 hw1 (hd.trans (adjointDomain_input hw0 hw1 u v h).symm)

private theorem add_adjoint (d e : Domain hw0 hw1 (width := width)) :
    AdjointPair hw0 hw1
      (BF4WilsonAllNomeComplexBondOSTime.add hw0 hw1 (input hw0 hw1 d) (input hw0 hw1 e))
      (BF4WilsonAllNomeComplexBondOSTime.add hw0 hw1 (output hw0 hw1 d) (output hw0 hw1 e)) := by
  intro p
  rw [BF4WilsonAllNomeComplexBondOSTime.inner_add_left,
    BF4WilsonAllNomeComplexBondOSTime.inner_add_left,
    domain_adjoint hw0 hw1 d p,domain_adjoint hw0 hw1 e p]

/-- Actual graph addition on arbitrary domain classes, with no representatives. -/
def add (d e : Domain hw0 hw1 (width := width)) : Domain hw0 hw1 (width := width) :=
  adjointDomain hw0 hw1
    (BF4WilsonAllNomeComplexBondOSTime.add hw0 hw1 (input hw0 hw1 d) (input hw0 hw1 e))
    (BF4WilsonAllNomeComplexBondOSTime.add hw0 hw1 (output hw0 hw1 d) (output hw0 hw1 e))

theorem add_input (d e : Domain hw0 hw1 (width := width)) :
    input hw0 hw1 (add hw0 hw1 d e) =
      BF4WilsonAllNomeComplexBondOSTime.add hw0 hw1 (input hw0 hw1 d) (input hw0 hw1 e) :=
  adjointDomain_input hw0 hw1 _ _ (add_adjoint hw0 hw1 d e)

theorem add_output (d e : Domain hw0 hw1 (width := width)) :
    output hw0 hw1 (add hw0 hw1 d e) =
      BF4WilsonAllNomeComplexBondOSTime.add hw0 hw1 (output hw0 hw1 d) (output hw0 hw1 e) :=
  adjointDomain_output hw0 hw1 _ _ (add_adjoint hw0 hw1 d e)

private theorem smul_adjoint (s t : CReal) (cs : QCauchy s.approx) (ct : QCauchy t.approx)
    (d : Domain hw0 hw1 (width := width)) :
    AdjointPair hw0 hw1
      (BF4WilsonAllNomeComplexBondOSTime.smul hw0 hw1 s t cs ct (input hw0 hw1 d))
      (BF4WilsonAllNomeComplexBondOSTime.smul hw0 hw1 s t cs ct (output hw0 hw1 d)) := by
  intro p
  rw [BF4WilsonAllNomeComplexBondOSTime.inner_smul_left,
    BF4WilsonAllNomeComplexBondOSTime.inner_smul_left,domain_adjoint hw0 hw1 d p]

/-- Constructive complex scaling retains both supplied real scalar moduli. -/
def smul (s t : CReal) (cs : QCauchy s.approx) (ct : QCauchy t.approx)
    (d : Domain hw0 hw1 (width := width)) : Domain hw0 hw1 (width := width) :=
  adjointDomain hw0 hw1
    (BF4WilsonAllNomeComplexBondOSTime.smul hw0 hw1 s t cs ct (input hw0 hw1 d))
    (BF4WilsonAllNomeComplexBondOSTime.smul hw0 hw1 s t cs ct (output hw0 hw1 d))

theorem smul_input (s t : CReal) (cs : QCauchy s.approx) (ct : QCauchy t.approx)
    (d : Domain hw0 hw1 (width := width)) :
    input hw0 hw1 (smul hw0 hw1 s t cs ct d) =
      BF4WilsonAllNomeComplexBondOSTime.smul hw0 hw1 s t cs ct (input hw0 hw1 d) :=
  adjointDomain_input hw0 hw1 _ _ (smul_adjoint hw0 hw1 s t cs ct d)

theorem smul_output (s t : CReal) (cs : QCauchy s.approx) (ct : QCauchy t.approx)
    (d : Domain hw0 hw1 (width := width)) :
    output hw0 hw1 (smul hw0 hw1 s t cs ct d) =
      BF4WilsonAllNomeComplexBondOSTime.smul hw0 hw1 s t cs ct (output hw0 hw1 d) :=
  adjointDomain_output hw0 hw1 _ _ (smul_adjoint hw0 hw1 s t cs ct d)

theorem nonnegative (d : Domain hw0 hw1 (width := width)) :
    RCnonneg (I (input hw0 hw1 d) (output hw0 hw1 d)).1 := by
  rcases d with ⟨d₁,d₂⟩
  refine Quotient.inductionOn₂ d₁ d₂ ?_
  intro p q
  change RCnonneg (I (input hw0 hw1 (ofPoint hw0 hw1 (p,q)))
    (output hw0 hw1 (ofPoint hw0 hw1 (p,q)))).1
  rw [inner_value,value_input_ofPoint,value_output_ofPoint]
  exact BF4WilsonAllNomeComplexSectorDerivative.domain_nonnegative hw0 hw1 (p,q)

/-- The original vacuum, with zero imaginary component. -/
def vacuum : H := (BF4WilsonAllNomeBondOSTime.vacuum hw0 hw1,
  BF4WilsonAllNomeBondOSLinear.zero hw0 hw1)

theorem value_vacuum : value hw0 hw1 (vacuum hw0 hw1 (width := width)) =
    BF4WilsonAllNomeComplexGap.complexUnit hw0 hw1 width := by
  apply Prod.ext
  · change bondValue hw0 hw1 (BF4WilsonAllNomeBondOSTime.vacuum hw0 hw1) = _
    rw [BF4WilsonAllNomeBondOSTime.vacuum,BF4WilsonAllNomeBondOSTime.bondValue_ofSource,
      BF4WilsonAllNomeBondOSRealization.image_unit]
    rfl
  · exact bondValue_zero hw0 hw1

/-- The SAME fixed-nome/width form margin, with full complex vacuum orthogonality. -/
theorem form_gap (d : Domain hw0 hw1 (width := width))
    (h : I (vacuum hw0 hw1) (input hw0 hw1 d) = (RCzero,RCzero)) :
    RCle (RCscale (BF4WilsonAllNomeLogCoreGap.coreMargin hw0 hw1 width)
      (I (input hw0 hw1 d) (input hw0 hw1 d)).1)
      (I (input hw0 hw1 d) (output hw0 hw1 d)).1 := by
  rcases d with ⟨d₁,d₂⟩
  revert h
  refine Quotient.inductionOn₂ d₁ d₂ ?_
  intro p q h
  change I (vacuum hw0 hw1) (input hw0 hw1 (ofPoint hw0 hw1 (p,q))) = (RCzero,RCzero) at h
  change RCle (RCscale (BF4WilsonAllNomeLogCoreGap.coreMargin hw0 hw1 width)
    (I (input hw0 hw1 (ofPoint hw0 hw1 (p,q)))
      (input hw0 hw1 (ofPoint hw0 hw1 (p,q)))).1)
    (I (input hw0 hw1 (ofPoint hw0 hw1 (p,q)))
      (output hw0 hw1 (ofPoint hw0 hw1 (p,q)))).1
  rw [inner_value,value_vacuum,value_input_ofPoint] at h
  rw [inner_value,inner_value,value_input_ofPoint,value_output_ofPoint]
  exact BF4WilsonAllNomeComplexSectorDerivative.domain_form_gap hw0 hw1 (p,q) h

theorem adjoint_form_gap (u v : H) (h : AdjointPair hw0 hw1 u v)
    (hu : I (vacuum hw0 hw1) u = (RCzero,RCzero)) :
    RCle (RCscale (BF4WilsonAllNomeLogCoreGap.coreMargin hw0 hw1 width) (I u u).1) (I u v).1 := by
  have hi := adjointDomain_input hw0 hw1 u v h
  have ho := adjointDomain_output hw0 hw1 u v h
  have hg := form_gap hw0 hw1 (adjointDomain hw0 hw1 u v) (by rw [hi]; exact hu)
  simpa only [hi,ho] using hg

/-- Supplied physical rows compute actual dense domain classes and a modulus. -/
def densityCertificate (X : Rows hw0 hw1 (width := width)) :
    Σ' points : Nat → Domain hw0 hw1 (width := width), Σ' modulus : Q' → Nat,
      ∀ e : Q', (0 : Q') < e → ∀ n, modulus e ≤ n →
        RCle (distance hw0 hw1 (input hw0 hw1 (points n)) (ofRows hw0 hw1 X)) (rat e) := by
  let C := BF4WilsonAllNomeComplexSectorDerivative.coreDensityCertificate hw0 hw1
    (rowState hw0 hw1 X)
  refine ⟨fun n => ofPoint hw0 hw1 (C.1 n),C.2.1,?_⟩
  intro e he n hn
  rw [distance_value,value_input_ofPoint,value_ofRows]
  exact C.2.2 e he n hn

/-- Actual complex bond remainder, retaining both original time actions. -/
def remainder (t : PositiveTime) (u v : H) : H :=
  (BF4WilsonAllNomeBondOSDerivative.bondRemainder hw0 hw1 t u.1 v.1,
   BF4WilsonAllNomeBondOSDerivative.bondRemainder hw0 hw1 t u.2 v.2)

theorem remainder_value (t : PositiveTime) (p : Point hw0 hw1 (width := width)) :
    value hw0 hw1 (remainder hw0 hw1 t (input hw0 hw1 (ofPoint hw0 hw1 p))
      (output hw0 hw1 (ofPoint hw0 hw1 p))) =
      BF4WilsonAllNomeComplexSectorDerivative.remainder hw0 hw1 t p := by
  apply Prod.ext
  · dsimp only [value,remainder,input,output,ofPoint]
    rw [BF4WilsonAllNomeBondOSDerivative.bondValue_remainder,
      bondValue_input_mk,bondValue_output_mk]
    rfl
  · dsimp only [value,remainder,input,output,ofPoint]
    rw [BF4WilsonAllNomeBondOSDerivative.bondValue_remainder,
      bondValue_input_mk,bondValue_output_mk]
    rfl

/-- Original graph points compute a radius for EVERY small positive real
increment, measured in the SAME physical complex bond norm and lattice time. -/
def realTaylorCertificate (p : Point hw0 hw1 (width := width))
    (e : Q') (he : (0 : Q') < e) :
    Σ' r : Q', ((0 : Q') < r) ×'
      (∀ t : PositiveTime, RCle (realValue (timeValue t)) (rat r) →
        RCle (I (remainder hw0 hw1 t (input hw0 hw1 (ofPoint hw0 hw1 p))
            (output hw0 hw1 (ofPoint hw0 hw1 p)))
          (remainder hw0 hw1 t (input hw0 hw1 (ofPoint hw0 hw1 p))
            (output hw0 hw1 (ofPoint hw0 hw1 p)))).1
          (RCmul (RCmul (realValue (timeValue t)) (realValue (timeValue t))) (rat e))) := by
  let C := BF4WilsonAllNomeComplexSectorDerivative.realTaylorCertificate hw0 hw1 p e he
  refine ⟨C.1,C.2.1,?_⟩
  intro t ht
  rw [inner_value,remainder_value]
  exact C.2.2 t ht

#print axioms input
#print axioms output
#print axioms ofPoint
#print axioms value_input_ofPoint
#print axioms value_output_ofPoint
#print axioms input_injective
#print axioms AdjointPair
#print axioms adjoint_components
#print axioms components_adjoint
#print axioms domain_adjoint
#print axioms adjointDomain
#print axioms adjointDomain_input
#print axioms adjointDomain_output
#print axioms ofAdjoint
#print axioms adjointDomain_unique
#print axioms add
#print axioms add_input
#print axioms add_output
#print axioms smul
#print axioms smul_input
#print axioms smul_output
#print axioms nonnegative
#print axioms vacuum
#print axioms value_vacuum
#print axioms form_gap
#print axioms adjoint_form_gap
#print axioms densityCertificate
#print axioms remainder
#print axioms remainder_value
#print axioms realTaylorCertificate

end YMGap.Continuum.BF4WilsonAllNomeComplexBondOSDerivative
