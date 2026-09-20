/-
# Composition and adjoint closure of the original chronological operators

The finite program syntax computes products and adjoints of the SAME bounded
operators. Equality means agreement on EVERY completed input, not agreement
on the vacuum. This relation is preserved by composition and adjoint reversal;
the resulting involution and product laws are proved on the actual carrier.

The existing completed pairing supplies real linearity for scalars with
explicit Cauchy data. The reversed program retains the original rational
squared cap, and vacuum moments of p* q are the already constructed mixed
Wilson matrix elements. No observable quotient is assumed to be an operator
quotient. Equality on all finite vacuum-generated program inputs is sufficient:
the existing modulus-bearing stage density and adjoint balance prove this,
without a common support bound or quotient-representative selection.
This is fixed-spacing, guarded SU(2) operator algebra, not a full
local observable net, canonical continuum OS reconstruction, or a Clay claim.
-/
import YMGap.Continuum.BF4WilsonChronologicalCompositionSyntax
import YMGap.Continuum.BF4WilsonSpatialUnionCompletedRealScalar

namespace YMGap.Continuum.BF4WilsonChronologicalOperatorAlgebra

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonChronologicalProgram
open YMGap.Continuum.BF4WilsonChronologicalOperator
open YMGap.Continuum.BF4WilsonChronologicalCompositionSyntax
open YMGap.Continuum.BF4WilsonWindowRealization (stageProgram stageProgram_pin)
open YMGap.Continuum.BF4WilsonSpatialUnionSeminorm
open YMGap.Continuum.BF4WilsonSpatialUnionPairingData
open YMGap.Continuum.BF4WilsonSpatialUnionBilinear
open YMGap.Continuum.BF4WilsonSpatialUnionCompletedRealScalar
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)

local notation "V" => UnionCompletion hw0 hw1 hsmall hd hs
local notation "B" => completedInner hw0 hw1 hsmall hd hs
local notation "Op" => act hw0 hw1 hsmall hd hs
local notation "Adj" => adjointAct hw0 hw1 hsmall hd hs
local notation "U" => completedUnit hw0 hw1 hsmall hd hs

theorem act_compose {base : Nat} (p q : Program base) (x : V) :
    Op (compose p q) x = Op p (Op q x) := by
  induction p <;> simp only [compose, act, *]

/-- The finite reversed code realizes the already proved adjoint action. -/
theorem act_dagger {base : Nat} (p : Program base) (x : V) :
    Op (dagger p) x = Adj p x := by
  induction p generalizing x <;> simp only [dagger, act_compose, act, adjointAct, *]

/-- Full witnessed real linearity, not only the rational coefficient action. -/
theorem act_realSmul {base : Nat} (p : Program base)
    (s : CReal) (cs : QCauchy s.approx) (x : V) :
    Op p (completedRealSmul hw0 hw1 hsmall hd hs s cs x) =
      completedRealSmul hw0 hw1 hsmall hd hs s cs (Op p x) := by
  apply completed_eq_of_pairings hw0 hw1 hsmall hd hs
  intro test
  simp only [adjoint_balance, completedInner_realSmul_left]

theorem adjoint_realSmul {base : Nat} (p : Program base)
    (s : CReal) (cs : QCauchy s.approx) (x : V) :
    Adj p (completedRealSmul hw0 hw1 hsmall hd hs s cs x) =
      completedRealSmul hw0 hw1 hsmall hd hs s cs (Adj p x) := by
  simp only [← act_dagger, act_realSmul]

private theorem adjoint_balance_reverse {base : Nat} (p : Program base) (x y : V) :
    B (Adj p x) y = B x (Op p y) := by
  rw [completedInner_symm hw0 hw1 hsmall hd hs (Adj p x) y,
    ← adjoint_balance, completedInner_symm]

/-- This is operator equality, deliberately stronger than equality on U. -/
def OperatorEq {base : Nat} (p q : Program base) : Prop := ∀ x : V, Op p x = Op q x

/-- The actual finite program vectors separate arbitrary completion elements;
every original stage is compiled at its OWN spatial base and time radius. -/
theorem completed_eq_of_program_pairings (x y : V)
    (h : ∀ {base : Nat} (p : Program base),
      B x (evaluate hw0 hw1 hsmall hd hs p) = B y (evaluate hw0 hw1 hsmall hd hs p)) : x = y := by
  apply completed_eq_of_pairings hw0 hw1 hsmall hd hs
  intro z
  revert h
  refine Quotient.inductionOn₃ x y z ?_
  intro X Y Z h
  apply Quotient.sound
  apply CRealSeminormPairingCompletion.representativeInner_eq_of_right_stage_pairings
    (pairingData hw0 hw1 hsmall hd hs) X Y Z
  intro stage
  have hp := h (stageProgram stage)
  rw [stageProgram_pin] at hp
  exact Quotient.exact hp

/-- All finite vacuum-generated test inputs suffice for an operator identity.
A SINGLE common vacuum output does not suffice; see the concrete counterexample. -/
theorem operatorEq_of_program_inputs {base : Nat} (p q : Program base)
    (h : ∀ {testBase : Nat} (r : Program testBase),
      Op p (evaluate hw0 hw1 hsmall hd hs r) = Op q (evaluate hw0 hw1 hsmall hd hs r)) :
    OperatorEq hw0 hw1 hsmall hd hs p q := by
  have hadj (test : V) : Adj p test = Adj q test := by
    apply completed_eq_of_program_pairings hw0 hw1 hsmall hd hs
    intro testBase r
    rw [adjoint_balance_reverse, adjoint_balance_reverse, h r]
  intro x
  apply completed_eq_of_pairings hw0 hw1 hsmall hd hs
  intro test
  rw [adjoint_balance, adjoint_balance, hadj test]

theorem operatorEq_iff_program_inputs {base : Nat} (p q : Program base) :
    OperatorEq hw0 hw1 hsmall hd hs p q ↔
      (∀ {testBase : Nat} (r : Program testBase),
        Op p (evaluate hw0 hw1 hsmall hd hs r) = Op q (evaluate hw0 hw1 hsmall hd hs r)) :=
  ⟨fun h _ r => h (evaluate hw0 hw1 hsmall hd hs r),
    operatorEq_of_program_inputs hw0 hw1 hsmall hd hs p q⟩

theorem operatorEq_compose {base : Nat} {p p' q q' : Program base}
    (hp : OperatorEq hw0 hw1 hsmall hd hs p p')
    (hq : OperatorEq hw0 hw1 hsmall hd hs q q') :
    OperatorEq hw0 hw1 hsmall hd hs (compose p q) (compose p' q') := by
  intro x
  rw [act_compose, act_compose, hq x, hp]

theorem operatorEq_dagger {base : Nat} {p q : Program base}
    (h : OperatorEq hw0 hw1 hsmall hd hs p q) :
    OperatorEq hw0 hw1 hsmall hd hs (dagger p) (dagger q) := by
  intro x
  apply completed_eq_of_pairings hw0 hw1 hsmall hd hs
  intro test
  simp only [act_dagger, adjoint_balance_reverse, h test]

theorem compose_associative {base : Nat} (p q r : Program base) :
    OperatorEq hw0 hw1 hsmall hd hs (compose (compose p q) r) (compose p (compose q r)) := by
  intro x
  simp only [act_compose]

theorem compose_unit {base : Nat} (p : Program base) :
    OperatorEq hw0 hw1 hsmall hd hs (compose .vacuum p) p ∧
      OperatorEq hw0 hw1 hsmall hd hs (compose p .vacuum) p := by
  constructor <;> intro x <;> simp only [act_compose, act]

theorem dagger_involutive {base : Nat} (p : Program base) :
    OperatorEq hw0 hw1 hsmall hd hs (dagger (dagger p)) p := by
  intro x
  apply completed_eq_of_pairings hw0 hw1 hsmall hd hs
  intro test
  rw [act_dagger, adjoint_balance_reverse, act_dagger, ← adjoint_balance]

theorem dagger_compose {base : Nat} (p q : Program base) :
    OperatorEq hw0 hw1 hsmall hd hs (dagger (compose p q)) (compose (dagger q) (dagger p)) := by
  intro x
  apply completed_eq_of_pairings hw0 hw1 hsmall hd hs
  intro test
  calc
    B (Op (dagger (compose p q)) x) test = B x (Op (compose p q) test) := by
      rw [act_dagger, adjoint_balance_reverse]
    _ = B x (Op p (Op q test)) := by rw [act_compose]
    _ = B (Adj p x) (Op q test) := (adjoint_balance_reverse hw0 hw1 hsmall hd hs p x _).symm
    _ = B (Adj q (Adj p x)) test := (adjoint_balance_reverse hw0 hw1 hsmall hd hs q _ _).symm
    _ = B (Op (compose (dagger q) (dagger p)) x) test := by rw [act_compose, act_dagger, act_dagger]

private theorem scale_eq_of_eqv {a b : Q'} (h : Q'.eqv a b) (x : RC) :
    RCscale a x = RCscale b x := by
  refine Quotient.inductionOn x ?_
  intro X
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.mul_eqv_congr_right _ _ _ h))

/-- The original cap is also a bound for the reversed operator, on all inputs. -/
theorem adjoint_norm_bound {base : Nat} (p : Program base) (x : V) :
    RCle (B (Adj p x) (Adj p x)) (RCscale (squaredCap p) (B x x)) := by
  have h := act_norm_bound hw0 hw1 hsmall hd hs (dagger p) x
  rw [act_dagger, scale_eq_of_eqv (squaredCap_dagger p)] at h
  exact h

/-- Actual mixed Wilson vectors become vacuum matrix elements of an actual product. -/
theorem mixed_vacuum_product {base : Nat} (p q : Program base) :
    B (evaluate hw0 hw1 hsmall hd hs p) (evaluate hw0 hw1 hsmall hd hs q) =
      B U (Op (compose (dagger p) q) U) := by
  rw [act_compose, act_dagger, ← adjoint_balance, act_unit, act_unit]

theorem vacuum_star_square_nonnegative {base : Nat} (p : Program base) :
    RCnonneg (B U (Op (compose (dagger p) p) U)) := by
  rw [← mixed_vacuum_product]
  exact completedInner_nonnegative hw0 hw1 hsmall hd hs _

end YMGap.Continuum.BF4WilsonChronologicalOperatorAlgebra

#print axioms YMGap.Continuum.BF4WilsonChronologicalOperatorAlgebra.act_compose
#print axioms YMGap.Continuum.BF4WilsonChronologicalOperatorAlgebra.act_dagger
#print axioms YMGap.Continuum.BF4WilsonChronologicalOperatorAlgebra.act_realSmul
#print axioms YMGap.Continuum.BF4WilsonChronologicalOperatorAlgebra.adjoint_realSmul
#print axioms YMGap.Continuum.BF4WilsonChronologicalOperatorAlgebra.OperatorEq
#print axioms YMGap.Continuum.BF4WilsonChronologicalOperatorAlgebra.completed_eq_of_program_pairings
#print axioms YMGap.Continuum.BF4WilsonChronologicalOperatorAlgebra.operatorEq_of_program_inputs
#print axioms YMGap.Continuum.BF4WilsonChronologicalOperatorAlgebra.operatorEq_iff_program_inputs
#print axioms YMGap.Continuum.BF4WilsonChronologicalOperatorAlgebra.operatorEq_compose
#print axioms YMGap.Continuum.BF4WilsonChronologicalOperatorAlgebra.operatorEq_dagger
#print axioms YMGap.Continuum.BF4WilsonChronologicalOperatorAlgebra.compose_associative
#print axioms YMGap.Continuum.BF4WilsonChronologicalOperatorAlgebra.compose_unit
#print axioms YMGap.Continuum.BF4WilsonChronologicalOperatorAlgebra.dagger_involutive
#print axioms YMGap.Continuum.BF4WilsonChronologicalOperatorAlgebra.dagger_compose
#print axioms YMGap.Continuum.BF4WilsonChronologicalOperatorAlgebra.adjoint_norm_bound
#print axioms YMGap.Continuum.BF4WilsonChronologicalOperatorAlgebra.mixed_vacuum_product
#print axioms YMGap.Continuum.BF4WilsonChronologicalOperatorAlgebra.vacuum_star_square_nonnegative
