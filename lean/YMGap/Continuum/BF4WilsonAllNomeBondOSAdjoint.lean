/-
# Intrinsic adjoint graph on the original completed physical bond carrier

The already constructed positive resolvent gives an actual derivative-domain
class for every intrinsic adjoint pair: apply (I+A)^(-1) to u+v. Symmetry and
surjectivity identify its input and output without selecting representatives
of either quotient. This is the real, fixed-nome/width lattice-time graph;
it is not a continuum Hamiltonian or a physical scaling estimate.
-/

import YMGap.Continuum.BF4WilsonAllNomeBondOSResolvent

namespace YMGap.Continuum.BF4WilsonAllNomeBondOSAdjoint

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner (completedInner)
open YMGap.Continuum.BF4WilsonAllNomeLinear
  (completedAdd completedNeg completedSub)
open YMGap.Continuum.BF4WilsonAllNomeLinearLaws
  (completedAdd_assoc completedAdd_comm completedNeg_add completedZero_add
    completedSmul_one)
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
  (completedInner_add_left completedInner_add_right completedInner_zero_left)
open YMGap.Continuum.BF4WilsonAllNomeDistance (completedDist_zero_iff)
open YMGap.Continuum.BF4WilsonAllNomeBondOSCompletion
  (BondCompletion bondCompletedInner)
open YMGap.Continuum.BF4WilsonAllNomeBondOSTime
  (bondValue bondValue_injective bondValue_inner)
open YMGap.Continuum.BF4WilsonAllNomeBondOSLinear
  (bondValue_add bondValue_sub bondValue_smul)
open YMGap.Continuum.BF4WilsonAllNomeBondOSDerivative
  (Domain input output input_injective symmetric)
open YMGap.Continuum.BF4WilsonAllNomeBondOSResolvent
  (shifted resolventDomain inverse_right)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "H" => BondCompletion hw0 hw1 (width := width)
local notation "D" => Domain hw0 hw1 (width := width)
local notation "B" => bondCompletedInner hw0 hw1
local notation "BV" => completedInner hw0 hw1
local notation "value" => bondValue hw0 hw1
local notation "Add" => BF4WilsonAllNomeBondOSLinear.add hw0 hw1
local notation "Sub" => BF4WilsonAllNomeBondOSLinear.sub hw0 hw1
local notation "In" => input hw0 hw1
local notation "Out" => output hw0 hw1

private theorem inner_add_left (x y z : H) :
    B (Add x y) z = RCadd (B x z) (B y z) := by
  rw [bondValue_inner, bondValue_add, completedInner_add_left,
    bondValue_inner, bondValue_inner]

private theorem inner_add_right (x y z : H) :
    B x (Add y z) = RCadd (B x y) (B x z) := by
  rw [bondValue_inner, bondValue_add, completedInner_add_right,
    bondValue_inner, bondValue_inner]

/-- Intrinsic tests against EVERY actual physical derivative-domain class. -/
def AdjointPair (u v : H) : Prop :=
  ∀ d : D, B u (Out d) = B v (In d)

theorem domain_adjoint (d : D) : AdjointPair hw0 hw1 (In d) (Out d) :=
  fun e => (symmetric hw0 hw1 d e).symm

/-- The candidate is computed by the actual positive resolvent, independently
of the adjoint proof. No representative of u or v is chosen. -/
def adjointDomain (u v : H) : D :=
  resolventDomain hw0 hw1 1 (by decide) (Add u v)

private theorem shifted_one_value (d : D) :
    value (shifted hw0 hw1 1 d) = completedAdd hw0 hw1 (value (In d)) (value (Out d)) := by
  unfold shifted
  rw [bondValue_add, bondValue_smul, completedSmul_one]

private theorem shifted_one (d : D) :
    shifted hw0 hw1 1 d = Add (In d) (Out d) := by
  apply bondValue_injective hw0 hw1
  rw [shifted_one_value, bondValue_add]

private theorem adjoint_shifted_pairing (u v : H) (h : AdjointPair hw0 hw1 u v)
    (e : D) : B u (shifted hw0 hw1 1 e) = B (Add u v) (In e) := by
  rw [shifted_one, inner_add_right, h e, inner_add_left]

private theorem candidate_pairings (u v : H) (h : AdjointPair hw0 hw1 u v)
    (z : H) : B u z = B (In (adjointDomain hw0 hw1 u v)) z := by
  let d := adjointDomain hw0 hw1 u v
  let e := resolventDomain hw0 hw1 1 (by decide) z
  have he : shifted hw0 hw1 1 e = z := inverse_right hw0 hw1 1 (by decide) z
  have hd : shifted hw0 hw1 1 d = Add u v :=
    inverse_right hw0 hw1 1 (by decide) (Add u v)
  calc
    B u z = B (Add u v) (In e) := by rw [← he]; exact adjoint_shifted_pairing hw0 hw1 u v h e
    _ = B (shifted hw0 hw1 1 d) (In e) := by rw [hd]
    _ = B (In d) (shifted hw0 hw1 1 e) := by
      rw [shifted_one, shifted_one, inner_add_left, inner_add_right, symmetric hw0 hw1 d e]
    _ = B (In d) z := by rw [he]

/-- Adjoint tests identify the candidate's input by testing the actual
physical difference against itself; no test outside the bond carrier. -/
theorem adjointDomain_input (u v : H) (h : AdjointPair hw0 hw1 u v) :
    In (adjointDomain hw0 hw1 u v) = u := by
  let x := In (adjointDomain hw0 hw1 u v)
  let z := Sub u x
  have hp := candidate_pairings hw0 hw1 u v h z
  rw [bondValue_inner, bondValue_inner, bondValue_sub] at hp
  let U := value u
  let X := value x
  let Z := completedSub hw0 hw1 U X
  have hz : BV Z Z = RCzero := calc
    BV Z Z = RCadd (BV U Z) (BV (completedNeg hw0 hw1 X) Z) :=
      completedInner_add_left hw0 hw1 U (completedNeg hw0 hw1 X) Z
    _ = RCadd (BV X Z) (BV (completedNeg hw0 hw1 X) Z) := by rw [hp]
    _ = BV (completedAdd hw0 hw1 X (completedNeg hw0 hw1 X)) Z :=
      (completedInner_add_left hw0 hw1 X (completedNeg hw0 hw1 X) Z).symm
    _ = RCzero := by rw [completedAdd_comm, completedNeg_add, completedInner_zero_left]
  exact (bondValue_injective hw0 hw1 ((completedDist_zero_iff hw0 hw1 U X).mp hz)).symm

/-- The same shifted resolvent identity then identifies the actual output. -/
theorem adjointDomain_output (u v : H) (h : AdjointPair hw0 hw1 u v) :
    Out (adjointDomain hw0 hw1 u v) = v := by
  have hs := congrArg value (inverse_right hw0 hw1 1 (by decide) (Add u v))
  rw [shifted_one_value, bondValue_add] at hs
  change completedAdd hw0 hw1 (value (In (adjointDomain hw0 hw1 u v)))
    (value (Out (adjointDomain hw0 hw1 u v))) =
      completedAdd hw0 hw1 (value u) (value v) at hs
  rw [adjointDomain_input hw0 hw1 u v h] at hs
  have hc := congrArg (fun a => completedAdd hw0 hw1 (completedNeg hw0 hw1 (value u)) a) hs
  dsimp only at hc
  rw [← completedAdd_assoc, completedNeg_add, completedZero_add,
    ← completedAdd_assoc, completedNeg_add, completedZero_add] at hc
  exact bondValue_injective hw0 hw1 hc

/-- Type-valued intrinsic adjoint reconstruction on EVERY bond class. -/
def ofAdjoint (u v : H) (h : AdjointPair hw0 hw1 u v) :
    Σ' d : D, (In d = u) ×' (Out d = v) :=
  ⟨adjointDomain hw0 hw1 u v,
    adjointDomain_input hw0 hw1 u v h, adjointDomain_output hw0 hw1 u v h⟩

theorem adjointDomain_unique (u v : H) (h : AdjointPair hw0 hw1 u v)
    (d : D) (hd : In d = u) : d = adjointDomain hw0 hw1 u v :=
  input_injective hw0 hw1 (hd.trans (adjointDomain_input hw0 hw1 u v h).symm)

/-- The graph constructed from an adjoint pair retains the existing
fixed-parameter vacuum-complement form margin, with no new gap premise. -/
theorem adjoint_form_gap (u v : H) (h : AdjointPair hw0 hw1 u v)
    (hu : B (BF4WilsonAllNomeBondOSTime.vacuum hw0 hw1 (width := width)) u = RCzero) :
    RCle (RCscale (BF4WilsonAllNomeLogCoreGap.coreMargin hw0 hw1 width) (B u u)) (B u v) := by
  have hi := adjointDomain_input hw0 hw1 u v h
  have ho := adjointDomain_output hw0 hw1 u v h
  have hg := BF4WilsonAllNomeBondOSDerivative.form_gap hw0 hw1
    (adjointDomain hw0 hw1 u v) (by rw [hi]; exact hu)
  simpa only [hi, ho] using hg

#print axioms AdjointPair
#print axioms domain_adjoint
#print axioms adjointDomain
#print axioms adjointDomain_input
#print axioms adjointDomain_output
#print axioms ofAdjoint
#print axioms adjointDomain_unique
#print axioms adjoint_form_gap

end YMGap.Continuum.BF4WilsonAllNomeBondOSAdjoint
