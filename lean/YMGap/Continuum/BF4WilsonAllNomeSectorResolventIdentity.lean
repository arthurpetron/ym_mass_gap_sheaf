/-
# Resolvent parameter identity on the original witnessed sector

Two positive rational shifts of the SAME derivative satisfy the exact
resolvent difference identity, including equal parameters. This follows
from the already constructed two-sided inverse on its actual domain; no
commuting spectral model or full-carrier inverse is assumed.
-/

import YMGap.Continuum.BF4WilsonAllNomeSectorResolvent

namespace YMGap.Continuum.BF4WilsonAllNomeSectorResolventIdentity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomeCompletedPairingContinuity
open YMGap.Continuum.BF4WilsonAllNomeCompletedRealScalar (completed_eq_of_pairings)
open YMGap.Continuum.BF4WilsonAllNomeTimeSector (State)
open YMGap.Continuum.BF4WilsonAllNomeSectorDerivative (DomainPoint)
open YMGap.Continuum.BF4WilsonAllNomeSectorResolvent
open YMGap.Continuum.BF4WilsonAllNomeResolventLimit (resolvent)
open YMGap.Continuum.BF4WilsonAllNomeResolventEquation
  (resolvent_sub resolvent_smul)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "S" => completedSmul hw0 hw1
local notation "Sub" => completedSub hw0 hw1
local notation "R" => resolvent hw0 hw1
local notation "Sector" => State hw0 hw1 (width := width)
local notation "Point" => DomainPoint hw0 hw1 (width := width)

private theorem scalar_shift (lambda mu : Q') (a b : RC) :
    RCadd (RCscale lambda a) b =
      RCsub (RCadd (RCscale mu a) b) (RCscale (mu-lambda) a) := by
  refine Quotient.inductionOn₂ a b ?_
  intro A B'
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.var 2)) (.var 3))
      (.add (.add (.mul (.var 1) (.var 2)) (.var 3))
        (.neg (.mul (.add (.var 1) (.neg (.var 0))) (.var 2))))
      (by decide) (fun | 0 => lambda | 1 => mu | 2 => A.approx n | _ => B'.approx n)))

private theorem scalar_sub_switch (a b : RC) : RCsub a (RCsub a b) = b := by
  refine Quotient.inductionOn₂ a b ?_
  intro A B'
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.var 0) (.neg (.add (.var 0) (.neg (.var 1))))) (.var 1)
      (by decide) (fun | 0 => A.approx n | _ => B'.approx n)))

/-- Changing the shift does not change the derivative domain point. -/
theorem shifted_change (lambda mu : Q') (p : Point) :
    (shifted hw0 hw1 lambda p).val =
      Sub (shifted hw0 hw1 mu p).val (S (mu-lambda) p.input.val) := by
  apply completed_eq_of_pairings hw0 hw1
  intro y
  change B (completedAdd hw0 hw1 (S lambda p.input.val) p.output.val) y = _
  simp only [shifted, completedInner_sub_left, completedInner_add_left,
    completedInner_smul_left]
  exact scalar_shift lambda mu _ _

/-- The actual original resolvents obey the parameter identity without
dividing by their difference or assuming distinct parameters. -/
theorem resolvent_identity (lambda mu : Q')
    (hl : (0 : Q') < lambda) (hm : (0 : Q') < mu) (x : Sector) :
    Sub (R lambda hl x.val) (R mu hm x.val) =
      S (mu-lambda) (R lambda hl (R mu hm x.val)) := by
  let p := domainPoint hw0 hw1 mu hm x
  have hc : (shifted hw0 hw1 lambda p).val =
      Sub x.val (S (mu-lambda) (R mu hm x.val)) := by
    rw [shifted_change hw0 hw1 lambda mu p, inverse_right]
    rfl
  have hi : R lambda hl (shifted hw0 hw1 lambda p).val = R mu hm x.val :=
    inverse_left hw0 hw1 lambda hl p
  rw [hc, resolvent_sub, resolvent_smul] at hi
  apply completed_eq_of_pairings hw0 hw1
  intro y
  have hh := congrArg (fun u => B u y) hi
  dsimp only at hh
  rw [completedInner_sub_left, completedInner_smul_left] at hh
  rw [completedInner_sub_left, completedInner_smul_left, ← hh]
  exact scalar_sub_switch _ _

#print axioms shifted_change
#print axioms resolvent_identity

end YMGap.Continuum.BF4WilsonAllNomeSectorResolventIdentity
