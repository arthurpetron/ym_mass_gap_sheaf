/-
# Robust3 undershooting AF schedule, instance B: step-2 fine nome `279/500` (additive W558 copy)

**Label: PROVED `NomeSchedule` construction plus PROVED decidable `DyadicRGStep` checks. NOT gap
evidence.**  Additive copy of `Robust3UndershootAfSchedule` whose head (`j < 6`) is read from
`dyTableB` instead of `dyTable`; the only changed nome is index 3 (`279/500` instead of `14/25`).
The data window `r3Tab` and the exact tail `1 − r3Gap` are reused unchanged.  The original
schedule is untouched.

U(1) note (unchanged): the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian
evidence; any uniform gap at w ≳ 1/8 would be genuine non-abelian content.
Constructive, no external library; axioms within `propext`, `Quot.sound`.
-/

import YMGap.RG.DyadicCrossoverScheduleW558
import YMGap.RG.Robust3UndershootAfSchedule

namespace YMGap.RG.Robust3UndershootAfScheduleW558

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4WilsonAllNomeDyadicSmoothedTrajectory (NomeSchedule)
open YMGap.RG.StrongCouplingNomeThreshold (inv55)
open YMGap.RG.DyadicCrossoverSchedule (DyadicRGStep dyTable)
open YMGap.RG.DyadicCrossoverScheduleW558 (dyTableB dyTableB_eq)
open YMGap.RG.Robust3UndershootAfSchedule
  (r3Tab r3Gap r3Gap_anti r3Gap_pos r3Gap_lt_one r3Gap_le_of_modulus r3Nome
   robust3UndershootSchedule)

/-- Instance-B nome: `dyTableB` head, then the unchanged `Robust3` window and tail. -/
def r3NomeB (j : Nat) : Q' :=
  if j < 6 then dyTableB j else if j < 11 then r3Tab j else (1 : Q') - r3Gap (j - 11)

theorem r3NomeB_three : r3NomeB 3 = Q'.mkPos 279 500 (by decide) := rfl

/-- Instance B agrees with `Robust3` away from index 3. -/
theorem r3NomeB_eq (j : Nat) (h : j ≠ 3) : r3NomeB j = r3Nome j := by
  unfold r3NomeB r3Nome
  by_cases a : j < 6
  · rw [if_pos a, if_pos a]; exact dyTableB_eq j h
  · rw [if_neg a, if_neg a]

private theorem not_lt_of_le'' {a b : Nat} (h : b ≤ a) : ¬ a < b := fun h' =>
  Nat.lt_irrefl a (Nat.lt_of_lt_of_le h' h)

private theorem tail_eqB (j : Nat) (hj : 11 ≤ j) : r3NomeB j = (1 : Q') - r3Gap (j - 11) := by
  unfold r3NomeB
  rw [if_neg (not_lt_of_le'' (Nat.le_trans (by decide : 6 ≤ 11) hj)), if_neg (not_lt_of_le'' hj)]

private theorem head_posB : ∀ j, j < 11 → (0 : Q') < r3NomeB j := by decide
private theorem head_lt_oneB : ∀ j, j < 11 → r3NomeB j < (1 : Q') := by decide
private theorem head_monoB : ∀ j, j < 11 → r3NomeB j ≤ r3NomeB (j+1) := by decide

/-- Instance-B head is strictly increasing (decidable; cf. `Robust3NomeInjective.head_strict`). -/
theorem head_strictB : ∀ j, j < 11 → r3NomeB j < r3NomeB (j+1) := by decide

private theorem one_sub_leB {a b : Q'} (h : a ≤ b) : (1 : Q') - b ≤ (1 : Q') - a :=
  Q'.add_le_add_left 1 _ _ (Q'.neg_le_neg h)

private theorem r3B_mono (j : Nat) : r3NomeB j ≤ r3NomeB (j+1) := by
  by_cases h : j < 11
  · exact head_monoB j h
  · have hj : 11 ≤ j := Nat.not_lt.mp h
    have e : j + 1 - 11 = (j - 11) + 1 := Nat.succ_sub hj
    rw [tail_eqB j hj, tail_eqB (j+1) (Nat.le_succ_of_le hj), e]
    exact one_sub_leB (r3Gap_anti (j - 11))

/-- **Instance B is a `NomeSchedule` (PROVED; proofs copied from `Robust3`).** -/
def robust3UndershootScheduleB : NomeSchedule where
  nome := r3NomeB
  nome_pos := fun j => by
    by_cases h : j < 11
    · exact head_posB j h
    · rw [tail_eqB j (Nat.not_lt.mp h)]
      exact YMGap.Continuum.HKPos.one_sub_pos (r3Gap_lt_one _)
  nome_lt_one := fun j => by
    by_cases h : j < 11
    · exact head_lt_oneB j h
    · rw [tail_eqB j (Nat.not_lt.mp h)]
      exact YMGap.Continuum.AFTrajectoryCertificate.one_sub_lt_one (r3Gap_pos _)
  nome_mono := r3B_mono
  limitModulus := fun eps => 11 + 4 * eps.den
  nome_limit := fun eps he j hj => by
    rw [tail_eqB j (Nat.le_trans (Nat.le_add_right 11 _) hj)]
    have hj' : 4 * eps.den + 11 ≤ j := by rw [Nat.add_comm]; exact hj
    exact one_sub_leB (r3Gap_le_of_modulus eps he (j - 11) (Nat.le_sub_of_add_le hj'))

theorem robust3B_nome_eq (j : Nat) (h : j ≠ 3) :
    robust3UndershootScheduleB.nome j = robust3UndershootSchedule.nome j := r3NomeB_eq j h

/-- Seed `1/64 ≤ 1/55`; head equals `dyTableB`; `w_6 = 779/1000`. -/
theorem robust3B_join :
    robust3UndershootScheduleB.nome 0 ≤ inv55 ∧
    (∀ j, j < 6 → robust3UndershootScheduleB.nome j = dyTableB j) ∧
    robust3UndershootScheduleB.nome 6 = Q'.mkPos 779 1000 (by decide) := by
  decide

/-- **Every instance-B step `0 → … → 45` passes `DyadicRGStep` (decidable, exact rationals),**
including `7/20 → 279/500 → 67/100`. -/
theorem robust3_stepsB :
    ∀ n, n < 45 → DyadicRGStep (robust3UndershootScheduleB.nome n)
      (robust3UndershootScheduleB.nome (n+1)) := by
  decide

end YMGap.RG.Robust3UndershootAfScheduleW558

#print axioms YMGap.RG.Robust3UndershootAfScheduleW558.robust3UndershootScheduleB
#print axioms YMGap.RG.Robust3UndershootAfScheduleW558.r3NomeB_eq
#print axioms YMGap.RG.Robust3UndershootAfScheduleW558.robust3B_join
#print axioms YMGap.RG.Robust3UndershootAfScheduleW558.robust3_stepsB
#print axioms YMGap.RG.Robust3UndershootAfScheduleW558.head_strictB
