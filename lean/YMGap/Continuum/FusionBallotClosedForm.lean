/-
`FusionBallotClosedForm` — an explicit guarded ballot formula for the
fundamental SU(2) Bratteli path count.

The executable `FusionBratteli.pathCount` is convenient for finite checks,
while `PNPaths.ballotNat` is the closed Pascal-row expression

    C(p,(p-s)/2) - C(p,(p-s)/2-1).

The latter expression has spurious values outside the reachable cone and
off the parity lattice because natural subtraction/division are total.  The
public carrier below therefore retains both exact support guards.  This file
proves the Pascal arithmetic needed to identify the guarded closed form with
the sparse recurrence from `FusionBallotRecurrence`.

Constructive contract: Mathlib-free; no `Classical`, `native_decide`,
`sorry`, new axiom, or noncomputable definition.
-/

import YMGap.Continuum.FusionBallotRecurrence
import YMGap.Continuum.PNPaths

namespace YMGap.Continuum.FusionBallotClosedForm

open YMGap.Continuum.FusionBratteli
open YMGap.Continuum.FusionBallotRecurrence

/-- The total closed-form carrier: the Pascal ballot coefficient on the
reachable parity cone, and zero everywhere else. -/
def guardedBallotNat (p s : Nat) : Nat :=
  if s ≤ p ∧ (p + s) % 2 = 0 then PNPaths.ballotNat p s else 0

theorem guardedBallotNat_eq_ballotNat (p s : Nat)
    (hs : s ≤ p) (hpar : (p + s) % 2 = 0) :
    guardedBallotNat p s = PNPaths.ballotNat p s := by
  simp [guardedBallotNat, hs, hpar]

theorem guardedBallotNat_eq_zero_of_lt (p s : Nat) (h : p < s) :
    guardedBallotNat p s = 0 := by
  simp [guardedBallotNat, show ¬ s ≤ p by omega]

theorem guardedBallotNat_eq_zero_of_parity_ne (p s : Nat)
    (h : (p + s) % 2 ≠ 0) : guardedBallotNat p s = 0 := by
  simp [guardedBallotNat, h]

/-! ## Pascal arithmetic -/

private theorem choose_zero_of_lt : ∀ n k : Nat,
    n < k → PNPaths.choose n k = 0
  | _, 0, h => by omega
  | 0, _ + 1, _ => rfl
  | n + 1, k + 1, h => by
      simp only [PNPaths.choose]
      rw [choose_zero_of_lt n k (by omega),
        choose_zero_of_lt n (k + 1) (by omega)]

private theorem choose_self : ∀ n : Nat, PNPaths.choose n n = 1
  | 0 => rfl
  | n + 1 => by
      simp only [PNPaths.choose]
      rw [choose_self n, choose_zero_of_lt n (n + 1) (by omega)]

private theorem choose_pred : ∀ n : Nat,
    PNPaths.choose (n + 1) n = n + 1
  | 0 => rfl
  | n + 1 => by
      simp only [PNPaths.choose]
      rw [choose_pred n, choose_self,
        choose_zero_of_lt n (n + 1) (by omega)]

private theorem choose_zero : ∀ n : Nat, PNPaths.choose n 0 = 1
  | 0 => rfl
  | _ + 1 => rfl

private theorem choose_one : ∀ n : Nat, PNPaths.choose n 1 = n
  | 0 => rfl
  | n + 1 => by
      simp only [PNPaths.choose, choose_one n, choose_zero n]
      omega

/-- Adjacent-binomial cross identity for the self-contained Pascal carrier. -/
private theorem choose_adjacent_cross : ∀ p q : Nat, q < p →
    (q + 1) * PNPaths.choose p (q + 1) =
      (p - q) * PNPaths.choose p q
  | 0, q, h => by omega
  | p + 1, 0, _ => by rw [choose_one, choose_zero]; omega
  | p + 1, q + 1, h => by
      by_cases hlt : q + 1 < p
      · simp only [PNPaths.choose]
        have h1 := choose_adjacent_cross p q (by omega)
        have h2 := choose_adjacent_cross p (q + 1) hlt
        have htop : p + 1 - (q + 1) = p - q := by omega
        rw [htop]
        have hs : p - q = (p - (q + 1)) + 1 := by omega
        rw [hs] at h1 ⊢
        rw [Nat.mul_add, Nat.mul_add, h2]
        have hqa :
            (q + 1 + 1) * PNPaths.choose p (q + 1) =
              (q + 1) * PNPaths.choose p (q + 1) +
                PNPaths.choose p (q + 1) := by
          rw [Nat.add_mul]
          simp
        rw [hqa, h1]
        simp only [Nat.add_mul, Nat.one_mul]
        omega
      · have heq : q + 1 = p := by omega
        subst p
        rw [choose_self, choose_pred (q + 1)]
        have hs : q + 1 + 1 - (q + 1) = 1 := by omega
        rw [hs]
        omega

/-- On the increasing half of a Pascal row, the adjacent coefficient does
not decrease. -/
private theorem choose_pred_le (p q : Nat) (hq : 0 < q)
    (hh : 2 * q ≤ p + 1) :
    PNPaths.choose p (q - 1) ≤ PNPaths.choose p q := by
  have hqle : q ≤ p := by omega
  have hcross := choose_adjacent_cross p (q - 1) (by omega)
  have hback : q - 1 + 1 = q := by omega
  rw [hback] at hcross
  have hcoef : q ≤ p - (q - 1) := by omega
  have hscaled :
      q * PNPaths.choose p (q - 1) ≤
        q * PNPaths.choose p q := by
    rw [hcross]
    exact Nat.mul_le_mul_right (PNPaths.choose p (q - 1)) hcoef
  exact Nat.le_of_mul_le_mul_left hscaled hq

/-! ## The ballot coefficient in deficit coordinates -/

/-- The Pascal difference at down-step count `q`.  Unlike `ballotNat`, this
coordinate does not perform the endpoint-to-deficit division internally. -/
private def ballotAt (p : Nat) : Nat → Nat
  | 0 => 1
  | q + 1 => PNPaths.choose p (q + 1) - PNPaths.choose p q

private theorem ballotNat_eq_ballotAt (p s : Nat) :
    PNPaths.ballotNat p s = ballotAt p ((p - s) / 2) := by
  unfold PNPaths.ballotNat
  rfl

/-- Pascal's rule for ballot differences.  The half-row condition makes
both natural subtractions genuine differences rather than truncations. -/
private theorem ballotAt_succ (p q : Nat) (hq : 0 < q)
    (hh : 2 * q ≤ p + 1) :
    ballotAt (p + 1) q = ballotAt p q + ballotAt p (q - 1) := by
  cases q with
  | zero => omega
  | succ q =>
      cases q with
      | zero =>
          simp only [ballotAt, PNPaths.choose]
          rw [choose_one]
          omega
      | succ r =>
          have hhi : 2 * (r + 1 + 1) ≤ p + 1 := by omega
          have htop := choose_pred_le p (r + 1 + 1) (by omega) hhi
          have hmid := choose_pred_le p (r + 1) (by omega) (by omega)
          simp only [Nat.add_sub_cancel] at htop hmid ⊢
          simp only [ballotAt, PNPaths.choose]
          omega

/-- The extra Pascal difference just beyond the midpoint of an odd row is
zero.  This is the reflecting-wall cancellation. -/
private theorem ballotAt_central_zero (p q : Nat) (hq : 0 < q)
    (hmid : p + 1 = 2 * q) : ballotAt p q = 0 := by
  have hcross := choose_adjacent_cross p (q - 1) (by omega)
  have hback : q - 1 + 1 = q := by omega
  have hcoef : p - (q - 1) = q := by omega
  rw [hback, hcoef] at hcross
  have heq : PNPaths.choose p q = PNPaths.choose p (q - 1) :=
    Nat.eq_of_mul_eq_mul_left hq hcross
  cases q with
  | zero => omega
  | succ q =>
      simp only [ballotAt]
      have hback' : q + 1 - 1 = q := by omega
      rw [hback'] at heq
      rw [heq, Nat.sub_self]

/-- At the reflecting wall, the next even-time return coefficient is the
previous odd-time height-one coefficient. -/
private theorem ballotNat_wall (p : Nat) (hpar : (p + 1) % 2 = 0) :
    PNPaths.ballotNat (p + 1) 0 = PNPaths.ballotNat p 1 := by
  let q := (p + 1) / 2
  have hq : 0 < q := by dsimp [q]; omega
  have hmid : p + 1 = 2 * q := by dsimp [q]; omega
  have hleft : (p + 1 - 0) / 2 = q := rfl
  have hright : (p - 1) / 2 = q - 1 := by dsimp [q]; omega
  rw [ballotNat_eq_ballotAt, ballotNat_eq_ballotAt, hleft, hright]
  rw [ballotAt_succ p q hq (by omega), ballotAt_central_zero p q hq hmid]
  omega

/-- Interior Pascal recurrence for endpoint ballot numbers.  The successor
is guarded because it leaves the cone at the top edge `s=p`. -/
private theorem ballotNat_succ_endpoint (p s : Nat)
    (hs : s ≤ p) (hpar : (p + s) % 2 = 0) :
    PNPaths.ballotNat (p + 1) (s + 1) =
      PNPaths.ballotNat p s + guardedBallotNat p (s + 2) := by
  let q := (p - s) / 2
  by_cases hq0 : q = 0
  · have hsp : s = p := by dsimp [q] at hq0; omega
    subst s
    rw [guardedBallotNat_eq_zero_of_lt p (p + 2) (by omega)]
    simp only [Nat.add_zero]
    rw [ballotNat_eq_ballotAt, ballotNat_eq_ballotAt]
    have h0 : (p + 1 - (p + 1)) / 2 = 0 := by omega
    have h1 : (p - p) / 2 = 0 := by omega
    rw [h0, h1]
    rfl
  · have hq : 0 < q := Nat.pos_of_ne_zero hq0
    have hs2 : s + 2 ≤ p := by dsimp [q] at hq hq0; omega
    have hpar2 : (p + (s + 2)) % 2 = 0 := by omega
    rw [guardedBallotNat_eq_ballotNat p (s + 2) hs2 hpar2]
    rw [ballotNat_eq_ballotAt, ballotNat_eq_ballotAt,
      ballotNat_eq_ballotAt]
    have hnew : (p + 1 - (s + 1)) / 2 = q := by dsimp [q]; omega
    have hold : (p - s) / 2 = q := rfl
    have hnext : (p - (s + 2)) / 2 = q - 1 := by dsimp [q]; omega
    rw [hnew, hold, hnext]
    exact ballotAt_succ p q hq (by dsimp [q]; omega)

/-! ## The guarded closed form obeys the sparse path recurrence -/

theorem guardedBallotNat_succ (p s : Nat) :
    guardedBallotNat (p + 1) s =
      (if s = 0 then 0 else guardedBallotNat p (s - 1)) +
        guardedBallotNat p (s + 1) := by
  cases s with
  | zero =>
      simp only [if_pos, Nat.zero_add, Nat.zero_sub]
      by_cases hpar : (p + 1) % 2 = 0
      · rw [guardedBallotNat_eq_ballotNat (p + 1) 0 (by omega) (by
            simpa only [Nat.add_zero] using hpar)]
        rw [guardedBallotNat_eq_ballotNat p 1 (by omega) (by
            simpa only [Nat.add_comm] using hpar)]
        exact ballotNat_wall p hpar
      · rw [guardedBallotNat_eq_zero_of_parity_ne (p + 1) 0 (by
            simpa only [Nat.add_zero] using hpar)]
        rw [guardedBallotNat_eq_zero_of_parity_ne p 1 (by
            simpa only [Nat.add_comm] using hpar)]
  | succ s =>
      simp only [Nat.succ_ne_zero, if_false, Nat.succ_sub_one]
      by_cases hsupport : s + 1 ≤ p + 1 ∧ (p + 1 + (s + 1)) % 2 = 0
      · have hs : s ≤ p := by omega
        have hpar : (p + s) % 2 = 0 := by omega
        rw [guardedBallotNat_eq_ballotNat (p + 1) (s + 1)
          hsupport.1 hsupport.2]
        rw [guardedBallotNat_eq_ballotNat p s hs hpar]
        exact ballotNat_succ_endpoint p s hs hpar
      · rw [show guardedBallotNat (p + 1) (s + 1) = 0 by
          by_cases hcone : s + 1 ≤ p + 1
          · apply guardedBallotNat_eq_zero_of_parity_ne
            intro hp
            exact hsupport ⟨hcone, hp⟩
          · exact guardedBallotNat_eq_zero_of_lt _ _ (by omega)]
        by_cases hcone : s ≤ p
        · have hpar : (p + s) % 2 ≠ 0 := by
            intro hp
            apply hsupport
            exact ⟨by omega, by omega⟩
          rw [guardedBallotNat_eq_zero_of_parity_ne p s hpar,
            guardedBallotNat_eq_zero_of_parity_ne p (s + 2) (by omega)]
        · rw [guardedBallotNat_eq_zero_of_lt p s (by omega),
            guardedBallotNat_eq_zero_of_lt p (s + 2) (by omega)]

/-! ## Exact identification with the executable path count -/

/-- **Explicit guarded ballot closed form.**  The fundamental SU(2) Bratteli
path count is exactly the Pascal ballot coefficient on its reachable parity
cone, with zero supplied by the two exact support guards. -/
theorem pathCount_j1_eq_guardedBallotNat : ∀ p s : Nat,
    pathCount 1 p s = guardedBallotNat p s
  | 0, s => by
      cases s with
      | zero => decide
      | succ s =>
          rw [pathCount_j1_eq_zero_of_lt 0 (s + 1) (by omega),
            guardedBallotNat_eq_zero_of_lt 0 (s + 1) (by omega)]
  | p + 1, s => by
      rw [pathCount_j1_succ, guardedBallotNat_succ,
        pathCount_j1_eq_guardedBallotNat p (s - 1),
        pathCount_j1_eq_guardedBallotNat p (s + 1)]

/-- Supported specialization: no guards remain in the value. -/
theorem pathCount_j1_eq_ballotNat (p s : Nat)
    (hs : s ≤ p) (hpar : (p + s) % 2 = 0) :
    pathCount 1 p s = PNPaths.ballotNat p s := by
  rw [pathCount_j1_eq_guardedBallotNat,
    guardedBallotNat_eq_ballotNat p s hs hpar]

end YMGap.Continuum.FusionBallotClosedForm

#print axioms YMGap.Continuum.FusionBallotClosedForm.guardedBallotNat_eq_ballotNat
#print axioms YMGap.Continuum.FusionBallotClosedForm.guardedBallotNat_eq_zero_of_lt
#print axioms YMGap.Continuum.FusionBallotClosedForm.guardedBallotNat_eq_zero_of_parity_ne
#print axioms YMGap.Continuum.FusionBallotClosedForm.guardedBallotNat_succ
#print axioms YMGap.Continuum.FusionBallotClosedForm.pathCount_j1_eq_guardedBallotNat
#print axioms YMGap.Continuum.FusionBallotClosedForm.pathCount_j1_eq_ballotNat
