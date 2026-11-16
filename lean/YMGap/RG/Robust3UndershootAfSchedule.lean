/-
# Exact-rational undershooting AF nome schedule (additive variant `Robust3`)

**Label: PROVED `NomeSchedule` construction plus PROVED decidable `DyadicRGStep` checks. The robust design
and every all-`j` margin statement are MOTIVATION from numerics and asymptotic analysis (audit), NOT
theorems. NOT gap evidence. `δ_min = 0` for `ℓ ≤ 1` is only a NECESSARY condition: it removes the
obstruction but does not prove `hafδ`.**

U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it
would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). Per the
numerics, the U(1) transition lies between 1/8 and 1/2, inside the crossover.

Schedule `robust3UndershootSchedule` (index-consistent with `scaleChain`, no offset):
* `j < 6`: `dyTable`; `6 ≤ j ≤ 10`: `r3Tab` (the same window as `Robust2`);
* `j ≥ 11`, `k = j − 11`, `m = k + 4`, `n = k + 14`: `w_j = 1 − 1/E_k`. There are no integer floors. `ecomp k` is
  the exact closed form `E = D·B`, computed as a reduced Nat fraction:
  `D = m + 9989/2000 + κ'_n·H_{m+3} + κ'_n²·(H_m + 1)/m + (16/17)·Σ_{t=m}^{m+16} 1/t`,
  `κ'_n = (51/121)/L_n`, `B = 22·L_n/(3·P_n)`, `L_n = Σ_{k≤n} 1/(k·2^k)` (`≤ ln 2`),
  `P_n = 18·(Σ_{k≤n} 1/(k²·C(2k,k)) + (4/3)/((n+1)²·C(2n+2,n+1)))` (`≥ π²`). So `B ≤ 1/A`, i.e. the
  effective `A'_n = 1/B ≥ A = 3π²/(22 ln 2)`, rounded UP with error `O(2^{-n})`. This is analysis, NOT used by
  any theorem here.
* `E_k` is the running max of `max(ecomp k, (k+1)/4)` (`r3E`). This makes monotonicity and the modulus
  structural. Numerically the envelope and the floor are never active (audit), so `E_k = ecomp k`.

Constructive, no external library; axioms within `propext`, `Quot.sound`.
-/

import YMGap.RG.DyadicCrossoverSchedule
import YMGap.Constructive.RegularCRealArith

namespace YMGap.RG.Robust3UndershootAfSchedule

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4WilsonAllNomeDyadicSmoothedTrajectory (NomeSchedule)
open YMGap.RG.StrongCouplingNomeThreshold (inv55)
open YMGap.RG.DyadicCrossoverSchedule (DyadicRGStep dyTable)

/-- Data-window table, `j = 6..10` (identical to `Robust2`). -/
def r3Tab : Nat → Q'
  | 6 => Q'.mkPos 779 1000 (by decide)
  | 7 => Q'.mkPos 794701 1000000 (by decide)
  | 8 => Q'.mkPos 808737 1000000 (by decide)
  | 9 => Q'.mkPos 32873 40000 (by decide)
  | _ => Q'.mkPos 166761 200000 (by decide)

/-- Nonnegative rational as a Nat pair in lowest terms (computation only; no theorem depends on its
semantics). -/
structure NQ where
  n : Nat
  d : Nat

namespace NQ
def red (a b : Nat) : NQ := ⟨a / Nat.gcd a b, b / Nat.gcd a b⟩
def add (x y : NQ) : NQ := red (x.n * y.d + y.n * x.d) (x.d * y.d)
def mul (x y : NQ) : NQ := red (x.n * y.n) (x.d * y.d)
def div (x y : NQ) : NQ := red (x.n * y.d) (x.d * y.n)
def toQ (x : NQ) : Q' := ⟨Int.ofNat x.n, x.d - 1⟩
end NQ

/-- Harmonic number `H_m`. -/
def harm : Nat → NQ
  | 0 => ⟨0, 1⟩
  | m+1 => NQ.add (harm m) ⟨1, m+1⟩

/-- `L_n = Σ_{k=1}^n 1/(k·2^k)`. -/
def lnS : Nat → NQ
  | 0 => ⟨0, 1⟩
  | k+1 => NQ.add (lnS k) ⟨1, (k+1) * 2 ^ (k+1)⟩

/-- `(S_n, t_{n+1})` with `t_k = 1/(k²·C(2k,k))`, `S_n = Σ_{k≤n} t_k`, via `t_{k+1} = t_k·k²/((2k+1)(2k+2))`. -/
def piST : Nat → NQ × NQ
  | 0 => (⟨0, 1⟩, ⟨1, 2⟩)
  | n+1 => let p := piST n
      (NQ.add p.1 p.2, NQ.mul p.2 ⟨(n+1) * (n+1), (2*n+3) * (2*n+4)⟩)

/-- `P_n = 18·(S_n + (4/3)·t_{n+1})`. -/
def pUp (n : Nat) : NQ :=
  let p := piST n
  NQ.mul ⟨18, 1⟩ (NQ.add p.1 (NQ.mul ⟨4, 3⟩ p.2))

/-- `Σ_{c<r} 1/(m+c)`. -/
def seg (m : Nat) : Nat → NQ
  | 0 => ⟨0, 1⟩
  | r+1 => NQ.add (seg m r) ⟨1, m + r⟩

/-- The exact closed form `E = D·B` at tail index `k` (`m = k+4`, `n = k+14`). -/
def ecomp (k : Nat) : NQ :=
  let L := lnS (k + 14)
  let kp := NQ.div ⟨51, 121⟩ L
  let D := NQ.add (NQ.add (NQ.add (NQ.add ⟨k + 4, 1⟩ ⟨9989, 2000⟩) (NQ.mul kp (harm (k + 7))))
      (NQ.div (NQ.mul (NQ.mul kp kp) (NQ.add (harm (k + 4)) ⟨1, 1⟩)) ⟨k + 4, 1⟩))
      (NQ.mul ⟨16, 17⟩ (seg (k + 4) 17))
  NQ.mul D (NQ.div (NQ.mul ⟨22, 3⟩ L) (pUp (k + 14)))

/-- Floor `(k+1)/4` (numerically inactive). -/
def r3Floor (k : Nat) : Q' := Q'.mkPos ((k + 1 : Nat) : Int) 4 (by decide)

def r3Raw (k : Nat) : Q' := Q'.max' (NQ.toQ (ecomp k)) (r3Floor k)

/-- Running max (numerically equal to `ecomp k`). -/
def r3E : Nat → Q'
  | 0 => r3Raw 0
  | k+1 => Q'.max' (r3E k) (r3Raw (k+1))

theorem r3E_mono (k : Nat) : r3E k ≤ r3E (k+1) := Q'.le_max'_left _ _

theorem r3Raw_le (k : Nat) : r3Raw k ≤ r3E k := by
  cases k with
  | zero => exact Q'.le_refl' _
  | succ k => exact Q'.le_max'_right _ _

theorem r3Floor_le (k : Nat) : r3Floor k ≤ r3E k :=
  Q'.le_trans' _ _ _ (Q'.le_max'_right _ _) (r3Raw_le k)

theorem r3E0_le : ∀ k, r3E 0 ≤ r3E k
  | 0 => Q'.le_refl' _
  | k+1 => Q'.le_trans' _ _ _ (r3E0_le k) (r3E_mono k)

private theorem one_lt_E0 : (1 : Q') < r3E 0 := by decide

theorem one_lt_r3E (k : Nat) : (1 : Q') < r3E k := by
  have h1 : (1 : Int) * ((r3E 0).den : Int) < (r3E 0).num * 1 := one_lt_E0
  have h2 : (r3E 0).num * ((r3E k).den : Int) ≤ (r3E k).num * ((r3E 0).den : Int) := r3E0_le k
  rw [Int.one_mul, Int.mul_one] at h1
  show (1 : Int) * ((r3E k).den : Int) < (r3E k).num * 1
  rw [Int.one_mul, Int.mul_one]
  have hd0 : (0 : Int) < ((r3E 0).den : Int) := Int.ofNat_lt.mpr (Q'.den_pos _)
  have hdk : (0 : Int) < ((r3E k).den : Int) := Int.ofNat_lt.mpr (Q'.den_pos _)
  have h3 : ((r3E 0).den : Int) * ((r3E k).den : Int) < (r3E 0).num * ((r3E k).den : Int) :=
    Int.mul_lt_mul_of_pos_right h1 hdk
  have h4 : ((r3E 0).den : Int) * ((r3E k).den : Int) < ((r3E 0).den : Int) * (r3E k).num := by
    rw [Int.mul_comm ((r3E 0).den : Int) (r3E k).num]; exact Int.lt_of_lt_of_le h3 h2
  exact Int.lt_of_mul_lt_mul_left h4 (Int.le_of_lt hd0)

theorem r3E_num_pos (k : Nat) : 0 < (r3E k).num := by
  have h : (1 : Int) * ((r3E k).den : Int) < (r3E k).num * 1 := one_lt_r3E k
  rw [Int.one_mul, Int.mul_one] at h
  exact Int.lt_trans (Int.ofNat_lt.mpr (Q'.den_pos _)) h

theorem r3E_toNat (k : Nat) : (((r3E k).num.toNat : Nat) : Int) = (r3E k).num :=
  Int.toNat_of_nonneg (Int.le_of_lt (r3E_num_pos k))

theorem r3E_toNat_pos (k : Nat) : 0 < (r3E k).num.toNat := by
  have h := r3E_num_pos k
  rw [← r3E_toNat k] at h
  exact Int.ofNat_lt.mp h

/-- Tail gap `1 − w_{11+k} = 1/E_k`. -/
def r3Gap (k : Nat) : Q' := Q'.mkPos ((r3E k).den : Int) (r3E k).num.toNat (r3E_toNat_pos k)

theorem r3Gap_den (k : Nat) : ((r3Gap k).den : Int) = (r3E k).num := by
  unfold r3Gap; rw [Q'.mkPos_den]; exact r3E_toNat k

theorem r3Gap_anti (k : Nat) : r3Gap (k+1) ≤ r3Gap k := by
  show ((r3E (k+1)).den : Int) * ((r3Gap k).den : Int) ≤ ((r3E k).den : Int) * ((r3Gap (k+1)).den : Int)
  rw [r3Gap_den, r3Gap_den]
  have h : (r3E k).num * ((r3E (k+1)).den : Int) ≤ (r3E (k+1)).num * ((r3E k).den : Int) := r3E_mono k
  rw [Int.mul_comm ((r3E (k+1)).den : Int), Int.mul_comm ((r3E k).den : Int)]
  exact h

theorem r3Gap_pos (k : Nat) : (0 : Q') < r3Gap k := by
  show (0 : Int) * ((r3Gap k).den : Int) < ((r3E k).den : Int) * 1
  rw [Int.zero_mul, Int.mul_one]
  exact Int.ofNat_lt.mpr (Q'.den_pos _)

theorem r3Gap_lt_one (k : Nat) : r3Gap k < (1 : Q') := by
  show ((r3E k).den : Int) * 1 < 1 * ((r3Gap k).den : Int)
  rw [r3Gap_den]
  have h : (1 : Int) * ((r3E k).den : Int) < (r3E k).num * 1 := one_lt_r3E k
  rw [Int.one_mul, Int.mul_one] at h
  rw [Int.one_mul, Int.mul_one]; exact h

theorem r3Gap_le_of_modulus (eps : Q') (he : (0 : Q') < eps) (k : Nat)
    (hk : 4 * eps.den ≤ k) : r3Gap k ≤ eps := by
  have hn1 : (1 : Int) ≤ eps.num := Int.add_one_le_of_lt (Q'.num_pos_of_pos he)
  show ((r3E k).den : Int) * (eps.den : Int) ≤ eps.num * ((r3Gap k).den : Int)
  rw [r3Gap_den]
  have hf : ((k + 1 : Nat) : Int) * ((r3E k).den : Int) ≤ (r3E k).num * ((4 : Nat) : Int) :=
    r3Floor_le k
  have hk' : ((4 * eps.den : Nat) : Int) ≤ ((k + 1 : Nat) : Int) :=
    Int.ofNat_le.mpr (Nat.le_succ_of_le hk)
  rw [Int.natCast_mul] at hk'
  have hd : (0 : Int) ≤ ((r3E k).den : Int) := Int.natCast_nonneg _
  have h1 : ((4 : Nat) : Int) * ((eps.den : Nat) : Int) * ((r3E k).den : Int)
      ≤ (r3E k).num * ((4 : Nat) : Int) :=
    Int.le_trans (Int.mul_le_mul_of_nonneg_right hk' hd) hf
  rw [Int.mul_assoc, Int.mul_comm (r3E k).num] at h1
  have h2 : ((eps.den : Nat) : Int) * ((r3E k).den : Int) ≤ (r3E k).num :=
    Int.le_of_mul_le_mul_left h1 (by decide)
  have h3 : (1 : Int) * (r3E k).num ≤ eps.num * (r3E k).num :=
    Int.mul_le_mul_of_nonneg_right hn1 (Int.le_of_lt (r3E_num_pos k))
  rw [Int.one_mul] at h3
  rw [Int.mul_comm]
  exact Int.le_trans h2 h3

/-- The exact-rational nome joined to the dyadic crossover. -/
def r3Nome (j : Nat) : Q' :=
  if j < 6 then dyTable j else if j < 11 then r3Tab j else (1 : Q') - r3Gap (j - 11)

private theorem not_lt_of_le' {a b : Nat} (h : b ≤ a) : ¬ a < b := fun h' =>
  Nat.lt_irrefl a (Nat.lt_of_lt_of_le h' h)

private theorem tail_eq (j : Nat) (hj : 11 ≤ j) : r3Nome j = (1 : Q') - r3Gap (j - 11) := by
  unfold r3Nome
  rw [if_neg (not_lt_of_le' (Nat.le_trans (by decide : 6 ≤ 11) hj)), if_neg (not_lt_of_le' hj)]

private theorem head_pos : ∀ j, j < 11 → (0 : Q') < r3Nome j := by decide
private theorem head_lt_one : ∀ j, j < 11 → r3Nome j < (1 : Q') := by decide
private theorem head_mono : ∀ j, j < 11 → r3Nome j ≤ r3Nome (j+1) := by decide

private theorem one_sub_le {a b : Q'} (h : a ≤ b) : (1 : Q') - b ≤ (1 : Q') - a :=
  Q'.add_le_add_left 1 _ _ (Q'.neg_le_neg h)

private theorem r3_mono (j : Nat) : r3Nome j ≤ r3Nome (j+1) := by
  by_cases h : j < 11
  · exact head_mono j h
  · have hj : 11 ≤ j := Nat.not_lt.mp h
    have e : j + 1 - 11 = (j - 11) + 1 := Nat.succ_sub hj
    rw [tail_eq j hj, tail_eq (j+1) (Nat.le_succ_of_le hj), e]
    exact one_sub_le (r3Gap_anti (j - 11))

/-- **The exact-rational schedule is a `NomeSchedule` (PROVED).**
U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it
would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). Per the
numerics, the U(1) transition lies between 1/8 and 1/2, inside the crossover. -/
def robust3UndershootSchedule : NomeSchedule where
  nome := r3Nome
  nome_pos := fun j => by
    by_cases h : j < 11
    · exact head_pos j h
    · rw [tail_eq j (Nat.not_lt.mp h)]
      exact YMGap.Continuum.HKPos.one_sub_pos (r3Gap_lt_one _)
  nome_lt_one := fun j => by
    by_cases h : j < 11
    · exact head_lt_one j h
    · rw [tail_eq j (Nat.not_lt.mp h)]
      exact YMGap.Continuum.AFTrajectoryCertificate.one_sub_lt_one (r3Gap_pos _)
  nome_mono := r3_mono
  limitModulus := fun eps => 11 + 4 * eps.den
  nome_limit := fun eps he j hj => by
    rw [tail_eq j (Nat.le_trans (Nat.le_add_right 11 _) hj)]
    have hj' : 4 * eps.den + 11 ≤ j := by rw [Nat.add_comm]; exact hj
    exact one_sub_le (r3Gap_le_of_modulus eps he (j - 11) (Nat.le_sub_of_add_le hj'))

/-- Seed `w_0 = 1/64 ≤ 1/55`; `w_j = dyTable j` for `j < 6`; `w_6 = 779/1000` (join, no offset). -/
theorem robust3_join :
    robust3UndershootSchedule.nome 0 ≤ inv55 ∧
    (∀ j, j < 6 → robust3UndershootSchedule.nome j = dyTable j) ∧
    robust3UndershootSchedule.nome 6 = Q'.mkPos 779 1000 (by decide) := by
  decide

/-- **Every step `0 → … → 45` passes `DyadicRGStep` (decidable, exact rationals).** `DyadicRGStep`
only bounds steps from above, so it accepts undershooting steps.
U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it
would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). Per the
numerics, the U(1) transition lies between 1/8 and 1/2, inside the crossover. -/
theorem robust3_steps :
    ∀ n, n < 45 → DyadicRGStep (robust3UndershootSchedule.nome n) (robust3UndershootSchedule.nome (n+1)) := by
  decide

end YMGap.RG.Robust3UndershootAfSchedule
