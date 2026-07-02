/-
# The genuine `arctan(1/5)` coefficient model: `SeriesData (1/5)` inhabited

## What this module does

`YMGap.Continuum.SeriesComposition.SeriesData x` is the honest `Type`-level
carrier that upgrades the arctan↔trig tangent link `sin(arctan x) ≃ x·cos(arctan x)`
from a scaffold to a genuine `CReal` statement.  Its non-vacuity was previously
witnessed only by the degenerate all-zero sequence (`seriesData_zero`), and a
stale note claimed the *actual* arctan coefficients could not be built for want of
`Q'` division.

That claim is **false**: `Q'.divPos` (division by a positive rational denominator,
`RegularCRealArith.lean`) is axiom-clean and total on positive denominators.  This
module uses it to build the genuine solved recurrence

    p_{n+2} = (q_{n+1} − n·pₙ)/(n+2),   q_{n+2} = (−p_{n+1} − n·qₙ)/(n+2),
    (p₀,q₀) = (0,1),   (p₁,q₁) = (1,0),

discharge every `SeriesData` recurrence field from `divPos_mul_eqv`, prove the
uniform coefficient bound `|pₙ|,|qₙ| ≤ 1`, majorize the power series by the
geometric `(1/2)ⁿ` (since `|1/5| ≤ 1/2`), and thereby construct the two `CReal`
limits `sval = sin(arctan(1/5))`, `cval = cos(arctan(1/5))` with a genuine
geometric Cauchy modulus.  Feeding the assembled `SeriesData (1/5)` to the green
`tanLink_of_data` closes `TanLink (1/5) cval sval`.

## Structure

* **Layer A** — reused verbatim: `Q'.divPos`, `divPos_mul_eqv`,
  `divPos_le_of_le_mul`, `le_divPos_of_mul_le`.
* **Layer B** — `arctanTwo`/`pc`/`qc`, the two-step pair recursion, and the
  recurrence-discharge lemmas (`pc_rec`, `qc_rec`, base values).
* **Layer C** — `coeff_le_one` (uniform bound), the `(1/2)ⁿ` majorant, the block
  bounds, and the `CReal` build with a geometric Cauchy modulus (mirroring the
  `CReal.artanh` template); the two `ConvergesTo` collapse to `convergesTo_self`.
* **Layer D** — assemble `arctanSeriesData` and close `tanLink_arctan_fifth`.

## Axiom gate (AGENTS.md Rule 1 / Rule 8)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, `native_decide`,
`sorry`, or custom `axiom`.  All witnesses are `Type`-level data (Rule 8).
-/

import YMGap.Continuum.SeriesComposition
import YMGap.Constructive.RegularCRealArith
import YMGap.Constructive.CRealLog
import YMGap.Constructive.HalfPow
import YMGap.Constructive.ExpNeg
import YMGap.Constructive.GeometricTail
import YMGap.Constructive.TrigBound
import YMGap.Constructive.CauchyConv

namespace YMGap.Constructive.QDivArctanSeries

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.TanArctan
open YMGap.Continuum.SeriesComposition

/-! ## Layer B — the arctan coefficient recursion via `Q'.divPos` -/

/-- One recurrence step producing the pair at index `n+2` from the pairs at `n`
(`pn`) and `n+1` (`pn1`):
`p_{n+2} = (q_{n+1} − n·pₙ)/(n+2)`, `q_{n+2} = (−p_{n+1} − n·qₙ)/(n+2)`. -/
def stepPair (n : Nat) (pn pn1 : Q' × Q') : Q' × Q' :=
  (Q'.divPos (pn1.2 + -(Q'.ofNat n * pn.1)) (Q'.ofNat (n + 2)) (Q'.ofNat_succ_pos (n + 1)),
   Q'.divPos (-(pn1.1) + -(Q'.ofNat n * pn.2)) (Q'.ofNat (n + 2)) (Q'.ofNat_succ_pos (n + 1)))

/-- The two-window recursion carrying `(pair n, pair (n+1))`.  Base
`((0,1),(1,0))`; each step drops the old window and appends `stepPair`. -/
def arctanTwo : Nat → (Q' × Q') × (Q' × Q')
  | 0 => ((0, 1), (1, 0))
  | n + 1 =>
    let prev := arctanTwo n
    (prev.2, stepPair n prev.1 prev.2)

/-- The sine coefficient `pₙ`. -/
def pc (n : Nat) : Q' := (arctanTwo n).1.1
/-- The cosine coefficient `qₙ`. -/
def qc (n : Nat) : Q' := (arctanTwo n).1.2

@[simp] theorem pc_zero : pc 0 = 0 := rfl
@[simp] theorem qc_zero : qc 0 = 1 := rfl
@[simp] theorem pc_one : pc 1 = 1 := rfl
@[simp] theorem qc_one : qc 1 = 0 := rfl

/-- The second window is the next first window (`rfl`). -/
theorem window_shift (n : Nat) : (arctanTwo n).2 = (arctanTwo (n + 1)).1 := rfl

/-- The defining equation for `pc (n+2)`. -/
theorem pc_def (n : Nat) :
    pc (n + 2) =
      Q'.divPos (qc (n + 1) + -(Q'.ofNat n * pc n)) (Q'.ofNat (n + 2))
        (Q'.ofNat_succ_pos (n + 1)) := rfl

/-- The defining equation for `qc (n+2)`. -/
theorem qc_def (n : Nat) :
    qc (n + 2) =
      Q'.divPos (-(pc (n + 1)) + -(Q'.ofNat n * qc n)) (Q'.ofNat (n + 2))
        (Q'.ofNat_succ_pos (n + 1)) := rfl

/-! ### Small `Q'` glue: additive cancellation `(a + -b) + b ≃ a` -/

/-- `(a + -b) + b ≃ a`. -/
theorem addNegCancelL (a b : Q') : ((a + -b) + b).eqv a := by
  refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv a (-b) b) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left a (-b + b) 0 (Q'.neg_add_self_eqv b)) ?_
  exact Q'.eqv_of_eq (Q'.add_zero' a)

/-- `d · divPos p d hd ≃ p` (the commuted defining identity). -/
theorem mul_divPos_eqv (p d : Q') (hd : (0 : Q') < d) :
    (d * Q'.divPos p d hd).eqv p :=
  Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv d (Q'.divPos p d hd)) (Q'.divPos_mul_eqv p d hd)

/-! ### The recurrence-discharge lemmas (the `SeriesData` REC fields) -/

/-- `hp0`: `pc 1 ≃ qc 0`. -/
theorem hp0 : (pc 1).eqv (qc 0) := by decide

/-- `hp0init`: `pc 0 ≃ 0`. -/
theorem hp0init : (pc 0).eqv 0 := by decide

/-- `hq0`: `qc 1 ≃ -(pc 0)`. -/
theorem hq0 : (qc 1).eqv (-(pc 0)) := by decide

/-- `hp`: `(n+2)·p_{n+2} + n·pₙ ≃ q_{n+1}`. -/
theorem pc_rec (n : Nat) :
    (Q'.ofNat (n + 2) * pc (n + 2) + Q'.ofNat n * pc n).eqv (qc (n + 1)) := by
  have hd : (0 : Q') < Q'.ofNat (n + 2) := Q'.ofNat_succ_pos (n + 1)
  have key : (Q'.ofNat (n + 2) * pc (n + 2)).eqv
      (qc (n + 1) + -(Q'.ofNat n * pc n)) := by
    rw [pc_def n]
    exact mul_divPos_eqv (qc (n + 1) + -(Q'.ofNat n * pc n)) (Q'.ofNat (n + 2)) hd
  have hstep :
      (Q'.ofNat (n + 2) * pc (n + 2) + Q'.ofNat n * pc n).eqv
        ((qc (n + 1) + -(Q'.ofNat n * pc n)) + Q'.ofNat n * pc n) :=
    Q'.add_eqv_congr' key (Q'.eqv_refl (Q'.ofNat n * pc n))
  exact Q'.eqv_trans _ _ _ hstep (addNegCancelL (qc (n + 1)) (Q'.ofNat n * pc n))

/-- `hq`: `(n+2)·q_{n+2} + n·qₙ ≃ -(p_{n+1})`. -/
theorem qc_rec (n : Nat) :
    (Q'.ofNat (n + 2) * qc (n + 2) + Q'.ofNat n * qc n).eqv (-(pc (n + 1))) := by
  have hd : (0 : Q') < Q'.ofNat (n + 2) := Q'.ofNat_succ_pos (n + 1)
  have key : (Q'.ofNat (n + 2) * qc (n + 2)).eqv
      (-(pc (n + 1)) + -(Q'.ofNat n * qc n)) := by
    rw [qc_def n]
    exact mul_divPos_eqv (-(pc (n + 1)) + -(Q'.ofNat n * qc n)) (Q'.ofNat (n + 2)) hd
  have hstep :
      (Q'.ofNat (n + 2) * qc (n + 2) + Q'.ofNat n * qc n).eqv
        ((-(pc (n + 1)) + -(Q'.ofNat n * qc n)) + Q'.ofNat n * qc n) :=
    Q'.add_eqv_congr' key (Q'.eqv_refl (Q'.ofNat n * qc n))
  exact Q'.eqv_trans _ _ _ hstep (addNegCancelL (-(pc (n + 1))) (Q'.ofNat n * qc n))

/-! ## Layer C — the uniform coefficient bound `|pₙ|,|qₙ| ≤ 1` -/

open YMGap.Continuum.TsumDeriv (abs_add_le)
open YMGap.Continuum.TsumDeriv.Q' (abs_neg abs_mul_le)

/-- `|ofNat n| = ofNat n`. -/
theorem abs_ofNat (n : Nat) : Q'.abs (Q'.ofNat n) = Q'.ofNat n := by
  unfold Q'.abs
  rw [if_pos (ExpNeg.ofNat_nonneg' n)]

/-- **The quotient stays in the unit ball.**  If `|num| ≤ d` then
`|num / d| ≤ 1` (both sides of the two-sided quotient bound). -/
theorem abs_divPos_le_one {num d : Q'} (hd : (0 : Q') < d)
    (h : Q'.abs num ≤ d) : Q'.abs (Q'.divPos num d hd) ≤ 1 := by
  refine Q'.abs_le ?_ ?_
  · -- -(1) ≤ divPos num d hd
    have hnd : -num ≤ d := Q'.le_trans' _ _ _ (Q'.neg_le_abs num) h
    have hdn : -d ≤ num :=
      Q'.le_trans' _ _ _ (Q'.neg_le_neg hnd) (Q'.le_of_eqv (Q'.neg_neg_eqv num))
    have he : ((-(1 : Q')) * d).eqv (-d) :=
      Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 d) (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv d))
    have hmul : (-(1 : Q')) * d ≤ num := Q'.le_trans' _ _ _ (Q'.le_of_eqv he) hdn
    exact Q'.le_divPos_of_mul_le num d hd hmul
  · -- divPos num d hd ≤ 1
    have hnd : num ≤ d := Q'.le_trans' _ _ _ (Q'.le_abs_self num) h
    have hmul : num ≤ (1 : Q') * d :=
      Q'.le_trans' _ _ _ hnd (Q'.ge_of_eqv (Q'.one_mul_eqv d))
    exact Q'.divPos_le_of_le_mul num d hd hmul

/-- **Numerator bound.**  With `|c|,|b| ≤ 1`, the recurrence numerator
`c − n·b` has magnitude `≤ n+2`. -/
theorem numAbs_le (c b : Q') (n : Nat) (hc : Q'.abs c ≤ 1) (hb : Q'.abs b ≤ 1) :
    Q'.abs (c + -(Q'.ofNat n * b)) ≤ Q'.ofNat (n + 2) := by
  -- |c + -(n·b)| ≤ |c| + |n·b|
  have htri : Q'.abs (c + -(Q'.ofNat n * b)) ≤ Q'.abs c + Q'.abs (Q'.ofNat n * b) := by
    refine Q'.le_trans' _ _ _ (abs_add_le c (-(Q'.ofNat n * b))) ?_
    exact Q'.add_le_add_left _ _ _ (Q'.le_of_eqv (abs_neg (Q'.ofNat n * b)))
  -- |n·b| ≤ n
  have hmul : Q'.abs (Q'.ofNat n * b) ≤ Q'.ofNat n := by
    refine Q'.le_trans' _ _ _ (abs_mul_le (Q'.ofNat n) b) ?_
    rw [abs_ofNat n]
    refine Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hb (ExpNeg.ofNat_nonneg' n)) ?_
    exact Q'.le_of_eqv (Q'.mul_one_eqv (Q'.ofNat n))
  have hsum : Q'.abs c + Q'.abs (Q'.ofNat n * b) ≤ (1 : Q') + Q'.ofNat n :=
    Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ _ hc) (Q'.add_le_add_left _ _ _ hmul)
  have hlast : (1 : Q') + Q'.ofNat n ≤ Q'.ofNat (n + 2) := by
    have he : ((1 : Q') + Q'.ofNat n).eqv (Q'.ofNat (n + 1)) := by
      refine Q'.eqv_trans _ _ _ (Q'.add_comm_eqv 1 (Q'.ofNat n)) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left (Q'.ofNat n) 1 (Q'.ofNat 1) (by decide)) ?_
      exact Q'.eqv_symm (Q'.ofNat_add_eqv n 1)
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv he) ?_
    exact CReal.ofNat_le_ofNat (by omega)
  exact Q'.le_trans' _ _ _ htri (Q'.le_trans' _ _ _ hsum hlast)

/-- **The uniform coefficient bound, paired for two-step induction.**
`|pₙ|,|qₙ| ≤ 1` and `|p_{n+1}|,|q_{n+1}| ≤ 1`. -/
theorem coeff_pair_le_one : ∀ n,
    (Q'.abs (pc n) ≤ 1 ∧ Q'.abs (qc n) ≤ 1) ∧
    (Q'.abs (pc (n + 1)) ≤ 1 ∧ Q'.abs (qc (n + 1)) ≤ 1)
  | 0 => by refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> decide
  | k + 1 => by
    obtain ⟨⟨hpk, hqk⟩, ⟨hpk1, hqk1⟩⟩ := coeff_pair_le_one k
    refine ⟨⟨hpk1, hqk1⟩, ?_, ?_⟩
    · rw [pc_def k]
      exact abs_divPos_le_one _ (numAbs_le (qc (k + 1)) (pc k) k hqk1 hpk)
    · rw [qc_def k]
      refine abs_divPos_le_one _ (numAbs_le (-(pc (k + 1))) (qc k) k ?_ hqk)
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (abs_neg (pc (k + 1)))) hpk1

/-- `|pₙ| ≤ 1`. -/
theorem coeff_pc_le_one (n : Nat) : Q'.abs (pc n) ≤ 1 := (coeff_pair_le_one n).1.1
/-- `|qₙ| ≤ 1`. -/
theorem coeff_qc_le_one (n : Nat) : Q'.abs (qc n) ≤ 1 := (coeff_pair_le_one n).1.2

/-! ## Layer C — the geometric `(1/2)ⁿ` majorant and the `CReal` limits -/

/-- The base value `1/5`. -/
def xv : Q' := Q'.mkPos 1 5 (by decide)

/-- `|1/5| ≤ 1/2`. -/
theorem abs_xv_le_half : Q'.abs xv ≤ HalfPow.half := by decide

/-- `|xⁿ| ≤ (1/2)ⁿ` for `x = 1/5`. -/
theorem abs_qpow_le : ∀ j, Q'.abs (qpow xv j) ≤ HalfPow.half ^ j
  | 0 => by
    show Q'.abs (qpow xv 0) ≤ HalfPow.half ^ 0
    exact Q'.abs_le (by decide) (by decide)
  | j + 1 => by
    show Q'.abs (xv * qpow xv j) ≤ HalfPow.half * HalfPow.half ^ j
    refine Q'.le_trans' _ _ _ (abs_mul_le xv (qpow xv j)) ?_
    exact Q'.mul_le_mul_of_nonneg abs_xv_le_half (abs_qpow_le j)
      HalfPow.half_nonneg (Q'.abs_nonneg _)

/-- Termwise majorant: `|aⱼ·xʲ| ≤ (1/2)ʲ` when `|aⱼ| ≤ 1`. -/
theorem term_maj_le (a : Nat → Q') (ha : ∀ j, Q'.abs (a j) ≤ 1) (j : Nat) :
    Q'.abs (a j * qpow xv j) ≤ HalfPow.half ^ j :=
  Q'.le_trans' _ _ _ (TrigBound.abs_mul_le_of_abs_le_one (ha j)) (abs_qpow_le j)

/-- The magnitude majorant of the block `[n, n+d)`: `Σ_{j<d} (1/2)^{n+j}`. -/
def majBlock (n : Nat) : Nat → Q'
  | 0 => 0
  | d + 1 => majBlock n d + HalfPow.half ^ (n + d)

/-- `(1/2)^{n+j} ≃ (1/2)ⁿ · (1/2)ʲ`. -/
theorem pow_add_split (q : Q') (n : Nat) : ∀ j, (q ^ (n + j)).eqv (q ^ n * q ^ j)
  | 0 => Q'.eqv_symm (Q'.mul_one_eqv (q ^ n))
  | j + 1 => by
    show (q * q ^ (n + j)).eqv (q ^ n * (q * q ^ j))
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left q (q ^ (n + j)) (q ^ n * q ^ j) (pow_add_split q n j)) ?_
    exact mulSwap q (q ^ n) (q ^ j)

theorem majBlock_eq_finSum (n : Nat) :
    ∀ d, majBlock n d = RationalTail.finSum (fun j => HalfPow.half ^ (n + j)) d
  | 0 => rfl
  | d + 1 => by
    show majBlock n d + HalfPow.half ^ (n + d)
        = RationalTail.finSum (fun j => HalfPow.half ^ (n + j)) d + HalfPow.half ^ (n + d)
    rw [majBlock_eq_finSum n d]

/-- **Geometric block closure.**  `majBlock n d ≤ H` whenever `H` closes the
one-step recurrence `(1/2)ⁿ + (1/2)·H ≤ H`. -/
theorem majBlock_le (n : Nat) (H : Q') (hH : (0 : Q') ≤ H)
    (hrec : HalfPow.half ^ n + HalfPow.half * H ≤ H) (d : Nat) :
    majBlock n d ≤ H := by
  rw [majBlock_eq_finSum]
  refine Q'.le_trans' _ _ _
    (ExpNeg.finSum_le_finSum_of_termwise (fun j => HalfPow.half ^ (n + j))
      (fun j => HalfPow.half ^ n * HalfPow.half ^ j)
      (fun j => Q'.le_of_eqv (pow_add_split HalfPow.half n j)) d) ?_
  exact RationalTail.geometric_tail_closure (HalfPow.half ^ n) HalfPow.half H
    HalfPow.half_nonneg hH hrec d

/-! ### Two-sided block bounds on the signed partial sums -/

/-- `series a xv (n+d) ≤ series a xv n + majBlock n d`. -/
theorem block_upper (a : Nat → Q') (ha : ∀ j, Q'.abs (a j) ≤ 1) (n : Nat) :
    ∀ d, series a xv (n + d) ≤ series a xv n + majBlock n d
  | 0 => Q'.add_le_self_of_nonneg _ _ (Q'.le_refl' 0)
  | d + 1 => by
    have ih := block_upper a ha n d
    show series a xv (n + d) + a (n + d) * qpow xv (n + d)
        ≤ series a xv n + (majBlock n d + HalfPow.half ^ (n + d))
    have ht : a (n + d) * qpow xv (n + d) ≤ HalfPow.half ^ (n + d) :=
      Q'.le_trans' _ _ _ (Q'.le_abs_self _) (term_maj_le a ha (n + d))
    exact Q'.le_trans' _ _ _
      (Q'.add_le_add_left _ _ _ ht)
      (Q'.le_trans' _ _ _
        (Q'.add_le_add_right _ _ _ ih)
        (Q'.le_of_eqv (Q'.add_assoc_eqv (series a xv n) (majBlock n d)
          (HalfPow.half ^ (n + d)))))

/-- `series a xv n ≤ series a xv (n+d) + majBlock n d`. -/
theorem block_lower (a : Nat → Q') (ha : ∀ j, Q'.abs (a j) ≤ 1) (n : Nat) :
    ∀ d, series a xv n ≤ series a xv (n + d) + majBlock n d
  | 0 => Q'.add_le_self_of_nonneg _ _ (Q'.le_refl' 0)
  | d + 1 => by
    have ih := block_lower a ha n d
    have hneg : -(a (n + d) * qpow xv (n + d)) ≤ HalfPow.half ^ (n + d) :=
      Q'.le_trans' _ _ _ (Q'.neg_le_abs _) (term_maj_le a ha (n + d))
    have hnn : (0 : Q') ≤ (a (n + d) * qpow xv (n + d)) + HalfPow.half ^ (n + d) := by
      refine Q'.le_trans' _ _ _
        (Q'.ge_of_eqv (Q'.neg_add_self_eqv (a (n + d) * qpow xv (n + d)))) ?_
      refine Q'.le_trans' _ _ _
        (Q'.add_le_add_right _ _ (a (n + d) * qpow xv (n + d)) hneg) ?_
      exact Q'.le_of_eqv (Q'.add_comm_eqv (HalfPow.half ^ (n + d))
        (a (n + d) * qpow xv (n + d)))
    show series a xv n
        ≤ (series a xv (n + d) + a (n + d) * qpow xv (n + d))
          + (majBlock n d + HalfPow.half ^ (n + d))
    refine Q'.le_trans' _ _ _ ih ?_
    exact Q'.le_trans' _ _ _
      (Q'.add_le_self_of_nonneg (series a xv (n + d) + majBlock n d) _ hnn)
      (Q'.le_of_eqv (Q'.add_swap_inner (series a xv (n + d)) (majBlock n d)
        (a (n + d) * qpow xv (n + d)) (HalfPow.half ^ (n + d))))

/-- **The `CReal` limit of the majorized power series.**  Approximations are the
signed partial sums `series a xv`; the geometric Cauchy modulus is
`N = (½ε).den`. -/
def limCReal (a : Nat → Q') (ha : ∀ j, Q'.abs (a j) ≤ 1) : CReal where
  approx := series a xv
  cauchy := by
    intro ε hε
    have hhe : (0 : Q') < HalfPow.half * ε := ExpNeg.half_mul_pos ε hε
    refine ⟨(HalfPow.half * ε).den, fun m n hm hn => ?_⟩
    have dir : ∀ k l : Nat, (HalfPow.half * ε).den ≤ k → k ≤ l →
        series a xv l ≤ series a xv k + ε ∧ series a xv k ≤ series a xv l + ε := by
      intro k l hk hkl
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkl
      have hmod : HalfPow.half ^ k ≤ HalfPow.half * ε := by
        obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le hk
        rw [he]
        exact Q'.le_trans' _ _ _ (ExpNeg.pow_half_antitone (HalfPow.half * ε).den e)
          (HalfPow.pow_half_le (HalfPow.half * ε) hhe)
      have hrec : HalfPow.half ^ k + HalfPow.half * ε ≤ ε := by
        refine Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ _ hmod) ?_
        exact Q'.le_of_eqv (ExpNeg.two_halves ε)
      have htail : majBlock k d ≤ ε := majBlock_le k ε (Q'.le_of_lt hε) hrec d
      exact ⟨Q'.le_trans' _ _ _ (block_upper a ha k d)
               (Q'.add_le_add_left _ _ _ htail),
             Q'.le_trans' _ _ _ (block_lower a ha k d)
               (Q'.add_le_add_left _ _ _ htail)⟩
    rcases Nat.le_total m n with hmn | hnm
    · exact ⟨(dir m n hm hmn).2, (dir m n hm hmn).1⟩
    · exact ⟨(dir n m hn hnm).1, (dir n m hn hnm).2⟩

@[simp] theorem limCReal_approx (a : Nat → Q') (ha : ∀ j, Q'.abs (a j) ≤ 1) (N : Nat) :
    (limCReal a ha).approx N = series a xv N := rfl

/-- The genuine sine value `sin(arctan(1/5))`. -/
def sval : CReal := limCReal pc coeff_pc_le_one
/-- The genuine cosine value `cos(arctan(1/5))`. -/
def cval : CReal := limCReal qc coeff_qc_le_one

/-- Every partial sum has magnitude `< 2` (geometric closure at `n = 0`). -/
theorem abs_series_le_two (a : Nat → Q') (ha : ∀ j, Q'.abs (a j) ≤ 1) (n : Nat) :
    Q'.abs (series a xv n) ≤ (2 : Q') := by
  have hb : majBlock 0 n ≤ (2 : Q') := by
    refine majBlock_le 0 2 (by decide) ?_ n
    show HalfPow.half ^ 0 + HalfPow.half * (2 : Q') ≤ (2 : Q')
    decide
  have hu : series a xv (0 + n) ≤ series a xv 0 + majBlock 0 n := block_upper a ha 0 n
  have hl : series a xv 0 ≤ series a xv (0 + n) + majBlock 0 n := block_lower a ha 0 n
  rw [Nat.zero_add] at hu hl
  have h0 : series a xv 0 = 0 := rfl
  rw [h0] at hu hl
  refine Q'.abs_le ?_ ?_
  · -- -(2) ≤ series
    have hns : -(series a xv n) ≤ majBlock 0 n := by
      refine Q'.le_trans' _ _ _
        (Q'.ge_of_eqv (Q'.eqv_of_eq (Q'.add_zero' (-(series a xv n))))) ?_
      refine Q'.le_trans' _ _ _
        (Q'.add_le_add_left (-(series a xv n)) 0 (series a xv n + majBlock 0 n) hl) ?_
      refine Q'.le_of_eqv ?_
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_symm (Q'.add_assoc_eqv (-(series a xv n)) (series a xv n) (majBlock 0 n))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ 0 (majBlock 0 n) (Q'.neg_add_self_eqv (series a xv n))) ?_
      exact Q'.eqv_of_eq (Q'.zero_add' (majBlock 0 n))
    have hns2 : -(series a xv n) ≤ (2 : Q') := Q'.le_trans' _ _ _ hns hb
    exact Q'.le_trans' _ _ _ (Q'.neg_le_neg hns2)
      (Q'.le_of_eqv (Q'.neg_neg_eqv (series a xv n)))
  · -- series ≤ 2
    refine Q'.le_trans' _ _ _ hu ?_
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.eqv_of_eq (Q'.zero_add' (majBlock 0 n)))) hb

/-! ## Layer D — assemble `SeriesData (1/5)` and close the tangent link -/

/-- **The genuine arctan(1/5) series data.**  Every REC recurrence is discharged
by `divPos_mul_eqv`, both convergence witnesses collapse to `convergesTo_self`,
and the cosine/`x` bound is `B = 2`.  This upgrades the non-vacuous
`seriesData_zero` scaffold to the actual arctan model. -/
def arctanSeriesData : SeriesData xv where
  p := pc
  q := qc
  cval := cval
  sval := sval
  B := 2
  hB := by decide
  hxB := by decide
  hcB := fun n => abs_series_le_two qc coeff_qc_le_one n
  hsval := CReal.convergesTo_self sval
  hcval := CReal.convergesTo_self cval
  hp0 := hp0
  hp := pc_rec
  hq0 := hq0
  hq := qc_rec
  hp0init := hp0init

/-- **The tangent link at `1/5`, closed.**  `sin(arctan(1/5)) ≃ (1/5)·cos(arctan(1/5))`
— the genuine `CReal` statement, from the assembled arctan series data. -/
theorem tanLink_arctan_fifth :
    TanLink xv (tanArctanModel_of_data arctanSeriesData).cval
      (tanArctanModel_of_data arctanSeriesData).sval :=
  tanLink_of_data arctanSeriesData

end YMGap.Constructive.QDivArctanSeries

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Constructive.QDivArctanSeries.pc_rec
#print axioms YMGap.Constructive.QDivArctanSeries.qc_rec
#print axioms YMGap.Constructive.QDivArctanSeries.hp0
#print axioms YMGap.Constructive.QDivArctanSeries.hq0
#print axioms YMGap.Constructive.QDivArctanSeries.hp0init
#print axioms YMGap.Constructive.QDivArctanSeries.abs_divPos_le_one
#print axioms YMGap.Constructive.QDivArctanSeries.numAbs_le
#print axioms YMGap.Constructive.QDivArctanSeries.coeff_pc_le_one
#print axioms YMGap.Constructive.QDivArctanSeries.coeff_qc_le_one
#print axioms YMGap.Constructive.QDivArctanSeries.abs_qpow_le
#print axioms YMGap.Constructive.QDivArctanSeries.majBlock_le
#print axioms YMGap.Constructive.QDivArctanSeries.block_upper
#print axioms YMGap.Constructive.QDivArctanSeries.block_lower
#print axioms YMGap.Constructive.QDivArctanSeries.abs_series_le_two
#print axioms YMGap.Constructive.QDivArctanSeries.arctanSeriesData
#print axioms YMGap.Constructive.QDivArctanSeries.tanLink_arctan_fifth
