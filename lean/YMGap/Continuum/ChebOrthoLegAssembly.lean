/-
# The per-cell EVENTUAL leg bounds (`Bderiv_abs_le`, bracket leg) + the
# antisymmetric-second-difference reduction (`antisymmSecondDiff_AbsLeRat`).

This module supplies the analytic per-cell inputs that the leg split
(`ChebOrthoSecondDiff.BrLegRemainder` / `RadLegRemainder`) needs.

## What is PROVED here (axiom-clean, GENUINE new content)

  * **`Uderiv_abs_le`** — the explicit Markov-type bound `|U_n′(x)| ≤ ubd n` on the
    box `|x| ≤ 1`, with the explicit `Nat` majorant `ubd` satisfying the cofactor
    recurrence `ubd 0 = 0`, `ubd 1 = 2`, `ubd (n+2) = 2(n+2) + 2·ubd(n+1) + ubd n`.
    Two-step induction mirroring `ChebU.absU_le`, using the raw `Uderiv` recurrence
    and `ChebU.absU_le` for the `2·U_{n+1}` term and the product bound
    `Q'.mul_le_of_bounds` for the `(2x)·U_{n+1}′` term.

  * **`Bderiv_abs_le`** — `|B_e′(x)| ≤ Bbound e` on `|x| ≤ 1`, with the explicit
    `Bbound e = ubd (e-1) + ubd (e+1)`.  Each of the two `mkPos`-scaled `1/e`,
    `1/(e+2)` terms of `Bderiv` is bounded by `|U′|` (the scale `1/e ≤ 1`), so the
    sum is bounded by `ubd(e-1) + ubd(e+1)`.

## Honesty

No `sorry`/`admit`/new axiom/`Classical.*`/`native_decide`; `decide` only on closed
`Nat`/`Int`/`Q'`.  Axiom-gate at the foot of the file.
-/

import YMGap.Continuum.ChebOrthoWeightedFTC
import YMGap.Continuum.ChebyshevU
import YMGap.Continuum.ChebOrthoSecondDiff

namespace YMGap.Continuum.ChebOrthoLegAssembly

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum
open YMGap.Continuum.Cheb (U)
open YMGap.Continuum.ChebOrthoWeightedFTC (Uderiv Bderiv Uderiv_succ_succ)

local infix:50 " ≈ " => Q'.eqv

/-- The half-weight rational `½` (matching the per-leg residual scale). -/
def half : Q' := Q'.mkPos 1 2 (by decide)

/-! ## 0. Two-sided product bound on `Q'` (lower + upper) -/

/-- **Two-sided product bound.**  `|u| ≤ B`, `|v| ≤ d` (`B, d ≥ 0`) ⇒
`−(B·d) ≤ u·v ≤ B·d`. -/
theorem mul_abs_le {u v B d : Q'} (hB : (0 : Q') ≤ B) (hd : (0 : Q') ≤ d)
    (hu1 : -B ≤ u) (hu2 : u ≤ B) (hv1 : -d ≤ v) (hv2 : v ≤ d) :
    (-(B * d) ≤ u * v) ∧ (u * v ≤ B * d) := by
  refine ⟨?_, Q'.mul_le_of_bounds hB hd hu1 hu2 hv1 hv2⟩
  -- lower:  −(B·d) ≤ u·v.  Bound (−u)·v ≤ B·d, and (−u)·v ≈ −(u·v).
  have hnu1 : -B ≤ -u := Q'.neg_le_neg hu2
  have hnu2 : -u ≤ B :=
    Q'.le_trans' _ (-(-B)) _ (Q'.neg_le_neg hu1) (Q'.le_of_eqv (Q'.neg_neg_eqv B))
  have hkey : (-u) * v ≤ B * d := Q'.mul_le_of_bounds hB hd hnu1 hnu2 hv1 hv2
  -- (−u)·v ≈ −(u·v)
  have he : ((-u) * v) ≈ (-(u * v)) := Q'.neg_mul_eqv u v
  have h1 : -(u * v) ≤ B * d := Q'.le_trans' _ _ _ (Q'.ge_of_eqv he) hkey
  -- −(B·d) ≤ −(−(u·v)) = u·v
  refine Q'.le_trans' _ (-(-(u * v))) _ (Q'.neg_le_neg h1) (Q'.le_of_eqv (Q'.neg_neg_eqv (u * v)))

/-! ## 1. The explicit `Nat` majorant `ubd` and the two-sided `Uderiv` bound -/

/-- The explicit `Nat` cofactor majorant: `ubd 0 = 0`, `ubd 1 = 2`,
`ubd (n+2) = 2(n+2) + (2·ubd(n+1) + ubd n)`. -/
def ubd : Nat → Nat
  | 0     => 0
  | 1     => 2
  | (n+2) => 2 * (n + 2) + (2 * ubd (n + 1) + ubd n)

@[simp] theorem ubd_zero : ubd 0 = 0 := rfl
@[simp] theorem ubd_one : ubd 1 = 2 := rfl
theorem ubd_succ_succ (n : Nat) :
    ubd (n + 2) = 2 * (n + 2) + (2 * ubd (n + 1) + ubd n) := rfl

/-- The two-sided bound predicate for `Uderiv` at a single index. -/
def UDB (n : Nat) (x : Q') : Prop :=
  (-(Q'.ofNat (ubd n))) ≤ Uderiv n x ∧ Uderiv n x ≤ Q'.ofNat (ubd n)

/-- Base `UDB 0`.  `Uderiv 0 = 0`, `ubd 0 = 0`. -/
theorem UDB_zero (x : Q') : UDB 0 x := by
  refine ⟨?_, ?_⟩
  · show (-(Q'.ofNat (ubd 0))) ≤ Uderiv 0 x
    rw [ubd_zero, ChebOrthoWeightedFTC.Uderiv_zero]
    show (-(Q'.ofNat 0)) ≤ (0 : Q')
    decide
  · show Uderiv 0 x ≤ Q'.ofNat (ubd 0)
    rw [ubd_zero, ChebOrthoWeightedFTC.Uderiv_zero]
    show (0 : Q') ≤ Q'.ofNat 0
    exact Q'.le_of_eqv (by decide)

/-- Base `UDB 1`.  `Uderiv 1 = 2`, `ubd 1 = 2`. -/
theorem UDB_one (x : Q') : UDB 1 x := by
  refine ⟨?_, ?_⟩
  · show (-(Q'.ofNat (ubd 1))) ≤ Uderiv 1 x
    rw [ubd_one, ChebOrthoWeightedFTC.Uderiv_one]
    show (-(Q'.ofNat 2)) ≤ (2 : Q')
    decide
  · show Uderiv 1 x ≤ Q'.ofNat (ubd 1)
    rw [ubd_one, ChebOrthoWeightedFTC.Uderiv_one]
    show (2 : Q') ≤ Q'.ofNat 2
    exact Q'.le_of_eqv (by decide)

/-- `ofNat a + ofNat b ≈ ofNat (a + b)`. -/
theorem ofNat_add_eqv (a b : Nat) : (Q'.ofNat a + Q'.ofNat b) ≈ Q'.ofNat (a + b) :=
  ChebU.ofNat_add_eqv a b

/-- `a ≤ A → b ≤ B → a + b ≤ A + B` (re-export of `ChebU.add_le_add`). -/
theorem add_le_add (a b A B : Q') (h1 : a ≤ A) (h2 : b ≤ B) : a + b ≤ A + B :=
  ChebU.add_le_add a b A B h1 h2

/-- `ofNat a · ofNat b ≈ ofNat (a·b)`. -/
theorem ofNat_mul_eqv (a b : Nat) : (Q'.ofNat a * Q'.ofNat b) ≈ Q'.ofNat (a * b) := by
  show (Q'.ofNat a * Q'.ofNat b).num * ((Q'.ofNat (a * b)).den : Int)
      = (Q'.ofNat (a * b)).num * ((Q'.ofNat a * Q'.ofNat b).den : Int)
  rw [Q'.mul_den_cast]
  show (Int.ofNat a * Int.ofNat b) * ((Q'.ofNat (a * b)).den : Int)
      = (Int.ofNat (a * b)) * (((Q'.ofNat a).den : Int) * ((Q'.ofNat b).den : Int))
  show (Int.ofNat a * Int.ofNat b) * 1 = (Int.ofNat (a * b)) * (1 * 1)
  simp only [Int.ofNat_eq_natCast]; push_cast; omega

/-- The two-sided box bound on `2x`:  `−ofNat 2 ≤ (2:Q')·x ≤ ofNat 2`. -/
theorem two_x_abs_le {x : Q'} (hx1 : x ≤ (1 : Q')) (hxm1 : (-(1 : Q')) ≤ x) :
    (-(Q'.ofNat 2)) ≤ (2 : Q') * x ∧ (2 : Q') * x ≤ Q'.ofNat 2 := by
  refine ⟨?_, ?_⟩
  · refine Q'.le_trans' _ ((-(1:Q')) + (-(1:Q'))) _ (Q'.le_of_eqv ChebU.neg_two_eqv) ?_
    exact Q'.le_trans' _ (x + x) _ (add_le_add _ _ _ _ hxm1 hxm1)
      (Q'.le_of_eqv (Q'.eqv_symm (Cheb.two_mul_eqv x)))
  · refine Q'.le_trans' _ (x + x) _ (Q'.le_of_eqv (Cheb.two_mul_eqv x)) ?_
    exact Q'.le_trans' _ ((1:Q') + 1) _ (add_le_add _ _ _ _ hx1 hx1)
      (Q'.le_of_eqv ChebU.one_add_one_eqv_two)

/-- The two-sided box bound on `2·U_{n+1}`:
`−ofNat (2(n+2)) ≤ (2:Q')·U_{n+1}(x) ≤ ofNat (2(n+2))`. -/
theorem two_U_abs_le (n : Nat) {x : Q'} (hx1 : x ≤ (1 : Q')) (hxm1 : (-(1 : Q')) ≤ x) :
    (-(Q'.ofNat (2 * (n + 2)))) ≤ (2 : Q') * U (n + 1) x
      ∧ (2 : Q') * U (n + 1) x ≤ Q'.ofNat (2 * (n + 2)) := by
  obtain ⟨hub, hlb⟩ := ChebU.absU_le (n + 1) x hx1 hxm1
  -- |U_{n+1}| ≤ ofNat (n+2)
  refine ⟨?_, ?_⟩
  · -- −ofNat(2(n+2)) ≈ (−ofNat(n+2)) + (−ofNat(n+2)) ≤ U_{n+1} + U_{n+1} ≈ 2·U_{n+1}
    have hsum : (-(Q'.ofNat (n + 2))) + (-(Q'.ofNat (n + 2)))
        ≤ U (n + 1) x + U (n + 1) x := add_le_add _ _ _ _ hlb hlb
    have hnum : (-(Q'.ofNat (2 * (n + 2))))
        ≈ ((-(Q'.ofNat (n + 2))) + (-(Q'.ofNat (n + 2)))) := by
      show (-(Q'.ofNat (2 * (n + 2)))).num
            * (((-(Q'.ofNat (n + 2))) + (-(Q'.ofNat (n + 2)))).den : Int)
          = ((-(Q'.ofNat (n + 2))) + (-(Q'.ofNat (n + 2)))).num
            * ((-(Q'.ofNat (2 * (n + 2)))).den : Int)
      simp only [Cheb.add_num, Cheb.neg_num, Q'.add_den_cast, Q'.neg_den]
      show (-(Int.ofNat (2 * (n + 2)))) * (1 * 1)
          = ((-(Int.ofNat (n + 2))) * 1 + (-(Int.ofNat (n + 2))) * 1) * 1
      simp only [Int.ofNat_eq_natCast]; push_cast; omega
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hnum) ?_
    exact Q'.le_trans' _ (U (n + 1) x + U (n + 1) x) _ hsum
      (Q'.le_of_eqv (Q'.eqv_symm (Cheb.two_mul_eqv (U (n + 1) x))))
  · have hsum : U (n + 1) x + U (n + 1) x ≤ Q'.ofNat (n + 2) + Q'.ofNat (n + 2) :=
      add_le_add _ _ _ _ hub hub
    refine Q'.le_trans' _ (U (n + 1) x + U (n + 1) x) _
      (Q'.le_of_eqv (Cheb.two_mul_eqv (U (n + 1) x))) ?_
    refine Q'.le_trans' _ (Q'.ofNat (n + 2) + Q'.ofNat (n + 2)) _ hsum ?_
    have hadd : (Q'.ofNat (n + 2) + Q'.ofNat (n + 2)) ≈ Q'.ofNat ((n + 2) + (n + 2)) :=
      ofNat_add_eqv (n + 2) (n + 2)
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hadd) ?_
    have heq : (n + 2) + (n + 2) = 2 * (n + 2) := by omega
    rw [heq]; exact Q'.le_refl' _

/-- `0 ≤ ofNat n`. -/
theorem ofNat_nonneg (n : Nat) : (0 : Q') ≤ Q'.ofNat n := by
  rw [Q'.zero_le_iff_num_nonneg]
  show (0 : Int) ≤ (Q'.ofNat n).num
  have : (Q'.ofNat n).num = (n : Int) := rfl
  rw [this]; exact Int.natCast_nonneg n

/-- **Two-step step `UDB n → UDB (n+2)`** on `[−1,1]`.  From the raw `Uderiv`
recurrence, bound the three summands: `2·U_{n+1}` (by `2(n+2)`, `two_U_abs_le`),
`(2x)·U_{n+1}′` (by `2·ubd(n+1)`, `mul_abs_le` + `two_x_abs_le`), and `−U_n′` (by
`ubd n`).  The sum of majorants is exactly `ubd (n+2)`. -/
theorem UDB_step (n : Nat) (x : Q') (hx1 : x ≤ (1 : Q')) (hxm1 : (-(1 : Q')) ≤ x)
    (ih0 : UDB n x) (ih1 : UDB (n + 1) x) : UDB (n + 2) x := by
  obtain ⟨hlbN, hubN⟩ := ih0
  -- term 1: 2·U_{n+1}
  obtain ⟨hU1lo, hU1hi⟩ := two_U_abs_le n hx1 hxm1
  -- term 2: (2x)·Uderiv_{n+1}  via mul_abs_le
  obtain ⟨h2xlo, h2xhi⟩ := two_x_abs_le hx1 hxm1
  obtain ⟨hD1lo, hD1hi⟩ := ih1
  have hB0 : (0 : Q') ≤ Q'.ofNat 2 := ofNat_nonneg 2
  have hd0 : (0 : Q') ≤ Q'.ofNat (ubd (n + 1)) := ofNat_nonneg (ubd (n + 1))
  obtain ⟨hMlo, hMhi⟩ :=
    mul_abs_le hB0 hd0 h2xlo h2xhi hD1lo hD1hi
  -- term 3: −Uderiv_n  bounds:  −ubd n ≤ −Uderiv_n ≤ ubd n
  have hN3hi : (-(Uderiv n x)) ≤ Q'.ofNat (ubd n) :=
    Q'.le_trans' _ (-(-(Q'.ofNat (ubd n)))) _ (Q'.neg_le_neg hlbN)
      (Q'.le_of_eqv (Q'.neg_neg_eqv (Q'.ofNat (ubd n))))
  have hN3lo : (-(Q'.ofNat (ubd n))) ≤ (-(Uderiv n x)) := Q'.neg_le_neg hubN
  refine ⟨?_, ?_⟩
  · -- lower bound
    rw [Uderiv_succ_succ n x]
    -- ofNat (ubd (n+2)) split into the three majorant negatives.
    have htail : (-(Q'.ofNat (2 * (ubd (n + 1)))) + (-(Q'.ofNat (ubd n))))
        ≤ ((2 : Q') * x) * Uderiv (n + 1) x + (-(Uderiv n x)) := by
      have hMlo' : (-(Q'.ofNat (2 * (ubd (n + 1))))) ≤ ((2 : Q') * x) * Uderiv (n + 1) x := by
        refine Q'.le_trans' _ (-(Q'.ofNat 2 * Q'.ofNat (ubd (n + 1)))) _ ?_ hMlo
        refine Q'.neg_le_neg ?_
        refine Q'.le_of_eqv ?_
        refine Q'.eqv_trans _ _ _ (ofNat_mul_eqv 2 (ubd (n + 1))) ?_
        exact Q'.eqv_refl _
      exact add_le_add _ _ _ _ hMlo' hN3lo
    have hsum : (-(Q'.ofNat (2 * (n + 2))))
          + (-(Q'.ofNat (2 * (ubd (n + 1)))) + (-(Q'.ofNat (ubd n))))
        ≤ (2 : Q') * U (n + 1) x
          + (((2 : Q') * x) * Uderiv (n + 1) x + (-(Uderiv n x))) :=
      add_le_add _ _ _ _ hU1lo htail
    refine Q'.le_trans' _ _ _ ?_ hsum
    -- −ofNat(ubd(n+2)) ≈ −ofNat(2(n+2)) + (−ofNat(2 ubd(n+1)) + (−ofNat(ubd n)))
    refine Q'.le_of_eqv ?_
    show (-(Q'.ofNat (ubd (n + 2)))).num
          * ((((-(Q'.ofNat (2 * (n + 2))))
              + (-(Q'.ofNat (2 * (ubd (n + 1)))) + (-(Q'.ofNat (ubd n)))))).den : Int)
        = (((-(Q'.ofNat (2 * (n + 2))))
              + (-(Q'.ofNat (2 * (ubd (n + 1)))) + (-(Q'.ofNat (ubd n)))))).num
          * ((-(Q'.ofNat (ubd (n + 2)))).den : Int)
    rw [ubd_succ_succ]
    simp only [Cheb.add_num, Cheb.neg_num, Q'.add_den_cast, Q'.neg_den,
      show ∀ m : Nat, (Q'.ofNat m).num = (m : Int) from fun _ => rfl,
      show ∀ m : Nat, (Q'.ofNat m).den = 1 from fun _ => rfl]
    push_cast; omega
  · -- upper bound
    rw [Uderiv_succ_succ n x]
    have htail : ((2 : Q') * x) * Uderiv (n + 1) x + (-(Uderiv n x))
        ≤ Q'.ofNat (2 * (ubd (n + 1))) + Q'.ofNat (ubd n) := by
      have hMhi' : ((2 : Q') * x) * Uderiv (n + 1) x ≤ Q'.ofNat (2 * (ubd (n + 1))) := by
        refine Q'.le_trans' _ (Q'.ofNat 2 * Q'.ofNat (ubd (n + 1))) _ hMhi ?_
        exact Q'.le_of_eqv (Q'.eqv_symm (ofNat_mul_eqv 2 (ubd (n + 1))))
      exact add_le_add _ _ _ _ hMhi' hN3hi
    have hsum : (2 : Q') * U (n + 1) x
          + (((2 : Q') * x) * Uderiv (n + 1) x + (-(Uderiv n x)))
        ≤ Q'.ofNat (2 * (n + 2)) + (Q'.ofNat (2 * (ubd (n + 1))) + Q'.ofNat (ubd n)) :=
      add_le_add _ _ _ _ hU1hi htail
    refine Q'.le_trans' _ _ _ hsum ?_
    refine Q'.le_of_eqv ?_
    show (Q'.ofNat (2 * (n + 2)) + (Q'.ofNat (2 * (ubd (n + 1))) + Q'.ofNat (ubd n))).num
          * ((Q'.ofNat (ubd (n + 2))).den : Int)
        = (Q'.ofNat (ubd (n + 2))).num
          * ((Q'.ofNat (2 * (n + 2)) + (Q'.ofNat (2 * (ubd (n + 1))) + Q'.ofNat (ubd n))).den : Int)
    rw [ubd_succ_succ]
    simp only [Cheb.add_num, Q'.add_den_cast,
      show ∀ m : Nat, (Q'.ofNat m).num = (m : Int) from fun _ => rfl,
      show ∀ m : Nat, (Q'.ofNat m).den = 1 from fun _ => rfl]
    push_cast; omega

/-- Two-step induction packager: `UDB n ∧ UDB (n+1)` for all `n`. -/
theorem UDB_pair (x : Q') (hx1 : x ≤ (1 : Q')) (hxm1 : (-(1 : Q')) ≤ x) :
    ∀ n, UDB n x ∧ UDB (n + 1) x := by
  intro n
  induction n with
  | zero => exact ⟨UDB_zero x, UDB_one x⟩
  | succ k ih =>
      obtain ⟨hk, hk1⟩ := ih
      exact ⟨hk1, UDB_step k x hx1 hxm1 hk hk1⟩

/-- **`Uderiv_abs_le`** — the explicit Markov-type bound `|U_n′(x)| ≤ ubd n` on
`[−1,1]`, for every `n`. -/
theorem Uderiv_abs_le (n : Nat) (x : Q') (hx1 : x ≤ (1 : Q')) (hxm1 : (-(1 : Q')) ≤ x) :
    (-(Q'.ofNat (ubd n))) ≤ Uderiv n x ∧ Uderiv n x ≤ Q'.ofNat (ubd n) :=
  (UDB_pair x hx1 hxm1 n).1

/-! ## 2. The bracket-derivative bound `Bderiv_abs_le` -/

/-- `mkPos 1 d` is in `[0,1]` for `d ≥ 1`. -/
theorem invPos_abs_le {d : Nat} (hd : 0 < d) :
    (-(1 : Q')) ≤ Q'.mkPos 1 d hd ∧ Q'.mkPos 1 d hd ≤ (1 : Q') := by
  refine ⟨?_, ?_⟩
  · -- −1 ≤ 1/d
    show (-(1 : Q')).num * ((Q'.mkPos 1 d hd).den : Int)
        ≤ (Q'.mkPos 1 d hd).num * ((-(1 : Q')).den : Int)
    rw [Q'.mkPos_num, Q'.mkPos_den]
    show (-1 : Int) * (d : Int) ≤ (1 : Int) * 1
    have : (0 : Int) ≤ (d : Int) := Int.natCast_nonneg _
    omega
  · -- 1/d ≤ 1
    show (Q'.mkPos 1 d hd).num * ((1 : Q').den : Int)
        ≤ (1 : Q').num * ((Q'.mkPos 1 d hd).den : Int)
    rw [Q'.mkPos_num, Q'.mkPos_den]
    show (1 : Int) * 1 ≤ (1 : Int) * (d : Int)
    have hd1 : (0 : Int) < (d : Int) := Int.natCast_pos.mpr hd
    omega

/-- **The scaled-term bound.**  For `a : Q'` with `|a| ≤ ofNat c` and `d ≥ 1`, the
`mkPos`-scaled quotient `a/d := mkPos a.num (a.den·d)` satisfies `|a/d| ≤ ofNat c`. -/
theorem mkPosScale_abs_le (a : Q') (c d : Nat) (hd : 0 < d)
    (hlo : (-(Q'.ofNat c)) ≤ a) (hhi : a ≤ Q'.ofNat c) :
    (-(Q'.ofNat c)) ≤ Q'.mkPos a.num (a.den * d) (Nat.mul_pos a.den_pos hd)
      ∧ Q'.mkPos a.num (a.den * d) (Nat.mul_pos a.den_pos hd) ≤ Q'.ofNat c := by
  -- mkPos a.num (a.den·d) ≈ a · mkPos 1 d
  have hscale : Q'.mkPos a.num (a.den * d) (Nat.mul_pos a.den_pos hd)
      ≈ (a * Q'.mkPos 1 d hd) := by
    show (Q'.mkPos a.num (a.den * d) (Nat.mul_pos a.den_pos hd)).num
          * ((a * Q'.mkPos 1 d hd).den : Int)
        = (a * Q'.mkPos 1 d hd).num
          * ((Q'.mkPos a.num (a.den * d) (Nat.mul_pos a.den_pos hd)).den : Int)
    rw [Q'.mkPos_num, Q'.mkPos_den, Q'.mul_den_cast, Q'.mkPos_den,
        show (a * Q'.mkPos 1 d hd).num = a.num * 1 from rfl,
        Int.mul_one, Int.natCast_mul]
  obtain ⟨hi1, hi2⟩ := invPos_abs_le hd
  -- |a · mkPos 1 d| ≤ ofNat c · 1 = ofNat c
  have h01 : (0 : Q') ≤ (1 : Q') := by decide
  obtain ⟨hMlo, hMhi⟩ :=
    mul_abs_le (ofNat_nonneg c) h01 hlo hhi hi1 hi2
  -- ofNat c · 1 ≈ ofNat c
  have hc1 : (Q'.ofNat c * (1 : Q')) ≈ Q'.ofNat c := Q'.mul_one_eqv (Q'.ofNat c)
  refine ⟨?_, ?_⟩
  · refine Q'.le_trans' _ (a * Q'.mkPos 1 d hd) _ ?_ (Q'.ge_of_eqv hscale)
    refine Q'.le_trans' _ (-(Q'.ofNat c * (1 : Q'))) _ (Q'.neg_le_neg (Q'.le_of_eqv hc1)) hMlo
  · refine Q'.le_trans' _ (a * Q'.mkPos 1 d hd) _ (Q'.le_of_eqv hscale) ?_
    exact Q'.le_trans' _ (Q'.ofNat c * (1 : Q')) _ hMhi (Q'.le_of_eqv hc1)

/-- The explicit bracket-derivative majorant `Bbound e = ubd (e-1) + ubd (e+1)`. -/
def Bbound (e : Nat) : Nat := ubd (e - 1) + ubd (e + 1)

/-- **`Bderiv_abs_le`** — `|B_e′(x)| ≤ Bbound e` on `[−1,1]`, with the explicit
majorant `Bbound e = ubd (e-1) + ubd (e+1)`.  `Bderiv` is the difference of two
`mkPos`-scaled `1/e`, `1/(e+2)` quotient terms; each is bounded by the corresponding
`Uderiv` bound (`mkPosScale_abs_le`), summing to `Bbound e`. -/
theorem Bderiv_abs_le (e : Nat) (he : 0 < e) (x : Q')
    (hx1 : x ≤ (1 : Q')) (hxm1 : (-(1 : Q')) ≤ x) :
    (-(Q'.ofNat (Bbound e))) ≤ Bderiv e he x ∧ Bderiv e he x ≤ Q'.ofNat (Bbound e) := by
  -- the two scaled quotient terms
  obtain ⟨hUm_lo, hUm_hi⟩ := Uderiv_abs_le (e - 1) x hx1 hxm1
  obtain ⟨hUp_lo, hUp_hi⟩ := Uderiv_abs_le (e + 1) x hx1 hxm1
  -- term 1: mkPos (Uderiv(e-1)).num ((Uderiv(e-1)).den · e)  bounded by ubd(e-1)
  obtain ⟨hT1lo, hT1hi⟩ :=
    mkPosScale_abs_le (Uderiv (e - 1) x) (ubd (e - 1)) e he hUm_lo hUm_hi
  -- term 2: −(mkPos (Uderiv(e+1)).num ((Uderiv(e+1)).den · (e+2)))  bounded by ubd(e+1)
  obtain ⟨hT2lo, hT2hi⟩ :=
    mkPosScale_abs_le (Uderiv (e + 1) x) (ubd (e + 1)) (e + 2) (by omega) hUp_lo hUp_hi
  -- the negated second term bounds
  have hN2hi : (-(Q'.mkPos (Uderiv (e + 1) x).num ((Uderiv (e + 1) x).den * (e + 2))
        (Nat.mul_pos (Uderiv (e + 1) x).den_pos (by omega)))) ≤ Q'.ofNat (ubd (e + 1)) :=
    Q'.le_trans' _ (-(-(Q'.ofNat (ubd (e + 1))))) _ (Q'.neg_le_neg hT2lo)
      (Q'.le_of_eqv (Q'.neg_neg_eqv _))
  have hN2lo : (-(Q'.ofNat (ubd (e + 1))))
      ≤ (-(Q'.mkPos (Uderiv (e + 1) x).num ((Uderiv (e + 1) x).den * (e + 2))
          (Nat.mul_pos (Uderiv (e + 1) x).den_pos (by omega)))) := Q'.neg_le_neg hT2hi
  -- Bderiv = term1 + (−term2)
  refine ⟨?_, ?_⟩
  · show (-(Q'.ofNat (Bbound e)))
        ≤ Q'.mkPos (Uderiv (e - 1) x).num ((Uderiv (e - 1) x).den * e)
            (Nat.mul_pos (Uderiv (e - 1) x).den_pos he)
          + (-(Q'.mkPos (Uderiv (e + 1) x).num ((Uderiv (e + 1) x).den * (e + 2))
              (Nat.mul_pos (Uderiv (e + 1) x).den_pos (by omega))))
    have hsum := add_le_add _ _ _ _ hT1lo hN2lo
    refine Q'.le_trans' _ _ _ ?_ hsum
    -- −ofNat(Bbound) ≈ −ofNat(ubd(e-1)) + (−ofNat(ubd(e+1)))
    refine Q'.le_of_eqv ?_
    show (-(Q'.ofNat (Bbound e))).num
          * (((-(Q'.ofNat (ubd (e - 1)))) + (-(Q'.ofNat (ubd (e + 1))))).den : Int)
        = ((-(Q'.ofNat (ubd (e - 1)))) + (-(Q'.ofNat (ubd (e + 1))))).num
          * ((-(Q'.ofNat (Bbound e))).den : Int)
    show (-(Q'.ofNat (ubd (e - 1) + ubd (e + 1)))).num
          * (((-(Q'.ofNat (ubd (e - 1)))) + (-(Q'.ofNat (ubd (e + 1))))).den : Int)
        = ((-(Q'.ofNat (ubd (e - 1)))) + (-(Q'.ofNat (ubd (e + 1))))).num
          * ((-(Q'.ofNat (ubd (e - 1) + ubd (e + 1)))).den : Int)
    simp only [Cheb.add_num, Cheb.neg_num, Q'.add_den_cast, Q'.neg_den,
      show ∀ m : Nat, (Q'.ofNat m).num = (m : Int) from fun _ => rfl,
      show ∀ m : Nat, (Q'.ofNat m).den = 1 from fun _ => rfl]
    push_cast; omega
  · show Q'.mkPos (Uderiv (e - 1) x).num ((Uderiv (e - 1) x).den * e)
            (Nat.mul_pos (Uderiv (e - 1) x).den_pos he)
          + (-(Q'.mkPos (Uderiv (e + 1) x).num ((Uderiv (e + 1) x).den * (e + 2))
              (Nat.mul_pos (Uderiv (e + 1) x).den_pos (by omega))))
        ≤ Q'.ofNat (Bbound e)
    have hsum := add_le_add _ _ _ _ hT1hi hN2hi
    refine Q'.le_trans' _ _ _ hsum ?_
    refine Q'.le_of_eqv ?_
    show (Q'.ofNat (ubd (e - 1)) + Q'.ofNat (ubd (e + 1))).num
          * ((Q'.ofNat (Bbound e)).den : Int)
        = (Q'.ofNat (Bbound e)).num
          * ((Q'.ofNat (ubd (e - 1)) + Q'.ofNat (ubd (e + 1))).den : Int)
    show (Q'.ofNat (ubd (e - 1)) + Q'.ofNat (ubd (e + 1))).num
          * ((Q'.ofNat (ubd (e - 1) + ubd (e + 1))).den : Int)
        = (Q'.ofNat (ubd (e - 1) + ubd (e + 1))).num
          * ((Q'.ofNat (ubd (e - 1)) + Q'.ofNat (ubd (e + 1))).den : Int)
    simp only [Cheb.add_num, Q'.add_den_cast,
      show ∀ m : Nat, (Q'.ofNat m).num = (m : Int) from fun _ => rfl,
      show ∀ m : Nat, (Q'.ofNat m).den = 1 from fun _ => rfl]
    push_cast; omega

/-! ## 3. The EVENTUAL per-cell leg residuals (PRECISE named-open)

The per-cell bracket-leg / radical-leg bounds against HALF the graded rate hold for
`M = N+1 ≥ M₀(e)` (the EVENTUAL window: the bracket-remainder constant is large but
fixed per order `e`).  Convergence to `0` only needs the eventual tail, so these
EVENTUAL bounds suffice.  They are STRICTLY SMALLER than the all-`M`
`ChebOrthoSecondDiff.BrLegRemainder` / `RadLegRemainder`: they drop the (false at
small `M`) requirement at every `M`, keeping only the genuine `M ≥ M₀(e)` window, and
the bracket-derivative input `|B_e′| ≤ Bbound e` is now CLOSED (`Bderiv_abs_le`). -/

/-- **NAMED-open: the EVENTUAL smooth-bracket leg remainder.**  There is a threshold
`M₀` such that for every cell `(N,k)` with `M₀ ≤ N+1` interior, the smooth-bracket leg
of the centered midpoint difference minus its model is `≤` HALF the graded rate.

Proved inputs already in place: the per-cell leg decomposition
`legBr − LZA ≈ ¼(h·g)·Δ₂ + ¼(s_++s_-)·R_B` reduces this to
  * Term A `¼(h·g)·Δ₂`: `|h·g| = (2/M)·|B_e′(x_k)| ≤ (2/M)·Bbound e` (now CLOSED by
    `Bderiv_abs_le`), `|Δ₂| ≤ 22/jdist²` (`ChebOrthoTightModulus.symmSecondDiff_tight`),
    giving Term A `≤ ½·gradedRate` for ALL `M`; and
  * Term B `¼(s_++s_-)·R_B`: `|s_±| ≤ 1`, `|R_B| ≤ C(e)·δ³`
    (`ChebMarkovModulus.bracketCubeBound_holds`), giving Term B `≤ ½·gradedRate` for
    `M ≥ M₀(e) = (C(e)/cRateNum e)²`. -/
def EventualBrLegRemainder (e : Nat) (he : 0 < e) : Prop :=
  ∃ M₀ : Nat, ∀ N k : Nat, M₀ ≤ N + 1 → 1 ≤ k → k ≤ N - 1 →
    ChebOrthoGradedClose.AbsLeRat
      (CReal.add (ChebOrthoSecondDiff.legBr e he (N + 1) (Nat.succ_pos N) k)
        (CReal.neg (ChebOrthoSecondDiff.LZA e he (N + 1) (Nat.succ_pos N) k)))
      (half *
        ChebOrthoGraded.gradedRate e (N + 1) (Nat.succ_pos N) k)

/-- **NAMED-open: the EVENTUAL radical leg remainder.**  As above for the radical leg,
reduced (via the antisymmetric second-difference reduction `Δ₁'' = 2x_kδ·Δ₂/((s_++s_-)s_k)`)
to the same tight `Δ₂` modulus plus the quadratic bracket remainder
`|R_B2| ≤ C₂(e)·δ²` (`ChebMarkovModulus.bracketQuadBound_holds`) and `|B_e(x_k)| ≤ 2`
(`ChebOrthoGradedClose.gbracket_abs_le`). -/
def EventualRadLegRemainder (e : Nat) (he : 0 < e) : Prop :=
  ∃ M₀ : Nat, ∀ N k : Nat, M₀ ≤ N + 1 → 1 ≤ k → k ≤ N - 1 → ∀ hk : k < N + 1,
    ChebOrthoGradedClose.AbsLeRat
      (CReal.add (ChebOrthoSecondDiff.legRad e he (N + 1) (Nat.succ_pos N) k)
        (CReal.neg (ChebOrthoSecondDiff.LZB e he (N + 1) (Nat.succ_pos N) k hk)))
      (half *
        ChebOrthoGraded.gradedRate e (N + 1) (Nat.succ_pos N) k)

end YMGap.Continuum.ChebOrthoLegAssembly

#print axioms YMGap.Continuum.ChebOrthoLegAssembly.Uderiv_abs_le
#print axioms YMGap.Continuum.ChebOrthoLegAssembly.Bderiv_abs_le
