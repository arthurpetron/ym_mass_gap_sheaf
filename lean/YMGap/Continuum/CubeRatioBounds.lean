/-
Track B / R2 — the **two rational bounds on the self-fusion cube target** that the
matched-retune carrier left as clean named hypotheses, and the resulting
**UNCONDITIONAL carrier inhabitant**.

# What this module closes

The matched-retune carrier carries `ρ` as a constructive real with `ρ³ = R`,
`R = g₁/(2·g₀)` the self-fusion coefficient ratio (`gₛ = bondMovedCoeff N w 2 s`).
Its inhabitation was guarded by two clean NAMED rational hypotheses, `0 < R` and
`R < 1`, deliberately not discharged at the carrier site.  This module discharges
both, purely at the `Q'` level.

## (A) Positivity `0 < R`

`0 < g₀` is the fused-vacuum positivity.  For `0 < g₁` we open the `s = 1` Clebsch
double sum `g₁ ≃ ∑_{a,b≤N} fusionInd a b 1 · (cₐ·c_b)` (`c = coeffW w`) and extract
the single off-diagonal channel `(a,b) = (0,1)`: `fusionOK 0 1 1` holds, the summand
is `c₀·c₁ > 0`, and every other summand is `≥ 0`.  (Needs the index `b = 1` to be in
range, i.e. `1 ≤ N`.)  Then `0 < R` follows from `divPos_pos`.

## (B) Sub-unit bound `R < 1`

`R < 1` is the strict ratio bound `g₁ < 2·g₀`.  The denominator's diagonal collapse
gives `g₀ ≃ D = ∑_{a≤N} cₐ²`.  The numerator's `s = 1` channel is bounded by the
arithmetic-geometric-mean inequality `2·(cₐ·c_b) ≤ cₐ² + c_b²` applied termwise,
followed by a count of the `s = 1` fusion channel: each row `a` has at most two
admissible partners (`b = a±1`) and the vacuum row `a = 0` has exactly one (`b = 1`),
the slack `(2 − count 0)·c₀² = c₀² = 1 > 0` that makes the bound strict:
`g₁ ≃ T1 ≤ 2·D − c₀² < 2·D ≃ 2·g₀`.

## (C) The unconditional carrier

Feeding `0 < R` and `R < 1` to the carrier's inhabitation glue yields
`exists_matchedRetuneP2_unconditional : MatchedRetuneP2 N w hw` with NO ratio
hypotheses (only the structural side condition `1 ≤ N`).

## Honest scope

This discharges the carrier's two named rational ratio hypotheses.  It is NOT a 4D
Yang–Mills mass gap; the continuum/OS frontier is untouched.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'` order/sum algebra (`fsum`/`finSum`), the existing self-fusion collapse
lemmas, and the carrier glue.  Every load-bearing declaration is gated with
`#print axioms`; permitted output is `propext` / `Quot.sound` only.  No `Classical.*`,
no `native_decide`, no `sorry`.
-/

import YMGap.Continuum.MatchedRetuneBridge
import YMGap.Continuum.FusionResidualBound
import YMGap.Continuum.FusionRDFactor
import YMGap.Continuum.FusionQuotientCollapse
import YMGap.Continuum.FusionPositivity
import YMGap.Continuum.BondMovingMoment
import YMGap.Continuum.MovingCutoff
import YMGap.Constructive.SumOfSquares
import YMGap.Constructive.FinSumAlg

namespace YMGap.Continuum.CubeRatioBounds

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.MatchedRetune
open YMGap.Continuum.FusionResidualBound
open YMGap.Continuum.FusionRDFactor
open YMGap.Continuum.FusionQuotientCollapse
open YMGap.Continuum.FusionPositivity
open YMGap.Continuum.BondMovingMoment
open YMGap.Continuum.MovingCutoff

/-! ## 0. Small `Q'` order glue (kept local; the foundation does not export these
in the `Q'` namespace at the import depth this module lives). -/

/-- `a < b → b ≤ c → a < c` on `Q'` (cross-multiplication form). -/
theorem q_lt_of_lt_of_le {a b c : Q'} (h1 : a < b) (h2 : b ≤ c) : a < c :=
  YMGap.Continuum.MatchedRetuneBridge.q_lt_of_lt_of_le h1 h2

/-- Strict positivity transports across `eqv` on the left: `a ≃ b → 0 < b → 0 < a`. -/
theorem pos_of_eqv_of_pos {a b : Q'} (h : a.eqv b) (hb : (0 : Q') < b) : (0 : Q') < a :=
  q_lt_of_lt_of_le hb (Q'.ge_of_eqv h)

/-- Subtracting a strictly positive value strictly decreases: `0 < b → a + -b < a`. -/
theorem sub_lt_self_of_pos {a b : Q'} (hb : (0 : Q') < b) : a + -b < a := by
  have hbnum : (0 : Int) < b.num := CReal.num_pos_of_pos hb
  -- (a + -b).den = a.den * b.den ; (a + -b).num = a.num*b.den + (-b.num)*a.den.
  have hden_pos : 0 < a.den * b.den := Nat.mul_pos (Q'.den_pos a) (Q'.den_pos b)
  have hden_eq : (a + -b).den = a.den * b.den := by
    show (Q'.add a (-b)).denPred + 1 = a.den * b.den
    show (a.den * (-b).den - 1) + 1 = a.den * b.den
    show (a.den * b.den - 1) + 1 = a.den * b.den
    exact Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hden_pos))
  have hnum_eq : (a + -b).num = a.num * (b.den : Int) + (-b.num) * (a.den : Int) := rfl
  show (a + -b).num * (a.den : Int) < a.num * ((a + -b).den : Int)
  rw [hnum_eq, hden_eq]
  show (a.num * (b.den : Int) + (-b.num) * (a.den : Int)) * (a.den : Int)
      < a.num * (((a.den * b.den : Nat) : Int))
  rw [Int.natCast_mul]
  have hL : (a.num * (b.den : Int) + (-b.num) * (a.den : Int)) * (a.den : Int)
      = a.num * ((a.den : Int) * (b.den : Int)) + (-(b.num * (a.den : Int) * (a.den : Int))) := by
    have e1 : (a.num * (b.den : Int) + (-b.num) * (a.den : Int)) * (a.den : Int)
        = a.num * (b.den : Int) * (a.den : Int) + (-b.num) * (a.den : Int) * (a.den : Int) :=
      Int.add_mul _ _ _
    rw [e1]
    have e2 : a.num * (b.den : Int) * (a.den : Int)
        = a.num * ((a.den : Int) * (b.den : Int)) := by
      rw [Int.mul_assoc a.num (b.den : Int) (a.den : Int), Int.mul_comm (b.den : Int) (a.den : Int)]
    have e3 : (-b.num) * (a.den : Int) * (a.den : Int)
        = -(b.num * (a.den : Int) * (a.den : Int)) := by
      rw [Int.neg_mul, Int.neg_mul]
    rw [e2, e3]
  rw [hL]
  have hpos : (0 : Int) < b.num * (a.den : Int) * (a.den : Int) :=
    Int.mul_pos (Int.mul_pos hbnum (by exact_mod_cast Q'.den_pos a))
      (by exact_mod_cast Q'.den_pos a)
  omega

/-- `ofNat 2 · x ≃ x + x`. -/
theorem ofNat_two_mul_eqv (x : Q') : (Q'.ofNat 2 * x).eqv (x + x) := by
  show (Q'.ofNat 2 * x).num * ((x + x).den : Int)
      = (x + x).num * ((Q'.ofNat 2 * x).den : Int)
  -- LHS num = 2 * x.num, den of (x+x) = x.den * x.den ; RHS num = 2*(x.num*x.den), den = 1*x.den.
  have hn : (Q'.ofNat 2 * x).num = (2 : Int) * x.num := rfl
  have hd2 : ((Q'.ofNat 2 * x).den : Int) = (x.den : Int) := by
    show (((Q'.ofNat 2).den * x.den - 1 + 1 : Nat) : Int) = (x.den : Int)
    rw [show (Q'.ofNat 2).den = 1 from rfl, Nat.one_mul,
      Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (Q'.den_pos x)))]
  have hxxn : (x + x).num = x.num * (x.den : Int) + x.num * (x.den : Int) := rfl
  have hxxd : ((x + x).den : Int) = (x.den : Int) * (x.den : Int) := by
    show (((x.den * x.den - 1) + 1 : Nat) : Int) = (x.den : Int) * (x.den : Int)
    rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr
      (Nat.pos_iff_ne_zero.mp (Nat.mul_pos (Q'.den_pos x) (Q'.den_pos x)))), Int.natCast_mul]
  rw [hn, hd2, hxxn, hxxd]
  -- (2*x.num)*(x.den*x.den) = (x.num*x.den + x.num*x.den)*x.den
  rw [Int.add_mul, Int.two_mul, Int.add_mul]
  rw [Int.mul_assoc x.num (x.den : Int) (x.den : Int)]

/-- Cancel a doubling in a strict inequality: `a + a < b + b → a < b`. -/
theorem lt_of_add_self_lt_add_self {a b : Q'} (h : a + a < b + b) : a < b := by
  -- (a+a).num = 2 a.num a.den, (a+a).den = a.den² ; similarly for b.
  have han : (a + a).num = a.num * (a.den : Int) + a.num * (a.den : Int) := rfl
  have hbn : (b + b).num = b.num * (b.den : Int) + b.num * (b.den : Int) := rfl
  have had : ((a + a).den : Int) = (a.den : Int) * (a.den : Int) := by
    show (((a.den * a.den - 1) + 1 : Nat) : Int) = (a.den : Int) * (a.den : Int)
    rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr
      (Nat.pos_iff_ne_zero.mp (Nat.mul_pos (Q'.den_pos a) (Q'.den_pos a)))), Int.natCast_mul]
  have hbd : ((b + b).den : Int) = (b.den : Int) * (b.den : Int) := by
    show (((b.den * b.den - 1) + 1 : Nat) : Int) = (b.den : Int) * (b.den : Int)
    rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr
      (Nat.pos_iff_ne_zero.mp (Nat.mul_pos (Q'.den_pos b) (Q'.den_pos b)))), Int.natCast_mul]
  have hraw : (a + a).num * ((b + b).den : Int) < (b + b).num * ((a + a).den : Int) := h
  rw [han, hbn, had, hbd] at hraw
  show a.num * (b.den : Int) < b.num * (a.den : Int)
  -- hraw : (2 a.num a.den)·(b.den²) < (2 b.num b.den)·(a.den²)
  -- = 2·(a.num b.den)·(a.den b.den) < 2·(b.num a.den)·(a.den b.den) ; cancel 2 a.den b.den > 0.
  have hk : (0 : Int) < (2 : Int) * ((a.den : Int) * (b.den : Int)) :=
    Int.mul_pos (by decide)
      (Int.mul_pos (by exact_mod_cast Q'.den_pos a) (by exact_mod_cast Q'.den_pos b))
  -- reshape hraw into k * (a.num b.den) < k * (b.num a.den)
  have hL : (a.num * (a.den : Int) + a.num * (a.den : Int)) * ((b.den : Int) * (b.den : Int))
      = ((2 : Int) * ((a.den : Int) * (b.den : Int))) * (a.num * (b.den : Int)) := by
    rw [← Int.two_mul]
    ac_rfl
  have hR : (b.num * (b.den : Int) + b.num * (b.den : Int)) * ((a.den : Int) * (a.den : Int))
      = ((2 : Int) * ((a.den : Int) * (b.den : Int))) * (b.num * (a.den : Int)) := by
    rw [← Int.two_mul]
    ac_rfl
  rw [hL, hR] at hraw
  exact Int.lt_of_mul_lt_mul_left hraw (Int.le_of_lt hk)

/-! ## 1. Local finite-sum algebra on `fsum`

`fsum` (BondMovingStep) and `RationalTail.finSum` agree (`fsum_eq_finSum`), so the
`RationalTail`/`FinSumAlg` additivity / const-pull / congruence lemmas lift to `fsum`.
We also prove the double-sum index swap directly on `fsum`. -/

/-- Additivity of `fsum`: `Σ (f + g) ≃ Σ f + Σ g`. -/
theorem fsum_add (f g : Nat → Q') (n : Nat) :
    (fsum (fun i => f i + g i) n).eqv (fsum f n + fsum g n) := by
  rw [fsum_eq_finSum (fun i => f i + g i) n, fsum_eq_finSum f n, fsum_eq_finSum g n]
  exact RationalTail.finSum_add f g n

/-- Pull a constant out of an `fsum` on the right: `(Σ f)·c ≃ Σ (f·c)`. -/
theorem fsum_mul_const (f : Nat → Q') (c : Q') (n : Nat) :
    (fsum f n * c).eqv (fsum (fun i => f i * c) n) := by
  rw [fsum_eq_finSum f n, fsum_eq_finSum (fun i => f i * c) n]
  exact RationalTail.finSum_mul_const f c n

/-- Termwise `eqv` lifts to `fsum`. -/
theorem fsum_eqv_congr (f g : Nat → Q') (h : ∀ i, (f i).eqv (g i)) (n : Nat) :
    (fsum f n).eqv (fsum g n) := by
  rw [fsum_eq_finSum f n, fsum_eq_finSum g n]
  exact RationalTail.finSum_eqv_congr f g h n

/-- Range-restricted termwise `eqv` lifts to `fsum` (agreement on `i < n` suffices). -/
theorem fsum_eqv_congr_lt (f g : Nat → Q') (n : Nat)
    (h : ∀ i, i < n → (f i).eqv (g i)) : (fsum f n).eqv (fsum g n) := by
  rw [fsum_eq_finSum f n, fsum_eq_finSum g n]
  exact RationalTail.finSum_eqv_congr_lt f g n h

/-- Pull a constant out of an `fsum` on the left: `c·(Σ f) ≃ Σ (c·f)`. -/
theorem fsum_const_mul (c : Q') (f : Nat → Q') (n : Nat) :
    (c * fsum f n).eqv (fsum (fun i => c * f i) n) := by
  rw [fsum_eq_finSum f n, fsum_eq_finSum (fun i => c * f i) n]
  exact RationalTail.const_mul_finSum f c n

/-- `Σ (-f) ≃ -(Σ f)`. -/
theorem fsum_neg (f : Nat → Q') : ∀ n, (fsum (fun i => -(f i)) n).eqv (-(fsum f n))
  | 0 => by
      show (0 : Q').eqv (-(0 : Q'))
      decide
  | n + 1 => by
      show (fsum (fun i => -(f i)) n + -(f n)).eqv (-(fsum f n + f n))
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ (-(f n)) (fsum_neg f n)) ?_
      exact Q'.eqv_symm (Q'.neg_add_eqv (fsum f n) (f n))

/-- A range-restricted termwise `≤` lifts to `fsum` (uses `fsum_mono` after patching
the sequence to agree below `n`). -/
theorem fsum_mono_lt {f g : Nat → Q'} (n : Nat) (h : ∀ i, i < n → f i ≤ g i) :
    fsum f n ≤ fsum g n := by
  -- Patch g to f above n is unnecessary: prove directly by induction.
  induction n with
  | zero => exact Q'.le_refl' 0
  | succ m ih =>
      show fsum f m + f m ≤ fsum g m + g m
      exact Q'.add_le_add (ih (fun i hi => h i (Nat.lt_succ_of_lt hi)))
        (h m (Nat.lt_succ_self m))

/-- `fsum` of the zero sequence is `0`. -/
theorem fsum_zero_seq (n : Nat) : fsum (fun _ => (0 : Q')) n = 0 := by
  rw [fsum_eq_finSum (fun _ => (0 : Q')) n]; exact RationalTail.finSum_zero_seq n

/-- **Double-sum index swap on `fsum`.**
`Σ_{a<m} Σ_{b<n} g a b ≃ Σ_{b<n} Σ_{a<m} g a b`.  Induction on `m`, peeling the
outer index and folding it into each inner sum via `fsum_add`. -/
theorem fsum_swap (g : Nat → Nat → Q') :
    ∀ m n, (fsum (fun a => fsum (fun b => g a b) n) m).eqv
        (fsum (fun b => fsum (fun a => g a b) m) n)
  | 0, n => by
      show (0 : Q').eqv (fsum (fun b => fsum (fun a => g a b) 0) n)
      refine Q'.eqv_symm ?_
      refine Q'.eqv_trans _ _ _ (fsum_eqv_congr _ (fun _ => 0) (fun _ => Q'.eqv_refl 0) n) ?_
      exact Q'.eqv_of_eq (fsum_zero_seq n)
  | m + 1, n => by
      show (fsum (fun a => fsum (fun b => g a b) n) m + fsum (fun b => g m b) n).eqv
          (fsum (fun b => fsum (fun a => g a b) (m + 1)) n)
      -- RHS inner (m+1)-sum splits: Σ_{a<m+1} g a b = Σ_{a<m} g a b + g m b.
      refine Q'.eqv_trans _ _ _ ?_
        (Q'.eqv_symm (fsum_add (fun b => fsum (fun a => g a b) m) (fun b => g m b) n))
      exact Q'.add_eqv_congr_right _ _ (fsum (fun b => g m b) n) (fsum_swap g m n)

/-! ## 2. AM-GM at the `Q'` level -/

/-- **AM-GM (cleared, summed form).**  `(x·y) + (x·y) ≤ x·x + y·y`, from
`0 ≤ (x + -y)·(x + -y)`. -/
theorem amgm_two (x y : Q') : (x * y) + (x * y) ≤ x * x + y * y := by
  -- 0 ≤ (x-y)² = x·x + -(x·y) + (-(x·y) + y·y), rearranged.
  have hsq : (0 : Q') ≤ (x + -y) * (x + -y) := SumOfSquares.q_mul_self_nonneg (x + -y)
  -- Expand (x + -y)·(x + -y).
  -- (x + -y)·(x + -y) = x·(x + -y) + (-y)·(x + -y)
  have e1 : ((x + -y) * (x + -y)).eqv (x * (x + -y) + (-y) * (x + -y)) :=
    Q'.add_mul_eqv x (-y) (x + -y)
  -- x·(x + -y) = x·x + x·(-y)
  have e2 : (x * (x + -y)).eqv (x * x + x * (-y)) := Q'.mul_add_eqv x x (-y)
  -- (-y)·(x + -y) = (-y)·x + (-y)·(-y)
  have e3 : ((-y) * (x + -y)).eqv ((-y) * x + (-y) * (-y)) := Q'.mul_add_eqv (-y) x (-y)
  -- Identify the cross terms with -(x·y) and the square term with y·y.
  -- x·(-y) ≃ -(x·y)
  have hxny : (x * (-y)).eqv (-(x * y)) := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv x (-y)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv y x) ?_
    exact Q'.neg_eqv_congr _ _ (Q'.mul_comm_eqv y x)
  -- (-y)·x ≃ -(x·y)
  have hnyx : ((-y) * x).eqv (-(x * y)) := by
    refine Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv y x) ?_
    exact Q'.neg_eqv_congr _ _ (Q'.mul_comm_eqv y x)
  -- (-y)·(-y) ≃ y·y
  have hnyny : ((-y) * (-y)).eqv (y * y) := by
    refine Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv y (-y)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ (Q'.mul_comm_eqv y (-y))) ?_
    refine Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ (Q'.neg_mul_eqv y y)) ?_
    exact Q'.neg_neg_eqv (y * y)
  -- Assemble: (x-y)² ≃ (x·x + -(x·y)) + (-(x·y) + y·y)
  have hexp : ((x + -y) * (x + -y)).eqv
      ((x * x + -(x * y)) + (-(x * y) + y * y)) := by
    refine Q'.eqv_trans _ _ _ e1 ?_
    refine Q'.add_eqv_congr' ?_ ?_
    · -- x·(x + -y) ≃ x·x + -(x·y)
      refine Q'.eqv_trans _ _ _ e2 (Q'.add_eqv_congr_left (x * x) _ _ hxny)
    · -- (-y)·(x + -y) ≃ -(x·y) + y·y
      refine Q'.eqv_trans _ _ _ e3 ?_
      exact Q'.add_eqv_congr' hnyx hnyny
  -- So 0 ≤ (x·x + -(x·y)) + (-(x·y) + y·y), regroup to (x·y)+(x·y) ≤ x·x + y·y.
  have hge : (0 : Q') ≤ (x * x + -(x * y)) + (-(x * y) + y * y) :=
    Q'.le_trans' _ _ _ hsq (Q'.le_of_eqv hexp)
  -- Add (x·y)+(x·y) to both sides and cancel.
  -- (x·x + -(x·y)) + (-(x·y) + y·y) ≃ (x·x + y·y) + (-(x·y) + -(x·y))
  have hregroup : ((x * x + -(x * y)) + (-(x * y) + y * y)).eqv
      ((x * x + y * y) + (-(x * y) + -(x * y))) := by
    -- (A + s) + (s + B) ≃ (A + s) + (B + s) ≃ (A + B) + (s + s) (A=x·x, B=y·y, s=-(x·y)).
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left _ _ _ (Q'.add_comm_eqv (-(x * y)) (y * y))) ?_
    exact Q'.eqv_symm (Q'.add_swap_inner (x * x) (y * y) (-(x * y)) (-(x * y)))
  have hge2 : (0 : Q') ≤ (x * x + y * y) + (-(x * y) + -(x * y)) :=
    Q'.le_trans' _ _ _ hge (Q'.le_of_eqv hregroup)
  -- 0 ≤ (x·x+y·y) + -( (x·y)+(x·y) ).  Then (x·y)+(x·y) ≤ x·x+y·y.
  have hneg : (-(x * y) + -(x * y)).eqv (-((x * y) + (x * y))) :=
    Q'.eqv_symm (Q'.neg_add_eqv (x * y) (x * y))
  have hge3 : (0 : Q') ≤ (x * x + y * y) + -((x * y) + (x * y)) :=
    Q'.le_trans' _ _ _ hge2 (Q'.le_of_eqv (Q'.add_eqv_congr_left _ _ _ hneg))
  exact Q'.le_of_sub_nonneg hge3

/-! ## 3. Positivity of the cube target — `0 < g₁` and `0 < R` -/

/-- The `s = 1` Clebsch double sum form of `g₁`.  (Just `bondMovedCoeff_p2_doubleSum`
specialized to `s = 1`, named for readability.) -/
theorem g1_doubleSum {w : Q'} (N : Nat) :
    (bondMovedCoeff N w 2 1).eqv
      (fsum (fun a => fsum (fun b =>
        fusionInd a b 1 * (coeffW w a * coeffW w b)) (N + 1)) (N + 1)) :=
  bondMovedCoeff_p2_doubleSum N 1

/-- **The off-diagonal `s = 1` vacuum channel makes `g₁` strictly positive.**
For `1 ≤ N`, `0 < bondMovedCoeff N w 2 1`: the `(a,b) = (0,1)` summand of the
`s = 1` double sum is `1·(c₀·c₁) > 0`, and every summand is `≥ 0`. -/
theorem bondMovedCoeff_one_pos (N : Nat) {w : Q'} (hw : (0 : Q') < w) (hN : 1 ≤ N) :
    (0 : Q') < bondMovedCoeff N w 2 1 := by
  refine pos_of_eqv_of_pos (g1_doubleSum N) ?_
  -- 0 < T1.  Inner sums ≥ 0; the a=0 inner sum ≥ the (b=1) summand = c₀·c₁ > 0.
  -- nonnegativity of each outer term
  have houter_nn : ∀ a, (0 : Q')
      ≤ fsum (fun b => fusionInd a b 1 * (coeffW w a * coeffW w b)) (N + 1) := by
    intro a
    refine fsum_nonneg (fun b => ?_) (N + 1)
    exact Q'.mul_nonneg _ _ (fusionInd_nonneg a b 1)
      (Q'.mul_nonneg _ _ (coeffW_nonneg (Q'.le_of_lt hw) a) (coeffW_nonneg (Q'.le_of_lt hw) b))
  -- a = 0 outer term ≤ T1
  have ha0 : fsum (fun b => fusionInd 0 b 1 * (coeffW w 0 * coeffW w b)) (N + 1)
      ≤ fsum (fun a => fsum (fun b =>
          fusionInd a b 1 * (coeffW w a * coeffW w b)) (N + 1)) (N + 1) :=
    fsum_term_le_of_nonneg houter_nn 0 (N + 1) (Nat.succ_pos N)
  -- inside a = 0: the b = 1 summand ≤ inner sum
  have hinner_nn : ∀ b, (0 : Q') ≤ fusionInd 0 b 1 * (coeffW w 0 * coeffW w b) := by
    intro b
    exact Q'.mul_nonneg _ _ (fusionInd_nonneg 0 b 1)
      (Q'.mul_nonneg _ _ (coeffW_nonneg (Q'.le_of_lt hw) 0) (coeffW_nonneg (Q'.le_of_lt hw) b))
  have hb1 : fusionInd 0 1 1 * (coeffW w 0 * coeffW w 1)
      ≤ fsum (fun b => fusionInd 0 b 1 * (coeffW w 0 * coeffW w b)) (N + 1) :=
    fsum_term_le_of_nonneg hinner_nn 1 (N + 1) (Nat.lt_succ_of_le hN)
  -- the (0,1) summand is positive: fusionInd 0 1 1 = 1, c₀·c₁ > 0
  have hind : fusionInd 0 1 1 = (1 : Q') := by decide
  have hpos_summand : (0 : Q') < fusionInd 0 1 1 * (coeffW w 0 * coeffW w 1) := by
    rw [hind]
    exact pos_of_eqv_of_pos (Q'.one_mul_eqv (coeffW w 0 * coeffW w 1))
      (Q'.mul_pos (coeffW_pos hw 0) (coeffW_pos hw 1))
  exact q_lt_of_lt_of_le hpos_summand (Q'.le_trans' _ _ _ hb1 ha0)

/-- **`0 < cubeRatio N w hw`** (for `1 ≤ N`).  The denominator `2·g₀ > 0` and the
numerator `g₁ > 0`, so the quotient is positive (`divPos_pos`). -/
theorem cubeRatio_pos (N : Nat) (w : Q') (hw : (0 : Q') < w) (hN : 1 ≤ N) :
    (0 : Q') < MatchedRetune.cubeRatio N w hw := by
  unfold MatchedRetune.cubeRatio
  exact Q'.divPos_pos _ _ _ (bondMovedCoeff_one_pos N hw hN)

/-! ## 4. The strict ratio bound `g₁ < 2·g₀` (the AM-GM / count slack) -/

/-- Per-term AM-GM, weighted by the (nonnegative) fusion indicator and pushed through
the distribution: `ind·(cₐc_b) + ind·(cₐc_b) ≤ ind·(cₐ²) + ind·(c_b²)`. -/
theorem term_amgm (a b : Nat) (c : Nat → Q') :
    (fusionInd a b 1 * (c a * c b)) + (fusionInd a b 1 * (c a * c b))
      ≤ fusionInd a b 1 * (c a * c a) + fusionInd a b 1 * (c b * c b) := by
  -- ind·((cₐc_b)+(cₐc_b)) ≤ ind·(cₐ²+c_b²) = ind·cₐ² + ind·c_b²
  have hind : (0 : Q') ≤ fusionInd a b 1 := fusionInd_nonneg a b 1
  have hamgm : (c a * c b) + (c a * c b) ≤ c a * c a + c b * c b := amgm_two (c a) (c b)
  have hmul : fusionInd a b 1 * ((c a * c b) + (c a * c b))
      ≤ fusionInd a b 1 * (c a * c a + c b * c b) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hamgm hind
  -- LHS ≃ ind·(cₐc_b) + ind·(cₐc_b)
  have hLeqv : (fusionInd a b 1 * ((c a * c b) + (c a * c b))).eqv
      ((fusionInd a b 1 * (c a * c b)) + (fusionInd a b 1 * (c a * c b))) :=
    Q'.mul_add_eqv (fusionInd a b 1) (c a * c b) (c a * c b)
  -- RHS ≃ ind·cₐ² + ind·c_b²
  have hReqv : (fusionInd a b 1 * (c a * c a + c b * c b)).eqv
      (fusionInd a b 1 * (c a * c a) + fusionInd a b 1 * (c b * c b)) :=
    Q'.mul_add_eqv (fusionInd a b 1) (c a * c a) (c b * c b)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hLeqv)
    (Q'.le_trans' _ _ _ hmul (Q'.le_of_eqv hReqv))

/-- The diagonal form of `g₀`: `g₀ ≃ D = ∑_{a≤N} (c a)²`.  The `s = 0` channel of
the `p = 2` self-fusion collapses to the diagonal (`fusionProduct_zero_diag`), then
the inner `fusionPow … 1 a ≃ c a` (`fusionPow_one_eq`, `a ≤ N`) gives the square. -/
theorem g0_diag {w : Q'} (N : Nat) :
    (bondMovedCoeff N w 2 0).eqv (fsum (fun a => coeffW w a * coeffW w a) (N + 1)) := by
  -- g₀ = fusionProduct N (fusionPow N (coeffW w) 1) (coeffW w) 0
  show (fusionProduct N (fusionPow N (coeffW w) 1) (coeffW w) 0).eqv
      (fsum (fun a => coeffW w a * coeffW w a) (N + 1))
  refine Q'.eqv_trans _ _ _
    (fusionProduct_zero_diag N (fusionPow N (coeffW w) 1) (coeffW w)) ?_
  -- ∑ (fusionPow … 1 a · c a)  ≃  ∑ (c a · c a), termwise for a < N+1 (so a ≤ N).
  refine fsum_eqv_congr_lt _ _ (N + 1) ?_
  intro a haN
  exact Q'.mul_eqv_congr_right _ _ (coeffW w a) (fusionPow_one_eq (Nat.lt_succ_iff.mp haN))

/-- The single-point indicator `δ_{·,j}` (as `Q'`). -/
def delta (j b : Nat) : Q' := if b = j then 1 else 0

theorem delta_nonneg (j b : Nat) : (0 : Q') ≤ delta j b := by
  unfold delta; by_cases h : b = j
  · rw [if_pos h]; decide
  · rw [if_neg h]; decide

/-- A single-point indicator sums to at most `1` over any range. -/
theorem fsum_delta_le_one (j : Nat) : ∀ n, fsum (fun b => delta j b) n ≤ (1 : Q')
  | 0 => by
      show (0 : Q') ≤ (1 : Q')
      decide
  | n + 1 => by
      show fsum (fun b => delta j b) n + delta j n ≤ (1 : Q')
      by_cases h : n = j
      · -- the term at n is 1; all earlier terms are 0 (since b ≠ j for b < n once n = j).
        subst h
        -- earlier indices b < n satisfy b ≠ n, so δ = 0; fsum over them ≃ 0.
        have hzero : (fsum (fun b => delta n b) n).eqv 0 := by
          refine Q'.eqv_trans _ _ _
            (fsum_eqv_congr_lt (fun b => delta n b) (fun _ => 0) n ?_) ?_
          · intro b hb
            show (delta n b).eqv 0
            unfold delta
            rw [if_neg (by omega : ¬ b = n)]
            exact Q'.eqv_refl 0
          · exact Q'.eqv_of_eq (fsum_zero_seq n)
        have hdn : delta n n = (1 : Q') := by unfold delta; rw [if_pos rfl]
        rw [hdn]
        -- fsum … n + 1 ≃ 0 + 1 ≃ 1
        refine Q'.le_trans' _ _ _
          (Q'.le_of_eqv (Q'.add_eqv_congr_right _ _ 1 hzero)) ?_
        exact Q'.le_of_eqv (QPoly.q_zero_add_eqv 1)
      · -- the term at n is 0; reduce to the IH.
        have hdn : delta j n = (0 : Q') := by unfold delta; rw [if_neg (by omega)]
        rw [hdn]
        refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (QPoly.q_add_zero_eqv _)) ?_
        exact fsum_delta_le_one j n

/-- The `s = 1` fusion row count `count a = ∑_{b≤N} fusionInd a b 1`. -/
def count (N a : Nat) : Q' := fsum (fun b => fusionInd a b 1) (N + 1)

theorem count_nonneg (N a : Nat) : (0 : Q') ≤ count N a :=
  fsum_nonneg (fun b => fusionInd_nonneg a b 1) (N + 1)

/-- **The `s = 1` fusion indicator is at most the two-neighbour indicator.**
`fusionInd a b 1 ≤ δ_{b,a+1} + δ_{a,b+1}` (the only admissible partners are
`b = a±1`). -/
theorem fusionInd_one_le_deltaPair (a b : Nat) :
    fusionInd a b 1 ≤ delta (a + 1) b + delta (b + 1) a := by
  unfold fusionInd
  by_cases hok : fusionOK a b 1
  · rw [if_pos hok]
    -- fusionOK a b 1 ⟹ b = a+1 ∨ a = b+1, so one of the two deltas is 1.
    have hcond := (fusionOK_eq_true_iff a b 1).mp hok
    obtain ⟨h1, h2, h3⟩ := hcond
    have hmax : a ≤ Nat.max a b := Nat.le_max_left a b
    have hmax' : b ≤ Nat.max a b := Nat.le_max_right a b
    have hmin : Nat.min a b ≤ a := Nat.min_le_left a b
    have hmin' : Nat.min a b ≤ b := Nat.min_le_right a b
    -- from h1 (max - min ≤ 1) and h3 (a+b+1 even ⟹ a+b odd ⟹ a ≠ b): |a-b| = 1.
    have hne : a ≠ b := by
      intro he; subst he; omega
    by_cases hba : b = a + 1
    · -- delta (a+1) b = 1
      have hd : delta (a + 1) b = (1 : Q') := by unfold delta; rw [if_pos hba]
      rw [hd]
      exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.eqv_symm (QPoly.q_add_zero_eqv 1)))
        (Q'.add_le_add_left 1 0 (delta (b + 1) a) (delta_nonneg (b + 1) a))
    · -- then a = b+1
      have hab : a = b + 1 := by omega
      have hd : delta (b + 1) a = (1 : Q') := by unfold delta; rw [if_pos hab]
      rw [hd]
      refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.eqv_symm (QPoly.q_zero_add_eqv 1))) ?_
      exact Q'.add_le_add_right 0 (delta (a + 1) b) 1 (delta_nonneg (a + 1) b)
  · rw [if_neg hok]
    exact Q'.zero_le_add _ _ (delta_nonneg (a + 1) b) (delta_nonneg (b + 1) a)

/-- **The fusion row count is at most `2`.**  `count N a ≤ 2`. -/
theorem count_le_two (N a : Nat) : count N a ≤ Q'.ofNat 2 := by
  unfold count
  refine Q'.le_trans' _ _ _
    (fsum_mono (fun b => fusionInd_one_le_deltaPair a b) (N + 1)) ?_
  -- ∑ (δ_{b,a+1} + δ_{a,b+1}) ≤ 1 + 1 = 2
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (fsum_add (fun b => delta (a + 1) b) (fun b => delta (b + 1) a) (N + 1))) ?_
  -- second sum ∑_b δ_{a,b+1} ≤ 1: it is a single-point indicator in b (b = a-1).
  have hsum1 : fsum (fun b => delta (a + 1) b) (N + 1) ≤ (1 : Q') :=
    fsum_delta_le_one (a + 1) (N + 1)
  have hsum2 : fsum (fun b => delta (b + 1) a) (N + 1) ≤ (1 : Q') := by
    -- δ_{b+1 = a} as a function of b is δ_{b, a-1} (1 only at b = a-1); ≤ 1.
    refine Q'.le_trans' _ _ _ (fsum_mono (fun b => ?_) (N + 1)) (fsum_delta_le_one (a - 1) (N + 1))
    show delta (b + 1) a ≤ delta (a - 1) b
    unfold delta
    by_cases h : a = b + 1
    · rw [if_pos h, if_pos (by omega : b = a - 1)]; exact Q'.le_refl' 1
    · rw [if_neg h]; exact delta_nonneg (a - 1) b
  have h2 : (1 : Q') + 1 ≤ Q'.ofNat 2 := by decide
  exact Q'.le_trans' _ _ _ (Q'.add_le_add hsum1 hsum2) h2

/-- **The vacuum fusion row count is at most `1`.**  `count N 0 ≤ 1`.  For `a = 0`
the only admissible partner is `b = 1` (`a = b+1` is impossible). -/
theorem count_zero_le_one (N : Nat) : count N 0 ≤ (1 : Q') := by
  unfold count
  refine Q'.le_trans' _ _ _ (fsum_mono (fun b => ?_) (N + 1)) (fsum_delta_le_one 1 (N + 1))
  show fusionInd 0 b 1 ≤ delta 1 b
  unfold fusionInd delta
  by_cases hok : fusionOK 0 b 1
  · rw [if_pos hok]
    have hcond := (fusionOK_eq_true_iff 0 b 1).mp hok
    obtain ⟨h1, h2, h3⟩ := hcond
    simp only [Nat.zero_max, Nat.zero_min] at h1
    -- 0+b sep ≤ 1 ⟹ b ≤ 1; 1 ≤ 0+b ⟹ b ≥ 1; so b = 1.
    rw [if_pos (by omega : b = 1)]; exact Q'.le_refl' 1
  · rw [if_neg hok]
    by_cases hb : b = 1
    · rw [if_pos hb]; decide
    · rw [if_neg hb]; decide

/-! ### The defect form `S1 ≤ 2·D − c₀²` and the final assembly -/

/-- `fusionInd a b 1 = fusionInd b a 1` (the `s = 1` channel is symmetric in `a, b`). -/
theorem fusionInd_one_comm (a b : Nat) : fusionInd a b 1 = fusionInd b a 1 := by
  -- max a b = max b a and min a b = min b a (commutativity, as Nat equalities).
  have hmax : Nat.max a b = Nat.max b a := Nat.max_comm a b
  have hmin : Nat.min a b = Nat.min b a := Nat.min_comm a b
  have hOK : fusionOK a b 1 = fusionOK b a 1 := by
    cases hab : fusionOK a b 1 with
    | true =>
        have h := (fusionOK_eq_true_iff a b 1).mp hab
        obtain ⟨h1, h2, h3⟩ := h
        refine Eq.symm ((fusionOK_eq_true_iff b a 1).mpr ⟨?_, ?_, ?_⟩)
        · rw [← hmax, ← hmin]; exact h1
        · omega
        · have he : b + a + 1 = a + b + 1 := by omega
          rw [he]; exact h3
    | false =>
        have h := (fusionOK_eq_false_iff a b 1).mp hab
        refine Eq.symm ((fusionOK_eq_false_iff b a 1).mpr ?_)
        intro hcon
        obtain ⟨h1, h2, h3⟩ := hcon
        refine h ⟨?_, ?_, ?_⟩
        · rw [hmax, hmin]; exact h1
        · omega
        · have he : a + b + 1 = b + a + 1 := by omega
          rw [he]; exact h3
  unfold fusionInd
  rw [hOK]

/-- The squared-diagonal sum `D = ∑_{a≤N} (c a)²`. -/
def Dsum {w : Q'} (N : Nat) : Q' := fsum (fun a => coeffW w a * coeffW w a) (N + 1)

/-- The count-weighted diagonal sum `S1' = ∑_{a≤N} count a · (c a)²`. -/
def S1weighted {w : Q'} (N : Nat) : Q' :=
  fsum (fun a => count N a * (coeffW w a * coeffW w a)) (N + 1)

/-- **`g₁` is bounded by twice `D` minus the vacuum square.**
`(bondMovedCoeff N w 2 1) + (bondMovedCoeff N w 2 1) ≤ (2·D − c₀²) + (2·D − c₀²)`
(the doubled AM-GM/count bound, kept doubled to avoid a cancellation step). -/
theorem g1_double_le {w : Q'} (N : Nat) :
    (bondMovedCoeff N w 2 1) + (bondMovedCoeff N w 2 1)
      ≤ (Q'.ofNat 2 * (@Dsum w N) + -(coeffW w 0 * coeffW w 0))
        + (Q'.ofNat 2 * (@Dsum w N) + -(coeffW w 0 * coeffW w 0)) := by
  -- Notation.
  -- T1 = ∑_a ∑_b ind·(cₐc_b) ; S1 = ∑_a ∑_b ind·cₐ² ; S2 = ∑_a ∑_b ind·c_b².
  -- (1) g₁ + g₁ ≤ S1 + S2 (doubled termwise AM-GM).
  -- (2) S2 ≃ S1 (swap + symmetry).
  -- (3) S1 ≃ S1weighted (count collapse).
  -- (4) S1weighted ≤ 2D − c₀² (defect ≥ 0 + vacuum slack).
  -- ---- (1) ----
  have hg1 := g1_doubleSum (w := w) N
  -- T1 + T1 ≃ ∑_a (outerT1 a + outerT1 a)
  have hdbl :
      ((fsum (fun a => fsum (fun b => fusionInd a b 1 * (coeffW w a * coeffW w b)) (N + 1)) (N + 1))
        + (fsum (fun a => fsum (fun b => fusionInd a b 1 * (coeffW w a * coeffW w b)) (N + 1)) (N + 1))).eqv
      (fsum (fun a =>
        fsum (fun b => fusionInd a b 1 * (coeffW w a * coeffW w b)) (N + 1)
          + fsum (fun b => fusionInd a b 1 * (coeffW w a * coeffW w b)) (N + 1)) (N + 1)) :=
    Q'.eqv_symm (fsum_add
      (fun a => fsum (fun b => fusionInd a b 1 * (coeffW w a * coeffW w b)) (N + 1))
      (fun a => fsum (fun b => fusionInd a b 1 * (coeffW w a * coeffW w b)) (N + 1)) (N + 1))
  -- per-a: outerT1 a + outerT1 a ≤ outerS1 a + outerS2 a
  have hstep1 :
      (fsum (fun a =>
        fsum (fun b => fusionInd a b 1 * (coeffW w a * coeffW w b)) (N + 1)
          + fsum (fun b => fusionInd a b 1 * (coeffW w a * coeffW w b)) (N + 1)) (N + 1))
      ≤ fsum (fun a =>
          fsum (fun b => fusionInd a b 1 * (coeffW w a * coeffW w a)) (N + 1)
            + fsum (fun b => fusionInd a b 1 * (coeffW w b * coeffW w b)) (N + 1)) (N + 1) := by
    refine fsum_mono (fun a => ?_) (N + 1)
    -- outerT1 a + outerT1 a ≃ ∑_b (term + term) ≤ ∑_b (ind·cₐ² + ind·c_b²) ≃ outerS1 a + outerS2 a
    refine Q'.le_trans' _ _ _
      (Q'.ge_of_eqv (fsum_add
        (fun b => fusionInd a b 1 * (coeffW w a * coeffW w b))
        (fun b => fusionInd a b 1 * (coeffW w a * coeffW w b)) (N + 1))) ?_
    refine Q'.le_trans' _ _ _
      (fsum_mono (fun b => term_amgm a b (coeffW w)) (N + 1)) ?_
    exact Q'.le_of_eqv (fsum_add
      (fun b => fusionInd a b 1 * (coeffW w a * coeffW w a))
      (fun b => fusionInd a b 1 * (coeffW w b * coeffW w b)) (N + 1))
  -- split the outer sum: ∑_a (outerS1 a + outerS2 a) ≃ S1 + S2
  have hsplit :
      (fsum (fun a =>
        fsum (fun b => fusionInd a b 1 * (coeffW w a * coeffW w a)) (N + 1)
          + fsum (fun b => fusionInd a b 1 * (coeffW w b * coeffW w b)) (N + 1)) (N + 1)).eqv
      ((fsum (fun a => fsum (fun b => fusionInd a b 1 * (coeffW w a * coeffW w a)) (N + 1)) (N + 1))
        + (fsum (fun a => fsum (fun b => fusionInd a b 1 * (coeffW w b * coeffW w b)) (N + 1)) (N + 1))) :=
    fsum_add
      (fun a => fsum (fun b => fusionInd a b 1 * (coeffW w a * coeffW w a)) (N + 1))
      (fun a => fsum (fun b => fusionInd a b 1 * (coeffW w b * coeffW w b)) (N + 1)) (N + 1)
  -- ---- (2) S2 ≃ S1 ----
  -- S2 = ∑_a ∑_b ind a b 1 · (c_b·c_b).  Swap a,b then use ind symmetry.
  have hswap :
      (fsum (fun a => fsum (fun b => fusionInd a b 1 * (coeffW w b * coeffW w b)) (N + 1)) (N + 1)).eqv
      (fsum (fun b => fsum (fun a => fusionInd a b 1 * (coeffW w b * coeffW w b)) (N + 1)) (N + 1)) :=
    fsum_swap (fun a b => fusionInd a b 1 * (coeffW w b * coeffW w b)) (N + 1) (N + 1)
  -- rename + symmetry: ∑_b ∑_a ind a b 1·c_b² ≃ ∑_a ∑_b ind a b 1·c_a²  (= S1)
  have hsym :
      (fsum (fun b => fsum (fun a => fusionInd a b 1 * (coeffW w b * coeffW w b)) (N + 1)) (N + 1)).eqv
      (fsum (fun a => fsum (fun b => fusionInd a b 1 * (coeffW w a * coeffW w a)) (N + 1)) (N + 1)) := by
    refine fsum_eqv_congr _ _ ?_ (N + 1)
    intro a
    refine fsum_eqv_congr _ _ ?_ (N + 1)
    intro b
    -- ind b a 1 · (c_a·c_a) ≃ ind a b 1 · (c_a·c_a)
    rw [fusionInd_one_comm b a]
    exact Q'.eqv_refl _
  have hS2_eq_S1 :
      (fsum (fun a => fsum (fun b => fusionInd a b 1 * (coeffW w b * coeffW w b)) (N + 1)) (N + 1)).eqv
      (fsum (fun a => fsum (fun b => fusionInd a b 1 * (coeffW w a * coeffW w a)) (N + 1)) (N + 1)) :=
    Q'.eqv_trans _ _ _ hswap hsym
  -- ---- (3) S1 ≃ S1weighted ----
  have hS1_count :
      (fsum (fun a => fsum (fun b => fusionInd a b 1 * (coeffW w a * coeffW w a)) (N + 1)) (N + 1)).eqv
      (@S1weighted w N) := by
    unfold S1weighted count
    refine fsum_eqv_congr _ _ ?_ (N + 1)
    intro a
    -- ∑_b ind a b 1 · (cₐ²) ≃ (∑_b ind a b 1) · cₐ²
    exact Q'.eqv_symm (fsum_mul_const (fun b => fusionInd a b 1) (coeffW w a * coeffW w a) (N + 1))
  -- ---- (4) S1weighted ≤ 2D − c₀² ----
  -- defect a := 2·cₐ² + -(count a · cₐ²) ≥ 0, and c₀² ≤ defect 0.
  have hdefct_nn : ∀ a, (0 : Q') ≤
      Q'.ofNat 2 * (coeffW w a * coeffW w a) + -(count N a * (coeffW w a * coeffW w a)) := by
    intro a
    -- 2·cₐ² − count a·cₐ² = (2 − count a)·cₐ² ≥ 0  (count a ≤ 2, cₐ² ≥ 0).
    have hca2 : (0 : Q') ≤ coeffW w a * coeffW w a := SumOfSquares.q_mul_self_nonneg (coeffW w a)
    have hc2 : count N a ≤ Q'.ofNat 2 := count_le_two N a
    have hmono : count N a * (coeffW w a * coeffW w a) ≤ Q'.ofNat 2 * (coeffW w a * coeffW w a) :=
      Q'.mul_le_mul_of_nonneg_right _ _ _ hc2 hca2
    exact Q'.sub_nonneg_of_le hmono
  -- fsum defct (N+1) ≃ 2D + -(S1weighted)
  have hdefct_sum :
      (fsum (fun a =>
        Q'.ofNat 2 * (coeffW w a * coeffW w a) + -(count N a * (coeffW w a * coeffW w a))) (N + 1)).eqv
      (Q'.ofNat 2 * (@Dsum w N) + -(@S1weighted w N)) := by
    -- split fsum (A + B) = fsum A + fsum B with A a = 2·cₐ², B a = -(count·cₐ²)
    refine Q'.eqv_trans _ _ _
      (fsum_add (fun a => Q'.ofNat 2 * (coeffW w a * coeffW w a))
        (fun a => -(count N a * (coeffW w a * coeffW w a))) (N + 1)) ?_
    refine Q'.add_eqv_congr' ?_ ?_
    · -- ∑ (2 · cₐ²) ≃ 2 · D
      unfold Dsum
      exact Q'.eqv_symm
        (fsum_const_mul (Q'.ofNat 2) (fun a => coeffW w a * coeffW w a) (N + 1))
    · -- ∑ -(count·cₐ²) ≃ -(S1weighted)
      unfold S1weighted
      exact fsum_neg (fun a => count N a * (coeffW w a * coeffW w a)) (N + 1)
  -- defect 0 ≥ c₀² (count 0 ≤ 1 ⟹ (2 − count 0)·c₀² ≥ c₀²).
  have hdefct0 : coeffW w 0 * coeffW w 0
      ≤ Q'.ofNat 2 * (coeffW w 0 * coeffW w 0) + -(count N 0 * (coeffW w 0 * coeffW w 0)) := by
    -- c₀² ≤ 2c₀² − count0·c₀²  ⟺  count0·c₀² ≤ c₀²  (count 0 ≤ 1)
    -- 2c₀² − count0·c₀² − c₀² = (1 − count0)·c₀² ≥ 0.
    have hca2 : (0 : Q') ≤ coeffW w 0 * coeffW w 0 := SumOfSquares.q_mul_self_nonneg (coeffW w 0)
    -- count0·c₀² ≤ 1·c₀² = c₀² and c₀² ≤ 2·c₀², combine.
    -- Use sub_nonneg form: 0 ≤ (2c₀² + -(count0·c₀²)) + -(c₀²).
    -- (2c₀² + -(count0 c₀²)) + -(c₀²) ≃ c₀² + -(count0 c₀²) (since 2c₀² - c₀² = c₀²).
    -- Simpler: c₀² ≤ defct0 ⟺ c₀² + count0·c₀² ≤ 2c₀²; both ≤ via count0 ≤ 1.
    refine Q'.le_of_sub_nonneg ?_
    -- 0 ≤ (2c₀² + -(count0·c₀²)) + -(c₀²)
    -- regroup ≃ (2c₀² + -(c₀²)) + -(count0·c₀²) ≃ c₀² + -(count0·c₀²) = c₀²·(1 − count0) ≥ 0
    have hco1 : count N 0 ≤ (1 : Q') := count_zero_le_one N
    have hcount_le : count N 0 * (coeffW w 0 * coeffW w 0) ≤ coeffW w 0 * coeffW w 0 := by
      refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ hco1 hca2) ?_
      exact Q'.le_of_eqv (Q'.one_mul_eqv (coeffW w 0 * coeffW w 0))
    -- 0 ≤ c₀² + -(count0·c₀²)
    have hgoal1 : (0 : Q') ≤ coeffW w 0 * coeffW w 0 + -(count N 0 * (coeffW w 0 * coeffW w 0)) :=
      Q'.sub_nonneg_of_le hcount_le
    -- and (2c₀² + -(count0 c₀²)) + -(c₀²) ≃ c₀² + -(count0·c₀²)
    refine Q'.le_trans' _ _ _ hgoal1 (Q'.le_of_eqv ?_)
    -- show (c₀² + -(count0 c₀²)) ≃ (2c₀² + -(count0 c₀²)) + -(c₀²)
    -- RHS = (2c₀² + -c₀²) + -(count0 c₀²) by regroup; 2c₀² + -c₀² ≃ c₀² (via ofNat_two_mul_eqv).
    have hreg : ((Q'.ofNat 2 * (coeffW w 0 * coeffW w 0)
          + -(count N 0 * (coeffW w 0 * coeffW w 0))) + -(coeffW w 0 * coeffW w 0)).eqv
        ((Q'.ofNat 2 * (coeffW w 0 * coeffW w 0) + -(coeffW w 0 * coeffW w 0))
          + -(count N 0 * (coeffW w 0 * coeffW w 0))) := by
      -- (A + s) + t ≃ (A + t) + s  with A=2c₀², s=-(count0 c₀²), t=-(c₀²)
      refine Q'.eqv_trans _ _ _
        (Q'.add_assoc_eqv (Q'.ofNat 2 * (coeffW w 0 * coeffW w 0))
          (-(count N 0 * (coeffW w 0 * coeffW w 0))) (-(coeffW w 0 * coeffW w 0))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left _ _ _
          (Q'.add_comm_eqv (-(count N 0 * (coeffW w 0 * coeffW w 0)))
            (-(coeffW w 0 * coeffW w 0)))) ?_
      exact Q'.eqv_symm (Q'.add_assoc_eqv (Q'.ofNat 2 * (coeffW w 0 * coeffW w 0))
        (-(coeffW w 0 * coeffW w 0)) (-(count N 0 * (coeffW w 0 * coeffW w 0))))
    -- 2c₀² + -c₀² ≃ c₀²
    have htwo : (Q'.ofNat 2 * (coeffW w 0 * coeffW w 0) + -(coeffW w 0 * coeffW w 0)).eqv
        (coeffW w 0 * coeffW w 0) := by
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ _ (ofNat_two_mul_eqv (coeffW w 0 * coeffW w 0))) ?_
      -- (c₀² + c₀²) + -c₀² ≃ c₀² + (c₀² + -c₀²) ≃ c₀² + 0 ≃ c₀²
      refine Q'.eqv_trans _ _ _
        (Q'.add_assoc_eqv (coeffW w 0 * coeffW w 0) (coeffW w 0 * coeffW w 0)
          (-(coeffW w 0 * coeffW w 0))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left _ _ _ (Q'.add_neg_self_eqv (coeffW w 0 * coeffW w 0))) ?_
      exact QPoly.q_add_zero_eqv (coeffW w 0 * coeffW w 0)
    -- assemble: target eqv is symm of [(2c₀²+-c₀²)+-(count0 c₀²) ≃ c₀²+-(count0 c₀²)] composed with hreg
    refine Q'.eqv_symm (Q'.eqv_trans _ _ _ hreg ?_)
    exact Q'.add_eqv_congr_right _ _ (-(count N 0 * (coeffW w 0 * coeffW w 0))) htwo
  -- defect 0 ≤ ∑ defect  (single-term ≤ nonneg sum)
  have hdefct0_le_sum :
      (Q'.ofNat 2 * (coeffW w 0 * coeffW w 0) + -(count N 0 * (coeffW w 0 * coeffW w 0)))
      ≤ fsum (fun a =>
          Q'.ofNat 2 * (coeffW w a * coeffW w a)
            + -(count N a * (coeffW w a * coeffW w a))) (N + 1) :=
    fsum_term_le_of_nonneg hdefct_nn 0 (N + 1) (Nat.succ_pos N)
  -- so c₀² ≤ 2D + -(S1weighted), i.e. S1weighted ≤ 2D − c₀².
  have hc0_le : coeffW w 0 * coeffW w 0 ≤ Q'.ofNat 2 * (@Dsum w N) + -(@S1weighted w N) :=
    Q'.le_trans' _ _ _ hdefct0
      (Q'.le_trans' _ _ _ hdefct0_le_sum (Q'.le_of_eqv hdefct_sum))
  -- S1weighted ≤ 2D − c₀²  (rearrange c₀² ≤ 2D − S1weighted)
  have hS1w_le : (@S1weighted w N)
      ≤ Q'.ofNat 2 * (@Dsum w N) + -(coeffW w 0 * coeffW w 0) := by
    -- from c₀² + S1weighted ≤ 2D  (add S1weighted to both sides of hc0_le and cancel -S1w)
    -- c₀² ≤ 2D + -(S1w)  ⟹  S1w + c₀² ≤ 2D  ⟹  S1w ≤ 2D + -(c₀²).
    -- Step: S1w ≤ 2D + -c₀² ⟺ S1w + c₀² ≤ 2D.  Use le_of_sub_nonneg / sub_nonneg machinery.
    refine Q'.le_of_sub_nonneg ?_
    -- 0 ≤ (2D + -c₀²) + -(S1w)
    -- hc0_le ⟹ 0 ≤ (2D + -S1w) + -(c₀²) ; regroup to (2D + -c₀²) + -(S1w).
    have h0 : (0 : Q') ≤ (Q'.ofNat 2 * (@Dsum w N) + -(@S1weighted w N))
        + -(coeffW w 0 * coeffW w 0) := Q'.sub_nonneg_of_le hc0_le
    refine Q'.le_trans' _ _ _ h0 (Q'.le_of_eqv ?_)
    -- (2D + -S1w) + -c₀² ≃ (2D + -c₀²) + -S1w
    refine Q'.eqv_trans _ _ _
      (Q'.add_assoc_eqv (Q'.ofNat 2 * (@Dsum w N)) (-(@S1weighted w N))
        (-(coeffW w 0 * coeffW w 0))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left _ _ _
        (Q'.add_comm_eqv (-(@S1weighted w N)) (-(coeffW w 0 * coeffW w 0)))) ?_
    exact Q'.eqv_symm (Q'.add_assoc_eqv (Q'.ofNat 2 * (@Dsum w N))
      (-(coeffW w 0 * coeffW w 0)) (-(@S1weighted w N)))
  -- ---- assemble g₁ + g₁ ≤ (2D − c₀²) + (2D − c₀²) ----
  -- g₁ ≃ T1 ; g₁ + g₁ ≃ T1 + T1 ≤ S1 + S2 = S1 + S1 ≤ S1w + S1w ≤ (2D−c₀²)+(2D−c₀²)
  -- Bound: T1 + T1 ≤ S1 + S2.
  have hT1T1_le :
      (fsum (fun a => fsum (fun b => fusionInd a b 1 * (coeffW w a * coeffW w b)) (N + 1)) (N + 1))
        + (fsum (fun a => fsum (fun b => fusionInd a b 1 * (coeffW w a * coeffW w b)) (N + 1)) (N + 1))
      ≤ (fsum (fun a => fsum (fun b => fusionInd a b 1 * (coeffW w a * coeffW w a)) (N + 1)) (N + 1))
        + (fsum (fun a => fsum (fun b => fusionInd a b 1 * (coeffW w b * coeffW w b)) (N + 1)) (N + 1)) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hdbl) (Q'.le_trans' _ _ _ hstep1 (Q'.le_of_eqv hsplit))
  -- S1 + S2 ≃ S1w + S1w
  have hS1S2_eq :
      ((fsum (fun a => fsum (fun b => fusionInd a b 1 * (coeffW w a * coeffW w a)) (N + 1)) (N + 1))
        + (fsum (fun a => fsum (fun b => fusionInd a b 1 * (coeffW w b * coeffW w b)) (N + 1)) (N + 1))).eqv
      ((@S1weighted w N) + (@S1weighted w N)) :=
    Q'.add_eqv_congr' hS1_count (Q'.eqv_trans _ _ _ hS2_eq_S1 hS1_count)
  -- S1w + S1w ≤ (2D−c₀²)+(2D−c₀²)
  have hfinal_sum : ((@S1weighted w N) + (@S1weighted w N))
      ≤ (Q'.ofNat 2 * (@Dsum w N) + -(coeffW w 0 * coeffW w 0))
        + (Q'.ofNat 2 * (@Dsum w N) + -(coeffW w 0 * coeffW w 0)) :=
    Q'.add_le_add hS1w_le hS1w_le
  -- transport g₁ ≃ T1
  have hg1g1 : ((bondMovedCoeff N w 2 1) + (bondMovedCoeff N w 2 1)).eqv
      ((fsum (fun a => fsum (fun b => fusionInd a b 1 * (coeffW w a * coeffW w b)) (N + 1)) (N + 1))
        + (fsum (fun a => fsum (fun b => fusionInd a b 1 * (coeffW w a * coeffW w b)) (N + 1)) (N + 1))) :=
    Q'.add_eqv_congr' hg1 hg1
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hg1g1)
    (Q'.le_trans' _ _ _ hT1T1_le
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hS1S2_eq) hfinal_sum))

/-- **The KEY strict ratio bound:** `g₁ < 2·g₀`
(`bondMovedCoeff N w 2 1 < Q'.ofNat 2 · bondMovedCoeff N w 2 0`), for `0 < w`.
The doubled AM-GM/count bound `g₁+g₁ ≤ (2D−c₀²)+(2D−c₀²)`, the strict vacuum slack
`c₀² = 1 > 0`, and the doubling-cancellation. -/
theorem g1_lt_two_g0 (N : Nat) {w : Q'} (hw : (0 : Q') < w) :
    bondMovedCoeff N w 2 1 < Q'.ofNat 2 * bondMovedCoeff N w 2 0 := by
  -- abbreviations
  -- X := 2D − c₀² ; c₀² > 0 since c 0 = 1.
  have hc0sq_pos : (0 : Q') < coeffW w 0 * coeffW w 0 :=
    Q'.mul_pos (coeffW_pos hw 0) (coeffW_pos hw 0)
  -- g₀ ≃ D ; so 2·g₀ ≃ 2·D.
  have hg0 := g0_diag (w := w) N
  have h2g0_eq : (Q'.ofNat 2 * bondMovedCoeff N w 2 0).eqv (Q'.ofNat 2 * (@Dsum w N)) := by
    unfold Dsum
    exact Q'.mul_eqv_congr_left (Q'.ofNat 2) _ _ hg0
  -- 2·D = X + c₀²  (X = 2D + -(c₀²)).
  have hX_plus : (Q'.ofNat 2 * (@Dsum w N)).eqv
      ((Q'.ofNat 2 * (@Dsum w N) + -(coeffW w 0 * coeffW w 0)) + (coeffW w 0 * coeffW w 0)) := by
    -- A ≃ (A + -c) + c
    refine Q'.eqv_symm ?_
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv _ _ _) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left _ _ _
        (Q'.eqv_trans _ _ _ (Q'.add_comm_eqv (-(coeffW w 0 * coeffW w 0)) (coeffW w 0 * coeffW w 0))
          (Q'.add_neg_self_eqv (coeffW w 0 * coeffW w 0)))) ?_
    exact QPoly.q_add_zero_eqv _
  -- the doubled bound on g₁
  have hdb := g1_double_le (w := w) N
  -- 2g₀ + 2g₀ ≃ (X + c₀²) + (X + c₀²) ≃ (X + X) + (c₀² + c₀²)
  -- So (X + X) < (2g₀ + 2g₀).
  have hX_lt : ((Q'.ofNat 2 * (@Dsum w N) + -(coeffW w 0 * coeffW w 0))
        + (Q'.ofNat 2 * (@Dsum w N) + -(coeffW w 0 * coeffW w 0)))
      < (Q'.ofNat 2 * bondMovedCoeff N w 2 0) + (Q'.ofNat 2 * bondMovedCoeff N w 2 0) := by
    -- RHS ≃ 2D + 2D ≃ (X + c₀²) + (X + c₀²) ≃ (X+X) + (c₀²+c₀²) > X+X.
    have hrhs : ((Q'.ofNat 2 * bondMovedCoeff N w 2 0) + (Q'.ofNat 2 * bondMovedCoeff N w 2 0)).eqv
        (((Q'.ofNat 2 * (@Dsum w N) + -(coeffW w 0 * coeffW w 0))
            + (Q'.ofNat 2 * (@Dsum w N) + -(coeffW w 0 * coeffW w 0)))
          + ((coeffW w 0 * coeffW w 0) + (coeffW w 0 * coeffW w 0))) := by
      -- 2g₀+2g₀ ≃ 2D+2D ≃ (X+c₀²)+(X+c₀²) ≃ (X+X)+(c₀²+c₀²)
      refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' h2g0_eq h2g0_eq) ?_
      refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hX_plus hX_plus) ?_
      exact Q'.add_swap_inner _ _ _ _
    -- X+X < (X+X)+(c₀²+c₀²) ≃ 2g₀+2g₀
    refine q_lt_of_lt_of_le
      (AFRateCalibration.lt_add_of_pos_right _ _ (Q'.add_pos hc0sq_pos hc0sq_pos))
      (Q'.ge_of_eqv hrhs)
  -- chain: g₁+g₁ ≤ X+X < 2g₀+2g₀, then cancel doubling.
  exact lt_of_add_self_lt_add_self (Q'.lt_of_le_of_lt hdb hX_lt)

/-! ## 5. The two cube-ratio bounds and the unconditional carrier -/

/-- `divPos p q hq < 1` when `p < q`.  `divPos p q = p·(1/q)`; multiply `p < q` by the
positive `1/q` and collapse `q·(1/q) ≃ 1`. -/
theorem divPos_lt_one_of_lt (p q : Q') (hq : (0 : Q') < q) (h : p < q) :
    Q'.divPos p q hq < (1 : Q') := by
  unfold Q'.divPos
  -- p·(1/q) ≃ (1/q)·p < (1/q)·q ≃ 1
  have hrp : (0 : Q') < Q'.recipPos q hq := Q'.recipPos_pos q hq
  have hstep : Q'.recipPos q hq * p < Q'.recipPos q hq * q :=
    Q'.mul_lt_mul_of_pos_left hrp h
  -- p·(1/q) ≃ (1/q)·p
  have hcomm : (p * Q'.recipPos q hq).eqv (Q'.recipPos q hq * p) := Q'.mul_comm_eqv p _
  -- (1/q)·q ≃ q·(1/q) ≃ 1
  have hone : (Q'.recipPos q hq * q).eqv (1 : Q') :=
    Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv (Q'.recipPos q hq) q) (Q'.mul_recipPos_eqv q hq)
  -- p·(1/q) ≤ (1/q)·p < (1/q)·q ≃ 1
  exact q_lt_of_lt_of_le (Q'.lt_of_le_of_lt (Q'.le_of_eqv hcomm) hstep) (Q'.le_of_eqv hone)

/-- **`cubeRatio N w hw < 1`** (for `0 < w`).  The numerator `g₁` is strictly less than
the denominator `2·g₀` (`g1_lt_two_g0`), so the quotient is strictly sub-unit. -/
theorem cubeRatio_lt_one (N : Nat) (w : Q') (hw : (0 : Q') < w) :
    MatchedRetune.cubeRatio N w hw < (1 : Q') := by
  unfold MatchedRetune.cubeRatio
  exact divPos_lt_one_of_lt _ _ _ (g1_lt_two_g0 N hw)

/-- **The matched-retune carrier, inhabited UNCONDITIONALLY** (modulo the structural
side condition `1 ≤ N`).  Both ratio hypotheses of the carrier glue are now discharged:
`0 < cubeRatio` (`cubeRatio_pos`) and `cubeRatio < 1` (`cubeRatio_lt_one`).  This is NOT
a 4D Yang–Mills mass gap. -/
def exists_matchedRetuneP2_unconditional (N : Nat) (w : Q') (hw : (0 : Q') < w) (hN : 1 ≤ N) :
    MatchedRetune.MatchedRetuneP2 N w hw :=
  MatchedRetuneBridge.exists_matchedRetuneP2 N w hw
    (cubeRatio_pos N w hw hN) (cubeRatio_lt_one N w hw)

end YMGap.Continuum.CubeRatioBounds

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.CubeRatioBounds.amgm_two
#print axioms YMGap.Continuum.CubeRatioBounds.fsum_swap
#print axioms YMGap.Continuum.CubeRatioBounds.lt_of_add_self_lt_add_self
#print axioms YMGap.Continuum.CubeRatioBounds.sub_lt_self_of_pos
#print axioms YMGap.Continuum.CubeRatioBounds.term_amgm
#print axioms YMGap.Continuum.CubeRatioBounds.fusionInd_one_comm
#print axioms YMGap.Continuum.CubeRatioBounds.count_le_two
#print axioms YMGap.Continuum.CubeRatioBounds.count_zero_le_one
#print axioms YMGap.Continuum.CubeRatioBounds.g0_diag
#print axioms YMGap.Continuum.CubeRatioBounds.bondMovedCoeff_one_pos
#print axioms YMGap.Continuum.CubeRatioBounds.g1_double_le
#print axioms YMGap.Continuum.CubeRatioBounds.cubeRatio_pos
#print axioms YMGap.Continuum.CubeRatioBounds.g1_lt_two_g0
#print axioms YMGap.Continuum.CubeRatioBounds.cubeRatio_lt_one
#print axioms YMGap.Continuum.CubeRatioBounds.exists_matchedRetuneP2_unconditional
