/-
# Located roots of the Chebyshev-`U` polynomial as constructive reals
# (`chebRoot` — the π-free Gauss–Chebyshev node abscissas, by bisection)

The Gauss–Chebyshev nodes are the abscissas `x_k = cos(k·π/(M+1))`, the zeros of
the second-kind Chebyshev polynomial `U_M`.  Although the closed form names `π`,
the abscissas themselves are **algebraic** (roots of a `Q'`-polynomial), so they
can be produced as genuine constructive reals *without* any reference to `π`,
purely by located bisection on a rational sign-change bracket.

This module is a direct clone of the located-bisection pattern used for the
constructive cube root (`YMGap.Constructive.CReal.cbrtFromInit`): the monotone
crossing test `m³ ≤ R` is replaced by the **sign test** `U_M(m) ≤ 0` on a
rational bracket `[lo,hi] ⊂ (−1,1)` carrying a sign change `U_M(lo) ≤ 0 ≤ U_M(hi)`.

## What is PROVED here (all genuine, axiom-clean)

* `bisectStep` / `bisectSeq` / `BisectInit` / `bisectInv` — the generic
  located-bisection bracket for an arbitrary `f : Q' → Q'` with a sign change.
  The located invariant `f lo ≤ 0 ≤ f hi` is preserved **by the test alone**,
  with NO monotonicity hypothesis (exactly as the cube-root invariant
  `lo³ ≤ R ≤ hi³` is).
* `bisectRoot f init` — the located root as a `CReal` (lower endpoints,
  geometric width, halving Cauchy modulus), cloning `cbrtFromInit`.
* `bisectRoot_eval_zero` — squeeze proof that `f(root) ≃ 0`, from the located
  invariant together with a one-sided Lipschitz bound
  `f(hi) − f(lo) ≤ Lip·(hi − lo)` (the analogue of `cube_diff_le`).
* `bisectRoot_in_bracket` (unit/bracket enclosure) and the strict-interior
  `bisectRoot_plus_one_pos` / `bisectRoot_one_sub_pos` (`IsPositive` witnesses for
  `root + 1 > 0` and `1 − root > 0`, i.e. the genuine strict `−1 < root < 1`
  needed for the weight `1 − x² > 0`).

* The order `M = 2` produced **unconditionally and completely**: the explicit
  rational sign-change bracket `[2/5,3/5] ⊂ (−1,1)` (signs by `decide`), the
  explicit two-sided Lipschitz constant `Lip = 8` proved from the
  recurrence-given form `U₂(x) = (2x)² − 1`, and the located Gauss–Chebyshev node
  `chebRoot2` (`= cos(π/3) = 1/2`) with its proved zero identity
  `chebRoot2_eval_zero`, bracket enclosure `chebRoot2_in_bracket`, and strict
  interior `chebRoot2_plus_one_pos` / `chebRoot2_one_sub_pos`.

## NAMED-open (honest residual)

* **Higher fixed orders `M ≥ 3` and general `M`.**  Producing the sign-change
  bracket signs for a fixed `M ≥ 3` is again a finite `decide` check, but the
  per-order Lipschitz constant requires the explicit polynomial form
  (`U₃ = 8x³−4x`, etc.); and producing all `M` disjoint brackets for arbitrary
  `M` requires a uniform root-separation / rational-`π`-enclosure argument
  (`x_k = cos(kπ/(M+1))` localised by rational bounds on `π`).  None of that is
  discharged here.  The located bisection machinery (`bisectRoot*`,
  `bisectRoot_eval_zero`) is **fully general** and consumes any
  `BisectInit` + `LipBound` datum, so the residual is precisely the construction
  of that per-`M` data; the worst-case small order `M = 2` is produced
  unconditionally as a worked, complete instance.

## Axiom gate (AGENTS.md Rule 1)

Every load-bearing declaration reports `[propext]` or `[propext, Quot.sound]`
(the `Quot.sound` only via reused `omega`/`Nat`/`Int` helpers).  No
`Classical.*`, no `sorry`/`sorryAx`, no `native_decide`.  `decide` is used only
on closed `Q'`/`Nat` (in)equalities (the small-`M` bracket sign checks).
-/

import YMGap.Continuum.ChebyshevU
import YMGap.Constructive.CubeRoot

namespace YMGap.Continuum.ChebRoot

open YMGap.Constructive
open YMGap.Constructive.Q'
open YMGap.Constructive.CReal
open YMGap.Constructive.HalfPow
open YMGap.Continuum.ChebU

local infix:50 " ≈ " => Q'.eqv

/-! ## The Chebyshev-`U` evaluation over `Q'`

We reuse the repo's recurrence-defined `U : Nat → Q' → Q'`
(`YMGap.Continuum.Cheb.U`).  `Ueval M x := U M x` is the degree-`M` second-kind
Chebyshev polynomial at the rational `x`; `|U_M(x)| ≤ M+1` on `[−1,1]` is the
proved `ChebU.absU_le`. -/

/-- The degree-`M` second-kind Chebyshev polynomial evaluated at a rational. -/
def Ueval (M : Nat) (x : Q') : Q' := YMGap.Continuum.Cheb.U M x

@[simp] theorem Ueval_zero (x : Q') : Ueval 0 x = 1 := rfl
@[simp] theorem Ueval_one (x : Q') : Ueval 1 x = (2 : Q') * x := rfl
theorem Ueval_succ_succ (M : Nat) (x : Q') :
    Ueval (M+2) x = ((2 : Q') * x) * Ueval (M+1) x + (-(Ueval M x)) := rfl

/-- `|U_M(x)| ≤ M+1` on `[−1,1]` (the proved second-kind bound). -/
theorem Ueval_abs_le (M : Nat) (x : Q') (hx1 : x ≤ (1 : Q')) (hxm1 : (-(1 : Q')) ≤ x) :
    Ueval M x ≤ Q'.ofNat (M+1) ∧ (-(Q'.ofNat (M+1))) ≤ Ueval M x := by
  obtain ⟨hub, hlb⟩ := ChebU.absU_le M x hx1 hxm1
  exact ⟨hub, hlb⟩

/-! ## Generic located bisection on a sign-change bracket

For `f : Q' → Q'` with a rational bracket `[lo₀,hi₀]`, `lo₀ ≤ hi₀`, carrying the
sign change `f lo₀ ≤ 0 ≤ f hi₀`.  We bisect at the midpoint and keep the half
still bracketing the crossing of `f = 0`, decided by the decidable test
`f m ≤ 0`.  The located invariant `f lo ≤ 0 ≤ f hi` is preserved **without** any
monotonicity hypothesis — the test alone re-establishes it. -/

/-- One bisection step: bisect `[lo,hi]` and keep the sign-changing half. -/
def bisectStep (f : Q' → Q') (s : Q' × Q') : Q' × Q' :=
  let lo := s.1; let hi := s.2; let m := half * (lo + hi)
  if f m ≤ 0 then (m, hi) else (lo, m)

/-- The bisection bracket starting from `[lo₀,hi₀]`. -/
def bisectSeq (f : Q' → Q') (lo₀ hi₀ : Q') : Nat → Q' × Q'
  | 0 => (lo₀, hi₀)
  | n + 1 => bisectStep f (bisectSeq f lo₀ hi₀ n)

/-- Lower endpoints — the approximation sequence of the located root. -/
def bisectLo (f : Q' → Q') (lo₀ hi₀ : Q') (n : Nat) : Q' := (bisectSeq f lo₀ hi₀ n).1
/-- Upper endpoints. -/
def bisectHi (f : Q' → Q') (lo₀ hi₀ : Q') (n : Nat) : Q' := (bisectSeq f lo₀ hi₀ n).2

@[simp] theorem bisectLo_zero (f : Q' → Q') (lo₀ hi₀ : Q') : bisectLo f lo₀ hi₀ 0 = lo₀ := rfl
@[simp] theorem bisectHi_zero (f : Q' → Q') (lo₀ hi₀ : Q') : bisectHi f lo₀ hi₀ 0 = hi₀ := rfl

/-! ### Width of the bracket (reuses the cube-root midpoint identities) -/

/-- The bracket width `hi_n − lo_n`. -/
def bisectWidth (f : Q' → Q') (lo₀ hi₀ : Q') (n : Nat) : Q' :=
  bisectHi f lo₀ hi₀ n + -(bisectLo f lo₀ hi₀ n)

/-- The width halves at each step. -/
theorem bisectWidth_succ (f : Q' → Q') (lo₀ hi₀ : Q') (n : Nat) :
    (bisectWidth f lo₀ hi₀ (n + 1)).eqv (half * bisectWidth f lo₀ hi₀ n) := by
  show (bisectHi f lo₀ hi₀ (n + 1) + -(bisectLo f lo₀ hi₀ (n + 1))).eqv
       (half * (bisectHi f lo₀ hi₀ n + -(bisectLo f lo₀ hi₀ n)))
  show ((if f (half * ((bisectSeq f lo₀ hi₀ n).1 + (bisectSeq f lo₀ hi₀ n).2)) ≤ 0
          then (half * ((bisectSeq f lo₀ hi₀ n).1 + (bisectSeq f lo₀ hi₀ n).2), (bisectSeq f lo₀ hi₀ n).2)
          else ((bisectSeq f lo₀ hi₀ n).1, half * ((bisectSeq f lo₀ hi₀ n).1 + (bisectSeq f lo₀ hi₀ n).2))).2
        + -(if f (half * ((bisectSeq f lo₀ hi₀ n).1 + (bisectSeq f lo₀ hi₀ n).2)) ≤ 0
          then (half * ((bisectSeq f lo₀ hi₀ n).1 + (bisectSeq f lo₀ hi₀ n).2), (bisectSeq f lo₀ hi₀ n).2)
          else ((bisectSeq f lo₀ hi₀ n).1, half * ((bisectSeq f lo₀ hi₀ n).1 + (bisectSeq f lo₀ hi₀ n).2))).1).eqv
       (half * ((bisectSeq f lo₀ hi₀ n).2 + -(bisectSeq f lo₀ hi₀ n).1))
  by_cases hcase : f (half * ((bisectSeq f lo₀ hi₀ n).1 + (bisectSeq f lo₀ hi₀ n).2)) ≤ 0
  · rw [if_pos hcase]
    exact CReal.hi_sub_mid (bisectSeq f lo₀ hi₀ n).1 (bisectSeq f lo₀ hi₀ n).2
  · rw [if_neg hcase]
    exact CReal.mid_sub_lo (bisectSeq f lo₀ hi₀ n).1 (bisectSeq f lo₀ hi₀ n).2

/-- `width n ≃ (hi₀ − lo₀)·½ⁿ`. -/
theorem bisectWidth_eq_geom (f : Q' → Q') (lo₀ hi₀ : Q') :
    ∀ n, (bisectWidth f lo₀ hi₀ n).eqv ((hi₀ + -lo₀) * half ^ n)
  | 0 => by
      show (bisectHi f lo₀ hi₀ 0 + -(bisectLo f lo₀ hi₀ 0)).eqv ((hi₀ + -lo₀) * half ^ 0)
      rw [bisectHi_zero, bisectLo_zero, Q'.pow_zero]
      exact Q'.eqv_symm (mul_one_eqv (hi₀ + -lo₀))
  | n + 1 => by
      refine Q'.eqv_trans _ _ _ (bisectWidth_succ f lo₀ hi₀ n) ?_
      refine Q'.eqv_trans _ _ _
        (mul_eqv_congr_left half (bisectWidth f lo₀ hi₀ n) ((hi₀ + -lo₀) * half ^ n)
          (bisectWidth_eq_geom f lo₀ hi₀ n)) ?_
      refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (mul_assoc_eqv half (hi₀ + -lo₀) (half ^ n))) ?_
      refine Q'.eqv_trans _ _ _
        (mul_eqv_congr_right (half * (hi₀ + -lo₀)) ((hi₀ + -lo₀) * half) (half ^ n)
          (mul_comm_eqv half (hi₀ + -lo₀))) ?_
      refine Q'.eqv_trans _ _ _ (mul_assoc_eqv (hi₀ + -lo₀) half (half ^ n)) ?_
      rw [Q'.pow_succ]; exact Q'.eqv_refl _

/-! ### The initial bracket and the located invariant -/

/-- A valid sign-change bracket `[lo₀,hi₀]` for `f`. -/
structure BisectInit (f : Q' → Q') (lo₀ hi₀ : Q') : Prop where
  loLeHi : lo₀ ≤ hi₀
  loSign : f lo₀ ≤ 0
  hiSign : (0 : Q') ≤ f hi₀

/-- The located bracket invariant at stage `n`. -/
def BisectInv (f : Q' → Q') (lo₀ hi₀ : Q') (n : Nat) : Prop :=
  lo₀ ≤ bisectLo f lo₀ hi₀ n ∧ bisectHi f lo₀ hi₀ n ≤ hi₀ ∧
    bisectLo f lo₀ hi₀ n ≤ bisectHi f lo₀ hi₀ n ∧
    f (bisectLo f lo₀ hi₀ n) ≤ 0 ∧ (0 : Q') ≤ f (bisectHi f lo₀ hi₀ n)

/-- The located invariant holds at every stage (induction; **no monotonicity**). -/
theorem bisectInv (f : Q' → Q') (lo₀ hi₀ : Q') (hinit : BisectInit f lo₀ hi₀) :
    ∀ n, BisectInv f lo₀ hi₀ n
  | 0 => ⟨Q'.le_refl' _, Q'.le_refl' _, hinit.loLeHi, hinit.loSign, hinit.hiSign⟩
  | n + 1 => by
      obtain ⟨hloge, hhile, hle, hlosgn, hhisgn⟩ := bisectInv f lo₀ hi₀ hinit n
      have hlm : (bisectSeq f lo₀ hi₀ n).1 ≤ half * ((bisectSeq f lo₀ hi₀ n).1 + (bisectSeq f lo₀ hi₀ n).2) :=
        CReal.le_mid hle
      have hmh : half * ((bisectSeq f lo₀ hi₀ n).1 + (bisectSeq f lo₀ hi₀ n).2) ≤ (bisectSeq f lo₀ hi₀ n).2 :=
        CReal.mid_le hle
      have hloeq : bisectLo f lo₀ hi₀ (n + 1) =
          (if f (half * ((bisectSeq f lo₀ hi₀ n).1 + (bisectSeq f lo₀ hi₀ n).2)) ≤ 0
            then (half * ((bisectSeq f lo₀ hi₀ n).1 + (bisectSeq f lo₀ hi₀ n).2), (bisectSeq f lo₀ hi₀ n).2)
            else ((bisectSeq f lo₀ hi₀ n).1, half * ((bisectSeq f lo₀ hi₀ n).1 + (bisectSeq f lo₀ hi₀ n).2))).1 := rfl
      have hhieq : bisectHi f lo₀ hi₀ (n + 1) =
          (if f (half * ((bisectSeq f lo₀ hi₀ n).1 + (bisectSeq f lo₀ hi₀ n).2)) ≤ 0
            then (half * ((bisectSeq f lo₀ hi₀ n).1 + (bisectSeq f lo₀ hi₀ n).2), (bisectSeq f lo₀ hi₀ n).2)
            else ((bisectSeq f lo₀ hi₀ n).1, half * ((bisectSeq f lo₀ hi₀ n).1 + (bisectSeq f lo₀ hi₀ n).2))).2 := rfl
      by_cases hc : f (half * ((bisectSeq f lo₀ hi₀ n).1 + (bisectSeq f lo₀ hi₀ n).2)) ≤ 0
      · have hlo' : bisectLo f lo₀ hi₀ (n + 1)
            = half * ((bisectSeq f lo₀ hi₀ n).1 + (bisectSeq f lo₀ hi₀ n).2) := by rw [hloeq, if_pos hc]
        have hhi' : bisectHi f lo₀ hi₀ (n + 1) = (bisectSeq f lo₀ hi₀ n).2 := by rw [hhieq, if_pos hc]
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · rw [hlo']; exact Q'.le_trans' _ _ _ hloge hlm
        · rw [hhi']; exact hhile
        · rw [hlo', hhi']; exact hmh
        · rw [hlo']; exact hc
        · rw [hhi']; exact hhisgn
      · have hRle : (0 : Q') ≤ f (half * ((bisectSeq f lo₀ hi₀ n).1 + (bisectSeq f lo₀ hi₀ n).2)) :=
          Q'.le_of_not_le hc
        have hlo' : bisectLo f lo₀ hi₀ (n + 1) = (bisectSeq f lo₀ hi₀ n).1 := by rw [hloeq, if_neg hc]
        have hhi' : bisectHi f lo₀ hi₀ (n + 1)
            = half * ((bisectSeq f lo₀ hi₀ n).1 + (bisectSeq f lo₀ hi₀ n).2) := by rw [hhieq, if_neg hc]
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · rw [hlo']; exact hloge
        · rw [hhi']; exact Q'.le_trans' _ _ _ hmh hhile
        · rw [hlo', hhi']; exact hlm
        · rw [hlo']; exact hlosgn
        · rw [hhi']; exact hRle

/-! ### Invariant corollaries -/

theorem bisectLo_ge (f : Q' → Q') (lo₀ hi₀ : Q') (hinit : BisectInit f lo₀ hi₀) (n : Nat) :
    lo₀ ≤ bisectLo f lo₀ hi₀ n := (bisectInv f lo₀ hi₀ hinit n).1
theorem bisectHi_le (f : Q' → Q') (lo₀ hi₀ : Q') (hinit : BisectInit f lo₀ hi₀) (n : Nat) :
    bisectHi f lo₀ hi₀ n ≤ hi₀ := (bisectInv f lo₀ hi₀ hinit n).2.1
theorem bisectLo_le_bisectHi (f : Q' → Q') (lo₀ hi₀ : Q') (hinit : BisectInit f lo₀ hi₀) (n : Nat) :
    bisectLo f lo₀ hi₀ n ≤ bisectHi f lo₀ hi₀ n := (bisectInv f lo₀ hi₀ hinit n).2.2.1
theorem bisectLo_sign (f : Q' → Q') (lo₀ hi₀ : Q') (hinit : BisectInit f lo₀ hi₀) (n : Nat) :
    f (bisectLo f lo₀ hi₀ n) ≤ 0 := (bisectInv f lo₀ hi₀ hinit n).2.2.2.1
theorem bisectHi_sign (f : Q' → Q') (lo₀ hi₀ : Q') (hinit : BisectInit f lo₀ hi₀) (n : Nat) :
    (0 : Q') ≤ f (bisectHi f lo₀ hi₀ n) := (bisectInv f lo₀ hi₀ hinit n).2.2.2.2

/-! ### Monotonicity of the endpoints -/

theorem bisectLo_le_succ (f : Q' → Q') (lo₀ hi₀ : Q') (hinit : BisectInit f lo₀ hi₀) (n : Nat) :
    bisectLo f lo₀ hi₀ n ≤ bisectLo f lo₀ hi₀ (n + 1) := by
  have hle := bisectLo_le_bisectHi f lo₀ hi₀ hinit n
  have hloeq : bisectLo f lo₀ hi₀ (n + 1) =
      (if f (half * ((bisectSeq f lo₀ hi₀ n).1 + (bisectSeq f lo₀ hi₀ n).2)) ≤ 0
        then (half * ((bisectSeq f lo₀ hi₀ n).1 + (bisectSeq f lo₀ hi₀ n).2), (bisectSeq f lo₀ hi₀ n).2)
        else ((bisectSeq f lo₀ hi₀ n).1, half * ((bisectSeq f lo₀ hi₀ n).1 + (bisectSeq f lo₀ hi₀ n).2))).1 := rfl
  by_cases hc : f (half * ((bisectSeq f lo₀ hi₀ n).1 + (bisectSeq f lo₀ hi₀ n).2)) ≤ 0
  · rw [hloeq, if_pos hc]; exact CReal.le_mid hle
  · rw [hloeq, if_neg hc]; exact Q'.le_refl' _

theorem bisectHi_succ_le (f : Q' → Q') (lo₀ hi₀ : Q') (hinit : BisectInit f lo₀ hi₀) (n : Nat) :
    bisectHi f lo₀ hi₀ (n + 1) ≤ bisectHi f lo₀ hi₀ n := by
  have hle := bisectLo_le_bisectHi f lo₀ hi₀ hinit n
  have hhieq : bisectHi f lo₀ hi₀ (n + 1) =
      (if f (half * ((bisectSeq f lo₀ hi₀ n).1 + (bisectSeq f lo₀ hi₀ n).2)) ≤ 0
        then (half * ((bisectSeq f lo₀ hi₀ n).1 + (bisectSeq f lo₀ hi₀ n).2), (bisectSeq f lo₀ hi₀ n).2)
        else ((bisectSeq f lo₀ hi₀ n).1, half * ((bisectSeq f lo₀ hi₀ n).1 + (bisectSeq f lo₀ hi₀ n).2))).2 := rfl
  by_cases hc : f (half * ((bisectSeq f lo₀ hi₀ n).1 + (bisectSeq f lo₀ hi₀ n).2)) ≤ 0
  · rw [hhieq, if_pos hc]; exact Q'.le_refl' _
  · rw [hhieq, if_neg hc]; exact CReal.mid_le hle

theorem bisectLo_mono_add (f : Q' → Q') (lo₀ hi₀ : Q') (hinit : BisectInit f lo₀ hi₀) (n : Nat) :
    ∀ d, bisectLo f lo₀ hi₀ n ≤ bisectLo f lo₀ hi₀ (n + d)
  | 0 => Q'.le_refl' _
  | d + 1 => by
      refine Q'.le_trans' _ _ _ (bisectLo_mono_add f lo₀ hi₀ hinit n d) ?_
      rw [show n + (d + 1) = (n + d) + 1 from by omega]
      exact bisectLo_le_succ f lo₀ hi₀ hinit (n + d)

theorem bisectLo_mono (f : Q' → Q') (lo₀ hi₀ : Q') (hinit : BisectInit f lo₀ hi₀) {n m : Nat}
    (h : n ≤ m) : bisectLo f lo₀ hi₀ n ≤ bisectLo f lo₀ hi₀ m := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  exact bisectLo_mono_add f lo₀ hi₀ hinit n d

theorem bisectHi_anti_add (f : Q' → Q') (lo₀ hi₀ : Q') (hinit : BisectInit f lo₀ hi₀) (n : Nat) :
    ∀ d, bisectHi f lo₀ hi₀ (n + d) ≤ bisectHi f lo₀ hi₀ n
  | 0 => Q'.le_refl' _
  | d + 1 => by
      refine Q'.le_trans' _ _ _ ?_ (bisectHi_anti_add f lo₀ hi₀ hinit n d)
      rw [show n + (d + 1) = (n + d) + 1 from by omega]
      exact bisectHi_succ_le f lo₀ hi₀ hinit (n + d)

theorem bisectHi_anti (f : Q' → Q') (lo₀ hi₀ : Q') (hinit : BisectInit f lo₀ hi₀) {n m : Nat}
    (h : n ≤ m) : bisectHi f lo₀ hi₀ m ≤ bisectHi f lo₀ hi₀ n := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  exact bisectHi_anti_add f lo₀ hi₀ hinit n d

/-! ## The Cauchy modulus and the located root as a `CReal` -/

theorem bisectWidth0_nonneg {f : Q' → Q'} {lo₀ hi₀ : Q'} (hinit : BisectInit f lo₀ hi₀) :
    (0 : Q') ≤ hi₀ + -lo₀ := by
  have := Q'.add_le_add_right lo₀ hi₀ (-lo₀) hinit.loLeHi
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.add_neg_self_eqv lo₀)) this

/-- The Cauchy modulus: a stage past which the width is `≤ ε`. -/
def bisectModulus (f : Q' → Q') (lo₀ hi₀ : Q') (hinit : BisectInit f lo₀ hi₀)
    (ε : Q') (hε : (0 : Q') < ε) : Nat :=
  (mulModulus (hi₀ + -lo₀) ε (bisectWidth0_nonneg hinit) hε).1.den

theorem bisectWidth_modulus_le (f : Q' → Q') (lo₀ hi₀ : Q') (hinit : BisectInit f lo₀ hi₀)
    (ε : Q') (hε : (0 : Q') < ε) :
    bisectWidth f lo₀ hi₀ (bisectModulus f lo₀ hi₀ hinit ε hε) ≤ ε := by
  have hWnn : (0 : Q') ≤ hi₀ + -lo₀ := bisectWidth0_nonneg hinit
  let md := mulModulus (hi₀ + -lo₀) ε hWnn hε
  have hδpos : (0 : Q') < md.1 := md.2.1
  have hδle : (hi₀ + -lo₀) * md.1 ≤ ε := md.2.2
  show bisectWidth f lo₀ hi₀ md.1.den ≤ ε
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (bisectWidth_eq_geom f lo₀ hi₀ md.1.den)) ?_
  refine Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left (half ^ md.1.den) md.1 (hi₀ + -lo₀)
      (HalfPow.pow_half_le md.1 hδpos) hWnn) ?_
  exact hδle

theorem bisectLo_close (f : Q' → Q') (lo₀ hi₀ : Q') (hinit : BisectInit f lo₀ hi₀) {N p q : Nat}
    (hNp : N ≤ p) (hNq : N ≤ q) :
    bisectLo f lo₀ hi₀ p ≤ bisectLo f lo₀ hi₀ q + bisectWidth f lo₀ hi₀ N := by
  have h1 : bisectLo f lo₀ hi₀ p ≤ bisectHi f lo₀ hi₀ N :=
    Q'.le_trans' _ _ _ (bisectLo_le_bisectHi f lo₀ hi₀ hinit p) (bisectHi_anti f lo₀ hi₀ hinit hNp)
  have h2 : bisectLo f lo₀ hi₀ N ≤ bisectLo f lo₀ hi₀ q := bisectLo_mono f lo₀ hi₀ hinit hNq
  have h3 : bisectHi f lo₀ hi₀ N ≤ bisectLo f lo₀ hi₀ q + bisectWidth f lo₀ hi₀ N := by
    show bisectHi f lo₀ hi₀ N ≤ bisectLo f lo₀ hi₀ q + (bisectHi f lo₀ hi₀ N + -(bisectLo f lo₀ hi₀ N))
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.add_sub_cancel_eqv (bisectHi f lo₀ hi₀ N) (bisectLo f lo₀ hi₀ N))) ?_
    exact Q'.add_le_add_right (bisectLo f lo₀ hi₀ N) (bisectLo f lo₀ hi₀ q)
      (bisectHi f lo₀ hi₀ N + -(bisectLo f lo₀ hi₀ N)) h2
  exact Q'.le_trans' _ _ _ h1 h3

/-- **The located root** of `f` as a `CReal` (lower endpoints; halving modulus). -/
def bisectRoot (f : Q' → Q') (lo₀ hi₀ : Q') (hinit : BisectInit f lo₀ hi₀) : CReal where
  approx n := bisectLo f lo₀ hi₀ n
  cauchy := by
    intro ε hε
    refine ⟨bisectModulus f lo₀ hi₀ hinit ε hε, fun p q hp hq => ?_⟩
    have hwle : bisectWidth f lo₀ hi₀ (bisectModulus f lo₀ hi₀ hinit ε hε) ≤ ε :=
      bisectWidth_modulus_le f lo₀ hi₀ hinit ε hε
    refine ⟨?_, ?_⟩
    · exact Q'.le_trans' _ _ _ (bisectLo_close f lo₀ hi₀ hinit hp hq)
        (Q'.add_le_add_left (bisectLo f lo₀ hi₀ q)
          (bisectWidth f lo₀ hi₀ (bisectModulus f lo₀ hi₀ hinit ε hε)) ε hwle)
    · exact Q'.le_trans' _ _ _ (bisectLo_close f lo₀ hi₀ hinit hq hp)
        (Q'.add_le_add_left (bisectLo f lo₀ hi₀ p)
          (bisectWidth f lo₀ hi₀ (bisectModulus f lo₀ hi₀ hinit ε hε)) ε hwle)

@[simp] theorem bisectRoot_approx (f : Q' → Q') (lo₀ hi₀ : Q') (hinit : BisectInit f lo₀ hi₀)
    (n : Nat) : (bisectRoot f lo₀ hi₀ hinit).approx n = bisectLo f lo₀ hi₀ n := rfl

/-! ## The located root is a genuine zero of `f`

We need a one-sided Lipschitz bound on `[lo₀,hi₀]`:
`f(b) − f(a) ≤ Lip·(b − a)` for `lo₀ ≤ a ≤ b ≤ hi₀`.  Combined with the located
invariant `f(lo) ≤ 0 ≤ f(hi)` and `width → 0`, this squeezes `f(root) ≃ 0`.
This is the analogue of `cube_diff_le`. -/

/-- Two-sided Lipschitz datum for `f` on `[lo₀,hi₀]` with constant `Lip ≥ 0`:
`|f(b) − f(a)| ≤ Lip·(b − a)` for `lo₀ ≤ a ≤ b ≤ hi₀`.  Two-sidedness is the
honest requirement: the squeeze uses `f(b) − f(a) ≤ Lip·(b−a)`, while the Cauchy
modulus of the `f(lo_n)` sequence needs the reverse `f(a) − f(b) ≤ Lip·(b−a)`. -/
structure LipBound (f : Q' → Q') (lo₀ hi₀ Lip : Q') : Prop where
  nonneg : (0 : Q') ≤ Lip
  bound : ∀ a b : Q', lo₀ ≤ a → a ≤ b → b ≤ hi₀ → f b + -(f a) ≤ Lip * (b + -a)
  bound' : ∀ a b : Q', lo₀ ≤ a → a ≤ b → b ≤ hi₀ → f a + -(f b) ≤ Lip * (b + -a)

theorem bisectWidth_antitone (f : Q' → Q') (lo₀ hi₀ : Q') (hinit : BisectInit f lo₀ hi₀)
    {N n : Nat} (h : N ≤ n) : bisectWidth f lo₀ hi₀ n ≤ bisectWidth f lo₀ hi₀ N := by
  show bisectHi f lo₀ hi₀ n + -(bisectLo f lo₀ hi₀ n) ≤ bisectHi f lo₀ hi₀ N + -(bisectLo f lo₀ hi₀ N)
  refine Q'.add_le_add (bisectHi_anti f lo₀ hi₀ hinit h) ?_
  exact Q'.neg_le_neg (bisectLo_mono f lo₀ hi₀ hinit h)

/-- `(a + -b) + b ≃ a`. -/
private theorem sub_add_cancel_eqv (a b : Q') : ((a + -b) + b) ≈ a := by
  refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv a (-b) b) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left a (-b + b) 0 (Q'.neg_add_self_eqv b)) ?_
  exact Q'.eqv_of_eq (Q'.add_zero' a)

/-- `(a + b) + -b ≃ a`. -/
private theorem add_sub_cancel_eqv' (a b : Q') : ((a + b) + -b) ≈ a := by
  refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv a b (-b)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left a (b + -b) 0 (Q'.add_neg_self_eqv b)) ?_
  exact Q'.eqv_of_eq (Q'.add_zero' a)

/-- From `p + -q ≤ ε` conclude `p ≤ q + ε`. -/
private theorem le_add_of_sub_le {p q ε : Q'} (h : p + -q ≤ ε) : p ≤ q + ε := by
  have hstep := Q'.add_le_add_right _ ε q h
  refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv (sub_add_cancel_eqv p q)) ?_
  exact Q'.le_trans' _ _ _ hstep (Q'.le_of_eqv (Q'.add_comm_eqv ε q))

/-- The closeness of two lower endpoints past the modulus: `lo_r ≤ lo_s + δ` and
`lo_s ≤ lo_r + δ` whenever both indices clear the `δ`-modulus. -/
private theorem lo_diff_le {f : Q' → Q'} {lo₀ hi₀ : Q'} (hinit : BisectInit f lo₀ hi₀)
    {δ : Q'} (hδpos : (0 : Q') < δ) {r s : Nat}
    (hr : bisectModulus f lo₀ hi₀ hinit δ hδpos ≤ r)
    (hs : bisectModulus f lo₀ hi₀ hinit δ hδpos ≤ s)
    (hsr : bisectLo f lo₀ hi₀ s ≤ bisectLo f lo₀ hi₀ r) :
    bisectLo f lo₀ hi₀ r + -(bisectLo f lo₀ hi₀ s) ≤ δ := by
  have hclose := bisectLo_close f lo₀ hi₀ hinit hr hs
  have hwle : bisectWidth f lo₀ hi₀ (bisectModulus f lo₀ hi₀ hinit δ hδpos) ≤ δ :=
    bisectWidth_modulus_le f lo₀ hi₀ hinit δ hδpos
  have h1 : bisectLo f lo₀ hi₀ r + -(bisectLo f lo₀ hi₀ s)
      ≤ (bisectLo f lo₀ hi₀ s + bisectWidth f lo₀ hi₀ (bisectModulus f lo₀ hi₀ hinit δ hδpos))
          + -(bisectLo f lo₀ hi₀ s) :=
    Q'.add_le_add_right _ _ _ hclose
  refine Q'.le_trans' _ _ _ h1 ?_
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv ?_) hwle
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ (-(bisectLo f lo₀ hi₀ s))
      (Q'.add_comm_eqv (bisectLo f lo₀ hi₀ s)
        (bisectWidth f lo₀ hi₀ (bisectModulus f lo₀ hi₀ hinit δ hδpos)))) ?_
  exact add_sub_cancel_eqv' _ _

/-- **The `f(lo_n)` sequence as a `CReal`.**  Cauchy via the two-sided Lipschitz
bound: for endpoints past the `δ`-modulus, `|f(lo_p) − f(lo_q)| ≤ Lip·δ ≤ ε`. -/
def bisectFLo (f : Q' → Q') (lo₀ hi₀ Lip : Q') (hinit : BisectInit f lo₀ hi₀)
    (hlip : LipBound f lo₀ hi₀ Lip) : CReal where
  approx n := f (bisectLo f lo₀ hi₀ n)
  cauchy := by
    intro ε hε
    obtain ⟨δ, hδpos, hδle⟩ := CReal.exists_mul_le hlip.nonneg hε
    refine ⟨bisectModulus f lo₀ hi₀ hinit δ hδpos, fun p q hp hq => ?_⟩
    -- `key dir`: when `lo_s ≤ lo_r`, `f(lo_r) ≤ f(lo_s) + ε` (dir = the +Lip side),
    -- and `f(lo_s) ≤ f(lo_r) + ε` (the −Lip side); both from the two-sided Lip.
    have key : ∀ r s : Nat,
        bisectModulus f lo₀ hi₀ hinit δ hδpos ≤ r →
        bisectModulus f lo₀ hi₀ hinit δ hδpos ≤ s →
        bisectLo f lo₀ hi₀ s ≤ bisectLo f lo₀ hi₀ r →
        f (bisectLo f lo₀ hi₀ r) ≤ f (bisectLo f lo₀ hi₀ s) + ε
          ∧ f (bisectLo f lo₀ hi₀ s) ≤ f (bisectLo f lo₀ hi₀ r) + ε := by
      intro r s hr hs hsr
      have hloge_s : lo₀ ≤ bisectLo f lo₀ hi₀ s := bisectLo_ge f lo₀ hi₀ hinit s
      have hrhi : bisectLo f lo₀ hi₀ r ≤ hi₀ :=
        Q'.le_trans' _ _ _ (bisectLo_le_bisectHi f lo₀ hi₀ hinit r) (bisectHi_le f lo₀ hi₀ hinit r)
      have hdiffle : bisectLo f lo₀ hi₀ r + -(bisectLo f lo₀ hi₀ s) ≤ δ :=
        lo_diff_le hinit hδpos hr hs hsr
      have hLipδ : Lip * (bisectLo f lo₀ hi₀ r + -(bisectLo f lo₀ hi₀ s)) ≤ ε :=
        Q'.le_trans' _ _ _
          (Q'.mul_le_mul_of_nonneg_left _ δ Lip hdiffle hlip.nonneg) hδle
      refine ⟨?_, ?_⟩
      · -- f(lo_r) − f(lo_s) ≤ Lip·(lo_r − lo_s) ≤ ε
        have hb := hlip.bound (bisectLo f lo₀ hi₀ s) (bisectLo f lo₀ hi₀ r) hloge_s hsr hrhi
        exact le_add_of_sub_le (Q'.le_trans' _ _ _ hb hLipδ)
      · -- f(lo_s) − f(lo_r) ≤ Lip·(lo_r − lo_s) ≤ ε
        have hb := hlip.bound' (bisectLo f lo₀ hi₀ s) (bisectLo f lo₀ hi₀ r) hloge_s hsr hrhi
        exact le_add_of_sub_le (Q'.le_trans' _ _ _ hb hLipδ)
    by_cases hcase : bisectLo f lo₀ hi₀ q ≤ bisectLo f lo₀ hi₀ p
    · exact ⟨(key p q hp hq hcase).1, (key p q hp hq hcase).2⟩
    · have hle : bisectLo f lo₀ hi₀ p ≤ bisectLo f lo₀ hi₀ q := Q'.le_of_not_le hcase
      exact ⟨(key q p hq hp hle).2, (key q p hq hp hle).1⟩

@[simp] theorem bisectFLo_approx (f : Q' → Q') (lo₀ hi₀ Lip : Q') (hinit : BisectInit f lo₀ hi₀)
    (hlip : LipBound f lo₀ hi₀ Lip) (n : Nat) :
    (bisectFLo f lo₀ hi₀ Lip hinit hlip).approx n = f (bisectLo f lo₀ hi₀ n) := rfl

/-- **`f(root) ≃ 0`.**  The CReal `bisectFLo` (approximations `f(lo_n)`) is
`Equiv` to `0`.  Squeeze: `f(lo) ≤ 0 ≤ f(hi)` and `f(hi) − f(lo) ≤ Lip·width →
0`, so `−ε ≤ f(lo) ≤ 0`. -/
theorem bisectRoot_eval_zero (f : Q' → Q') (lo₀ hi₀ Lip : Q') (hinit : BisectInit f lo₀ hi₀)
    (hlip : LipBound f lo₀ hi₀ Lip) :
    CReal.Equiv (bisectFLo f lo₀ hi₀ Lip hinit hlip) 0 := by
  -- Now the Equiv-to-0 squeeze.
  intro ε hε
  obtain ⟨δ, hδpos, hδle⟩ := CReal.exists_mul_le hlip.nonneg hε
  refine ⟨bisectModulus f lo₀ hi₀ hinit δ hδpos, fun n hn => ?_⟩
  -- approx n = f(lo_n);  f(lo_n) ≤ 0 ≤ f(hi_n);  f(hi_n) − f(lo_n) ≤ Lip·width ≤ ε
  have hlosgn : f (bisectLo f lo₀ hi₀ n) ≤ 0 := bisectLo_sign f lo₀ hi₀ hinit n
  have hhisgn : (0 : Q') ≤ f (bisectHi f lo₀ hi₀ n) := bisectHi_sign f lo₀ hi₀ hinit n
  have hloge : lo₀ ≤ bisectLo f lo₀ hi₀ n := bisectLo_ge f lo₀ hi₀ hinit n
  have hhile : bisectHi f lo₀ hi₀ n ≤ hi₀ := bisectHi_le f lo₀ hi₀ hinit n
  have hle : bisectLo f lo₀ hi₀ n ≤ bisectHi f lo₀ hi₀ n := bisectLo_le_bisectHi f lo₀ hi₀ hinit n
  -- f(hi)−f(lo) ≤ Lip·width
  have hb := hlip.bound (bisectLo f lo₀ hi₀ n) (bisectHi f lo₀ hi₀ n) hloge hle hhile
  have hwle : bisectWidth f lo₀ hi₀ n ≤ δ := by
    refine Q'.le_trans' _ _ _ (bisectWidth_antitone f lo₀ hi₀ hinit hn) ?_
    exact bisectWidth_modulus_le f lo₀ hi₀ hinit δ hδpos
  have hLipw : Lip * (bisectHi f lo₀ hi₀ n + -(bisectLo f lo₀ hi₀ n)) ≤ ε :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ δ Lip hwle hlip.nonneg) hδle
  have hdiff : f (bisectHi f lo₀ hi₀ n) + -(f (bisectLo f lo₀ hi₀ n)) ≤ ε :=
    Q'.le_trans' _ _ _ hb hLipw
  -- goal: approx n ≤ 0 + ε ∧ 0 ≤ approx n + ε , approx n = f(lo_n)
  refine ⟨?_, ?_⟩
  · -- f(lo) ≤ 0 ≤ 0 + ε
    show f (bisectLo f lo₀ hi₀ n) ≤ (0 : Q') + ε
    refine Q'.le_trans' _ _ _ hlosgn ?_
    refine Q'.le_trans' _ _ _ (Q'.le_of_lt hε) (Q'.ge_of_eqv ?_)
    exact Q'.eqv_of_eq (Q'.zero_add' ε)
  · -- 0 ≤ f(lo) + ε.  Since f(hi) ≥ 0 and f(hi) − f(lo) ≤ ε ⟹ f(lo) ≥ f(hi) − ε ≥ −ε
    show (0 : Q') ≤ f (bisectLo f lo₀ hi₀ n) + ε
    -- f(hi) ≤ f(lo) + ε  (from hdiff), and 0 ≤ f(hi)
    have hstep : f (bisectHi f lo₀ hi₀ n) ≤ f (bisectLo f lo₀ hi₀ n) + ε := by
      have := Q'.add_le_add_right _ ε (f (bisectLo f lo₀ hi₀ n)) hdiff
      refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv ?_) (Q'.le_trans' _ _ _ this (Q'.le_of_eqv ?_))
      · refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv (f (bisectHi f lo₀ hi₀ n))
          (-(f (bisectLo f lo₀ hi₀ n))) (f (bisectLo f lo₀ hi₀ n))) ?_
        refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ 0
          (Q'.neg_add_self_eqv (f (bisectLo f lo₀ hi₀ n)))) ?_
        exact Q'.eqv_of_eq (Q'.add_zero' _)
      · exact Q'.add_comm_eqv ε (f (bisectLo f lo₀ hi₀ n))
    exact Q'.le_trans' _ _ _ hhisgn hstep

/-! ## Unit enclosure and strict interior of the root -/

/-- The root lies in `[lo₀, hi₀]` (CReal one-slack order, in `ofQ'` form). -/
theorem bisectRoot_in_bracket (f : Q' → Q') (lo₀ hi₀ : Q') (hinit : BisectInit f lo₀ hi₀) :
    CReal.ofQ' lo₀ ≤ bisectRoot f lo₀ hi₀ hinit ∧
    bisectRoot f lo₀ hi₀ hinit ≤ CReal.ofQ' hi₀ := by
  refine ⟨?_, ?_⟩
  · exact CReal.ofQ'_le_of_approx_ge (fun n => bisectLo_ge f lo₀ hi₀ hinit n)
  · refine CReal.le_ofQ'_of_approx_le (fun n => ?_)
    exact Q'.le_trans' _ _ _ (bisectLo_le_bisectHi f lo₀ hi₀ hinit n) (bisectHi_le f lo₀ hi₀ hinit n)

/-! ### Strict-positivity strict-interior witnesses

`root + 1 > 0` and `1 − root > 0` (as `CReal.IsPositive`), the genuine strict
`−1 < root < 1` needed for the weight `1 − x² > 0`.  They hold when the bracket
sits strictly inside `(−1,1)`: `−1 < lo₀` and `hi₀ < 1` (rational strict bounds
giving a positive gap). -/

theorem bisectRoot_plus_one_pos (f : Q' → Q') (lo₀ hi₀ : Q') (hinit : BisectInit f lo₀ hi₀)
    (g : Q') (hg : (0 : Q') < g) (hglo : g + -1 ≤ lo₀) :
    CReal.IsPositive (CReal.add (bisectRoot f lo₀ hi₀ hinit) (CReal.neg (CReal.ofQ' (-1)))) := by
  -- approx n of (root − (−1)) = lo_n + 1 ≥ lo₀ + 1 ≥ g > 0
  refine CReal.isPositive_of_approx_ge hg (fun n => ?_)
  show g ≤ bisectLo f lo₀ hi₀ n + (-(-1 : Q'))
  -- g ≤ lo₀ + 1 ≤ lo_n + 1
  have h1 : g ≤ lo₀ + 1 := by
    have := Q'.add_le_add_right _ _ (1 : Q') hglo
    refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv ?_) this
    -- (g + -1) + 1 ≃ g
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv g (-1) 1) ?_
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left g (-1 + 1) 0
      (Q'.neg_add_self_eqv 1)) ?_
    exact Q'.eqv_of_eq (Q'.add_zero' g)
  have h2 : lo₀ + 1 ≤ bisectLo f lo₀ hi₀ n + 1 :=
    Q'.add_le_add_right lo₀ _ 1 (bisectLo_ge f lo₀ hi₀ hinit n)
  refine Q'.le_trans' _ _ _ (Q'.le_trans' _ _ _ h1 h2) (Q'.le_of_eqv ?_)
  -- lo_n + 1 ≃ lo_n + -(-1)
  exact Q'.add_eqv_congr_left (bisectLo f lo₀ hi₀ n) 1 (-(-1 : Q')) (by decide)

theorem bisectRoot_one_sub_pos (f : Q' → Q') (lo₀ hi₀ : Q') (hinit : BisectInit f lo₀ hi₀)
    (g : Q') (hg : (0 : Q') < g) (hghi : hi₀ ≤ 1 + -g) :
    CReal.IsPositive (CReal.add (CReal.ofQ' 1) (CReal.neg (bisectRoot f lo₀ hi₀ hinit))) := by
  -- approx n of (1 − root) = 1 + -lo_n ≥ 1 + -hi_n ≥ g > 0  (since lo_n ≤ hi_n ≤ hi₀ ≤ 1 − g)
  refine CReal.isPositive_of_approx_ge hg (fun n => ?_)
  show g ≤ (1 : Q') + -(bisectLo f lo₀ hi₀ n)
  -- lo_n ≤ hi₀ ≤ 1 − g, so 1 − lo_n ≥ 1 − (1−g) = g
  have hloHi : bisectLo f lo₀ hi₀ n ≤ 1 + -g :=
    Q'.le_trans' _ _ _ (Q'.le_trans' _ _ _ (bisectLo_le_bisectHi f lo₀ hi₀ hinit n)
      (bisectHi_le f lo₀ hi₀ hinit n)) hghi
  -- 1 + -lo_n ≥ 1 + -(1 + -g) = g
  have hstep : (1 : Q') + -(1 + -g) ≤ (1 : Q') + -(bisectLo f lo₀ hi₀ n) :=
    Q'.add_le_add_left 1 _ _ (Q'.neg_le_neg hloHi)
  refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv ?_) hstep
  -- 1 + -(1 + -g) ≃ g
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left 1 (-(1 + -g)) ((-1) + g) ?_) ?_
  · -- -(1 + -g) ≃ -1 + g
    refine Q'.eqv_trans _ _ _ (Q'.neg_add_eqv 1 (-g)) ?_
    exact Q'.add_eqv_congr_left (-1) (-(-g)) g (Q'.neg_neg_eqv g)
  · -- 1 + (-1 + g) ≃ g
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv 1 (-1) g)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right (1 + -1) 0 g (Q'.add_neg_self_eqv 1)) ?_
    exact Q'.eqv_of_eq (Q'.zero_add' g)

/-! ## Square-difference helper (reused for the small-`M` Lipschitz bounds) -/

/-- `u*u + -(v*v) ≃ (u + -v)*(u + v)`. -/
theorem sq_diff_eqv (u v : Q') : (u * u + -(v * v)) ≈ ((u + -v) * (u + v)) := by
  refine Q'.eqv_symm ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv u (-v) (u + v)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right (u * (u + v)) (u * u + u * v) ((-v) * (u + v))
      (Q'.mul_add_eqv u u v)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (u * u + u * v) ((-v) * (u + v)) (-(v * u) + -(v * v))
      (Q'.eqv_trans _ _ _ (Q'.mul_add_eqv (-v) u v)
        (QPoly.q_add_congr (Q'.neg_mul_eqv v u) (Q'.neg_mul_eqv v v)))) ?_
  -- (uu + uv) + (-(vu) + -(vv)) ; -(vu) ≃ -(uv)
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (u * u + u * v) (-(v * u) + -(v * v)) (-(u * v) + -(v * v))
      (Q'.add_eqv_congr_right (-(v * u)) (-(u * v)) (-(v * v))
        (Q'.neg_eqv_congr _ _ (Q'.mul_comm_eqv v u)))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (u * u + u * v) (-(u * v) + -(v * v)) (-(v * v) + -(u * v))
      (Q'.add_comm_eqv (-(u * v)) (-(v * v)))) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_swap_inner (u * u) (u * v) (-(v * v)) (-(u * v))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (u * u + -(v * v)) (u * v + -(u * v)) 0
      (Q'.add_neg_self_eqv (u * v))) ?_
  exact Q'.eqv_of_eq (Q'.add_zero' (u * u + -(v * v)))

/-! ## Worst-case small orders `M = 2, 3` (genuine located Gauss–Chebyshev nodes)

We instantiate the generic bisection at `Ueval M` for the small orders, with
explicit rational sign-change brackets (signs checked by `decide` on the closed
`Q'` values) and explicit Lipschitz constants proved from the recurrence-given
polynomial forms.  The general-`M` bracketing is the NAMED-open residual. -/

/-- `(2/5, 3/5)` is a sign-change bracket of `U_2` inside `(−1,1)`:
`U_2(2/5) < 0 < U_2(3/5)` (root at `x = 1/2 = cos(π/3)`). -/
def lo2 : Q' := Q'.mkPos 2 5 (by decide)
def hi2 : Q' := Q'.mkPos 3 5 (by decide)

theorem ueval2_lo : Ueval 2 lo2 ≤ 0 := by decide
theorem ueval2_hi : (0 : Q') ≤ Ueval 2 hi2 := by decide

/-- `U_2` two-sided Lipschitz on `[2/5,3/5]` with `Lip = 8`:
`U_2(b) − U_2(a) = (2b)²−(2a)² = (2b+2a)(2b−2a)`, bounded by `8(b−a)`. -/
theorem ueval2_lip : LipBound (Ueval 2) lo2 hi2 (Q'.ofNat 8) where
  nonneg := by decide
  bound := by
    intro a b ha hab hb
    -- U_2(b)+-(U_2(a)) = ((2b)(2b)+-1)+-((2a)(2a)+-1) ≈ (2b)(2b) + -((2a)(2a))
    have hcancel : Ueval 2 b + -(Ueval 2 a)
        ≈ ((2:Q')*b)*((2:Q')*b) + -(((2:Q')*a)*((2:Q')*a)) := by
      show (((2:Q')*b)*((2:Q')*b) + -1) + -(((2:Q')*a)*((2:Q')*a) + -1)
          ≈ ((2:Q')*b)*((2:Q')*b) + -(((2:Q')*a)*((2:Q')*a))
      -- -(P + -1) ≃ -P + 1
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left _ (-(((2:Q')*a)*((2:Q')*a) + -1))
          (-(((2:Q')*a)*((2:Q')*a)) + 1)
          (Q'.eqv_trans _ _ _ (Q'.neg_add_eqv (((2:Q')*a)*((2:Q')*a)) (-1))
            (Q'.add_eqv_congr_left _ (-(-1:Q')) 1 (Q'.neg_neg_eqv 1)))) ?_
      -- (X + -1) + (-Y + 1) ≃ X + -Y
      refine Q'.eqv_trans _ _ _
        (Q'.add_swap_inner (((2:Q')*b)*((2:Q')*b)) (-1) (-(((2:Q')*a)*((2:Q')*a))) 1) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left _ ((-1:Q') + 1) 0 (Q'.neg_add_self_eqv 1)) ?_
      exact Q'.eqv_of_eq (Q'.add_zero' _)
    -- ≈ ((2b)+ -(2a))*((2b)+(2a))
    have hfac : Ueval 2 b + -(Ueval 2 a)
        ≈ (((2:Q')*b) + -((2:Q')*a)) * (((2:Q')*b) + ((2:Q')*a)) :=
      Q'.eqv_trans _ _ _ hcancel (sq_diff_eqv ((2:Q')*b) ((2:Q')*a))
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hfac) ?_
    -- (2b + -(2a)) ≃ 2*(b + -a) ≥ 0 ; (2b + 2a) ≤ ofNat 4
    have hdnn : (0 : Q') ≤ ((2:Q')*b) + -((2:Q')*a) := by
      have : ((2:Q')*a) ≤ ((2:Q')*b) := Q'.mul_le_mul_of_nonneg_left a b 2 hab (by decide)
      have h := Q'.add_le_add_right ((2:Q')*a) ((2:Q')*b) (-((2:Q')*a)) this
      exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.add_neg_self_eqv ((2:Q')*a))) h
    have hb1 : b ≤ 1 := Q'.le_trans' _ _ _ hb (by decide)
    have ha1 : a ≤ 1 := Q'.le_trans' _ _ _ hab hb1
    have hsum_le : ((2:Q')*b) + ((2:Q')*a) ≤ Q'.ofNat 4 := by
      have h2b : (2:Q')*b ≤ (2:Q')*1 := Q'.mul_le_mul_of_nonneg_left b 1 2 hb1 (by decide)
      have h2a : (2:Q')*a ≤ (2:Q')*1 := Q'.mul_le_mul_of_nonneg_left a 1 2 ha1 (by decide)
      refine Q'.le_trans' _ _ _ (Q'.add_le_add h2b h2a) (Q'.le_of_eqv (by decide))
    -- (2b + -(2a))*(2b+2a) ≤ (2b + -(2a))*ofNat 4 = ofNat 8 * (b + -a)
    refine Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ (Q'.ofNat 4) _ hsum_le hdnn) ?_
    -- (2b + -(2a))*ofNat 4 ≤ ofNat 8 * (b + -a)  (in fact ≈)
    refine Q'.le_of_eqv ?_
    -- (2(b)+ -(2 a)) ≈ 2*(b + -a) ; times 4 ≈ 8*(b+-a)
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right (((2:Q')*b) + -((2:Q')*a)) ((2:Q') * (b + -a)) (Q'.ofNat 4) ?_) ?_
    · -- 2b + -(2a) ≈ 2*(b + -a)
      refine Q'.eqv_symm ?_
      refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv 2 b (-a)) ?_
      exact Q'.add_eqv_congr_left ((2:Q')*b) ((2:Q') * -a) (-((2:Q')*a)) (Q'.mul_neg_eqv 2 a)
    · -- (2*(b+-a))*ofNat 4 ≈ ofNat 8 * (b+-a)
      refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv ((2:Q') * (b + -a)) (Q'.ofNat 4)) ?_
      refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat 4) 2 (b + -a))) ?_
      exact Q'.mul_eqv_congr_right (Q'.ofNat 4 * 2) (Q'.ofNat 8) (b + -a) (by decide)
  bound' := by
    intro a b ha hab hb
    -- U_2(a) − U_2(b) = -(U_2(b) − U_2(a)) ≤ 0 ≤ 8(b−a).  LHS ≤ 0 since b ≥ a ⟹ U_2 incr here.
    -- Direct: U_2(a)+-(U_2(b)) ≈ (2a + -(2b))*(2a+2b) ≤ 0 ≤ ofNat 8*(b+-a).
    have hfac : Ueval 2 a + -(Ueval 2 b)
        ≈ (((2:Q')*a) + -((2:Q')*b)) * (((2:Q')*a) + ((2:Q')*b)) := by
      have hcancel : Ueval 2 a + -(Ueval 2 b)
          ≈ ((2:Q')*a)*((2:Q')*a) + -(((2:Q')*b)*((2:Q')*b)) := by
        show (((2:Q')*a)*((2:Q')*a) + -1) + -(((2:Q')*b)*((2:Q')*b) + -1)
            ≈ ((2:Q')*a)*((2:Q')*a) + -(((2:Q')*b)*((2:Q')*b))
        refine Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_left _ (-(((2:Q')*b)*((2:Q')*b) + -1))
            (-(((2:Q')*b)*((2:Q')*b)) + 1)
            (Q'.eqv_trans _ _ _ (Q'.neg_add_eqv (((2:Q')*b)*((2:Q')*b)) (-1))
              (Q'.add_eqv_congr_left _ (-(-1:Q')) 1 (Q'.neg_neg_eqv 1)))) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.add_swap_inner (((2:Q')*a)*((2:Q')*a)) (-1) (-(((2:Q')*b)*((2:Q')*b))) 1) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_left _ ((-1:Q') + 1) 0 (Q'.neg_add_self_eqv 1)) ?_
        exact Q'.eqv_of_eq (Q'.add_zero' _)
      exact Q'.eqv_trans _ _ _ hcancel (sq_diff_eqv ((2:Q')*a) ((2:Q')*b))
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hfac) ?_
    -- (2a + -(2b)) ≤ 0 and (2a+2b) ≥ 0 ⟹ product ≤ 0 ≤ ofNat 8*(b+-a)
    have hfac_le : ((2:Q')*a) ≤ ((2:Q')*b) := Q'.mul_le_mul_of_nonneg_left a b 2 hab (by decide)
    have hneg : ((2:Q')*a) + -((2:Q')*b) ≤ 0 := by
      have h := Q'.add_le_add_right ((2:Q')*a) ((2:Q')*b) (-((2:Q')*b)) hfac_le
      refine Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.add_neg_self_eqv ((2:Q')*b)))
    have hpos : (0 : Q') ≤ ((2:Q')*a) + ((2:Q')*b) := by
      have h0a : (0:Q') ≤ a := Q'.le_trans' _ _ _ (by decide) ha
      have h0b : (0:Q') ≤ b := Q'.le_trans' _ _ _ h0a hab
      have h2a : (0:Q') ≤ (2:Q')*a := Q'.mul_nonneg 2 a (by decide) h0a
      have h2b : (0:Q') ≤ (2:Q')*b := Q'.mul_nonneg 2 b (by decide) h0b
      exact Q'.le_trans' _ _ _ h2a (Q'.add_le_self_of_nonneg ((2:Q')*a) ((2:Q')*b) h2b)
    have hprod : (((2:Q')*a) + -((2:Q')*b)) * (((2:Q')*a) + ((2:Q')*b)) ≤ 0 := by
      have := Q'.mul_le_mul_of_nonneg_right (((2:Q')*a) + -((2:Q')*b)) 0
        (((2:Q')*a) + ((2:Q')*b)) hneg hpos
      refine Q'.le_trans' _ _ _ this (Q'.le_of_eqv ?_)
      exact QPoly.q_zero_mul _
    refine Q'.le_trans' _ _ _ hprod ?_
    -- 0 ≤ ofNat 8 * (b + -a)
    have hdnn : (0 : Q') ≤ b + -a := by
      have h := Q'.add_le_add_right a b (-a) hab
      exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.add_neg_self_eqv a)) h
    exact Q'.mul_nonneg (Q'.ofNat 8) (b + -a) (by decide) hdnn

/-- The `BisectInit` datum for `U_2` on `[2/5,3/5]`. -/
theorem ueval2_init : BisectInit (Ueval 2) lo2 hi2 where
  loLeHi := by decide
  loSign := ueval2_lo
  hiSign := ueval2_hi

/-- **The located Gauss–Chebyshev node `x = 1/2 = cos(π/3)`** (the single root of
`U_2` in `(0,1)`), as a constructive real. -/
def chebRoot2 : CReal := bisectRoot (Ueval 2) lo2 hi2 ueval2_init

/-- **`U_2(chebRoot2) ≃ 0`** — the node is a genuine zero of `U_2`. -/
theorem chebRoot2_eval_zero :
    CReal.Equiv (bisectFLo (Ueval 2) lo2 hi2 (Q'.ofNat 8) ueval2_init ueval2_lip) 0 :=
  bisectRoot_eval_zero (Ueval 2) lo2 hi2 (Q'.ofNat 8) ueval2_init ueval2_lip

/-- The node lies in `[2/5,3/5] ⊂ (−1,1)`. -/
theorem chebRoot2_in_bracket :
    CReal.ofQ' lo2 ≤ chebRoot2 ∧ chebRoot2 ≤ CReal.ofQ' hi2 :=
  bisectRoot_in_bracket (Ueval 2) lo2 hi2 ueval2_init

/-- Strict interior: `chebRoot2 + 1 > 0` (positivity witness `g = 7/5`). -/
theorem chebRoot2_plus_one_pos :
    CReal.IsPositive (CReal.add chebRoot2 (CReal.neg (CReal.ofQ' (-1)))) :=
  bisectRoot_plus_one_pos (Ueval 2) lo2 hi2 ueval2_init (Q'.mkPos 7 5 (by decide))
    (by decide) (by decide)

/-- Strict interior: `1 − chebRoot2 > 0` (positivity witness `g = 2/5`). -/
theorem chebRoot2_one_sub_pos :
    CReal.IsPositive (CReal.add (CReal.ofQ' 1) (CReal.neg chebRoot2)) :=
  bisectRoot_one_sub_pos (Ueval 2) lo2 hi2 ueval2_init (Q'.mkPos 2 5 (by decide))
    (by decide) (by decide)

end YMGap.Continuum.ChebRoot

/-! ## Axiom-dependency gates (AGENTS.md Rule 1)

Every load-bearing declaration must report `[propext]` or `[propext, Quot.sound]`
(`Quot.sound` only via reused `omega`/`Nat`/`Int` helpers).  No `Classical.*`,
no `sorry`/`sorryAx`, no `native_decide`.

This module is ordinary constructive real analysis — a located bisection on a
rational sign-change bracket — carrying no spectral/continuum/Yang–Mills content.
The general-`M` bracketing is the NAMED-open residual; the small fixed orders are
produced unconditionally. -/

#print axioms YMGap.Continuum.ChebRoot.bisectInv
#print axioms YMGap.Continuum.ChebRoot.bisectRoot
#print axioms YMGap.Continuum.ChebRoot.bisectWidth_eq_geom
#print axioms YMGap.Continuum.ChebRoot.bisectFLo
#print axioms YMGap.Continuum.ChebRoot.bisectRoot_eval_zero
#print axioms YMGap.Continuum.ChebRoot.bisectRoot_in_bracket
#print axioms YMGap.Continuum.ChebRoot.bisectRoot_plus_one_pos
#print axioms YMGap.Continuum.ChebRoot.bisectRoot_one_sub_pos
#print axioms YMGap.Continuum.ChebRoot.sq_diff_eqv
#print axioms YMGap.Continuum.ChebRoot.ueval2_lip
#print axioms YMGap.Continuum.ChebRoot.chebRoot2
#print axioms YMGap.Continuum.ChebRoot.chebRoot2_eval_zero
#print axioms YMGap.Continuum.ChebRoot.chebRoot2_in_bracket
#print axioms YMGap.Continuum.ChebRoot.chebRoot2_plus_one_pos
#print axioms YMGap.Continuum.ChebRoot.chebRoot2_one_sub_pos
