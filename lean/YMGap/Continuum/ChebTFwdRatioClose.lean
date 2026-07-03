/-
# Closing `ChebTFwdRatioData` — the forward-`T` Taylor bracket engine (Chain A)

`ChebTFwdBoundClose` genuinely discharged the summability leaf `FwdSummable`
(from a one-step `Nat` ratio bound) and left exactly ONE honest residual:
`ChebTFwdBoundClose.ChebTFwdRatioData x`, which bundles the forward-`T` second-order
Taylor bracket bound `ChebTFwdBound x` with the one-step ratio cap its majorant
obeys.  This module CONSTRUCTS that residual.

## Objects (fix `x`, offset `h`)

  * `Pfwd x h m := T_m(x+h) − T_m(x)`                        — the `O(h)` driver `P_m`.
  * `Lcoef x 0 := 0`, `Lcoef x (m+1) := (m+1)·U_m(x)`        — the `T'_m = m·U_{m-1}` coeff.
  * `Bfwd x h m := Pfwd x h m − Lcoef x m · h`               — the `O(h²)` bracket `B_m`.

**Defeq anchor:** `chebTBracket x n h = Bfwd x h (n+1)` (both unfold to
`(T_{n+1}(x+h) − T_{n+1}(x)) + (−((n+1)·U_n(x))·h)`).

## The forward recurrences (§2)

  * `Pfwd_rec` : `P_{m+2} ≈ (2x·P_{m+1} − P_m) + 2h·(P_{m+1} + T_{m+1}(x))`.
  * `Lcoef_rec`: `L_{m+2} ≈ (2x·L_{m+1} − L_m) + 2·T_{m+1}(x)`.  Its load-bearing core
    is the already-proved shift identity `ChebU.Tshift : T_{n+2} ≈ x·U_{n+1} − U_n`.
  * `Bfwd_rec` : `B_{m+2} ≈ (2x·B_{m+1} − B_m) + 2h·P_{m+1}`, the `T`-analogue of
    `ChebMarkovModulus.Sdiff_rec`, via `diffRec_core2` verbatim.

## The signed-driver engine variant (§3)

`step_bound_signed` — `ChebMarkovModulus.step_bound` with a SIGNED driver
coefficient `g` bounded `−G ≤ g ≤ G` (here `g = 2h`, `G = 2|h|`), routed through
the already-two-sided `mul_abs_bound`.

## The 2-sequence induction and the base-5 envelope (§4–§6)

`QBfwd`, two-step induction `QBfwd_all`, the `Nat` envelope `pmaj m, bmaj m ≤ 5^m`
(base 5 is the smallest integer base that closes the `b`-row `4r+1 ≤ r²`), and the
assembled `chebTFwdBound`/`chebTFwdRatioData`.

## Axiom gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, no `native_decide`,
no `sorry`.
-/

import YMGap.Continuum.ChebTFwdBoundClose
import YMGap.Continuum.ChebMarkovModulus
import YMGap.Continuum.CosPiEnclosure

namespace YMGap.Continuum.ChebTFwdRatioClose

open YMGap.Constructive
open YMGap.Constructive.Q'
open YMGap.Continuum
open YMGap.Continuum.Cheb
open YMGap.Continuum.ChebBracketTaylor
open YMGap.Continuum.ChebMarkovModulus

local infix:50 " ≈ " => Q'.eqv

instance : Trans (Q'.eqv) (Q'.eqv) (Q'.eqv) where
  trans h1 h2 := Q'.eqv_trans _ _ _ h1 h2

/-! ## 1. The forward objects and the `Nat` majorants -/

/-- The `O(h)` forward driver `P_m = T_m(x+h) − T_m(x)`. -/
def Pfwd (x h : Q') (m : Nat) : Q' := Cheb.T m (x + h) + (-(Cheb.T m x))

/-- The linear (Taylor) coefficient `L_m = m·U_{m-1}(x) = T'_m(x)`. -/
def Lcoef (x : Q') : Nat → Q'
  | 0     => 0
  | (m+1) => Q'.ofNat (m+1) * Cheb.U m x

/-- The `O(h²)` forward bracket `B_m = P_m − L_m·h`. -/
def Bfwd (x h : Q') (m : Nat) : Q' := Pfwd x h m + (-(Lcoef x m * h))

/-- The `O(h)` (P-row) `Nat` majorant. -/
def pmaj : Nat → Nat
  | 0     => 0
  | 1     => 1
  | (m+2) => 3 * pmaj (m+1) + pmaj m + 2

/-- The `O(h²)` (B-row) `Nat` majorant. -/
def bmaj : Nat → Nat
  | 0     => 0
  | 1     => 0
  | (m+2) => 2 * bmaj (m+1) + bmaj m + 2 * pmaj (m+1)

theorem pmaj_succ (m : Nat) : pmaj (m+2) = 3 * pmaj (m+1) + pmaj m + 2 := rfl
theorem bmaj_succ (m : Nat) : bmaj (m+2) = 2 * bmaj (m+1) + bmaj m + 2 * pmaj (m+1) := rfl

/-! ## 2. The base-5 envelope (§D, corrected base) -/

theorem one_le_five_pow : ∀ k, 1 ≤ (5:Nat)^k
  | 0     => by decide
  | (k+1) => by
      have h := one_le_five_pow k
      rw [Nat.pow_succ]; omega

/-- `pmaj m ≤ 5^m` (two-step `Nat` induction). -/
theorem pmaj_le : ∀ m, pmaj m ≤ (5:Nat)^m ∧ pmaj (m+1) ≤ (5:Nat)^(m+1)
  | 0     => ⟨by decide, by decide⟩
  | (k+1) => by
      obtain ⟨h0, h1⟩ := pmaj_le k
      refine ⟨h1, ?_⟩
      show 3 * pmaj (k+1) + pmaj k + 2 ≤ (5:Nat)^(k+2)
      have e1 : (5:Nat)^(k+1) = 5^k * 5 := Nat.pow_succ 5 k
      have e2 : (5:Nat)^(k+2) = 5^k * 5 * 5 := by rw [Nat.pow_succ, Nat.pow_succ]
      have hp1 := one_le_five_pow k
      rw [e1] at h1
      rw [e2]
      omega

/-- `bmaj m ≤ 5^m` (two-step `Nat` induction, using the `pmaj` envelope). -/
theorem bmaj_le : ∀ m, bmaj m ≤ (5:Nat)^m ∧ bmaj (m+1) ≤ (5:Nat)^(m+1)
  | 0     => ⟨by decide, by decide⟩
  | (k+1) => by
      obtain ⟨hb0, hb1⟩ := bmaj_le k
      refine ⟨hb1, ?_⟩
      show 2 * bmaj (k+1) + bmaj k + 2 * pmaj (k+1) ≤ (5:Nat)^(k+2)
      have hp := (pmaj_le k).2
      have e1 : (5:Nat)^(k+1) = 5^k * 5 := Nat.pow_succ 5 k
      have e2 : (5:Nat)^(k+2) = 5^k * 5 * 5 := by rw [Nat.pow_succ, Nat.pow_succ]
      rw [e1] at hb1 hp
      rw [e2]
      omega

/-! ## 3. The signed-driver step bound (§B) -/

/-- **The signed-driver two-sided step bound.**  As `ChebMarkovModulus.step_bound`
but the driver coefficient `g` is SIGNED with `−G ≤ g ≤ G` (`G ≥ 0`).  The driver
`g·w1` is bounded through the already-two-sided `mul_abs_bound`. -/
theorem step_bound_signed {x g v2 v1 v0 w1 Bv1 Bv0 G Bw1 : Q'}
    (hrec : v2 ≈ ((((1:Q')+(1:Q'))*x) * v1 + (-v0)) + g * w1)
    (hx1 : x ≤ (1:Q')) (hxm1 : (-(1:Q')) ≤ x)
    (hBv1 : (0:Q') ≤ Bv1) (_hBv0 : (0:Q') ≤ Bv0) (hG : (0:Q') ≤ G) (hBw1 : (0:Q') ≤ Bw1)
    (hga : (-G) ≤ g) (hgb : g ≤ G)
    (hv1a : (-Bv1) ≤ v1) (hv1b : v1 ≤ Bv1)
    (hv0a : (-Bv0) ≤ v0) (hv0b : v0 ≤ Bv0)
    (hw1a : (-Bw1) ≤ w1) (hw1b : w1 ≤ Bw1) :
    (-((((1:Q')+(1:Q'))*Bv1 + Bv0) + G*Bw1)) ≤ v2
      ∧ v2 ≤ (((1:Q')+(1:Q'))*Bv1 + Bv0) + G*Bw1 := by
  obtain ⟨hXl, hXu⟩ := twoX_bounds x hx1 hxm1
  obtain ⟨hP1l, hP1u⟩ := mul_abs_bound two_nonneg hBv1 hXl hXu hv1a hv1b
  have hN0u : (-v0) ≤ Bv0 :=
    Q'.le_trans' _ (-(-Bv0)) _ (Q'.neg_le_neg hv0a) (Q'.le_of_eqv (Q'.neg_neg_eqv Bv0))
  have hN0l : (-Bv0) ≤ (-v0) := Q'.neg_le_neg hv0b
  obtain ⟨hW1l, hW1u⟩ := mul_abs_bound hG hBw1 hga hgb hw1a hw1b
  have hupper : v2 ≤ (((1:Q')+(1:Q'))*Bv1 + Bv0) + G*Bw1 := by
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hrec) ?_
    exact Q'.add_le_add (Q'.add_le_add hP1u hN0u) hW1u
  have hlower : (-((((1:Q')+(1:Q'))*Bv1 + Bv0) + G*Bw1)) ≤ v2 := by
    refine Q'.le_trans' _ _ _ ?_ (Q'.ge_of_eqv hrec)
    refine Q'.le_trans' _ (((-(((1:Q')+(1:Q'))*Bv1)) + (-Bv0)) + (-(G*Bw1))) _
      (Q'.le_of_eqv ?_) ?_
    · refine Q'.eqv_trans _ _ _ (Cheb.neg_add_eqv _ _) ?_
      exact Q'.add_eqv_congr_right _ _ _ (Cheb.neg_add_eqv _ _)
    · exact Q'.add_le_add (Q'.add_le_add hP1l hN0l) hW1l
  exact ⟨hlower, hupper⟩

/-! ## 4. The forward recurrences (§A) -/

/-- A 5-term additive rearrangement:
`((t1+t2)+t3)+(t4+t5) ≈ ((t1+t4)+(t3+t5))+t2`. -/
theorem add5_rearr (t1 t2 t3 t4 t5 : Q') :
    ((t1 + t2) + t3) + (t4 + t5) ≈ ((t1 + t4) + (t3 + t5)) + t2 := by
  have hL : ((t1 + t2) + t3) + (t4 + t5) ≈ t1 + (t2 + (t3 + (t4 + t5))) := by
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv (t1 + t2) t3 (t4 + t5)) ?_
    exact Q'.add_assoc_eqv t1 t2 (t3 + (t4 + t5))
  have hR : ((t1 + t4) + (t3 + t5)) + t2 ≈ t1 + (t2 + (t3 + (t4 + t5))) := by
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv (t1 + t4) (t3 + t5) t2) ?_
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv t1 t4 ((t3 + t5) + t2)) ?_
    refine Q'.add_eqv_congr_left _ _ _ ?_
    calc t4 + ((t3 + t5) + t2)
        ≈ t4 + (t2 + (t3 + t5)) :=
          Q'.add_eqv_congr_left _ _ _ (Q'.add_comm_eqv (t3 + t5) t2)
      _ ≈ (t4 + t2) + (t3 + t5) := Q'.eqv_symm (Q'.add_assoc_eqv t4 t2 (t3 + t5))
      _ ≈ (t2 + t4) + (t3 + t5) := Q'.add_eqv_congr_right _ _ _ (Q'.add_comm_eqv t4 t2)
      _ ≈ t2 + (t4 + (t3 + t5)) := Q'.add_assoc_eqv t2 t4 (t3 + t5)
      _ ≈ t2 + ((t4 + t3) + t5) :=
          Q'.add_eqv_congr_left _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv t4 t3 t5))
      _ ≈ t2 + ((t3 + t4) + t5) :=
          Q'.add_eqv_congr_left _ _ _ (Q'.add_eqv_congr_right _ _ _ (Q'.add_comm_eqv t4 t3))
      _ ≈ t2 + (t3 + (t4 + t5)) :=
          Q'.add_eqv_congr_left _ _ _ (Q'.add_assoc_eqv t3 t4 t5)
  exact Q'.eqv_trans _ _ _ hL (Q'.eqv_symm hR)

/-- Abstract core of `Pfwd_rec` (`A = T_{m+1}(x+h)`, `a = T_{m+1}(x)`,
`B = T_m(x+h)`, `b = T_m(x)`; the `2h·T_{m+1}(x)` split of the shifted node). -/
theorem Pfwd_core (x h A a B b : Q') :
    ((((1:Q')+(1:Q'))*(x + h))*A + (-B)) + (-((((1:Q')+(1:Q'))*x)*a + (-b)))
      ≈ ((((1:Q')+(1:Q'))*x)*(A + (-a)) + (-(B + (-b))))
          + (((1:Q')+(1:Q'))*h)*((A + (-a)) + a) := by
  have hLHS : ((((1:Q')+(1:Q'))*(x + h))*A + (-B)) + (-((((1:Q')+(1:Q'))*x)*a + (-b)))
      ≈ (((((1:Q')+(1:Q'))*x)*A + (((1:Q')+(1:Q'))*h)*A) + (-B))
          + ((-((((1:Q')+(1:Q'))*x)*a)) + b) :=
    addC _ _ _ _ (addC _ _ _ _ (twoShiftR x h A) (Q'.eqv_refl (-B)))
      (negSub (((1:Q')+(1:Q'))*x*a) b)
  have hM1 : (((1:Q')+(1:Q'))*x)*(A + (-a))
      ≈ (((1:Q')+(1:Q'))*x)*A + (-((((1:Q')+(1:Q'))*x)*a)) :=
    Q'.eqv_trans _ _ _ (Q'.mul_add_eqv (((1:Q')+(1:Q'))*x) A (-a))
      (Q'.add_eqv_congr_left _ _ _ (Q'.mul_neg_eqv (((1:Q')+(1:Q'))*x) a))
  have hcancel : (A + (-a)) + a ≈ A := by
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv A (-a) a) ?_
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ (Q'.neg_add_self_eqv a)) ?_
    rw [Q'.add_zero']
    exact Q'.eqv_refl _
  have hRHS : ((((1:Q')+(1:Q'))*x)*(A + (-a)) + (-(B + (-b))))
        + (((1:Q')+(1:Q'))*h)*((A + (-a)) + a)
      ≈ (((((1:Q')+(1:Q'))*x)*A + (-((((1:Q')+(1:Q'))*x)*a))) + ((-B) + b))
          + (((1:Q')+(1:Q'))*h)*A :=
    addC _ _ _ _ (addC _ _ _ _ hM1 (negSub B b))
      (Q'.mul_eqv_congr_left _ _ _ hcancel)
  refine Q'.eqv_trans _ _ _ hLHS ?_
  refine Q'.eqv_trans _ _ _
    (add5_rearr (((1:Q')+(1:Q'))*x*A) (((1:Q')+(1:Q'))*h*A) (-B)
      (-((((1:Q')+(1:Q'))*x)*a)) b) ?_
  exact Q'.eqv_symm hRHS

/-- **A1: the forward driver recurrence.**
`P_{m+2} ≈ (2x·P_{m+1} − P_m) + 2h·(P_{m+1} + T_{m+1}(x))`. -/
theorem Pfwd_rec (x h : Q') (m : Nat) :
    Pfwd x h (m+2)
      ≈ ((((1:Q')+(1:Q'))*x) * Pfwd x h (m+1) + (-(Pfwd x h m)))
          + (((1:Q')+(1:Q'))*h) * (Pfwd x h (m+1) + Cheb.T (m+1) x) := by
  unfold Pfwd
  rw [Cheb.T_succ_succ m (x + h), Cheb.T_succ_succ m x]
  exact Pfwd_core x h (Cheb.T (m+1) (x+h)) (Cheb.T (m+1) x) (Cheb.T m (x+h)) (Cheb.T m x)

/-- Abstract core of `Lcoef_rec`, after substituting the `U`-recurrence
`U_{m+2} = 2x·U_{m+1} − U_m` (into `p,q`) and the shift `T_{m+2} = x·U_{m+1} − U_m`. -/
theorem Lcoef_core (x p q c1 c2 c3 : Q')
    (hc2 : c2 + (1:Q') ≈ c3) (hc1 : c1 + ((1:Q')+(1:Q')) ≈ c3) :
    c3 * ((((1:Q')+(1:Q'))*x)*p + (-q))
      ≈ ((((1:Q')+(1:Q'))*x)*(c2*p) + (-(c1*q))) + ((1:Q')+(1:Q'))*(x*p + (-q)) := by
  have hL : c3 * ((((1:Q')+(1:Q'))*x)*p + (-q))
      ≈ ((((1:Q')+(1:Q'))*x)*c3)*p + (-(c3*q)) := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv c3 ((((1:Q')+(1:Q'))*x)*p) (-q)) ?_
    refine addC _ _ _ _ ?_ (Q'.mul_neg_eqv c3 q)
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv c3 (((1:Q')+(1:Q'))*x) p)) ?_
    exact Q'.mul_eqv_congr_right _ _ p (Q'.mul_comm_eqv c3 (((1:Q')+(1:Q'))*x))
  have e2 : ((1:Q')+(1:Q'))*(x*p + (-q))
      ≈ ((((1:Q')+(1:Q'))*x)*p) + (-(((1:Q')+(1:Q'))*q)) := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv ((1:Q')+(1:Q')) (x*p) (-q)) ?_
    refine addC _ _ _ _ ?_ (Q'.mul_neg_eqv ((1:Q')+(1:Q')) q)
    exact Q'.eqv_symm (Q'.mul_assoc_eqv ((1:Q')+(1:Q')) x p)
  have e1 : (((1:Q')+(1:Q'))*x)*(c2*p) ≈ ((((1:Q')+(1:Q'))*x)*c2)*p :=
    Q'.eqv_symm (Q'.mul_assoc_eqv (((1:Q')+(1:Q'))*x) c2 p)
  have hR : (((((1:Q')+(1:Q'))*x)*(c2*p) + (-(c1*q))) + ((1:Q')+(1:Q'))*(x*p + (-q)))
      ≈ ((((1:Q')+(1:Q'))*x)*c3)*p + (-(c3*q)) := by
    refine Q'.eqv_trans _ _ _
      (addC _ _ _ _ (addC _ _ _ _ e1 (Q'.eqv_refl (-(c1*q)))) e2) ?_
    refine Q'.eqv_trans _ _ _ (Q'.add_swap_inner _ _ _ _) ?_
    refine addC _ _ _ _ ?_ ?_
    · refine Q'.eqv_trans _ _ _
        (Q'.eqv_symm (addmul ((((1:Q')+(1:Q'))*x)*c2) (((1:Q')+(1:Q'))*x) p)) ?_
      refine Q'.mul_eqv_congr_right _ _ p ?_
      refine Q'.eqv_trans _ _ _
        (addC _ _ _ _ (Q'.eqv_refl _) (Q'.eqv_symm (Q'.mul_one_eqv (((1:Q')+(1:Q'))*x)))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_symm (Q'.mul_add_eqv (((1:Q')+(1:Q'))*x) c2 (1:Q'))) ?_
      exact Q'.mul_eqv_congr_left _ _ _ hc2
    · refine Q'.eqv_trans _ _ _
        (Q'.eqv_symm (Cheb.neg_add_eqv (c1*q) (((1:Q')+(1:Q'))*q))) ?_
      refine Q'.neg_eqv_congr _ _ ?_
      refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (addmul c1 ((1:Q')+(1:Q')) q)) ?_
      exact Q'.mul_eqv_congr_right _ _ q hc1
  exact Q'.eqv_trans _ _ _ hL (Q'.eqv_symm hR)

/-- **A2: the linear-coefficient recurrence.**
`L_{m+2} ≈ (2x·L_{m+1} − L_m) + 2·T_{m+1}(x)`. -/
theorem Lcoef_rec (x : Q') (m : Nat) :
    Lcoef x (m+2)
      ≈ ((((1:Q')+(1:Q'))*x) * Lcoef x (m+1) + (-(Lcoef x m)))
          + ((1:Q')+(1:Q')) * Cheb.T (m+1) x := by
  cases m with
  | zero =>
      show (Q'.ofNat 2 * Cheb.U 1 x)
          ≈ ((((1:Q')+(1:Q'))*x) * (Q'.ofNat 1 * Cheb.U 0 x) + (-(Lcoef x 0)))
              + ((1:Q')+(1:Q')) * Cheb.T 1 x
      rw [Cheb.U_one, Cheb.U_zero, Cheb.T_one]
      have hL : Q'.ofNat 2 * ((2:Q')*x)
          ≈ ((1:Q')+(1:Q'))*x + ((1:Q')+(1:Q'))*x := by
        refine Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm ChebU.one_add_one_eqv_two)) ?_
        refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (Cheb.two_mul_eqv x)) ?_
        exact Q'.mul_add_eqv _ _ _
      have hR : ((((1:Q')+(1:Q'))*x) * (Q'.ofNat 1 * (1:Q')) + (-(Lcoef x 0)))
            + ((1:Q')+(1:Q'))*x
          ≈ ((1:Q')+(1:Q'))*x + ((1:Q')+(1:Q'))*x := by
        refine addC _ _ _ _ ?_ (Q'.eqv_refl _)
        have h11 : Q'.ofNat 1 * (1:Q') ≈ (1:Q') := by decide
        have h0 : (-(Lcoef x 0)) ≈ (0:Q') := by show (-(0:Q')) ≈ (0:Q'); decide
        refine Q'.eqv_trans _ _ _ (addC _ _ _ _
          (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ h11)
            (Q'.mul_one_eqv _)) h0) ?_
        rw [Q'.add_zero']
        exact Q'.eqv_refl _
      exact Q'.eqv_trans _ _ _ hL (Q'.eqv_symm hR)
  | succ k =>
      have hc2 : Q'.ofNat (k+2) + (1:Q') ≈ Q'.ofNat (k+3) := by
        refine Q'.eqv_trans _ _ _
          (addC _ _ _ _ (Q'.eqv_refl _) (show (1:Q') ≈ Q'.ofNat 1 by decide)) ?_
        exact ChebU.ofNat_add_eqv (k+2) 1
      have hc1 : Q'.ofNat (k+1) + ((1:Q')+(1:Q')) ≈ Q'.ofNat (k+3) := by
        refine Q'.eqv_trans _ _ _
          (addC _ _ _ _ (Q'.eqv_refl _) ChebU.one_add_one_eqv_two) ?_
        exact ChebU.ofNat_add_eqv (k+1) 2
      show (Q'.ofNat (k+3) * Cheb.U (k+2) x)
          ≈ ((((1:Q')+(1:Q'))*x) * (Q'.ofNat (k+2) * Cheb.U (k+1) x)
                + (-(Q'.ofNat (k+1) * Cheb.U k x)))
              + ((1:Q')+(1:Q')) * Cheb.T (k+2) x
      rw [Cheb.U_succ_succ k x]
      refine Q'.eqv_trans _ _ _
        (Lcoef_core x (Cheb.U (k+1) x) (Cheb.U k x)
          (Q'.ofNat (k+1)) (Q'.ofNat (k+2)) (Q'.ofNat (k+3)) hc2 hc1) ?_
      refine addC _ _ _ _ (Q'.eqv_refl _) ?_
      exact Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (ChebU.Tshift k x))

/-- `L_{m+2}·h` in the shape required by `diffRec_core2`. -/
theorem Lcoef_rec_h (x h : Q') (m : Nat) :
    Lcoef x (m+2) * h
      ≈ ((((1:Q')+(1:Q'))*x) * (Lcoef x (m+1) * h) + (-(Lcoef x m * h)))
          + (((1:Q')+(1:Q'))*h) * Cheb.T (m+1) x := by
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ h (Lcoef_rec x m)) ?_
  refine Q'.eqv_trans _ _ _
    (addmul ((((1:Q')+(1:Q'))*x) * Lcoef x (m+1) + (-(Lcoef x m)))
      (((1:Q')+(1:Q')) * Cheb.T (m+1) x) h) ?_
  refine addC _ _ _ _ ?_ ?_
  · refine Q'.eqv_trans _ _ _
      (addmul ((((1:Q')+(1:Q'))*x) * Lcoef x (m+1)) (-(Lcoef x m)) h) ?_
    refine addC _ _ _ _ ?_ (Q'.neg_mul_eqv (Lcoef x m) h)
    exact Q'.mul_assoc_eqv (((1:Q')+(1:Q'))*x) (Lcoef x (m+1)) h
  · refine Q'.eqv_trans _ _ _
      (Q'.mul_assoc_eqv ((1:Q')+(1:Q')) (Cheb.T (m+1) x) h) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_comm_eqv (Cheb.T (m+1) x) h)) ?_
    exact Q'.eqv_symm (Q'.mul_assoc_eqv ((1:Q')+(1:Q')) h (Cheb.T (m+1) x))

/-- **A3: the forward bracket recurrence.**
`B_{m+2} ≈ (2x·B_{m+1} − B_m) + 2h·P_{m+1}`. -/
theorem Bfwd_rec (x h : Q') (m : Nat) :
    Bfwd x h (m+2)
      ≈ ((((1:Q')+(1:Q'))*x) * Bfwd x h (m+1) + (-(Bfwd x h m)))
          + (((1:Q')+(1:Q'))*h) * Pfwd x h (m+1) := by
  show (Pfwd x h (m+2) + (-(Lcoef x (m+2) * h))) ≈ _
  refine Q'.eqv_trans _ _ _
    (addC _ _ _ _ (Pfwd_rec x h m) (Q'.neg_eqv_congr _ _ (Lcoef_rec_h x h m))) ?_
  refine Q'.eqv_trans _ _ _
    (diffRec_core2 (((1:Q')+(1:Q'))*x) (((1:Q')+(1:Q'))*h)
      (Pfwd x h (m+1)) (Pfwd x h m) (Pfwd x h (m+1) + Cheb.T (m+1) x)
      (Lcoef x (m+1) * h) (Lcoef x m * h) (Cheb.T (m+1) x)) ?_
  refine addC _ _ _ _ (Q'.eqv_refl _) ?_
  refine Q'.mul_eqv_congr_left _ _ _ ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_assoc_eqv (Pfwd x h (m+1)) (Cheb.T (m+1) x) (-(Cheb.T (m+1) x))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left _ _ _ (ChebU.add_neg_self_eqv (Cheb.T (m+1) x))) ?_
  rw [Q'.add_zero']
  exact Q'.eqv_refl _

/-! ## 5. The 2-sequence bound predicate, bases, and induction (§C) -/

/-- `a + 0 ≈ a`. -/
theorem add_zero_eqv (a : Q') : a + (0:Q') ≈ a := by
  rw [Q'.add_zero']; exact Q'.eqv_refl a

/-- Two-sided bound from an absolute-value bound. -/
theorem abs_two_sided {v B : Q'} (hvB : Q'.abs v ≤ B) : (-B) ≤ v ∧ v ≤ B := by
  refine ⟨?_, Q'.le_trans' _ _ _ (Q'.le_abs_self v) hvB⟩
  have h1 : (-B) ≤ (-(Q'.abs v)) := Q'.neg_le_neg hvB
  have h2 : (-(Q'.abs v)) ≤ v :=
    Q'.le_trans' _ (-(-v)) _ (Q'.neg_le_neg (Q'.neg_le_abs v)) (Q'.le_of_eqv (Q'.neg_neg_eqv v))
  exact Q'.le_trans' _ _ _ h1 h2

/-- **The P-row reconciliation** (wider-box): using `2|h| ≤ 1`,
`R ≤ ofNat(3p1 + p0 + 2)·δ`. -/
theorem Precon (p1 p0 : Nat) {δ : Q'} (hδ0 : (0:Q') ≤ δ)
    (hb1 : ((1:Q')+(1:Q'))*δ ≤ (1:Q')) :
    (((1:Q')+(1:Q'))*(Q'.ofNat p1 * δ) + Q'.ofNat p0 * δ)
        + (((1:Q')+(1:Q'))*δ)*(Q'.ofNat p1 * δ + (1:Q'))
      ≤ Q'.ofNat (3*p1 + p0 + 2) * δ := by
  have hdriver : (((1:Q')+(1:Q'))*δ)*(Q'.ofNat p1 * δ + (1:Q'))
      ≤ Q'.ofNat p1 * δ + Q'.ofNat 2 * δ := by
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_add_eqv (((1:Q')+(1:Q'))*δ) (Q'.ofNat p1 * δ) (1:Q'))) ?_
    refine Q'.add_le_add ?_ ?_
    · refine Q'.le_trans' _ ((1:Q')*(Q'.ofNat p1 * δ)) _
        (Q'.mul_le_mul_of_nonneg_right _ _ _ hb1 (ofNat_lin_nonneg p1 hδ0)) ?_
      exact Q'.le_of_eqv (Q'.one_mul_eqv _)
    · refine Q'.le_trans' _ (((1:Q')+(1:Q'))*δ) _ (Q'.le_of_eqv (Q'.mul_one_eqv _)) ?_
      exact Q'.le_of_eqv (Q'.mul_eqv_congr_right _ _ _ ChebU.one_add_one_eqv_two)
  refine Q'.le_trans' _ _ _
    (Q'.add_le_add (Q'.add_le_add (Q'.le_of_eqv (two_mul_ofNat_mul p1 δ)) (Q'.le_refl' _)) hdriver) ?_
  refine Q'.le_of_eqv ?_
  refine Q'.eqv_trans _ _ _
    (addC _ _ _ _ (ofNat_add_mul (2*p1) p0 δ) (ofNat_add_mul p1 2 δ)) ?_
  refine Q'.eqv_trans _ _ _ (ofNat_add_mul (2*p1+p0) (p1+2) δ) ?_
  have he : (2*p1+p0) + (p1+2) = 3*p1 + p0 + 2 := by omega
  rw [he]; exact Q'.eqv_refl _

/-- The 2-sided P/B bounds at index `m`, with box variable `δ = |h|`. -/
def QBfwd (x h : Q') (m : Nat) : Prop :=
  ((-(Q'.ofNat (pmaj m) * Q'.abs h)) ≤ Pfwd x h m
      ∧ Pfwd x h m ≤ Q'.ofNat (pmaj m) * Q'.abs h)
  ∧ ((-(Q'.ofNat (bmaj m) * (Q'.abs h * Q'.abs h))) ≤ Bfwd x h m
      ∧ Bfwd x h m ≤ Q'.ofNat (bmaj m) * (Q'.abs h * Q'.abs h))

/-! ### Base value identities -/

theorem Pfwd_zero_eqv (x h : Q') : Pfwd x h 0 ≈ (0:Q') := by
  show (Cheb.T 0 (x+h) + (-(Cheb.T 0 x))) ≈ (0:Q')
  rw [Cheb.T_zero, Cheb.T_zero]
  exact ChebU.add_neg_self_eqv (1:Q')

theorem Bfwd_zero_eqv (x h : Q') : Bfwd x h 0 ≈ (0:Q') := by
  show (Pfwd x h 0 + (-(Lcoef x 0 * h))) ≈ (0:Q')
  have hz : Lcoef x 0 * h ≈ (0:Q') := by
    show (0:Q') * h ≈ (0:Q')
    exact Q'.zero_mul_eqv h
  refine Q'.eqv_trans _ _ _
    (addC _ _ _ _ (Pfwd_zero_eqv x h) (Q'.neg_eqv_congr _ _ hz)) ?_
  exact ChebU.add_neg_self_eqv (0:Q')

theorem Pfwd_one_eqv (x h : Q') : Pfwd x h 1 ≈ h := by
  show (Cheb.T 1 (x+h) + (-(Cheb.T 1 x))) ≈ h
  rw [Cheb.T_one, Cheb.T_one]
  calc (x + h) + (-x)
      ≈ (h + x) + (-x) := Q'.add_eqv_congr_right _ _ _ (Q'.add_comm_eqv x h)
    _ ≈ h + (x + (-x)) := Q'.add_assoc_eqv h x (-x)
    _ ≈ h + (0:Q') := Q'.add_eqv_congr_left _ _ _ (ChebU.add_neg_self_eqv x)
    _ ≈ h := add_zero_eqv h

theorem Bfwd_one_eqv (x h : Q') : Bfwd x h 1 ≈ (0:Q') := by
  show (Pfwd x h 1 + (-(Lcoef x 1 * h))) ≈ (0:Q')
  have hL1 : Lcoef x 1 * h ≈ h := by
    show ((Q'.ofNat 1 * Cheb.U 0 x) * h) ≈ h
    rw [Cheb.U_zero]
    have h11 : Q'.ofNat 1 * (1:Q') ≈ (1:Q') := by decide
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ h h11) ?_
    exact Q'.one_mul_eqv h
  refine Q'.eqv_trans _ _ _
    (addC _ _ _ _ (Pfwd_one_eqv x h) (Q'.neg_eqv_congr _ _ hL1)) ?_
  exact ChebU.add_neg_self_eqv h

/-! ### Base predicates -/

theorem QBfwd_zero (x h : Q') : QBfwd x h 0 := by
  have hδ0 : (0:Q') ≤ Q'.abs h := Q'.abs_nonneg h
  refine ⟨?_, ?_⟩
  · exact bound_of_eqv_nonneg
      (Q'.eqv_trans _ _ _ (Pfwd_zero_eqv x h) (Q'.eqv_symm (ofNat_zero_mul (Q'.abs h))))
      (ofNat_lin_nonneg 0 hδ0)
  · exact bound_of_eqv_nonneg
      (Q'.eqv_trans _ _ _ (Bfwd_zero_eqv x h)
        (Q'.eqv_symm (ofNat_zero_mul (Q'.abs h * Q'.abs h))))
      (ofNat_sq_nonneg 0 (Q'.abs h))

theorem QBfwd_one (x h : Q') : QBfwd x h 1 := by
  have hδ0 : (0:Q') ≤ Q'.abs h := Q'.abs_nonneg h
  obtain ⟨hhl, hhu⟩ := abs_two_sided (Q'.le_refl' (Q'.abs h))
  have hb1 : Q'.ofNat 1 * Q'.abs h ≈ Q'.abs h := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (show Q'.ofNat 1 ≈ (1:Q') by decide)) ?_
    exact Q'.one_mul_eqv _
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact Q'.le_trans' _ (-(Q'.abs h)) _
      (Q'.le_of_eqv (Q'.neg_eqv_congr _ _ hb1))
      (Q'.le_trans' _ h _ hhl (Q'.ge_of_eqv (Pfwd_one_eqv x h)))
  · exact Q'.le_trans' _ h _ (Q'.le_of_eqv (Pfwd_one_eqv x h))
      (Q'.le_trans' _ (Q'.abs h) _ hhu (Q'.ge_of_eqv hb1))
  · exact bound_of_eqv_nonneg
      (Q'.eqv_trans _ _ _ (Bfwd_one_eqv x h)
        (Q'.eqv_symm (ofNat_zero_mul (Q'.abs h * Q'.abs h))))
      (ofNat_sq_nonneg 0 (Q'.abs h))

/-! ### The inductive step -/

theorem QBfwd_step (x h : Q') (hx1 : x ≤ (1:Q')) (hxm1 : (-(1:Q')) ≤ x)
    (hh : Q'.abs h ≤ HalfPow.half) (m : Nat)
    (hn : QBfwd x h m) (hn1 : QBfwd x h (m+1)) : QBfwd x h (m+2) := by
  obtain ⟨⟨hPd0l, hPd0u⟩, ⟨hBd0l, hBd0u⟩⟩ := hn
  obtain ⟨⟨hPd1l, hPd1u⟩, ⟨hBd1l, hBd1u⟩⟩ := hn1
  have hδ0 : (0:Q') ≤ Q'.abs h := Q'.abs_nonneg h
  obtain ⟨hhl, hhu⟩ := abs_two_sided (Q'.le_refl' (Q'.abs h))
  obtain ⟨hTl, hTu⟩ := abs_two_sided (CosPiEnclosure.absT_le_one (m+1) x hx1 hxm1)
  have hG : (0:Q') ≤ ((1:Q')+(1:Q'))*Q'.abs h := twoδ_nonneg hδ0
  have hgu : ((1:Q')+(1:Q'))*h ≤ ((1:Q')+(1:Q'))*Q'.abs h :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hhu two_nonneg
  have hgl : (-(((1:Q')+(1:Q'))*Q'.abs h)) ≤ ((1:Q')+(1:Q'))*h :=
    Q'.le_trans' _ (((1:Q')+(1:Q'))*(-(Q'.abs h))) _
      (Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_neg_eqv ((1:Q')+(1:Q')) (Q'.abs h))))
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hhl two_nonneg)
  have hb1 : ((1:Q')+(1:Q'))*Q'.abs h ≤ (1:Q') :=
    Q'.le_trans' _ (((1:Q')+(1:Q'))*HalfPow.half) _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hh two_nonneg)
      (Q'.le_of_eqv (show ((1:Q')+(1:Q'))*HalfPow.half ≈ (1:Q') by decide))
  refine ⟨?_, ?_⟩
  · -- P-row
    obtain ⟨hl, hu⟩ := step_bound_signed (Pfwd_rec x h m) hx1 hxm1
      (ofNat_lin_nonneg (pmaj (m+1)) hδ0) (ofNat_lin_nonneg (pmaj m) hδ0) hG
      (Q'.le_trans' _ (Q'.ofNat (pmaj (m+1)) * Q'.abs h) _
        (ofNat_lin_nonneg (pmaj (m+1)) hδ0)
        (Q'.add_le_self_of_nonneg _ (1:Q') Q'.zero_le_one))
      hgl hgu hPd1l hPd1u hPd0l hPd0u
      (Q'.le_trans' _ ((-(Q'.ofNat (pmaj (m+1)) * Q'.abs h)) + (-(1:Q'))) _
        (Q'.le_of_eqv (Cheb.neg_add_eqv (Q'.ofNat (pmaj (m+1)) * Q'.abs h) (1:Q')))
        (Q'.add_le_add hPd1l hTl))
      (Q'.add_le_add hPd1u hTu)
    refine tighten hl hu ?_
    rw [pmaj_succ]
    exact Precon (pmaj (m+1)) (pmaj m) hδ0 hb1
  · -- B-row
    obtain ⟨hl, hu⟩ := step_bound_signed (Bfwd_rec x h m) hx1 hxm1
      (ofNat_sq_nonneg (bmaj (m+1)) (Q'.abs h)) (ofNat_sq_nonneg (bmaj m) (Q'.abs h)) hG
      (ofNat_lin_nonneg (pmaj (m+1)) hδ0)
      hgl hgu hBd1l hBd1u hBd0l hBd0u hPd1l hPd1u
    refine tighten hl hu (Q'.le_of_eqv ?_)
    refine Q'.eqv_trans _ _ _
      (R_recon (bmaj (m+1)) (bmaj m) (pmaj (m+1))
        (Q'.eqv_refl _) (Q'.eqv_refl _) (inhom_S (pmaj (m+1)) (Q'.abs h))) ?_
    have hbm : 2*bmaj (m+1) + 2*pmaj (m+1) + bmaj m = bmaj (m+2) := by rw [bmaj_succ]; omega
    rw [hbm]; exact Q'.eqv_refl _

/-- `QBfwd` for all `m` (two-step induction). -/
theorem QBfwd_all (x h : Q') (hx1 : x ≤ (1:Q')) (hxm1 : (-(1:Q')) ≤ x)
    (hh : Q'.abs h ≤ HalfPow.half) : ∀ m, QBfwd x h m ∧ QBfwd x h (m+1) := by
  intro m
  induction m with
  | zero => exact ⟨QBfwd_zero x h, QBfwd_one x h⟩
  | succ k ih =>
      obtain ⟨hk, hk1⟩ := ih
      exact ⟨hk1, QBfwd_step x h hx1 hxm1 hh k hk hk1⟩

/-! ## 6. Assembly: `ChebTFwdBound` and `ChebTFwdRatioData` (§E) -/

/-- **The forward-`T` Taylor bracket bound**, with majorant `KT n = 5^{n+1}`. -/
def chebTFwdBound (x : Q') (hx1 : x ≤ (1:Q')) (hxm1 : (-(1:Q')) ≤ x) :
    ThetaSeriesC1Close.ChebTFwdBound x :=
  { KT := fun n => 5^(n+1)
    bound := fun n h hh => by
      show Q'.abs (Bfwd x h (n+1)) ≤ Q'.ofNat (5^(n+1)) * (Q'.abs h * Q'.abs h)
      obtain ⟨_, hBl, hBu⟩ := (QBfwd_all x h hx1 hxm1 hh (n+1)).1
      refine Q'.le_trans' _ _ _ (Q'.abs_le_of_bounds hBl hBu) ?_
      exact Q'.mul_le_mul_of_nonneg_right _ _ _
        (ChebTFwdBoundClose.ofNat_le_ofNat (bmaj_le (n+1)).1)
        (Cheb.square_nonneg (Q'.abs h)) }

/-- **THE CHAIN-A RESIDUAL, CONSTRUCTED.**  The forward-`T` Taylor bracket engine
together with the one-step base-5 ratio cap its majorant obeys. -/
def chebTFwdRatioData (x : Q') (hx1 : x ≤ (1:Q')) (hxm1 : (-(1:Q')) ≤ x) :
    ChebTFwdBoundClose.ChebTFwdRatioData x :=
  { fb := chebTFwdBound x hx1 hxm1
    c := 5
    hc := by decide
    hratio := fun n => by
      show (5:Nat)^(n+1+1) ≤ 5 * 5^(n+1)
      rw [Nat.pow_succ]; omega }

end YMGap.Continuum.ChebTFwdRatioClose

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.ChebTFwdRatioClose.pmaj_le
#print axioms YMGap.Continuum.ChebTFwdRatioClose.bmaj_le
#print axioms YMGap.Continuum.ChebTFwdRatioClose.step_bound_signed
#print axioms YMGap.Continuum.ChebTFwdRatioClose.Pfwd_rec
#print axioms YMGap.Continuum.ChebTFwdRatioClose.Lcoef_rec
#print axioms YMGap.Continuum.ChebTFwdRatioClose.Bfwd_rec
#print axioms YMGap.Continuum.ChebTFwdRatioClose.QBfwd_step
#print axioms YMGap.Continuum.ChebTFwdRatioClose.QBfwd_all
#print axioms YMGap.Continuum.ChebTFwdRatioClose.chebTFwdBound
#print axioms YMGap.Continuum.ChebTFwdRatioClose.chebTFwdRatioData
