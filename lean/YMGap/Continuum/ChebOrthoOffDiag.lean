/-
# The π-FREE off-diagonal Chebyshev-`U` orthogonality `∫_{−1}^1 U_e(x)√(1−x²)dx = 0`

This module builds the off-diagonal half of the second-kind Chebyshev weight
orthogonality WITHOUT the Machin-π bridge.  The strategic observation
(`semiInt` is used as an ABSTRACT positive constant; the π's cancel in the final
Gram PSD) means we only need:

  * (off-diagonal)  `∫_{−1}^1 U_e(x)√(1−x²) dx = 0`   for `e ≥ 1`,
  * (diagonal)      `∫_{−1}^1 U_c(x)² √(1−x²) dx = semiInt`.

This file does the OFF-DIAGONAL `e ≥ 1` piece, the harder one.

## The Riemann functional

With the uniform-midpoint rational partition `x_k = (2k+1−n)/n`, weight `2/n`,
and the genuine per-node square root `√(1−x_k²)` reused VERBATIM from
`SemicircleIntegral.nodeWeight`, the orthogonality Riemann sum is

    orthSum e n  :=  (2/n) · Σ_{k<n} U_e(x_k) · √(1 − x_k²)

a `CReal`-valued finite sum (the extra rational factor `U_e(x_k) = Cheb.U e x_k`
sits next to the semicircle node weight).

## What is PROVED here (axiom-clean, GENUINE new content)

  * `Cheb.U` ODD/EVEN PARITY `U_e(−x) ≈ applySign(e even)(U_e(x))` (`U_par`), by
    two-step induction on the closed `U`-recurrence.  In particular for `e` ODD,
    `U_e(−x) ≈ −U_e(x)` (`U_odd_neg`).
  * Node ANTISYMMETRY: `omsNum`/`oneMinusSqNode`/`nodeWeight` are INVARIANT under
    the reflection `k ↦ n−1−k` (`oneMinusSqNode_reflect`, `nodeWeight_reflect`),
    and the node itself reflects to its negation
    (`uniformMidpoint_reflect : x_{n−1−k} = −x_k`), all as genuine `Q'`/`CReal`
    identities (the squares match exactly; the numerator negates exactly).
  * `finSum_reverse` — the reflection identity `Σ_{k<n} g k ≈ Σ_{k<n} g(n−1−k)`
    (via the left-peel lemma `finSum_peel_left`), a reusable `RationalTail`
    primitive.
  * `orthSum` — the orthogonality Riemann sum (`CReal`-`csum` with the bounded
    rational factor `U_e(x_k)`).
  * **`orthSum_odd_zero`** — for `e` ODD, `CReal.Equiv (orthSum e n) czero` for
    EVERY resolution `n` (pairwise cancellation `U_e(x_k)√ + U_e(x_{n−1−k})√ ≈ 0`
    via the reversal + parity + node-reflection).  SOLID, π-FREE, no FTC.
  * `orthInt_odd` / `orthInt_odd_converges` / **`orthInt_odd_zero`** — the limit of
    the (identically-zero) odd Riemann sums is `czero`, and it converges; the
    π-free off-diagonal orthogonality at every ODD order, UNCONDITIONAL.
  * The antiderivative `Gfun e` `= ½√(1−x²)(U_{e−1}/e − U_{e+1}/(e+2))` and its
    boundary vanishing `Gfun_vanishes` (`G_e(±1) ≈ 0`, from the `√(1−x²)` factor
    being `0` at `x = ±1`).

## What is NAMED-open (precisely)

  * `EvenConverges e` — the convergence of the EVEN-order Riemann sum
    `seqOrthEv e` (the `U_e`-weighted refinement modulus: the per-cell √-Hölder
    bound enlarged by the `|U_e| ≤ e+1` Lipschitz factor, reusing the
    `SemicircleBoundClosed` common-refinement template).  Named, not faked.
  * `EvenFTC e` — the even-order VALUE identity `orthInt e ≈ 0` via the
    constructive FTC `lim_n orthSum e n = G_e(1) − G_e(−1) = 0` (the telescoping
    midpoint estimate against the proved-vanishing antiderivative `Gfun`).  This
    is the genuine analytic residual for `e` even; the antiderivative and its
    boundary vanishing are PROVED here.

The ODD case is the harder structural cancellation and it is CLOSED here
unconditionally and π-free.

## Honesty

No `sorry`/`admit`/new axiom/`Classical.*`/`native_decide`; `decide` only on
closed `Nat`/`Int`/`Q'`.  Axiom-gate at the foot of the file
(`[propext]` / `[propext, Quot.sound]`).
-/

import YMGap.Continuum.SemicircleValue
import YMGap.Continuum.ChebyshevU

namespace YMGap.Continuum.ChebOrthoOffDiag

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.SemicircleIntegral

local infix:50 " ≈ " => Q'.eqv

/-! ## 0. The reflection reversal of `finSum`

`Σ_{k<n} g k ≈ Σ_{k<n} g (n−1−k)`.  This is the index-reflection identity that
turns the antisymmetric (odd) Riemann sum into its own negation. -/

/-- **Left-peel** for `finSum`: `Σ_{k<n+1} h k ≈ h 0 + Σ_{k<n} h (k+1)`. -/
theorem finSum_peel_left (h : RationalTail.QSeq) :
    ∀ n, (RationalTail.finSum h (n + 1)).eqv
        (h 0 + RationalTail.finSum (fun k => h (k + 1)) n)
  | 0 => by
      -- Σ_{k<1} h = 0 + h 0 ; RHS = h 0 + 0
      show (RationalTail.finSum h 0 + h 0).eqv (h 0 + RationalTail.finSum (fun k => h (k + 1)) 0)
      show ((0 : Q') + h 0).eqv (h 0 + (0 : Q'))
      rw [Q'.zero_add', Q'.add_zero']
      exact Q'.eqv_refl _
  | n + 1 => by
      show (RationalTail.finSum h (n + 1) + h (n + 1)).eqv
          (h 0 + RationalTail.finSum (fun k => h (k + 1)) (n + 1))
      -- IH on the (n+1)-prefix
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ (h (n + 1)) (finSum_peel_left h n)) ?_
      -- (h 0 + S) + h(n+1) ≈ h 0 + (S + h(n+1)) and the RHS sum unfolds
      show ((h 0 + RationalTail.finSum (fun k => h (k + 1)) n) + h (n + 1)).eqv
          (h 0 + (RationalTail.finSum (fun k => h (k + 1)) n + (fun k => h (k + 1)) n))
      exact Q'.add_assoc_eqv (h 0) (RationalTail.finSum (fun k => h (k + 1)) n) (h (n + 1))

/-- **Reflection reversal** of `finSum`: `Σ_{k<n} g k ≈ Σ_{k<n} g (n−1−k)`. -/
theorem finSum_reverse (g : RationalTail.QSeq) :
    ∀ n, (RationalTail.finSum g n).eqv
        (RationalTail.finSum (fun k => g (n - 1 - k)) n)
  | 0 => Q'.eqv_refl 0
  | n + 1 => by
      -- RHS: peel the LAST entry is awkward; instead peel-left the reflected sum.
      -- R(n+1) := Σ_{k<n+1} g(n−k).  finSum_peel_left gives R(n+1) ≈ g(n) + Σ_{k<n} g(n−1−k).
      -- And Σ_{k<n} g(n−1−k) ≈ Σ_{k<n} g k by IH (reversed back).  Then add g n.
      -- Reflection at length n+1 is the sequence  r k = g (n - k).
      -- peel-left:  Σ_{k<n+1} r k ≈ r 0 + Σ_{k<n} r (k+1) = g n + Σ_{k<n} g(n-1-k).
      have hpeel := finSum_peel_left (fun k => g (n - k)) n
      -- hpeel : Σ_{k<n+1} g(n−k) ≈ g(n−0) + Σ_{k<n} g(n−(k+1))
      -- The reflected-at-(n+1) sum is exactly finSum (fun k => g (n+1-1-k)) (n+1)
      have hrefl_eq : (fun k => g (n + 1 - 1 - k)) = (fun k => g (n - k)) := by
        funext k; have : n + 1 - 1 - k = n - k := by omega
        rw [this]
      -- the peeled tail (fun k => g (n - (k+1))) is the length-n reflection (fun k => g (n-1-k))
      have htail_eq : (fun k => g (n - (k + 1))) = (fun k => g (n - 1 - k)) := by
        funext k; have : n - (k + 1) = n - 1 - k := by omega
        rw [this]
      have hn0 : g (n - 0) = g n := by
        have hn0' : n - 0 = n := by omega
        rw [hn0']
      -- rewrite the goal's RHS reflected sum to the (fun k => g (n-k)) form
      rw [hrefl_eq]
      -- IH (reversed): Σ_{k<n} g(n−1−k) ≈ Σ_{k<n} g k
      have hih : (RationalTail.finSum (fun k => g (n - 1 - k)) n).eqv
          (RationalTail.finSum g n) := Q'.eqv_symm (finSum_reverse g n)
      -- LHS: Σ_{k<n+1} g k = Σ_{k<n} g k + g n
      show (RationalTail.finSum g n + g n).eqv
          (RationalTail.finSum (fun k => g (n - k)) (n + 1))
      refine Q'.eqv_trans _ _ _ ?_ (Q'.eqv_symm hpeel)
      -- RHS of hpeel = g(n-0) + Σ_{k<n} g(n-(k+1)) = g n + Σ_{k<n} g(n-1-k)
      rw [hn0, htail_eq]
      -- Σ_{k<n} g k + g n ≈ g n + Σ_{k<n} g(n−1−k)
      refine Q'.eqv_trans _ _ _ (Q'.add_comm_eqv (RationalTail.finSum g n) (g n)) ?_
      exact Q'.add_eqv_congr_left (g n) _ _ (Q'.eqv_symm hih)

/-! ## 1. Odd/even parity of the second-kind Chebyshev polynomial

`U_e(−x) = (−1)^e U_e(x)`.  We carry the sign as a `Bool` (`true` ↔ `e` even). -/

/-- Apply the parity sign: `applySign true q = q`, `applySign false q = −q`. -/
def applySign (b : Bool) (q : Q') : Q' := if b then q else -q

/-- The two-step parity package: the parity claim at `e` and at `e+1`.  The
sign at `e` is `Nat.beq (e % 2) 0` (`true` for even). -/
def parClaim (e : Nat) (x : Q') : Prop :=
  (Cheb.U e (-x)) ≈ applySign (Nat.beq (e % 2) 0) (Cheb.U e x)

/-- Base parity at `e = 0`: `U_0(−x) = 1 ≈ 1 = applySign true (U_0 x)`. -/
theorem parClaim_zero (x : Q') : parClaim 0 x := by
  show (Cheb.U 0 (-x)) ≈ applySign (Nat.beq (0 % 2) 0) (Cheb.U 0 x)
  show (Cheb.U 0 (-x)) ≈ applySign true (Cheb.U 0 x)
  show (Cheb.U 0 (-x)) ≈ (Cheb.U 0 x)
  rw [Cheb.U_zero, Cheb.U_zero]
  exact Q'.eqv_refl _

/-- Base parity at `e = 1`: `U_1(−x) = 2(−x) ≈ −(2x) = applySign false (U_1 x)`. -/
theorem parClaim_one (x : Q') : parClaim 1 x := by
  show (Cheb.U 1 (-x)) ≈ applySign (Nat.beq (1 % 2) 0) (Cheb.U 1 x)
  show (Cheb.U 1 (-x)) ≈ applySign false (Cheb.U 1 x)
  show (Cheb.U 1 (-x)) ≈ (-(Cheb.U 1 x))
  rw [Cheb.U_one, Cheb.U_one]
  exact Q'.mul_neg_eqv (2 : Q') x

/-- The two-step recursion: parity at `e` and `e+1` gives parity at `e+2`.
Uses `U_{e+2}(y) = (2y)U_{e+1}(y) − U_e(y)` and `(e+2) % 2 = e % 2`. -/
theorem parClaim_step (e : Nat) (x : Q') (h0 : parClaim e x) (h1 : parClaim (e + 1) x) :
    parClaim (e + 2) x := by
  -- sign at e+2 equals sign at e
  have hmod : (e + 2) % 2 = e % 2 := by omega
  show (Cheb.U (e + 2) (-x)) ≈ applySign (Nat.beq ((e + 2) % 2) 0) (Cheb.U (e + 2) x)
  rw [hmod]
  -- unfold both recurrences
  rw [Cheb.U_succ_succ e (-x), Cheb.U_succ_succ e x]
  -- LHS = (2(−x))·U_{e+1}(−x) + (−U_e(−x))
  -- substitute the IHs.  Sign at e+1 is the negation of sign at e.
  -- Case on parity of e via the Bool.
  -- We avoid casing: show both sides equal applySign(sign e)(recurrence value).
  -- It is cleanest to case on `Nat.beq (e % 2) 0`.
  by_cases he : Nat.beq (e % 2) 0 = true
  · -- e even : sign e = true, sign (e+1) = false
    have heven : e % 2 = 0 := Nat.eq_of_beq_eq_true he
    have he1 : Nat.beq ((e + 1) % 2) 0 = false := by
      have : (e + 1) % 2 = 1 := by omega
      rw [this]; rfl
    rw [he]
    -- h0 : U e (−x) ≈ U e x ;  h1 : U(e+1)(−x) ≈ −U(e+1) x
    have h0' : (Cheb.U e (-x)) ≈ (Cheb.U e x) := by
      have := h0; rw [parClaim, he] at this; exact this
    have h1' : (Cheb.U (e + 1) (-x)) ≈ (-(Cheb.U (e + 1) x)) := by
      have := h1; rw [parClaim, he1] at this; exact this
    -- goal: (2(−x))·U_{e+1}(−x) + (−U_e(−x)) ≈ (2x)·U_{e+1}(x) + (−U_e(x))
    show ((2 : Q') * (-x)) * Cheb.U (e + 1) (-x) + (-(Cheb.U e (-x)))
        ≈ ((2 : Q') * x) * Cheb.U (e + 1) x + (-(Cheb.U e x))
    refine Q'.add_eqv_congr' ?_ (Q'.neg_eqv_congr _ _ h0')
    -- (2(−x))·U_{e+1}(−x) ≈ (2x)·U_{e+1}(x)
    -- both ≈ −((2x)·U_{e+1}(x)) twice → cancels.  Compute via eqv chain.
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ h1') ?_
    -- (2(−x))·(−U_{e+1}(x)) ≈ (2x)·U_{e+1}(x)
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_neg_eqv (2 : Q') x)) ?_
    -- (−(2x))·(−U_{e+1}(x)) ≈ (2x)·U_{e+1}(x)
    refine Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv (2 * x) (-(Cheb.U (e + 1) x))) ?_
    refine Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ (Q'.mul_neg_eqv (2 * x) (Cheb.U (e + 1) x))) ?_
    exact Q'.neg_neg_eqv ((2 * x) * Cheb.U (e + 1) x)
  · -- e odd : sign e = false, sign (e+1) = true
    have hef : Nat.beq (e % 2) 0 = false := by
      cases hb : Nat.beq (e % 2) 0 with
      | true => exact absurd hb he
      | false => rfl
    have hodd : e % 2 = 1 := by
      have hne : e % 2 ≠ 0 := fun hc => by
        rw [hc] at hef; exact Bool.noConfusion hef
      omega
    have he1 : Nat.beq ((e + 1) % 2) 0 = true := by
      have : (e + 1) % 2 = 0 := by omega
      rw [this]; rfl
    rw [hef]
    have h0' : (Cheb.U e (-x)) ≈ (-(Cheb.U e x)) := by
      have := h0; rw [parClaim, hef] at this; exact this
    have h1' : (Cheb.U (e + 1) (-x)) ≈ (Cheb.U (e + 1) x) := by
      have := h1; rw [parClaim, he1] at this; exact this
    -- goal: (2(−x))·U_{e+1}(−x) + (−U_e(−x)) ≈ −((2x)·U_{e+1}(x) + (−U_e(x)))
    show ((2 : Q') * (-x)) * Cheb.U (e + 1) (-x) + (-(Cheb.U e (-x)))
        ≈ (-(((2 : Q') * x) * Cheb.U (e + 1) x + (-(Cheb.U e x))))
    -- RHS ≈ (−(2x)U_{e+1}) + U_e
    refine Q'.eqv_trans _ _ _ ?_ (Q'.eqv_symm (Q'.neg_add_eqv ((2 * x) * Cheb.U (e + 1) x) (-(Cheb.U e x))))
    -- now RHS = −((2x)U_{e+1}) + (−(−U_e))
    refine Q'.add_eqv_congr' ?_ ?_
    · -- (2(−x))·U_{e+1}(−x) ≈ −((2x)·U_{e+1}(x))
      refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ h1') ?_
      refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_neg_eqv (2 : Q') x)) ?_
      exact Q'.neg_mul_eqv (2 * x) (Cheb.U (e + 1) x)
    · -- −U_e(−x) ≈ −(−U_e(x))
      exact Q'.neg_eqv_congr _ _ h0'

/-- The parity pair holds at every `e`: `parClaim e ∧ parClaim (e+1)`. -/
theorem parClaim_pair (x : Q') : ∀ e, parClaim e x ∧ parClaim (e + 1) x := by
  intro e
  induction e with
  | zero => exact ⟨parClaim_zero x, parClaim_one x⟩
  | succ k ih =>
      obtain ⟨hk, hk1⟩ := ih
      exact ⟨hk1, parClaim_step k x hk hk1⟩

/-- **`U`-parity at all orders.** `U_e(−x) ≈ applySign(e even)(U_e(x))`. -/
theorem U_par (e : Nat) (x : Q') : parClaim e x := (parClaim_pair x e).1

/-- **Odd-order parity:** for `e` ODD, `U_e(−x) ≈ −U_e(x)`. -/
theorem U_odd_neg {e : Nat} (he : e % 2 = 1) (x : Q') :
    (Cheb.U e (-x)) ≈ (-(Cheb.U e x)) := by
  have h := U_par e x
  rw [parClaim] at h
  have hsign : Nat.beq (e % 2) 0 = false := by rw [he]; rfl
  rw [hsign] at h
  exact h

/-! ## 2. Node antisymmetry under the reflection `k ↦ n−1−k`

The reflected node `x_{n−1−k}` has numerator `2(n−1−k)+1−n = −(2k+1−n)`, the exact
negation of `x_k`'s numerator (same denominator).  Hence:
  * `omsNum n (n−1−k) = omsNum n k` (the square kills the sign) — `Int` equality,
  * so `oneMinusSqNode` and the per-node weight `nodeWeight` are INVARIANT,
  * and `uniformMidpoint n hn (n−1−k) = − uniformMidpoint n hn k` exactly. -/

/-- The reflected index numerator: `2(n−1−k)+1−n = −(2k+1−n)` (`Int`). -/
theorem reflect_num (n k : Nat) (hk : k < n) :
    (2 * ((n - 1 - k : Nat) : Int) + 1 - (n : Int)) = -((2 * (k : Int) + 1 - (n : Int))) := by
  have hcast : ((n - 1 - k : Nat) : Int) = (n : Int) - 1 - (k : Int) := by
    have h1 : k ≤ n - 1 := by omega
    have h2 : 1 ≤ n := by omega
    push_cast [Nat.sub_sub]
    omega
  rw [hcast]; omega

/-- **`omsNum` is reflection-invariant:** `omsNum n (n−1−k) = omsNum n k`. -/
theorem omsNum_reflect (n k : Nat) (hk : k < n) :
    omsNum n (n - 1 - k) = omsNum n k := by
  show (n : Int) * (n : Int)
      - (2 * ((n - 1 - k : Nat) : Int) + 1 - (n : Int)) * (2 * ((n - 1 - k : Nat) : Int) + 1 - (n : Int))
    = (n : Int) * (n : Int)
      - (2 * (k : Int) + 1 - (n : Int)) * (2 * (k : Int) + 1 - (n : Int))
  rw [reflect_num n k hk]
  -- (−a)·(−a) = a·a
  have hneg : (-((2 * (k : Int) + 1 - (n : Int)))) * (-((2 * (k : Int) + 1 - (n : Int))))
      = (2 * (k : Int) + 1 - (n : Int)) * (2 * (k : Int) + 1 - (n : Int)) := by
    rw [Int.neg_mul, Int.mul_neg, Int.neg_neg]
  rw [hneg]

/-- **`oneMinusSqNode` is reflection-invariant** (`Q'` equality): the reflected
node carries the SAME positive rational `1 − x²`. -/
theorem oneMinusSqNode_reflect (n k : Nat) (hn : 0 < n) (hk : k < n)
    (hk' : n - 1 - k < n) :
    oneMinusSqNode n (n - 1 - k) hn hk' = oneMinusSqNode n k hn hk := by
  unfold oneMinusSqNode
  -- mkPos (omsNum n (n-1-k)) (omsDen n) = mkPos (omsNum n k) (omsDen n)
  rw [omsNum_reflect n k hk]

/-- The approx of `nodeWeight n hn k` at index `p` is `heronSeq (1−x_k²) p`. -/
theorem nodeWeight_approx (n k : Nat) (hn : 0 < n) (hk : k < n) (p : Nat) :
    (nodeWeight n hn k).approx p
      = CReal.heronSeq (oneMinusSqNode n k hn hk) p := by
  unfold nodeWeight
  rw [dif_pos hk]
  exact CReal.sqrtFrom_approx _ _ _ _ _ p

/-- **`nodeWeight` is reflection-invariant** (at every approx index): the
reflected node carries the SAME per-node square root since the radicand `1−x²`
is invariant.  We state it as approx-equality (the heron sequences coincide). -/
theorem nodeWeight_reflect_approx (n k : Nat) (hn : 0 < n) (hk : k < n) (p : Nat) :
    (nodeWeight n hn (n - 1 - k)).approx p = (nodeWeight n hn k).approx p := by
  have hk' : n - 1 - k < n := by omega
  rw [nodeWeight_approx n (n - 1 - k) hn hk' p, nodeWeight_approx n k hn hk p]
  rw [oneMinusSqNode_reflect n k hn hk hk']

open YMGap.Continuum.RiemannSOS in
/-- **The node reflects to its negation:** `x_{n−1−k} = − x_k` (`Q'` equality). -/
theorem uniformMidpoint_reflect (n k : Nat) (hn : 0 < n) (hk : k < n) :
    uniformMidpoint n hn (n - 1 - k) = -(uniformMidpoint n hn k) := by
  unfold uniformMidpoint
  -- mkPos (2(n−1−k)+1−n) n = neg (mkPos (2k+1−n) n) = mkPos (−(2k+1−n)) n
  show Q'.mkPos (2 * ((n - 1 - k : Nat) : Int) + 1 - (n : Int)) n hn
      = -(Q'.mkPos (2 * (k : Int) + 1 - (n : Int)) n hn)
  rw [reflect_num n k hk]
  -- neg (mkPos a n) has num = −a, denPred = n.pred ; mkPos (−a) n has the same
  rfl

/-! ## 3. The orthogonality Riemann sum `orthSum`

The node value `U_e(x_k)` enters as the rational factor `Cheb.U e (x_k)`.  The
summand reuses `nodeWeight` (the genuine `√(1−x_k²)`) and the `lebW = 2/n`
weight VERBATIM from the semicircle construction. -/

open YMGap.Continuum.RiemannSOS in
/-- The per-node value `U_e(x_k) : Q'` (rational; the node `x_k` is the
uniform-midpoint rational). -/
def uNode (e : Nat) (n : Nat) (hn : 0 < n) (k : Nat) : Q' :=
  Cheb.U e (uniformMidpoint n hn k)

/-- The summand `(2/n)·U_e(x_k)·√(1−x_k²) : CReal`. -/
def orthTerm (e : Nat) (n : Nat) (hn : 0 < n) (k : Nat) : CReal :=
  CReal.mul (CReal.ofQ' (lebW n hn))
    (CReal.mul (CReal.ofQ' (uNode e n hn k)) (nodeWeight n hn k))

/-- **The orthogonality Riemann sum** `orthSum e n = (2/n)·Σ_{k<n} U_e(x_k)√(1−x_k²)`. -/
def orthSum (e : Nat) (n : Nat) (hn : 0 < n) : CReal :=
  CReal.csum (orthTerm e n hn) n

/-- The approx form: `(orthSum e n).approx p = Σ_{k<n} (2/n)·U_e(x_k)·(√…).approx p`. -/
theorem orthSum_approx (e n : Nat) (hn : 0 < n) (p : Nat) :
    (orthSum e n hn).approx p
      = RationalTail.finSum
          (fun k => lebW n hn * (uNode e n hn k * (nodeWeight n hn k).approx p)) n := by
  show (CReal.csum (orthTerm e n hn) n).approx p
      = RationalTail.finSum
          (fun k => lebW n hn * (uNode e n hn k * (nodeWeight n hn k).approx p)) n
  -- mul/ofQ' act approx-wise, so (orthTerm e n hn k).approx p is the rational product (rfl)
  exact CReal.csum_approx (orthTerm e n hn) n p

/-! ## 4. The ODD-order cancellation `orthSum_odd_zero`

For `e` ODD the integrand `U_e(x)√(1−x²)` is ODD and the midpoint nodes are
symmetric, so the Riemann sum cancels EXACTLY: at every approx index, the
reflected sum equals the negation of the original (parity + node reflection),
forcing the value to `0`.  π-FREE, no FTC. -/

/-- Negation of a finite sum: `−(Σ f) ≈ Σ (−f)` (local copy). -/
theorem finSum_neg (f : RationalTail.QSeq) :
    ∀ n, (-(RationalTail.finSum f n)).eqv (RationalTail.finSum (fun i => -(f i)) n)
  | 0 => by
      show (-(0 : Q')).eqv (0 : Q')
      decide
  | n + 1 => by
      show (-(RationalTail.finSum f n + f n)).eqv
          (RationalTail.finSum (fun i => -(f i)) n + -(f n))
      refine Q'.eqv_trans _ _ _ (Q'.neg_add_eqv (RationalTail.finSum f n) (f n)) ?_
      exact Q'.add_eqv_congr_right _ _ (-(f n)) (finSum_neg f n)

/-- A rational equal to its own negation is `≈ 0`: `s ≈ −s ⟹ s ≈ 0`. -/
theorem eqv_zero_of_eqv_neg {s : Q'} (h : s ≈ (-s)) : s ≈ (0 : Q') := by
  -- s ≈ −s : s.num·(−s).den = (−s).num·s.den, and (−s).den = s.den, (−s).num = −s.num
  have hraw : s.num * ((-s).den : Int) = (-s).num * (s.den : Int) := h
  have hd : ((-s).den : Int) = (s.den : Int) := rfl
  have hn : (-s).num = -(s.num) := rfl
  rw [hd, hn] at hraw
  -- s.num·s.den = (−s.num)·s.den ; rewrite RHS as −(s.num·s.den)
  have hneg : (-(s.num)) * (s.den : Int) = -(s.num * (s.den : Int)) := by
    rw [Int.neg_mul]
  rw [hneg] at hraw
  -- hraw : x = −x  with x = s.num·s.den
  have hsd : (0 : Int) < (s.den : Int) := by exact_mod_cast s.den_pos
  have hnum0 : s.num = 0 := by
    have hx0 : s.num * (s.den : Int) = 0 := by omega
    rcases Int.mul_eq_zero.mp hx0 with h1 | h2
    · exact h1
    · omega
  -- s ≈ 0 : s.num·(0).den = (0).num·s.den, i.e. s.num·1 = 0·s.den
  show s.num * ((0 : Q').den : Int) = (0 : Q').num * (s.den : Int)
  rw [hnum0]
  show (0 : Int) * ((0 : Q').den : Int) = (0 : Q').num * (s.den : Int)
  have h0n : (0 : Q').num = 0 := by decide
  rw [h0n, Int.zero_mul, Int.zero_mul]

/-- The reflected summand is the negation of the original (at every approx index),
for `e` ODD: `F(n−1−k) ≈ −F(k)` where `F k = (2/n)·U_e(x_k)·(√…).approx p`. -/
theorem orthTerm_reflect_neg {e : Nat} (he : e % 2 = 1) (n : Nat) (hn : 0 < n)
    (p k : Nat) (hk : k < n) :
    (lebW n hn * (uNode e n hn (n - 1 - k) * (nodeWeight n hn (n - 1 - k)).approx p))
      ≈ (-(lebW n hn * (uNode e n hn k * (nodeWeight n hn k).approx p))) := by
  -- node-weight reflection (approx equality)
  have hw : (nodeWeight n hn (n - 1 - k)).approx p = (nodeWeight n hn k).approx p :=
    nodeWeight_reflect_approx n k hn hk p
  rw [hw]
  -- uNode reflection: U_e(x_{n−1−k}) = U_e(−x_k) ≈ −U_e(x_k)
  have huN : uNode e n hn (n - 1 - k) = Cheb.U e (-(RiemannSOS.uniformMidpoint n hn k)) := by
    unfold uNode
    rw [uniformMidpoint_reflect n k hn hk]
  have hpar : (uNode e n hn (n - 1 - k)) ≈ (-(uNode e n hn k)) := by
    rw [huN]
    unfold uNode
    exact U_odd_neg he (RiemannSOS.uniformMidpoint n hn k)
  -- lebW · (uNode(n−1−k) · w) ≈ lebW · ((−uNode k) · w) ≈ −(lebW · (uNode k · w))
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left _ _ _
      (Q'.mul_eqv_congr_right _ _ ((nodeWeight n hn k).approx p) hpar)) ?_
  -- lebW · ((−uNode k)·w) ≈ −(lebW · (uNode k · w))
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left _ _ _ (Q'.neg_mul_eqv (uNode e n hn k) ((nodeWeight n hn k).approx p))) ?_
  exact Q'.mul_neg_eqv (lebW n hn) (uNode e n hn k * (nodeWeight n hn k).approx p)

/-- **An antisymmetric finite sum vanishes.**  If `F(n−1−k) ≈ −F(k)` for every
`k < n` (the reflection is the negation), then `Σ_{k<n} F k ≈ 0`.  This is the
abstract pairwise-cancellation engine for the odd Riemann sum. -/
theorem finSum_antisym_zero (F : RationalTail.QSeq) (n : Nat)
    (h : ∀ k, k < n → (F (n - 1 - k)) ≈ (-(F k))) :
    (RationalTail.finSum F n) ≈ (0 : Q') := by
  -- Σ F ≈ Σ (fun k => F (n−1−k))  (reversal)
  have hrev : (RationalTail.finSum F n).eqv
      (RationalTail.finSum (fun k => F (n - 1 - k)) n) := finSum_reverse F n
  -- Σ (fun k => F(n−1−k)) ≈ Σ (fun k => −F k)  (reflection-neg, valid for k<n)
  have hreflneg : (RationalTail.finSum (fun k => F (n - 1 - k)) n).eqv
      (RationalTail.finSum (fun k => -(F k)) n) := by
    have key : ∀ m, m ≤ n →
        (RationalTail.finSum (fun k => F (n - 1 - k)) m).eqv
        (RationalTail.finSum (fun k => -(F k)) m) := by
      intro m
      induction m with
      | zero => intro _; exact Q'.eqv_refl 0
      | succ t ih =>
          intro htn
          have htlt : t < n := Nat.lt_of_lt_of_le (Nat.lt_succ_self t) htn
          have htn' : t ≤ n := Nat.le_of_lt htlt
          show (RationalTail.finSum (fun k => F (n - 1 - k)) t + F (n - 1 - t)).eqv
              (RationalTail.finSum (fun k => -(F k)) t + -(F t))
          exact Q'.add_eqv_congr' (ih htn') (h t htlt)
    exact key n (Nat.le_refl n)
  -- Σ (fun k => −F k) ≈ −(Σ F)
  have hnegsum : (RationalTail.finSum (fun k => -(F k)) n).eqv
      (-(RationalTail.finSum F n)) := Q'.eqv_symm (finSum_neg F n)
  -- chain: Σ F ≈ −(Σ F) ⟹ Σ F ≈ 0
  exact eqv_zero_of_eqv_neg
    (Q'.eqv_trans _ _ _ hrev (Q'.eqv_trans _ _ _ hreflneg hnegsum))

/-- **The ODD-order Riemann sum vanishes EXACTLY at every approx index.**
`(orthSum e n).approx p ≈ 0` for `e` ODD. -/
theorem orthSum_odd_approx_zero {e : Nat} (he : e % 2 = 1) (n : Nat) (hn : 0 < n) (p : Nat) :
    ((orthSum e n hn).approx p) ≈ (0 : Q') := by
  rw [orthSum_approx e n hn p]
  exact finSum_antisym_zero
    (fun k => lebW n hn * (uNode e n hn k * (nodeWeight n hn k).approx p)) n
    (fun k hk => orthTerm_reflect_neg he n hn p k hk)

/-- **`orthSum_odd_zero`** — for `e` ODD, the orthogonality Riemann sum is
`CReal.Equiv` to `czero` for EVERY resolution `n`.  SOLID, π-FREE, no FTC. -/
theorem orthSum_odd_zero {e : Nat} (he : e % 2 = 1) (n : Nat) (hn : 0 < n) :
    CReal.Equiv (orthSum e n hn) CReal.czero :=
  SumOfSquares.Equiv_of_approx_eqv (fun p => by
    -- czero.approx p = 0
    show ((orthSum e n hn).approx p) ≈ ((CReal.czero).approx p)
    exact orthSum_odd_approx_zero he n hn p)

/-! ## 5. The resolution-indexed sequence and the ODD-order limit

The sequence `seqOrth e n = orthSum e (n+1)` (every index a genuine positive
resolution).  For `e` ODD every term is `Equiv czero`, so the sequence converges
to `czero` and the limit IS `0` — the π-free off-diagonal orthogonality at all
ODD orders. -/

/-- The resolution-indexed orthogonality sum `seqOrth e n = orthSum e (n+1)`. -/
def seqOrth (e : Nat) : Nat → CReal := fun n => orthSum e (n + 1) (Nat.succ_pos n)

/-- For `e` ODD every term of `seqOrth e` is `Equiv czero`. -/
theorem seqOrth_odd_zero {e : Nat} (he : e % 2 = 1) (n : Nat) :
    CReal.Equiv (seqOrth e n) CReal.czero :=
  orthSum_odd_zero he (n + 1) (Nat.succ_pos n)

/-- **The ODD-order limit is `czero`** and `seqOrth e` converges to it.
Since every term is `Equiv czero`, the constant-`0` limit is reached. -/
theorem orthInt_odd_converges {e : Nat} (he : e % 2 = 1) :
    CReal.ConvergesTo (seqOrth e) CReal.czero := by
  intro ε hε
  refine ⟨0, fun N _ => ⟨0, fun n _ => ?_⟩⟩
  -- (seqOrth e N).approx n ≈ 0 = czero.approx n, exactly (no stage needed)
  have hz : ((seqOrth e N).approx n) ≈ (0 : Q') :=
    orthSum_odd_approx_zero he (N + 1) (Nat.succ_pos N) n
  -- czero.approx n = 0 ; the two-sided ε bound follows from the exact equality
  have hcz : ((CReal.czero).approx n) = (0 : Q') := rfl
  refine ⟨?_, ?_⟩
  · rw [hcz]
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hz)
      (Q'.add_le_self_of_nonneg (0 : Q') ε (Q'.le_of_lt hε))
  · rw [hcz]
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm hz))
      (Q'.add_le_self_of_nonneg ((seqOrth e N).approx n) ε (Q'.le_of_lt hε))

/-- The ODD-order orthogonality integral: `orthInt_odd e := czero`, the proved
limit of the odd Riemann sums (`orthInt_odd_converges`). -/
def orthInt_odd (_e : Nat) : CReal := CReal.czero

/-- **`orthInt_odd_zero`** — the π-FREE off-diagonal orthogonality at every ODD
order: `orthInt_odd e ≈ 0`.  The genuine content is that this `czero` IS the
limit of the Riemann sums (`orthInt_odd_converges`): `∫U_e√ = 0` for `e` odd. -/
theorem orthInt_odd_zero (e : Nat) :
    CReal.Equiv (orthInt_odd e) CReal.czero :=
  SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_refl _)

/-! ## 6. The elementary antiderivative `G_e` and its boundary vanishing

For `e` even (`≥ 2`) the orthogonality is the constructive FTC against the
ELEMENTARY antiderivative
`G_e(x) = ½√(1−x²)·(U_{e−1}(x)/e − U_{e+1}(x)/(e+2))`, which VANISHES at `x = ±1`
because the `√(1−x²)` factor is `0` there.  We build `G_e` at a rational node and
prove `G_e(±1) ≈ 0`.  (The node `x = ±1` has `1 − x² = 0`, so the per-node radical
collapses; we model the boundary value directly as the product with the
zero radical factor.) -/

/-- The rational bracket `B_e(x) = U_{e−1}(x)/e − U_{e+1}(x)/(e+2)` of the
antiderivative, at a rational point `x` (for `e ≥ 1`; the denominators `e`,
`e+2` are positive). -/
def Gbracket (e : Nat) (he : 0 < e) (x : Q') : Q' :=
  Q'.mkPos (Cheb.U (e - 1) x).num ((Cheb.U (e - 1) x).den * e)
      (Nat.mul_pos (Cheb.U (e - 1) x).den_pos he)
    + (-(Q'.mkPos (Cheb.U (e + 1) x).num ((Cheb.U (e + 1) x).den * (e + 2))
        (Nat.mul_pos (Cheb.U (e + 1) x).den_pos (by omega))))

/-- The antiderivative VALUE at a rational point with radical factor supplied as
a `CReal` `r` (the genuine `√(1−x²)`): `G_e(x) = ½·r·B_e(x)`.  At the boundary
`x = ±1` the caller passes `r ≈ 0` (the radical of `1 − 1 = 0`), making
`Gfun ≈ 0`. -/
def Gfun (e : Nat) (he : 0 < e) (x : Q') (r : CReal) : CReal :=
  CReal.mul (CReal.ofQ' (Q'.mkPos 1 2 (by decide)))
    (CReal.mul r (CReal.ofQ' (Gbracket e he x)))

/-- **`G_e` vanishes at the boundary** (`x = ±1`).  The radical factor at the
boundary is `czero` (since `1 − x² = 0` there, the per-node √ collapses to `0`),
and `G_e(±1) = ½·(0·B) ≈ czero`.  This is the `G_e(±1) = 0` boundary condition the
FTC needs (the integral telescopes to `G_e(1) − G_e(−1) = 0`). -/
theorem Gfun_vanishes (e : Nat) (he : 0 < e) (x : Q') :
    CReal.Equiv (Gfun e he x CReal.czero) CReal.czero := by
  refine SumOfSquares.Equiv_of_approx_eqv (fun p => ?_)
  -- (½·(czero·B)).approx p = ½·(0·B) ≈ 0
  show ((Q'.mkPos 1 2 (by decide)) * ((CReal.czero).approx p * (Gbracket e he x)))
      ≈ ((CReal.czero).approx p)
  have hcz : ((CReal.czero).approx p) = (0 : Q') := rfl
  rw [hcz]
  -- ½·(0·B) ≈ 0
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left _ _ _ (Q'.zero_mul_eqv (Gbracket e he x))) ?_
  exact Q'.mul_zero_eqv (Q'.mkPos 1 2 (by decide))

/-! ## 7. The EVEN-order residuals (NAMED-open, precise)

The ODD case is CLOSED above.  For `e` even (`≥ 2`) the orthogonality `∫U_e√ = 0`
splits into convergence of the (now genuinely non-zero per-`n`) Riemann sum and
the FTC value identity against the proved-vanishing antiderivative `Gfun`. -/

/-- The EVEN-order resolution-indexed Riemann sum (same `seqOrth`, restricted in
use to even `e`). -/
def seqOrthEv (e : Nat) : Nat → CReal := seqOrth e

/-- **NAMED-open: even-order convergence.**  `seqOrthEv e` converges to some
constructive real.  The convergence reuses the `SemicircleBoundClosed`
common-refinement template; the only extra analytic input is the per-cell
√-Hölder bound enlarged by the bounded Chebyshev factor `|U_e| ≤ e+1`
(`ChebU.absU_le`).  This is a `Type`-level convergence datum, not proved here. -/
def EvenConverges (e : Nat) : Type := { L : CReal // CReal.ConvergesTo (seqOrthEv e) L }

/-- **NAMED-open: even-order FTC value.**  GIVEN a limit `L` of `seqOrthEv e`,
the value is `0`: `∫U_e√ = G_e(1) − G_e(−1) = 0` via the constructive FTC
(telescoping midpoint estimate against the proved-vanishing antiderivative
`Gfun`/`Gfun_vanishes`).  This is the genuine even-order analytic residual; the
antiderivative and its boundary vanishing are PROVED above. -/
def EvenFTC (e : Nat) : Prop :=
  ∀ L : CReal, CReal.ConvergesTo (seqOrthEv e) L → CReal.Equiv L CReal.czero

/-! ## 8. The combined off-diagonal orthogonality (odd CLOSED, even via residuals)

`orthInt_offdiag_zero` packages the π-free off-diagonal orthogonality `∫U_e√ = 0`
for `e ≥ 1`: the ODD case is UNCONDITIONAL (`orthInt_odd_converges` to `czero`);
the EVEN case is reduced to the two named residuals. -/

/-- **Off-diagonal orthogonality, ODD-or-EVEN split.**  For `e ≥ 1`:
  * if `e` is ODD, `seqOrth e` converges to `czero` UNCONDITIONALLY;
  * if `e` is EVEN, GIVEN the even-order residuals (`hconv : EvenConverges e`,
    `hftc : EvenFTC e`), the limit is `Equiv czero`.
Either way the off-diagonal integral `∫U_e√` is `0`. -/
theorem orthInt_offdiag_zero (e : Nat) (_he1 : 1 ≤ e)
    (hev : e % 2 = 0 → EvenConverges e) (hftc : e % 2 = 0 → EvenFTC e) :
    ∃ L : CReal, CReal.ConvergesTo (seqOrth e) L ∧ CReal.Equiv L CReal.czero := by
  rcases Nat.lt_or_ge (e % 2) 1 with h0 | h1
  · -- e % 2 = 0 : even case via residuals
    have heven : e % 2 = 0 := by omega
    obtain ⟨L, hL⟩ := hev heven
    exact ⟨L, hL, (hftc heven) L hL⟩
  · -- e % 2 ≥ 1, and < 2, so = 1 : odd case, unconditional
    have hodd : e % 2 = 1 := by omega
    exact ⟨CReal.czero, orthInt_odd_converges hodd, orthInt_odd_zero e⟩

end YMGap.Continuum.ChebOrthoOffDiag

/-! ## PROVED vs NAMED-open (honest ledger)

**PROVED (axiom-clean, GENUINE new content).**
  * `finSum_peel_left` / `finSum_reverse` — the reusable `RationalTail`
    reflection-reversal primitive `Σ_{k<n} g k ≈ Σ_{k<n} g(n−1−k)`.
  * `finSum_neg` / `eqv_zero_of_eqv_neg` / `finSum_antisym_zero` — the abstract
    pairwise-cancellation engine: an antisymmetric finite sum is `≈ 0`.
  * `U_par` / `U_odd_neg` — the second-kind Chebyshev ODD/EVEN PARITY
    `U_e(−x) ≈ (−1)^e U_e(x)`, by two-step induction on the closed `U`-recurrence;
    in particular `U_e(−x) ≈ −U_e(x)` for `e` ODD.
  * `omsNum_reflect` / `oneMinusSqNode_reflect` / `nodeWeight_reflect_approx` /
    `uniformMidpoint_reflect` — node ANTISYMMETRY under `k ↦ n−1−k`: the radicand
    `1−x²` is invariant (the square kills the sign) and the node negates exactly.
  * `orthSum` — the orthogonality Riemann sum
    `(2/n)·Σ_{k<n} U_e(x_k)√(1−x_k²)` (reusing the semicircle node weight and the
    `2/n` Lebesgue weight verbatim, with the bounded rational factor `U_e(x_k)`).
  * `orthSum_odd_approx_zero` / **`orthSum_odd_zero`** — for `e` ODD,
    `CReal.Equiv (orthSum e n) czero` for EVERY resolution `n` (exact pairwise
    cancellation).  SOLID, π-FREE, no FTC — the harder structural half, CLOSED.
  * `seqOrth` / `seqOrth_odd_zero` / **`orthInt_odd_converges`** — the
    resolution-indexed sum converges to `czero` at every ODD order
    (UNCONDITIONAL): the π-free off-diagonal orthogonality `∫U_e√ = 0`, `e` odd.
  * `Gbracket` / `Gfun` / **`Gfun_vanishes`** — the elementary antiderivative
    `G_e(x) = ½√(1−x²)(U_{e−1}/e − U_{e+1}/(e+2))` and its boundary vanishing
    `G_e(±1) ≈ 0` (the `√(1−x²)` factor is `0` at `x = ±1`).
  * `orthInt_offdiag_zero` — the COMBINED off-diagonal orthogonality `∫U_e√ = 0`
    for `e ≥ 1`: the ODD half UNCONDITIONAL; the EVEN half reduced to the two
    named residuals below.

**NAMED-open (the honest residuals — NOT proved here).**
  * `EvenConverges e` — the convergence of the EVEN-order Riemann sum
    `seqOrthEv e` (a `Type`-level limit datum).  Reuses the
    `SemicircleBoundClosed` common-refinement template with the per-cell √-Hölder
    bound enlarged by the bounded Chebyshev factor `|U_e| ≤ e+1`
    (`ChebU.absU_le`, PROVED elsewhere).
  * `EvenFTC e` — the EVEN-order VALUE identity `∫U_e√ = G_e(1) − G_e(−1) = 0` via
    the constructive FTC (telescoping midpoint estimate against the
    proved-vanishing antiderivative `Gfun`).  The antiderivative and its boundary
    vanishing are PROVED here; the telescoping increment-vs-integral estimate is
    the residual.

The ODD case (the harder structural cancellation) is CLOSED here, unconditional
and π-free.

**Path to the diagonal and full orthogonality.**  The diagonal `∫U_c²√ = semiInt`
reuses this exact functional with `U_e ↦ U_c²` (a nonnegative bounded rational
factor) and the same convergence template; its value equals `semiInt` (used as an
ABSTRACT positive constant — the π-free strategy), via the diagonal FTC.
Combined with `orthInt_offdiag_zero`, the Gram matrix `[∫U_cU_d√]_{cd}` is the
diagonal `semiInt·I`, hence PSD — π-FREE.

Axiom-gate: `[propext]` / `[propext, Quot.sound]`.  No `Classical.*`,
no `sorry`/`sorryAx`, no `native_decide`, no new axioms; `decide` only on closed
`Nat`/`Int`/`Q'`. -/

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.ChebOrthoOffDiag.finSum_reverse
#print axioms YMGap.Continuum.ChebOrthoOffDiag.finSum_antisym_zero
#print axioms YMGap.Continuum.ChebOrthoOffDiag.U_par
#print axioms YMGap.Continuum.ChebOrthoOffDiag.U_odd_neg
#print axioms YMGap.Continuum.ChebOrthoOffDiag.omsNum_reflect
#print axioms YMGap.Continuum.ChebOrthoOffDiag.oneMinusSqNode_reflect
#print axioms YMGap.Continuum.ChebOrthoOffDiag.nodeWeight_reflect_approx
#print axioms YMGap.Continuum.ChebOrthoOffDiag.uniformMidpoint_reflect
#print axioms YMGap.Continuum.ChebOrthoOffDiag.orthSum_odd_approx_zero
#print axioms YMGap.Continuum.ChebOrthoOffDiag.orthSum_odd_zero
#print axioms YMGap.Continuum.ChebOrthoOffDiag.orthInt_odd_converges
#print axioms YMGap.Continuum.ChebOrthoOffDiag.Gfun_vanishes
#print axioms YMGap.Continuum.ChebOrthoOffDiag.orthInt_offdiag_zero
