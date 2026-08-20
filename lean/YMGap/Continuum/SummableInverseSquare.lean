/-
The constructive **inverse-square summability endpoint** — closing a series whose
terms are dominated by `A · 1/(k+b)²` with an EXPLICIT Cauchy modulus.

# What this module delivers

Given a nonnegative term sequence `δ : Nat → Q'` and a quadratic majorant

    δ k  ≤  A · 1/(k+b)²        (A > 0, b ≥ 1 a fixed positive offset),

this module proves — entirely in the constructive rationals `Q'`, axiom-clean —
that the series `∑ δ k` is Cauchy with an explicit, witnessed modulus.  The route
is the classical telescoping `p`-series bound, but made constructive end to end:

  * **Telescoping tail (pure `Q'`).**  `1/m² ≤ 1/(m−1) − 1/m` for `m ≥ 2`
    (`invSq_le_telescope`), hence the finite-tail collapse
    `∑_{k=N}^{N+M} 1/(k+b)² ≤ 1/(N+b−1)` (`tailSum_invSq_le`).

  * **The bound form.**  `summableBound_of_invSq` packages the *uniform tail
    bound* `∑_{k=N}^{N+M} δ k ≤ A/(N+b−1)` for every window `(N, M)` — the
    `∑ ≤ R`-shaped summability statement this repo uses (the partial-sum bound
    shape of `lossSum`/`lossSummable` upstream).

  * **The modulus form (the endpoint).**  `summable_of_inverse_square_bound`
    returns, as `Type`-level data (AGENTS.md Rule 8.3), a modulus
    `N : Nat → Nat` with the witnessed guarantee that, for every precision `r`,

        ∀ N' , ∑_{k = N r}^{N' } δ k  ≤  (1/2)^r ,

    i.e. the tails past `N r` are below the dyadic threshold `(1/2)^r`.  The
    modulus is the explicit `N r = 1 + A.num.toNat · 2^r` style ceiling.

# Honesty

This is pure constructive analysis, fully proved — no open hypotheses, no
compactness, no smuggled limit.  Both the `∑ ≤ R` *bound* form and the dyadic
*modulus* form are delivered (matching whatever a downstream consumer needs).
The offset `b` is a positive `Nat` (so the denominators `(k+b)` are honest
integers and the telescope is a clean `Q'` identity); a real-valued offset is
not needed for the endpoint and is not claimed.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Every load-bearing declaration is gated with `#print axioms` at the bottom; the
permitted output is `propext` / `Quot.sound` only.  No `Classical.*`, no
`native_decide`, no `sorry`.  The modulus is `Type`-level `Q'`/`Nat` data.
-/

import YMGap.Constructive.Rationals
import YMGap.Constructive.RationalsMul
import YMGap.Constructive.Sqrt
import YMGap.Constructive.RegularCRealArith
import YMGap.Constructive.HalfPow
import YMGap.Constructive.Reals

namespace YMGap.Continuum.SummableInverseSquare

open YMGap.Constructive

/-! ## 1. Unit fractions `1/m` and the inverse-square term

`unit m = 1/m` for `m ≥ 1` (as a single `Q'`, denominator `m`).  The
inverse-square majorant term is `invSq m = 1/m² = unit (m*m)`. -/

/-- `1/m` as a `Q'` (numerator `1`, denominator `m`).  Requires `0 < m`. -/
def unit (m : Nat) (hm : 0 < m) : Q' := Q'.mkPos 1 m hm

theorem unit_num (m : Nat) (hm : 0 < m) : (unit m hm).num = 1 := rfl
theorem unit_den (m : Nat) (hm : 0 < m) : ((unit m hm).den : Int) = (m : Int) := by
  show ((Q'.mkPos 1 m hm).den : Int) = (m : Int)
  rw [Q'.mkPos_den]

theorem unit_pos (m : Nat) (hm : 0 < m) : (0 : Q') < unit m hm := by
  show (0 : Int) * ((unit m hm).den : Int) < (unit m hm).num * (1 : Int)
  rw [Int.zero_mul, Int.mul_one, unit_num]; decide

theorem unit_nonneg (m : Nat) (hm : 0 < m) : (0 : Q') ≤ unit m hm :=
  Q'.le_of_lt (unit_pos m hm)

/-! ## 2. The telescoping tail inequality (pure `Q'`)

The two facts that make the `p`-series collapse:

  * **antitone denominator:** `1/(m·m) ≤ 1/((m−1)·m)` (bigger positive
    denominator ⇒ smaller unit fraction), and
  * **telescope identity:** `1/((m−1)·m) ≃ 1/(m−1) − 1/m`.

Combined: `1/m² ≤ 1/(m−1) − 1/m` for `m ≥ 2`. -/

/-- **Antitone unit fractions.**  For `0 < a ≤ b`, `1/b ≤ 1/a`. -/
theorem unit_antitone {a b : Nat} (ha : 0 < a) (hb : 0 < b) (hab : a ≤ b) :
    unit b hb ≤ unit a ha := by
  show (unit b hb).num * ((unit a ha).den : Int)
     ≤ (unit a ha).num * ((unit b hb).den : Int)
  rw [unit_num, unit_num, unit_den, unit_den, Int.one_mul, Int.one_mul]
  exact_mod_cast hab

/-- `0 < m·m` for `2 ≤ m`. -/
theorem mm_pos (m : Nat) (hm : 2 ≤ m) : 0 < m * m :=
  Nat.mul_pos (by omega) (by omega)

/-- `0 < (m−1)·m` for `2 ≤ m`. -/
theorem m1m_pos (m : Nat) (hm : 2 ≤ m) : 0 < (m - 1) * m :=
  Nat.mul_pos (by omega) (by omega)

/-- `1/m² ≤ 1/((m−1)·m)` for `m ≥ 2` (antitone, `(m−1)·m ≤ m·m`). -/
theorem invSq_le_lower (m : Nat) (hm : 2 ≤ m) :
    unit (m * m) (mm_pos m hm) ≤ unit ((m - 1) * m) (m1m_pos m hm) := by
  refine unit_antitone (m1m_pos m hm) (mm_pos m hm) ?_
  -- (m-1)*m ≤ m*m
  have h : m - 1 ≤ m := by omega
  exact Nat.mul_le_mul_right m h

/-- **The telescope identity.**  `1/((m−1)·m) ≃ 1/(m−1) − 1/m` for `m ≥ 2`.
At the cross-product level: `den(LHS)=(m-1)m`, `RHS = 1/(m-1) + (−1/m)` has
`num = m − (m−1) = 1` over `den = (m-1)·m`, so both are `1/((m-1)m)`. -/
theorem telescope_identity (m : Nat) (hm : 2 ≤ m) :
    (unit ((m - 1) * m) (m1m_pos m hm)).eqv
      (unit (m - 1) (by omega) - unit m (by omega)) := by
  have hm1 : 0 < m - 1 := by omega
  have hm0 : 0 < m := by omega
  -- The RHS `1/(m-1) - 1/m = 1/(m-1) + (-(1/m))`.
  -- Compute its num/den via the add/neg cross-product layout.
  -- LHS num = 1, LHS den = (m-1)*m.
  -- RHS = a + (-b) with a = unit (m-1), b = unit m.
  -- (a + c).num = a.num*c.den + c.num*a.den ; (a+c).den = a.den*c.den.
  -- a.num=1, a.den=m-1 ; (-b).num = -1, (-b).den = m.
  -- RHS.num = 1*m + (-1)*(m-1) = m - (m-1) = 1.
  -- RHS.den = (m-1)*m.
  -- Compute the LHS and RHS numerators/denominators as explicit Int values.
  -- LHS = unit ((m-1)*m): num = 1, den = (m-1)*m.
  -- RHS = unit (m-1) - unit m = a + (-b):
  --   num = a.num*(-b).den + (-b).num*a.den = 1*m + (-1)*(m-1)
  --   den = a.den*b.den = (m-1)*m.
  have hLnum : (unit ((m - 1) * m) (m1m_pos m hm)).num = 1 := unit_num _ _
  have hLden : ((unit ((m - 1) * m) (m1m_pos m hm)).den : Int)
      = (((m - 1) * m : Nat) : Int) := unit_den _ _
  have hRnum : (unit (m - 1) hm1 - unit m hm0).num
      = (m : Int) + (-1) * (((m - 1 : Nat)) : Int) := by
    show (unit (m - 1) hm1).num * ((-(unit m hm0)).den : Int)
          + (-(unit m hm0)).num * ((unit (m - 1) hm1).den : Int)
        = (m : Int) + (-1) * (((m - 1 : Nat)) : Int)
    rw [unit_num]
    have hbnum : (-(unit m hm0)).num = -1 := rfl
    have hbden : ((-(unit m hm0)).den : Int) = (m : Int) := unit_den m hm0
    have haden : ((unit (m - 1) hm1).den : Int) = (((m - 1 : Nat)) : Int) :=
      unit_den (m - 1) hm1
    rw [hbnum, hbden, haden, Int.one_mul]
  have hRden : ((unit (m - 1) hm1 - unit m hm0).den : Int)
      = (((m - 1 : Nat)) : Int) * (m : Int) := by
    show (((unit (m - 1) hm1).den * (unit m hm0).den : Nat) : Int)
        = (((m - 1 : Nat)) : Int) * (m : Int)
    rw [Int.natCast_mul]
    have haden : ((unit (m - 1) hm1).den : Int) = (((m - 1 : Nat)) : Int) :=
      unit_den (m - 1) hm1
    have hbden : ((unit m hm0).den : Int) = (m : Int) := unit_den m hm0
    rw [haden, hbden]
  -- Reduce the eqv cross product to an Int equation.
  show (unit ((m - 1) * m) (m1m_pos m hm)).num
        * ((unit (m - 1) hm1 - unit m hm0).den : Int)
     = (unit (m - 1) hm1 - unit m hm0).num
        * ((unit ((m - 1) * m) (m1m_pos m hm)).den : Int)
  rw [hLnum, hLden, hRnum, hRden]
  -- Goal: 1 * ((m-1)*m cast) = (m + (-1)*(m-1)) * ((m-1)*m cast).
  -- Use the Nat-product cast and the coefficient m + (-1)*(m-1) = 1.
  have hprodcast : (((m - 1) * m : Nat) : Int) = (((m - 1 : Nat)) : Int) * (m : Int) :=
    Int.natCast_mul _ _
  have hcast : (((m - 1 : Nat)) : Int) = (m : Int) - 1 := by
    have : 1 ≤ m := by omega
    omega
  rw [hprodcast, hcast, Int.one_mul]
  -- Goal: (m-1)*m = (m + (-1)*(m-1)) * ((m-1)*m), with m-1 = m-1 (Int).
  -- coefficient (m + (-1)*(m-1)) = 1.
  have hcoef : (m : Int) + (-1) * ((m : Int) - 1) = 1 := by omega
  rw [hcoef, Int.one_mul]

/-- **The telescoping tail inequality.**  `1/m² ≤ 1/(m−1) − 1/m` for `m ≥ 2`
(antitone bound chained through the telescope identity). -/
theorem invSq_le_telescope (m : Nat) (hm : 2 ≤ m) :
    unit (m * m) (mm_pos m hm)
      ≤ unit (m - 1) (by omega) - unit m (by omega) := by
  exact Q'.le_trans' _ _ _ (invSq_le_lower m hm)
    (Q'.le_of_eqv (telescope_identity m hm))

/-! ## 3. The inverse-square term, the potential, and the finite-tail bound

Fix a positive `Nat` offset `B ≥ 2` (so every denominator `k + B ≥ 2` and the
telescope fires).  The majorant term is `invSqTerm B k = 1/(k+B)²`, the
telescoping potential is `pot B k = 1/(k+B−1)`, and the finite tail
`∑_{k=N}^{N+M−1} 1/(k+B)²` is bounded by `pot B N = 1/(N+B−1)`. -/

/-- `0 < k + B` for `B ≥ 2`. -/
theorem denom_pos (B k : Nat) (hB : 2 ≤ B) : 0 < k + B := by omega

/-- The inverse-square majorant term `1/(k+B)²`. -/
def invSqTerm (B : Nat) (hB : 2 ≤ B) (k : Nat) : Q' :=
  unit ((k + B) * (k + B)) (Nat.mul_pos (denom_pos B k hB) (denom_pos B k hB))

theorem invSqTerm_nonneg (B : Nat) (hB : 2 ≤ B) (k : Nat) :
    (0 : Q') ≤ invSqTerm B hB k :=
  unit_nonneg _ _

/-- The inverse-square majorant decreases as its natural index increases. -/
theorem invSqTerm_antitone (B : Nat) (hB : 2 <= B)
    {i j : Nat} (hij : i <= j) :
    invSqTerm B hB j <= invSqTerm B hB i := by
  unfold invSqTerm
  apply unit_antitone
  exact Nat.mul_le_mul (Nat.add_le_add_right hij B)
    (Nat.add_le_add_right hij B)

/-- The telescoping potential `1/(k+B−1)` (`= S k`). -/
def pot (B : Nat) (hB : 2 ≤ B) (k : Nat) : Q' :=
  unit (k + B - 1) (by omega)

theorem pot_nonneg (B : Nat) (hB : 2 ≤ B) (k : Nat) : (0 : Q') ≤ pot B hB k :=
  unit_nonneg _ _

/-- `pot B (k+1) = 1/((k+1)+B−1) = 1/(k+B)`, the right end of the telescope step.
This is the bookkeeping equation `S (k+1) = 1/(k+B)`. -/
theorem pot_succ_eq (B : Nat) (hB : 2 ≤ B) (k : Nat) :
    pot B hB (k + 1) = unit (k + B) (denom_pos B k hB) := by
  show unit ((k + 1) + B - 1) (by omega) = unit (k + B) (denom_pos B k hB)
  -- (k+1)+B-1 = k+B; positivity proof is irrelevant (Prop).
  congr 1
  omega

/-- **The per-term telescope step.**  `1/(k+B)² + 1/(k+B) ≤ 1/(k+B−1)`,
i.e. `invSqTerm B k + pot B (k+1) ≤ pot B k`. -/
theorem invSqTerm_add_pot_succ_le (B : Nat) (hB : 2 ≤ B) (k : Nat) :
    invSqTerm B hB k + pot B hB (k + 1) ≤ pot B hB k := by
  -- Let m := k + B (≥ 2).  Then:
  --   invSqTerm = 1/m², pot (k+1) = 1/m, pot k = 1/(m-1).
  -- The telescope `1/m² ≤ 1/(m-1) - 1/m` rearranges to `1/m² + 1/m ≤ 1/(m-1)`.
  have hm : 2 ≤ k + B := by omega
  -- pot k = unit (k+B-1); note k+B-1 = (k+B)-1 = m-1.
  -- Rewrite pot (k+1) to unit (k+B).
  rw [pot_succ_eq B hB k]
  -- invSqTerm = unit ((k+B)*(k+B)); pot k = unit (k+B-1).
  show unit ((k + B) * (k + B)) _ + unit (k + B) (denom_pos B k hB)
      ≤ unit (k + B - 1) (by omega)
  -- From invSq_le_telescope at m = k+B: unit (m*m) ≤ unit (m-1) - unit m.
  have htel : unit ((k + B) * (k + B)) (mm_pos (k + B) hm)
      ≤ unit (k + B - 1) (by omega) - unit (k + B) (by omega) :=
    invSq_le_telescope (k + B) hm
  -- Add unit (k+B) to both sides: LHS + unit m ≤ (unit (m-1) - unit m) + unit m ≃ unit (m-1).
  have hstep : unit ((k + B) * (k + B)) (mm_pos (k + B) hm)
        + unit (k + B) (denom_pos B k hB)
      ≤ (unit (k + B - 1) (by omega) - unit (k + B) (by omega))
        + unit (k + B) (denom_pos B k hB) :=
    Q'.add_le_add_right _ _ _ htel
  refine Q'.le_trans' _ _ _ hstep ?_
  -- (unit (m-1) - unit m) + unit m ≃ unit (m-1).
  have hcollapse :
      ((unit (k + B - 1) (by omega) - unit (k + B) (by omega))
        + unit (k + B) (denom_pos B k hB)).eqv (unit (k + B - 1) (by omega)) := by
    -- (a + (-b)) + b ≃ a + ((-b) + b) ≃ a + 0 ≃ a.
    refine Q'.eqv_trans _ _ _
      (Q'.add_assoc_eqv (unit (k + B - 1) (by omega))
        (-(unit (k + B) (by omega))) (unit (k + B) (denom_pos B k hB))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (unit (k + B - 1) (by omega)) _ 0
        (Q'.neg_add_self_eqv (unit (k + B) (by omega)))) ?_
    exact Q'.eqv_of_eq (Q'.add_zero' (unit (k + B - 1) (by omega)))
  exact Q'.le_of_eqv hcollapse

/-! ## 4. The finite-tail sum bound

`tailSum f N M = ∑_{j<M} f (N+j)` (a window of `M` terms starting at `N`).  The
telescoping potential bounds the inverse-square tail:
`tailSum invSqTerm N M ≤ pot B N = 1/(N+B−1)`, uniformly in the window length
`M`. -/

/-- `tailSum f N M = ∑_{j<M} f (N+j)`. -/
def tailSum (f : Nat → Q') (N : Nat) : Nat → Q'
  | 0 => 0
  | M + 1 => tailSum f N M + f (N + M)

@[simp] theorem tailSum_zero (f : Nat → Q') (N : Nat) : tailSum f N 0 = 0 := rfl
@[simp] theorem tailSum_succ (f : Nat → Q') (N M : Nat) :
    tailSum f N (M + 1) = tailSum f N M + f (N + M) := rfl

/-- `tailSum` of a nonnegative sequence is nonnegative. -/
theorem tailSum_nonneg (f : Nat → Q') (hf : ∀ k, (0 : Q') ≤ f k) (N : Nat) :
    ∀ M, (0 : Q') ≤ tailSum f N M
  | 0 => Q'.le_refl' 0
  | M + 1 => by
    show (0 : Q') ≤ tailSum f N M + f (N + M)
    exact Q'.zero_le_add _ _ (tailSum_nonneg f hf N M) (hf (N + M))

/-- **The telescoping collapse (inequality form).**  For the inverse-square term,
`tailSum invSqTerm N M + pot B (N+M) ≤ pot B N` for every window length `M`.
Induction on `M`: the step adds the per-term telescope
`invSqTerm (N+M) + pot (N+M+1) ≤ pot (N+M)`. -/
theorem tailSum_invSq_add_pot_le (B : Nat) (hB : 2 ≤ B) (N : Nat) :
    ∀ M, tailSum (invSqTerm B hB) N M + pot B hB (N + M) ≤ pot B hB N
  | 0 => by
    -- tailSum .. 0 + pot (N+0) = 0 + pot N ≤ pot N.
    show (0 : Q') + pot B hB (N + 0) ≤ pot B hB N
    have he : N + 0 = N := by omega
    rw [he]
    exact Q'.le_of_eqv (Q'.eqv_of_eq (Q'.zero_add' (pot B hB N)))
  | M + 1 => by
    have ih := tailSum_invSq_add_pot_le B hB N M
    -- LHS = (tailSum .. M + invSqTerm (N+M)) + pot (N+M+1).
    show (tailSum (invSqTerm B hB) N M + invSqTerm B hB (N + M))
        + pot B hB (N + (M + 1)) ≤ pot B hB N
    -- Reassociate to tailSum .. M + (invSqTerm (N+M) + pot (N+(M+1))).
    have hidx : N + (M + 1) = (N + M) + 1 := by omega
    rw [hidx]
    -- per-term telescope at k = N+M: invSqTerm (N+M) + pot ((N+M)+1) ≤ pot (N+M).
    have hterm : invSqTerm B hB (N + M) + pot B hB ((N + M) + 1)
        ≤ pot B hB (N + M) :=
      invSqTerm_add_pot_succ_le B hB (N + M)
    -- (tailSum M + invSqTerm) + pot(N+M+1)  ≃  tailSum M + (invSqTerm + pot(N+M+1))
    have hassoc :
        ((tailSum (invSqTerm B hB) N M + invSqTerm B hB (N + M))
          + pot B hB ((N + M) + 1)).eqv
        (tailSum (invSqTerm B hB) N M
          + (invSqTerm B hB (N + M) + pot B hB ((N + M) + 1))) :=
      Q'.add_assoc_eqv _ _ _
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hassoc) ?_
    -- tailSum M + (invSqTerm + pot(N+M+1)) ≤ tailSum M + pot(N+M) ≤ pot N.
    have hmono : tailSum (invSqTerm B hB) N M
          + (invSqTerm B hB (N + M) + pot B hB ((N + M) + 1))
        ≤ tailSum (invSqTerm B hB) N M + pot B hB (N + M) :=
      Q'.add_le_add_left _ _ _ hterm
    exact Q'.le_trans' _ _ _ hmono ih

/-- **The finite inverse-square tail bound.**  `∑_{k=N}^{N+M−1} 1/(k+B)² ≤
1/(N+B−1)`, uniformly in `M` (drop the nonnegative `pot B (N+M)`). -/
theorem tailSum_invSq_le (B : Nat) (hB : 2 ≤ B) (N M : Nat) :
    tailSum (invSqTerm B hB) N M ≤ pot B hB N := by
  refine Q'.le_trans' _ _ _ ?_ (tailSum_invSq_add_pot_le B hB N M)
  exact Q'.add_le_self_of_nonneg _ _ (pot_nonneg B hB (N + M))

/-! ## 5. The scaled (majorant) tail bound

From `0 ≤ δ k ≤ A · invSqTerm B k`, the tail of `δ` is bounded by
`A · pot B N = A/(N+B−1)`. -/

/-- `tailSum δ N M ≤ A · tailSum invSqTerm N M` from the per-term majorant
`δ k ≤ A · invSqTerm k`.  Induction on `M`. -/
theorem tailSum_le_scaled (B : Nat) (hB : 2 ≤ B) (A : Q') (δ : Nat → Q')
    (hmaj : ∀ k, δ k ≤ A * invSqTerm B hB k) (N : Nat) :
    ∀ M, tailSum δ N M ≤ A * tailSum (invSqTerm B hB) N M
  | 0 => by
    -- 0 ≤ A * 0 ≃ 0
    show (0 : Q') ≤ A * (0 : Q')
    -- A * 0 ≃ 0 (mul_one? use mul on 0).  0 ≤ A*0 via eqv to 0.
    have h0 : (A * (0 : Q')).eqv 0 := by
      refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv A 0) ?_
      -- 0 * A ≃ 0
      show (0 * A).num * ((0 : Q').den : Int) = (0 : Q').num * ((0 * A).den : Int)
      show ((0 : Int) * A.num) * (1 : Int) = (0 : Int) * (((0 * A).den : Nat) : Int)
      rw [Int.zero_mul, Int.zero_mul, Int.zero_mul]
    exact Q'.ge_of_eqv h0
  | M + 1 => by
    have ih := tailSum_le_scaled B hB A δ hmaj N M
    show tailSum δ N M + δ (N + M)
        ≤ A * (tailSum (invSqTerm B hB) N M + invSqTerm B hB (N + M))
    -- A*(x+y) ≃ A*x + A*y
    have hdist : (A * (tailSum (invSqTerm B hB) N M + invSqTerm B hB (N + M))).eqv
        (A * tailSum (invSqTerm B hB) N M + A * invSqTerm B hB (N + M)) :=
      Q'.mul_add_eqv A _ _
    refine Q'.le_trans' _ _ _ ?_ (Q'.ge_of_eqv hdist)
    -- tailSum δ M + δ(N+M) ≤ A*tailSum invSq M + A*invSqTerm(N+M)
    have h1 : tailSum δ N M + δ (N + M)
        ≤ (A * tailSum (invSqTerm B hB) N M) + δ (N + M) :=
      Q'.add_le_add_right _ _ _ ih
    have h2 : (A * tailSum (invSqTerm B hB) N M) + δ (N + M)
        ≤ (A * tailSum (invSqTerm B hB) N M) + A * invSqTerm B hB (N + M) :=
      Q'.add_le_add_left _ _ _ (hmaj (N + M))
    exact Q'.le_trans' _ _ _ h1 h2

/-- **The scaled inverse-square tail bound (the `∑ ≤ R` bound form).**
For `A ≥ 0` and a majorant `0 ≤ δ k ≤ A · 1/(k+B)²`,

    ∑_{k=N}^{N+M−1} δ k  ≤  A / (N+B−1)        (= A · pot B N),

uniformly in the window length `M`. -/
theorem summableBound_of_invSq (B : Nat) (hB : 2 ≤ B) (A : Q') (hA : (0 : Q') ≤ A)
    (δ : Nat → Q') (hmaj : ∀ k, δ k ≤ A * invSqTerm B hB k) (N M : Nat) :
    tailSum δ N M ≤ A * pot B hB N := by
  refine Q'.le_trans' _ _ _ (tailSum_le_scaled B hB A δ hmaj N M) ?_
  -- A * tailSum invSq N M ≤ A * pot B N (mult by A ≥ 0 on the left, monotone)
  exact Q'.mul_le_mul_of_nonneg_left _ _ A (tailSum_invSq_le B hB N M) hA

/-! ## 6. The dyadic modulus form (the endpoint)

The dyadic threshold `(1/2)^r` equals the unit fraction `1/2^r`.  Choosing the
explicit modulus `N r = A.num.toNat · 2^r + 1`, the scaled tail bound
`A · 1/(N+B−1)` drops below `(1/2)^r`, giving the Cauchy-modulus statement:
for every precision `r`, every window past `N r` has `∑ δ ≤ (1/2)^r`. -/

/-- `2^r > 0` as a `Nat`. -/
theorem twoPow_pos (r : Nat) : 0 < 2 ^ r := Nat.pow_pos (by decide)

/-- **`(1/2)^r ≃ 1/2^r`.**  The dyadic threshold is the unit fraction with
denominator `2^r`.  Induction on `r`. -/
theorem half_pow_eqv_unit :
    ∀ r : Nat, (HalfPow.half ^ r).eqv (unit (2 ^ r) (twoPow_pos r))
  | 0 => by
    -- half^0 = 1 ; unit (2^0) = unit 1 = 1/1.  1 ≃ 1/1.
    show ((1 : Q')).eqv (unit (2 ^ 0) (twoPow_pos 0))
    show ((1 : Q')).num * ((unit (2 ^ 0) (twoPow_pos 0)).den : Int)
        = (unit (2 ^ 0) (twoPow_pos 0)).num * ((1 : Q').den : Int)
    rw [unit_num, unit_den]
    -- 1 * (2^0 : Int) = 1 * 1 ; 2^0 = 1.
    show (1 : Int) * ((2 ^ 0 : Nat) : Int) = (1 : Int) * (1 : Int)
    have h20 : (2 ^ 0 : Nat) = 1 := by decide
    rw [h20]
    have hc : ((1 : Nat) : Int) = (1 : Int) := by decide
    rw [hc]
  | r + 1 => by
    -- half^(r+1) = half * half^r ≃ half * unit(2^r) ≃ unit(2^(r+1)).
    show (HalfPow.half * HalfPow.half ^ r).eqv (unit (2 ^ (r + 1)) (twoPow_pos (r + 1)))
    have ih := half_pow_eqv_unit r
    -- half * half^r ≃ half * unit(2^r)
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left HalfPow.half _ _ ih) ?_
    -- half * unit(2^r) ≃ unit(2^(r+1)): num 1*1=1, den 2*2^r = 2^(r+1).
    show (HalfPow.half * unit (2 ^ r) (twoPow_pos r)).eqv
        (unit (2 ^ (r + 1)) (twoPow_pos (r + 1)))
    show (HalfPow.half * unit (2 ^ r) (twoPow_pos r)).num
          * ((unit (2 ^ (r + 1)) (twoPow_pos (r + 1))).den : Int)
        = (unit (2 ^ (r + 1)) (twoPow_pos (r + 1))).num
          * ((HalfPow.half * unit (2 ^ r) (twoPow_pos r)).den : Int)
    rw [unit_num, unit_den]
    -- LHS num = half.num * (unit).num = 1 * 1 = 1.
    have hlnum : (HalfPow.half * unit (2 ^ r) (twoPow_pos r)).num = 1 := by
      show HalfPow.half.num * (unit (2 ^ r) (twoPow_pos r)).num = 1
      rw [unit_num]
      show (1 : Int) * 1 = 1
      decide
    -- LHS den = half.den * (unit).den = 2 * 2^r = 2^(r+1).
    have hlden : ((HalfPow.half * unit (2 ^ r) (twoPow_pos r)).den : Int)
        = ((2 ^ (r + 1) : Nat) : Int) := by
      rw [Q'.mul_den_cast]
      -- half.den = 2 ; unit (2^r).den = 2^r.  Keep the `2` as a Nat-cast so it
      -- matches the cast of the product on the RHS.
      have hhd : (HalfPow.half.den : Int) = ((2 : Nat) : Int) := by decide
      have hud : ((unit (2 ^ r) (twoPow_pos r)).den : Int) = ((2 ^ r : Nat) : Int) :=
        unit_den _ _
      rw [hhd, hud]
      -- 2 * 2^r = 2^(r+1)
      have hp : (2 ^ (r + 1) : Nat) = 2 * 2 ^ r := by
        rw [Nat.pow_succ, Nat.mul_comm]
      rw [hp, Int.natCast_mul]
    rw [hlnum, hlden]

/-- The explicit dyadic modulus `N r = A.num.toNat · 2^r + 1`. -/
def invSqModulus (A : Q') (r : Nat) : Nat := A.num.toNat * 2 ^ r + 1

/-- **The scaled tail at the modulus drops below `1/2^r`.**  For `A ≥ 0`,
`A · pot B (N r) ≤ unit (2^r) = 1/2^r`, where `N r = invSqModulus A r`.
At the cross-product level (`pot B N = 1/(N+B−1)`, `unit(2^r) = 1/2^r`):
`A.num · 2^r ≤ A.den · (N+B−1)` since `N+B−1 ≥ A.num.toNat·2^r ≥ A.num·2^r`
and `A.den ≥ 1`. -/
theorem scaled_pot_le_unit (B : Nat) (hB : 2 ≤ B) (A : Q') (hA : (0 : Q') ≤ A)
    (r : Nat) :
    A * pot B hB (invSqModulus A r)
      ≤ unit (2 ^ r) (twoPow_pos r) := by
  have hAnum : 0 ≤ A.num := (Q'.zero_le_iff_num_nonneg A).mp hA
  -- pot B N = unit (N + B - 1).
  show A * unit (invSqModulus A r + B - 1) (by omega)
      ≤ unit (2 ^ r) (twoPow_pos r)
  -- Cross product of `A * unit d ≤ unit (2^r)`.
  -- (A * unit d).num = A.num * 1 = A.num ; (A * unit d).den = A.den * d.
  show (A * unit (invSqModulus A r + B - 1) (by omega)).num
        * ((unit (2 ^ r) (twoPow_pos r)).den : Int)
     ≤ (unit (2 ^ r) (twoPow_pos r)).num
        * ((A * unit (invSqModulus A r + B - 1) (by omega)).den : Int)
  -- numerators / denominators.
  have hLnum : (A * unit (invSqModulus A r + B - 1) (by omega)).num = A.num := by
    show A.num * (unit (invSqModulus A r + B - 1) (by omega)).num = A.num
    rw [unit_num, Int.mul_one]
  have hLden : ((A * unit (invSqModulus A r + B - 1) (by omega)).den : Int)
      = (A.den : Int) * ((invSqModulus A r + B - 1 : Nat) : Int) := by
    rw [Q'.mul_den_cast]
    have hud : ((unit (invSqModulus A r + B - 1) (by omega)).den : Int)
        = ((invSqModulus A r + B - 1 : Nat) : Int) := unit_den _ _
    rw [hud]
  rw [hLnum, hLden, unit_num, unit_den, Int.one_mul]
  -- Goal: A.num * (2^r : Int) ≤ A.den * (N+B-1 : Int).
  -- N + B - 1 = A.num.toNat*2^r + B - 1 ≥ A.num.toNat*2^r (since B ≥ 2 ≥ 1).
  -- A.den ≥ 1, A.num.toNat = A.num (A.num ≥ 0). So RHS ≥ A.num*2^r = LHS.
  have htoNat : (A.num.toNat : Int) = A.num := Int.toNat_of_nonneg hAnum
  -- Lower-bound the Nat (N+B-1) by A.num.toNat * 2^r.
  have hNB : A.num.toNat * 2 ^ r ≤ invSqModulus A r + B - 1 := by
    show A.num.toNat * 2 ^ r ≤ (A.num.toNat * 2 ^ r + 1) + B - 1
    omega
  have hNBcast : (A.num.toNat : Int) * ((2 ^ r : Nat) : Int)
      ≤ ((invSqModulus A r + B - 1 : Nat) : Int) := by
    have := hNB
    have hc : ((A.num.toNat * 2 ^ r : Nat) : Int)
        ≤ ((invSqModulus A r + B - 1 : Nat) : Int) := by exact_mod_cast this
    rwa [Int.natCast_mul] at hc
  -- A.num * 2^r = A.num.toNat * 2^r ≤ (N+B-1) ≤ A.den * (N+B-1).
  have hden1 : (1 : Int) ≤ (A.den : Int) := by exact_mod_cast A.den_pos
  have hstep1 : A.num * ((2 ^ r : Nat) : Int)
      ≤ ((invSqModulus A r + B - 1 : Nat) : Int) := by
    rw [← htoNat]; exact hNBcast
  have hNBnn : (0 : Int) ≤ ((invSqModulus A r + B - 1 : Nat) : Int) := by
    exact_mod_cast Nat.zero_le _
  have hstep2 : ((invSqModulus A r + B - 1 : Nat) : Int)
      ≤ (A.den : Int) * ((invSqModulus A r + B - 1 : Nat) : Int) := by
    have := Int.mul_le_mul_of_nonneg_right hden1 hNBnn
    rwa [Int.one_mul] at this
  exact Int.le_trans hstep1 hstep2

/-- **The inverse-square summability endpoint (modulus form).**  For `A > 0`,
offset `B ≥ 2`, and a nonnegative sequence `δ` dominated by `δ k ≤ A · 1/(k+B)²`,
the series `∑ δ` is Cauchy with the EXPLICIT modulus `N r = A.num.toNat·2^r + 1`:
for every precision `r` and every window length `M`,

    ∑_{k = N r}^{N r + M − 1} δ k  ≤  (1/2)^r .

The modulus is returned as `Type`-level data (a function `Nat → Nat`) together
with the witnessed tail guarantee (AGENTS.md Rule 8.3). -/
def summable_of_inverse_square_bound
    (A : Q') (B : Nat) (hA : (0 : Q') < A) (hB : 2 ≤ B)
    (δ : Nat → Q')
    (_hδ0 : ∀ k, (0 : Q') ≤ δ k)
    (hδmaj : ∀ k, δ k ≤ A * invSqTerm B hB k) :
    Σ' N : Nat → Nat,
      ∀ r M, tailSum δ (N r) M ≤ HalfPow.half ^ r :=
  ⟨invSqModulus A, fun r M => by
    -- tail ≤ A·pot B (N r) ≤ unit(2^r) ≃ (1/2)^r.
    have h1 : tailSum δ (invSqModulus A r) M
        ≤ A * pot B hB (invSqModulus A r) :=
      summableBound_of_invSq B hB A (Q'.le_of_lt hA) δ hδmaj (invSqModulus A r) M
    have h2 : A * pot B hB (invSqModulus A r) ≤ unit (2 ^ r) (twoPow_pos r) :=
      scaled_pot_le_unit B hB A (Q'.le_of_lt hA) r
    have h3 : unit (2 ^ r) (twoPow_pos r) ≤ HalfPow.half ^ r :=
      Q'.ge_of_eqv (half_pow_eqv_unit r)
    exact Q'.le_trans' _ _ _ h1 (Q'.le_trans' _ _ _ h2 h3)⟩

/-! ## 7. Demo: the theorem fires on `δ_k = 1/(k+2)²`

A self-contained instance.  With `B = 2`, `A = 1`, and `δ k = 1/(k+2)²`
(`= invSqTerm 2 k`), the majorant `δ k ≤ 1 · 1/(k+2)²` holds (with equality), so
the endpoint produces the explicit Cauchy modulus `N r = 2^r + 1`. -/

/-- The demo sequence `δ_k = 1/(k+2)²`. -/
def demoSeq (k : Nat) : Q' := invSqTerm 2 (by decide) k

/-- The demo majorant `1/(k+2)² ≤ 1 · 1/(k+2)²` (with equality). -/
theorem demo_majorant (k : Nat) :
    demoSeq k ≤ (1 : Q') * invSqTerm 2 (by decide) k := by
  show invSqTerm 2 (by decide) k ≤ (1 : Q') * invSqTerm 2 (by decide) k
  exact Q'.ge_of_eqv (Q'.one_mul_eqv (invSqTerm 2 (by decide) k))

/-- **The endpoint fires on `δ_k = 1/(k+2)²`.**  An explicit Cauchy modulus
`Σ' N, ∀ r M, ∑_{k=N r}^{N r + M − 1} δ k ≤ (1/2)^r` for the inverse-square
series, with modulus `N r = invSqModulus 1 r = 2^r + 1`. -/
def demo_summable :
    Σ' N : Nat → Nat,
      ∀ r M, tailSum demoSeq (N r) M ≤ HalfPow.half ^ r :=
  summable_of_inverse_square_bound 1 2 (by decide) (by decide)
    demoSeq (fun k => invSqTerm_nonneg 2 (by decide) k) demo_majorant

end YMGap.Continuum.SummableInverseSquare

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.SummableInverseSquare.unit_antitone
#print axioms YMGap.Continuum.SummableInverseSquare.invSqTerm_antitone
#print axioms YMGap.Continuum.SummableInverseSquare.invSq_le_lower
#print axioms YMGap.Continuum.SummableInverseSquare.telescope_identity
#print axioms YMGap.Continuum.SummableInverseSquare.invSq_le_telescope
#print axioms YMGap.Continuum.SummableInverseSquare.invSqTerm_add_pot_succ_le
#print axioms YMGap.Continuum.SummableInverseSquare.tailSum_invSq_add_pot_le
#print axioms YMGap.Continuum.SummableInverseSquare.tailSum_invSq_le
#print axioms YMGap.Continuum.SummableInverseSquare.tailSum_le_scaled
#print axioms YMGap.Continuum.SummableInverseSquare.summableBound_of_invSq
#print axioms YMGap.Continuum.SummableInverseSquare.half_pow_eqv_unit
#print axioms YMGap.Continuum.SummableInverseSquare.scaled_pot_le_unit
#print axioms YMGap.Continuum.SummableInverseSquare.summable_of_inverse_square_bound
#print axioms YMGap.Continuum.SummableInverseSquare.demo_summable
