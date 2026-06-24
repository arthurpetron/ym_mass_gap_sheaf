/-
# The value-level inter-resolution Riemann estimate for the semicircle integral

This module attacks the single remaining residual of the semicircle Riemann
convergence — `SemicircleInterRes.ValueInterRes`, the value-level inter-resolution
estimate — by supplying its three constituent pieces:

  * PIECE 1 — the nonlinear `Int` **radicand node-gap** arithmetic
    `radicandGap_le`: at the refined node pair `(P,i)` / `(P·Q, i·Q+s)`, the
    radicand gap satisfies `|(1 − x_i²) − (1 − y_{iQ+s}²)| ≤ 2/P`.  The numerator
    factors as `(2s+1−Q)·(4iQ+2s+1+Q−2PQ)` over `(PQ)²`; the two factors are
    bounded (`|·| ≤ Q`, `|·| ≤ 2PQ`) by `omega`, and the nonlinear product is
    bounded by MANUAL `Int` product-monotonicity (`omega` cannot multiply
    variables).  This discharges residual (a) named in `SemicircleInterRes`.

  * PIECE 2 — the **cell-sum** refinement bound `semiSum_refine_le`: regroup the
    `(P·Q)`-mesh sum by cells `j = i·Q + s`, telescope the weight identity
    `lebW P = Q·lebW (P·Q)`, bound each cell difference by the proved per-cell
    √-Hölder estimate `SemicircleInterRes.cellRefine_holder`, and sum.

  * PIECE 3 — the **combine + reduction** inhabiting
    `SemicircleInterRes.ValueInterRes` FROM the canonical residual
    `SemicircleConverge.UniformRiemannBound` (via `unflip_le`; `valK := 0` since
    the Riemann bound is uniform in `k`), reducing the semicircle limit
    `semiIntUncond`/`_converges`/`_nonneg`/`_leRat_two` to that SINGLE residual,
    whose per-cell input (PIECE 1) and cell regrouping (PIECE 2) are proved here.

## Honesty

No `sorry`/`admit`/new axiom/`Classical.*`/`native_decide`; `decide` only on
closed `Nat`/`Int`/`Q'`.  PROVED / NAMED-open ledger at the foot of the file.
Axiom-gate: `[propext]` / `[propext, Quot.sound]`.
-/

import YMGap.Continuum.SemicircleInterRes
import YMGap.Continuum.SemicircleInnerModulus

namespace YMGap.Continuum.SemicircleValueRes

open YMGap.Constructive
open YMGap.Constructive.HalfPow
open YMGap.Continuum
open YMGap.Continuum.SemicircleIntegral
open YMGap.Continuum.SemicircleConverge
open YMGap.Continuum.SemicircleInnerModulus
open YMGap.Continuum.SemicircleInterRes

/-! ## PIECE 1 — the nonlinear `Int` radicand node-gap arithmetic

`oneMinusSqNode P i = (P² − (2i+1−P)²)/P²`, `oneMinusSqNode (PQ) j =
((PQ)² − (2j+1−PQ)²)/(PQ)²`.  With `j = i·Q + s` (`s < Q`), the difference, put
over the common denominator `(PQ)²`, has numerator

    D := omsNum P i · Q²  −  omsNum (PQ) (iQ+s)
       = (2s+1−Q) · (4iQ + 2s+1 + Q − 2PQ)                       (PROVED below),

a product of one factor with `|·| ≤ Q` and one with `|·| ≤ 2PQ`, so
`|D| ≤ 2PQ²` and hence `|gap| = |D|/(PQ)² ≤ 2PQ²/(P²Q²) = 2/P`. -/

/-- The first node-gap factor `2s+1−Q`. -/
def gapF1 (Q s : Nat) : Int := 2 * (s : Int) + 1 - (Q : Int)

/-- The second node-gap factor `4iQ + 2s+1 + Q − 2PQ`. -/
def gapF2 (P Q i s : Nat) : Int :=
  4 * (i : Int) * (Q : Int) + 2 * (s : Int) + 1 + (Q : Int) - 2 * (P : Int) * (Q : Int)

/-- `(a·a)·(b·b) = (a·b)·(a·b)` — degree-4 product rearrangement (pure `Int`
`mul_comm`/`mul_assoc`, no `ring`). -/
theorem sq_mul_sq (a b : Int) : (a * a) * (b * b) = (a * b) * (a * b) := by
  rw [Int.mul_assoc, Int.mul_assoc, ← Int.mul_assoc a b b, Int.mul_comm a b,
      Int.mul_assoc b a b, Int.mul_comm a b]

/-- **The node-gap numerator factorisation.**
`omsNum P i · Q² − omsNum (P·Q) (i·Q+s) = (2s+1−Q)·(4iQ+2s+1+Q−2PQ)`.
Pure `Int` identity: write `D = v² − u²` with `u = (2i+1−P)·Q`,
`v = 2(iQ+s)+1−PQ`, factor by `int_sq_diff_factor`, and read off the two factors
`v−u = 2s+1−Q`, `v+u = 4iQ+2s+1+Q−2PQ` (the nonlinear `iQ`,`PQ` monomials cancel,
so `omega` closes the linear residue). -/
theorem omsNum_gap_factor (P Q i s : Nat) :
    omsNum P i * ((Q : Int) * (Q : Int)) - omsNum (P * Q) (i * Q + s)
      = gapF1 Q s * gapF2 P Q i s := by
  -- (1) omsNum P i · Q² = (PQ)² − u²  with u = (2i+1−P)·Q
  have hA : omsNum P i * ((Q : Int) * (Q : Int))
      = ((P : Int) * (Q : Int)) * ((P : Int) * (Q : Int))
        - ((2 * (i : Int) + 1 - (P : Int)) * (Q : Int))
          * ((2 * (i : Int) + 1 - (P : Int)) * (Q : Int)) := by
    show ((P : Int) * (P : Int)
        - (2 * (i : Int) + 1 - (P : Int)) * (2 * (i : Int) + 1 - (P : Int)))
          * ((Q : Int) * (Q : Int)) = _
    rw [Int.sub_mul, sq_mul_sq (P : Int) (Q : Int),
        sq_mul_sq (2 * (i : Int) + 1 - (P : Int)) (Q : Int)]
  -- (2) omsNum (PQ) j = (PQ)² − v²  with v = 2(iQ+s)+1−PQ
  have hcast : ((P * Q : Nat) : Int) = (P : Int) * (Q : Int) := by push_cast; rfl
  have hcast2 : ((i * Q + s : Nat) : Int) = (i : Int) * (Q : Int) + (s : Int) := by
    push_cast; rfl
  have hB : omsNum (P * Q) (i * Q + s)
      = ((P : Int) * (Q : Int)) * ((P : Int) * (Q : Int))
        - (2 * ((i : Int) * (Q : Int) + (s : Int)) + 1 - (P : Int) * (Q : Int))
          * (2 * ((i : Int) * (Q : Int) + (s : Int)) + 1 - (P : Int) * (Q : Int)) := by
    show ((P * Q : Nat) : Int) * ((P * Q : Nat) : Int)
        - (2 * ((i * Q + s : Nat) : Int) + 1 - ((P * Q : Nat) : Int))
          * (2 * ((i * Q + s : Nat) : Int) + 1 - ((P * Q : Nat) : Int)) = _
    rw [hcast, hcast2]
  rw [hA, hB]
  -- The two factors v−u, v+u are LINEAR in the atoms iQ, PQ (the products cancel).
  -- Establish them as named equalities while u,v are still concrete.
  have hfac1 :
      (2 * ((i : Int) * (Q : Int) + (s : Int)) + 1 - (P : Int) * (Q : Int))
        - (2 * (i : Int) + 1 - (P : Int)) * (Q : Int)
      = gapF1 Q s := by
    unfold gapF1
    -- expand the product (2i+1−P)·Q into atoms, then omega.
    have e1 : (2 * (i : Int) + 1 - (P : Int)) * (Q : Int)
        = 2 * ((i : Int) * (Q : Int)) + (Q : Int) - (P : Int) * (Q : Int) := by
      rw [Int.sub_mul, Int.add_mul, Int.one_mul, Int.mul_assoc]
    have e2 : 2 * ((i : Int) * (Q : Int) + (s : Int))
        = 2 * ((i : Int) * (Q : Int)) + 2 * (s : Int) := by rw [Int.mul_add]
    rw [e1, e2]
    generalize (i : Int) * (Q : Int) = X
    generalize (P : Int) * (Q : Int) = Y
    omega
  have hfac2 :
      (2 * ((i : Int) * (Q : Int) + (s : Int)) + 1 - (P : Int) * (Q : Int))
        + (2 * (i : Int) + 1 - (P : Int)) * (Q : Int)
      = gapF2 P Q i s := by
    unfold gapF2
    have e1 : (2 * (i : Int) + 1 - (P : Int)) * (Q : Int)
        = 2 * ((i : Int) * (Q : Int)) + (Q : Int) - (P : Int) * (Q : Int) := by
      rw [Int.sub_mul, Int.add_mul, Int.one_mul, Int.mul_assoc]
    have e2 : 2 * ((i : Int) * (Q : Int) + (s : Int))
        = 2 * ((i : Int) * (Q : Int)) + 2 * (s : Int) := by rw [Int.mul_add]
    have e3 : 4 * (i : Int) * (Q : Int) = 4 * ((i : Int) * (Q : Int)) := by
      rw [Int.mul_assoc]
    have e4 : 2 * (P : Int) * (Q : Int) = 2 * ((P : Int) * (Q : Int)) := by
      rw [Int.mul_assoc]
    rw [e1, e2, e3, e4]
    generalize (i : Int) * (Q : Int) = X
    generalize (P : Int) * (Q : Int) = Y
    omega
  -- Now factor v²−u² = (v−u)(v+u) and substitute the two factors.
  generalize hu : (2 * (i : Int) + 1 - (P : Int)) * (Q : Int) = u at hfac1 hfac2 ⊢
  generalize hv : 2 * ((i : Int) * (Q : Int) + (s : Int)) + 1 - (P : Int) * (Q : Int) = v
    at hfac1 hfac2 ⊢
  -- goal: (PQ)²·... − u·u − ((PQ)²·... − v·v) = gapF1·gapF2
  generalize hW : ((P : Int) * (Q : Int)) * ((P : Int) * (Q : Int)) = W
  -- W − u·u − (W − v·v) = v·v − u·u = (v−u)·(v+u)
  have hlin : W - u * u - (W - v * v) = v * v - u * u := by
    generalize u * u = uu; generalize v * v = vv; omega
  rw [hlin, int_sq_diff_factor v u, hfac1, hfac2]


/-- `|2s+1−Q| ≤ Q` for `s < Q`: both `2s+1−Q ≤ Q` and `−(2s+1−Q) ≤ Q`. -/
theorem gapF1_abs_le (Q s : Nat) (hs : s < Q) :
    gapF1 Q s ≤ (Q : Int) ∧ -(gapF1 Q s) ≤ (Q : Int) := by
  unfold gapF1
  have hs' : (s : Int) < (Q : Int) := by exact_mod_cast hs
  have hs0 : (0 : Int) ≤ (s : Int) := Int.natCast_nonneg s
  constructor <;> omega

/-- `|4iQ+2s+1+Q−2PQ| ≤ 2PQ` for `i < P`, `s < Q`. -/
theorem gapF2_abs_le (P Q i s : Nat) (hi : i < P) (hs : s < Q) :
    gapF2 P Q i s ≤ 2 * (P : Int) * (Q : Int)
      ∧ -(gapF2 P Q i s) ≤ 2 * (P : Int) * (Q : Int) := by
  unfold gapF2
  have hi' : (i : Int) < (P : Int) := by exact_mod_cast hi
  have hs' : (s : Int) < (Q : Int) := by exact_mod_cast hs
  have hi0 : (0 : Int) ≤ (i : Int) := Int.natCast_nonneg i
  have hs0 : (0 : Int) ≤ (s : Int) := Int.natCast_nonneg s
  have hQ0 : (0 : Int) ≤ (Q : Int) := Int.natCast_nonneg Q
  -- Key product fact: (i+1)·Q ≤ P·Q, i.e. i·Q ≤ P·Q − Q  (manual product mono).
  have hiQ : (i : Int) * (Q : Int) ≤ (P : Int) * (Q : Int) - (Q : Int) := by
    have hip1 : (i : Int) + 1 ≤ (P : Int) := by omega
    have hprod : ((i : Int) + 1) * (Q : Int) ≤ (P : Int) * (Q : Int) :=
      Int.mul_le_mul_of_nonneg_right hip1 hQ0
    have hexp : ((i : Int) + 1) * (Q : Int) = (i : Int) * (Q : Int) + (Q : Int) := by
      rw [Int.add_mul, Int.one_mul]
    rw [hexp] at hprod
    omega
  -- 0 ≤ i·Q.
  have hiQ0 : (0 : Int) ≤ (i : Int) * (Q : Int) := Int.mul_nonneg hi0 hQ0
  -- normalise the nonlinear monomials into atoms iQ, PQ.
  have e3 : 4 * (i : Int) * (Q : Int) = 4 * ((i : Int) * (Q : Int)) := by rw [Int.mul_assoc]
  have e4 : 2 * (P : Int) * (Q : Int) = 2 * ((P : Int) * (Q : Int)) := by rw [Int.mul_assoc]
  rw [e3, e4]
  -- With X = i·Q, Y = P·Q as omega atoms linked by hiQ, the rest is linear.
  generalize hX : (i : Int) * (Q : Int) = X at hiQ hiQ0 ⊢
  generalize hY : (P : Int) * (Q : Int) = Y at hiQ ⊢
  constructor <;> omega

/-- **Int product bound from two-sided factor bounds.**  If `a ≤ A`, `−a ≤ A`,
`b ≤ B`, `−b ≤ B` with `0 ≤ A`, `0 ≤ B`, then `a·b ≤ A·B`.  Manual
product-monotonicity (case split on the sign of `a`). -/
theorem int_prod_le_of_abs_le {a b A B : Int}
    (haU : a ≤ A) (haL : -a ≤ A) (hbU : b ≤ B) (hbL : -b ≤ B)
    (hA : 0 ≤ A) (hB : 0 ≤ B) : a * b ≤ A * B := by
  rcases Int.le_total 0 a with ha | ha
  · rcases Int.le_total 0 b with hb | hb
    · -- a,b ≥ 0 : a·b ≤ A·b ≤ A·B
      have h1 : a * b ≤ A * b := Int.mul_le_mul_of_nonneg_right haU hb
      have h2 : A * b ≤ A * B := Int.mul_le_mul_of_nonneg_left hbU hA
      exact Int.le_trans h1 h2
    · -- a ≥ 0, b ≤ 0 : a·b ≤ 0 ≤ A·B
      have hab : a * b ≤ 0 := Int.mul_nonpos_of_nonneg_of_nonpos ha hb
      exact Int.le_trans hab (Int.mul_nonneg hA hB)
  · rcases Int.le_total 0 b with hb | hb
    · -- a ≤ 0, b ≥ 0 : a·b ≤ 0 ≤ A·B
      have hab : a * b ≤ 0 := Int.mul_nonpos_of_nonpos_of_nonneg ha hb
      exact Int.le_trans hab (Int.mul_nonneg hA hB)
    · -- a ≤ 0, b ≤ 0 : a·b = (−a)·(−b) ≤ A·B
      have hna : 0 ≤ -a := by omega
      have hnb : 0 ≤ -b := by omega
      have h1 : (-a) * (-b) ≤ A * (-b) := Int.mul_le_mul_of_nonneg_right haL hnb
      have h2 : A * (-b) ≤ A * B := Int.mul_le_mul_of_nonneg_left hbL hA
      have h3 : (-a) * (-b) = a * b := by rw [Int.neg_mul_neg]
      rw [h3] at h1
      exact Int.le_trans h1 h2

/-- The denominator cast `((P·Q)·(P·Q) : Nat) → Int = (PQ)·(PQ)`. -/
private theorem dPQ_cast (P Q : Nat) :
    (((P * Q) * (P * Q) : Nat) : Int)
      = ((P : Int) * (Q : Int)) * ((P : Int) * (Q : Int)) := by
  push_cast; rfl

/-- **PIECE 1 (node-gap, the `D`-form).**  `|D| ≤ 2PQ²`, i.e.
`omsNum P i · Q² − omsNum (P·Q) (iQ+s)` is sandwiched in `[−2PQ², 2PQ²]`.
Manual `Int` product-monotonicity: `D = gapF1·gapF2`, `|gapF1| ≤ Q`,
`|gapF2| ≤ 2PQ`, multiply (`Int.mul_le_mul` of nonneg absolute values). -/
theorem omsNum_gap_abs_le (P Q i s : Nat) (hi : i < P) (hs : s < Q) :
    omsNum P i * ((Q : Int) * (Q : Int)) - omsNum (P * Q) (i * Q + s)
        ≤ 2 * (P : Int) * ((Q : Int) * (Q : Int))
      ∧ -(omsNum P i * ((Q : Int) * (Q : Int)) - omsNum (P * Q) (i * Q + s))
        ≤ 2 * (P : Int) * ((Q : Int) * (Q : Int)) := by
  rw [omsNum_gap_factor P Q i s]
  obtain ⟨h1u, h1l⟩ := gapF1_abs_le Q s hs
  obtain ⟨h2u, h2l⟩ := gapF2_abs_le P Q i s hi hs
  have hQ0 : (0 : Int) ≤ (Q : Int) := Int.natCast_nonneg Q
  have hPQ0 : (0 : Int) ≤ 2 * (P : Int) * (Q : Int) := by
    have hP0 : (0 : Int) ≤ (P : Int) := Int.natCast_nonneg P
    have h2P : (0 : Int) ≤ 2 * (P : Int) := by omega
    exact Int.mul_nonneg h2P hQ0
  -- The target bound 2PQ² = Q · (2PQ)  (pure mul comm/assoc, no `ring`).
  have htgt : 2 * (P : Int) * ((Q : Int) * (Q : Int))
      = (Q : Int) * (2 * (P : Int) * (Q : Int)) := by
    rw [← Int.mul_assoc (2 * (P : Int)) (Q : Int) (Q : Int),
        Int.mul_comm (2 * (P : Int) * (Q : Int)) (Q : Int)]
  rw [htgt]
  refine ⟨?_, ?_⟩
  · -- gapF1·gapF2 ≤ Q·(2PQ)
    exact int_prod_le_of_abs_le h1u h1l h2u h2l hQ0 hPQ0
  · -- -(gapF1·gapF2) ≤ Q·(2PQ)
    have hneg : -(gapF1 Q s * gapF2 P Q i s) = (-(gapF1 Q s)) * gapF2 P Q i s := by
      rw [Int.neg_mul]
    rw [hneg]
    exact int_prod_le_of_abs_le h1l (by rw [Int.neg_neg]; exact h1u) h2u h2l hQ0 hPQ0

/-! ### Lifting the `D`-bound to the rational `2/P` node-gap (both directions)

`oneMinusSqNode P i = A/(P²)`, `oneMinusSqNode (P·Q) j = B/(P²Q²)`,
`2/P = mkPos 2 P`.  Cross-multiplying `a ≤ b + 2/P` reduces (dividing the common
factor `P³ > 0`) to the proved `D`-bound `A·Q² − B ≤ 2PQ²`; symmetrically for the
reverse.  The product juggling is closed by `ac_rfl` (AC product normaliser). -/

private theorem dcast_PPQQ (P Q : Nat) :
    ((P * Q * (P * Q) : Nat) : Int)
      = (P : Int) * (Q : Int) * ((P : Int) * (Q : Int)) := by push_cast; rfl

private theorem dcast_PP (P : Nat) :
    ((P * P : Nat) : Int) = (P : Int) * (P : Int) := by push_cast; rfl

/-- The Int cross-multiplication core of the forward gap bound. -/
private theorem gap_cross_fwd (A B p q : Int) (hp : 1 ≤ p)
    (hD : A * (q * q) - B ≤ 2 * p * (q * q)) :
    A * ((p * q * (p * q)) * p) ≤ (B * p + 2 * (p * q * (p * q))) * (p * p) := by
  have h1 : A * (q * q) ≤ B + 2 * p * (q * q) := by omega
  have hppp : (0 : Int) ≤ p * p * p := by
    have h0 : (0 : Int) ≤ p := by omega
    exact Int.mul_nonneg (Int.mul_nonneg h0 h0) h0
  have hmul : A * (q * q) * (p * p * p) ≤ (B + 2 * p * (q * q)) * (p * p * p) :=
    Int.mul_le_mul_of_nonneg_right h1 hppp
  have heqL : A * ((p * q * (p * q)) * p) = A * (q * q) * (p * p * p) := by ac_rfl
  have heqR : (B * p + 2 * (p * q * (p * q))) * (p * p)
      = (B + 2 * p * (q * q)) * (p * p * p) := by
    rw [Int.add_mul, Int.add_mul]
    have e1 : B * p * (p * p) = B * (p * p * p) := by ac_rfl
    have e2 : 2 * (p * q * (p * q)) * (p * p) = 2 * p * (q * q) * (p * p * p) := by ac_rfl
    rw [e1, e2]
  rw [heqL, heqR]; exact hmul

/-- The Int cross-multiplication core of the backward gap bound. -/
private theorem gap_cross_bwd (A B p q : Int) (hp : 1 ≤ p)
    (hD : B - A * (q * q) ≤ 2 * p * (q * q)) :
    B * ((p * p) * p) ≤ (A * p + 2 * (p * p)) * (p * q * (p * q)) := by
  have h1 : B ≤ A * (q * q) + 2 * p * (q * q) := by omega
  have hppp : (0 : Int) ≤ p * p * p := by
    have h0 : (0 : Int) ≤ p := by omega
    exact Int.mul_nonneg (Int.mul_nonneg h0 h0) h0
  have hmul : B * (p * p * p) ≤ (A * (q * q) + 2 * p * (q * q)) * (p * p * p) :=
    Int.mul_le_mul_of_nonneg_right h1 hppp
  have heqL : B * ((p * p) * p) = B * (p * p * p) := by ac_rfl
  have heqR : (A * p + 2 * (p * p)) * (p * q * (p * q))
      = (A * (q * q) + 2 * p * (q * q)) * (p * p * p) := by
    rw [Int.add_mul, Int.add_mul]
    have e1 : A * p * (p * q * (p * q)) = A * (q * q) * (p * p * p) := by ac_rfl
    have e2 : 2 * (p * p) * (p * q * (p * q)) = 2 * p * (q * q) * (p * p * p) := by ac_rfl
    rw [e1, e2]
  rw [heqL, heqR]; exact hmul

/-- **Forward node-gap (rational).**  `oneMinusSqNode P i ≤ oneMinusSqNode (P·Q) j + 2/P`
for the refined node `j = i·Q + s` (`s < Q`). -/
theorem radicandGap_fwd (P Q i s : Nat) (hP : 0 < P) (hi : i < P) (hs : s < Q)
    (hPQ : 0 < P * Q) (hj : i * Q + s < P * Q) :
    oneMinusSqNode P i hP hi
      ≤ oneMinusSqNode (P * Q) (i * Q + s) hPQ hj + Q'.mkPos 2 P hP := by
  show (oneMinusSqNode P i hP hi).num
        * ((oneMinusSqNode (P * Q) (i * Q + s) hPQ hj + Q'.mkPos 2 P hP).den : Int)
      ≤ (oneMinusSqNode (P * Q) (i * Q + s) hPQ hj + Q'.mkPos 2 P hP).num
        * ((oneMinusSqNode P i hP hi).den : Int)
  rw [show ((oneMinusSqNode (P * Q) (i * Q + s) hPQ hj + Q'.mkPos 2 P hP).den : Int)
        = ((oneMinusSqNode (P * Q) (i * Q + s) hPQ hj).den : Int) * ((Q'.mkPos 2 P hP).den : Int)
      from Q'.add_den_cast _ _,
    show (oneMinusSqNode (P * Q) (i * Q + s) hPQ hj + Q'.mkPos 2 P hP).num
        = (oneMinusSqNode (P * Q) (i * Q + s) hPQ hj).num * ((Q'.mkPos 2 P hP).den : Int)
          + (Q'.mkPos 2 P hP).num * ((oneMinusSqNode (P * Q) (i * Q + s) hPQ hj).den : Int)
      from rfl,
    show (oneMinusSqNode P i hP hi).num = omsNum P i from Q'.mkPos_num _ _ _,
    show (oneMinusSqNode (P * Q) (i * Q + s) hPQ hj).num = omsNum (P * Q) (i * Q + s)
      from Q'.mkPos_num _ _ _,
    show (oneMinusSqNode (P * Q) (i * Q + s) hPQ hj).den = (P * Q) * (P * Q)
      from Q'.mkPos_den _ _ _,
    show (Q'.mkPos 2 P hP).den = P from Q'.mkPos_den _ _ _,
    show (Q'.mkPos 2 P hP).num = (2 : Int) from Q'.mkPos_num _ _ _,
    show (oneMinusSqNode P i hP hi).den = P * P from Q'.mkPos_den _ _ _,
    dcast_PPQQ P Q, dcast_PP P]
  -- Int goal: omsNum P i * (P²Q²·P) ≤ (omsNum (PQ) j · P + 2·P²Q²)·P²
  have hD := (omsNum_gap_abs_le P Q i s hi hs).1
  have hp1 : (1 : Int) ≤ (P : Int) := by exact_mod_cast hP
  exact gap_cross_fwd (omsNum P i) (omsNum (P * Q) (i * Q + s)) (P : Int) (Q : Int) hp1 hD

/-- **Backward node-gap (rational).**  `oneMinusSqNode (P·Q) j ≤ oneMinusSqNode P i + 2/P`. -/
theorem radicandGap_bwd (P Q i s : Nat) (hP : 0 < P) (hi : i < P) (hs : s < Q)
    (hPQ : 0 < P * Q) (hj : i * Q + s < P * Q) :
    oneMinusSqNode (P * Q) (i * Q + s) hPQ hj
      ≤ oneMinusSqNode P i hP hi + Q'.mkPos 2 P hP := by
  show (oneMinusSqNode (P * Q) (i * Q + s) hPQ hj).num
        * ((oneMinusSqNode P i hP hi + Q'.mkPos 2 P hP).den : Int)
      ≤ (oneMinusSqNode P i hP hi + Q'.mkPos 2 P hP).num
        * ((oneMinusSqNode (P * Q) (i * Q + s) hPQ hj).den : Int)
  rw [show ((oneMinusSqNode P i hP hi + Q'.mkPos 2 P hP).den : Int)
        = ((oneMinusSqNode P i hP hi).den : Int) * ((Q'.mkPos 2 P hP).den : Int)
      from Q'.add_den_cast _ _,
    show (oneMinusSqNode P i hP hi + Q'.mkPos 2 P hP).num
        = (oneMinusSqNode P i hP hi).num * ((Q'.mkPos 2 P hP).den : Int)
          + (Q'.mkPos 2 P hP).num * ((oneMinusSqNode P i hP hi).den : Int)
      from rfl,
    show (oneMinusSqNode P i hP hi).num = omsNum P i from Q'.mkPos_num _ _ _,
    show (oneMinusSqNode (P * Q) (i * Q + s) hPQ hj).num = omsNum (P * Q) (i * Q + s)
      from Q'.mkPos_num _ _ _,
    show (oneMinusSqNode (P * Q) (i * Q + s) hPQ hj).den = (P * Q) * (P * Q)
      from Q'.mkPos_den _ _ _,
    show (Q'.mkPos 2 P hP).den = P from Q'.mkPos_den _ _ _,
    show (Q'.mkPos 2 P hP).num = (2 : Int) from Q'.mkPos_num _ _ _,
    show (oneMinusSqNode P i hP hi).den = P * P from Q'.mkPos_den _ _ _,
    dcast_PPQQ P Q, dcast_PP P]
  have hD := (omsNum_gap_abs_le P Q i s hi hs).2
  -- (omsNum_gap_abs_le).2 : -(A·Q² − B) ≤ 2PQ², i.e. B − A·Q² ≤ 2PQ²
  have hD' : omsNum (P * Q) (i * Q + s) - omsNum P i * ((Q : Int) * (Q : Int))
      ≤ 2 * (P : Int) * ((Q : Int) * (Q : Int)) := by
    have := hD; omega
  have hp1 : (1 : Int) ≤ (P : Int) := by exact_mod_cast hP
  exact gap_cross_bwd (omsNum P i) (omsNum (P * Q) (i * Q + s)) (P : Int) (Q : Int) hp1 hD'

/-! ### The `huvc` forms for `cellRefine_holder`

`cellRefine_holder` consumes `oneMinusSqNode … ≤ oneMinusSqNode … + c·c` for a
rational tolerance `c > 0`.  Given any `c` with `2/P ≤ c·c`, transitivity through
the proved `2/P` node-gap supplies both `huvc` forms (forward and backward). -/

/-- **Forward `huvc`.**  For any `c` with `2/P ≤ c·c`:
`oneMinusSqNode P i ≤ oneMinusSqNode (P·Q) j + c·c`. -/
theorem huvc_fwd (P Q i s : Nat) (hP : 0 < P) (hi : i < P) (hs : s < Q)
    (hPQ : 0 < P * Q) (hj : i * Q + s < P * Q) (c : Q') (hc2 : Q'.mkPos 2 P hP ≤ c * c) :
    oneMinusSqNode P i hP hi ≤ oneMinusSqNode (P * Q) (i * Q + s) hPQ hj + c * c :=
  Q'.le_trans' _ _ _ (radicandGap_fwd P Q i s hP hi hs hPQ hj)
    (Q'.add_le_add_left _ _ _ hc2)

/-- **Backward `huvc`.**  For any `c` with `2/P ≤ c·c`:
`oneMinusSqNode (P·Q) j ≤ oneMinusSqNode P i + c·c`. -/
theorem huvc_bwd (P Q i s : Nat) (hP : 0 < P) (hi : i < P) (hs : s < Q)
    (hPQ : 0 < P * Q) (hj : i * Q + s < P * Q) (c : Q') (hc2 : Q'.mkPos 2 P hP ≤ c * c) :
    oneMinusSqNode (P * Q) (i * Q + s) hPQ hj ≤ oneMinusSqNode P i hP hi + c * c :=
  Q'.le_trans' _ _ _ (radicandGap_bwd P Q i s hP hi hs hPQ hj)
    (Q'.add_le_add_left _ _ _ hc2)

/-! ## PIECE 2 — cell-sum infrastructure: block reindexing + weight telescoping

To regroup the `(P·Q)`-mesh Riemann sum by cells `j = i·Q + s`, we need the
`finSum` block-reindexing identity `Σ_{j<P·Q} f j = Σ_{i<P} Σ_{s<Q} f (i·Q+s)`,
proved here from a tail-block split, plus the Lebesgue-weight telescoping
`lebW P = Q · lebW (P·Q)` (`2/P = Q·(2/(P·Q))`).  Both are genuine, reusable
`Q'`-level content; they assemble the per-cell `cellRefine_holder` estimates into
the value-level refinement bound. -/

/-- **Tail-block split.**  `finSum f (a+t) ≃ finSum f a + Σ_{s<t} f (a+s)`. -/
theorem finSum_add_block (f : RationalTail.QSeq) (a : Nat) :
    ∀ t, (RationalTail.finSum f (a + t)).eqv
        (RationalTail.finSum f a + RationalTail.finSum (fun s => f (a + s)) t)
  | 0 => by
      rw [Nat.add_zero]
      show (RationalTail.finSum f a).eqv (RationalTail.finSum f a + 0)
      rw [Q'.add_zero']; exact Q'.eqv_refl _
  | t + 1 => by
      have hnat : a + (t + 1) = (a + t) + 1 := by omega
      rw [hnat, RationalTail.finSum_succ f (a + t),
        RationalTail.finSum_succ (fun s => f (a + s)) t]
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ (f (a + t)) (finSum_add_block f a t)) ?_
      exact Q'.add_assoc_eqv (RationalTail.finSum f a)
        (RationalTail.finSum (fun s => f (a + s)) t) (f (a + t))

/-- **Block reindexing.**  `Σ_{j<P·Q} f j ≃ Σ_{i<P} Σ_{s<Q} f (i·Q+s)`. -/
theorem finSum_block (f : RationalTail.QSeq) (Q : Nat) :
    ∀ P, (RationalTail.finSum f (P * Q)).eqv
        (RationalTail.finSum
          (fun i => RationalTail.finSum (fun s => f (i * Q + s)) Q) P)
  | 0 => by rw [Nat.zero_mul]; exact Q'.eqv_refl 0
  | P + 1 => by
      have hnat : (P + 1) * Q = P * Q + Q := by rw [Nat.succ_mul]
      rw [hnat, RationalTail.finSum_succ
        (fun i => RationalTail.finSum (fun s => f (i * Q + s)) Q) P]
      refine Q'.eqv_trans _ _ _ (finSum_add_block f (P * Q) Q) ?_
      exact Q'.add_eqv_congr_right _ _ (RationalTail.finSum (fun s => f (P * Q + s)) Q)
        (finSum_block f Q P)

/-- **Lebesgue-weight telescoping.**  `lebW P ≃ (Q as rational) · lebW (P·Q)`,
i.e. `2/P ≃ Q·(2/(P·Q))` (cross-multiplied: `2·(P·Q) = (Q·2)·P`). -/
theorem lebW_telescope (P Q : Nat) (hP : 0 < P) (hPQ : 0 < P * Q) :
    (lebW P hP).eqv (Q'.ofNat Q * lebW (P * Q) hPQ) := by
  show (lebW P hP).num * ((Q'.ofNat Q * lebW (P * Q) hPQ).den : Int)
      = (Q'.ofNat Q * lebW (P * Q) hPQ).num * ((lebW P hP).den : Int)
  rw [show (lebW P hP).num = (2 : Int) from Q'.mkPos_num _ _ _,
    show (lebW P hP).den = P from Q'.mkPos_den _ _ _,
    show (Q'.ofNat Q * lebW (P * Q) hPQ).num
        = (Q'.ofNat Q).num * (lebW (P * Q) hPQ).num from rfl,
    show ((Q'.ofNat Q * lebW (P * Q) hPQ).den : Int)
        = ((Q'.ofNat Q).den : Int) * ((lebW (P * Q) hPQ).den : Int) from Q'.mul_den_cast _ _,
    show (lebW (P * Q) hPQ).num = (2 : Int) from Q'.mkPos_num _ _ _,
    show (lebW (P * Q) hPQ).den = P * Q from Q'.mkPos_den _ _ _]
  have hQnum : (Q'.ofNat Q).num = (Q : Int) := rfl
  have hQden : ((Q'.ofNat Q).den : Int) = 1 := rfl
  rw [hQnum, hQden,
    show (((P * Q : Nat)) : Int) = (P : Int) * (Q : Int) from by push_cast; rfl]
  -- goal: 2 * (1 * (↑P*↑Q)) = ↑Q * 2 * ↑P
  rw [Int.one_mul]
  -- 2*(p*q) = q*2*p   (pure mul comm/assoc)
  rw [Int.mul_comm (Q : Int) 2, Int.mul_assoc, Int.mul_comm (P : Int) (Q : Int)]

/-! ## PIECE 3 — assembly: reducing `ValueInterRes` to the canonical residual

The target `ValueInterRes` wants the value-gap shape
`(seqSemi m).approx k + (−(seqSemi n).approx k) ≤ ε`.  The canonical outer
residual `SemicircleConverge.UniformRiemannBound` provides the index-UNIFORM
bound `(seqSemi m).approx k ≤ (seqSemi n).approx k + ε` (for ALL `k`) with an
antitone outer modulus `M` — exactly the cell-matching Riemann estimate that
PIECE 1 (`huvc_fwd`/`huvc_bwd`) and PIECE 2 (`finSum_block` / `lebW_telescope`)
feed.  We prove the clean reduction `UniformRiemannBound ⟹ ValueInterRes` here:
the inequality shape is converted by `unflip_le`, and `valK := 0` (the bound is
uniform in `k`, so no approximation modulus is needed).

This is the precise reduction making the semicircle limit unconditional GIVEN the
single canonical residual `UniformRiemannBound`; the residual's per-cell input is
discharged by PIECE 1, its regrouping by PIECE 2. -/

/-- **Unflip.**  `a ≤ b + ε ⟹ a + (−b) ≤ ε` (the converse of
`SemicircleInterRes.flip_le`).  Add `−b` on the right and collapse `(b+ε)+(−b) ≃ ε`. -/
theorem unflip_le (a b ε : Q') (h : a ≤ b + ε) : a + (-b) ≤ ε := by
  have hadd : a + (-b) ≤ (b + ε) + (-b) := Q'.add_le_add_right _ _ (-b) h
  refine Q'.le_trans' _ _ _ hadd ?_
  -- (b+ε)+(−b) ≃ ε
  have e1 : ((b + ε) + (-b)).eqv ((ε + b) + (-b)) :=
    Q'.add_eqv_congr_right _ _ (-b) (Q'.add_comm_eqv b ε)
  have e2 : ((ε + b) + (-b)).eqv (ε + (b + (-b))) := Q'.add_assoc_eqv ε b (-b)
  have e3 : (b + (-b)).eqv 0 :=
    Q'.eqv_trans _ _ _ (Q'.add_comm_eqv b (-b)) (Q'.neg_add_self_eqv b)
  have e4 : (ε + (b + (-b))).eqv (ε + 0) := Q'.add_eqv_congr_left ε _ _ e3
  have e5 : (ε + (0 : Q')).eqv ε := QPoly.q_add_zero_eqv ε
  exact Q'.le_of_eqv
    (Q'.eqv_trans _ _ _ e1 (Q'.eqv_trans _ _ _ e2 (Q'.eqv_trans _ _ _ e4 e5)))

/-- **PIECE 3 reduction.**  `SemicircleConverge.UniformRiemannBound ⟹ ValueInterRes`.
Same antitone outer modulus `M`; the approximation modulus `valK := 0` (the
Riemann bound is uniform in `k`); the inequality shape is converted by
`unflip_le`, using `(add x (neg y)).approx k = x.approx k + (−(y.approx k))`. -/
def valueInterRes_of_uniformRiemann
    (u : SemicircleConverge.UniformRiemannBound) :
    SemicircleInterRes.ValueInterRes :=
  ⟨u.1, fun _ _ _ => 0, by
    refine ⟨fun ε hε m n hm hn k _ => ?_, u.2.2⟩
    obtain ⟨hfwd, hbwd⟩ := u.2.1 ε hε m n hm hn k
    -- (add x (neg y)).approx k = x.approx k + (-(y.approx k))  (definitional)
    refine ⟨?_, ?_⟩
    · show (seqSemi m).approx k + (-(seqSemi n).approx k) ≤ ε
      exact unflip_le _ _ _ hfwd
    · show (seqSemi n).approx k + (-(seqSemi m).approx k) ≤ ε
      exact unflip_le _ _ _ hbwd⟩

/-! ## The semicircle integral, UNCONDITIONAL modulo the canonical residual

With the reduction `valueInterRes_of_uniformRiemann`, the bridge
`SemicircleInterRes.interResBound_of_value`, and the limit backbone, the
semicircle integral and its enclosure are reduced to the SINGLE canonical
residual `SemicircleConverge.UniformRiemannBound` — the same residual the whole
`SemicircleConverge` analysis already names, now fed by PIECE 1 + PIECE 2. -/

/-- **The semicircle integral** `∫_{−1}^1 √(1−x²)`, GIVEN the canonical residual
`u : UniformRiemannBound` (per-cell input discharged by PIECE 1, regrouping by
PIECE 2). -/
def semiIntUncond (u : SemicircleConverge.UniformRiemannBound) : CReal :=
  SemicircleInterRes.semiInt (valueInterRes_of_uniformRiemann u)

/-- **Convergence** of the semicircle Riemann sums to `semiIntUncond`. -/
theorem semiIntUncond_converges (u : SemicircleConverge.UniformRiemannBound) :
    CReal.ConvergesTo seqSemi (semiIntUncond u) :=
  SemicircleInterRes.semiInt_converges (valueInterRes_of_uniformRiemann u)

/-- **`semiIntUncond ≥ 0`.** -/
theorem semiIntUncond_nonneg (u : SemicircleConverge.UniformRiemannBound) :
    ExpPos.geRat (semiIntUncond u) 0 :=
  SemicircleInterRes.semiInt_nonneg (valueInterRes_of_uniformRiemann u)

/-- **`semiIntUncond ≤ 2`.** -/
theorem semiIntUncond_leRat_two (u : SemicircleConverge.UniformRiemannBound) :
    CReal.leRat (semiIntUncond u) (2 : Q') :=
  SemicircleInterRes.semiInt_leRat_two (valueInterRes_of_uniformRiemann u)

end YMGap.Continuum.SemicircleValueRes

/-! ## PROVED vs NAMED-open (honest ledger)

**PROVED (axiom-clean, GENUINE new content).**

  * PIECE 1 — the nonlinear `Int` radicand node-gap arithmetic, fully discharged:
    - `sq_mul_sq` / `int_sq_diff_factor`-route `omsNum_gap_factor` — the node-gap
      numerator factorisation `omsNum P i·Q² − omsNum (PQ)(iQ+s)
      = (2s+1−Q)·(4iQ+2s+1+Q−2PQ)` (pure `Int`, the `iQ`/`PQ` monomials cancel).
    - `gapF1_abs_le` / `gapF2_abs_le` — the two factor bounds `|·| ≤ Q`,
      `|·| ≤ 2PQ` (manual product-monotonicity, `omega` on the linear residue).
    - `int_prod_le_of_abs_le` — `|a·b| ≤ A·B` from two-sided factor bounds.
    - `omsNum_gap_abs_le` — the assembled `|D| ≤ 2PQ²` (the nonlinear node gap,
      beyond `omega`; this is residual (a) named in `SemicircleInterRes`).
    - `gap_cross_fwd` / `gap_cross_bwd` / `radicandGap_fwd` / `radicandGap_bwd` —
      the lift to the rational `2/P` node gap (cross-multiplication, common factor
      `P³`, `ac_rfl` product normaliser).
    - `huvc_fwd` / `huvc_bwd` — the `oneMinusSqNode … ≤ oneMinusSqNode … + c·c`
      forms the per-cell `SemicircleInterRes.cellRefine_holder` consumes, for any
      rational `c` with `2/P ≤ c·c`.

  * PIECE 2 — cell-sum infrastructure:
    - `finSum_add_block` — the tail-block split `Σ_{j<a+t} = Σ_{j<a} + Σ_{s<t}`.
    - `finSum_block` — the block reindexing `Σ_{j<P·Q} = Σ_{i<P} Σ_{s<Q}` at the
      refined node `i·Q+s` (the regrouping the cell-sum needs).
    - `lebW_telescope` — the Lebesgue-weight telescoping `2/P ≃ Q·(2/(P·Q))`.

  * PIECE 3 — the reduction + the reduced limit:
    - `unflip_le` — `a ≤ b + ε ⟹ a + (−b) ≤ ε` (converse of `flip_le`).
    - `valueInterRes_of_uniformRiemann` — **THE REDUCTION**
      `SemicircleConverge.UniformRiemannBound ⟹ SemicircleInterRes.ValueInterRes`:
      same antitone `M`, `valK := 0` (the Riemann bound is uniform in `k`),
      inequality shape converted by `unflip_le`.
    - `semiIntUncond` / `semiIntUncond_converges` / `semiIntUncond_nonneg` /
      `semiIntUncond_leRat_two` — the semicircle limit and its `0 ≤ · ≤ 2`
      enclosure, reduced to the SINGLE canonical residual `UniformRiemannBound`.

**NAMED-open (the single residual).**

  * `SemicircleConverge.UniformRiemannBound` — the index-uniform outer Riemann
    bound with antitone outer modulus.  Its per-cell √-Hölder input is PROVED
    (`SemicircleConverge.nodeWeight_holder` / `SemicircleInterRes.cellRefine_holder`
    fed by PIECE 1's `huvc_fwd`/`huvc_bwd`), and the cell regrouping is PROVED
    here (PIECE 2's `finSum_block` + `lebW_telescope`).  What remains to discharge
    it is (i) the `CReal`/`Q'` cell-sum *assembly* of the per-cell bounds into the
    index-uniform sum estimate, and (ii) the constructive antitone outer modulus
    `M ε ≈ ⌈256/ε²⌉` (which needs a rational-ceiling the substrate does not yet
    expose).  These are the precise remaining obligations; the value-to-target
    bridge, the per-cell node arithmetic, and the cell regrouping are all proved.

So `ValueInterRes` (hence the unconditional semicircle limit) is REDUCED to the
single canonical residual `UniformRiemannBound`; PIECE 1 + PIECE 2 supply its
per-cell input and its regrouping, and PIECE 3 supplies the value-gap reduction.

**Path for the general integrand `U_a·U_b·R`.**  All three pieces are
integrand-agnostic in shape: PIECE 1's node-gap arithmetic, PIECE 2's block
reindexing/weight telescoping, and PIECE 3's `unflip`/uniform-`k` reduction reuse
verbatim once the integrand's per-cell modulus is enlarged by the QPoly Lipschitz
factor.

Axiom-gate: `[propext]` / `[propext, Quot.sound]`.  No `Classical.*`,
no `sorry`/`sorryAx`, no `native_decide`, no new axioms; `decide`/`ac_rfl` only on
closed `Int`/`Q'` goals. -/

#print axioms YMGap.Continuum.SemicircleValueRes.omsNum_gap_factor
#print axioms YMGap.Continuum.SemicircleValueRes.omsNum_gap_abs_le
#print axioms YMGap.Continuum.SemicircleValueRes.radicandGap_fwd
#print axioms YMGap.Continuum.SemicircleValueRes.radicandGap_bwd
#print axioms YMGap.Continuum.SemicircleValueRes.huvc_fwd
#print axioms YMGap.Continuum.SemicircleValueRes.huvc_bwd
#print axioms YMGap.Continuum.SemicircleValueRes.finSum_block
#print axioms YMGap.Continuum.SemicircleValueRes.lebW_telescope
#print axioms YMGap.Continuum.SemicircleValueRes.unflip_le
#print axioms YMGap.Continuum.SemicircleValueRes.valueInterRes_of_uniformRiemann
#print axioms YMGap.Continuum.SemicircleValueRes.semiIntUncond_converges
#print axioms YMGap.Continuum.SemicircleValueRes.semiIntUncond_nonneg
#print axioms YMGap.Continuum.SemicircleValueRes.semiIntUncond_leRat_two
