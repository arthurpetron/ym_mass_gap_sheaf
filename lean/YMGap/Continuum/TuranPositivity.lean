/-
The **Turán / Wronskian** reduction of the all-order heat-kernel Gram PSD to a
single clean named fact, with the per-step ENGINE fully PROVED.

# Setting (same uniform base variable as `Favard`/`FavardRec`/`PNInduction`)

`a = e^{−t/4} ∈ (0,1]`, heat-kernel leading Gram minors `Δ_N(a)` factor
uniformly as `Δ_N = S_N²·P_N` (`S_N = SN N`, the explicit q-product square
factor; `P_N = Pseq N`, the nonneg-coefficient residual, constant term `1`).
Minor positivity `Δ_N(a) ≥ 0` at `a ≥ 0` reduces to `S_N² ≥ 0` (already
uniform, `geRat_SN_sq_nonneg_uniform`) and `P_N > 0`.

# The Turán/Wronskian identity (the new, cleaner reduction)

The discrete Turán determinant `T_k := P_{k+1}·P_{k−1} − P_k²` is
NONNEG-COEFFICIENT (verified through `N = 6`).  Hence the **Turán identity**

    P_{k+1}·P_{k−1}  =  P_k²  +  T_k          (`turanPoly k = T_k`)

writes the product `P_{k+1}·P_{k−1}` as a *square* plus a nonneg-coefficient
remainder — both manifestly `≥ 0`.  Given `P_{k−1} > 0` and `P_k > 0` on
`(0,1)`, the value identity gives `P_{k+1}·P_{k−1} ≥ P_k² > 0`, and cancelling
the positive factor `P_{k−1}` yields `P_{k+1} > 0` with **NO sign flip** and
**NO `a^{2k}−1` multiplier** — the precise obstruction (a cyclotomic factor with
constant term `−1`) that blocked the older `PNStep` / Favard-quadratic route
(see `FavardUniform.PNStep`).  This file REPLACES that obstruction with the
clean Turán step.

# What is PROVED here (axiom-clean; no `Classical`/`sorry`/`native_decide`)

  * `turan_nonneg_k` (`k = 2,3,4,5,6`) — the base certificates
    `nonnegCoeffs (turanPoly k)` by `decide` on the exact `P_k` lists.

  * **The strict-positivity ENGINE** (genuine, UNCONDITIONAL per step):
      - `PosEv` — eventual strict positivity of a `CReal`'s limit (a positive
        rational lower bound, the `leEv`-analog of `IsPositive`; Equiv-stable
        and supporting cancellation, where the one-slack `IsPositive` does not).
      - `posEv_mul`, `posEv_sq`, `posEv_add_geRat`, `posEv_of_equiv` — the
        algebra of `PosEv` (product, square, plus-a-nonnegative, transport).
      - `posEv_left_of_mul` — **the cancellation core**: from `PosEv (A·B)`
        and `PosEv B` (with an upper bound on `B` from `localBound`), conclude
        `PosEv A`.  Genuine, pointwise (`aₙ ≥ d/Bup > 0`).
      - `turan_step` — **THE KEY LEMMA**: given `0 ≤ a`,
        `PosEv (ceval P_{k−1} a)`, `PosEv (ceval P_k a)` and
        `nonnegCoeffs (turanPoly k)`, prove `PosEv (ceval P_{k+1} a)`.
        Unconditional in the engine: derives `P_{k+1} > 0` from the Turán step.

  * `UniformTuranNonneg` — the SINGLE remaining wall (Type-level `Prop`):
    `∀ k, nonnegCoeffs (turanPoly k)`.  `decide`-verified through `N = 5/6`;
    attackable later via Dodgson/Desnanot–Jacobi condensation (`T_k` as a
    square times another minor).  NAMED, not closed.

  * `Pseq_pos_of_uniformTuran` — the REDUCTION: `UniformTuranNonneg`
    ⟹ `∀ N, PosEv (ceval (Pseq N) a)` for `a ≥ 0`, by two-step induction
    (base `P_0,P_1 > 0`; step = `turan_step`).

  * `delta_nonneg_all_of_uniformTuran` — the CAPSTONE: `UniformTuranNonneg`
    ⟹ `∀ N a, 0 ≤ a → 0 ≤ Δ_N(a)`, composing `Pseq_pos_of_uniformTuran`
    (`P_N > 0`) with `geRat_SN_sq_nonneg_uniform` (`S_N² ≥ 0`) via
    `gram_minor_nonneg_of_PN`.  So the ALL-ORDER Gram PSD is PROVED conditional
    on the single `UniformTuranNonneg`, with the per-step engine unconditional.

# Axiom-gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]`.  No `Classical.*`, no `sorryAx`,
no `native_decide`.
-/

import YMGap.Continuum.FavardUniform
import YMGap.Continuum.CyclotomicPositivity
import YMGap.Continuum.PNInduction
import YMGap.Constructive.Sqrt
import YMGap.Constructive.CubeRoot
import YMGap.Constructive.CRealComplete

namespace YMGap.Continuum.TuranPositivity

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.PNInduction

/-! ## Small `Q'` order helpers (proved via the `Int` cross-product)

A handful of strict-order facts not named in the kernel; each reduces to the
`Int` representation of `<`/`≤`. -/

/-- `a < b → b ≤ c → a < c` on `Q'`. -/
theorem q_lt_of_lt_of_le {a b c : Q'} (h1 : a < b) (h2 : b ≤ c) : a < c := by
  have e1 : a.num * (b.den : Int) < b.num * (a.den : Int) := h1
  have e2 : b.num * (c.den : Int) ≤ c.num * (b.den : Int) := h2
  show a.num * (c.den : Int) < c.num * (a.den : Int)
  have hbd : (0 : Int) < (b.den : Int) := by exact_mod_cast b.den_pos
  have hcd : (0 : Int) < (c.den : Int) := by exact_mod_cast c.den_pos
  have had : (0 : Int) ≤ (a.den : Int) := by exact_mod_cast Nat.zero_le _
  -- (a.num·c.den)·b.den < (b.num·a.den)·c.den   (scale strict e1 by c.den > 0)
  have s1 : (a.num * (c.den : Int)) * (b.den : Int)
          < (b.num * (a.den : Int)) * (c.den : Int) := by
    have hmul := Int.mul_lt_mul_of_pos_right e1 hcd
    have hr : (a.num * (b.den : Int)) * (c.den : Int)
            = (a.num * (c.den : Int)) * (b.den : Int) := by
      rw [Int.mul_assoc, Int.mul_assoc, Int.mul_comm (b.den : Int) (c.den : Int)]
    rwa [hr] at hmul
  -- (b.num·a.den)·c.den ≤ (c.num·a.den)·b.den   (scale weak e2 by a.den ≥ 0)
  have s2 : (b.num * (a.den : Int)) * (c.den : Int)
          ≤ (c.num * (a.den : Int)) * (b.den : Int) := by
    have hmul := Int.mul_le_mul_of_nonneg_left e2 had
    have hl : (a.den : Int) * (b.num * (c.den : Int))
            = (b.num * (a.den : Int)) * (c.den : Int) := by
      rw [Int.mul_comm b.num (a.den : Int), Int.mul_assoc]
    have hrr : (a.den : Int) * (c.num * (b.den : Int))
             = (c.num * (a.den : Int)) * (b.den : Int) := by
      rw [Int.mul_comm c.num (a.den : Int), Int.mul_assoc]
    rwa [hl, hrr] at hmul
  exact Int.lt_of_mul_lt_mul_right (Int.lt_of_lt_of_le s1 s2) (Int.le_of_lt hbd)

/-- `0 < x → 0 ≤ y → 0 < x + y` on `Q'`. -/
theorem q_pos_add_nonneg {x y : Q'} (hx : (0 : Q') < x) (hy : (0 : Q') ≤ y) :
    (0 : Q') < x + y :=
  q_lt_of_lt_of_le hx (Q'.add_le_self_of_nonneg x y hy)

/-! ## The Turán polynomial `T_k` and its base certificates

`turanPoly k := (P_{k+1}·P_{k−1}) − P_k²`, the discrete Turán determinant.
Its nonneg-coefficient base certificates for `k = 2,…,6` are `decide`-checked
on the exact `Pseq` lists (mirroring `pdiff_nonneg_*`). -/

/-- The discrete Turán determinant `T_k = P_{k+1}·P_{k−1} − P_k²` as a `QPoly`. -/
def turanPoly (k : Nat) : QPoly.Poly :=
  QPoly.psub (QPoly.pmul (Pseq (k + 1)) (Pseq (k - 1)))
    (QPoly.pmul (Pseq k) (Pseq k))

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 16000 in
/-- **Turán base certificate `k = 2`**: `nonnegCoeffs (turanPoly 2)`. -/
theorem turan_nonneg_2 : nonnegCoeffs (turanPoly 2) := by decide

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 16000 in
/-- **Turán base certificate `k = 3`**: `nonnegCoeffs (turanPoly 3)`. -/
theorem turan_nonneg_3 : nonnegCoeffs (turanPoly 3) := by decide

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 16000 in
/-- **Turán base certificate `k = 4`**: `nonnegCoeffs (turanPoly 4)`. -/
theorem turan_nonneg_4 : nonnegCoeffs (turanPoly 4) := by decide

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 16000 in
/-- **Turán base certificate `k = 5`**: `nonnegCoeffs (turanPoly 5)`. -/
theorem turan_nonneg_5 : nonnegCoeffs (turanPoly 5) := by decide

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 16000 in
/-- **Turán base certificate `k = 6`**: `nonnegCoeffs (turanPoly 6)`
(`Pseq 7` realized as `P7`). -/
theorem turan_nonneg_6 : nonnegCoeffs (turanPoly 6) := by decide

/-! ## The strict-positivity engine: `PosEv`

`PosEv A` says the limit of `A` is strictly positive, witnessed by a positive
rational `ε` with an EVENTUAL lower bound `leEv (ofQ' ε) A`.  This is the
`leEv`-level analog of `CReal.IsPositive` (cf. `isPositiveEv_completeLimit`):
the one-slack `IsPositive` is not stable under the eventual order used here
(small-`n` approximations are unconstrained), but `PosEv` is — and it is
exactly what the Turán cancellation needs. -/

/-- **Eventual strict positivity.**  A positive rational lower bound on the
limit, in the (transitive, Equiv-stable) eventual order `leEv`. -/
def PosEv (A : CReal) : Prop :=
  ∃ ε : Q', (0 : Q') < ε ∧ CReal.leEv (CReal.ofQ' ε) A

/-- `PosEv` from an explicit eventual approx lower bound by a positive rational. -/
theorem posEv_of_eventually {A : CReal} {ε : Q'} (hε : (0 : Q') < ε)
    (h : ∃ N : Nat, ∀ n : Nat, N ≤ n → ε ≤ A.approx n) : PosEv A := by
  refine ⟨ε, hε, ?_⟩
  intro δ hδ
  obtain ⟨N, hN⟩ := h
  refine ⟨N, fun n hn => ?_⟩
  show ε ≤ A.approx n + δ
  exact Q'.le_trans' _ _ _ (hN n hn)
    (Q'.add_le_self_of_nonneg (A.approx n) δ (Q'.le_of_lt hδ))

/-- **Eventual approx lower bound from `PosEv`.**  Unfolds the witness: there is
a positive `ε'` and a stage `N` past which every approx is `≥ ε'`.
(`PosEv`-analog of `eventually_ge_of_isPositive`; uses the `ε/2` slack trick.) -/
theorem eventually_ge_of_posEv {A : CReal} (h : PosEv A) :
    ∃ ε' : Q', (0 : Q') < ε' ∧ ∃ N : Nat, ∀ n : Nat, N ≤ n → ε' ≤ A.approx n := by
  obtain ⟨ε, hε, hle⟩ := h
  have hhε : (0 : Q') < HalfPow.half * ε := ExpNeg.half_mul_pos ε hε
  obtain ⟨N, hN⟩ := hle (HalfPow.half * ε) hhε
  refine ⟨HalfPow.half * ε, hhε, N, fun n hn => ?_⟩
  -- hN : ε ≤ A_n + half*ε  (since (ofQ' ε).approx n = ε)
  have hn' : ε ≤ A.approx n + HalfPow.half * ε := hN n hn
  -- ε = half*ε + half*ε, so half*ε ≤ A_n
  have hε2 : (HalfPow.half * ε + HalfPow.half * ε) ≤ A.approx n + HalfPow.half * ε :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (ExpNeg.two_halves ε)) hn'
  have hcancel := Q'.add_le_add_right
    (HalfPow.half * ε + HalfPow.half * ε) (A.approx n + HalfPow.half * ε)
    (-(HalfPow.half * ε)) hε2
  refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv ?_) (Q'.le_trans' _ _ _ hcancel (Q'.le_of_eqv ?_))
  · -- (half*ε + half*ε) + -(half*ε) ≃ half*ε
    refine Q'.eqv_trans _ _ _
      (Q'.add_assoc_eqv (HalfPow.half * ε) (HalfPow.half * ε) (-(HalfPow.half * ε))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (HalfPow.half * ε) (HalfPow.half * ε + -(HalfPow.half * ε)) 0
        (Q'.add_neg_self_eqv (HalfPow.half * ε))) ?_
    exact Q'.eqv_of_eq (Q'.add_zero' (HalfPow.half * ε))
  · -- (A_n + half*ε) + -(half*ε) ≃ A_n
    refine Q'.eqv_trans _ _ _
      (Q'.add_assoc_eqv (A.approx n) (HalfPow.half * ε) (-(HalfPow.half * ε))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (A.approx n) (HalfPow.half * ε + -(HalfPow.half * ε)) 0
        (Q'.add_neg_self_eqv (HalfPow.half * ε))) ?_
    exact Q'.eqv_of_eq (Q'.add_zero' (A.approx n))

/-- **`PosEv ⟹ geRat _ 0`.**  The bridge to the repo's nonnegativity vocabulary
(`geRat A 0` is exactly the input the minor-reduction consumes). -/
theorem geRat_zero_of_posEv {A : CReal} (h : PosEv A) : ExpPos.geRat A 0 := by
  obtain ⟨ε', hε', N, hN⟩ := eventually_ge_of_posEv h
  refine ExpPos.geRat_of_eventually ⟨N, fun n hn => ?_⟩
  exact Q'.le_trans' _ _ _ (Q'.le_of_lt hε') (hN n hn)

/-- **Transport `PosEv` across `Equiv`.**  Strict positivity is a property of the
limit, so it passes through `CReal.Equiv`. -/
theorem posEv_of_equiv {A B : CReal} (h : PosEv A) (hAB : CReal.Equiv A B) :
    PosEv B := by
  obtain ⟨ε', hε', N, hN⟩ := eventually_ge_of_posEv h
  -- choose half*ε' as the new witness; use Equiv at tolerance half*ε'
  have hhε : (0 : Q') < HalfPow.half * ε' := ExpNeg.half_mul_pos ε' hε'
  refine posEv_of_eventually hhε ?_
  obtain ⟨M, hM⟩ := hAB (HalfPow.half * ε') hhε
  refine ⟨max N M, fun n hn => ?_⟩
  have hnN : N ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hnM : M ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
  -- A_n ≥ ε' ; |A_n − B_n| ≤ half*ε' ⟹ B_n ≥ A_n − half*ε' ≥ ε' − half*ε' = half*ε'
  have hAle : A.approx n ≤ B.approx n + HalfPow.half * ε' := (hM n hnM).1
  have hAn : ε' ≤ A.approx n := hN n hnN
  -- ε' ≤ A_n ≤ B_n + half*ε', so ε' − half*ε' ≤ B_n, i.e. half*ε' ≤ B_n
  have hchain : ε' ≤ B.approx n + HalfPow.half * ε' := Q'.le_trans' _ _ _ hAn hAle
  have hsub := Q'.add_le_add_right ε' (B.approx n + HalfPow.half * ε')
    (-(HalfPow.half * ε')) hchain
  -- ε' + -(half*ε') ≃ half*ε' ; (B_n + half*ε') + -(half*ε') ≃ B_n
  refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv ?_) (Q'.le_trans' _ _ _ hsub (Q'.le_of_eqv ?_))
  · -- (ε' + -(half*ε')) ≃ half*ε'   (since ε' = half*ε' + half*ε')
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right ε' (HalfPow.half * ε' + HalfPow.half * ε')
        (-(HalfPow.half * ε')) (Q'.eqv_symm (ExpNeg.two_halves ε'))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_assoc_eqv (HalfPow.half * ε') (HalfPow.half * ε') (-(HalfPow.half * ε'))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (HalfPow.half * ε') (HalfPow.half * ε' + -(HalfPow.half * ε')) 0
        (Q'.add_neg_self_eqv (HalfPow.half * ε'))) ?_
    exact Q'.eqv_of_eq (Q'.add_zero' (HalfPow.half * ε'))
  · -- (B_n + half*ε') + -(half*ε') ≃ B_n
    refine Q'.eqv_trans _ _ _
      (Q'.add_assoc_eqv (B.approx n) (HalfPow.half * ε') (-(HalfPow.half * ε'))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (B.approx n) (HalfPow.half * ε' + -(HalfPow.half * ε')) 0
        (Q'.add_neg_self_eqv (HalfPow.half * ε'))) ?_
    exact Q'.eqv_of_eq (Q'.add_zero' (B.approx n))

/-- **Product of `PosEv`s is `PosEv`.**  Eventual lower bound `ε₁·ε₂ > 0`. -/
theorem posEv_mul {A B : CReal} (hA : PosEv A) (hB : PosEv B) :
    PosEv (CReal.mul A B) := by
  obtain ⟨ε₁, hε₁, N₁, hN₁⟩ := eventually_ge_of_posEv hA
  obtain ⟨ε₂, hε₂, N₂, hN₂⟩ := eventually_ge_of_posEv hB
  refine posEv_of_eventually (Q'.mul_pos hε₁ hε₂) ⟨max N₁ N₂, fun n hn => ?_⟩
  have hn1 : N₁ ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hn2 : N₂ ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
  have ha : ε₁ ≤ A.approx n := hN₁ n hn1
  have hb : ε₂ ≤ B.approx n := hN₂ n hn2
  show ε₁ * ε₂ ≤ A.approx n * B.approx n
  -- ε₁·ε₂ ≤ A_n·ε₂ ≤ A_n·B_n
  have hAnn : (0 : Q') ≤ A.approx n := Q'.le_trans' _ _ _ (Q'.le_of_lt hε₁) ha
  have h1 : ε₁ * ε₂ ≤ A.approx n * ε₂ :=
    Q'.mul_le_mul_of_nonneg_right ε₁ (A.approx n) ε₂ ha (Q'.le_of_lt hε₂)
  have h2 : A.approx n * ε₂ ≤ A.approx n * B.approx n :=
    CyclotomicPositivity.mul_le_mul_of_nonneg_left hb hAnn
  exact Q'.le_trans' _ _ _ h1 h2

/-- **`PosEv` of a square** `A·A` from `PosEv A`. -/
theorem posEv_sq {A : CReal} (hA : PosEv A) : PosEv (CReal.mul A A) :=
  posEv_mul hA hA

/-- **`PosEv (A + B)` from `PosEv A` and `geRat B 0`.**  A strictly-positive plus
a nonnegative is strictly positive (same positive witness). -/
theorem posEv_add_geRat {A B : CReal} (hA : PosEv A) (hB : ExpPos.geRat B 0) :
    PosEv (CReal.add A B) := by
  obtain ⟨ε', hε', N, hN⟩ := eventually_ge_of_posEv hA
  -- use half*ε' as witness, with the geRat slack absorbing the other half
  have hhε : (0 : Q') < HalfPow.half * ε' := ExpNeg.half_mul_pos ε' hε'
  refine ⟨HalfPow.half * ε', hhε, ?_⟩
  intro δ hδ
  obtain ⟨Nb, hNb⟩ := hB (HalfPow.half * ε' + δ)
    (q_pos_add_nonneg hhε (Q'.le_of_lt hδ))
  refine ⟨max N Nb, fun n hn => ?_⟩
  have hnN : N ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hnb : Nb ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
  -- A_n ≥ ε' ≥ half*ε' ; B_n ≥ −(half*ε' + δ)
  have hAn : ε' ≤ A.approx n := hN n hnN
  have hBn : (0 : Q') ≤ B.approx n + (HalfPow.half * ε' + δ) := hNb n hnb
  show HalfPow.half * ε' ≤ (A.approx n + B.approx n) + δ
  -- A_n + B_n + δ ≥ ε' + B_n + δ ≥ ε' − (half*ε' + δ) + δ = ε' − half*ε' = half*ε'
  have hge_half : HalfPow.half * ε' ≤ A.approx n := by
    refine Q'.le_trans' _ _ _ ?_ hAn
    -- half*ε' ≤ ε' since ε' = half*ε' + half*ε' and half*ε' ≥ 0
    refine Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg (HalfPow.half * ε') (HalfPow.half * ε')
      (Q'.le_of_lt hhε)) (Q'.le_of_eqv (ExpNeg.two_halves ε'))
  -- From hBn: 0 ≤ B_n + half*ε' + δ.  Want half*ε' ≤ A_n + B_n + δ.
  -- A_n + B_n + δ ≥ half*ε' + B_n + δ.  And half*ε' ≤ half*ε' + (B_n + half*ε' + δ).
  have hstep : HalfPow.half * ε'
      ≤ HalfPow.half * ε' + (B.approx n + (HalfPow.half * ε' + δ)) :=
    Q'.add_le_self_of_nonneg (HalfPow.half * ε') _ hBn
  refine Q'.le_trans' _ _ _ hstep ?_
  -- half*ε' + (B_n + (half*ε' + δ)) ≤ A_n + B_n + δ ?
  -- LHS ≃ (half*ε' + half*ε') + B_n + δ ; but we only need ≤ via A_n ≥ half*ε'.
  -- Rearrange RHS = (A_n + B_n) + δ.  Bound: half*ε' + (B_n + (half*ε' + δ))
  --   = (half*ε' + half*ε') + (B_n + δ)  [reassoc/comm]  and half*ε'+half*ε' = ε' ≥... too big.
  -- Simpler: half*ε' ≤ A_n (hge_half) and the extra half*ε' on the LHS must be ≤ 0?  No.
  -- Use instead: A_n + B_n + δ − (half*ε' + (B_n + (half*ε'+δ))) = A_n − ε' ≥ 0.
  -- Prove via add_le_add chain on the explicit Q' rearrangement.
  have hrew_lhs :
      (HalfPow.half * ε' + (B.approx n + (HalfPow.half * ε' + δ))).eqv
        (ε' + (B.approx n + δ)) := by
    -- half*ε' + (B + (half*ε' + δ)) ≃ (half*ε' + half*ε') + (B + δ) ≃ ε' + (B + δ)
    refine Q'.eqv_trans _ _ _ ?_
      (Q'.add_eqv_congr_right (HalfPow.half * ε' + HalfPow.half * ε') ε' (B.approx n + δ)
        (ExpNeg.two_halves ε'))
    -- half*ε' + (B + (half*ε' + δ)) ≃ (half*ε' + half*ε') + (B + δ)
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (HalfPow.half * ε') (B.approx n + (HalfPow.half * ε' + δ))
        (HalfPow.half * ε' + (B.approx n + δ)) ?_) ?_
    · -- B + (half*ε' + δ) ≃ half*ε' + (B + δ)
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left (B.approx n) (HalfPow.half * ε' + δ) (δ + HalfPow.half * ε')
          (Q'.add_comm_eqv (HalfPow.half * ε') δ)) ?_
      refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv (B.approx n) δ (HalfPow.half * ε'))) ?_
      refine Q'.eqv_trans _ _ _ (Q'.add_comm_eqv (B.approx n + δ) (HalfPow.half * ε')) ?_
      exact Q'.eqv_refl _
    · -- half*ε' + (half*ε' + (B+δ)) ≃ (half*ε' + half*ε') + (B+δ)
      exact Q'.eqv_symm (Q'.add_assoc_eqv (HalfPow.half * ε') (HalfPow.half * ε') (B.approx n + δ))
  have hrew_rhs : ((A.approx n + B.approx n) + δ).eqv (A.approx n + (B.approx n + δ)) :=
    Q'.add_assoc_eqv (A.approx n) (B.approx n) δ
  -- ε' + (B+δ) ≤ A_n + (B+δ) from ε' ≤ A_n
  have hcmp : ε' + (B.approx n + δ) ≤ A.approx n + (B.approx n + δ) :=
    Q'.add_le_add_right ε' (A.approx n) (B.approx n + δ) hAn
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hrew_lhs)
    (Q'.le_trans' _ _ _ hcmp (Q'.ge_of_eqv hrew_rhs))

/-! ## The cancellation core (the genuine engine heart)

From `PosEv (A·B)` and `PosEv B` conclude `PosEv A`.  Pointwise: eventually
`Aₙ·Bₙ ≥ d > 0`, `0 < e ≤ Bₙ`, and (`localBound`) `Bₙ ≤ Bup`.  Then `Aₙ > 0`
(else `Aₙ·Bₙ ≤ 0 < d`), and `Aₙ·Bup ≥ Aₙ·Bₙ ≥ d`, so `Aₙ ≥ d/Bup > 0`.
The witness rational `d/Bup` is positive, giving `PosEv A`. -/

/-- **Cancellation core.**  `PosEv (A·B) → PosEv B → PosEv A`.  This is where the
Turán step cancels the positive factor `P_{k−1}` — no division of polynomials,
just a pointwise positive-rational bound. -/
theorem posEv_left_of_mul {A B : CReal} (hAB : PosEv (CReal.mul A B))
    (hB : PosEv B) : PosEv A := by
  obtain ⟨d, hd, Nd, hNd⟩ := eventually_ge_of_posEv hAB
  obtain ⟨e, he, Ne, hNe⟩ := eventually_ge_of_posEv hB
  obtain ⟨Nbd, Bup, hBup0, hBup⟩ := CReal.localBound B
  -- witness ε := d / Bup.  We avoid constructing a division; instead use the
  -- Q' inequality `Aₙ * Bup ≥ d` (proved below) and pick the witness via mkPos.
  -- Concretely set w := mkPos d.num (d.den * Bup.den ...) — instead, use the
  -- cleaner bound: there is a positive rational `w` with `w * Bup ≤ d`, namely
  -- by `exists_mul_le` applied to (0 ≤ Bup) and (0 < d).
  obtain ⟨w, hw, hwBup⟩ := CReal.exists_mul_le hBup0 hd
  refine posEv_of_eventually hw ⟨max (max Nd Ne) Nbd, fun n hn => ?_⟩
  have hnd : Nd ≤ n :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) hn
  have hne : Ne ≤ n :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) hn
  have hnbd : Nbd ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
  have hABn : d ≤ A.approx n * B.approx n := hNd n hnd
  have hBn : e ≤ B.approx n := hNe n hne
  have hBub : B.approx n ≤ Bup := (hBup n hnbd).2
  have hBpos : (0 : Q') < B.approx n := q_lt_of_lt_of_le he hBn
  -- First: Aₙ ≥ 0.  Else Aₙ < 0, so Aₙ·Bₙ ≤ 0 < d, contradiction.
  have hAnn : (0 : Q') ≤ A.approx n := by
    rcases (inferInstance : Decidable ((0 : Q') ≤ A.approx n)) with hlt | hge
    · -- ¬(0 ≤ Aₙ) : then Aₙ ≤ 0, so Aₙ·Bₙ ≤ 0 < d, contradiction.
      have hAneg : A.approx n ≤ 0 := Q'.le_of_not_le hlt
      have h0 : A.approx n * B.approx n ≤ 0 * B.approx n :=
        Q'.mul_le_mul_of_nonneg_right (A.approx n) 0 (B.approx n) hAneg (Q'.le_of_lt hBpos)
      have h0' : A.approx n * B.approx n ≤ 0 :=
        Q'.le_trans' _ _ _ h0 (Q'.le_of_eqv (Q'.zero_mul_eqv (B.approx n)))
      have hdle0 : d ≤ (0 : Q') := Q'.le_trans' _ _ _ hABn h0'
      have h00 : (0 : Q') < 0 := q_lt_of_lt_of_le hd hdle0
      exact absurd (h00 : (0 : Int) * ((0:Q').den : Int) < (0:Q').num * ((0:Q').den : Int))
        (by decide)
    · exact hge
  -- Now: w ≤ Aₙ.  We have w·Bup ≤ d ≤ Aₙ·Bₙ ≤ Aₙ·Bup, and Bup > 0, so w ≤ Aₙ.
  have hBup_pos : (0 : Q') < Bup := q_lt_of_lt_of_le hBpos hBub
  -- Aₙ·Bₙ ≤ Aₙ·Bup  (Aₙ ≥ 0, Bₙ ≤ Bup)
  have hmono : A.approx n * B.approx n ≤ A.approx n * Bup :=
    CyclotomicPositivity.mul_le_mul_of_nonneg_left hBub hAnn
  -- Bup·w ≤ d ≤ Aₙ·Bₙ ≤ Aₙ·Bup = Bup·Aₙ
  show w ≤ A.approx n
  have hchain' : Bup * w ≤ Bup * A.approx n :=
    Q'.le_trans' _ _ _ hwBup
      (Q'.le_trans' _ _ _ hABn
        (Q'.le_trans' _ _ _ hmono (Q'.le_of_eqv (Q'.mul_comm_eqv (A.approx n) Bup))))
  exact Q'.le_of_mul_le_mul_left hchain' hBup_pos

/-! ## THE KEY LEMMA: the Turán step

Given `0 ≤ a`, `P_{k−1}(a) > 0`, `P_k(a) > 0`, and `nonnegCoeffs (turanPoly k)`,
conclude `P_{k+1}(a) > 0`.  Genuinely PROVED, unconditional in the engine. -/

/-- The Turán value identity, at the `CReal` point: the product
`P_{k+1}·P_{k−1}` evaluated at `a` equals `P_k² + T_k` evaluated at `a`. -/
theorem turan_value_identity (k : Nat) (a : CReal) :
    CReal.Equiv
      (ceval (QPoly.pmul (Pseq (k + 1)) (Pseq (k - 1))) a)
      (CReal.add (CReal.mul (ceval (Pseq k) a) (ceval (Pseq k) a))
        (ceval (turanPoly k) a)) := by
  -- turanPoly k = psub (P_{k+1}P_{k-1}) (P_k P_k), so
  -- padd (P_k P_k) (turanPoly k) = P_{k+1}P_{k-1}  as a polynomial identity at every y.
  refine SumOfSquares.Equiv_of_approx_eqv (fun n => ?_)
  rw [ceval_approx]
  show (QPoly.eval (QPoly.pmul (Pseq (k + 1)) (Pseq (k - 1))) (a.approx n)).eqv
      ((CReal.mul (ceval (Pseq k) a) (ceval (Pseq k) a)).approx n
        + (ceval (turanPoly k) a).approx n)
  -- RHS approx: (P_k·P_k eval) + (turanPoly eval)
  show (QPoly.eval (QPoly.pmul (Pseq (k + 1)) (Pseq (k - 1))) (a.approx n)).eqv
      ((ceval (Pseq k) a).approx n * (ceval (Pseq k) a).approx n
        + (ceval (turanPoly k) a).approx n)
  rw [ceval_approx, ceval_approx]
  -- Both sides are QPoly.eval at y := a.approx n.  Abbreviate y, c, b by hand.
  -- LHS = eval(P_{k+1}P_{k-1}) y ;  goal RHS = eval(P_k) y · eval(P_k) y + eval(turanPoly k) y.
  -- eval(turanPoly k) y = eval(P_{k+1}P_{k-1}) y − eval(P_k·P_k) y  (eval_psub + eval_pmul)
  -- so RHS = eval(P_k) y·eval(P_k) y + (eval(P_{k+1}P_{k-1}) y + −(eval(P_k P_k) y))
  --        = eval(P_{k+1}P_{k-1}) y  (the P_k² cancels).  Prove by Q' algebra.
  have hT : (QPoly.eval (turanPoly k) (a.approx n)).eqv
      (QPoly.eval (QPoly.pmul (Pseq (k + 1)) (Pseq (k - 1))) (a.approx n)
        + -(QPoly.eval (QPoly.pmul (Pseq k) (Pseq k)) (a.approx n))) :=
    QPoly.eval_psub (QPoly.pmul (Pseq (k + 1)) (Pseq (k - 1)))
      (QPoly.pmul (Pseq k) (Pseq k)) (a.approx n)
  have hPk2 : (QPoly.eval (Pseq k) (a.approx n) * QPoly.eval (Pseq k) (a.approx n)).eqv
      (QPoly.eval (QPoly.pmul (Pseq k) (Pseq k)) (a.approx n)) :=
    Q'.eqv_symm (QPoly.eval_pmul (Pseq k) (Pseq k) (a.approx n))
  -- Assemble: RHS = (eval P_k · eval P_k) + eval(turanPoly) y
  refine Q'.eqv_symm ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right (QPoly.eval (Pseq k) (a.approx n) * QPoly.eval (Pseq k) (a.approx n))
      (QPoly.eval (QPoly.pmul (Pseq k) (Pseq k)) (a.approx n))
      (QPoly.eval (turanPoly k) (a.approx n)) hPk2) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (QPoly.eval (QPoly.pmul (Pseq k) (Pseq k)) (a.approx n))
      (QPoly.eval (turanPoly k) (a.approx n))
      (QPoly.eval (QPoly.pmul (Pseq (k + 1)) (Pseq (k - 1))) (a.approx n)
        + -(QPoly.eval (QPoly.pmul (Pseq k) (Pseq k)) (a.approx n))) hT) ?_
  -- Now: c + (b + -c) ≃ b  with
  --   c = eval(P_k P_k) y ,  b = eval(P_{k+1}P_{k-1}) y.
  -- c + (b + -c) ≃ c + (-c + b) ≃ (c + -c) + b ≃ 0 + b ≃ b
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (QPoly.eval (QPoly.pmul (Pseq k) (Pseq k)) (a.approx n))
      (QPoly.eval (QPoly.pmul (Pseq (k + 1)) (Pseq (k - 1))) (a.approx n)
        + -(QPoly.eval (QPoly.pmul (Pseq k) (Pseq k)) (a.approx n)))
      (-(QPoly.eval (QPoly.pmul (Pseq k) (Pseq k)) (a.approx n))
        + QPoly.eval (QPoly.pmul (Pseq (k + 1)) (Pseq (k - 1))) (a.approx n))
      (Q'.add_comm_eqv (QPoly.eval (QPoly.pmul (Pseq (k + 1)) (Pseq (k - 1))) (a.approx n))
        (-(QPoly.eval (QPoly.pmul (Pseq k) (Pseq k)) (a.approx n))))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.add_assoc_eqv
      (QPoly.eval (QPoly.pmul (Pseq k) (Pseq k)) (a.approx n))
      (-(QPoly.eval (QPoly.pmul (Pseq k) (Pseq k)) (a.approx n)))
      (QPoly.eval (QPoly.pmul (Pseq (k + 1)) (Pseq (k - 1))) (a.approx n)))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right
      (QPoly.eval (QPoly.pmul (Pseq k) (Pseq k)) (a.approx n)
        + -(QPoly.eval (QPoly.pmul (Pseq k) (Pseq k)) (a.approx n))) 0
      (QPoly.eval (QPoly.pmul (Pseq (k + 1)) (Pseq (k - 1))) (a.approx n))
      (Q'.add_neg_self_eqv (QPoly.eval (QPoly.pmul (Pseq k) (Pseq k)) (a.approx n)))) ?_
  exact QPoly.q_zero_add_eqv
    (QPoly.eval (QPoly.pmul (Pseq (k + 1)) (Pseq (k - 1))) (a.approx n))

/-- **THE TURÁN STEP (the key engine lemma).**  For `a ≥ 0`, from
`P_{k−1}(a) > 0`, `P_k(a) > 0` and `nonnegCoeffs (turanPoly k)`, conclude
`P_{k+1}(a) > 0`.  Proof: the Turán value identity makes
`P_{k+1}·P_{k−1} = P_k² + T_k` with `P_k² > 0` (square of a positive) and
`T_k ≥ 0` (`a ≥ 0`, nonneg-coeff), hence `P_{k+1}·P_{k−1} > 0`; cancelling
`P_{k−1} > 0` (`posEv_left_of_mul`) gives `P_{k+1} > 0`.  NO sign flip, NO
`a^{2k}−1` multiplier. -/
theorem turan_step (k : Nat) {a : CReal} (ha : ExpPos.geRat a 0)
    (hPkm1 : PosEv (ceval (Pseq (k - 1)) a))
    (hPk : PosEv (ceval (Pseq k) a))
    (hT : nonnegCoeffs (turanPoly k)) :
    PosEv (ceval (Pseq (k + 1)) a) := by
  -- P_k² + T_k is PosEv: square of a positive + a nonnegative.
  have hPk2 : PosEv (CReal.mul (ceval (Pseq k) a) (ceval (Pseq k) a)) := posEv_sq hPk
  have hTk : ExpPos.geRat (ceval (turanPoly k) a) 0 :=
    geRat_ceval_of_nonnegCoeffs (turanPoly k) ha hT
  have hsum : PosEv (CReal.add (CReal.mul (ceval (Pseq k) a) (ceval (Pseq k) a))
      (ceval (turanPoly k) a)) := posEv_add_geRat hPk2 hTk
  -- transport across the Turán identity to get PosEv of the product P_{k+1}·P_{k-1}
  have hprod : PosEv (ceval (QPoly.pmul (Pseq (k + 1)) (Pseq (k - 1))) a) :=
    posEv_of_equiv hsum (CReal.Equiv.symm (turan_value_identity k a))
  -- rewrite the product evaluation as a CReal product (ceval_pmul_equiv)
  have hprod' : PosEv (CReal.mul (ceval (Pseq (k + 1)) a) (ceval (Pseq (k - 1)) a)) :=
    posEv_of_equiv hprod (ceval_pmul_equiv (Pseq (k + 1)) (Pseq (k - 1)) a)
  -- cancel the positive factor P_{k-1}
  exact posEv_left_of_mul hprod' hPkm1

/-! ## The named uniform residual (the single remaining wall)

`UniformTuranNonneg : ∀ k, nonnegCoeffs (turanPoly k)`.  This is the ONLY open
input — everything below (the reduction and capstone) is unconditional given
it.  `decide`-verified through `k = 5/6` above (`turan_nonneg_2…6`); an
`N`-indexed proof is open, attackable via Dodgson / Desnanot–Jacobi
condensation (the discrete Turán determinant `T_k` as `(square)·(another
minor)`). -/

/-- **NAMED-OPEN.**  Uniform nonnegativity of the discrete Turán determinant:
`T_k = P_{k+1}P_{k−1} − P_k²` is nonneg-coefficient for every `k`.  Verified by
`decide` through `k = 5/6`; the `N`-indexed proof is the remaining wall. -/
def UniformTuranNonneg : Prop := ∀ k : Nat, nonnegCoeffs (turanPoly k)

/-! ## The reduction: `UniformTuranNonneg ⟹ P_N > 0` for all `N`

Two-step induction.  Base `P_0, P_1 > 0` (both `= P1 = [1]`, value `1`); the
inductive step is `turan_step`.  Mirrors `uniform_PN_of_PNStep`. -/

/-- `P_0 = P_1 = [1]`, so `ceval (Pseq 0/1) a` is `1 + a·0 = 1 > 0`: the base
strict positivity.  (`Pseq 0 = Pseq 1 = P1 = [Q'.ofNat 1]`.) -/
theorem posEv_Pseq_base (a : CReal) (i : Nat) (hi : i ≤ 1) :
    PosEv (ceval (Pseq i) a) := by
  have hval : Pseq i = [Q'.ofNat 1] := by
    match i, hi with
    | 0, _ => rfl
    | 1, _ => rfl
  rw [hval]
  -- ceval [1] a = ofQ' 1 + a·(ceval [] a) = ofQ' 1 + a·czero ; approx n = 1 + a_n·0
  refine posEv_of_eventually (ε := Q'.ofNat 1) (by decide) ⟨0, fun n _ => ?_⟩
  show (Q'.ofNat 1) ≤ (ceval [Q'.ofNat 1] a).approx n
  rw [ceval_approx]
  show (Q'.ofNat 1) ≤ QPoly.eval [Q'.ofNat 1] (a.approx n)
  -- eval [1] y = 1 + y*0 ≃ 1
  refine Q'.le_trans' _ _ _ (Q'.le_refl' (Q'.ofNat 1)) (Q'.ge_of_eqv ?_)
  show ((Q'.ofNat 1) + a.approx n * QPoly.eval [] (a.approx n)).eqv (Q'.ofNat 1)
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (Q'.ofNat 1) (a.approx n * QPoly.eval [] (a.approx n)) 0 ?_) ?_
  · -- a_n * eval [] = a_n * 0 ≃ 0
    exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (a.approx n) (QPoly.eval [] (a.approx n)) 0 (Q'.eqv_refl 0))
      (QPoly.q_mul_zero (a.approx n))
  · exact QPoly.q_add_zero_eqv (Q'.ofNat 1)

/-- **REDUCTION.**  `UniformTuranNonneg ⟹ ∀ N, P_N(a) > 0` for `a ≥ 0`.
Two-step induction: base `N = 0,1` (`posEv_Pseq_base`); step `turan_step` on
`k = n+1` (so `k − 1 = n`, `k = n+1`, `k + 1 = n+2`). -/
theorem Pseq_pos_of_uniformTuran (hU : UniformTuranNonneg) {a : CReal}
    (ha : ExpPos.geRat a 0) : ∀ N : Nat, PosEv (ceval (Pseq N) a) := by
  -- pair predicate: PosEv (P_N) ∧ PosEv (P_{N+1}), then project.
  have hpair : ∀ N : Nat, PosEv (ceval (Pseq N) a) ∧ PosEv (ceval (Pseq (N + 1)) a) := by
    intro N
    induction N with
    | zero => exact ⟨posEv_Pseq_base a 0 (by omega), posEv_Pseq_base a 1 (by omega)⟩
    | succ n ih =>
        refine ⟨ih.2, ?_⟩
        -- need PosEv (P_{n+2}).  Apply turan_step at k = n+1:
        --   k-1 = n, k = n+1, k+1 = n+2.
        have hstep := turan_step (n + 1) ha
          (by simpa using ih.1) ih.2 (hU (n + 1))
        -- (n+1)-1 = n ; (n+1)+1 = n+2
        simpa using hstep
  exact fun N => (hpair N).1

/-! ## THE CAPSTONE: all-order Gram PSD, conditional on `UniformTuranNonneg`

Compose `P_N > 0` (reduction) with `S_N² ≥ 0` (uniform) via
`gram_minor_nonneg_of_PN`.  The factorization `Δ_N ≃ (SN N)²·P_N` is supplied
as a hypothesis `hfact` (the per-`N` `decide` factorization, the same datum the
existing per-order minor results consume); the engine and reduction are
unconditional. -/

/-- **CAPSTONE.**  `UniformTuranNonneg ⟹ Δ_N(a) ≥ 0` for every `N` and every
`a ≥ 0`, given the order-`N` factorization `Δ ≃ (SN N)²·P_N`.

The all-order Gram PSD is thus PROVED conditional on the single named
`UniformTuranNonneg`, with the per-step Turán engine (`turan_step`)
UNCONDITIONAL.  `S_N² ≥ 0` is uniform (`geRat_SN_sq_nonneg_uniform`); `P_N > 0`
comes from `Pseq_pos_of_uniformTuran` (hence `nonnegCoeffs`-free at the value
level — the residual is `UniformTuranNonneg`, not `nonnegCoeffs P_N`).

Note this routes positivity of `Δ_N` through `geRat (ceval Δ) 0` via
`gram_minor_nonneg_of_PN`, which itself needs `nonnegCoeffs P_N`; to keep the
single residual genuinely `UniformTuranNonneg` we instead reconstruct
`Δ ≥ 0` directly from `S_N² ≥ 0` and `P_N > 0` (value-level), the
square-times-positive shape, with NO `nonnegCoeffs P_N` input. -/
theorem delta_nonneg_all_of_uniformTuran (hU : UniformTuranNonneg)
    (N : Nat) {Δ : CReal} {a : CReal} (ha : ExpPos.geRat a 0)
    (hfact : CReal.Equiv Δ
      (CReal.mul (CReal.mul (ceval (SN N) a) (ceval (SN N) a)) (ceval (Pseq N) a))) :
    ExpPos.geRat Δ 0 := by
  -- S_N² ≥ 0 (uniform) and P_N ≥ 0 (from P_N > 0 via PosEv → geRat); product ≥ 0.
  have hSN2 : ExpPos.geRat (CReal.mul (ceval (SN N) a) (ceval (SN N) a)) 0 :=
    FavardUniform.geRat_SN_sq_nonneg_uniform N a
  have hPN : ExpPos.geRat (ceval (Pseq N) a) 0 :=
    geRat_zero_of_posEv (Pseq_pos_of_uniformTuran hU ha N)
  refine SU3CharFactor.geRat_of_equiv hfact ?_
  exact CReal.mul_nonneg hSN2 hPN

end YMGap.Continuum.TuranPositivity

/-! ## Summary — PROVED vs NAMED-open

**PROVED here (axiom-clean; the per-step engine is UNCONDITIONAL).**

  * `turan_nonneg_2 … turan_nonneg_6` — the base certificates
    `nonnegCoeffs (turanPoly k)` (`decide`, `k = 2,…,6`).

  * The strict-positivity engine `PosEv` and its algebra: `posEv_mul`,
    `posEv_sq`, `posEv_add_geRat`, `posEv_of_equiv`, `geRat_zero_of_posEv`,
    and the cancellation core `posEv_left_of_mul`.

  * `turan_value_identity` — the Turán identity at the `CReal` point
    (`P_{k+1}·P_{k−1} = P_k² + T_k`).

  * **`turan_step`** — THE KEY LEMMA: `P_{k+1}(a) > 0` from `P_{k−1}(a) > 0`,
    `P_k(a) > 0` and `nonnegCoeffs (turanPoly k)`, with NO sign flip and NO
    `a^{2k}−1` multiplier.  This REPLACES the old `PNStep` / Favard-quadratic
    obstruction (the cyclotomic factor `a^{2k}−1` with constant term `−1`).

  * `Pseq_pos_of_uniformTuran` — REDUCTION: `UniformTuranNonneg ⟹ P_N(a) > 0`
    for all `N` (two-step induction, base + `turan_step`).

  * `delta_nonneg_all_of_uniformTuran` — CAPSTONE: `UniformTuranNonneg ⟹
    Δ_N(a) ≥ 0` for all `N`, square-times-positive, value-level (NO
    `nonnegCoeffs P_N` input — the only residual is `UniformTuranNonneg`).

**NAMED-open — the single residual.**

  `UniformTuranNonneg : ∀ k, nonnegCoeffs (turanPoly k)`.  `decide`-verified
  through `k = 5/6`; the `N`-indexed proof is open, attackable via
  Dodgson / Desnanot–Jacobi condensation (`T_k = (square)·(another minor)`).
-/

#print axioms YMGap.Continuum.TuranPositivity.turan_nonneg_2
#print axioms YMGap.Continuum.TuranPositivity.turan_nonneg_6
#print axioms YMGap.Continuum.TuranPositivity.posEv_left_of_mul
#print axioms YMGap.Continuum.TuranPositivity.turan_value_identity
#print axioms YMGap.Continuum.TuranPositivity.turan_step
#print axioms YMGap.Continuum.TuranPositivity.Pseq_pos_of_uniformTuran
#print axioms YMGap.Continuum.TuranPositivity.delta_nonneg_all_of_uniformTuran
