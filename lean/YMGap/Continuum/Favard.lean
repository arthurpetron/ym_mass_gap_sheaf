/-
Research frontier — the **Favard / three-term-recurrence** route to the
uniform-in-`N` SU(2) heat-kernel Gram positivity.

Setup (same uniform base variable as `MomentPositivity`):
`a = e^{−t/4} ∈ (0,1]`, moments `m_s = (s+1)·a^{s(s+2)}`, and the leading
principal Gram minors `Δ_N(a) = det G[0..N−1]` factor uniformly as

    Δ_N(a) = S_N(a)² · P_N(a),

with `S_N` a (integer-coefficient) polynomial and `P_N` an all-nonnegative
coefficient polynomial with constant term `1` (verified by exact computer
algebra through `N = 6`; the cyclotomic part of every `Δ_N` carries even
multiplicity, so it is a perfect square `S_N²`, and the residual `P_N` is a
positive combination of monomials in `a²` with `P_N(0) = 1`).

For the monic orthogonal polynomials of the heat-kernel moment functional,
the three-term recurrence `Q_{s+1} = (x−α_s)Q_s − β_s Q_{s−1}` has

    β_s = Δ_s · Δ_{s−2} / Δ_{s−1}²      (ratio of consecutive leading minors)

and Favard's theorem says the moment functional is positive (⟺ Gram-PSD at
every order) iff `β_s ≥ 0` for all `s`.  Using the factorization,

    β_s = (S_s·S_{s−2} / S_{s−1}²)² · (P_s·P_{s−2} / P_{s−1}²),

a perfect square times a ratio of all-positive polynomials, so `β_s ≥ 0`.
Since `Δ_{s−1}² ≥ 0` for free, the *division-free* content of `β_s ≥ 0` is

    Δ_s · Δ_{s−2} ≥ 0,    and    Δ_s·Δ_{s−2} = (S_s·S_{s−2})²·(P_s·P_{s−2}),

i.e. a perfect square times a **product of two nonneg-coefficient
polynomials** — and a product of nonneg-coefficient polynomials is again
nonneg-coefficient.  This file proves exactly that division-free engine,
plus the strengthening `P_N ≥ 1` (constant term `1`), and the concrete
`β_s`-numerator nonnegativity for `s = 1,2,3,4`.

What is proved here (axiom-clean, no `Classical`/`sorry`):

  * `geRat_ceval_ge_const` — a nonneg-coefficient polynomial evaluated at
    `x ≥ 0` is `≥` its constant term (Horner: `c₀ + x·(nonneg)`).  Hence
  * `geRat_ceval_ge_one_of_constOne` / `P_N ≥ 1` for the concrete `P_N`.
  * `nonnegCoeffsB_padd`, `nonnegCoeffsB_pscale`, `nonnegCoeffs_pmul` — the
    nonneg-coefficient cone is closed under `+`, nonneg-scaling, and `·`.
  * `favard_numer_nonneg` — the **Favard reduction** (division-free): given
    `Δ_s = S_s²·P_s` and `Δ_{s−2} = S_{s−2}²·P_{s−2}` with `P_s,P_{s−2}`
    nonneg-coefficient, the recurrence numerator `Δ_s·Δ_{s−2} ≥ 0`, as
    `(S_s S_{s−2})²·(P_s·P_{s−2})` — square × nonneg-coeff product.
  * `beta1/2/3/4_numer_nonneg` — the concrete instances for `s = 1,2,3,4`
    from the exact `(S_k,P_k)` lists (all `decide` factorizations).

# Axiom-gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]`.  No `Classical.*`, no `sorryAx`.
-/

import YMGap.Continuum.MomentPositivity

namespace YMGap.Continuum

open YMGap.Constructive

/-! ## Strengthening the positivity engine: `ceval p x ≥ c₀`

The existing `geRat_ceval_of_nonnegCoeffs` gives `ceval p x ≥ 0`.  Horner
actually keeps the constant term as a *floor*: `ceval (c₀::cs) x =
c₀ + x·(ceval cs x)`, and `x·(ceval cs x) ≥ 0` when the tail is
nonneg-coefficient and `x ≥ 0`, so `ceval (c₀::cs) x ≥ c₀`.  Applied to a
`P_N` (constant term `1`) this yields the strict floor `P_N(a) ≥ 1 > 0`. -/

/-- A nonneg-coefficient polynomial evaluated at `x ≥ 0` is **≥ its constant
term**.  For the empty list the "constant term" is `0`. -/
theorem geRat_ceval_ge_const :
    ∀ (p : QPoly.Poly) {x : CReal}, ExpPos.geRat x 0 → nonnegCoeffs p →
      ExpPos.geRat (ceval p x) (match p with | [] => 0 | (c :: _) => c)
  | [], _, _, _ => SumOfSquares.geRat_czero
  | (c :: cs), x, hx, h => by
      have hb : nonnegCoeffsB cs = true := by
        have h' := h
        rw [nonnegCoeffs, nonnegCoeffsB, Bool.and_eq_true] at h'
        exact h'.2
      have hcs : ExpPos.geRat (ceval cs x) 0 :=
        geRat_ceval_of_nonnegCoeffs cs hx hb
      have hprod : ExpPos.geRat (CReal.mul x (ceval cs x)) 0 :=
        CReal.mul_nonneg hx hcs
      -- ceval (c::cs) x = ofQ' c + x·(ceval cs x) ≥ c + 0 = c
      have hsum : ExpPos.geRat
          (CReal.add (CReal.ofQ' c) (CReal.mul x (ceval cs x))) (c + 0) :=
        SumOfSquares.geRat_add
          (ExpPos.geRat_of_eventually ⟨0, fun _ _ => Q'.le_refl' c⟩) hprod
      exact ExpPos.geRat_mono hsum (Q'.le_of_eqv (Q'.eqv_symm (QPoly.q_add_zero_eqv c)))

/-- **`P_N ≥ 1`.**  A nonneg-coefficient polynomial with head coefficient
`c ≥ 1`, evaluated at `x ≥ 0`, is `≥ 1` — the constant-term-`1`
strengthening of the engine (every `P_N` has constant term `1`, so
`P_N(a) ≥ 1 > 0`).  Stated in cons form so the floor is `c`. -/
theorem geRat_ceval_ge_one_of_headGeOne (c : Q') (cs : QPoly.Poly) {x : CReal}
    (hx : ExpPos.geRat x 0) (h : nonnegCoeffs (c :: cs)) (hc : (1 : Q') ≤ c) :
    ExpPos.geRat (ceval (c :: cs) x) 1 :=
  ExpPos.geRat_mono (geRat_ceval_ge_const (c :: cs) hx h) hc

/-! ## The nonneg-coefficient cone is closed under `+`, scaling, and `·`

`P_s·P_{s−2}` must itself be nonneg-coefficient for the Favard reduction; it
is, because the `QPoly` ring operation `pmul` builds it from `padd` of
`pscale`-d copies, and the nonneg cone is closed under each. -/

/-- `padd` of two nonneg-coefficient lists is nonneg-coefficient. -/
theorem nonnegCoeffsB_padd :
    ∀ (p q : QPoly.Poly), nonnegCoeffsB p = true → nonnegCoeffsB q = true →
      nonnegCoeffsB (QPoly.padd p q) = true
  | [], q, _, hq => hq
  | (a :: p), [], hp, _ => hp
  | (a :: p), (b :: q), hp, hq => by
      rw [nonnegCoeffsB, Bool.and_eq_true] at hp hq
      have ha : (0 : Q') ≤ a := of_decide_eq_true hp.1
      have hb : (0 : Q') ≤ b := of_decide_eq_true hq.1
      show nonnegCoeffsB ((a + b) :: QPoly.padd p q) = true
      rw [nonnegCoeffsB, Bool.and_eq_true]
      exact ⟨decide_eq_true (Q'.zero_le_add a b ha hb),
        nonnegCoeffsB_padd p q hp.2 hq.2⟩

/-- Scaling a nonneg-coefficient list by `k ≥ 0` keeps it nonneg-coefficient. -/
theorem nonnegCoeffsB_pscale {k : Q'} (hk : (0 : Q') ≤ k) :
    ∀ (p : QPoly.Poly), nonnegCoeffsB p = true →
      nonnegCoeffsB (QPoly.pscale k p) = true
  | [], _ => rfl
  | (c :: cs), h => by
      rw [nonnegCoeffsB, Bool.and_eq_true] at h
      have hc : (0 : Q') ≤ c := of_decide_eq_true h.1
      show nonnegCoeffsB ((k * c) :: QPoly.pscale k cs) = true
      rw [nonnegCoeffsB, Bool.and_eq_true]
      exact ⟨decide_eq_true (Q'.mul_nonneg k c hk hc),
        nonnegCoeffsB_pscale hk cs h.2⟩

/-- Prepending `0` keeps a nonneg-coefficient list nonneg-coefficient. -/
theorem nonnegCoeffsB_cons_zero {p : QPoly.Poly} (h : nonnegCoeffsB p = true) :
    nonnegCoeffsB ((0 : Q') :: p) = true := by
  rw [nonnegCoeffsB, Bool.and_eq_true]
  exact ⟨decide_eq_true (Q'.le_refl' 0), h⟩

/-- **The nonneg-coefficient cone is closed under multiplication.**  Horner
`pmul (a::p) q = padd (pscale a q) (0 :: pmul p q)`: a nonneg-scaling plus a
`0`-shifted product, both nonneg by the closure lemmas above. -/
theorem nonnegCoeffsB_pmul :
    ∀ (p q : QPoly.Poly), nonnegCoeffsB p = true → nonnegCoeffsB q = true →
      nonnegCoeffsB (QPoly.pmul p q) = true
  | [], _, _, _ => rfl
  | (a :: p), q, hp, hq => by
      rw [nonnegCoeffsB, Bool.and_eq_true] at hp
      have ha : (0 : Q') ≤ a := of_decide_eq_true hp.1
      show nonnegCoeffsB (QPoly.padd (QPoly.pscale a q) (0 :: QPoly.pmul p q)) = true
      exact nonnegCoeffsB_padd _ _
        (nonnegCoeffsB_pscale ha q hq)
        (nonnegCoeffsB_cons_zero (nonnegCoeffsB_pmul p q hp.2 hq))

/-- Wrapper at the `nonnegCoeffs` (`Prop`) level. -/
theorem nonnegCoeffs_pmul {p q : QPoly.Poly}
    (hp : nonnegCoeffs p) (hq : nonnegCoeffs q) : nonnegCoeffs (QPoly.pmul p q) :=
  nonnegCoeffsB_pmul p q hp hq

/-! ## The Favard reduction (division-free)

`β_s = Δ_s·Δ_{s−2} / Δ_{s−1}²`.  The denominator `Δ_{s−1}²` is a square, so
`β_s ≥ 0 ⟺ Δ_s·Δ_{s−2} ≥ 0`.  With `Δ_s = S_s²·P_s`,
`Δ_{s−2} = S_{s−2}²·P_{s−2}`,

    Δ_s·Δ_{s−2} = (S_s·S_{s−2})²·(P_s·P_{s−2}),

a perfect square times a nonneg-coefficient product.  This lemma packages
that as a single consumable: supply the four lists `(S_s,P_s,S_{s−2},P_{s−2})`
and the two factorization identities, and conclude the numerator `≥ 0`. -/

/-- **Favard recurrence-numerator positivity.**  If two minors factor as
`Δ₁ = S₁²·P₁`, `Δ₂ = S₂²·P₂` with `P₁,P₂` nonneg-coefficient, then the
product (the `β`-numerator `Δ_s·Δ_{s−2}`) is `≥ 0`, certified as
`(S₁·S₂)²·(P₁·P₂)`. -/
theorem favard_numer_nonneg {Δ₁ Δ₂ : CReal} (S₁ P₁ S₂ P₂ : QPoly.Poly)
    {x : CReal} (hx : ExpPos.geRat x 0)
    (hP₁ : nonnegCoeffs P₁) (hP₂ : nonnegCoeffs P₂)
    (hΔ₁ : CReal.Equiv Δ₁ (CReal.mul (CReal.mul (ceval S₁ x) (ceval S₁ x)) (ceval P₁ x)))
    (hΔ₂ : CReal.Equiv Δ₂ (CReal.mul (CReal.mul (ceval S₂ x) (ceval S₂ x)) (ceval P₂ x))) :
    ExpPos.geRat (CReal.mul Δ₁ Δ₂) 0 := by
  -- Δ₁·Δ₂ ≃ (S₁²P₁)·(S₂²P₂); the RHS is (square)·(nonneg) = nonneg.
  refine SU3CharFactor.geRat_of_equiv
    (Pivot2.mul_congr hΔ₁ hΔ₂) ?_
  -- product of two nonnegatives
  exact CReal.mul_nonneg
    (CReal.mul_nonneg (geRat_sq_ceval S₁ x) (geRat_ceval_of_nonnegCoeffs P₁ hx hP₁))
    (CReal.mul_nonneg (geRat_sq_ceval S₂ x) (geRat_ceval_of_nonnegCoeffs P₂ hx hP₂))

/-! ## Concrete `(S_N, P_N)` lists for `N = 1,2,4` and the `β_s` numerators

Coefficient lists (low→high), from exact computer-algebra factorization of
the heat-kernel Gram minors:

  S₁ = [1]                              P₁ = [1]
  S₂ = a²−1                             P₂ = 1 + 2a² + 3a⁴
  S₃ (and P₃) are `MomentPositivity.S3`, `P3`.
  S₄ = degree-20, P₄ = degree-40 (below).

`β_s`-numerator `= Δ_s·Δ_{s−2}`, with `Δ_0 = Δ_{−1} = 1`:
  s=1 :  Δ₁·Δ_{−1} = Δ₁          (= 1)
  s=2 :  Δ₂·Δ₀     = Δ₂          (= S₂²·P₂)
  s=3 :  Δ₃·Δ₁     = Δ₃          (= S₃²·P₃)
  s=4 :  Δ₄·Δ₂     = (S₄·S₂)²·(P₄·P₂). -/

/-- `Δ_1 = 1` coefficient list. -/
def Δ1 : QPoly.Poly := [Q'.ofNat 1]
/-- `S_1 = 1`. -/
def S1 : QPoly.Poly := [Q'.ofNat 1]
/-- `P_1 = 1`. -/
def P1 : QPoly.Poly := [Q'.ofNat 1]

/-- `Δ_2` coefficient list (low→high): `1 − 4a⁶ + 3a⁸`. -/
def Δ2 : QPoly.Poly :=
  [Q'.ofNat 1, 0, 0, 0, 0, 0, -(Q'.ofNat 4), 0, Q'.ofNat 3]
/-- `S_2 = a²−1`. -/
def S2 : QPoly.Poly := [-(1 : Q'), 0, Q'.ofNat 1]
/-- `P_2 = 1 + 2a² + 3a⁴`. -/
def P2 : QPoly.Poly := [Q'.ofNat 1, 0, Q'.ofNat 2, 0, Q'.ofNat 3]

/-- `S_4` coefficient list (low→high), degree 20. -/
def S4 : QPoly.Poly :=
  [Q'.ofNat 1, 0, -(Q'.ofNat 3), 0, Q'.ofNat 1, 0, Q'.ofNat 4, 0,
   -(Q'.ofNat 2), 0, -(Q'.ofNat 2), 0, -(Q'.ofNat 2), 0, Q'.ofNat 4, 0,
   Q'.ofNat 1, 0, -(Q'.ofNat 3), 0, Q'.ofNat 1]
/-- `Δ_4` coefficient list (low→high), degree 80 — the expanded 4×4 minor.
(Used only inside the `decide`-checked factorization identities.) -/
def Δ4 : QPoly.Poly :=
  [Q'.ofNat 1, 0, 0, 0, 0, 0, -(Q'.ofNat 12), 0, Q'.ofNat 9, 0, 0, 0,
   Q'.ofNat 16, 0, 0, 0, Q'.ofNat 9, 0, -(Q'.ofNat 32), 0, 0, 0,
   -(Q'.ofNat 36), 0, -(Q'.ofNat 44), 0, Q'.ofNat 144, 0, 0, 0,
   -(Q'.ofNat 68), 0, Q'.ofNat 30, 0, Q'.ofNat 144, 0, -(Q'.ofNat 128), 0,
   -(Q'.ofNat 144), 0, -(Q'.ofNat 90), 0, Q'.ofNat 160, 0, Q'.ofNat 96, 0,
   -(Q'.ofNat 144), 0, Q'.ofNat 142, 0, Q'.ofNat 192, 0, 0, 0,
   -(Q'.ofNat 372), 0, -(Q'.ofNat 108), 0, Q'.ofNat 144, 0, Q'.ofNat 256, 0,
   -(Q'.ofNat 516), 0, Q'.ofNat 225, 0, Q'.ofNat 720, 0, -(Q'.ofNat 384), 0,
   -(Q'.ofNat 396), 0, -(Q'.ofNat 279), 0, Q'.ofNat 576, 0, Q'.ofNat 144, 0,
   -(Q'.ofNat 360), 0, Q'.ofNat 105]

/-- `P_4` coefficient list (low→high), all nonnegative, degree 40. -/
def P4 : QPoly.Poly :=
  [Q'.ofNat 1, 0, Q'.ofNat 6, 0, Q'.ofNat 25, 0, Q'.ofNat 70, 0,
   Q'.ofNat 169, 0, Q'.ofNat 340, 0, Q'.ofNat 616, 0, Q'.ofNat 988, 0,
   Q'.ofNat 1462, 0, Q'.ofNat 1956, 0, Q'.ofNat 2446, 0, Q'.ofNat 2796, 0,
   Q'.ofNat 2982, 0, Q'.ofNat 2904, 0, Q'.ofNat 2640, 0, Q'.ofNat 2148, 0,
   Q'.ofNat 1617, 0, Q'.ofNat 1050, 0, Q'.ofNat 609, 0, Q'.ofNat 270, 0,
   Q'.ofNat 105]

/-- `P_1` is nonneg-coefficient. -/
theorem P1_nonneg : nonnegCoeffs P1 := by decide
/-- `P_2` is nonneg-coefficient. -/
theorem P2_nonneg : nonnegCoeffs P2 := by decide
/-- `P_4` is nonneg-coefficient. -/
theorem P4_nonneg : nonnegCoeffs P4 := by decide

/-- **`P_2(a) ≥ 1`** for `a ≥ 0` — constant-term-`1` floor. -/
theorem P2_ge_one {a : CReal} (ha : ExpPos.geRat a 0) :
    ExpPos.geRat (ceval P2 a) 1 :=
  geRat_ceval_ge_one_of_headGeOne (Q'.ofNat 1) _ ha P2_nonneg (by decide)

/-- **`P_4(a) ≥ 1`** for `a ≥ 0` — constant-term-`1` floor. -/
theorem P4_ge_one {a : CReal} (ha : ExpPos.geRat a 0) :
    ExpPos.geRat (ceval P4 a) 1 :=
  geRat_ceval_ge_one_of_headGeOne (Q'.ofNat 1) _ ha P4_nonneg (by decide)

/-- **`P_3(a) ≥ 1`** for `a ≥ 0` (`P3` from `MomentPositivity`). -/
theorem P3_ge_one {a : CReal} (ha : ExpPos.geRat a 0) :
    ExpPos.geRat (ceval P3 a) 1 :=
  geRat_ceval_ge_one_of_headGeOne (Q'.ofNat 1) _ ha P3_nonneg (by decide)

/-! ### Factorization identities (`decide`) -/

/-- `Δ_2 = S_2²·P_2`. -/
theorem delta2_factor (a : Q') :
    (QPoly.eval Δ2 a).eqv (QPoly.eval (QPoly.pmul (QPoly.pmul S2 S2) P2) a) :=
  QPoly.poly_eqv _ _ a (by decide)

set_option maxRecDepth 4000 in
/-- `Δ_4 = S_4²·P_4` (degree-80 `QPoly` identity, `decide`). -/
theorem delta4_factor (a : Q') :
    (QPoly.eval Δ4 a).eqv (QPoly.eval (QPoly.pmul (QPoly.pmul S4 S4) P4) a) :=
  QPoly.poly_eqv _ _ a (by decide)

set_option maxRecDepth 8000 in
/-- `Δ_4·Δ_2 = (S_4·S_2)²·(P_4·P_2)` — the `β_4`-numerator factorization
(`decide`). -/
theorem beta4_numer_factor (a : Q') :
    (QPoly.eval (QPoly.pmul Δ4 Δ2) a).eqv
      (QPoly.eval (QPoly.pmul
        (QPoly.pmul (QPoly.pmul S4 S2) (QPoly.pmul S4 S2))
        (QPoly.pmul P4 P2)) a) :=
  QPoly.poly_eqv _ _ a (by decide)

/-! ### Bridge: a `decide`-level factorization gives `ceval Δ a ≥ 0`

The `ceval ∘ pmul` push-through (each `ceval` acts approx-wise, so it agrees
with `QPoly.eval ∘ pmul` pointwise) lets a `QPoly`-identity
`Δ = pmul (pmul S S) P` certify `ceval Δ a ≥ 0`, for any `a ≥ 0` and
nonneg-coefficient `P`.  This is the order-`N`-uniform consumer (the `N = 3`
instance is `MomentPositivity.delta3_nonneg`). -/

/-- `ceval (pmul p q) a ≃ (ceval p a)·(ceval q a)` as `CReal`s. -/
theorem ceval_pmul_equiv (p q : QPoly.Poly) (a : CReal) :
    CReal.Equiv (ceval (QPoly.pmul p q) a) (CReal.mul (ceval p a) (ceval q a)) :=
  SumOfSquares.Equiv_of_approx_eqv (fun n => by
    rw [ceval_approx]
    show (QPoly.eval (QPoly.pmul p q) (a.approx n)).eqv
        ((ceval p a).approx n * (ceval q a).approx n)
    rw [ceval_approx, ceval_approx]
    exact QPoly.eval_pmul p q (a.approx n))

/-- **Single-minor bridge.**  Given the `QPoly` identity
`Δ = pmul (pmul S S) P` and `nonnegCoeffs P`, the constructive-real
evaluation `ceval Δ a ≥ 0` for `a ≥ 0`. -/
theorem ceval_factor_nonneg (Δ S P : QPoly.Poly) {a : CReal}
    (ha : ExpPos.geRat a 0) (hP : nonnegCoeffs P)
    (hid : ∀ y : Q', (QPoly.eval Δ y).eqv (QPoly.eval (QPoly.pmul (QPoly.pmul S S) P) y)) :
    ExpPos.geRat (ceval Δ a) 0 := by
  refine geRat_minor_factored S P ha hP ?_
  refine Pivot2.equiv_trans (ceval_equiv_of_polyEqv (p := Δ)
    (q := QPoly.pmul (QPoly.pmul S S) P) hid a) ?_
  refine Pivot2.equiv_trans (ceval_pmul_equiv (QPoly.pmul S S) P a) ?_
  exact Pivot2.mul_congr_left (ceval_pmul_equiv S S a)

/-! ### `β_s`-numerator nonnegativity, `s = 1,2,3,4`

`β_s`-numerator `= Δ_s·Δ_{s−2}` (with `Δ_0 = Δ_{−1} = 1`).  For `s = 1,2,3`
this reduces to the single minor `Δ_s` (the other factor is `1`); for `s = 4`
it is the genuine product `Δ_4·Δ_2 = (S_4·S_2)²·(P_4·P_2)`.  Each is `≥ 0` at
`a = e^{−t/4} ≥ 0`, certified by a square × nonneg-coefficient product. -/

/-- **`β_1`-numerator `≥ 0`.**  `Δ_1·Δ_{−1} = 1 = 1²·1`. -/
theorem beta1_numer_nonneg {a : CReal} (ha : ExpPos.geRat a 0) :
    ExpPos.geRat (ceval Δ1 a) 0 :=
  ceval_factor_nonneg Δ1 S1 P1 ha P1_nonneg
    (fun y => QPoly.poly_eqv _ _ y (by decide))

/-- **`β_2`-numerator `≥ 0`.**  `Δ_2·Δ_0 = Δ_2 = S_2²·P_2`. -/
theorem beta2_numer_nonneg {a : CReal} (ha : ExpPos.geRat a 0) :
    ExpPos.geRat (ceval Δ2 a) 0 :=
  ceval_factor_nonneg Δ2 S2 P2 ha P2_nonneg (fun y => delta2_factor y)

/-- **`β_3`-numerator `≥ 0`.**  `Δ_3·Δ_1 = Δ_3 = S_3²·P_3`
(`Δ3,S3,P3` from `MomentPositivity`). -/
theorem beta3_numer_nonneg {a : CReal} (ha : ExpPos.geRat a 0) :
    ExpPos.geRat (ceval Δ3 a) 0 :=
  ceval_factor_nonneg Δ3 S3 P3 ha P3_nonneg (fun y => delta3_factor y)

/-- **`β_4`-numerator `≥ 0`.**  The genuine product
`Δ_4·Δ_2 = (S_4·S_2)²·(P_4·P_2)`: a perfect square times the product of two
nonneg-coefficient polynomials (`P_4·P_2` nonneg by `nonnegCoeffs_pmul`). -/
theorem beta4_numer_nonneg {a : CReal} (ha : ExpPos.geRat a 0) :
    ExpPos.geRat (ceval (QPoly.pmul Δ4 Δ2) a) 0 :=
  ceval_factor_nonneg (QPoly.pmul Δ4 Δ2) (QPoly.pmul S4 S2)
    (QPoly.pmul P4 P2) ha (nonnegCoeffs_pmul P4_nonneg P2_nonneg)
    (fun y => beta4_numer_factor y)

/-! ### `β_s`-numerator at the heat-kernel point `a = e^{−t/4}`

The uniform base variable `aVar t = e^{−t/4} ≥ 0` (`MomentPositivity`)
discharges the hypothesis `a ≥ 0`, so each numerator is `≥ 0` for every
`t ≥ 0`. -/

theorem beta1_numer_nonneg_at (t : Q') (ht : (0 : Q') ≤ t) :
    ExpPos.geRat (ceval Δ1 (aVar t ht)) 0 := beta1_numer_nonneg (aVar_nonneg t ht)

theorem beta2_numer_nonneg_at (t : Q') (ht : (0 : Q') ≤ t) :
    ExpPos.geRat (ceval Δ2 (aVar t ht)) 0 := beta2_numer_nonneg (aVar_nonneg t ht)

theorem beta3_numer_nonneg_at (t : Q') (ht : (0 : Q') ≤ t) :
    ExpPos.geRat (ceval Δ3 (aVar t ht)) 0 := beta3_numer_nonneg (aVar_nonneg t ht)

theorem beta4_numer_nonneg_at (t : Q') (ht : (0 : Q') ≤ t) :
    ExpPos.geRat (ceval (QPoly.pmul Δ4 Δ2) (aVar t ht)) 0 :=
  beta4_numer_nonneg (aVar_nonneg t ht)

end YMGap.Continuum

/-! ## OPEN obligation (the uniform `N`-indexed Favard step)

What is **proved** above (axiom-clean):

  * the `ceval p x ≥ c₀` constant-term floor, hence `P_N(a) ≥ 1` for the
    concrete `N = 2,3,4` (and the reusable engine for any nonneg-coefficient
    `P` with head `≥ 1`);
  * closure of the nonneg-coefficient cone under `+`, nonneg-scaling, and
    `·` (`nonnegCoeffs_pmul`);
  * the **division-free Favard reduction** `favard_numer_nonneg`: given the
    two factorizations `Δ_s = S_s²·P_s`, `Δ_{s−2} = S_{s−2}²·P_{s−2}` (with
    `P_s,P_{s−2}` nonneg-coefficient), the recurrence numerator
    `Δ_s·Δ_{s−2} = (S_s·S_{s−2})²·(P_s·P_{s−2})` is `≥ 0`;
  * the concrete `β_s`-numerators `Δ_s·Δ_{s−2} ≥ 0` for `s = 1,2,3,4`,
    both as polynomials in `a` and at the heat-kernel point `a = e^{−t/4}`.

This is the genuine content of `β_s ≥ 0`: since `β_s = Δ_s·Δ_{s−2}/Δ_{s−1}²`
and `Δ_{s−1}² ≥ 0` for free, `β_s ≥ 0 ⟺ Δ_s·Δ_{s−2} ≥ 0`, which is exactly
what is certified.

**OPEN.**  The remaining mathematics is the *uniform `N`-indexed*
construction of the lists `(S_N, P_N)`: a proof that

    Δ_N(a) = S_N(a)²·P_N(a),   P_N nonneg-coefficient, P_N(0) = 1,

holds for **all** `N` (here discharged per-`N` by exact computer algebra and
`decide` through `N = 4`, with the factorization separately verified through
`N = 6`).  The pattern in the data is sharp and worth recording:

  * `S_N²` is exactly the **cyclotomic** part of `Δ_N`, and every cyclotomic
    factor of `Δ_N` occurs with *even* multiplicity — empirically, the
    `d`-th cyclotomic polynomial `Φ_d` (`d ≥ 1`) appears in `Δ_N` to a power
    that grows linearly in `N` with the *same parity for all N of a fixed
    residue*, always even.  Concretely (multiplicities through `N = 6`):
        Φ_1Φ_2 = (a−1)(a+1): 2,6,12,20,30  (= N(N−1));
        Φ_4 = a²+1:          2,4,8,12      (even);
        Φ_3Φ_6 = a²±a+1:     2,4,6         (even);
        Φ_8 = a⁴+1:          2,4;  Φ_5Φ_10 = a⁴±a³+…: 2.
    The *evenness* of every cyclotomic multiplicity is the crux: it is what
    makes the cyclotomic part a perfect square `S_N²`.  A representation-
    theoretic reason (the heat-kernel measure is supported on roots of unity
    in the `a → root` degenerations, with the Gram determinant vanishing to
    even order by a pairing/Vandermonde-squared argument) is the most
    promising route to an `N`-indexed proof.

  * `P_N` is the *residual* `Δ_N / S_N²`; empirically it has all-positive
    coefficients, only even exponents (a positive polynomial in `a²`), and
    constant term `1` (the `a → 0` value, where `Δ_N → 1` since the moment
    matrix degenerates to the identity).  An `N`-indexed positivity of the
    `P_N` coefficients is the second half; the leading coefficient is the
    odd double factorial `(2N−1)!! = 1,3,15,105,945,10395`, consistent with
    a Hankel/Selberg-type product formula whose positivity would give the
    whole `P_N`.

  * **Favard form of the same obstruction.**  Equivalently, prove
    `β_s(a) ≥ 0` for all `s` directly from a closed form / monotone
    structure of the recurrence coefficients of the heat-kernel orthogonal
    polynomials.  The reduction `favard_numer_nonneg` already consumes the
    per-`s` factorization; what is missing is a *uniform* supply of
    `(S_s, P_s)` — i.e. the same `N`-indexed factorization, viewed through
    the recurrence rather than the determinant.

**Assessment.**  The most promising path is the *evenness of cyclotomic
multiplicities* in `Δ_N`: it is the single structural fact that yields the
perfect square `S_N²` uniformly, and it has a plausible
representation-theoretic / Vandermonde-squared origin (the Gram determinant
as a squared Slater/Vandermonde object on the discrete heat-kernel spectrum).
Combined with a Hankel product formula for the residual `P_N` (leading
coefficient `(2N−1)!!`), this would close the uniform step.  The
`decide`-level per-`N` factorizations here (through `N = 4`) plus the
verified pattern through `N = 6` give strong evidence but are **not** an
`N`-indexed theorem; that induction remains open.

This file does not depend on the `MomentPositivity` moment-bridge OPEN (that
`ceval (Δ_N list) (e^{−t/4})` equals the actual CReal Gram minor) — the
results here are stated about the *polynomial* `ceval Δ_N a`, exactly as the
`N = 3` result `delta3_nonneg` is.
-/

#print axioms YMGap.Continuum.geRat_ceval_ge_const
#print axioms YMGap.Continuum.geRat_ceval_ge_one_of_headGeOne
#print axioms YMGap.Continuum.nonnegCoeffs_pmul
#print axioms YMGap.Continuum.favard_numer_nonneg
#print axioms YMGap.Continuum.P2_ge_one
#print axioms YMGap.Continuum.P3_ge_one
#print axioms YMGap.Continuum.P4_ge_one
#print axioms YMGap.Continuum.delta2_factor
#print axioms YMGap.Continuum.delta4_factor
#print axioms YMGap.Continuum.beta4_numer_factor
#print axioms YMGap.Continuum.beta1_numer_nonneg
#print axioms YMGap.Continuum.beta2_numer_nonneg
#print axioms YMGap.Continuum.beta3_numer_nonneg
#print axioms YMGap.Continuum.beta4_numer_nonneg
#print axioms YMGap.Continuum.beta4_numer_nonneg_at
