/-
Track B / E1 — the real single-edge SU(2) heat-kernel Wilson functional,
via character orthogonality.

The heat-kernel measure on one edge, `dμ_t(g) = K_t(g) dg` with
`K_t(g) = Σ_λ dim(λ)·χ_λ(g)·e^{−t·C₂(λ)}`, is a genuine probability
measure on `SU(2)` (the only rep contributing to `∫K_t` is the trivial one,
so `∫K_t = 1`).  By Peter–Weyl / character orthogonality
(`∫ χ_μ χ_λ dg = δ_{μλ}` for the self-conjugate SU(2) reps) the
gauge-invariant character expectations are

    ⟨χ_{s/2}⟩_t = ∫ χ_{s/2}(g) K_t(g) dg = dim(s)·e^{−t·C₂(s)},

with `dim(s) = s+1` and `C₂(s) = s(s+2)/4` (`RepTheory.SU2`).  This is the
*actual* Wilson measure's character moments — a genuine first piece of the
continuum-existence construction (`docs/track-b-continuum-plan.md` E1),
reusing the A1 exponential (`expNeg`) and the SU(2) Casimir.  It replaces
the trivial functional `ObservableMeasure.trivFunc` with real
finite-volume (single-edge) heat-kernel expectations.

# What is genuine here

  * `wilsonCharExp t s = dim(s)·e^{−t·C₂(s)}` — the heat-kernel expectation
    of the spin-`s/2` character (`CReal`), the moment `⟨χ⟩_t`.
  * `wilsonCharExp_nonneg` — each character moment is `≥ 0`.
  * `wilsonCharExp_unit` — `⟨χ_{triv}⟩_t = ⟨1⟩ = 1`: the measure is
    NORMALIZED (the genuine probability condition).

# What remains (the analytic completion of E1)

  * Full positivity `0 ≤ E(a*·a)` for a general observable `a = Σ c_μ χ_μ`
    — the positive-definiteness of the heat-kernel measure (a Gram-matrix
    condition in the character basis).  This upgrades `wilsonCharExp` to a
    full `ProbFunctional` and is the next E1 sub-step; the heat kernel IS a
    positive measure, so it holds, but proving it from the character data is
    genuine work.
  * The plaquette-coupled finite lattice (E1 → E2) and the
    infinite-volume / RG-consistent family (E2, E3) — see the roadmap.

# Axiom-gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]`.  No `Classical.*`, no `sorryAx`.
-/

import YMGap.RepTheory.SU2
import YMGap.Constructive.SU3CharFactor

namespace YMGap.Continuum.WilsonFunctional

open YMGap.Constructive
open YMGap.RepTheory

/-- `C₂(s) = s(s+2)/4` for SU(2) spin-`s/2`, as a `Q'`. -/
def casimirQ (s : Nat) : Q' := Q'.mkPos (SU2.fourTimesCasimir s : Int) 4 (by decide)

theorem casimirQ_nonneg (s : Nat) : (0 : Q') ≤ casimirQ s := by
  rw [Q'.zero_le_iff_num_nonneg]
  exact Int.natCast_nonneg _

theorem tcasimirQ_nonneg (t : Q') (ht : (0 : Q') ≤ t) (s : Nat) :
    (0 : Q') ≤ t * casimirQ s :=
  Q'.mul_nonneg t (casimirQ s) ht (casimirQ_nonneg s)

/-- **The single-edge heat-kernel Wilson character expectation**
`⟨χ_{s/2}⟩_t = dim(s)·e^{−t·C₂(s)}` — the genuine moment of the SU(2)
heat-kernel measure (`CReal`). -/
def wilsonCharExp (t : Q') (ht : (0 : Q') ≤ t) (s : Nat) : CReal :=
  CReal.mul (CReal.ofQ' (Q'.ofNat (SU2.dimension s)))
    (ExpNeg.expNeg (t * casimirQ s) (tcasimirQ_nonneg t ht s))

/-- Each character moment is `≥ 0` (`dim ≥ 0`, `e^{−·} ≥ 0`). -/
theorem wilsonCharExp_nonneg (t : Q') (ht : (0 : Q') ≤ t) (s : Nat) :
    ExpPos.geRat (wilsonCharExp t ht s) 0 := by
  refine ExpPos.geRat_mono
    (SU3CharFactor.geRat_smul_nonneg (c := Q'.ofNat (SU2.dimension s))
      (SU3CharFactor.ofNat_nonneg _) (expNeg_geRat_zero _ _)) ?_
  -- 0 ≤ dim · 0
  rw [Q'.zero_le_iff_num_nonneg]
  exact Int.natCast_nonneg _

/-! ## Normalization: `⟨1⟩ = 1` (the probability condition)

At the trivial rep `s = 0`: `dim 0 = 1`, `C₂(0) = 0`, `e^{0} = 1`, so the
unit observable has expectation `1`.  We prove `e^{−t·C₂(0)} ≃ e^{0}` via
`expNeg_eqv_congr` (since `t·C₂(0) ≃ 0`), then `1·e^{0} ≃ 1` by the
scalar-mul bounds. -/

theorem tcasimir_zero_eqv (t : Q') : (t * casimirQ 0).eqv 0 := by
  show t.num * 0 * ((0 : Q').den : Int) = 0 * ((t * casimirQ 0).den : Int)
  omega

/-- `⟨1⟩_t ≤ 1`. -/
theorem wilsonCharExp_unit_le (t : Q') (ht : (0 : Q') ≤ t) :
    CReal.leRat (wilsonCharExp t ht 0) 1 := by
  refine CReal.leRat_mono
    (CReal.leRat_smul_nonneg (c := Q'.ofNat (SU2.dimension 0)) (by decide)
      (SU3CharFactor.expNeg_le_one (t * casimirQ 0) (tcasimirQ_nonneg t ht 0))) ?_
  decide

/-- `⟨1⟩_t ≥ 1`. -/
theorem wilsonCharExp_unit_ge (t : Q') (ht : (0 : Q') ≤ t) :
    ExpPos.geRat (wilsonCharExp t ht 0) 1 := by
  have hge0 : ExpPos.geRat (ExpNeg.expNeg (t * casimirQ 0) (tcasimirQ_nonneg t ht 0)) 1 :=
    SU3CharFactor.geRat_of_equiv
      (expNeg_eqv_congr (tcasimirQ_nonneg t ht 0) (by decide) (tcasimir_zero_eqv t))
      SU3CharFactor.geRat_expNeg_zero
  refine ExpPos.geRat_mono
    (SU3CharFactor.geRat_smul_nonneg (c := Q'.ofNat (SU2.dimension 0)) (by decide) hge0) ?_
  decide

/-- **Normalization** `⟨1⟩_t = 1`: the single-edge heat-kernel measure is a
probability measure (`⟨χ_{triv}⟩ = 1`, both bounds). -/
theorem wilsonCharExp_unit (t : Q') (ht : (0 : Q') ≤ t) :
    CReal.leRat (wilsonCharExp t ht 0) 1 ∧ ExpPos.geRat (wilsonCharExp t ht 0) 1 :=
  ⟨wilsonCharExp_unit_le t ht, wilsonCharExp_unit_ge t ht⟩

/-! ## Positivity: the Gram entries and the nonnegative cone

For a real observable `a = Σ_{μ} c_μ χ_μ` the GNS positivity is
`0 ≤ E(a*·a) = Σ_{μν} c_μ c_ν G_{μν}`, where the **Gram matrix**
`G_{μν} = ⟨χ_μ χ_ν⟩_t = Σ_c N^c_{μν} ⟨χ_c⟩_t` (fusion multiplicities times
moments).  By the SU(2) Clebsch–Gordan rule
`χ_a χ_b = χ_{|a−b|} + χ_{|a−b|+2} + ⋯ + χ_{a+b}` (steps of 2), each Gram
entry is a sum of nonnegative moments, hence `G_{μν} ≥ 0`
(`gramEntry_nonneg`).  Therefore `E` is **positive on the cone of
observables with nonnegative coefficients** (`coneExp_nonneg`).

FULL positivity (arbitrary real `c_μ`, where cross terms can be negative)
is `G` being positive-SEMIdefinite — equivalently the heat-kernel measure
being a positive measure (heat-semigroup positivity / the parabolic
maximum principle; equivalently Poisson summation for the SU(2) theta
function).  Even the `2×2` minor is `1 + 3e^{−2t} − 4e^{−3t/2} ≥ 0` (true
by weighted AM–GM).  That PSD theorem is the analytic completion of E1 and
is NOT proved here; the cone positivity below is the genuine partial
result, with the gap precisely the off-cone (sign-indefinite) directions. -/

/-- Lower-bound companion of `leRat_add`: `geRat x a → geRat y b →
geRat (x+y) (a+b)` (mirrors `CReal.leRat_add`, splitting `ε` evenly). -/
theorem geRat_add {x y : CReal} {a b : Q'}
    (hx : ExpPos.geRat x a) (hy : ExpPos.geRat y b) :
    ExpPos.geRat (CReal.add x y) (a + b) := by
  intro ε hε
  have hhε : (0 : Q') < HalfPow.half * ε := ExpNeg.half_mul_pos ε hε
  obtain ⟨Nx, hNx⟩ := hx (HalfPow.half * ε) hhε
  obtain ⟨Ny, hNy⟩ := hy (HalfPow.half * ε) hhε
  refine ⟨max Nx Ny, fun n hn => ?_⟩
  have hnx : Nx ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hny : Ny ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
  have h1 := hNx n hnx
  have h2 := hNy n hny
  have hsum : a + b ≤ (x.approx n + HalfPow.half * ε) + (y.approx n + HalfPow.half * ε) :=
    Q'.add_le_add h1 h2
  have ereg : ((x.approx n + HalfPow.half * ε) + (y.approx n + HalfPow.half * ε)).eqv
      ((x.approx n + y.approx n) + (HalfPow.half * ε + HalfPow.half * ε)) :=
    Q'.regroup (x.approx n) (y.approx n) (HalfPow.half * ε)
  have etwo : ((x.approx n + y.approx n) + (HalfPow.half * ε + HalfPow.half * ε)).eqv
      ((x.approx n + y.approx n) + ε) :=
    Q'.add_eqv_congr_left (x.approx n + y.approx n)
      (HalfPow.half * ε + HalfPow.half * ε) ε (ExpNeg.two_halves ε)
  exact Q'.le_trans' _ _ _ hsum
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv ereg) (Q'.le_of_eqv etwo))

/-- `czero ≥ 0`. -/
theorem geRat_czero : ExpPos.geRat CReal.czero 0 :=
  ExpPos.geRat_of_eventually ⟨0, fun _ _ => Q'.le_refl' 0⟩

/-- A finite sum of nonnegative constructive reals is `≥ 0`. -/
theorem geRat_csum_nonneg {A : Nat → CReal} (h : ∀ i, ExpPos.geRat (A i) 0) :
    ∀ n, ExpPos.geRat (CReal.csum A n) 0
  | 0 => geRat_czero
  | (n + 1) => by
      rw [CReal.csum_succ]
      exact ExpPos.geRat_mono (geRat_add (geRat_csum_nonneg h n) (h n)) (by decide)

/-- `|a − b|` (the lowest spin in the SU(2) fusion `χ_a χ_b`). -/
def fusionLow (a b : Nat) : Nat := max a b - min a b

/-- **The Gram entry** `G_{ab} = ⟨χ_a χ_b⟩_t = Σ_{j=0}^{min a b}
⟨χ_{|a−b|+2j}⟩_t` — the heat-kernel expectation of the character product,
via the SU(2) Clebsch–Gordan decomposition. -/
def gramEntry (t : Q') (ht : (0 : Q') ≤ t) (a b : Nat) : CReal :=
  CReal.csum (fun j => wilsonCharExp t ht (fusionLow a b + 2 * j)) (min a b + 1)

/-- **Each Gram entry is `≥ 0`** (a sum of nonnegative moments). -/
theorem gramEntry_nonneg (t : Q') (ht : (0 : Q') ≤ t) (a b : Nat) :
    ExpPos.geRat (gramEntry t ht a b) 0 :=
  geRat_csum_nonneg (fun _ => wilsonCharExp_nonneg t ht _) _

/-- `E(a*·a)` for `a = Σ_{μ<N} c_μ χ_μ`: the bilinear form
`Σ_{μ,ν<N} c_μ c_ν G_{μν}` (real SU(2): `star = id`, so `a*·a = a²`). -/
def coneExp (t : Q') (ht : (0 : Q') ≤ t) (c : Nat → Q') (N : Nat) : CReal :=
  CReal.csum (fun μ => CReal.csum (fun ν =>
    CReal.mul (CReal.ofQ' (c μ * c ν)) (gramEntry t ht μ ν)) N) N

/-- **Positivity on the nonnegative cone:** `0 ≤ E(a*·a)` for any observable
`a = Σ c_μ χ_μ` with nonnegative coefficients `c_μ ≥ 0` (every term
`c_μ c_ν G_{μν} ≥ 0`).  A genuine partial GNS positivity; full positivity
is the heat-kernel Gram-PSD theorem (see the section note). -/
theorem coneExp_nonneg (t : Q') (ht : (0 : Q') ≤ t)
    (c : Nat → Q') (hc : ∀ i, (0 : Q') ≤ c i) (N : Nat) :
    ExpPos.geRat (coneExp t ht c N) 0 := by
  refine geRat_csum_nonneg (fun μ => geRat_csum_nonneg (fun ν => ?_) N) N
  refine ExpPos.geRat_mono
    (SU3CharFactor.geRat_smul_nonneg (c := c μ * c ν)
      (Q'.mul_nonneg _ _ (hc μ) (hc ν)) (gramEntry_nonneg t ht μ ν)) ?_
  exact Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (hc μ) (hc ν)) (Q'.le_refl' 0)

end YMGap.Continuum.WilsonFunctional

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.WilsonFunctional.wilsonCharExp_nonneg
#print axioms YMGap.Continuum.WilsonFunctional.wilsonCharExp_unit
#print axioms YMGap.Continuum.WilsonFunctional.geRat_csum_nonneg
#print axioms YMGap.Continuum.WilsonFunctional.gramEntry_nonneg
#print axioms YMGap.Continuum.WilsonFunctional.coneExp_nonneg
