/-
The **all-order moment-square positivity** `E(q²) ≥ 0` for the SU(2)
heat-kernel character functional — the analytic completion of the real Wilson
functional — assembled from the existing moment-positivity tower and reduced to
ONE precise, research-grade residual.

# The target

`E` is the SU(2) heat-kernel moment functional with moments
`m_s = ⟨χ_{s/2}⟩_t = (s+1)·a^{s(s+2)}` (`a = e^{−t/4} ∈ (0,1]`).  For a finite
character combination `q = Σ_{μ<N} c_μ χ_μ` the SU(2) Clebsch–Gordan fusion
gives `E(q²) = Σ_{μ,ν<N} c_μ c_ν G_{μν}` with `G_{μν} = Σ_c N^c_{μν} m_c` the
character Gram entry.  The full positivity statement — the GNS energy of every
observable is nonnegative — is the predicate already named on the abstract
moment data:

    MomentSquarePos M  :=  ∀ N c, E(q²) = momentSquare M c N ≥ 0.

Once supplied, the algebraic reduction (the quadratic-form identity
`Q_N(c) = E(q²)`) turns it into the positive-semidefiniteness of the heat-kernel
character Gram matrix at *every* order `N` simultaneously — the all-order PSD of
the real Wilson functional.

# What this file does (all genuine — no fakes)

  * **Finite orders, unconditional.**  At the *quadratic-form* level the SU(2)
    heat-kernel `E(q²) ≥ 0` is already discharged with NO analytic input at
    orders `N = 0,1,2,3`: the `2×2`/`3×3` cases are the LDLᵀ-certified
    `coneExp_psd_two` / `coneExp_psd_three`, transported across the
    Gram↔functional bridge; `N = 0,1` are the empty/diagonal cases.  We
    assemble these into `momentSquarePos_upTo N` — `E(q²) ≥ 0` for every order
    `≤ N`, for the genuinely-closed range `N ≤ 3`.

  * **The single residual, named once.**  The all-order statement is reduced to
    exactly ONE Type-level obligation, `UniformGramSOS M`: a *uniform* supply,
    at every order `N` and every coefficient vector `c`, of a manifestly
    nonnegative certificate `Equiv (momentSquare M c N) W` with `W ≥ 0`.  This
    is precisely the all-order content of the heat-kernel Gram positivity — in
    the determinant picture it is the uniform `Δ_N = S_N²·P_N` factorization
    with `P_N` nonneg-coefficient (the *q-total-positivity* / **P_N wall**),
    whose surviving route is a vicious-walker / Lindström–Gessel–Viennot
    planar-network argument (Pan–Zeng; Sokal).  The perfect-square factor `S_N`
    is *already* produced uniformly by the q-product `SN N`
    (`QHankel.geRat_minor_SN_factored`); the open part is exactly
    `nonnegCoeffs P_N` for all `N`, packaged here as the consumable
    `UniformGramSOS`.

  * **The reduction, a THEOREM.**  `momentSquarePos_of_uniformSOS` proves
    `UniformGramSOS M ⇒ MomentSquarePos M`: transport each certificate through
    `geRat_of_equiv`.  Hence the all-order heat-kernel character Gram PSD is
    conditional on EXACTLY this one named, research-grade-but-known input, with
    everything else proved.  Composing with the algebraic reduction gives
    `gram_psd_of_uniformSOS` (`UniformGramSOS ⇒` PSD at every order) and the
    SU(2)-Wilson specialization `wilson_psd_of_uniformSOS`.

  * **The cone direction, unconditional.**  `UniformGramSOS` restricted to
    nonnegative coefficient vectors holds with no input (`uniformSOS_cone`):
    the genuine analytic content of the residual is exactly the off-cone
    directions.

# Honesty

All-order PSD is **NOT** proved here.  It is *reduced* to the single named
obligation `UniformGramSOS` (equivalently the uniform `nonnegCoeffs P_N` of the
`Δ_N = S_N²·P_N` factorization — the P_N / q-total-positivity wall, known but a
major formalization via the vicious-walker / LGV argument).  The finite orders
`N ≤ 3` are unconditional theorems.  The reduction `UniformGramSOS ⇒` all-order
PSD is a theorem.  No `sorry`/`admit`/new axiom/`Classical.*`/`native_decide`;
the only `decide` uses are inherited from the closed finite-order certificates.

# Axiom-gate

`[propext]` / `[propext, Quot.sound]`.  No `Classical.*`, no `sorryAx`.
-/

import YMGap.Continuum.GramReduction
import YMGap.Continuum.GramReduction3
import YMGap.Continuum.Favard
import YMGap.Continuum.QHankel

namespace YMGap.Continuum.MomentSquarePSD

open YMGap.Constructive
open YMGap.Continuum.Pivot2 (equiv_trans)
open YMGap.Continuum.GramRed (equiv_refl czero_add_eqv)
open YMGap.Continuum.GramRed (MomentData MomentSquarePos MomentSquarePosAt momentSquare
  wilsonMoments momentSquare_eq_coneExp psd_of_momentSquare_nonneg
  wilson_psd_of_momentSquare_nonneg gramForm_pos_cone gram_nonneg)

/-! ## Part 1 — the genuine finite-order result

At the *quadratic-form* level the SU(2) heat-kernel `E(q²) ≥ 0` is already
proved unconditionally through order `N = 3`:

  * `N = 0` : the empty sum `momentSquare M c 0 = 0 ≥ 0`;
  * `N = 1` : the diagonal `c₀²·G₀₀ ≥ 0` (a single nonnegative moment);
  * `N = 2` : `GramRed.coneExp_psd_two` (the `2×2` LDLᵀ certificate, bridged);
  * `N = 3` : `GramRed3.coneExp_psd_three` (the `3×3` LDLᵀ certificate, bridged).

The `N = 2,3` cases live on `WilsonFunctional.coneExp`; via
`momentSquare_eq_coneExp` (they are the SAME `CReal`) they transfer to the
abstract `momentSquare (wilsonMoments t ht)`, i.e. they ARE the per-order
hypothesis `MomentSquarePosAt` discharged. -/

/-- `E(q²) ≥ 0` at order `N = 0` for any moment data: the empty sum is `0`. -/
theorem momentSquarePosAt_zero (M : MomentData) : MomentSquarePosAt M 0 :=
  fun _ => SumOfSquares.geRat_czero

/-- `E(q²) ≥ 0` at order `N = 1` for any moment data: the single diagonal term
`c₀² · G₀₀` is a square coefficient `c₀·c₀ ≥ 0` times the nonnegative moment
`G₀₀`.  `momentSquare M c 1` is `czero + (czero + (c₀c₀)·G₀₀)`; we transport
across the two empty-sum strips to the single nonnegative term. -/
theorem momentSquarePosAt_one (M : MomentData) : MomentSquarePosAt M 1 := by
  intro c
  -- the single surviving term `(c 0 * c 0)·G₀₀ ≥ 0`
  have hterm : ExpPos.geRat
      (CReal.mul (CReal.ofQ' (c 0 * c 0)) (GramRed.gram M 0 0)) 0 := by
    refine ExpPos.geRat_mono
      (SU3CharFactor.geRat_smul_nonneg (c := c 0 * c 0)
        (SumOfSquares.q_mul_self_nonneg (c 0)) (gram_nonneg M 0 0)) ?_
    exact Q'.le_of_eqv (Q'.eqv_symm (QPoly.q_mul_zero (c 0 * c 0)))
  -- momentSquare M c 1 ≃ that single term (strip the two czero leaders)
  refine SU3CharFactor.geRat_of_equiv
    (equiv_trans (czero_add_eqv _) (czero_add_eqv _)) hterm

/-- `E(q²) ≥ 0` at order `N = 2` for the SU(2) heat-kernel moments,
UNCONDITIONALLY — `GramRed.coneExp_psd_two` transported through
`momentSquare = coneExp`. -/
theorem momentSquarePosAt_two (t : Q') (ht : (0 : Q') ≤ t) :
    MomentSquarePosAt (wilsonMoments t ht) 2 := by
  intro c
  exact SU3CharFactor.geRat_of_equiv (momentSquare_eq_coneExp t ht c 2)
    (GramRed.coneExp_psd_two t ht c)

/-- `E(q²) ≥ 0` at order `N = 3` for the SU(2) heat-kernel moments,
UNCONDITIONALLY — `GramRed3.coneExp_psd_three` transported through
`momentSquare = coneExp`. -/
theorem momentSquarePosAt_three (t : Q') (ht : (0 : Q') ≤ t) :
    MomentSquarePosAt (wilsonMoments t ht) 3 := by
  intro c
  exact SU3CharFactor.geRat_of_equiv (momentSquare_eq_coneExp t ht c 3)
    (GramRed3.coneExp_psd_three t ht c)

/-- **The genuinely-closed finite range.**  For the SU(2) heat-kernel moments,
`E(q²) ≥ 0` at *every* order `N ≤ 3`, UNCONDITIONALLY (no analytic input).
This is `MomentSquarePos` restricted to the orders the tower closes outright:
`N = 0,1` (empty/diagonal) and `N = 2,3` (the bridged LDLᵀ certificates). -/
theorem momentSquarePos_upTo (t : Q') (ht : (0 : Q') ≤ t) :
    ∀ N, N ≤ 3 → MomentSquarePosAt (wilsonMoments t ht) N := by
  intro N hN
  match N, hN with
  | 0, _ => exact momentSquarePosAt_zero _
  | 1, _ => exact momentSquarePosAt_one _
  | 2, _ => exact momentSquarePosAt_two t ht
  | 3, _ => exact momentSquarePosAt_three t ht

/-! ## Part 2 — the single residual and the reduction to all-order PSD

The only thing standing between the finite orders and all-order positivity is a
*uniform* (all-`N`) supply of a manifestly-nonnegative certificate for each
`E(q²)`.  We name exactly that, once, as a Type-level obligation.

In the determinant picture this is the uniform `Δ_N = S_N²·P_N` factorization
with `P_N` nonneg-coefficient: the q-product square factor `S_N` is *already*
uniform (`QHankel.SN`, `QHankel.geRat_minor_SN_factored`,
`QHankel.geRat_SN_sq_nonneg`), so the residual is precisely `nonnegCoeffs P_N`
for all `N` — the **P_N / q-total-positivity wall**.  Its surviving proof route
is a vicious-walker / Lindström–Gessel–Viennot planar-network argument
(Pan–Zeng; Sokal): known mathematics, but a major formalization.  We phrase the
consumable abstractly so the reduction is independent of the eventual route. -/

/-- **The single residual (Type-level).**  A *uniform* certificate that
`E(q²) ≥ 0` at every order: for each order `N` and each coefficient vector `c`,
a constructive real `W` together with `W ≥ 0` and `Equiv (momentSquare M c N) W`
— i.e. each GNS energy is exhibited as `Equiv` to a manifestly nonnegative
object, uniformly in `N`.

This packages exactly the all-order content of the heat-kernel Gram positivity.
Concretely the witness is the `Δ_N = S_N²·P_N` certificate
(`(square)·(nonneg-coefficient poly)`) supplied at every order — the uniform
`nonnegCoeffs P_N` of the q-product factorization, the **P_N / q-total-
positivity wall** (vicious-walker / LGV; Pan–Zeng, Sokal).  It is carried as
`Type`-level data (`Σ`/`fun`-valued, not a `Prop` `∃`) so the certificate is
genuine computational content (AGENTS.md Rule 8). -/
def UniformGramSOS (M : MomentData) : Type :=
  (N : Nat) → (c : Nat → Q') →
    (W : CReal) ×' (ExpPos.geRat W 0 ×' CReal.Equiv (momentSquare M c N) W)

/-- **The reduction — a THEOREM.**  `UniformGramSOS M ⇒ MomentSquarePos M`:
the uniform certificate gives `E(q²) ≥ 0` at every order, by transporting each
witness through `geRat_of_equiv`.  So all-order moment-square positivity is
conditional on EXACTLY the single named obligation `UniformGramSOS`. -/
theorem momentSquarePos_of_uniformSOS (M : MomentData) (h : UniformGramSOS M) :
    MomentSquarePos M := by
  intro N c
  obtain ⟨W, hW, hEq⟩ := h N c
  exact SU3CharFactor.geRat_of_equiv hEq hW

/-- **All-order Gram PSD, conditional on the residual.**  Composing the
reduction with the algebraic Gram↔functional reduction: `UniformGramSOS M`
gives positive-semidefiniteness of the character Gram quadratic form at *every*
order `N`. -/
theorem gram_psd_of_uniformSOS (M : MomentData) (h : UniformGramSOS M)
    (N : Nat) (c : Nat → Q') :
    ExpPos.geRat (GramRed.gramForm M c N) 0 :=
  psd_of_momentSquare_nonneg M (momentSquarePos_of_uniformSOS M h) N c

/-- **SU(2) heat-kernel all-order Gram PSD, conditional on the residual.**
Stated directly on `WilsonFunctional.coneExp`: given the single uniform
obligation `UniformGramSOS (wilsonMoments t ht)`, the heat-kernel character
Gram matrix is positive-semidefinite at every order `N`. -/
theorem wilson_psd_of_uniformSOS (t : Q') (ht : (0 : Q') ≤ t)
    (h : UniformGramSOS (wilsonMoments t ht)) (N : Nat) (c : Nat → Q') :
    ExpPos.geRat (WilsonFunctional.coneExp t ht c N) 0 :=
  wilson_psd_of_momentSquare_nonneg t ht (momentSquarePos_of_uniformSOS _ h) N c

/-! ## Part 3 — the cone direction of the residual is unconditional

The nonnegative-cone directions of `UniformGramSOS` carry no analytic content:
when every `c_μ ≥ 0` the certificate is `W := momentSquare M c N` itself, which
is `≥ 0` by `gramForm_pos_cone` (each term `c_μ c_ν G_{μν} ≥ 0`).  This isolates
the genuine analytic content of the residual as exactly the off-cone directions
— the part the vicious-walker / LGV argument is needed for. -/

/-- **The cone restriction of the residual holds with no input.**  For
coefficient vectors with all entries `≥ 0`, the uniform certificate is the form
itself, nonnegative by `gramForm_pos_cone`.  (`momentSquare = gramForm`
definitionally, so the reflexive `Equiv` serves as the witness.) -/
def uniformSOS_cone (M : MomentData) (c : Nat → Q')
    (hc : ∀ i, (0 : Q') ≤ c i) (N : Nat) :
    (W : CReal) ×' (ExpPos.geRat W 0 ×' CReal.Equiv (momentSquare M c N) W) :=
  ⟨momentSquare M c N,
    SU3CharFactor.geRat_of_equiv (GramRed.gramForm_eq_momentSquare M c N)
      (gramForm_pos_cone M c hc N),
    equiv_refl _⟩

/-! ## Part 4 — the proven uniform half: the q-product square factor

The residual is *not* a black box: its perfect-square half is already proved
uniformly.  We re-export the q-product engine to record exactly which half of
the `Δ_N = S_N²·P_N` certificate is closed for ALL `N` and which is the open
`P_N` wall.

  * `sq_factor_nonneg_uniform` — the cyclotomic square factor `(ceval (SN N) a)²`
    is `≥ 0` for *every* order `N` and every `a` (`QHankel.geRat_SN_sq_nonneg`).
    This is the uniform-in-`N` half, proved with NO per-order work.

  * `minor_nonneg_of_PN_nonneg` — the uniform minor reduction: for *every* `N`,
    a single supplied datum `nonnegCoeffs P_N` (plus the factorization identity)
    discharges `Δ_N ≥ 0` at order `N`, the square factor coming from `SN N`.
    The residual `UniformGramSOS` is the all-`N` supply of those `P_N`-data,
    promoted from the minor (`Δ_N`) to the quadratic form (`E(q²)`) via the
    Sylvester/moment bookkeeping documented at the foot of the file. -/

/-- **Uniform square-factor positivity (re-export).**  For every order `N` and
every constructive real `a`, the q-product cyclotomic square factor of the
heat-kernel Gram minor is nonnegative — `(ceval (SN N) a)² ≥ 0`.  The proven
uniform half of the `Δ_N = S_N²·P_N` certificate. -/
theorem sq_factor_nonneg_uniform (N : Nat) (a : CReal) :
    ExpPos.geRat (CReal.mul (ceval (SN N) a) (ceval (SN N) a)) 0 :=
  geRat_SN_sq_nonneg N a

/-- **Uniform minor reduction from `P_N` (re-export).**  For every order `N`:
if the minor `Δ` factors as `(ceval (SN N) a)²·(ceval P a)` with `P`
nonneg-coefficient and `a ≥ 0`, then `Δ ≥ 0`.  Supplying the single datum
`nonnegCoeffs P_N` discharges `Δ_N ≥ 0` at order `N`; the square factor is the
*uniform* `SN N`.  The all-`N` supply of these data is exactly the open `P_N`
wall inside `UniformGramSOS`. -/
theorem minor_nonneg_of_PN_nonneg (N : Nat) {Δ : CReal} (P : QPoly.Poly)
    {a : CReal} (ha : ExpPos.geRat a 0) (hP : nonnegCoeffs P)
    (hΔ : CReal.Equiv Δ
      (CReal.mul (CReal.mul (ceval (SN N) a) (ceval (SN N) a)) (ceval P a))) :
    ExpPos.geRat Δ 0 :=
  geRat_minor_SN_factored N P ha hP hΔ

end YMGap.Continuum.MomentSquarePSD

/-! ## OPEN obligation (the single named residual) and what surrounds it

**Proved here, unconditional.**
  * `momentSquarePos_upTo` — `E(q²) ≥ 0` for the SU(2) heat-kernel at every
    order `N ≤ 3` (empty/diagonal + the bridged `2×2`/`3×3` LDLᵀ certificates).
  * `uniformSOS_cone` — the nonnegative-cone directions of the residual, for
    any moment data, with no analytic input.
  * `sq_factor_nonneg_uniform`, `minor_nonneg_of_PN_nonneg` — the uniform-in-`N`
    half of the `Δ_N = S_N²·P_N` certificate (the perfect-square factor `S_N`,
    produced by the q-product `SN N`).

**Proved here, the reduction (THEOREM).**
  * `momentSquarePos_of_uniformSOS : UniformGramSOS M ⇒ MomentSquarePos M`, and
    its compositions `gram_psd_of_uniformSOS` / `wilson_psd_of_uniformSOS` —
    the single named residual implies all-order character Gram PSD.

**OPEN — the single residual.**  `UniformGramSOS M`: a uniform (all-`N`) supply
of a manifestly nonnegative certificate `Equiv (momentSquare M c N) W`, `W ≥ 0`.
Concretely this is the uniform `nonnegCoeffs P_N` of the factorization
`Δ_N = S_N²·P_N` — the **P_N wall / q-total-positivity** of the heat-kernel
q-Hankel determinant.  This is *known mathematics*: it is the statement that the
heat-kernel character Gram matrix is totally nonnegative (equivalently the
moment functional is positive), provable by a Lindström–Gessel–Viennot /
vicious-walker planar-network argument (Pan–Zeng; Sokal) — but it is a major
formalization, not closed here.  Exact computer algebra verifies the
factorization (and `P_N` nonnegativity) through `N = 6/8`; that is strong
per-order evidence, not an `N`-indexed theorem.

**OPEN — the surrounding bookkeeping (no new mathematics).**  Turning a uniform
*minor* nonnegativity `Δ_N ≥ 0 ∀N` into the uniform *quadratic-form*
`momentSquare ≥ 0` (the residual `UniformGramSOS`) needs (i) the order-`N`
moment-bridge — that the CReal Gram minor built from the `expNeg` moments equals
`ceval (Δ_N list) (e^{−t/4})` (the order-`N` analogue of the proven `N = 2`
moment-bridge) — and (ii) the Sylvester step `Δ_N ≥ 0 ∀N ⟹` Gram-PSD ∀N.  Both
are mechanical; the genuine wall is the uniform `P_N` nonnegativity above.

All-order moment-square positivity is therefore **NOT** closed: it is reduced to
the single named obligation `UniformGramSOS` (= the P_N / q-total-positivity /
vicious-walker wall), with the finite orders `N ≤ 3` unconditional and the
reduction a theorem.
-/

#print axioms YMGap.Continuum.MomentSquarePSD.momentSquarePosAt_zero
#print axioms YMGap.Continuum.MomentSquarePSD.momentSquarePosAt_one
#print axioms YMGap.Continuum.MomentSquarePSD.momentSquarePosAt_two
#print axioms YMGap.Continuum.MomentSquarePSD.momentSquarePosAt_three
#print axioms YMGap.Continuum.MomentSquarePSD.momentSquarePos_upTo
#print axioms YMGap.Continuum.MomentSquarePSD.momentSquarePos_of_uniformSOS
#print axioms YMGap.Continuum.MomentSquarePSD.gram_psd_of_uniformSOS
#print axioms YMGap.Continuum.MomentSquarePSD.wilson_psd_of_uniformSOS
#print axioms YMGap.Continuum.MomentSquarePSD.uniformSOS_cone
#print axioms YMGap.Continuum.MomentSquarePSD.sq_factor_nonneg_uniform
#print axioms YMGap.Continuum.MomentSquarePSD.minor_nonneg_of_PN_nonneg
