/-
Track B / R2 — the **CUBING TRICK** for the matched-retune DERIVATIVE magnitude
frontier: eliminate the irrational cube-root `ρ` from the per-step derivative bound by
CUBING, reducing the `BoxRatioDerivative` obligation to a pure-`Q'` cubed inequality
(no `ρ`, no `CReal`, no bracket explosion), and bridge that cubed `Q'` inequality back
to the genuine `BoxRatioDerivative.derivative` field via cube monotonicity.

# Why this module exists — the cube-root is the only irrational, so cube it away

The matched kernel coefficient is `ĉ_s = (s+1)·ρ^{C₄(s)}` with `ρ³ = R = g₁/(2 g₀)` a
positive RATIONAL (`g_s = bondMovedCoeff N w 2 s`).  The ONLY irrational datum in the
whole matched tower is the cube root `ρ = ∛R`.  The per-step DERIVATIVE bound the engine
consumes is

    δ_k  =  (g_{k+1}·ĉ_k)/(g_k·ĉ_{k+1}) − 1   ≤   C·u³·(2k+3),     u = 1 − w,

which (clearing the positive denominator) is the numerator inequality

    g_{k+1}·ĉ_k  ≤  (1 + C·u³·(2k+3))·(g_k·ĉ_{k+1}).

Every quantity here is positive, so the inequality is EQUIVALENT to its CUBE, and the
cube of the genuine matched coefficient is RATIONAL:

    (ĉ_s)³  =  ((s+1)·ρ^{C₄(s)})³  =  (s+1)³·(ρ³)^{C₄(s)}  =  (s+1)³·R^{C₄(s)},

so cubing ELIMINATES `ρ` entirely (`coeffMatched_cube_rational` below).  The derivative
bound thus reduces to a PURE-`Q'` cubed inequality in the self-fusion box sums and the
rational `R = g₁/(2 g₀)` — exactly the discrete-local-CLT content, with the foundational
cube-root obstruction removed.

# What is GENUINELY PROVED here (axiom-clean)

THE Q' CUBE ALGEBRA (proved):
  * `qcube` — the `Q'` cube `a³ = a·a·a`; `qcube_mul` — `(a·b)³ ≃ a³·b³`;
    `qcube_nonneg` / `qcube_pos` — sign laws.

THE ρ-ELIMINATION (proved — the heart of the cubing trick):
  * `crealPowNat_cube_rational` — `(ρ^c)³ ≃ ofQ'(R^c)` from the cube identity
    `ρ³ ≃ ofQ' R` (via the shared `crealPowNat` exponent laws).
  * `coeffMatched_cube_rational` — **the genuine matched coefficient, CUBED, is
    RATIONAL**: `(coeffMatched ρ s)³ ≃ ofQ'((s+1)³·R^{C₄(s)})`.  This is the statement
    that cubing removes the only irrational factor; `ρ` is gone.

THE CUBING BRIDGE (proved — the deliverable that always holds):
  * `le_of_qcube_le` — the pure-`Q'` cube-monotone step `x³ ≤ y³ ⟹ x ≤ y` (re-export of
    `le_of_cube_le_cube`); `qcube_mul` packages the cube on PRODUCTS.
  * `CubedDerivativeIneq` — the pure-`Q'` CUBED derivative residual on the proved box
    form `g_s` and the DECOMPOSED+DEPTH brackets `coeffMatchedHi/Lo R hR D` of `ĉ`,
    WINDOWED to the active window `1 ≤ k ≤ S`:

        [g_{k+1}·ĉ_k^{hi}]³  ≤  [(1 + C·u³·(2k+3))·(g_k·ĉ_{k+1}^{lo})]³   (1 ≤ k ≤ S),

    NO `ρ`, NO `CReal` — a finite rational inequality about the self-fusion box sums.
    Windowed because (exact arithmetic) `δ_k/(u³·(2k+3))` grows unbounded in the tail, so
    the unwindowed `∀ k` form is false-as-stated.
  * `cubed_derivative_implies_box` — **THE BRIDGE**: a `CubedDerivativeIneq` witness
    inhabits `BoxRatioDerivative N w hw R hR D C S` (its `derivative` field), by cube
    monotonicity per active mode (threading `k ≤ S`).  The cubing has ELIMINATED `ρ`: the
    input is a pure-`Q'`
    cubed inequality, the output is the genuine bracketed derivative obligation.
  * `boxRatioDerivative_of_cubed` — alias producing the `BoxRatioDerivative` carrier from
    the cubed residual; `frontier_quotientCert` then fires off the resulting per-step data.

# NAMED OPEN — the cubed local CLT (honest scope)

  * `CubedDerivativeIneq` is NOT inhabited here.  It is the genuine discrete-local-CLT
    content, now PURE-`Q'` (the cubing trick removed the cube root), and WINDOWED to the
    active window `1 ≤ k ≤ S`.  Reconnaissance (the box-inequality study, exact
    arithmetic) confirms the EXACT inequality `δ_k ≤ C·u³·(2k+3)` is TRUE with `C = 1/2`
    only on the ACTIVE WINDOW `k ≤ S(τ)` (`S ≍ τ^{−1/2}`): in the TAIL `δ_k/(u³·(2k+3))`
    grows unbounded (fails near `y ≈ 44`), so the unwindowed `∀ k` form is
    false-as-stated — the field is windowed by `k ≤ S` to be the TRUE statement.  On the
    DECOMPOSED+DEPTH brackets it further requires a `w`-growing bisection depth `D` (the
    bounded bracket slack absorbed by the explicit `C·u³·(2k+3)` margin), so it is NOT
    inhabitable at a fixed `D` uniformly in `w`.  We name the windowed cubed `Q'`
    inequality precisely and PROVE the bridge from it to (the windowed)
    `BoxRatioDerivative`; we do NOT inhabit the cubed inequality.  This is the technical
    crossover lever — NOT a 4D Yang–Mills mass gap.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic, the cube-order lemmas of `CubeRoot`, the shared `crealPowNat`
exponent laws, reused `Q'` order / `divPos` lemmas.  Every load-bearing declaration is
gated with `#print axioms`; permitted output is `propext` / `Quot.sound` only.  No
`Classical.*`, no `native_decide` (only `decide` on decidable facts), no `sorry`.  All
witnesses are `Type`-level data.
-/

import YMGap.Continuum.FusionRDFactor
import YMGap.Continuum.MatchedRetune
import YMGap.Continuum.MatchedRetuneBridge
import YMGap.Continuum.MatchedRetuneFrontier
import YMGap.Constructive.CubeRoot

namespace YMGap.Continuum.CubedDerivative

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BondMovingMoment
open YMGap.Continuum.FusionRDFactor
open YMGap.Continuum.MatchedRetune
open YMGap.Continuum.MatchedRetuneBridge
open YMGap.Continuum.MatchedRetuneFrontier
open YMGap.Continuum.CRealContinuumAlg

/-! ## 0. The `Q'` cube and its algebra -/

/-- The `Q'` cube `a³ = (a·a)·a` (matching the `CubeRoot` cube shape `a*a*a`). -/
def qcube (a : Q') : Q' := a * a * a

/-- `0 ≤ a → 0 ≤ a³`. -/
theorem qcube_nonneg {a : Q'} (ha : (0 : Q') ≤ a) : (0 : Q') ≤ qcube a :=
  Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ ha ha) ha

/-- `0 < a → 0 < a³`. -/
theorem qcube_pos {a : Q'} (ha : (0 : Q') < a) : (0 : Q') < qcube a :=
  Q'.mul_pos (Q'.mul_pos ha ha) ha

/-- **`(a·b)³ ≃ a³·b³`** — the cube distributes over a product.  PROOF: regroup the six
factors `((a·b)·(a·b))·(a·b)` into `(a·a·a)·(b·b·b)` via commutativity/associativity. -/
theorem qcube_mul (a b : Q') : (qcube (a * b)).eqv (qcube a * qcube b) := by
  show (((a * b) * (a * b)) * (a * b)).eqv ((a * a * a) * (b * b * b))
  -- step 1: (a·b)·(a·b) ≃ (a·a)·(b·b)
  have h1 : (((a * b) * (a * b)) * (a * b)).eqv (((a * a) * (b * b)) * (a * b)) :=
    Q'.mul_eqv_congr_right _ _ (a * b)
      (FusionResidualBound.mul_four_regroup a b a b)
  -- step 2: ((a·a)·(b·b))·(a·b) ≃ ((a·a)·a)·((b·b)·b)
  refine Q'.eqv_trans _ _ _ h1 ?_
  exact FusionResidualBound.mul_four_regroup (a * a) (b * b) a b

/-- `qcube` is monotone-reflecting: `0 ≤ x → 0 ≤ y → x³ ≤ y³ → x ≤ y` (the
cube-order reflection of `CubeRoot.le_of_cube_le_cube` on the `qcube` shape). -/
theorem le_of_qcube_le {x y : Q'} (hx : (0 : Q') ≤ x) (hy : (0 : Q') ≤ y)
    (h : qcube x ≤ qcube y) : x ≤ y :=
  CReal.le_of_cube_le_cube hx hy h

/-- **`CReal` four-factor regroup** `(A·B)·(C·D) ≃ (A·C)·(B·D)` (pointwise mirror of the
`Q'` `mul_four_regroup`), via `cmul_assoc`/`cmul_comm`. -/
theorem cmul_four_regroup (A B C D : CReal) :
    CReal.Equiv (CReal.mul (CReal.mul A B) (CReal.mul C D))
      (CReal.mul (CReal.mul A C) (CReal.mul B D)) := by
  refine Pivot2.equiv_trans (CRealAlg.cmul_assoc A B (CReal.mul C D)) ?_
  refine Pivot2.equiv_trans ?_ (CReal.Equiv.symm (CRealAlg.cmul_assoc A C (CReal.mul B D)))
  refine Pivot2.mul_congr_right ?_
  -- B·(C·D) ≃ (B·C)·D ≃ (C·B)·D ≃ C·(B·D)
  refine Pivot2.equiv_trans (CReal.Equiv.symm (CRealAlg.cmul_assoc B C D)) ?_
  refine Pivot2.equiv_trans (Pivot2.mul_congr_left (CRealAlg.cmul_comm B C)) ?_
  exact CRealAlg.cmul_assoc C B D

/-! ## 1. The ρ-ELIMINATION — cubing removes the only irrational factor

`ρ³ ≃ ofQ' R` (the carrier cube identity).  Then `(ρ^c)³ = ρ^{3c} = (ρ³)^c ≃ ofQ'(R^c)`,
and the genuine matched coefficient `ĉ_s = (s+1)·ρ^{C₄(s)}` cubes to the RATIONAL
`(s+1)³·R^{C₄(s)}`: the cube root is gone. -/

/-- **`(ρ^c)³ ≃ ofQ'(R^c)`** given the cube identity `ρ³ ≃ ofQ' R`.  PROOF:
`(ρ^c)³ = ρ^c·ρ^c·ρ^c ≃ ρ^{c+c+c} = ρ^{3c}`, and `ρ^{3c} ≃ ofQ'(R^c)` by
`crealPowNat_mul3`.  The cube collapses the triple `ρ`-power to the rational `R`-power. -/
theorem crealPowNat_cube_rational (x : CReal) (R : Q')
    (hcube : CReal.Equiv (crealPowNat x 3) (CReal.ofQ' R)) (c : Nat) :
    CReal.Equiv
      (CReal.mul (CReal.mul (crealPowNat x c) (crealPowNat x c)) (crealPowNat x c))
      (CReal.ofQ' (qpow R c)) := by
  -- (x^c · x^c) · x^c ≃ x^{c+c} · x^c ≃ x^{(c+c)+c} = x^{3c}
  have h1 : CReal.Equiv (CReal.mul (crealPowNat x c) (crealPowNat x c))
      (crealPowNat x (c + c)) := CReal.Equiv.symm (crealPowNat_add x c c)
  have h2 : CReal.Equiv
      (CReal.mul (CReal.mul (crealPowNat x c) (crealPowNat x c)) (crealPowNat x c))
      (CReal.mul (crealPowNat x (c + c)) (crealPowNat x c)) :=
    CRealContinuumAlg.cmul_congr_left h1
  have h3 : CReal.Equiv (CReal.mul (crealPowNat x (c + c)) (crealPowNat x c))
      (crealPowNat x ((c + c) + c)) := CReal.Equiv.symm (crealPowNat_add x (c + c) c)
  have h3c : (c + c) + c = 3 * c := by omega
  have h4 : CReal.Equiv (crealPowNat x ((c + c) + c)) (CReal.ofQ' (qpow R c)) := by
    rw [h3c]; exact crealPowNat_mul3 x R hcube c
  exact CReal.Equiv.trans h2 (CReal.Equiv.trans h3 h4)

/-- **THE ρ-ELIMINATION: the cubed genuine matched coefficient is RATIONAL.**  For
`ρ = ∛R`, `(coeffMatched ρ s)³ ≃ ofQ'((s+1)³·R^{C₄(s)})`.  The cube removes the only
irrational factor (the cube root `ρ`), leaving the rational `dimQ s ³ · R^{C₄(s)}`.
PROOF: `coeffMatched ρ s = ofQ'(dimQ s)·ρ^{C₄ s}`; cube both factors
(`qcube` of `ofQ'` is `ofQ'` of the rational cube; `crealPowNat_cube_rational` for the
`ρ`-power), regroup the six factors, and fold the two rational pieces by `cofQ'_mul`. -/
theorem coeffMatched_cube_rational (R : Q') (hR : (0 : Q') < R) (s : Nat) :
    CReal.Equiv
      (CReal.mul (CReal.mul (coeffMatched (CReal.cbrtFrom R hR) s)
          (coeffMatched (CReal.cbrtFrom R hR) s)) (coeffMatched (CReal.cbrtFrom R hR) s))
      (CReal.ofQ' (qcube (dimQ s) * qpow R (c4 s))) := by
  have hcube : CReal.Equiv (crealPowNat (CReal.cbrtFrom R hR) 3) (CReal.ofQ' R) :=
    cbrt_crealPowNat_cube R hR
  -- abbreviations (definitional: coeffMatched ρ s = d · p)
  let d : CReal := CReal.ofQ' (dimQ s)
  let p : CReal := crealPowNat (CReal.cbrtFrom R hR) (c4 s)
  -- coeffMatched ρ s = d · p ; cube = ((d·p)·(d·p))·(d·p) ≃ (d·d·d)·(p·p·p)
  show CReal.Equiv (CReal.mul (CReal.mul (CReal.mul d p) (CReal.mul d p)) (CReal.mul d p))
      (CReal.ofQ' (qcube (dimQ s) * qpow R (c4 s)))
  -- regroup six factors into (d·d·d)·(p·p·p)
  have hreg1 : CReal.Equiv
      (CReal.mul (CReal.mul (CReal.mul d p) (CReal.mul d p)) (CReal.mul d p))
      (CReal.mul (CReal.mul (CReal.mul d d) (CReal.mul p p)) (CReal.mul d p)) :=
    Pivot2.mul_congr_left (cmul_four_regroup d p d p)
  have hreg2 : CReal.Equiv
      (CReal.mul (CReal.mul (CReal.mul d d) (CReal.mul p p)) (CReal.mul d p))
      (CReal.mul (CReal.mul (CReal.mul d d) d) (CReal.mul (CReal.mul p p) p)) :=
    cmul_four_regroup (CReal.mul d d) (CReal.mul p p) d p
  refine CReal.Equiv.trans (CReal.Equiv.trans hreg1 hreg2) ?_
  -- (d·d·d) ≃ ofQ'(dimQ s ³) ; (p·p·p) ≃ ofQ'(R^{C₄ s})
  have hd : CReal.Equiv (CReal.mul (CReal.mul d d) d) (CReal.ofQ' (qcube (dimQ s))) := by
    show CReal.Equiv (CReal.mul (CReal.mul (CReal.ofQ' (dimQ s)) (CReal.ofQ' (dimQ s)))
        (CReal.ofQ' (dimQ s))) (CReal.ofQ' (dimQ s * dimQ s * dimQ s))
    refine CReal.Equiv.trans
      (CRealContinuumAlg.cmul_congr_left (CReal.Equiv.symm (cofQ'_mul (dimQ s) (dimQ s)))) ?_
    exact CReal.Equiv.symm (cofQ'_mul (dimQ s * dimQ s) (dimQ s))
  have hp : CReal.Equiv (CReal.mul (CReal.mul p p) p) (CReal.ofQ' (qpow R (c4 s))) :=
    crealPowNat_cube_rational (CReal.cbrtFrom R hR) R hcube (c4 s)
  -- (ofQ' A)·(ofQ' B) ≃ ofQ'(A·B)
  refine CReal.Equiv.trans (Pivot2.mul_congr hd hp) ?_
  exact CReal.Equiv.symm (cofQ'_mul (qcube (dimQ s)) (qpow R (c4 s)))

/-- **`qcube (qpow x j) ≃ qpow x (3·j)`** — cubing a `Q'` power triples the exponent. -/
theorem qcube_qpow (x : Q') (j : Nat) : (qcube (qpow x j)).eqv (qpow x (3 * j)) := by
  show ((qpow x j * qpow x j) * qpow x j).eqv (qpow x (3 * j))
  have e1 : ((qpow x j * qpow x j) * qpow x j).eqv (qpow x (j + j) * qpow x j) :=
    Q'.mul_eqv_congr_right _ _ (qpow x j) (Q'.eqv_symm (HeatKernelRGStep.qpow_add x j j))
  have e2 : (qpow x (j + j) * qpow x j).eqv (qpow x ((j + j) + j)) :=
    Q'.eqv_symm (HeatKernelRGStep.qpow_add x (j + j) j)
  have e3 : (j + j) + j = 3 * j := by omega
  rw [e3] at e2
  exact Q'.eqv_trans _ _ _ e1 e2

/-- **The cubed UPPER bracket is an explicit rational** (ρ-free):
`(coeffMatchedHi R hR D s)³ ≃ (s+1)³·R^{3·⌊C₄ s/3⌋}·rhoHi^{3·(C₄ s%3)}`.  Every factor is
rational — the cube root never appears.  This makes the cubed residual a CONCRETE rational
inequality. -/
theorem qcube_coeffMatchedHi (R : Q') (hR : (0 : Q') < R) (D s : Nat) :
    (qcube (coeffMatchedHi R hR D s)).eqv
      (qcube (dimQ s) * qpow R (3 * (c4 s / 3)) * qpow (rhoHi R hR D) (3 * (c4 s % 3))) := by
  show (qcube (dimQ s * qpow R (c4 s / 3) * qpow (rhoHi R hR D) (c4 s % 3))).eqv
      (qcube (dimQ s) * qpow R (3 * (c4 s / 3)) * qpow (rhoHi R hR D) (3 * (c4 s % 3)))
  -- qcube ((A·B)·C) ≃ qcube(A·B)·qcube C ≃ (qcube A·qcube B)·qcube C
  refine Q'.eqv_trans _ _ _
    (qcube_mul (dimQ s * qpow R (c4 s / 3)) (qpow (rhoHi R hR D) (c4 s % 3))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ (qcube (qpow (rhoHi R hR D) (c4 s % 3)))
      (qcube_mul (dimQ s) (qpow R (c4 s / 3)))) ?_
  -- replace qcube of the two qpow's by the tripled-exponent powers
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left _ _ _ (qcube_qpow (rhoHi R hR D) (c4 s % 3))) ?_
  exact Q'.mul_eqv_congr_right _ _ _
    (Q'.mul_eqv_congr_left _ _ _ (qcube_qpow R (c4 s / 3)))

/-- **The cubed LOWER bracket is an explicit rational** (ρ-free):
`(coeffMatchedLo R hR D s)³ ≃ (s+1)³·R^{3·⌊C₄ s/3⌋}·rhoLo^{3·(C₄ s%3)}`. -/
theorem qcube_coeffMatchedLo (R : Q') (hR : (0 : Q') < R) (D s : Nat) :
    (qcube (coeffMatchedLo R hR D s)).eqv
      (qcube (dimQ s) * qpow R (3 * (c4 s / 3)) * qpow (rhoLo R hR D) (3 * (c4 s % 3))) := by
  show (qcube (dimQ s * qpow R (c4 s / 3) * qpow (rhoLo R hR D) (c4 s % 3))).eqv
      (qcube (dimQ s) * qpow R (3 * (c4 s / 3)) * qpow (rhoLo R hR D) (3 * (c4 s % 3)))
  refine Q'.eqv_trans _ _ _
    (qcube_mul (dimQ s * qpow R (c4 s / 3)) (qpow (rhoLo R hR D) (c4 s % 3))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ (qcube (qpow (rhoLo R hR D) (c4 s % 3)))
      (qcube_mul (dimQ s) (qpow R (c4 s / 3)))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left _ _ _ (qcube_qpow (rhoLo R hR D) (c4 s % 3))) ?_
  exact Q'.mul_eqv_congr_right _ _ _
    (Q'.mul_eqv_congr_left _ _ _ (qcube_qpow R (c4 s / 3)))

/-! ## 2. The CUBED derivative residual — the pure-`Q'` content (ρ-free)

With the cube-root eliminated, the derivative bound is a pure-`Q'` cubed inequality on the
proved box form `g_s = bondMovedCoeff N w 2 s` and the DECOMPOSED+DEPTH brackets
`coeffMatchedHi/Lo R hR D` of `ĉ`.  We carry it as a `Type`-level obligation. -/

/-- **THE CUBED DERIVATIVE residual (pure `Q'`, ρ-free) — WINDOWED to `k ≤ S`.**  With the
explicit constant `C`, the moving cutoff `S : Nat`, and the target deviation
`D_k = C·u³·(2k+3)` (`u = 1 − w`), the CUBED box numerator inequality on the active window
`1 ≤ k ≤ S`:

    [g_{k+1}·ĉ_k^{hi}]³  ≤  [(1 + C·u³·(2k+3))·(g_k·ĉ_{k+1}^{lo})]³,

`g_s` in closed `(r,d)` box form, `ĉ^{hi/lo} = coeffMatchedHi/Lo R hR D` the rational
decomposed+depth brackets.  Equivalent (all quantities positive) to the LINEAR
`BoxRatioDerivative.derivative` field — the cube is taken to render the matched coefficient
RATIONAL (cube root eliminated).

WINDOWING (exact-arithmetic correction).  The per-step ratio `δ_k/(u³·(2k+3))` is bounded
only on the ACTIVE WINDOW `k ≤ S(τ)` (`S ≍ τ^{−1/2}`, where `y_k ≲ O(1)`); in the TAIL it
grows UNBOUNDED (it fails near `y ≈ 44`).  So the unwindowed `∀ k` form is FALSE-as-stated;
the field is guarded by `k ≤ S`, which is the TRUE statement.  NOT inhabited here (the cubed
discrete local CLT). -/
structure CubedDerivativeIneq (N : Nat) (w : Q') (hw : (0 : Q') < w)
    (R : Q') (hR : (0 : Q') < R) (D : Nat) (C : Q') (S : Nat) : Type where
  /-- The CUBED box derivative inequality on the active window `1 ≤ k ≤ S`. -/
  cubed : ∀ k, 1 ≤ k → k ≤ S →
    qcube (bondMovedCoeff N w 2 (k + 1) * coeffMatchedHi R hR D k)
      ≤ qcube (((1 : Q') + C * (((1 : Q') - w) * ((1 : Q') - w) * ((1 : Q') - w))
          * Q'.ofNat (2 * k + 3))
        * (bondMovedCoeff N w 2 k * coeffMatchedLo R hR D (k + 1)))

/-! ## 3. THE CUBING BRIDGE — cubed `Q'` inequality ⟹ `BoxRatioDerivative`

The bridge cubes nothing itself: it UN-cubes.  Given the pure-`Q'` cubed inequality
(ρ already eliminated), cube monotonicity (`le_of_qcube_le`) recovers the LINEAR
`BoxRatioDerivative.derivative` field — provided both sides are nonnegative, which they
are (the `g`'s are nonnegative box sums, the brackets are positive, the slack factor
`1 + C·u³·(2k+3) ≥ 0`).  This is the deliverable that ALWAYS holds: the cubing trick has
removed the cube root, and this wire connects the resulting pure-`Q'` cubed obligation to
the genuine bracketed derivative obligation. -/

/-- Nonnegativity of the LHS `g_{k+1}·ĉ_k^{hi}`. -/
theorem box_lhs_nonneg (N : Nat) {w : Q'} (hw : (0 : Q') ≤ w)
    (R : Q') (hR : (0 : Q') < R) (D k : Nat) :
    (0 : Q') ≤ bondMovedCoeff N w 2 (k + 1) * coeffMatchedHi R hR D k :=
  Q'.mul_nonneg _ _ (bondMovedCoeff_nonneg N hw 2 (k + 1))
    (Q'.le_of_lt (coeffMatchedHi_pos R hR D k))

/-- Nonnegativity of the RHS `(1 + C·u³·(2k+3))·(g_k·ĉ_{k+1}^{lo})` for `C·u³·(2k+3) ≥ 0`. -/
theorem box_rhs_nonneg (N : Nat) {w : Q'} (hw : (0 : Q') ≤ w)
    (R : Q') (hR : (0 : Q') < R) (D k : Nat) {C : Q'}
    (hslack : (0 : Q') ≤ C * (((1 : Q') - w) * ((1 : Q') - w) * ((1 : Q') - w))
      * Q'.ofNat (2 * k + 3)) :
    (0 : Q') ≤ ((1 : Q') + C * (((1 : Q') - w) * ((1 : Q') - w) * ((1 : Q') - w))
        * Q'.ofNat (2 * k + 3))
      * (bondMovedCoeff N w 2 k * coeffMatchedLo R hR D (k + 1)) := by
  have h1D : (0 : Q') ≤ (1 : Q') + C * (((1 : Q') - w) * ((1 : Q') - w) * ((1 : Q') - w))
      * Q'.ofNat (2 * k + 3) :=
    Q'.le_trans' _ _ _ (by decide : (0 : Q') ≤ 1) (Q'.add_le_self_of_nonneg 1 _ hslack)
  refine Q'.mul_nonneg _ _ h1D ?_
  exact Q'.mul_nonneg _ _ (bondMovedCoeff_nonneg N hw 2 k)
    (Q'.le_of_lt (coeffMatchedLo_pos R hR D (k + 1)))

/-- **THE CUBING BRIDGE.**  A `CubedDerivativeIneq` witness (the pure-`Q'` cubed
derivative residual, with the cube root ELIMINATED) inhabits `BoxRatioDerivative N w hw R
hR D C` (the genuine bracketed `derivative` field).

PROOF.  For each active mode `1 ≤ k`, the field requires the LINEAR inequality
`g_{k+1}·ĉ_k^{hi} ≤ (1 + C·u³·(2k+3))·(g_k·ĉ_{k+1}^{lo})`.  Both sides are nonnegative
(`box_lhs_nonneg`, `box_rhs_nonneg`), so by cube monotonicity (`le_of_qcube_le`) it
suffices to prove the CUBED inequality — which is exactly the `cubed` field.  The cubing
trick is what makes that cubed inequality pure-`Q'` (the matched coefficient cubes to the
rational `(s+1)³·R^{C₄(s)}`; `ρ` is gone). -/
def cubed_derivative_implies_box (N : Nat) (w : Q') (hw : (0 : Q') < w) (hw1 : w ≤ (1 : Q'))
    (R : Q') (hR : (0 : Q') < R) (D : Nat) (C : Q') (hC : (0 : Q') ≤ C) (S : Nat)
    (ineq : CubedDerivativeIneq N w hw R hR D C S) :
    BoxRatioDerivative N w hw R hR D C S where
  derivative := by
    intro k hk hkS
    have htau_nn : (0 : Q') ≤ (1 : Q') - w := Q'.sub_nonneg_of_le hw1
    have hu3_nn : (0 : Q') ≤ ((1 : Q') - w) * ((1 : Q') - w) * ((1 : Q') - w) :=
      Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ htau_nn htau_nn) htau_nn
    have hslack : (0 : Q') ≤ C * (((1 : Q') - w) * ((1 : Q') - w) * ((1 : Q') - w))
        * Q'.ofNat (2 * k + 3) :=
      Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ hC hu3_nn)
        (HeatKernelRGStep.zero_le_ofNat _)
    refine le_of_qcube_le
      (box_lhs_nonneg N (Q'.le_of_lt hw) R hR D k)
      (box_rhs_nonneg N (Q'.le_of_lt hw) R hR D k hslack) ?_
    exact ineq.cubed k hk hkS

/-- **The carrier alias.**  Produce the `BoxRatioDerivative` carrier directly from the
cubed residual; downstream `perstep_le_of_box` then supplies the per-step derivative bound
`δ_k ≤ C·u³·(2k+3)` and `frontier_quotientCert` fires the engine. -/
def boxRatioDerivative_of_cubed (N : Nat) (w : Q') (hw : (0 : Q') < w) (hw1 : w ≤ (1 : Q'))
    (R : Q') (hR : (0 : Q') < R) (D : Nat) (C : Q') (hC : (0 : Q') ≤ C) (S : Nat)
    (ineq : CubedDerivativeIneq N w hw R hR D C S) :
    BoxRatioDerivative N w hw R hR D C S :=
  cubed_derivative_implies_box N w hw hw1 R hR D C hC S ineq

/-! ## 4. The conditional per-step derivative bound through the bridge

Closing the loop to the engine: from the cubed residual (cube root eliminated) plus the
matched-carrier brackets, the per-step increment `δ_k ≤ C·u³·(2k+3)` on the active window
— the exact `cumsum`-summand the matched-retune engine telescopes.  This is
`perstep_le_of_box` applied to the `BoxRatioDerivative` carrier the bridge produces. -/

/-- **The per-step derivative bound from the cubed residual.**  Composing the bridge
`cubed_derivative_implies_box` with `MatchedRetuneFrontier.perstep_le_of_box`: from the
pure-`Q'` cubed inequality and a sequence `chat` sandwiched by the brackets
`coeffMatchedLo ≤ chat ≤ coeffMatchedHi`, the matched increment is `≤ C·u³·(2k+3)` on
`1 ≤ k`.  The cube root has been eliminated end-to-end. -/
theorem perstep_le_of_cubed (N : Nat) {w : Q'} (hw : (0 : Q') < w) (hw1 : w ≤ (1 : Q'))
    (R : Q') (hR : (0 : Q') < R) (D : Nat) (C : Q') (hC : (0 : Q') ≤ C) (S : Nat)
    (chat : Nat → Q')
    (hchatLo : ∀ s, coeffMatchedLo R hR D s ≤ chat s)
    (hchatHi : ∀ s, chat s ≤ coeffMatchedHi R hR D s)
    (ineq : CubedDerivativeIneq N w hw R hR D C S)
    (k : Nat) (hk : 1 ≤ k) (hkS : k ≤ S)
    (hden : (0 : Q') < bondMovedCoeff N w 2 k * chat (k + 1)) :
    stepDeltaQ' N w chat k hden
      ≤ C * (((1 : Q') - w) * ((1 : Q') - w) * ((1 : Q') - w)) * Q'.ofNat (2 * k + 3) :=
  perstep_le_of_box N hw hw1 R hR D C hC S chat hchatLo hchatHi
    (cubed_derivative_implies_box N w hw hw1 R hR D C hC S ineq) k hk hkS hden

/-! ## 5. Doc-section — PROVED vs. NAMED-open (CRITICAL honesty)

PROVED (axiom-clean):
  * `qcube` / `qcube_nonneg` / `qcube_pos` / `qcube_mul` / `le_of_qcube_le` — the `Q'`
    cube algebra and its order-reflection (cube monotonicity).
  * `crealPowNat_cube_rational` — `(ρ^c)³ ≃ ofQ'(R^c)` (cube collapses the triple
    `ρ`-power to the rational `R`-power, via the cube identity `ρ³ ≃ ofQ' R`).
  * `coeffMatched_cube_rational` — **THE ρ-ELIMINATION**: the genuine matched coefficient,
    CUBED, is RATIONAL: `(coeffMatched ρ s)³ ≃ ofQ'((s+1)³·R^{C₄(s)})`.  The cube root is
    gone; this is the algebraic heart of the cubing trick.
  * `qcube_qpow` / `qcube_coeffMatchedHi` / `qcube_coeffMatchedLo` — the cubed DECOMPOSED
    brackets as EXPLICIT rationals `(s+1)³·R^{3⌊C₄ s/3⌋}·(rhoHi/rhoLo)^{3(C₄ s%3)}`, making
    the cubed residual a concrete ρ-free rational inequality.
  * `cubed_derivative_implies_box` / `boxRatioDerivative_of_cubed` — **THE CUBING BRIDGE**:
    a pure-`Q'` cubed derivative inequality (`CubedDerivativeIneq`, ρ-free) inhabits the
    genuine `BoxRatioDerivative N w hw R hR D C` via cube monotonicity, per active mode.
    Sorry-free, unconditional given the cubed input.
  * `perstep_le_of_cubed` — the per-step derivative bound `δ_k ≤ C·u³·(2k+3)` on the
    active window from the cubed residual, through the bridge + `perstep_le_of_box`.

NAMED OPEN (NOT inhabited) — the cubed discrete local CLT:
  * `CubedDerivativeIneq` — the pure-`Q'` cubed inequality
    `[g_{k+1}·ĉ_k^{hi}]³ ≤ [(1 + C·u³·(2k+3))·(g_k·ĉ_{k+1}^{lo})]³` on the proved box form
    and the decomposed+depth brackets, WINDOWED to the active window `1 ≤ k ≤ S`.
    Reconnaissance (exact arithmetic) confirms the EXACT bound holds with `C = 1/2` only on
    the ACTIVE WINDOW `k ≤ S(τ)` (`S ≍ τ^{−1/2}`); in the tail `δ_k/(u³·(2k+3))` grows
    unbounded (fails near `y ≈ 44`), so the unwindowed `∀ k` form is false-as-stated and the
    field is windowed by `k ≤ S` to be TRUE.  On the brackets it further needs a `w`-growing
    bisection depth `D` (the bounded bracket slack absorbed by the `C·u³·(2k+3)` margin), so
    it is NOT inhabitable at a fixed `D` uniformly in `w`.  The cubing trick has made the
    residual PURE-`Q'` (the cube-root obstruction is removed) — that is what this module
    delivers; the cubed local-CLT
    inequality itself is the remaining content, NOT closed here.

HONEST VERDICT.  The CUBING TRICK is realized: `coeffMatched_cube_rational` proves the
cube ELIMINATES the only irrational datum (the cube root `ρ`), and
`cubed_derivative_implies_box` proves the resulting pure-`Q'` cubed inequality BRIDGES to
the genuine `BoxRatioDerivative.derivative` obligation by cube monotonicity.  The bridge is
unconditional and sorry-free.  The cubed inequality `CubedDerivativeIneq` (now ρ-free,
pure-`Q'`) is the genuine discrete-local-CLT residual; it is NAMED precisely and is NOT
inhabited (it requires a `w`-growing bracket depth, per reconnaissance).  This is the
technical crossover lever exposing the local-CLT structure — NOT a 4D Yang–Mills mass gap. -/

end YMGap.Continuum.CubedDerivative

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.CubedDerivative.qcube_mul
#print axioms YMGap.Continuum.CubedDerivative.le_of_qcube_le
#print axioms YMGap.Continuum.CubedDerivative.crealPowNat_cube_rational
#print axioms YMGap.Continuum.CubedDerivative.coeffMatched_cube_rational
#print axioms YMGap.Continuum.CubedDerivative.qcube_qpow
#print axioms YMGap.Continuum.CubedDerivative.qcube_coeffMatchedHi
#print axioms YMGap.Continuum.CubedDerivative.qcube_coeffMatchedLo
#print axioms YMGap.Continuum.CubedDerivative.box_lhs_nonneg
#print axioms YMGap.Continuum.CubedDerivative.box_rhs_nonneg
#print axioms YMGap.Continuum.CubedDerivative.cubed_derivative_implies_box
#print axioms YMGap.Continuum.CubedDerivative.boxRatioDerivative_of_cubed
#print axioms YMGap.Continuum.CubedDerivative.perstep_le_of_cubed
