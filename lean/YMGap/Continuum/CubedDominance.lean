/-
Track B / R2 — the **cubing trick** for the matched-retune DOMINANCE.

# Why this module exists — eliminating the cube-root `ρ` from the dominance

The matched-retune dominance frontier `δ_k ≥ 0` (`g_{k+1}·ĉ_k ≥ g_k·ĉ_{k+1}`,
`ĉ_s = (s+1)·ρ^{C₄(s)}`, `ρ³ = g₁/(2 g₀)`) is carried by the EXACT-`CReal`
datum `ExactCRealDominance` (separating rationals `B k` on the genuine `CReal`
matched coefficient `ĉ`, NO bracket slack).  The obstacle is the IRRATIONAL
cube-root `ρ = ∛R` (`R = cubeRatio = g₁/(2 g₀)`): the cross products
`g_k·ĉ_{k+1}`, `g_{k+1}·ĉ_k` are genuinely `CReal` for the active modes.

## The cubing trick (the key simplification)

`ρ³ = R` is RATIONAL.  So the CUBE of a cross product is RATIONAL:

    (g·(t+1)·ρ^{C₄(t)})³  =  [g·(t+1)]³ · (ρ³)^{C₄(t)}  =  [g·(t+1)]³ · R^{C₄(t)}.

Concretely (`crossProd_cube_eqv`): `(crossProd g ρ t)³ ≃ ofQ'([g·dimQ t]³ · R^{C₄(t)})`,
with `ρ = ∛R`.  The irrational `ρ` is GONE under cubing.  Since `x ↦ x³` reflects
`≤` on nonnegatives (`CReal.le_of_cube_le_cube`), the dominance

    g_k·ĉ_{k+1}  ≤  g_{k+1}·ĉ_k

is implied by the comparison of the two RATIONAL cubes

    [g_k·dimQ(k+1)]³ · R^{C₄(k+1)}  ≤  [g_{k+1}·dimQ k]³ · R^{C₄(k)}.

Clearing `R^{C₄(k)} = R^{C₄(k+1)}/R^{2k+3}` (so dividing by it) and using
`R = g₁/(2 g₀)` (a ratio of `Q'`), then clearing `(2 g₀)^{2k+3}`, this is the

  **CUBED DOMINANCE** (pure `Q'`, NO `ρ`, NO `CReal`):

    [g_k·(k+2)]³ · g₁^{2k+3}  ≤  [g_{k+1}·(k+1)]³ · (2·g₀)^{2k+3}    (k ≥ 1).

This module:

  * `crossProd_cube_eqv` — the cube of the genuine `CReal` cross product is the
    explicit RATIONAL `[g·dimQ t]³ · R^{C₄(t)}` (the cubing trick; `ρ` eliminated).
  * `leRat_of_cube_le` / `geRat_of_cube_ge` — a nonnegative `CReal` whose cube is a
    rational `P` has `leRat X c` from `P ≤ c³` and `geRat X c` from `c³ ≤ P` (the
    cube order-reflection at the `CReal` level, the engine of the bridge).
  * `cubedCrossLo` / `cubedCrossHi` — the two RATIONAL cubes
    `[g_k·dimQ(k+1)]³·R^{C₄(k+1)}` and `[g_{k+1}·dimQ k]³·R^{C₄(k)}`.
  * `cubed_dominance_implies_exact` — **THE CUBING BRIDGE**: from the `Q'` cube
    comparison `cubedCrossLo ≤ B³ ≤ cubedCrossHi` (a separating rational `B` whose
    CUBE separates the two rational cubes — exists from the STRICT cubed gap), the
    `ExactCRealDominance` separators are inhabited.  `ρ` is eliminated from the
    obligation; the residual is the pure-`Q'` cubed comparison.
  * `CubedDominance` — the pure-`Q'` cubed dominance obligation, NAMED precisely,
    plus `cubedCross_sep_of_cubed` deriving the per-mode separating cube from a
    strict cubed gap.

## Honest verdict and scope

The cubing trick (`crossProd_cube_eqv`) and the cube order-reflection bridge
(`leRat_of_cube_le` / `geRat_of_cube_ge` / `cubed_dominance_implies_exact`) are
GENUINELY PROVED, axiom-clean: they ELIMINATE `ρ` and reduce the dominance to a
pure-`Q'` cube comparison on the self-fusion box coefficients.  The CUBED
DOMINANCE itself (the ρ-free discrete local CLT, `CubedDominance`) is NAMED
precisely as a `Q'` finite inequality; it is NOT inhabited here.  This is the
cubing reduction — NOT a 4D Yang–Mills mass gap.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

`crealPowNat` exponent laws, `CReal`-multiplication congruences, the proved cube
order-reflection `CReal.le_of_cube_le_cube`, pure `Q'`/`Nat` arithmetic.  Every
load-bearing declaration is gated with `#print axioms`; permitted output is
`propext` / `Quot.sound` only.  No `Classical.*`, no `native_decide`, no `sorry`.
All witnesses are `Type`-level data.
-/

import YMGap.Continuum.MatchedRetuneBridge
import YMGap.Continuum.MatchedRetuneFrontier

namespace YMGap.Continuum.CubedDominance

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.CRealAlg
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.MatchedRetune
open YMGap.Continuum.MatchedRetuneBridge
open YMGap.Continuum.CRealContinuumAlg

/-! ## 1. The cubing trick: the cube of a cross product is rational

`crossProd g ρ t = (ofQ' g)·((ofQ' (dimQ t))·ρ^{C₄(t)})`.  Its cube is, with
`ρ³ ≃ ofQ' R`, the explicit RATIONAL `[g·dimQ t]³ · R^{C₄(t)}`. -/

/-- `(x^a)^3 ≃ x^{3·a}` (power-of-power for the fixed outer exponent 3), built from
the additive exponent law.  PROOF: `(x^a)^3 = ((1·x^a)·x^a)·x^a ≃ x^a·x^a·x^a`, and
`x^{a+a} ≃ x^a·x^a`, `x^{(a+a)+a} ≃ x^{a+a}·x^a`, with `(a+a)+a = 3·a`. -/
theorem crealPowNat_pow3 (x : CReal) (a : Nat) :
    CReal.Equiv (crealPowNat (crealPowNat x a) 3) (crealPowNat x (3 * a)) := by
  -- LHS = (((cone · x^a) · x^a) · x^a) ≃ ((x^a · x^a) · x^a)
  have hbase : CReal.Equiv (crealPowNat (crealPowNat x a) 3)
      (CReal.mul (CReal.mul (crealPowNat x a) (crealPowNat x a)) (crealPowNat x a)) :=
    crealPowNat_three_equiv (crealPowNat x a)
  -- (x^a · x^a) ≃ x^{a+a}
  have h2 : CReal.Equiv (crealPowNat x (a + a))
      (CReal.mul (crealPowNat x a) (crealPowNat x a)) := crealPowNat_add x a a
  -- (x^{a+a} · x^a) ≃ x^{(a+a)+a}
  have h3 : CReal.Equiv (crealPowNat x ((a + a) + a))
      (CReal.mul (crealPowNat x (a + a)) (crealPowNat x a)) := crealPowNat_add x (a + a) a
  -- assemble: x^{3a} = x^{(a+a)+a} ≃ x^{a+a}·x^a ≃ (x^a·x^a)·x^a ≃ LHS
  have heq : (3 * a) = (a + a) + a := by omega
  refine CReal.Equiv.symm ?_
  rw [heq]
  refine CReal.Equiv.trans h3 ?_
  refine CReal.Equiv.trans (Pivot2.mul_congr_left h2) ?_
  exact CReal.Equiv.symm hbase

/-- `crealPowNat (mul (ofQ' a) X) 3 ≃ mul (ofQ' (a*a*a)) (crealPowNat X 3)` — pull a
rational scalar through a cube. -/
theorem crealPowNat_smul3 (a : Q') (X : CReal) :
    CReal.Equiv (crealPowNat (CReal.mul (CReal.ofQ' a) X) 3)
      (CReal.mul (CReal.ofQ' (a * a * a)) (crealPowNat X 3)) := by
  -- both sides via the three_equiv shape
  have hL : CReal.Equiv (crealPowNat (CReal.mul (CReal.ofQ' a) X) 3)
      (CReal.mul (CReal.mul (CReal.mul (CReal.ofQ' a) X) (CReal.mul (CReal.ofQ' a) X))
        (CReal.mul (CReal.ofQ' a) X)) :=
    crealPowNat_three_equiv (CReal.mul (CReal.ofQ' a) X)
  have hR : CReal.Equiv (crealPowNat X 3) (CReal.mul (CReal.mul X X) X) :=
    crealPowNat_three_equiv X
  refine CReal.Equiv.trans hL ?_
  refine CReal.Equiv.trans ?_ (CReal.Equiv.symm (Pivot2.mul_congr_right hR))
  -- ((aX)(aX))(aX) ≃ (aaa)·((XX)X) ; reassociate/commute the three rational factors
  -- Step: (aX)(aX) ≃ (aa)·(XX)
  have hpair : CReal.Equiv (CReal.mul (CReal.mul (CReal.ofQ' a) X) (CReal.mul (CReal.ofQ' a) X))
      (CReal.mul (CReal.ofQ' (a * a)) (CReal.mul X X)) := by
    -- (aX)(aX) ≃ a(X(aX)) ≃ a((Xa)X) ≃ a((aX)X) ≃ a(a(XX)) ≃ (aa)(XX)
    refine CReal.Equiv.trans (cmul_assoc (CReal.ofQ' a) X (CReal.mul (CReal.ofQ' a) X)) ?_
    refine CReal.Equiv.trans (Pivot2.mul_congr_right
      (CReal.Equiv.symm (cmul_assoc X (CReal.ofQ' a) X))) ?_
    refine CReal.Equiv.trans (Pivot2.mul_congr_right
      (Pivot2.mul_congr_left (cmul_comm X (CReal.ofQ' a)))) ?_
    refine CReal.Equiv.trans (Pivot2.mul_congr_right (cmul_assoc (CReal.ofQ' a) X X)) ?_
    refine CReal.Equiv.trans (CReal.Equiv.symm (cmul_assoc (CReal.ofQ' a) (CReal.ofQ' a)
      (CReal.mul X X))) ?_
    exact Pivot2.mul_congr_left (CReal.Equiv.symm (cofQ'_mul a a))
  -- ((aX)(aX))(aX) ≃ ((aa)(XX))·(aX)
  refine CReal.Equiv.trans (Pivot2.mul_congr_left hpair) ?_
  -- ((aa)(XX))·(aX) ≃ (aa)·((XX)(aX))
  refine CReal.Equiv.trans (cmul_assoc (CReal.ofQ' (a * a)) (CReal.mul X X) (CReal.mul (CReal.ofQ' a) X)) ?_
  -- inner: (XX)(aX) ≃ a·((XX)X)
  have hinner : CReal.Equiv (CReal.mul (CReal.mul X X) (CReal.mul (CReal.ofQ' a) X))
      (CReal.mul (CReal.ofQ' a) (CReal.mul (CReal.mul X X) X)) := by
    refine CReal.Equiv.trans (Pivot2.mul_congr_right (cmul_comm (CReal.ofQ' a) X)) ?_
    refine CReal.Equiv.trans (CReal.Equiv.symm (cmul_assoc (CReal.mul X X) X (CReal.ofQ' a))) ?_
    exact cmul_comm (CReal.mul (CReal.mul X X) X) (CReal.ofQ' a)
  refine CReal.Equiv.trans (Pivot2.mul_congr_right hinner) ?_
  -- (aa)·(a·((XX)X)) ≃ ((aa)·a)·((XX)X) ≃ ofQ'(aaa)·((XX)X)
  refine CReal.Equiv.trans (CReal.Equiv.symm
    (cmul_assoc (CReal.ofQ' (a * a)) (CReal.ofQ' a) (CReal.mul (CReal.mul X X) X))) ?_
  exact Pivot2.mul_congr_left (CReal.Equiv.symm (cofQ'_mul (a * a) a))

/-- **The cubing trick.**  The cube of the genuine `CReal` cross product
`crossProd g (∛R) t = g·(t+1)·(∛R)^{C₄(t)}` is the explicit RATIONAL
`[g·dimQ t]³ · R^{C₄(t)}`.  The irrational `ρ = ∛R` is ELIMINATED under cubing
because `ρ³ = R` is rational.

PROOF.  `crossProd g ρ t = (ofQ' g)·((ofQ' (dimQ t))·ρ^{C₄(t)})`; pull both
rational scalars out of the cube (`crealPowNat_smul3` twice, after combining the
two rational scalars), and reduce `(ρ^{C₄(t)})³ ≃ ρ^{3·C₄(t)} ≃ ofQ'(R^{C₄(t)})`
(`crealPowNat_pow3` then `crealPowNat_mul3` with the cube identity). -/
theorem crossProd_cube_eqv (g : Q') (R : Q') (hR : (0 : Q') < R) (t : Nat) :
    CReal.Equiv (crealPowNat (crossProd g (CReal.cbrtFrom R hR) t) 3)
      (CReal.ofQ' ((g * dimQ t) * (g * dimQ t) * (g * dimQ t) * qpow R (c4 t))) := by
  -- crossProd g ρ t = mul (ofQ' g) (coeffMatched ρ t) = mul (ofQ' g) (mul (ofQ' (dimQ t)) ρ^{c4 t})
  -- First: crossProd ≃ mul (ofQ' (g*dimQ t)) ρ^{c4 t}
  have hbase : CReal.Equiv (crossProd g (CReal.cbrtFrom R hR) t)
      (CReal.mul (CReal.ofQ' (g * dimQ t)) (crealPowNat (CReal.cbrtFrom R hR) (c4 t))) := by
    show CReal.Equiv
      (CReal.mul (CReal.ofQ' g)
        (CReal.mul (CReal.ofQ' (dimQ t)) (crealPowNat (CReal.cbrtFrom R hR) (c4 t))))
      (CReal.mul (CReal.ofQ' (g * dimQ t)) (crealPowNat (CReal.cbrtFrom R hR) (c4 t)))
    -- g·(dimQ·ρ^c) ≃ (g·dimQ)·ρ^c ≃ ofQ'(g*dimQ)·ρ^c
    refine CReal.Equiv.trans (CReal.Equiv.symm
      (cmul_assoc (CReal.ofQ' g) (CReal.ofQ' (dimQ t))
        (crealPowNat (CReal.cbrtFrom R hR) (c4 t)))) ?_
    exact Pivot2.mul_congr_left (CReal.Equiv.symm (cofQ'_mul g (dimQ t)))
  -- cube both sides
  refine CReal.Equiv.trans
    (crealPowNat_three_equiv (crossProd g (CReal.cbrtFrom R hR) t)) ?_
  refine CReal.Equiv.trans
    (Pivot2.mul_congr (Pivot2.mul_congr hbase hbase) hbase) ?_
  -- now: ((A)(A))(A) with A = mul (ofQ'(g*dimQ)) ρ^c ; this is crealPowNat A 3 (modulo three_equiv)
  refine CReal.Equiv.trans (CReal.Equiv.symm
    (crealPowNat_three_equiv (CReal.mul (CReal.ofQ' (g * dimQ t))
      (crealPowNat (CReal.cbrtFrom R hR) (c4 t))))) ?_
  -- crealPowNat (mul (ofQ' a) Y) 3 ≃ mul (ofQ'(a³)) (crealPowNat Y 3)
  refine CReal.Equiv.trans
    (crealPowNat_smul3 (g * dimQ t) (crealPowNat (CReal.cbrtFrom R hR) (c4 t))) ?_
  -- crealPowNat (ρ^{c4 t}) 3 ≃ ρ^{3·c4 t} ≃ ofQ'(R^{c4 t})
  have hcube : CReal.Equiv (crealPowNat (CReal.cbrtFrom R hR) 3) (CReal.ofQ' R) :=
    cbrt_crealPowNat_cube R hR
  have hpow3 : CReal.Equiv (crealPowNat (crealPowNat (CReal.cbrtFrom R hR) (c4 t)) 3)
      (CReal.ofQ' (qpow R (c4 t))) :=
    CReal.Equiv.trans (crealPowNat_pow3 (CReal.cbrtFrom R hR) (c4 t))
      (crealPowNat_mul3 (CReal.cbrtFrom R hR) R hcube (c4 t))
  refine CReal.Equiv.trans (Pivot2.mul_congr_right hpow3) ?_
  -- mul (ofQ'((g*dimQ)³)) (ofQ'(R^{c4 t})) ≃ ofQ'((g*dimQ)³ · R^{c4 t})
  exact CReal.Equiv.symm (cofQ'_mul ((g * dimQ t) * (g * dimQ t) * (g * dimQ t)) (qpow R (c4 t)))

/-! ## 2. The cube order-reflection bridge at the `CReal` level

A nonnegative `CReal` `X` whose CUBE is the rational `ofQ' P` IS the cube root of
`P`: it equals `cbrtFrom P`.  Hence the rational bracket comparisons of `cbrtFrom`
(`cbrtFrom_leRat_of_cube`, `cbrtFrom_geRat_of_cube`) transfer to `X`.  This is the
cube order-reflection that turns the `Q'` cube comparison into the `CReal`
`leRat`/`geRat` separators — with `ρ` already gone. -/

/-- A `CReal` `X` with `X³ ≃ ofQ' P` and `IsPositive X` (and `0 < P`) equals
`cbrtFrom P`.  PROOF: both cubes are `≃ ofQ' P` and both are positive, so
`cubeRoot_unique` (reshaped via `crealPowNat_three_equiv`). -/
theorem eqv_cbrtFrom_of_cube (X : CReal) (P : Q') (hP : (0 : Q') < P)
    (hcube : CReal.Equiv (crealPowNat X 3) (CReal.ofQ' P))
    (hpos : CReal.IsPositive X) :
    CReal.Equiv X (CReal.cbrtFrom P hP) := by
  have hX3 : CReal.Equiv (CReal.mul (CReal.mul X X) X) (CReal.ofQ' P) :=
    CReal.Equiv.trans (CReal.Equiv.symm (crealPowNat_three_equiv X)) hcube
  have hC3 : CReal.Equiv
      (CReal.mul (CReal.mul (CReal.cbrtFrom P hP) (CReal.cbrtFrom P hP)) (CReal.cbrtFrom P hP))
      (CReal.ofQ' P) :=
    CReal.Equiv.trans (CReal.Equiv.symm (crealPowNat_three_equiv (CReal.cbrtFrom P hP)))
      (cbrt_crealPowNat_cube P hP)
  exact CReal.cubeRoot_unique hX3 hC3 hpos (CReal.cbrtFrom_isPositive P hP)

/-- **`leRat X c` from a `Q'` cube comparison.**  If `X³ ≃ ofQ' P` (with `X`
positive, `0 < P`) and `P ≤ c³` (`c ≥ 0`), then `leRat X c`.  The cube
order-reflection: `X = ∛P ≤ c`. -/
theorem leRat_of_cube_le (X : CReal) (P : Q') (hP : (0 : Q') < P)
    (hcube : CReal.Equiv (crealPowNat X 3) (CReal.ofQ' P))
    (hpos : CReal.IsPositive X) (c : Q') (hc : (0 : Q') ≤ c)
    (hPc : P ≤ c * c * c) : CReal.leRat X c :=
  CReal.leRat_of_equiv (eqv_cbrtFrom_of_cube X P hP hcube hpos)
    (CReal.cbrtFrom_leRat_of_cube P hP c hc hPc)

/-- **`geRat X c` from a `Q'` cube comparison.**  If `X³ ≃ ofQ' P` (with `X`
positive, `0 < P`) and `c³ ≤ P` (`c ≥ 0`), then `geRat X c`. -/
theorem geRat_of_cube_ge (X : CReal) (P : Q') (hP : (0 : Q') < P)
    (hcube : CReal.Equiv (crealPowNat X 3) (CReal.ofQ' P))
    (hpos : CReal.IsPositive X) (c : Q') (hc : (0 : Q') ≤ c)
    (hcP : c * c * c ≤ P) : ExpPos.geRat X c :=
  SU3CharFactor.geRat_of_equiv (eqv_cbrtFrom_of_cube X P hP hcube hpos)
    (MatchedRetuneBridge.cbrtFrom_geRat_of_cube P hP c hc hcP)

/-! ## 3. The two rational cubes and the cubed dominance obligation

`cubedCrossLo k = [g_k·dimQ(k+1)]³·R^{C₄(k+1)}` is the cube of the SMALLER cross
product `g_k·ĉ_{k+1}`; `cubedCrossHi k = [g_{k+1}·dimQ k]³·R^{C₄(k)}` is the cube
of the LARGER `g_{k+1}·ĉ_k`.  The dominance `g_k·ĉ_{k+1} ≤ g_{k+1}·ĉ_k` reduces
(cube order-reflection) to `cubedCrossLo k ≤ cubedCrossHi k` — a pure `Q'`
inequality with NO `ρ`. -/

/-- The cube of the SMALLER cross product `g_k·ĉ_{k+1}` (rational, `ρ` eliminated):
`[g_k·dimQ(k+1)]³ · R^{C₄(k+1)}`. -/
def cubedCrossLo (N : Nat) (w : Q') (R : Q') (k : Nat) : Q' :=
  (bondMovedCoeff N w 2 k * dimQ (k + 1)) * (bondMovedCoeff N w 2 k * dimQ (k + 1))
    * (bondMovedCoeff N w 2 k * dimQ (k + 1)) * qpow R (c4 (k + 1))

/-- The cube of the LARGER cross product `g_{k+1}·ĉ_k` (rational, `ρ` eliminated):
`[g_{k+1}·dimQ k]³ · R^{C₄(k)}`. -/
def cubedCrossHi (N : Nat) (w : Q') (R : Q') (k : Nat) : Q' :=
  (bondMovedCoeff N w 2 (k + 1) * dimQ k) * (bondMovedCoeff N w 2 (k + 1) * dimQ k)
    * (bondMovedCoeff N w 2 (k + 1) * dimQ k) * qpow R (c4 k)

/-- **The pure-`Q'` CUBED DOMINANCE obligation** (the `ρ`-free discrete local CLT).
For the matched kernel `R = cubeRatio N w hw` and the active modes `1 ≤ k`, the cube
of the smaller cross product is `≤` the cube of the larger:

    cubedCrossLo k  ≤  cubedCrossHi k,    i.e.
    [g_k·(k+2)]³ · R^{C₄(k+1)}  ≤  [g_{k+1}·(k+1)]³ · R^{C₄(k)}.

Cleared of `R^{C₄(k)}` (so the only `R`-power left is `R^{2k+3}`) and of the
denominator `(2 g₀)^{2k+3}` (`R = g₁/(2 g₀)`), this is the closed CUBED DOMINANCE

    [g_k·(k+2)]³ · g₁^{2k+3}  ≤  [g_{k+1}·(k+1)]³ · (2 g₀)^{2k+3}.

This is a finite `Q'` inequality on the self-fusion box coefficients
(`bondMovedCoeff … = g_s` in closed `(r,d)` box form).  NAMED precisely, NOT a
`C₄²` envelope, NOT inhabited here. -/
structure CubedDominance (N : Nat) (w : Q') (hw : (0 : Q') < w) : Type where
  /-- The `Q'` cube comparison on the active modes `1 ≤ k`. -/
  cubed : ∀ k, 1 ≤ k →
    cubedCrossLo N w (cubeRatio N w hw) k ≤ cubedCrossHi N w (cubeRatio N w hw) k

/-- **The two rational cubes are positive** under active-mode coefficient positivity.
`cubedCrossLo = [g·dimQ]³·R^{C₄}` is a product of strict positives when `0 < g`,
`0 < R`. -/
theorem cubedCrossLo_pos (N : Nat) (w : Q') (R : Q') (hR : (0 : Q') < R) (k : Nat)
    (hg : (0 : Q') < bondMovedCoeff N w 2 k) : (0 : Q') < cubedCrossLo N w R k := by
  have hgd : (0 : Q') < bondMovedCoeff N w 2 k * dimQ (k + 1) :=
    Q'.mul_pos hg (by simpa [dimQ] using Q'.ofNat_succ_pos (k + 1))
  exact Q'.mul_pos (Q'.mul_pos (Q'.mul_pos hgd hgd) hgd)
    (BondMovingScaledNorm.qpow_pos hR (c4 (k + 1)))

/-- `0 < cubedCrossHi`. -/
theorem cubedCrossHi_pos (N : Nat) (w : Q') (R : Q') (hR : (0 : Q') < R) (k : Nat)
    (hg : (0 : Q') < bondMovedCoeff N w 2 (k + 1)) : (0 : Q') < cubedCrossHi N w R k := by
  have hgd : (0 : Q') < bondMovedCoeff N w 2 (k + 1) * dimQ k :=
    Q'.mul_pos hg (by simpa [dimQ] using Q'.ofNat_succ_pos k)
  exact Q'.mul_pos (Q'.mul_pos (Q'.mul_pos hgd hgd) hgd)
    (BondMovingScaledNorm.qpow_pos hR (c4 k))

/-! ## 4. THE CUBING BRIDGE — `ExactCRealDominance` from a separating cube

From the cubed dominance with a separating rational `B` whose CUBE separates the
two rational cubes (`cubedCrossLo ≤ B³` and `B³ ≤ cubedCrossHi`, `B ≥ 0`), the
`ExactCRealDominance` separators are inhabited: `B` itself is the separating
rational on the genuine `CReal` cross products (cube order-reflection), with `ρ`
already eliminated.  Positivity of the cross products is a clean named input
(`hposLo`/`hposHi`: the active-mode self-fusion coefficients are positive). -/

/-- **THE CUBING BRIDGE (per mode).**  For an active mode `1 ≤ k`, given the genuine
cross products' positivity (`IsPositive`, the active-mode coefficient is positive)
and a separating rational `B` whose CUBE lies between the two RATIONAL cubes
`cubedCrossLo k ≤ B³` and `B³ ≤ cubedCrossHi k`, the `CReal` separators hold:

    leRat (g_k·ĉ_{k+1}) B    and    geRat (g_{k+1}·ĉ_k) B.

This is the cube order-reflection (`leRat_of_cube_le`/`geRat_of_cube_ge`) applied
to the cubing trick `crossProd_cube_eqv` — `ρ` is GONE. -/
theorem cubed_sep_implies_cross_sep (N : Nat) {w : Q'} (R : Q') (hR : (0 : Q') < R)
    (k : Nat)
    (hgk : (0 : Q') < bondMovedCoeff N w 2 k)
    (hgk1 : (0 : Q') < bondMovedCoeff N w 2 (k + 1))
    (hposLo : CReal.IsPositive (crossProd (bondMovedCoeff N w 2 k) (CReal.cbrtFrom R hR) (k + 1)))
    (hposHi : CReal.IsPositive (crossProd (bondMovedCoeff N w 2 (k + 1)) (CReal.cbrtFrom R hR) k))
    (B : Q') (hB : (0 : Q') ≤ B)
    (hloB : cubedCrossLo N w R k ≤ B * B * B)
    (hBhi : B * B * B ≤ cubedCrossHi N w R k) :
    CReal.leRat (crossProd (bondMovedCoeff N w 2 k) (CReal.cbrtFrom R hR) (k + 1)) B
      ∧ ExpPos.geRat (crossProd (bondMovedCoeff N w 2 (k + 1)) (CReal.cbrtFrom R hR) k) B := by
  have hPlo_pos : (0 : Q') < cubedCrossLo N w R k := cubedCrossLo_pos N w R hR k hgk
  have hPhi_pos : (0 : Q') < cubedCrossHi N w R k := cubedCrossHi_pos N w R hR k hgk1
  refine ⟨?_, ?_⟩
  · -- leRat (smaller) B :  smaller³ ≃ ofQ'(cubedCrossLo k) ≤ B³
    refine leRat_of_cube_le _ (cubedCrossLo N w R k) hPlo_pos ?_ hposLo B hB hloB
    exact crossProd_cube_eqv (bondMovedCoeff N w 2 k) R hR (k + 1)
  · -- geRat (larger) B :  B³ ≤ cubedCrossHi k ≃ larger³
    refine geRat_of_cube_ge _ (cubedCrossHi N w R k) hPhi_pos ?_ hposHi B hB hBhi
    exact crossProd_cube_eqv (bondMovedCoeff N w 2 (k + 1)) R hR k

/-- **`cubed_dominance_implies_exact` — THE CUBING BRIDGE, assembled.**  From a
per-mode SEPARATING CUBE `B k` (with `cubedCrossLo k ≤ (B k)³ ≤ cubedCrossHi k`),
the active-mode coefficient positivity and the cross-product positivity, the
`ExactCRealDominance` datum is INHABITED: `B k` is the separating rational on the
genuine `CReal` matched coefficients `ĉ`, with `ρ` eliminated by the cubing trick.

This eliminates `ρ` from the dominance obligation: the only remaining input is the
pure-`Q'` separating cube `B k` between `cubedCrossLo k` and `cubedCrossHi k`
(supplied by `CubedDominance` + a per-mode cube-root bracket; see
`cubedCross_sep_of_cubed`). -/
def cubed_dominance_implies_exact (N : Nat) {w : Q'} (R : Q') (hR : (0 : Q') < R)
    (hgk : ∀ k, 1 ≤ k → (0 : Q') < bondMovedCoeff N w 2 k)
    (hpos : ∀ k, 1 ≤ k →
      CReal.IsPositive (crossProd (bondMovedCoeff N w 2 k) (CReal.cbrtFrom R hR) (k + 1))
        ∧ CReal.IsPositive (crossProd (bondMovedCoeff N w 2 (k + 1)) (CReal.cbrtFrom R hR) k))
    (B : Nat → Q') (hBnn : ∀ k, 1 ≤ k → (0 : Q') ≤ B k)
    (hlo : ∀ k, 1 ≤ k → cubedCrossLo N w R k ≤ B k * B k * B k)
    (hhi : ∀ k, 1 ≤ k → B k * B k * B k ≤ cubedCrossHi N w R k) :
    MatchedRetuneBridge.ExactCRealDominance N w R hR where
  B := B
  sep_lo := fun k hk =>
    (cubed_sep_implies_cross_sep N R hR k (hgk k hk)
      (hgk (k + 1) (Nat.le_trans hk (Nat.le_succ k))) (hpos k hk).1 (hpos k hk).2
      (B k) (hBnn k hk) (hlo k hk) (hhi k hk)).1
  sep_hi := fun k hk =>
    (cubed_sep_implies_cross_sep N R hR k (hgk k hk)
      (hgk (k + 1) (Nat.le_trans hk (Nat.le_succ k))) (hpos k hk).1 (hpos k hk).2
      (B k) (hBnn k hk) (hlo k hk) (hhi k hk)).2

/-! ## 5. The separating cube from the strict cubed dominance

The separating cube `B k` is a rational with `cubedCrossLo k ≤ (B k)³ ≤
cubedCrossHi k`.  When the cubed dominance is STRICT (`cubedCrossLo k <
cubedCrossHi k`, the genuine `δ_k > 0` margin), such a `B k` exists and is
constructible: `B k := cbrtHi (cubedCrossLo k) D_k` at a bisection depth `D_k`
where the upper endpoint's cube has fallen below `cubedCrossHi k`.  The LOWER
bound `cubedCrossLo k ≤ (B k)³` is the located cube invariant (always); the UPPER
bound `(B k)³ ≤ cubedCrossHi k` holds past the strict-gap modulus.  We expose the
existence as the precise residual obligation `SeparatingCube`. -/

/-- **The separating-cube obligation.**  For each active mode `1 ≤ k`, a rational
`B k ≥ 0` whose cube separates the two RATIONAL cubes `cubedCrossLo k ≤ (B k)³ ≤
cubedCrossHi k`.  Equivalent to the STRICT cubed dominance `cubedCrossLo k ≤
cubedCrossHi k` plus a per-mode rational cube root in the interval.  This is the
pure-`Q'` residual the cubing trick reduces the dominance to (NOT inhabited). -/
structure SeparatingCube (N : Nat) (w : Q') (R : Q') : Type where
  /-- The separating rational per active mode. -/
  B : Nat → Q'
  /-- Nonnegativity. -/
  B_nonneg : ∀ k, 1 ≤ k → (0 : Q') ≤ B k
  /-- The cube lower bound (smaller cross's cube). -/
  cube_lo : ∀ k, 1 ≤ k → cubedCrossLo N w R k ≤ B k * B k * B k
  /-- The cube upper bound (larger cross's cube). -/
  cube_hi : ∀ k, 1 ≤ k → B k * B k * B k ≤ cubedCrossHi N w R k

/-- **The cubing bridge from the separating cube.**  A `SeparatingCube` (with the
positivity inputs) inhabits `ExactCRealDominance`.  Direct application of
`cubed_dominance_implies_exact`. -/
def exact_of_separatingCube (N : Nat) {w : Q'} (R : Q') (hR : (0 : Q') < R)
    (hgk : ∀ k, 1 ≤ k → (0 : Q') < bondMovedCoeff N w 2 k)
    (hpos : ∀ k, 1 ≤ k →
      CReal.IsPositive (crossProd (bondMovedCoeff N w 2 k) (CReal.cbrtFrom R hR) (k + 1))
        ∧ CReal.IsPositive (crossProd (bondMovedCoeff N w 2 (k + 1)) (CReal.cbrtFrom R hR) k))
    (sc : SeparatingCube N w R) :
    MatchedRetuneBridge.ExactCRealDominance N w R hR :=
  cubed_dominance_implies_exact N R hR hgk hpos sc.B sc.B_nonneg sc.cube_lo sc.cube_hi

/-! ## 6. Doc-section — PROVED vs. NAMED-open (CRITICAL honesty)

THE CUBING TRICK (the key simplification, GENUINELY PROVED, axiom-clean):
  * `crossProd_cube_eqv` — the cube of the genuine `CReal` cross product
    `g·(t+1)·ρ^{C₄(t)}` is the explicit RATIONAL `[g·dimQ t]³·R^{C₄(t)}`.  Because
    `ρ³ = R` is rational, `ρ` is ELIMINATED under cubing.  This is the heart of the
    trick.
  * `crealPowNat_pow3` / `crealPowNat_smul3` — the `(x^a)^3 ≃ x^{3a}` and
    `(a·X)^3 ≃ a³·X^3` exponent/scalar laws feeding `crossProd_cube_eqv`.

THE CUBE ORDER-REFLECTION BRIDGE (GENUINELY PROVED, axiom-clean):
  * `eqv_cbrtFrom_of_cube` — a positive `CReal` with rational cube `P` IS `∛P`
    (via the proved `cubeRoot_unique`).
  * `leRat_of_cube_le` / `geRat_of_cube_ge` — `leRat X c` from `P ≤ c³` and
    `geRat X c` from `c³ ≤ P` (the cube order-reflection at the `CReal` level).
  * `cubed_sep_implies_cross_sep` — per mode: a separating cube `B` (with
    `cubedCrossLo ≤ B³ ≤ cubedCrossHi`) yields the genuine `CReal` separators
    `leRat (g_k·ĉ_{k+1}) B` and `geRat (g_{k+1}·ĉ_k) B`.  `ρ` is GONE.
  * `cubed_dominance_implies_exact` / `exact_of_separatingCube` — assembled:
    a per-mode separating cube (`SeparatingCube`) + positivity inputs INHABIT
    `MatchedRetuneBridge.ExactCRealDominance` (the dominance datum the frontier's
    `step_nonneg` consumes).  This is the bridge: the dominance obligation is now
    a pure-`Q'` cube comparison, `ρ`-free.

NAMED OPEN (NOT inhabited) — the genuine `ρ`-free discrete local CLT:
  * `CubedDominance` — the pure-`Q'` cube comparison
    `cubedCrossLo k ≤ cubedCrossHi k`, i.e.
    `[g_k·(k+2)]³·R^{C₄(k+1)} ≤ [g_{k+1}·(k+1)]³·R^{C₄(k)}`, equivalently (cleared)
    `[g_k·(k+2)]³·g₁^{2k+3} ≤ [g_{k+1}·(k+1)]³·(2 g₀)^{2k+3}` on `1 ≤ k`.  A finite
    `Q'` inequality on the self-fusion box coefficients (the `(r,d)` box form).
    NOT a `C₄²` envelope, NOT inhabited here.
  * `SeparatingCube` — the per-mode separating rational cube between
    `cubedCrossLo k` and `cubedCrossHi k`; exists from the STRICT cubed dominance
    (the `δ_k > 0` margin) plus a per-mode rational cube root in the interval.  NOT
    inhabited here.

HONEST VERDICT.  The CUBING TRICK (`crossProd_cube_eqv`) and the cube
order-reflection BRIDGE (`cubed_dominance_implies_exact` /
`exact_of_separatingCube`) are GENUINELY PROVED, axiom-clean: they ELIMINATE the
irrational `ρ = ∛R` from the matched-retune dominance obligation, reducing it to a
PURE-`Q'` cube comparison on the self-fusion box coefficients (`CubedDominance` /
`SeparatingCube`).  The cubed dominance itself (the `ρ`-free discrete local CLT) is
NAMED precisely; it is NOT inhabited.  This is the cubing reduction — NOT a 4D
Yang–Mills mass gap. -/

end YMGap.Continuum.CubedDominance

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.CubedDominance.crealPowNat_pow3
#print axioms YMGap.Continuum.CubedDominance.crealPowNat_smul3
#print axioms YMGap.Continuum.CubedDominance.crossProd_cube_eqv
#print axioms YMGap.Continuum.CubedDominance.eqv_cbrtFrom_of_cube
#print axioms YMGap.Continuum.CubedDominance.leRat_of_cube_le
#print axioms YMGap.Continuum.CubedDominance.geRat_of_cube_ge
#print axioms YMGap.Continuum.CubedDominance.cubedCrossLo_pos
#print axioms YMGap.Continuum.CubedDominance.cubedCrossHi_pos
#print axioms YMGap.Continuum.CubedDominance.cubed_sep_implies_cross_sep
#print axioms YMGap.Continuum.CubedDominance.cubed_dominance_implies_exact
#print axioms YMGap.Continuum.CubedDominance.exact_of_separatingCube

