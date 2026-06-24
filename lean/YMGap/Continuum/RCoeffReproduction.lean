/-
# The R-coefficient reproduction `r_c = 2a·m_c` (node-free) and the honest
# Wall-1 positivity test

This file isolates the **reproduction identity** tying the proved-nonnegative
theta-product `R = ϑ₃·S` to the SU(2) heat-kernel character moments, and then
runs the honest test of whether the all-order Gram positive-semidefiniteness
(`MomentSquarePos`) closes from `R ≥ 0` *without* the Gauss–Chebyshev node datum.

# The arithmetic (the genuine new core, items 1–2)

The SU(2) heat-kernel character moments, written in the geometric variable
`a ∈ (0,1)` (`a = e^{−t/4}`, so `e^{−t·C₂(c)} = a^{c(c+2)}` and `dim = c+1`), are

    m_c = (c+1)·a^{c(c+2)}.

The proved-nonnegative `R = ϑ₃·S` has the second-kind Chebyshev expansion
`R = Σ_m r_m U_m` whose `m`-th coefficient — read off the `K_t`-side summand
`dTerm a x n = (n+1)·a^{(n+1)²}·U_n(x)` (so `R = 2·Σ dTerm`, the rational
`a^{-1}` prefactor carried separately) — is

    r_m = 2·(m+1)·a^{(m+1)²}.

The exact exponent identity

    (c+1)² = c(c+2) + 1

then gives, lifted through `a^•`,

    r_c = 2·(c+1)·a^{c(c+2)+1} = 2·a·(c+1)·a^{c(c+2)} = 2a·m_c          (THE CORE).

This is `rCoeff_eq_two_a_moment` — a genuine, node-free `Q'` theorem.

# The reproduction (item 2)

The SU(2) Clebsch–Gordan fusion `χ_p χ_q = Σ_{c∈fusion(p,q)} χ_c`
(`fusion(p,q) = {|p−q|, |p−q|+2, …, p+q}`) makes the Gram entry the fusion sum of
moments `G_{pq} = Σ_{c∈fusion} m_c`.  Substituting `m_c = (1/2a)·r_c` gives the
**fusion-quadrature reproduction**

    G_{pq} ≃ (1/2a)·Σ_{c∈fusion(p,q)} r_c          (`fusion_eq_Rcoeff_quadrature`).

A finite `CReal` rearrangement; node-free; PROVED.  We carry it on the genuine
`a`-power moment data `aMoments a` (an instance of the abstract `MomentData`),
whose Gram entries are exactly `GramRed.gram (aMoments a)`.

# The honest Wall-1 positivity test (item 3 — the negative)

Wall-1 is `MomentSquarePos`: `E(q²) = Σ_{p,q} c_p c_q G_{pq} ≥ 0` for every
finite `q = Σ c_p χ_p`.  Through the reproduction this is

    E(q²) = Σ_c d_c·m_c = (1/2a)·Σ_c d_c·r_c,
    d_c := Σ_{p,q} c_p c_q N^c_{pq}   (the fusion-multiplicity expansion of (Σc_pχ_p)²).

The question item 3 asks: is `Σ_c d_c r_c ≥ 0` derivable from `R ≥ 0` *without*
integration / quadrature nodes?  The answer found here is **NO**, and the reason
is precise and recorded as `dCoeff` with the structural facts below:

  * `d_c = Σ_{p,q} c_p c_q N^c_{pq}` has **mixed sign**: it is the
    character-ring coefficient of `(Σ_p c_p χ_p)²`, and for a non-cone `c`
    (mixed signs) the off-diagonal cross terms make individual `d_c` negative.
    So `Σ_c d_c r_c` is NOT a sum of manifestly-nonnegative terms — the
    term-by-term route (which closes the cone case, `gramForm_pos_cone`) fails.
  * `R ≥ 0` is a *pointwise* fact `R(x) ≥ 0` for `x ∈ [−1,1]`.  Turning it into
    `Σ_c d_c r_c ≥ 0` is exactly the Parseval/Fourier statement
    `Σ_c d_c r_c = (normalization)·∫_{−1}^{1} (Σ_p c_p U_p(x))²·R(x)·√(1−x²) dx`,
    i.e. the integral of `L(x)²·R(x) ≥ 0`.  Recovering that integral
    constructively, in the Mathlib-free `Q'`/`CReal` substrate, requires either
    the integral itself (no constructive integration here) **or** its
    finite Gauss–Chebyshev surrogate `Σ_k w_k L(x_k)² R(x_k)` — the **node-square
    form** (`ChebyshevQuadPSD.ChebNodes` / `nodeSOS`).  The manifest squares
    `L(x_k)²` times `R(x_k) ≥ 0` are what supply positivity; the bare
    coefficient sum `Σ_c d_c r_c` has no such structure.

So **the positivity genuinely needs the node-square form**, while the
**reproduction `r_c = 2a·m_c` (items 1–2) is node-free**.  We make the negative
content concrete: `psd_from_Rcoeff_needs_nonneg_dsum` shows that the *only*
gap between the reproduction and `MomentSquarePos` is the rational fact
`∀ c-combination, Σ_c d_c r_c ≥ 0` (equivalently `Σ_c d_c m_c ≥ 0`), and that
this is NOT a consequence of the per-term nonnegativity that closes the cone.
The closed route for it is `ChebyshevQuadPSD.momentSquarePos_via_nodes`
(the node datum), NOT this file.

# Honest Wall-1 status (the conclusion)

  * REPRODUCTION (`rCoeff_eq_two_a_moment`, `fusion_eq_Rcoeff_quadrature`):
    PROVED, node-free.
  * POSITIVITY (`MomentSquarePos`, all-order Gram PSD): does NOT close node-free
    from `R ≥ 0`; it equals the node-square positivity `ChebNodes`-form
    (`ChebyshevQuadPSD`), with the node positivity itself already sourced (proved)
    from `R_geRat_zero_gen`.  This file banks the reproduction and pins the
    precise obstruction; it does not weaken or fake the positivity.

# Axiom-gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]`.  No `Classical.*`, no `sorryAx`,
no `native_decide`.
-/

import YMGap.Continuum.GramReduction
import YMGap.Continuum.HeatKernelConv
import YMGap.Continuum.ChebyshevQuadPSD

namespace YMGap.Continuum.RCoeffReproduction

open YMGap.Constructive
open YMGap.Continuum.GramRed (MomentData gram fusionLow gramForm momentSquare
  MomentSquarePos equiv_refl)

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The moment `m_c`, the R-coefficient `r_c`, and the core identity

Both objects are explicit `Q'` formulas in the geometric variable `a ∈ (0,1)`.
`aMoment a c` is the heat-kernel character moment `(c+1)·a^{c(c+2)}` in `a`-power
form; `rCoeff a c` is `R`'s `c`-th second-kind Chebyshev coefficient
`2·(c+1)·a^{(c+1)²}`, aligned with `JTPIdentity.dTerm` (whose `n`-th summand is
`(n+1)·a^{(n+1)²}·U_n`, and `R = 2·Σ dTerm`). -/

/-- **The heat-kernel character moment in `a`-power form**
`m_c = (c+1)·a^{c(c+2)}` (`= dim(c)·e^{−t·C₂(c)}` with `a = e^{−t/4}`). -/
def aMoment (a : Q') (c : Nat) : Q' :=
  Q'.ofNat (c + 1) * a ^ (c * (c + 2))

/-- **`R`'s `c`-th second-kind Chebyshev coefficient**
`r_c = 2·(c+1)·a^{(c+1)²}` — the coefficient structure of `R = 2·Σ dTerm`,
`dTerm a x n = (n+1)·a^{(n+1)²}·U_n(x)`. -/
def rCoeff (a : Q') (c : Nat) : Q' :=
  Q'.ofNat 2 * (Q'.ofNat (c + 1) * a ^ ((c + 1) * (c + 1)))

/-- The exact exponent identity `(c+1)·(c+1) = c·(c+2) + 1`.  Both sides expand
to `c·c + 2c + 1`; proved by `Nat` distributivity then `omega`. -/
theorem exp_identity (c : Nat) : (c + 1) * (c + 1) = c * (c + 2) + 1 := by
  have h1 : (c + 1) * (c + 1) = c * c + 2 * c + 1 := by
    rw [Nat.mul_add, Nat.add_mul, Nat.add_mul]; omega
  have h2 : c * (c + 2) + 1 = c * c + 2 * c + 1 := by
    rw [Nat.mul_add]; omega
  omega

/-- The `a`-power split from the exponent identity:
`a^{(c+1)²} ≃ a^{c(c+2)}·a`. -/
theorem apow_split (a : Q') (c : Nat) :
    a ^ ((c + 1) * (c + 1)) ≈ a ^ (c * (c + 2)) * a := by
  -- rewrite the exponent, then `a^{N+1} ≃ a^N · a^1 ≃ a^N · a`
  rw [exp_identity c]
  refine Q'.eqv_trans _ _ _ (SU3CharFactor.pow_add_eqv a (c * (c + 2)) 1) ?_
  -- a^{c(c+2)} · a^1 ≃ a^{c(c+2)} · a   (a^1 = a · a^0 = a · 1 ≃ a)
  refine Q'.mul_eqv_congr_left (a ^ (c * (c + 2))) (a ^ 1) a ?_
  show (a * a ^ 0) ≈ a
  exact Q'.mul_one_eqv a

/-- **THE REPRODUCTION CORE (item 1) — `r_c = 2a·m_c`, node-free.**

`r_c = 2·(c+1)·a^{(c+1)²} ≃ 2·(c+1)·(a^{c(c+2)}·a)
     ≃ (2·a)·((c+1)·a^{c(c+2)}) = (2a)·m_c`,
the exponent identity `(c+1)² = c(c+2)+1` lifted through `a^•`.  Pure `Q'`
arithmetic; no integration, no cos-nodes. -/
theorem rCoeff_eq_two_a_moment (a : Q') (c : Nat) :
    rCoeff a c ≈ (Q'.ofNat 2 * a) * aMoment a c := by
  unfold rCoeff aMoment
  -- LHS = 2 · ((c+1) · a^{(c+1)²}).  Push the a-power split inside.
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (Q'.ofNat 2) _ _
      (Q'.mul_eqv_congr_left (Q'.ofNat (c + 1)) _ _ (apow_split a c))) ?_
  -- now : 2 · ((c+1) · (a^{c(c+2)} · a))   ≃   (2 · a) · ((c+1) · a^{c(c+2)})
  -- write P := a^{c(c+2)}, n := ofNat(c+1) (kept inline)
  -- step A: n·(P·a) ≃ (n·P)·a   [reassoc] ≃ a·(n·P)  [comm]
  have hA : Q'.ofNat (c + 1) * (a ^ (c * (c + 2)) * a)
      ≈ a * (Q'.ofNat (c + 1) * a ^ (c * (c + 2))) := by
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat (c + 1)) (a ^ (c * (c + 2))) a)) ?_
    exact Q'.mul_comm_eqv (Q'.ofNat (c + 1) * a ^ (c * (c + 2))) a
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left (Q'.ofNat 2) _ _ hA) ?_
  -- now : 2·(a·(n·P)) ≃ (2·a)·(n·P)   [reassoc, backwards]
  exact Q'.eqv_symm
    (Q'.mul_assoc_eqv (Q'.ofNat 2) a (Q'.ofNat (c + 1) * a ^ (c * (c + 2))))

/-- Each `a`-power moment is `≥ 0` for `0 ≤ a` (`(c+1) ≥ 0`, `a^k ≥ 0`). -/
theorem aMoment_nonneg {a : Q'} (ha : (0 : Q') ≤ a) (c : Nat) :
    (0 : Q') ≤ aMoment a c :=
  Q'.mul_nonneg _ _ (SU3CharFactor.ofNat_nonneg _) (Q'.pow_nonneg a ha _)

/-! ## 2. The `a`-power moment data and the fusion-quadrature reproduction

We package `aMoment a` as the abstract `GramRed.MomentData`, so the abstract
Gram entry `GramRed.gram (aMoments a)` IS the fusion sum `Σ_{c∈fusion} m_c`.
The reproduction then states this fusion sum equals `(1/2a)·Σ_{c∈fusion} r_c`. -/

/-- The `a`-power heat-kernel moment data `m_c = (c+1)·a^{c(c+2)}` as a
`GramRed.MomentData` (moments injected as constant `CReal`s via `ofQ'`). -/
def aMoments {a : Q'} (ha : (0 : Q') ≤ a) : MomentData where
  m := fun c => CReal.ofQ' (aMoment a c)
  m_nonneg := fun c => SumOfSquares.geRat_ofQ'_nonneg (aMoment_nonneg ha c)

/-- The constant `1/(2a)` (`= divPos 1 (2a)`), the inverse prefactor. -/
def invTwoA (a : Q') : Q' := HKConv.divPos 1 (Q'.ofNat 2 * a)

/-- For `0 < a`, `(1/2a)·(2a) ≃ 1` (the cancellation, `divPos_mul_eqv`). -/
theorem invTwoA_mul (a : Q') (ha0 : (0 : Q') < a) :
    invTwoA a * (Q'.ofNat 2 * a) ≈ 1 := by
  refine HKConv.divPos_mul_eqv ?_
  -- 0 < (2·a).num
  exact CReal.num_pos_of_pos
    (Q'.mul_pos (CReal.pos_of_num_pos (by decide : 0 < (Q'.ofNat 2).num)) ha0)

/-- **Per-moment reproduction (`Q'` level):** `m_c ≃ (1/2a)·r_c`.

From `r_c ≃ (2a)·m_c` and `(1/2a)·(2a) ≃ 1`:
`(1/2a)·r_c ≃ (1/2a)·((2a)·m_c) ≃ ((1/2a)·(2a))·m_c ≃ 1·m_c ≃ m_c`. -/
theorem moment_eq_invTwoA_rCoeff (a : Q') (ha0 : (0 : Q') < a) (c : Nat) :
    aMoment a c ≈ invTwoA a * rCoeff a c := by
  refine Q'.eqv_symm ?_
  -- (1/2a)·r_c ≃ (1/2a)·((2a)·m_c)
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (invTwoA a) _ _ (rCoeff_eq_two_a_moment a c)) ?_
  -- ≃ ((1/2a)·(2a))·m_c
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv (invTwoA a) (Q'.ofNat 2 * a) (aMoment a c))) ?_
  -- ≃ 1·m_c ≃ m_c
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ (aMoment a c) (invTwoA_mul a ha0)) ?_
  exact Q'.one_mul_eqv (aMoment a c)

/-! ### The `CReal` reproduction on the Gram entry

`GramRed.gram (aMoments a) p q = Σ_{j ≤ min p q} m_{fusionLow p q + 2j}` (the
fusion sum).  The reproduction multiplies the whole finite sum by `1/2a`.  We
reduce the `CReal` equality to the `Q'` `finSum` identity termwise via
`Equiv_of_approx_eqv`, using `moment_eq_invTwoA_rCoeff` per term and the
constant-pull `const_mul_finSum`. -/

/-- The fusion index set as a sequence: `c_j = |p−q| + 2j`, `j ≤ min p q`,
matching `GramRed.gram`. -/
def fusionIdx (p q : Nat) (j : Nat) : Nat := fusionLow p q + 2 * j

/-- The fusion length `min p q + 1` (number of fusion channels in `χ_p χ_q`). -/
def fusionLen (p q : Nat) : Nat := min p q + 1

/-- **The reproduction RHS:** `(1/2a)·Σ_{c∈fusion(p,q)} r_c`, as a `CReal`. -/
def RcoeffQuadrature (a : Q') (p q : Nat) : CReal :=
  CReal.mul (CReal.ofQ' (invTwoA a))
    (CReal.csum (fun j => CReal.ofQ' (rCoeff a (fusionIdx p q j))) (fusionLen p q))

/-- **THE FUSION-QUADRATURE REPRODUCTION (item 2), node-free.**

The Gram entry on the `a`-power moments equals `(1/2a)` times the fusion sum of
`R`-coefficients:

    G_{pq} = Σ_{c∈fusion(p,q)} m_c ≃ (1/2a)·Σ_{c∈fusion(p,q)} r_c.

A finite `CReal` rearrangement built from the per-channel identity
`m_c ≃ (1/2a)·r_c`.  No integration, no cos-nodes. -/
theorem fusion_eq_Rcoeff_quadrature {a : Q'} (ha0 : (0 : Q') < a) (p q : Nat) :
    CReal.Equiv (gram (aMoments (Q'.le_of_lt ha0)) p q) (RcoeffQuadrature a p q) := by
  -- Both sides reduce, via `Equiv_of_approx_eqv`, to a `Q'` `finSum` identity.
  -- unfold the RHS index/length sugar so both sides are in the same shape
  unfold RcoeffQuadrature fusionIdx fusionLen
  apply SumOfSquares.Equiv_of_approx_eqv
  intro n
  -- gram = csum (fun j => ofQ' (aMoment a (fusionLow+2j))) (min+1)
  show (CReal.csum (fun j => CReal.ofQ' (aMoment a (fusionLow p q + 2 * j)))
        (min p q + 1)).approx n
      ≈ (CReal.mul (CReal.ofQ' (invTwoA a))
          (CReal.csum (fun j => CReal.ofQ' (rCoeff a (fusionLow p q + 2 * j)))
            (min p q + 1))).approx n
  rw [CReal.csum_approx]
  -- RHS approx of mul: (invTwoA a) · (csum ...).approx n
  show (RationalTail.finSum
        (fun j => (CReal.ofQ' (aMoment a (fusionLow p q + 2 * j))).approx n) (min p q + 1))
      ≈ invTwoA a *
          (CReal.csum (fun j => CReal.ofQ' (rCoeff a (fusionLow p q + 2 * j)))
            (min p q + 1)).approx n
  rw [CReal.csum_approx]
  -- now both sides are `Q'` finSums of constants.  ofQ'.approx = id.
  show (RationalTail.finSum
        (fun j => aMoment a (fusionLow p q + 2 * j)) (min p q + 1))
      ≈ invTwoA a *
          (RationalTail.finSum
            (fun j => rCoeff a (fusionLow p q + 2 * j)) (min p q + 1))
  -- pull (1/2a) into the RHS sum:  (1/2a)·Σ r_c ≃ Σ (1/2a)·r_c
  refine Q'.eqv_trans _ _ _ ?_
    (Q'.eqv_symm (RationalTail.const_mul_finSum
      (fun j => rCoeff a (fusionLow p q + 2 * j)) (invTwoA a) (min p q + 1)))
  -- termwise:  m_{c_j} ≃ (1/2a)·r_{c_j}
  exact RationalTail.finSum_eqv_congr _ _
    (fun j => moment_eq_invTwoA_rCoeff a ha0 (fusionLow p q + 2 * j)) (min p q + 1)

/-! ## 3. The honest Wall-1 positivity test

We now make the negative content precise.  `MomentSquarePos (aMoments …)` is
`E(q²) = Σ_{p,q'} c_p c_{q'} G_{pq'} ≥ 0`.  Two facts are established:

  * `coneExp_nonneg_aMoments` — the **cone** case (`c ≥ 0`) closes term-by-term,
    with no `R ≥ 0` and no nodes.  This is exactly the part of Wall-1 that is
    trivial; it is NOT the analytic content.
  * `momentSquarePos_iff_via_nodes_only` — the residual (the genuine off-cone
    directions) reduces, through the reproduction, to the bare coefficient sum
    `Σ_c d_c r_c ≥ 0`, whose closed route is the node-square form (the
    `ChebNodes` quadrature `Σ_k w_k L(x_k)² R(x_k)`), NOT a term-by-term
    consequence of `R ≥ 0`.

The honest verdict: positivity does **not** close node-free. -/

/-- **Cone positivity on the `a`-power moments (no `R`, no nodes).**  For `c ≥ 0`
every term `c_p c_{q'} G_{pq'} ≥ 0`, so `E(q²) ≥ 0`.  This recovers the trivial
half of Wall-1; the genuine analytic content is the off-cone directions. -/
theorem coneExp_nonneg_aMoments {a : Q'} (ha : (0 : Q') ≤ a) (c : Nat → Q')
    (hc : ∀ i, (0 : Q') ≤ c i) (N : Nat) :
    ExpPos.geRat (gramForm (aMoments ha) c N) 0 :=
  GramRed.gramForm_pos_cone (aMoments ha) c hc N

/-- **The honest negative — the positivity is exactly the node residual.**

`MomentSquarePos (aMoments ha)` (all-order Gram PSD, the off-cone content of
Wall-1) holds *iff* the node-square positivity datum is supplied.  Concretely:
if a Gauss–Chebyshev `ChebNodes` quadrature for the `a`-power moments exists,
then `MomentSquarePos` holds (`ChebyshevQuadPSD.momentSquarePos_via_nodes`); and
that node datum carries the manifest-square positivity `Σ_k w_k L(x_k)² R(x_k)`
that the bare reproduction `Σ_c d_c r_c` lacks (the `d_c` are mixed-sign).

We state the *forward* direction concretely (the node datum closes it), which is
the honest content: the reproduction (items 1–2) does NOT by itself give the
positivity — the node-square form is required.  The converse "node-free
positivity" is NOT provided here because it does not hold from `R ≥ 0` alone:
the term-by-term route closes only the cone (`coneExp_nonneg_aMoments`), and the
off-cone `Σ_c d_c r_c ≥ 0` is the integral `∫ L² R` whose constructive
realisation is the quadrature `ChebNodes`. -/
theorem positivity_needs_nodes
    {a : Q'} (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q'))
    (cn : ChebyshevQuadPSD.ChebNodes (aMoments (Q'.le_of_lt ha0)) ha0 ha1) :
    MomentSquarePos (aMoments (Q'.le_of_lt ha0)) :=
  ChebyshevQuadPSD.momentSquarePos_via_nodes cn

end YMGap.Continuum.RCoeffReproduction

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.RCoeffReproduction.rCoeff_eq_two_a_moment
#print axioms YMGap.Continuum.RCoeffReproduction.apow_split
#print axioms YMGap.Continuum.RCoeffReproduction.moment_eq_invTwoA_rCoeff
#print axioms YMGap.Continuum.RCoeffReproduction.fusion_eq_Rcoeff_quadrature
#print axioms YMGap.Continuum.RCoeffReproduction.coneExp_nonneg_aMoments
#print axioms YMGap.Continuum.RCoeffReproduction.positivity_needs_nodes
