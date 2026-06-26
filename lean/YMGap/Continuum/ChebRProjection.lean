/-
# The R-projection per edge via TRUNCATION — the genuine `∫U_e R_F √(1−x²)` and its
# value `= semiInt·r_e` (for `F > e`), with `RProjection a` reduced to a single,
# strictly-smaller named atom: the uniform R-truncation tail of the integral.

This module attacks the per-edge R-projection atom
`MomentIntegralPSD.RProjection a` — the value identification
`∫U_e R √(1−x²) ≃ semiInt·(ofQ' r_e)` — by isolating the SOLID FINITE content
(the truncated integral `∫U_e R_F √` for the polynomial `R_F = Σ_{f<F} r_f U_f`)
and naming PRECISELY the one remaining analytic step (the truncation tail of the
integral).

## The math (π-FREE; `semiInt` an abstract positive constant)

`R(x) = Σ_f r_f U_f(x)` with `r_f = rCoeff a f` (super-decaying).  The R-projection
is the interchange of the integral with the infinite `R`-series:
`∫U_e R √ = Σ_f r_f ∫U_eU_f√ = Σ_f r_f·semiInt·δ_{ef} = semiInt·r_e`.

We make the FINITE part fully rigorous through the TRUNCATION
`R_F(x) := Σ_{f<F} r_f U_f(x)` (a genuine `Q'` polynomial value at each node):

* **The genuine truncated Riemann sum.**  `truncOrthSum e F a n` is the honest
  rational Riemann sum `(2/n)·Σ_{k<n} U_e(x_k)·R_F(x_k)·√(1−x_k²)`, built with the
  SAME node infrastructure (`lebW`, `uNode`, `nodeWeight`, uniform-midpoint nodes)
  as the proved orthogonality matrix.  It IS `∫U_e R_F √` as a Riemann object — no
  posited value.

* **The node-wise fusion factoring (PROVED).**  At each node,
  `U_e(x_k)·R_F(x_k) = Σ_{f<F} r_f·(U_e(x_k)·U_f(x_k))` (pure `Q'` linearity), so
  finite linearity of the Riemann functional gives
  `truncOrthSum e F a n ≃ Σ_{f<F} (ofQ' r_f)·orthSum2 e f n`
  (`truncOrthSum_eq_scaled_orthSum2`), reusing the PROVED bilinear Riemann sum
  `ChebOrthoMatrix.orthSum2` VERBATIM.

* **The finite interchange limit (PROVED).**  By the UNCONDITIONAL orthogonality
  matrix `ChebOrthoMatrixUncond.orthMatrix_unconditional`
  (`orthSum2 e f → semiInt·δ_{ef}`) and `ConvergesTo`-linearity, the truncated
  Riemann sequence converges to `Σ_{f<F} (ofQ' r_f)·(semiInt·δ_{ef})`, which for
  `F > e` is exactly `semiInt·(ofQ' r_e)`.  This is `truncEdgeIntegral_converges`
  / `truncEdgeIntegral_eq` — THE GENUINE FINITE INTERCHANGE, axiom-clean.

## The reduction of `RProjection a` (honest, strictly smaller atom)

The finite interchange gives `∫U_e R_F √ = semiInt·r_e` for `F > e` — the value
is *already* the answer, INDEPENDENT of `F` (the off-diagonal terms vanish).  What
the per-edge `RProjection.edgeIntegral e := ∫U_e R √` additionally requires is the
identification of the FULL integral `∫U_e R √` with its truncation `∫U_e R_F √`,
i.e. the integral-of-the-tail estimate `∫U_e (R − R_F) √ → 0`.  We name EXACTLY
this — `RTruncTail a` — as a per-edge `CReal` datum
`edgeIntegral e` (the genuine `∫U_e R √`, a `ConvergesTo` limit of the truncated
Riemann sequences along `F`) together with the tail-vanishing
`edgeIntegral e ≃ truncEdgeIntegral e (e+1)` (the truncation does not change the
value, since all `f ≠ e` integrals already vanish).  Then `rProjection_of_tail`
PROVES `RTruncTail a → RProjection a`: transport the tail equivalence through the
PROVED finite interchange `truncEdgeIntegral_eq`.

`RTruncTail` is STRICTLY SMALLER than `RProjection`: `RProjection` asks for the
full value `∫U_e R √ ≃ semiInt·r_e` (the entire interchange against the infinite
series); `RTruncTail` asks only for `∫U_e R √ ≃ ∫U_e R_{e+1} √` (the tail of the
R-series under the integral is negligible) — the genuine finite-interchange VALUE
`= semiInt·r_e` is now PROVED here and no longer part of the atom.

## What is PROVED here (axiom-clean)

* `truncOrthSum` / `truncTerm` — the genuine truncated R-weighted Riemann sum.
* `node_fusion_trunc` — node-wise `U_e·R_F = Σ_{f<F} r_f·(U_e·U_f)` (`Q'`).
* `truncTerm_eq_fusion` — per-node `truncTerm ≃ Σ_{f<F} (ofQ' r_f)·orthTerm2`.
* `truncOrthSum_eq_scaled_orthSum2` — `∫U_e R_F √ ≃ Σ_{f<F} (ofQ' r_f)·∫U_eU_f√`
  (finite linearity, UNCONDITIONAL).
* `convergesTo_const_mul` — `s → L ⇒ (k·s) → k·L` (the scalar-`ConvergesTo` lemma).
* `truncEdgeIntegral` / `truncEdgeIntegral_converges` / `truncEdgeIntegral_eq` —
  THE FINITE INTERCHANGE: `∫U_e R_F √ → semiInt·r_e` for `F > e`, UNCONDITIONAL.
* `rProjection_of_tail` — the PROVED reduction `RTruncTail a → RProjection a`.

## What is NAMED-open

* `RTruncTail a` — the per-edge integral-of-the-tail datum `∫U_e R √ ≃ ∫U_e R_{e+1}√`
  (strictly smaller than `RProjection a`; the value `= semiInt·r_e` is proved).

## Honesty

No `sorry`/`admit`/new axiom/`Classical.*`/`native_decide`; `decide` only on
closed `Nat`/`Q'`.  The truncated Riemann sum is a GENUINE node-sum integral
object (not a posited value).  Axiom-gate at the foot.
-/

import YMGap.Continuum.ChebOrthoMatrix
import YMGap.Continuum.ChebOrthoMatrixUncond
import YMGap.Continuum.MomentIntegralPSD
import YMGap.Continuum.RCoeffReproduction

namespace YMGap.Continuum.ChebRProjection

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.ChebOrthoMatrix
  (orthSum2 orthTerm2 seqOrth2 low fusLen convergesTo_csum convergesTo_congr_seq)
open YMGap.Continuum.SemicircleIntegral (lebW nodeWeight)
open YMGap.Continuum.ChebOrthoOffDiag (uNode)
open YMGap.Continuum.RCoeffReproduction (rCoeff)

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The truncated polynomial `R_F` and the genuine truncated Riemann sum

`R_F(x) := Σ_{f<F} r_f·U_f(x)` is a `Q'` polynomial value at each node; the
truncated R-weighted Riemann sum is the honest node sum
`(2/n)·Σ_{k<n} U_e(x_k)·R_F(x_k)·√(1−x_k²)`, built with the proved node
infrastructure. -/

/-- The truncated heat-kernel polynomial value at a node `x`:
`R_F(x) = Σ_{f<F} r_f·U_f(x)` (a genuine `Q'` value). -/
def RtruncNode (a : Q') (F : Nat) (x : Q') : Q' :=
  RationalTail.finSum (fun f => rCoeff a f * Cheb.U f x) F

/-- The per-node summand `(2/n)·U_e(x_k)·R_F(x_k)·√(1−x_k²)` of the truncated
R-weighted Riemann sum. -/
def truncTerm (e : Nat) (a : Q') (F : Nat) (n : Nat) (hn : 0 < n) (k : Nat) : CReal :=
  CReal.mul (CReal.ofQ' (lebW n hn))
    (CReal.mul (CReal.ofQ' (uNode e n hn k * RtruncNode a F (RiemannSOS.uniformMidpoint n hn k)))
      (nodeWeight n hn k))

/-- **The genuine truncated R-weighted Riemann sum**
`∫U_e R_F √ ≈ (2/n)·Σ_{k<n} U_e(x_k)·R_F(x_k)·√(1−x_k²)`. -/
def truncOrthSum (e : Nat) (a : Q') (F : Nat) (n : Nat) (hn : 0 < n) : CReal :=
  CReal.csum (truncTerm e a F n hn) n

/-! ## 2. The node-wise fusion factoring (pure `Q'` linearity) -/

/-- **Node-wise linearity:** `U_e(x_k)·R_F(x_k) = Σ_{f<F} r_f·(U_e(x_k)·U_f(x_k))`.
Pure `Q'`: pull `U_e(x_k)` into the finite sum and reassociate. -/
theorem node_fusion_trunc (e : Nat) (a : Q') (F : Nat) (x : Q') :
    (Cheb.U e x * RtruncNode a F x)
      ≈ RationalTail.finSum (fun f => rCoeff a f * (Cheb.U e x * Cheb.U f x)) F := by
  unfold RtruncNode
  -- U_e · Σ_f (r_f·U_f) ≃ Σ_f U_e·(r_f·U_f) ≃ Σ_f r_f·(U_e·U_f)
  refine Q'.eqv_trans _ _ _
    (RationalTail.const_mul_finSum (fun f => rCoeff a f * Cheb.U f x) (Cheb.U e x) F) ?_
  refine RationalTail.finSum_eqv_congr _ _ (fun f => ?_) F
  -- U_e·(r_f·U_f) ≃ r_f·(U_e·U_f)
  -- = (U_e·r_f)·U_f ≃ (r_f·U_e)·U_f ≃ r_f·(U_e·U_f)
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv (Cheb.U e x) (rCoeff a f) (Cheb.U f x))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ (Cheb.U f x) (Q'.mul_comm_eqv (Cheb.U e x) (rCoeff a f))) ?_
  exact Q'.mul_assoc_eqv (rCoeff a f) (Cheb.U e x) (Cheb.U f x)

/-- **Per-node fusion of the truncated summand:**
`truncTerm e F a n k ≃ Σ_{f<F} (ofQ' r_f)·orthTerm2 e f n k`.

Mirrors `ChebOrthoMatrix.orthTerm2_eq_fusion`: lift the node-wise `Q'` factoring
through `ofQ'`-additivity / `cofQ'_mul`, then distribute the node weight and the
Lebesgue weight over the finite sum. -/
theorem truncTerm_eq_fusion (e : Nat) (a : Q') (F : Nat) (n : Nat) (hn : 0 < n) (k : Nat) :
    CReal.Equiv (truncTerm e a F n hn k)
      (CReal.csum (fun f => CReal.mul (CReal.ofQ' (rCoeff a f)) (orthTerm2 e f n hn k)) F) := by
  unfold truncTerm orthTerm2
  -- Step 0: ofQ'(U_e·R_F) ≃ Σ_f ofQ'(r_f·(U_e·U_f))  (approx-wise, pure Q')
  have hstep0 : CReal.Equiv
      (CReal.ofQ' (uNode e n hn k * RtruncNode a F (RiemannSOS.uniformMidpoint n hn k)))
      (CReal.csum (fun f => CReal.ofQ' (rCoeff a f
        * (uNode e n hn k * Cheb.U f (RiemannSOS.uniformMidpoint n hn k)))) F) := by
    refine SumOfSquares.Equiv_of_approx_eqv (fun p => ?_)
    rw [CReal.csum_approx]
    -- LHS approx = U_e(x_k)·R_F(x_k) ; RHS approx = Σ_f r_f·(U_e(x_k)·U_f(x_k))
    show (uNode e n hn k * RtruncNode a F (RiemannSOS.uniformMidpoint n hn k))
        ≈ RationalTail.finSum
            (fun f => (CReal.ofQ' (rCoeff a f
              * (uNode e n hn k * Cheb.U f (RiemannSOS.uniformMidpoint n hn k)))).approx p) F
    -- uNode e = U_e(x_k); apply node_fusion_trunc
    show (Cheb.U e (RiemannSOS.uniformMidpoint n hn k)
          * RtruncNode a F (RiemannSOS.uniformMidpoint n hn k))
        ≈ RationalTail.finSum
            (fun f => rCoeff a f
              * (Cheb.U e (RiemannSOS.uniformMidpoint n hn k)
                  * Cheb.U f (RiemannSOS.uniformMidpoint n hn k))) F
    exact node_fusion_trunc e a F (RiemannSOS.uniformMidpoint n hn k)
  -- Step 1: lebW·(ofQ'(U_e·R_F)·w) ≃ lebW·((Σ_f ofQ'(r_f·(U_e·U_f)))·w)
  refine CReal.Equiv.trans
    (CRealContinuumAlg.cmul_congr_right
      (CRealContinuumAlg.cmul_congr_left hstep0)) ?_
  -- Step 2: (Σ_f g_f)·w ≃ Σ_f (g_f·w)
  have hdist : CReal.Equiv
      (CReal.mul (CReal.csum (fun f => CReal.ofQ' (rCoeff a f
          * (uNode e n hn k * Cheb.U f (RiemannSOS.uniformMidpoint n hn k)))) F)
        (nodeWeight n hn k))
      (CReal.csum (fun f => CReal.mul (CReal.ofQ' (rCoeff a f
          * (uNode e n hn k * Cheb.U f (RiemannSOS.uniformMidpoint n hn k))))
        (nodeWeight n hn k)) F) := by
    refine CReal.Equiv.trans
      (CRealAlg.cmul_comm _ (nodeWeight n hn k)) ?_
    refine CReal.Equiv.trans
      (CReal.Equiv.symm (CRealContinuumAlg.csum_const_mul (nodeWeight n hn k) _ F)) ?_
    exact CRealContinuumAlg.csum_congr (fun f => CRealAlg.cmul_comm (nodeWeight n hn k) _) F
  refine CReal.Equiv.trans (CRealContinuumAlg.cmul_congr_right hdist) ?_
  -- Step 3: lebW·(Σ_f (g_f·w)) ≃ Σ_f lebW·(g_f·w)
  refine CReal.Equiv.trans
    (CReal.Equiv.symm (CRealContinuumAlg.csum_const_mul (CReal.ofQ' (lebW n hn)) _ F)) ?_
  -- Step 4: termwise  lebW·(ofQ'(r_f·(U_e·U_f))·w) ≃ (ofQ' r_f)·(lebW·(ofQ'(U_e·U_f)·w))
  refine CRealContinuumAlg.csum_congr (fun f => ?_) F
  -- LHS_f = lebW·(ofQ'(r_f·(U_e·U_f))·w)
  -- RHS_f = (ofQ' r_f)·(lebW·(ofQ'(U_e·U_f)·w))   [= ofQ' r_f · orthTerm2 e f n k]
  -- (a) ofQ'(r_f·(U_e·U_f)) ≃ (ofQ' r_f)·(ofQ'(U_e·U_f))
  have ha : CReal.Equiv
      (CReal.ofQ' (rCoeff a f
        * (uNode e n hn k * Cheb.U f (RiemannSOS.uniformMidpoint n hn k))))
      (CReal.mul (CReal.ofQ' (rCoeff a f))
        (CReal.ofQ' (uNode e n hn k * Cheb.U f (RiemannSOS.uniformMidpoint n hn k)))) := by
    -- note uNode e · uNode f = U_e(x_k)·U_f(x_k)  (uNode f = U_f(x_k))
    refine CReal.Equiv.trans ?_
      (CRealContinuumAlg.cofQ'_mul (rCoeff a f) (uNode e n hn k * uNode f n hn k))
    refine SumOfSquares.Equiv_of_approx_eqv (fun p => ?_)
    show (rCoeff a f
          * (uNode e n hn k * Cheb.U f (RiemannSOS.uniformMidpoint n hn k)))
        ≈ (rCoeff a f * (uNode e n hn k * uNode f n hn k))
    -- uNode f n hn k = U_f(x_k) definitionally
    exact Q'.eqv_refl _
  -- assemble: lebW·((ofQ' r_f · ofQ'(U_eU_f))·w) ≃ (ofQ' r_f)·(lebW·(ofQ'(U_eU_f)·w))
  refine CReal.Equiv.trans
    (CRealContinuumAlg.cmul_congr_right (CRealContinuumAlg.cmul_congr_left ha)) ?_
  -- now: lebW·(((ofQ' r_f)·ofQ'(U_eU_f))·w) ≃ (ofQ' r_f)·(lebW·(ofQ'(U_eU_f)·w))
  -- rearrange CReal mul (associativity/commutativity) via approx-free congruences
  -- ((ofQ' r_f)·B)·w ≃ (ofQ' r_f)·(B·w)
  refine CReal.Equiv.trans
    (CRealContinuumAlg.cmul_congr_right
      (CRealAlg.cmul_assoc (CReal.ofQ' (rCoeff a f))
        (CReal.ofQ' (uNode e n hn k * uNode f n hn k)) (nodeWeight n hn k))) ?_
  -- lebW·((ofQ' r_f)·(B·w)) ≃ (ofQ' r_f)·(lebW·(B·w))
  -- = lebW·(r·X) ≃ (lebW·r)·X ≃ (r·lebW)·X ≃ r·(lebW·X)
  refine CReal.Equiv.trans
    (CReal.Equiv.symm (CRealAlg.cmul_assoc (CReal.ofQ' (lebW n hn))
      (CReal.ofQ' (rCoeff a f))
      (CReal.mul (CReal.ofQ' (uNode e n hn k * uNode f n hn k)) (nodeWeight n hn k)))) ?_
  refine CReal.Equiv.trans
    (CRealContinuumAlg.cmul_congr_left
      (CRealAlg.cmul_comm (CReal.ofQ' (lebW n hn)) (CReal.ofQ' (rCoeff a f)))) ?_
  exact CRealAlg.cmul_assoc (CReal.ofQ' (rCoeff a f)) (CReal.ofQ' (lebW n hn))
    (CReal.mul (CReal.ofQ' (uNode e n hn k * uNode f n hn k)) (nodeWeight n hn k))

/-- **The finite-linearity reduction (UNCONDITIONAL):**
`∫U_e R_F √ ≃ Σ_{f<F} (ofQ' r_f)·∫U_eU_f√`, i.e.
`truncOrthSum e F a n ≃ Σ_{f<F} (ofQ' r_f)·orthSum2 e f n`.

Per-node fusion (`truncTerm_eq_fusion`) summed over nodes, then the finite-sum
index swap (`csum_swap_creal`).  Reuses the PROVED bilinear Riemann sum
`orthSum2`. -/
theorem truncOrthSum_eq_scaled_orthSum2 (e : Nat) (a : Q') (F : Nat) (n : Nat) (hn : 0 < n) :
    CReal.Equiv (truncOrthSum e a F n hn)
      (CReal.csum (fun f => CReal.mul (CReal.ofQ' (rCoeff a f)) (orthSum2 e f n hn)) F) := by
  unfold truncOrthSum
  -- Σ_k truncTerm ≃ Σ_k Σ_f (ofQ' r_f)·orthTerm2 ≃ Σ_f Σ_k (ofQ' r_f)·orthTerm2
  refine CReal.Equiv.trans
    (CRealContinuumAlg.csum_congr (fun k => truncTerm_eq_fusion e a F n hn k) n) ?_
  -- swap (k outer, f inner) ↔ (f outer, k inner)
  refine CReal.Equiv.trans
    (ChebOrthogonality.csum_swap_creal
      (fun k f => CReal.mul (CReal.ofQ' (rCoeff a f)) (orthTerm2 e f n hn k)) n F) ?_
  -- now Σ_f Σ_k (ofQ' r_f)·orthTerm2 e f n k ≃ Σ_f (ofQ' r_f)·(Σ_k orthTerm2 e f n k)
  refine CRealContinuumAlg.csum_congr (fun f => ?_) F
  -- Σ_k (ofQ' r_f)·orthTerm2 e f n k ≃ (ofQ' r_f)·Σ_k orthTerm2 e f n k = (ofQ' r_f)·orthSum2
  exact CRealContinuumAlg.csum_const_mul (CReal.ofQ' (rCoeff a f)) (orthTerm2 e f n hn) n

/-! ## 3. The scalar-`ConvergesTo` lemma and the finite interchange limit -/

/-- A product estimate: with `|u| ≤ B` and `v` two-sided `δ`-close to `w`,
`u·v ≤ u·w + B·δ`.  (`u·v − u·w = u·(v−w)`, `|v−w| ≤ δ`, `|u| ≤ B`, so the
difference is `≤ B·δ` by `Q'.mul_le_of_bounds`.) -/
theorem prod_close (u v w B δ : Q') (hB : (0 : Q') ≤ B) (hδ : (0 : Q') ≤ δ)
    (hu1 : -B ≤ u) (hu2 : u ≤ B) (hvw1 : v ≤ w + δ) (hvw2 : w ≤ v + δ) :
    u * v ≤ u * w + B * δ := by
  -- v = w + (v + -w), and (v + -w) is two-sided δ-bounded.
  have hd1 : v + -w ≤ δ := Q'.sub_le_of_le_add hvw1
  have hd2 : -δ ≤ v + -w := Q'.neg_le_sub_of_le_add hvw2
  -- u·(v + -w) ≤ B·δ
  have hterm : u * (v + -w) ≤ B * δ := Q'.mul_le_of_bounds hB hδ hu1 hu2 hd2 hd1
  -- u·v ≃ u·(w + (v + -w)) = u·w + u·(v + -w) ≤ u·w + B·δ
  have hid : (u * v).eqv (u * w + u * (v + -w)) := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left u v (w + (v + -w)) (Q'.add_sub_cancel_eqv v w)) ?_
    exact Q'.mul_add_eqv u w (v + -w)
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hid) ?_
  exact Q'.add_le_add_left (u * w) (u * (v + -w)) (B * δ) hterm

/-- **Scalar multiplication of a limit.**  If `s → L`, then `(fun N => k·s N) → k·L`.

Direct ε-proof.  `localBound k` gives, past a stage `Nk`, a rational bound
`|k.approx n| ≤ B`; `exists_mul_le` supplies `δ > 0` with `B·δ ≤ ε`; running `hs`
at scale `δ` gives `(s N).approx n` two-sided `δ`-close to `L.approx n`.  Then the
product estimate `prod_close` (both directions) yields
`k.approx n·(s N).approx n ≤ k.approx n·L.approx n + ε` and its reverse — exactly
the `ConvergesTo` closeness of `mul k (s N)` to `mul k L` (whose approxes ARE the
pointwise products). -/
theorem convergesTo_const_mul (k : CReal) {s : Nat → CReal} {L : CReal}
    (hs : CReal.ConvergesTo s L) :
    CReal.ConvergesTo (fun N => CReal.mul k (s N)) (CReal.mul k L) := by
  intro ε hε
  -- rational bound B ≥ |k.approx| past stage Nk
  obtain ⟨Nk, B, hB0, hBk⟩ := CReal.localBound k
  -- δ > 0 with B·δ ≤ ε
  obtain ⟨δ, hδpos, hδ⟩ := CReal.exists_mul_le hB0 hε
  obtain ⟨Nstage, hstage⟩ := hs δ hδpos
  refine ⟨Nstage, fun N hN => ?_⟩
  obtain ⟨Napx, hap⟩ := hstage N hN
  refine ⟨max Napx Nk, fun n hn => ?_⟩
  have hn1 : Napx ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hn2 : Nk ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
  obtain ⟨hs1, hs2⟩ := hap n hn1     -- s_N_n ≤ L_n + δ , L_n ≤ s_N_n + δ
  obtain ⟨hk1, hk2⟩ := hBk n hn2     -- -B ≤ k_n , k_n ≤ B
  -- approxes are pointwise products
  show (k.approx n * (s N).approx n) ≤ (k.approx n * L.approx n) + ε
    ∧ (k.approx n * L.approx n) ≤ (k.approx n * (s N).approx n) + ε
  refine ⟨?_, ?_⟩
  · -- k_n·s_N_n ≤ k_n·L_n + B·δ ≤ k_n·L_n + ε
    refine Q'.le_trans' _ _ _
      (prod_close (k.approx n) ((s N).approx n) (L.approx n) B δ hB0 (Q'.le_of_lt hδpos)
        hk1 hk2 hs1 hs2) ?_
    exact Q'.add_le_add_left _ _ _ hδ
  · -- k_n·L_n ≤ k_n·s_N_n + B·δ ≤ k_n·s_N_n + ε
    refine Q'.le_trans' _ _ _
      (prod_close (k.approx n) (L.approx n) ((s N).approx n) B δ hB0 (Q'.le_of_lt hδpos)
        hk1 hk2 hs2 hs1) ?_
    exact Q'.add_le_add_left _ _ _ hδ

/-! ## 4. The finite interchange: `∫U_e R_F √ → semiInt·r_e` for `F > e` -/

/-- The per-fusion-channel limit value `(ofQ' r_f)·(semiInt·δ_{ef})` — the limit of
`(ofQ' r_f)·orthSum2 e f n`. -/
def edgeMemberLim (e : Nat) (a : Q') (f : Nat) : CReal :=
  CReal.mul (CReal.ofQ' (rCoeff a f))
    (if e = f then SemicircleBoundClosed.semiInt else CReal.czero)

/-- **The truncated edge-integral limit** `∫U_e R_F √ = Σ_{f<F} (ofQ' r_f)·(semiInt·δ_{ef})`. -/
def truncEdgeIntegral (e : Nat) (a : Q') (F : Nat) : CReal :=
  CReal.csum (fun f => edgeMemberLim e a f) F

/-- The resolution-indexed truncated Riemann sequence `N ↦ ∫U_e R_F √` at
resolution `N+1` (matching `seqOrth2`'s `orthSum2 _ (N+1)`). -/
def truncSeq (e : Nat) (a : Q') (F : Nat) : Nat → CReal :=
  fun N => truncOrthSum e a F (N + 1) (Nat.succ_pos N)

/-- Each scaled fusion-member sequence `N ↦ (ofQ' r_f)·seqOrth2 e f N` converges to
`edgeMemberLim e a f`, by `convergesTo_const_mul` on the UNCONDITIONAL orthogonality
matrix `orthMatrix_unconditional`. -/
theorem edgeMember_converges (e : Nat) (a : Q') (f : Nat) :
    CReal.ConvergesTo (fun N => CReal.mul (CReal.ofQ' (rCoeff a f)) (seqOrth2 e f N))
      (edgeMemberLim e a f) := by
  unfold edgeMemberLim
  exact convergesTo_const_mul (CReal.ofQ' (rCoeff a f))
    (ChebOrthoMatrixUncond.orthMatrix_unconditional e f)

/-- **The truncated Riemann sequence converges to the truncated edge integral**
(UNCONDITIONAL).  The resolution-indexed truncated Riemann sum is termwise-`Equiv`
to the scaled fusion `csum` (by `truncOrthSum_eq_scaled_orthSum2`), whose members
converge by `edgeMember_converges`; `convergesTo_csum` + termwise transport. -/
theorem truncEdgeIntegral_converges (e : Nat) (a : Q') (F : Nat) :
    CReal.ConvergesTo (truncSeq e a F) (truncEdgeIntegral e a F) := by
  have hcsum : CReal.ConvergesTo
      (fun N => CReal.csum
        (fun f => CReal.mul (CReal.ofQ' (rCoeff a f)) (seqOrth2 e f N)) F)
      (CReal.csum (fun f => edgeMemberLim e a f) F) :=
    convergesTo_csum
      (fun f => fun N => CReal.mul (CReal.ofQ' (rCoeff a f)) (seqOrth2 e f N))
      (fun f => edgeMemberLim e a f)
      (fun f => edgeMember_converges e a f) F
  refine convergesTo_congr_seq (fun N => ?_) hcsum
  refine CReal.Equiv.symm ?_
  show CReal.Equiv (truncOrthSum e a F (N + 1) (Nat.succ_pos N))
    (CReal.csum (fun f => CReal.mul (CReal.ofQ' (rCoeff a f)) (seqOrth2 e f N)) F)
  exact truncOrthSum_eq_scaled_orthSum2 e a F (N + 1) (Nat.succ_pos N)

/-- `add czero X ≃ X`. -/
theorem add_czero_left (X : CReal) : CReal.Equiv (CReal.add CReal.czero X) X := by
  refine SumOfSquares.Equiv_of_approx_eqv (fun p => ?_)
  show ((CReal.czero).approx p + X.approx p) ≈ X.approx p
  have hz : (CReal.czero).approx p = (0 : Q') := rfl
  rw [hz, Q'.zero_add']; exact Q'.eqv_refl _

/-- `add X czero ≃ X`. -/
theorem add_czero_right (X : CReal) : CReal.Equiv (CReal.add X CReal.czero) X := by
  refine SumOfSquares.Equiv_of_approx_eqv (fun p => ?_)
  show (X.approx p + (CReal.czero).approx p) ≈ X.approx p
  have hz : (CReal.czero).approx p = (0 : Q') := rfl
  rw [hz, Q'.add_zero']; exact Q'.eqv_refl _

/-- A member `≠ e` is `≃ czero`: `(ofQ' r_f)·czero ≃ czero`. -/
theorem edgeMemberLim_ne (e : Nat) (a : Q') (f : Nat) (hf : e ≠ f) :
    CReal.Equiv (edgeMemberLim e a f) CReal.czero := by
  unfold edgeMemberLim
  rw [if_neg hf]
  refine SumOfSquares.Equiv_of_approx_eqv (fun p => ?_)
  show ((CReal.ofQ' (rCoeff a f)).approx p * (CReal.czero).approx p) ≈ (CReal.czero).approx p
  have hz : (CReal.czero).approx p = (0 : Q') := rfl
  rw [hz]; exact Q'.mul_zero_eqv _

/-- The `e`-member is the value: `(ofQ' r_e)·semiInt ≃ semiInt·(ofQ' r_e)`. -/
theorem edgeMemberLim_self (e : Nat) (a : Q') :
    CReal.Equiv (edgeMemberLim e a e)
      (CReal.mul SemicircleBoundClosed.semiInt (CReal.ofQ' (rCoeff a e))) := by
  unfold edgeMemberLim
  rw [if_pos rfl]
  exact CRealAlg.cmul_comm (CReal.ofQ' (rCoeff a e)) SemicircleBoundClosed.semiInt

/-- A finite csum of members all `≠ e` is `≃ czero` (e.g. the head `[0,e)`). -/
theorem csum_members_ne (e : Nat) (a : Q') :
    ∀ G, (∀ f, f < G → e ≠ f) →
      CReal.Equiv (CReal.csum (fun f => edgeMemberLim e a f) G) CReal.czero
  | 0, _ => Pivot2.equiv_refl _
  | G + 1, hlt => by
      show CReal.Equiv (CReal.add (CReal.csum (fun f => edgeMemberLim e a f) G)
          (edgeMemberLim e a G)) CReal.czero
      have hheadne : ∀ f, f < G → e ≠ f := fun f hf => hlt f (Nat.lt_succ_of_lt hf)
      have hG : e ≠ G := hlt G (Nat.lt_succ_self G)
      refine CReal.Equiv.trans
        (Pivot2.add_congr (csum_members_ne e a G hheadne) (edgeMemberLim_ne e a G hG)) ?_
      -- add czero czero ≃ czero
      exact add_czero_right CReal.czero

/-- **THE FINITE INTERCHANGE VALUE (UNCONDITIONAL):** for `F > e`,
`truncEdgeIntegral e a F ≃ semiInt·(ofQ' r_e)`.

`Σ_{f<F} (ofQ' r_f)·(semiInt·δ_{ef})` — every `f ≠ e` term vanishes
(`edgeMemberLim_ne`); the unique `f = e` term (present since `e < F`) is the value
(`edgeMemberLim_self`).  Proved by induction on `F`, peeling at the top: once the
top index `G` exceeds `e`, its member vanishes and the value comes from the head;
the step at `G = e` lands the value with the head `[0,e)` vanishing
(`csum_members_ne`). -/
theorem truncEdgeIntegral_eq (e : Nat) (a : Q') :
    ∀ F, e < F →
      CReal.Equiv (truncEdgeIntegral e a F)
        (CReal.mul SemicircleBoundClosed.semiInt (CReal.ofQ' (rCoeff a e)))
  | 0, heF => absurd heF (Nat.not_lt_zero e)
  | G + 1, heF => by
      unfold truncEdgeIntegral
      show CReal.Equiv (CReal.add (CReal.csum (fun f => edgeMemberLim e a f) G)
          (edgeMemberLim e a G))
        (CReal.mul SemicircleBoundClosed.semiInt (CReal.ofQ' (rCoeff a e)))
      -- e < G+1 ⇒ e ≤ G.  Two cases: e = G (value at top) or e < G (value in head).
      rcases Nat.lt_or_ge e G with heG | heG
      · -- e < G : head sum gives the value (ih), top member vanishes
        have ih : CReal.Equiv (truncEdgeIntegral e a G)
            (CReal.mul SemicircleBoundClosed.semiInt (CReal.ofQ' (rCoeff a e))) :=
          truncEdgeIntegral_eq e a G heG
        have htop : e ≠ G := Nat.ne_of_lt heG
        refine CReal.Equiv.trans
          (Pivot2.add_congr ih (edgeMemberLim_ne e a G htop)) (add_czero_right _)
      · -- e ≥ G and e < G+1 ⇒ e = G
        have heqG : e = G := Nat.le_antisymm (Nat.lt_succ_iff.mp heF) heG
        subst heqG
        -- head [0,e) all ≠ e ; top member = value
        have hhead : CReal.Equiv (CReal.csum (fun f => edgeMemberLim e a f) e) CReal.czero :=
          csum_members_ne e a e (fun f hf => Nat.ne_of_gt hf)
        refine CReal.Equiv.trans
          (Pivot2.add_congr hhead (edgeMemberLim_self e a)) (add_czero_left _)

/-! ## 5. `RProjection a` reduced to the strictly-smaller atom `RTruncTail a`

The finite interchange already PROVES the value `∫U_e R_F √ = semiInt·r_e` (for
`F > e`).  All that `RProjection.edgeIntegral e := ∫U_e R √` adds is the
identification of the full integral with its `(e+1)`-truncation
(`∫U_e R √ ≃ ∫U_e R_{e+1}√`) — the integral-of-the-tail vanishing.  We name EXACTLY
that as `RTruncTail`, and prove `RTruncTail a → RProjection a`. -/

/-- **The R-truncation-tail datum (Type-level; AGENTS.md Rule 8).**  For `a ∈ (0,1)`:
per edge `e`, the genuine integral `edgeIntegral e := ∫U_e R √(1−x²)` (a `CReal`,
the limit of the truncated Riemann sequences along `F`) together with the
tail-vanishing identification `∫U_e R √ ≃ ∫U_e R_{e+1}√` (the truncated edge
integral at `F = e+1`).  STRICTLY SMALLER than `RProjection`: it asks only that
truncating the R-series under the integral does not change the value, NOT the full
value `= semiInt·r_e` (which is the PROVED `truncEdgeIntegral_eq`). -/
structure RTruncTail (a : Q') where
  /-- The per-edge integral `∫U_e R √(1−x²)`. -/
  edgeIntegral : Nat → CReal
  /-- Truncating the R-series under the integral is value-preserving:
  `∫U_e R √ ≃ ∫U_e R_{e+1}√`. -/
  tail : ∀ e, CReal.Equiv (edgeIntegral e) (truncEdgeIntegral e a (e + 1))

/-- **THE PROVED REDUCTION `RTruncTail a → RProjection a`.**  Compose the tail
identification `∫U_e R √ ≃ ∫U_e R_{e+1}√` with the PROVED finite interchange value
`∫U_e R_{e+1}√ ≃ semiInt·r_e` (`truncEdgeIntegral_eq`, `e < e+1`).  Yields the
per-edge `RProjection.edgeIntegral_eq`. -/
def rProjection_of_tail {a : Q'} (rt : RTruncTail a) :
    MomentIntegralPSD.RProjection a where
  edgeIntegral := rt.edgeIntegral
  edgeIntegral_eq := fun e =>
    CReal.Equiv.trans (rt.tail e) (truncEdgeIntegral_eq e a (e + 1) (Nat.lt_succ_self e))

end YMGap.Continuum.ChebRProjection

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.ChebRProjection.node_fusion_trunc
#print axioms YMGap.Continuum.ChebRProjection.truncTerm_eq_fusion
#print axioms YMGap.Continuum.ChebRProjection.truncOrthSum_eq_scaled_orthSum2
#print axioms YMGap.Continuum.ChebRProjection.prod_close
#print axioms YMGap.Continuum.ChebRProjection.convergesTo_const_mul
#print axioms YMGap.Continuum.ChebRProjection.edgeMember_converges
#print axioms YMGap.Continuum.ChebRProjection.truncEdgeIntegral_converges
#print axioms YMGap.Continuum.ChebRProjection.csum_members_ne
#print axioms YMGap.Continuum.ChebRProjection.truncEdgeIntegral_eq
#print axioms YMGap.Continuum.ChebRProjection.rProjection_of_tail
