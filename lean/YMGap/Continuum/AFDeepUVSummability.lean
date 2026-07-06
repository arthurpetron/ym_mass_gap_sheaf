/-
Track B / R2 — **DERIVING the deep-UV block-spin summability `δ_ren,k ∼ 1/k²`
from the PROVED one-loop asymptotic-freedom running.**

# The missing link, now closed (for the one-loop / deep-UV regime)

`RenDefectQuadFactor.bondMovingDeltaRen_le_sixp` proves the per-step renormalized
block-spin defect is QUADRATIC in the weak-coupling margin:

    δ_ren(N,p,w)  ≤  6·p·(1 − w)² .

`NetDriftInvSqBudget.netDriftFloor_of_invSq` proves that a per-step `O(1/k²)`
defect `δ_k ≤ Dδ·1/(k+1)²` (plus anchor-dominance) yields a positive uniform
floor for the dimensionless margin, hence `physGapMin > 0`.

THE LINK between them is the **asymptotic-freedom rate**: the coupling `g_k²` must
decay like `1/(k+1)` in the UV so that `(1 − w_k) ∼ g_k² ∼ 1/(k+1)` and the
quadratic factor gives `δ_ren,k ∼ 1/(k+1)²`.  This module DERIVES that `1/(k+1)`
rate — NOT from a named two-loop recurrence (as `AFReciprocalRate` does), but
DIRECTLY from the PROVED one-loop *linear* inverse-coupling law

    u(k) = u₀ + β₀·k        (`FourDExistence.invRunningCoupling`, β₀ > 0 proved),

so that `g_k² = 1/u(k)`.  The derivation is a clean `Q'` `divPos` monotonicity:
because `u(k) = u₀ + β₀·k` grows linearly and `β₀ > 0`, `1/u(k) ≤ D'/(k+1)`.

# What is PROVED here (axiom-clean, pure `Q'`/`Nat`)

  * `invRunningCoupling_pos` — `u(k) > 0` from `u₀ > 0`, `β₀ ≥ 0`.
  * `af_coupling_invSq` — **THE DERIVED AF RATE.**  From the proved linear law,
    `g_k² = 1/u(k) ≤ D'·1/(k+1)` for any `D'` with `1 ≤ D'·u₀`, `1 ≤ D'·β₀`.
    This GENUINELY uses AF: the `1/(k+1)` decay comes entirely from the `β₀·k`
    term (`β₀ > 0`); with `β₀ = 0`, `u(k)` is constant and `g_k²` does NOT decay.
  * `weight_le_coupling` — compose the DERIVED coupling rate with the NAMED
    weight↔coupling scalar link `(1 − w_k) ≤ C·g_k²` (the heat-kernel dictionary
    `1 − e^{−C·g²} ≤ C·g²`, carried as a hypothesis exactly as `AFReciprocalRate`
    carries `1 − w ≤ τ`) to get `(1 − w_k) ≤ (C·D')·1/(k+1)`.
  * `invSucc_sq_eqv_recipSqSucc` — `(1/(k+1))² ≃ 1/(k+1)²` (the squaring bridge).
  * `af_defect_invSq` — **THE COMPOSED DEEP-UV BOUND.**  Chaining the quadratic
    factorization `bondMovingDeltaRen_le_sixp_invSq` with the squared AF rate,
    `δ_ren,k = bondMovingDeltaRen N p (w k) ≤ Dδ·1/(k+1)²` with the explicit
    `Dδ = 6·p·(C·D')²` (in the un-collapsed `ofNat p·dimQ 1·3·(C·D')²` form).  This
    is the DERIVED per-step `1/k²` scaling that `netDriftFloor_of_invSq` consumes.
  * `af_netDriftFloor` — feeds `af_defect_invSq` into `netDriftFloor_of_invSq`:
    proved-one-loop-AF + quadratic-factorization + named weight link ⟹ the
    positive uniform margin floor.  (The δ-summability slot is DISCHARGED from AF;
    the physical recursion/erosion slots remain named inputs.)

# HONEST SCOPE (what is DERIVED vs what stays OPEN)

  * DERIVED: the deep-UV `δ_ren,k ∼ 1/k²` summability scaling, obtained from the
    ONE-LOOP linear law `u = u₀ + β₀·k` (proved in `FourDExistence`) and the exact
    quadratic factorization of the renormalized bond-moving defect.
  * NAMED (honest inputs, not derived here):
      - the weight↔coupling dictionary `(1 − w_k) ≤ C·g_k²` (heat-kernel model);
      - the physical additive-erosion step law, `ε_k` budget, and anchor-dominance
        (the crossover / no-gap-closing content);
      - the moment-uniformity constant `α < 1` (`FullModeAssembly.hMoment`).
  * OPEN (unchanged): the genuine NONPERTURBATIVE running beyond one-loop, the
    finite crossover `k < K` no-gap-closing, and `hMoment`.  This module does NOT
    close the full YM defect bound — only the deep-UV/one-loop-AF derivation of the
    `1/k²` scaling.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic reusing the proved `invRunningCoupling` linear law, the
`divPos` order characterizations, and the `bondMovingDeltaRen_le_sixp_invSq`
factorization.  Every load-bearing declaration is gated with `#print axioms`;
permitted output is `propext` / `Quot.sound` only.  No `Classical.*`, no
`native_decide`, no `sorry`.  All witnesses are `Type`-level `Q'` data.
-/

import YMGap.Continuum.RenDefectQuadFactor
import YMGap.Continuum.NetDriftInvSqBudget
import YMGap.Continuum.FourDExistence
import YMGap.Continuum.AFRateCalibration

namespace YMGap.Continuum.AFDeepUVSummability

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.SummableInverseSquare
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingQuadratic
open YMGap.Continuum.RenDefectQuadFactor
open YMGap.Continuum.FourDExistence
open YMGap.Continuum.AFRateCalibration
open YMGap.Continuum.HeatKernelRGStep

/-! ## 1. Positivity of the proved one-loop inverse coupling `u(k) = u₀ + β₀·k`. -/

/-- **The inverse running coupling is strictly positive** for `u₀ > 0`, `β₀ ≥ 0`.
`u(k) = u₀ + β₀·(ofNat k) ≥ u₀ > 0` since `β₀·(ofNat k) ≥ 0`. -/
theorem invRunningCoupling_pos {u0 c2adj : Q'} (hu0 : (0 : Q') < u0)
    (hβ : (0 : Q') ≤ betaZero c2adj) (k : Nat) :
    (0 : Q') < invRunningCoupling u0 c2adj k := by
  -- u(k) = u0 + betaZero c2adj * ofNat k
  show (0 : Q') < u0 + betaZero c2adj * Q'.ofNat k
  have hnn : (0 : Q') ≤ betaZero c2adj * Q'.ofNat k :=
    Q'.mul_nonneg _ _ hβ (zero_le_ofNat k)
  exact lt_of_lt_of_le hu0
    (Q'.add_le_self_of_nonneg u0 (betaZero c2adj * Q'.ofNat k) hnn)

/-! ## 2. THE DERIVED AF RATE — `g_k² = 1/u(k) ≤ D'/(k+1)` from the linear law. -/

/-- **`af_coupling_invSq` — the deep-UV coupling rate DERIVED from one-loop AF.**
From the PROVED linear inverse-coupling law `u(k) = u₀ + β₀·k` (`β₀ > 0`), the
running coupling `g_k² = 1/u(k)` obeys the reciprocal `1/(k+1)` decay

    g_k²  =  1/u(k)  ≤  D'·(1/(k+1)) ,

for any `D' ≥ 0` calibrated by `1 ≤ D'·u₀` and `1 ≤ D'·β₀` (both satisfiable, e.g.
`D' = 1/min(u₀,β₀)`).  The decay is genuinely AF-driven: the `k`-growth of the
denominator is entirely the `β₀·k` term (`hDβ` uses `β₀`); with `β₀ = 0` the
coupling would not decay.  Proof: `divPos_le_of_le_mul` reduces to
`1 ≤ (D'·(1/(k+1)))·u(k)`, established from `harmDen 1 k = (k+1) ≤ D'·u(k)` and
`(1/(k+1))·(k+1) ≃ 1`. -/
theorem af_coupling_invSq {u0 c2adj D' : Q'}
    (hD' : (0 : Q') ≤ D') (hDu0 : (1 : Q') ≤ D' * u0)
    (hDβ : (1 : Q') ≤ D' * betaZero c2adj) (k : Nat)
    (hu : (0 : Q') < invRunningCoupling u0 c2adj k) :
    Q'.divPos 1 (invRunningCoupling u0 c2adj k) hu ≤ D' * Q'.invSucc k := by
  -- Sub-lemma A:  harmDen 1 k = (ofNat k + 1)  ≤  D' · u(k).
  -- First: ofNat k ≤ D'·(β·ofNat k).
  have hterm : Q'.ofNat k ≤ D' * (betaZero c2adj * Q'.ofNat k) := by
    -- D'·(β·ofNat k) ≃ (D'·β)·ofNat k ≥ 1·ofNat k ≃ ofNat k.
    have hassoc : (D' * (betaZero c2adj * Q'.ofNat k)).eqv
        ((D' * betaZero c2adj) * Q'.ofNat k) :=
      Q'.eqv_symm (Q'.mul_assoc_eqv D' (betaZero c2adj) (Q'.ofNat k))
    have hmono : (1 : Q') * Q'.ofNat k ≤ (D' * betaZero c2adj) * Q'.ofNat k :=
      Q'.mul_le_mul_of_nonneg_right _ _ _ hDβ (zero_le_ofNat k)
    have hone : ((1 : Q') * Q'.ofNat k).eqv (Q'.ofNat k) := Q'.one_mul_eqv (Q'.ofNat k)
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hone)
      (Q'.le_trans' _ _ _ hmono (Q'.ge_of_eqv hassoc))
  -- Assemble:  ofNat k + 1 ≤ D'·(β·ofNat k) + D'·u0  ≃  D'·u(k).
  have hsum : Q'.ofNat k + 1 ≤ D' * (betaZero c2adj * Q'.ofNat k) + D' * u0 :=
    Q'.le_trans' _ _ _
      (Q'.add_le_add_right _ _ 1 hterm)
      (Q'.add_le_add_left (D' * (betaZero c2adj * Q'.ofNat k)) 1 (D' * u0) hDu0)
  -- D'·(β·ofNat k) + D'·u0 ≃ D'·u0 + D'·(β·ofNat k) ≃ D'·(u0 + β·ofNat k) = D'·u(k).
  have hcollapse : (D' * (betaZero c2adj * Q'.ofNat k) + D' * u0).eqv
      (D' * (u0 + betaZero c2adj * Q'.ofNat k)) := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_comm_eqv (D' * (betaZero c2adj * Q'.ofNat k)) (D' * u0)) ?_
    exact Q'.eqv_symm (Q'.mul_add_eqv D' u0 (betaZero c2adj * Q'.ofNat k))
  have hA : Q'.ofNat k + 1 ≤ D' * (u0 + betaZero c2adj * Q'.ofNat k) :=
    Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv hcollapse)
  -- harmDen 1 k = ofNat k + 1  (defeq).
  have hAharm : harmDen 1 k ≤ D' * (u0 + betaZero c2adj * Q'.ofNat k) := hA
  -- Main:  1 ≤ (D'·invSucc k)·u(k).
  refine Q'.divPos_le_of_le_mul 1 (invRunningCoupling u0 c2adj k) hu ?_
  -- u(k) is defeq to u0 + betaZero c2adj * ofNat k.
  show (1 : Q') ≤ (D' * Q'.invSucc k) * (u0 + betaZero c2adj * Q'.ofNat k)
  -- (D'·invSucc k)·u(k) ≃ invSucc k·(D'·u(k)).
  have hrearr : ((D' * Q'.invSucc k) * (u0 + betaZero c2adj * Q'.ofNat k)).eqv
      (Q'.invSucc k * (D' * (u0 + betaZero c2adj * Q'.ofNat k))) := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ (u0 + betaZero c2adj * Q'.ofNat k)
        (Q'.mul_comm_eqv D' (Q'.invSucc k))) ?_
    exact Q'.mul_assoc_eqv (Q'.invSucc k) D' (u0 + betaZero c2adj * Q'.ofNat k)
  -- invSucc k·(harmDen 1 k) ≤ invSucc k·(D'·u(k)).
  have hmul : Q'.invSucc k * harmDen 1 k
      ≤ Q'.invSucc k * (D' * (u0 + betaZero c2adj * Q'.ofNat k)) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hAharm (Q'.invSucc_nonneg k)
  -- invSucc k·(harmDen 1 k) ≃ 1.
  have hone1 : (Q'.invSucc k * harmDen 1 k).eqv 1 := invSucc_mul_harmDen_one_eqv k
  -- Chain: 1 ≃ invSucc k·harmDen ≤ invSucc k·(D'·u(k)) ≃ (D'·invSucc k)·u(k).
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hone1)
    (Q'.le_trans' _ _ _ hmul (Q'.ge_of_eqv hrearr))

/-! ## 3. Compose with the NAMED weight↔coupling dictionary link. -/

/-- **`weight_le_coupling` — the per-scale margin rate `(1 − w_k) ≤ (C·D')/(k+1)`.**
Composes the DERIVED coupling rate `af_coupling_invSq` (`g_k² ≤ D'/(k+1)`) with the
NAMED heat-kernel dictionary link `(1 − w_k) ≤ C·g_k²` (`hlink`; the scalar
relation `1 − e^{−C·g²} ≤ C·g²`, carried as input exactly as `AFReciprocalRate`
carries `1 − w ≤ τ`).  Result:

    1 − w_k  ≤  (C·D')·(1/(k+1)) . -/
theorem weight_le_coupling {u0 c2adj C D' : Q'} (w : Nat → Q')
    (hC : (0 : Q') ≤ C) (hD' : (0 : Q') ≤ D')
    (hDu0 : (1 : Q') ≤ D' * u0) (hDβ : (1 : Q') ≤ D' * betaZero c2adj)
    (k : Nat) (hu : (0 : Q') < invRunningCoupling u0 c2adj k)
    (hlink : (1 : Q') - w k ≤ C * Q'.divPos 1 (invRunningCoupling u0 c2adj k) hu) :
    (1 : Q') - w k ≤ (C * D') * Q'.invSucc k := by
  -- 1 − w_k ≤ C·g_k² ≤ C·(D'·invSucc k) ≃ (C·D')·invSucc k.
  have hcoup : C * Q'.divPos 1 (invRunningCoupling u0 c2adj k) hu
      ≤ C * (D' * Q'.invSucc k) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ (af_coupling_invSq hD' hDu0 hDβ k hu) hC
  have hassoc : (C * (D' * Q'.invSucc k)).eqv ((C * D') * Q'.invSucc k) :=
    Q'.eqv_symm (Q'.mul_assoc_eqv C D' (Q'.invSucc k))
  exact Q'.le_trans' _ _ _ hlink
    (Q'.le_trans' _ _ _ hcoup (Q'.le_of_eqv hassoc))

/-! ## 4. The squaring bridge `(1/(k+1))² ≃ 1/(k+1)²`. -/

/-- `(1/(k+1))·(1/(k+1)) ≃ 1/(k+1)²`.  Both are `unit`-shaped with numerator `1`;
the denominators are `(k+1)·(k+1)` on each side.  Cross-product identity. -/
theorem invSucc_sq_eqv_recipSqSucc (k : Nat) :
    (Q'.invSucc k * Q'.invSucc k).eqv (recipSqSucc k) := by
  -- numerators are both 1, denominators both (k+1)*(k+1).
  have hnum : (Q'.invSucc k * Q'.invSucc k).num = 1 := by
    show (Q'.invSucc k).num * (Q'.invSucc k).num = 1
    rw [Q'.invSucc_num]; decide
  have hden : ((Q'.invSucc k * Q'.invSucc k).den : Int) = (((k + 1) * (k + 1) : Nat) : Int) := by
    show (((Q'.invSucc k).den * (Q'.invSucc k).den : Nat) : Int)
        = (((k + 1) * (k + 1) : Nat) : Int)
    rw [Q'.invSucc_den]
  have hrnum : (recipSqSucc k).num = 1 :=
    unit_num ((k + 1) * (k + 1)) (Nat.mul_pos (Nat.succ_pos k) (Nat.succ_pos k))
  have hrden : ((recipSqSucc k).den : Int) = (((k + 1) * (k + 1) : Nat) : Int) :=
    unit_den ((k + 1) * (k + 1)) (Nat.mul_pos (Nat.succ_pos k) (Nat.succ_pos k))
  show (Q'.invSucc k * Q'.invSucc k).num * ((recipSqSucc k).den : Int)
      = (recipSqSucc k).num * ((Q'.invSucc k * Q'.invSucc k).den : Int)
  rw [hnum, hden, hrnum, hrden]

/-! ## 5. Small associativity/commutativity `Q'` glue for the composition. -/

/-- `(a·b)·(c·d) ≃ (a·c)·(b·d)`. -/
theorem mul_mul_mul_comm_eqv (a b c d : Q') :
    ((a * b) * (c * d)).eqv ((a * c) * (b * d)) := by
  -- (a·b)·(c·d) ≃ a·(b·(c·d)) ≃ a·((b·c)·d) ≃ a·((c·b)·d) ≃ a·(c·(b·d)) ≃ (a·c)·(b·d)
  refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv a b (c * d)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left a _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv b c d))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left a _ _
      (Q'.mul_eqv_congr_right _ _ d (Q'.mul_comm_eqv b c))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left a _ _ (Q'.mul_assoc_eqv c b d)) ?_
  exact Q'.eqv_symm (Q'.mul_assoc_eqv a c (b * d))

/-- Pull a fourth factor out to the right:
`a·(b·(c·(d·R))) ≃ (a·(b·(c·d)))·R`. -/
theorem four_factor_assoc (a b c d R : Q') :
    (a * (b * (c * (d * R)))).eqv ((a * (b * (c * d))) * R) := by
  -- c·(d·R) ≃ (c·d)·R
  have h1 : (c * (d * R)).eqv ((c * d) * R) := Q'.eqv_symm (Q'.mul_assoc_eqv c d R)
  -- b·(c·(d·R)) ≃ b·((c·d)·R) ≃ (b·(c·d))·R
  have h2 : (b * (c * (d * R))).eqv ((b * (c * d)) * R) :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left b _ _ h1)
      (Q'.eqv_symm (Q'.mul_assoc_eqv b (c * d) R))
  -- a·(...) ≃ a·((b·(c·d))·R) ≃ (a·(b·(c·d)))·R
  exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left a _ _ h2)
    (Q'.eqv_symm (Q'.mul_assoc_eqv a (b * (c * d)) R))

/-- `((D·i)·(D·i)) ≃ (D·D)·(1/(k+1)²)` for `i = 1/(k+1)`. -/
theorem rr_eqv (D : Q') (k : Nat) :
    (((D * Q'.invSucc k) * (D * Q'.invSucc k))).eqv ((D * D) * recipSqSucc k) := by
  refine Q'.eqv_trans _ _ _ (mul_mul_mul_comm_eqv D (Q'.invSucc k) D (Q'.invSucc k)) ?_
  exact Q'.mul_eqv_congr_left (D * D) _ _ (invSucc_sq_eqv_recipSqSucc k)

/-! ## 6. THE COMPOSED DEEP-UV BOUND `δ_ren,k ≤ Dδ·1/(k+1)²`. -/

/-- The DERIVED per-step scale `Dδ = ofNat p·dimQ 1·3·(C·D')² = 6·p·(C·D')²`. -/
def afDefectScale (C D' : Q') (p : Nat) : Q' :=
  Q'.ofNat p * (dimQ 1 * (Q'.ofNat 3 * ((C * D') * (C * D'))))

theorem afDefectScale_nonneg (C D' : Q') (p : Nat)
    (hC : (0 : Q') ≤ C) (hD' : (0 : Q') ≤ D') : (0 : Q') ≤ afDefectScale C D' p := by
  have hCD : (0 : Q') ≤ C * D' := Q'.mul_nonneg _ _ hC hD'
  have hsq : (0 : Q') ≤ (C * D') * (C * D') := Q'.mul_nonneg _ _ hCD hCD
  refine Q'.mul_nonneg _ _ (zero_le_ofNat p) ?_
  refine Q'.mul_nonneg _ _ (dimQ_nonneg 1) ?_
  exact Q'.mul_nonneg _ _ (zero_le_ofNat 3) hsq

/-- **`af_defect_invSq` — the DERIVED deep-UV per-step `1/k²` defect bound.**

    δ_ren,k  =  bondMovingDeltaRen N p (w k)  ≤  Dδ·(1/(k+1)²),     Dδ = 6·p·(C·D')² ,

composing (i) the exact quadratic factorization `bondMovingDeltaRen_le_sixp_invSq`
(`δ_ren ≤ 6p·r²` for any margin control `1 − w ≤ r`) with (ii) the DERIVED-from-AF
margin rate `weight_le_coupling` (`1 − w_k ≤ (C·D')·1/(k+1)`), squared via
`rr_eqv` into the `1/(k+1)²` shape.  This is exactly the `hδ`-slot shape consumed
by `netDriftFloor_of_invSq`. -/
theorem af_defect_invSq {u0 c2adj C D' : Q'} (w : Nat → Q') (N p : Nat)
    (hC : (0 : Q') ≤ C) (hD' : (0 : Q') ≤ D')
    (hDu0 : (1 : Q') ≤ D' * u0) (hDβ : (1 : Q') ≤ D' * betaZero c2adj)
    (hw0 : ∀ k, (0 : Q') ≤ w k) (hw1 : ∀ k, w k ≤ (1 : Q'))
    (k : Nat) (hu : (0 : Q') < invRunningCoupling u0 c2adj k)
    (hlink : (1 : Q') - w k ≤ C * Q'.divPos 1 (invRunningCoupling u0 c2adj k) hu) :
    bondMovingDeltaRen N p (w k) ≤ afDefectScale C D' p * recipSqSucc k := by
  -- Margin rate:  1 − w_k ≤ (C·D')·invSucc k.
  have hr : (1 : Q') - w k ≤ (C * D') * Q'.invSucc k :=
    weight_le_coupling w hC hD' hDu0 hDβ k hu hlink
  -- Quadratic factorization with r = (C·D')·invSucc k.
  have hb : bondMovingDeltaRen N p (w k)
      ≤ Q'.ofNat p * (dimQ 1 * (Q'.ofNat 3 *
          (((C * D') * Q'.invSucc k) * ((C * D') * Q'.invSucc k)))) :=
    bondMovingDeltaRen_le_sixp_invSq (hw0 k) (hw1 k) hr N p
  -- r² ≃ (C·D')²·recipSqSucc k, then pull recipSqSucc to the right.
  have hrr : (((C * D') * Q'.invSucc k) * ((C * D') * Q'.invSucc k)).eqv
      (((C * D') * (C * D')) * recipSqSucc k) := rr_eqv (C * D') k
  have heq1 : (Q'.ofNat p * (dimQ 1 * (Q'.ofNat 3 *
          (((C * D') * Q'.invSucc k) * ((C * D') * Q'.invSucc k))))).eqv
      (Q'.ofNat p * (dimQ 1 * (Q'.ofNat 3 *
          (((C * D') * (C * D')) * recipSqSucc k)))) :=
    Q'.mul_eqv_congr_left _ _ _
      (Q'.mul_eqv_congr_left _ _ _
        (Q'.mul_eqv_congr_left _ _ _ hrr))
  -- pull recipSqSucc k out of the 4-fold product.
  have heq2 : (Q'.ofNat p * (dimQ 1 * (Q'.ofNat 3 *
          (((C * D') * (C * D')) * recipSqSucc k)))).eqv
      (afDefectScale C D' p * recipSqSucc k) :=
    four_factor_assoc (Q'.ofNat p) (dimQ 1) (Q'.ofNat 3)
      ((C * D') * (C * D')) (recipSqSucc k)
  exact Q'.le_trans' _ _ _ hb
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv heq1) (Q'.le_of_eqv heq2))

/-! ## 7. FEED THE FLOOR — proved-AF + quadratic-factorization ⟹ positive floor. -/

/-- **`af_netDriftFloor` — the deep-UV positive margin floor from ONE-LOOP AF.**

Given the physical additive-erosion recursion (`hstep`, `ε` bounds, anchor) and the
AF-rate inputs (proved linear law via `hDu0`/`hDβ`, weight link `hlink`,
`w_k ∈ [0,1]`), the DERIVED per-step defect `δ_k := bondMovingDeltaRen N p (w k)`
obeys `δ_k ≤ Dδ·1/(k+1)²` (`af_defect_invSq`) and is nonnegative
(`bondMovingDeltaRen_nonneg`), so `netDriftFloor_of_invSq` yields the positive
uniform floor `(1 − 2·Dδ)·margin 0 − 2·Dε > 0` for the dimensionless margin.

The δ-summability slot is DISCHARGED from AF; the `hδ1` cap, the `ε`-budget, and
the `anchor` (the crossover / no-gap-closing content) remain named physical
inputs — this is the honest deep-UV composition, NOT closure of the full bound. -/
theorem af_netDriftFloor {u0 c2adj C D' Dε : Q'}
    (margin ε : Nat → Q') (w : Nat → Q') (N p : Nat)
    (hC : (0 : Q') ≤ C) (hD' : (0 : Q') ≤ D')
    (hDu0 : (1 : Q') ≤ D' * u0) (hDβ : (1 : Q') ≤ D' * betaZero c2adj)
    (hw0 : ∀ k, (0 : Q') ≤ w k) (hw1 : ∀ k, w k ≤ (1 : Q'))
    (hu : ∀ k, (0 : Q') < invRunningCoupling u0 c2adj k)
    (hlink : ∀ k, (1 : Q') - w k
        ≤ C * Q'.divPos 1 (invRunningCoupling u0 c2adj k) (hu k))
    (hstep : ∀ k, (1 - bondMovingDeltaRen N p (w k)) * margin k - ε k ≤ margin (k + 1))
    (hδ1 : ∀ k, bondMovingDeltaRen N p (w k) ≤ 1)
    (hεnn : ∀ k, (0 : Q') ≤ ε k) (hm0 : (0 : Q') ≤ margin 0)
    (hDε : (0 : Q') ≤ Dε) (hε : ∀ k, ε k ≤ Dε * recipSqSucc k)
    (hanchor : 2 * Dε < (1 - 2 * afDefectScale C D' p) * margin 0) :
    ∀ k, (1 - 2 * afDefectScale C D' p) * margin 0 - 2 * Dε ≤ margin k
       ∧ (0 : Q') < (1 - 2 * afDefectScale C D' p) * margin 0 - 2 * Dε :=
  netDriftFloor_of_invSq margin (fun k => bondMovingDeltaRen N p (w k)) ε
    (afDefectScale C D' p) Dε
    hstep
    (fun k => bondMovingDeltaRen_nonneg (hw0 k) (hw1 k) N p)
    hδ1 hεnn hm0
    (afDefectScale_nonneg C D' p hC hD') hDε
    (fun k => af_defect_invSq w N p hC hD' hDu0 hDβ hw0 hw1 k (hu k) (hlink k))
    hε hanchor

end YMGap.Continuum.AFDeepUVSummability

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.AFDeepUVSummability.invRunningCoupling_pos
#print axioms YMGap.Continuum.AFDeepUVSummability.af_coupling_invSq
#print axioms YMGap.Continuum.AFDeepUVSummability.weight_le_coupling
#print axioms YMGap.Continuum.AFDeepUVSummability.invSucc_sq_eqv_recipSqSucc
#print axioms YMGap.Continuum.AFDeepUVSummability.mul_mul_mul_comm_eqv
#print axioms YMGap.Continuum.AFDeepUVSummability.four_factor_assoc
#print axioms YMGap.Continuum.AFDeepUVSummability.rr_eqv
#print axioms YMGap.Continuum.AFDeepUVSummability.afDefectScale_nonneg
#print axioms YMGap.Continuum.AFDeepUVSummability.af_defect_invSq
#print axioms YMGap.Continuum.AFDeepUVSummability.af_netDriftFloor
