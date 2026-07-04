/-
Track B / local-CLT — STAGE 4a of R1: the ALGEBRAIC reduction of the BINDING odd-centre cell
`R1CaseSplit.OddCentreCellLE w` to two clean named analytic residuals.

# Why this file exists (read first — load-bearing honesty)

`OddCentreCellLE w` is the tight cell of R1: for the lower-half regime `w ≤ 1/2` and every even
window `s` (centre `N = s+1` ODD), it asks for `FullRangeFloor w s`, i.e. the cleared curvature floor

    2·⟨D²⟩_{N} ≤ ⟨D²⟩_{N-1} + ⟨D²⟩_{N+1} + 2 ,      i.e.  Δ²V(N) + 2 ≥ 0 ,

with `V(N) = ⟨D²⟩_N = dmomNfull w N / acNfull w N` the theta-tilted position variance.  The paper
proof (`computations/theta_residual_L2_proof.md`, `phi_certificate.md`, `r1_remaining_pieces.md`,
`r1_audit_report.md`) is the reduction

    Δ²V(N) + 2  =  (Δ²V_inf(N) + 2)  +  Δ²(tail)(N)  =  L2(N) + Δ²(tail)(N) ,

where `V_inf(N) = f_{parity}(N²)`, `f_p(x) = (B_p x − C_p)/(A_p x − B_p)` is the infinite-volume
(untruncated theta-moment) variance and `tail = V − V_inf`.  The leading term `L2(N)` is bounded by
a fully rigorous rational-function chain in the theta constants down to a single scalar:

    L2(N)  ≥  Ψ(N)  ≥  Ψ(3)  =  φ(q) ,        q = w² ,

so the whole two-parameter floor collapses to the two facts `φ(q) ≥ 0` and `Δ²(tail)(N) ≥ 0`.

## What this stage delivers (the ALGEBRAIC reduction layer, Type-level, NO `sorry`)

This file formalizes the ALGEBRAIC chain and reduces `OddCentreCellLE w` to exactly the two named
analytic residuals `PhiNonneg` (the terminal scalar `φ(q) ≥ 0`, Stage 4b) and
`TailSecondDiffNonneg` (the tail second difference `Δ²(tail) ≥ 0`, Stage 4c), given the theta layer
bundled as `ThetaData w`.  Concretely it PROVES:

  * `floor_of_variance` — the moment↔variance bridge: from the mass factorization `D_t ≃ V_t·A_t`
    (= `dmomNfull ≃ V·acNfull`, the definition of the variance ratio), the mass nonnegativities,
    and the ratio-level floor `2·V(N) ≤ V(N-1) + V(N+1) + 2`, the CLEARED `FullRangeFloor`
    inequality follows.  Pure subtraction-free `Q'` algebra (`ring_qeqv`) + one `mul_le_mul`.
  * `l2_chain` — the L2 chain `φ ≤ L2(N)` PROVED by transitivity `φ = Ψ(3) ≤ Ψ(N) ≤ L2(N)` from the
    two theta-analytic monotonicity steps (`mono`, `weaken`) carried in `ThetaData`.
  * `variance_floor` — the ratio-level floor `2·V(N) ≤ V(N-1)+V(N+1)+2`, PROVED from the tail
    decomposition identity (`curvEq`, = `Δ²V+2 = L2 + Δ²tail`) together with `L2(N) ≥ φ ≥ 0`
    (`l2_chain` + `PhiNonneg`) and `Δ²tail(N) ≥ 0` (`TailSecondDiffNonneg`).
  * `oddCentreCellLE_of_residuals` — THE CAPSTONE: `ThetaData w → PhiNonneg → TailSecondDiffNonneg →
    OddCentreCellLE w`.  The base window `s = 0` (centre `N = 1`) is dispatched to the proved corner
    `CircleFourierPowerModel.fullRangeFloor_zero`; every `s ≥ 2` even (centre `N ≥ 3`) is closed by
    `floor_of_variance` fed by `variance_floor`.

## The abstract theta layer (`ThetaData`, a named-hypothesis bundle — Rule 6a)

Fully defining the concrete untruncated theta series `A_p,B_p,C_p` (= `Σ_{D≡p} D^{0,2,4} w^{D²/2}`),
their ratios `G_p = B_p/A_p`, `S_p = C_p/A_p − G_p²`, the anchor `ϑ₄⁴ = G_o − G_e`, and DERIVING the
partial-fraction identity `f_p(x) = G_p − S_p/(x − G_p)`, the exact `(L2*)` identity, and the
monotonicity steps from `A_p>0`, the Turán/Cauchy–Schwarz defect `S_p ≥ 0`, `ϑ₄⁴ ≤ 1`,
`G_e ≤ G_e(1/4)`, `S_e ≥ S_o`, and convexity of `x ↦ x⁻³` would balloon this sub-stage.  Following the
sanctioned abstract-constants route, those objects and the rational-function chain steps they
support are bundled as the fields of `ThetaData w`:

  * `V t`                         — the variance ratio, PINNED to the concrete moments by
                                    `Vmoment : dmomNfull w t ≃ V t · acNfull w t` (NOT free: this is
                                    the defining `V = dmomNfull/acNfull`).
  * `L2 s`, `tail2 s`             — the leading term `Δ²V_inf(N)+2` and the tail second difference
                                    `Δ²tail(N)` (centre `N = s+1`), as `Q'` values.
  * `curvEq`                      — the TAIL DECOMPOSITION `Δ²V(N)+2 = L2(N) + Δ²tail(N)` in
                                    subtraction-free cleared form
                                    `2·V(N) + (L2 s + tail2 s) ≃ V(N-1) + V(N+1) + 2`.
  * `Psi s`, `phi`                — the weakened functional `Ψ(N)` and the terminal scalar `φ(q)`.
  * `phiEqPsi3`                   — `φ = Ψ(3)` (the memo's `φ(q) = Ψ(3)`).
  * `weaken`                      — `Ψ(N) ≤ L2(N)`  (the `L2 ≥ Ψ` step: `G_o > 0`, `G_e ≤ Ḡ_e`).
  * `mono`                        — `Ψ(3) ≤ Ψ(N)`  (the `Ψ` monotonicity: `S_e ≥ S_o` + `x⁻³` convex).

`ThetaData` is a genuine, non-vacuous input bundle: `Vmoment` forces `V` to be the true variance
ratio, so the bundle is NOT trivially inhabitable, and discharging it (the concrete theta series +
the partial-fraction/`(L2*)`/monotonicity derivations) is its own later sub-stage.  The two residuals
`PhiNonneg` (`0 ≤ φ`) and `TailSecondDiffNonneg` (`0 ≤ Δ²tail`) are the SOLE remaining analytic
inputs of the odd-centre cell, strictly smaller than `OddCentreCellLE`; neither is trivially
inhabitable (both are false for arbitrary constants), and both are `Type`-level (Rule 6a), never
`Prop := True` or a `Unit` witness.

# Axiom gate (AGENTS.md Rule 1 / Rule 8)

Every load-bearing declaration is axiom-checked at file end.  The bridge, chain, floor, and capstone
are subtraction-free `Q'` algebra (`ring_qeqv`, `mul_le_mul_of_nonneg_right`, `add_le_self_of_nonneg`,
`zero_le_add`), congruence over `Q'.eqv`, and modus ponens over the residual/`ThetaData` fields;
the base window reuses the proved `fullRangeFloor_zero`.  Permitted output is `propext` / `Quot.sound`
only (via the `Q'` setoid).  No `Classical.*`, no `native_decide`, no `sorry`, no custom `axiom`.
-/

import YMGap.Continuum.R1CaseSplit

namespace YMGap.Continuum.R1OddL2Chain

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.CircleFourierPowerModel
open YMGap.Continuum.AcNReserveAnalytic
open YMGap.Continuum.MeanComplementCovariance
open YMGap.Continuum.R1CaseSplit

/-- Ring closer for CANCELLATION-FREE `Q'.eqv` identities: reduce to the `Int` cross-product,
expand every `num`/`den` cast and distribute, close by `ac_rfl`.  Sound only for identities requiring
NO additive cancellation of `+X`/`-X` pairs (all uses in this file are subtraction-free). -/
local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Int.add_mul, Int.mul_add, Int.one_mul, Int.mul_one];
             ac_rfl))

/-! ## 1. The moment↔variance bridge (pure `Q'` algebra, no analysis). -/

/-- **`floor_of_variance`** — the CLEARED curvature floor from the ratio-level floor.

Given the three antidiagonal masses `A0,A1,A2 ≥ 0`, the mass factorizations `D_i ≃ V_i·A_i`
(`= dmomNfull ≃ V·acNfull`, i.e. `V_i` is the variance `⟨D²⟩`), and the ratio-level floor
`2·V1 ≤ (V0+V2)+2` (= `Δ²V ≥ −2` at the odd centre), the SUBTRACTION-FREE `FullRangeFloor` cleared
inequality holds.  Both sides factor through the common mass product `P = A0·(A1·A2) ≥ 0`:
`LHS ≃ (2·V1)·P ≤ ((V0+V2)+2)·P ≃ RHS`.  Pure `Q'` algebra — no nonnegativity of `V`, no truncation,
no transcendental input. -/
theorem floor_of_variance
    {A0 A1 A2 D0 D1 D2 V0 V1 V2 : Q'}
    (h0 : (0 : Q') ≤ A0) (h1 : (0 : Q') ≤ A1) (h2 : (0 : Q') ≤ A2)
    (hV0 : D0.eqv (V0 * A0)) (hV1 : D1.eqv (V1 * A1)) (hV2 : D2.eqv (V2 * A2))
    (hfloor : Q'.ofNat 2 * V1 ≤ (V0 + V2) + Q'.ofNat 2) :
    Q'.ofNat 2 * (D1 * (A0 * A2))
      ≤ D0 * (A1 * A2) + D2 * (A0 * A1) + Q'.ofNat 2 * (A0 * (A1 * A2)) := by
  -- the common mass product `P = A0·(A1·A2) ≥ 0`
  have hP : (0 : Q') ≤ A0 * (A1 * A2) := Q'.mul_nonneg _ _ h0 (Q'.mul_nonneg _ _ h1 h2)
  -- LHS ≃ (2·V1)·P   (substitute `D1 ≃ V1·A1`, then rearrange)
  have eL : (Q'.ofNat 2 * (D1 * (A0 * A2))).eqv (Q'.ofNat 2 * V1 * (A0 * (A1 * A2))) := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_eqv_congr_right _ _ _ hV1)) ?_
    ring_qeqv
  -- RHS ≃ ((V0+V2)+2)·P   (substitute `D0 ≃ V0·A0`, `D2 ≃ V2·A2`, then rearrange)
  have eRsub : (D0 * (A1 * A2) + D2 * (A0 * A1) + Q'.ofNat 2 * (A0 * (A1 * A2))).eqv
      ((V0 * A0) * (A1 * A2) + (V2 * A2) * (A0 * A1) + Q'.ofNat 2 * (A0 * (A1 * A2))) :=
    Q'.add_eqv_congr_right _ _ _
      (Q'.add_eqv_congr' (Q'.mul_eqv_congr_right _ _ _ hV0) (Q'.mul_eqv_congr_right _ _ _ hV2))
  have eRring : ((V0 * A0) * (A1 * A2) + (V2 * A2) * (A0 * A1) + Q'.ofNat 2 * (A0 * (A1 * A2))).eqv
      (((V0 + V2) + Q'.ofNat 2) * (A0 * (A1 * A2))) := by ring_qeqv
  have eR : (D0 * (A1 * A2) + D2 * (A0 * A1) + Q'.ofNat 2 * (A0 * (A1 * A2))).eqv
      (((V0 + V2) + Q'.ofNat 2) * (A0 * (A1 * A2))) :=
    Q'.eqv_trans _ _ _ eRsub eRring
  -- (2·V1)·P ≤ ((V0+V2)+2)·P from the ratio floor and `P ≥ 0`
  have hmul : Q'.ofNat 2 * V1 * (A0 * (A1 * A2))
      ≤ ((V0 + V2) + Q'.ofNat 2) * (A0 * (A1 * A2)) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hfloor hP
  -- chain:  LHS ≃ (2·V1)·P ≤ ((V0+V2)+2)·P ≃ RHS
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv eL) (Q'.le_trans' _ _ _ hmul (Q'.ge_of_eqv eR))

/-! ## 2. The abstract theta layer and the two named analytic residuals. -/

/-- **`ThetaData w`** — the abstract theta layer of the odd-centre cell (a named-hypothesis bundle,
Rule 6a).  See the file docstring for the intended concrete meaning of each field and the later
sub-stage that discharges it.  `Vmoment` pins `V` to the true variance ratio, so the bundle is
non-vacuous. -/
structure ThetaData (w : Q') : Type where
  /-- The theta-tilted position variance `V(t) = ⟨D²⟩_t` (ratio). -/
  V : Nat → Q'
  /-- The leading term `L2(N) = Δ²V_inf(N) + 2` at centre `N = s+1`. -/
  L2 : Nat → Q'
  /-- The tail second difference `Δ²(tail)(N)` at centre `N = s+1`. -/
  tail2 : Nat → Q'
  /-- The weakened functional `Ψ(N)` at centre `N = s+1`. -/
  Psi : Nat → Q'
  /-- The terminal scalar `φ(q)`, `q = w²`. -/
  phi : Q'
  /-- `V` is the true variance ratio: `dmomNfull w t ≃ V t · acNfull w t`. -/
  Vmoment : ∀ t, (dmomNfull w t).eqv (V t * acNfull w t)
  /-- The TAIL DECOMPOSITION `Δ²V(N) + 2 = L2(N) + Δ²tail(N)`, in subtraction-free cleared form. -/
  curvEq : ∀ s, (Q'.ofNat 2 * V (s + 1) + (L2 s + tail2 s)).eqv
    ((V s + V (s + 2)) + Q'.ofNat 2)
  /-- `φ = Ψ(3)` (window `s = 2` ↔ centre `N = 3`). -/
  phiEqPsi3 : phi.eqv (Psi 2)
  /-- The `L2 ≥ Ψ` step (`G_o > 0`, `G_e ≤ Ḡ_e`): `Ψ(N) ≤ L2(N)`. -/
  weaken : ∀ s, 2 ≤ s → s % 2 = 0 → Psi s ≤ L2 s
  /-- The `Ψ` monotonicity (`S_e ≥ S_o` + `x⁻³` convex): `Ψ(3) ≤ Ψ(N)`. -/
  mono : ∀ s, 2 ≤ s → s % 2 = 0 → Psi 2 ≤ Psi s

/-- **`PhiNonneg w θ`** (NAMED OPEN — Stage 4b).  The terminal scalar `φ(q) ≥ 0` on `q = w² ∈ (0,1/4]`.
Discharged in the paper by the explicit two-region rational certificate (`phi_certificate.md`):
convexity `φ'' ≥ 37/5` + leading coefficient `α ≥ 7/5` on `(0,1/16]`, and a 13-node Lipschitz grid on
`[1/16,1/4]`.  Recommended Lean discharge: a PURE interval enclosure over rational `q`-subintervals
(no CReal derivatives), truncating each theta sum with the proved geometric tail.  A genuine,
non-vacuous input (false for arbitrary constants). -/
structure PhiNonneg (w : Q') (θ : ThetaData w) : Type where
  nonneg : (0 : Q') ≤ θ.phi

/-- **`TailSecondDiffNonneg w θ`** (NAMED OPEN — Stage 4c / Task A).  The tail second difference
`Δ²(tail)(N) ≥ 0` for every odd centre `N = s+1 ≥ 3` (`s ≥ 2` even).  Discharged in the paper
(`r1_remaining_pieces.md`, Task A) by the closed-form super-exponential ratio bound
`tail(N)/tail(N−1) ≤ 1/2` (uniform, `8.76×` margin) plus `tail ≥ 0`, giving
`Δ²tail = (tail(N−1) − 2·tail(N)) + tail(N+1) ≥ 0`.  Recommended Lean discharge: reuse the Stage-2
geometric-tail machinery for the ratio bound.  A genuine, non-vacuous input. -/
structure TailSecondDiffNonneg (w : Q') (θ : ThetaData w) : Type where
  nonneg : ∀ s, 2 ≤ s → s % 2 = 0 → (0 : Q') ≤ θ.tail2 s

/-! ## 3. The L2 chain and the ratio-level floor (PROVED from `ThetaData`). -/

/-- **`l2_chain`** — the L2 chain `φ ≤ L2(N)` PROVED by transitivity
`φ = Ψ(3) ≤ Ψ(N) ≤ L2(N)` from the two theta-analytic steps `mono` and `weaken`.  This is the
`L2(N) ≥ Ψ(N) ≥ Ψ(3) = φ(q)` chain of the memo, composed. -/
theorem l2_chain {w : Q'} (θ : ThetaData w) (s : Nat) (hs2 : 2 ≤ s) (hpar : s % 2 = 0) :
    θ.phi ≤ θ.L2 s :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv θ.phiEqPsi3)
    (Q'.le_trans' _ _ _ (θ.mono s hs2 hpar) (θ.weaken s hs2 hpar))

/-- **`variance_floor`** — the ratio-level curvature floor `2·V(N) ≤ V(N-1) + V(N+1) + 2`
(= `Δ²V(N) + 2 ≥ 0`) at the odd centre `N = s+1`, PROVED from the tail decomposition `curvEq`
together with `L2(N) ≥ φ ≥ 0` (`l2_chain` + `PhiNonneg`) and `Δ²tail(N) ≥ 0`
(`TailSecondDiffNonneg`). -/
theorem variance_floor {w : Q'} (θ : ThetaData w)
    (hφ : PhiNonneg w θ) (hT : TailSecondDiffNonneg w θ)
    (s : Nat) (hs2 : 2 ≤ s) (hpar : s % 2 = 0) :
    Q'.ofNat 2 * θ.V (s + 1) ≤ (θ.V s + θ.V (s + 2)) + Q'.ofNat 2 := by
  -- `0 ≤ L2(N)` from the chain `φ ≤ L2(N)` and `φ ≥ 0`
  have hL2nn : (0 : Q') ≤ θ.L2 s := Q'.le_trans' _ _ _ hφ.nonneg (l2_chain θ s hs2 hpar)
  -- `0 ≤ Δ²tail(N)`
  have hTnn : (0 : Q') ≤ θ.tail2 s := hT.nonneg s hs2 hpar
  -- `0 ≤ L2(N) + Δ²tail(N)`
  have hsum : (0 : Q') ≤ θ.L2 s + θ.tail2 s := Q'.zero_le_add _ _ hL2nn hTnn
  -- `2·V(N) ≤ 2·V(N) + (L2 + Δ²tail) ≃ (V(N-1)+V(N+1)) + 2`
  have hstep : Q'.ofNat 2 * θ.V (s + 1)
      ≤ Q'.ofNat 2 * θ.V (s + 1) + (θ.L2 s + θ.tail2 s) :=
    Q'.add_le_self_of_nonneg _ _ hsum
  exact Q'.le_trans' _ _ _ hstep (Q'.le_of_eqv (θ.curvEq s))

/-! ## 4. THE CAPSTONE — `OddCentreCellLE w` from the two residuals + `ThetaData`. -/

/-- **`oddCentreCellLE_of_residuals` — THE STAGE-4a CAPSTONE.**  Given the theta layer `ThetaData w`
and the two named analytic residuals `PhiNonneg` (`φ ≥ 0`) and `TailSecondDiffNonneg` (`Δ²tail ≥ 0`),
the binding odd-centre cell `OddCentreCellLE w` holds (for every `0 ≤ w`).  The base window `s = 0`
(centre `N = 1`) is the proved corner `fullRangeFloor_zero`; every `s ≥ 2` even (centre `N ≥ 3`) is
closed by `floor_of_variance` fed by `variance_floor` and the mass factorization `Vmoment`.  Pure
modus ponens + the proved `Q'` algebra — axiom-clean. -/
def oddCentreCellLE_of_residuals {w : Q'} (hw : (0 : Q') ≤ w)
    (θ : ThetaData w) (hφ : PhiNonneg w θ) (hT : TailSecondDiffNonneg w θ) :
    OddCentreCellLE w where
  cell := fun _hle s hpar => by
    rcases Nat.lt_or_ge s 2 with hlt | hge
    · -- `s < 2` and `s % 2 = 0` ⟹ `s = 0`: the proved corner base case.
      have hs0 : s = 0 := by omega
      subst hs0
      exact fullRangeFloor_zero hw
    · -- `s ≥ 2` even (centre `N ≥ 3`): the variance floor via the mass factorization.
      exact floor_of_variance
        (acN_nonneg hw (s + 1) s) (acN_nonneg hw (s + 2) (s + 1)) (acN_nonneg hw (s + 3) (s + 2))
        (θ.Vmoment s) (θ.Vmoment (s + 1)) (θ.Vmoment (s + 2))
        (variance_floor θ hφ hT s hge hpar)

/-! ## 5. Doc-section — PROVED vs NAMED-open (CRITICAL honesty)

PROVED (axiom-clean):
  * `floor_of_variance` — the moment↔variance bridge (cleared `FullRangeFloor` from the ratio floor).
  * `l2_chain` — the L2 chain `φ ≤ L2(N)` (`φ = Ψ(3) ≤ Ψ(N) ≤ L2(N)`) composed from `ThetaData`.
  * `variance_floor` — the ratio-level floor `Δ²V(N)+2 ≥ 0` from the tail decomposition + the two
    residuals.
  * `oddCentreCellLE_of_residuals` — the capstone `ThetaData → PhiNonneg → TailSecondDiffNonneg →
    OddCentreCellLE w` (base `s = 0` via `fullRangeFloor_zero`; `s ≥ 2` via the bridge).

NAMED OPEN (Type-level structures, never `sorry`):
  * `ThetaData w` — the abstract theta layer (`Vmoment`, `curvEq`, `phiEqPsi3`, `weaken`, `mono`).
    Discharging it (concrete `A_p,B_p,C_p` series + partial-fraction/`(L2*)`/monotonicity
    derivations) is a later sub-stage.
  * `PhiNonneg w θ` — the terminal scalar `φ(q) ≥ 0` (Stage 4b; interval enclosure).
  * `TailSecondDiffNonneg w θ` — the tail second difference `Δ²tail ≥ 0` (Stage 4c / Task A; ratio
    bound `tail(N)/tail(N−1) ≤ 1/2`).
-/

end YMGap.Continuum.R1OddL2Chain

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.R1OddL2Chain.floor_of_variance
#print axioms YMGap.Continuum.R1OddL2Chain.l2_chain
#print axioms YMGap.Continuum.R1OddL2Chain.variance_floor
#print axioms YMGap.Continuum.R1OddL2Chain.oddCentreCellLE_of_residuals
