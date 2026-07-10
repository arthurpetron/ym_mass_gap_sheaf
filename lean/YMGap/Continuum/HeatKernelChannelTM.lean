/-
`HeatKernelChannelTM` — Milestone 13.4, step 2 (second half, part 1): the
DERIVED heat-kernel channels — the uniform channel enclosures of
`pilot_defect_uniform` DISCHARGED for the exact Peter–Weyl channel form
`c_j(u) = d_j · (1 − u)^{C₄(j)}`.

# What is delivered (all PROVED, axiom-clean)

  * `one_sub_nonneg` / `one_sub_le_one` — for `u ∈ [0, 1]` the coupling
    `w = 1 − u` stays in `[0, 1]` (via the `le_add_cancel_right`
    cancellation and the `neg_add_self` collapse);
  * `hk_channel_nonneg` / `hk_channel_le` — an exact Peter–Weyl channel
    `d · qpow (1 − u) n` with `d ≥ 0` lies in `[0, d]` UNIFORMLY on
    `u ∈ [0, 1]` (`qpow_le_one` on the shrunken coupling) — the uniform
    enclosure DERIVED, not supplied;
  * **`hk_defect_uniform`** — the parametric certificate: for ANY four
    exact heat-kernel channels with amplitudes `d_j ≥ 0` and ANY channel
    exponents, if the single kernel `decide` `Σ d_j ≤ 6` passes then the
    truncated defect `(Σ_j d_j (1−u)^{n_j}) · u² ≤ 6u²` at EVERY
    `u ∈ [0, 1]` — the whole trajectory tail in one check, with the
    channel u-dependence now REAL (heat-kernel), not a constant enclosure;
  * `pilot_hk_defect_uniform` — the concrete instantiation at the pilot's
    certified amplitudes (`Σ = 39/10 ≤ 6`, axiom-clean `decide`) and the
    genuine Casimir exponents `C₄(j) = j(j+2)`.

# What remains open (AGENTS.md Rule 6)

The AMPLITUDE IDENTIFICATION: that the true fused block-spin channel
coefficients are dominated by exact heat-kernel channels at these
amplitudes (the item-9-scouted fusion normalization) — plus the ϑ₃
truncation tail into the remainder and the assembly into
`TMDefectCertificate`.  Named, not faked.  No frontier type is touched;
the Clay problem remains OPEN.

# Constructive contract (`lean/AGENTS.md` Rules 1, 6, 8)

Mathlib-free; pure `Q'` / `Nat` core.  No `Classical.*`, no `Real`, no
`native_decide`, no `by_contra`, no `sorry` / `admit` / new `axiom`.
Gated with `#print axioms` (permitted: `propext` / `Quot.sound`).
-/

import YMGap.Continuum.TaylorModelStep2
import YMGap.Continuum.HeatKernelGap
import YMGap.Continuum.EpsSplitAdjudication

namespace YMGap.Continuum.HeatKernelChannelTM

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.TaylorModel
open YMGap.Continuum.TaylorModelStep2
open YMGap.Continuum.TruncatedBlockSpinContraction
open YMGap.Continuum.EpsSplitAdjudication

/-! ## 1. The coupling window: `u ∈ [0,1] → 1 − u ∈ [0,1]` -/

/-- `(1 − u) + u ≃ 1` (the sub/add collapse; `x − y` is `x + (−y)`
definitionally). -/
theorem one_sub_add_self (u : Q') : (((1 : Q') - u) + u).eqv 1 := by
  refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv 1 (-u) u) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left 1 ((-u) + u) 0 (Q'.neg_add_self_eqv u)) ?_
  exact Q'.eqv_of_eq (Q'.add_zero' 1)

/-- `u ≤ 1 → 0 ≤ 1 − u`. -/
theorem one_sub_nonneg {u : Q'} (hu1 : u ≤ (1 : Q')) :
    (0 : Q') ≤ (1 : Q') - u := by
  refine le_add_cancel_right (c := u) ?_
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_of_eq (Q'.zero_add' u))) ?_
  exact Q'.le_trans' _ _ _ hu1 (Q'.ge_of_eqv (one_sub_add_self u))

/-- `0 ≤ u → 1 − u ≤ 1`. -/
theorem one_sub_le_one {u : Q'} (hu0 : (0 : Q') ≤ u) :
    (1 : Q') - u ≤ 1 := by
  refine le_add_cancel_right (c := u) ?_
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (one_sub_add_self u)) ?_
  exact Q'.add_le_self_of_nonneg 1 u hu0

/-! ## 2. The exact Peter–Weyl channel enclosure, DERIVED -/

/-- A heat-kernel channel is nonnegative on the window. -/
theorem hk_channel_nonneg {d : Q'} (hd : (0 : Q') ≤ d) (n : Nat)
    {u : Q'} (hu1 : u ≤ (1 : Q')) :
    (0 : Q') ≤ d * qpow ((1 : Q') - u) n :=
  Q'.mul_nonneg _ _ hd (qpow_nonneg _ (one_sub_nonneg hu1) n)

/-- A heat-kernel channel is dominated by its amplitude UNIFORMLY on the
window: `d · (1−u)^n ≤ d`. -/
theorem hk_channel_le {d : Q'} (hd : (0 : Q') ≤ d) (n : Nat)
    {u : Q'} (hu0 : (0 : Q') ≤ u) (hu1 : u ≤ (1 : Q')) :
    d * qpow ((1 : Q') - u) n ≤ d := by
  refine Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _
      (qpow_le_one (one_sub_nonneg hu1) (one_sub_le_one hu0) n) hd) ?_
  exact Q'.le_of_eqv (Q'.mul_one_eqv d)

/-! ## 3. THE PARAMETRIC CERTIFICATE -/

/-- **`hk_defect_uniform` (PROVED).**  For ANY four exact heat-kernel
channels `d_j · (1−u)^{n_j}` with `d_j ≥ 0`, if the single kernel
certificate `Σ_j d_j ≤ 6` passes then the truncated defect obeys the
`singleStep`-shaped bound at EVERY `u ∈ [0, 1]`:

    (Σ_j d_j (1−u)^{n_j}) · u²  ≤  6u². -/
theorem hk_defect_uniform (d0 d1 d2 d3 : Q') (n0 n1 n2 n3 : Nat)
    (h0 : (0 : Q') ≤ d0) (h1 : (0 : Q') ≤ d1)
    (h2 : (0 : Q') ≤ d2) (h3 : (0 : Q') ≤ d3)
    (hcert : coeffLeB [0, 0, ((d0 + d1) + d2) + d3] sixUsq = true) :
    ∀ u, (0 : Q') ≤ u → u ≤ (1 : Q') →
      (((d0 * qpow ((1 : Q') - u) n0 + d1 * qpow ((1 : Q') - u) n1)
          + d2 * qpow ((1 : Q') - u) n2)
        + d3 * qpow ((1 : Q') - u) n3) * (u * u)
      ≤ evalPoly sixUsq u := by
  intro u hu0 hu1
  have husq : (0 : Q') ≤ u * u := Q'.mul_nonneg _ _ hu0 hu0
  have hsum : ((d0 * qpow ((1 : Q') - u) n0 + d1 * qpow ((1 : Q') - u) n1)
        + d2 * qpow ((1 : Q') - u) n2) + d3 * qpow ((1 : Q') - u) n3
      ≤ ((d0 + d1) + d2) + d3 :=
    Q'.add_le_add
      (Q'.add_le_add
        (Q'.add_le_add (hk_channel_le h0 n0 hu0 hu1)
          (hk_channel_le h1 n1 hu0 hu1))
        (hk_channel_le h2 n2 hu0 hu1))
      (hk_channel_le h3 n3 hu0 hu1)
  refine Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hsum husq) ?_
  refine Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (evalPoly_c2 (((d0 + d1) + d2) + d3) u)) ?_
  exact evalPoly_le_of_coeffLeB hu0 [0, 0, ((d0 + d1) + d2) + d3] sixUsq
    hcert

/-! ## 4. The pilot instantiation (genuine Casimir exponents) -/

/-- **`pilot_hk_defect_uniform` (PROVED — the pilot channels DERIVED).**
The concrete uniform bound for exact heat-kernel channels at the pilot's
certified amplitudes (`Σ = 39/10 ≤ 6`, one axiom-clean `decide`) and the
genuine Casimir exponents `C₄(j) = j(j+2)` — the channel `u`-dependence is
now the REAL heat-kernel decay, not a constant enclosure.  The remaining
named input is the amplitude identification (the fused normalization). -/
theorem pilot_hk_defect_uniform :
    ∀ u, (0 : Q') ≤ u → u ≤ (1 : Q') →
      (((coeff0.hi * qpow ((1 : Q') - u) (c4 0)
            + coeff1.hi * qpow ((1 : Q') - u) (c4 1))
          + coeff2.hi * qpow ((1 : Q') - u) (c4 2))
        + coeff3.hi * qpow ((1 : Q') - u) (c4 3)) * (u * u)
      ≤ evalPoly sixUsq u :=
  hk_defect_uniform coeff0.hi coeff1.hi coeff2.hi coeff3.hi
    (c4 0) (c4 1) (c4 2) (c4 3)
    (by decide) (by decide) (by decide) (by decide)
    (by decide)

end YMGap.Continuum.HeatKernelChannelTM

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.HeatKernelChannelTM.one_sub_add_self
#print axioms YMGap.Continuum.HeatKernelChannelTM.one_sub_nonneg
#print axioms YMGap.Continuum.HeatKernelChannelTM.one_sub_le_one
#print axioms YMGap.Continuum.HeatKernelChannelTM.hk_channel_nonneg
#print axioms YMGap.Continuum.HeatKernelChannelTM.hk_channel_le
#print axioms YMGap.Continuum.HeatKernelChannelTM.hk_defect_uniform
#print axioms YMGap.Continuum.HeatKernelChannelTM.pilot_hk_defect_uniform
