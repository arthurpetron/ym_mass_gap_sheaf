/-
`TMDefectCertOneSided` — Milestone 13.4, step 2 (second half, part 3): the
CORRECTED certificate interface, forced by the `OneSubPowTM.exact_cert_fails`
refutation.

# The correction

`TaylorModel.TMDefectCertificate` demanded a coefficientwise two-sided
certificate against `6u²` — machine-refuted as UNSATISFIABLE for the exact
alternating heat-kernel expansion.  The correct interface is ONE-SIDED:
carry the four channel amplitudes and exponents, the DOMINATION of the real
defect by the exact heat-kernel form, and the single kernel certificate
`Σ d_j ≤ 6`.  The producer (`defect_le_sixUsq_of_certOS`) then yields the
uniform `singleStep`-shaped bound on the whole window through the PROVED
`hk_defect_uniform`.

# The honest open field

`dominate` — that the TRUE truncated block-spin defect (as a function of
`u = 1 − w`) is dominated by the exact heat-kernel channel form at the
carried amplitudes — is the AMPLITUDE IDENTIFICATION: precisely the fused
normalization the item-9 scouting measured and the remaining genuine
physics of the pilot chain (together with the ϑ₃ truncation-tail
enclosure, which enters by enlarging the amplitudes).  Everything else in
the structure is decidable or proved.  This is a NAMED reduction carrier,
deliberately not inhabited for the real defect here — the model
self-inhabitation (`certOS_hk_selfdom`) is provided only as the
non-vacuity/wiring check.

# Constructive contract (`lean/AGENTS.md` Rules 1, 6, 8)

Mathlib-free; pure `Q'` / `Nat` core.  No `Classical.*`, no `Real`, no
`native_decide`, no `sorry` / `admit` / new `axiom`.  Gated with
`#print axioms` (permitted: `propext` / `Quot.sound`).
-/

import YMGap.Continuum.OneSubPowTM

namespace YMGap.Continuum.TMDefectCertOneSided

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.TaylorModel
open YMGap.Continuum.TaylorModelStep2
open YMGap.Continuum.TruncatedBlockSpinContraction
open YMGap.Continuum.HeatKernelChannelTM

/-- The exact four-channel heat-kernel defect form. -/
def hkDefect (d0 d1 d2 d3 : Q') (n0 n1 n2 n3 : Nat) (u : Q') : Q' :=
  (((d0 * qpow ((1 : Q') - u) n0 + d1 * qpow ((1 : Q') - u) n1)
      + d2 * qpow ((1 : Q') - u) n2)
    + d3 * qpow ((1 : Q') - u) n3) * (u * u)

/-- **The corrected (one-sided) defect certificate.**  Amplitudes,
exponents, nonnegativity, the DOMINATION of the real defect by the exact
heat-kernel form (the amplitude identification — the open physics), and
the single kernel certificate `Σ d_j ≤ 6`. -/
structure TMDefectCertificateOS (u₀ : Q') (defect : Q' → Q') : Type where
  /-- The four channel amplitudes. -/
  d0 : Q'
  d1 : Q'
  d2 : Q'
  d3 : Q'
  /-- The four channel exponents. -/
  n0 : Nat
  n1 : Nat
  n2 : Nat
  n3 : Nat
  /-- Amplitudes are nonnegative. -/
  h0 : (0 : Q') ≤ d0
  h1 : (0 : Q') ≤ d1
  h2 : (0 : Q') ≤ d2
  h3 : (0 : Q') ≤ d3
  /-- **The amplitude identification (the open physics):** the real defect
  is dominated by the exact heat-kernel form on the window. -/
  dominate : ∀ u, (0 : Q') ≤ u → u ≤ u₀ →
    defect u ≤ hkDefect d0 d1 d2 d3 n0 n1 n2 n3 u
  /-- The single kernel certificate `Σ d_j ≤ 6`. -/
  cert : coeffLeB [0, 0, ((d0 + d1) + d2) + d3] sixUsq = true

/-- **The producer (PROVED):** a one-sided certificate yields the uniform
`singleStep`-shaped bound `defect u ≤ 6u²` on the whole window `[0, u₀]`
(for `u₀ ≤ 1`), through the derived channel enclosures. -/
theorem defect_le_sixUsq_of_certOS {u₀ : Q'} {defect : Q' → Q'}
    (C : TMDefectCertificateOS u₀ defect) (hu₀ : u₀ ≤ (1 : Q')) :
    ∀ u, (0 : Q') ≤ u → u ≤ u₀ → defect u ≤ evalPoly sixUsq u := by
  intro u hu0 hu1
  refine Q'.le_trans' _ _ _ (C.dominate u hu0 hu1) ?_
  exact hk_defect_uniform C.d0 C.d1 C.d2 C.d3 C.n0 C.n1 C.n2 C.n3
    C.h0 C.h1 C.h2 C.h3 C.cert u hu0 (Q'.le_trans' _ _ _ hu1 hu₀)

/-- **Non-vacuity / wiring check (PROVED):** the exact heat-kernel defect
at the pilot amplitudes self-inhabits the corrected certificate (the
`dominate` field by reflexivity) — the structure is satisfiable and the
producer path is exercised end-to-end.  The REAL inhabitation obligation
(the true fused defect in the `defect` slot) remains open. -/
def certOS_hk_selfdom :
    TMDefectCertificateOS 1
      (hkDefect coeff0.hi coeff1.hi coeff2.hi coeff3.hi
        (c4 0) (c4 1) (c4 2) (c4 3)) where
  d0 := coeff0.hi
  d1 := coeff1.hi
  d2 := coeff2.hi
  d3 := coeff3.hi
  n0 := c4 0
  n1 := c4 1
  n2 := c4 2
  n3 := c4 3
  h0 := by decide
  h1 := by decide
  h2 := by decide
  h3 := by decide
  dominate := fun u _ _ => Q'.le_refl' _
  cert := by decide

end YMGap.Continuum.TMDefectCertOneSided

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.TMDefectCertOneSided.defect_le_sixUsq_of_certOS
#print axioms YMGap.Continuum.TMDefectCertOneSided.certOS_hk_selfdom
