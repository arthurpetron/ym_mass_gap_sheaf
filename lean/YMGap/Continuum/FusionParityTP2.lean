/-
`FusionParityTP2` — Milestone 13.2, step 2: the TP₂ (total-positivity) route
to the fusion log-concavity, ADJUDICATED and OPENED at the atomic level:

  * the NAIVE route is machine-REFUTED twice:
    (1) the raw fusion kernel is NOT TP₂ — parity interlacing produces a 2×2
        minor of the wrong sign already at `j = 1`, `(a, a') = (0, 1)`,
        `(s, s') = (0, 1)` (`fusionKernel_not_TP2`);
    (2) DISCOVERED IN MECHANIZATION (a false pen-and-paper lemma caught by
        the failing kernel check): even PARITY-CONSISTENT TP₂ fails for
        `j ≥ 2` — the REFLECTION CORNER at spin `0` kills the minor at
        `j = 2`, `(a, a') = (0, 2)`, `(s, s') = (0, 2)`: the fusion window is
        not the plain band `|a − s| ≤ j` but the band CUT by the corner
        `a + s ≥ j`, and the diagonal corner is not implied by the cross
        corners (`fusionKernel_not_TP2_parity`);
  * the CORRECT atomic brick is PROVED: on a parity-consistent sublattice
    AND above the corner (`j ≤ a + s`), the 2×2 minor is nonnegative
    (`fusionOK_TP2_step` / `stepN_TP2`), by pure `Nat` window arithmetic over
    the ladder normal form; at `j = 1` the corner is FREE by parity, so the
    fundamental-representation kernel is unconditionally parity-TP₂
    (`stepN_TP2_j1`).

# Where this sits in the campaign (honest scope)

`FusionConvLogConcaveCore.cauchyBinet` asks for log-concavity of the WEIGHTED
p = 2 box sum in the raw mode index `s, s+1, s+2` — MIXED parity.  The two
refutations pin the architecture: no unweighted TP₂/Karlin argument alone
can give it (already at `N = 1` the claim reduces exactly to the
`strongCoupling` field `c₁² ≤ 3c₀²`), and away from `j = 1` even the
same-parity comparison must carry the corner data.  The campaign is
therefore: (i) corner-aware parity-TP₂ (the brick PROVED here) → same-parity
log-concavity of the path counts (composition / LGV, next step); (ii) the
weighted cross-parity interlacing under `strongCoupling` (where the analysis
lives).  Kernel-checked SUPPORT-lattice log-concavity anchors for the pure
counts (`j = 1, 2`, `p ≤ 8`, axiom-free) pin the shape of (i).  Nothing here
inhabits `FusionConvLogConcaveCore`; the `hlocalize` wall and the Clay
problem remain OPEN.

# Constructive contract (`lean/AGENTS.md` Rules 1, 6, 8)

Mathlib-free; pure `Nat` / `Bool` core.  No `Classical.*`, no `Real`, no
`native_decide`, no `sorry` / `admit` / new `axiom`.  Gated with
`#print axioms` (permitted: `propext` / `Quot.sound`).
-/

import YMGap.Continuum.FusionBratteli

namespace YMGap.Continuum.FusionParityTP2

open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FusionBratteli

/-! ## 1. The `Nat`-valued step kernel -/

/-- The 0/1 step kernel of the spin-`j` reflected walk. -/
def stepN (j a s : Nat) : Nat := if fusionOK a j s then 1 else 0

/-! ## 2. The REFUTATION: the raw kernel is NOT TP₂ (parity interlacing) -/

/-- **`fusionKernel_not_TP2` (PROVED — the naive TP₂ route is DEAD).**  The
raw fusion kernel violates the 2×2 TP₂ minor inequality at `j = 1`,
`(a, a') = (0, 1)`, `(s, s') = (0, 1)`: both CROSS entries are `1`
(`0 ⊗ 1 ∋ 1` and `1 ⊗ 1 ∋ 0`) while both DIAGONAL entries are `0` (parity:
`0 ⊗ 1 ∌ 0`, `1 ⊗ 1 ∌ 1`).  An odd shift in `a` and `s` simultaneously
flips the parity constraint, so no unweighted TP₂/Karlin composition can
control the mixed-parity index `s, s+1, s+2` of
`FusionConvLogConcaveCore.cauchyBinet` — the cross-parity comparison must
come from the WEIGHTS (the `strongCoupling` regime).  Refutation banked per
the Lakatos discipline. -/
theorem fusionKernel_not_TP2 :
    ¬ (∀ (j a a' s s' : Nat), a ≤ a' → s ≤ s' →
        stepN j a s' * stepN j a' s ≤ stepN j a s * stepN j a' s') := by
  intro h
  have := h 1 0 1 0 1 (by decide) (by decide)
  revert this
  decide

/-! ## 3. Refutation 2: parity-consistent TP₂ still fails for `j ≥ 2`
(the reflection corner) -/

/-- **`fusionKernel_not_TP2_parity` (PROVED — the parity-only route is ALSO
dead, `j ≥ 2`).**  Restricting to parity-consistent sublattices does NOT
rescue TP₂: at `j = 2`, `(a, a') = (0, 2)`, `(s, s') = (0, 2)` (both shifts
even) the cross entries are occupied (`0 ⊗ 2 ∋ 2`, `2 ⊗ 2 ∋ 0`) but the
diagonal entry `0 ⊗ 2 ∋ 0` is CORNER-cut (`a + s = 0 < j`): the fusion
window is the band `|a − s| ≤ j` intersected with `a + s ≥ j`, and the
diagonal corner does not follow from the cross corners.  The corrected brick
must carry the corner hypothesis. -/
theorem fusionKernel_not_TP2_parity :
    ¬ (∀ (j a a' s s' : Nat), a ≤ a' → s ≤ s' →
        (a' - a) % 2 = 0 → (s' - s) % 2 = 0 →
        stepN j a s' * stepN j a' s ≤ stepN j a s * stepN j a' s') := by
  intro h
  have := h 2 0 2 0 2 (by decide) (by decide) (by decide) (by decide)
  revert this
  decide

/-! ## 4. The PROVED brick: corner-aware parity-consistent TP₂ -/

/-- **`fusionOK_TP2_step` (PROVED — the atomic parity-TP₂ implication,
corner-aware).**  On a parity-consistent 2×2 sublattice (`a ≤ a'`, `s ≤ s'`,
both shifts even) ABOVE THE CORNER (`j ≤ a + s`), if both CROSS entries of
the fusion kernel are occupied then both DIAGONAL entries are: the ladder
windows squeeze monotonically, the even shifts preserve parity, and the
corner hypothesis supplies exactly the reflection cutoff that refutation 2
shows cannot be dropped. -/
theorem fusionOK_TP2_step (j a a' s s' : Nat)
    (haa : a ≤ a') (hss : s ≤ s')
    (ha2 : (a' - a) % 2 = 0) (hs2 : (s' - s) % 2 = 0)
    (hcorner : j ≤ a + s)
    (hcross1 : fusionOK a j s' = true) (hcross2 : fusionOK a' j s = true) :
    fusionOK a j s = true ∧ fusionOK a' j s' = true := by
  obtain ⟨k1, hk1a, hk1j, he1⟩ := (fusionOK_iff_ladder a j s').mp hcross1
  obtain ⟨k2, hk2a, hk2j, he2⟩ := (fusionOK_iff_ladder a' j s).mp hcross2
  constructor
  · -- a ⊗ j ∋ s: witness k = (a + j − s) / 2, in range by the squeeze
    refine (fusionOK_iff_ladder a j s).mpr ?_
    have hdm := Nat.div_add_mod (a + j - s) 2
    have hmod : (a + j - s) % 2 = 0 := by omega
    exact ⟨(a + j - s) / 2, by omega, by omega, by omega⟩
  · -- a' ⊗ j ∋ s': witness k = (a' + j − s') / 2, in range by the squeeze
    refine (fusionOK_iff_ladder a' j s').mpr ?_
    have hdm := Nat.div_add_mod (a' + j - s') 2
    have hmod : (a' + j - s') % 2 = 0 := by omega
    exact ⟨(a' + j - s') / 2, by omega, by omega, by omega⟩

/-- **`stepN_TP2` (PROVED — the 2×2 minor form).**  The `Nat` product form
of the corner-aware parity-consistent TP₂ property: on even shifts above
the corner, the cross product is dominated by the diagonal product. -/
theorem stepN_TP2 (j a a' s s' : Nat)
    (haa : a ≤ a') (hss : s ≤ s')
    (ha2 : (a' - a) % 2 = 0) (hs2 : (s' - s) % 2 = 0)
    (hcorner : j ≤ a + s) :
    stepN j a s' * stepN j a' s ≤ stepN j a s * stepN j a' s' := by
  unfold stepN
  by_cases h1 : fusionOK a j s' = true
  · by_cases h2 : fusionOK a' j s = true
    · obtain ⟨hd1, hd2⟩ :=
        fusionOK_TP2_step j a a' s s' haa hss ha2 hs2 hcorner h1 h2
      rw [if_pos h1, if_pos h2, if_pos hd1, if_pos hd2]
      exact Nat.le_refl 1
    · rw [if_neg h2, Nat.mul_zero]
      exact Nat.zero_le _
  · rw [if_neg h1, Nat.zero_mul]
    exact Nat.zero_le _

/-- **`stepN_TP2_j1` (PROVED — the fundamental representation is
unconditionally parity-TP₂).**  At `j = 1` the corner is FREE: the parity
constraint forces `a + s` odd on the occupied sublattice, so `a + s ≥ 1 = j`
whenever the cross entries are occupied, and the corner-aware brick applies.
This is the clean Karlin-composable kernel for the `j = 1` fusion tower. -/
theorem stepN_TP2_j1 (a a' s s' : Nat)
    (haa : a ≤ a') (hss : s ≤ s')
    (ha2 : (a' - a) % 2 = 0) (hs2 : (s' - s) % 2 = 0) :
    stepN 1 a s' * stepN 1 a' s ≤ stepN 1 a s * stepN 1 a' s' := by
  by_cases h1 : fusionOK a 1 s' = true
  · -- parity of the occupied cross entry forces the corner
    obtain ⟨k, hka, hkj, he⟩ := (fusionOK_iff_ladder a 1 s').mp h1
    exact stepN_TP2 1 a a' s s' haa hss ha2 hs2 (by omega)
  · unfold stepN
    rw [if_neg h1, Nat.zero_mul]
    exact Nat.zero_le _

/-! ## 5. Kernel-checked SUPPORT-lattice log-concavity anchors

The pure path counts are log-concave along the parity SUPPORT lattice
(step 2 in the endpoint) — the shape of the claim the parity-TP₂ brick
feeds.  Axiom-free kernel computations. -/

/-- `j = 1, p = 6`: profile `(5, 9, 5, 1)` — `5·5 ≤ 81`, `9·1 ≤ 25`. -/
theorem pathCount_logconcave_p6 :
    pathCount 1 6 0 * pathCount 1 6 4 ≤ pathCount 1 6 2 * pathCount 1 6 2
    ∧ pathCount 1 6 2 * pathCount 1 6 6 ≤ pathCount 1 6 4 * pathCount 1 6 4 := by
  refine ⟨by decide, by decide⟩

/-- `j = 1, p = 8`: profile `(14, 28, 20, 7, 1)` — three interior minors. -/
theorem pathCount_logconcave_p8 :
    pathCount 1 8 0 * pathCount 1 8 4 ≤ pathCount 1 8 2 * pathCount 1 8 2
    ∧ pathCount 1 8 2 * pathCount 1 8 6 ≤ pathCount 1 8 4 * pathCount 1 8 4
    ∧ pathCount 1 8 4 * pathCount 1 8 8 ≤ pathCount 1 8 6 * pathCount 1 8 6 := by
  refine ⟨by decide, by decide, by decide⟩

/-- `j = 2, p = 4`: profile `(3, 6, 6, 3, 1)` on the even support — the
higher-spin anchor. -/
theorem pathCount_logconcave_j2p4 :
    pathCount 2 4 0 * pathCount 2 4 4 ≤ pathCount 2 4 2 * pathCount 2 4 2
    ∧ pathCount 2 4 2 * pathCount 2 4 6 ≤ pathCount 2 4 4 * pathCount 2 4 4
    ∧ pathCount 2 4 4 * pathCount 2 4 8 ≤ pathCount 2 4 6 * pathCount 2 4 6 := by
  refine ⟨by decide, by decide, by decide⟩

end YMGap.Continuum.FusionParityTP2

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.FusionParityTP2.fusionKernel_not_TP2
#print axioms YMGap.Continuum.FusionParityTP2.fusionKernel_not_TP2_parity
#print axioms YMGap.Continuum.FusionParityTP2.fusionOK_TP2_step
#print axioms YMGap.Continuum.FusionParityTP2.stepN_TP2
#print axioms YMGap.Continuum.FusionParityTP2.stepN_TP2_j1
#print axioms YMGap.Continuum.FusionParityTP2.pathCount_logconcave_p6
#print axioms YMGap.Continuum.FusionParityTP2.pathCount_logconcave_p8
#print axioms YMGap.Continuum.FusionParityTP2.pathCount_logconcave_j2p4
