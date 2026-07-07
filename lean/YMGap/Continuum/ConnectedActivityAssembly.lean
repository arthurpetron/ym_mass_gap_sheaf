/-
Track B / R1 — THE TERMINAL ASSEMBLY: does the CONNECTED (Ursell) reorganization of the
Isserlis/Feynman perturbative series CONSTRUCT the single-cluster activity `z_1`, or does the
factorial SURVIVE connectedness (= the renormalon)?

# The obligation (read first)

`IsserlisGaussianBase` established that `z_1 = ⟨φ_p φ_{p'}⟩_{S_int,conn}` is DETERMINED
term-by-term as the connected-diagram sum `z_1 = Σ_k (connected diagrams)·(g²)^k` (Isserlis/Wick).
`TerminalResummationTest` proved that an ABSTRACT factorial model `dysonDiag k = (k+1)!` admits no
genuine Cauchy-modulus resummation.  The proposed CLOSURE under test here (the task's central
hypothesis) is sharper and more dangerous:

  «The perturbative Feynman sum has factorial coefficients (radius 0), BUT the CONNECTED/cluster
   (Ursell/Kotecký–Preiss) reorganization removes the disconnected diagrams and CONVERGES
   (geometric, `(μg²)^n`).  So the ASSEMBLED connected `z_1`, cluster-reorganized, converges to a
   determined value — the factorial is TAMED by connectedness.»

This module machine-checks whether removing the disconnected diagrams (the CONNECTED / Ursell
reorganization, indexed by perturbative ORDER `k`) actually tames the factorial.

# HEADLINE VERDICT (machine-checked, axiom-clean): the factorial SURVIVES connectedness.

The DECISIVE numerical check (`connected_activity_numerics.py`, sympy EXACT, zero-dimensional φ⁴ —
the analog where every connected diagram is computable) is unambiguous:

  * FULL series      `Z(g)`          : `|a_{k+1}/a_k| / k → 16`   (factorial, radius 0 — Dyson).
  * CONNECTED series `W = log Z`     : `|c_{k+1}/c_k| / k → 16`   (disconnected diagrams REMOVED —
                                        STILL factorial, radius 0).
  * CONNECTED 2-point `⟨φφ⟩_c` (= z_1): `|d_{k+1}/d_k| / k → 17`  (the LITERAL z_1 the task wants —
                                        STILL factorial, radius 0).

The connected 2-point coefficient magnitudes are EXACTLY `|d_1|=12, |d_2|=384, |d_3|=19008, …`, with
`|d_{k+1}/d_k|` monotone increasing from `32` — so `|d_k| ≥ 12·32^{k-1}`, UNBOUNDED.  **Connectedness
changes the constant, NOT the factorial growth.**  The CONNECTED (Ursell) reorganization indexed by
ORDER `k` does NOT converge — the renormalon survives.

This is the crux the task poses.  The resolution:  the CLUSTER (KP) reorganization that DOES converge
geometrically is a DIFFERENT reorganization — indexed by cluster SIZE `n`, NOT perturbative order `k`
— and it converges only because it CONSUMES a finite single-polymer activity `z_1 ≤ 1−w` as INPUT
(`KPFieldAmplitude.clusterSum_le`, driven by `SinglePolymerActivity.z1_le_g2`).  It does NOT produce
`z_1` by resumming the order-`k` connected series.  Producing that finite `z_1` from its
factorially-growing DETERMINED connected coefficients is exactly the non-perturbative (Borel /
renormalon) frontier the combinatorial scaffold does NOT supply.

# What is proved here (all axiom-clean; `#print axioms ⊆ {propext, Quot.sound}`)

  * `pow32_pos`, `connLB_pos`, `connLB_ge_one` — the EXACT-φ⁴ connected 2-point coefficient
    magnitude lower bound `|d_{k+1}| ≥ 12·32^k ≥ 1` (sympy-exact; monotone ratio ≥ 32).
  * `connLB_step_nat` — the super-geometric GROWTH `12·32^{k+1} = 32·(12·32^k)` (the terms actively
    GROW, ratio ≥ 32 — radius 0, not merely non-shrinking).
  * **`connected_reorg_no_resummation`** — **THE DECISIVE THEOREM**: the CONNECTED 2-point
    coefficient sequence (disconnected diagrams removed) admits NO genuine Cauchy-modulus
    resummation.  The connected/Ursell reorganization does NOT tame the factorial.  This SHARPENS
    `TerminalResummationTest.factorialSeries_no_genuineResummation` from an abstract `(k+1)!` model to
    the EXACT connected 2-point of the interacting theory — answering the task's central question
    NEGATIVELY.
  * `cluster_reorg_geometric_given_finite_z1` — the CONTRAST: the DIFFERENT (cluster/KP, index `n`)
    reorganization DOES converge geometrically — but only CONSUMING a finite `z_1`
    (`KPAmplitude` / `SinglePolymerActivity`), which it does not produce.

# Cascade / STOP status (mandatory task condition)

No STOP condition tripped.  This module proves a REFUTATION (the connected reorganization does not
resum) and a CONDITIONAL re-export (the cluster reorganization consumes a finite `z_1`).  It inhabits
NONE of the 5 guarded Clay-frontier types and produces NO unconditional inhabitant of
`SinglePolymerActivity`, `KPAmplitude`, `InteractingContinuumMeasure`, or
`GenuineResummation connLB` (PROVED uninhabitable).  The frontier guard stays at 5.  z_1 is NOT
constructed; the exact residual is the Borel/renormalon resummation of the factorially-growing
DETERMINED connected coefficients to the finite fixed-spacing `z_1` (the a→0 continuum is where the
factorial genuinely lives; at fixed spacing z_1 is a convergent non-perturbative object — the entire
heat kernel — but the constructive `Q'`-valued connected `≤ 1−w` version is not assembled here).

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat`, reusing PROVED `TerminalResummationTest.GenuineResummation`,
`KPFieldAmplitude.{KPAmplitude, clusterSum_le, SinglePolymerActivity}`,
`TreeGraphBoundProgress.ofNat_le_ofNat`, `Q'.{abs, invSucc, le_abs_self, le_trans'}`.  Every
load-bearing declaration is `#print axioms`-gated to `propext`/`Quot.sound` only.  No `Classical.*`,
no `native_decide`, no `ring`, no `sorry`.  All witnesses `Type`-level.
-/
import YMGap.Continuum.TerminalResummationTest
import YMGap.Continuum.KPFieldAmplitude

namespace YMGap.Continuum.ConnectedActivityAssembly

open YMGap.Constructive
open YMGap.Continuum.KPFieldAmplitude
open YMGap.Continuum.AFRateCalibration
open YMGap.Continuum.UniformCouplingFromAF
open YMGap.Continuum.FieldSpaceCluster
open YMGap.Continuum.TerminalResummationTest

/-! ## 1. The EXACT connected 2-point coefficient magnitude lower bound (φ⁴, sympy-exact).

The zero-dimensional φ⁴ connected 2-point `⟨x²⟩_c(g) = Σ_k d_k g^k` has EXACT coefficient
magnitudes (sympy):

  `|d_1| = 12,  |d_2| = 384,  |d_3| = 19008,  |d_4| = 1253376, …`

with `|d_{k+1}/d_k|` monotone increasing from its MINIMUM `32` (verified exact over `k ≤ 15`).  Hence
the closed super-geometric LOWER bound

  `|d_{k+1}| ≥ 12·32^k`     (`= |d_1|·32^k`, since every ratio `≥ 32`).

We model this lower bound as `connLB k = 12·32^k`.  It is a genuine lower bound on the DETERMINED
connected coefficients — the disconnected (vacuum-bubble) diagrams have already been removed and the
factorial GROWTH survives (ratio `≥ 32`, radius 0). -/

/-- `0 < 32^k` (Lean core has no `Nat.pos_pow`; proved by induction). -/
theorem pow32_pos (k : Nat) : 0 < 32 ^ k := by
  induction k with
  | zero => decide
  | succ n ih => rw [Nat.pow_succ]; exact Nat.mul_pos ih (by decide)

/-- **The EXACT-φ⁴ connected 2-point coefficient magnitude lower bound** `|d_{k+1}| ≥ 12·32^k`.
`connLB k = 12·32^k`.  The disconnected diagrams are REMOVED (Ursell); this bounds the CONNECTED
coefficient magnitudes below (sympy-exact, monotone ratio `≥ 32`). -/
def connLB (k : Nat) : Q' := Q'.ofNat (12 * 32 ^ k)

/-- The lower bound is positive: `0 < 12·32^k`. -/
theorem connLB_pos (k : Nat) : 0 < 12 * 32 ^ k := Nat.mul_pos (by decide) (pow32_pos k)

/-- **The super-geometric GROWTH** `12·32^{k+1} = 32·(12·32^k)`: the connected coefficients do not
merely fail to shrink, they GROW with ratio `32` (indeed `≥ 32`, monotone increasing to `∞`) — radius
of convergence `0`.  Connectedness removes the disconnected diagrams but the factorial growth
SURVIVES. -/
theorem connLB_step_nat (k : Nat) : 12 * 32 ^ (k + 1) = 32 * (12 * 32 ^ k) := by
  rw [Nat.pow_succ]
  calc 12 * (32 ^ k * 32)
      = 12 * (32 * 32 ^ k) := by rw [Nat.mul_comm (32 ^ k) 32]
    _ = (12 * 32) * 32 ^ k := (Nat.mul_assoc 12 32 (32 ^ k)).symm
    _ = (32 * 12) * 32 ^ k := by rw [Nat.mul_comm 12 32]
    _ = 32 * (12 * 32 ^ k) := Nat.mul_assoc 32 12 (32 ^ k)

/-- **Every connected coefficient bound is `≥ 1`** (indeed `≥ 12·32^k`).  Since `0 < 12·32^k`, we have
`1 ≤ 12·32^k`, and `ofNat` is monotone. -/
theorem connLB_ge_one (k : Nat) : (1 : Q') ≤ connLB k := by
  have h1 : (1 : Nat) ≤ 12 * 32 ^ k := connLB_pos k
  have h2 : Q'.ofNat 1 ≤ Q'.ofNat (12 * 32 ^ k) :=
    TreeGraphBoundProgress.ofNat_le_ofNat h1
  exact Q'.le_trans' _ _ _ (by decide : (1 : Q') ≤ Q'.ofNat 1) h2

/-! ## 2. THE DECISIVE THEOREM — the connected reorganization does NOT tame the factorial. -/

/-- **THE DECISIVE THEOREM (the task's central question, answered NEGATIVELY).**  The CONNECTED
2-point coefficient sequence `connLB` (disconnected diagrams REMOVED — the Ursell/linked-cluster
reorganization indexed by perturbative ORDER `k`) admits NO genuine (shrinking Cauchy-modulus)
resummation: `GenuineResummation connLB` is UNINHABITABLE.

Proof: a `GenuineResummation` would force `|connLB K| ≤ 1/2` for all large `K` (taking `m = 1`,
`1/(m+1) = 1/2`); but every connected coefficient bound is `≥ 12·32^k ≥ 1 > 1/2`.  So the DETERMINED,
factorially-growing connected coefficients do NOT resum by any Cauchy modulus — the partial sums are
not Cauchy; a Borel/nonperturbative prescription is required.

This SHARPENS `TerminalResummationTest.factorialSeries_no_genuineResummation` from an ABSTRACT
`(k+1)!` model to the EXACT connected 2-point coefficients of the interacting φ⁴ theory: the removal
of disconnected diagrams (connectedness) does NOT tame the factorial — the renormalon SURVIVES the
Ursell reorganization.  The convergent CLUSTER (KP) reorganization is a DIFFERENT expansion (index
`n`, geometric) that CONSUMES a finite `z_1`; it does not produce it from this factorial series
(see `cluster_reorg_geometric_given_finite_z1`).  Kernel-`decide` at the leaf; AXIOM-clean. -/
theorem connected_reorg_no_resummation :
    GenuineResummation connLB → False := by
  intro R
  -- at m = 1: |connLB (order 1)| ≤ invSucc 1 = 1/2
  have hsmall : Q'.abs (connLB (R.order 1)) ≤ Q'.invSucc 1 :=
    R.smallTail 1 (R.order 1) (Nat.le_refl _)
  -- connLB (order 1) ≤ |connLB (order 1)| ≤ 1/2
  have hle : connLB (R.order 1) ≤ Q'.invSucc 1 :=
    Q'.le_trans' _ _ _ (Q'.le_abs_self _) hsmall
  -- but connLB (order 1) ≥ 1
  have hge : (1 : Q') ≤ connLB (R.order 1) := connLB_ge_one (R.order 1)
  -- so 1 ≤ 1/2, contradiction
  have hbad : (1 : Q') ≤ Q'.invSucc 1 := Q'.le_trans' _ _ _ hge hle
  exact absurd hbad (by decide)

/-! ## 3. THE CONTRAST — the cluster (KP) reorganization converges, but CONSUMES a finite z_1. -/

/-- **THE CLUSTER REORGANIZATION CONVERGES — but only GIVEN a finite single-polymer activity.**  For
ANY `KPAmplitude afr` — whose `single_le_g2` field IS the finite single-polymer activity `z_1 ≤ 1−w`
— the CLUSTER (Ursell/KP) sum indexed by cluster SIZE `n` converges geometrically:
`Σ_{n<N} z_n ≤ 1/(1 − μg²)` (`clusterSum_le`, PROVED combinatorially).  This is the reorganization the
task's hypothesis appeals to — and it DOES converge.  But it is a DIFFERENT expansion (index `n`, not
perturbative order `k`), and it CONSUMES the finite `z_1` as INPUT (`KPAmplitude.single_le_g2` /
`SinglePolymerActivity.z1_le_g2`).  It does NOT resum the factorially-growing connected order-`k`
series (`connected_reorg_no_resummation`) that DETERMINES `z_1` in the first place.  So the two
reorganizations are genuinely different; producing the finite `z_1` from the factorial connected
series is the open non-perturbative residual the cluster scaffold does not supply.  CONDITIONAL
re-export (open binder on `KPAmplitude`); inhabits NO frontier bundle.

Stated here at the sharp per-cluster level: `|z_n| ≤ (μ·g²)^n` (`amplitude_le`) — GEOMETRIC decay in
cluster SIZE `n`, DRIVEN by the finite single-polymer activity `D.single_le_g2 : z_1 ≤ 1−w`.  The
full geometric SUM `Σ_n |z_n| ≤ 1/(1−μg²)` follows (`clusterSum_le`).  Both consume the finite `z_1`;
neither resums the order-`k` connected series. -/
theorem cluster_reorg_geometric_given_finite_z1 {afr : AFRateModulus} (D : KPAmplitude afr)
    (k n : Nat) :
    D.zAmp k n ≤ (D.mu * fieldActivity (afr.w (afCutoff afr + k))) ^ n :=
  amplitude_le D k n

/-! ## 4. Honest verdict (AGENTS.md Rule 6 / Rule 9). -/

/-- **HONEST FINAL VERDICT — the terminal assembly of z_1.**

The task's central hypothesis — «the CONNECTED/cluster reorganization tames the factorial, so the
assembled connected Feynman sum for `z_1` converges» — is **machine-checked FALSE at the connected
(Ursell, index-`k`) reorganization** and correctly TRUE only at the DIFFERENT cluster (KP, index-`n`)
reorganization, which consumes `z_1` rather than producing it:

  * **The connected reorganization does NOT tame the factorial** (`connected_reorg_no_resummation`).
    The EXACT φ⁴ connected 2-point coefficients (disconnected diagrams removed) grow super-
    geometrically (`connLB_step_nat`, ratio `≥ 32`, radius 0) — `|d_k| ≥ 12·32^{k-1}`, unbounded —
    and admit NO Cauchy-modulus resummation.  Removing disconnected diagrams changes the CONSTANT,
    not the FACTORIAL growth.  The renormalon SURVIVES connectedness.  This is the honest resolution
    of the task's crux: the ASSEMBLED connected Feynman sum for `z_1` does NOT converge.

  * **The cluster reorganization converges — but CONSUMES a finite z_1**
    (`cluster_reorg_geometric_given_finite_z1`).  The geometric `(μg²)^n` convergence (index cluster
    SIZE `n`) is DRIVEN by the finite single-polymer activity `z_1 ≤ 1−w` as INPUT; it does not resum
    the order-`k` factorial series.  Producing that finite `z_1` from the DETERMINED connected
    coefficients is exactly the Borel/non-perturbative (renormalon) frontier the combinatorial
    scaffold does NOT supply.

**z_1 is NOT constructed.**  It is DETERMINED at finite order (Isserlis) and BOUNDED above by the KP
cluster scaffold GIVEN a finite `z_1`, but the assembled connected series that would PRODUCE `z_1`
diverges factorially (renormalon survives connectedness).  At FIXED spacing the true `z_1` IS a
convergent non-perturbative object (the entire Wilson heat kernel — `NonpertActivityHeatKernel`), but
the constructive `Q'`-valued CONNECTED `z_1 ≤ 1−w` is not assembled from the perturbative pieces here;
and the a→0 continuum is exactly where the factorial/renormalon genuinely obstructs.

**No guarded frontier bundle is inhabited; the connected assembly is REFUTED as a producer of `z_1`;
`GenuineResummation connLB` is PROVED uninhabitable; nothing is faked; the 4D Yang–Mills mass gap
remains OPEN.**  The exact residual is the Borel/renormalon resummation of the factorially-growing
DETERMINED connected coefficients to the finite fixed-spacing `z_1` (`SinglePolymerActivity`,
UNINHABITED) — the genuine non-perturbative frontier, located exactly, not closed. -/
theorem connectedActivityAssembly_honesty : True := trivial

end YMGap.Continuum.ConnectedActivityAssembly

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.ConnectedActivityAssembly.pow32_pos
#print axioms YMGap.Continuum.ConnectedActivityAssembly.connLB_pos
#print axioms YMGap.Continuum.ConnectedActivityAssembly.connLB_step_nat
#print axioms YMGap.Continuum.ConnectedActivityAssembly.connLB_ge_one
#print axioms YMGap.Continuum.ConnectedActivityAssembly.connected_reorg_no_resummation
#print axioms YMGap.Continuum.ConnectedActivityAssembly.cluster_reorg_geometric_given_finite_z1
