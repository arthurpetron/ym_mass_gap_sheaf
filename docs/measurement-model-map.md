# The measurement-model map — how the Lean structure mirrors the real-world
# measurement of the mass gap (living document; refine every session)

**Status: v2 (2026-07-09).** v2 adds §0 (why the gap exists — the model's
two reality-facts) and CORRECTS §6: the matching stage is a DERIVATION,
not an empirical import — the proof is constructive, not computational.

## 0. Why the gap exists — the two structural facts of the model

The measurements come out gapped because of two facts about the modeled
system, BOTH already internal to the Wilson-measure model (no empirical
input):

  * **COMPACTNESS.** The field is compact-group-valued. The Laplacian on
    SU(2) has a discrete spectrum gapped by the first Casimir, so the
    single-plaquette transfer kernel is gapped; every gauge-invariant
    excitation is a CLOSED FLUX STRUCTURE (Elitzur: no Goldstone route;
    a free gluon is not gauge-invariant), so correlation over distance
    `d` must be carried by a structure of size ≥ `d` — formalized as the
    (D2) size floor (`enum_reach_floor`), a THEOREM in-repo. At strong
    coupling "action cost beats entropy" for flux structures — the
    fixed-spacing gap, PROVED.
  * **SELF-CHARGE (non-abelian sign).** The field carries its own charge;
    the vacuum ANTI-screens; the coupling GROWS under coarse-graining.
    This is why the gap PERSISTS to the continuum: blocking any physical
    scale far enough lands in the provably gapped compact strong-coupling
    regime. Dimensional transmutation is this statement, and `singleStep`
    (the margin recursion) is its exact quantitative form: "the flow runs
    toward the provable regime fast enough."

Model of the thing (Wilson measure) + model of the measurement (the
correlator pipeline, §§1–5) + these two facts ⟹ the gap, constructively.
The whole Clay problem is that the SECOND fact must be made uniform-in-
scale as a theorem. There is no missing third ingredient.

The purpose of this document is to keep the
formal development honest about WHAT PHYSICAL PROCEDURE each Lean object
formalizes. The mass gap is "measured in reality" by lattice Monte Carlo
glueball spectroscopy (pure SU(N): m(0⁺⁺) ≈ 3.7√σ; in full QCD its shadow
is the scalar-glueball component near 1.6–1.7 GeV). The repository is a
RIGOROUS REPLICA of that measurement pipeline: every stage that a lattice
collaboration performs with statistics and fits, the proof performs with a
theorem. The mapping, stage by stage:

## 1. The apparatus = the transfer matrix (PROVED layer)

Real measurement: a finite hypercubic lattice with the Wilson action; the
Euclidean correlator `C(t) = ⟨O(t)O(0)⟩ − ⟨O⟩²` of a gauge-invariant
(smeared plaquette/loop) operator; the effective mass
`m_eff(t) = log C(t)/C(t+1)` plateaus at `a·m_lat`.

Lean counterpart (fixed spacing, unconditional): the reconstructed transfer
operator (`reconTransfer` → Peter–Weyl-resummed `effTransfer`), the real
Wilson correlator `wilsonG`, geometric clustering, and the PROVED effective-
mass plateau `m_eff(t) → m_phys` (`mass_gap_hamiltonian_all`). The repo even
ran its own SU(2) MC (`computations/`, `mcmc-16.log`, `run-L16-b2.4.log`) —
the literal experiment — as scouting, never as proof input.

## 2. The observable = the truncated two-point function (13.1 layer)

Real measurement: the CONNECTED (vacuum-subtracted) correlator, estimated
with jackknife/bootstrap; positivity and unimodality of its spectral
weights (Källén–Lehmann) justify the single-exponential fit window.

Lean counterpart: the two-point Mayer layer over the polymer gas — the
EXACT four-cell identity `T·Ξ² = A·B − E·D`
(`XiAvoidanceCorrelation.truncated_numerator_mayer`) is the formal
"vacuum subtraction"; the bridge/chain majorants
(`XiPinnedBridge`, `XiChainBound`) are the proof-side substitute for the
estimator's error analysis; the (D2) size floor
(`DecoderReachFloor.enum_reach_floor`) is the statement that signal at
separation `d` must be carried by structures of size ≥ d — the physical
locality of the measurement. The still-open decaying-envelope sharpening
(`A·B − E·D`) is the connectedness cancellation a numericist gets "for
free" from vacuum subtraction; the proof must construct it.

## 3. The spectral-weight positivity = the fusion tower (13.2 layer)

Real measurement: variational/GEVP spectroscopy over a finite operator
basis; excited-state contamination suppressed exponentially; the spectral
decomposition has positive weights.

Lean counterpart: the SU(2) fusion tower (`boxSum`, `bondMovedCoeff`); the
Bratteli path counts (`pathCount`) ARE the multiplicity/weight
combinatorics; log-concavity in the mode index (the `hlocalize` wall,
`UniformBoxLogConcave`) is the unimodality of the spectral weights that
licenses the plateau; the parity-TP₂ bricks and CB₂ composition are the
order structure of that spectrum. The corner refutations
(`FusionParityTP2`) record where naive spectral-order arguments FAIL —
the reflection at spin 0 (the vacuum boundary of the operator basis).

## 4. The continuum extrapolation = the RG margin recursion (the Clay core)

Real measurement: repeat at several `a` along "lines of constant physics"
(tune `g(a)` by asymptotic freedom, set the scale by `√σ`/`r₀`/`w₀`),
extrapolate `a → 0` with a FIT ansatz `m(a) = m + c·a² + …`; quote the fit
systematics.

Lean counterpart — THE decisive replacement of fit by proof: the
dimensionless margin `tm k = m_lat(a_k)/a_k` and the additive-erosion
recursion `(1 − δ_k)·tm k ≤ tm (k+1)` (`SingleStepDefectBound`). Where the
numericist FITS the a-dependence, the proof must BOUND the per-blocking
degradation δ_k. Anchor-dominance `(1 − Σδ)·m₀ > Σε` is the requirement
that the accumulated systematic budget stay below the measured signal at
the strong-coupling anchor — the exact analogue of "total systematic error
smaller than the plateau signal". This is `singleStep` — the atomic wall —
and the adjudications (per-move, resummation, variance, ε-split) are
machine-checked proofs that no bookkeeping rearrangement of the error
budget avoids bounding the physical per-step defect.

## 5. The error bars = certified interval/Taylor arithmetic (13.4 layer)

Real measurement: statistical errors (bootstrap) + systematic errors
(discretization, finite volume, excited states), combined into the quoted
uncertainty.

Lean counterpart: the certified `QI` interval kernel and the Taylor-model
layer in `u = 1 − w` — `hk_defect_uniform`/`magnitude_of_certOS`: ONE
kernel-`decide` coefficient certificate bounds the defect at EVERY coupling
in the window simultaneously (`defect(1−w) ≤ 6(1−w)²`), replacing per-`a`
error estimation the way a proven envelope replaces a fitted slope. The
machine-refuted `exact_cert_fails` records that the naive two-sided
certificate cannot represent the alternating discretization series — the
proof-side analogue of "you cannot bound a signed systematic by termwise
absolute values"; the corrected one-sided interface
(`TMDefectCertificateOS`) carries the honest residual.

## 6. The one open field = the matching computation

Real measurement: MCRG/Swendsen blocking matches effective actions between
lattice spacings; the item-9 Python scouting MEASURED the fused channel
amplitudes (the pilot enclosures `[c_j^lo, c_j^hi]`).

Lean counterpart: `TMDefectCertificateOS.dominate` — the amplitude
identification. **v2 CORRECTION (constructive, not computational):** the
fused channel amplitudes are NOT empirical quantities to be matched — one
RG block step on a compact group is a FINITE Haar integral = a finite
character sum = an EXACT RATIONAL already representable in-substrate
(`bondMovedCoeff`/`boxSum` ARE these objects). `dominate` must be
inhabited by DERIVATION from the Wilson measure (character/Clebsch
calculus of one block step, then channel-wise domination by the
heat-kernel form); the item-9 MCMC was Lakatos SCOUTING ONLY — it told
us which scheme and truncation to build the derivation around, and its
numbers never enter the proof. The reason we know the derivation is
there to be found is §0's second fact.

## The model in one sentence

The development replaces each stage of a lattice measurement —
spectroscopy, vacuum subtraction, spectral positivity, continuum
extrapolation, error budget, RG matching — by a machine-checked theorem
with exact rational data, and the whole Clay problem is now the single
stage a numericist calls "the matching": proving the measured per-blocking
defect amplitudes bound the true interacting defect.

## Refinement queue (update each session)

- v1 → v2: when the pathCount ballot layer lands, refine §3 with the
  explicit weight-positivity ↔ reflected-walk dictionary.
- When the `A·B − E·D` envelope lands, refine §2 with the decay-rate ↔
  fit-window correspondence.
- When `dominate` is attacked, refine §6 with the explicit item-9
  amplitude table and its Lean enclosures (provenance of every rational).
