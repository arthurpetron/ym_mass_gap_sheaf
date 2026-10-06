# Math note: what `PathShiftedWindowSurvival` means, and what could prove it (2026-10-06)

Paper only. No Lean. Status: `PathShiftedWindowSurvival` is OPEN. This note
argues that it is a quantitative continuum-scaling statement. No known
rigorous technique for 4D SU(2) reaches it.

## 0. Setup

At scale `j` the carrier is the completed Wilson/heat-kernel carrier at nome
`w_j`. Its spatial width is `W_j = side_j² + 1` lattice units, it is infinite in
time, and the one-step transfer operator is `T`. On the vacuum complement `T`
is self-adjoint with `0 ≤ T ≤ 1`. The anchor `x_j = Y_j` is the box-smoothed
centered plaquette family, and

  `R_j(n) = <x_j, T^n x_j> = ∫_[0,1] λ^n dμ_j(λ)`,

where `μ_j` is the spectral measure of `x_j` for `T`. Write `λ = e^{-aE}`,
with `a = a(w_j)` the lattice spacing and `E` a physical energy. Lean never
builds `μ_j`. It uses only the Hausdorff moment positivity
`m(k,l) = ∫ λ^k (1-λ)^l dμ ≥ 0`, which is the source of convexity,
log-convexity and monotonicity. Everything below is the measure-theoretic
reading of statements that Lean handles through moments.

The Prop, for `s = side_j` and `j ≥ 1`:

  `θ R_j(s/2) ≤ R_j(s+1)`   (fixed `θ ∈ (0,1]`, uniform in `j`).

## 1. Spectral meaning

Let `ν_s` be the probability measure proportional to `λ^{s/2} dμ`: the
spectral measure of the time-shifted anchor `T^{s/4} x`. Then the Prop reads

  `∫ λ^{s/2+1} dν_s(λ) ≥ θ`.

- **Necessity.** For `c > 0`, the part of `ν_s` on `λ < 1 - c/s` contributes at most
  `(1 - c/s)^{s/2+1} ≤ e^{-c/2}`. Hence `ν_s([1 - c/s, 1]) ≥ θ - e^{-c/2}`.
  With `c = 2 log(2/θ)`, at least `θ/2` of the shifted weight sits at `λ ≥ 1 - c/s`,
  i.e. at `aE ≲ c/s`.
- **Sufficiency.** If `ν_s([1 - c/s, 1]) ≥ p`, then the integral is at least
  `p (1 - c/s)^{s/2+1} ≈ p e^{-c/2}`.

So, up to constants, the Prop says this: **after evolving for `s/2` steps, a
fixed fraction of the anchor's remaining spectral weight sits at energies
`E ≲ C/(s·a)`.** On an AF-calibrated schedule `s·a(w_j) ≍ L` is a fixed
physical length, so these are energies `O(1/L)` in physical units. The
shift `λ^{s/2}` already removes weight at `aE ≫ 1/s`, including the UV part of
a lattice plaquette. What remains to control is the low-lying part, relative
to itself. The Prop fails exactly when the shifted weight piles up at
`aE ≈ K/s` with `K → ∞`.

Two consequences:

- **It is an upper bound on the gap in lattice units.** The Prop implies
  that the anchor channel has spectral weight at `1 - λ ≲ C/s`, i.e. lattice
  mass `m(w_j)·a ≲ C/side_j`. Equivalently, the correlation length in
  lattice units is at least `side_j/C`. This is the opposite direction from a
  mass-gap lower bound. It is a scaling statement, and the mass gap is not
  what it asks for.
- **It is consistent with a mass gap.** If a continuum limit with physical
  gap `m > 0` exists on this schedule, then `1 - λ_gap ≈ m a ≈ mL/side`. If
  the anchor's shifted weight is dominated by states with `E ≲ C'/L`, then
  `R(s+1)/R(s/2) ≳ e^{-(C'/2)(1 + 2/s)}`. The plaquette's small overlap with
  low states (polynomial in `a`) does not matter, because the Prop is a ratio
  taken after the shift. Note also that the spatial width
  `W_j = side_j² + 1` is `≈ side_j·L` in physical units. The carrier therefore
  approaches infinite physical volume, so the Prop includes the infrared
  problem as well as the scaling problem.

## 2. Sanity check: it FAILS at any fixed coupling

At fixed `w < 1` in the strong-coupling regime, the cluster expansion
(Osterwalder–Seiler 1978; see also Seiler, LNP 159, 1982) gives exponential
clustering uniformly in the volume, with a lattice mass `m_lat(w) > 0` that
grows as the coupling gets stronger (roughly like `-log` of the
character-expansion parameter). Through the transfer matrix, the gauge-invariant
vacuum complement has spectrum in `[0, e^{-m_lat}]`. Then

  `R(s+1) ≤ e^{-m_lat (s/2+1)} R(s/2)`,

so for fixed `θ` the Prop fails once `s > 2 log(1/θ)/m_lat`. This matches
the Lean screen `path_shiftedEps_forces_rate` (`side_j (1 - r_j) ≤ c0`): a
certified uniform rate `r_j ≤ r < 1` is incompatible with the shifted H1 for
large `side_j`. The same holds at ANY fixed coupling where a lattice gap
exists. So the Prop can hold only along `w_j → 1` at a rate matched to
`side_j`, and AF calibration is meant to arrange exactly that. Strong coupling
itself is never on the path (`w_j → 1` is weak coupling). This check only
confirms that the Prop has real content.

The opposite extreme is abelian. In 4D U(1) at weak coupling the Coulomb
phase is massless (Guth 1980; Fröhlich–Spencer 1982). Correlations decay
polynomially, and the analogous Prop would hold trivially even at fixed
coupling. Nothing transfers this to SU(2).

## 3. Known rigorous inputs and what they give

| Input | What it gives | Does it imply the Prop? |
|---|---|---|
| Reflection positivity / transfer matrix (Osterwalder–Seiler 1978; Seiler LNP 159) | `T` self-adjoint and positive; `R` is a Hausdorff moment sequence, so log-convex and antitone | No. Already used in Lean. Log-convexity turns a one-step ratio at lag `s/2` into survival, but that one-step bound is itself an eps-type bound, so this is circular. |
| Chessboard estimates (Fröhlich–Israel–Lieb–Simon 1978) | UPPER bounds on expectations of products of local observables (Peierls arguments, phase transitions) | No. Wrong direction. They give no lower bounds on long-time correlations. |
| Infrared bounds / Gaussian domination (Fröhlich–Simon–Spencer 1976) | For RP models with a suitable quadratic structure: upper bounds on the Fourier two-point function. With a sum rule they give long-range order in spin models | No for SU(2). Gaussian domination needs structure that nonabelian Wilson actions lack. The abelian Coulomb-phase results use different methods. |
| Strong-coupling / cluster expansions (Osterwalder–Seiler; Seiler LNP 159) | Mass gap and exponential decay at small `β` | No. They show the Prop FAILS there (§2). |
| Balaban's RG program (CMP series, mid-1980s; expository rederivation by Dimock, "The renormalization group according to Balaban") | UV stability: bounds on effective actions and partition functions uniform in the lattice spacing, in a FIXED finite physical volume, while the coupling at the final scale stays small | Not as it stands. It controls effective actions, not correlation functions or the transfer-matrix spectrum at distance `~ side` lattice units. It does not cover the infrared, i.e. large physical volume where the coupling grows. Our carrier has growing physical width. |
| Perturbation theory | Two-loop running (the source of the AF calibration); asymptotic expansions | No. Asymptotic only, with no nonperturbative control of the long-distance spectrum. |
| Griffiths/GKS/Ginibre correlation inequalities | Monotonicity in couplings and lower bounds for ferromagnetic Ising/abelian (Z2, U(1)) systems, including abelian gauge theories | No. To my knowledge no Griffiths/Ginibre second-inequality analogue is available for SU(2) lattice gauge theory that would give monotonicity in `β` or lower bounds on loop correlations. |

## 4. What statement would actually be needed, and how close it is to the full problem

A sufficient (and essentially necessary) pair of conditions:

- **(a) Scaling.** Along `w_j`, the lattice correlation length in the
  anchor channel satisfies `ξ(w_j) ≥ side_j/C` in lattice units, uniformly in the
  growing spatial width. This is a LOWER bound on correlations at time distance
  `~ side_j`.
- **(b) No escape.** After the `s/2` shift, the anchor's normalized spectral
  weight does not migrate to `aE ≫ 1/side_j`. Given (a) and a reasonable
  continuum limit, this is a statement about overlaps with the low-lying states.

(a) is a quantitative form of the existence of a nontrivial continuum scaling
limit: the correlation length diverges at the asymptotic-freedom rate. That is
a core part of the "existence" half of the Yang–Mills problem, and it is not
the mass-gap half. Adding a mass gap gives `ξ ≍ side_j`. To my knowledge it is
not even rigorously known that the 4D SU(2) lattice correlation length (in
lattice units, infinite volume) diverges as `β → ∞`, let alone at the AF rate.
**Assessment: the Prop on the AF schedule, as posed in growing physical
volume, is out of reach of known methods.** In difficulty it is comparable
to a substantial part of the full problem.

## 5. Possible partial routes (honest)

1. **A fixed-physical-volume variant.** Change the carrier width from
   `side_j² + 1` to `c·side_j + 1`, a fixed physical box of size `~ cL`. The Prop
   then becomes a small/finite-volume weak-coupling statement. There, the
   theory is expected to be perturbative at the box scale (with the usual
   zero-mode/torelon subtleties), and Balaban-type UV control is the
   relevant input. It would still need an extension of that control to
   correlation functions and the transfer matrix, which is not available.
   It would also change the A03 setup: the padding currently needs faces in
   `spatialFaces(side_j²)` with `side_j² < W_j`. It would be a well-posed
   research direction rather than a wall, but the result would be finite-volume
   only and would not by itself give the infinite-volume package.
2. **Abelian/Gaussian comparison.** The free field (heuristic: window survival
   flat in `side` at bounded `L`) and U(1) Coulomb phase (polynomial decay)
   both satisfy the analogue. No comparison inequality transfers this to SU(2).
3. **Weakening the Prop.** A survival `θ_j` that decays slowly (e.g. polylog in
   `side_j`) would feed a `j`-dependent `c0_j`. The current Lean statements fix
   `c0` and `δ` uniformly. Whether A03 could absorb `c0_j → ∞` is an open
   design question for YM Bot or darthur. It would weaken the conclusion
   (`κ_j → 0`).
4. **Numerics.** The MC window-survival estimates (P6) are unsettled at side 10
   (streams A/B disagree by ~2.4σ, and W is sensitive to vacuum subtraction at large lag).
   They can support plausibility but not prove anything.

## References (cited only at the level I am confident of)

- K. Osterwalder, E. Seiler, "Gauge field theories on a lattice", Ann. Phys. 110 (1978): RP, transfer matrix, strong-coupling cluster expansion and mass gap.
- E. Seiler, *Gauge Theories as a Problem of Constructive Quantum Field Theory and Statistical Mechanics*, Lecture Notes in Physics 159, Springer (1982).
- J. Fröhlich, R. Israel, E. Lieb, B. Simon, "Phase transitions and reflection positivity I", Commun. Math. Phys. 62 (1978): chessboard estimates.
- J. Fröhlich, B. Simon, T. Spencer, "Infrared bounds, phase transitions and continuous symmetry breaking", Commun. Math. Phys. 50 (1976).
- T. Bałaban, series "Renormalization group approach to lattice gauge field theories" and "Large field renormalization", Commun. Math. Phys. (1983–1989).
- J. Dimock, expository series "The renormalization group according to Balaban" (2010s).
- A. Guth, "Existence proof of a nonconfining phase in four-dimensional U(1) lattice gauge theory", Phys. Rev. D 21 (1980); J. Fröhlich, T. Spencer, "Massless phases and symmetry restoration in abelian gauge theories and spin systems", Commun. Math. Phys. 83 (1982).

No theorem numbers are cited. Exact page and volume details beyond the above
should be checked before reuse.
