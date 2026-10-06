# MATH NOTE — H1 at a fixed scale: what it requires, toy instances, and compatibility (2026-10-05)

Scope: paper-level analysis of H1 = `PathEpsBound tr c0`, i.e. at every dyadic scale `j`

    side_j · E_j ≤ c0 · B(Y_j, Y_j),   E_j = B(Y_j,Y_j) − B(Y_j, T Y_j),

for the box-smoothed coherent family state `Y_j = Y_{M_j}`, `M_j = m·side_j`, on the
all-nome completed Wilson carrier at nome `w_j`, width `side_j² + 1`. Lean companion:
`lean/YMGap/Continuum/BF4WilsonAllNomeH1FixedScale.lean`
(audit `audits/AUDIT-H1-FIXED-SCALE-2026-10-05.md`).

Every claim is tagged:

* **[PROVED]**: Lean-checked in the companion file or earlier repo files (axioms `propext`, `Quot.sound` only).
* **[PAPER]**: a rigorous derivation on paper from standard facts that the repo does not
  formalize (for example the spectral theorem for the positive contraction `T`).
* **[HEURISTIC]**: rests on physics input such as free-field spectral densities or
  two-loop asymptotic freedom (AF), or on numerics. These are not theorems.

---

## 0. Repo conventions that matter (checked in the sources)

* `Y_M = orbitSum x0 (timeKernel M)`, with `timeKernel M = boxKernel ((M+1)⁻¹) M`
  (lags `0..M`, weight `(M+1)⁻¹`). So `Y_M = p(T) x0` with the Fejér/box polynomial
  `p(λ) = (M+1)⁻¹ Σ_{k≤M} λ^k`.
* `T = completedTime 1`. It is symmetric (`completedInner_time_balance`) and positive
  (`mixedMoment_nonnegative`, `B(y,T^n y) ≥ 0`), a contraction (`response_le_of_le`), and it
  preserves the vacuum complement. On the complement, therefore, spectrum(T) ⊂ [0,1].
* `SmoothedCoherentEpsBound M scale c0 := side·E_M ≤ c0·B(Y_M,Y_M)`.
* `spacing j · side j = 1` (`unit_side`). The geometric spacing is *assigned* ("not a
  physical-time calibration"). So "`side_j` lattice steps = one unit of physical time"
  holds only under an AF calibration of the nome.
* AF interface: `AFRateCalibration.AFRateModulus` encodes `A'/(k+B) ≤ 1 − w_k ≤ A/(k+B)`
  ("`1 − w_k ≍ g_k² ≍ 1/k`"). The trajectory's link `NomeScheduleAFJustified` is OPEN and
  consumed nowhere. `dyadicNomeSchedule` (`1 − w_j = 2^{-(j+1)}`) is an interface witness
  only. It eventually violates the AF lower rate, because `2^{-(j+1)} < A'/(j+B)` for large `j`.
* The band `PathPhysicalContractionBand` and the producer `completedSectorContraction`
  (`w ≤ 1/2`) live on the **SU(2) extent-one cube** carrier, not on the all-nome Wilson
  carrier that carries H1. In the repo no bridge moves a cube rate onto the Wilson carrier.

---

## 1. Exact structure of `E_M` (fixed scale)

**1.1 Exact Fejér telescope [PROVED, `smoothedEnergy_telescope`].**

    E_M = (M+1)⁻¹ · ( B(x0, Y_M) − B(T^{M+1} x0, Y_M) ).

Spectrally this is the identity `(1−λ)p(λ) = (1−λ^{M+1})/(M+1)`. In Lean it is a response-level
telescope over `boxKernel` (`boxSum_shift_telescope`).

**1.2 Unconditional energy bound [PROVED, `smoothedEnergy_le_familyNorm`].**
`(M+1)·E_M ≤ B(x0,x0)`. The tail overlap `B(T^{M+1}x0, Y_M)` is nonnegative, and the
head overlap is `B(x0,Y_M) = avg_{k≤M} R_x(k) ≤ R_x(0)`.

**1.3 H1 restated exactly [PAPER, immediate from 1.1].** With `M = m·side`, H1 at scale `j` is
equivalent to

    avg_{k≤M} R_x(k) − avg_{k≤M} R_x(k+M+1)  ≤  c0·(M+1)/side · avg_{k,l≤M} R_x(k+l),

where `R_x(n) = B(x0, T^n x0)` and `(M+1)/side ≈ m`. H1 is thus a comparison between the
**single** box average of the unsmoothed family correlator and its **double** box
average. A lag-0 (ultraviolet) spike `R_x(0) ≫ R_x(k≥1)` enters the left side as
`R_x(0)/(M+1)` but the right side only as `R_x(0)/(M+1)²`. H1 holds iff the correlator
keeps a fraction of order `1/(c0·m)` of its box-averaged mass out to lag `~2M`.

**1.4 H2 ⟹ H1 [PROVED, `smoothedEpsBound_of_relativeFloor`,
`pathEpsBound_of_familyRadiusSurvival`].** `θ·B(x0,x0) ≤ B(Y,Y)` together with
`side ≤ c0·θ·(M+1)` gives H1. Along the trajectory, `PathFamilyRadiusSurvival tr θ` and
`1 ≤ c0·θ·m` give `PathEpsBound tr c0`. So the full A03 normalized-anchor package
follows from H2 alone (`path_normalized_anchor_of_familyRadiusSurvival`). H2 remains
OPEN and is the harder statement. Section 2 argues that it is false for local
plaquette families in the UV-dominated regime, and so is H1 for the unshifted kernel.

**1.5 Spectral formula [PAPER].** Let `μ_x` be the spectral measure of `x0` for `T` on the
vacuum complement, supported in `[0,1]`. Then

    B(Y,Y) = ∫ p(λ)² dμ_x,      E_M = ∫ (1−λ) p(λ)² dμ_x,      eps := E_M / B(Y,Y),

    p(λ)² = ( (1 − λ^{M+1}) / ((M+1)(1−λ)) )².

With `λ = e^{−εa}`, where ε is the physical energy and `a` the spacing:

* `p² ≈ 1` for `εa ≪ 1/M`;
* `p² ≈ (M εa)^{-2}` for `1/M ≪ εa ≲ 1`;
* `p(0)² = (M+1)^{-2}`, which never vanishes.

The box kernel suppresses UV weight only **polynomially, at second order**. It never suppresses
it exponentially, because its lag-0 weight is `(M+1)⁻¹ ≠ 0`. This is the Fourier transform of
the Fejér-type kernel that the parent asked for. Equivalently, the spectral weight seen by
`Y` is `μ_x` multiplied by `|p̂|²` evaluated at `λ = e^{−εa}`.

---

## 2. (a) What nome rate does H1 require?

### 2.1 Testing the proposed weak-coupling heuristic [HEURISTIC, with numerics]

The proposed picture: `Y_M` is a zero-momentum, time-smoothed F²-like composite, its weight
sits at two-particle states with energy `~2|p|`, and smoothing at radius `~side` removes
`|p| ≳ 1/side`, so `eps ~ 1/side`. Two corrections apply.

1. **Gapped spectrum.** In a gapped theory, zero-total-momentum two-particle states have
   `ε = 2√(p²+m²) ≥ 2m`, not `~2|p|`. This gives a *lower* bound `eps ≳ 1 − e^{−2m a}`
   (see 4.1). It is harmless for H1 only if `m·a_j ≲ 1/side_j`, which is a calibration
   condition (2.3).
2. **Smoothing removes the relative momentum only polynomially.** Zero total momentum, set
   by the spatial family coefficients, does not restrict the *relative* momentum of the
   pair. A local plaquette composite has dimension-4 spectral density
   `ρ(ε) ∝ ε^{2Δ−4} = ε⁴` at zero total momentum, at leading (Gaussian/free) order.
   The coupling prefactor (`∝ g⁴`) multiplies the numerator and the denominator of `eps`
   alike and cancels. So weak coupling does not help. In lattice units:
   * the UV part `εa ~ 1` contributes `~1/M²` to both `∫p²dμ` and `∫(1−λ)p²dμ`;
   * the IR window `εa ≲ 1/M` contributes only `~M^{-5}`.
   
   Hence `eps(Y_M) = O(1)`, not `O(1/side)`.

Numerics (`ρ ∝ ε⁴` on `[0,4]` in lattice units, `M = side`, script reproduced in the audit):

| side | 4 | 16 | 64 | 256 | 1024 |
|---|---|---|---|---|---|
| unshifted box: `eps·side` | 3.8 | 15.2 | 61 | 244 | 975 |
| shifted by `T^{side}`: `eps·side` | 1.5 | 1.8 | 1.85 | 1.87 | 1.88 |

The unshifted row is `eps ≈ 0.95` at every size, so H1 fails. The shifted row has
`eps ≈ 1.9/side`, so H1 holds with `c0 ≈ 2`. A massive version (threshold `2ma`, `ρ ∝
√(ε−2ma)·ε³`, physical box `L = side·a = 1`) gives the same split: unshifted `≈ 0.95`,
shifted `≈ 2.9/side`.

**Verdict [HEURISTIC]: with the repo's unshifted box kernel, H1 fails for local
plaquette families at every nome rate, weak coupling included.** This is a property of
the kernel, not of the schedule. The proposed heuristic is right in spirit only for a
UV-*suppressed* state.

### 2.2 The fix: a UV-suppressed anchor state [PAPER for the structure, HEURISTIC for the numbers]

Replace `Y_j` by `Y'_j = T^{h_j} Y_j`, with `h_j ≈ side_j/2` or `side_j`. Alternatively
use a smooth kernel such as `((1+T)/2)^{2M}`. Then the spectral weight acquires the factor
`λ^{2h} = e^{−2hεa}`, which suppresses UV exponentially, and

    eps(Y'_j) ≈ a_j · ⟨ε⟩_{e^{−2hεa} p² dμ}   with ⟨ε⟩ ~ max( c / (physical smoothing time), 2m ).

Structural points:

* [PAPER] `B(T^h Y, T^n T^h Y) = R_Y(n+2h)`, so the shifted eps involves only responses at
  lags `≥ 2h`. Those are the lags the A03 targets use anyway.
* [PROVED, d7e6b45d] The `NormalizedAnchorData` / `block_floor` / `real_floor` machinery is
  generic in the vector. A shifted anchor can feed it directly, provided there is a
  per-scale positive norm floor for `T^h Y`. That floor equals `R_Y(2h)`, which is itself a
  survival statement. At a fixed scale it is positive whenever a one-step floor exists; see
  2.4 for the caveat.
* This reformulation (call it H1′) is a *recommendation* and is **not implemented**.

### 2.3 The nome rate H1′ needs [HEURISTIC: AF and spectral input]

Write `L_j := side_j · a(w_j)` for the physical length/time of `side_j` lattice steps.
`a(w)` is the lattice spacing in units of the inverse physical mass `1/m`. From 2.2 and
the numerics, with a fixed `ρ` shape and varying `L` at `side = 256`:

| L | 1/16 | 1/4 | 1 | 4 | 16 |
|---|---|---|---|---|---|
| shifted `eps·side` | 1.69 | 1.81 | 2.92 | 8.64 | 30.8 |
| `2mL` | 0.125 | 0.5 | 2 | 8 | 32 |

So `eps_j·side_j ≈ max(O(1), 2m·L_j)`. **H1′ with a fixed `c0` requires `L_j` to stay
bounded: `a(w_j) ≲ c0/(2m·side_j)`.** The lattice spacing must shrink at least as fast as
`1/side_j`, which means `w_j → 1` at least as fast as the AF trajectory.

Two-loop AF gives `a(g)·Λ ∝ (b0 g²)^{−b1/(2b0²)} e^{−1/(2b0 g²)}`. For `L_j` bounded above
and below,

    1/(2 b0 g_j²) = j·ln 2 + (b1/(2b0²))·ln j + O(1).

At weak coupling the nome margin is linear in `g²` (`1 − w ≈ c_w g²`; I did **not** verify
the repo's exact `w ↔ β ↔ g²` constant `c_w`). This gives

    1 − w_j ≈ A_AF / (j + κ log j + O(1)),   A_AF = c_w / (2 b0 ln 2),   κ = b1/(2 b0² ln 2).

This is the repo's `AFRateModulus` shape, `1 − w_k ≍ A/(k+B)` with `k = j`, but with a
**pinned leading constant**. A two-sided `A/(k+B)` bound whose `A` differs from the AF value
gives `L_j ∝ 2^{j(1 − A_AF/A)}`, up to logarithms, and that tends to 0 or ∞. H1′ by itself
needs only the *upper* half, namely `L_j` bounded: `1 − w_j ≲ A_AF/j` asymptotically. A
fixed physical box (4.2) needs both halves.

**Consequence for `(1−w_j)·side_j` [HEURISTIC/AF]:** on any physical (AF-calibrated)
schedule,

    (1 − w_j) · side_j ≍ A_AF · 2^j / j  →  ∞.

It must diverge. If it stays bounded, as on `dyadicNomeSchedule` where it equals `1/2`, then
`g_j² = O(2^{−j})`, `a(w_j) ~ exp(−c·2^j) ≪ 1/side_j`, and `L_j → 0` superexponentially.
H1′ is then heuristically harmless, because the theory is effectively free and
`eps·side = O(1)`, but the "physical box" has zero size and nothing physical survives.

### 2.4 Where a "bounded `(1−w)·side`" condition *would* come from [PROVED ingredients, PAPER combination]

The only repo route from carrier data to H2, and hence to H1, is:

* the kinetic bound `E(x0) ≤ 192(1−w)·|qs|·Σc²`
  (`PlaquetteFamilyKineticUpper.completed_family_energy_nome_bound`);
* the norm floor `B(x0,x0) ≥ varianceFloor(w)·Σc²`;
* odd Jensen (`familyRadiusSurvival_of_oneStep_floor`), which gives `θ = ρ^{2M}` with
  `ρ = 1 − 192(1−w)|qs|/varianceFloor(w)`;
* then 1.4.

Uniformity would need `(1−w_j)·side_j·|qs_j| / varianceFloor(w_j)` to stay bounded. That
fails on AF schedules, where `(1−w)·side → ∞`. It also requires that `varianceFloor(w)`
stays bounded below as `w → 1`. It is `(localFloor w)^{24} / (600·(localCap w)^{24})`, a
crude heat-kernel density ratio. **I did not check** its `w → 1` behaviour; it very
plausibly degenerates. Also caution: the kinetic file requires faces in `spatialFaces base`
with `base < width`, a hypothesis the trajectory structure does not record. This route is
therefore not uniform, and on physical schedules it is not even consistent with the needed
rate.

---

## 3. (b) Toy instances

* **[PROVED] Fixed-scale H1 holds unconditionally with `c0 = side`**
  (`smoothedEpsBound_trivial`, because `E ≤ B(Y,Y)`). H1 is never vacuous or contradictory
  at a single scale on the actual carrier. All its content lies in the uniformity of `c0`.
* **[PROVED] Any instance of H2 is an instance of H1** (1.4).
* **[PROVED] The rate Prop is satisfiable**: `wilsonVacuumRayleighRate_one` (rate `r = 1`).
  Its content is `r < 1`.
* **[PAPER] Scalar toy.** Let `μ_x = δ_λ` with `λ = 1 − κ/side`, i.e. one mode at lattice
  energy `κ/side`. Then `p` drops out, `eps = 1 − λ = κ/side`, and H1 holds with `c0 = κ`.
  The Rayleigh rate `r = λ` gives `side·(1−r) = κ ≤ c0`, which is exactly the screen in 4.1,
  saturated. The Prop shape is therefore consistent. This toy cannot be plugged into
  `PathEpsBound`, because that Prop is tied to the Wilson carrier. The repo has no abstract
  `(B,T)` structure that `PathEpsBound` is generic over.
* **No uniform repo instance is known.**
  * The only explicit spectral toys in the repo are at a *fixed* gap. One is the
    five-holonomy Gaussian Perron ratio `q0 = 3 − 2√2 ≤ 9/50`
    (`BF4GaussianPerronRatio`). The other is the cube contraction rate
    `q(w) = (1+6C)/(2+6C)` at `w ≤ 1/2`.
  * Both are strong-coupling or fixed-mass data. Transported to the anchor state, they
    would *violate* H1 for `side > c0/(1−q)`, by 4.1.
  * The U(1) files (`BF4U1*`) are exponent-Gram and probability-tail carriers, with no
    transfer operator acting on a smoothed composite. I found no U(1) or Gaussian carrier
    with an explicit `T` on which H1 could be checked.
  * Strong coupling is the regime where H1 is checkably *false*, not true.

---

## 4. (c) Interaction with the `w ≤ 1/2` limit, the band, and a uniform physical gap

**4.1 Gap screen [PROVED, `oneStep_energy_ge_of_rayleighRate`, `epsBound_forces_rate`,
`path_epsBound_forces_rate`].** For any one-step Rayleigh rate `r` on the vacuum complement
of the *same* Wilson carrier (`WilsonVacuumRayleighRate r`: `B(y,Ty) ≤ r·B(y,y)`), we have
`E ≥ (1−r)·B(Y,Y)`. Therefore

    H1 at scale j  ⟹  side_j · (1 − r_j) ≤ c0     (rational form; distinct faces, nonzero coefficients).

H1 is an **upper** bound on every certified per-step gap: the lattice gap must close at
least like `c0/side_j = c0·spacing_j`. A gap gives only a *lower* bound on `eps`, so H1 is
not implied by a gap. H1 requires the anchor's spectral weight to sit near the bottom of
the spectrum.

**4.2 `w ≤ 1/2` [PROVED screen + PAPER transport].** The cube producer gives a fixed rate
`q(w) < 1` for `w ≤ 1/2`. If such a fixed rate held on the Wilson carrier along a schedule
staying in `w ≤ 1/2`, then 4.1 would contradict H1 as soon as `side_j > c0/(1−q)`. So the
`w ≤ 1/2` restriction is not an obstacle to be removed "for H1". H1 *needs* `w_j → 1`, which
is consistent with `nomeSchedule_eventually_not_le_half`. The transport of the cube rate to
the Wilson carrier is not in the repo; with it, the statement becomes a theorem.

**4.3 The band [PAPER, given a cube→Wilson rate bridge].** `PathPhysicalContractionBand`
asks for `m·spacing_j ≤ 1 − rate_j ≤ M·spacing_j` on the cube carrier. Under a bridge
identifying `rate_j` with a Wilson-carrier Rayleigh rate:

* H1 implies the **upper half with `M = c0`**, by 4.1 and `spacing_j = 1/side_j`.
* The **lower half** (a uniform physical gap `m`) is compatible with H1 **iff `m ≤ c0`**.
  With `r_j = 1 − m/side_j`, 4.1 gives exactly `m ≤ c0`.

So the answer to (c) is **yes, compatible**, with these constraints:

1. `c0 ≥ m`. The A03 parameters only need `c0 ≤ 2^a·δ`, so this is satisfiable by taking
   `a` large.
2. The schedule must be AF-calibrated so that `L_j = side_j·a(w_j)` is bounded above (for
   H1′) and below (for a physical gap measured in the unit `side_j` steps), as in 2.3.
3. The anchor state must be UV-suppressed (2.2). With the current unshifted box kernel,
   H1 is heuristically false, so compatibility is moot.

Taken together, a gap and H1 pin the anchor's spectral weight at physical energies in
`[m, c0]` in units of `1/L`. That is consistent with the shifted-kernel numerics, where
`eps·side ≈ 2mL` for `L ≳ 1`.

---

## 5. Summary table

| Item | Status |
|---|---|
| `E_M = (M+1)⁻¹(B(x0,Y)−B(T^{M+1}x0,Y))`, `(M+1)E_M ≤ B(x0,x0)` | PROVED |
| H1 at a fixed scale with `c0 = side` | PROVED (non-vacuity) |
| H2 ⟹ H1 (fixed scale and path); A03 anchor from H2 alone | PROVED (H2 OPEN) |
| Rayleigh rate ⟹ `E ≥ (1−r)B`; H1 ⟹ `side_j(1−r_j) ≤ c0` | PROVED (rate Prop OPEN for `r<1`) |
| Spectral formula, Fejér transform `p(λ)²` | PAPER |
| Unshifted box kernel: `eps = O(1)` for plaquette composites, H1 false at every rate | HEURISTIC (free-field `ρ ∝ ε⁴` plus numerics) |
| Shifted/smooth kernel: `eps·side ≈ max(O(1), 2m·L_j)` | HEURISTIC |
| Required rate for H1′: `L_j` bounded ⇔ `1−w_j ≲ A_AF/j`; `(1−w_j)·side_j → ∞` like `2^j/j` | HEURISTIC (AF; repo `w↔g²` constant not verified) |
| `dyadicNomeSchedule` ((1−w)side = 1/2) is not AF; physical box → 0 | PAPER (vs `AFRateModulus`) / HEURISTIC (box) |
| H1 incompatible with any fixed rate `r<1` (e.g. `w ≤ 1/2` cube rate) | PROVED on the Wilson carrier; PAPER for the cube transport |
| H1 compatible with a uniform physical gap `m` iff `m ≤ c0` | PROVED inequality given rates; PAPER for the band bridge |

**Recommendation.** Reformulate H1 for a UV-suppressed anchor, either `T^{side_j/2}Y_j` or
a smooth time kernel, and feed it to the existing generic `NormalizedAnchorData`. Keep H2
out of the critical path: as stated, H2 is at least as hard as H1 and is heuristically false
for unsmoothed local families.
