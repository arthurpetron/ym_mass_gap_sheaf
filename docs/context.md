# Conversation Summary

This file is the seed context for Claude Code sessions working on the
constructive Yang–Mills mass gap program. It summarizes the analytic
reframings agreed in conversation, isolates the load-bearing
hypotheses, and records the open obligations. The authoritative
specification lives in `docs/outline.md`; this file is the
*motivation* for that spec.

---

## 1. Intuitionistic gap audit of the original outline

A constructive (Bishop / Martin-Löf, not merely non-circular classical)
reading of the original depth-5 outline surfaces four families of gap.
These motivate the moduli registry and constructive law in
`docs/outline.md` §0 and §2.

### 1.1. Existence claims without explicit moduli

- Polymer activity summability must return an explicit pair
  $(\rho, K)$ with
$$
\sum_{X \ni x} |a(X)| \, e^{\rho(X)} \le K,
$$
both computable from $G$ and the RG scale. "Summable" without a
witness function is not constructively meaningful.
- $\sigma_G > 0$ requires a positive rational lower bound
  $\sigma_G \ge \sigma_0(G, a, L) > 0$ with $\sigma_0$ computable from the
  input datum. Otherwise its survival under RG scaling cannot be
  tracked.
- The continuum modulus $\varepsilon(r, N)$ must be presented up
  front, not extracted post hoc.

### 1.2. LEM / choice usage hidden in standard tools

- The classical conversion of Euclidean time-direction exponential
  decay into a transfer-matrix gap uses the spectral theorem for
  self-adjoint operators on a separable Hilbert space, which requires
  countable choice. The constructive substitute is a quantitative
  resolvent bound
$$
\|(H - z)^{-1}\| \le M_G(d(z))
$$
on an explicit annulus around $0$. Bridges–Ishihara have constructive
spectral-gap lemmas; the program must cite one rather than appealing
to "the transfer matrix has a gap."
- The vacuum $\Omega_G$ must be constructed as the limit of
  finite-volume ground states with an explicit rate, inherited from
  the finite-volume gap modulus, not as the lowest eigenvector of a
  classically self-adjoint Hamiltonian.
- The observable algebra stays at the pre-$C^*$ level; operator-norm
  completion happens only inside GNS with explicit Cauchy witnesses.

### 1.3. Genuine logical circularity that survives "no-circularity"

This is where the original outline was most vulnerable:

- **Pointwise vs. uniform clustering.** The chain
  finite-scale-clustering $\to$ spectral-gap-transfer $\to$
  regulator-comparison silently switches between
  *clustering at fixed $(a, L)$* and *clustering with $(a, L)$-uniform
  constants*. The latter is strictly stronger. Both must appear in
  the moduli registry as separate quantities $m_0(G,a,L)$ and
  $m_\infty(G, r)$, and the implication must be proved, not assumed.
- **RG survival of the area-law constant.** The block-spin map
  generates new operators. The area-law constant $\sigma$ is defined
  for the *original* action, so its survival under RG is a separate
  theorem, not a corollary.

### 1.4. Smaller issues

- Gribov-safe finite patches must be exhibited with a computable
  partition of unity. The Singer obstruction means there is no global
  section; the patch atlas is part of the constructive output.
- "Nonzero" and "bounded away from zero by an explicit estimate" are
  different constructive claims. Only the latter is admissible as a
  nontriviality witness.
- Reflection positivity is action-dependent. For the heat-kernel
  action it uses character-expansion positivity (Menotti–Onofri).

---

## 2. The $\sigma$-1 / $\sigma$-2 / $\sigma$-3 distinction

The statement "$\sigma_G > 0$ with constants surviving RG scaling" is
ambiguous between three different things, and which one is intended
controls everything downstream.

- **($\sigma$-1) Pointwise survival.** For each scale $k$, there
  exists $\sigma_k > 0$ with
$$
\langle W_R(C) \rangle \le C_k \exp(-\sigma_k A(C))
$$
at scale $k$. Insufficient: $\sigma_k$ could tend to $0$.

- **($\sigma$-2) Uniform survival.** There exists $\sigma_* > 0$ such
  that $\sigma_k \ge \sigma_*$ for all $k$ in the RG trajectory.
  Useful only after fixing length renormalization, because $\sigma_k$
  is dimensionful.

- **($\sigma$-3) Renormalized survival.** There exists
  $\sigma_{\mathrm{phys}}(G) > 0$ and a dimensional rescaling
  $\widehat{\sigma}_k := a_k^2 \sigma_k$ such that
$$
\widehat{\sigma}_k \ge \sigma_{\mathrm{phys}}(G) > 0
$$
uniformly in $k$. This is what is physically true (string tension
has dimensions of mass squared, so it rescales).

The program targets ($\sigma$-3). Once length renormalization is
fixed, ($\sigma$-3) reduces to ($\sigma$-2) for the renormalized
quantity $\widehat{\sigma}_k$.

---

## 3. The Uniform Area-Law hypothesis $\mathrm{UAL}(G)$

### 3.1. The classical obstruction

Configuration space at scale $k$ is $\Omega_k = G^{E_k}$ where $E_k$
is the set of links at lattice spacing $a_k$. Bałaban's small-field
region is
$$
\Omega_k^{\mathrm{sf}} = \{ U \in \Omega_k : \forall p, \ d(U_p, 1) < \delta_k \}
$$
where $\delta_k$ is a scale-dependent smallness parameter (typically
$\delta_k \sim g_k^\alpha$ for some $\alpha \in (0, 1)$) and $d$ is the
geodesic distance on $G$. The complement
$\Omega_k^{\mathrm{lf}}$ is the large-field region.

The two activity bounds in play:

**Small-field bound.** On $\Omega_k^{\mathrm{sf}}$, after gauge-fixing
to a Gribov-safe patch, the action is approximately Gaussian:
$$
S_k(U) = \tfrac{1}{2} \langle A, \Delta_k A \rangle + V_k(A),
$$
where $A$ is the exponential-coordinate gauge field, $\Delta_k$ is a
covariant Laplacian, and $V_k$ is a polynomial interaction of degree
$\ge 3$. The polymer activity satisfies
$$
|a_k^{\mathrm{sf}}(X)| \le \exp\!\left( -\rho_{\mathrm{sf}} \cdot |X|_{\mathrm{phys}} / a_k \right)
$$
with $\rho_{\mathrm{sf}} > 0$ controlled by the spectral gap of
$\Delta_k$ on $X$. This is Bałaban's small-field stability theorem;
it depends on continuum-like propagator estimates.

**Large-field bound.** On $\Omega_k^{\mathrm{lf}}$, the action is
controlled by the heat-kernel character expansion
$$
K_t(g) = \sum_\lambda d_\lambda \, \chi_\lambda(g) \, e^{-t C_2(\lambda)},
$$
and polymer activities are bounded by
$$
|a_k^{\mathrm{lf}}(X)| \le \exp(-\rho_{\mathrm{lf}} |X|_{\mathrm{plaq}}),
$$
where $|X|_{\mathrm{plaq}}$ counts plaquettes (not continuum volume),
and $\rho_{\mathrm{lf}}$ depends on the Casimir gap
$C_2(\lambda_1) - C_2(\lambda_0) = C_2(\lambda_1)$.

**Why this is hard.** The two bounds live on different geometric
objects: small-field on a continuum-like density indexed by physical
units, large-field on a lattice-combinatorial density indexed by
plaquette count. A single inductive invariant has to choose units,
and either choice penalizes the other regime.

Bałaban's response was to keep the small-field expansion as master
and treat large-field as corrections with an absolutely convergent
expansion of their own. The corrections accumulate over scales, and
the accumulation has never been bounded uniformly in $k$.

The crisp version of the difficulty:

> The small-field activity and the large-field activity are not
> restrictions of a single function to two subsets of $\Omega_k$.
> They are two different upper bounds derived under two different
> approximations of the action. The gluing on the overlap is not "the
> function on $X \cap Y$ is well-defined"; it is "we have two
> different upper bounds that need to be reconciled." That is a
> *cocycle* problem, not a *restriction* problem.

This is the observation the sheaf reformulation leverages.

### 3.2. The sheaf reformulation

Define a Grothendieck site over $\Omega_k$ whose objects are pairs
$(U, X)$ with $U \subseteq \Omega_k$ open and $X$ a finite connected
polymer, with morphisms $(U, X) \to (U', X')$ when $U \subseteq U'$
and $X \subseteq X'$. The coverage is generated by the
small / large / buffer decomposition:
$$
\{(\Omega_k^{\mathrm{sf}}, X), (\Omega_k^{\mathrm{lf}}, X), (\Omega_k^{\cap}, X)\}
\Rightarrow (\Omega_k, X).
$$

Two coupled sheaves live on this site.

**Bound-witness sheaf $\mathcal{A}_k$.** A presheaf of activity bounds
with values in the poset $(\mathbb{R}_{\ge 0}, \le)$:
$$
\mathcal{A}_k(U, X) = \{ f : U \to \mathbb{R}_{\ge 0} : f \text{ bounds the polymer contribution of } X \text{ on } U \},
$$
Bishop-constructive with explicit modulus. Restriction means "this
bound remains valid on the smaller open" (so tighter bounds on smaller
sets are admissible). Gluing on overlaps is by domination, not
equality:
$$
s^{\cap} = \max(s^{\mathrm{sf}}, s^{\mathrm{lf}}).
$$
With values in $(\mathbb{R}_{\ge 0}, \le)$ and gluing as pointwise
supremum, $\mathcal{A}_k$ is *flabby*: every section over an open
extends to a larger open by taking the bound looser. The sheaf
condition is then automatic, which means the analytic content lives
elsewhere.

**Summability-certificate presheaf $\mathcal{S}_k$.** For each
admissible bound in $\mathcal{A}_k$, a certificate of Kotecký–Preiss
convergence: a pair $(\rho, K)$ satisfying
$$
\sum_{X \ni x} |a_k(X)| \, e^{\rho(X)} \le K.
$$
Small-field, large-field, and overlap each carry their own KP
witnesses
$(\rho_{\mathrm{sf}}, K_{\mathrm{sf}})$,
$(\rho_{\mathrm{lf}}, K_{\mathrm{lf}})$,
$(\rho_{\cap}, K_{\cap})$.

The compatibility between $\mathcal{A}_k$ and $\mathcal{S}_k$
is what carries the analytic content. The sheaf reformulation
*isolates* the overlap summability obligation as a free-standing
problem, rather than entangling it with the small-field and
large-field bounds as in the classical Bałaban setup.

### 3.3. The inductive step

At each RG step $k \to k+1$, prove:

Given
- a cover $\{\Omega_k^{\mathrm{sf}}, \Omega_k^{\mathrm{lf}}, \Omega_k^{\cap}\}$ of $\Omega_k$ with smallness parameter $\delta_k$,
- small-field bounds $s^{\mathrm{sf}} \in \mathcal{A}_k(\Omega_k^{\mathrm{sf}}, \cdot)$ with KP data $(\rho_{\mathrm{sf}}, K_{\mathrm{sf}})$,
- large-field bounds $s^{\mathrm{lf}} \in \mathcal{A}_k(\Omega_k^{\mathrm{lf}}, \cdot)$ with KP data $(\rho_{\mathrm{lf}}, K_{\mathrm{lf}})$,
- overlap compatibility: $\max(s^{\mathrm{sf}}, s^{\mathrm{lf}})$ on $\Omega_k^{\cap}$ has KP data $(\rho_{\cap}, K_{\cap})$,

then after applying the block-spin map $T_b$ there exist a new cover
$\{\Omega_{k+1}^{\mathrm{sf}}, \Omega_{k+1}^{\mathrm{lf}}, \Omega_{k+1}^{\cap}\}$,
pushforward bounds $(T_b)_* s^{\mathrm{sf}}$, $(T_b)_* s^{\mathrm{lf}}$,
and new KP data $(\rho'_{\mathrm{sf}}, K'_{\mathrm{sf}})$,
$(\rho'_{\mathrm{lf}}, K'_{\mathrm{lf}})$, $(\rho'_{\cap}, K'_{\cap})$,
satisfying:

1. $\rho'_{\mathrm{sf}} \ge \rho_{\mathrm{sf}} - \varepsilon_{\mathrm{sf}}(b, g_k)$, controlled by the small-field machinery.
2. $\rho'_{\mathrm{lf}} \ge \rho_{\mathrm{lf}} - \varepsilon_{\mathrm{lf}}(b, g_k)$, controlled by character-expansion stability.
3. $K'_{\cap} \le K_{\cap} + \Delta_{\cap}(b, g_k)$ with $\sum_k \Delta_{\cap}(b, g_k) < \infty$.
4. The renormalized string tension transports through a sheaf 2-cell
$$
\Theta_k : \widehat{\sigma}_{k+1} \Rightarrow \widehat{\sigma}_k - \eta_k,
$$
with $\eta_k \ge 0$, $\sum_k \eta_k < \widehat{\sigma}_0$, so that
$\inf_k \widehat{\sigma}_k > 0$.

If this inductive step closes, $\mathrm{UAL}(G)$ holds and the mass
gap follows by the spectral-gap transfer (`docs/outline.md` §12).

### 3.4. The overlap measure bound

Define the buffer region
$$
\Omega_k^{\cap} = \{ U \in \Omega_k : \exists p, \ \delta_k / 2 < d(U_p, 1) < 2 \delta_k \}.
$$
This is the set of configurations where some plaquette is in the
indeterminate zone, neither clearly small nor clearly large. By
construction $\Omega_k^{\cap} \supseteq \Omega_k^{\mathrm{sf}} \cap \Omega_k^{\mathrm{lf}}$ for an appropriate buffer thickness.

The claim is that the measure of the buffer admits a constructive bound
$$
\mu_k(\Omega_k^{\cap}) \le N_p(k) \cdot C(G) \cdot \exp\!\left( -\frac{\kappa(G)}{g_k^2} \right) \cdot g_k^{\beta(G)},
$$
where
- $N_p(k)$ is the number of plaquettes at scale $k$ (polynomial in $L_k / a_k$),
- $\kappa(G) > 0$ is set by the smallest nonzero Casimir $C_2(\lambda_1)$ in the heat-kernel expansion,
- $\beta(G)$ is determined by the dimension of the buffer shell in $\mathfrak{g}$-space,
- $C(G)$ is an explicit constant from the heat-kernel asymptotics.

These constants are computable from the representation-theoretic data
in `docs/outline.md` §3.4.

The structural fact: the bound depends on $g_k$ exponentially through
$\exp(-\kappa / g_k^2)$, not polynomially. So as long as $g_k$ stays
bounded above by some $g_{\max} < \infty$ throughout the RG trajectory
(which it does, because the running is logarithmic and only finitely
many scales are traversed before the IR cutoff), the overlap measure
is summable in $k$. The constant $\kappa(G)$ is structural — not
sensitive to which scale you are at.

**Warning.** The union bound used to sum the single-plaquette tail
estimate over plaquettes is doing real work and may be too loose.
$N_p(k)$ grows like $(L_k / a_k)^4$ in 4D, and the exponential has to
beat it. Exponentials beat polynomials for fixed $g_k$, but the
question is whether the constants align with the small-field and
large-field KP constants in a single inequality. This is the place
to do explicit SU(2) calculations before claiming success.

A separate issue: the overlap measure bound gives "small probability
of buffer," not "small KP contribution from buffer." Converting one
to the other uses Hölder against the polymer activity, which is what
the constant $K_{\cap}$ in §3.3 encodes.

---

## 4. The three approaches considered, and why approach (ii) was chosen

Three approaches were considered for proving $\mathrm{UAL}(G)$:

### Approach (i): Optimize the matching scale $k_*$

In the classical Bałaban-plus-strong-coupling strategy, the
compatibility requirement
$$
K(G; k_*) < r(g_{k_*})
$$
links the accumulated polymer mass from small-field control up to
scale $k_*$ with the strong-coupling radius of convergence of the
heat-kernel character expansion at the effective coupling $g_{k_*}$.
Both quantities are explicit functions of $G$'s representation theory
and the two-loop $\beta$-function running. There may be a sweet spot
$k_*(G)$ where the inequality holds with room to spare. Computing
the curve $K(G; k_*)$ vs. $r(g_{k_*})$ explicitly would be a
publishable theorem on its own. The reason this is hard: the
inequality has to hold *with the right constants*, and the
effective-theory polymer corrections couple the two sides.

### Approach (ii): Sheaf-glued continuous interpolation [CHOSEN]

Instead of UV-Bałaban-up-to-$k_*$ then strong-coupling-from-$k_*$-on,
run a single expansion whose activity bound interpolates between the
two regimes. Brydges–Slade in their lace-expansion work and the
Gawędzki–Kupiainen hierarchical models both have versions of this:
the activity has a perturbative small-field contribution and a
nonperturbative large-field contribution, bounded together by a
single inductive invariant. For Yang–Mills the obstacle has always
been that the large-field bound uses character expansion
(lattice-discrete) while the small-field bound uses Gaussian
propagator estimates (continuum-like). Sheaf-theoretic gluing of
local data is exactly the structure needed to interpolate between two
locally-defined activity bounds on overlapping configuration regions.

This is the approach the program develops.

### Approach (iii): Exploit the global form datum

Most existing attempts work with $SU(N)$. The center symmetry —
$Z_N$ for $SU(N)$, trivial for the adjoint form — interacts with the
area law via 't Hooft loops. For the adjoint form $G / Z(G)$, the
center symmetry is gauged away and 't Hooft loops are local
operators. This changes the polymer expansion structure
non-trivially. The program's input datum (`docs/outline.md` §1.1
item 2) already carries the global form, so this approach remains
available as a flanking move after the SU(2) pilot.

---

## 5. Open analytic obligations

The architecture isolates, but does not discharge, the following
analytic obligations. These are documented in `docs/outline.md` §17.

1. **Overlap bound rigor.** The buffer-shell union bound must be
   tightened or replaced by a chaining/correlated-plaquette estimate
   if too loose.
2. **Block-spin pushforward of $K_{\cap}$.** Need explicit proof that
   $K_{\cap, k+1} \le K_{\cap, k} + \Delta_{\cap}(b, g_k)$ with
   $\sum_k \Delta_{\cap} < \infty$. The block-spin map can smooth
   configurations but can also create overlap.
3. **Dimensional rescaling as sheaf 2-cell.** The identity
   $a_k^2 \sigma_k \rightsquigarrow a_{k+1}^2 \sigma_{k+1}$
   must be proven as compatibility data of the block-spin sheaf
   morphism, not inserted by definition.
4. **Gribov copies in the overlap.** Small-field gauge ambiguity is
   localized to the buffer region. The overlap measure must absorb
   the Gribov boundary contribution with explicit constants.

None of these are "open problem nobody can solve." All are concrete
calculations. That is a different kind of obligation than the
matching-scale problem of approach (i), which was a fundamental
compatibility question. The sheaf architecture eats the
compatibility question and leaves bookkeeping.

---

## 6. The Codynamic / sensor-data transfer

The repository `codynamic-sensor-data` is relevant *structurally*,
not because its code can be applied directly to Yang–Mills.

| Sensor-fusion library | Yang–Mills program |
|---|---|
| local sensor section | local activity-bound witness |
| overlap agreement | overlap domination / summability |
| gluing failure | failure of KP compatibility |
| rewind event | RG correction / degradation event |
| RewindBudget | summable degradation budget $\sum_k \Delta_{\cap}$ |
| manifold-aware estimator | Lie-group / gauge-field local chart |
| cadence / discontinuity detector | small / large / buffer regime detector |

The type signature to port:

> local trusted estimate $+$ overlap compatibility $+$ summable
> innovation budget $\Rightarrow$ global stable bound.

This is the same proof shape required for sheaf-glued Yang–Mills
activity bounds. The EKF/UKF inductive invariant in
`codynamic-sensor-data` has, internally:
"covariance bound at step $k+1$ $\le$ covariance bound at step $k$ $+$
innovation, with innovation summable over $k$." That is
structurally identical to obligations (1)–(3) of the inductive step in
§3.3, with the manifold support (SO(3), SE(3)) playing the role of
the gauge group support (compact simple $G$).

The Codynamic frame is not an analogy; it is a *typed template* whose
test cases in `codynamic-sensor-data` constitute a working existence
proof that constructive sheaf-gluing of bound certificates can be
made to close inductively. The YM theorems are not corollaries of
the sensor-fusion theorems, but the proof technology transfers.

---

## 7. The pilot plan: SU(2)

The next concrete step is to instantiate the full apparatus for
$G = SU(2)$. The five-step pilot, expanded from `docs/outline.md`
§18:

1. **Site with small / large / overlap cover.** Define
$$
\Omega_k = SU(2)^{E_k}
$$
and the cover
$\{\Omega_k^{\mathrm{sf}}, \Omega_k^{\mathrm{lf}}, \Omega_k^{\cap}\}$
with explicit $\delta_k$.

2. **Sheaf $\mathcal{A}_k$.** Bishop-constructive nonnegative bounds
   on polymer contribution, with overlap gluing
   $s^{\cap} = \max(s^{\mathrm{sf}}, s^{\mathrm{lf}})$.

3. **Summability presheaf $\mathcal{S}_k$.** Compute explicit
   candidate KP constants
   $(\rho_{\mathrm{sf}}, K_{\mathrm{sf}})$,
   $(\rho_{\mathrm{lf}}, K_{\mathrm{lf}})$,
   $(\rho_{\cap}, K_{\cap})$
   from SU(2) representation theory.

4. **Explicit overlap measure bound** with SU(2) constants:
$$
\kappa_{SU(2)} \sim \tfrac{3}{4}, \qquad \beta(SU(2)) = 3,
$$
up to heat-kernel normalization conventions, giving
$$
\mu_k(\Omega_k^{\cap}) \le N_p(k) \cdot C_{SU(2)} \cdot \exp\!\left(-\frac{3}{4 g_k^2}\right) g_k^3.
$$
This is the place where the union bound's looseness must be checked.

5. **Block-spin pushforward as sheaf morphism** with dimensional
   rescaling encoded as a 2-cell
$$
\Theta_k : (T_b)_*(a_k^2 \sigma_k) \Rightarrow a_{k+1}^2 \sigma_{k+1}.
$$
Prove the 2-cell carries an explicit degradation term $\eta_k$ with
$\sum_{k=0}^{K} \eta_k < \widehat{\sigma}_0$ on the tested RG range.

### Success criterion

The finite pilot succeeds if, for a few RG steps, it verifies
explicit numerical constants satisfying:

1. Small-field KP condition.
2. Large-field KP condition.
3. Overlap KP condition.
4. Summable degradation of $K_{\cap}$.
5. Positive retained renormalized string tension: $\widehat{\sigma}_k > 0$.

This would not solve the Clay problem. It would be a serious
publishable SU(2) reduction and a concrete template for general
compact simple $G$.