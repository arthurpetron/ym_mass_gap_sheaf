# The sector-SOS certificate: X_11 > 0 on ALL of (0,1) (work_plan §17g)

Companion note to `computations/sector_sos.py`,
`computations/u1_conjugation_fence.py`,
`scripts/gen_sector_sos_lean.py` and
`dual_kappa_spike/SectorSOSLedger.lean`.  Executes queue item **P3**
(overlap closure / the atlas-adequacy lemma) — and supersedes the
mechanism P3 was expected to need.

## 1. What P3 asked for, and why it could not be met as posed

MD.4 asks for a finite Sturm-certified rational cover of the compact
middle regime `[2^{-1/3}, s_*]`, chaining the unconditional
strong-coupling anchor window `[0, 2^{-1/3})` to the validity edge
`s_*` of the MD.3 weak-coupling envelope.  The coverage audit is
blunt:

| regime | instrument | coverage in s |
|---|---|---|
| strong | located single-edge gap, unconditional | `[0, 0.793701)` |
| middle | (the atlas) | **was EMPTY** |
| weak | §17c majorant envelope, `tau <= 2^-44` | `[1 - 5.68e-14, 1)` |
| — | banked §16h–§17e one-step CERT grid | `s <= 5/8 = 0.625` |

The banked certified grid — every point bought in §§16h–16l and §17e
at exponentially rising cost — lies **entirely inside the
unconditional anchor**.  It contributes *zero* coverage to the
interval the atlas exists for.  §17.2's finding F1 called the
s-marching "off-geodesic by cost"; the sharper statement is that it
was off-geodesic by *domain*.

## 2. The structure that closes it

The M -> infinity owned-boundary slab kernel decomposes over
**transverse sectors** `sigma = (q, w)` — the perimeter-class and
interior-wall labels, which sit on theta-invariant faces
(`su2_cs_tail`, §16h):

    T[n,m](s) = sum_sigma W_sigma(s) G_sigma[n,m](s),
    W_sigma(s) = prod_i dim(q_i)^2 s^{2C(q_i)} * prod_i dim(w_i) s^{C(w_i)} > 0.

Three facts, in order.

**(F1) Each `G_sigma` is an EXACT finite polynomial.**  At fixed
sector the triad constraint `triad(n, q_i, a_i)` forces
`|n - q_i| <= a_i <= n + q_i`, so the tile sums TERMINATE.  There is
no truncation error inside a sector — ever.  This is what removes the
entire tail/unresolved-diagonal apparatus from the lower-bound
direction.  (Gate `g_exact`: kernels at tile cutoff M and M+1 are
identical; at cap<=2 the M=2 kernels differ on 144/187 sectors, so
the gate has teeth.)

**(F2) Each `G_sigma` is PSD** as a 2x2 matrix over `(n,m) in {0,1}^2`.
This is the banked §16h input — sector-wise Osterwalder–Seiler
link-reflection positivity of the half-config Gram
`H[(n,a),(m,b)] = N(n,m,sigma,a,b)` — together with
`G_sigma = V^T H V`, `V`'s columns the strictly positive tile weights.
(Gate `g_psd`: exact square-root-free LDL on `H`, all 16 sectors of
the certificate family; independently all 187 sectors of the cap<=2
family.  Teeth: every `H` is rank-deficient, so the zero-pivot branch
fires, and 71 of the 187 have a negative entry — PSD is not entrywise
positivity.)

**(F3) det is superadditive on PSD 2x2 matrices.**
`det(X+Y) = det X + det Y + tr(X adj Y)` exactly, and for PSD `X, Y`
both `det Y >= 0` and `tr(X adj Y) >= 0` (the adjugate of a PSD 2x2 is
PSD).  Hence for every finite sector family `S`

    det T_S(s)  <=  det T_full(s)     for all s in (0,1).      (*)

Equivalently, expanding (1) pairwise,

    det T_full = sum_sigma W_sigma^2 det G_sigma
               + sum_{sigma<sigma'} W_sigma W_sigma' Q(sigma,sigma'),
    Q(sigma,sigma') = A B' + B A' - 2 C C'  >=  0,

a sum of **non-negative** terms indexed by sector pairs — the depth-1
analogue of the §17e depth-2 Lagrange/Cauchy–Binet SOS, and the reason
the name "sector-SOS".  (Gate `g_pairs`: the expansion holds as an
exact rational identity and no `Q` is negative.)

## 3. The certificate

Family: the 16 sectors with all labels <= 1.  Their exact assembled
kernels are small integer polynomials:

    T00 = 1 + 16 s^18 + 16 s^30 + 32 s^36 + 16 s^42 + 4 s^48
    T01 = 2 s^12 + 8 s^24 + 8 s^30 + 24 s^32 + 14 s^36 + 24 s^44
          + 24 s^46 + 36 s^52 + 24 s^60 + 6 s^68
    T11 = 5 s^24 + 12 s^30 + 2 s^36 + 24 s^38 + 60 s^46 + 36 s^52
          + 24 s^54 + 6 s^56 + 48 s^60 + 36 s^62 + 42 s^68 + 36 s^78
          + 9 s^88

    det_S = T00 T11 - T01^2 = s^24 P(s),  deg P = 106,  P(0) = 1,
    16 of P's 46 terms NEGATIVE (so positivity is not coefficientwise).

**The Moebius step.**  `s = 1/(1+t)` is a bijection `(0,1) -> (0,inf)`.
With `R(t) = (1+t)^{106} P(1/(1+t))`:

    R(t) = t^4 * Rhat(t),   Rhat has 103 integer coefficients,
    ALL >= 0,   Rhat(0) = 15972864 > 0.

So `Rhat > 0` on `[0, inf)`, hence `P > 0` on `(0,1)`, hence by (*)

    **T00 T11 - T01^2 > 0, i.e. X_11(s) > 0, for the FULL
      M -> infinity kernel, on ALL of s in (0,1).**

Positivity has become a comparison of 103 integers against zero.  That
is a Descartes-rule certificate, not a Sturm count, and it is why the
statement transports to the Lean kernel as an **interval** theorem —
the program's first; every prior certified statement was pointwise.

Independent replication on a disjointly-built family: cap<=2, **187
sectors**, built with an independent exact spin-network evaluator
(gated bit-for-bit against the incumbent `dp3_fixed_tile` evaluator on
all 171 cap<=1 configurations, 320 character-orthogonality identities
and 130 random networks): `det_S2` has degree 376, 69/163 coefficients
negative, **0 roots in (0,1)** by both Sturm and the Descartes
certificate, `Rhat(0) = 230460431616`.

## 4. Consistency gates against the banked instrument

* `g_census`: the cap<=1 sector assembly reproduces the banked M=2
  census polynomial (`dp3_m2_entries`) **exactly** on the leading
  block of every entry (exps 0,18,30,36,42 for T00; 12,24,30,32,36,44
  for T01; 24,30,36,38,60 for T11) and is coefficientwise **dominated**
  by it everywhere else — the relation a positive sub-sum must satisfy.
* `g_grid`: at every §16l CERT point the truncated assembly's `det_S`
  is positive, and its `X_11` sits at or above the banked certified
  floor (at `s = 1/2`: 0.258391, equal to the banked floor to six
  decimals — the two routes meet).
* Non-vacuity: the dominant trivial sector is **exactly rank one**
  (`det G = 0` identically), and the diagonal part of the pair
  expansion is `7.1e-14` of `det_S` at `s = 1/2`.  The certificate is
  entirely cross-sector interference; it is not a single-sector
  artifact.

## 5. The U(1) mirror fence (§17.4), and where non-abelian-ness enters

The abelian kernel is `T[n,m] = D_n D_m Phi(n-m)` with
`Phi(k) = sum_c s^{a(c)} (s^{2S(c)})^k` a **Stieltjes moment
sequence** — so the observable's matrix is a **Toeplitz** form in
`Phi`.  Charge conjugation is `n -> nbar = -n`, so the OS Gram object
is `T[-n,m] = D_n D_m Phi(n+m)`: a **Hankel** form in the same `Phi`.
Hankel of a moment sequence is PSD; Toeplitz is not.  That one word is
the whole fence:

* per abelian orbit `{c,-c}`, `det G_sigma = s^{2a+8}(4 - (t+1/t)^2) < 0`
  whenever `S(c) != 0` (`t = s^{2S(c)}`) — a **proof**, not a numeric;
  270 of 313 orbits in `|c|_inf <= 2` carry a strictly negative exact
  determinant (witness `c=(1,0,0,0)` at `s=1/2`: `-225/16777216`);
* the *assembled* abelian 2x2 has certified negative determinant, so
  **no** sector decomposition whatsoever can be sector-wise PSD
  abelian-ly — the fence is decomposition-independent;
* the conjugated blocks are rank one (`M_c = x x^T`, `det = 0`) and
  their sum is PSD — the conjugated form PASSES;
* kernel-checked exponent form (`SectorSOSLedger`):
  `2 Qmin(n,m) - Qmin(n,n) - Qmin(m,m) = -2(n-m)^2` (unconjugated,
  wrong sign) versus
  `2 Qmin(-n,m) - Qmin(-n,n) - Qmin(-m,m) = +2(n-m)^2` (conjugated,
  right sign);
* closed form of the abelian observable, the exact mirror of the SU(2)
  statement with the opposite sign:
  `X_U1(s) = -2 log(Phi(1)/Phi(0)) < 0` for **every** `s in (0,1)`
  (reproducing the banked `X_U1(1/2) = -0.35636`).

**Where SU(2) enters.**  OS positivity delivers PSD of `[T[nbar,m]]`.
SU(2) is self-conjugate (`chi_jbar = chi_j`), so `nbar = n` and the
OS-PSD object and the `X_11` object are *literally the same matrix*,
sector by sector.  For U(1) they are two different matrices with
opposite determinant signs.  That identification, and nothing else
about the group at this step, licenses (F2).

**Two flags.**  (i) Self-conjugacy is used *twice*: once for the
boundary charge (above) and once for sector-preservation — the
reflection must map each transverse sector to itself, not merely
permute sectors (abelian-ly it sends `c -> -c`, which is why the
abelian analysis needs `±c` orbits).  For SU(2) both follow from
self-conjugacy of the transverse irreps, and the machine gate
`g_psd` checks the resulting sector blocks directly on 16 + 187
sectors.  (ii) Self-conjugacy is an SU(2)/A_1 fact, not a general
compact-simple-G fact; the all-group statement therefore rides the R1
worst-case spine (invariant P6), and this is recorded as inherited
debt, not discharged here.

## 6. Lean transport

`dual_kappa_spike/SectorSOSLedger.lean` (generated, eighth spike
target).  In-kernel: the sector weights and exponents **rederived**
from the labelling; the assembly **rederived** coefficient by
coefficient against declared integer polynomials with an
exponent-completeness guard; `det_S` formed; the Moebius transform by
Horner in `u = 1+t`; then

    theorem sector_sos_certified : rHat.all (fun c => decide (0 <= c)) = true

by `decide` — plus `r_low_order` (order exactly 4 at `t=0`, leading
15972864), `p_has_negative_coefficients` (=16, non-vacuity),
`det_bottom`, `sector_blocks_psd_on_grid`,
`trivial_sector_rank_one`, and the three U(1) fence theorems.

Verification (cloud, Lean 4.29.1, `LEAN_NUM_THREADS=1 -M 8192`): build
**exit code 0**, no errors, no warnings.  `#print axioms`: ten of the
eleven theorems depend on **no axioms at all**; `r_low_order` depends
on `[propext]` only — inside the `{propext, Quot.sound}` budget.
**Mutation-tested**: changing a single transcribed Haar value
`(34, 9/16) -> (34, 10/16)` makes `t_rederived` fail (`decide` proves
the proposition false), so the ledger is not vacuous.
`tests/test_sector_sos.py` 13/13 (47 s).  **Mac-side lake run is NOT
claimed** — no Lean was run on the host this session.

## 7. What is closed, what is open

**Closed (modulo the banked (F2) OS input, which is the same input
§16h–§17e already consume — not a new frontier atom).**  The
anti-screening SIGN of the one-step blocked observable, uniformly on
`(0,1)`.  The sign half of MD.4 atlas-adequacy: the middle regime is
covered, by one polynomial rather than a cover, and the atlas
requirement collapses from "finitely many expensive windows meeting
`s_*`" to "one coefficient-sign check".  De-prioritised as a
consequence: further one-step s-marching, the recoupling evaluator as
a *sign* consumer, and the (0,3)/(3,3)-class diagonal lane as a *sign*
consumer.

**Open, and sharpened.**  The RATE.  `det_S` yields a quantitative
floor only after an upper bound on `T01` (one entry — the cheap
direction of the window instrument), and near `s = 1` the floor it
gives is `O(tau^4)`, not the true `O(tau^2)`.  **Banked refutation:**
enlarging the transverse family cannot fix this.  The cap<=2 family
(187 sectors) has the *same* order-4 vanishing at `s = 1`, because
every sector shares the `s -> 1` collapse of `T` onto the rank-one
dimension kernel `That[n,m] = d_n d_m s^{12(n+m)} T00`, with the two
exact coincidences `T00(1) x_2 = u_1^2` and
`T00(1) x_3 + T00'(1) x_2 = 2 u_1 u_2`
(`u = T01 - 2T00`, `x = T11 - 4T01 + 4T00`) holding in *both*
families.  The order-4 degeneracy is **protected**, not a
small-family artifact.

**The named next front.**  Work with the deviation kernel
`delta = T - That` directly — specifically `delta11 - 4 s^12 delta01`,
whose order-3 coefficient is the first quantity the protection
mechanism does *not* fix — rather than with `det T`.  That is where
the MD.3 two-sided envelope `1 < tau'/tau <= 1 + c tau` and the P3
overlap closure now live.

**§17g addendum (same session): the next front OPENED and its first
guess REFUTED.**  The deviation kernel `delta = T - That`,
`That[n,m] = d_n d_m s^{12(n+m)} T00`, was named above as the way past
the protected order-4 degeneracy.  Computed exactly in both families:

* `delta01 = T01 - 2 s^12 T00` and `delta11 = T11 - 4 s^24 T00` each
  vanish to order EXACTLY 2 at `s = 1`, with `delta11 = 4 * delta01` at
  leading order EXACTLY — cap<=1: 16896 = 4 * 4224; cap<=2:
  2899680 = 4 * 724920.  The protection relation is confirmed
  independently of `det`.
* The proposed escape combination `delta11 - 4 s^12 delta01
  = T11 - 4 s^12 T01 + 4 s^24 T00` vanishes to order **4**, not 3 —
  leading coefficient 397824 (cap<=1) and 181063296 (cap<=2), both
  positive.  **The "order-3 coefficient" guess is REFUTED**: the
  order-4 vanishing is a property of the OBSERVABLE CLASS, not of the
  transverse family, and subtracting the rank-one dimension kernel does
  not break it.
* What DOES respond to the family is the SIZE, not the order: every
  leading coefficient grows by 2-4 orders from cap<=1 to cap<=2
  (4224 -> 724920; 397824 -> 181063296; det's 15972864 ->
  230460431616).  So family enlargement buys magnitude, never order.

Consequence for the ranking: the rate must come from the RELATIVE
quantity `X_11 / tau^2`, i.e. from pairing `det_S` with a uniform UPPER
bound on `T01` alone (the cheap direction of the window instrument),
not from any further algebraic recombination of the same entries.  That
is now the single next item.
