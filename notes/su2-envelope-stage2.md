# The envelope lemma, stage two: sharpened constants from the exact complex (work_plan §17b)

Companion note to `computations/su2_envelope2.py` (theorems + gates) and the
§17b work_plan entry.  Stage one is `computations/su2_envelope.py` (§17a),
which this stage both REPAIRS and supersedes numerically.

## The statement (unchanged shape, sharpened constants)

For all 0 < tau <= tau* = 2^-55, with K_X ~ 3.799e33 an explicit rational:

    | X_11(tau) - 6 tau^2 - (115/6) tau^3 |  <=  K_X tau^4,

hence X_11 > 0 on (0, tau*] (margin K_X tau*^2 <= 3 < 6) and the two-sided
envelope X_11 in 6 tau^2 (1 +- rho), rho = (115/36) tau + (K_X/6) tau^2.
Stage one (as released) claimed tau* = 2^-82 with an unsound constant (see
Repair); the repaired stage-one pipeline gives tau* = 2^-76, and this stage
gives 2^-55: a 2^27 certified-domain gain over the original release with
soundness restored.

## The repair

Stage one's smallness condition r0 <= 1/(4 g3 CM^2) took g3 = 64 as a global
cubic majorant for the action remainder on the Cauchy circle.  The cubic of
phi_f^2 - theta_f^2 is 2 theta_f . Delta_2,f per face, and the per-face crude
majorants SUM over 20 faces to more than 64 |x|max^3 — the constant
under-counted the face sum.  The exact accounting rescues and improves it:

* **Vanishing lemma.**  theta . Delta_2 is a sum of scalar triple products
  x_k . (x_i x x_j) over word positions.  Any face word with <= 2 distinct
  links puts a repeated vector in every triple product: the cubic VANISHES
  IDENTICALLY.  That is 16 of the 20 faces (13 two-letter + 3 one-letter).
* The four surviving faces (three 4-letter, one 3-letter, all with distinct
  links) carry at most G3_TOT = 39/2 triple-product terms
  (6 per 4-letter face, 3/2 for the 3-letter face).
* Quartic-and-higher (ALL orders) close under the positive-coefficient
  Dynkin majorant with Q(sigma) <= QHAT sigma^4, QHAT = 5/2 certified on
  sigma <= 1/50 (note: q_hat(1/8) ~ 2.74 > 5/2 — the domain assert in
  r0_choice is load-bearing; the actual circle cap is 4 r0 = 2/195).
* Budget split 1/4 = 1/5 + 1/20 gives r0 = 1/390 > 1/1024: the repair
  SHARPENS stage one (K_X 3.8e49 -> 1.663e46, tau* 2^-82 -> 2^-76).

Machine gates: `gate_repair` (literals vs the exact complex),
`gate_cubic` (the vanishing lemma + triple-sum bound on exact rational
vectors; Delta_2 formula independently checked against mpmath matrix logs).

## Stage-two sharpenings

With eta = sqrt(8 tau), x = eta M xi, on the circle |eta'| = r0/(CM |xi|)
every link field obeys ||x'_e|| <= (c_e/CM) r0 <= r0 UNIFORMLY in xi
(c_e^2 >= (G^-1)_ee certified by isqrt; max = 367/96 < 4).

1. **Exact per-face insertion budget.**  |Delta S_f| <= 2|theta.Delta_2|
   + Q(sigma_f) with sigma_f <= (r0/CM) s_f |xi| ... the total budget on
   the circle is

       (r0/CM) T3 |xi|^2 + qhat (r0/CM)^2 S4 |xi|^2 / 2  <=  kappa |xi|^2,

   with the exact complex constants T3 = 50.851 (only 4 faces), S4 = 4524.5,
   s_max = 6.117.  The all-orders closure needs no G4.
2. **kappa optimized.**  E[|xi|^8 e^{kappa|xi|^2}] =
   (1-2 kappa)^{-(d/2+4)} 48*50*52*54; minimizing r0^-8 (1-2k)^-28 over a
   dyadic grid lands kappa = 1/9 (stage one: 1/4, cost 2^28).
   Result: r0 = 3853/2^20 ~ 3.675e-3.
3. **A0 uniform.**  Characters (n, m <= 1): 4 e^{(||theta_t||+||theta_b||)/2}
   with ||theta|| <= (r0/CM) c_link — xi-INDEPENDENT.  Face Jacobians
   |z/sin z| and link Haar |sin z / z|^2 at |z| <= 2 s0, s0 = (r0/CM) s_max:
   certified series bounds give A0 = 4.0198 (stage one: 4 * 2^20).

Shells (large field, images, log composition, exp_le_power) are imported
from stage one unchanged; K_X = 8 (K_small + 1).

## The U(1) mirror lane (§17.4 fence executed)

Identical machinery, one abelian component (c_su2_assembly g4 convention:
covariance 8 tau G^-1, characters e^{i m theta}).  Abelian => Delta S == 0,
no Jacobians: the main branch is entire, kappa = 0, and the lane's constants
are tiny: K_U1 ~ 7.67e6 with

    | X_U1(tau) + 8 tau |  <=  K_U1 tau^4        on (0, tau*],

the linear term being -8 (G^-1)_{t,b} tau, (G^-1)_{t,b} = 1 exact, and
kappa_2 = kappa_3 = 0 the banked §16f g4 / §16g mirror gates.  Consequence,
certified two-sidedly on the COMMON interval:

    X_SU2(tau)  >  0  >  X_U1(tau)       for all tau in (0, 2^-55]

— anti-screening vs screening, nonperturbative on the interval, the model of
admissible evidence demanded by the §17.4 mirror fence.  Scheme covariance
of the mirror sign: the second banked U(1) instrument (theta kernel,
Qmin = 3n^2 + 3m^2 + 2nm) gives X_lin = -2 tau, and the engine/theta
conversion is EXACTLY 4 on both diagonal (12 vs 3) and cross (8 vs 2)
(`gate_mirror`) — the screening sign is convention-invariant.

## Verification

Cloud container.  `python -m computations.su2_envelope2`: all six gates
PASSED; ledger `su2_envelope2_results.json` (exact rationals).  Stage-one
module re-run regenerates its ledger with the repaired values.  Tests:
`tests/test_envelope2.py` (5 pins incl. the q_hat domain trap) +
`tests/test_envelope.py` (4, unchanged) green; MD-era subset 182 passed /
4 skipped (rust engine unbuilt in this container).  Full-tree pytest:
756 passed / 20 failed / 4 skipped — the 20 are PRE-EXISTING stale pins in
Phase 1–4-era files (test_chaining_eta*, test_continuum_limit,
test_long_k_trajectory, test_mass_gap_bound, test_q_lift), none of which
import anything touched here; recorded, not repaired (they pin superseded
constants from the May c_lambda change and the old K-trajectory pilot).
`pyproject.toml`: the `slow` marker is now registered (collection under
--strict-markers previously errored on test_dp3_m2.py in a bare container).

## Honesty

One-step, thickness-one slab; discriminator form.  The matched-flow
envelope 1 < tau'/tau <= 1 + c tau still awaits the diagonal kappa_3 or the
P2 iterated-map consumer.  tau* = 2^-55 remains far below the atlas range;
the dominant structural loss is the GLOBAL Cauchy circle (radius ~ 1/|xi|).
Ranked next levers: (i) polydisc Cauchy in per-face variables (removes the
global |xi| shrink); (ii) the tau^4 cross law (remainder -> tau^5, rho's
linear term sharp); (iii) D4-class tightening of T3.  Mac session-lock run
unaffected (no Lean in this stage); push owed.
