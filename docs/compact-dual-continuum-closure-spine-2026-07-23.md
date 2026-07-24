# Compact-dual spacing-uniform gap closure spine

## Outcome

The compact-dual program is on a logically complete route to spacing-uniform
continuum gap survival, but it has not yet crossed the first analytic gate.
The exact sign work establishes that the dual coordinate remains viable.  It
does not establish the physical block map or any uniform estimate.

`computations/compact_dual_continuum_route.py` now makes the whole dependency
chain executable and fail-closed.  Its current-route constructor contains the
pinned finite sign evidence and no analytic witness, so its first open gate is
exactly:

```text
CD-2 physical block and overlap remainder
```

No census count, nonnegative finite Gram, or local sign law can change that
answer.  A gate closes only when its physical witness data are present and
compose with all earlier gates.

## Dependency-complete route

| Gate | Required constructive output | What cannot substitute for it |
|---|---|---|
| CD-2 | Source-indexed positive row-normalized kernel on the actual fine/coarse physical labellings; exact pushforward; complete reflected channels; computed overlap remainder with zero total mass; reflection intertwining | A positive scalar channel, a detached stochastic matrix, or entrywise fixed-channel positivity |
| CD-3 | Norm of that exact CD-2 remainder; `c(1-w)^2`-type cap; cutoff-independent constant; volume-uniform bound; explicit representation-tail modulus | Any norm of a surrogate remainder or a constant growing with cutoff/volume |
| CD-4 / RG-I7 | A pinned self-mapping physical coefficient ball; reflection-cone preservation; either `q<1` or an explicit accumulated contraction envelope | Positivity, compactness, or an unquantified stable-manifold statement |
| CD-5 / RG-I8 | Computed scale and computed physical state entering exactly the CD-4 enclosure | Eventuality, subsequence compactness, or entry of an unpinned trajectory |
| RG-I9 | Separate summable block-remainder, dynamic, and interface ledgers with exact tail moduli and a physical comparison theorem | Per-scale convergence without a summable modulus |
| Continuum survival | Physical Wilson/gap readout; volume-uniform modulus; spacing conversion; OS binding; a strict exact floor after every certified loss | A fixed-spacing gap or a limit statement with no quantitative positive margin |

The final acceptance inequality is explicit.  If `m_latt` is the pinned
fixed-spacing gap, the route returns a continuum certificate only when

\[
  m_{\rm latt}
  - E_{\rm block}
  - E_{\rm dyn}
  - E_{\rm int}
  - E_{\rm vol}
  - E_{\rm spacing}
  > 0,
\]

where every `E` is computed from a constructive geometric tail modulus at its
certified start scale.  Equality to zero fails the gate.

## Exact current position

The finite evidence object records:

- 100 complete four-cube binary-pair orbits;
- 65 complete six-valent pair orbits;
- 14 exact first-branching nonzero-defect channel orbits;
- nonnegativity of every tested complete sum;
- the combined cycle/branch local sign law.

Its `analytic_gates_discharged` value is definitionally zero.  This is the
program-distance firewall in executable form.

The current missing CD-2 fields are the same ones isolated by the exact
manifest audit:

1. pin the wheel/rim geometry to
   `CompactDualPhysicalData.faceEdges` and `enumeratedLinks`;
2. prove the exact-Haar integrator equals the corresponding finite fiber sum
   of `CompactDualPhysicalData.physicalTerm`;
3. pin `s` to the physical rational coupling and its `4*C₂` exponent;
4. map every reflected boundary channel, not just the positive rim channel;
5. construct the physical source-dependent kernel;
6. compute and retain the overlap remainder.

Only after these six items may `SpinFoamRPBlockRemainder` be inhabited.  The
next work step is therefore the physical geometry/integrator semantic bridge,
not a larger sign census.

## What this advances

This gate does not prove a new analytic estimate.  It closes a serious
program-control ambiguity: all remaining work now has a typed quantitative
consumer, and the present exact evidence is unable by construction to
overstate its distance to the continuum theorem.  It also fixes the order of
attack.  CD-3 cannot be explored honestly until CD-2 returns the actual
remainder; RG-I7 cannot be claimed until that same norm is used; and the
continuum floor cannot be returned unless every infinite error ledger is
strictly paid from the physical gap anchor.
