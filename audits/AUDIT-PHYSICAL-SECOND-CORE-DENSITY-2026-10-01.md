# Explicit density for the original physical second derivative core

Date: 2026-10-01 UTC. PROGRESS after `61773ff`: every supplied complex
physical Rows witness now constructs second-core input approximants with an
explicit all-tail modulus. Their adjoining second-domain witnesses are the
original objects already constructed by `BF4WilsonAllNomeComplexBondOSSecondCore`.
Coupling and spatial width remain fixed. This does not construct continuous
unitary time or supply the primary complete signed-error scaling estimate.

## Constructed approximants

All new declarations are in
`lean/YMGap/Continuum/BF4WilsonAllNomeComplexBondOSSecondCoreDensity.lean`.
For a supplied real physical state x and positive rational tolerance e,
`baseSource` (:51) samples the ORIGINAL range witness at its own modulus
for e/4. `correctionDepth` (:56) reads that sampled Cauchy representative's
rational norm ceiling through `representedTailModulus`; it is not a source-
uniform cutoff. `approximationSource` (:59) returns the actual finite inverse-
sum Cauchy representative, and `approximationSource_pin` (:63) identifies it
with the existing completed inverse sum.

Write X for the sampled preimage and Y for that inverse sum. The original
range witness gives dist(T X,x)<=e/4. The checked inverse-sum error identity
and computed tail modulus give dist(T X,T^2 Y)<=e/4. The ACTUAL squared-
distance triangle doubles both terms, giving dist(T^2 Y,x)<=e. This is
`approximationSource_bound` (:71). No representative of a bare quotient
value is selected and no injectivity of T on the ambient completion is used.

`pairSources` (:106) applies this construction to BOTH components of the
supplied physical Rows object at half*invSucc(n). `pairSources_bound` (:120)
uses the original physical distance/value pin and the actual second-core
first-input pin. Its bound is the sum of the two component squared distances:

    distance(input(SecondCore.first(pairSources(X,n))),ofRows(X)) <= invSucc(n).

`densityCertificate` (:149) returns Type-level data: the actual domain-point
sequence, the rational-tolerance modulus e.den, and the all-tail bound. The
existing inverse-successor denominator inequality proves that e.den<=n
implies the displayed physical squared distance is at most e. Every point
has the adjoining `SecondCore.second(pairSources(X,n))` witness; its input
equals the first point's output by the EXISTING checked join.

## Scope and causal consumer

This removes the assembled density obligation for these second-core INPUTS
on supplied physical Rows. It is not a theorem that T^2 has dense range in
the ambient completion, and it does not assert arbitrary-domain invariance.
Each source ceiling and finite inverse-sum depth depends on the sampled
original witness. The second-output norm ceiling can grow with n; no
uniform second-derivative bound on the approximating sequence is proved.

The next operator consumer is a scaled imaginary-shift/Cayley construction
and a local consistency estimate on fixed second-core points, followed by
a product-Cauchy modulus. Those maps and estimates remain OPEN. The existing
plus/minus convention also requires its factor-two phase calibration.

PRIMARY remains useful complete signed error versus SAME interacting variance
on a justified coupling/spatial/spacing family. Nontrivial continuum survival,
physical time and positive physical mass, full same-theory continuum OS/QFT,
Yang--Mills field/UV identification, every compact simple group and the Clay
target remain OPEN. No canonical frontier field or displayed chart claim
changes, so the unchanged ASCII chart was not reprinted.

## Focused verification and review

The resumed existing session 50299 returned terminal exit zero; its final
log contains all EIGHT gates, exactly {propext,Quot.sound}. Independent Sol
mathematical review and Luna source/log/hash review passed. No sorry, new
axiom, Classical dependency, native_decide, noncomputable declaration,
analytic premise or weakened frontier was introduced.

Only main compiled through the safe-build skill and monitored launcher:
one worker, 20 GiB ceiling, unchanged 12 GiB OS reserve and dynamic telemetry.
No raised limit, full-root/tree build, broad audit, guard, progress-metric
script or CI change. Root imports are registered only, not aggregate-checked.
The documentation skill preserves the represented-density and open-scaling
boundaries; saved repository Markdown is not an external Page publication.

Accepted log: `/tmp/ym-complex-bond-second-density-first-20261001.log`.
SHA-256: `3bc069a2681e19c52a87818f3e4b1830090f2352e461471208999febee38d363`.
