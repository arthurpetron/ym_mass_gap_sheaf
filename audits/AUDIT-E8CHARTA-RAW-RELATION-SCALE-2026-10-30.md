# Audit: E8ChartA monolith raw-relation scale fix (2026-10-30)

`lean/YMGap/Continuum/HarmonicLowerSixTailEnvelopeCertificateE8ChartA.lean`
stated `tailEnvelopeE8ChartA_raw_relation` with clearing factor `64 ^ u`.
That statement is false: the authoritative chart base is
`tailEnvelopeModeChartBase = 14`, as used by every sliced certificate
(`...E8ChartASlice{0..11}.tailEnvelopeE8ChartA_raw_slice*`, `14 ^ (start + localRow)`)
and by `...E8ChartACoefficientCertificate.tailEnvelopeE8ChartA_raw_at` (`14 ^ i`).
The `rfl` failure at line 60 was therefore a genuine counterexample, not a
reduction-depth / heartbeat / memory problem. Upstream definitions are unchanged
since 69fd174a (2026-07-17); the module is an orphan (imported by nothing,
superseded by the sliced CoefficientCertificate) and had no olean in any
checkout, i.e. it never built.

Fix: `64 ^ u` -> `14 ^ u` (and the docstring `x=64/n` -> `x=14/n`). Proof
unchanged (`rfl`, kernel-checked). No downstream statement depends on this
module, so no load-bearing claim changes.

Checked with `scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 8 --check`
(LEAN_NUM_THREADS=2, nice 10): elaborates in ~3 min under the 8 GiB cap.
`#print axioms`: raw_relation [propext]; xPascal/yPascal/bernstein_nonnegative/
shift [propext]; scale_relation none; transform_at, bernstein_nonnegative_at
[propext, Quot.sound]. No sorry/native_decide/Classical.
