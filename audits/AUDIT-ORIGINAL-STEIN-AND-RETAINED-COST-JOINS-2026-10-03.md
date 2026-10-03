# Original Stein limit and retained macro-to-cost join

The unchanged goal is nontrivial continuum Yang--Mills on R^4 for every
compact simple group, with full SAME-theory QFT structure and a positive
physical Hamiltonian mass gap. It remains OPEN. This increment connects
the forward original source to its completed signed gain, and connects two
alternative backward analytic inputs. Neither useful analytic input is
assumed to have been produced.

## Forward: the actual moving mean is paid

At fixed 0<w<1, width and source loop, let E be the original positive even
partition and c the actual OWN odd-law mean at K=headCutoff(w)+stage and
terminal depth n. The existing full-source identity retains the complete
original action and gives

    G/E = fullSourceDefectPair/E + residue/E,
    |residue/E| <= 8*(1-a)*mixRate(w,width)^n,  0<=a<=1.

The new approximation pays the residue and existing finite-gain error with
epsilon/2 each, in both orders. Its computed diagonal stage is the maximum
of the existing gain cutoff/time thresholds and mean-residue depth cutoff,
all at epsilon/2. The gain CReal representative threshold remains separate.
The resulting sequence converges to the EXISTING gainLimit, not a newly
selected real or replacement carrier. Moduli depend on w, width and loop;
they are not spatial/spacing-uniform.

For the literal padded square, the original Stein identity has exactly the
same residue. Cancelling it identifies the normalized full source with the
literal signed Green-gradient sum, at a=w^(12*side). Its fundamental kinetic
label requires K>=1, retained explicitly and paid by the diagonal max with
one. The sum consequently converges to the existing centered C2-a*C1;
the existing completed pin uses the SAME original state, inner product and
time map. No odd/even partition equality, interacting eigenpin, favorable
source sign, survival reserve or new limit object is used.

## Backward: retained response pays later relative cost

For every state of the existing original completion, write C(k)=B(x,T(k)x).
Positive mixed moments give the retained telescoping estimate

    s*(C(L+s)-C(L+s+1)) <= C(L)-C(L+s),  s>=1.

Multiplying by a supplied kappa>=0 and using the SAME-state hypothesis
kappa*C(L)<=C(L+s) gives

    kappa*s*(C(L+s)-C(L+s+1)) <= (1-kappa)*C(L+s).

This is a conditional implication, not a ratio producer. A useful retained
fraction requires kappa>0; kappa=0 yields only the degenerate bound. No real
division or denominator floor is needed to prove the cleared statement.
The existing dyadic unit response specialization has L=s=2t, hence its drop
is at lag 4t. It matches the original block-cost limit at block parameter
2t, NOT t. No physical-time convention or finite estimate obtained by
reversing convergence is asserted.

## Remaining mathematical input

The unpaid producer remains the COMBINED original energy and signed
multiplication cost against the half-smoothed interacting square, with the
actual mean and BOTH partitions retained, on a JUSTIFIED changing family:
s*D<=C*Z1*ell(b^2), or the SAME retained macroscopic-response-ratio
alternative. The new source limit pays centering, not useful signed alignment.
The new conditional join lets a useful ratio pay later completed relative
cost, but supplies neither that ratio nor the changing family. Separate
absolute term bounds can discard the cancellation present in the exact
original split; no such substitution is made here. Growing-loop/spatial/
spacing control, continuum survival, calibration, full QFT structure and
every compact simple group remain OPEN.

## Declaration anchors

Source prefix: `lean/YMGap/Continuum/`.

- `BF4WilsonAllNomeDyadicSteinGainLimit.lean:59`, `normalizedSourcePair`;
  :68, `sourcePairDiagonalModulus`; :126, `normalizedSourcePair_approx`;
  :167, `source_pair_diagonal_converges`; :185, `normalizedSteinGradient`;
  :195, `paddedSquare_sourcePair_stein_pin`;
  :222, `paddedSquare_stein_diagonal_converges`;
  :248, `paddedSquare_stein_centered_converges`;
  :261, `paddedSquare_stein_completed_pin`.
- `BF4WilsonAllNomeMacroRatioFilteredCost.lean:100`, `retained_time_budget`;
  :123, `macro_to_filtered_budget`; :139, `dyadicUnit_macro_filtered_budget`.
- Existing gain approximation: `BF4WilsonAllNomeFilteredFiniteGainLimit.lean:111`,
  `normalizedFiniteGain_approx`; completed gain:
  `BF4WilsonAllNomeFilteredGainLimit.lean:131`, `gainLimit_completed_pin`.
- Existing original split: `BF4ExactSlabFixedSpatialBlockRayleighSplit.lean:234`,
  `original_block_rayleigh_split`; original cost limit:
  `BF4WilsonAllNomeDyadicOriginalRayleighLimit.lean:157`,
  `originalOwnBlockCost_converges`.

## Verification evidence

Two final serialized focused checks exited zero. All 12 printed gates
(9+3) depend only on {propext, Quot.sound}. Accepted logs contain no
errors, warnings, sorryAx or PANIC. Development logs a are excluded.
Macro elaboration was corrected by an explicit beta-reduced target and
RHS-specific distribution rewrite; Stein elaboration by unfolding its local
reference and giving explicit loop expressions. Statements and limits were
not weakened; proof/resource limits were not raised.

Every launch used fresh memory/process/swap checks and the monitored safe
launcher: one worker, 12GiB reserve, 20GiB worker ceiling. Accepted preflights
showed 83--84% free memory, zero swap and no competing proof process.

| Source basename | Accepted log under /tmp | Gates | Source SHA-256 | Log SHA-256 |
| --- | --- | ---: | --- | --- |
| `BF4WilsonAllNomeDyadicSteinGainLimit.lean` | `ym-original-stein-gain-limit-20261003-b.log` | 9 | `59004e0f541e53f2582e63f4628b163fa080fe826e90ee15f2eab361ea4e8bd1` | `9307745ad0c6032d9aa4839dfbe2aeec3793979bfb7d01ffcc26cb4aa618fe9b` |
| `BF4WilsonAllNomeMacroRatioFilteredCost.lean` | `ym-macro-ratio-filtered-cost-20261003-b.log` | 3 | `49d1f02a8a5b6134862d53b8730dd7836055c37780623ffa8e0000718033ecec` | `30c909cd177cfd494d20c624e1a2ba8b0aeb3a3972f04afe2a1c1ed7da5c5290` |

Independent Sol source/math review passed the actual centering, shared
partition, half-epsilon/depth/representative guards and completed Stein pin.
Root separately reviewed both full sources. Source reviews are not kernel
checks. Root imports are registration-only; aggregate root, full-tree build,
broad audit/guard and progress metric were NOT run. Only new proof modules
and root import registrations changed among Lean sources; no sorry, axiom,
classical shortcut or resource option was added. CI remains manual-only.
The canonical first chart fence remains unchanged, SHA-256
`0d9295165945a8acea2c4037bd951f9060a1dfcc22448bde4462d0c795b12145`.
No exact displayed scaling claim closed, so no ASCII chart is reprinted.

Independent Luna evidence/documentation QA passed the four source/log hashes,
12 gates, declaration anchors, unique imports, conditional-versus-produced
status boundary, dyadic lag convention, unchanged chart fence and manual CI.
