# Original filtered source compared with its own interacting variance

The complete signed radius-two source now meets its OWN finite interacting
variance through the original mixed edge, with one fixed original odd mean.
The finite boundary error and whole-word quartic correction are paid at the
same computed depth onset. Three favorable corrections remain in the bound.
This removes the mixed-variance identification seam; it does not produce a
useful relative budget or a continuum survival witness.

## Exact identity and original center

Let W be the ORIGINAL mixedDensity(n,1,n+1), E its evenPartition, f the
actual upper fundamental trace, r the actual whole-word chordal square,
and c the existing original odd-window mean at depth n. Put

    R = H[W*r*(4-f^2)], Q = H[W*r^2], L = H[W*r],
    Vmid = H[W*(c-f)^2], U = H[W*r*(c-f)^2],
    Y = H[W*(t*(c-f)-c*r)^2].

`weighted_young_moments_identity`,
`lean/YMGap/Continuum/QuaternionHaarRadialMeanYoung.lean:244`, proves

    t*(R+Q) + t*U + Y = t^2*Vmid + (t+c^2)*Q + t*(4-c^2)*L.

This equality holds with literally the same W and arbitrary rational c,t;
it needs no positivity, stationarity or independence premise. It retains
both squares that the existing Young inequality could otherwise discard.

`mixed_own_young_identity`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFilteredOwnYoung.lean:273`,
instantiates it with the actual mixed weight and `ownMean`. This is the
existing `WilsonMeanRadial.mean`, not a new mean selected in the mixed law.
The actual drift D remains the existing driftSquare, and the literal
source S remains the original numerator of filteredExpression.

## Finite comparison to the original variance

`upperCenteredSquare_interval`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFilteredOwnYoung.lean:127`,
constructs an Interval of cap 16 on the CENTERED SQUARE. The cap is not
16 on the unsquared trace. The upper word has square cap 4, and the
SAME original odd mean has square at most 4.

Padded original-Haar coefficient transport and the exact matched upper/lower
marginal identify the matched window(n,1,n) with OWN oddVariance. The
existing arbitrary-polynomial window comparison then compares it to
window(n,1,n+1), keeping the same center throughout. Clearing only that
mixed window's positive partition gives

    Vmid <= [OWNVar + 32*mixRate(w,width)^n]*E.

This is `mixedCenteredMoment_le_ownVariance`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFilteredOwnYoung.lean:237`.
The coefficient 32 is independent of path length, cutoff and terminal
depth; mixRate depends on nome and width. This theorem neither equates
finite odd/even partitions nor replaces an inserted endpoint marginal.

## Complete source with corrections retained

For t>=0, `filtered_loop_own_young_bound`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFilteredOwnYoung.lean:318`,
combines S<=2R+2Q-2D with the exact identity and finite variance comparison:

    t*S + 2*t*U + 2*Y + 2*t*D
      <= 2*t^2*[OWNVar+32*mixRate^n]*E
           + 2*(t+c^2)*Q + 2*t*(4-c^2)*L.

The ORIGINAL action, source, center and mixed even partition remain.
No analytic cancellation is assigned a useful sign or size by assumption.

`filtered_loop_own_young_paid`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFilteredOwnYoung.lean:342`,
uses the already constructed complete-word quartic producer. With
b=16*length^4*(40*24576^2*(1-w)^2+2*epsilon), it gives

    t*S + 2*t*U + 2*Y + 2*t*D
      <= 2*{E*[t^2*(OWNVar+epsilon)+(t+c^2)*b]
               + t*(4-c^2)*L}.

The exact guards remain: 16/17<=w<1, epsilon>0, headCutoff(w)<=K,
quarticCutoff(w,epsilon)<=K, actual active links, and
mixedQuarticDepthCutoff(w,width,epsilon)<=n. This SAME depth onset pays
both the quartic boundary error and variance error. It is computed but
not uniform in width/nome along a changing physical family.

NEXT: pay the actual mixed chord moment without applying a same-source
quadratic order bound to different terminal sources; then estimate the
COMPLETE retained cost relative to OWN variance and lag-one reserve on
a justified changing family. The backward consumer remains
`BF4WilsonAllNomeDyadicFilteredGeometricSurvival.dyadicUnitResponse_filtered_block_floor`,
`lean/YMGap/Continuum/BF4WilsonAllNomeDyadicFilteredGeometricSurvival.lean:154`.
Its family-wide finite C and positive reserve are not produced here.

## Verification and open boundary

The FIRST focused exact-moment check and THIRD focused concrete check
exited zero, with 9 and 11 printed gates. The first includes eight existing
Young gates and one new gate. Every accepted dependency is within
{propext,Quot.sound}, or empty; the accepted logs have no errors, warnings
or sorryAx. Independent mathematical source, accepted-log and hash review
passed. Preliminary
concrete errors were a missing namespace open and unresolved rational
placeholders; no statement or guard was weakened.

| Artifact | SHA256 |
| --- | --- |
| `QuaternionHaarRadialMeanYoung.lean` | `d549dc25e9f2dd081ae3847304d0b13e356667b059b5b0b8da0c69c09c8ebc6c` |
| `/tmp/ym-radial-young-exact-20261002-first.log` | `c02ba6b72b753e9ab5778a09a9fed4e91061dd3d786501d77312a496bf1176a1` |
| `BF4ExactSlabFixedSpatialFilteredOwnYoung.lean` | `e0e2bfae3a99f468734125332921b56b9e64a6b363267fe15736a2468ad67b0a` |
| `/tmp/ym-filtered-own-young-20261002-third.log` | `8506dfec3e315c2d5b4b4bb80c0330fc9d817d92e23651b10fb9e5bdc107a724` |

All launches used a fresh memory preflight, one worker, a 20-GiB ceiling
and 12-GiB OS reserve; preflights showed 85 percent pressure-free memory
and zero swap. The root import is registered, NOT aggregate-checked.
Root/tree, broad audit/guard and progress metric were NOT run. No new sorry,
axiom, classical shortcut, weakened field, substituted source or CI change.
The documentation skill kept the finite variance join distinct from the
missing useful changing-family estimate. The exact canonical chart is
unchanged, so there is no ASCII reprint. Spatial/spacing control, continuum
survival, physical mass calibration, full SAME QFT, every compact simple
group and the Clay target remain OPEN.
