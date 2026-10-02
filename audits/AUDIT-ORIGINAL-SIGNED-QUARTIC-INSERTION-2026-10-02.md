# Signed quartic insertion with the original terminal source

The actual centered Wilson-square quartic insertion now has a two-sided
bound against its SAME original odd partition, without the raw Haar source
norm cost of the universal signed Schur estimate. The complete filtered
slope and its ratio to OWN interacting variance remain OPEN.

## Original source and signed insertion

`squareSignedQuarticInsertion`,
`lean/YMGap/Continuum/BF4DyadicWilsonSquareSignedQuarticInsertion.lean:183`,
uses the original `selectedInsertion`. Its source at BOTH endpoints is
a=spatialWeight*terminalMessage_depth; every other selected heat factor
remains in the original spectator product. The selected factor is the
actual quartic chord polynomial times its original heat prefix.

The inserted signed factor is psi(lower)*psi(upper), with psi the literal
padded fundamental square centered at its OWN original odd mean, at the
same cutoff, width and terminal depth. No source independence, channelwise
center or mean replacement is assumed.

The private Type-valued `selected_weight_certificate` at line 193 constructs
the actual positive source/spectator/quartic weight. This is a Haar square
certificate, NOT positive-definiteness of the quartic integral operator.
Lifted square-bound transport uses padded coefficient equality and its
original Haar carrier; no pointwise-to-coefficient inference is used.

## Proved bounds and explicit parameters

`squareSignedQuarticInsertion_young_upper`,
`lean/YMGap/Continuum/BF4DyadicWilsonSquareSignedQuarticInsertion.lean:230`,
first proves twice the signed insertion is at most the SUM of its two
actual endpoint-diagonal insertions. Neither diagonal is discarded at
this stage, so sharper source-specific moment estimates remain usable.

The constructed OWN-centered square bound has cap 16.
`squareSignedQuarticInsertion_bounds` at line 263 therefore gives

    -16*M <= signedInsertion <= 16*M,

where M is the SAME original selected quartic mass. Both signs are
controlled by positive square certificates under the complete retained
weight; the bilateral signed source is not treated as pointwise positive.

For 16/17<=w<1, epsilon>0 and EVERY inclusive K>=quarticCutoff(w,epsilon),
`squareSignedQuarticInsertion_tolerance_bounds` at line 293 and
`squareSignedQuarticInsertion_abs_le` at line 309 give

    abs(signedInsertion)
      <= 16*(40*24576^2*(1-w)^2+epsilon)*oddMass(w,K,width,depth).

The existing `selectedChordInsertion_le_tolerance`,
`lean/YMGap/Continuum/SU2HeatJacobiOriginalHaarQuarticCutoff.lean:140`,
constructs the all-later cutoff from both original inclusive heat tails
and the original head guard. `quarticProfileCoefficient`,
`lean/YMGap/Continuum/SU2HeatJacobiFinitePrefixMargin.lean:52`, defines the
displayed nome-dependent coefficient. The head proof used to construct
the OWN center stays explicit. The estimate requires a valid padded
square and active selected link; there is no extra K>=2 restriction.

The coefficient and computed cutoff are independent of spatial width,
square size and terminal depth. The insertion, center and SAME odd mass
retain those parameters. This does not claim beta-independent control or
identify nome with physical lattice spacing.

## Remaining forward and backward join

The full-product signed Schur theorem pays raw source-square norm. This
new particular-source estimate avoids that cost by retaining the original
positive terminal source and bounding the signed observable cross term.
It does not prove a general raw-to-interacting norm comparison.

No declaration here identifies this selected quartic insertion with the
complete signed radius-two source. In particular it does not estimate
noise-minus-drift, supply m*(R1-R2)<=C*R1, or prove a useful family-wide
lag-one reserve. The backward blocked-survival consumer remains conditional:
`dyadicUnitResponse_filtered_block_floor`,
`lean/YMGap/Continuum/BF4WilsonAllNomeDyadicFilteredGeometricSurvival.lean:154`.
An actual source decomposition and the complete relative estimate must
connect the fronts. The finite even partition of the noise/drift fold is
not replaced by this odd partition.

## Verification

The final SECOND focused monitored check exited zero. All five public
gates use only {propext,Quot.sound}; no final error or warning occurs.
Independent mathematical and source/log/hash review passed. The first
check rejected a Type-valued certificate declared as a theorem and two
ambiguous let-body separators; the final source uses a data definition
and explicit separators. Statements and guards were unchanged.

| Artifact | SHA256 |
| --- | --- |
| `BF4DyadicWilsonSquareSignedQuarticInsertion.lean` | `00c03d7379b47563d90e02b4c4557b646a6684bd6bda878d86be105904e40333` |
| `/tmp/ym-original-signed-quartic-insertion-20261002-second.log` | `2151d40ce67e7815dbcb22df670bde8e3b462338db21965d8fe35547b02dec1c` |

One worker, explicit 20-GiB ceiling and 12-GiB OS reserve. Fresh dynamic
preflights showed 85 percent pressure-free memory and zero swap. Root
import registered, NOT aggregate-checked. No new sorry, axiom, classical
shortcut, weakened field, surrogate source, broad audit or CI change.
The documentation skill kept this insertion bound distinct from the
unproved filtered/scaling claims. Exact chart unchanged; no ASCII reprint.
Spatial/spacing control, continuum survival, physical mass calibration,
full SAME QFT, every compact simple group and the Clay target remain OPEN.
