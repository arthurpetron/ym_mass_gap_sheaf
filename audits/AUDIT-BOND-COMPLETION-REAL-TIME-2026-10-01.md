# Positive real time on the physical bond completion

Date: 2026-10-01 UTC. The completed physical odd-window bond sources now
carry the original time evolution at numerical positive real times.
Explicit represented states supply positive rational continuity radii.
This fills a fixed-nome, fixed-width reconstruction step with already
constructed inputs. It does not supply a continuum theory or physical mass.

## Construction and original object identities

`BF4WilsonAllNomeBondOSTime.sectorActionRep`
(`lean/YMGap/Continuum/BF4WilsonAllNomeBondOSTime.lean:83`)
uses the existing original `positiveAction_preservesRange` to compute the
output range witness before quotienting. `bondAction`
(`lean/YMGap/Continuum/BF4WilsonAllNomeBondOSTime.lean:104`)
transports this through the previously checked inverse maps between the
represented bond completion and the witnessed sector quotient. No preimage
is selected and no replacement carrier or inner product is postulated.

`bondAction_value`, `bondValue_distance` and `bondValue_inner`
(`lean/YMGap/Continuum/BF4WilsonAllNomeBondOSTime.lean:115`,
`:122`, `:130`) identify the action and geometry with the ORIGINAL completed
vector. `bondAction_ofSource_one`
(`lean/YMGap/Continuum/BF4WilsonAllNomeBondOSTime.lean:171`)
recovers the actual one-step geometric advance of a finite source.

`BF4WilsonAllNomeBondOSRealTime.action`
(`lean/YMGap/Continuum/BF4WilsonAllNomeBondOSRealTime.lean:63`)
then descends to numerical positive real time: equivalent time data give
identical bond states. `action_addTime`, `action_distance_bound`,
`action_symmetric`, `action_nonnegative`, `action_norm_bound` and
`action_vacuum` (same module, lines 78, 85, 91, 96, 101 and 106) preserve
the existing laws on this physical bond completion. The legacy modules
contribute only the carrier-free numerical time quotient and addition;
no legacy operator or state space is substituted.

## Computed continuity data

For an explicit physical Cauchy row X, `continuityRadius`
(`lean/YMGap/Continuum/BF4WilsonAllNomeBondOSRealTime.lean:119`)
uses the range witness of its computed original limit. It is the existing
radius `2^(-k-1)`, where k is computed from that witness and the requested
squared-distance tolerance. `action_smallTime` (same module, line 126)
proves that every positive numerical time below the radius moves the bond
state by at most that tolerance in squared bond distance.

`continuityCertificate` (same module, line 137) returns the radius and proof
as Type-level data. It takes explicit rows, not just an arbitrary quotient
class. `action_smallIncrement` (line 147) combines composition and
contraction to use the SAME radius for every positive forward increment.
This does not claim uniformity in nome, width or state. Zero is a limiting
time, not an added element of the positive-time datatype.

## Remaining mathematical inputs

The primary analytic frontier remains a useful signed cost bound versus
the SAME interacting variance on a justified scaling family, with actual
physical-time calibration. The parallel source review is recorded in
`audits/RESEARCH-TARGETED-YM-FRONTIER-2026-09-30.md`, under Signed family
and original weight review. It supplies no new scaling inequality.

This construction does not restrict time-zero multipliers to the sector;
the existing width-one obstruction is retained. It does not identify the
canonical limiting half-space observable algebra, reconstruct continuum
local fields, calibrate a physical Hamiltonian, prove survival or cover
every compact simple group. No canonical frontier field is changed.

## Verification

Both final focused checks passed, with 34 printed axiom gates exactly in
{propext, Quot.sound}. No sorry, new axiom, Classical dependency,
native_decide or noncomputable declaration was introduced. Initial quotient
elaboration errors were fixed before acceptance, and the complete final
source of each module was checked. Independent read-only review found no
quotient representative selection or scope mismatch.

Only the main agent compiled. The safe launcher serialized checks with
one worker, a 20 GiB ceiling and 12 GiB OS reserve. Preflight found no
competing Lean/Lake/test/runner process; memory pressure reported 90 percent
free. No full root build, full-tree audit or guard was run. Aggregate root
imports were added but not compiled. Automatic CI remains manual-only.
The canonical chart is unchanged and was not reprinted.

Final logs and SHA-256 values:

- `/tmp/ym-bond-os-time-final-20261001.log`:
  `a5875bee12b45edfebad30e3338eb35f9e19319efd15d93455eaadd2047af374`.
- `/tmp/ym-bond-os-real-time-20261001.log`:
  `6e982c37ba9abcd3fb3d5c5cf905d63d0d343cdbfeb2a508e62cf0861cd61efb`.

## Addendum: complex physical bond completion and time

The previously absent physical/complex join is now constructed, at the SAME
fixed nome and literal width. It uses two existing real BondCompletion
factors, not a new analytic Hilbert carrier or an assumed isometry.

In `lean/YMGap/Continuum/BF4WilsonAllNomeComplexBondOSCompletion.lean`,
`value_injective` (line 60) embeds the pair in the EXISTING complex Wilson
completion. `toSector` and `fromSector` (lines 107 and 115) descend explicit
representative operations to the existing complex value-based sector setoid.
`toSector_fromSector` and `fromSector_toSector` (lines 133 and 138) prove both
inverse laws; `toSector_isometry` (line 166) proves the original norm pin.
Range witness records are not equated, nor selected from quotient classes.

`inner` (line 144) consists of the four existing physical real bond pairings:

    Re = B(x_re,y_re)+B(x_im,y_im),
    Im = B(x_re,y_im)-B(x_im,y_re).

`source_pairing` (line 204) identifies all four terms with the ORIGINAL
normalized odd reflected joint limits. `inner_conj_symm`, `inner_nonnegative`
and `inner_posdef` (lines 177, 181 and 185) give the actual Hermitian/null
geometry. The raw ambient time kernel is not discarded by decree.

`denseSource_bound` (line 224) computes an actual finite paired Wilson source
from supplied physical rows at half tolerance per coordinate.
`CauchySequence` (line 237) requires represented paired rows and one explicit
all-tail modulus. `limitRows` and `limitCertificate` (lines 254 and 267)
return new physical rows and a computed joint rate from the original complex
sector limits. No arbitrary quotient-sequence representative stream is chosen.

In `lean/YMGap/Continuum/BF4WilsonAllNomeComplexBondOSTime.lean`, `value_add`
and `value_smul` (lines 59 and 66) pin complex operations to the existing
ones, retaining the supplied constructive-real scalar moduli. The Hermitian
add/scalar laws have the correct conjugate-linear first argument.
`action_value`, `action_addTime`, `action_symmetric` and
`action_distance_bound` (lines 160, 168, 174 and 183) identify numerical
positive time with the original action. `action_ofSource_one` (line 200)
preserves the ORIGINAL advance of both finite source components.
`continuityRadius` (line 213) is the minimum of the two physical row radii at
half tolerance; `action_smallTime` and `continuityCertificate` (lines 225
and 257) control every numerical positive time below that radius.

This fills only the complex physical bond carrier/pairing/time join. No
existing canonical full-QFT consumer accepts it without the missing SAME
continuum Schwinger functional, half-space observable/support/reflection
realization and scaling/time/generator calibration. Complex scalar-field
instances, full QFT, survival, all compact simple groups and Clay closure
are not asserted. The primary signed energy/variance scaling estimate is
still OPEN; no canonical scorecard field or displayed chart status changed.

Both final focused checks exited zero, with 23 completion and 19 time gates
exactly in {propext, Quot.sound}. Independent read-only review confirmed
source pins, witness flow, scalar signs, radius and parameter scope. Main
alone compiled with the SAME one-worker 20 GiB ceiling and 12 GiB OS reserve;
initial elaboration/syntax failures were repaired before acceptance, without
raising heartbeat or safety limits. Preflight found no competing compiler/
runner, 84 percent pressure-free memory and zero swap. No full root/tree
build, broad audit or guard was run; root imports are registration only.
The safe-build skill confined checks to the actual changed files. CI remains
manual-only; the unchanged chart was not printed.

Accepted logs and SHA-256:

- `/tmp/ym-complex-bond-completion-repaired-20261001.log`:
  `bda514f9c892849f9e27d4353bdb4e55d8d92fdb7ec3592781fae64718694fb5`.
- `/tmp/ym-complex-bond-time-repaired-20261001.log`:
  `8a06cd56ec3d2c6c9de5276e4713fa59d82e25c2c4becc8a839d71437bd59c6e`.
