# Original spin zero insertion clock

The current all-nome Wilson carrier now has an exact spin-zero clock pin.
The ambient time-zero multiplier is identity, while its buffered physical
bond insertion is the original one-step transfer. Arbitrarily long zero-spin
words retain their length on every bond class and in original signed-source
correlations. This is a fixed-parameter reconstruction consistency result,
not the missing scaling estimate or continuum QFT construction.

## Checked declarations

All entries below are in
`lean/YMGap/Continuum/BF4WilsonAllNomeSpinZeroClock.lean`.
The only gauge/parameter inputs are the supplied SU(2) source loops, literal
width and `0 < w < 1`. There is no small-nome, gap or scaling hypothesis.

| Declaration | Source line | Exact result |
| --- | --- | --- |
| `completedMultiply_spin_zero` | 109 | Spin-zero multiplier is identity on every ambient completion class. |
| `timeOne` | 122 | Constructed positive dyadic time for one original lattice step. |
| `act_spin_zero_value` | 125 | Ambient value of physical insertion equals original `completedTime 1`. |
| `act_spin_zero_time` | 131 | Actual insertion equals `bondAction timeOne` on every physical bond class. |
| `wordAct_spin_zero_value` | 137 | Ambient value of every zero-spin word equals original time at its length. |
| `wordAct_spin_zero_ofSource` | 149 | The actual physical source advances by that same length. |
| `wordAct_spin_zero_pairing` | 163 | Every completed mixed matrix element is the corresponding original time pairing. |
| `wordAct_spin_zero_source_pairing` | 172 | Every signed-source matrix element is the original odd reflected joint limit. |
| `wordAct_insert_spin_zero` | 185 | An interior zero label retains an explicit original step between arbitrary surrounding words. |

## Mathematical join

At a common horizon J, the multiplier's source polynomial is a product of
the original source with a lifted spin-zero character. The character is one,
but its lifted zero exponents require PADDED congruence; they are not a free
coefficient identity. `SU2QuaternionAuxiliaryLiftAlgebra.lift_one`
(`lean/YMGap/Continuum/SU2QuaternionAuxiliaryLiftAlgebra.lean:95`) supplies
that congruence. Both sources remain supported on `(2*J+1)*N` blocks.

`BF4WilsonAllNomeWindowPins.originalJoint_padded_congr`
(`lean/YMGap/Continuum/BF4WilsonAllNomeWindowPins.lean:65`) transports it
through the SAME original joint limit at horizon `2*J`.
`BF4WilsonAllNomeReflectedForm.intrinsicForm_chart`
(`lean/YMGap/Continuum/BF4WilsonAllNomeReflectedForm.lean:163`) and symmetry
give equality against every dense test.
`BF4WilsonAllNomeLinear.completion_eq_of_pointwise`
(`lean/YMGap/Continuum/BF4WilsonAllNomeLinear.lean:169`) descends this to
actual quotient equality on every ambient Cauchy class.

The physical insertion is already pinned to `R M R` by
`BF4WilsonAllNomeBondOSInsertion.act_root_pin`
(`lean/YMGap/Continuum/BF4WilsonAllNomeBondOSInsertion.lean:100`).
The new multiplier identity leaves `R^2`, which is ORIGINAL time one by
`BF4WilsonAllNomeNestedRootCompatibility.root_square`
(`lean/YMGap/Continuum/BF4WilsonAllNomeNestedRootCompatibility.lean:186`)
and `BF4WilsonAllNomeNestedRootBasics.root_zero_depth`
(`lean/YMGap/Continuum/BF4WilsonAllNomeNestedRootBasics.lean:230`).
`BF4WilsonAllNomeBondOSTime.bondValue_injective`
(`lean/YMGap/Continuum/BF4WilsonAllNomeBondOSTime.lean:72`) identifies the
physical operators themselves, not merely their dense-source values.

The immediate consumer is the EXISTING separated word action
`BF4WilsonAllNomeBondOSSeparatedWords.wordAct`
(`lean/YMGap/Continuum/BF4WilsonAllNomeBondOSSeparatedWords.lean:66`).
Induction retains one original step per zero-labelled letter.
`BF4WilsonAllNomeBondOSCompletion.constant_pairing`
(`lean/YMGap/Continuum/BF4WilsonAllNomeBondOSCompletion.lean:365`) then gives
the original joint-limit correlation with BOTH signed sources preserved.
No commutativity of buffered letters is used.

## Verification boundary

The final source passed this focused command with exit zero and no warnings:

```sh
python3 scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 20 --check lean/YMGap/Continuum/BF4WilsonAllNomeSpinZeroClock.lean --check-output lean/.lake/build/lib/lean/YMGap/Continuum/BF4WilsonAllNomeSpinZeroClock.olean --log-file /tmp/ym-all-nome-spin-zero-clock-20261002-final.log
```

All eight theorem gates reported `{propext, Quot.sound}`. The `timeOne`
definition reported `{propext}`. No `sorryAx`, classical axiom, custom axiom,
`native_decide`, `noncomputable` declaration or new analytic premise was added.
Independent Sol mathematical/source review passed; its wording cautions about
the empty word and deletion were resolved before the final source check.

Source SHA-256:
`7b33da883bc999c5732cee68cb733cd4c78861d3bc41bf0288f1743c6331e439`.
Final log SHA-256:
`325e603a9e9529844e6e0351a52859a01e1146a78e6096014ab1825f4131d9f6`.

Preflight and post-check observations reported 86 percent pressure-free memory
and zero swap on the 64-GiB host. No competing or surviving compiler/runner
process was found. One capped worker and a 12-GiB OS reserve were retained.
One root import was added; full root/tree builds, audits, guards and metrics
were NOT run. Automatic GitHub CI remains disabled. Canonical chart blocks
are unchanged; their SHA-256 is
`6f64d1437f38622c455b8d123f001def2a5c459eebf9e785b3e40d117b19a179`.

## Remaining goal inputs

The empty word is identity, and time fixes the vacuum. The interior-zero law
does not prove inequality against a deleted-word operator. It retains the
explicit step in the exact formula, while spin-zero label geometry becomes
inert. The signed input sources and original action remain unchanged.

The source-specific signed energy/OWN-variance estimate on a justified changing
family, physical time/spacing calibration, nonzero continuum survival, full
same-theory QFT structure and every compact simple group remain OPEN. No
canonical frontier field or displayed chart claim was weakened or closed.
