# A concrete original derivative-domain excitation

The unchanged goal is nontrivial continuum Yang--Mills on R^4 for every
compact simple group, with SAME-theory QFT axioms and a positive physical
Hamiltonian mass gap. It remains OPEN. This increment supplies a concrete
nonzero input/action pair and quantitative Taylor witness for the EXISTING
original derivative graph, at fixed nome 1/16 and spatial width two.

## Forward object meets the existing backward domain

Let v be the EXISTING centered vector of the literal six-edge bent loop,
T the ORIGINAL completed time map, and A its constructed range derivative.
No state, action, mean, partition, domain or operator is postulated here.

    p = DerivativeGraph.fromTime(v),
    input(p)=T(1)v, action(p)=A(v),
    input(p) is orthogonal to the SAME unit vacuum,
    ||input(p)||^2 >= r=2^-128 > 0.

The existing positive image floor now supplies an actual named domain
element, not a conditional request for one. Its input and action are both
proved nonzero. This does NOT assert that p is an eigenstate.

The sharp graph and domain form bounds retain the actual one-step margin
m=mixFraction(w,width)=kineticFloor/kineticCap, not the older squared-rate
margin. For EVERY original graph-domain input in its vacuum complement,

    m*||input||^2 <= <input,action>.

For p, the computed centered-stream ceiling c=centeredNormCeiling(bentLoop)
bounds BOTH ||input(p)||^2 and ||action(p)||^2. Nonnegativity of
||input(p)-action(p)||^2 then gives the finite energy interval

    0 < m*r <= E=<input(p),action(p)> <= c.

All three constants are explicit rational data. Nome, width and the
particular observable remain fixed; no family-uniform ceiling or physically
rescaled energy bound is asserted.

## Constructed positive-real-time derivative witness

`bentDerivativeTaylorCertificate(epsilon,he)` returns a positive rational
radius in Type. For EVERY supplied positive real time t below that radius,
on the ORIGINAL positive-real-time action S,

    ||input(p)-S(t)input(p)-t*action(p)||^2 <= epsilon*t^2.

The caller supplies only the tolerance and its positivity proof, not a
graph witness, inverse time image, norm cap or chosen representative.
The preimage stream is constantly the literal `centeredStream` of v.
Its time-map representative supplies the input; `derivativeCertificate`
supplies the output representative. The existing real Taylor construction
therefore applies without quotient representative selection.

This is the actual range derivative graph. It is NOT a proved self-adjoint
physical Hamiltonian, equality with the regularized-log graph, a physical
time calibration, or continuum survival.

## Declaration anchors

All paths below have prefix `lean/YMGap/Continuum/`.

- `BF4WilsonAllNomeDerivativeGraphGap.lean:182`, `graph_form_sharp_gap`;
  :206, `action_form_sharp_gap`.
- `BF4WilsonSmallNomeBentDerivativeExcitation.lean:61`, `bentDerivativePoint`;
  :64, `bentDerivativeNormCeiling`; :68, `bentDerivativeEnergyFloor`;
  :72, `bentDerivativeEnergy`; :77, `bentDerivativePoint_pins`;
  :87, `bentDerivativePoint_orthogonal`; :94, `bentDerivativePoint_norm_bounds`;
  :107, `bentDerivativePoint_norm_floor`; :113, `bentDerivativePoint_input_ne_zero`;
  :162, `bentDerivativeEnergy_bounds`; :176, `bentDerivativeEnergy_ne_zero`;
  :188, `bentDerivativePoint_action_ne_zero`; :197, `bentDerivativeTaylorCertificate`.
- Existing `BF4WilsonAllNomeOneStepGap.lean:159`,
  `completed_oneStep_defect_margin`; `BF4WilsonAllNomeDerivativeGraph.lean:231`,
  `fromTime`; `BF4WilsonAllNomeCenteredVector.lean:177`, `centeredNormCeiling`;
  `BF4WilsonAllNomeDerivativeGraphReal.lean:180`, `realTaylorCertificate`.

## Continuing from both ends

The forward review found no new near-one action-dependent relative estimate.
The exact square Ward/Taylor identity and its completed energy/variance joins
already exist. Initial OWN-variance control is a sufficient alternative to
the stronger initial-energy-versus-filtered-variance target: existing positive
response powers propagate an actual initial adjacent ratio. The complete
original action/Ward correction is still unpaid; no wrapper was added for it.

The independent structural target is now a finite root/log polynomial
sandwich, with a positive finite primitive argument, to identify A and the
EXISTING regularizedLog on the SAME carrier. The scalar producer and actual
operator lift are still unproved; see
`audits/MATH-NOTE-ORIGINAL-ROOT-LOG-SANDWICH-2026-10-03.md`.
Spatial/spacing control, justified changing-family survival, physical mass
calibration, full QFT axioms, every group and Clay closure remain OPEN.

## Verification boundary

Both accepted serialized focused checks exited zero. Their 20 printed gates
(15 new, five unchanged) depend only on {propext, Quot.sound}; accepted logs
contain no errors, warnings, sorryAx or PANIC. Root read both full source
files. Sol constructed the concrete source; independent Luna static review
confirmed the literal carrier/domain pins and scope. Reviews are not kernel
checks.

| Source basename | Accepted log under /tmp | Gates | Source SHA-256 | Log SHA-256 |
| --- | --- | ---: | --- | --- |
| `BF4WilsonAllNomeDerivativeGraphGap.lean` | `ym-derivative-graph-sharp-20261003-b.log` | 7 | `8f20ffefb976a3f6df5bbeea65bc44036da4249cc5204aa9e57ffa9fec7b02c5` | `395fa31c8ab300917f0f361b6e61228ec7e1b798709c07a98172c6b9135e0e52` |
| `BF4WilsonSmallNomeBentDerivativeExcitation.lean` | `ym-bent-derivative-excitation-20261003-b.log` | 13 | `35136ab8b04582e514f82b81179662331794b31610f3865498b46052500af8f4` | `ea4fa552b0fdaaeae1b8e7eb94e9c9f62deecae9447e257ca194aeb3838797d6` |

The failed development logs a are excluded. The first used an incorrect
source path; the concrete source's first check rejected a local transparency
reclassification and its dependent representation equalities. Removing the
unnecessary reclassification restored default transparency; the unchanged
mathematical statements then passed. No unsafe option, sorry, new axiom,
classical shortcut or resource increase was introduced.

Every launch had fresh memory/process/swap checks and the safe launcher:
one worker, 12GiB reserve, 20GiB worker ceiling. Preflights showed 84% free
memory, zero swap and no competing proof job. No full build, aggregate root,
broad audit/guard or progress metric was run. The root import is registration
only; CI stays manual-only. The canonical first chart fence stays unchanged,
SHA-256 `0d9295165945a8acea2c4037bd951f9060a1dfcc22448bde4462d0c795b12145`.
No exact displayed scaling/continuum claim changed, so no chart is reprinted.

Independent Luna final evidence/documentation QA confirmed all source/log
hashes, 20 accepted gates, current declaration anchors, unique root import,
explicit fixed-parameter boundary, unchanged chart fence and manual-only CI.
Staged diff whitespace checks passed.
