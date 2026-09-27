# Curvature lower-bound scope correction (2026-09-27)

This audit corrects the historical verdicts in
[`docs/curvature-2026-07-06.md`](../docs/curvature-2026-07-06.md) and
[`docs/uniform-cd-inhabitation-scope-2026-06-22.md`](../docs/uniform-cd-inhabitation-scope-2026-06-22.md).
The mathematical declarations in `CurvatureSingleStepAssessment.lean` were
not changed by this documentation correction. Its current comment-only scope
correction is consistent with the declaration statements below; this audit
does not report a new compiler check.

## What the primary paper supplies

[Shen–Zhu–Zhu, *A stochastic analysis approach to lattice Yang–Mills at
strong coupling*, arXiv:2204.12737](https://arxiv.org/pdf/2204.12737),
Lemma 4.1 (4.2), bounds the **absolute value** of the Wilson-action Hessian
quadratic form by `8(d−1)N|β|` times squared tangent norm. Equation (4.7)
then bounds `Ric−Hess S` **from below** by `K_S`; Assumption 1.1 sets the SU(N)
coefficient to `(N+2)/2−1−8N|β|(d−1)`. At `N=2`, `d=4`, `β≥0`, this is
`1−48β`. A negative value means that particular lower bound no longer
certifies positive curvature. It gives no upper bound or sign determination
for actual curvature. The paper studies Wilson-action Langevin dynamics;
no identification with this repository's conditional heat action follows.

## Exact repository evidence and limit

| Declaration | Source | What it proves |
| --- | --- | --- |
| `free_curvature_anchor_bundled` | [`CurvatureSingleStepAssessment.lean:51`](../lean/YMGap/Continuum/CurvatureSingleStepAssessment.lean#L51) | Free Casimir/diagonal facts, using `free_DiagCD` in [`HeatKernelCurvature.lean:172`](../lean/YMGap/Continuum/HeatKernelCurvature.lean#L172). |
| `bondMovingDeltaRen_one_factor`, `curvature_lands_on_marginal_not_residual` | [`CurvatureSingleStepAssessment.lean:58`](../lean/YMGap/Continuum/CurvatureSingleStepAssessment.lean#L58), [`:73`](../lean/YMGap/Continuum/CurvatureSingleStepAssessment.lean#L73) | Exact rational residual factorization, using `renDefect_factor` in [`RenDefectQuadFactor.lean:193`](../lean/YMGap/Continuum/RenDefectQuadFactor.lean#L193), plus the free Casimir identity. Neither statement compares actual interacting Hessians or establishes a method no-go. |
| `szzCurvature` and its three sample theorems | [`CurvatureSingleStepAssessment.lean:87`](../lean/YMGap/Continuum/CurvatureSingleStepAssessment.lean#L87)–`:98` | Define and evaluate only the rational scalar `1−48β`. The historically named `szz_interacting_curvature_goes_negative` at `:94` means **that scalar** is negative at `β=1`. |
| `curvature_route_verdict` | [`CurvatureSingleStepAssessment.lean:103`](../lean/YMGap/Continuum/CurvatureSingleStepAssessment.lean#L103) | A conjunction of the free anchor, rational factorization and negative scalar sample; its name is not a proof that a curvature route fails. |

The live frontier types remain unsupplied: `SingleStepDefectBound` is declared
in [`SingleStepDefectReduction.lean:284`](../lean/YMGap/Continuum/SingleStepDefectReduction.lean#L284),
and `UniformCurvatureBound.uniform_CD` in
[`UniformCurvatureBound.lean:134`](../lean/YMGap/Continuum/UniformCurvatureBound.lean#L134)
demands one positive `K` for every indexed generator **plus** the bundle's
other fields. These scalar/free results neither inhabit nor refute either
type. The historical claims that every relevant curvature estimate is
analytic or polynomial in coupling, that curvature is necessarily
“wrong-form” for dimensional transmutation, that the actual interacting
curvature is negative, or that all curvature methods provably fail are
superseded. No claim that a sharper curvature method succeeds is made.

This is a scope correction only: no continuum, same-theory identification,
physical Hamiltonian gap, or new Yang–Mills result is established.
