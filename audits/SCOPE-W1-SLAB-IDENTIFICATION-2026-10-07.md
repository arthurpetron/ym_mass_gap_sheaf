# Scope: identifying the W = 1 tridiagonal model with the repo's width-1 slab transfer (2026-10-07)

Verdict: NOT cheap, and the identification as posed is FALSE. The tridiagonal spin-chain
model (`W1StrongCouplingPerturbation`, `W1VacuumTailRowSum`, `W1VariationalMinMax`) is a
one-plaquette/one-character MODEL. It is not the repo operator at width 1. No Lean was started.

## (a) The repo operator and space

- **Space.** `BF4WilsonAllNomeCompletedInner.Completion hw0 hw1 width`, defined as
  `(seminorm hw0 hw1 (width := width)).Completion` (file `BF4WilsonAllNomeCompletedInner.lean`).
  - It is the Cauchy completion of `IntrinsicExpression width`
    (`BF4ExactSlabFixedSpatialWilsonIntrinsicForm`): finite-radius polynomial observables in
    the quaternion link coordinates of a Z4 slab, under the reflected all-nome form
    `BF4WilsonAllNomeReflectedForm.intrinsicForm`.
  - The inner product is `completedInner` (= `CRealSeminormPairingCompletion.completedInner`
    of `pairingData`), valued in RC.
  - The vacuum is `unitState`/`U`. `VacuumComplement := {x // B U x = RCzero}`
    (`BF4WilsonAllNomeCompletedTime.lean:171`).
- **Operator.** `T 1 = completedTime hw0 hw1 1` (`BF4WilsonAllNomeCompletedTime`). It descends
  `BF4ExactSlabFixedSpatialWilsonPhysicalTime.advance`, which shifts the expression radius by 1
  (one lattice time step).
- **Contraction.** `WilsonVacuumSqContraction r` (`BF4WilsonAllNomeExprMixRateContraction.lean:61`)
  is `∀ y : VacuumComplement, B(T1 y, T1 y) ≤ r²·B(y,y)`.
  - It is already PROVED at `r = mixRate = 1 − kineticFloor/kineticCap`
    (`wilsonVacuumSqContraction_mixRate`, from `completed_oneStep_norm_gap`).
  - Here `kineticFloor = headFloor w ^ |temporalFaces width|` and
    `kineticCap = prefixCap w ^ |temporalFaces width|` (`BF4ExactSlabFixedSpatialTransferSandwich`).
- **Geometry: a Z4 spatial slice, not a single plaquette.** `width` is the side of the boxed
  spatial slice.
  - `BF4ExactSlabFixedSpatialSliceCarrier.baseLinks width` = boundary-complete slab links
    satisfying `SliceLink width 0`.
  - The spatial weight is
    `spatialWeight w K width = Π_{face ∈ spatialFaces width} heatPrefix w K (plaquette width face).scalar`.
  - There are |temporalFaces width| kinetic faces, and Haar is taken over `N width` quaternion
    blocks.
  - Even at width = 1 this is a multi-link, multi-plaquette slice. Gauge-invariant observables
    include products of several plaquette characters, Polyakov-type loops and so on. So the
    single-chain tridiagonal model on spins s ≥ 0 is **not** the repo operator. At best it is
    a heuristic for one plaquette-character sector.

## (b) The minimal statement an identification would need

1. A linear map `J : (Nat →₀ Q') → Completion hw0 hw1 1` (finitely supported spin sequences)
   with:
   - `J χ₀ = U`;
   - isometry: `completedInner (J x) (J y) = Σ x_s y_s`;
   - intertwining at the form level: `B (T 1 (J x)) (J y) = triForm`-bilinear `⟨x, T_model y⟩`.
2. Invariance or decoupling. Either `range J` is `T 1`-invariant and its orthogonal complement
   is controlled separately, or `range J ⊇ VacuumComplement`.
   - The second is false: there are many other gauge-invariant observables.
   - So even (1) only gives a **compression**. The variational bound then constrains `T 1`
     on `range J` only, not on `VacuumComplement`.
3. Even then, the target `WilsonVacuumSqContraction` is about `‖T1 y‖²`, i.e. `T²`, while the
   model bound is about `⟨Tx,x⟩`. Passing from one to the other needs positivity and symmetry
   of `T 1` on the range. Those exist in the repo: `completedInner_oneStep_nonnegative` and
   `completedInner_time_balance`.

Part (1) requires computing Haar integrals of products of plaquette characters on the width-1
slice and proving they are tridiagonal in spin. That is false beyond one plaquette, because
neighbouring plaquettes share links and recouple through 6j symbols. It is not cheap.

## (c) Is "1 + κχ₁" exact for the repo weight?

- **Character expansion.** The repo weight is a heat-kernel (nome) weight, not the Wilson
  exp(β Re tr). Per plaquette,
  `faceHeatPolynomial w K id = Σ_{s≤K} coeffW w s · χ_s`, with `coeffW w s = (s+1)·w^{c4 s}`
  and `c4 s = s(s+2)` (`BondMovingStep.coeffW`; `heatKernelPacket` in
  `Z4FiniteBoxHeatKernelPacketState`; `BF4ExactSlabInterfaceHeatProduct.faceHeatPolynomial`).
  - The character expansion is EXACT: the Fourier coefficients are `coeffW`.
  - The K-truncation tail is controlled by `prefixCap`/`spacingClosedTail`.
  - There is no separate Wilson factor to linearize.
- **Leading order only.** `1 + κχ₁` with κ = `coeffW w 1` = `2w³` is the truncation at s ≤ 1.
  The model's fixed κ = 1/4 does not match `2w³` for general w. The model theorems are
  κ-parametric (they only need κ ≥ 0 and the `hsmall` condition), so κ = 2w³ is admissible.
- **Error term.** With |χ_s| ≤ s+1 on SU(2), the sup-norm error is
  `Σ_{s≥2} (s+1)² w^{s(s+2)} = 9w⁸ + 16w¹⁵ + 25w²⁴ + …`.
  - Successive term ratios are ≤ (16/9)·w⁷ ≤ 1/72 for w ≤ 1/2.
  - So the error is **≤ 10·w⁸ for 0 ≤ w ≤ 1/2** (pencil bound, not formalized). It is relative
    to the s = 0 coefficient 1.
- **Model exponent.** The model's diagonal entries `w^{4c4(s)}` are a separate heuristic: four
  heat factors per spin-s sector. The repo has not derived them for the width-1 slice.

## U(1) rule

The repo's `mixRate < 1` result and the model bound are both strong-coupling Doeblin/row-sum
statements. They hold equally for the U(1) analogue, so neither is evidence of a continuum
gap. The real content is the scale-uniform lower margin (OPEN, see
`BF4WilsonAllNomeExprMixRateContraction`).

## Conclusion

- The identification fails as stated: the repo operator lives on a Z4 spatial slice.
- The useful honest statement is only a compression on a one-plaquette-character sector, and
  that still needs Haar computations on the slice.
- Recommendation: do not pursue. The repo already has a stronger all-vector contraction
  (`mixRate`) on the true carrier. The open item there is the lower margin, not the W = 1 model.
