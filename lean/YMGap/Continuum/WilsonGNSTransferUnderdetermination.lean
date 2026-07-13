/-
The exact dynamics boundary of `WilsonGNSData`.

`WilsonGNSData` determines the static Wilson observable algebra, its positive
expectation form, the radical quotient, and the completed GNS Hilbert space.  It
contains no Euclidean time-shift map.  Consequently it cannot select a physical
transfer operator.  This file makes that underdetermination kernel-visible.

First, every `GNSData` supports a second canonical transfer operator besides the
existing identity: the constant embedded-zero operator.  It is self-adjoint,
positive, and contractive.  On the same nondegenerate rank-one Wilson datum
`qWilsonGNS 1`, the identity and zero operators are provably distinct.  Their
nonzero dense head is an exact eigenvector with eigenvalue respectively `1` and
`0`; the former one-mode spectrum has no located gap, while the latter has the
located separator `0`.  Thus identical `WilsonGNSData` fields admit incompatible
realized transfer spectra.

Second, the missing data are isolated without weakening the conclusion:

  * `WilsonTimeTranslationPin` supplies an observable time shift `tau`, a
    completed positive self-adjoint contraction, and the dense intertwining
    equation `T(embed a) = embed(tau a)`.  Radical preservation is then proved,
    not assumed.
  * `WilsonCharacterSpectrumPin` adds exactly the finite character-coordinate
    Schur identities.  This pins the normalized eigenvalues
    `qpow w (c4(i+1))` to the selected operator's quadratic form and yields the
    genuine operator-form gap through the existing physical character theorem.

The first pin selects dynamics; the second is indispensable because the present
`SpectralGapData` otherwise packages its `op` and finite `model` without a
compatibility field.  No inhabitant for the general interacting Wilson theory
is fabricated here.

# Axiom-gate (AGENTS.md Rule 1)

All declarations below have axiom dependencies contained in
`{propext, Quot.sound}`.  No `Classical.*`, `sorry`, `native_decide`, custom
axiom, or noncomputable definition is used.  Closed rational facts use kernel
`decide` only.
-/

import YMGap.Continuum.ContinuousFunctionalCalculusForm
import YMGap.Continuum.PhysicalWilsonBridge
import YMGap.Continuum.WilsonSchurIdentities

namespace YMGap.Continuum.WilsonGNSTransferUnderdetermination

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.HamiltonianScalar
open YMGap.Continuum.SpectralGap
open YMGap.Continuum.WilsonGNS

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. A second canonical transfer on every completed GNS space -/

/-- The constant embedded-zero transfer operator.  The completed zero-inner
identities make it self-adjoint and positive, while reflection positivity of
the original form proves contraction. -/
def zeroTransfer (D : GNSData) : TransferOperator D.gnsComplete where
  T := fun _ => embedV D D.zero
  vacuum := embedV D D.zero
  selfAdjoint := fun x y => by
    show D.cinnerCompl (embedV D D.zero) y =
      D.cinnerCompl x (embedV D D.zero)
    rw [D.cinnerCompl_embedZero_left, D.cinnerCompl_embedZero_right]
  positive := fun x => by
    show CReal.RCnonneg (D.cinnerCompl (embedV D D.zero) x)
    rw [D.cinnerCompl_embedZero_left]
    exact CReal.RCle_refl CReal.RCzero
  contraction := fun x => by
    show CReal.RCle
      (D.cinnerCompl (embedV D D.zero) (embedV D D.zero))
      (D.cinnerCompl x x)
    rw [D.cinnerCompl_embedZero_left]
    exact D.cinner_self_nonneg x

/-! ## 2. The same nondegenerate Wilson datum has two distinct dynamics -/

/-- The concrete nondegenerate static Wilson datum used for the no-go fence. -/
def qW : WilsonGNSData qObsAlg := qWilsonGNS 1 (by decide)

/-- Its genuine completion scalar action.  The underlying `GNSData` is
definitionally the one obtained from `qW`. -/
def qS : SmulGNSData := qSmulGNS 1 (by decide)

/-- Exact identity of every static `GNSData` field in the scalar and Wilson
presentations used below. -/
theorem qS_toGNSData_eq_qW : qS.toGNSData = qW.toGNSData := rfl

/-- Carrier-equivalent vectors have equal dense images in the completion. -/
theorem embedV_eq_of_veq (D : GNSData) {a b : D.V} (h : D.veq a b) :
    embedV D a = embedV D b := by
  apply Quotient.sound
  exact embed_null_of_rad D (rad_of_veq D h)

/-- A nonzero dense head in the rank-one Wilson completion. -/
def qHead : GNSCompletionSpace qW.toGNSData :=
  embedV qW.toGNSData ((1 : Q') : qW.toGNSData.V)

/-- The dense head is not the embedded zero.  Injectivity of the completion
embedding reduces this to the closed exact fact `B(1,1) != 0`. -/
theorem qHead_ne_zero :
    qHead ≠ embedV qW.toGNSData qW.toGNSData.zero := by
  intro h
  change embedV qW.toGNSData (1 : Q') =
    embedV qW.toGNSData (0 : Q') at h
  have hq : qW.toGNSData.qmk (1 : Q') =
      qW.toGNSData.qmk (0 : Q') :=
    embedQuot_injective qW.toGNSData h
  have hr : qW.toGNSData.rad (1 : Q') (0 : Q') := Quotient.exact hq
  have he := (qW.toGNSData.rad_zero_iff (1 : Q')).mp hr
  exact (by decide :
    ¬ ((qW.toGNSData.B (1 : Q') (1 : Q')).eqv 0)) he

/-- The identity and zero transfers on the identical Wilson GNS completion are
different operator maps. -/
theorem idTransfer_T_ne_zeroTransfer_T :
    (qW.toGNSData.idTransfer).T ≠ (zeroTransfer qW.toGNSData).T := by
  intro h
  have hh := congrFun h qHead
  exact qHead_ne_zero hh

/-! ## 3. The minimal time-translation pin -/

/-- The minimal datum selecting Wilson dynamics: an observable time shift, a
completed positive self-adjoint contraction, and their dense intertwining
equation.  No separate quotient well-definedness premise is required. -/
structure WilsonTimeTranslationPin {A : ObservableMeasure.ObsAlg}
    (W : WilsonGNSData A) : Type where
  /-- Euclidean one-step shift on Wilson observables. -/
  tau : A.carrier → A.carrier
  /-- Its completed transfer operator. -/
  op : TransferOperator W.toGNSData.gnsComplete
  /-- The completed action extends the observable shift on the dense image. -/
  dense_intertwines : ∀ a,
    op.T (embedV W.toGNSData a) = embedV W.toGNSData (tau a)

/-- Dense intertwining forces the observable time shift to preserve the GNS
radical, so it genuinely descends to the quotient. -/
theorem WilsonTimeTranslationPin.tau_preserves_rad
    {A : ObservableMeasure.ObsAlg} {W : WilsonGNSData A}
    (P : WilsonTimeTranslationPin W) {a b : A.carrier}
    (h : W.toGNSData.rad a b) :
    W.toGNSData.rad (P.tau a) (P.tau b) := by
  have hab : embedV W.toGNSData a = embedV W.toGNSData b := by
    apply Quotient.sound
    exact embed_null_of_rad W.toGNSData h
  have hT : embedV W.toGNSData (P.tau a) =
      embedV W.toGNSData (P.tau b) := by
    rw [← P.dense_intertwines a, ← P.dense_intertwines b, hab]
  exact constCauchy_null_imp_rad W.toGNSData (Quotient.exact hT)

/-- Positivity of the selected dynamics, exposed directly from the pin. -/
theorem WilsonTimeTranslationPin.positive
    {A : ObservableMeasure.ObsAlg} {W : WilsonGNSData A}
    (P : WilsonTimeTranslationPin W) (x : GNSCompletionSpace W.toGNSData) :
    CReal.RCnonneg (W.toGNSData.cinnerCompl (P.op.T x) x) :=
  P.op.positive x

/-- Contractivity of the selected dynamics, exposed directly from the pin. -/
theorem WilsonTimeTranslationPin.contraction
    {A : ObservableMeasure.ObsAlg} {W : WilsonGNSData A}
    (P : WilsonTimeTranslationPin W) (x : GNSCompletionSpace W.toGNSData) :
    CReal.RCle
      (W.toGNSData.cinnerCompl (P.op.T x) (P.op.T x))
      (W.toGNSData.cinnerCompl x x) :=
  P.op.contraction x

/-- Identity observable dynamics on the fixed static Wilson datum. -/
def qIdentityPin : WilsonTimeTranslationPin qW where
  tau := id
  op := qW.toGNSData.idTransfer
  dense_intertwines := fun _ => rfl

/-- Zero observable dynamics on that same static Wilson datum. -/
def qZeroPin : WilsonTimeTranslationPin qW where
  tau := fun _ => qW.toGNSData.zero
  op := zeroTransfer qW.toGNSData
  dense_intertwines := fun _ => rfl

/-! ## 4. Incompatible realized head spectra on identical static fields -/

/-- One nonzero spectral mode at eigenvalue one. -/
def unitModel : SpectralModel where
  k := 1
  w := fun _ => 1
  lam := fun _ => 1
  w_nonneg := fun _ => by decide
  lam_nonneg := fun _ => by decide

/-- One nonzero spectral mode at eigenvalue zero. -/
def zeroModel : SpectralModel where
  k := 1
  w := fun _ => 1
  lam := fun _ => 0
  w_nonneg := fun _ => by decide
  lam_nonneg := fun _ => by decide

/-- The zero head spectrum has the maximal separator `0 < 1`. -/
def zeroLocatedGap : LocatedSpectralGap zeroModel where
  sep := 0
  sep_lt_one := by decide
  bound := fun _ => Q'.le_refl' 0

/-- The unit head spectrum admits no separator below the vacuum eigenvalue. -/
theorem unitModel_no_located_gap : LocatedSpectralGap unitModel → False := by
  intro g
  have hle : (1 : Q') <= g.sep := by
    simpa [unitModel] using g.bound 0
  exact (by decide : ¬ ((1 : Q') < (1 : Q')))
    (Q'.lt_of_le_of_lt hle g.sep_lt_one)

/-- An honest head-spectrum realization: the model's zeroth eigenvalue acts on
a nonzero completed vector through the genuine completion scalar action. -/
structure HeadSpectrumRealization
    (P : WilsonTimeTranslationPin qW) (model : SpectralModel) : Type where
  head : GNSCompletionSpace qW.toGNSData
  head_ne_zero : head ≠ embedV qW.toGNSData qW.toGNSData.zero
  head_eigen : P.op.T head = qS.cSmul (model.lam 0) head

/-- The identity dynamics realizes eigenvalue one on the nonzero head. -/
def unitRealization : HeadSpectrumRealization qIdentityPin unitModel where
  head := qHead
  head_ne_zero := qHead_ne_zero
  head_eigen := by
    show qHead = qS.cSmul 1 qHead
    unfold qHead
    change embedV qS.toGNSData (1 : Q') =
      qS.cSmul 1 (embedV qS.toGNSData (1 : Q'))
    rw [qS.cSmul_embed]
    exact (embedV_eq_of_veq qS.toGNSData (Q'.one_mul_eqv 1)).symm

/-- The zero dynamics realizes eigenvalue zero on the same nonzero head. -/
def zeroRealization : HeadSpectrumRealization qZeroPin zeroModel where
  head := qHead
  head_ne_zero := qHead_ne_zero
  head_eigen := by
    show embedV qW.toGNSData qW.toGNSData.zero = qS.cSmul 0 qHead
    unfold qHead
    change embedV qS.toGNSData (0 : Q') =
      qS.cSmul 0 (embedV qS.toGNSData (1 : Q'))
    rw [qS.cSmul_embed]
    exact (embedV_eq_of_veq qS.toGNSData (QPoly.q_zero_mul 1)).symm

/-- The zero dynamics and its zero head spectrum form an actual located
`SpectralGapData` on the same Wilson completion. -/
def qZeroPinnedSpectralGapData : SpectralGapData qW.toGNSData.gnsComplete where
  op := qZeroPin.op
  model := zeroModel
  gap := zeroLocatedGap

/-- The zero dynamics also satisfies the operator-form realization of its
separator: both `inner(Tx,x)` and `0 * inner(x,x)` are the real zero. -/
def qZeroPinnedFormGap : TransferFormGapResidual qZeroPinnedSpectralGapData where
  scaledInner := fun _ => CReal.RCzero
  form_gap := by
    intro x _
    show CReal.RCle
      (qW.toGNSData.cinnerCompl (embedV qW.toGNSData qW.toGNSData.zero) x)
      CReal.RCzero
    rw [qW.toGNSData.cinnerCompl_embedZero_left]
    exact CReal.RCle_refl CReal.RCzero

/-- The two realized head eigenvalues are exactly incompatible. -/
theorem unit_zero_head_eigen_ne :
    ¬ (unitModel.lam 0 ≈ zeroModel.lam 0) := by
  decide

/-- The complete machine-checked underdetermination witness: two selected
dynamics on the identical static Wilson datum, two actual nonzero head
eigenvectors, unequal operator maps, and unequal eigenvalues. -/
structure IncompatibleWilsonTimeSpectra : Type where
  P : WilsonTimeTranslationPin qW
  Q : WilsonTimeTranslationPin qW
  unit_realized : HeadSpectrumRealization P unitModel
  zero_realized : HeadSpectrumRealization Q zeroModel
  action_ne : P.op.T ≠ Q.op.T
  head_eigen_ne : ¬ (unitModel.lam 0 ≈ zeroModel.lam 0)

/-- `WilsonGNSData` underdetermines the transfer spectrum, inhabited on the
nondegenerate rank-one Wilson datum without adding any axiom. -/
def qWilson_incompatible_time_spectra : IncompatibleWilsonTimeSpectra where
  P := qIdentityPin
  Q := qZeroPin
  unit_realized := unitRealization
  zero_realized := zeroRealization
  action_ne := idTransfer_T_ne_zeroTransfer_T
  head_eigen_ne := unit_zero_head_eigen_ne

/-- The underdetermination witness stated as the two decisive propositions. -/
theorem qWilson_same_static_datum_supports_incompatible_spectra :
    qWilson_incompatible_time_spectra.P.op.T ≠
        qWilson_incompatible_time_spectra.Q.op.T ∧
      ¬ (unitModel.lam 0 ≈ zeroModel.lam 0) :=
  ⟨qWilson_incompatible_time_spectra.action_ne,
    qWilson_incompatible_time_spectra.head_eigen_ne⟩

/-! ## 5. Minimal spectral pin and normalized character gap -/

/-- The additional datum that couples the selected Wilson dynamics to the
normalized finite character spectrum: precisely the physical finite-coordinate
map and its two Schur identities. -/
structure WilsonCharacterSpectrumPin
    {A : ObservableMeasure.ObsAlg} (W : WilsonGNSData A)
    (P : WilsonTimeTranslationPin W)
    (w t : Q') (ht : (0 : Q') <= t) (N : Nat) : Type where
  diagonal : PhysicalWilsonBridge.PhysicalCharacterCoordinateMap
    W.toGNSData.gnsComplete P.op w t ht N

/-- Once a time translation has been selected, its normalized excited-character
model has the constructive located separator `heatKernelSep w < 1`.  This datum
alone records the finite model; the following `formGap` is what couples it to
the selected operator. -/
def WilsonTimeTranslationPin.normalizedCharacterGapData
    {A : ObservableMeasure.ObsAlg} {W : WilsonGNSData A}
    (P : WilsonTimeTranslationPin W)
    {w : Q'} {N : Nat}
    (hw0 : (0 : Q') <= w) (hw1 : w < (1 : Q')) :
    SpectralGapData W.toGNSData.gnsComplete :=
  WilsonSpectralBridge.excitedCharSpectralGapData P.op w hw0 hw1 N

/-- Its located margin is the normalized heat-kernel character margin. -/
theorem WilsonTimeTranslationPin.normalizedCharacter_gapMargin_eq
    {A : ObservableMeasure.ObsAlg} {W : WilsonGNSData A}
    (P : WilsonTimeTranslationPin W)
    {w : Q'} {N : Nat}
    (hw0 : (0 : Q') <= w) (hw1 : w < (1 : Q')) :
    (P.normalizedCharacterGapData (N := N) hw0 hw1).gap.gapMargin =
      (1 : Q') - HeatKernelGap.heatKernelSep w := rfl

/-- The Schur pin couples the normalized character gap to the selected Wilson
operator and yields the actual operator-form bound on the vacuum complement. -/
def WilsonCharacterSpectrumPin.formGap
    {A : ObservableMeasure.ObsAlg} {W : WilsonGNSData A}
    {P : WilsonTimeTranslationPin W}
    {w t : Q'} {ht : (0 : Q') <= t} {N : Nat}
    (M : WilsonCharacterSpectrumPin W P w t ht N)
    (hw0 : (0 : Q') <= w) (hw1 : w < (1 : Q')) :
    TransferFormGapResidual
      (P.normalizedCharacterGapData (N := N) hw0 hw1) :=
  PhysicalWilsonBridge.physicalWilsonFormGap P.op w t ht hw0 hw1 N
    WilsonSchurIdentities.rscale_mono M.diagonal

end YMGap.Continuum.WilsonGNSTransferUnderdetermination

#print axioms YMGap.Continuum.WilsonGNSTransferUnderdetermination.zeroTransfer
#print axioms YMGap.Continuum.WilsonGNSTransferUnderdetermination.qW
#print axioms YMGap.Continuum.WilsonGNSTransferUnderdetermination.qS
#print axioms YMGap.Continuum.WilsonGNSTransferUnderdetermination.qS_toGNSData_eq_qW
#print axioms YMGap.Continuum.WilsonGNSTransferUnderdetermination.embedV_eq_of_veq
#print axioms YMGap.Continuum.WilsonGNSTransferUnderdetermination.qHead_ne_zero
#print axioms YMGap.Continuum.WilsonGNSTransferUnderdetermination.idTransfer_T_ne_zeroTransfer_T
#print axioms YMGap.Continuum.WilsonGNSTransferUnderdetermination.WilsonTimeTranslationPin
#print axioms YMGap.Continuum.WilsonGNSTransferUnderdetermination.WilsonTimeTranslationPin.tau_preserves_rad
#print axioms YMGap.Continuum.WilsonGNSTransferUnderdetermination.WilsonTimeTranslationPin.positive
#print axioms YMGap.Continuum.WilsonGNSTransferUnderdetermination.WilsonTimeTranslationPin.contraction
#print axioms YMGap.Continuum.WilsonGNSTransferUnderdetermination.qIdentityPin
#print axioms YMGap.Continuum.WilsonGNSTransferUnderdetermination.qZeroPin
#print axioms YMGap.Continuum.WilsonGNSTransferUnderdetermination.unitModel
#print axioms YMGap.Continuum.WilsonGNSTransferUnderdetermination.zeroModel
#print axioms YMGap.Continuum.WilsonGNSTransferUnderdetermination.zeroLocatedGap
#print axioms YMGap.Continuum.WilsonGNSTransferUnderdetermination.unitModel_no_located_gap
#print axioms YMGap.Continuum.WilsonGNSTransferUnderdetermination.HeadSpectrumRealization
#print axioms YMGap.Continuum.WilsonGNSTransferUnderdetermination.unitRealization
#print axioms YMGap.Continuum.WilsonGNSTransferUnderdetermination.zeroRealization
#print axioms YMGap.Continuum.WilsonGNSTransferUnderdetermination.qZeroPinnedSpectralGapData
#print axioms YMGap.Continuum.WilsonGNSTransferUnderdetermination.qZeroPinnedFormGap
#print axioms YMGap.Continuum.WilsonGNSTransferUnderdetermination.unit_zero_head_eigen_ne
#print axioms YMGap.Continuum.WilsonGNSTransferUnderdetermination.IncompatibleWilsonTimeSpectra
#print axioms YMGap.Continuum.WilsonGNSTransferUnderdetermination.qWilson_incompatible_time_spectra
#print axioms YMGap.Continuum.WilsonGNSTransferUnderdetermination.qWilson_same_static_datum_supports_incompatible_spectra
#print axioms YMGap.Continuum.WilsonGNSTransferUnderdetermination.WilsonCharacterSpectrumPin
#print axioms YMGap.Continuum.WilsonGNSTransferUnderdetermination.WilsonTimeTranslationPin.normalizedCharacterGapData
#print axioms YMGap.Continuum.WilsonGNSTransferUnderdetermination.WilsonTimeTranslationPin.normalizedCharacter_gapMargin_eq
#print axioms YMGap.Continuum.WilsonGNSTransferUnderdetermination.WilsonCharacterSpectrumPin.formGap
