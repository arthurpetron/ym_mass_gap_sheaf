/-
M4l -- strengthen the selected Wilson form gap to the bounded transfer
operator-norm gap by isolating the one missing square-resolution identity.

`WilsonCharacterOS4Pin` already supplies Parseval for `x` and the diagonal
formula for `<T x,x>`.  Those data yield the canonical linear form gap, but not
the squared-norm estimate `||T x||^2 <= sep^2 ||x||^2`.  The latter needs the
diagonal formula for `<T^2 x,x>` (equivalently, by self-adjointness,
`<T x,T x>`).

The single additional field below completes `BoundedTransferCalculus`'s
`DiagResolution` on the *selected* OS4 spectral record.  The termwise linear
and quadratic eigenvalue bounds are then proved from the existing Casimir
ordering.  No continuum datum or square-resolution inhabitant is constructed.
-/

import YMGap.Continuum.BoundedTransferCalculus
import YMGap.Continuum.WilsonLinkedOSReconstruction

namespace YMGap.Continuum.WilsonOperatorNormGapHandoff

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum
open YMGap.Continuum.BoundedTransferCalculus
open YMGap.Continuum.ContinuumMeasure
open YMGap.Continuum.FourDExistence
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.MeasureLinkedOSReconstruction
open YMGap.Continuum.PhysicalWilsonBridge
open YMGap.Continuum.RGTransport
open YMGap.Continuum.WilsonGNSTransferUnderdetermination
open YMGap.Continuum.WilsonLinkedOSReconstruction
open YMGap.Continuum.WilsonSpectralBridge

/-- The one Schur identity missing from the linear character/OS4 pin: the
selected transfer's squared form is diagonal with eigenvalues `lambda_i^2` in
the same physical character coordinates. -/
structure WilsonCharacterSquarePin
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {D : MeasureLinkedOSGNSData H}
    {W : WilsonGNS.WilsonGNSData H.os_axioms.A}
    {P : WilsonTimeTranslationPin W}
    {w t : Q'} {ht : (0 : Q') <= t} {N : Nat}
    {hw0 : (0 : Q') <= w} {hw1 : w < (1 : Q')}
    (B : WilsonLinkedOSGNSData.WilsonCharacterOS4Pin
      D P ht N hw0 hw1) : Type 2 where
  /-- Diagonal resolution of `<T^2 x,x>` in the coordinates already selected
  by `B.character`. -/
  innerTsq_diag : forall x,
    W.toGNSData.gnsComplete.hilbert.cinner (P.op.T (P.op.T x)) x =
      RCfinSum N (fun i => RCscale
        (qpow w (c4 (i.val + 1)) * qpow w (c4 (i.val + 1)))
        ((physicalCharacterDiagResolution P.op w t ht N
          B.character.diagonal).coeffSq x i))

namespace WilsonCharacterSquarePin

/-- The linear Schur data plus the square identity form the full diagonal
resolution needed for the selected transfer-operator norm gap. -/
def toSelectedDiagResolution
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {D : MeasureLinkedOSGNSData H}
    {W : WilsonGNS.WilsonGNSData H.os_axioms.A}
    {P : WilsonTimeTranslationPin W}
    {w t : Q'} {ht : (0 : Q') <= t} {N : Nat}
    {hw0 : (0 : Q') <= w} {hw1 : w < (1 : Q')}
    {B : WilsonLinkedOSGNSData.WilsonCharacterOS4Pin
      D P ht N hw0 hw1}
    (S : WilsonCharacterSquarePin B) :
    DiagResolution (selectedSpectralGapData D P) :=
  let C := physicalCharacterDiagResolution P.op w t ht N B.character.diagonal
  { k := N
    lam := fun i => qpow w (c4 (i.val + 1))
    coeffSq := C.coeffSq
    coeffSq_nonneg := C.coeffSq_nonneg
    innerSelf_diag := C.parseval_self
    innerT_diag := C.parseval_T
    innerTsq_diag := S.innerTsq_diag
    eigen_le_sep := by
      intro x _hx i
      rw [B.separatorPinned]
      exact WilsonSchurIdentities.rscale_mono
        (casimir_qpow_le hw0 (Q'.le_of_lt hw1) i.val)
        (C.coeffSq_nonneg x i)
    eigenSq_le := by
      intro x _hx i
      rw [B.separatorPinned]
      have hlam : qpow w (c4 (i.val + 1)) <= heatKernelSep w :=
        casimir_qpow_le hw0 (Q'.le_of_lt hw1) i.val
      have hnonneg : (0 : Q') <= qpow w (c4 (i.val + 1)) :=
        qpow_nonneg w hw0 (c4 (i.val + 1))
      have hmul :
          qpow w (c4 (i.val + 1)) * qpow w (c4 (i.val + 1)) <=
            heatKernelSep w * qpow w (c4 (i.val + 1)) :=
        Q'.mul_le_mul_of_nonneg_right _ _ _ hlam hnonneg
      exact WilsonSchurIdentities.rscale_mono hmul
        (C.coeffSq_nonneg x i) }

/-- The genuine bounded-operator gap on the selected Wilson GNS carrier:
`||T x||^2 <= sep^2 ||x||^2` for every vector orthogonal to the selected
vacuum. -/
theorem selectedOperatorNormGap
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {D : MeasureLinkedOSGNSData H}
    {W : WilsonGNS.WilsonGNSData H.os_axioms.A}
    {P : WilsonTimeTranslationPin W}
    {w t : Q'} {ht : (0 : Q') <= t} {N : Nat}
    {hw0 : (0 : Q') <= w} {hw1 : w < (1 : Q')}
    {B : WilsonLinkedOSGNSData.WilsonCharacterOS4Pin
      D P ht N hw0 hw1}
    (S : WilsonCharacterSquarePin B)
    {x : W.toGNSData.gnsComplete.hilbert.carrier}
    (hx : (selectedSpectralGapData D P).vacPerp x) :
    RCle
      (W.toGNSData.gnsComplete.hilbert.cinner (P.op.T x) (P.op.T x))
      (RCscale
        ((selectedSpectralGapData D P).gap.sep *
          (selectedSpectralGapData D P).gap.sep)
        (W.toGNSData.gnsComplete.hilbert.cinner x x)) :=
  diagResolution_normGap S.toSelectedDiagResolution hx

end WilsonCharacterSquarePin

end YMGap.Continuum.WilsonOperatorNormGapHandoff

#print axioms YMGap.Continuum.WilsonOperatorNormGapHandoff.WilsonCharacterSquarePin.toSelectedDiagResolution
#print axioms YMGap.Continuum.WilsonOperatorNormGapHandoff.WilsonCharacterSquarePin.selectedOperatorNormGap
