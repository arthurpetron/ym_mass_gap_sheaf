/-
Strengthen the legacy transfer form-gap residual by fixing its right-hand side
to the actual constructive-real scalar multiple of the Hilbert norm.

`TransferFormGapResidual` carries an arbitrary map named `scaledInner`; its
docstring says that the map stands for `sep * inner`, but the type does not
enforce that statement.  The canonical structure below removes that freedom:

    <T x, x> <= RCscale sep <x, x>.

It projects to the legacy residual for compatibility.  A finite spectral
resolution using the already constructed concrete `RCscale` supplies the
canonical structure directly.
-/

import YMGap.Continuum.RCScaleClose

namespace YMGap.Continuum.CanonicalTransferFormGap

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.HamiltonianScalar
open YMGap.Continuum.RCScaleClose

/-- The operator-form gap with its scale fixed definitionally to the concrete
constructive-real scalar action. -/
structure CanonicalTransferFormGap
    {D : GNSData} {H : CompleteGNSHilbert D}
    (G : SpectralGapData H) : Type where
  form_gap : forall {x : H.hilbert.carrier}, G.vacPerp x ->
    CReal.RCle (H.hilbert.cinner (G.op.T x) x)
      (CReal.RCscale G.gap.sep (H.hilbert.cinner x x))

namespace CanonicalTransferFormGap

/-- Forget the definitional scaling equation and recover the legacy residual
interface. -/
def toResidual
    {D : GNSData} {H : CompleteGNSHilbert D}
    {G : SpectralGapData H}
    (F : CanonicalTransferFormGap G) : TransferFormGapResidual G where
  scaledInner := fun x => CReal.RCscale G.gap.sep (H.hilbert.cinner x x)
  form_gap := F.form_gap

end CanonicalTransferFormGap

/-- A finite spectral resolution with the concrete `RCscale` produces the
canonical, not merely nominal, operator-form gap. -/
def HamiltonianScalar.TransferSpectralBridge.toCanonicalFormGap
    {D : GNSData} {H : CompleteGNSHilbert D}
    {G : SpectralGapData H}
    (Br : TransferSpectralBridge G rcScaleResidualPlus) :
    CanonicalTransferFormGap G where
  form_gap := by
    intro x hx
    exact Br.toFormGapResidual.form_gap hx

end YMGap.Continuum.CanonicalTransferFormGap

#print axioms YMGap.Continuum.CanonicalTransferFormGap.CanonicalTransferFormGap.toResidual
#print axioms YMGap.Continuum.CanonicalTransferFormGap.HamiltonianScalar.TransferSpectralBridge.toCanonicalFormGap
