/-
M4p -- matrix-coefficient decay from the iterated Wilson norm gap.

`WilsonIteratedNormDecayHandoff` proves the squared-norm estimate

  ||T^n x||^2 <= (sep^2)^n ||x||^2

on the selected vacuum complement.  RC-valued Cauchy--Schwarz bounds the
square of `<T^n x,y>` by `||T^n x||^2 ||y||^2`.  The only glue needed is
monotonicity of `RCmul` by a nonnegative factor.  That law is proved here by
descending the existing constructive `CReal.leEv_mul_nonneg_left` theorem to
the real quotient.

The result is the bounded-transfer matrix-coefficient decay estimate.  It does
not identify a particular coefficient with a local connected OS correlator;
that remains a separate same-object analytic handoff.
-/

import YMGap.Continuum.FCNormBoundLimit
import YMGap.Continuum.WilsonIteratedNormDecayHandoff

namespace YMGap.Constructive.CReal

/-- Multiplication in the real quotient is monotone in the right input when
the left factor is nonnegative. -/
theorem RCmul_mono_nonneg_left {F a b : RC}
    (hF : RCnonneg F) (hab : RCle a b) :
    RCle (RCmul F a) (RCmul F b) := by
  refine Quotient.inductionOn₃ F a b ?_ hF hab
  intro f x y hf hxy
  exact leEv_mul_nonneg_left hf hxy

end YMGap.Constructive.CReal

namespace YMGap.Continuum.WilsonMatrixCoefficientDecayHandoff

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum
open YMGap.Continuum.BoundedTransferCalculus
open YMGap.Continuum.ContinuumMeasure
open YMGap.Continuum.FourDExistence
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.WilsonIteratedNormDecayHandoff
open YMGap.Continuum.WilsonMinimalBoundedMassGapHandoff

namespace WilsonIteratedBoundedMassGap

/-- Squared matrix coefficients decay at the same geometric rate as the
iterated norm.  Only the propagated vector `x` must lie in `Omega^perp`; the
test vector `y` is arbitrary. -/
theorem matrixCoefficientSqDecay
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {D : WilsonSelectedOSGNSData H}
    (G : WilsonIteratedBoundedMassGap D)
    (n : Nat)
    {x : D.wilson.toGNSData.gnsComplete.hilbert.carrier}
    (hx : D.selectedSpectralData.vacPerp x)
    (y : D.wilson.toGNSData.gnsComplete.hilbert.carrier) :
    RCle
      (RCmul
        (D.wilson.toGNSData.gnsComplete.hilbert.cinner
          (Tpow D.timeTranslation.op n x) y)
        (D.wilson.toGNSData.gnsComplete.hilbert.cinner
          (Tpow D.timeTranslation.op n x) y))
      (RCmul
        (RCscale
          ((D.selectedSpectralData.gap.sep *
              D.selectedSpectralData.gap.sep) ^ n)
          (D.wilson.toGNSData.gnsComplete.hilbert.cinner x x))
        (D.wilson.toGNSData.gnsComplete.hilbert.cinner y y)) := by
  let z := Tpow D.timeTranslation.op n x
  have hcs := D.wilson.toGNSData.RC_cauchy_schwarz z y
  have hnorm := G.iteratedNormGap n hx
  change RCle
    (D.wilson.toGNSData.cinnerCompl z z)
    (RCscale
      ((D.selectedSpectralData.gap.sep *
          D.selectedSpectralData.gap.sep) ^ n)
      (D.wilson.toGNSData.cinnerCompl x x)) at hnorm
  have hyNonneg := D.wilson.toGNSData.cinner_self_nonneg y
  have hmul := RCmul_mono_nonneg_left hyNonneg hnorm
  refine RCle_trans hcs ?_
  change RCle
    (RCmul
      (D.wilson.toGNSData.cinnerCompl z z)
      (D.wilson.toGNSData.cinnerCompl y y))
    (RCmul
      (RCscale
        ((D.selectedSpectralData.gap.sep *
            D.selectedSpectralData.gap.sep) ^ n)
        (D.wilson.toGNSData.cinnerCompl x x))
      (D.wilson.toGNSData.cinnerCompl y y))
  rw [RCmul_comm
    (D.wilson.toGNSData.cinnerCompl z z)
    (D.wilson.toGNSData.cinnerCompl y y),
    RCmul_comm
      (RCscale
        ((D.selectedSpectralData.gap.sep *
            D.selectedSpectralData.gap.sep) ^ n)
        (D.wilson.toGNSData.cinnerCompl x x))
      (D.wilson.toGNSData.cinnerCompl y y)]
  exact hmul

/-- Autocorrelation is the diagonal specialization of the matrix-coefficient
bound. -/
theorem autocorrelationSqDecay
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {D : WilsonSelectedOSGNSData H}
    (G : WilsonIteratedBoundedMassGap D)
    (n : Nat)
    {x : D.wilson.toGNSData.gnsComplete.hilbert.carrier}
    (hx : D.selectedSpectralData.vacPerp x) :
    RCle
      (RCmul
        (D.wilson.toGNSData.gnsComplete.hilbert.cinner
          (Tpow D.timeTranslation.op n x) x)
        (D.wilson.toGNSData.gnsComplete.hilbert.cinner
          (Tpow D.timeTranslation.op n x) x))
      (RCmul
        (RCscale
          ((D.selectedSpectralData.gap.sep *
              D.selectedSpectralData.gap.sep) ^ n)
          (D.wilson.toGNSData.gnsComplete.hilbert.cinner x x))
        (D.wilson.toGNSData.gnsComplete.hilbert.cinner x x)) :=
  matrixCoefficientSqDecay G n hx x

end WilsonIteratedBoundedMassGap

end YMGap.Continuum.WilsonMatrixCoefficientDecayHandoff

#print axioms YMGap.Constructive.CReal.RCmul_mono_nonneg_left
#print axioms YMGap.Continuum.WilsonMatrixCoefficientDecayHandoff.WilsonIteratedBoundedMassGap.matrixCoefficientSqDecay
#print axioms YMGap.Continuum.WilsonMatrixCoefficientDecayHandoff.WilsonIteratedBoundedMassGap.autocorrelationSqDecay
