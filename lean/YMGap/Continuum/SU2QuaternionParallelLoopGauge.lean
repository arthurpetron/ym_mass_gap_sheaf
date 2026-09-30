/-
# Two parallel paths form a gauge-invariant closed loop

The same endpoint gauges act on both path holonomies. Reversing the second
path makes the common finish gauge cancel, leaving conjugation by the common
start gauge. These are arbitrary-insertion Haar-carrier identities, not
statements about the original interacting slab measure.
-/

import YMGap.Continuum.SU2QuaternionHaarGaugeCancellation

namespace YMGap.Continuum.SU2QuaternionParallelLoopGauge

set_option autoImplicit false

open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionSpinTwoConditionalHaar
open YMGap.Continuum.SU2QuaternionHaarGaugeCancellation

local infixl:70 " *q " => PolyQuaternion.mul
local prefix:80 "bar " => PolyQuaternion.conj

/-- Two parallel paths close after reversing the second path. The finish
gauge cancels while the start gauge remains as a closed conjugation. -/
theorem parallel_loop_gauge_word {blocks : Nat}
    (start finish u v : PolyQuaternion)
    (hfinish : HaarCarrierEqv blocks (polyQuaternionNorm finish) polyOne) :
    PolyQuaternionHaarCarrierEqv blocks
      (gaugeLink start u finish *q bar (gaugeLink start v finish))
      (gaugeLink start (u *q bar v) start) :=
  ((PolyQuaternionHaarCarrierEqv.refl blocks (gaugeLink start u finish)).mul
    (PolyQuaternionHaarCarrierEqv.of_coeff (gaugeLink_conj start v finish))).trans
      (gaugeLink_compose hfinish start u (bar v) start)

/-- The scalar of the parallel-path Wilson loop is gauge invariant in the
same arbitrary-insertion Haar carrier. -/
theorem parallel_loop_gauge_scalar {blocks : Nat}
    (start finish u v : PolyQuaternion)
    (hstart : HaarCarrierEqv blocks (polyQuaternionNorm start) polyOne)
    (hfinish : HaarCarrierEqv blocks (polyQuaternionNorm finish) polyOne) :
    HaarCarrierEqv blocks
      (gaugeLink start u finish *q bar (gaugeLink start v finish)).scalar
      (u *q bar v).scalar :=
  HaarCarrierEqv.trans (parallel_loop_gauge_word start finish u v hfinish).scalar
    (gaugeLink_closed_scalar hstart (u *q bar v))

/-- Every retained spin character of the closed parallel-path holonomy is
gauge invariant under the same two endpoint transformations. -/
theorem parallel_loop_gauge_character {blocks : Nat}
    (start finish u v : PolyQuaternion)
    (hstart : HaarCarrierEqv blocks (polyQuaternionNorm start) polyOne)
    (hfinish : HaarCarrierEqv blocks (polyQuaternionNorm finish) polyOne)
    (spin : Nat) :
    HaarCarrierEqv blocks
      (characterPolynomial
        (gaugeLink start u finish *q bar (gaugeLink start v finish)).scalar spin)
      (characterPolynomial (u *q bar v).scalar spin) :=
  character_haar_congr
    (parallel_loop_gauge_scalar start finish u v hstart hfinish) spin

#print axioms parallel_loop_gauge_word
#print axioms parallel_loop_gauge_scalar
#print axioms parallel_loop_gauge_character

end YMGap.Continuum.SU2QuaternionParallelLoopGauge
