/-
# Finite-prefix response floor for a same-object completed channel

Every supplied dynamic same-object channel already carries a strictly positive
rational norm floor at each scale.  This module takes the constructive minimum
over a finite scale prefix and transports it to the literal completed
zero-time connected autocorrelation.  It is a finite-regulator survival
certificate only: no all-scale response floor or continuum excitation is
asserted.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
`noncomputable` declaration is used.
-/

import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorSameObjectRCChannel
import YMGap.Continuum.BF4PhysicalChangingNomeDynamicFamily
import YMGap.Continuum.WindowedSpacingFloor

namespace YMGap.Continuum.BF4PhysicalDynamicVacuumSectorFinitePrefixResponse

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalChangingNomeDynamicFamily
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorSameObjectRCChannel
open YMGap.Continuum.WindowedSpacingFloor

structure FinitePrefixResponseFloor
    {half : Nat}
    {family : DynamicVacuumSectorCompletedFamily half}
    (channel : DynamicVacuumSectorSameObjectRCChannel family)
    (bound : Nat) : Type 1 where
  floor : Q'
  floor_pos : (0 : Q') < floor
  lowerNorm : ∀ scale, scale ≤ bound →
    CReal.RCle
      (Quotient.mk CReal.crealSetoid (CReal.ofQ' floor))
      (channel.normSq scale)

def finitePrefixResponseFloor
    {half : Nat}
    {family : DynamicVacuumSectorCompletedFamily half}
    (channel : DynamicVacuumSectorSameObjectRCChannel family)
    (bound : Nat) : Q' :=
  finMin channel.normFloor bound

theorem finitePrefixResponseFloor_pos
    {half : Nat}
    {family : DynamicVacuumSectorCompletedFamily half}
    (channel : DynamicVacuumSectorSameObjectRCChannel family)
    (bound : Nat) :
    (0 : Q') < finitePrefixResponseFloor channel bound := by
  unfold finitePrefixResponseFloor
  exact finMin_pos channel.normFloor channel.normFloor_pos bound

def finitePrefixResponseCertificate
    {half : Nat}
    {family : DynamicVacuumSectorCompletedFamily half}
    (channel : DynamicVacuumSectorSameObjectRCChannel family)
    (bound : Nat) :
    FinitePrefixResponseFloor channel bound where
  floor := finitePrefixResponseFloor channel bound
  floor_pos := finitePrefixResponseFloor_pos channel bound
  lowerNorm := by
    intro scale hscale
    have hmin : finitePrefixResponseFloor channel bound ≤
        channel.normFloor scale :=
      finMin_le channel.normFloor bound scale hscale
    refine CReal.RCle_trans ?_ (channel.normFloor_le_normSq scale)
    rw [CReal.RCle_mk]
    exact CReal.leEv_of_le (CReal.ofQ'_le_ofQ' hmin)

theorem finitePrefixResponseFloor_le_zeroTime
    {half : Nat}
    {family : DynamicVacuumSectorCompletedFamily half}
    (channel : DynamicVacuumSectorSameObjectRCChannel family)
    (bound scale : Nat) (hscale : scale ≤ bound) :
    CReal.RCle
      (Quotient.mk CReal.crealSetoid
        (CReal.ofQ' (finitePrefixResponseFloor channel bound)))
      (channel.connectedAutocorrelation scale 0) := by
  rw [channel.connectedAutocorrelation_zero_eq_normSq scale]
  exact (finitePrefixResponseCertificate channel bound).lowerNorm scale hscale

def changingNomeFinitePrefixResponseCertificate
    (bound : Nat) :
    FinitePrefixResponseFloor changingNomeMovingCubeChannel bound :=
  finitePrefixResponseCertificate changingNomeMovingCubeChannel bound

theorem changingNomeFinitePrefixResponseFloor_pos (bound : Nat) :
    (0 : Q') <
      finitePrefixResponseFloor changingNomeMovingCubeChannel bound :=
  finitePrefixResponseFloor_pos changingNomeMovingCubeChannel bound

theorem changingNomeFinitePrefixResponseFloor_le_zeroTime
    (bound scale : Nat) (hscale : scale ≤ bound) :
    CReal.RCle
      (Quotient.mk CReal.crealSetoid
        (CReal.ofQ'
          (finitePrefixResponseFloor changingNomeMovingCubeChannel bound)))
      (changingNomeMovingCubeChannel.connectedAutocorrelation scale 0) :=
  finitePrefixResponseFloor_le_zeroTime
    changingNomeMovingCubeChannel bound scale hscale

end YMGap.Continuum.BF4PhysicalDynamicVacuumSectorFinitePrefixResponse

#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorFinitePrefixResponse.finitePrefixResponseCertificate
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorFinitePrefixResponse.finitePrefixResponseFloor_le_zeroTime
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorFinitePrefixResponse.changingNomeFinitePrefixResponseCertificate
