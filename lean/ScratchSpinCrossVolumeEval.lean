import YMGap.Continuum.Z4SpinSummedTargetCylinderStability

open YMGap.Constructive
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.Z4ParametricPhysicalCutoffPartition
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

def firstSixSpinTwo : EdgeLabelling :=
  fun edge => if edge < 6 then 2 else 0

def firstSixMixed : EdgeLabelling :=
  fun edge =>
    if edge = 0 then 2 else
    if edge = 1 then 2 else
    if edge = 2 then 4 else
    if edge = 3 then 2 else
    if edge = 4 then 4 else
    if edge = 5 then 2 else 0

def twiceUnitCubeSurfaceLabel (n : Nat) : EdgeLabelling :=
  fun edge => 2 * unitCubeSurfaceLabel n edge

#eval! (parametricKPhysicalTerm anchorCoupling 4 1 firstSixSpinTwo).num
#eval! (parametricKPhysicalTerm anchorCoupling 4 1 firstSixSpinTwo).den
#eval! (parametricKPhysicalTerm anchorCoupling 4 2 firstSixSpinTwo).num
#eval! (parametricKPhysicalTerm anchorCoupling 4 2 firstSixSpinTwo).den

#eval! (parametricKPhysicalTerm anchorCoupling 4 1 firstSixMixed).num
#eval! (parametricKPhysicalTerm anchorCoupling 4 1 firstSixMixed).den
#eval! (parametricKPhysicalTerm anchorCoupling 4 2 firstSixMixed).num
#eval! (parametricKPhysicalTerm anchorCoupling 4 2 firstSixMixed).den

#eval! (parametricKPhysicalTerm anchorCoupling 1 2
  (unitCubeSurfaceLabel 2)).num
#eval! (parametricKPhysicalTerm anchorCoupling 1 2
  (unitCubeSurfaceLabel 2)).den
#eval! (parametricKPhysicalTerm anchorCoupling 1 3
  (unitCubeSurfaceLabel 3)).num
#eval! (parametricKPhysicalTerm anchorCoupling 1 3
  (unitCubeSurfaceLabel 3)).den

#eval! (parametricKPhysicalTerm anchorCoupling 2 2
  (twiceUnitCubeSurfaceLabel 2)).num
#eval! (parametricKPhysicalTerm anchorCoupling 2 2
  (twiceUnitCubeSurfaceLabel 2)).den
#eval! (parametricKPhysicalTerm anchorCoupling 2 3
  (twiceUnitCubeSurfaceLabel 3)).num
#eval! (parametricKPhysicalTerm anchorCoupling 2 3
  (twiceUnitCubeSurfaceLabel 3)).den
