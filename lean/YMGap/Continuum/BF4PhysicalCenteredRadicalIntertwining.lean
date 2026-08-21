/-
# Exact physical centering intertwines modulo the BF4 GNS radical

Finite BF4 observables can be centered by subtracting their exact stationary
rational mean.  Constants are fixed by the physical Markov kernel only on the
retained positive-marginal rows, so centering does not commute pointwise with
the literal Markov action on the entire function carrier.  It does commute in
the physical GNS quotient.

This file proves the precise carrier-level statement.  Radical-equivalent raw
realizations remain radical-equivalent after centering, and the Markov action
of a centered observable is radical-equivalent to the centered Markov action.
No thermodynamic or continuum limit is asserted here.
-/

import YMGap.Continuum.BF4PhysicalCompletedCenteredFormGap

namespace YMGap.Continuum.BF4PhysicalCenteredRadicalIntertwining

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4PhysicalCompletedCenteredFormGap
open YMGap.Continuum.BF4PhysicalCompletedMacroCorrelator
open YMGap.Continuum.BF4PhysicalMarkovGNSCompletion
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.HamiltonianScalar
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

local infix:50 " ≈ " => Q'.eqv

/-- Scaling preserves the physical GNS radical. -/
theorem centralPhysical_rad_smul
    (w : Q') (hw : (0 : Q') <= w) (K half : Nat)
    (scalar : Q') {a b : EdgeLabelling -> Q'}
    (hab : (centralPhysicalSmulGNS w hw K half).toGNSData.rad a b) :
    (centralPhysicalSmulGNS w hw K half).toGNSData.rad
      ((centralPhysicalSmulGNS w hw K half).toGNSData.smul scalar a)
      ((centralPhysicalSmulGNS w hw K half).toGNSData.smul scalar b) := by
  let D := (centralPhysicalSmulGNS w hw K half).toGNSData
  change D.distSqQ (D.smul scalar a) (D.smul scalar b) ≈ 0
  exact Q'.eqv_trans _ _ _
    ((centralPhysicalSmulGNS w hw K half).distSqQ_smul scalar a b)
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (scalar * scalar) _ _ hab)
      (Q'.mul_zero_eqv (scalar * scalar)))

/-- Radical-equivalent physical observables have the same stationary mean.
This is the finite GNS statement that the mean is pairing with the vacuum. -/
theorem centralPhysicalStationaryMean_eqv_of_rad
    (w : Q') (hw : (0 : Q') <= w) (K half : Nat)
    {a b : EdgeLabelling -> Q'}
    (hab : (centralPhysicalSmulGNS w hw K half).toGNSData.rad a b) :
    centralPhysicalStationaryMean w hw K half a ≈
      centralPhysicalStationaryMean w hw K half b := by
  let D := (centralPhysicalSmulGNS w hw K half).toGNSData
  have hinner : D.B a centralPhysicalVacuumCarrier ≈
      D.B b centralPhysicalVacuumCarrier :=
    D.B_welldef hab (D.rad_refl centralPhysicalVacuumCarrier)
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (centralPhysicalWeightedInner_vacuum_right w hw K half a))
    (Q'.eqv_trans _ _ _ hinner
      (centralPhysicalWeightedInner_vacuum_right w hw K half b))

/-- Exact stationary centering respects pointwise physical carrier
equivalence. -/
theorem centralPhysicalCenteredObservable_congr
    (w : Q') (hw : (0 : Q') <= w) (K half : Nat)
    {a b : EdgeLabelling -> Q'}
    (hab : (centralPhysicalSmulGNS w hw K half).toGNSData.veq a b) :
    (centralPhysicalSmulGNS w hw K half).toGNSData.veq
      (centralPhysicalCenteredObservable w hw K half a)
      (centralPhysicalCenteredObservable w hw K half b) := by
  let D := (centralPhysicalSmulGNS w hw K half).toGNSData
  have hmean :
      centralPhysicalStationaryMean w hw K half a ≈
        centralPhysicalStationaryMean w hw K half b :=
    centralPhysicalStationaryMean_eqv_of_rad w hw K half
      (rad_of_veq D hab)
  intro state
  unfold centralPhysicalCenteredObservable
  exact Q'.add_eqv_congr' (hab state)
    (Q'.neg_eqv_congr _ _ hmean)

/-- Exact stationary centering respects physical radical equivalence. -/
theorem centralPhysicalCenteredObservable_rad_congr
    (w : Q') (hw : (0 : Q') <= w) (K half : Nat)
    {a b : EdgeLabelling -> Q'}
    (hab : (centralPhysicalSmulGNS w hw K half).toGNSData.rad a b) :
    (centralPhysicalSmulGNS w hw K half).toGNSData.rad
      (centralPhysicalCenteredObservable w hw K half a)
      (centralPhysicalCenteredObservable w hw K half b) := by
  let D := (centralPhysicalSmulGNS w hw K half).toGNSData
  let meanA := centralPhysicalStationaryMean w hw K half a
  let meanB := centralPhysicalStationaryMean w hw K half b
  have hmean : meanA ≈ meanB :=
    centralPhysicalStationaryMean_eqv_of_rad w hw K half hab
  have hscaledVeq : D.veq
      (D.smul meanA centralPhysicalVacuumCarrier)
      (D.smul meanB centralPhysicalVacuumCarrier) := by
    intro state
    exact Q'.mul_eqv_congr_right meanA meanB
      (centralPhysicalVacuumCarrier state) hmean
  have hscaled : D.rad
      (D.smul meanA centralPhysicalVacuumCarrier)
      (D.smul meanB centralPhysicalVacuumCarrier) :=
    rad_of_veq D hscaledVeq
  have hsub : D.rad
      (D.sub a (D.smul meanA centralPhysicalVacuumCarrier))
      (D.sub b (D.smul meanB centralPhysicalVacuumCarrier)) :=
    D.rad_add hab (D.rad_neg hscaled)
  have hleft : D.rad
      (centralPhysicalCenteredObservable w hw K half a)
      (D.sub a (D.smul meanA centralPhysicalVacuumCarrier)) :=
    rad_of_veq D
      (centralPhysicalCenteredObservable_veq_sub_smul w hw K half a)
  have hright : D.rad
      (D.sub b (D.smul meanB centralPhysicalVacuumCarrier))
      (centralPhysicalCenteredObservable w hw K half b) :=
    D.rad_symm
      (rad_of_veq D
        (centralPhysicalCenteredObservable_veq_sub_smul w hw K half b))
  exact D.rad_trans hleft (D.rad_trans hsub hright)

/-- The literal finite physical Markov action commutes with exact stationary
centering modulo the physical GNS radical.  This is the sound replacement for
the false pointwise identity on discarded zero-marginal rows. -/
theorem centralPhysicalMarkovApply_centered_rad
    (w : Q') (hw : (0 : Q') <= w) (K half : Nat)
    (observable : EdgeLabelling -> Q') :
    (centralPhysicalSmulGNS w hw K half).toGNSData.rad
      (centralPhysicalMarkovApply w hw K half
        (centralPhysicalCenteredObservable w hw K half observable))
      (centralPhysicalCenteredObservable w hw K half
        (centralPhysicalMarkovApply w hw K half observable)) := by
  let D := (centralPhysicalSmulGNS w hw K half).toGNSData
  let mean := centralPhysicalStationaryMean w hw K half observable
  let transferred := centralPhysicalMarkovApply w hw K half observable
  have hcenter : D.veq
      (centralPhysicalCenteredObservable w hw K half observable)
      (D.sub observable (D.smul mean centralPhysicalVacuumCarrier)) :=
    centralPhysicalCenteredObservable_veq_sub_smul
      w hw K half observable
  have hmarkovCenter : D.veq
      (centralPhysicalMarkovApply w hw K half
        (centralPhysicalCenteredObservable w hw K half observable))
      (centralPhysicalMarkovApply w hw K half
        (D.sub observable (D.smul mean centralPhysicalVacuumCarrier))) :=
    centralPhysicalMarkovApply_congr w hw K half hcenter
  have hmarkovSub : D.veq
      (centralPhysicalMarkovApply w hw K half
        (D.sub observable (D.smul mean centralPhysicalVacuumCarrier)))
      (D.sub transferred
        (centralPhysicalMarkovApply w hw K half
          (D.smul mean centralPhysicalVacuumCarrier))) :=
    centralPhysicalMarkovApply_sub w hw K half observable
      (D.smul mean centralPhysicalVacuumCarrier)
  have hmarkovSmul : D.veq
      (centralPhysicalMarkovApply w hw K half
        (D.smul mean centralPhysicalVacuumCarrier))
      (D.smul mean
        (centralPhysicalMarkovApply w hw K half
          centralPhysicalVacuumCarrier)) :=
    centralPhysicalMarkovApply_smul w hw K half mean
      centralPhysicalVacuumCarrier
  have hlinear : D.veq
      (centralPhysicalMarkovApply w hw K half
        (centralPhysicalCenteredObservable w hw K half observable))
      (D.sub transferred
        (D.smul mean
          (centralPhysicalMarkovApply w hw K half
            centralPhysicalVacuumCarrier))) := by
    exact D.veq_trans hmarkovCenter
      (D.veq_trans hmarkovSub
        (D.add_congr (D.veq_refl transferred) (D.neg_congr hmarkovSmul)))
  have hlinearRad : D.rad
      (centralPhysicalMarkovApply w hw K half
        (centralPhysicalCenteredObservable w hw K half observable))
      (D.sub transferred
        (D.smul mean
          (centralPhysicalMarkovApply w hw K half
            centralPhysicalVacuumCarrier))) :=
    rad_of_veq D hlinear
  have hvacuumScaled : D.rad
      (D.smul mean
        (centralPhysicalMarkovApply w hw K half
          centralPhysicalVacuumCarrier))
      (D.smul mean centralPhysicalVacuumCarrier) :=
    centralPhysical_rad_smul w hw K half mean
      (centralPhysicalVacuumCarrier_rad_fixed w hw K half)
  have hfixedMean : D.rad
      (D.sub transferred
        (D.smul mean
          (centralPhysicalMarkovApply w hw K half
            centralPhysicalVacuumCarrier)))
      (D.sub transferred (D.smul mean centralPhysicalVacuumCarrier)) :=
    D.rad_add (D.rad_refl transferred) (D.rad_neg hvacuumScaled)
  have hstationary :
      centralPhysicalStationaryMean w hw K half transferred ≈ mean :=
    centralPhysicalStationaryMean_markovApply
      w hw K half observable
  have hmeanScaledVeq : D.veq
      (D.smul mean centralPhysicalVacuumCarrier)
      (D.smul
        (centralPhysicalStationaryMean w hw K half transferred)
        centralPhysicalVacuumCarrier) := by
    intro state
    exact Q'.mul_eqv_congr_right mean
      (centralPhysicalStationaryMean w hw K half transferred)
      (centralPhysicalVacuumCarrier state) (Q'.eqv_symm hstationary)
  have hmeanScaled : D.rad
      (D.smul mean centralPhysicalVacuumCarrier)
      (D.smul
        (centralPhysicalStationaryMean w hw K half transferred)
        centralPhysicalVacuumCarrier) :=
    rad_of_veq D hmeanScaledVeq
  have hcorrectMean : D.rad
      (D.sub transferred (D.smul mean centralPhysicalVacuumCarrier))
      (D.sub transferred
        (D.smul
          (centralPhysicalStationaryMean w hw K half transferred)
          centralPhysicalVacuumCarrier)) :=
    D.rad_add (D.rad_refl transferred) (D.rad_neg hmeanScaled)
  have hcenteredTarget : D.rad
      (D.sub transferred
        (D.smul
          (centralPhysicalStationaryMean w hw K half transferred)
          centralPhysicalVacuumCarrier))
      (centralPhysicalCenteredObservable w hw K half transferred) :=
    D.rad_symm
      (rad_of_veq D
        (centralPhysicalCenteredObservable_veq_sub_smul
          w hw K half transferred))
  exact D.rad_trans hlinearRad
    (D.rad_trans hfixedMean
      (D.rad_trans hcorrectMean hcenteredTarget))

/-- A raw finite realization intertwining modulo the physical radical induces
the centered intertwining needed by the graph-norm compiler. -/
theorem centralPhysicalCenteredTransfer_rad_of_raw
    (w : Q') (hw : (0 : Q') <= w) (K half : Nat)
    (source target : EdgeLabelling -> Q')
    (hraw : (centralPhysicalSmulGNS w hw K half).toGNSData.rad
      (centralPhysicalMarkovApply w hw K half source) target) :
    (centralPhysicalSmulGNS w hw K half).toGNSData.rad
      (centralPhysicalMarkovApply w hw K half
        (centralPhysicalCenteredObservable w hw K half source))
      (centralPhysicalCenteredObservable w hw K half target) := by
  let D := (centralPhysicalSmulGNS w hw K half).toGNSData
  exact D.rad_trans
    (centralPhysicalMarkovApply_centered_rad w hw K half source)
    (centralPhysicalCenteredObservable_rad_congr w hw K half hraw)

end YMGap.Continuum.BF4PhysicalCenteredRadicalIntertwining

#print axioms YMGap.Continuum.BF4PhysicalCenteredRadicalIntertwining.centralPhysical_rad_smul
#print axioms YMGap.Continuum.BF4PhysicalCenteredRadicalIntertwining.centralPhysicalStationaryMean_eqv_of_rad
#print axioms YMGap.Continuum.BF4PhysicalCenteredRadicalIntertwining.centralPhysicalCenteredObservable_congr
#print axioms YMGap.Continuum.BF4PhysicalCenteredRadicalIntertwining.centralPhysicalCenteredObservable_rad_congr
#print axioms YMGap.Continuum.BF4PhysicalCenteredRadicalIntertwining.centralPhysicalMarkovApply_centered_rad
#print axioms YMGap.Continuum.BF4PhysicalCenteredRadicalIntertwining.centralPhysicalCenteredTransfer_rad_of_raw
