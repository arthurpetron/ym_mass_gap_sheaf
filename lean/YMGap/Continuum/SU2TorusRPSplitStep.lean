/-
# Torus RP (d4e): one concrete crossing-link split on the torus integrand

`split_step`: for a left/inverse selected shear (selected `s` = crossing link block, multiplier `m` = a block not
otherwise used), `∫_{n} Π_ps T_K = ∫_{n} Π_ps T_K[U_s ↦ U_m* U_s]`. Unconditional in degree (all-degree selected Haar
translation), needs only block support.

**RP FOR THE ACTUAL TORUS MEASURE IS OPEN.**
-/

import YMGap.Continuum.SU2TorusRPSplitTK

namespace YMGap.Continuum.SU2TorusRPSplitStep

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2HaarL1Activity (prodPoly)
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4TorusGeometry
open YMGap.Continuum.SU2QuaternionSelectedHaarTranslationChain
open YMGap.Continuum.SU2TorusRPSplitTK (plaqIdx imgTK split_prod_haar)
open PolyQuaternion (mul conj)

/-- Coordinate image of a left/inverse split shear. -/
def stepImg (s m : Nat) (b : Nat) : PolyQuaternion :=
  if b = s then mul (conj (PolyQuaternion.coordinateVariable m)) (PolyQuaternion.coordinateVariable s)
  else PolyQuaternion.coordinateVariable b

theorem split_step {tailBlocks : Nat} (hb : 0 < tailBlocks) (step : SelectedTranslationStep tailBlocks)
    (hside : step.side = .left) (hor : step.multiplierOrientation = .inverse)
    (links : List Z4Link) (N : Nat) (β : Q') (K : Nat) (ps : List Z4Plaq)
    (hsup : YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini.SupportedQuaternionBlocks (tailBlocks + 1)
      (prodPoly (YMGap.Continuum.SU2WilsonPolymerIdentity.TK links N β K) ps))
    (hps : ∀ p ∈ ps, ∀ b ∈ plaqIdx links N p, b < tailBlocks + 1) :
    (quaternionHaar (tailBlocks + 1) (prodPoly (YMGap.Continuum.SU2WilsonPolymerIdentity.TK links N β K) ps)).eqv
      (quaternionHaar (tailBlocks + 1) (prodPoly (imgTK links N β K (stepImg step.selected step.multiplier)) ps)) := by
  refine split_prod_haar links N β K (YMGap.Continuum.SU2TorusRPStepSub.steps_ringSub hb [step]) ps
    (YMGap.Continuum.SU2QuaternionAllDegreeHaarTranslationChain.applySelectedTranslationSteps_haar hb [step] _ hsup)
    _ (fun b hbl => ?_) hps
  unfold stepImg
  by_cases h : b = step.selected
  · rw [if_pos h]; subst h
    exact YMGap.Continuum.SU2TorusRPStepCoord.step_coord_sel hb step hside hor
  · rw [if_neg h]
    exact YMGap.Continuum.SU2TorusRPStepCoord.step_coord_other hb step b hbl h

end YMGap.Continuum.SU2TorusRPSplitStep

#print axioms YMGap.Continuum.SU2TorusRPSplitStep.split_step
