/-
# Torus RP (d4c): action of one split shear on link coordinates

For a left/inverse selected shear `step` (selected `s`, multiplier `m`):
* `step_coord_sel`: `U_s ↦ U_m* · U_s` (up to QPE);
* `step_coord_other`: `U_b ↦ U_b` for `b ≠ s`.
Together with `steps_ringSub` and `TK_word_sub`, the shear maps every crossing plaquette word to its split
form `(ΘB)* B …` with `ΘB := U_m` a fresh block. This is the concrete crossing split, one link at a time.

**RP FOR THE ACTUAL TORUS MEASURE IS OPEN.**
-/

import YMGap.Continuum.SU2TorusRPStepSub
import YMGap.Continuum.SU2QuaternionTranslationCoordinateCoefficients

namespace YMGap.Continuum.SU2TorusRPStepCoord

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.SU2HaarAlgebra (PE pe_refl pe_trans)
open YMGap.Continuum.SU2QuaternionSelectedHaarTranslationChain
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2TorusRPSubst (RingSub QPE qsub qpe_trans qmul_sub qconj_sub qpe_mul qpe_conj)
open YMGap.Continuum.SU2QuaternionInverseTranslationCoordinates (coordinateImage)

theorem qpe_of_coeff (n : Nat) {q r : PolyQuaternion} (h : PolyQuaternionCoeffEqv q r) : QPE n q r :=
  ⟨YMGap.Continuum.SU2TorusRPKernel.pe_of_coeff n h.scalar, YMGap.Continuum.SU2TorusRPKernel.pe_of_coeff n h.iPart,
   YMGap.Continuum.SU2TorusRPKernel.pe_of_coeff n h.jPart, YMGap.Continuum.SU2TorusRPKernel.pe_of_coeff n h.kPart⟩

abbrev idR (n : Nat) : RatPoly → RatPoly :=
  YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection.reindexQuaternionPolynomial
    (identityQuaternionBlockInvolution n)

theorem id_coord (n b : Nat) (hb : b < n) :
    QPE n (qsub (idR n) (PolyQuaternion.coordinateVariable b)) (PolyQuaternion.coordinateVariable b) :=
  YMGap.Continuum.SU2TorusRPReindex.reindex_coord _ b hb

theorem step_coord_raw {tailBlocks : Nat} (hb : 0 < tailBlocks) (step : SelectedTranslationStep tailBlocks)
    (b : Nat) (hbl : b < tailBlocks + 1) :
    QPE (tailBlocks + 1) (qsub (applySelectedTranslationSteps hb [step]) (PolyQuaternion.coordinateVariable b))
      (qsub (idR (tailBlocks + 1)) (coordinateImage step b)) :=
  qpe_of_coeff _ (YMGap.Continuum.SU2QuaternionTranslationCoordinateCoefficients.applySelectedTranslationStep_coordinate_coeffEqv
    hb step b hbl)

theorem step_coord_sel {tailBlocks : Nat} (hb : 0 < tailBlocks) (step : SelectedTranslationStep tailBlocks)
    (hside : step.side = .left) (hor : step.multiplierOrientation = .inverse) :
    QPE (tailBlocks + 1) (qsub (applySelectedTranslationSteps hb [step])
        (PolyQuaternion.coordinateVariable step.selected))
      (PolyQuaternion.mul (PolyQuaternion.conj (PolyQuaternion.coordinateVariable step.multiplier))
        (PolyQuaternion.coordinateVariable step.selected)) := by
  have h := step_coord_raw hb step step.selected step.selected_lt
  have himg : coordinateImage step step.selected =
      PolyQuaternion.mul (PolyQuaternion.conj (PolyQuaternion.coordinateVariable step.multiplier))
        (PolyQuaternion.coordinateVariable step.selected) := by
    unfold coordinateImage; rw [if_pos rfl, hside, hor]
  rw [himg] at h
  have hR := YMGap.Continuum.SU2TorusRPReindex.reindex_ringSub (identityQuaternionBlockInvolution (tailBlocks + 1))
  exact qpe_trans h (qpe_trans (qmul_sub hR _ _) (qpe_mul (qpe_trans (qconj_sub hR _)
    (qpe_conj (id_coord _ _ step.multiplier_lt))) (id_coord _ _ step.selected_lt)))

theorem step_coord_other {tailBlocks : Nat} (hb : 0 < tailBlocks) (step : SelectedTranslationStep tailBlocks)
    (b : Nat) (hbl : b < tailBlocks + 1) (hne : b ≠ step.selected) :
    QPE (tailBlocks + 1) (qsub (applySelectedTranslationSteps hb [step]) (PolyQuaternion.coordinateVariable b))
      (PolyQuaternion.coordinateVariable b) := by
  have h := step_coord_raw hb step b hbl
  have himg : coordinateImage step b = PolyQuaternion.coordinateVariable b := by
    unfold coordinateImage; rw [if_neg hne]
  rw [himg] at h
  exact qpe_trans h (id_coord _ _ hbl)

end YMGap.Continuum.SU2TorusRPStepCoord

#print axioms YMGap.Continuum.SU2TorusRPStepCoord.step_coord_sel
#print axioms YMGap.Continuum.SU2TorusRPStepCoord.step_coord_other
