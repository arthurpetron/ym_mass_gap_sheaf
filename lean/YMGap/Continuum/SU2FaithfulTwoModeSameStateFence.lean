/-
# Same-state fence for the faithful two-mode connector

The normalized midpoint Gram in `SU2FaithfulTwoModeGNSConnector` is indexed by
`chi0, chi1`, so its first basis vector is the constant (vacuum) character.
Its `denseCharacterTransfer`, however, imports the two *excited* eigenvalues
`1/8, 1/256` from `SU2HaarTwoModePositiveTimePilot`.  The genuine same-state
Wilson block has vacuum/fundamental transfer eigenvalues `1, 1/8`.

This successor makes the mismatch kernel-visible.  In fact there is no
setoid-linear, vacuum-preserving intertwiner from the frozen faithful transfer
to the genuine same-state Wilson transfer.  Thus the former cannot be declared
to be the physical `E_Lambda` transfer by adding a compatibility assertion; its
mode indexing must first be repaired (or a separate vacuum mode added).
-/

import YMGap.Continuum.SU2FaithfulTwoModeGNSConnectorClosed
import YMGap.Continuum.SU2FaithfulTwoModeCompletedTransfer
import YMGap.Continuum.SU2PeterWeylWilsonBlock

namespace YMGap.Continuum.SU2FaithfulTwoModeSameStateFence

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.SU2FaithfulTwoModeGNSConnector
open YMGap.Continuum.SU2HaarTwoModePositiveTimePilot

local infix:50 " ≈ " => Q'.eqv

/-- The natural coordinate identification does not identify the two rational
states: the second retained vector has norm `1` in the normalized Haar Gram
and norm `1/8` in the one-link interacting Wilson Gram. -/
theorem natural_state_forms_disagree :
    ¬ (∀ a b : Q' × Q',
      faithfulModeGNS.B a b ≈
        SU2PeterWeylWilsonBlock.wilsonModeGNS.B a b) := by
  intro h
  have hf : faithfulModeGNS.B secondModeVector secondModeVector ≈ 1 := by
    simpa [modeVector, modeOne] using mode_gram modeOne modeOne
  have hw :
      SU2PeterWeylWilsonBlock.wilsonModeGNS.B
          secondModeVector secondModeVector ≈
        SU2PeterWeylWilsonBlock.eighth := by
    simpa [secondModeVector, SU2PeterWeylWilsonBlock.fundamentalMode] using
      SU2PeterWeylWilsonBlock.fundamental_norm
  have hbad : (1 : Q') ≈ SU2PeterWeylWilsonBlock.eighth :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm hf)
      (Q'.eqv_trans _ _ _ (h secondModeVector secondModeVector) hw)
  exact (by decide : ¬ ((1 : Q') ≈ SU2PeterWeylWilsonBlock.eighth)) hbad

/-- Even before completion, the naturally identified transfer maps disagree
on the first retained coordinate: `1/8` versus the Wilson vacuum eigenvalue
`1`. -/
theorem natural_transfer_first_mode_disagrees :
    ¬ SU2PeterWeylWilsonBlock.modeEqv
      (denseCharacterTransfer firstModeVector)
      (SU2PeterWeylWilsonBlock.sameStateTransfer firstModeVector) := by
  intro h
  have hfirst := h.1
  have htoEighth :
      firstEigenvalue * (1 : Q') ≈ SU2PeterWeylWilsonBlock.eighth :=
    Q'.eqv_trans _ _ _ (Q'.mul_one_eqv firstEigenvalue) (by
      simpa [SU2PeterWeylWilsonBlock.eighth] using firstEigenvalue_exact)
  have hbad : SU2PeterWeylWilsonBlock.eighth ≈ (1 : Q') :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm htoEighth) hfirst
  exact (by decide :
    ¬ (SU2PeterWeylWilsonBlock.eighth ≈ (1 : Q'))) hbad

/-- No setoid-linear map can both send the frozen connector's first vector to
the Wilson vacuum and intertwine its `1/8,1/256` transfer with the genuine
same-state `1,1/8` Wilson transfer.  This rules out every linear relabelling,
not only the identity coordinate map. -/
theorem no_linear_vacuum_preserving_sameState_intertwiner
    (phi : faithfulModeGNS.V → SU2PeterWeylWilsonBlock.ModeVec)
    (map_veq : ∀ {a b}, faithfulModeGNS.veq a b →
      SU2PeterWeylWilsonBlock.modeEqv (phi a) (phi b))
    (map_smul : ∀ s a,
      SU2PeterWeylWilsonBlock.modeEqv
        (phi (faithfulModeGNS.smul s a))
        (SU2PeterWeylWilsonBlock.modeSmul s (phi a)))
    (maps_first_to_vacuum :
      SU2PeterWeylWilsonBlock.modeEqv (phi firstModeVector)
        SU2PeterWeylWilsonBlock.vacuumMode)
    (intertwines : ∀ a,
      SU2PeterWeylWilsonBlock.modeEqv
        (phi (denseCharacterTransfer a))
        (SU2PeterWeylWilsonBlock.sameStateTransfer (phi a))) : False := by
  let D := SU2PeterWeylWilsonBlock.wilsonModeGNS
  have hscaled : SU2PeterWeylWilsonBlock.modeEqv
      (SU2PeterWeylWilsonBlock.modeSmul firstEigenvalue
        (phi firstModeVector))
      (SU2PeterWeylWilsonBlock.modeSmul firstEigenvalue
        SU2PeterWeylWilsonBlock.vacuumMode) := by
    exact ⟨Q'.mul_eqv_congr_left firstEigenvalue _ _ maps_first_to_vacuum.1,
      Q'.mul_eqv_congr_left firstEigenvalue _ _ maps_first_to_vacuum.2⟩
  have hleft : SU2PeterWeylWilsonBlock.modeEqv
      (phi (denseCharacterTransfer firstModeVector))
      (SU2PeterWeylWilsonBlock.sameStateTransfer
        SU2PeterWeylWilsonBlock.vacuumMode) :=
    D.veq_trans (intertwines firstModeVector)
      (SU2PeterWeylWilsonBlock.sameStateTransfer_map_veq
        maps_first_to_vacuum)
  have hright : SU2PeterWeylWilsonBlock.modeEqv
      (phi (denseCharacterTransfer firstModeVector))
      (SU2PeterWeylWilsonBlock.modeSmul firstEigenvalue
        SU2PeterWeylWilsonBlock.vacuumMode) :=
    D.veq_trans (map_veq dense_character_first_eigen)
      (D.veq_trans (map_smul firstEigenvalue firstModeVector) hscaled)
  have hbad : SU2PeterWeylWilsonBlock.modeEqv
      (SU2PeterWeylWilsonBlock.sameStateTransfer
        SU2PeterWeylWilsonBlock.vacuumMode)
      (SU2PeterWeylWilsonBlock.modeSmul firstEigenvalue
        SU2PeterWeylWilsonBlock.vacuumMode) :=
    D.veq_trans (D.veq_symm hleft) hright
  have hfirst := hbad.1
  have htoEighth :
      firstEigenvalue * (1 : Q') ≈ SU2PeterWeylWilsonBlock.eighth :=
    Q'.eqv_trans _ _ _ (Q'.mul_one_eqv firstEigenvalue) (by
      simpa [SU2PeterWeylWilsonBlock.eighth] using firstEigenvalue_exact)
  have honeEighth : (1 : Q') ≈ SU2PeterWeylWilsonBlock.eighth :=
    Q'.eqv_trans _ _ _ hfirst htoEighth
  exact (by decide :
    ¬ ((1 : Q') ≈ SU2PeterWeylWilsonBlock.eighth)) honeEighth

end YMGap.Continuum.SU2FaithfulTwoModeSameStateFence

#print axioms YMGap.Continuum.SU2FaithfulTwoModeSameStateFence.natural_state_forms_disagree
#print axioms YMGap.Continuum.SU2FaithfulTwoModeSameStateFence.natural_transfer_first_mode_disagrees
#print axioms YMGap.Continuum.SU2FaithfulTwoModeSameStateFence.no_linear_vacuum_preserving_sameState_intertwiner
