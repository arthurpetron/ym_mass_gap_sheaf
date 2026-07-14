/-
# Completed spectral localization of the canonical Wilson compression

The exact canonical positive-time compression is now carried through the GNS
completion and linked to a one-mode connected spectral model.  The completed
operator fixes the nonzero vacuum and sends the nonzero fundamental mode to
exactly `1/8` times itself.  Those two representatives are orthogonal and span
the rational dense carrier, so the model/operator relation is explicit rather
than an unlinked juxtaposition.

This is a finite two-mode spectral localization inside the canonical Wilson
state.  It is not a uniform-volume or continuum spectral theorem.
-/

import YMGap.Continuum.PositiveTimeCompressedSpectralGapHalf
import YMGap.Continuum.SU2PeterWeylWilsonBlockCompleted
import YMGap.Continuum.SU2QuaternionCanonicalEightPositiveTimeCompression

namespace YMGap.Continuum.SU2QuaternionCanonicalEightCompressedSpectralGap

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.HamiltonianScalar
open YMGap.Continuum.PositiveTimeCompressedSpectralGapHalf
open YMGap.Continuum.SpectralGap
open YMGap.Continuum.SU2PeterWeylWilsonBlock
open YMGap.Continuum.SU2PeterWeylWilsonBlockCompleted
open YMGap.Continuum.SU2QuaternionCanonicalEightPositiveTimeCompression

local infix:50 " ≈ " => Q'.eqv

/-- The completed operator is defined from the actual canonical compression,
not reconstructed independently from its displayed eigenvalues. -/
def canonicalCompressedTransferOperator : TransferOperator wilsonModeGNS.gnsComplete where
  T := canonicalPositiveTimeCompression.completedTransfer
  vacuum := embedV wilsonModeGNS vacuumMode
  selfAdjoint := canonicalPositiveTimeCompression.completedTransfer_selfAdjoint
  positive := canonicalPositiveTimeCompression.completedTransfer_positive
  contraction := canonicalPositiveTimeCompression.completedTransfer_contraction

theorem canonicalCompleted_vacuum_eigen :
    canonicalCompressedTransferOperator.T (embedV wilsonModeGNS vacuumMode) =
      embedV wilsonModeGNS vacuumMode := by
  refine Eq.trans
    (canonicalPositiveTimeCompression.completedTransfer_embed vacuumMode) ?_
  apply Quotient.sound
  exact embed_null_of_rad wilsonModeGNS
    (rad_of_veq wilsonModeGNS vacuum_eigen)

theorem canonicalCompleted_fundamental_eigen :
    canonicalCompressedTransferOperator.T
        (embedV wilsonModeGNS fundamentalMode) =
      embedV wilsonModeGNS (modeSmul eighth fundamentalMode) := by
  refine Eq.trans
    (canonicalPositiveTimeCompression.completedTransfer_embed fundamentalMode) ?_
  apply Quotient.sound
  exact embed_null_of_rad wilsonModeGNS
    (rad_of_veq wilsonModeGNS fundamental_eighth_eigen)

/-- The connected model lists only the fundamental excitation. -/
def canonicalFundamentalSpectralModel : SpectralModel where
  k := 1
  w := fun _ => 1
  lam := fun _ => eighth
  w_nonneg := fun _ => by decide
  lam_nonneg := fun _ => by decide

def canonicalFundamentalLocatedGap :
    LocatedSpectralGap canonicalFundamentalSpectralModel where
  sep := eighth
  sep_lt_one := eighth_strict_window.2
  bound := fun _ => Q'.le_refl' eighth

def canonicalCompressedSpectralGapData :
    SpectralGapData wilsonModeGNS.gnsComplete where
  op := canonicalCompressedTransferOperator
  model := canonicalFundamentalSpectralModel
  gap := canonicalFundamentalLocatedGap

theorem canonical_vacuum_fundamental_orthogonal :
    wilsonModeGNS.B vacuumMode fundamentalMode ≈ 0 := by
  decide

theorem canonical_fundamental_qmk_ne_vacuum :
    wilsonModeGNS.qmk fundamentalMode ≠ wilsonModeGNS.qmk vacuumMode := by
  intro h
  have hr : wilsonModeGNS.rad fundamentalMode vacuumMode := Quotient.exact h
  have hnot : ¬ wilsonModeGNS.rad fundamentalMode vacuumMode := by
    unfold GNSData.rad GNSData.sub wilsonModeGNS modeAdd modeNeg
      vacuumMode fundamentalMode modeZero reflectedWilsonGram
      bareHaarLinkEntry coupling
    decide
  exact hnot hr

theorem canonicalModes_span_dense (a : ModeVec) :
    ∃ alpha beta : Q',
      modeEqv a
        (modeAdd (modeSmul alpha vacuumMode)
          (modeSmul beta fundamentalMode)) := by
  refine ⟨a.1, a.2, ?_⟩
  unfold modeEqv modeAdd modeSmul vacuumMode fundamentalMode
  constructor
  · exact Q'.eqv_symm
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr'
          (Q'.mul_one_eqv a.1) (QPoly.q_mul_zero a.2))
        (QPoly.q_add_zero_eqv a.1))
  · exact Q'.eqv_symm
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr'
          (QPoly.q_mul_zero a.1) (Q'.mul_one_eqv a.2))
        (QPoly.q_zero_add_eqv a.2))

/-- Exact operator/model compatibility for the actual canonical compression. -/
def canonicalDenseTwoModeCompatibility :
    DenseTwoModeSpectralCompatibility canonicalCompressedSpectralGapData where
  vacuumRep := vacuumMode
  excitedRep := fundamentalMode
  operator_vacuum := rfl
  vacuum_ne_zero := vacuum_qmk_ne_zero
  excited_ne_zero := fundamental_qmk_ne_zero
  excited_ne_vacuum := canonical_fundamental_qmk_ne_vacuum
  vacuum_excited_orthogonal := canonical_vacuum_fundamental_orthogonal
  connected_model_one_mode := rfl
  connected_weight_pos := by decide
  vacuum_eigen := canonicalCompleted_vacuum_eigen
  excited_eigen := canonicalCompleted_fundamental_eigen
  rational_dense_span := canonicalModes_span_dense

def sevenEighths : Q' := Q'.mkPos 7 8 (by decide)

theorem canonical_gapMargin_eqv_sevenEighths :
    canonicalFundamentalLocatedGap.gapMargin ≈ sevenEighths := by
  decide

theorem canonical_gapMargin_pos :
    (0 : Q') < canonicalFundamentalLocatedGap.gapMargin :=
  canonicalFundamentalLocatedGap.gapMargin_pos

theorem canonical_linked_fundamental_window :
    (0 : Q') < canonicalCompressedSpectralGapData.model.lam 0 ∧
      canonicalCompressedSpectralGapData.model.lam 0 < (1 : Q') :=
  eighth_strict_window

end YMGap.Continuum.SU2QuaternionCanonicalEightCompressedSpectralGap

#print axioms YMGap.Continuum.SU2QuaternionCanonicalEightCompressedSpectralGap.canonicalCompressedTransferOperator
#print axioms YMGap.Continuum.SU2QuaternionCanonicalEightCompressedSpectralGap.canonicalCompleted_fundamental_eigen
#print axioms YMGap.Continuum.SU2QuaternionCanonicalEightCompressedSpectralGap.canonicalFundamentalLocatedGap
#print axioms YMGap.Continuum.SU2QuaternionCanonicalEightCompressedSpectralGap.canonicalDenseTwoModeCompatibility
#print axioms YMGap.Continuum.SU2QuaternionCanonicalEightCompressedSpectralGap.canonical_gapMargin_pos
