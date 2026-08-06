/-
Track 11.7-fusion / R2l -- first physical-ladder fusion-power audit.

`P2RetunedRatioCertificate` provides genuine canonical p=2 controls at the
fixed heat weight `11/12` for cutoffs two and three.  They are individually
valid localization cells, but they do not automatically form an exact RG
trajectory.  This module checks the first adjacent pair in the kernel.

For the minimal physical block exponent `b = 1`, exact self-similarity asks
that the coarse eigenvalue be the square of the fine eigenvalue.  Across every
non-vacuum mode displayed by the two finite spectra, the required cross
product is false.  Thus the existing fixed-weight cutoff ladder cannot be
relabelled as the missing physical fusion-power family: the scale weights (or
the spectral trajectory) must genuinely run.

No `Classical`, `native_decide`, `sorry`, custom axiom, or noncomputable
declaration.
-/

import YMGap.Continuum.P2RetunedFusionDefectPower
import YMGap.Continuum.P2RetunedRatioCertificate

namespace YMGap.Continuum.P2RetunedFusionPowerFenceAudit

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.FusionKernelStatement
open YMGap.Continuum.RebasedBulkLocalizationBridge
open YMGap.Continuum.P2RetunedRatioCertificate
open YMGap.Continuum.P2RetunedFusionPowerCertificate
open YMGap.Continuum.P2RetunedFusionDefectPower

set_option maxHeartbeats 4000000
set_option maxRecDepth 30000

/-- The exact selected p=2 eigenvalue at the first reflected cutoff. -/
def fenceModeN2Q (s : Nat) : Q' :=
  fusionEig 2 fenceW 2 s (fenceRetunedControlN2.denomPos s)

/-- The exact selected p=2 eigenvalue at the next reflected cutoff. -/
def fenceModeN3Q (s : Nat) : Q' :=
  fusionEig 3 fenceW 2 s (fenceRetunedControlN3.denomPos s)

/-- **Exact first-ladder obstruction.**  No non-vacuum mode in the full
cutoff-two support is the square of any non-vacuum mode in the full
cutoff-three support.  The proof enumerates only 24 exact integer cross
products; rational normalization and constructive-real powers are absent. -/
theorem fenceN2N3_no_supported_nonvacuum_square
    (coarseMode fineMode : Nat)
    (hcoarsePos : 1 <= coarseMode) (hcoarseSupport : coarseMode <= 4)
    (hfinePos : 1 <= fineMode) (hfineSupport : fineMode <= 6) :
    qPowerCellCheck (fenceModeN2Q coarseMode)
      (fenceModeN3Q fineMode) 2 = false := by
  have hcoarse :
      coarseMode = 1 \/ coarseMode = 2 \/ coarseMode = 3 \/ coarseMode = 4 := by
    omega
  have hfine :
      fineMode = 1 \/ fineMode = 2 \/ fineMode = 3 \/ fineMode = 4 \/
        fineMode = 5 \/ fineMode = 6 := by
    omega
  clear hcoarsePos hcoarseSupport hfinePos hfineSupport
  rcases hcoarse with rfl | rfl | rfl | rfl <;>
    rcases hfine with rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide

/-- Consequently the corresponding exact `QPowerCell` is uninhabited. -/
theorem fenceN2N3_no_supported_nonvacuum_cell
    (coarseMode fineMode : Nat)
    (hcoarsePos : 1 <= coarseMode) (hcoarseSupport : coarseMode <= 4)
    (hfinePos : 1 <= fineMode) (hfineSupport : fineMode <= 6)
    (C : QPowerCell (fenceModeN2Q coarseMode)
      (fenceModeN3Q fineMode) 2) : False := by
  have htrue : qPowerCellCheck (fenceModeN2Q coarseMode)
      (fenceModeN3Q fineMode) 2 = true :=
    (qPowerCellCheck_eq_true_iff _ _ _).2 C.eqv
  have hfalse := fenceN2N3_no_supported_nonvacuum_square
    coarseMode fineMode hcoarsePos hcoarseSupport hfinePos hfineSupport
  rw [hfalse] at htrue
  cases htrue

/-! ## A genuine one-step defect-power cell -/

/-- The exact defect factor for coarse mode two and fine mode one.  It is the
reduced rational quotient `lambda_(N=2,s=2) / lambda_(N=3,s=1)^2`. -/
def fenceN2N3ModeTwoOneFactor : Q' :=
  Q'.mkPos
    35736905739694159537141398825689611546601069007797396546110936952779965841
    51343908758468552538253145237793429616323588652033109686252847894970236928
    (by decide)

/-- The factor is a physical contraction factor. -/
theorem fenceN2N3ModeTwoOneFactor_nonneg :
    (0 : Q') <= fenceN2N3ModeTwoOneFactor := by decide

theorem fenceN2N3ModeTwoOneFactor_le_one :
    fenceN2N3ModeTwoOneFactor <= (1 : Q') := by decide

/-- Its one-step loss is within the half-loss window consumed by the
constructive product-floor compiler. -/
theorem fenceN2N3ModeTwoOneFactor_loss_le_half :
    (1 : Q') - fenceN2N3ModeTwoOneFactor <= HalfPow.half := by decide

/-- The full exact eigenvalue identity is recomputed by the kernel as one
integer cross product. -/
theorem fenceN2N3ModeTwoOne_check :
    qDefectPowerCellCheck (fenceModeN2Q 2) (fenceModeN3Q 1)
      fenceN2N3ModeTwoOneFactor 2 = true := by decide

/-- A non-vacuum, supported defect-power certificate for the first cutoff
step.  This validates the corrected carrier without claiming an all-scale
running family. -/
def fenceN2N3ModeTwoOne_cell :
    QDefectPowerCell (fenceModeN2Q 2) (fenceModeN3Q 1)
      fenceN2N3ModeTwoOneFactor 2 :=
  QDefectPowerCell.ofCheck fenceN2N3ModeTwoOne_check

end YMGap.Continuum.P2RetunedFusionPowerFenceAudit

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.P2RetunedFusionPowerFenceAudit.fenceN2N3_no_supported_nonvacuum_square
#print axioms YMGap.Continuum.P2RetunedFusionPowerFenceAudit.fenceN2N3_no_supported_nonvacuum_cell
#print axioms YMGap.Continuum.P2RetunedFusionPowerFenceAudit.fenceN2N3ModeTwoOneFactor_loss_le_half
#print axioms YMGap.Continuum.P2RetunedFusionPowerFenceAudit.fenceN2N3ModeTwoOne_check
#print axioms YMGap.Continuum.P2RetunedFusionPowerFenceAudit.fenceN2N3ModeTwoOne_cell
