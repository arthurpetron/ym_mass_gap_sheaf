/-
Track 11.7-fusion / R2o -- all-cutoff physical mode-one compiler.

`P2RetunedTailRatio` already bounds each normalized p=2 fusion mode by a
retuned heat factor times its predecessor.  That factor is in `[0,1]`.
Consequently the same local certificate that constructs
`CanonicalBulkControl` also makes the displayed non-vacuum spectrum
monotone, and every mode is bounded by mode one.

This is the proof-about-computation replacement for a growing finite scan of
all modes at every cutoff.  It also formally separates the physical gap-edge
mode from any auxiliary bulk-localization label.

No `Classical`, `native_decide`, `sorry`, custom axiom, or noncomputable
declaration.
-/

import YMGap.Continuum.P2RetunedFusionDefectPower

namespace YMGap.Continuum.P2RetunedFusionPhysicalMode

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FusionKernelStatement
open YMGap.Continuum.VacNormEigShift
open YMGap.Continuum.P2RetunedRatioCompiler
open YMGap.Continuum.P2RetunedBlockingDictionary
open YMGap.Continuum.P2RetunedFusionPowerCertificate
open YMGap.Continuum.P2RetunedFusionDefectPower

/-- Every normalized p=2 fusion eigenvalue is nonnegative. -/
theorem p2VacNorm_nonneg (N : Nat) {w : Q'}
    (hw0 : (0 : Q') <= w) (hw1 : w <= (1 : Q')) (s : Nat) :
    (0 : Q') <= p2VacNorm N hw0 hw1 s := by
  unfold p2VacNorm vacNorm Q'.divPos
  exact Q'.mul_nonneg _ _ (bondMovedCoeff_nonneg N hw0 2 s)
    (Q'.le_of_lt (Q'.recipPos_pos _ _))

/-- One local retuned-tail atom implies ordinary adjacent monotonicity because
its heat factor is at most one. -/
theorem p2VacNorm_succ_le_of_tail {N : Nat} {w : Q'}
    (hw0 : (0 : Q') <= w) (hw1 : w <= (1 : Q'))
    (T : P2RetunedTailRatio N w hw0 hw1) (s : Nat)
    (hs : 1 <= s) (hsN : s < 2 * N) :
    p2VacNorm N hw0 hw1 (s + 1) <= p2VacNorm N hw0 hw1 s := by
  have htail := T.tail s hs hsN
  have hpow : qpow (p2RetunedWeight w) (2 * s + 3) <= (1 : Q') :=
    qpow_le_one (p2RetunedWeight_nonneg hw0)
      (p2RetunedWeight_le_one hw1) (2 * s + 3)
  have hscaled :
      qpow (p2RetunedWeight w) (2 * s + 3) *
          p2VacNorm N hw0 hw1 s <=
        (1 : Q') * p2VacNorm N hw0 hw1 s :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hpow
      (p2VacNorm_nonneg N hw0 hw1 s)
  exact Q'.le_trans' _ _ _ htail
    (Q'.le_trans' _ _ _ hscaled
      (Q'.le_of_eqv (Q'.one_mul_eqv (p2VacNorm N hw0 hw1 s))))

/-- Proof-about-computation induction: every displayed non-vacuum normalized
mode lies below mode one. -/
theorem p2VacNorm_le_modeOne_of_tail {N : Nat} {w : Q'}
    (hw0 : (0 : Q') <= w) (hw1 : w <= (1 : Q'))
    (T : P2RetunedTailRatio N w hw0 hw1) :
    forall s, 1 <= s -> s <= 2 * N ->
      p2VacNorm N hw0 hw1 s <= p2VacNorm N hw0 hw1 1
  | 0, hs, _ => by omega
  | 1, _, _ => Q'.le_of_eqv (Q'.eqv_refl _)
  | s + 2, _, hsN => by
      have hstep := p2VacNorm_succ_le_of_tail hw0 hw1 T (s + 1)
        (by omega) (by omega)
      have hind := p2VacNorm_le_modeOne_of_tail hw0 hw1 T (s + 1)
        (by omega) (by omega)
      exact Q'.le_trans' _ _ _ hstep hind

/-- The same theorem in the exact `fusionEig` notation used by the physical
separator carrier. -/
theorem fusionEig_le_modeOne_of_tail {N : Nat} {w : Q'}
    (hw0 : (0 : Q') <= w) (hw1 : w <= (1 : Q'))
    (T : P2RetunedTailRatio N w hw0 hw1) (s : Nat)
    (hs : 1 <= s) (hsN : s <= 2 * N) :
    fusionEig N w 2 s (p2DenomPos N hw0 hw1 s) <=
      fusionEig N w 2 1 (p2DenomPos N hw0 hw1 1) := by
  have hleft := Q'.le_of_eqv (fusionEig_eqv_p2VacNorm N hw0 hw1 s)
  have hmid := p2VacNorm_le_modeOne_of_tail hw0 hw1 T s hs hsN
  have hright := Q'.ge_of_eqv (fusionEig_eqv_p2VacNorm N hw0 hw1 1)
  exact Q'.le_trans' _ _ _ hleft (Q'.le_trans' _ _ _ hmid hright)

/-- Constant mode-one selector. -/
def modeOne (_k : Nat) : Nat := 1

/-- **All-cutoff physical separator theorem.**  Any compiled retuned-control
family carries mode one as the dominant displayed non-vacuum p=2 fusion mode.
No additional scan, bulk label, or spectral hypothesis is required. -/
def P2RetunedControlFamily.modeOnePhysical (F : P2RetunedControlFamily) :
    P2PhysicalSeparatorMode F modeOne where
  nonvacuum := fun _ => by
    unfold modeOne
    decide
  support := fun k => by
    unfold modeOne
    have := F.hN k
    omega
  dominates := fun k s hs hsN => by
    simpa only [modeOne, fusionModeQ, P2RetunedControlFamily.control] using
      (fusionEig_le_modeOne_of_tail (F.hw0 k) (F.hw1 k)
        (F.tailRatio k) s hs hsN)

end YMGap.Continuum.P2RetunedFusionPhysicalMode

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.P2RetunedFusionPhysicalMode.p2VacNorm_nonneg
#print axioms YMGap.Continuum.P2RetunedFusionPhysicalMode.p2VacNorm_succ_le_of_tail
#print axioms YMGap.Continuum.P2RetunedFusionPhysicalMode.p2VacNorm_le_modeOne_of_tail
#print axioms YMGap.Continuum.P2RetunedFusionPhysicalMode.fusionEig_le_modeOne_of_tail
#print axioms YMGap.Continuum.P2RetunedFusionPhysicalMode.P2RetunedControlFamily.modeOnePhysical
