/-
# Fence: independent channel sections do not yet form the CG direct sum

The explicit right inverse for one guarded transvectant is genuine, but it is
not automatically killed by the other contraction orders.  The smallest
spin-half example records that distinction before the full fusion-tree basis
construction.
-/

import YMGap.Continuum.SU2TransvectantTrivalentCoordinateBasis

namespace YMGap.Continuum.SU2TransvectantLocalSectionInterferenceFence

open YMGap.Constructive
open YMGap.Continuum.BinaryForms
open YMGap.Continuum.TransvectantCG
open YMGap.Continuum.SU2TransvectantAdmissibleSynthesis
open YMGap.Continuum.BondMovingStep

theorem spinZeroGuard : fusionOK 1 1 0 = true := by decide

def spinZeroLocalSection : BForm2 :=
  admissibleSynth 1 1 0 spinZeroGuard (mono 0)

/-- The section does exactly invert its intended antisymmetric scalar
transvectant. -/
theorem spinZeroLocalSection_target :
    (transvect 1 1 1 spinZeroLocalSection 0).eqv 1 := by
  have h := admissibleSynth_rightInverse 1 1 0 spinZeroGuard (mono 0) 0
    (by decide)
  simpa only [spinZeroLocalSection, mono] using h

/-- But the same local section leaks into the symmetric order-zero channel.
Therefore separate channel right inverses cannot simply be concatenated into
the Clebsch--Gordan direct-sum coordinate basis. -/
theorem spinZeroLocalSection_leaks_orderZero :
    (transvect 1 1 0 spinZeroLocalSection 1).eqv 1 := by
  decide

theorem spinZeroLocalSection_not_orderZero_kernel :
    ¬ (transvect 1 1 0 spinZeroLocalSection 1).eqv 0 := by
  intro h
  have h1 := spinZeroLocalSection_leaks_orderZero
  have : (1 : Q').eqv 0 := Q'.eqv_trans _ _ _ (Q'.eqv_symm h1) h
  exact (by decide : ¬ (1 : Q').eqv 0) this

end YMGap.Continuum.SU2TransvectantLocalSectionInterferenceFence

#print axioms YMGap.Continuum.SU2TransvectantLocalSectionInterferenceFence.spinZeroLocalSection_target
#print axioms YMGap.Continuum.SU2TransvectantLocalSectionInterferenceFence.spinZeroLocalSection_leaks_orderZero
#print axioms YMGap.Continuum.SU2TransvectantLocalSectionInterferenceFence.spinZeroLocalSection_not_orderZero_kernel
