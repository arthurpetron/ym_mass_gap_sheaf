/-
# Coupling fence between the exact spin foam and the 4D KP anchor

The present exact finite-box spin-foam chain is instantiated with the Wilson
block coupling `1/2`.  The genuine 4D lattice-animal/KP estimate is proved at
`w4 = 1/20`.  They are different finite-volume measures, already at the
fundamental face coefficient, so the abstract-to-real bridge must first
parameterize the exact spin-foam derivation in the coupling.
-/

import YMGap.Continuum.Z4ExplicitCutoffOneSurfaceSelection
import YMGap.Continuum.Stage1LoopyReduction

namespace YMGap.Continuum.Z4SpinFoamKPCouplingFence

open YMGap.Constructive
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.Stage1LoopyReduction
open YMGap.Continuum.SU2PeterWeylWilsonBlock

local infix:50 " ≈ " => Q'.eqv

theorem exactSpinFoamCoupling_eqv_half :
    coupling ≈ Q'.mkPos 1 2 (by decide) := by
  decide

theorem kpAnchorCoupling_eqv_one_twentieth :
    w4 ≈ Q'.mkPos 1 20 (by decide) := by
  decide

theorem exactSpinFoamCoupling_ne_kpAnchor :
    ¬ coupling ≈ w4 := by
  decide

theorem exactSpinFoamFundamentalCoefficient_eqv_quarter :
    coeffW coupling 1 ≈ Q'.mkPos 1 4 (by decide) := by
  decide

theorem kpAnchorFundamentalCoefficient_eqv_one_four_thousandth :
    coeffW w4 1 ≈ Q'.mkPos 1 4000 (by decide) := by
  decide

theorem fundamentalCoefficients_ne :
    ¬ coeffW coupling 1 ≈ coeffW w4 1 := by
  decide

end YMGap.Continuum.Z4SpinFoamKPCouplingFence

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4SpinFoamKPCouplingFence.exactSpinFoamCoupling_ne_kpAnchor
#print axioms YMGap.Continuum.Z4SpinFoamKPCouplingFence.kpAnchorFundamentalCoefficient_eqv_one_four_thousandth
#print axioms YMGap.Continuum.Z4SpinFoamKPCouplingFence.fundamentalCoefficients_ne
