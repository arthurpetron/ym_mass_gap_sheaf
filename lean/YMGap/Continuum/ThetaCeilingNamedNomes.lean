/-
# Certified theta-ceiling at the named nomes w = 1/2 and w = 4/5

For the SAME constructed limit `D_∞(x) = productRadialCostCReal` of the actual signed radial cost, and every
rational `x ∈ [-1,1]`: `D_∞(x) ≤ 2w/(1-w²)`, i.e. `≤ 4/3` at `w = 1/2` and `≤ 40/9` at `w = 4/5`.

Certificate data (all checked by kernel `decide`):
* `w = 1/2`: onset `N = 2` (`c_2 = 1/32 ≤ 1/8`), tail payment `4c_2/(1-w²) = 1/6`, budget `4/3 - 1/6 = 7/6`;
  14 dyadic cells (finest width 1/16).
* `w = 4/5`: onset `N = 5` (`c_5 = (4/5)^11 ≈ 0.0859 ≤ 1/8`; `N = 4` fails), payment `≈ 0.954`, budget
  `≈ 3.490`; 66 dyadic cells (finest width 1/256).
The enclosure is monotone interval arithmetic per cell (ThetaCeilingCells), not a Lipschitz constant.
The "addition + tail gives D_N ≤ 3/[2(1-w)]" shortcut is not used.  Nome-specific, not uniform in w.  Not an
addition identity, an angular or Haar certificate, or a physical statement.
-/

import YMGap.Continuum.ThetaCeilingCells
import YMGap.Continuum.JacobiHeatTransverseCurvature

namespace YMGap.Continuum.ThetaCeilingNamedNomes

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.JacobiProductRadialSignedTail (eighth radialTailPayment)
open YMGap.Continuum.JacobiProductRadialLimit (productRadialCostCReal)
open YMGap.Continuum.JacobiHeatTransverseCurvature (transverseCap)
open YMGap.Continuum.ThetaCeilingCells

/-- The dyadic rational `n / 2^k`. -/
def dy (n : Int) (k : Nat) : Q' := ⟨n, 2 ^ k - 1⟩

def wHalf : Q' := Q'.mkPos 1 2 (by decide)
def wFF : Q' := Q'.mkPos 4 5 (by decide)

/-- Cell endpoints after `-1` for `w = 1/2`. -/
def ptsHalf : List Q' := [
  dy (-7) 3, dy (-13) 4, dy (-3) 2, dy (-11) 4, dy (-5) 3, dy (-9) 4,
  dy (-1) 1, dy (-3) 3, dy (-1) 2, dy (0) 0, dy (1) 2, dy (1) 1,
  dy (1) 0]

/-- Cell endpoints after `-1` for `w = 4/5`. -/
def ptsFF : List Q' := [
  dy (-63) 6, dy (-125) 7, dy (-249) 8, dy (-31) 5, dy (-247) 8, dy (-123) 7,
  dy (-245) 8, dy (-61) 6, dy (-243) 8, dy (-121) 7, dy (-241) 8, dy (-15) 4,
  dy (-239) 8, dy (-119) 7, dy (-237) 8, dy (-59) 6, dy (-235) 8, dy (-117) 7,
  dy (-233) 8, dy (-29) 5, dy (-231) 8, dy (-115) 7, dy (-229) 8, dy (-57) 6,
  dy (-227) 8, dy (-113) 7, dy (-225) 8, dy (-7) 3, dy (-223) 8, dy (-111) 7,
  dy (-221) 8, dy (-55) 6, dy (-219) 8, dy (-109) 7, dy (-217) 8, dy (-27) 5,
  dy (-107) 7, dy (-53) 6, dy (-105) 7, dy (-13) 4, dy (-103) 7, dy (-51) 6,
  dy (-101) 7, dy (-25) 5, dy (-99) 7, dy (-49) 6, dy (-3) 2, dy (-47) 6,
  dy (-23) 5, dy (-45) 6, dy (-11) 4, dy (-43) 6, dy (-21) 5, dy (-5) 3,
  dy (-19) 5, dy (-9) 4, dy (-17) 5, dy (-1) 1, dy (-7) 4, dy (-3) 3,
  dy (-1) 2, dy (0) 0, dy (1) 2, dy (1) 1, dy (1) 0]

theorem half_onset : HKPos.geoAmp wHalf 2 ≤ eighth := by decide
theorem ff_onset : HKPos.geoAmp wFF 5 ≤ eighth := by decide

/-- The ceiling constants are exactly `2w/(1-w²)`. -/
theorem half_cap : (transverseCap wHalf).eqv (Q'.mkPos 4 3 (by decide)) := by decide
theorem ff_cap : (transverseCap wFF).eqv (Q'.mkPos 40 9 (by decide)) := by decide

theorem half_chain : chainOK wHalf (Q'.mkPos 4 3 (by decide) + -(radialTailPayment wHalf 2)) 2 (-1)
    (dy (-15) 4 :: ptsHalf) = true := by decide +kernel

theorem ff_chain : chainOK wFF (Q'.mkPos 40 9 (by decide) + -(radialTailPayment wFF 5)) 5 (-1)
    (dy (-127) 7 :: ptsFF) = true := by decide +kernel

/-- **Theta-ceiling at `w = 1/2` (PROVED).**  `D_∞(x) ≤ 4/3 = 2w/(1-w²)` on all rational `x ∈ [-1,1]`. -/
theorem theta_ceiling_half (x : Q') (hx0 : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) :
    CReal.leRat (productRadialCostCReal (w := wHalf) (by decide) (by decide) hx0 hx1) (Q'.mkPos 4 3 (by decide)) :=
  ceiling_of_chain (by decide) (by decide) _ 2 half_onset _ _ half_chain (by decide) x hx0 hx1

/-- **Theta-ceiling at `w = 4/5` (PROVED).**  `D_∞(x) ≤ 40/9 = 2w/(1-w²)` on all rational `x ∈ [-1,1]`. -/
theorem theta_ceiling_ff (x : Q') (hx0 : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) :
    CReal.leRat (productRadialCostCReal (w := wFF) (by decide) (by decide) hx0 hx1) (Q'.mkPos 40 9 (by decide)) :=
  ceiling_of_chain (by decide) (by decide) _ 5 ff_onset _ _ ff_chain (by decide) x hx0 hx1

end YMGap.Continuum.ThetaCeilingNamedNomes
