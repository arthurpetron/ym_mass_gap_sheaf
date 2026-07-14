/-
# A checked obstruction to extracting constant F-coefficients from linearity alone

Leakage-free shell coordinates reconstruct arbitrary source tensors, but that
fact alone cannot force the coefficients of a trilinear map in right channels
to be independent of the probed monomial shell.  The diagonal linear twist
below gives a smallest exact counterexample: on `(0,1,1) -> 2` there is only
one admissible right channel, yet its required scalar is one on one monomial
and two on another.  Thus the next positive construction must use the SU(2)
intertwining covariance (a constructive Schur-uniqueness argument), not merely
shellwise coordinate inversion.
-/

import YMGap.Continuum.SU2TransvectantCentralChannelEquation

namespace YMGap.Continuum.SU2TransvectantConstantCoefficientObstruction

open YMGap.Constructive
open YMGap.Continuum.BinaryForms
open YMGap.Continuum.SU2TransvectantMixedPentagon

local infix:50 " ≈ " => Q'.eqv

/-- A rational diagonal linear map which fixes degree zero and doubles every
positive monomial coordinate. -/
def degreeTwist (y : BForm) : BForm := fun s =>
  (if s = 0 then (1 : Q') else 2) * y s

/-- The right channel `(0 (1 1)_2)_2`, precomposed with the diagonal twist in
its middle input.  It is still pointwise trilinear, but not SU(2)-equivariant. -/
def twistedRightMap (x y z : BForm) : BForm :=
  triRight 0 1 1 2 2 x (degreeTwist y) z

theorem twistedRightMap_probe_zero :
    twistedRightMap (mono 0) (mono 0) (mono 0) 0 ≈ 1 := by
  decide

theorem twistedRightMap_probe_one :
    twistedRightMap (mono 0) (mono 1) (mono 0) 1 ≈ 2 := by
  decide

theorem untwistedRightMap_probe_zero :
    triRight 0 1 1 2 2 (mono 0) (mono 0) (mono 0) 0 ≈ 1 := by
  decide

theorem untwistedRightMap_probe_one :
    triRight 0 1 1 2 2 (mono 0) (mono 1) (mono 0) 1 ≈ 1 := by
  decide

/-- **Constant-coefficient obstruction.**  No single rational scalar turns
the unique right channel into the twisted trilinear map on the complete
monomial basis. -/
theorem no_constant_right_channel_coefficient :
    ¬ ∃ q : Q',
      TriMapEqv 0 1 1 2 twistedRightMap
        (fun x y z => scaleForm q (triRight 0 1 1 2 2 x y z)) := by
  intro hex
  rcases hex with ⟨q, hq⟩
  have hprobe0 := hq 0 (by omega) 0 (by omega) 0 (by omega) 0 (by omega)
  have hprobe1 := hq 0 (by omega) 1 (by omega) 0 (by omega) 1 (by omega)
  have hscale0 :
      scaleForm q
          (triRight 0 1 1 2 2 (mono 0) (mono 0) (mono 0)) 0 ≈ q := by
    unfold scaleForm
    refine Q'.eqv_trans _ (q * 1) _
      (Q'.mul_eqv_congr_left q _ _ untwistedRightMap_probe_zero) ?_
    exact Q'.mul_one_eqv q
  have hscale1 :
      scaleForm q
          (triRight 0 1 1 2 2 (mono 0) (mono 1) (mono 0)) 1 ≈ q := by
    unfold scaleForm
    refine Q'.eqv_trans _ (q * 1) _
      (Q'.mul_eqv_congr_left q _ _ untwistedRightMap_probe_one) ?_
    exact Q'.mul_one_eqv q
  have hone : (1 : Q') ≈ q :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm twistedRightMap_probe_zero)
      (Q'.eqv_trans _ _ _ hprobe0 hscale0)
  have htwo : (2 : Q') ≈ q :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm twistedRightMap_probe_one)
      (Q'.eqv_trans _ _ _ hprobe1 hscale1)
  have hfalse : (2 : Q') ≈ 1 :=
    Q'.eqv_trans _ _ _ htwo (Q'.eqv_symm hone)
  have hne : ¬ ((2 : Q') ≈ 1) := by decide
  exact hne hfalse

end YMGap.Continuum.SU2TransvectantConstantCoefficientObstruction

#print axioms YMGap.Continuum.SU2TransvectantConstantCoefficientObstruction.twistedRightMap_probe_zero
#print axioms YMGap.Continuum.SU2TransvectantConstantCoefficientObstruction.twistedRightMap_probe_one
#print axioms YMGap.Continuum.SU2TransvectantConstantCoefficientObstruction.no_constant_right_channel_coefficient
