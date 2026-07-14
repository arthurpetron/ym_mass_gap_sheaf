/-
# Observable coherence on the exact mixed SU(2) pentagon

The completed mixed transvectant pentagon already proves that its long and
short fusion routes produce the same final GNS state.  Here that equality is
consumed by the full two-coordinate observable carrier: every matrix action,
same-state quadratic numerator, norm, and normalized expectation in the final
path chart is independent of the chosen pentagon route.

This proves final-chart observable coherence for the existing `(2,2,1,1)`
pentagon.  Edge-by-edge conjugation coherence for arbitrary labels and all
fusion trees remains open.
-/

import YMGap.Continuum.SU2FourValentFMoveObservableCovariance
import YMGap.Continuum.SU2TransvectantMixedPentagonGNSCompleted

namespace YMGap.Continuum.SU2MixedPentagonObservableCoherence

set_option maxHeartbeats 900000
set_option maxRecDepth 16000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.SU2FourValentMatrixO4Response
open YMGap.Continuum.SU2FourValentFMoveObservableCovariance
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2TransvectantMixedPentagonGNSCompleted

local infix:50 " ≈ " => Q'.eqv

private theorem q_mul_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ (a' * b) _
    (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left a' _ _ hb)

/-- The final path form `diag(8,16)` used by the completed mixed pentagon. -/
def path3Form (x y : Q' × Q') : Q' :=
  8 * (x.1 * y.1) + 16 * (x.2 * y.2)

def path3Norm (x : Q' × Q') : Q' := path3Form x x

def path3Quadratic (x : Q' × Q') (M : IntertwinerMat2) : Q' :=
  path3Form x (matApply M x)

theorem path3Form_eq_gns (x y : Q' × Q') :
    path3Form x y ≈ path3GNS.B x y := by
  change 8 * (x.1 * y.1) + 16 * (x.2 * y.2) ≈
    8 * (x.1 * y.1) + 16 * (x.2 * y.2)
  exact Q'.eqv_refl _

theorem path3Form_congr {x x' y y' : Q' × Q'}
    (hx : VecEq x x') (hy : VecEq y y') :
    path3Form x y ≈ path3Form x' y' := by
  unfold path3Form
  exact QPoly.q_add_congr
    (Q'.mul_eqv_congr_left 8 _ _ (q_mul_congr hx.1 hy.1))
    (Q'.mul_eqv_congr_left 16 _ _ (q_mul_congr hx.2 hy.2))

theorem mixedPentagon_state_eq (x : Q' × Q') :
    VecEq (longChart x) (shortChart x) :=
  dense_mixed_pentagon x

theorem mixedPentagon_observable_action (M : IntertwinerMat2)
    (x : Q' × Q') :
    VecEq (matApply M (longChart x)) (matApply M (shortChart x)) :=
  matApply_congr M (mixedPentagon_state_eq x)

theorem mixedPentagon_norm_eqv (x : Q' × Q') :
    path3Norm (longChart x) ≈ path3Norm (shortChart x) := by
  unfold path3Norm
  exact path3Form_congr (mixedPentagon_state_eq x)
    (mixedPentagon_state_eq x)

theorem mixedPentagon_quadratic_eqv (M : IntertwinerMat2)
    (x : Q' × Q') :
    path3Quadratic (longChart x) M ≈
      path3Quadratic (shortChart x) M := by
  unfold path3Quadratic
  exact path3Form_congr (mixedPentagon_state_eq x)
    (mixedPentagon_observable_action M x)

theorem shortRoute_norm_pos (x : Q' × Q')
    (hpos : (0 : Q') < path3Norm (longChart x)) :
    (0 : Q') < path3Norm (shortChart x) :=
  Q'.pos_of_lt_of_le hpos
    (Q'.ge_of_eqv (Q'.eqv_symm (mixedPentagon_norm_eqv x)))

private theorem divPos_eqv_divPos_of_cross {p q p' q' : Q'}
    (hq : (0 : Q') < q) (hq' : (0 : Q') < q')
    (hcross : (p * q') ≈ (p' * q)) :
    Q'.divPos p q hq ≈ Q'.divPos p' q' hq' := by
  let c := Q'.divPos p' q' hq'
  have hright : ((c * q) * q') ≈ (p' * q) := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv c q q') ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left c _ _ (Q'.mul_comm_eqv q q')) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv c q' q)) ?_
    exact Q'.mul_eqv_congr_right _ _ q (Q'.divPos_mul_eqv p' q' hq')
  have hmul : (p * q') ≈ ((c * q) * q') :=
    Q'.eqv_trans _ _ _ hcross (Q'.eqv_symm hright)
  have hcancel : p ≈ (c * q) := by
    apply Q'.mul_left_cancel_of_pos hq'
    refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv q' p) ?_
    refine Q'.eqv_trans _ _ _ hmul ?_
    exact Q'.mul_comm_eqv (c * q) q'
  apply Q'.mul_left_cancel_of_pos hq
  refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv q (Q'.divPos p q hq)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.divPos_mul_eqv p q hq) ?_
  refine Q'.eqv_trans _ _ _ hcancel ?_
  exact Q'.mul_comm_eqv c q

private theorem divPos_eqv_congr {p p' q q' : Q'}
    (hq : (0 : Q') < q) (hq' : (0 : Q') < q')
    (hp : p ≈ p') (hden : q ≈ q') :
    Q'.divPos p q hq ≈ Q'.divPos p' q' hq' := by
  apply divPos_eqv_divPos_of_cross hq hq'
  exact Q'.eqv_trans _ (p' * q') _
    (Q'.mul_eqv_congr_right _ _ _ hp)
    (Q'.mul_eqv_congr_left p' _ _ (Q'.eqv_symm hden))

def path3NormalizedExpectation (x : Q' × Q')
    (hpos : (0 : Q') < path3Norm x) (M : IntertwinerMat2) : Q' :=
  Q'.divPos (path3Quadratic x M) (path3Norm x) hpos

/-- The final normalized observable value is independent of the long or short
route through the exact mixed pentagon. -/
theorem mixedPentagon_normalizedExpectation_eqv (M : IntertwinerMat2)
    (x : Q' × Q') (hpos : (0 : Q') < path3Norm (longChart x)) :
    path3NormalizedExpectation (longChart x) hpos M ≈
      path3NormalizedExpectation (shortChart x)
        (shortRoute_norm_pos x hpos) M := by
  unfold path3NormalizedExpectation
  apply divPos_eqv_congr
  · exact mixedPentagon_quadratic_eqv M x
  · exact mixedPentagon_norm_eqv x

theorem long_basis0_norm_pos :
    (0 : Q') < path3Norm (longChart basis0) := by
  unfold path3Norm path3Form longChart edge01Chart edge12Chart edge23Chart basis0
  decide

theorem basis0_normalizedExpectation_pentagon_coherent
    (M : IntertwinerMat2) :
    path3NormalizedExpectation (longChart basis0) long_basis0_norm_pos M ≈
      path3NormalizedExpectation (shortChart basis0)
        (shortRoute_norm_pos basis0 long_basis0_norm_pos) M :=
  mixedPentagon_normalizedExpectation_eqv M basis0 long_basis0_norm_pos

end YMGap.Continuum.SU2MixedPentagonObservableCoherence

#print axioms YMGap.Continuum.SU2MixedPentagonObservableCoherence.mixedPentagon_observable_action
#print axioms YMGap.Continuum.SU2MixedPentagonObservableCoherence.mixedPentagon_quadratic_eqv
#print axioms YMGap.Continuum.SU2MixedPentagonObservableCoherence.mixedPentagon_normalizedExpectation_eqv
#print axioms YMGap.Continuum.SU2MixedPentagonObservableCoherence.basis0_normalizedExpectation_pentagon_coherent
