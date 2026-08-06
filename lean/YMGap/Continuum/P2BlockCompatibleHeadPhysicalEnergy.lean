/-
Track 11.7-fusion / R3l -- slow log-curvature of the physical head.

Ordinary log-concavity is insufficient for the two-step Dirichlet-energy
comparison: an arbitrarily narrow log-concave peak is a counterexample.  The
physical heat string has the stronger exact ratio law

  c_s*c_(s+2) / c_(s+1)^2
    = w^2 * (s+1)(s+3)/(s+2)^2.

At every open scale `k>=8`, `w>=127/128`; for `s>=1` the dimension ratio is at
least `8/9`.  The fixed rational comparison
`(7/8) <= (8/9)*(127/128)^2` therefore gives the uniform reverse-curvature
factor `7/8`.  This is proof about the growing coefficient computation, not a
scale-by-scale evaluation.

No `Classical`, `native_decide`, `sorry`, custom axiom, or noncomputable
declaration.
-/

import YMGap.Continuum.P2BlockCompatibleHeadPhysicalBoundary
import YMGap.Continuum.FusionGenFunction

namespace YMGap.Continuum.P2BlockCompatibleHeadPhysicalEnergy

set_option maxRecDepth 30000
set_option maxHeartbeats 2000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FusionGenFunction
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.P2BlockCompatibleSchedule
open YMGap.Continuum.P2BlockCompatibleScheduleClosed
open YMGap.Continuum.RGTransport

local infix:50 " ≈ " => Q'.eqv

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.mul_num_cast, Q'.mul_den_cast];
             ac_rfl))

private def q127 : Q' := Q'.mkPos 127 128 (by decide)
private def qSevenEighths : Q' := Q'.mkPos 7 8 (by decide)
private def qEightNinths : Q' := Q'.mkPos 8 9 (by decide)

private theorem physicalWeightDen_ge_128 (r : Nat) :
    128 <= physicalWeightDen (r + 8) := by
  have hp : 4 ^ 8 <= 4 ^ (r + 8) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have h := Nat.mul_le_mul_left 12 hp
  unfold physicalWeightDen
  exact Nat.le_trans (by decide : 128 <= 12 * 4 ^ 8) h

private theorem q127_le_closedWeight (D : Nat) (hD : 0 < D)
    (h128 : 128 <= D) :
    q127 <= Q'.mkPos ((D - 1 : Nat) : Int) D hD := by
  show q127.num * ((Q'.mkPos ((D - 1 : Nat) : Int) D hD).den : Int) <=
    (Q'.mkPos ((D - 1 : Nat) : Int) D hD).num * (q127.den : Int)
  unfold q127
  rw [Q'.mkPos_num, Q'.mkPos_den, Q'.mkPos_num, Q'.mkPos_den]
  push_cast
  exact_mod_cast (show 127 * D <= (D - 1) * 128 by omega)

/-- Every physical head scale lies in the fixed weak-coupling interval used
by the reverse-curvature certificate. -/
theorem physicalWeight_ge_127 (r : Nat) :
    q127 <= blockWeight (r + 8) := by
  let D := physicalWeightDen (r + 8)
  have hclosed := blockWeight_eqv_closed (r + 8)
  have hnum : physicalWeightNum (r + 8) = D - 1 := rfl
  rw [hnum] at hclosed
  exact Q'.le_trans' _ _ _
    (q127_le_closedWeight D (physicalWeightDen_pos (r + 8))
      (physicalWeightDen_ge_128 r))
    (Q'.ge_of_eqv hclosed)

private theorem dimension_reverse_curvature (s : Nat) (hs : 1 <= s) :
    qEightNinths * (dimQ (s + 1) * dimQ (s + 1)) <=
      dimQ s * dimQ (s + 2) := by
  have hsq : 1 <= s * s := Nat.mul_le_mul hs hs
  have hnat :
      8 * ((s + 1 + 1) * (s + 1 + 1)) <=
        (s + 1) * (s + 1 + 1 + 1) * 9 := by
    simp only [Nat.mul_add, Nat.add_mul]
    omega
  show
    (qEightNinths * (dimQ (s + 1) * dimQ (s + 1))).num *
        ((dimQ s * dimQ (s + 2)).den : Int) <=
      (dimQ s * dimQ (s + 2)).num *
        ((qEightNinths * (dimQ (s + 1) * dimQ (s + 1))).den : Int)
  unfold qEightNinths dimQ
  simp only [Q'.mul_num_cast, Q'.mul_den_cast, Q'.ofNat_num_cast,
    Q'.ofNat_den_cast, Q'.mkPos_num, Q'.mkPos_den, Int.mul_one]
  push_cast
  exact_mod_cast hnat

private theorem scalar_reverse_curvature {w : Q'}
    (hw : q127 <= w) (s : Nat) (hs : 1 <= s) :
    qSevenEighths * (dimQ (s + 1) * dimQ (s + 1)) <=
      (dimQ s * dimQ (s + 2)) * qpow w 2 := by
  have hconst :
      qSevenEighths <= qEightNinths * qpow q127 2 := by
    decide
  have hD0 : (0 : Q') <= dimQ (s + 1) * dimQ (s + 1) :=
    Q'.mul_nonneg _ _ (dimQ_nonneg _) (dimQ_nonneg _)
  have hq0 : (0 : Q') <= qpow q127 2 := qpow_nonneg _ (by decide) 2
  have hscale := Q'.mul_le_mul_of_nonneg_right _ _
    (dimQ (s + 1) * dimQ (s + 1)) hconst hD0
  have hdim := Q'.mul_le_mul_of_nonneg_left _ _
    (qpow q127 2) (dimension_reverse_curvature s hs) hq0
  have hpow : qpow q127 2 <= qpow w 2 := qpow_mono (by decide) hw 2
  have hDprod0 : (0 : Q') <= dimQ s * dimQ (s + 2) :=
    Q'.mul_nonneg _ _ (dimQ_nonneg _) (dimQ_nonneg _)
  have hpowScaled := Q'.mul_le_mul_of_nonneg_left _ _
    (dimQ s * dimQ (s + 2)) hpow hDprod0
  have hre1 :
      (qEightNinths * qpow q127 2) *
          (dimQ (s + 1) * dimQ (s + 1)) ≈
        qpow q127 2 *
          (qEightNinths * (dimQ (s + 1) * dimQ (s + 1))) := by
    ring_qeqv
  have hre2 :
      qpow q127 2 * (dimQ s * dimQ (s + 2)) ≈
        (dimQ s * dimQ (s + 2)) * qpow q127 2 :=
    Q'.mul_comm_eqv _ _
  exact Q'.le_trans' _ _ _ hscale
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hre1)
      (Q'.le_trans' _ _ _ hdim
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv hre2) hpowScaled)))

/-- **Broad physical peak.**  Consecutive heat coefficients cannot form the
narrow log-concave spike that defeats the two-step energy inequality. -/
theorem physical_coeff_reverse_curvature (r s : Nat) (hs : 1 <= s) :
    qSevenEighths *
        (coeffW (blockWeight (r + 8)) (s + 1) *
          coeffW (blockWeight (r + 8)) (s + 1)) <=
      coeffW (blockWeight (r + 8)) s *
        coeffW (blockWeight (r + 8)) (s + 2) := by
  let w := blockWeight (r + 8)
  let H := heatNorm w (s + 1) * heatNorm w (s + 1)
  have hw0 : (0 : Q') <= w := blockWeight_nonneg (r + 8)
  have hscalar := scalar_reverse_curvature (physicalWeight_ge_127 r) s hs
  have hH0 : (0 : Q') <= H :=
    Q'.mul_nonneg _ _ (qpow_nonneg _ hw0 _) (qpow_nonneg _ hw0 _)
  have hscaled := Q'.mul_le_mul_of_nonneg_right _ _ H hscalar hH0
  have hleft :
      qSevenEighths * (coeffW w (s + 1) * coeffW w (s + 1)) ≈
        (qSevenEighths * (dimQ (s + 1) * dimQ (s + 1))) * H := by
    unfold H heatNorm
    change qSevenEighths *
        ((dimQ (s + 1) * qpow w (c4 (s + 1))) *
          (dimQ (s + 1) * qpow w (c4 (s + 1)))) ≈ _
    refine Q'.eqv_trans _
      (qSevenEighths *
        ((dimQ (s + 1) * dimQ (s + 1)) *
          (qpow w (c4 (s + 1)) * qpow w (c4 (s + 1))))) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left qSevenEighths _ _ (mul_swap4 _ _ _ _)
    · exact Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)
  have hright :
      ((dimQ s * dimQ (s + 2)) * qpow w 2) * H ≈
        coeffW w s * coeffW w (s + 2) := by
    unfold H
    have hheat := heatNorm_logConcave_exact w s
    change ((dimQ s * dimQ (s + 2)) * qpow w 2) *
        (heatNorm w (s + 1) * heatNorm w (s + 1)) ≈
      (dimQ s * heatNorm w s) * (dimQ (s + 2) * heatNorm w (s + 2))
    refine Q'.eqv_trans _
      ((dimQ s * dimQ (s + 2)) *
        (qpow w 2 * (heatNorm w (s + 1) * heatNorm w (s + 1)))) _ ?_ ?_
    · exact Q'.mul_assoc_eqv _ _ _
    · refine Q'.eqv_trans _
        ((dimQ s * dimQ (s + 2)) *
          (heatNorm w s * heatNorm w (s + 2))) _
          (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hheat)) ?_
      exact Q'.eqv_symm (mul_swap4 _ _ _ _)
  dsimp only [w] at hleft hright hscaled ⊢
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hright))

#print axioms physicalWeight_ge_127
#print axioms physical_coeff_reverse_curvature

end YMGap.Continuum.P2BlockCompatibleHeadPhysicalEnergy
