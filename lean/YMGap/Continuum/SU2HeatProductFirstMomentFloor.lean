/-
# A first-moment floor for a product of truncated SU(2) heat modes

This is the scalar inequality used after a positive harmonic decomposition.
It makes no assertion that such a decomposition exists for a given carrier.
-/

import YMGap.Continuum.SU2HeatProductTaylorRemainder
import YMGap.Continuum.HeatKernelRGStep

namespace YMGap.Continuum.SU2HeatProductFirstMomentFloor

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.SU2HeatCutoffCasimirBound
open YMGap.Continuum.SU2HeatProductTaylorRemainder

local infix:50 " ≈ " => Q'.eqv

/-- The integral total Casimir exponent attached to a list of SU(2) labels. -/
def totalCasimirNat : List Nat → Nat
  | [] => 0
  | d :: ds => d * (d + 2) + totalCasimirNat ds

/-- The rational and integral presentations of total Casimir agree. -/
theorem totalCasimir_eq_ofNat : ∀ ds : List Nat,
    totalCasimir ds ≈ Q'.ofNat (totalCasimirNat ds)
  | [] => by
      change (0 : Q') ≈ Q'.ofNat 0
      decide
  | d :: ds => by
      change Q'.ofNat (d * (d + 2)) + totalCasimir ds ≈
        Q'.ofNat (d * (d + 2) + totalCasimirNat ds)
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left _ _ _ (totalCasimir_eq_ofNat ds))
        (Q'.eqv_symm (Q'.ofNat_add_eqv _ _))

/-- If every label survives the cutoff, the product attenuation is the power
whose exponent is the integral total Casimir. -/
theorem productAttenuation_eq_qpow_total {w : Q'} (K : Nat) :
    ∀ ds : List Nat, (∀ d, d ∈ ds → d ≤ K) →
      productAttenuation w K ds ≈ RGTransport.qpow w (totalCasimirNat ds)
  | [], _ => by
      change (1 : Q') ≈ RGTransport.qpow w 0
      exact Q'.eqv_refl _
  | d :: ds, hlabels => by
      have hd : d ≤ K := hlabels d (by simp)
      have htail : ∀ e, e ∈ ds → e ≤ K := by
        intro e he
        exact hlabels e (by simp [he])
      change attenuation w K d * productAttenuation w K ds ≈
        RGTransport.qpow w (d * (d + 2) + totalCasimirNat ds)
      unfold attenuation
      rw [if_pos hd]
      exact Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left _ _ _
          (productAttenuation_eq_qpow_total K ds htail))
        (Q'.eqv_symm (HeatKernelRGStep.qpow_add w _ _))

/-- Powers on `[0,1]` decrease when their exponent increases. -/
theorem qpow_antitone_exponent {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw1 : w ≤ (1 : Q')) {a b : Nat} (hab : a ≤ b) :
    RGTransport.qpow w b ≤ RGTransport.qpow w a := by
  have hfactor : RGTransport.qpow w (b - a) ≤ (1 : Q') := qpow_le_one hw0 hw1 _
  have hmul := Q'.mul_le_mul_of_nonneg_left _ _ (RGTransport.qpow w a) hfactor
    (qpow_nonneg w hw0 a)
  have hab' : a + (b - a) = b := Nat.add_sub_of_le hab
  have hadd := HeatKernelRGStep.qpow_add w a (b - a)
  rw [hab'] at hadd
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv hadd)
    (Q'.le_trans' _ _ _ hmul (Q'.le_of_eqv (Q'.mul_one_eqv _)))

private theorem label_le_totalCasimirNat {d : Nat} : ∀ {ds : List Nat},
    d ∈ ds → d ≤ totalCasimirNat ds
  | [], h => by simp at h
  | e :: es, h => by
      simp only [List.mem_cons] at h
      unfold totalCasimirNat
      rcases h with rfl | htail
      · have hpos : 0 < d + 2 := by omega
        exact Nat.le_trans (Nat.le_mul_of_pos_right d hpos) (Nat.le_add_right _ _)
      · exact Nat.le_trans (label_le_totalCasimirNat htail) (Nat.le_add_left _ _)

private theorem productAttenuation_nonnegative {w : Q'} (hw0 : (0 : Q') ≤ w)
    (K : Nat) : ∀ ds : List Nat, (0 : Q') ≤ productAttenuation w K ds
  | [] => Q'.zero_le_one
  | d :: ds => Q'.mul_nonneg _ _ (attenuation_nonnegative hw0 K d)
      (productAttenuation_nonnegative hw0 K ds)

private theorem sub_nonpos_of_le {a b : Q'} (h : a ≤ b) :
    a - b ≤ (0 : Q') := by
  have hadd := Q'.add_le_add_right a b (-b) h
  exact Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv (Q'.add_neg_self_eqv b))

private theorem sub_le_self_of_nonnegative (a : Q') {b : Q'}
    (hb : (0 : Q') ≤ b) : a - b ≤ a := by
  have hneg : -b ≤ (0 : Q') := by
    have hadd := Q'.add_le_add_right 0 b (-b) hb
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.eqv_symm (QPoly.q_zero_add_eqv (-b))))
      (Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv (Q'.add_neg_self_eqv b)))
  have hadd := Q'.add_le_add_left a (-b) 0 hneg
  rw [Q'.add_zero' a] at hadd
  exact hadd

/-- First-moment lower floor for the actual product attenuation.  Below total
Casimir `M`, all labels survive when `M ≤ K`, and `w^t ≥ w^M`; above `M`
the affine factor on the left is nonpositive. -/
theorem productAttenuation_firstMoment_floor {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (K M : Nat) (hMK : M ≤ K) (ds : List Nat) :
    RGTransport.qpow w M * (Q'.ofNat M - totalCasimir ds) ≤
      Q'.ofNat M * productAttenuation w K ds := by
  have hM0 : (0 : Q') ≤ Q'.ofNat M := zero_le_ofNat M
  have ht0 : (0 : Q') ≤ totalCasimir ds := by
    exact Q'.le_trans' _ _ _ (zero_le_ofNat (totalCasimirNat ds))
      (Q'.ge_of_eqv (totalCasimir_eq_ofNat ds))
  by_cases hlow : totalCasimirNat ds ≤ M
  · have hlabels : ∀ d, d ∈ ds → d ≤ K := by
      intro d hd
      exact Nat.le_trans (Nat.le_trans (label_le_totalCasimirNat hd) hlow) hMK
    have hprod := productAttenuation_eq_qpow_total (w := w) K ds hlabels
    have hpow : RGTransport.qpow w M ≤ RGTransport.qpow w (totalCasimirNat ds) :=
      qpow_antitone_exponent hw0 hw1 hlow
    have hsub : Q'.ofNat M - totalCasimir ds ≤ Q'.ofNat M :=
      sub_le_self_of_nonnegative _ ht0
    have hleft := Q'.mul_le_mul_of_nonneg_left _ _ (RGTransport.qpow w M) hsub
      (qpow_nonneg w hw0 M)
    have hright := Q'.mul_le_mul_of_nonneg_right _ _ (Q'.ofNat M) hpow hM0
    exact Q'.le_trans' _ _ _ hleft
      (Q'.le_trans' _ _ _ hright (Q'.le_of_eqv
        (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _)
          (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hprod)))))
  · have hhigh : M ≤ totalCasimirNat ds := by omega
    have hMT : Q'.ofNat M ≤ totalCasimir ds :=
      Q'.le_trans' _ _ _ (CReal.ofNat_le_ofNat hhigh)
        (Q'.ge_of_eqv (totalCasimir_eq_ofNat ds))
    have hleft0 : RGTransport.qpow w M * (Q'.ofNat M - totalCasimir ds) ≤ (0 : Q') :=
      Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_left _ _ (RGTransport.qpow w M)
          (sub_nonpos_of_le hMT) (qpow_nonneg w hw0 M))
        (Q'.le_of_eqv (Q'.mul_zero_eqv _))
    have hright0 : (0 : Q') ≤ Q'.ofNat M * productAttenuation w K ds :=
      Q'.mul_nonneg _ _ hM0 (productAttenuation_nonnegative hw0 K ds)
    exact Q'.le_trans' _ _ _ hleft0 hright0

#print axioms totalCasimirNat
#print axioms totalCasimir_eq_ofNat
#print axioms productAttenuation_eq_qpow_total
#print axioms qpow_antitone_exponent
#print axioms productAttenuation_firstMoment_floor

end YMGap.Continuum.SU2HeatProductFirstMomentFloor
