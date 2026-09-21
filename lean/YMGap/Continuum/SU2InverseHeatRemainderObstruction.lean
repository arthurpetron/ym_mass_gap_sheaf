/-
# A coefficient-level inverse-heat remainder obstruction

On the SU(2) character labels, the physical heat coefficient is
`physLinkWeight w j = w^(j*(j+2))`.  Successive labels therefore differ by
the exact factor `w^(2*j+3)`.  At `w = 1/2`, the inverse of that factor grows
like `2^(2*j+3)`, and the positive commutator remainder below is at least
`6*4^j`.

This is deliberately only a scalar coefficient certificate.  It does not
assert an arbitrary-spin `productMap` eigenvector theorem for the interacting
slab, does not identify a signed character input with the positive endpoint
weight, and does not lower-bound the full double commutator (whose discarded
negative-square diagonal has the opposite high-spin effect).
-/

import YMGap.Continuum.PeterWeylRealWeight
import YMGap.Continuum.BF4ExactSlabThermodynamicDyadicEnergy
import YMGap.Continuum.SU2PointwiseHeatSpacingCompletion
import YMGap.Constructive.CRealLogRatCongruence

namespace YMGap.Continuum.SU2InverseHeatRemainderObstruction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.RGTransport
open YMGap.Continuum.PeterWeylRealWeight
open YMGap.Continuum.BondMovingScaledNorm (qpow_pos c4_succ)
open YMGap.Continuum.BF4ExactSlabThermodynamicDyadicEnergy (half_power_normalizes)

local infix:50 " ≈ " => Q'.eqv

private theorem half_pos : (0 : Q') < HalfPow.half := by decide

private theorem recip_eqv_of_mul_eqv_one {q r : Q'} (hq : (0 : Q') < q)
    (h : q * r ≈ 1) : Q'.recipPos q hq ≈ r := by
  show (Q'.recipPos q hq).num * (r.den : Int) =
    r.num * ((Q'.recipPos q hq).den : Int)
  rw [Q'.recipPos_num, Q'.recipPos_den]
  show (q.den : Int) * (r.den : Int) = r.num * q.num
  have h' : q.num * r.num = (q.den : Int) * (r.den : Int) := by
    change (q * r).num * (1 : Int) = (1 : Int) * ((q * r).den : Int) at h
    simpa only [Q'.mul_num_cast, Q'.mul_den_cast, Int.mul_one, Int.one_mul] using h
  rw [← h', Int.mul_comm q.num r.num]

private theorem half_qpow_normalizes (k : Nat) :
    RGTransport.qpow HalfPow.half k * Q'.ofNat (2 ^ k) ≈ 1 :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _
      (SU2PointwiseHeatSpacingCompletion.qpow_eqv_pow HalfPow.half k))
    (half_power_normalizes k)

/-- The constructive reciprocal of a dyadic heat power is the corresponding
integer power of two. -/
theorem recip_half_qpow (k : Nat) :
    Q'.recipPos (RGTransport.qpow HalfPow.half k) (qpow_pos half_pos k) ≈
      Q'.ofNat (2 ^ k) :=
  recip_eqv_of_mul_eqv_one (qpow_pos half_pos k) (half_qpow_normalizes k)

/-- Exact adjacent-label factorization of the physical heat coefficient. -/
theorem physLinkWeight_succ_factor (w : Q') (j : Nat) :
    physLinkWeight w (j + 1) ≈
      physLinkWeight w j * RGTransport.qpow w (2 * j + 3) := by
  unfold physLinkWeight
  rw [c4_succ j]
  exact HeatKernelRGStep.qpow_add w (c4 j) (2 * j + 3)

private theorem mul_recip_mul_right {a b : Q'} (ha : (0 : Q') < a) :
    (a * b) * Q'.recipPos a ha ≈ b := by
  refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv a b (Q'.recipPos a ha)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left a _ _ (Q'.mul_comm_eqv b (Q'.recipPos a ha))) ?_
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv a (Q'.recipPos a ha) b)) ?_
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_recipPos_eqv a ha))
    (Q'.one_mul_eqv b)

private theorem mul_recip_mul_left {a b : Q'} (ha : (0 : Q') < a)
    (hb : (0 : Q') < b) :
    a * Q'.recipPos (a * b) (Q'.mul_pos ha hb) ≈ Q'.recipPos b hb := by
  apply Q'.eqv_symm
  apply recip_eqv_of_mul_eqv_one hb
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv b a (Q'.recipPos (a*b) (Q'.mul_pos ha hb)))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv b a)) ?_
  exact Q'.mul_recipPos_eqv (a*b) (Q'.mul_pos ha hb)

private theorem recip_mul_factor {a b : Q'} (ha : (0 : Q') < a)
    (hb : (0 : Q') < b) :
    Q'.recipPos a ha ≈ b * Q'.recipPos (a*b) (Q'.mul_pos ha hb) := by
  apply recip_eqv_of_mul_eqv_one ha
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv a b (Q'.recipPos (a*b) (Q'.mul_pos ha hb)))) ?_
  exact Q'.mul_recipPos_eqv (a*b) (Q'.mul_pos ha hb)

/-- The positive coefficient remainder at an arbitrary strictly positive nome,
after isolating the inverse successor factor.  This is not the full
double-commutator diagonal. -/
def inverseHeatRemainderAt (w : Q') (hw0 : (0 : Q') < w) (j : Nat) : Q' :=
  (1 + -(RGTransport.qpow w 2)) *
    (Q'.recipPos (RGTransport.qpow w (2 * j + 3)) (qpow_pos hw0 (2 * j + 3)) +
      RGTransport.qpow w (2 * j + 1))

/-- The same coefficient remainder written directly as the four adjacent
ratios of the physical Peter--Weyl heat weights. -/
def rawAdjacentRemainder (w : Q') (hw0 : (0 : Q') < w) (j : Nat) : Q' :=
  let lam := physLinkWeight w
  lam (j+1) * Q'.recipPos (lam (j+2)) (qpow_pos hw0 (c4 (j+2))) +
    lam (j+1) * Q'.recipPos (lam j) (qpow_pos hw0 (c4 j)) +
    -(lam (j+2) * Q'.recipPos (lam (j+1)) (qpow_pos hw0 (c4 (j+1))) +
      lam j * Q'.recipPos (lam (j+1)) (qpow_pos hw0 (c4 (j+1))))

/-- Exact reduction of the four actual adjacent heat-weight ratios to the
factorized scalar remainder.  The displayed label is `j+1`, hence is nonzero. -/
theorem rawAdjacentRemainder_eq_factorized (w : Q') (hw0 : (0 : Q') < w)
    (j : Nat) : rawAdjacentRemainder w hw0 j ≈ inverseHeatRemainderAt w hw0 (j+1) := by
  let a := physLinkWeight w (j+1)
  let p := RGTransport.qpow w (2*j+3)
  let q := RGTransport.qpow w (2*(j+1)+3)
  let s := RGTransport.qpow w 2
  have ha : (0 : Q') < a := qpow_pos hw0 (c4 (j+1))
  have hp : (0 : Q') < p := qpow_pos hw0 (2*j+3)
  have hq : (0 : Q') < q := qpow_pos hw0 (2*(j+1)+3)
  have hs : (0 : Q') < s := qpow_pos hw0 2
  have hprev := physLinkWeight_succ_factor w j
  have hnext := physLinkWeight_succ_factor w (j+1)
  have hqsplit : q ≈ p * s := by
    unfold q p s
    rw [show 2 * (j+1) + 3 = (2*j+3)+2 by omega]
    exact HeatKernelRGStep.qpow_add w (2*j+3) 2
  have hprevPos : (0 : Q') < physLinkWeight w j := qpow_pos hw0 (c4 j)
  have hnextPos : (0 : Q') < physLinkWeight w (j+2) := qpow_pos hw0 (c4 (j+2))
  have hu : physLinkWeight w (j+1) *
      Q'.recipPos (physLinkWeight w (j+2)) hnextPos ≈ Q'.recipPos q hq := by
    have hr := Q'.recipPos_eqv_congr _ _ hnextPos (Q'.mul_pos ha hq) hnext
    exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hr)
      (mul_recip_mul_left ha hq)
  have hd : physLinkWeight w (j+1) *
      Q'.recipPos (physLinkWeight w j) hprevPos ≈ p := by
    exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hprev)
      (mul_recip_mul_right hprevPos)
  have hv : physLinkWeight w (j+2) *
      Q'.recipPos (physLinkWeight w (j+1)) ha ≈ q := by
    exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hnext)
      (mul_recip_mul_right ha)
  have he : physLinkWeight w j *
      Q'.recipPos (physLinkWeight w (j+1)) ha ≈ Q'.recipPos p hp := by
    have hr := Q'.recipPos_eqv_congr _ _ ha (Q'.mul_pos hprevPos hp) hprev
    exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hr)
      (mul_recip_mul_left hprevPos hp)
  have heSplit : Q'.recipPos p hp ≈ s * Q'.recipPos q hq := by
    have hr := Q'.recipPos_eqv_congr _ _ hq (Q'.mul_pos hp hs) hqsplit
    exact Q'.eqv_trans _ _ _ (recip_mul_factor hp hs)
      (Q'.mul_eqv_congr_left s _ _ (Q'.eqv_symm hr))
  have hsub : q ≈ p*s := hqsplit
  unfold rawAdjacentRemainder inverseHeatRemainderAt
  dsimp only
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr'
      (Q'.add_eqv_congr' hu hd)
      (Q'.neg_eqv_congr _ _ (Q'.add_eqv_congr' hv he))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.neg_eqv_congr _ _ (Q'.add_eqv_congr' hsub heSplit))) ?_
  exact poly_identity_of_normal_eq
    (.add (.add (.var 0) (.var 1))
      (.neg (.add (.mul (.var 1) (.var 2)) (.mul (.var 2) (.var 0)))))
    (.mul (.add (.const 1) (.neg (.var 2))) (.add (.var 0) (.var 1)))
    (by decide) (fun | 0 => Q'.recipPos q hq | 1 => p | _ => s)

/-- Dyadic specialization used for the explicit `6*4^j` certificate. -/
def inverseHeatRemainder (j : Nat) : Q' :=
  inverseHeatRemainderAt HalfPow.half half_pos j

theorem inverseHeatRemainder_half (j : Nat) :
    inverseHeatRemainder j =
      inverseHeatRemainderAt HalfPow.half half_pos j := rfl

private theorem two_pow_odd (j : Nat) :
    2 ^ (2 * j + 3) = 8 * 4 ^ j := by
  rw [show 2 * j + 3 = 3 + 2 * j by omega, Nat.pow_add]
  change 8 * 2 ^ (2 * j) = 8 * 4 ^ j
  congr 1
  rw [Nat.pow_mul]

private theorem leading_term (j : Nat) :
    (1 + -(RGTransport.qpow HalfPow.half 2)) *
      Q'.recipPos (RGTransport.qpow HalfPow.half (2 * j + 3))
        (qpow_pos half_pos (2 * j + 3)) ≈
      6 * Q'.ofNat (4 ^ j) := by
  have hr := recip_half_qpow (2 * j + 3)
  have hp : Q'.ofNat (2 ^ (2 * j + 3)) ≈ 8 * Q'.ofNat (4 ^ j) := by
    rw [two_pow_odd j]
    exact HeatKernelRGStep.ofNat_mul_eqv 8 (4 ^ j)
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hr) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hp) ?_
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
    (Q'.mul_eqv_congr_right _ _ _
      (by decide : ((1 + -(RGTransport.qpow HalfPow.half 2)) * 8) ≈ 6))

/-- At the dyadic nome, the positive inverse-heat remainder grows at least as
`6*4^j`.  Hence this particular positive remainder has no spin-uniform cap. -/
theorem six_four_pow_le_inverseHeatRemainder (j : Nat) :
    6 * Q'.ofNat (4 ^ j) ≤ inverseHeatRemainder j := by
  unfold inverseHeatRemainder inverseHeatRemainderAt
  have htail : (0 : Q') ≤
      (1 + -(RGTransport.qpow HalfPow.half 2)) * RGTransport.qpow HalfPow.half (2 * j + 1) := by
    exact Q'.mul_nonneg _ _ (by decide)
      (RGTransport.qpow_nonneg HalfPow.half HalfPow.half_nonneg _)
  have hsplit : inverseHeatRemainder j ≈
      (1 + -(RGTransport.qpow HalfPow.half 2)) *
          Q'.recipPos (RGTransport.qpow HalfPow.half (2 * j + 3))
            (qpow_pos half_pos (2 * j + 3)) +
        (1 + -(RGTransport.qpow HalfPow.half 2)) * RGTransport.qpow HalfPow.half (2 * j + 1) :=
    Q'.mul_add_eqv _ _ _
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (leading_term j))
    (Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ _ htail)
      (Q'.le_of_eqv (Q'.eqv_symm hsplit)))

/-- Pure scalar bookkeeping explaining the scope: adding the discarded
negative-square diagonal to the positive remainder cancels the growing
inverse terms rather than preserving their lower bound. -/
theorem full_diagonal_cancellation (u d v e : Q') :
    (4 + -(u + d + v + e)) + (u + d + -(v + e)) ≈
      4 + -(2 * (v + e)) := by
  exact poly_identity_of_normal_eq
    (.add (.add (.const 4) (.neg (.add (.add (.add (.var 0) (.var 1)) (.var 2)) (.var 3))))
      (.add (.add (.var 0) (.var 1)) (.neg (.add (.var 2) (.var 3)))))
    (.add (.const 4) (.neg (.mul (.const 2) (.add (.var 2) (.var 3)))))
    (by decide) (fun | 0 => u | 1 => d | 2 => v | _ => e)

end YMGap.Continuum.SU2InverseHeatRemainderObstruction

#print axioms YMGap.Continuum.SU2InverseHeatRemainderObstruction.recip_half_qpow
#print axioms YMGap.Continuum.SU2InverseHeatRemainderObstruction.physLinkWeight_succ_factor
#print axioms YMGap.Continuum.SU2InverseHeatRemainderObstruction.inverseHeatRemainderAt
#print axioms YMGap.Continuum.SU2InverseHeatRemainderObstruction.rawAdjacentRemainder
#print axioms YMGap.Continuum.SU2InverseHeatRemainderObstruction.rawAdjacentRemainder_eq_factorized
#print axioms YMGap.Continuum.SU2InverseHeatRemainderObstruction.inverseHeatRemainder
#print axioms YMGap.Continuum.SU2InverseHeatRemainderObstruction.inverseHeatRemainder_half
#print axioms YMGap.Continuum.SU2InverseHeatRemainderObstruction.six_four_pow_le_inverseHeatRemainder
#print axioms YMGap.Continuum.SU2InverseHeatRemainderObstruction.full_diagonal_cancellation
