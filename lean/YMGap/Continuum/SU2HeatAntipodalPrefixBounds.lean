/-
# Strict antipodal jet margins for every original later heat prefix

At the explicit nome 5/8, the ORIGINAL inclusive SU(2) character sums
have H_K>0 and B_K>6 H_K for every K>=4. Here B_K is THREE times
the selected antipodal second angular jet, not a replacement heat law.
The geometric Casimir tail is bounded after label five, so no infinite
series, alternating-series oracle or pointwise interpretation of a Haar
certificate is used. The quaternion jet identification is separate.

These scalar signs reject a universal positive-curvature shortcut for a
single heat factor. They assert nothing about the complete interacting
BF4 weight, a signed aggregate estimate, or continuum Yang--Mills.
-/

import YMGap.Continuum.BondMovingScaledNorm
import YMGap.Constructive.CornerBound
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.SU2HeatAntipodalPrefixBounds

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv

private theorem strict_add_cancel {a b c : Q'} (h : a+c < b+c) : a < b := by
  apply Int.not_le.mp
  intro hab
  exact (Int.not_le.mpr h) (Q'.add_le_add_right _ _ c hab)

/-- Original character value at the antipode, including label zero. -/
def endpointValue (w : Q') (K : Nat) : Q' :=
  finSum (fun j => (-1 : Q')^j * Q'.ofNat ((j+1)^2) * qpow w (c4 j)) (K+1)

/-- Three times the original antipodal second angular jet. -/
def endpointSecondThree (w : Q') (K : Nat) : Q' :=
  finSum (fun j => (-1 : Q')^(j+1) * Q'.ofNat ((j+1)^2*c4 j) *
    qpow w (c4 j)) (K+1)

/-- A concrete strict nome, not a scaling-family parameter. -/
def witnessNome : Q' := Q'.mkPos 5 8 (by decide)

private theorem unitSign_bounds (n : Nat) :
    (-1 : Q')^n ≤ 1 ∧ -((-1 : Q')^n) ≤ 1 := by
  induction n with
  | zero => exact ⟨by decide, by decide⟩
  | succ n ih =>
      have h : (-1 : Q') * (-1 : Q')^n ≈ -((-1 : Q')^n) :=
        poly_identity_of_normal_eq (.mul (.const (-1)) (.var 0))
          (.neg (.var 0)) (by decide) (fun _ => (-1 : Q')^n)
      constructor
      · exact Q'.le_trans' _ _ _ (Q'.le_of_eqv h) ih.2
      · exact Q'.le_trans' _ _ _ (Q'.le_of_eqv
          (Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ h)
            (Q'.neg_neg_eqv _))) ih.1

private theorem signed_product_bound (n : Nat) {a b : Q'}
    (ha : (0 : Q') ≤ a) (hab : a ≤ b) :
    (-1 : Q')^n*a ≤ b ∧ -((-1 : Q')^n*a) ≤ b := by
  have h := unitSign_bounds n
  constructor
  · exact Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ a h.1 ha)
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.one_mul_eqv a)) hab)
  · exact Q'.le_trans' _ _ _
      (Q'.ge_of_eqv (Q'.neg_mul_eqv ((-1 : Q')^n) a))
      (Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right _ _ a h.2 ha)
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.one_mul_eqv a)) hab))

private theorem casimir_le_square (j : Nat) : c4 j ≤ (j+1)^2 := by
  unfold c4
  simp only [Nat.pow_succ, Nat.pow_zero, Nat.mul_one, Nat.mul_add, Nat.add_mul,
    Nat.one_mul]
  omega

private theorem valueTerm_bound {w : Q'} (hw : (0 : Q') ≤ w) (j : Nat) :
    (-1 : Q')^j * Q'.ofNat ((j+1)^2) * qpow w (c4 j) ≤ tailTerm w 4 j ∧
      -((-1 : Q')^j * Q'.ofNat ((j+1)^2) * qpow w (c4 j)) ≤ tailTerm w 4 j := by
  have hnat : (j+1)^2 ≤ (j+1)^4 := Nat.pow_le_pow_right (by omega) (by decide)
  have hab := Q'.mul_le_mul_of_nonneg_right _ _ (qpow w (c4 j))
    (CReal.ofNat_le_ofNat hnat) (qpow_nonneg w hw _)
  have h := signed_product_bound j
    (Q'.mul_nonneg _ _ (zero_le_ofNat _) (qpow_nonneg w hw _)) hab
  have hp : (-1 : Q')^j * Q'.ofNat ((j+1)^2) * qpow w (c4 j) ≈
      (-1 : Q')^j * (Q'.ofNat ((j+1)^2) * qpow w (c4 j)) :=
    Q'.mul_assoc_eqv _ _ _
  exact ⟨Q'.le_trans' _ _ _ (Q'.le_of_eqv hp) h.1,
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.neg_eqv_congr _ _ hp)) h.2⟩

private theorem secondTerm_bound {w : Q'} (hw : (0 : Q') ≤ w) (j : Nat) :
    (-1 : Q')^(j+1) * Q'.ofNat ((j+1)^2*c4 j) * qpow w (c4 j) ≤ tailTerm w 4 j ∧
      -((-1 : Q')^(j+1) * Q'.ofNat ((j+1)^2*c4 j) * qpow w (c4 j)) ≤
        tailTerm w 4 j := by
  have hnat : (j+1)^2*c4 j ≤ (j+1)^4 := by
    have h := Nat.mul_le_mul_left ((j+1)^2) (casimir_le_square j)
    simpa only [← Nat.pow_add] using h
  have hab := Q'.mul_le_mul_of_nonneg_right _ _ (qpow w (c4 j))
    (CReal.ofNat_le_ofNat hnat) (qpow_nonneg w hw _)
  have h := signed_product_bound (j+1)
    (Q'.mul_nonneg _ _ (zero_le_ofNat _) (qpow_nonneg w hw _)) hab
  have hp : (-1 : Q')^(j+1) * Q'.ofNat ((j+1)^2*c4 j) * qpow w (c4 j) ≈
      (-1 : Q')^(j+1) * (Q'.ofNat ((j+1)^2*c4 j) * qpow w (c4 j)) :=
    Q'.mul_assoc_eqv _ _ _
  exact ⟨Q'.le_trans' _ _ _ (Q'.le_of_eqv hp) h.1,
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.neg_eqv_congr _ _ hp)) h.2⟩

private theorem tail_bound (M : Nat) : tailWindow witnessNome 4 5 M ≤ dyad 10 :=
  tail_modulus (by decide) (by decide) 4 10 5 (by decide) (by decide) M

private theorem prefix_corridor (f : Nat → Q')
    (hf : ∀ j, f j ≤ tailTerm witnessNome 4 j ∧ -f j ≤ tailTerm witnessNome 4 j)
    (K : Nat) (hK : 4 ≤ K) :
    finSum f (K+1) ≤ finSum f 5 + dyad 10 ∧
      finSum f 5 ≤ finSum f (K+1) + dyad 10 := by
  have hs := finSum_split f 5 (K-4)
  have he : 5+(K-4)=K+1 := by omega
  rw [he] at hs
  have hu := Q'.le_trans' _ _ _
    (CharacterTail.finSum_le_termwise _ _ (fun j => (hf (5+j)).1) (K-4))
    (tail_bound (K-4))
  have hl := Q'.le_trans' _ _ _ (Q'.le_of_eqv (neg_finSum _ (K-4)))
    (Q'.le_trans' _ _ _
      (CharacterTail.finSum_le_termwise _ _ (fun j => (hf (5+j)).2) (K-4))
      (tail_bound (K-4)))
  constructor
  · exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hs)
      (Q'.add_le_add_left _ _ _ hu)
  · have hnegative : -(dyad 10) ≤ finSum (fun j => f (5+j)) (K-4) :=
      Q'.le_trans' _ _ _ (Q'.neg_le_neg hl) (Q'.le_of_eqv (Q'.neg_neg_eqv _))
    have h0 : (0 : Q') ≤ finSum (fun j => f (5+j)) (K-4) + dyad 10 :=
      Q'.le_trans' _ _ _
        (Q'.ge_of_eqv (poly_identity_of_normal_eq
          (.add (.neg (.var 0)) (.var 0)) (.const 0)
          (by decide) (fun _ => dyad 10)))
        (Q'.add_le_add_right _ _ _ hnegative)
    exact Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ _ h0)
      (Q'.le_of_eqv (Q'.eqv_trans _ _ _
        (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _))
        (Q'.add_eqv_congr_right _ _ _ (Q'.eqv_symm hs))))

/-- Both sides of the SAME original inclusive value, uniformly in later K. -/
theorem endpointValue_corridor (K : Nat) (hK : 4 ≤ K) :
    endpointValue witnessNome K ≤ endpointValue witnessNome 4 + dyad 10 ∧
      endpointValue witnessNome 4 ≤ endpointValue witnessNome K + dyad 10 :=
  prefix_corridor _ (valueTerm_bound (by decide)) K hK

/-- Both sides of the SAME second jet, with the identical cutoff and tail. -/
theorem endpointSecondThree_corridor (K : Nat) (hK : 4 ≤ K) :
    endpointSecondThree witnessNome K ≤ endpointSecondThree witnessNome 4 + dyad 10 ∧
      endpointSecondThree witnessNome 4 ≤ endpointSecondThree witnessNome K + dyad 10 :=
  prefix_corridor _ (secondTerm_bound (by decide)) K hK

/-- Strict positivity comes from finite scalar arithmetic, NOT Haar positivity. -/
theorem endpointValue_positive (K : Nat) (hK : 4 ≤ K) :
    (0 : Q') < endpointValue witnessNome K := by
  have h := (endpointValue_corridor K hK).2
  have hbase : Q'.mkPos 1 5 (by decide) < endpointValue witnessNome 4 := by decide
  have hsmall : dyad 10 < Q'.mkPos 1 5 (by decide) := by decide
  have hlt : dyad 10 < endpointValue witnessNome K + dyad 10 :=
    HeatKernelRGStep.lt_of_lt_of_le
      (HeatKernelRGStep.lt_of_lt_of_le hsmall (Q'.le_of_lt hbase)) h
  exact strict_add_cancel (Q'.lt_of_le_of_lt
    (Q'.le_of_eqv (QPoly.q_zero_add_eqv _)) hlt)

/-- An actual positive log-Hessian numerator beyond the Ricci-two threshold.
The THREE convention is retained, so there is no reciprocal or logarithm. -/
theorem endpointSecondThree_gt_six_value (K : Nat) (hK : 4 ≤ K) :
    6*endpointValue witnessNome K < endpointSecondThree witnessNome K := by
  let H := endpointValue witnessNome K
  let B := endpointSecondThree witnessNome K
  let H4 := endpointValue witnessNome 4
  let B4 := endpointSecondThree witnessNome 4
  let d := dyad 10
  have hu : H ≤ H4+d := (endpointValue_corridor K hK).1
  have hl : B4 ≤ B+d := (endpointSecondThree_corridor K hK).2
  have h6 := Q'.mul_le_mul_of_nonneg_left _ _ 6 hu (by decide)
  have hbase : 6*H4+7*d < B4 := by decide
  have hleft : 6*H+d < B+d :=
    Q'.lt_of_le_of_lt
      (Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ d h6)
        (Q'.le_of_eqv (poly_identity_of_normal_eq
          (.add (.mul (.const 6) (.add (.var 0) (.var 1))) (.var 1))
          (.add (.mul (.const 6) (.var 0)) (.mul (.const 7) (.var 1)))
          (by decide) (fun | 0 => H4 | _ => d))))
      (HeatKernelRGStep.lt_of_lt_of_le
        hbase hl)
  exact strict_add_cancel hleft

#print axioms endpointValue_corridor
#print axioms endpointSecondThree_corridor
#print axioms endpointValue_positive
#print axioms endpointSecondThree_gt_six_value

end YMGap.Continuum.SU2HeatAntipodalPrefixBounds
