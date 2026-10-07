/-
# Literal one-sided theta series as constructive reals

The alternating half-shift prefix, one-sided odd prefix, and odd endpoint
frequency prefix retain their original N-th rational approximations.
Their actual terms are dominated by the checked derivative-weighted shell
after index zero. The named cutoff is precisely the existing shell cutoff
and is independent of the coordinate on the full interval [-1,1].

The reusable telescope proves a finite Cauchy estimate, not an analytic
input bundle. No theta addition formula, derivative-limit interchange,
curvature ceiling, original-action estimate or physical bound is claimed.
-/

import YMGap.Continuum.ThetaAlternatingKernel
import YMGap.Continuum.ThetaAlternatingEndpointRectangle
import YMGap.Continuum.ThetaAngularShellTail
import YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
import YMGap.Constructive.Reals
import YMGap.Constructive.CauchyConv

namespace YMGap.Continuum.ThetaOneSidedSeriesCompletion

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail (finSum)
open YMGap.Continuum.ThetaAlternatingKernel (alternatingTerm alternatingPartial)
open YMGap.Continuum.ThetaAlternatingMixedRectangle (oddTerm oddPartial)
open YMGap.Continuum.ThetaAlternatingEndpointRectangle (oddEndpointTerm oddEndpointJet)
open YMGap.Continuum.ThetaAngularShellTail (shellTerm shellTailCutoff shellTail_le_epsilon)
open YMGap.Continuum.ThetaParityShellWeights (chebT_abs_le_one)
open YMGap.Continuum.ChebTFwdBoundClose (ofNat_nonneg ofNat_mul_eqv ofNat_le_ofNat)
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm (listQSum)
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm (listQSum_append)
open YMGap.Continuum (telescope_up telescope_lo)

local infix:50 " ≈ " => Q'.eqv

/-- The original shell-tail cutoff, with no prefix shift or new modulus. -/
def oneSidedCutoff (w epsilon : Q') : Nat := shellTailCutoff w epsilon

private theorem abs_product_le {a b A B : Q'}
    (ha : Q'.abs a ≤ A) (hb : Q'.abs b ≤ B) (hA : (0 : Q') ≤ A) :
    Q'.abs (a*b) ≤ A*B :=
  Q'.le_trans' _ _ _ (TsumDeriv.Q'.abs_mul_le a b)
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ ha (Q'.abs_nonneg b))
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hb hA))

private theorem sign_power_abs : ∀ n : Nat, Q'.abs ((-1 : Q')^n) ≤ (1 : Q')
  | 0 => Q'.le_of_eqv (TsumDeriv.Q'.abs_of_nonneg (by decide : (0 : Q') ≤ 1))
  | n+1 => by
      rw [Q'.pow_succ]
      have hpin : (-1 : Q')*((-1 : Q')^n) ≈ -((-1 : Q')^n) :=
        Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 _)
          (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv _))
      exact Q'.le_trans' _ _ _
        (Q'.le_of_eqv (Q'.eqv_trans _ _ _
          (TsumDeriv.Q'.abs_eqv_congr hpin) (TsumDeriv.Q'.abs_neg _)))
        (sign_power_abs n)

private theorem halfShift_abs_le (n : Nat) {x : Q'}
    (hx0 : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) :
    Q'.abs (ChebyshevHalfShiftProduct.halfShiftCoord n x) ≤ Q'.ofNat (2*n+1) := by
  have hu := ChebU.absU_le n x hx1 hx0
  have hU : Q'.abs (Cheb.U n x) ≤ Q'.ofNat (n+1) := Q'.abs_le hu.2 hu.1
  have hS : Q'.abs (ChebyshevEvenSOS.sinCoord n x) ≤ Q'.ofNat n := by
    cases n with
    | zero => exact Q'.le_of_eqv (TsumDeriv.Q'.abs_of_nonneg (Q'.le_refl' 0))
    | succ n =>
        have h := ChebU.absU_le n x hx1 hx0
        exact Q'.abs_le h.2 h.1
  have hcap : Q'.ofNat (n+1)+Q'.ofNat n ≈ Q'.ofNat (2*n+1) := by
    rw [show 2*n+1 = (n+1)+n by omega]
    exact Q'.eqv_symm (Q'.ofNat_add_eqv (n+1) n)
  exact Q'.le_trans' _ _ _ (Q'.abs_add_le' _ _)
    (Q'.le_trans' _ _ _ (Q'.add_le_add hU hS) (Q'.le_of_eqv hcap))

private theorem linear_coefficient_le {n : Nat} (hn : 1 ≤ n) :
    2*n+1 ≤ 16*(n*n*n) := by
  have hn2 : n ≤ n*n := by
    have h := Nat.mul_le_mul_left n hn
    simpa only [Nat.mul_one] using h
  have hn3 : n*n ≤ n*n*n := by
    have h := Nat.mul_le_mul_left (n*n) hn
    simpa only [Nat.mul_one] using h
  omega

private theorem squared_coefficient_le {n : Nat} (hn : 1 ≤ n) :
    (2*n+1)*(2*n+1) ≤ 16*(n*n*n) := by
  have hlinear : 2*n+1 ≤ 3*n := by omega
  have hs := Nat.mul_le_mul hlinear hlinear
  have hpin : (3*n)*(3*n) = 9*(n*n) := by
    calc
      (3*n)*(3*n) = (3*3)*(n*n) := by ac_rfl
      _ = 9*(n*n) := by rw [show 3*3 = 9 by decide]
  have hn3 : n*n ≤ n*n*n := by
    have h := Nat.mul_le_mul_left (n*n) hn
    simpa only [Nat.mul_one] using h
  rw [hpin] at hs
  omega

private theorem gaussian_shell_le {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (n E c : Nat) (hE : n*n ≤ E)
    (hc : c ≤ 16*(n*n*n)) : Q'.ofNat c*w^E ≤ shellTerm w n := by
  have hp : (0 : Q') ≤ w^E := Q'.pow_nonneg w (Q'.le_of_lt hw0) E
  have hcoef : Q'.ofNat c ≤ 16*Q'.ofNat (n*n*n) :=
    Q'.le_trans' _ _ _ (ofNat_le_ofNat hc)
      (Q'.le_of_eqv (ofNat_mul_eqv 16 (n*n*n)))
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hcoef hp)
    (Q'.mul_le_mul_of_nonneg_left _ _ _
      (HKConvGen.pow_base_antitone (Q'.le_of_lt hw0) (Q'.le_of_lt hw1) hE)
      (Q'.mul_nonneg _ _ (by decide) (ofNat_nonneg _)))

/-- The actual alternating term, including its literal sign power, pays
the same shell on the whole coordinate interval. -/
theorem alternatingTerm_shell_abs_le {w x : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hx0 : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) (n : Nat) (hn : 1 ≤ n) :
    Q'.abs (alternatingTerm w x n) ≤ shellTerm w n := by
  have hp : (0 : Q') ≤ w^(n*(n+1)) := Q'.pow_nonneg w (Q'.le_of_lt hw0) _
  have hs : Q'.abs ((-1 : Q')^n*w^(n*(n+1))) ≤ w^(n*(n+1)) :=
    Q'.le_trans' _ _ _
      (abs_product_le (sign_power_abs n)
        (Q'.le_of_eqv (TsumDeriv.Q'.abs_of_nonneg hp)) (by decide))
      (Q'.le_of_eqv (Q'.one_mul_eqv _))
  have ht := abs_product_le hs (halfShift_abs_le n hx0 hx1) hp
  exact Q'.le_trans' _ _ _ ht (Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))
    (gaussian_shell_le hw0 hw1 n (n*(n+1)) (2*n+1)
      (by simp only [Nat.mul_add, Nat.mul_one]; omega) (linear_coefficient_le hn)))

/-- The original one-sided odd coordinate term has the same shell bound. -/
theorem oddTerm_shell_abs_le {w x : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hx0 : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) (n : Nat) (hn : 1 ≤ n) :
    Q'.abs (oddTerm w x n) ≤ shellTerm w n := by
  have hp : (0 : Q') ≤ w^(2*(n*(n+1))) := Q'.pow_nonneg w (Q'.le_of_lt hw0) _
  have ht := abs_product_le
    (Q'.le_of_eqv (TsumDeriv.Q'.abs_of_nonneg hp))
    (chebT_abs_le_one (2*n+1) hx0 hx1) hp
  exact Q'.le_trans' _ _ _ ht (Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.mul_one_eqv _)
      (Q'.eqv_symm (Q'.one_mul_eqv _))))
    (gaussian_shell_le hw0 hw1 n (2*(n*(n+1))) 1
      (by simp only [Nat.mul_add, Nat.mul_one]; omega)
      (Nat.le_trans (by omega) (linear_coefficient_le hn))))

/-- The literal odd endpoint-square frequency term pays the same shell. -/
theorem oddEndpointTerm_shell_abs_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (n : Nat) (hn : 1 ≤ n) :
    Q'.abs (oddEndpointTerm w n) ≤ shellTerm w n := by
  have hp : (0 : Q') ≤ w^(2*(n*(n+1))) := Q'.pow_nonneg w (Q'.le_of_lt hw0) _
  have hterm : (0 : Q') ≤ oddEndpointTerm w n :=
    Q'.mul_nonneg _ _ hp (ofNat_nonneg _)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (TsumDeriv.Q'.abs_of_nonneg hterm))
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))
      (gaussian_shell_le hw0 hw1 n (2*(n*(n+1))) ((2*n+1)*(2*n+1))
        (by simp only [Nat.mul_add, Nat.mul_one]; omega) (squared_coefficient_le hn)))

private theorem prefix_succ (f : Nat → Q') (N : Nat) :
    listQSum f (List.range (N+1+1)) ≈
      listQSum f (List.range (N+1)) + f (N+1) := by
  rw [List.range_succ]
  exact Q'.eqv_trans _ _ _ (listQSum_append f _ _)
    (Q'.add_eqv_congr_left _ _ _ (Q'.eqv_of_eq (Q'.add_zero' _)))

/-- Finite telescope with the explicit original shell cutoff. S may be any
actual prefix whose increment pin and shell domination have been proved. -/
theorem shellPrefix_cauchy {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (S f : Nat → Q') (hstep : ∀ N, S (N+1) ≈ S N + f (N+1))
    (hbound : ∀ n, 1 ≤ n → Q'.abs (f n) ≤ shellTerm w n)
    (epsilon : Q') (he : (0 : Q') < epsilon) (m n : Nat)
    (hm : oneSidedCutoff w epsilon ≤ m) (hn : oneSidedCutoff w epsilon ≤ n) :
    S m ≤ S n+epsilon ∧ S n ≤ S m+epsilon := by
  have hup : ∀ N, S (N+1) ≤ S N+shellTerm w (N+1) := by
    intro N
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (hstep N))
      (Q'.add_le_add_left _ _ _
        (Q'.le_trans' _ _ _ (Q'.le_abs_self _) (hbound (N+1) (by omega))))
  have hlo : ∀ N, S N ≤ S (N+1)+shellTerm w (N+1) := by
    intro N
    have hf : -(shellTerm w (N+1)) ≤ f (N+1) :=
      Q'.le_trans' _ _ _ (Q'.neg_le_neg (hbound (N+1) (by omega)))
        (Q'.le_trans' _ _ _ (Q'.neg_le_neg (Q'.neg_le_abs _))
          (Q'.le_of_eqv (Q'.neg_neg_eqv _)))
    have hz : (0 : Q') ≤ f (N+1)+shellTerm w (N+1) :=
      Q'.le_trans' _ _ _ (Q'.sub_nonneg_of_le hf)
        (Q'.le_of_eqv (Q'.add_eqv_congr_left _ _ _ (Q'.neg_neg_eqv _)))
    exact Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg (S N) _ hz)
      (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _))
        (Q'.add_eqv_congr_right _ _ _ (Q'.eqv_symm (hstep N)))))
  have htail : ∀ L d, oneSidedCutoff w epsilon ≤ L →
      finSum (fun i => shellTerm w (L+i+1)) d ≤ epsilon := by
    intro L d hL
    have h := shellTail_le_epsilon hw0 hw1 he (L+1) d (by
      change shellTailCutoff w epsilon ≤ L at hL
      omega)
    have hi : (fun j => shellTerm w ((L+1)+j)) =
        (fun j => shellTerm w (L+j+1)) := by
      funext j
      rw [show (L+1)+j = L+j+1 by omega]
    rw [hi] at h
    exact h
  rcases Nat.le_total m n with hmn | hnm
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
    have ht := htail m d hm
    exact ⟨Q'.le_trans' _ _ _ (telescope_lo S (fun N => shellTerm w (N+1)) hlo m d)
        (Q'.add_le_add_left _ _ _ ht),
      Q'.le_trans' _ _ _ (telescope_up S (fun N => shellTerm w (N+1)) hup m d)
        (Q'.add_le_add_left _ _ _ ht)⟩
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnm
    have ht := htail n d hn
    exact ⟨Q'.le_trans' _ _ _ (telescope_up S (fun N => shellTerm w (N+1)) hup n d)
        (Q'.add_le_add_left _ _ _ ht),
      Q'.le_trans' _ _ _ (telescope_lo S (fun N => shellTerm w (N+1)) hlo n d)
        (Q'.add_le_add_left _ _ _ ht)⟩

/-- Direct constructive real from proved actual shell increments; its
approximant is literally S N, with the named cutoff as Cauchy witness. -/
def shellPrefixCReal {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (S f : Nat → Q') (hstep : ∀ N, S (N+1) ≈ S N+f (N+1))
    (hbound : ∀ n, 1 ≤ n → Q'.abs (f n) ≤ shellTerm w n) : CReal where
  approx := S
  cauchy := fun epsilon he => ⟨oneSidedCutoff w epsilon,
    shellPrefix_cauchy hw0 hw1 S f hstep hbound epsilon he⟩

theorem alternating_cauchy {w x : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hx0 : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (epsilon : Q') (he : (0 : Q') < epsilon) (m n : Nat)
    (hm : oneSidedCutoff w epsilon ≤ m) (hn : oneSidedCutoff w epsilon ≤ n) :
    alternatingPartial w x m ≤ alternatingPartial w x n+epsilon ∧
      alternatingPartial w x n ≤ alternatingPartial w x m+epsilon :=
  shellPrefix_cauchy hw0 hw1 (alternatingPartial w x) (alternatingTerm w x)
    (prefix_succ (alternatingTerm w x))
    (alternatingTerm_shell_abs_le hw0 hw1 hx0 hx1) epsilon he m n hm hn

theorem odd_cauchy {w x : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hx0 : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (epsilon : Q') (he : (0 : Q') < epsilon) (m n : Nat)
    (hm : oneSidedCutoff w epsilon ≤ m) (hn : oneSidedCutoff w epsilon ≤ n) :
    oddPartial w x m ≤ oddPartial w x n+epsilon ∧ oddPartial w x n ≤ oddPartial w x m+epsilon :=
  shellPrefix_cauchy hw0 hw1 (oddPartial w x) (oddTerm w x)
    (prefix_succ (oddTerm w x)) (oddTerm_shell_abs_le hw0 hw1 hx0 hx1) epsilon he m n hm hn

theorem oddEndpoint_cauchy {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (epsilon : Q') (he : (0 : Q') < epsilon) (m n : Nat)
    (hm : oneSidedCutoff w epsilon ≤ m) (hn : oneSidedCutoff w epsilon ≤ n) :
    oddEndpointJet w m ≤ oddEndpointJet w n+epsilon ∧ oddEndpointJet w n ≤ oddEndpointJet w m+epsilon :=
  shellPrefix_cauchy hw0 hw1 (oddEndpointJet w) (oddEndpointTerm w)
    (prefix_succ (oddEndpointTerm w)) (oddEndpointTerm_shell_abs_le hw0 hw1) epsilon he m n hm hn

def alternatingCReal {w x : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hx0 : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) : CReal :=
  shellPrefixCReal hw0 hw1 (alternatingPartial w x) (alternatingTerm w x)
    (prefix_succ (alternatingTerm w x)) (alternatingTerm_shell_abs_le hw0 hw1 hx0 hx1)

def oddCReal {w x : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hx0 : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) : CReal :=
  shellPrefixCReal hw0 hw1 (oddPartial w x) (oddTerm w x)
    (prefix_succ (oddTerm w x)) (oddTerm_shell_abs_le hw0 hw1 hx0 hx1)

def oddEndpointCReal {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) : CReal :=
  shellPrefixCReal hw0 hw1 (oddEndpointJet w) (oddEndpointTerm w)
    (prefix_succ (oddEndpointTerm w)) (oddEndpointTerm_shell_abs_le hw0 hw1)

@[simp] theorem alternatingCReal_approx {w x : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hx0 : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) (N : Nat) :
    (alternatingCReal hw0 hw1 hx0 hx1).approx N = alternatingPartial w x N := rfl

@[simp] theorem oddCReal_approx {w x : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hx0 : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) (N : Nat) :
    (oddCReal hw0 hw1 hx0 hx1).approx N = oddPartial w x N := rfl

@[simp] theorem oddEndpointCReal_approx {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (N : Nat) :
    (oddEndpointCReal hw0 hw1).approx N = oddEndpointJet w N := rfl

end YMGap.Continuum.ThetaOneSidedSeriesCompletion

#print axioms YMGap.Continuum.ThetaOneSidedSeriesCompletion.oneSidedCutoff
#print axioms YMGap.Continuum.ThetaOneSidedSeriesCompletion.alternatingTerm_shell_abs_le
#print axioms YMGap.Continuum.ThetaOneSidedSeriesCompletion.oddTerm_shell_abs_le
#print axioms YMGap.Continuum.ThetaOneSidedSeriesCompletion.oddEndpointTerm_shell_abs_le
#print axioms YMGap.Continuum.ThetaOneSidedSeriesCompletion.shellPrefix_cauchy
#print axioms YMGap.Continuum.ThetaOneSidedSeriesCompletion.shellPrefixCReal
#print axioms YMGap.Continuum.ThetaOneSidedSeriesCompletion.alternating_cauchy
#print axioms YMGap.Continuum.ThetaOneSidedSeriesCompletion.odd_cauchy
#print axioms YMGap.Continuum.ThetaOneSidedSeriesCompletion.oddEndpoint_cauchy
#print axioms YMGap.Continuum.ThetaOneSidedSeriesCompletion.alternatingCReal
#print axioms YMGap.Continuum.ThetaOneSidedSeriesCompletion.oddCReal
#print axioms YMGap.Continuum.ThetaOneSidedSeriesCompletion.oddEndpointCReal
#print axioms YMGap.Continuum.ThetaOneSidedSeriesCompletion.alternatingCReal_approx
#print axioms YMGap.Continuum.ThetaOneSidedSeriesCompletion.oddCReal_approx
#print axioms YMGap.Continuum.ThetaOneSidedSeriesCompletion.oddEndpointCReal_approx
