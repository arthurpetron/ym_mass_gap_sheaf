/-
# Actual odd signed-interval boundary corrections

The signed odd prefix on -N,...,N has one unmatched nonnegative endpoint.
These finite identities retain that endpoint for both the coordinate value
and the endpoint frequency-square weight. They make no limit or derivative
claim.
-/

import YMGap.Continuum.ThetaEvenSeriesCompletion
import YMGap.Continuum.ThetaJointValuePin
import YMGap.Continuum.ThetaAlternatingMixedRectangle
import YMGap.Continuum.ThetaAlternatingEndpointRectangle
import YMGap.Continuum.FiniteDeterministicKernelPushforward
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.ThetaOddBoundaryPin

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ThetaParityConvolution (signedIndices)
open YMGap.Continuum.ThetaParityWeights (oddThetaTerm)
open YMGap.Continuum.ThetaAlternatingMixedRectangle (oddTerm oddPartial)
open YMGap.Continuum.ThetaAlternatingEndpointRectangle (oddEndpointTerm oddEndpointJet)
open YMGap.Continuum.ThetaJointValuePin (signed_succ_perm sum_perm)
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm (listQSum)
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm (listQSum_append)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv

private theorem add_congr {a b c d : Q'} (h : a ≈ b) (g : c ≈ d) :
    a+c ≈ b+d := Q'.add_eqv_congr' h g

private theorem sum_singleton {A : Type} (f : A → Q') (a : A) :
    listQSum f [a] ≈ f a := QPoly.q_add_zero_eqv _

private theorem signed_sum_step (f : Int → Q') (N : Nat) :
    listQSum f (signedIndices (N+1)) ≈
      f (-((N+1 : Nat) : Int)) +
        (listQSum f (signedIndices N) + f ((N+1 : Nat) : Int)) := by
  have hp := sum_perm f (signed_succ_perm N)
  have happ : listQSum f (signedIndices N ++ [((N+1 : Nat) : Int)]) ≈
      listQSum f (signedIndices N) + f ((N+1 : Nat) : Int) :=
    Q'.eqv_trans _ _ _ (listQSum_append f _ _)
      (add_congr (Q'.eqv_refl _) (sum_singleton f _))
  have htail : listQSum f (-((N+1 : Nat) : Int) ::
      (signedIndices N ++ [((N+1 : Nat) : Int)])) ≈
      f (-((N+1 : Nat) : Int)) +
        (listQSum f (signedIndices N) + f ((N+1 : Nat) : Int)) := by
    change f (-((N+1 : Nat) : Int)) +
      listQSum f (signedIndices N ++ [((N+1 : Nat) : Int)]) ≈ _
    exact add_congr (Q'.eqv_refl _) happ
  exact Q'.eqv_trans _ _ _ hp htail

private theorem oddTerm_negative_pin (w x : Q') (N : Nat) :
    oddThetaTerm w x (-((N+1 : Nat) : Int)) = oddTerm w x N := by
  unfold oddThetaTerm oddTerm
  have hpow :
      ((-((N+1 : Nat) : Int)) * (-((N+1 : Nat) : Int) + 1)).toNat = N*(N+1) := by
    let a : Int := ((N+1 : Nat) : Int)
    have hmul :
        -a * (-a + 1) = (N : Int)*(N+1 : Int) := by
      calc
        -a * (-a + 1) = -a * (-(a-1)) := by congr 2 <;> omega
        _ = a*(a-1) := Int.neg_mul_neg _ _
        _ = (N : Int)*(N+1 : Int) := by
          rw [show a-1 = (N : Int) by dsimp [a]; omega]
          exact Int.mul_comm _ _
    have hcast : (N : Int)*(N+1 : Int) = ((N*(N+1) : Nat) : Int) := by
      simp only [Int.natCast_mul, Int.natCast_add, Int.natCast_one]
    have h := congrArg Int.toNat (hmul.trans hcast)
    simpa only [Int.toNat_natCast] using h
  have hindex : 2 * (-((N+1 : Nat) : Int)) + 1 = -((2*N+1 : Nat) : Int) := by omega
  rw [hpow, hindex, Int.natAbs_neg]
  simp only [Int.natAbs_natCast]

private theorem oddTerm_positive_pin (w x : Q') (N : Nat) :
    oddThetaTerm w x ((N+1 : Nat) : Int) = oddTerm w x (N+1) := by
  unfold oddThetaTerm oddTerm
  have hmul : ((N+1 : Nat) : Int) * (((N+1 : Nat) : Int)+1) =
      (((N+1)*(N+2) : Nat) : Int) := by
    have hadd : ((N+1 : Nat) : Int)+1 = ((N+2 : Nat) : Int) := by omega
    rw [hadd]
    simp only [Int.natCast_mul]
  have hpow := congrArg Int.toNat hmul
  have hfreq : (2*((N+1 : Nat) : Int)+1) = ((2*(N+1)+1 : Nat) : Int) := by
    simp only [Int.natCast_add, Int.natCast_mul, Int.natCast_one]
    rfl
  rw [hpow, hfreq]
  simp only [Int.toNat_natCast, Int.natAbs_natCast]

private theorem oddEndpoint_negative_pin (w : Q') (N : Nat) :
    w^(2*((-((N+1 : Nat) : Int) * (-((N+1 : Nat) : Int) + 1)).toNat)) *
        Q'.ofNat ((2 * (-((N+1 : Nat) : Int)) + 1).natAbs *
          (2 * (-((N+1 : Nat) : Int)) + 1).natAbs) = oddEndpointTerm w N := by
  unfold oddEndpointTerm
  have hpow :
      ((-((N+1 : Nat) : Int)) * (-((N+1 : Nat) : Int) + 1)).toNat = N*(N+1) := by
    let a : Int := ((N+1 : Nat) : Int)
    have hmul :
        -a * (-a + 1) = (N : Int)*(N+1 : Int) := by
      calc
        -a * (-a + 1) = -a * (-(a-1)) := by congr 2 <;> omega
        _ = a*(a-1) := Int.neg_mul_neg _ _
        _ = (N : Int)*(N+1 : Int) := by
          rw [show a-1 = (N : Int) by dsimp [a]; omega]
          exact Int.mul_comm _ _
    have hcast : (N : Int)*(N+1 : Int) = ((N*(N+1) : Nat) : Int) := by
      simp only [Int.natCast_mul, Int.natCast_add, Int.natCast_one]
    have h := congrArg Int.toNat (hmul.trans hcast)
    simpa only [Int.toNat_natCast] using h
  have hindex : 2 * (-((N+1 : Nat) : Int)) + 1 = -((2*N+1 : Nat) : Int) := by omega
  rw [hpow, hindex, Int.natAbs_neg]
  simp only [Int.natAbs_natCast]

private theorem oddEndpoint_positive_pin (w : Q') (N : Nat) :
    w^(2*(((N+1 : Nat) : Int)*(((N+1 : Nat) : Int)+1)).toNat) *
        Q'.ofNat ((2*((N+1 : Nat) : Int)+1).natAbs *
          (2*((N+1 : Nat) : Int)+1).natAbs) = oddEndpointTerm w (N+1) := by
  unfold oddEndpointTerm
  have hmul : ((N+1 : Nat) : Int) * (((N+1 : Nat) : Int)+1) =
      (((N+1)*(N+2) : Nat) : Int) := by
    have hadd : ((N+1 : Nat) : Int)+1 = ((N+2 : Nat) : Int) := by omega
    rw [hadd]
    simp only [Int.natCast_mul]
  have hpow := congrArg Int.toNat hmul
  have hfreq : (2*((N+1 : Nat) : Int)+1) = ((2*(N+1)+1 : Nat) : Int) := by
    simp only [Int.natCast_add, Int.natCast_mul, Int.natCast_one]
    rfl
  rw [hpow, hfreq]
  simp only [Int.toNat_natCast, Int.natAbs_natCast]

private theorem oddPartial_succ (w x : Q') (N : Nat) :
    oddPartial w x (N+1) ≈ oddPartial w x N + oddTerm w x (N+1) := by
  unfold oddPartial
  rw [List.range_succ]
  exact Q'.eqv_trans _ _ _ (listQSum_append _ _ _)
    (Q'.add_eqv_congr_left _ _ _ (Q'.eqv_of_eq (Q'.add_zero' _)))

private theorem oddEndpointJet_succ (w : Q') (N : Nat) :
    oddEndpointJet w (N+1) ≈ oddEndpointJet w N + oddEndpointTerm w (N+1) := by
  unfold oddEndpointJet
  rw [List.range_succ]
  exact Q'.eqv_trans _ _ _ (listQSum_append _ _ _)
    (Q'.add_eqv_congr_left _ _ _ (Q'.eqv_of_eq (Q'.add_zero' _)))

private theorem double_boundary_algebra (a b c : Q') :
    a + ((2*b + -a) + c) ≈ 2*(b+c) + -c :=
  poly_identity_of_normal_eq
    (.add (.var 0) (.add (.add (.mul (.const 2) (.var 1)) (.neg (.var 0))) (.var 2)))
    (.add (.mul (.const 2) (.add (.var 1) (.var 2))) (.neg (.var 2)))
    (by decide) (fun | 0 => a | 1 => b | _ => c)

/-- The actual signed odd coordinate prefix has its literal unmatched top
term removed from twice the one-sided prefix. -/
def oddSignedPrefix (w x : Q') (N : Nat) : Q' :=
  listQSum (oddThetaTerm w x) (signedIndices N)

theorem odd_signed_boundary_pin (w x : Q') : ∀ N,
    oddSignedPrefix w x N ≈
      2*oddPartial w x N + -(oddTerm w x N)
  | 0 => by
      have hidx : signedIndices 0 = [0] := by simp [signedIndices]
      unfold oddSignedPrefix oddPartial
      rw [hidx]
      simp only [List.range_succ, List.range_zero]
      change oddThetaTerm w x 0 + 0 ≈
        2*(oddTerm w x 0 + 0) + -(oddTerm w x 0)
      have ht : oddThetaTerm w x 0 = oddTerm w x 0 := by
        simp [oddThetaTerm, oddTerm]
      rw [ht]
      exact poly_identity_of_normal_eq
        (.add (.var 0) (.const 0))
        (.add (.mul (.const 2) (.add (.var 0) (.const 0))) (.neg (.var 0)))
        (by decide) (fun _ => oddTerm w x 0)
  | N+1 => by
      have hrec := signed_sum_step (oddThetaTerm w x) N
      have hlow : oddThetaTerm w x (-((N+1 : Nat) : Int)) = oddTerm w x N :=
        oddTerm_negative_pin w x N
      have hhigh : oddThetaTerm w x ((N+1 : Nat) : Int) = oddTerm w x (N+1) :=
        oddTerm_positive_pin w x N
      have hprev := odd_signed_boundary_pin w x N
      have hpartial := oddPartial_succ w x N
      unfold oddSignedPrefix at hrec ⊢
      have hrewrite := Q'.eqv_trans _ _ _ hrec
        (add_congr (Q'.eqv_of_eq hlow)
          (add_congr hprev (Q'.eqv_of_eq hhigh)))
      exact Q'.eqv_trans _ _ _ hrewrite
        (Q'.eqv_trans _ _ _
          (double_boundary_algebra (oddTerm w x N)
            (oddPartial w x N) (oddTerm w x (N+1)))
          (add_congr (Q'.mul_eqv_congr_left 2 _ _ (Q'.eqv_symm hpartial))
            (Q'.eqv_refl _)))

/-- The actual signed endpoint-frequency prefix has the same unbalanced
boundary, with the squared odd frequency retained. -/
def oddSignedEndpointPrefix (w : Q') (N : Nat) : Q' :=
  listQSum (fun k : Int =>
    w^(2*(k*(k+1)).toNat) *
      Q'.ofNat ((2*k+1).natAbs*(2*k+1).natAbs)) (signedIndices N)

theorem odd_signed_endpoint_boundary_pin (w : Q') : ∀ N,
    oddSignedEndpointPrefix w N ≈
      2*oddEndpointJet w N + -(oddEndpointTerm w N)
  | 0 => by
      have hidx : signedIndices 0 = [0] := by simp [signedIndices]
      unfold oddSignedEndpointPrefix oddEndpointJet
      rw [hidx]
      simp only [List.range_succ, List.range_zero]
      change (w^(2*((0:Int)*(0+1)).toNat) *
        Q'.ofNat ((2*(0:Int)+1).natAbs*(2*(0:Int)+1).natAbs) + 0) ≈
          2*(oddEndpointTerm w 0 + 0) + -(oddEndpointTerm w 0)
      have ht : w^(2*((0:Int)*(0+1)).toNat) *
          Q'.ofNat ((2*(0:Int)+1).natAbs*(2*(0:Int)+1).natAbs) =
            oddEndpointTerm w 0 := by simp [oddEndpointTerm]
      rw [ht]
      exact poly_identity_of_normal_eq
        (.add (.var 0) (.const 0))
        (.add (.mul (.const 2) (.add (.var 0) (.const 0))) (.neg (.var 0)))
        (by decide) (fun _ => oddEndpointTerm w 0)
  | N+1 => by
      let f : Int → Q' := fun k =>
        w^(2*(k*(k+1)).toNat) *
          Q'.ofNat ((2*k+1).natAbs*(2*k+1).natAbs)
      have hrec := signed_sum_step f N
      have hlow : f (-((N+1 : Nat) : Int)) = oddEndpointTerm w N := by
        dsimp [f]
        exact oddEndpoint_negative_pin w N
      have hhigh : f ((N+1 : Nat) : Int) = oddEndpointTerm w (N+1) := by
        dsimp [f]
        exact oddEndpoint_positive_pin w N
      have hprev := odd_signed_endpoint_boundary_pin w N
      have hpartial := oddEndpointJet_succ w N
      unfold oddSignedEndpointPrefix at hrec ⊢
      have hrewrite := Q'.eqv_trans _ _ _ hrec
        (add_congr (Q'.eqv_of_eq hlow)
          (add_congr hprev (Q'.eqv_of_eq hhigh)))
      exact Q'.eqv_trans _ _ _ hrewrite
        (Q'.eqv_trans _ _ _
          (double_boundary_algebra (oddEndpointTerm w N)
            (oddEndpointJet w N) (oddEndpointTerm w (N+1)))
          (add_congr (Q'.mul_eqv_congr_left 2 _ _ (Q'.eqv_symm hpartial))
            (Q'.eqv_refl _)))

end YMGap.Continuum.ThetaOddBoundaryPin

#print axioms YMGap.Continuum.ThetaOddBoundaryPin.oddSignedPrefix
#print axioms YMGap.Continuum.ThetaOddBoundaryPin.odd_signed_boundary_pin
#print axioms YMGap.Continuum.ThetaOddBoundaryPin.oddSignedEndpointPrefix
#print axioms YMGap.Continuum.ThetaOddBoundaryPin.odd_signed_endpoint_boundary_pin
