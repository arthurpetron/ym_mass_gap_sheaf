/-
# Exact size stratification and an explicit finite geometric tail budget

For a finite family with size-n count at most C*D^n, weights r^size sum
under C*(D*r)^d/(1-D*r), provided every size is at least d and 0<=D*r<1.
The finite source is grouped by its actual sizes; no infinite rearrangement,
analytic limit or summability assumption is used. The budget is rational
data and the finite upper cutoff disappears from the resulting bound.
-/

import YMGap.Continuum.FiniteSelectionMobius
import YMGap.Continuum.ClusterCount
import YMGap.Continuum.CayleyParentInj
import YMGap.Continuum.TotalMajorantClose
import YMGap.Continuum.HeatKernelPos
import YMGap.Constructive.GeometricTail

namespace YMGap.Continuum.FiniteSizeGeometricSum

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteSelectionMobius
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.RingNormaliser (PolyExpr poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv

theorem sum_le_on {A : Type} (f g : A → Q') : ∀ xs : List A,
    (∀ x, x ∈ xs → f x ≤ g x) → listQSum f xs ≤ listQSum g xs
  | [], _ => Q'.le_refl' _
  | x :: xs, h => Q'.add_le_add (h x List.mem_cons_self)
      (sum_le_on f g xs (fun y hy => h y (List.mem_cons_of_mem x hy)))

theorem sum_const {A : Type} (c : Q') : ∀ xs : List A,
    listQSum (fun _ => c) xs ≈ Q'.ofNat xs.length * c
  | [] => Q'.eqv_symm (Q'.zero_mul_eqv c)
  | _ :: xs => by
      refine Q'.eqv_trans _ (c + Q'.ofNat xs.length*c) _
        (Q'.add_eqv_congr_left c _ _ (sum_const c xs)) ?_
      apply Q'.eqv_symm
      refine Q'.eqv_trans _ ((Q'.ofNat xs.length+1)*c) _
        (Q'.mul_eqv_congr_right _ _ c (Q'.ofNat_add_eqv xs.length 1)) ?_
      refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv _ _ _) ?_
      exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ (Q'.one_mul_eqv c)) (Q'.add_comm_eqv _ _)

theorem sum_range (f : Nat → Q') : ∀ n : Nat,
    listQSum f (List.range n) ≈ finSum f n
  | 0 => Q'.eqv_refl _
  | n+1 => by
      rw [List.range_succ]
      exact Q'.eqv_trans _ _ _ (sum_append f _ _)
        (Q'.add_eqv_congr' (sum_range f n) (Q'.eqv_of_eq (Q'.add_zero' (f n))))

/-- The combined counting and weight rate, with both parameters explicit. -/
def entropyRate (D : Nat) (rate : Q') : Q' := Q'.ofNat D * rate

def tailBudget (C D d : Nat) (rate : Q') (hs : entropyRate D rate < 1) : Q' :=
  (Q'.ofNat C * (entropyRate D rate)^d) * Q'.recipPos (1 + -entropyRate D rate) (HKPos.one_sub_pos hs)

theorem tailBudget_nonnegative (C D d : Nat) {rate : Q'} (hr : (0 : Q') ≤ rate)
    (hs : entropyRate D rate < 1) : (0 : Q') ≤ tailBudget C D d rate hs :=
  Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (ClusterCount.ofNat_nonneg C)
    (Q'.pow_nonneg _ (Q'.mul_nonneg _ _ (ClusterCount.ofNat_nonneg D) hr) d))
    (Q'.le_of_lt (Q'.recipPos_pos _ _))

theorem size_stratum_bound {A : Type} (xs : List A) (size : A → Nat) (C D n : Nat)
    {rate : Q'} (hr : (0 : Q') ≤ rate)
    (hc : (xs.filter (fun x => decide (n = size x))).length ≤ C*D^n) :
    fiberWeight xs (fun x => rate^(size x)) size n ≤ Q'.ofNat C * (entropyRate D rate)^n := by
  have hconst : fiberWeight xs (fun x => rate^(size x)) size n ≈
      Q'.ofNat (xs.filter (fun x => decide (n = size x))).length * rate^n :=
    Q'.eqv_trans _ _ _ (listQSum_congr_on _ _ _ (fun x hx => by
      have he : n = size x := of_decide_eq_true (List.mem_filter.mp hx).2
      exact Q'.eqv_of_eq (congrArg (fun k => rate^k) he.symm))) (sum_const _ _)
  have hn : Q'.ofNat (xs.filter (fun x => decide (n = size x))).length ≤
      Q'.ofNat C * (Q'.ofNat D)^n :=
    Q'.le_trans' _ _ _ (ClusterCount.ofNat_le_ofNat hc)
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (ClusterCount.ofNat_mul_eqv C (D^n)))
        (Q'.mul_le_mul_of_nonneg_left _ _ _ (ClusterCount.ofNat_pow_le D n) (ClusterCount.ofNat_nonneg C)))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hconst)
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ hn (Q'.pow_nonneg rate hr n))
      (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _)
        (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (TotalMajorantClose.mul_pow (Q'.ofNat D) rate n))))))

private theorem reciprocal_step (s : Q') (hs : s < 1) :
    (1 : Q') + s * Q'.recipPos (1 + -s) (HKPos.one_sub_pos hs) ≈
      Q'.recipPos (1 + -s) (HKPos.one_sub_pos hs) := by
  let r := Q'.recipPos (1 + -s) (HKPos.one_sub_pos hs)
  have hi : ((1 : Q') + -s)*r ≈ 1 := Q'.mul_recipPos_eqv _ _
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_eqv_congr' hi (Q'.eqv_refl (s*r)))) ?_
  exact poly_identity_of_normal_eq
    (.add (.mul (.add (.const 1) (.neg (.var 0))) (.var 1)) (.mul (.var 0) (.var 1)))
    (.var 1) (by decide) (fun i => if i = 0 then s else r)

private theorem scaled_series_bound (eta s : Q') (heta : (0 : Q') ≤ eta)
    (hs0 : (0 : Q') ≤ s) (hs : s < 1) (N : Nat) :
    finSum (fun k => eta*s^k) N ≤ eta * Q'.recipPos (1 + -s) (HKPos.one_sub_pos hs) := by
  let r := Q'.recipPos (1 + -s) (HKPos.one_sub_pos hs)
  apply geometric_tail_closure eta s (eta*r) hs0
    (Q'.mul_nonneg _ _ heta (Q'.le_of_lt (Q'.recipPos_pos _ _))) _ N
  apply Q'.le_of_eqv
  refine Q'.eqv_trans _ (eta*((1 : Q')+s*r)) _ ?_ (Q'.mul_eqv_congr_left eta _ _ (reciprocal_step s hs))
  exact poly_identity_of_normal_eq
    (.add (.var 0) (.mul (.var 1) (.mul (.var 0) (.var 2))))
    (.mul (.var 0) (.add (.const 1) (.mul (.var 1) (.var 2)))) (by decide)
    (fun i => if i = 0 then eta else if i = 1 then s else r)

/-- Actual finite size fibers exhaust the source, and their geometric budget
is independent of the supplied finite upper size bound. -/
theorem size_sum_bound {A : Type} (xs : List A) (size : A → Nat) (C D d upper : Nat)
    {rate : Q'} (hr : (0 : Q') ≤ rate) (hs : entropyRate D rate < 1)
    (hlo : ∀ x, x ∈ xs → d ≤ size x) (hhi : ∀ x, x ∈ xs → size x ≤ upper)
    (hcount : ∀ n, (xs.filter (fun x => decide (n = size x))).length ≤ C*D^n) :
    listQSum (fun x => rate^(size x)) xs ≤ tailBudget C D d rate hs := by
  let targets := (List.range (upper+1)).map (fun k => d+k)
  have ht : targets.Nodup := CayleyPruferInjection.nodup_map_of_injOn _ _
    (CayleyParentInj.range_nodup _) (fun a _ b _ he => by omega)
  have hcover : ∀ x, x ∈ xs → size x ∈ targets := by
    intro x hx
    apply List.mem_map.mpr
    refine ⟨size x-d, List.mem_range.mpr ?_, ?_⟩
    · have h := hhi x hx; omega
    · have h := hlo x hx; omega
  have htotal := fiberWeight_total xs (fun x => rate^(size x)) size targets ht hcover
  have hbound := sum_le_on _ _ targets (fun n _ => size_stratum_bound xs size C D n hr (hcount n))
  have hrecode : listQSum (fun n => Q'.ofNat C*(entropyRate D rate)^n) targets ≈
      finSum (fun k => (Q'.ofNat C*(entropyRate D rate)^d)*(entropyRate D rate)^k) (upper+1) := by
    rw [show targets = (List.range (upper+1)).map (fun k => d+k) from rfl, sum_map]
    refine Q'.eqv_trans _ _ _ (listQSum_congr_on _ _ _ (fun k _ => ?_)) (sum_range _ _)
    exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _ (YMGap.Continuum.Q'.pow_add_eqv _ d k))
      (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv htotal)
    (Q'.le_trans' _ _ _ hbound (Q'.le_trans' _ _ _ (Q'.le_of_eqv hrecode)
      (scaled_series_bound _ _ (Q'.mul_nonneg _ _ (ClusterCount.ofNat_nonneg C)
        (Q'.pow_nonneg _ (Q'.mul_nonneg _ _ (ClusterCount.ofNat_nonneg D) hr) d))
        (Q'.mul_nonneg _ _ (ClusterCount.ofNat_nonneg D) hr) hs (upper+1))))

end YMGap.Continuum.FiniteSizeGeometricSum

#print axioms YMGap.Continuum.FiniteSizeGeometricSum.sum_le_on
#print axioms YMGap.Continuum.FiniteSizeGeometricSum.sum_const
#print axioms YMGap.Continuum.FiniteSizeGeometricSum.sum_range
#print axioms YMGap.Continuum.FiniteSizeGeometricSum.entropyRate
#print axioms YMGap.Continuum.FiniteSizeGeometricSum.tailBudget
#print axioms YMGap.Continuum.FiniteSizeGeometricSum.tailBudget_nonnegative
#print axioms YMGap.Continuum.FiniteSizeGeometricSum.size_stratum_bound
#print axioms YMGap.Continuum.FiniteSizeGeometricSum.size_sum_bound
