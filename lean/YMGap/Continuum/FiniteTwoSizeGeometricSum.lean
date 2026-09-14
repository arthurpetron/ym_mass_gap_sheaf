/-
# Two exact finite mass strata give a product geometric budget

If the actual (n,m) fiber has at most D^n*E^m members, the sum of
r^n*s^m over a finite source with n>=d is bounded by
(D*r)^d / (1-D*r) / (1-E*s). All source multiplicities are retained.
The two upper mass bounds are used only to cover the finite source and
disappear from the explicit rational budget. No infinite sum is rearranged.
-/

import YMGap.Continuum.FiniteSizeGeometricSum
import YMGap.Continuum.FiniteWeightedGramSOS

namespace YMGap.Continuum.FiniteTwoSizeGeometricSum

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS (listQSum_mul_right)
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv

theorem one_entropy_guard {r : Q'} (hr : r < 1) : entropyRate 1 r < 1 :=
  HKPos.q_lt_of_le_of_lt (Q'.le_of_eqv (Q'.one_mul_eqv r)) hr

theorem tailBudget_scale (C D d : Nat) (r : Q') (hr : entropyRate D r < 1) :
    tailBudget C D d r hr ≈ Q'.ofNat C*tailBudget 1 D d r hr := by
  unfold tailBudget
  exact poly_identity_of_normal_eq
    (.mul (.mul (.var 0) (.var 1)) (.var 2))
    (.mul (.var 0) (.mul (.mul (.const 1) (.var 1)) (.var 2))) (by decide)
    (fun i => if i=0 then Q'.ofNat C else if i=1 then (entropyRate D r)^d
      else Q'.recipPos (1 + -entropyRate D r) (HKPos.one_sub_pos hr))

theorem distinct_mass_sum (ns : List Nat) (d upper : Nat) {r : Q'}
    (hr : (0 : Q') ≤ r) (hs : r < 1) (hn : ns.Nodup)
    (hlo : ∀ n, n ∈ ns → d ≤ n) (hhi : ∀ n, n ∈ ns → n ≤ upper) :
    listQSum (fun n => r^n) ns ≤ tailBudget 1 1 d r (one_entropy_guard hs) := by
  apply size_sum_bound ns id 1 1 d upper hr (one_entropy_guard hs) hlo hhi
  intro n
  have hc := nodup_subset_length_le (ns.filter (fun x => decide (n=id x))) [n] (hn.filter _) (by
    intro x hx
    have he : n=x := of_decide_eq_true (List.mem_filter.mp hx).2
    exact he ▸ List.mem_cons_self)
  simpa only [List.length_cons,List.length_nil,Nat.one_pow,Nat.mul_one] using hc

theorem first_mass_fiber_bound {A : Type} (xs : List A) (first second : A → Nat)
    (D E n upper : Nat) {r s : Q'} (hr : (0 : Q') ≤ r) (hs : (0 : Q') ≤ s)
    (hsmall : entropyRate E s < 1)
    (hhi : ∀ x, x ∈ xs → second x ≤ upper)
    (hcount : ∀ m, ((xs.filter (fun x => decide (n=first x))).filter
      (fun x => decide (m=second x))).length ≤ D^n*E^m) :
    fiberWeight xs (fun x => r^(first x)*s^(second x)) first n ≤
      (entropyRate D r)^n*tailBudget 1 E 0 s hsmall := by
  let ys := xs.filter (fun x => decide (n=first x))
  have hsum := size_sum_bound ys second (D^n) E 0 upper hs hsmall
    (fun _ _ => Nat.zero_le _) (fun x hx => hhi x (List.mem_filter.mp hx).1) hcount
  have hfactor : fiberWeight xs (fun x => r^(first x)*s^(second x)) first n ≈
      r^n*listQSum (fun x => s^(second x)) ys := by
    refine Q'.eqv_trans _ _ _ (listQSum_congr_on _ _ ys (fun x hx => ?_)) (listQSum_mul_left _ _ _)
    have he : n=first x := of_decide_eq_true (List.mem_filter.mp hx).2
    rw [he]
    exact Q'.eqv_refl _
  have hscaled : tailBudget (D^n) E 0 s hsmall ≤
      (Q'.ofNat D)^n*tailBudget 1 E 0 s hsmall :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (tailBudget_scale (D^n) E 0 s hsmall))
      (Q'.mul_le_mul_of_nonneg_right _ _ _ (ClusterCount.ofNat_pow_le D n)
        (tailBudget_nonnegative 1 E 0 hs hsmall))
  have he : r^n*((Q'.ofNat D)^n*tailBudget 1 E 0 s hsmall) ≈
      (entropyRate D r)^n*tailBudget 1 E 0 s hsmall := by
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
    apply Q'.mul_eqv_congr_right
    exact Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _)
      (Q'.eqv_symm (TotalMajorantClose.mul_pow (Q'.ofNat D) r n))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hfactor) (Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ (Q'.le_trans' _ _ _ hsum hscaled) (Q'.pow_nonneg r hr n))
    (Q'.le_of_eqv he))

def twoMassBudget (D E d : Nat) (r s : Q')
    (hr : entropyRate D r < 1) (hs : entropyRate E s < 1) : Q' :=
  tailBudget 1 1 d (entropyRate D r) (one_entropy_guard hr)*tailBudget 1 E 0 s hs

theorem twoMassBudget_nonnegative (D E d : Nat) {r s : Q'}
    (hr : (0 : Q') ≤ r) (hs : (0 : Q') ≤ s)
    (hx : entropyRate D r < 1) (hy : entropyRate E s < 1) :
    (0 : Q') ≤ twoMassBudget D E d r s hx hy :=
  Q'.mul_nonneg _ _
    (tailBudget_nonnegative 1 1 d (Q'.mul_nonneg _ _ (ClusterCount.ofNat_nonneg D) hr) (one_entropy_guard hx))
    (tailBudget_nonnegative 1 E 0 hs hy)

theorem two_size_sum_bound {A : Type} (xs : List A) (first second : A → Nat)
    (D E d firstUpper secondUpper : Nat) {r s : Q'}
    (hr : (0 : Q') ≤ r) (hs : (0 : Q') ≤ s)
    (hx : entropyRate D r < 1) (hy : entropyRate E s < 1)
    (hlo : ∀ x, x ∈ xs → d ≤ first x)
    (hfirst : ∀ x, x ∈ xs → first x ≤ firstUpper)
    (hsecond : ∀ x, x ∈ xs → second x ≤ secondUpper)
    (hcount : ∀ n m, ((xs.filter (fun x => decide (n=first x))).filter
      (fun x => decide (m=second x))).length ≤ D^n*E^m) :
    listQSum (fun x => r^(first x)*s^(second x)) xs ≤ twoMassBudget D E d r s hx hy := by
  let targets := (List.range (firstUpper+1)).map (fun k => d+k)
  have ht : targets.Nodup := nodup_map_of_injOn _ _ (CayleyParentInj.range_nodup _)
    (fun a _ b _ he => by omega)
  have hcover : ∀ x, x ∈ xs → first x ∈ targets := by
    intro x hm
    have hl := hlo x hm
    have hu := hfirst x hm
    exact List.mem_map.mpr ⟨first x-d,List.mem_range.mpr (by omega),by omega⟩
  have htotal := fiberWeight_total xs (fun x => r^(first x)*s^(second x)) first targets ht hcover
  have hf := sum_le_on _ _ targets (fun n _ =>
    first_mass_fiber_bound xs first second D E n secondUpper hr hs hy hsecond (hcount n))
  have hsum := distinct_mass_sum targets d (d+firstUpper)
    (Q'.mul_nonneg _ _ (ClusterCount.ofNat_nonneg D) hr) hx ht
    (by intro n hn; obtain ⟨k,_,rfl⟩ := List.mem_map.mp hn; omega)
    (by intro n hn; obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hn; have := List.mem_range.mp hk; omega)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv htotal) (Q'.le_trans' _ _ _ hf
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (listQSum_mul_right _ _ targets))
      (Q'.mul_le_mul_of_nonneg_right _ _ _ hsum (tailBudget_nonnegative 1 E 0 hs hy))))

end YMGap.Continuum.FiniteTwoSizeGeometricSum

#print axioms YMGap.Continuum.FiniteTwoSizeGeometricSum.one_entropy_guard
#print axioms YMGap.Continuum.FiniteTwoSizeGeometricSum.tailBudget_scale
#print axioms YMGap.Continuum.FiniteTwoSizeGeometricSum.distinct_mass_sum
#print axioms YMGap.Continuum.FiniteTwoSizeGeometricSum.first_mass_fiber_bound
#print axioms YMGap.Continuum.FiniteTwoSizeGeometricSum.twoMassBudget
#print axioms YMGap.Continuum.FiniteTwoSizeGeometricSum.twoMassBudget_nonnegative
#print axioms YMGap.Continuum.FiniteTwoSizeGeometricSum.two_size_sum_bound
