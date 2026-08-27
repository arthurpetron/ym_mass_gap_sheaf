/-
# Two-replica Cartan split--swap--recombine transport

A geometric face switch changes external symmetric-power labels.  At one
link, write the first source degree as `m+n` and the second as `p+q`, with
the first summand in each decomposition selected.  The local operation is

  split both sources -> swap the selected packets -> recombine crossed pairs.

This module realizes that operation on monomial coefficients.  Its finite
carrier records the two split indices.  The product of the two normalized
Cartan rows is a nonnegative row of exact mass one, and the output map sends
the packet indices to degrees `p+n` and `m+q`.  An observable expectation is
therefore a literal finite pushforward through the crossed recombination.

No Schur reassociation, lattice Gibbs weight, component geometry, OS form
bound, or continuum claim is included here.

Constructive contract: Mathlib-free, exact `Q'` arithmetic, structural finite
lists, no choice, no `Classical`, no `sorry`, and no new axiom.
-/

import YMGap.Continuum.SU2CartanBranchingEquivariance
import YMGap.Continuum.FiniteWeightedCartesianInjection

namespace YMGap.Continuum.SU2CartanTwoReplicaCrossTransport

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.BinaryForms
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2TransvectantFactorialRecurrence
open YMGap.Continuum.SU2CartanBranchingKernel
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.FiniteWeightedCartesianInjection

local infix:50 " ≈ " => Q'.eqv

private theorem mul_eqv_congr {a b c d : Q'}
    (hac : a ≈ c) (hbd : b ≈ d) : a * b ≈ c * d :=
  Q'.eqv_trans _ (c * b) _
    (Q'.mul_eqv_congr_right _ _ b hac)
    (Q'.mul_eqv_congr_left c _ _ hbd)

private theorem scale_zero (q x : Q') (hx : x ≈ 0) : q * x ≈ 0 :=
  Q'.eqv_trans _ (q * 0) _ (Q'.mul_eqv_congr_left q _ _ hx)
    (Q'.mul_zero_eqv q)

private theorem zero_scale (q x : Q') (hx : x ≈ 0) : x * q ≈ 0 :=
  Q'.eqv_trans _ (0 * q) _ (Q'.mul_eqv_congr_right _ _ q hx)
    (Q'.zero_mul_eqv q)

private theorem tvBinomQ_zero_of_lt (n i : Nat) (hi : n < i) :
    tvBinomQ n i ≈ 0 := by
  refine Q'.eqv_trans _ (Q'.ofNat (PNPaths.choose n i)) _
    (tvBinomQ_eqv_choose_all n i) ?_
  rw [choose_zero_of_lt n i hi]
  exact Q'.ofNat_zero_eqv

private theorem cartanBranchKernelAt_zero_of_unphysical
    (m n s : Nat) (hs : s ≤ m + n) (i : Nat)
    (hunphysical : m < i ∨ n < s - i) :
    cartanBranchKernelAt m n s hs i ≈ 0 := by
  unfold cartanBranchKernelAt Q'.divPos cartanBranchRawAt
  rcases hunphysical with hi | hj
  · have hraw : tvBinomQ m i * tvBinomQ n (s - i) ≈ 0 :=
      zero_scale _ _ (tvBinomQ_zero_of_lt m i hi)
    exact zero_scale _ _ hraw
  · have hraw : tvBinomQ m i * tvBinomQ n (s - i) ≈ 0 :=
      scale_zero _ _ (tvBinomQ_zero_of_lt n (s - i) hj)
    exact zero_scale _ _ hraw

private theorem range_nodup (n : Nat) : (List.range n).Nodup := by
  induction n with
  | zero => exact List.nodup_nil
  | succ k ih =>
      rw [List.range_succ]
      refine List.nodup_append.mpr
        ⟨ih, List.nodup_cons.mpr
          ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
      intro x hx y hy hxy
      have hyk : y = k := List.mem_singleton.mp hy
      rw [hxy, hyk] at hx
      exact absurd (List.mem_range.mp hx) (Nat.lt_irrefl k)

private theorem listQSum_range_eq_finSum (value : Nat → Q') : ∀ count,
    listQSum value (List.range count) ≈ finSum value count
  | 0 => Q'.eqv_refl 0
  | count + 1 => by
      rw [List.range_succ, finSum_succ]
      exact Q'.eqv_trans _ _ _
        (listQSum_append value (List.range count) [count])
        (Q'.add_eqv_congr'
          (listQSum_range_eq_finSum value count)
          (Q'.eqv_of_eq (Q'.add_zero' (value count))))

/-! ## 1. The finite two-split carrier and its exact row law -/

/-- The two packet indices used to split the source monomials `s` and `t`. -/
def cartanCrossTargets (s t : Nat) : List (Nat × Nat) :=
  cartesian (List.range (s + 1)) (List.range (t + 1))

theorem cartanCrossTargets_nodup (s t : Nat) :
    (cartanCrossTargets s t).Nodup := by
  exact cartesian_nodup _ _ (range_nodup _) (range_nodup _)

/-- Product branching weight for the two source symmetric powers. -/
def cartanCrossKernelAt
    (m n p q s t : Nat) (hs : s ≤ m + n) (ht : t ≤ p + q)
    (packet : Nat × Nat) : Q' :=
  cartanBranchKernelAt m n s hs packet.1 *
    cartanBranchKernelAt p q t ht packet.2

theorem cartanCrossKernelAt_nonnegative
    (m n p q s t : Nat) (hs : s ≤ m + n) (ht : t ≤ p + q)
    (packet : Nat × Nat) :
    (0 : Q') ≤ cartanCrossKernelAt m n p q s t hs ht packet := by
  exact Q'.mul_nonneg _ _
    (cartanBranchKernelAt_nonnegative m n s hs packet.1)
    (cartanBranchKernelAt_nonnegative p q t ht packet.2)

/-- **The two-replica split row has exact mass one.** -/
theorem cartanCrossKernel_row_normalized
    (m n p q s t : Nat) (hs : s ≤ m + n) (ht : t ≤ p + q) :
    listQSum (cartanCrossKernelAt m n p q s t hs ht)
        (cartanCrossTargets s t) ≈ 1 := by
  refine Q'.eqv_trans _
    (listQSum (cartanBranchKernelAt m n s hs) (List.range (s + 1)) *
      listQSum (cartanBranchKernelAt p q t ht) (List.range (t + 1))) _ ?_ ?_
  · exact listQSum_cartesian_product
      (cartanBranchKernelAt m n s hs)
      (cartanBranchKernelAt p q t ht)
      (List.range (s + 1)) (List.range (t + 1))
  · refine Q'.eqv_trans _
      (cartanBranchRowMass m n s hs * cartanBranchRowMass p q t ht) _ ?_ ?_
    · exact mul_eqv_congr
        (listQSum_range_eq_finSum (cartanBranchKernelAt m n s hs) (s + 1))
        (listQSum_range_eq_finSum (cartanBranchKernelAt p q t ht) (t + 1))
    · exact Q'.eqv_trans _ ((1 : Q') * 1) _
        (mul_eqv_congr
          (cartanBranchKernel_row_normalized m n s hs)
          (cartanBranchKernel_row_normalized p q t ht))
        (Q'.one_mul_eqv 1)

/-! ## 2. Swap the selected packets and recombine their monomial indices -/

/-- Output monomial indices after selected-packet exchange.  If `i` and `k`
are the selected indices, the first output receives selected packet `k` and
the first source's unselected packet `s-i`; the second receives `i` and
`t-k`. -/
def cartanCrossOutput (s t : Nat) (packet : Nat × Nat) : Nat × Nat :=
  (packet.2 + (s - packet.1), packet.1 + (t - packet.2))

theorem cartanCrossOutput_total (s t : Nat) (packet : Nat × Nat)
    (hpacket : packet ∈ cartanCrossTargets s t) :
    (cartanCrossOutput s t packet).1 +
        (cartanCrossOutput s t packet).2 = s + t := by
  have hmem := (mem_cartesian_iff (List.range (s + 1))
    (List.range (t + 1)) packet).mp hpacket
  have hi : packet.1 ≤ s := by
    have := List.mem_range.mp hmem.1
    omega
  have hk : packet.2 ≤ t := by
    have := List.mem_range.mp hmem.2
    omega
  unfold cartanCrossOutput
  omega

/-- Physical packet bounds before the crossing. -/
def CartanPacketPhysical
    (m n p q s t : Nat) (packet : Nat × Nat) : Prop :=
  packet.1 ≤ m ∧ s - packet.1 ≤ n ∧
    packet.2 ≤ p ∧ t - packet.2 ≤ q

/-- Every packet outside one of the four symmetric-power rectangles carries
exactly zero branching weight. -/
theorem cartanCrossKernelAt_zero_of_unphysical
    (m n p q s t : Nat) (hs : s ≤ m + n) (ht : t ≤ p + q)
    (packet : Nat × Nat)
    (hunphysical : m < packet.1 ∨ n < s - packet.1 ∨
      p < packet.2 ∨ q < t - packet.2) :
    cartanCrossKernelAt m n p q s t hs ht packet ≈ 0 := by
  rcases hunphysical with hmi | hrest
  · exact zero_scale _ _
      (cartanBranchKernelAt_zero_of_unphysical m n s hs packet.1
        (Or.inl hmi))
  · rcases hrest with hnj | hrest
    · exact zero_scale _ _
        (cartanBranchKernelAt_zero_of_unphysical m n s hs packet.1
          (Or.inr hnj))
    · rcases hrest with hpk | hqt
      · exact scale_zero _ _
          (cartanBranchKernelAt_zero_of_unphysical p q t ht packet.2
            (Or.inl hpk))
      · exact scale_zero _ _
          (cartanBranchKernelAt_zero_of_unphysical p q t ht packet.2
            (Or.inr hqt))

/-- A physically supported packet lands in the crossed external degrees
`p+n` and `m+q`. -/
theorem cartanCrossOutput_physical
    (m n p q s t : Nat) (packet : Nat × Nat)
    (hphysical : CartanPacketPhysical m n p q s t packet) :
    (cartanCrossOutput s t packet).1 ≤ p + n ∧
      (cartanCrossOutput s t packet).2 ≤ m + q := by
  rcases packet with ⟨i, k⟩
  rcases hphysical with ⟨hi, hsi, hk, htk⟩
  simp only [cartanCrossOutput]
  constructor <;> omega

/-- Consequently, every packet carrying a nonzero row coefficient lands in
the two crossed physical output degrees. -/
theorem cartanCrossOutput_physical_of_kernel_nonzero
    (m n p q s t : Nat) (hs : s ≤ m + n) (ht : t ≤ p + q)
    (packet : Nat × Nat)
    (hne : ¬ cartanCrossKernelAt m n p q s t hs ht packet ≈ 0) :
    (cartanCrossOutput s t packet).1 ≤ p + n ∧
      (cartanCrossOutput s t packet).2 ≤ m + q := by
  have hi : packet.1 ≤ m := by
    by_cases h : packet.1 ≤ m
    · exact h
    · exact False.elim (hne (cartanCrossKernelAt_zero_of_unphysical
        m n p q s t hs ht packet (Or.inl (by omega))))
  have hsi : s - packet.1 ≤ n := by
    by_cases h : s - packet.1 ≤ n
    · exact h
    · exact False.elim (hne (cartanCrossKernelAt_zero_of_unphysical
        m n p q s t hs ht packet (Or.inr (Or.inl (by omega)))))
  have hk : packet.2 ≤ p := by
    by_cases h : packet.2 ≤ p
    · exact h
    · exact False.elim (hne (cartanCrossKernelAt_zero_of_unphysical
        m n p q s t hs ht packet (Or.inr (Or.inr (Or.inl (by omega))))))
  have htk : t - packet.2 ≤ q := by
    by_cases h : t - packet.2 ≤ q
    · exact h
    · exact False.elim (hne (cartanCrossKernelAt_zero_of_unphysical
        m n p q s t hs ht packet (Or.inr (Or.inr (Or.inr (by omega))))))
  exact cartanCrossOutput_physical m n p q s t packet ⟨hi, hsi, hk, htk⟩

/-! ## 3. Exact split amplitude and observable pushforward -/

private theorem cartanSplit_at_total (m n : Nat) (f : BForm)
    (i j s : Nat) (hij : i + j = s) (hs : s ≤ m + n) :
    cartanSplit m n f i j ≈
      cartanBranchKernelAt m n s hs i * f s := by
  subst s
  unfold cartanSplit
  rw [dif_pos hs]
  exact Q'.eqv_of_eq (by congr)

private theorem mul_four_interchange (a b c d : Q') :
    (a * b) * (c * d) ≈ (a * c) * (b * d) := by
  refine Q'.eqv_trans _ (a * (b * (c * d))) _
    (Q'.mul_assoc_eqv a b (c * d)) ?_
  refine Q'.eqv_trans _ (a * (c * (b * d))) _ ?_
    (Q'.eqv_symm (Q'.mul_assoc_eqv a c (b * d)))
  apply Q'.mul_eqv_congr_left a
  exact Q'.eqv_trans _ ((b * c) * d) _
    (Q'.eqv_symm (Q'.mul_assoc_eqv b c d))
    (Q'.eqv_trans _ ((c * b) * d) _
      (Q'.mul_eqv_congr_right _ _ d (Q'.mul_comm_eqv b c))
      (Q'.mul_assoc_eqv c b d))

/-- Product of the two literal split coefficients for one packet. -/
def cartanCrossPacketAmplitude
    (m n p q s t : Nat) (f g : BForm) (packet : Nat × Nat) : Q' :=
  cartanSplit m n f packet.1 (s - packet.1) *
    cartanSplit p q g packet.2 (t - packet.2)

/-- The product row is exactly the coefficient law obtained by literally
splitting the two source forms. -/
theorem cartanCrossPacketAmplitude_eq_kernel
    (m n p q s t : Nat) (hs : s ≤ m + n) (ht : t ≤ p + q)
    (f g : BForm) (packet : Nat × Nat)
    (hi : packet.1 ≤ s) (hk : packet.2 ≤ t) :
    cartanCrossPacketAmplitude m n p q s t f g packet ≈
      cartanCrossKernelAt m n p q s t hs ht packet * (f s * g t) := by
  have hfirst := cartanSplit_at_total m n f
    packet.1 (s - packet.1) s (Nat.add_sub_of_le hi) hs
  have hsecond := cartanSplit_at_total p q g
    packet.2 (t - packet.2) t (Nat.add_sub_of_le hk) ht
  refine Q'.eqv_trans _
    ((cartanBranchKernelAt m n s hs packet.1 * f s) *
      (cartanBranchKernelAt p q t ht packet.2 * g t)) _ ?_ ?_
  · exact mul_eqv_congr hfirst hsecond
  · exact mul_four_interchange _ _ _ _

/-- Finite expectation of an observable of the crossed, recombined output
monomial pair. -/
def cartanCrossExpectation
    (m n p q s t : Nat) (hs : s ≤ m + n) (ht : t ≤ p + q)
    (observable : Nat × Nat → Q') : Q' :=
  listQSum
    (fun packet => cartanCrossKernelAt m n p q s t hs ht packet *
      observable (cartanCrossOutput s t packet))
    (cartanCrossTargets s t)

/-- The crossed observable transport preserves the constant one. -/
theorem cartanCrossExpectation_one
    (m n p q s t : Nat) (hs : s ≤ m + n) (ht : t ≤ p + q) :
    cartanCrossExpectation m n p q s t hs ht (fun _ => 1) ≈ 1 := by
  refine Q'.eqv_trans _
    (listQSum (cartanCrossKernelAt m n p q s t hs ht)
      (cartanCrossTargets s t)) _ ?_
    (cartanCrossKernel_row_normalized m n p q s t hs ht)
  exact listQSum_congr
    (fun packet => Q'.mul_one_eqv
      (cartanCrossKernelAt m n p q s t hs ht packet))
    (cartanCrossTargets s t)

end YMGap.Continuum.SU2CartanTwoReplicaCrossTransport

#print axioms YMGap.Continuum.SU2CartanTwoReplicaCrossTransport.cartanCrossTargets_nodup
#print axioms YMGap.Continuum.SU2CartanTwoReplicaCrossTransport.cartanCrossKernelAt_nonnegative
#print axioms YMGap.Continuum.SU2CartanTwoReplicaCrossTransport.cartanCrossKernel_row_normalized
#print axioms YMGap.Continuum.SU2CartanTwoReplicaCrossTransport.cartanCrossOutput_total
#print axioms YMGap.Continuum.SU2CartanTwoReplicaCrossTransport.cartanCrossOutput_physical
#print axioms YMGap.Continuum.SU2CartanTwoReplicaCrossTransport.cartanCrossKernelAt_zero_of_unphysical
#print axioms YMGap.Continuum.SU2CartanTwoReplicaCrossTransport.cartanCrossOutput_physical_of_kernel_nonzero
#print axioms YMGap.Continuum.SU2CartanTwoReplicaCrossTransport.cartanCrossPacketAmplitude_eq_kernel
#print axioms YMGap.Continuum.SU2CartanTwoReplicaCrossTransport.cartanCrossExpectation_one
