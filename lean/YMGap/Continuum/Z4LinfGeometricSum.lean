/-
# Summing strict geometric distance decay over actual four-dimensional faces

Block the distance into N steps with 16*r^N <= 1/2. A block-index-n fiber
lies in a ball of radius M+N*(n+1). The explicit quartic ball count is at
most C*16^n, so the existing finite geometric sum applies with no stronger
smallness premise than 0<=r<1. The support loss M and rate dependence remain
explicit; the arbitrary finite face list disappears from the budget.

The consumer is the sum of isolated ORIGINAL coupling-defect responses.
This counting estimate does not supply heterogeneous-background mixing.
-/
import YMGap.Continuum.Z4LinfShellCount
import YMGap.Continuum.PolynomialGeometricDecay
import YMGap.Continuum.FiniteSizeGeometricSum

namespace YMGap.Continuum.Z4LinfGeometricSum

set_option autoImplicit false
open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SepLatticeZ4Linf (linfDist)
open YMGap.Continuum.Z4LinfShellCount (ball_count)
open YMGap.Continuum.PolynomialGeometricDecay (blockLength blockLength_pos block_gain)
open YMGap.Continuum.PartitionUpperBound (nat_pow_le_two_pow_pow)
open YMGap.Continuum.PositiveContractionResidual (geometricCutoff geometric_bound)
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm (listQSum)

def blockIndex (root : Z4Plaq) (r : Q') (M : Nat) (face : Z4Plaq) : Nat :=
  (linfDist root face-M) / blockLength r 4

/-- Rate and support-size dependence, but no root or finite-volume parameter. -/
def countCap (r : Q') (M : Nat) : Nat :=
  ((2*(M+blockLength r 4)+1)^4*6)*16

private theorem block_radius {d M N n : Nat} (hN : 0 < N) (h : (d-M)/N = n) :
    d ≤ M+N*(n+1) := by
  have hr := Nat.mod_lt (d-M) hN
  have he := Nat.div_add_mod (d-M) N
  rw [h] at he
  rw [Nat.mul_succ]
  omega

private theorem block_count_arithmetic (M N n : Nat) :
    (2*(M+N*(n+1))+1)^4*6 ≤ (((2*(M+N)+1)^4*6)*16)*16^n := by
  have hM := Nat.mul_le_mul_left M (by omega : 1 ≤ n+1)
  have hbase : 2*(M+N*(n+1))+1 ≤ (2*(M+N)+1)*(n+1) := by
    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul, Nat.mul_assoc] at hM ⊢
    omega
  have hpow : (2*(M+N*(n+1))+1)^4 ≤ (2*(M+N)+1)^4*(n+1)^4 := by
    simpa only [Nat.mul_pow] using Nat.pow_le_pow_left hbase 4
  have hpoly : (n+1)^4 ≤ 16^(n+1) := nat_pow_le_two_pow_pow 4 (n+1)
  calc
    _ ≤ ((2*(M+N)+1)^4*(n+1)^4)*6 := Nat.mul_le_mul_right 6 hpow
    _ ≤ ((2*(M+N)+1)^4*16^(n+1))*6 :=
      Nat.mul_le_mul_right 6 (Nat.mul_le_mul_left _ hpoly)
    _ = _ := by rw [Nat.pow_succ 16 n]; ac_rfl

theorem block_fiber_count (root : Z4Plaq) (r : Q') (M : Nat)
    (faces : List Z4Plaq) (hn : faces.Nodup) (n : Nat) :
    (faces.filter (fun face => decide (n = blockIndex root r M face))).length ≤ countCap r M*16^n := by
  let R := M+blockLength r 4*(n+1)
  have hsub : ∀ face, face ∈ faces.filter (fun f => decide (n = blockIndex root r M f)) →
      face ∈ faces.filter (fun f => decide (linfDist root f ≤ R)) := by
    intro face hf
    have h := List.mem_filter.mp hf
    exact List.mem_filter.mpr ⟨h.1, decide_eq_true
      (block_radius (blockLength_pos r 4) (of_decide_eq_true h.2).symm)⟩
  exact Nat.le_trans
    (CayleyPruferInjection.nodup_subset_length_le _ _ (hn.filter _) hsub)
    (Nat.le_trans (ball_count root R faces hn) (block_count_arithmetic M (blockLength r 4) n))

theorem block_rate_lt_one {r : Q'} (hr0 : (0 : Q') ≤ r) (hr1 : r < (1 : Q')) :
    entropyRate 16 (r^blockLength r 4) < (1 : Q') :=
  Q'.lt_of_le_of_lt (block_gain hr0 hr1 4) (by decide : HalfPow.half < (1 : Q'))

/-- Computed finite-family tail budget, including the support-offset loss. -/
def tailCap {r : Q'} (hr0 : (0 : Q') ≤ r) (hr1 : r < (1 : Q')) (M d : Nat) : Q' :=
  tailBudget (countCap r M) 16 d (r^blockLength r 4) (block_rate_lt_one hr0 hr1)

theorem tailCap_nonnegative {r : Q'} (hr0 : (0 : Q') ≤ r) (hr1 : r < (1 : Q')) (M d : Nat) :
    (0 : Q') ≤ tailCap hr0 hr1 M d :=
  tailBudget_nonnegative _ _ _ (Q'.pow_nonneg _ hr0 _) _

private def maxSize {A : Type} (size : A → Nat) : List A → Nat
  | [] => 0
  | x::xs => max (size x) (maxSize size xs)

private theorem le_maxSize {A : Type} (size : A → Nat) : ∀ (xs : List A) (x : A),
    x ∈ xs → size x ≤ maxSize size xs
  | [], _, h => False.elim (List.not_mem_nil h)
  | y::ys, x, h => by
      rcases List.mem_cons.mp h with h | h
      · subst x; exact Nat.le_max_left _ _
      · exact Nat.le_trans (le_maxSize size ys x h) (Nat.le_max_right _ _)

/-- Every finite set of actual faces, including arbitrarily large volumes.
A lower block-distance d also yields a geometric spatial tail. -/
theorem finite_tail_bound {r : Q'} (hr0 : (0 : Q') ≤ r) (hr1 : r < (1 : Q'))
    (root : Z4Plaq) (M d : Nat) (faces : List Z4Plaq) (hn : faces.Nodup)
    (hfar : ∀ face, face ∈ faces → d ≤ blockIndex root r M face) :
    listQSum (fun face => r^(linfDist root face-M)) faces ≤ tailCap hr0 hr1 M d := by
  have hp (face : Z4Plaq) : r^(linfDist root face-M) ≤
      (r^blockLength r 4)^(blockIndex root r M face) :=
    Q'.le_trans' _ _ _
      (HKConvGen.pow_base_antitone hr0 (Q'.le_of_lt hr1)
        (by simpa only [Nat.mul_comm] using Nat.div_mul_le_self (linfDist root face-M) (blockLength r 4)))
      (Q'.ge_of_eqv (TotalMajorantClose.pow_mul r (blockLength r 4) _))
  exact Q'.le_trans' _ _ _ (sum_le_on _ _ faces (fun face _ => hp face))
    (size_sum_bound faces (blockIndex root r M) (countCap r M) 16 d
      (maxSize (blockIndex root r M) faces) (Q'.pow_nonneg _ hr0 _)
      (block_rate_lt_one hr0 hr1) hfar (le_maxSize _ _) (block_fiber_count root r M faces hn))

theorem finite_sum_bound {r : Q'} (hr0 : (0 : Q') ≤ r) (hr1 : r < (1 : Q'))
    (root : Z4Plaq) (M : Nat) (faces : List Z4Plaq) (hn : faces.Nodup) :
    listQSum (fun face => r^(linfDist root face-M)) faces ≤ tailCap hr0 hr1 M 0 :=
  finite_tail_bound hr0 hr1 root M 0 faces hn (fun _ _ => Nat.zero_le _)

/-- Explicit block threshold for an amplitude-scaled spatial tail. -/
def blockCutoff {r : Q'} (hr0 : (0 : Q') ≤ r) (hr1 : r < (1 : Q'))
    (M : Nat) (A epsilon : Q') : Nat :=
  let s := entropyRate 16 (r^blockLength r 4)
  geometricCutoff s ((A*Q'.ofNat (countCap r M))*
    Q'.recipPos (1 + -s) (HKPos.one_sub_pos (block_rate_lt_one hr0 hr1))) epsilon

/-- A physical lattice-distance threshold, not just existence of a small tail. -/
def radiusCutoff {r : Q'} (hr0 : (0 : Q') ≤ r) (hr1 : r < (1 : Q'))
    (M : Nat) (A epsilon : Q') : Nat := M+blockLength r 4*blockCutoff hr0 hr1 M A epsilon

theorem scaled_tailCap_small {r A epsilon : Q'} (hr0 : (0 : Q') ≤ r) (hr1 : r < (1 : Q'))
    (hA : (0 : Q') ≤ A) (he : (0 : Q') < epsilon) (M d : Nat)
    (hd : blockCutoff hr0 hr1 M A epsilon ≤ d) : A*tailCap hr0 hr1 M d ≤ epsilon := by
  let s := entropyRate 16 (r^blockLength r 4)
  let i := Q'.recipPos (1 + -s) (HKPos.one_sub_pos (block_rate_lt_one hr0 hr1))
  have hs0 : (0 : Q') ≤ s := Q'.mul_nonneg _ _ (ClusterCount.ofNat_nonneg _) (Q'.pow_nonneg _ hr0 _)
  have hC : (0 : Q') ≤ (A*Q'.ofNat (countCap r M))*i :=
    Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ hA (ClusterCount.ofNat_nonneg _))
      (Q'.le_of_lt (Q'.recipPos_pos _ _))
  have hpin : Q'.eqv (A*tailCap hr0 hr1 M d) (s^d*((A*Q'.ofNat (countCap r M))*i)) := by
    change Q'.eqv (A*((Q'.ofNat (countCap r M)*s^d)*i)) _
    show _ * (_ : Int) = _ * (_ : Int)
    simp only [Q'.mul_num_cast, Q'.mul_den_cast]
    ac_rfl
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hpin)
    (geometric_bound hs0 (block_rate_lt_one hr0 hr1) hC he d hd)

theorem radiusCutoff_block_le {r : Q'} (hr0 : (0 : Q') ≤ r) (hr1 : r < (1 : Q'))
    (root face : Z4Plaq) (M : Nat) (A epsilon : Q')
    (h : radiusCutoff hr0 hr1 M A epsilon ≤ linfDist root face) :
    blockCutoff hr0 hr1 M A epsilon ≤ blockIndex root r M face := by
  apply (Nat.le_div_iff_mul_le (blockLength_pos r 4)).mpr
  change M+blockLength r 4*blockCutoff hr0 hr1 M A epsilon ≤ linfDist root face at h
  rw [Nat.mul_comm]
  omega

end YMGap.Continuum.Z4LinfGeometricSum

#print axioms YMGap.Continuum.Z4LinfGeometricSum.blockIndex
#print axioms YMGap.Continuum.Z4LinfGeometricSum.countCap
#print axioms YMGap.Continuum.Z4LinfGeometricSum.block_fiber_count
#print axioms YMGap.Continuum.Z4LinfGeometricSum.block_rate_lt_one
#print axioms YMGap.Continuum.Z4LinfGeometricSum.tailCap
#print axioms YMGap.Continuum.Z4LinfGeometricSum.tailCap_nonnegative
#print axioms YMGap.Continuum.Z4LinfGeometricSum.finite_tail_bound
#print axioms YMGap.Continuum.Z4LinfGeometricSum.finite_sum_bound
#print axioms YMGap.Continuum.Z4LinfGeometricSum.blockCutoff
#print axioms YMGap.Continuum.Z4LinfGeometricSum.radiusCutoff
#print axioms YMGap.Continuum.Z4LinfGeometricSum.scaled_tailCap_small
#print axioms YMGap.Continuum.Z4LinfGeometricSum.radiusCutoff_block_le
