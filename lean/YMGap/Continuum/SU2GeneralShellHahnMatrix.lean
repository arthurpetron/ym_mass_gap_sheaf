/-
# The general shell matrix for simultaneous Cayley channels

For a fixed total source weight `t`, the monomial tensors are indexed by their
left weight `i`, and the Clebsch--Gordan summands are indexed by contraction
order `k`.  This module identifies every matrix entry with the already derived
alternating falling-factorial coefficient and proves that the whole image is
supported on the single output monomial `t-k`.  The first three rows are then
exposed explicitly: constant, affine, and quadratic Hahn rows.

This is the square matrix whose constructive inverse is the next all-label
multi-channel task.  No determinant or nonsingularity premise is assumed here.
-/

import YMGap.Continuum.SU2SpinHalfAllLabelDirectSumCoordinateBasis

namespace YMGap.Continuum.SU2GeneralShellHahnMatrix

open YMGap.Constructive
open YMGap.Continuum.BinaryForms
open YMGap.Continuum.TransvectantCG
open YMGap.Continuum.SU2TransvectantLinearity
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2TransvectantFactorialSeed
open YMGap.Continuum.SU2TransvectantAllOrder

/-- Monomial tensor in the total-weight shell `t`, indexed by its left weight. -/
def shellBasis (t i : Nat) : BForm2 :=
  tprod (mono i) (mono (t - i))

/-- Exact `(contraction order, source weight)` matrix entry. -/
def hahnEntry (m n t k i : Nat) : Q' :=
  transvectFactorialCoeff m n k i (t - i)

/-- Physical source-column guard for a tensor in bidegree `(m,n)`. -/
def SourceActive (m n t i : Nat) : Prop :=
  i ≤ t ∧ i ≤ m ∧ t - i ≤ n

/-- Physical channel-row guard on total source weight `t`. -/
def ChannelActive (m n t k : Nat) : Prop :=
  k ≤ m ∧ k ≤ n ∧ k ≤ t ∧ t - k ≤ m + n - 2 * k

/-- First physical source weight on shell `t`. -/
def shellLo (n t : Nat) : Nat := t - n

/-- Last physical source weight on shell `t`. -/
def shellHi (m t : Nat) : Nat := min m t

/-- The common zero-based width of the physical source columns and channel
rows. -/
def shellWidth (m n t : Nat) : Nat := shellHi m t - shellLo n t

theorem shellLo_le_shellHi (m n t : Nat) (ht : t ≤ m + n) :
    shellLo n t ≤ shellHi m t := by
  unfold shellLo shellHi
  rw [Nat.le_min]
  constructor
  · omega
  · omega

/-- Zero-based source enumeration `a |-> t-n+a` lands in every physical
column when the shell itself is nonempty. -/
theorem sourceActive_of_index (m n t a : Nat) (ht : t ≤ m + n)
    (ha : a ≤ shellWidth m n t) :
    SourceActive m n t (shellLo n t + a) := by
  have hlo := shellLo_le_shellHi m n t ht
  have hsum : shellLo n t + a ≤ shellHi m t := by
    unfold shellWidth at ha
    omega
  unfold SourceActive shellLo shellHi at *
  constructor
  · exact Nat.le_trans hsum (Nat.min_le_right _ _)
  constructor
  · exact Nat.le_trans hsum (Nat.min_le_left _ _)
  · omega

/-- Every physical source column has a unique zero-based index in the common
interval. -/
theorem sourceActive_index_complete (m n t i : Nat) (hi : SourceActive m n t i) :
    let a := i - shellLo n t
    a ≤ shellWidth m n t ∧ shellLo n t + a = i := by
  dsimp
  have hlo : shellLo n t ≤ i := by
    unfold SourceActive shellLo at *
    omega
  have hihi : i ≤ shellHi m t := by
    unfold SourceActive shellHi at *
    exact Nat.le_min.mpr ⟨hi.2.1, hi.1⟩
  constructor
  · unfold shellWidth
    omega
  · omega

/-- The same zero-based interval enumerates every physical contraction row. -/
theorem channelActive_of_index (m n t k : Nat) (ht : t ≤ m + n)
    (hk : k ≤ shellWidth m n t) :
    ChannelActive m n t k := by
  have hlo := shellLo_le_shellHi m n t ht
  have hwidthHi : shellWidth m n t ≤ shellHi m t := by
    unfold shellWidth
    omega
  have hkm : k ≤ m :=
    Nat.le_trans (Nat.le_trans hk hwidthHi) (Nat.min_le_left _ _)
  have hkt : k ≤ t :=
    Nat.le_trans (Nat.le_trans hk hwidthHi) (Nat.min_le_right _ _)
  have hkn : k ≤ n := by
    unfold shellWidth shellHi shellLo at hk
    omega
  have htk : t + k ≤ m + n := by
    unfold shellWidth shellHi shellLo at hk
    omega
  have h2k : 2 * k ≤ m + n := by omega
  unfold ChannelActive
  exact ⟨hkm, hkn, hkt, by omega⟩

/-- Conversely, every physical contraction row lies in the common interval. -/
theorem channelActive_index_complete (m n t k : Nat) (ht : t ≤ m + n)
    (hk : ChannelActive m n t k) :
    k ≤ shellWidth m n t := by
  unfold ChannelActive shellWidth shellHi shellLo at *
  omega

/-- Every general shell-matrix column in channel `k` is exactly one monomial
times the alternating factorial entry. -/
theorem shellBasis_transvect_form (m n t k i : Nat)
    (hi : i ≤ t) (hk : k ≤ t) :
    BFormEqv (transvect m n k (shellBasis t i))
      (fun s => hahnEntry m n t k i * mono (t - k) s) := by
  intro s
  have hitotal : i + (t - i) = t := Nat.add_sub_of_le hi
  have h := transvect_monomial_factorial_formula m n k i (t - i) s
  by_cases hs : s = t - k
  · subst s
    have hcond : t - k + k = i + (t - i) := by
      rw [hitotal, Nat.sub_add_cancel hk]
    have hentry :
        (transvect m n k (shellBasis t i) (t - k)).eqv
          (hahnEntry m n t k i) := by
      simpa only [shellBasis, hahnEntry, if_pos hcond] using h
    refine Q'.eqv_trans _ (hahnEntry m n t k i) _ hentry ?_
    simp only [mono, if_pos]
    exact Q'.eqv_symm (Q'.mul_one_eqv _)
  · have hcond : ¬ s + k = i + (t - i) := by
      rw [hitotal]
      intro hsk
      have : s = t - k := by omega
      exact hs this
    have hzero :
        (transvect m n k (shellBasis t i) s).eqv 0 := by
      simpa only [shellBasis, if_neg hcond] using h
    refine Q'.eqv_trans _ 0 _ hzero ?_
    simp only [mono, if_neg hs]
    exact Q'.eqv_symm (Q'.mul_zero_eqv _)

/-- The zeroth Hahn row is constant one. -/
theorem hahnEntry_zero (m n t i : Nat) :
    (hahnEntry m n t 0 i).eqv 1 := by
  exact transvectFactorialCoeff_zero m n i (t - i)

/-- The first Hahn row is the signed affine Cayley coefficient. -/
theorem hahnEntry_one (m n t i : Nat) :
    (hahnEntry m n t 1 i).eqv
      (Q'.ofNat (i * (n - (t - i))) +
        -(Q'.ofNat ((m - i) * (t - i)))) := by
  exact transvectFactorialCoeff_one m n i (t - i)

/-- The second Hahn row is the exact quadratic three-term coefficient, with
the Pascal multiplicity two in its middle contraction. -/
theorem hahnEntry_two (m n t i : Nat) :
    (hahnEntry m n t 2 i).eqv
      (Q'.ofNat ((i * (i - 1)) *
          ((n - (t - i)) * (n - (t - i) - 1))) +
        -(Q'.ofNat (2 * i * (m - i) * (t - i) * (n - (t - i)))) +
        Q'.ofNat (((m - i) * (m - i - 1)) *
          ((t - i) * (t - i - 1)))) := by
  exact transvectFactorialCoeff_two m n i (t - i)

/-- Physical columns and rows use the same exact shell formula; the guards are
recorded explicitly for the coming square-matrix enumeration. -/
theorem active_shellBasis_transvect_form (m n t k i : Nat)
    (hi : SourceActive m n t i) (hk : ChannelActive m n t k) :
    BFormEqv (transvect m n k (shellBasis t i))
      (fun s => hahnEntry m n t k i * mono (t - k) s) :=
  shellBasis_transvect_form m n t k i hi.1 hk.2.2.1

end YMGap.Continuum.SU2GeneralShellHahnMatrix

#print axioms YMGap.Continuum.SU2GeneralShellHahnMatrix.shellBasis_transvect_form
#print axioms YMGap.Continuum.SU2GeneralShellHahnMatrix.sourceActive_of_index
#print axioms YMGap.Continuum.SU2GeneralShellHahnMatrix.sourceActive_index_complete
#print axioms YMGap.Continuum.SU2GeneralShellHahnMatrix.channelActive_of_index
#print axioms YMGap.Continuum.SU2GeneralShellHahnMatrix.channelActive_index_complete
#print axioms YMGap.Continuum.SU2GeneralShellHahnMatrix.hahnEntry_zero
#print axioms YMGap.Continuum.SU2GeneralShellHahnMatrix.hahnEntry_one
#print axioms YMGap.Continuum.SU2GeneralShellHahnMatrix.hahnEntry_two
#print axioms YMGap.Continuum.SU2GeneralShellHahnMatrix.active_shellBasis_transvect_form
