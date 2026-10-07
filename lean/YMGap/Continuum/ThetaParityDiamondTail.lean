/-
# Actual diamond-to-rectangle theta and endpoint-jet errors

The parity diamonds are filtered from their literal ambient box N+1.
Every omitted cell is injected into an explicitly enumerated positive
shell. Four points per radius unit, with the actual Gaussian/frequency
weights, pay the existing 16*T^3*w^(T^2) scalar tail. No finite diamond is
identified with a rectangle; odd boundary asymmetry is not removed.

The final cutoff controls the actual signed convolution and its actual
endpoint-frequency-square jet, uniformly in x,y at each named nome.
This is not a completed addition formula, curvature ceiling or mass gap.
-/

import YMGap.Continuum.ThetaParityShellEnumeration
import YMGap.Continuum.ThetaParityShellWeights
import YMGap.Continuum.ThetaAngularShellTail

namespace YMGap.Continuum.ThetaParityDiamondTail

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.ThetaParityConvolution
open YMGap.Continuum.ThetaParityWeights
open YMGap.Continuum.ThetaParityShellGeometry
open YMGap.Continuum.ThetaParityShellEnumeration
open YMGap.Continuum.ThetaParityShellWeights
open YMGap.Continuum.ThetaAngularShellTail
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.ChebTFwdBoundClose (ofNat_nonneg ofNat_mul_eqv ofNat_le_ofNat)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv

/-- Explicit derivative-weighted cap for one positive-radius shell cell. -/
def cellCap (w : Q') (T : Nat) : Q' :=
  4*(Q'.ofNat T*Q'.ofNat T)*w^(T*T)

/-- Actual scalar budget for the finite omitted shells. -/
def omittedBudget (w : Q') (N : Nat) : Q' :=
  finSum (fun j => shellTerm w (N+1+j)) (N+3)

private theorem cellCap_nonneg {w : Q'} (hw : (0 : Q') ≤ w) (T : Nat) :
    (0 : Q') ≤ cellCap w T := by
  exact Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _ (by decide)
      (Q'.mul_nonneg _ _ (ofNat_nonneg T) (ofNat_nonneg T)))
    (Q'.pow_nonneg w hw (T*T))

private theorem gaussian_le_cellCap {w : Q'} (hw : (0 : Q') ≤ w)
    {T : Nat} (hT : 1 ≤ T) : w^(T*T) ≤ cellCap w T := by
  have hn : 1 ≤ 4*(T*T) := by
    have hs := Nat.mul_le_mul hT hT
    omega
  have hpin : Q'.ofNat (4*(T*T)) ≈ 4*(Q'.ofNat T*Q'.ofNat T) :=
    Q'.eqv_trans _ _ _ (ofNat_mul_eqv 4 (T*T))
      (Q'.mul_eqv_congr_left 4 _ _ (ofNat_mul_eqv T T))
  have hc : (1 : Q') ≤ 4*(Q'.ofNat T*Q'.ofNat T) :=
    Q'.le_trans' _ _ _ (ofNat_le_ofNat hn) (Q'.le_of_eqv hpin)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (Q'.one_mul_eqv _)))
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hc (Q'.pow_nonneg w hw (T*T)))

private theorem count_cellCap_pin (w : Q') (T : Nat) :
    Q'.ofNat (4*T)*cellCap w T ≈ shellTerm w T := by
  have hc : Q'.ofNat (T*T*T) ≈ (Q'.ofNat T*Q'.ofNat T)*Q'.ofNat T :=
    Q'.eqv_trans _ _ _ (ofNat_mul_eqv (T*T) T)
      (Q'.mul_eqv_congr_right _ _ _ (ofNat_mul_eqv T T))
  refine Q'.eqv_trans _ ((4*Q'.ofNat T)*cellCap w T) _
    (Q'.mul_eqv_congr_right _ _ _ (ofNat_mul_eqv 4 T)) ?_
  refine Q'.eqv_trans _
    (16*((Q'.ofNat T*Q'.ofNat T)*Q'.ofNat T)*w^(T*T)) _ ?_ ?_
  · exact poly_identity_of_normal_eq
      (.mul (.mul (.const 4) (.var 0))
        (.mul (.mul (.const 4) (.mul (.var 0) (.var 0))) (.var 1)))
      (.mul (.mul (.const 16) (.mul (.mul (.var 0) (.var 0)) (.var 0))) (.var 1))
      (by decide) (fun | 0 => Q'.ofNat T | _ => w^(T*T))
  · exact Q'.mul_eqv_congr_right _ _ _
      (Q'.mul_eqv_congr_left 16 _ _ (Q'.eqv_symm hc))

private theorem sum_const {A : Type} (c : Q') : ∀ xs : List A,
    listQSum (fun _ => c) xs ≈ Q'.ofNat xs.length*c
  | [] => Q'.eqv_symm (Q'.zero_mul_eqv c)
  | _ :: xs => by
      refine Q'.eqv_trans _ (c+Q'.ofNat xs.length*c) _
        (Q'.add_eqv_congr_left c _ _ (sum_const c xs)) ?_
      apply Q'.eqv_symm
      refine Q'.eqv_trans _ ((Q'.ofNat xs.length+1)*c) _
        (Q'.mul_eqv_congr_right _ _ c (Q'.ofNat_add_eqv xs.length 1)) ?_
      refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv _ _ _) ?_
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left _ _ _ (Q'.one_mul_eqv c)) (Q'.add_comm_eqv _ _)

private theorem sum_range (f : Nat → Q') : ∀ n,
    listQSum f (List.range n) ≈ finSum f n
  | 0 => Q'.eqv_refl 0
  | n+1 => by
      rw [List.range_succ]
      exact Q'.eqv_trans _ _ _ (listQSum_append f _ _)
        (Q'.add_eqv_congr' (sum_range f n) (Q'.eqv_of_eq (Q'.add_zero' (f n))))

private theorem abs_sum_le {A : Type} (weight : A → Q') : ∀ xs,
    Q'.abs (listQSum weight xs) ≤ listQSum (fun z => Q'.abs (weight z)) xs
  | [] => by
      change Q'.abs (0 : Q') ≤ (0 : Q')
      decide
  | z :: zs =>
      Q'.le_trans' _ _ _ (TsumDeriv.abs_add_le _ _)
        (Q'.add_le_add_left _ _ _ (abs_sum_le weight zs))

/-- Finite weighted shell injection on a decidable carrier. The caller
supplies finite enumeration/pointwise proofs, not a discrepancy estimate;
below and in the mixed alternating consumer these are actual constructions. -/
theorem finite_shell_sum_bound {A : Type} [DecidableEq A]
    {w : Q'} (hw : (0 : Q') ≤ w)
    (N : Nat) (source : List A) (radius : A → Nat)
    (shell : Nat → List A) (weight : A → Q')
    (hnd : source.Nodup)
    (hlo : ∀ z, z ∈ source → N+1 ≤ radius z)
    (hhi : ∀ z, z ∈ source → radius z ≤ 2*N+3)
    (hcover : ∀ T, 1 ≤ T → ∀ z, radius z = T → z ∈ shell T)
    (hcount : ∀ T, (shell T).length = 4*T)
    (hweight : ∀ z, z ∈ source → Q'.abs (weight z) ≤ cellCap w (radius z)) :
    Q'.abs (listQSum weight source) ≤ omittedBudget w N := by
  let target := (List.range (N+3)).flatMap (fun i =>
    (shell (N+1+i)).map (fun z => (i,z)))
  let encodeCell := fun z : A => (radius z-(N+1),z)
  let targetWeight := fun p : Nat × A => cellCap w (N+1+p.1)
  have hinj : listQSum (fun z => Q'.abs (weight z)) source ≤
      listQSum targetWeight target := by
    apply listQSum_le_of_injective source target _ targetWeight encodeCell hnd
    · intro z hz
      have hlow := hlo z hz
      have hhigh := hhi z hz
      have hi : radius z-(N+1) < N+3 := by omega
      have he : N+1+(radius z-(N+1)) = radius z := by omega
      apply List.mem_flatMap.mpr
      refine ⟨radius z-(N+1), List.mem_range.mpr hi, ?_⟩
      apply List.mem_map.mpr
      refine ⟨z, hcover _ (by omega) z he.symm, rfl⟩
    · intro z _ z' _ he
      exact congrArg Prod.snd he
    · intro z hz
      have he : N+1+(radius z-(N+1)) = radius z := by
        have h := hlo z hz
        omega
      simpa only [targetWeight, encodeCell, he] using hweight z hz
    · intro p _
      exact cellCap_nonneg hw _
  have htarget : listQSum targetWeight target ≈ omittedBudget w N := by
    refine Q'.eqv_trans _ _ _ (listQSum_flatMap _ _ _) ?_
    refine Q'.eqv_trans _
      (listQSum (fun i => shellTerm w (N+1+i)) (List.range (N+3))) _ ?_
      (sum_range _ _)
    apply listQSum_congr
    intro i
    rw [listQSum_map]
    change listQSum (fun _ => cellCap w (N+1+i)) (shell (N+1+i)) ≈
      shellTerm w (N+1+i)
    refine Q'.eqv_trans _ _ _ (sum_const (cellCap w (N+1+i)) (shell (N+1+i))) ?_
    rw [hcount]
    exact count_cellCap_pin w _
  exact Q'.le_trans' _ _ _ (abs_sum_le weight source)
    (Q'.le_trans' _ _ _ hinj (Q'.le_of_eqv htarget))

private theorem natAbs_box_le (N : Nat) (a : Int)
    (hlo : -(N : Int) ≤ a) (hhi : a ≤ N) : a.natAbs ≤ N := by
  by_cases ha : 0 ≤ a
  · have habs := Int.natAbs_of_nonneg ha
    omega
  · have habs := Int.ofNat_natAbs_of_nonpos (show a ≤ 0 by omega)
    omega

private theorem even_box_radius_le (N : Nat) (z : SignedPair)
    (hz : z ∈ boxIndices (N+1)) : evenRadius z.1 z.2 ≤ 2*N+3 := by
  have hb := (boxIndices_mem (N+1) z).1 hz
  have hj := natAbs_box_le (N+1) z.1 hb.1 hb.2.1
  have hk := natAbs_box_le (N+1) z.2 hb.2.2.1 hb.2.2.2
  unfold evenRadius
  omega

private theorem odd_box_radius_le (N : Nat) (z : SignedPair)
    (hz : z ∈ boxIndices (N+1)) : oddRadius z.1 z.2 ≤ 2*N+3 := by
  have hb := (boxIndices_mem (N+1) z).1 hz
  rcases hb with ⟨hjl, hjr, hkl, hkr⟩
  have hj := natAbs_box_le (2*(N+1)+1) (2*z.1+1) (by omega) (by omega)
  have hk := natAbs_box_le (2*(N+1)+1) (2*z.2+1) (by omega) (by omega)
  have hf := oddRadius_frequency_formula z.1 z.2
  omega

private theorem filter_error_pin (weight : SignedPair → Q') (N : Nat)
    (test : SignedPair → Bool) :
    (listQSum weight (boxIndices (N+1)) +
      -listQSum weight ((boxIndices (N+1)).filter test)) ≈
      listQSum weight ((boxIndices (N+1)).filter (fun z => !(test z))) := by
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ _ (listQSum_filter_partition weight test _)) ?_
  exact poly_identity_of_normal_eq
    (.add (.add (.var 0) (.var 1)) (.neg (.var 0))) (.var 1) (by decide)
    (fun | 0 => listQSum weight ((boxIndices (N+1)).filter test)
         | _ => listQSum weight ((boxIndices (N+1)).filter (fun z => !(test z))))

private theorem even_omitted_bound {w : Q'} (hw : (0 : Q') ≤ w)
    (N : Nat) (weight : SignedPair → Q')
    (hweight : ∀ z, N+1 ≤ evenRadius z.1 z.2 →
      Q'.abs (weight z) ≤ cellCap w (evenRadius z.1 z.2)) :
    Q'.abs (listQSum weight (boxIndices (N+1))+
      -listQSum weight (evenDiamondIndices N)) ≤ omittedBudget w N := by
  let source := (boxIndices (N+1)).filter (fun z => !(decide (EvenDiamondBound N z)))
  have hlo : ∀ z, z ∈ source → N+1 ≤ evenRadius z.1 z.2 := by
    intro z hz
    have hp : ¬EvenDiamondBound N z := by
      intro hp
      have hb := (List.mem_filter.mp hz).2
      rw [decide_eq_true hp] at hb
      cases hb
    have hr : ¬evenRadius z.1 z.2 ≤ N := by
      intro h
      exact hp ((evenDiamond_iff_radius N z.1 z.2).2 h)
    omega
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (TsumDeriv.Q'.abs_eqv_congr
      (filter_error_pin weight N (fun z => decide (EvenDiamondBound N z))))) ?_
  apply finite_shell_sum_bound hw N source (fun z => evenRadius z.1 z.2) evenShellIndices weight
  · exact (boxIndices_nodup (N+1)).filter _
  · exact hlo
  · intro z hz
    exact even_box_radius_le N z (List.mem_filter.mp hz).1
  · intro T hT z hr
    exact evenShellIndices_mem_of_radius T hT z hr
  · exact evenShellIndices_length
  · intro z hz
    exact hweight z (hlo z hz)

private theorem odd_omitted_bound {w : Q'} (hw : (0 : Q') ≤ w)
    (N : Nat) (weight : SignedPair → Q')
    (hweight : ∀ z, N+1 ≤ oddRadius z.1 z.2 →
      Q'.abs (weight z) ≤ cellCap w (oddRadius z.1 z.2)) :
    Q'.abs (listQSum weight (boxIndices (N+1))+
      -listQSum weight (oddDiamondIndices N)) ≤ omittedBudget w N := by
  let source := (boxIndices (N+1)).filter (fun z => !(decide (OddDiamondBound N z)))
  have hlo : ∀ z, z ∈ source → N+1 ≤ oddRadius z.1 z.2 := by
    intro z hz
    have hp : ¬OddDiamondBound N z := by
      intro hp
      have hb := (List.mem_filter.mp hz).2
      rw [decide_eq_true hp] at hb
      cases hb
    have hr : ¬oddRadius z.1 z.2 ≤ N := by
      intro h
      exact hp ((oddDiamond_iff_radius N z.1 z.2).2 h)
    omega
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (TsumDeriv.Q'.abs_eqv_congr
      (filter_error_pin weight N (fun z => decide (OddDiamondBound N z))))) ?_
  apply finite_shell_sum_bound hw N source (fun z => oddRadius z.1 z.2) oddShellIndices weight
  · exact (boxIndices_nodup (N+1)).filter _
  · exact hlo
  · intro z hz
    exact odd_box_radius_le N z (List.mem_filter.mp hz).1
  · intro T _ z hr
    exact oddShellIndices_mem_of_radius T z hr
  · exact oddShellIndices_length
  · intro z hz
    exact hweight z (hlo z hz)

/-- Actual even value discrepancy, with no supplied tail estimate. -/
theorem even_value_rectangle_error_le {w x y : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (hx0 : (-(1 : Q')) ≤ x) (hx1 : x ≤ (1 : Q'))
    (hy0 : (-(1 : Q')) ≤ y) (hy1 : y ≤ (1 : Q')) (N : Nat) :
    Q'.abs (listQSum (evenCell w x y) (boxIndices (N+1))+
      -listQSum (evenCell w x y) (evenDiamondIndices N)) ≤ omittedBudget w N := by
  apply even_omitted_bound (Q'.le_of_lt hw0)
  intro z hz
  exact Q'.le_trans' _ _ _ (evenCell_abs_le hw0 hw1 hx0 hx1 hy0 hy1 z.1 z.2)
    (gaussian_le_cellCap (Q'.le_of_lt hw0) (by omega))

/-- Actual shifted-odd value discrepancy retains the extra nome factor. -/
theorem odd_value_rectangle_error_le {w x y : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (hx0 : (-(1 : Q')) ≤ x) (hx1 : x ≤ (1 : Q'))
    (hy0 : (-(1 : Q')) ≤ y) (hy1 : y ≤ (1 : Q')) (N : Nat) :
    Q'.abs (listQSum (oddCell w x y) (boxIndices (N+1))+
      -listQSum (oddCell w x y) (oddDiamondIndices N)) ≤ omittedBudget w N := by
  apply odd_omitted_bound (Q'.le_of_lt hw0)
  intro z hz
  exact Q'.le_trans' _ _ _ (oddCell_abs_le hw0 hw1 hx0 hx1 hy0 hy1 z.1 z.2)
    (gaussian_le_cellCap (Q'.le_of_lt hw0) (by omega))

/-- The actual even endpoint-frequency-square jet uses the same shell budget. -/
theorem even_frequency_rectangle_error_le {w x : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (hx0 : (-(1 : Q')) ≤ x) (hx1 : x ≤ (1 : Q')) (N : Nat) :
    Q'.abs (listQSum (evenFrequencyCell w x) (boxIndices (N+1))+
      -listQSum (evenFrequencyCell w x) (evenDiamondIndices N)) ≤ omittedBudget w N := by
  apply even_omitted_bound (Q'.le_of_lt hw0)
  intro z _
  exact evenFrequencyCell_abs_le hw0 hw1 hx0 hx1 z.1 z.2

/-- The actual odd endpoint-frequency-square jet uses the same shell budget. -/
theorem odd_frequency_rectangle_error_le {w x : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (hx0 : (-(1 : Q')) ≤ x) (hx1 : x ≤ (1 : Q')) (N : Nat) :
    Q'.abs (listQSum (oddFrequencyCell w x) (boxIndices (N+1))+
      -listQSum (oddFrequencyCell w x) (oddDiamondIndices N)) ≤ omittedBudget w N := by
  apply odd_omitted_bound (Q'.le_of_lt hw0)
  intro z _
  exact oddFrequencyCell_abs_le hw0 hw1 hx0 hx1 z.1 z.2

/-- Explicit cutoff data paying both actual parity errors. -/
def rectangleTailCutoff (w epsilon : Q') : Nat :=
  shellTailCutoff w (HalfPow.half*epsilon)

private theorem budget_le_half_epsilon {w epsilon : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (he : (0 : Q') < epsilon)
    (N : Nat) (hN : rectangleTailCutoff w epsilon ≤ N) :
    omittedBudget w N ≤ HalfPow.half*epsilon := by
  exact shellTail_le_epsilon hw0 hw1
    (Q'.mul_pos ThetaSeriesC1Close.half_pos he) (N+1) (N+3) (by
      change shellTailCutoff w (HalfPow.half*epsilon) ≤ N at hN
      omega)

private theorem combine_errors {R0 R1 D0 D1 B epsilon : Q'}
    (hpin : B ≈ D0+D1)
    (h0 : Q'.abs (R0+-D0) ≤ HalfPow.half*epsilon)
    (h1 : Q'.abs (R1+-D1) ≤ HalfPow.half*epsilon) :
    Q'.abs ((R0+R1)+-B) ≤ epsilon := by
  have he : ((R0+R1)+-B) ≈ (R0+-D0)+(R1+-D1) := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left _ _ _ (Q'.neg_eqv_congr _ _ hpin)) ?_
    exact poly_identity_of_normal_eq
      (.add (.add (.var 0) (.var 1)) (.neg (.add (.var 2) (.var 3))))
      (.add (.add (.var 0) (.neg (.var 2))) (.add (.var 1) (.neg (.var 3))))
      (by decide) (fun | 0 => R0 | 1 => R1 | 2 => D0 | _ => D1)
  have hh : (HalfPow.half*epsilon+HalfPow.half*epsilon) ≈ epsilon :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_mul_eqv _ _ _))
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ epsilon
          (by decide : (HalfPow.half+HalfPow.half) ≈ (1 : Q')))
        (Q'.one_mul_eqv epsilon))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (TsumDeriv.Q'.abs_eqv_congr he))
    (Q'.le_trans' _ _ _ (TsumDeriv.abs_add_le _ _)
      (Q'.le_trans' _ _ _ (Q'.add_le_add h0 h1) (Q'.le_of_eqv hh)))

/-- Actual signed theta convolution approaches its two literal parity
rectangles, uniformly on the full square at each named nome. -/
theorem theta_box_rectangle_error_close {w x y epsilon : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hx0 : (-(1 : Q')) ≤ x) (hx1 : x ≤ (1 : Q'))
    (hy0 : (-(1 : Q')) ≤ y) (hy1 : y ≤ (1 : Q')) (he : (0 : Q') < epsilon)
    (N : Nat) (hN : rectangleTailCutoff w epsilon ≤ N) :
    Q'.abs ((listQSum (evenCell w x y) (boxIndices (N+1))+
      listQSum (oddCell w x y) (boxIndices (N+1)))+
      -listQSum (thetaCell w x y) (boxIndices N)) ≤ epsilon := by
  have hb := budget_le_half_epsilon hw0 hw1 he N hN
  exact combine_errors (theta_box_eq_diamonds w x y N)
    (Q'.le_trans' _ _ _ (even_value_rectangle_error_le hw0 hw1 hx0 hx1 hy0 hy1 N) hb)
    (Q'.le_trans' _ _ _ (odd_value_rectangle_error_le hw0 hw1 hx0 hx1 hy0 hy1 N) hb)

/-- Actual endpoint jet convolution has the SAME explicit rectangle cutoff.
It is the frequency-square derivative, not a free recursively named jet. -/
theorem frequency_box_rectangle_error_close {w x epsilon : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hx0 : (-(1 : Q')) ≤ x) (hx1 : x ≤ (1 : Q')) (he : (0 : Q') < epsilon)
    (N : Nat) (hN : rectangleTailCutoff w epsilon ≤ N) :
    Q'.abs ((listQSum (evenFrequencyCell w x) (boxIndices (N+1))+
      listQSum (oddFrequencyCell w x) (boxIndices (N+1)))+
      -listQSum (frequencyCell w x) (boxIndices N)) ≤ epsilon := by
  have hb := budget_le_half_epsilon hw0 hw1 he N hN
  exact combine_errors (frequency_box_eq_diamonds w x N)
    (Q'.le_trans' _ _ _ (even_frequency_rectangle_error_le hw0 hw1 hx0 hx1 N) hb)
    (Q'.le_trans' _ _ _ (odd_frequency_rectangle_error_le hw0 hw1 hx0 hx1 N) hb)

private theorem sum_scale (a : Q') (f : Int → Q') : ∀ xs,
    listQSum (fun j => a*f j) xs ≈ a*listQSum f xs
  | [] => Q'.eqv_symm (Q'.mul_zero_eqv a)
  | _ :: js => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.eqv_refl _) (sum_scale a f js))
      (Q'.eqv_symm (Q'.mul_add_eqv _ _ _))

private theorem rectangle_product_pin (a : Q') (f g : Int → Q') (N : Nat) :
    listQSum (fun z : SignedPair => a*f z.1*g z.2) (boxIndices N) ≈
      a*(listQSum f (signedIndices N)*listQSum g (signedIndices N)) :=
  Q'.eqv_trans _ _ _
    (listQSum_cartesian_product (fun j => a*f j) g _ _)
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (sum_scale a f _)) (Q'.mul_assoc_eqv _ _ _))

private theorem even_rectangle_product_pin (f g : Int → Q') (N : Nat) :
    listQSum (fun z : SignedPair => f z.1*g z.2) (boxIndices N) ≈
      listQSum f (signedIndices N)*listQSum g (signedIndices N) :=
  listQSum_cartesian_product f g _ _

/-- Exact scalar factorization of the literal value rectangles. The odd
sum remains unbalanced; no unsupported finite factor four is inserted. -/
theorem theta_rectangle_factored_pin (w x y : Q') (N : Nat) :
    (listQSum (evenCell w x y) (boxIndices N)+
      listQSum (oddCell w x y) (boxIndices N)) ≈
      (listQSum (evenThetaTerm w x) (signedIndices N)*
        listQSum (evenThetaTerm w y) (signedIndices N))+
      w*(listQSum (oddThetaTerm w x) (signedIndices N)*
        listQSum (oddThetaTerm w y) (signedIndices N)) :=
  Q'.add_eqv_congr'
    (even_rectangle_product_pin (evenThetaTerm w x) (evenThetaTerm w y) N)
    (rectangle_product_pin w (oddThetaTerm w x) (oddThetaTerm w y) N)

/-- Exact scalar factorization of the literal endpoint jet rectangles. -/
theorem frequency_rectangle_factored_pin (w x : Q') (N : Nat) :
    (listQSum (evenFrequencyCell w x) (boxIndices N)+
      listQSum (oddFrequencyCell w x) (boxIndices N)) ≈
      (listQSum (evenThetaTerm w x) (signedIndices N)*
        listQSum (fun k => Q'.ofNat ((2*k).natAbs*(2*k).natAbs)*
          w^(2*(k.natAbs*k.natAbs))) (signedIndices N))+
      w*(listQSum (oddThetaTerm w x) (signedIndices N)*
        listQSum (fun k => Q'.ofNat ((2*k+1).natAbs*(2*k+1).natAbs)*
          w^(2*(k*(k+1)).toNat)) (signedIndices N)) :=
  Q'.add_eqv_congr'
    (even_rectangle_product_pin (evenThetaTerm w x)
      (fun k => Q'.ofNat ((2*k).natAbs*(2*k).natAbs)*
        w^(2*(k.natAbs*k.natAbs))) N)
    (rectangle_product_pin w (oddThetaTerm w x)
      (fun k => Q'.ofNat ((2*k+1).natAbs*(2*k+1).natAbs)*
        w^(2*(k*(k+1)).toNat)) N)

/-- The actual signed box approaches the factored actual scalar sums. -/
theorem theta_box_factored_error_close {w x y epsilon : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hx0 : (-(1 : Q')) ≤ x) (hx1 : x ≤ (1 : Q'))
    (hy0 : (-(1 : Q')) ≤ y) (hy1 : y ≤ (1 : Q')) (he : (0 : Q') < epsilon)
    (N : Nat) (hN : rectangleTailCutoff w epsilon ≤ N) :
    Q'.abs (((listQSum (evenThetaTerm w x) (signedIndices (N+1))*
      listQSum (evenThetaTerm w y) (signedIndices (N+1)))+
      w*(listQSum (oddThetaTerm w x) (signedIndices (N+1))*
        listQSum (oddThetaTerm w y) (signedIndices (N+1))))+
      -listQSum (thetaCell w x y) (boxIndices N)) ≤ epsilon := by
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (TsumDeriv.Q'.abs_eqv_congr
      (Q'.add_eqv_congr_right _ _ _
        (Q'.eqv_symm (theta_rectangle_factored_pin w x y (N+1)))))) ?_
  exact theta_box_rectangle_error_close hw0 hw1 hx0 hx1 hy0 hy1 he N hN

/-- The actual endpoint-frequency-square box approaches its factored
actual scalar sums with the SAME cutoff as the value convolution. -/
theorem frequency_box_factored_error_close {w x epsilon : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hx0 : (-(1 : Q')) ≤ x) (hx1 : x ≤ (1 : Q')) (he : (0 : Q') < epsilon)
    (N : Nat) (hN : rectangleTailCutoff w epsilon ≤ N) :
    Q'.abs (((listQSum (evenThetaTerm w x) (signedIndices (N+1))*
      listQSum (fun k => Q'.ofNat ((2*k).natAbs*(2*k).natAbs)*
        w^(2*(k.natAbs*k.natAbs))) (signedIndices (N+1)))+
      w*(listQSum (oddThetaTerm w x) (signedIndices (N+1))*
        listQSum (fun k => Q'.ofNat ((2*k+1).natAbs*(2*k+1).natAbs)*
          w^(2*(k*(k+1)).toNat)) (signedIndices (N+1))))+
      -listQSum (frequencyCell w x) (boxIndices N)) ≤ epsilon := by
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (TsumDeriv.Q'.abs_eqv_congr
      (Q'.add_eqv_congr_right _ _ _
        (Q'.eqv_symm (frequency_rectangle_factored_pin w x (N+1)))))) ?_
  exact frequency_box_rectangle_error_close hw0 hw1 hx0 hx1 he N hN

end YMGap.Continuum.ThetaParityDiamondTail

#print axioms YMGap.Continuum.ThetaParityDiamondTail.even_value_rectangle_error_le
#print axioms YMGap.Continuum.ThetaParityDiamondTail.odd_value_rectangle_error_le
#print axioms YMGap.Continuum.ThetaParityDiamondTail.even_frequency_rectangle_error_le
#print axioms YMGap.Continuum.ThetaParityDiamondTail.odd_frequency_rectangle_error_le
#print axioms YMGap.Continuum.ThetaParityDiamondTail.theta_box_rectangle_error_close
#print axioms YMGap.Continuum.ThetaParityDiamondTail.frequency_box_rectangle_error_close
#print axioms YMGap.Continuum.ThetaParityDiamondTail.theta_rectangle_factored_pin
#print axioms YMGap.Continuum.ThetaParityDiamondTail.frequency_rectangle_factored_pin
#print axioms YMGap.Continuum.ThetaParityDiamondTail.theta_box_factored_error_close
#print axioms YMGap.Continuum.ThetaParityDiamondTail.frequency_box_factored_error_close
#print axioms YMGap.Continuum.ThetaParityDiamondTail.omittedBudget
#print axioms YMGap.Continuum.ThetaParityDiamondTail.rectangleTailCutoff
#print axioms YMGap.Continuum.ThetaParityDiamondTail.cellCap
#print axioms YMGap.Continuum.ThetaParityDiamondTail.finite_shell_sum_bound
