/-
# Actual mixed alternating rectangle-to-half-diamond tail

The mixed cell retains both nome exponents and the signed Chebyshev
difference. The actual omitted rectangle cells are injected into the
existing even-shell enumeration on Nat times Int. Its mapped enumeration
can have duplicates; the finite shell bound requires only source Nodup,
coverage and the literal target-list length, not target Nodup.

Consumer: the independent exact alternating half-diamond reindex. The
original scalar shell modulus pays this tail; no new tail engine, supplied
discrepancy bound, completed addition identity or curvature ceiling is used.
-/

import YMGap.Continuum.ThetaParityDiamondTail

namespace YMGap.Continuum.ThetaAlternatingMixedTail

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ThetaParityConvolution
open YMGap.Continuum.ThetaParityShellGeometry
open YMGap.Continuum.ThetaParityShellEnumeration
open YMGap.Continuum.ThetaParityShellWeights (chebT_abs_le_one)
open YMGap.Continuum.ThetaParityDiamondTail (cellCap omittedBudget finite_shell_sum_bound)
open YMGap.Continuum.ThetaAngularShellTail
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm (listQSum)
open YMGap.Continuum.ChebTFwdBoundClose (ofNat_mul_eqv ofNat_le_ofNat)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv

/-- The literal mixed odd/even theta determinant cell. -/
def mixedCell (w x : Q') (p : Nat × Int) : Q' :=
  w^(2*(p.1*(p.1+1))+2*(p.2.natAbs*p.2.natAbs))*
    (Cheb.T (2*p.1+1) x + -(Cheb.T (2*p.2).natAbs x))

def mixedRectangleIndices (N : Nat) : List (Nat × Int) :=
  cartesian (List.range (N+1)) (signedIndices N)

/-- The exact half-diamond, not a rectangular replacement. -/
def mixedDiamondIndices (N : Nat) : List (Nat × Int) :=
  (mixedRectangleIndices N).filter (fun p => decide (p.1+p.2.natAbs ≤ N))

def mixedRadius (p : Nat × Int) : Nat := p.1+p.2.natAbs

private theorem mixed_exponent_ge_radius_sq (p : Nat × Int) :
    mixedRadius p*mixedRadius p ≤ 2*(p.1*(p.1+1))+2*(p.2.natAbs*p.2.natAbs) := by
  have hg := even_exponent_ge_radius_sq (p.1 : Int) p.2
  change (p.1+p.2.natAbs)*(p.1+p.2.natAbs) ≤
    2*(p.1*p.1+p.2.natAbs*p.2.natAbs) at hg
  change (p.1+p.2.natAbs)*(p.1+p.2.natAbs) ≤ _
  simp only [Nat.mul_add, Nat.mul_one] at hg ⊢
  omega

private theorem mixed_difference_abs_le_two {x : Q'}
    (hx0 : (-(1 : Q')) ≤ x) (hx1 : x ≤ (1 : Q')) (p : Nat × Int) :
    Q'.abs (Cheb.T (2*p.1+1) x + -(Cheb.T (2*p.2).natAbs x)) ≤ 2 := by
  have h1 := chebT_abs_le_one (2*p.1+1) hx0 hx1
  have h2 := chebT_abs_le_one (2*p.2).natAbs hx0 hx1
  have hn : Q'.abs (-(Cheb.T (2*p.2).natAbs x)) ≤ 1 :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (TsumDeriv.Q'.abs_neg _)) h2
  exact Q'.le_trans' _ _ _ (TsumDeriv.abs_add_le _ _)
    (Q'.le_trans' _ _ _ (Q'.add_le_add h1 hn)
      (Q'.le_of_eqv (by decide : (1 : Q')+1 ≈ 2)))

/-- Actual mixed-cell Gaussian estimate, including radius zero. -/
theorem mixedCell_abs_le {w x : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hx0 : (-(1 : Q')) ≤ x) (hx1 : x ≤ (1 : Q')) (p : Nat × Int) :
    Q'.abs (mixedCell w x p) ≤ 2*w^(mixedRadius p*mixedRadius p) := by
  let E := 2*(p.1*(p.1+1))+2*(p.2.natAbs*p.2.natAbs)
  have hp : (0 : Q') ≤ w^E := Q'.pow_nonneg w (Q'.le_of_lt hw0) E
  have hg : w^E ≤ w^(mixedRadius p*mixedRadius p) :=
    HKConvGen.pow_base_antitone (Q'.le_of_lt hw0) (Q'.le_of_lt hw1)
      (mixed_exponent_ge_radius_sq p)
  change Q'.abs (w^E*(Cheb.T (2*p.1+1) x + -(Cheb.T (2*p.2).natAbs x))) ≤ _
  refine Q'.le_trans' _ _ _ (TsumDeriv.Q'.abs_mul_le _ _) ?_
  refine Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ (mixed_difference_abs_le_two hx0 hx1 p)
      (Q'.abs_nonneg _)) ?_
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv
    (Q'.mul_eqv_congr_right _ _ 2 (TsumDeriv.Q'.abs_of_nonneg hp))) ?_
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv _ 2))
    (Q'.mul_le_mul_of_nonneg_left _ _ 2 hg (by decide))

/-- Every positive-radius mixed cell fits the already-constructed shell cap. -/
theorem mixedCell_abs_le_cellCap {w x : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hx0 : (-(1 : Q')) ≤ x) (hx1 : x ≤ (1 : Q')) (p : Nat × Int)
    (hR : 1 ≤ mixedRadius p) : Q'.abs (mixedCell w x p) ≤ cellCap w (mixedRadius p) := by
  have hn : 2 ≤ 4*(mixedRadius p*mixedRadius p) := by
    have hs := Nat.mul_le_mul hR hR
    omega
  have hpin : Q'.ofNat (4*(mixedRadius p*mixedRadius p)) ≈
      4*(Q'.ofNat (mixedRadius p)*Q'.ofNat (mixedRadius p)) :=
    Q'.eqv_trans _ _ _ (ofNat_mul_eqv 4 _)
      (Q'.mul_eqv_congr_left 4 _ _ (ofNat_mul_eqv _ _))
  have hc : (2 : Q') ≤ 4*(Q'.ofNat (mixedRadius p)*Q'.ofNat (mixedRadius p)) :=
    Q'.le_trans' _ _ _ (ofNat_le_ofNat hn) (Q'.le_of_eqv hpin)
  exact Q'.le_trans' _ _ _ (mixedCell_abs_le hw0 hw1 hx0 hx1 p)
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hc
      (Q'.pow_nonneg w (Q'.le_of_lt hw0) (mixedRadius p*mixedRadius p)))

private theorem range_nodup (N : Nat) : (List.range N).Nodup := by
  induction N with
  | zero => exact List.nodup_nil
  | succ N ih =>
      rw [List.range_succ]
      refine List.nodup_append.mpr
        ⟨ih, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
      intro i hi j hj hij
      have hjN : j = N := List.mem_singleton.mp hj
      rw [hij, hjN] at hi
      exact (Nat.lt_irrefl N) (List.mem_range.mp hi)

private theorem rectangle_nodup (N : Nat) : (mixedRectangleIndices N).Nodup := by
  have hi : (signedIndices N).Nodup :=
    YMGap.Continuum.TorusWilsonAction.nodup_map_on
      (fun i : Nat => (i : Int)-(N : Int))
      (fun i _ j _ he => by
        change (i : Int)-(N : Int) = (j : Int)-(N : Int) at he
        omega) (range_nodup (2*N+1))
  exact cartesian_nodup _ _ (range_nodup (N+1)) hi

private def mixedShellIndices (T : Nat) : List (Nat × Int) :=
  (evenShellIndices T).map (fun z => (z.1.toNat,z.2))

private theorem mixedShell_length (T : Nat) : (mixedShellIndices T).length = 4*T := by
  rw [mixedShellIndices, List.length_map, evenShellIndices_length]

private theorem mixedShell_covers (T : Nat) (hT : 1 ≤ T) (p : Nat × Int)
    (hr : mixedRadius p = T) : p ∈ mixedShellIndices T := by
  have hrs : evenRadius (p.1 : Int) p.2 = T := hr
  apply List.mem_map.mpr
  refine ⟨((p.1 : Int),p.2), evenShellIndices_mem_of_radius T hT _ hrs, ?_⟩
  cases p
  rfl

private theorem rectangle_radius_le (N : Nat) (p : Nat × Int)
    (hp : p ∈ mixedRectangleIndices N) : mixedRadius p ≤ 2*N+3 := by
  have hm := (mem_cartesian_iff (List.range (N+1)) (signedIndices N) p).1 hp
  have hh := List.mem_range.mp hm.1
  have hk := (signedIndices_mem N p.2).1 hm.2
  have hka : p.2.natAbs ≤ N := by
    by_cases hk0 : 0 ≤ p.2
    · have he := Int.natAbs_of_nonneg hk0
      omega
    · have he := Int.ofNat_natAbs_of_nonpos (show p.2 ≤ 0 by omega)
      omega
  dsimp [mixedRadius]
  omega

private theorem filter_error_pin (w x : Q') (N : Nat) :
    (listQSum (mixedCell w x) (mixedRectangleIndices N) +
      -listQSum (mixedCell w x) (mixedDiamondIndices N)) ≈
      listQSum (mixedCell w x) ((mixedRectangleIndices N).filter
        (fun p => !(decide (p.1+p.2.natAbs ≤ N)))) := by
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ _ (listQSum_filter_partition (mixedCell w x)
      (fun p => decide (p.1+p.2.natAbs ≤ N)) (mixedRectangleIndices N))) ?_
  exact poly_identity_of_normal_eq
    (.add (.add (.var 0) (.var 1)) (.neg (.var 0))) (.var 1) (by decide)
    (fun
      | 0 => listQSum (mixedCell w x) (mixedDiamondIndices N)
      | _ => listQSum (mixedCell w x) ((mixedRectangleIndices N).filter
          (fun p => !(decide (p.1+p.2.natAbs ≤ N)))))

/-- The literal mixed rectangle-to-half-diamond error is paid by the existing
Gaussian shell budget, uniformly in the actual scalar coordinate. -/
theorem mixed_rectangle_error_le {w x : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hx0 : (-(1 : Q')) ≤ x) (hx1 : x ≤ (1 : Q')) (N : Nat) :
    Q'.abs (listQSum (mixedCell w x) (mixedRectangleIndices N) +
      -listQSum (mixedCell w x) (mixedDiamondIndices N)) ≤ omittedBudget w N := by
  let source := (mixedRectangleIndices N).filter
    (fun p => !(decide (p.1+p.2.natAbs ≤ N)))
  have hlo : ∀ p, p ∈ source → N+1 ≤ mixedRadius p := by
    intro p hp
    have hn : ¬p.1+p.2.natAbs ≤ N := by
      intro h
      have hb := (List.mem_filter.mp hp).2
      rw [decide_eq_true h] at hb
      cases hb
    dsimp [mixedRadius]
    omega
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (TsumDeriv.Q'.abs_eqv_congr (filter_error_pin w x N))) ?_
  apply finite_shell_sum_bound (Q'.le_of_lt hw0) N source mixedRadius mixedShellIndices (mixedCell w x)
  · exact (rectangle_nodup N).filter _
  · exact hlo
  · intro p hp
    exact rectangle_radius_le N p (List.mem_filter.mp hp).1
  · exact mixedShell_covers
  · exact mixedShell_length
  · intro p hp
    exact mixedCell_abs_le_cellCap hw0 hw1 hx0 hx1 p (by
      have h := hlo p hp
      omega)

/-- Existing explicit nome-dependent shell cutoff pays any requested epsilon. -/
theorem mixed_rectangle_error_le_epsilon {w x epsilon : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hx0 : (-(1 : Q')) ≤ x) (hx1 : x ≤ (1 : Q')) (he : (0 : Q') < epsilon)
    (N : Nat) (hN : shellTailCutoff w epsilon ≤ N) :
    Q'.abs (listQSum (mixedCell w x) (mixedRectangleIndices N) +
      -listQSum (mixedCell w x) (mixedDiamondIndices N)) ≤ epsilon :=
  Q'.le_trans' _ _ _ (mixed_rectangle_error_le hw0 hw1 hx0 hx1 N)
    (shellTail_le_epsilon hw0 hw1 he (N+1) (N+3) (by omega))

end YMGap.Continuum.ThetaAlternatingMixedTail

#print axioms YMGap.Continuum.ThetaAlternatingMixedTail.mixedCell
#print axioms YMGap.Continuum.ThetaAlternatingMixedTail.mixedRectangleIndices
#print axioms YMGap.Continuum.ThetaAlternatingMixedTail.mixedDiamondIndices
#print axioms YMGap.Continuum.ThetaAlternatingMixedTail.mixedRadius
#print axioms YMGap.Continuum.ThetaAlternatingMixedTail.mixedCell_abs_le
#print axioms YMGap.Continuum.ThetaAlternatingMixedTail.mixedCell_abs_le_cellCap
#print axioms YMGap.Continuum.ThetaAlternatingMixedTail.mixed_rectangle_error_le
#print axioms YMGap.Continuum.ThetaAlternatingMixedTail.mixed_rectangle_error_le_epsilon
