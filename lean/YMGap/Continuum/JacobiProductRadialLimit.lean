/-
# The actual Jacobi product radial cost as a constructive real

The literal finite moment cost D_N is realized by its own rational
approximants. Signed increments are bounded by HKConv.sTerm, whose
base-w^2 majorant supplies convergence. The rational rescaling and Nat
cutoff are explicit data, not extracted from CReal's legacy Prop modulus.

Cstar(w) enters ONLY the convergence modulus. It is not a curvature
ceiling. A separate consumer transfers a bound on this SAME limit back
to finite prefixes using the signed small-tail payment, not monotonicity.
No theta addition identity, analytic ceiling, angular/Haar certificate,
original-action estimate, OS statement or physical scaling is asserted.
-/

import YMGap.Continuum.JacobiProductRadialSignedTail
import YMGap.Constructive.RegularCReal
import YMGap.Constructive.CRealLe

namespace YMGap.Continuum.JacobiProductRadialLimit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.JacobiHeatRadialMixtureCancellation
open YMGap.Continuum.JacobiProductRadialSignedTail
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv

private def costSequence (w x : Q') (N : Nat) : Q' :=
  productRadialCost (HKConv.sTerm w x) N x

private theorem nome_square_lt_one {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) : w*w < (1 : Q') :=
  HKPos.q_lt_of_le_of_lt (Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right w 1 w (Q'.le_of_lt hw1) (Q'.le_of_lt hw0))
    (Q'.le_of_eqv (Q'.one_mul_eqv w))) hw1

private theorem costSequence_succ (w x : Q') (N : Nat) :
    costSequence w x (N+1) ≈ costSequence w x N + radialSummand w x N :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (radialSummand_sum_pin w x (N+1)))
    (Q'.add_eqv_congr_right _ _ _ (radialSummand_sum_pin w x N))

/-- Actual signed radial increments have the all-cutoff geometric bound.
The density reciprocal belongs to this convergence estimate only. -/
theorem radialSummand_geo_bounds {w x : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hx0 : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) (N : Nat) :
    -(HKConvGen.geoIncrBase (HKConv.Cstar w) (w*w) N) ≤ radialSummand w x N ∧
      radialSummand w x N ≤ HKConvGen.geoIncrBase (HKConv.Cstar w) (w*w) N := by
  have hr := HKConvGen.sTerm_le_geoIncrBase hw0 hw1 hx0 N
  have hd := radialSummand_bounds hw0 hw1 hx0 hx1 N
  exact ⟨Q'.le_trans' _ _ _ (Q'.neg_le_neg hr) hd.1,
    Q'.le_trans' _ _ _ hd.2 hr⟩

private theorem costSequence_step_up {w x : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hx0 : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) (N : Nat) :
    costSequence w x (N+1) ≤ costSequence w x N +
      HKConvGen.geoIncrBase (HKConv.Cstar w) (w*w) N :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv (costSequence_succ w x N))
    (Q'.add_le_add_left _ _ _ (radialSummand_geo_bounds hw0 hw1 hx0 hx1 N).2)

private theorem costSequence_step_lo {w x : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hx0 : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) (N : Nat) :
    costSequence w x N ≤ costSequence w x (N+1) +
      HKConvGen.geoIncrBase (HKConv.Cstar w) (w*w) N := by
  let G := HKConvGen.geoIncrBase (HKConv.Cstar w) (w*w) N
  have hz : (0 : Q') ≤ radialSummand w x N + G :=
    Q'.le_trans' _ _ _
      (Q'.sub_nonneg_of_le (radialSummand_geo_bounds hw0 hw1 hx0 hx1 N).1)
      (Q'.le_of_eqv (Q'.add_eqv_congr_left _ _ _ (Q'.neg_neg_eqv G)))
  exact Q'.le_trans' _ _ _
    (Q'.add_le_self_of_nonneg (costSequence w x N) _ hz)
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _))
      (Q'.add_eqv_congr_right _ _ G (Q'.eqv_symm (costSequence_succ w x N)))))

/-- Geometric tail prefactor, used only to compute the convergence modulus. -/
def radialTailPrefactor (w : Q') : Q' :=
  HKConv.Cstar w * HKConv.divPos 1 (1 + -(w*w))

/-- Explicit rescaled tolerance; no existential witness is extracted. -/
def radialTolerance (w epsilon : Q') : Q' :=
  HKConv.divPos epsilon (radialTailPrefactor w)

/-- The actual finite-product cutoff, as Nat data. -/
def radialCutoff (w epsilon : Q') : Nat :=
  HKConvGen.powBaseCutoff (w*w) (radialTolerance w epsilon)

private theorem radialTailPrefactor_pos {w : Q'} (hw0 : (0 : Q') < w) :
    (0 : Q') < radialTailPrefactor w :=
  HKPos.q_mul_pos (CReal.pos_of_num_pos (HKConv.Cstar_num_pos hw0))
    (HKConv.divPos_pos (by decide : (0 : Int) < (1 : Q').num))

theorem radialTolerance_pos (w epsilon : Q') (hepsilon : (0 : Q') < epsilon) :
    (0 : Q') < radialTolerance w epsilon :=
  HKConv.divPos_pos (CReal.num_pos_of_pos hepsilon)

private theorem radialTolerance_payment {w : Q'} (hw0 : (0 : Q') < w)
    (epsilon : Q') : radialTailPrefactor w * radialTolerance w epsilon ≈ epsilon :=
  Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _)
    (HKConv.divPos_mul_eqv (CReal.num_pos_of_pos (radialTailPrefactor_pos hw0)))

/-- The named Nat cutoff pays the geometric tail at every later index. -/
theorem radialCutoff_tail_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon) (N : Nat)
    (hN : radialCutoff w epsilon ≤ N) :
    HKConvGen.geoTailBase (HKConv.Cstar w) (w*w) N ≤ epsilon := by
  have hpower : (w*w)^N ≤ radialTolerance w epsilon := Q'.le_trans' _ _ _
    (HKConvGen.pow_base_antitone (Q'.le_of_lt (HKPos.q_mul_pos hw0 hw0))
      (Q'.le_of_lt (nome_square_lt_one hw0 hw1)) hN)
    (HKConvGen.pow_base_le_cutoff (HKPos.q_mul_pos hw0 hw0)
      (nome_square_lt_one hw0 hw1) (radialTolerance_pos w epsilon hepsilon))
  have hpin : HKConvGen.geoTailBase (HKConv.Cstar w) (w*w) N ≈
      radialTailPrefactor w*(w*w)^N :=
    poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 1)) (.var 2))
      (.mul (.mul (.var 0) (.var 2)) (.var 1)) (by decide)
      (fun | 0 => HKConv.Cstar w | 1 => (w*w)^N
           | _ => HKConv.divPos 1 (1 + -(w*w)))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hpin)
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hpower
      (Q'.le_of_lt (radialTailPrefactor_pos hw0)))
      (Q'.le_of_eqv (radialTolerance_payment hw0 epsilon)))

/-- The limit is constructed from the actual finite moment costs. -/
def productRadialCostCReal {w x : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hx0 : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) : CReal :=
  HKConvGen.crealOfGeoIncrementBase (costSequence w x) (HKConv.Cstar w) (w*w)
    (Q'.le_of_lt (CReal.pos_of_num_pos (HKConv.Cstar_num_pos hw0)))
    (HKPos.q_mul_pos hw0 hw0) (nome_square_lt_one hw0 hw1)
    (costSequence_step_up hw0 hw1 hx0 hx1) (costSequence_step_lo hw0 hw1 hx0 hx1)
    (fun epsilon hepsilon => ⟨radialTolerance w epsilon,
      radialTolerance_pos w epsilon hepsilon,
      Q'.le_of_eqv (radialTolerance_payment hw0 epsilon)⟩)

/-- No reindexing or replacement of the actual finite product cost. -/
@[simp] theorem productRadialCostCReal_approx {w x : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hx0 : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) (N : Nat) :
    (productRadialCostCReal hw0 hw1 hx0 hx1).approx N =
      productRadialCost (HKConv.sTerm w x) N x := rfl

private theorem costSequence_tail_bounds {w x : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hx0 : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) (N L : Nat) :
    costSequence w x (N+L) ≤ costSequence w x N +
      HKConvGen.geoTailBase (HKConv.Cstar w) (w*w) N ∧
    costSequence w x N ≤ costSequence w x (N+L) +
      HKConvGen.geoTailBase (HKConv.Cstar w) (w*w) N := by
  have htail := HKConvGen.geoTailBase_series_le
    (Q'.le_of_lt (CReal.pos_of_num_pos (HKConv.Cstar_num_pos hw0)))
    (HKPos.q_mul_pos hw0 hw0) (nome_square_lt_one hw0 hw1) N L
  exact ⟨Q'.le_trans' _ _ _
    (telescope_up _ _ (costSequence_step_up hw0 hw1 hx0 hx1) N L)
    (Q'.add_le_add_left _ _ _ htail),
    Q'.le_trans' _ _ _
    (telescope_lo _ _ (costSequence_step_lo hw0 hw1 hx0 hx1) N L)
    (Q'.add_le_add_left _ _ _ htail)⟩

/-- Explicit modulus on the actual approximants, separate from the legacy
Prop-level CReal modulus. The cutoff depends on w and tolerance, not x. -/
theorem radialCutoff_cauchy {w x : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hx0 : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon) (m n : Nat)
    (hm : radialCutoff w epsilon ≤ m) (hn : radialCutoff w epsilon ≤ n) :
    productRadialCost (HKConv.sTerm w x) m x ≤
      productRadialCost (HKConv.sTerm w x) n x + epsilon ∧
    productRadialCost (HKConv.sTerm w x) n x ≤
      productRadialCost (HKConv.sTerm w x) m x + epsilon := by
  rcases Nat.le_total m n with hmn | hnm
  · obtain ⟨L, rfl⟩ := Nat.exists_eq_add_of_le hmn
    have h := costSequence_tail_bounds hw0 hw1 hx0 hx1 m L
    have ht := radialCutoff_tail_le hw0 hw1 epsilon hepsilon m hm
    exact ⟨Q'.le_trans' _ _ _ h.2 (Q'.add_le_add_left _ _ _ ht),
      Q'.le_trans' _ _ _ h.1 (Q'.add_le_add_left _ _ _ ht)⟩
  · obtain ⟨L, rfl⟩ := Nat.exists_eq_add_of_le hnm
    have h := costSequence_tail_bounds hw0 hw1 hx0 hx1 n L
    have ht := radialCutoff_tail_le hw0 hw1 epsilon hepsilon n hn
    exact ⟨Q'.le_trans' _ _ _ h.1 (Q'.add_le_add_left _ _ _ ht),
      Q'.le_trans' _ _ _ h.2 (Q'.add_le_add_left _ _ _ ht)⟩

/-- A bound on the SAME constructed limit pays a finite prefix with the
small signed tail. Cstar does not occur in this finite ceiling. -/
theorem productRadialCost_le_limit_ceiling {w x : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hx0 : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (C : Q') (hC : CReal.leRat (productRadialCostCReal hw0 hw1 hx0 hx1) C)
    (N : Nat) (hN : HKPos.geoAmp w N ≤ eighth) :
    productRadialCost (HKConv.sTerm w x) N x ≤ C + radialTailPayment w N := by
  apply Q'.le_of_le_add_mul_invSucc _ _ 1
  intro precision
  obtain ⟨M, hM⟩ := hC (Q'.invSucc precision) (Q'.invSucc_pos precision)
  let m := max N M
  have hm : N ≤ m := Nat.le_max_left _ _
  have hfinite := productRadialCost_finite_tail_le hw0 hw1 hx0 hx1 N hN (m-N)
  have he : N+(m-N) = m := Nat.add_sub_of_le hm
  rw [he] at hfinite
  have hlim : productRadialCost (HKConv.sTerm w x) m x ≤ C + Q'.invSucc precision :=
    hM m (Nat.le_max_right _ _)
  exact Q'.le_trans' _ _ _ hfinite (Q'.le_trans' _ _ _
    (Q'.add_le_add_right _ _ (radialTailPayment w N) hlim)
    (Q'.le_of_eqv (poly_identity_of_normal_eq
      (.add (.add (.var 0) (.var 1)) (.var 2))
      (.add (.add (.var 0) (.var 2)) (.mul (.const 1) (.var 1)))
      (by decide) (fun | 0 => C | 1 => Q'.invSucc precision | _ => radialTailPayment w N))))

end YMGap.Continuum.JacobiProductRadialLimit

#print axioms YMGap.Continuum.JacobiProductRadialLimit.radialSummand_geo_bounds
#print axioms YMGap.Continuum.JacobiProductRadialLimit.radialTailPrefactor
#print axioms YMGap.Continuum.JacobiProductRadialLimit.radialTolerance
#print axioms YMGap.Continuum.JacobiProductRadialLimit.radialCutoff
#print axioms YMGap.Continuum.JacobiProductRadialLimit.radialTolerance_pos
#print axioms YMGap.Continuum.JacobiProductRadialLimit.radialCutoff_tail_le
#print axioms YMGap.Continuum.JacobiProductRadialLimit.productRadialCostCReal
#print axioms YMGap.Continuum.JacobiProductRadialLimit.productRadialCostCReal_approx
#print axioms YMGap.Continuum.JacobiProductRadialLimit.radialCutoff_cauchy
#print axioms YMGap.Continuum.JacobiProductRadialLimit.productRadialCost_le_limit_ceiling
