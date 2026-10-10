/-
Type-level inner regularity for the ACTUAL pointwise CReal product. The only
anchors are values at the two supplied rate(1) stages. No cutoff is extracted
from a Prop-level Cauchy witness and no global input bound is assumed.
-/

import YMGap.Constructive.CRealInnerRegularity
import YMGap.Constructive.CRealMul

namespace YMGap.Constructive.CReal.InnerRegularity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal

/-- Computable post-rate(1) absolute anchor for a supplied real presentation. -/
def productAnchor {x : CReal} (X : InnerRegularity x) : Q' :=
  Q'.abs (x.approx (X.rate 1)) + 1

theorem productAnchor_nonnegative {x : CReal} (X : InnerRegularity x) :
    (0 : Q') ≤ productAnchor X :=
  Q'.le_trans' _ _ _ (Q'.abs_nonneg _)
    (Q'.add_le_self_of_nonneg _ 1 (by decide))

/-- Every approximation past the SUPPLIED anchor stage lies in its two-sided
interval, even when arbitrarily early approximations are unbounded. -/
theorem productAnchor_bounds {x : CReal} (X : InnerRegularity x)
    (n : Nat) (hn : X.rate 1 ≤ n) :
    -productAnchor X ≤ x.approx n ∧ x.approx n ≤ productAnchor X := by
  let N := X.rate 1
  obtain ⟨hub, hlb⟩ := X.regular 1 (by decide) n N hn (Nat.le_refl N)
  have hv : -(Q'.abs (x.approx N)) ≤ x.approx N :=
    Q'.le_trans' _ _ _
      (Q'.neg_le_neg (Q'.neg_le_abs (x.approx N)))
      (Q'.le_of_eqv (Q'.neg_neg_eqv (x.approx N)))
  have h1 : -(Q'.abs (x.approx N)) ≤ x.approx n + 1 :=
    Q'.le_trans' _ _ _ hv hlb
  have h2 : -(Q'.abs (x.approx N)) + -1 ≤ (x.approx n + 1) + -1 :=
    Q'.add_le_add_right _ _ _ h1
  have hcancel : ((x.approx n + 1) + -1).eqv (x.approx n) := by
    have e1 := Q'.add_assoc_eqv (x.approx n) 1 (-1)
    have e2 : (x.approx n + (1 + -1)).eqv (x.approx n + 0) :=
      Q'.add_eqv_congr_left (x.approx n) (1 + -1) 0
        (Q'.add_neg_self_eqv 1)
    rw [Q'.add_zero' (x.approx n)] at e2
    exact Q'.eqv_trans _ _ _ e1 e2
  refine ⟨?_, ?_⟩
  · exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.neg_add_eqv (Q'.abs (x.approx N)) 1))
      (Q'.le_trans' _ _ _ h2 (Q'.le_of_eqv hcancel))
  · exact Q'.le_trans' _ _ _ hub
      (Q'.add_le_add_right _ _ _ (Q'.le_abs_self _))

/-- Recoverable product cutoff. Its epsilon-specific tolerance depends only on
the two computable anchors; the two input rates remain Type-level data. -/
def productRate {x y : CReal} (X : InnerRegularity x) (Y : InnerRegularity y)
    (epsilon : Q') : Nat :=
  let A := productAnchor X
  let B := productAnchor Y
  let delta := scaleTolerance (A+B) epsilon
  max (max (X.rate 1) (Y.rate 1)) (max (X.rate delta) (Y.rate delta))

private theorem product_step (ap aq bp bq A B delta epsilon : Q')
    (hA : (0 : Q') ≤ A) (hB : (0 : Q') ≤ B)
    (hdelta : (0 : Q') ≤ delta)
    (ha : ap ≤ aq+delta ∧ aq ≤ ap+delta)
    (hb : bp ≤ bq+delta ∧ bq ≤ bp+delta)
    (hbp : -B ≤ bp ∧ bp ≤ B)
    (haq : -A ≤ aq ∧ aq ≤ A)
    (hbudget : (A+B)*delta ≤ epsilon) :
    ap*bp ≤ aq*bq+epsilon := by
  have hda1 : ap + -aq ≤ delta := Q'.sub_le_of_le_add ha.1
  have hda2 : -delta ≤ ap + -aq := Q'.neg_le_sub_of_le_add ha.2
  have hdb1 : bp + -bq ≤ delta := Q'.sub_le_of_le_add hb.1
  have hdb2 : -delta ≤ bp + -bq := Q'.neg_le_sub_of_le_add hb.2
  have termA : (ap + -aq)*bp ≤ delta*B :=
    Q'.mul_le_of_bounds hdelta hB hda2 hda1 hbp.1 hbp.2
  have idA : (ap*bp).eqv (aq*bp+(ap + -aq)*bp) := by
    have e1 := Q'.add_sub_cancel_eqv ap aq
    have e2 : (ap*bp).eqv ((aq+(ap + -aq))*bp) :=
      Q'.mul_eqv_congr_right ap (aq+(ap + -aq)) bp e1
    exact Q'.eqv_trans _ _ _ e2 (Q'.add_mul_eqv aq (ap + -aq) bp)
  have stepA : ap*bp ≤ aq*bp+delta*B :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv idA)
      (Q'.add_le_add_left _ _ _ termA)
  have termB : (bp + -bq)*aq ≤ delta*A :=
    Q'.mul_le_of_bounds hdelta hA hdb2 hdb1 haq.1 haq.2
  have idB : (aq*bp).eqv (aq*bq+(bp + -bq)*aq) := by
    have e1 := Q'.add_sub_cancel_eqv bp bq
    have e2 : (aq*bp).eqv (aq*(bq+(bp + -bq))) :=
      Q'.mul_eqv_congr_left aq bp (bq+(bp + -bq)) e1
    have e3 := Q'.mul_add_eqv aq bq (bp + -bq)
    have e4 := Q'.mul_comm_eqv aq (bp + -bq)
    exact Q'.eqv_trans _ _ _ e2
      (Q'.eqv_trans _ _ _ e3
        (Q'.add_eqv_congr_left (aq*bq) _ _ e4))
  have stepB : aq*bp ≤ aq*bq+delta*A :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv idB)
      (Q'.add_le_add_left _ _ _ termB)
  have hsum : delta*B+delta*A ≤ epsilon := by
    have e : (delta*A+delta*B).eqv ((A+B)*delta) :=
      Q'.eqv_trans _ _ _
        (Q'.eqv_symm (Q'.mul_add_eqv delta A B))
        (Q'.mul_comm_eqv delta (A+B))
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.eqv_trans _ _ _
        (Q'.add_comm_eqv (delta*B) (delta*A)) e)) hbudget
  have chain : ap*bp ≤ (aq*bq+delta*A)+delta*B :=
    Q'.le_trans' _ _ _ stepA (Q'.add_le_add_right _ _ _ stepB)
  have hreassoc : ((aq*bq+delta*A)+delta*B).eqv
      (aq*bq+(delta*B+delta*A)) :=
    Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv (aq*bq) (delta*A) (delta*B))
      (Q'.add_eqv_congr_left (aq*bq) _ _
        (Q'.add_comm_eqv (delta*A) (delta*B)))
  exact Q'.le_trans' _ _ _
    (Q'.le_trans' _ _ _ chain (Q'.le_of_eqv hreassoc))
    (Q'.add_le_add_left _ _ _ hsum)

/-- The actual pointwise product has a computable Type-level inner rate.
Signed or zero inputs are covered by the absolute anchors. -/
def mul {x y : CReal} (X : InnerRegularity x)
    (Y : InnerRegularity y) : InnerRegularity (CReal.mul x y) where
  rate := productRate X Y
  regular := by
    intro epsilon hepsilon p q hp hq
    let A := productAnchor X
    let B := productAnchor Y
    let delta := scaleTolerance (A+B) epsilon
    have hA : (0 : Q') ≤ A := productAnchor_nonnegative X
    have hB : (0 : Q') ≤ B := productAnchor_nonnegative Y
    have hsum : (0 : Q') ≤ A+B := Q'.zero_le_add A B hA hB
    have hdelta : (0 : Q') < delta :=
      scaleTolerance_pos (A+B) epsilon hepsilon
    have hbudget : (A+B)*delta ≤ epsilon :=
      mul_scaleTolerance_le (A+B) epsilon hsum hepsilon
    have hpa : X.rate 1 ≤ p :=
      Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) hp
    have hpb : Y.rate 1 ≤ p :=
      Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) hp
    have hqa : X.rate 1 ≤ q :=
      Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) hq
    have hqb : Y.rate 1 ≤ q :=
      Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) hq
    have hpda : X.rate delta ≤ p :=
      Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hp
    have hpdb : Y.rate delta ≤ p :=
      Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hp
    have hqda : X.rate delta ≤ q :=
      Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hq
    have hqdb : Y.rate delta ≤ q :=
      Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hq
    have hxp := productAnchor_bounds X p hpa
    have hxq := productAnchor_bounds X q hqa
    have hyp := productAnchor_bounds Y p hpb
    have hyq := productAnchor_bounds Y q hqb
    have hx := X.regular delta hdelta p q hpda hqda
    have hy := Y.regular delta hdelta p q hpdb hqdb
    change x.approx p*y.approx p ≤ x.approx q*y.approx q+epsilon ∧
      x.approx q*y.approx q ≤ x.approx p*y.approx p+epsilon
    exact ⟨product_step (x.approx p) (x.approx q) (y.approx p) (y.approx q)
      A B delta epsilon hA hB (Q'.le_of_lt hdelta) hx hy hyp hxq hbudget,
      product_step (x.approx q) (x.approx p) (y.approx q) (y.approx p)
      A B delta epsilon hA hB (Q'.le_of_lt hdelta)
      ⟨hx.2,hx.1⟩ ⟨hy.2,hy.1⟩ hyq hxp hbudget⟩

#print axioms productAnchor
#print axioms productAnchor_nonnegative
#print axioms productAnchor_bounds
#print axioms productRate
#print axioms mul

end YMGap.Constructive.CReal.InnerRegularity
