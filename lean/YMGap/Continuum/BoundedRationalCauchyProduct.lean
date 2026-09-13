/-
# Explicit product moduli for bounded rational Cauchy streams

For a supplied positive common absolute bound B, use delta=epsilon/(2B)
and the maximum of the two supplied delta-cutoffs. The regularized CReal
representative also has an exposed rational-stream modulus.
-/

import YMGap.Continuum.FCLimitContinuity

namespace YMGap.Continuum.BoundedRationalCauchyProduct

set_option autoImplicit false

open YMGap.Constructive

def tolerance (B : Q') (hB : (0 : Q') < B) (epsilon : Q') : Q' :=
  Q'.divPos (HalfPow.half * epsilon) B hB

theorem tolerance_pos (B : Q') (hB : (0 : Q') < B) {epsilon : Q'} (he : (0 : Q') < epsilon) :
    (0 : Q') < tolerance B hB epsilon := Q'.divPos_pos _ _ _ (ExpNeg.half_mul_pos epsilon he)

theorem tolerance_budget (B : Q') (hB : (0 : Q') < B) (epsilon : Q') :
    Q'.eqv (B * tolerance B hB epsilon + B * tolerance B hB epsilon) epsilon := by
  have h : Q'.eqv (B * tolerance B hB epsilon) (HalfPow.half * epsilon) :=
    Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.divPos_mul_eqv _ _ _)
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ h) (Q'.add_eqv_congr_left _ _ _ h))
    (ExpNeg.two_halves epsilon)

theorem product_close (a b c d B delta : Q') (hB : (0 : Q') ≤ B) (hd : (0 : Q') ≤ delta)
    (ha : Q'.abs a ≤ B) (hdb : Q'.abs d ≤ B)
    (hab : a ≤ b + delta ∧ b ≤ a + delta) (hcd : c ≤ d + delta ∧ d ≤ c + delta) :
    a * c ≤ b * d + (B * delta + B * delta) := by
  have low (x : Q') (hx : Q'.abs x ≤ B) : -B ≤ x :=
    Q'.le_trans' _ _ _ (Q'.neg_le_neg hx) (ExpNeg.neg_abs_le x)
  have h1 := Q'.mul_close_of_two_sided a c d B delta hB hd (low a ha)
    (Q'.le_trans' _ _ _ (Q'.le_abs_self a) ha) hcd.1 hcd.2
  have h2 : a * d ≤ b * d + B * delta :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv a d))
      (Q'.le_trans' _ _ _
        (Q'.mul_close_of_two_sided d a b B delta hB hd (low d hdb)
          (Q'.le_trans' _ _ _ (Q'.le_abs_self d) hdb) hab.1 hab.2)
        (Q'.le_of_eqv (Q'.add_eqv_congr_right _ _ _ (Q'.mul_comm_eqv d b))))
  exact Q'.le_trans' _ _ _ h1
    (Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ (B * delta) h2)
      (Q'.le_of_eqv (Q'.add_assoc_eqv _ _ _)))

def productCauchy {r s : Nat → Q'} (cr : CReal.QCauchy r) (cs : CReal.QCauchy s)
    (B : Q') (hB : (0 : Q') < B) (hr : ∀ n, Q'.abs (r n) ≤ B) (hs : ∀ n, Q'.abs (s n) ≤ B) :
    CReal.QCauchy (fun n => r n * s n) where
  M epsilon := max (cr.M (tolerance B hB epsilon)) (cs.M (tolerance B hB epsilon))
  bound := by
    intro epsilon he p q hp hq
    have hd := Q'.le_of_lt (tolerance_pos B hB he)
    have rpq := cr.bound _ (tolerance_pos B hB he) p q
      (Nat.le_trans (Nat.le_max_left _ _) hp) (Nat.le_trans (Nat.le_max_left _ _) hq)
    have spq := cs.bound _ (tolerance_pos B hB he) p q
      (Nat.le_trans (Nat.le_max_right _ _) hp) (Nat.le_trans (Nat.le_max_right _ _) hq)
    have step (i j : Nat) (rij : r i ≤ r j + tolerance B hB epsilon ∧ r j ≤ r i + tolerance B hB epsilon)
        (sij : s i ≤ s j + tolerance B hB epsilon ∧ s j ≤ s i + tolerance B hB epsilon) :
        r i * s i ≤ r j * s j + epsilon :=
      Q'.le_trans' _ _ _ (product_close _ _ _ _ _ _ (Q'.le_of_lt hB) hd (hr i) (hs j) rij sij)
        (Q'.le_of_eqv (Q'.add_eqv_congr_left _ _ _ (tolerance_budget B hB epsilon)))
    exact ⟨step p q rpq spq, step q p rpq.symm spq.symm⟩

/-- The modulus belongs to the actual CReal representative, not just its source stream. -/
def representativeCauchy (r : Nat → Q') (c : CReal.QCauchy r) :
    CReal.QCauchy (CReal.ofQ'CauchySeq r c).approx where
  M epsilon := epsilon.den
  bound := by
    intro epsilon he p q hp hq
    rcases Nat.le_total p q with hpq | hqp
    · exact CReal.QMhat_directed r c epsilon he p q hpq hp
    · exact (CReal.QMhat_directed r c epsilon he q p hqp hq).symm

end YMGap.Continuum.BoundedRationalCauchyProduct

#print axioms YMGap.Continuum.BoundedRationalCauchyProduct.tolerance
#print axioms YMGap.Continuum.BoundedRationalCauchyProduct.tolerance_pos
#print axioms YMGap.Continuum.BoundedRationalCauchyProduct.tolerance_budget
#print axioms YMGap.Continuum.BoundedRationalCauchyProduct.product_close
#print axioms YMGap.Continuum.BoundedRationalCauchyProduct.productCauchy
#print axioms YMGap.Continuum.BoundedRationalCauchyProduct.representativeCauchy
