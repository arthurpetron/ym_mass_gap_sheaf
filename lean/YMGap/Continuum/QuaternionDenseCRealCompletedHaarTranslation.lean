/-
Actual completed-multiplier translation of the ORIGINAL Haar candidate.
A supplied multiplier Cauchy row produces translated dense CReal data with
the same bound/radius and a retained inner rate. Quantitative row stability
compares it to computed rational multipliers, then original rational Haar
invariance pays four vanishing stage errors. Both completed-map arguments
are compared to the SAME rational translate, avoiding a nested diagonal or
chosen quotient representative. The actual Haar class descends in the
multiplier quotient. This is not full continuous Haar/J04, MAIN/scaling,
QFT axioms, a physical gap, or the Clay theorem.
-/

import YMGap.Continuum.QuaternionDenseCRealPointStability
import YMGap.Continuum.QuaternionDenseCRealHaarTranslation
import YMGap.Continuum.QuaternionDenseCRealHaarComparison

namespace YMGap.Continuum.QuaternionDenseCRealCompletedHaarTranslation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.RepTheory.RationalQuaternion
open YMGap.RepTheory.RationalQuaternionSphereNets
open YMGap.RepTheory.RationalQuaternionCauchyGroup
open YMGap.Continuum.QuaternionDenseCRealPointExtension
open YMGap.Continuum.QuaternionDenseCRealPointStability
open YMGap.Continuum.QuaternionDenseCRealHaarApproximation
open YMGap.Continuum.QuaternionDenseCRealHaarComparison
open YMGap.Continuum.QuaternionDenseCRealHaarTranslation

local infix:50 " ≈ " => Q'.eqv

/-- The SAME completed Hamilton product, on supplied rows in either order. -/
def translateRow (right : Bool) (G X : CauchyPoint) : CauchyPoint :=
  if right then multiplication.mapCauchy X G else multiplication.mapCauchy G X

theorem translateRow_seq (right : Bool) (G X : CauchyPoint) (n : Nat) :
    (translateRow right G X).seq n = translatePoint right (G.seq n) (X.seq n) := by
  cases right <;> rfl

private theorem distance_symm {a b : CReal} {eta : Q'}
    (h : leRat (CReal.abs (CReal.add a (CReal.neg b))) eta) :
    leRat (CReal.abs (CReal.add b (CReal.neg a))) eta := by
  intro e he
  obtain ⟨K, hK⟩ := h e he
  refine ⟨K, fun n hn => ?_⟩
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (ExpNeg.abs_sub_comm _ _)) (hK n hn)

private theorem distance_right_congr {a b c : CReal} {eta : Q'}
    (hbc : Equiv b c)
    (h : leRat (CReal.abs (CReal.add a (CReal.neg b))) eta) :
    leRat (CReal.abs (CReal.add a (CReal.neg c))) eta :=
  leRat_of_equiv (abs_equiv_congr (add_congr_right (neg_congr hbc.symm))) h

private theorem distance_triangle {a b c : CReal} {eta theta : Q'}
    (hab : leRat (CReal.abs (CReal.add a (CReal.neg b))) eta)
    (hbc : leRat (CReal.abs (CReal.add b (CReal.neg c))) theta) :
    leRat (CReal.abs (CReal.add a (CReal.neg c))) (eta + theta) := by
  intro e he
  have hh : (0 : Q') < HalfPow.half * e := Q'.mul_pos (by decide) he
  obtain ⟨K, hK⟩ := hab _ hh
  obtain ⟨L, hL⟩ := hbc _ hh
  refine ⟨max K L, fun n hn => ?_⟩
  have hpin : a.approx n + -(c.approx n) ≈
      (a.approx n + -(b.approx n)) + (b.approx n + -(c.approx n)) :=
    poly_identity_of_normal_eq
      (.add (.var 0) (.neg (.var 1)))
      (.add (.add (.var 0) (.neg (.var 2))) (.add (.var 2) (.neg (.var 1))))
      (by decide) (fun | 0 => a.approx n | 1 => c.approx n | _ => b.approx n)
  have hbudget : (eta + HalfPow.half*e) + (theta + HalfPow.half*e) ≈
      (eta + theta) + e := by
    have hr := poly_identity_of_normal_eq
      (.add (.add (.var 0) (.var 2)) (.add (.var 1) (.var 2)))
      (.add (.add (.var 0) (.var 1)) (.add (.var 2) (.var 2)))
      (by decide) (fun | 0 => eta | 1 => theta | _ => HalfPow.half*e)
    exact Q'.eqv_trans _ _ _ hr
      (Q'.add_eqv_congr_left (eta+theta) _ _ (ExpNeg.two_halves e))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (ExpNeg.abs_eqv_congr hpin))
    (Q'.le_trans' _ _ _ (ExpNeg.abs_add_le _ _)
      (Q'.le_trans' _ _ _
        (Q'.add_le_add (hK n (Nat.le_trans (Nat.le_max_left _ _) hn))
          (hL n (Nat.le_trans (Nat.le_max_right _ _) hn)))
        (Q'.le_of_eqv hbudget)))

variable (right : Bool) (G : CauchyPoint)
variable (F : UnitNorm → CReal) (R : ∀ q, InnerRegularity (F q))
variable (rho : Q' → Q')
variable (positive : ∀ e, (0 : Q') < e → (0 : Q') < rho e)
variable (modulus : ∀ e, (0 : Q') < e → ∀ q x,
  distSq q.val x.val ≤ rho e →
    leRat (CReal.abs (CReal.add (F q) (CReal.neg (F x)))) e)

private theorem rationalRow_value (g : UnitNorm) (X : CauchyPoint) :
    Equiv (rowImage F R rho positive modulus
      (translateRow right (chordSeminorm.constant g) X))
      (rowImage (translateInput right g F) (translateInner right g F R)
        rho positive (translate_modulus right g F rho modulus) X) := by
  have h := translateExtension_value right g F R rho positive modulus
    (Quotient.mk chordSeminorm.completionSetoid X)
  cases right <;> exact (Quotient.exact h).symm

/-- The actual translated input: evaluate the extension on the product row,
not on a selected representative of an RC value. -/
def completedInput (q : UnitNorm) : CReal :=
  rowImage F R rho positive modulus (translateRow right G (chordSeminorm.constant q))

/-- The produced input retains the actual product-image inner rate. -/
def completedInner : ∀ q, InnerRegularity (completedInput right G F R rho positive modulus q) :=
  fun q => rowImageInnerRegularity F R rho positive modulus
    (translateRow right G (chordSeminorm.constant q))

/-- Exact chord isometry at every multiplier stage preserves the SAME rho. -/
theorem completed_modulus (e : Q') (he : (0 : Q') < e) (q x : UnitNorm)
    (hd : distSq q.val x.val ≤ rho e) :
    leRat (CReal.abs (CReal.add (completedInput right G F R rho positive modulus q)
      (CReal.neg (completedInput right G F R rho positive modulus x)))) e := by
  apply rowImage_source_distance F R rho positive modulus _ _ e he 0
  intro n _
  rw [translateRow_seq, translateRow_seq]
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (translate_distSq right (G.seq n) q x)) hd

/-- The SAME input bound is derived from stable samples on the product row. -/
theorem completed_bound (M : Q') (bound : ∀ q, leRat (CReal.abs (F q)) M)
    (q : UnitNorm) :
    leRat (CReal.abs (completedInput right G F R rho positive modulus q)) M :=
  rowImage_bound F R rho positive modulus M bound
    (translateRow right G (chordSeminorm.constant q))

include positive in
private theorem multiplier_close (X : CauchyPoint) (eta : Q') (heta : (0 : Q') < eta)
    (n : Nat) (hn : G.modulus (rho eta) ≤ n) :
    distSq ((translateRow right G X).seq n).val
      ((translateRow right (chordSeminorm.constant (rowApproximation G (rho eta))) X).seq n).val
        ≤ rho eta := by
  have hg : chord (G.seq n) (rowApproximation G (rho eta)) ≤ rho eta :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (chord_symm _ _))
      (rowApproximation_bound G _ (positive eta heta) n hn)
  cases right with
  | false =>
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (chord_mul_right _ _ (X.seq n))) hg
  | true =>
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (chord_mul_left (X.seq n) _ _)) hg

/-- Computed rational multipliers approximate the ACTUAL completed input,
uniformly on every dense test point, using only G's supplied modulus. -/
theorem completedInput_rational_distance (eta : Q') (heta : (0 : Q') < eta)
    (q : UnitNorm) :
    leRat (CReal.abs (CReal.add (completedInput right G F R rho positive modulus q)
      (CReal.neg (translateInput right (rowApproximation G (rho eta)) F q)))) eta := by
  let g := rowApproximation G (rho eta)
  have h := rowImage_source_distance F R rho positive modulus
    (translateRow right G (chordSeminorm.constant q))
    (translateRow right (chordSeminorm.constant g) (chordSeminorm.constant q))
    eta heta (G.modulus (rho eta))
    (multiplier_close right G rho positive (chordSeminorm.constant q) eta heta)
  have hp := (rationalRow_value right F R rho positive modulus g
    (chordSeminorm.constant q)).trans
      (rowImage_constant (translateInput right g F) (translateInner right g F R)
        rho positive (translate_modulus right g F rho modulus) q)
  exact distance_right_congr hp h

/-- The ACTUAL produced translated extension is composition with the SAME
completed Hamilton product on EVERY Point, for either completed multiplier
order. Both comparisons use one computed rational translate; no diagonal
limit or completed-map identity is an input. -/
theorem completedExtension_value (x : Point) :
    pointExtension (completedInput right G F R rho positive modulus)
      (completedInner right G F R rho positive modulus) rho positive
      (completed_modulus right G F R rho positive modulus) x =
    pointExtension F R rho positive modulus
      (if right then completedMul x (Quotient.mk chordSeminorm.completionSetoid G)
        else completedMul (Quotient.mk chordSeminorm.completionSetoid G) x) := by
  refine Quotient.inductionOn x (fun X => ?_)
  have hout : Equiv
      (rowImage (completedInput right G F R rho positive modulus)
        (completedInner right G F R rho positive modulus) rho positive
        (completed_modulus right G F R rho positive modulus) X)
      (rowImage F R rho positive modulus (translateRow right G X)) := by
    apply Equiv_of_abs_sub_le_all_pos
    intro e he
    let eta := HalfPow.half * e
    have heta : (0 : Q') < eta := Q'.mul_pos (by decide) he
    let g := rowApproximation G (rho eta)
    have hA := rowImage_input_distance
      (completedInput right G F R rho positive modulus)
      (completedInner right G F R rho positive modulus) rho positive
      (completed_modulus right G F R rho positive modulus)
      (translateInput right g F) (translateInner right g F R) rho positive
      (translate_modulus right g F rho modulus) X eta
      (completedInput_rational_distance right G F R rho positive modulus eta heta)
    have hB := rowImage_source_distance F R rho positive modulus
      (translateRow right G X) (translateRow right (chordSeminorm.constant g) X)
      eta heta (G.modulus (rho eta))
      (multiplier_close right G rho positive X eta heta)
    have hB' := distance_right_congr (rationalRow_value right F R rho positive modulus g X) hB
    exact leRat_mono (distance_triangle hA (distance_symm hB'))
      (Q'.le_of_eqv (ExpNeg.two_halves e))
  cases right <;> exact Quotient.sound hout

variable (M : Q') (bound : ∀ q, leRat (CReal.abs (F q)) M)

/-- ORIGINAL Haar applied to the ACTUAL completed translated data. -/
def completedHaar : CReal :=
  haarApproximationReal (completedInput right G F R rho positive modulus)
    (completedInner right G F R rho positive modulus) M rho positive
    (completed_bound right G F R rho positive modulus M bound)
    (completed_modulus right G F R rho positive modulus)

def completedHaarInnerRegularity :
    InnerRegularity (completedHaar right G F R rho positive modulus M bound) :=
  haarApproximationInnerRegularity (completedInput right G F R rho positive modulus)
    (completedInner right G F R rho positive modulus) M rho positive
    (completed_bound right G F R rho positive modulus M bound)
    (completed_modulus right G F R rho positive modulus)

/-- Four vanishing stage errors are paid by epsilon/8 per error. -/
def completedHaarEqualityRate (epsilon : Q') : Nat :=
  (HalfPow.half * (HalfPow.half * (HalfPow.half * epsilon))).den

private theorem equality_budget (epsilon : Q') (he : (0 : Q') < epsilon)
    (n : Nat) (hn : completedHaarEqualityRate epsilon ≤ n) :
    (Q'.invSucc n + (HalfPow.half*epsilon + Q'.invSucc n)) +
      (Q'.invSucc n + Q'.invSucc n) ≤ epsilon := by
  let half := HalfPow.half * epsilon
  let quarter := HalfPow.half * half
  have hh : (0 : Q') < half := Q'.mul_pos (by decide) he
  have hq : (0 : Q') < quarter := Q'.mul_pos (by decide) hh
  have ht : Q'.invSucc n ≤ HalfPow.half * quarter :=
    Q'.le_trans' _ _ _ (ExpNeg.invSucc_le_of_le hn)
      (HalfPow.invSucc_den_le _ (Q'.mul_pos (by decide) hq))
  have htwo : Q'.invSucc n + Q'.invSucc n ≤ quarter :=
    Q'.le_trans' _ _ _ (Q'.add_le_add ht ht) (Q'.le_of_eqv (ExpNeg.two_halves quarter))
  have hp : (Q'.invSucc n + (half + Q'.invSucc n)) +
      (Q'.invSucc n + Q'.invSucc n) ≈
      half + ((Q'.invSucc n + Q'.invSucc n) + (Q'.invSucc n + Q'.invSucc n)) :=
    poly_identity_of_normal_eq
      (.add (.add (.var 0) (.add (.var 1) (.var 0))) (.add (.var 0) (.var 0)))
      (.add (.var 1) (.add (.add (.var 0) (.var 0)) (.add (.var 0) (.var 0))))
      (by decide) (fun | 0 => Q'.invSucc n | _ => half)
  have hlast : half + (quarter + quarter) ≈ epsilon :=
    Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left half _ _ (ExpNeg.two_halves half))
      (ExpNeg.two_halves epsilon)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hp)
    (Q'.le_trans' _ _ _ (Q'.add_le_add_left _ _ _ (Q'.add_le_add htwo htwo))
      (Q'.le_of_eqv hlast))

/-- Genuine invariance of the ACTUAL original-Haar candidate for a supplied
completed multiplier, with an explicit equality cutoff. The rational
comparison multiplier depends on epsilon; the two compared candidates do not. -/
theorem completedHaar_invariant :
    Equiv (completedHaar right G F R rho positive modulus M bound)
      (haarApproximationReal F R M rho positive bound modulus) := by
  intro epsilon he
  let eta := HalfPow.half * epsilon
  have heta : (0 : Q') < eta := Q'.mul_pos (by decide) he
  let g := rowApproximation G (rho eta)
  refine ⟨completedHaarEqualityRate epsilon, fun n hn => ?_⟩
  have hc := haarComparison_stage
    (completedInput right G F R rho positive modulus)
    (completedInner right G F R rho positive modulus) M rho positive
    (completed_bound right G F R rho positive modulus M bound)
    (completed_modulus right G F R rho positive modulus)
    (translateInput right g F) (translateInner right g F R) M rho positive
    (translate_bound right g F M bound) (translate_modulus right g F rho modulus)
    eta (completedInput_rational_distance right G F R rho positive modulus eta heta) n n
  have hr := translateHaar_stage right g F R M rho positive bound modulus n
  let a := (completedHaar right G F R rho positive modulus M bound).approx n
  let b := (translateHaar right g F R M rho positive bound modulus).approx n
  let c := (haarApproximationReal F R M rho positive bound modulus).approx n
  have hp : a + -c ≈ (a + -b) + (b + -c) :=
    poly_identity_of_normal_eq
      (.add (.var 0) (.neg (.var 1)))
      (.add (.add (.var 0) (.neg (.var 2))) (.add (.var 2) (.neg (.var 1))))
      (by decide) (fun | 0 => a | 1 => c | _ => b)
  have hb : Q'.abs (a + -c) ≤ epsilon :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (ExpNeg.abs_eqv_congr hp))
      (Q'.le_trans' _ _ _ (ExpNeg.abs_add_le _ _)
        (Q'.le_trans' _ _ _ (Q'.add_le_add hc hr) (equality_budget epsilon he n hn)))
  exact ⟨ExpNeg.le_add_of_abs_sub_le hb,
    ExpNeg.le_add_of_abs_sub_le (Q'.le_trans' _ _ _
      (Q'.le_of_eqv (ExpNeg.abs_sub_comm _ _)) hb)⟩

/-- Representative independence follows from the constructed invariant law;
no source-row equality or chosen completed representative is imposed. -/
def completedHaarClass : Point → RC :=
  Quotient.lift
    (fun X => Quotient.mk crealSetoid (completedHaar right X F R rho positive modulus M bound))
    (fun X Y _ => Quotient.sound
      ((completedHaar_invariant right X F R rho positive modulus M bound).trans
        (completedHaar_invariant right Y F R rho positive modulus M bound).symm))

/-- Every completed multiplier has the SAME original Haar value. The map
being compared is the quotient descent of the actual produced candidates. -/
theorem completedHaarClass_invariant (g : Point) :
    completedHaarClass right F R rho positive modulus M bound g =
      Quotient.mk crealSetoid (haarApproximationReal F R M rho positive bound modulus) := by
  refine Quotient.inductionOn g (fun G => ?_)
  exact Quotient.sound (completedHaar_invariant right G F R rho positive modulus M bound)

#print axioms translateRow
#print axioms translateRow_seq
#print axioms completedInput
#print axioms completedInner
#print axioms completed_modulus
#print axioms completed_bound
#print axioms completedInput_rational_distance
#print axioms completedExtension_value
#print axioms completedHaar
#print axioms completedHaarInnerRegularity
#print axioms completedHaarEqualityRate
#print axioms completedHaar_invariant
#print axioms completedHaarClass
#print axioms completedHaarClass_invariant

end YMGap.Continuum.QuaternionDenseCRealCompletedHaarTranslation
