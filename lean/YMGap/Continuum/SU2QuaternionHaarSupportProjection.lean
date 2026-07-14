/-
# Canonical projection to the eight quaternion coordinates

The raw polynomial carrier permits exponent lists longer than eight.  The
explicit product-Haar functional interprets every genuinely higher variable
as zero.  This file constructs the canonical eight-coordinate projection and
proves that it can be applied to both polynomial factors before a supported
Wilson weight is evaluated.
-/

import YMGap.Continuum.SU2QuaternionWilsonReferenceWeight

namespace YMGap.Continuum.SU2QuaternionHaarSupportProjection

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionPolynomialHaarLinearity
open YMGap.Continuum.SU2QuaternionHaarSphereIdeal
open YMGap.Continuum.SU2QuaternionHaarBihomogeneousPositivity
open YMGap.Continuum.SU2QuaternionHaarRadiusHomogenization
open YMGap.Continuum.SU2QuaternionHaarPolynomialPositivity
open YMGap.Continuum.SU2QuaternionWilsonReferenceWeight

local infix:50 " ≈ " => Q'.eqv

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

/-- Replace an exponent list by its first eight entries, and replace its
coefficient by zero when a genuine higher-coordinate exponent was present. -/
def projectEightTerm (t : RatTerm) : RatTerm :=
  (t.1.take 8, if allZero (t.1.drop 8) then t.2 else 0)

/-- Canonical eight-coordinate representative of a raw polynomial list. -/
def projectEight (p : RatPoly) : RatPoly := p.map projectEightTerm

theorem projectEight_supported (p : RatPoly) : Supported8 (projectEight p) := by
  intro t ht
  unfold projectEight at ht
  rw [List.mem_map] at ht
  obtain ⟨u, _, rfl⟩ := ht
  simp [projectEightTerm]
  omega

private theorem exponentAt_monoMul (a b : List Nat) (i : Nat) :
    exponentAt (monoMul a b) i = exponentAt a i + exponentAt b i := by
  induction a generalizing b i with
  | nil => simp [monoMul, exponentAt]
  | cons x xs ih =>
      cases b with
      | nil => simp [monoMul, exponentAt]
      | cons y ys =>
          cases i with
          | zero => simp [monoMul, exponentAt]
          | succ i =>
              change exponentAt (monoMul xs ys) i =
                exponentAt xs i + exponentAt ys i
              exact ih ys i

private theorem exponentAt_take_of_lt (m : List Nat) : ∀ n i : Nat,
    i < n → exponentAt (m.take n) i = exponentAt m i
  | 0, _, h => by omega
  | _ + 1, 0, _ => by cases m <;> simp [exponentAt]
  | n + 1, i + 1, h => by
      cases m with
      | nil => simp [exponentAt]
      | cons x xs =>
          simp only [List.take_succ_cons]
          change exponentAt (xs.take n) i = exponentAt xs i
          exact exponentAt_take_of_lt xs n i (by omega)

private theorem monoMul_drop (a b : List Nat) : ∀ n : Nat,
    (monoMul a b).drop n = monoMul (a.drop n) (b.drop n)
  | 0 => rfl
  | n + 1 => by
      cases a <;> cases b <;> simp [monoMul, monoMul_drop]
      next tail => cases tail.drop n <;> rfl

private theorem allZero_monoMul (a b : List Nat) :
    allZero (monoMul a b) = (allZero a && allZero b) := by
  induction a generalizing b with
  | nil => simp [monoMul, allZero]
  | cons x xs ih =>
      cases b with
      | nil => simp [monoMul, allZero]
      | cons y ys =>
          simp [monoMul, allZero, ih ys, Nat.add_eq_zero_iff,
            Bool.and_assoc, Bool.and_left_comm]

private theorem allZero_drop_of_length_le (m : List Nat)
    (hm : m.length ≤ 8) : allZero (m.drop 8) = true := by
  rw [List.drop_eq_nil_of_le hm]
  rfl

private theorem triple_tail_valid {w a b : List Nat}
    (hw : w.length ≤ 8)
    (ha : allZero (a.drop 8) = true)
    (hb : allZero (b.drop 8) = true) :
    allZero ((monoMul w (monoMul a b)).drop 8) = true := by
  rw [monoMul_drop, monoMul_drop, allZero_monoMul, allZero_monoMul,
    allZero_drop_of_length_le w hw, ha, hb]
  decide

private theorem projected_triple_tail_valid {w a b : List Nat}
    (hw : w.length ≤ 8) :
    allZero ((monoMul w (monoMul (a.take 8) (b.take 8))).drop 8) = true := by
  apply triple_tail_valid hw
  · rw [List.drop_eq_nil_of_le (List.length_take_le 8 a)]
    rfl
  · rw [List.drop_eq_nil_of_le (List.length_take_le 8 b)]
    rfl

private theorem productHaarMono_triple_project_valid
    {w a b : List Nat} (hw : w.length ≤ 8)
    (ha : allZero (a.drop 8) = true)
    (hb : allZero (b.drop 8) = true) :
    productHaarMono (monoMul w (monoMul a b)) =
      productHaarMono (monoMul w (monoMul (a.take 8) (b.take 8))) := by
  have ht := triple_tail_valid hw ha hb
  have htp := projected_triple_tail_valid (a := a) (b := b) hw
  have h0 : exponentAt (monoMul w (monoMul a b)) 0 =
      exponentAt (monoMul w (monoMul (a.take 8) (b.take 8))) 0 := by
    simp only [exponentAt_monoMul, exponentAt_take_of_lt _ 8 0 (by omega)]
  have h1 : exponentAt (monoMul w (monoMul a b)) 1 =
      exponentAt (monoMul w (monoMul (a.take 8) (b.take 8))) 1 := by
    simp only [exponentAt_monoMul, exponentAt_take_of_lt _ 8 1 (by omega)]
  have h2 : exponentAt (monoMul w (monoMul a b)) 2 =
      exponentAt (monoMul w (monoMul (a.take 8) (b.take 8))) 2 := by
    simp only [exponentAt_monoMul, exponentAt_take_of_lt _ 8 2 (by omega)]
  have h3 : exponentAt (monoMul w (monoMul a b)) 3 =
      exponentAt (monoMul w (monoMul (a.take 8) (b.take 8))) 3 := by
    simp only [exponentAt_monoMul, exponentAt_take_of_lt _ 8 3 (by omega)]
  have h4 : exponentAt (monoMul w (monoMul a b)) 4 =
      exponentAt (monoMul w (monoMul (a.take 8) (b.take 8))) 4 := by
    simp only [exponentAt_monoMul, exponentAt_take_of_lt _ 8 4 (by omega)]
  have h5 : exponentAt (monoMul w (monoMul a b)) 5 =
      exponentAt (monoMul w (monoMul (a.take 8) (b.take 8))) 5 := by
    simp only [exponentAt_monoMul, exponentAt_take_of_lt _ 8 5 (by omega)]
  have h6 : exponentAt (monoMul w (monoMul a b)) 6 =
      exponentAt (monoMul w (monoMul (a.take 8) (b.take 8))) 6 := by
    simp only [exponentAt_monoMul, exponentAt_take_of_lt _ 8 6 (by omega)]
  have h7 : exponentAt (monoMul w (monoMul a b)) 7 =
      exponentAt (monoMul w (monoMul (a.take 8) (b.take 8))) 7 := by
    simp only [exponentAt_monoMul, exponentAt_take_of_lt _ 8 7 (by omega)]
  unfold productHaarMono
  rw [if_pos ht, if_pos htp, h0, h1, h2, h3, h4, h5, h6, h7]

private theorem triple_tail_invalid_left {w a b : List Nat}
    (ha : allZero (a.drop 8) = false) :
    allZero ((monoMul w (monoMul a b)).drop 8) = false := by
  rw [monoMul_drop, monoMul_drop, allZero_monoMul, allZero_monoMul, ha]
  simp

private theorem triple_tail_invalid_right {w a b : List Nat}
    (hb : allZero (b.drop 8) = false) :
    allZero ((monoMul w (monoMul a b)).drop 8) = false := by
  rw [monoMul_drop, monoMul_drop, allZero_monoMul, allZero_monoMul, hb]
  simp

private def projectTripleCell (w a b : RatTerm) : Q' :=
  (w.2 * (a.2 * b.2)) *
    productHaarMono (monoMul w.1 (monoMul a.1 b.1))

private theorem projectTripleCell_zero_left (w a b : RatTerm)
    (ha : a.2 = 0) : projectTripleCell w a b ≈ 0 := by
  unfold projectTripleCell
  rw [ha]
  refine Q'.eqv_trans _ ((w.2 * 0) *
      productHaarMono (monoMul w.1 (monoMul a.1 b.1))) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _
      (Q'.mul_eqv_congr_left _ _ _ (Q'.zero_mul_eqv b.2))
  · refine Q'.eqv_trans _ (0 *
        productHaarMono (monoMul w.1 (monoMul a.1 b.1))) _
      (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_zero_eqv w.2)) ?_
    exact Q'.zero_mul_eqv _

private theorem projectTripleCell_zero_right (w a b : RatTerm)
    (hb : b.2 = 0) : projectTripleCell w a b ≈ 0 := by
  unfold projectTripleCell
  rw [hb]
  refine Q'.eqv_trans _ ((w.2 * 0) *
      productHaarMono (monoMul w.1 (monoMul a.1 b.1))) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _
      (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_zero_eqv a.2))
  · refine Q'.eqv_trans _ (0 *
        productHaarMono (monoMul w.1 (monoMul a.1 b.1))) _
      (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_zero_eqv w.2)) ?_
    exact Q'.zero_mul_eqv _

private theorem projectTripleCell_eq (w a b : RatTerm)
    (hw : w.1.length ≤ 8) :
    projectTripleCell w a b ≈
      projectTripleCell w (projectEightTerm a) (projectEightTerm b) := by
  by_cases ha : allZero (a.1.drop 8) = true
  · by_cases hb : allZero (b.1.drop 8) = true
    · unfold projectTripleCell projectEightTerm
      simp only [ha, hb, if_true]
      rw [productHaarMono_triple_project_valid hw ha hb]
      exact Q'.eqv_refl _
    · have hbf : allZero (b.1.drop 8) = false := by
        cases h : allZero (b.1.drop 8) with
        | false => rfl
        | true => exact (hb h).elim
      have hz := triple_tail_invalid_right (w := w.1) (a := a.1) hbf
      have hl : projectTripleCell w a b ≈ 0 := by
        unfold projectTripleCell productHaarMono
        rw [if_neg (by simp [hz])]
        exact Q'.mul_zero_eqv _
      have hpr : (projectEightTerm b).2 = 0 := by
        simp [projectEightTerm, hbf]
      exact Q'.eqv_trans _ 0 _ hl
        (Q'.eqv_symm (projectTripleCell_zero_right _ _ _ hpr))
  · have haf : allZero (a.1.drop 8) = false := by
      cases h : allZero (a.1.drop 8) with
      | false => rfl
      | true => exact (ha h).elim
    have hz := triple_tail_invalid_left (w := w.1) (b := b.1) haf
    have hl : projectTripleCell w a b ≈ 0 := by
      unfold projectTripleCell productHaarMono
      rw [if_neg (by simp [hz])]
      exact Q'.mul_zero_eqv _
    have hpl : (projectEightTerm a).2 = 0 := by
      simp [projectEightTerm, haf]
    exact Q'.eqv_trans _ 0 _ hl
      (Q'.eqv_symm (projectTripleCell_zero_left _ _ _ hpl))

private def projectTripleLast (w a : RatTerm) : RatPoly → Q'
  | [] => 0
  | b :: q => projectTripleCell w a b + projectTripleLast w a q

private def projectTripleMiddle (w : RatTerm) : RatPoly → RatPoly → Q'
  | [], _ => 0
  | a :: p, q => projectTripleLast w a q + projectTripleMiddle w p q

private def projectTriple : RatPoly → RatPoly → RatPoly → Q'
  | [], _, _ => 0
  | w :: ws, p, q => projectTripleMiddle w p q + projectTriple ws p q

private theorem haarRow_append (w : RatTerm) : ∀ p q : RatPoly,
    haarRow w (p ++ q) ≈ haarRow w p + haarRow w q
  | [], q => Q'.eqv_symm (QPoly.q_zero_add_eqv _)
  | a :: p, q => by
      change _ + haarRow w (p ++ q) ≈ (_ + haarRow w p) + haarRow w q
      refine Q'.eqv_trans _ (_ + (haarRow w p + haarRow w q)) _
        (Q'.add_eqv_congr_left _ _ _ (haarRow_append w p q)) ?_
      exact Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)

private theorem haarBilinear_append_left : ∀ p q r : RatPoly,
    haarBilinear (p ++ q) r ≈ haarBilinear p r + haarBilinear q r
  | [], q, r => Q'.eqv_symm (QPoly.q_zero_add_eqv _)
  | w :: p, q, r => by
      change haarRow w r + haarBilinear (p ++ q) r ≈
        (haarRow w r + haarBilinear p r) + haarBilinear q r
      refine Q'.eqv_trans _
        (haarRow w r + (haarBilinear p r + haarBilinear q r)) _
        (Q'.add_eqv_congr_left _ _ _ (haarBilinear_append_left p q r)) ?_
      exact Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)

private theorem haarRow_single_polyMul (w a : RatTerm) : ∀ q : RatPoly,
    haarRow w (polyMul [a] q) ≈ projectTripleLast w a q
  | [] => Q'.eqv_refl 0
  | b :: q => by
      change projectTripleCell w a b + haarRow w (polyMul [a] q) ≈
        projectTripleCell w a b + projectTripleLast w a q
      exact Q'.add_eqv_congr_left _ _ _ (haarRow_single_polyMul w a q)

private theorem haarRow_polyMul (w : RatTerm) : ∀ p q : RatPoly,
    haarRow w (polyMul p q) ≈ projectTripleMiddle w p q
  | [], _ => Q'.eqv_refl 0
  | a :: p, q => by
      have hmul : polyMul (a :: p) q = polyMul [a] q ++ polyMul p q := by
        simp [polyMul]
      rw [hmul]
      refine Q'.eqv_trans _
        (haarRow w (polyMul [a] q) + haarRow w (polyMul p q)) _
        (haarRow_append w _ _) ?_
      exact QPoly.q_add_congr
        (haarRow_single_polyMul w a q) (haarRow_polyMul w p q)

private theorem haarBilinear_triple : ∀ w p q : RatPoly,
    haarBilinear w (polyMul p q) ≈ projectTriple w p q
  | [], _, _ => Q'.eqv_refl 0
  | u :: w, p, q => QPoly.q_add_congr
      (haarRow_polyMul u p q) (haarBilinear_triple w p q)

private theorem productHaar_eq_triple (w p q : RatPoly) :
    productHaar (polyMul w (polyMul p q)) ≈ projectTriple w p q := by
  exact Q'.eqv_trans _ _ _
    (productHaar_polyMul_eq_bilinear w (polyMul p q))
    (haarBilinear_triple w p q)

private theorem projectTripleLast_project (w a : RatTerm)
    (hw : w.1.length ≤ 8) : ∀ q : RatPoly,
    projectTripleLast w a q ≈
      projectTripleLast w (projectEightTerm a) (projectEight q)
  | [] => Q'.eqv_refl 0
  | b :: q => QPoly.q_add_congr
      (projectTripleCell_eq w a b hw)
      (projectTripleLast_project w a hw q)

private theorem projectTripleMiddle_project (w : RatTerm)
    (hw : w.1.length ≤ 8) : ∀ p q : RatPoly,
    projectTripleMiddle w p q ≈
      projectTripleMiddle w (projectEight p) (projectEight q)
  | [], _ => Q'.eqv_refl 0
  | a :: p, q => QPoly.q_add_congr
      (projectTripleLast_project w a hw q)
      (projectTripleMiddle_project w hw p q)

private theorem projectTriple_project : ∀ w p q : RatPoly,
    Supported8 w → projectTriple w p q ≈
      projectTriple w (projectEight p) (projectEight q)
  | [], _, _, _ => Q'.eqv_refl 0
  | u :: w, p, q, hw =>
      QPoly.q_add_congr
        (projectTripleMiddle_project u (hw u (by simp)) p q)
        (projectTriple_project w p q (by
          intro v hv
          exact hw v (by simp [hv])))

/-- A supported weight cannot see raw variables above index seven: both
polynomial factors may be canonically projected before evaluation. -/
theorem productHaar_weighted_projectEight
    (w p q : RatPoly) (hw : Supported8 w) :
    productHaar (polyMul w (polyMul p q)) ≈
      productHaar (polyMul w (polyMul (projectEight p) (projectEight q))) := by
  exact Q'.eqv_trans _ _ _ (productHaar_eq_triple w p q)
    (Q'.eqv_trans _ _ _ (projectTriple_project w p q hw)
      (Q'.eqv_symm
        (productHaar_eq_triple w (projectEight p) (projectEight q))))

private theorem haarRow_one : ∀ q : RatPoly,
    haarRow ([], 1) q ≈ productHaarLinearSum q
  | [] => Q'.eqv_refl 0
  | b :: q => by
      change ((1 * b.2) * productHaarMono b.1) + haarRow ([], 1) q ≈
        b.2 * productHaarMono b.1 + productHaarLinearSum q
      exact QPoly.q_add_congr
        (Q'.mul_eqv_congr_right _ _ _ (Q'.one_mul_eqv b.2))
        (haarRow_one q)

/-- The explicit product-Haar functional evaluates multiplication by the
constant polynomial one as an identity. -/
theorem productHaar_polyOne_mul (r : RatPoly) :
    productHaar (polyMul polyOne r) ≈ productHaar r := by
  refine Q'.eqv_trans _ (haarBilinear polyOne r) _
    (productHaar_polyMul_eq_bilinear polyOne r) ?_
  change haarRow ([], 1) r + 0 ≈ productHaar r
  refine Q'.eqv_trans _ (haarRow ([], 1) r) _
    (QPoly.q_add_zero_eqv _) ?_
  exact Q'.eqv_trans _ _ _ (haarRow_one r)
    (Q'.eqv_symm (productHaar_eqv_linearSum r))

theorem polyOne_supported : Supported8 polyOne := by
  intro t ht
  simp [polyOne] at ht
  subst t
  decide

private theorem monoMul_length_le_eight {a b : List Nat}
    (ha : a.length ≤ 8) (hb : b.length ≤ 8) :
    (monoMul a b).length ≤ 8 := by
  apply List.drop_eq_nil_iff.mp
  rw [monoMul_drop]
  rw [List.drop_eq_nil_of_le ha, List.drop_eq_nil_of_le hb]
  rfl

private theorem mem_polyMul {p q : RatPoly} {u : RatTerm}
    (hu : u ∈ polyMul p q) :
    ∃ a, a ∈ p ∧ ∃ b, b ∈ q ∧
      u = (monoMul a.1 b.1, a.2 * b.2) := by
  unfold polyMul at hu
  rw [List.mem_flatMap] at hu
  obtain ⟨a, ha, hu⟩ := hu
  rw [List.mem_map] at hu
  obtain ⟨b, hb, rfl⟩ := hu
  exact ⟨a, ha, b, hb, rfl⟩

private theorem supported_polyAdd {p q : RatPoly}
    (hp : Supported8 p) (hq : Supported8 q) :
    Supported8 (polyAdd p q) := by
  intro t ht
  simp only [polyAdd, List.mem_append] at ht
  cases ht with
  | inl ht => exact hp t ht
  | inr ht => exact hq t ht

private theorem supported_polySmul (c : Q') {p : RatPoly}
    (hp : Supported8 p) : Supported8 (polySmul c p) := by
  intro t ht
  unfold polySmul at ht
  rw [List.mem_map] at ht
  obtain ⟨u, hu, rfl⟩ := ht
  exact hp u hu

private theorem supported_polyMul {p q : RatPoly}
    (hp : Supported8 p) (hq : Supported8 q) :
    Supported8 (polyMul p q) := by
  intro u hu
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_polyMul hu
  exact monoMul_length_le_eight (hp a ha) (hq b hb)

private theorem polyVar_supported_of_lt (i : Nat) (hi : i < 8) :
    Supported8 (polyVar i) := by
  intro t ht
  simp [polyVar] at ht
  subst t
  simp [varMono]
  omega

/-- The retained Wilson kernel uses only the eight quaternion coordinates. -/
theorem retainedRelativeWeight_supported :
    Supported8 retainedRelativeWeight := by
  unfold retainedRelativeWeight relativeFundamentalCharacter relativeDot
  apply supported_polyAdd polyOne_supported
  apply supported_polySmul
  apply supported_polySmul
  apply supported_polyAdd
  · exact supported_polyMul
      (polyVar_supported_of_lt 0 (by omega))
      (polyVar_supported_of_lt 4 (by omega))
  · apply supported_polyAdd
    · exact supported_polyMul
        (polyVar_supported_of_lt 1 (by omega))
        (polyVar_supported_of_lt 5 (by omega))
    · apply supported_polyAdd
      · exact supported_polyMul
          (polyVar_supported_of_lt 2 (by omega))
          (polyVar_supported_of_lt 6 (by omega))
      · exact supported_polyMul
          (polyVar_supported_of_lt 3 (by omega))
          (polyVar_supported_of_lt 7 (by omega))

/-- The raw product-Haar square expectation agrees with the square expectation
of the canonical eight-coordinate projection. -/
theorem productHaar_square_projectEight (p : RatPoly) :
    productHaar (polyMul p p) ≈
      productHaar (polyMul (projectEight p) (projectEight p)) := by
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm (productHaar_polyOne_mul (polyMul p p)))
    (Q'.eqv_trans _ _ _
      (productHaar_weighted_projectEight polyOne p p polyOne_supported)
      (productHaar_polyOne_mul
        (polyMul (projectEight p) (projectEight p))))

/-- Constructive all-degree positivity of the explicit product-Haar
functional on the full raw polynomial carrier. -/
theorem productHaar_all_degree_positive : ProductHaarAllDegreePositive := by
  intro p
  have hp := productHaar_square_nonneg
    (projectEight p) (projectEight_supported p)
  exact Q'.le_trans' _ _ _ hp
    (Q'.le_of_eqv (Q'.eqv_symm (productHaar_square_projectEight p)))

/-- Constructive all-degree positivity after multiplication by the exact
retained Wilson reference weight. -/
theorem retained_weighted_all_degree_positive :
    RetainedWeightedAllDegreePositive := by
  intro p
  have hp := retainedRelativeWeight_square_nonneg
    (projectEight p) (projectEight_supported p)
  exact Q'.le_trans' _ _ _ hp
    (Q'.le_of_eqv (Q'.eqv_symm
      (productHaar_weighted_projectEight retainedRelativeWeight p p
        retainedRelativeWeight_supported)))

/-- The canonical normalized product-Haar probability functional, now with
its positivity field discharged rather than assumed. -/
def constructiveProductHaarProbFunctional :
    ObservableMeasure.ProbFunctional quaternionPairAlg :=
  productHaarProbFunctional productHaar_all_degree_positive

/-- The nonconstant retained Wilson reference weight on the concrete carrier,
with both positivity fields discharged. -/
def constructiveRetainedReferenceWeight :
    FiniteVolume.ReferenceWeight quaternionPairAlg :=
  retainedReferenceWeight productHaar_all_degree_positive
    retained_weighted_all_degree_positive

end YMGap.Continuum.SU2QuaternionHaarSupportProjection

#print axioms YMGap.Continuum.SU2QuaternionHaarSupportProjection.productHaar_weighted_projectEight
#print axioms YMGap.Continuum.SU2QuaternionHaarSupportProjection.productHaar_square_projectEight
#print axioms YMGap.Continuum.SU2QuaternionHaarSupportProjection.productHaar_all_degree_positive
#print axioms YMGap.Continuum.SU2QuaternionHaarSupportProjection.retained_weighted_all_degree_positive
#print axioms YMGap.Continuum.SU2QuaternionHaarSupportProjection.constructiveRetainedReferenceWeight
