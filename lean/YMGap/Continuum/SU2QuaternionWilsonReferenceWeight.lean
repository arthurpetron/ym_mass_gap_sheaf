/-
# Wilson-weighted product-Haar reference functional

The retained kernel `1 + (1/4) chi_1(g h⁻¹)` is represented on
`S³ × S³` as a finite sum of polynomial squares.  This file transports the
all-degree product-Haar square theorem through that exact sum-of-squares
identity and packages the resulting nontrivial reference weight.
-/

import YMGap.Continuum.SU2QuaternionHaarPolynomialPositivity

namespace YMGap.Continuum.SU2QuaternionWilsonReferenceWeight

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2PeterWeylWilsonBlock
open YMGap.Continuum.SU2QuaternionPolynomialHaarLinearity
open YMGap.Continuum.SU2QuaternionHaarSphereIdeal
open YMGap.Continuum.SU2QuaternionHaarBihomogeneousPositivity
open YMGap.Continuum.SU2QuaternionHaarRadiusHomogenization
open YMGap.Continuum.SU2QuaternionHaarPolynomialPositivity

local infix:50 " ≈ " => Q'.eqv

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

private theorem productHaar_polyMul_add_left (p q r : RatPoly) :
    productHaar (polyMul (polyAdd p q) r) ≈
      productHaar (polyMul p r) + productHaar (polyMul q r) := by
  have hmul : polyMul (polyAdd p q) r =
      polyAdd (polyMul p r) (polyMul q r) := by
    simp [polyAdd, polyMul]
  rw [hmul]
  exact productHaar_add _ _

private theorem productHaar_polyMul_add_right (p q r : RatPoly) :
    productHaar (polyMul p (polyAdd q r)) ≈
      productHaar (polyMul p q) + productHaar (polyMul p r) := by
  refine Q'.eqv_trans _ (productHaar (polyMul (polyAdd q r) p)) _
    (productHaar_polyMul_comm p (polyAdd q r)) ?_
  refine Q'.eqv_trans _
    (productHaar (polyMul q p) + productHaar (polyMul r p)) _
    (productHaar_polyMul_add_left q r p) ?_
  exact QPoly.q_add_congr
    (productHaar_polyMul_comm q p) (productHaar_polyMul_comm r p)

/-- The four-factor Haar form, with the pairing chosen to expose squares. -/
def haarFour (p q r s : RatPoly) : Q' :=
  productHaar (polyMul (polyMul p q) (polyMul r s))

private theorem monoMul_four_swap (a b c d : List Nat) :
    monoMul (monoMul a b) (monoMul c d) =
      monoMul (monoMul a c) (monoMul b d) := by
  calc
    monoMul (monoMul a b) (monoMul c d) =
        monoMul a (monoMul b (monoMul c d)) := monoMul_assoc a b (monoMul c d)
    _ = monoMul a (monoMul (monoMul b c) d) := by
      rw [monoMul_assoc b c d]
    _ = monoMul a (monoMul (monoMul c b) d) := by
      rw [monoMul_comm b c]
    _ = monoMul a (monoMul c (monoMul b d)) := by
      rw [monoMul_assoc c b d]
    _ = monoMul (monoMul a c) (monoMul b d) := by
      rw [monoMul_assoc a c (monoMul b d)]

private def termMul (a b : RatTerm) : RatTerm :=
  (monoMul a.1 b.1, a.2 * b.2)

private def haarQuadCell (a b c d : RatTerm) : Q' :=
  ((a.2 * b.2) * (c.2 * d.2)) *
    productHaarMono (monoMul (monoMul a.1 b.1) (monoMul c.1 d.1))

private def haarQuadLast (a b c : RatTerm) : RatPoly → Q'
  | [] => 0
  | d :: s => haarQuadCell a b c d + haarQuadLast a b c s

private def haarQuadThird (a b : RatTerm) : RatPoly → RatPoly → Q'
  | [], _ => 0
  | c :: r, s => haarQuadLast a b c s + haarQuadThird a b r s

private def haarQuadSecond (a : RatTerm) : RatPoly → RatPoly → RatPoly → Q'
  | [], _, _ => 0
  | b :: q, r, s => haarQuadThird a b r s + haarQuadSecond a q r s

private def haarQuad : RatPoly → RatPoly → RatPoly → RatPoly → Q'
  | [], _, _, _ => 0
  | a :: p, q, r, s => haarQuadSecond a q r s + haarQuad p q r s

private theorem haarRow_append (a : RatTerm) : ∀ q r : RatPoly,
    haarRow a (q ++ r) ≈ haarRow a q + haarRow a r
  | [], r => Q'.eqv_symm (QPoly.q_zero_add_eqv _)
  | b :: q, r => by
      change _ + haarRow a (q ++ r) ≈ (_ + haarRow a q) + haarRow a r
      refine Q'.eqv_trans _ (_ + (haarRow a q + haarRow a r)) _
        (Q'.add_eqv_congr_left _ _ _ (haarRow_append a q r)) ?_
      exact Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)

private theorem haarBilinear_append_left : ∀ p q r : RatPoly,
    haarBilinear (p ++ q) r ≈ haarBilinear p r + haarBilinear q r
  | [], q, r => Q'.eqv_symm (QPoly.q_zero_add_eqv _)
  | a :: p, q, r => by
      change haarRow a r + haarBilinear (p ++ q) r ≈
        (haarRow a r + haarBilinear p r) + haarBilinear q r
      refine Q'.eqv_trans _
        (haarRow a r + (haarBilinear p r + haarBilinear q r)) _
        (Q'.add_eqv_congr_left _ _ _ (haarBilinear_append_left p q r)) ?_
      exact Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)

private theorem haarRow_single_polyMul (a b c : RatTerm) : ∀ s : RatPoly,
    haarRow (termMul a b) (polyMul [c] s) ≈ haarQuadLast a b c s
  | [] => Q'.eqv_refl 0
  | d :: s => by
      change haarQuadCell a b c d + haarRow (termMul a b) (polyMul [c] s) ≈
        haarQuadCell a b c d + haarQuadLast a b c s
      exact Q'.add_eqv_congr_left _ _ _ (haarRow_single_polyMul a b c s)

private theorem haarRow_polyMul (a b : RatTerm) : ∀ r s : RatPoly,
    haarRow (termMul a b) (polyMul r s) ≈ haarQuadThird a b r s
  | [], _ => Q'.eqv_refl 0
  | c :: r, s => by
      have hmul : polyMul (c :: r) s = polyMul [c] s ++ polyMul r s := by
        simp [polyMul]
      rw [hmul]
      refine Q'.eqv_trans _
        (haarRow (termMul a b) (polyMul [c] s) +
          haarRow (termMul a b) (polyMul r s)) _
        (haarRow_append _ _ _) ?_
      exact QPoly.q_add_congr
        (haarRow_single_polyMul a b c s) (haarRow_polyMul a b r s)

private theorem haarBilinear_single_polyMul (a : RatTerm) : ∀ q r s : RatPoly,
    haarBilinear (polyMul [a] q) (polyMul r s) ≈ haarQuadSecond a q r s
  | [], _, _ => Q'.eqv_refl 0
  | b :: q, r, s => by
      change haarRow (termMul a b) (polyMul r s) +
          haarBilinear (polyMul [a] q) (polyMul r s) ≈
        haarQuadThird a b r s + haarQuadSecond a q r s
      exact QPoly.q_add_congr
        (haarRow_polyMul a b r s) (haarBilinear_single_polyMul a q r s)

private theorem haarBilinear_polyMul_both : ∀ p q r s : RatPoly,
    haarBilinear (polyMul p q) (polyMul r s) ≈ haarQuad p q r s
  | [], _, _, _ => Q'.eqv_refl 0
  | a :: p, q, r, s => by
      have hmul : polyMul (a :: p) q = polyMul [a] q ++ polyMul p q := by
        simp [polyMul]
      rw [hmul]
      refine Q'.eqv_trans _
        (haarBilinear (polyMul [a] q) (polyMul r s) +
          haarBilinear (polyMul p q) (polyMul r s)) _
        (haarBilinear_append_left _ _ _) ?_
      exact QPoly.q_add_congr
        (haarBilinear_single_polyMul a q r s)
        (haarBilinear_polyMul_both p q r s)

private theorem haarFour_eq_quad (p q r s : RatPoly) :
    haarFour p q r s ≈ haarQuad p q r s := by
  unfold haarFour
  exact Q'.eqv_trans _ _ _
    (productHaar_polyMul_eq_bilinear (polyMul p q) (polyMul r s))
    (haarBilinear_polyMul_both p q r s)

private theorem haarQuadCell_swap (a b c d : RatTerm) :
    haarQuadCell a b c d ≈ haarQuadCell a c b d := by
  unfold haarQuadCell
  rw [monoMul_four_swap a.1 b.1 c.1 d.1]
  exact Q'.mul_eqv_congr_right _ _ _ (q_mul4_swap a.2 b.2 c.2 d.2)

private theorem haarQuadLast_swap (a b c : RatTerm) : ∀ s : RatPoly,
    haarQuadLast a b c s ≈ haarQuadLast a c b s
  | [] => Q'.eqv_refl 0
  | d :: s => QPoly.q_add_congr
      (haarQuadCell_swap a b c d) (haarQuadLast_swap a b c s)

private theorem haarQuadThird_single (a b c : RatTerm) (s : RatPoly) :
    haarQuadThird a b [c] s ≈ haarQuadLast a b c s := by
  change haarQuadLast a b c s + 0 ≈ haarQuadLast a b c s
  exact QPoly.q_add_zero_eqv _

private theorem haarQuadThird_append (a b : RatTerm) : ∀ r t s : RatPoly,
    haarQuadThird a b (r ++ t) s ≈
      haarQuadThird a b r s + haarQuadThird a b t s
  | [], t, s => Q'.eqv_symm (QPoly.q_zero_add_eqv _)
  | c :: r, t, s => by
      change haarQuadLast a b c s + haarQuadThird a b (r ++ t) s ≈
        (haarQuadLast a b c s + haarQuadThird a b r s) +
          haarQuadThird a b t s
      refine Q'.eqv_trans _
        (haarQuadLast a b c s +
          (haarQuadThird a b r s + haarQuadThird a b t s)) _
        (Q'.add_eqv_congr_left _ _ _ (haarQuadThird_append a b r t s)) ?_
      exact Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)

private theorem q_add4_swap (a b c d : Q') :
    (a + b) + (c + d) ≈ (a + c) + (b + d) := by
  refine Q'.eqv_trans _ (a + (b + (c + d))) _
    (Q'.add_assoc_eqv a b (c + d)) ?_
  refine Q'.eqv_trans _ (a + ((b + c) + d)) _
    (Q'.add_eqv_congr_left _ _ _
      (Q'.eqv_symm (Q'.add_assoc_eqv b c d))) ?_
  refine Q'.eqv_trans _ (a + ((c + b) + d)) _
    (Q'.add_eqv_congr_left _ _ _
      (Q'.add_eqv_congr_right _ _ _ (Q'.add_comm_eqv b c))) ?_
  refine Q'.eqv_trans _ (a + (c + (b + d))) _
    (Q'.add_eqv_congr_left _ _ _ (Q'.add_assoc_eqv c b d)) ?_
  exact Q'.eqv_symm (Q'.add_assoc_eqv a c (b + d))

private theorem haarQuadSecond_third_append (a : RatTerm) : ∀ q r t s : RatPoly,
    haarQuadSecond a q (r ++ t) s ≈
      haarQuadSecond a q r s + haarQuadSecond a q t s
  | [], _, _, _ => Q'.eqv_symm (QPoly.q_zero_add_eqv _)
  | b :: q, r, t, s => by
      refine Q'.eqv_trans _
        ((haarQuadThird a b r s + haarQuadThird a b t s) +
          (haarQuadSecond a q r s + haarQuadSecond a q t s)) _
        (QPoly.q_add_congr (haarQuadThird_append a b r t s)
          (haarQuadSecond_third_append a q r t s)) ?_
      exact q_add4_swap
        (haarQuadThird a b r s) (haarQuadThird a b t s)
        (haarQuadSecond a q r s) (haarQuadSecond a q t s)

private theorem haarQuadThird_swap_to_second
    (a b : RatTerm) : ∀ r s : RatPoly,
    haarQuadThird a b r s ≈ haarQuadSecond a r [b] s
  | [], _ => Q'.eqv_refl 0
  | c :: r, s => by
      refine Q'.eqv_trans _
        (haarQuadLast a c b s + haarQuadSecond a r [b] s) _
        (QPoly.q_add_congr (haarQuadLast_swap a b c s)
          (haarQuadThird_swap_to_second a b r s)) ?_
      exact Q'.eqv_symm
        (QPoly.q_add_congr (haarQuadThird_single a c b s) (Q'.eqv_refl _))

private theorem haarQuadSecond_third_nil (a : RatTerm) : ∀ r s : RatPoly,
    haarQuadSecond a r [] s ≈ 0
  | [], _ => Q'.eqv_refl 0
  | b :: r, s => by
      change 0 + haarQuadSecond a r [] s ≈ 0
      refine Q'.eqv_trans _ (haarQuadSecond a r [] s) _
        (QPoly.q_zero_add_eqv _) ?_
      exact haarQuadSecond_third_nil a r s

private theorem haarQuadSecond_swap (a : RatTerm) : ∀ q r s : RatPoly,
    haarQuadSecond a q r s ≈ haarQuadSecond a r q s
  | [], r, s => Q'.eqv_symm (haarQuadSecond_third_nil a r s)
  | b :: q, r, s => by
      refine Q'.eqv_trans _
        (haarQuadSecond a r [b] s + haarQuadSecond a r q s) _
        (QPoly.q_add_congr (haarQuadThird_swap_to_second a b r s)
          (haarQuadSecond_swap a q r s)) ?_
      exact Q'.eqv_symm
        (haarQuadSecond_third_append a r [b] q s)

private theorem haarQuad_swap : ∀ p q r s : RatPoly,
    haarQuad p q r s ≈ haarQuad p r q s
  | [], _, _, _ => Q'.eqv_refl 0
  | a :: p, q, r, s => QPoly.q_add_congr
      (haarQuadSecond_swap a q r s) (haarQuad_swap p q r s)

/-- Four-factor permutation under the exact Haar functional. -/
theorem productHaar_polyMul_four_swap (p q r s : RatPoly) :
    haarFour p q r s ≈ haarFour p r q s := by
  exact Q'.eqv_trans _ _ _ (haarFour_eq_quad p q r s)
    (Q'.eqv_trans _ _ _ (haarQuad_swap p q r s)
      (Q'.eqv_symm (haarFour_eq_quad p r q s)))

private theorem scaled_haarRow (c : Q') (a : RatTerm) : ∀ q : RatPoly,
    haarRow (a.1, c * a.2) q ≈ c * haarRow a q
  | [] => Q'.eqv_symm (Q'.mul_zero_eqv c)
  | b :: q => by
      refine Q'.eqv_trans _
        (c * ((a.2 * b.2) * productHaarMono (monoMul a.1 b.1)) +
          c * haarRow a q) _ ?_ ?_
      · exact QPoly.q_add_congr
          (Q'.eqv_trans _
            ((c * a.2) * (b.2 * productHaarMono (monoMul a.1 b.1))) _
            (Q'.mul_assoc_eqv (c * a.2) b.2 _)
            (Q'.eqv_trans _
              (c * (a.2 * (b.2 * productHaarMono (monoMul a.1 b.1)))) _
              (Q'.mul_assoc_eqv c a.2 _)
              (Q'.mul_eqv_congr_left _ _ _
                (Q'.eqv_symm (Q'.mul_assoc_eqv a.2 b.2 _)))))
          (scaled_haarRow c a q)
      · exact Q'.eqv_symm (Q'.mul_add_eqv c _ _)

private theorem scaled_haarBilinear_left (c : Q') : ∀ p q : RatPoly,
    haarBilinear (polySmul c p) q ≈ c * haarBilinear p q
  | [], _ => Q'.eqv_symm (Q'.mul_zero_eqv c)
  | a :: p, q => by
      change haarRow (a.1, c * a.2) q + haarBilinear (polySmul c p) q ≈
        c * (haarRow a q + haarBilinear p q)
      refine Q'.eqv_trans _
        (c * haarRow a q + c * haarBilinear p q) _
        (QPoly.q_add_congr (scaled_haarRow c a q)
          (scaled_haarBilinear_left c p q)) ?_
      exact Q'.eqv_symm (Q'.mul_add_eqv c _ _)

private theorem productHaar_polyMul_smul_left (c : Q') (p q : RatPoly) :
    productHaar (polyMul (polySmul c p) q) ≈
      c * productHaar (polyMul p q) := by
  refine Q'.eqv_trans _ (haarBilinear (polySmul c p) q) _
    (productHaar_polyMul_eq_bilinear _ _) ?_
  refine Q'.eqv_trans _ (c * haarBilinear p q) _
    (scaled_haarBilinear_left c p q) ?_
  exact Q'.mul_eqv_congr_left _ _ _
    (Q'.eqv_symm (productHaar_polyMul_eq_bilinear p q))

private theorem productHaar_polyMul_smul_right (c : Q') (p q : RatPoly) :
    productHaar (polyMul p (polySmul c q)) ≈
      c * productHaar (polyMul p q) := by
  refine Q'.eqv_trans _ (productHaar (polyMul (polySmul c q) p)) _
    (productHaar_polyMul_comm p (polySmul c q)) ?_
  refine Q'.eqv_trans _ (c * productHaar (polyMul q p)) _
    (productHaar_polyMul_smul_left c q p) ?_
  exact Q'.mul_eqv_congr_left _ _ _ (productHaar_polyMul_comm q p)

private theorem monoMul_drop_of_length_le (a b : List Nat) (n : Nat)
    (h : b.length ≤ n) : (monoMul a b).drop n = a.drop n := by
  induction n generalizing a b with
  | zero =>
      cases b with
      | nil => cases a <;> rfl
      | cons _ _ => simp at h
  | succ n ih =>
      cases a with
      | nil =>
          simp only [monoMul]
          exact List.drop_eq_nil_of_le h
      | cons x xs =>
          cases b with
          | nil => simp [monoMul]
          | cons y ys =>
              simp only [List.length_cons] at h
              simp [monoMul, ih xs ys (by omega)]

private theorem monoMul_length_le_eight {a b : List Nat}
    (ha : a.length ≤ 8) (hb : b.length ≤ 8) :
    (monoMul a b).length ≤ 8 := by
  apply List.drop_eq_nil_iff.mp
  rw [monoMul_drop_of_length_le a b 8 hb]
  exact List.drop_eq_nil_of_le ha

private theorem mem_polyMul {p q : RatPoly} {u : RatTerm}
    (hu : u ∈ polyMul p q) :
    ∃ a, a ∈ p ∧ ∃ b, b ∈ q ∧ u = termMul a b := by
  unfold polyMul at hu
  rw [List.mem_flatMap] at hu
  obtain ⟨a, ha, hu⟩ := hu
  rw [List.mem_map] at hu
  obtain ⟨b, hb, rfl⟩ := hu
  exact ⟨a, ha, b, hb, rfl⟩

private theorem Supported8_mul {p q : RatPoly}
    (hp : Supported8 p) (hq : Supported8 q) : Supported8 (polyMul p q) := by
  intro u hu
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_polyMul hu
  exact monoMul_length_le_eight (hp a ha) (hq b hb)

/-- The coordinate `g_i+h_i` whose square enters the retained-kernel SOS. -/
def diagonalCoordinate (i : Nat) : RatPoly :=
  polyAdd (gCoordinate i) (hCoordinate i)

theorem diagonalCoordinate_supported (i : Nat) (hi : i < 4) :
    Supported8 (diagonalCoordinate i) := by
  intro t ht
  simp [diagonalCoordinate, gCoordinate, hCoordinate, polyAdd, polyVar] at ht
  rcases ht with rfl | rfl <;> simp [varMono] <;> omega

/-- The exact polynomial SOS representative
`1/2 + (1/4) Σ_i (g_i+h_i)^2`. -/
def retainedSOSWeight : RatPoly :=
  polyAdd (polySmul half (polyMul polyOne polyOne))
    (polyAdd (polySmul quarter
        (polyMul (diagonalCoordinate 0) (diagonalCoordinate 0)))
      (polyAdd (polySmul quarter
          (polyMul (diagonalCoordinate 1) (diagonalCoordinate 1)))
        (polyAdd (polySmul quarter
            (polyMul (diagonalCoordinate 2) (diagonalCoordinate 2)))
          (polySmul quarter
            (polyMul (diagonalCoordinate 3) (diagonalCoordinate 3))))))

/-- The finite SOS value after multiplying by the input square. -/
def retainedSOSValue (p : RatPoly) : Q' :=
  half * haarFour polyOne polyOne p p +
    (quarter * haarFour (diagonalCoordinate 0) (diagonalCoordinate 0) p p +
      (quarter * haarFour (diagonalCoordinate 1) (diagonalCoordinate 1) p p +
        (quarter * haarFour (diagonalCoordinate 2) (diagonalCoordinate 2) p p +
          quarter * haarFour (diagonalCoordinate 3) (diagonalCoordinate 3) p p)))

theorem retainedSOSWeight_value (p : RatPoly) :
    productHaar (polyMul retainedSOSWeight (polyMul p p)) ≈
      retainedSOSValue p := by
  unfold retainedSOSWeight retainedSOSValue
  refine Q'.eqv_trans _
    (productHaar (polyMul (polySmul half (polyMul polyOne polyOne)) (polyMul p p)) +
      productHaar (polyMul
        (polyAdd (polySmul quarter
            (polyMul (diagonalCoordinate 0) (diagonalCoordinate 0)))
          (polyAdd (polySmul quarter
              (polyMul (diagonalCoordinate 1) (diagonalCoordinate 1)))
            (polyAdd (polySmul quarter
                (polyMul (diagonalCoordinate 2) (diagonalCoordinate 2)))
              (polySmul quarter
                (polyMul (diagonalCoordinate 3) (diagonalCoordinate 3))))))
        (polyMul p p))) _
    (productHaar_polyMul_add_left _ _ _) ?_
  refine QPoly.q_add_congr (productHaar_polyMul_smul_left _ _ _) ?_
  refine Q'.eqv_trans _
    (productHaar (polyMul (polySmul quarter
        (polyMul (diagonalCoordinate 0) (diagonalCoordinate 0))) (polyMul p p)) +
      productHaar (polyMul
        (polyAdd (polySmul quarter
            (polyMul (diagonalCoordinate 1) (diagonalCoordinate 1)))
          (polyAdd (polySmul quarter
              (polyMul (diagonalCoordinate 2) (diagonalCoordinate 2)))
            (polySmul quarter
              (polyMul (diagonalCoordinate 3) (diagonalCoordinate 3)))))
        (polyMul p p))) _
    (productHaar_polyMul_add_left _ _ _) ?_
  refine QPoly.q_add_congr (productHaar_polyMul_smul_left _ _ _) ?_
  refine Q'.eqv_trans _
    (productHaar (polyMul (polySmul quarter
        (polyMul (diagonalCoordinate 1) (diagonalCoordinate 1))) (polyMul p p)) +
      productHaar (polyMul
        (polyAdd (polySmul quarter
            (polyMul (diagonalCoordinate 2) (diagonalCoordinate 2)))
          (polySmul quarter
            (polyMul (diagonalCoordinate 3) (diagonalCoordinate 3))))
        (polyMul p p))) _
    (productHaar_polyMul_add_left _ _ _) ?_
  refine QPoly.q_add_congr (productHaar_polyMul_smul_left _ _ _) ?_
  refine Q'.eqv_trans _
    (productHaar (polyMul (polySmul quarter
        (polyMul (diagonalCoordinate 2) (diagonalCoordinate 2))) (polyMul p p)) +
      productHaar (polyMul (polySmul quarter
        (polyMul (diagonalCoordinate 3) (diagonalCoordinate 3))) (polyMul p p))) _
    (productHaar_polyMul_add_left _ _ _) ?_
  exact QPoly.q_add_congr
    (productHaar_polyMul_smul_left _ _ _)
    (productHaar_polyMul_smul_left _ _ _)

private theorem haarFour_square_nonneg (d p : RatPoly)
    (hd : Supported8 d) (hp : Supported8 p) :
    (0 : Q') ≤ haarFour d d p p := by
  have hsq : (0 : Q') ≤
      productHaar (polyMul (polyMul d p) (polyMul d p)) :=
    productHaar_square_nonneg (polyMul d p) (Supported8_mul hd hp)
  exact Q'.le_trans' _ _ _ hsq
    (Q'.le_of_eqv (Q'.eqv_symm (productHaar_polyMul_four_swap d d p p)))

/-- Positivity of the explicit retained-kernel SOS representative. -/
theorem retainedSOSWeight_square_nonneg (p : RatPoly) (hp : Supported8 p) :
    (0 : Q') ≤ productHaar (polyMul retainedSOSWeight (polyMul p p)) := by
  have h1 := haarFour_square_nonneg polyOne p (by
    intro t ht
    simp [polyOne] at ht
    rcases ht with rfl
    decide) hp
  have h0 := haarFour_square_nonneg (diagonalCoordinate 0) p
    (diagonalCoordinate_supported 0 (by omega)) hp
  have h1d := haarFour_square_nonneg (diagonalCoordinate 1) p
    (diagonalCoordinate_supported 1 (by omega)) hp
  have h2 := haarFour_square_nonneg (diagonalCoordinate 2) p
    (diagonalCoordinate_supported 2 (by omega)) hp
  have h3 := haarFour_square_nonneg (diagonalCoordinate 3) p
    (diagonalCoordinate_supported 3 (by omega)) hp
  have hv : (0 : Q') ≤ retainedSOSValue p :=
    Q'.zero_le_add _ _
      (Q'.mul_nonneg _ _ (by decide) h1)
      (Q'.zero_le_add _ _
        (Q'.mul_nonneg _ _ (by decide) h0)
        (Q'.zero_le_add _ _
          (Q'.mul_nonneg _ _ (by decide) h1d)
          (Q'.zero_le_add _ _
            (Q'.mul_nonneg _ _ (by decide) h2)
            (Q'.mul_nonneg _ _ (by decide) h3))))
  exact Q'.le_trans' _ _ _ hv
    (Q'.le_of_eqv (Q'.eqv_symm (retainedSOSWeight_value p)))

private theorem productHaar_triple_first_comm (p q r : RatPoly) :
    productHaar (polyMul (polyMul p q) r) ≈
      productHaar (polyMul (polyMul q p) r) := by
  refine Q'.eqv_trans _ (productHaar (polyMul p (polyMul q r))) _
    (productHaar_polyMul_assoc p q r) ?_
  refine Q'.eqv_trans _ (productHaar (polyMul p (polyMul r q))) _
    (productHaar_polyMul_middle_comm p q r) ?_
  refine Q'.eqv_trans _ (productHaar (polyMul (polyMul p r) q)) _
    (Q'.eqv_symm (productHaar_polyMul_assoc p r q)) ?_
  refine Q'.eqv_trans _ (productHaar (polyMul q (polyMul p r))) _
    (productHaar_polyMul_comm (polyMul p r) q) ?_
  exact Q'.eqv_symm (productHaar_polyMul_assoc q p r)

private theorem productHaar_expand_inner_add
    (p q s r : RatPoly) :
    productHaar (polyMul p (polyMul (polyAdd q s) r)) ≈
      productHaar (polyMul (polyMul p q) r) +
        productHaar (polyMul (polyMul p s) r) := by
  refine Q'.eqv_trans _
    (productHaar (polyMul p (polyMul r (polyAdd q s))) ) _
    (productHaar_polyMul_middle_comm p (polyAdd q s) r) ?_
  refine Q'.eqv_trans _
    (productHaar (polyMul (polyMul p r) (polyAdd q s))) _
    (Q'.eqv_symm (productHaar_polyMul_assoc p r (polyAdd q s))) ?_
  refine Q'.eqv_trans _
    (productHaar (polyMul (polyMul p r) q) +
      productHaar (polyMul (polyMul p r) s)) _
    (productHaar_polyMul_add_right (polyMul p r) q s) ?_
  exact QPoly.q_add_congr
    (Q'.eqv_trans _ _ _ (productHaar_polyMul_assoc p r q)
      (Q'.eqv_trans _ _ _ (productHaar_polyMul_middle_comm p r q)
        (Q'.eqv_symm (productHaar_polyMul_assoc p q r))))
    (Q'.eqv_trans _ _ _ (productHaar_polyMul_assoc p r s)
      (Q'.eqv_trans _ _ _ (productHaar_polyMul_middle_comm p r s)
        (Q'.eqv_symm (productHaar_polyMul_assoc p s r))))

/-- Bilinear expansion of `(g+h)^2`, valid after multiplying by any further
polynomial. -/
theorem productHaar_diagonal_square_expand (g h r : RatPoly) :
    productHaar
        (polyMul (polyMul (polyAdd g h) (polyAdd g h)) r) ≈
      (productHaar (polyMul (polyMul g g) r) +
        productHaar (polyMul (polyMul g h) r)) +
      (productHaar (polyMul (polyMul h g) r) +
        productHaar (polyMul (polyMul h h) r)) := by
  refine Q'.eqv_trans _
    (productHaar (polyMul (polyAdd g h)
      (polyMul (polyAdd g h) r))) _
    (productHaar_polyMul_assoc (polyAdd g h) (polyAdd g h) r) ?_
  refine Q'.eqv_trans _
    (productHaar (polyMul g (polyMul (polyAdd g h) r)) +
      productHaar (polyMul h (polyMul (polyAdd g h) r))) _
    (productHaar_polyMul_add_left g h _) ?_
  exact QPoly.q_add_congr
    (productHaar_expand_inner_add g g h r)
    (productHaar_expand_inner_add h g h r)

private def qsum4 (a b c d : Q') : Q' := a + (b + (c + d))

private theorem qsum4_congr {a b c d a' b' c' d' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') (hc : c ≈ c') (hd : d ≈ d') :
    qsum4 a b c d ≈ qsum4 a' b' c' d' := by
  unfold qsum4
  exact QPoly.q_add_congr ha (QPoly.q_add_congr hb (QPoly.q_add_congr hc hd))

private theorem qsum3_pair_regroup
    (a b c x y z : Q') :
    (a + x) + ((b + y) + (c + z)) ≈
      (a + (b + c)) + (x + (y + z)) := by
  refine Q'.eqv_trans _ ((a + x) + ((b + c) + (y + z))) _
    (Q'.add_eqv_congr_left _ _ _ (q_add4_swap b y c z)) ?_
  exact q_add4_swap a x (b + c) (y + z)

private theorem qsum4_pair_regroup
    (a b c d x y z w : Q') :
    qsum4 (a + x) (b + y) (c + z) (d + w) ≈
      qsum4 a b c d + qsum4 x y z w := by
  unfold qsum4
  refine Q'.eqv_trans _
    ((a + x) + ((b + (c + d)) + (y + (z + w)))) _
    (Q'.add_eqv_congr_left _ _ _ (qsum3_pair_regroup b c d y z w)) ?_
  exact q_add4_swap a x (b + (c + d)) (y + (z + w))

private theorem qsum4_smul (c a b d e : Q') :
    qsum4 (c * a) (c * b) (c * d) (c * e) ≈
      c * qsum4 a b d e := by
  unfold qsum4
  refine Q'.eqv_trans _
    (c * a + c * (b + (d + e))) _
    (Q'.add_eqv_congr_left _ _ _
      (Q'.eqv_trans _
        (c * b + c * (d + e)) _
        (Q'.add_eqv_congr_left _ _ _ (Q'.eqv_symm (Q'.mul_add_eqv c d e)))
        (Q'.eqv_symm (Q'.mul_add_eqv c b (d + e))))) ?_
  exact Q'.eqv_symm (Q'.mul_add_eqv c a (b + (d + e)))

private def polySum4 (a b c d : RatPoly) : RatPoly :=
  polyAdd a (polyAdd b (polyAdd c d))

private theorem productHaar_polySum4 (a b c d r : RatPoly) :
    productHaar (polyMul (polySum4 a b c d) r) ≈
      qsum4 (productHaar (polyMul a r)) (productHaar (polyMul b r))
        (productHaar (polyMul c r)) (productHaar (polyMul d r)) := by
  unfold polySum4 qsum4
  refine Q'.eqv_trans _
    (productHaar (polyMul a r) +
      productHaar (polyMul (polyAdd b (polyAdd c d)) r)) _
    (productHaar_polyMul_add_left _ _ _) ?_
  refine Q'.add_eqv_congr_left _ _ _ ?_
  refine Q'.eqv_trans _
    (productHaar (polyMul b r) +
      productHaar (polyMul (polyAdd c d) r)) _
    (productHaar_polyMul_add_left _ _ _) ?_
  exact Q'.add_eqv_congr_left _ _ _
    (productHaar_polyMul_add_left c d r)

private def gSquareSum : RatPoly := polySum4
  (polyMul (gCoordinate 0) (gCoordinate 0))
  (polyMul (gCoordinate 1) (gCoordinate 1))
  (polyMul (gCoordinate 2) (gCoordinate 2))
  (polyMul (gCoordinate 3) (gCoordinate 3))

private def hSquareSum : RatPoly := polySum4
  (polyMul (hCoordinate 0) (hCoordinate 0))
  (polyMul (hCoordinate 1) (hCoordinate 1))
  (polyMul (hCoordinate 2) (hCoordinate 2))
  (polyMul (hCoordinate 3) (hCoordinate 3))

private def forwardCrossSum : RatPoly := polySum4
  (polyMul (gCoordinate 0) (hCoordinate 0))
  (polyMul (gCoordinate 1) (hCoordinate 1))
  (polyMul (gCoordinate 2) (hCoordinate 2))
  (polyMul (gCoordinate 3) (hCoordinate 3))

private theorem gSquareSum_eq : gSquareSum = gRadiusPolynomial := by decide
private theorem hSquareSum_eq : hSquareSum = hRadiusPolynomial := by decide
private theorem forwardCrossSum_eq : forwardCrossSum = relativeDot := by decide

private theorem haarRow_one : ∀ q : RatPoly,
    haarRow ([], 1) q ≈ productHaarLinearSum q
  | [] => Q'.eqv_refl 0
  | b :: q => by
      change ((1 * b.2) * productHaarMono b.1) + haarRow ([], 1) q ≈
        b.2 * productHaarMono b.1 + productHaarLinearSum q
      exact QPoly.q_add_congr
        (Q'.mul_eqv_congr_right _ _ _ (Q'.one_mul_eqv b.2))
        (haarRow_one q)

private theorem productHaar_polyOne_mul (r : RatPoly) :
    productHaar (polyMul polyOne r) ≈ productHaar r := by
  refine Q'.eqv_trans _ (haarBilinear polyOne r) _
    (productHaar_polyMul_eq_bilinear polyOne r) ?_
  change haarRow ([], 1) r + 0 ≈ productHaar r
  refine Q'.eqv_trans _ (haarRow ([], 1) r) _
    (QPoly.q_add_zero_eqv _) ?_
  exact Q'.eqv_trans _ _ _ (haarRow_one r)
    (Q'.eqv_symm (productHaar_eqv_linearSum r))

private theorem productHaar_gRadius_left (r : RatPoly) :
    productHaar (polyMul gRadiusPolynomial r) ≈ productHaar r := by
  refine Q'.eqv_trans _ (productHaar (polyMul r gRadiusPolynomial)) _
    (productHaar_polyMul_comm gRadiusPolynomial r) ?_
  exact productHaar_mul_gRadius r

private theorem productHaar_hRadius_left (r : RatPoly) :
    productHaar (polyMul hRadiusPolynomial r) ≈ productHaar r := by
  refine Q'.eqv_trans _ (productHaar (polyMul r hRadiusPolynomial)) _
    (productHaar_polyMul_comm hRadiusPolynomial r) ?_
  exact productHaar_mul_hRadius r

private theorem diagonal_value_expand (i : Nat) (r : RatPoly) :
    productHaar (polyMul
        (polyMul (diagonalCoordinate i) (diagonalCoordinate i)) r) ≈
      (productHaar (polyMul (polyMul (gCoordinate i) (gCoordinate i)) r) +
        productHaar (polyMul (polyMul (hCoordinate i) (hCoordinate i)) r)) +
      (productHaar (polyMul (polyMul (gCoordinate i) (hCoordinate i)) r) +
        productHaar (polyMul (polyMul (gCoordinate i) (hCoordinate i)) r)) := by
  refine Q'.eqv_trans _
    ((productHaar (polyMul (polyMul (gCoordinate i) (gCoordinate i)) r) +
        productHaar (polyMul (polyMul (gCoordinate i) (hCoordinate i)) r)) +
      (productHaar (polyMul (polyMul (hCoordinate i) (gCoordinate i)) r) +
        productHaar (polyMul (polyMul (hCoordinate i) (hCoordinate i)) r))) _
    (productHaar_diagonal_square_expand (gCoordinate i) (hCoordinate i) r) ?_
  refine Q'.eqv_trans _
    ((productHaar (polyMul (polyMul (gCoordinate i) (gCoordinate i)) r) +
        productHaar (polyMul (polyMul (gCoordinate i) (hCoordinate i)) r)) +
      (productHaar (polyMul (polyMul (gCoordinate i) (hCoordinate i)) r) +
        productHaar (polyMul (polyMul (hCoordinate i) (hCoordinate i)) r))) _
    (Q'.add_eqv_congr_left _ _ _
      (Q'.add_eqv_congr_right _ _ _
        (productHaar_triple_first_comm (hCoordinate i) (gCoordinate i) r))) ?_
  refine Q'.eqv_trans _
    ((productHaar (polyMul (polyMul (gCoordinate i) (gCoordinate i)) r) +
        productHaar (polyMul (polyMul (gCoordinate i) (hCoordinate i)) r)) +
      (productHaar (polyMul (polyMul (hCoordinate i) (hCoordinate i)) r) +
        productHaar (polyMul (polyMul (gCoordinate i) (hCoordinate i)) r))) _
    (Q'.add_eqv_congr_left _ _ _ (Q'.add_comm_eqv _ _)) ?_
  refine Q'.eqv_trans _
    ((productHaar (polyMul (polyMul (gCoordinate i) (gCoordinate i)) r) +
        productHaar (polyMul (polyMul (hCoordinate i) (hCoordinate i)) r)) +
      (productHaar (polyMul (polyMul (gCoordinate i) (hCoordinate i)) r) +
        productHaar (polyMul (polyMul (gCoordinate i) (hCoordinate i)) r))) _
    (q_add4_swap _ _ _ _) ?_
  exact Q'.eqv_refl _

private def gSquareValue (i : Nat) (r : RatPoly) : Q' :=
  productHaar (polyMul (polyMul (gCoordinate i) (gCoordinate i)) r)

private def hSquareValue (i : Nat) (r : RatPoly) : Q' :=
  productHaar (polyMul (polyMul (hCoordinate i) (hCoordinate i)) r)

private def crossValue (i : Nat) (r : RatPoly) : Q' :=
  productHaar (polyMul (polyMul (gCoordinate i) (hCoordinate i)) r)

private def diagonalValue (i : Nat) (r : RatPoly) : Q' :=
  productHaar (polyMul
    (polyMul (diagonalCoordinate i) (diagonalCoordinate i)) r)

private theorem diagonalValue_expand (i : Nat) (r : RatPoly) :
    diagonalValue i r ≈
      (gSquareValue i r + hSquareValue i r) +
        (crossValue i r + crossValue i r) :=
  diagonal_value_expand i r

private theorem qsum4_gSquare (r : RatPoly) :
    qsum4 (gSquareValue 0 r) (gSquareValue 1 r)
      (gSquareValue 2 r) (gSquareValue 3 r) ≈
      productHaar (polyMul gRadiusPolynomial r) := by
  refine Q'.eqv_trans _ (productHaar (polyMul gSquareSum r)) _
    (Q'.eqv_symm (productHaar_polySum4 _ _ _ _ r)) ?_
  rw [gSquareSum_eq]
  exact Q'.eqv_refl _

private theorem qsum4_hSquare (r : RatPoly) :
    qsum4 (hSquareValue 0 r) (hSquareValue 1 r)
      (hSquareValue 2 r) (hSquareValue 3 r) ≈
      productHaar (polyMul hRadiusPolynomial r) := by
  refine Q'.eqv_trans _ (productHaar (polyMul hSquareSum r)) _
    (Q'.eqv_symm (productHaar_polySum4 _ _ _ _ r)) ?_
  rw [hSquareSum_eq]
  exact Q'.eqv_refl _

private theorem qsum4_cross (r : RatPoly) :
    qsum4 (crossValue 0 r) (crossValue 1 r)
      (crossValue 2 r) (crossValue 3 r) ≈
      productHaar (polyMul relativeDot r) := by
  refine Q'.eqv_trans _ (productHaar (polyMul forwardCrossSum r)) _
    (Q'.eqv_symm (productHaar_polySum4 _ _ _ _ r)) ?_
  rw [forwardCrossSum_eq]
  exact Q'.eqv_refl _

private theorem two_mul_eqv (x : Q') : (2 : Q') * x ≈ x + x := by
  refine Q'.eqv_trans _ (((1 : Q') + 1) * x) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _ (by decide)
  · refine Q'.eqv_trans _ (1 * x + 1 * x) _ (Q'.add_mul_eqv 1 1 x) ?_
    exact QPoly.q_add_congr (Q'.one_mul_eqv x) (Q'.one_mul_eqv x)

private theorem diagonalSum_value (r : RatPoly) :
    qsum4 (diagonalValue 0 r) (diagonalValue 1 r)
      (diagonalValue 2 r) (diagonalValue 3 r) ≈
      (productHaar (polyMul gRadiusPolynomial r) +
        productHaar (polyMul hRadiusPolynomial r)) +
          productHaar (polyMul relativeFundamentalCharacter r) := by
  refine Q'.eqv_trans _
    (qsum4
      (gSquareValue 0 r + hSquareValue 0 r)
      (gSquareValue 1 r + hSquareValue 1 r)
      (gSquareValue 2 r + hSquareValue 2 r)
      (gSquareValue 3 r + hSquareValue 3 r) +
    qsum4
      (crossValue 0 r + crossValue 0 r)
      (crossValue 1 r + crossValue 1 r)
      (crossValue 2 r + crossValue 2 r)
      (crossValue 3 r + crossValue 3 r)) _ ?_ ?_
  · refine Q'.eqv_trans _
      (qsum4
        ((gSquareValue 0 r + hSquareValue 0 r) +
          (crossValue 0 r + crossValue 0 r))
        ((gSquareValue 1 r + hSquareValue 1 r) +
          (crossValue 1 r + crossValue 1 r))
        ((gSquareValue 2 r + hSquareValue 2 r) +
          (crossValue 2 r + crossValue 2 r))
        ((gSquareValue 3 r + hSquareValue 3 r) +
          (crossValue 3 r + crossValue 3 r))) _
      (qsum4_congr
        (diagonalValue_expand 0 r) (diagonalValue_expand 1 r)
        (diagonalValue_expand 2 r) (diagonalValue_expand 3 r)) ?_
    exact qsum4_pair_regroup _ _ _ _ _ _ _ _
  · refine Q'.eqv_trans _
      ((qsum4 (gSquareValue 0 r) (gSquareValue 1 r)
          (gSquareValue 2 r) (gSquareValue 3 r) +
        qsum4 (hSquareValue 0 r) (hSquareValue 1 r)
          (hSquareValue 2 r) (hSquareValue 3 r)) +
       (qsum4 (crossValue 0 r) (crossValue 1 r)
          (crossValue 2 r) (crossValue 3 r) +
        qsum4 (crossValue 0 r) (crossValue 1 r)
          (crossValue 2 r) (crossValue 3 r))) _
      (QPoly.q_add_congr
        (qsum4_pair_regroup _ _ _ _ _ _ _ _)
        (qsum4_pair_regroup _ _ _ _ _ _ _ _)) ?_
    refine Q'.eqv_trans _
      ((productHaar (polyMul gRadiusPolynomial r) +
          productHaar (polyMul hRadiusPolynomial r)) +
        (productHaar (polyMul relativeDot r) +
          productHaar (polyMul relativeDot r))) _
      (QPoly.q_add_congr
        (QPoly.q_add_congr (qsum4_gSquare r) (qsum4_hSquare r))
        (QPoly.q_add_congr (qsum4_cross r) (qsum4_cross r))) ?_
    exact Q'.add_eqv_congr_left _ _ _
      (Q'.eqv_trans _ _ _ (Q'.eqv_symm (two_mul_eqv _))
        (Q'.eqv_trans _ _ _
          (Q'.eqv_symm
            (productHaar_polyMul_smul_left 2 relativeDot r))
          (Q'.eqv_refl _)))

private theorem half_two_quarters (x : Q') :
    half * x + (quarter * x + quarter * x) ≈ x := by
  refine Q'.eqv_trans _
    (half * x + (quarter + quarter) * x) _
    (Q'.add_eqv_congr_left _ _ _
      (Q'.eqv_symm (Q'.add_mul_eqv quarter quarter x))) ?_
  refine Q'.eqv_trans _ ((half + (quarter + quarter)) * x) _
    (Q'.eqv_symm (Q'.add_mul_eqv half (quarter + quarter) x)) ?_
  refine Q'.eqv_trans _ (1 * x) _
    (Q'.mul_eqv_congr_right _ _ _ (by decide)) ?_
  exact Q'.one_mul_eqv x

private theorem retainedSOSValue_common (p : RatPoly) :
    retainedSOSValue p ≈
      productHaar (polyMul p p) +
        quarter * productHaar
          (polyMul relativeFundamentalCharacter (polyMul p p)) := by
  let r := polyMul p p
  have hone : haarFour polyOne polyOne p p ≈ productHaar r := by
    unfold haarFour
    rw [show polyMul polyOne polyOne = polyOne by decide]
    exact productHaar_polyOne_mul r
  have hdiag :
      qsum4 (diagonalValue 0 r) (diagonalValue 1 r)
        (diagonalValue 2 r) (diagonalValue 3 r) ≈
        (productHaar (polyMul gRadiusPolynomial r) +
          productHaar (polyMul hRadiusPolynomial r)) +
            productHaar (polyMul relativeFundamentalCharacter r) :=
    diagonalSum_value r
  change half * haarFour polyOne polyOne p p +
      qsum4
        (quarter * diagonalValue 0 r) (quarter * diagonalValue 1 r)
        (quarter * diagonalValue 2 r) (quarter * diagonalValue 3 r) ≈
    productHaar r + quarter *
      productHaar (polyMul relativeFundamentalCharacter r)
  refine Q'.eqv_trans _
    (half * productHaar r + quarter *
      qsum4 (diagonalValue 0 r) (diagonalValue 1 r)
        (diagonalValue 2 r) (diagonalValue 3 r)) _ ?_ ?_
  · exact QPoly.q_add_congr
      (Q'.mul_eqv_congr_left _ _ _ hone)
      (qsum4_smul quarter _ _ _ _)
  refine Q'.eqv_trans _
    (half * productHaar r + quarter *
      ((productHaar (polyMul gRadiusPolynomial r) +
        productHaar (polyMul hRadiusPolynomial r)) +
          productHaar (polyMul relativeFundamentalCharacter r))) _
    (Q'.add_eqv_congr_left _ _ _
      (Q'.mul_eqv_congr_left _ _ _ hdiag)) ?_
  refine Q'.eqv_trans _
    (half * productHaar r + quarter *
      ((productHaar r + productHaar r) +
        productHaar (polyMul relativeFundamentalCharacter r))) _
    (Q'.add_eqv_congr_left _ _ _
      (Q'.mul_eqv_congr_left _ _ _
        (Q'.add_eqv_congr_right _ _ _
          (QPoly.q_add_congr
            (productHaar_gRadius_left r) (productHaar_hRadius_left r))))) ?_
  refine Q'.eqv_trans _
    (half * productHaar r +
      (quarter * (productHaar r + productHaar r) +
        quarter * productHaar (polyMul relativeFundamentalCharacter r))) _
    (Q'.add_eqv_congr_left _ _ _
      (Q'.mul_add_eqv quarter _ _)) ?_
  refine Q'.eqv_trans _
    (half * productHaar r +
      ((quarter * productHaar r + quarter * productHaar r) +
        quarter * productHaar (polyMul relativeFundamentalCharacter r))) _
    (Q'.add_eqv_congr_left _ _ _
      (Q'.add_eqv_congr_right _ _ _
        (Q'.mul_add_eqv quarter _ _))) ?_
  refine Q'.eqv_trans _
    ((half * productHaar r +
      (quarter * productHaar r + quarter * productHaar r)) +
        quarter * productHaar (polyMul relativeFundamentalCharacter r)) _
    (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)) ?_
  exact Q'.add_eqv_congr_right _ _ _ (half_two_quarters (productHaar r))

private theorem retainedRelativeWeight_common (p : RatPoly) :
    productHaar
        (polyMul retainedRelativeWeight (polyMul p p)) ≈
      productHaar (polyMul p p) +
        quarter * productHaar
          (polyMul relativeFundamentalCharacter (polyMul p p)) := by
  unfold retainedRelativeWeight
  refine Q'.eqv_trans _
    (productHaar (polyMul polyOne (polyMul p p)) +
      productHaar (polyMul (polySmul quarter relativeFundamentalCharacter)
        (polyMul p p))) _
    (productHaar_polyMul_add_left _ _ _) ?_
  exact QPoly.q_add_congr
    (productHaar_polyOne_mul (polyMul p p))
    (productHaar_polyMul_smul_left quarter relativeFundamentalCharacter
      (polyMul p p))

/-- Exact sphere-radius identification of the retained Wilson weight with its
finite polynomial sum-of-squares representative, after pairing with any
polynomial square. -/
theorem retainedSOSWeight_square_eq_retained (p : RatPoly) :
    productHaar (polyMul retainedSOSWeight (polyMul p p)) ≈
      productHaar (polyMul retainedRelativeWeight (polyMul p p)) := by
  refine Q'.eqv_trans _ (retainedSOSValue p) _
    (retainedSOSWeight_value p) ?_
  exact Q'.eqv_trans _ _ _ (retainedSOSValue_common p)
    (Q'.eqv_symm (retainedRelativeWeight_common p))

/-- Wilson-weighted all-degree positivity on every supported polynomial in
the eight quaternion coordinates. -/
theorem retainedRelativeWeight_square_nonneg
    (p : RatPoly) (hp : Supported8 p) :
    (0 : Q') ≤ productHaar
      (polyMul retainedRelativeWeight (polyMul p p)) := by
  have hsos := retainedSOSWeight_square_nonneg p hp
  exact Q'.le_trans' _ _ _ hsos
    (Q'.le_of_eqv (retainedSOSWeight_square_eq_retained p))

end YMGap.Continuum.SU2QuaternionWilsonReferenceWeight

#print axioms YMGap.Continuum.SU2QuaternionWilsonReferenceWeight.productHaar_polyMul_four_swap
#print axioms YMGap.Continuum.SU2QuaternionWilsonReferenceWeight.retainedSOSWeight_square_eq_retained
#print axioms YMGap.Continuum.SU2QuaternionWilsonReferenceWeight.retainedRelativeWeight_square_nonneg
