/-
# Constructive all-degree positivity of the quaternion product-Haar functional

This file partitions an arbitrary finite polynomial into one coordinate-parity
sector and its complement.  Exact parity orthogonality makes the Haar square
the sum of the two smaller squares.  Well-founded recursion on the complement
length then reduces every square to the fixed-sector positivity theorem.
-/

import YMGap.Continuum.SU2QuaternionHaarParityHomogenization

namespace YMGap.Continuum.SU2QuaternionHaarPolynomialPositivity

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionPolynomialHaarLinearity
open YMGap.Continuum.SU2QuaternionHaarParitySectors
open YMGap.Continuum.SU2QuaternionHaarParityPolynomial
open YMGap.Continuum.SU2QuaternionHaarBihomogeneousPositivity
open YMGap.Continuum.SU2QuaternionHaarRadiusHomogenization
open YMGap.Continuum.SU2QuaternionHaarParityHomogenization

local infix:50 " ≈ " => Q'.eqv

set_option maxHeartbeats 1800000
set_option maxRecDepth 10000

/-- The sub-polynomial whose monomials lie in the specified parity sector. -/
def paritySector (s : Parity8) : RatPoly → RatPoly
  | [] => []
  | t :: p =>
      if exponentParity8 t.1 = s then t :: paritySector s p
      else paritySector s p

/-- The complementary sub-polynomial. -/
def parityComplement (s : Parity8) : RatPoly → RatPoly
  | [] => []
  | t :: p =>
      if exponentParity8 t.1 = s then parityComplement s p
      else t :: parityComplement s p

theorem paritySector_all (s : Parity8) : ∀ p : RatPoly,
    AllParity8 s (paritySector s p)
  | [] => by
      intro t ht
      simp [paritySector] at ht
  | a :: p => by
      simp only [paritySector]
      split
      next ha =>
        intro t ht
        simp only [List.mem_cons] at ht
        rcases ht with rfl | ht
        · exact ha
        · exact paritySector_all s p t ht
      next _ => exact paritySector_all s p

theorem parityComplement_ne (s : Parity8) : ∀ p : RatPoly,
    ∀ t, t ∈ parityComplement s p → exponentParity8 t.1 ≠ s
  | [], t, ht => by simp [parityComplement] at ht
  | a :: p, t, ht => by
      simp only [parityComplement] at ht
      split at ht
      next _ => exact parityComplement_ne s p t ht
      next ha =>
        simp only [List.mem_cons] at ht
        rcases ht with rfl | ht
        · exact ha
        · exact parityComplement_ne s p t ht

theorem paritySector_supported (s : Parity8) : ∀ p : RatPoly,
    Supported8 p → Supported8 (paritySector s p)
  | [], _ => by
      intro t ht
      simp [paritySector] at ht
  | a :: p, hp => by
      simp only [paritySector]
      split
      next _ =>
        intro t ht
        simp only [List.mem_cons] at ht
        rcases ht with rfl | ht
        · exact hp t (by simp)
        · exact paritySector_supported s p (by
            intro u hu
            exact hp u (by simp [hu])) t ht
      next _ =>
        exact paritySector_supported s p (by
          intro u hu
          exact hp u (by simp [hu]))

theorem parityComplement_supported (s : Parity8) : ∀ p : RatPoly,
    Supported8 p → Supported8 (parityComplement s p)
  | [], _ => by
      intro t ht
      simp [parityComplement] at ht
  | a :: p, hp => by
      simp only [parityComplement]
      split
      next _ =>
        exact parityComplement_supported s p (by
          intro u hu
          exact hp u (by simp [hu]))
      next _ =>
        intro t ht
        simp only [List.mem_cons] at ht
        rcases ht with rfl | ht
        · exact hp t (by simp)
        · exact parityComplement_supported s p (by
            intro u hu
            exact hp u (by simp [hu])) t ht

theorem parityComplement_length_le (s : Parity8) : ∀ p : RatPoly,
    (parityComplement s p).length ≤ p.length
  | [] => by simp [parityComplement]
  | a :: p => by
      simp only [parityComplement]
      split
      next _ =>
        have h := parityComplement_length_le s p
        simp only [List.length_cons]
        omega
      next _ =>
        have h := parityComplement_length_le s p
        simp only [List.length_cons]
        omega

private theorem productHaar_polyMul_cons_left (a : RatTerm) (p q : RatPoly) :
    productHaar (polyMul (a :: p) q) ≈
      productHaar (polyMul [a] q) + productHaar (polyMul p q) := by
  have hmul : polyMul (a :: p) q = polyMul [a] q ++ polyMul p q := by
    simp [polyMul]
  rw [hmul]
  exact productHaar_append_eqv _ _

/-- Exact linear splitting of a Haar pairing by one selected parity sector. -/
theorem productHaar_parity_split_left (s : Parity8) : ∀ p q : RatPoly,
    productHaar (polyMul p q) ≈
      productHaar (polyMul (paritySector s p) q) +
        productHaar (polyMul (parityComplement s p) q)
  | [], q => by
      simp [paritySector, parityComplement, polyMul]
      exact Q'.eqv_symm (QPoly.q_zero_add_eqv 0)
  | a :: p, q => by
      by_cases ha : exponentParity8 a.1 = s
      · simp only [paritySector, parityComplement, if_pos ha]
        refine Q'.eqv_trans _
          (productHaar (polyMul [a] q) + productHaar (polyMul p q)) _
          (productHaar_polyMul_cons_left a p q) ?_
        refine Q'.eqv_trans _
          (productHaar (polyMul [a] q) +
            (productHaar (polyMul (paritySector s p) q) +
              productHaar (polyMul (parityComplement s p) q))) _
          (Q'.add_eqv_congr_left _ _ _
            (productHaar_parity_split_left s p q)) ?_
        refine Q'.eqv_trans _
          ((productHaar (polyMul [a] q) +
              productHaar (polyMul (paritySector s p) q)) +
            productHaar (polyMul (parityComplement s p) q)) _
          (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)) ?_
        exact Q'.add_eqv_congr_right _ _ _
          (Q'.eqv_symm
            (productHaar_polyMul_cons_left a (paritySector s p) q))
      · simp only [paritySector, parityComplement, if_neg ha]
        refine Q'.eqv_trans _
          (productHaar (polyMul [a] q) + productHaar (polyMul p q)) _
          (productHaar_polyMul_cons_left a p q) ?_
        refine Q'.eqv_trans _
          (productHaar (polyMul [a] q) +
            (productHaar (polyMul (paritySector s p) q) +
              productHaar (polyMul (parityComplement s p) q))) _
          (Q'.add_eqv_congr_left _ _ _
            (productHaar_parity_split_left s p q)) ?_
        refine Q'.eqv_trans _
          ((productHaar (polyMul [a] q) +
              productHaar (polyMul (paritySector s p) q)) +
            productHaar (polyMul (parityComplement s p) q)) _
          (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)) ?_
        refine Q'.eqv_trans _
          ((productHaar (polyMul (paritySector s p) q) +
              productHaar (polyMul [a] q)) +
            productHaar (polyMul (parityComplement s p) q)) _
          (Q'.add_eqv_congr_right _ _ _ (Q'.add_comm_eqv _ _)) ?_
        refine Q'.eqv_trans _
          (productHaar (polyMul (paritySector s p) q) +
            (productHaar (polyMul [a] q) +
              productHaar (polyMul (parityComplement s p) q))) _
          (Q'.add_assoc_eqv _ _ _) ?_
        exact Q'.add_eqv_congr_left _ _ _
          (Q'.eqv_symm
            (productHaar_polyMul_cons_left a (parityComplement s p) q))

theorem productHaar_parity_split_right (s : Parity8) (p q : RatPoly) :
    productHaar (polyMul p q) ≈
      productHaar (polyMul p (paritySector s q)) +
        productHaar (polyMul p (parityComplement s q)) := by
  refine Q'.eqv_trans _ (productHaar (polyMul q p)) _
    (productHaar_polyMul_comm p q) ?_
  refine Q'.eqv_trans _
    (productHaar (polyMul (paritySector s q) p) +
      productHaar (polyMul (parityComplement s q) p)) _
    (productHaar_parity_split_left s q p) ?_
  exact QPoly.q_add_congr
    (productHaar_polyMul_comm (paritySector s q) p)
    (productHaar_polyMul_comm (parityComplement s q) p)

private theorem productHaar_sector_complement_zero
    (s : Parity8) (p : RatPoly) :
    productHaar (polyMul (paritySector s p) (parityComplement s p)) ≈ 0 := by
  apply productHaar_mul_cross_parity_zero
  intro a ha b hb hab
  have has := paritySector_all s p a ha
  have hbs := parityComplement_ne s p b hb
  exact hbs (hab ▸ has)

private theorem productHaar_complement_sector_zero
    (s : Parity8) (p : RatPoly) :
    productHaar (polyMul (parityComplement s p) (paritySector s p)) ≈ 0 := by
  refine Q'.eqv_trans _
    (productHaar (polyMul (paritySector s p) (parityComplement s p))) _
    (productHaar_polyMul_comm _ _) ?_
  exact productHaar_sector_complement_zero s p

/-- Pythagorean identity for the selected parity sector and its complement. -/
theorem productHaar_parity_square_split (s : Parity8) (p : RatPoly) :
    productHaar (polyMul p p) ≈
      productHaar (polyMul (paritySector s p) (paritySector s p)) +
        productHaar (polyMul (parityComplement s p) (parityComplement s p)) := by
  refine Q'.eqv_trans _
    (productHaar (polyMul (paritySector s p) p) +
      productHaar (polyMul (parityComplement s p) p)) _
    (productHaar_parity_split_left s p p) ?_
  refine Q'.eqv_trans _
    ((productHaar (polyMul (paritySector s p) (paritySector s p)) +
        productHaar (polyMul (paritySector s p) (parityComplement s p))) +
      (productHaar (polyMul (parityComplement s p) (paritySector s p)) +
        productHaar (polyMul (parityComplement s p) (parityComplement s p)))) _
    (QPoly.q_add_congr
      (productHaar_parity_split_right s (paritySector s p) p)
      (productHaar_parity_split_right s (parityComplement s p) p)) ?_
  refine Q'.eqv_trans _
    ((productHaar (polyMul (paritySector s p) (paritySector s p)) + 0) +
      (0 + productHaar
        (polyMul (parityComplement s p) (parityComplement s p)))) _
    (QPoly.q_add_congr
      (QPoly.q_add_congr (Q'.eqv_refl _)
        (productHaar_sector_complement_zero s p))
      (QPoly.q_add_congr (productHaar_complement_sector_zero s p)
        (Q'.eqv_refl _))) ?_
  exact QPoly.q_add_congr
    (QPoly.q_add_zero_eqv _)
    (QPoly.q_zero_add_eqv _)

private theorem productHaar_square_nonneg_fuel : ∀ (n : Nat) (p : RatPoly),
    p.length ≤ n → Supported8 p →
      (0 : Q') ≤ productHaar (polyMul p p)
  | 0, [], _, _ =>
      productHaar_square_nonneg_of_parity zeroParity8 []
        (by intro t ht; simp at ht) (by intro t ht; simp at ht)
  | 0, _ :: _, hlen, _ => by simp at hlen
  | _ + 1, [], _, _ =>
      productHaar_square_nonneg_of_parity zeroParity8 []
        (by intro t ht; simp at ht) (by intro t ht; simp at ht)
  | n + 1, a :: p, hlen, hp8 => by
      let s := exponentParity8 a.1
      let b := paritySector s (a :: p)
      let r := parityComplement s (a :: p)
      have hb8 : Supported8 b := paritySector_supported s (a :: p) hp8
      have hbp : AllParity8 s b := paritySector_all s (a :: p)
      have hr8 : Supported8 r := parityComplement_supported s (a :: p) hp8
      have hrlen : r.length ≤ n := by
        have hcomp := parityComplement_length_le s p
        change (parityComplement s (a :: p)).length ≤ n
        rw [show parityComplement s (a :: p) = parityComplement s p by
          simp [parityComplement, s]]
        simp only [List.length_cons] at hlen
        omega
      have hb_nonneg : (0 : Q') ≤ productHaar (polyMul b b) :=
        productHaar_square_nonneg_of_parity s b hb8 hbp
      have hr_nonneg : (0 : Q') ≤ productHaar (polyMul r r) :=
        productHaar_square_nonneg_fuel n r hrlen hr8
      have hsum : (0 : Q') ≤
          productHaar (polyMul b b) + productHaar (polyMul r r) :=
        Q'.zero_le_add _ _ hb_nonneg hr_nonneg
      exact Q'.le_trans' _ _ _ hsum
        (Q'.le_of_eqv (Q'.eqv_symm
          (productHaar_parity_square_split s (a :: p))))

/-- The product-Haar moment functional is positive on the square of every
finite eight-coordinate rational polynomial. -/
theorem productHaar_square_nonneg (p : RatPoly) (hp8 : Supported8 p) :
    (0 : Q') ≤ productHaar (polyMul p p) :=
  productHaar_square_nonneg_fuel p.length p (Nat.le_refl _) hp8

end YMGap.Continuum.SU2QuaternionHaarPolynomialPositivity

#print axioms YMGap.Continuum.SU2QuaternionHaarPolynomialPositivity.productHaar_parity_square_split
#print axioms YMGap.Continuum.SU2QuaternionHaarPolynomialPositivity.productHaar_square_nonneg
