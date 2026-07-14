/-
# Radius homogenization algebra for quaternion product Haar

This module supplies the exact associative/commutative bookkeeping needed to
insert boundary radius polynomials into individual homogeneous components.
It proves that any finite number of first- or second-boundary radius factors
may be inserted into either side of a product-Haar pairing without changing
its value.
-/

import YMGap.Continuum.SU2QuaternionHaarBihomogeneousPositivity

namespace YMGap.Continuum.SU2QuaternionHaarRadiusHomogenization

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionPolynomialHaarLinearity
open YMGap.Continuum.SU2QuaternionHaarSphereIdeal
open YMGap.Continuum.SU2QuaternionHaarBihomogeneousPositivity

local infix:50 " ≈ " => Q'.eqv

set_option maxHeartbeats 1200000
set_option maxRecDepth 10000

theorem monoMul_comm (a b : List Nat) : monoMul a b = monoMul b a := by
  induction a generalizing b with
  | nil => cases b <;> rfl
  | cons x xs ih =>
      cases b with
      | nil => rfl
      | cons y ys => simp [monoMul, Nat.add_comm, ih ys]

theorem monoMul_assoc (a b c : List Nat) :
    monoMul (monoMul a b) c = monoMul a (monoMul b c) := by
  induction a generalizing b c with
  | nil => rfl
  | cons x xs ih =>
      cases b with
      | nil => rfl
      | cons y ys =>
          cases c with
          | nil => rfl
          | cons z zs => simp [monoMul, Nat.add_assoc, ih ys zs]

private def haarCell (a b : RatTerm) : Q' :=
  (a.2 * b.2) * productHaarMono (monoMul a.1 b.1)

private theorem haarCell_symm (a b : RatTerm) :
    haarCell a b ≈ haarCell b a := by
  unfold haarCell
  rw [monoMul_comm a.1 b.1]
  exact Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv a.2 b.2)

private theorem haarRow_nil_right : ∀ p : RatPoly, haarBilinear p [] ≈ 0
  | [] => Q'.eqv_refl 0
  | _ :: p => Q'.eqv_trans _ (0 + 0) _
      (Q'.add_eqv_congr_left 0 _ _ (haarRow_nil_right p))
      (QPoly.q_zero_add_eqv 0)

private theorem haarBilinear_symm : ∀ p q : RatPoly,
    haarBilinear p q ≈ haarBilinear q p
  | [], q => Q'.eqv_symm (haarRow_nil_right q)
  | a :: p, [] => haarRow_nil_right (a :: p)
  | a :: p, b :: q => by
      change (haarCell a b + haarRow a q) +
          haarBilinear p (b :: q) ≈
        (haarCell b a + haarRow b p) +
          haarBilinear q (a :: p)
      refine Q'.eqv_trans _
        ((haarCell a b + haarRow a q) +
          (haarRow b p + haarBilinear q p)) _
        (Q'.add_eqv_congr_left _ _ _ (by
          simpa [haarBilinear] using haarBilinear_symm p (b :: q))) ?_
      refine Q'.eqv_trans _
        ((haarCell b a + haarRow a q) +
          (haarRow b p + haarBilinear p q)) _
        (QPoly.q_add_congr
          (Q'.add_eqv_congr_right _ _ _ (haarCell_symm a b))
          (Q'.add_eqv_congr_left _ _ _
            (Q'.eqv_symm (haarBilinear_symm p q)))) ?_
      refine Q'.eqv_trans _
        ((haarCell b a + haarRow b p) +
          (haarRow a q + haarBilinear p q)) _
        (QPoly.q_interchange
          (haarCell b a) (haarRow a q) (haarRow b p) (haarBilinear p q)) ?_
      exact Q'.add_eqv_congr_left _ _ _ (by
        simpa [haarBilinear] using haarBilinear_symm (a :: p) q)

theorem productHaar_polyMul_comm (p q : RatPoly) :
    productHaar (polyMul p q) ≈ productHaar (polyMul q p) :=
  Q'.eqv_trans _ (haarBilinear p q) _
    (productHaar_polyMul_eq_bilinear p q)
    (Q'.eqv_trans _ (haarBilinear q p) _
      (haarBilinear_symm p q)
      (Q'.eqv_symm (productHaar_polyMul_eq_bilinear q p)))

private theorem haarRow_append (a : RatTerm) : ∀ p q : RatPoly,
    haarRow a (p ++ q) ≈ haarRow a p + haarRow a q
  | [], q => Q'.eqv_symm (QPoly.q_zero_add_eqv _)
  | b :: p, q => by
      change haarCell a b + haarRow a (p ++ q) ≈
        (haarCell a b + haarRow a p) + haarRow a q
      refine Q'.eqv_trans _
        (haarCell a b + (haarRow a p + haarRow a q)) _
        (Q'.add_eqv_congr_left _ _ _ (haarRow_append a p q)) ?_
      exact Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)

private theorem haarBilinear_append_left (p q r : RatPoly) :
    haarBilinear (p ++ q) r ≈ haarBilinear p r + haarBilinear q r := by
  induction p with
  | nil => exact Q'.eqv_symm (QPoly.q_zero_add_eqv _)
  | cons a p ih =>
      change haarRow a r + haarBilinear (p ++ q) r ≈
        (haarRow a r + haarBilinear p r) + haarBilinear q r
      refine Q'.eqv_trans _
        (haarRow a r + (haarBilinear p r + haarBilinear q r)) _
        (Q'.add_eqv_congr_left _ _ _ ih) ?_
      exact Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)

private theorem haarBilinear_append_right (p q r : RatPoly) :
    haarBilinear p (q ++ r) ≈ haarBilinear p q + haarBilinear p r := by
  refine Q'.eqv_trans _ (haarBilinear (q ++ r) p) _
    (haarBilinear_symm p (q ++ r)) ?_
  refine Q'.eqv_trans _ (haarBilinear q p + haarBilinear r p) _
    (haarBilinear_append_left q r p) ?_
  exact QPoly.q_add_congr
    (haarBilinear_symm q p) (haarBilinear_symm r p)

private def haarTripleCell (a b c : RatTerm) : Q' :=
  ((a.2 * b.2) * c.2) *
    productHaarMono (monoMul (monoMul a.1 b.1) c.1)

private def haarTripleLast (a b : RatTerm) : RatPoly → Q'
  | [] => 0
  | c :: r => haarTripleCell a b c + haarTripleLast a b r

private def haarTripleMiddle (a : RatTerm) : RatPoly → RatPoly → Q'
  | [], _ => 0
  | b :: q, r => haarTripleLast a b r + haarTripleMiddle a q r

private def haarTriple : RatPoly → RatPoly → RatPoly → Q'
  | [], _, _ => 0
  | a :: p, q, r => haarTripleMiddle a q r + haarTriple p q r

private theorem haarRow_generated (a b : RatTerm) : ∀ r : RatPoly,
    haarRow (monoMul a.1 b.1, a.2 * b.2) r ≈ haarTripleLast a b r
  | [] => Q'.eqv_refl 0
  | c :: r => by
      change haarTripleCell a b c +
          haarRow (monoMul a.1 b.1, a.2 * b.2) r ≈
        haarTripleCell a b c + haarTripleLast a b r
      exact Q'.add_eqv_congr_left _ _ _ (haarRow_generated a b r)

private theorem haarBilinear_generated (a : RatTerm) : ∀ q r : RatPoly,
    haarBilinear
      (q.map fun b => (monoMul a.1 b.1, a.2 * b.2)) r ≈
      haarTripleMiddle a q r
  | [], _ => Q'.eqv_refl 0
  | b :: q, r => by
      exact QPoly.q_add_congr
        (haarRow_generated a b r) (haarBilinear_generated a q r)

private theorem haarBilinear_polyMul_left : ∀ p q r : RatPoly,
    haarBilinear (polyMul p q) r ≈ haarTriple p q r
  | [], _, _ => Q'.eqv_refl 0
  | a :: p, q, r => by
      unfold polyMul List.flatMap
      refine Q'.eqv_trans _
        (haarBilinear
            (q.map fun b => (monoMul a.1 b.1, a.2 * b.2)) r +
          haarBilinear (polyMul p q) r) _
        (haarBilinear_append_left _ _ r) ?_
      exact QPoly.q_add_congr
        (haarBilinear_generated a q r)
        (haarBilinear_polyMul_left p q r)

private theorem haarCell_right_assoc (a b c : RatTerm) :
    haarCell a (monoMul b.1 c.1, b.2 * c.2) ≈ haarTripleCell a b c := by
  unfold haarCell haarTripleCell
  rw [← monoMul_assoc a.1 b.1 c.1]
  exact Q'.mul_eqv_congr_right _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv a.2 b.2 c.2))

private theorem haarRow_map_right (a b : RatTerm) : ∀ r : RatPoly,
    haarRow a (r.map fun c => (monoMul b.1 c.1, b.2 * c.2)) ≈
      haarTripleLast a b r
  | [] => Q'.eqv_refl 0
  | c :: r => by
      exact QPoly.q_add_congr
        (haarCell_right_assoc a b c) (haarRow_map_right a b r)

private theorem haarRow_polyMul_right (a : RatTerm) : ∀ q r : RatPoly,
    haarRow a (polyMul q r) ≈ haarTripleMiddle a q r
  | [], _ => Q'.eqv_refl 0
  | b :: q, r => by
      unfold polyMul List.flatMap
      refine Q'.eqv_trans _
        (haarRow a
            (r.map fun c => (monoMul b.1 c.1, b.2 * c.2)) +
          haarRow a (polyMul q r)) _
        (haarRow_append a _ _) ?_
      exact QPoly.q_add_congr
        (haarRow_map_right a b r) (haarRow_polyMul_right a q r)

private theorem haarBilinear_polyMul_right : ∀ p q r : RatPoly,
    haarBilinear p (polyMul q r) ≈ haarTriple p q r
  | [], _, _ => Q'.eqv_refl 0
  | a :: p, q, r => by
      exact QPoly.q_add_congr
        (haarRow_polyMul_right a q r)
        (haarBilinear_polyMul_right p q r)

private theorem haarTripleCell_swap_last (a b c : RatTerm) :
    haarTripleCell a b c ≈ haarTripleCell a c b := by
  unfold haarTripleCell
  have hm : monoMul (monoMul a.1 b.1) c.1 =
      monoMul (monoMul a.1 c.1) b.1 := by
    rw [monoMul_assoc, monoMul_comm b.1 c.1, ← monoMul_assoc]
  rw [hm]
  refine Q'.mul_eqv_congr_right _ _ _ ?_
  refine Q'.eqv_trans _ (a.2 * (b.2 * c.2)) _
    (Q'.mul_assoc_eqv _ _ _) ?_
  refine Q'.eqv_trans _ (a.2 * (c.2 * b.2)) _
    (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_comm_eqv _ _)) ?_
  exact Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)

private theorem haarTripleLast_nil (a b : RatTerm) :
    haarTripleLast a b [] ≈ 0 := Q'.eqv_refl 0

private theorem haarTripleMiddle_nil_right (a : RatTerm) : ∀ q : RatPoly,
    haarTripleMiddle a q [] ≈ 0
  | [] => Q'.eqv_refl 0
  | _ :: q => Q'.eqv_trans _ (0 + 0) _
      (Q'.add_eqv_congr_left 0 _ _ (haarTripleMiddle_nil_right a q))
      (QPoly.q_zero_add_eqv 0)

private theorem haarTripleMiddle_swap (a : RatTerm) : ∀ q r : RatPoly,
    haarTripleMiddle a q r ≈ haarTripleMiddle a r q
  | [], r => Q'.eqv_symm (haarTripleMiddle_nil_right a r)
  | b :: q, [] => haarTripleMiddle_nil_right a (b :: q)
  | b :: q, c :: r => by
      change (haarTripleCell a b c + haarTripleLast a b r) +
          haarTripleMiddle a q (c :: r) ≈
        (haarTripleCell a c b + haarTripleLast a c q) +
          haarTripleMiddle a r (b :: q)
      refine Q'.eqv_trans _
        ((haarTripleCell a b c + haarTripleLast a b r) +
          (haarTripleLast a c q + haarTripleMiddle a r q)) _
        (Q'.add_eqv_congr_left _ _ _ (by
          simpa [haarTripleMiddle] using
            haarTripleMiddle_swap a q (c :: r))) ?_
      refine Q'.eqv_trans _
        ((haarTripleCell a c b + haarTripleLast a b r) +
          (haarTripleLast a c q + haarTripleMiddle a q r)) _
        (QPoly.q_add_congr
          (Q'.add_eqv_congr_right _ _ _ (haarTripleCell_swap_last a b c))
          (Q'.add_eqv_congr_left _ _ _
            (Q'.eqv_symm (haarTripleMiddle_swap a q r)))) ?_
      refine Q'.eqv_trans _
        ((haarTripleCell a c b + haarTripleLast a c q) +
          (haarTripleLast a b r + haarTripleMiddle a q r)) _
        (QPoly.q_interchange
          (haarTripleCell a c b) (haarTripleLast a b r)
          (haarTripleLast a c q) (haarTripleMiddle a q r)) ?_
      exact Q'.add_eqv_congr_left _ _ _ (by
        simpa [haarTripleMiddle] using
          haarTripleMiddle_swap a (b :: q) r)

private theorem haarTriple_swap_last : ∀ p q r : RatPoly,
    haarTriple p q r ≈ haarTriple p r q
  | [], _, _ => Q'.eqv_refl 0
  | a :: p, q, r =>
      QPoly.q_add_congr
        (haarTripleMiddle_swap a q r) (haarTriple_swap_last p q r)

/-- The last two factors of a triple product may be exchanged under the exact
product-Haar functional.  This is the public permutation API used by the
Wilson-weighted sum-of-squares consumer. -/
theorem productHaar_polyMul_middle_comm (p q r : RatPoly) :
    productHaar (polyMul p (polyMul q r)) ≈
      productHaar (polyMul p (polyMul r q)) := by
  refine Q'.eqv_trans _ (haarBilinear p (polyMul q r)) _
    (productHaar_polyMul_eq_bilinear p (polyMul q r)) ?_
  refine Q'.eqv_trans _ (haarTriple p q r) _
    (haarBilinear_polyMul_right p q r) ?_
  refine Q'.eqv_trans _ (haarTriple p r q) _
    (haarTriple_swap_last p q r) ?_
  refine Q'.eqv_trans _ (haarBilinear p (polyMul r q)) _
    (Q'.eqv_symm (haarBilinear_polyMul_right p r q)) ?_
  exact Q'.eqv_symm
    (productHaar_polyMul_eq_bilinear p (polyMul r q))

theorem productHaar_polyMul_assoc (p q r : RatPoly) :
    productHaar (polyMul (polyMul p q) r) ≈
      productHaar (polyMul p (polyMul q r)) := by
  refine Q'.eqv_trans _ (haarBilinear (polyMul p q) r) _
    (productHaar_polyMul_eq_bilinear (polyMul p q) r) ?_
  refine Q'.eqv_trans _ (haarTriple p q r) _
    (haarBilinear_polyMul_left p q r) ?_
  refine Q'.eqv_trans _ (haarBilinear p (polyMul q r)) _
    (Q'.eqv_symm (haarBilinear_polyMul_right p q r)) ?_
  exact Q'.eqv_symm (productHaar_polyMul_eq_bilinear p (polyMul q r))

/-- Repeated right multiplication by a fixed polynomial. -/
def radiusIter (R : RatPoly) : Nat → RatPoly → RatPoly
  | 0, p => p
  | n + 1, p => polyMul (radiusIter R n p) R

theorem productHaar_radiusIter_g (p : RatPoly) : ∀ n,
    productHaar (radiusIter gRadiusPolynomial n p) ≈ productHaar p
  | 0 => Q'.eqv_refl _
  | n + 1 => Q'.eqv_trans _ _ _
      (productHaar_mul_gRadius (radiusIter gRadiusPolynomial n p))
      (productHaar_radiusIter_g p n)

theorem productHaar_radiusIter_h (p : RatPoly) : ∀ n,
    productHaar (radiusIter hRadiusPolynomial n p) ≈ productHaar p
  | 0 => Q'.eqv_refl _
  | n + 1 => Q'.eqv_trans _ _ _
      (productHaar_mul_hRadius (radiusIter hRadiusPolynomial n p))
      (productHaar_radiusIter_h p n)

private theorem productHaar_radius_step_g_pair (p q : RatPoly) :
    productHaar (polyMul (polyMul p gRadiusPolynomial) q) ≈
      productHaar (polyMul p q) := by
  refine Q'.eqv_trans _
    (productHaar (polyMul p (polyMul gRadiusPolynomial q))) _
    (productHaar_polyMul_assoc p gRadiusPolynomial q) ?_
  refine Q'.eqv_trans _
    (productHaar (polyMul p (polyMul q gRadiusPolynomial))) _
    (productHaar_polyMul_middle_comm p gRadiusPolynomial q) ?_
  refine Q'.eqv_trans _
    (productHaar (polyMul (polyMul p q) gRadiusPolynomial)) _
    (Q'.eqv_symm (productHaar_polyMul_assoc p q gRadiusPolynomial)) ?_
  exact productHaar_mul_gRadius (polyMul p q)

private theorem productHaar_radius_step_h_pair (p q : RatPoly) :
    productHaar (polyMul (polyMul p hRadiusPolynomial) q) ≈
      productHaar (polyMul p q) := by
  refine Q'.eqv_trans _
    (productHaar (polyMul p (polyMul hRadiusPolynomial q))) _
    (productHaar_polyMul_assoc p hRadiusPolynomial q) ?_
  refine Q'.eqv_trans _
    (productHaar (polyMul p (polyMul q hRadiusPolynomial))) _
    (productHaar_polyMul_middle_comm p hRadiusPolynomial q) ?_
  refine Q'.eqv_trans _
    (productHaar (polyMul (polyMul p q) hRadiusPolynomial)) _
    (Q'.eqv_symm (productHaar_polyMul_assoc p q hRadiusPolynomial)) ?_
  exact productHaar_mul_hRadius (polyMul p q)

theorem productHaar_radiusIter_g_pair (p q : RatPoly) : ∀ n,
    productHaar (polyMul (radiusIter gRadiusPolynomial n p) q) ≈
      productHaar (polyMul p q)
  | 0 => Q'.eqv_refl _
  | n + 1 => Q'.eqv_trans _ _ _
      (productHaar_radius_step_g_pair
        (radiusIter gRadiusPolynomial n p) q)
      (productHaar_radiusIter_g_pair p q n)

theorem productHaar_radiusIter_h_pair (p q : RatPoly) : ∀ n,
    productHaar (polyMul (radiusIter hRadiusPolynomial n p) q) ≈
      productHaar (polyMul p q)
  | 0 => Q'.eqv_refl _
  | n + 1 => Q'.eqv_trans _ _ _
      (productHaar_radius_step_h_pair
        (radiusIter hRadiusPolynomial n p) q)
      (productHaar_radiusIter_h_pair p q n)

end YMGap.Continuum.SU2QuaternionHaarRadiusHomogenization

#print axioms YMGap.Continuum.SU2QuaternionHaarRadiusHomogenization.productHaar_polyMul_assoc
#print axioms YMGap.Continuum.SU2QuaternionHaarRadiusHomogenization.productHaar_polyMul_middle_comm
#print axioms YMGap.Continuum.SU2QuaternionHaarRadiusHomogenization.productHaar_radiusIter_g_pair
#print axioms YMGap.Continuum.SU2QuaternionHaarRadiusHomogenization.productHaar_radiusIter_h_pair
