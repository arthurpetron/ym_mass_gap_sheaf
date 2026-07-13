/-
# The associative rational class-polynomial carrier for the SU(2) modes

`RGTransport.charAlg` is a useful spin-label carrier, but its multiplication
keeps only the lowest fusion channel and is not associative.  This module
builds the algebraic replacement on the existing constructive `QPoly`
substrate.  Equality is extensional rational evaluation up to `Q'.eqv`.

The carrier is proved to be a commutative associative unital algebra (at the
operations needed below), with identity star.  The first four SU(2)
second-kind character polynomials are explicit and the first nontrivial
Clebsch--Gordan products are kernel checked coefficient identities:

  chi1 * chi1 = chi0 + chi2
  chi1 * chi2 = chi1 + chi3.

This closes the algebra-normalization issue only.  It does not identify the
polynomial functional with the interacting finite-volume Wilson state or its
time evolution.
-/

import YMGap.Constructive.QPoly
import YMGap.Continuum.ChebyshevBound
import YMGap.Continuum.ChebOrthoMatrix

namespace YMGap.Continuum.SU2ClassPolynomialAlgebra

open YMGap.Constructive
open YMGap.Constructive.QPoly

/-- Extensional equality of rational class polynomials. -/
def PolyEqv (p q : Poly) : Prop :=
  ∀ x : Q', (eval p x).eqv (eval q x)

local infix:50 " ≈ₚ " => PolyEqv

theorem peqv_refl (p : Poly) : p ≈ₚ p :=
  fun x => Q'.eqv_refl (eval p x)

theorem peqv_symm {p q : Poly} (h : p ≈ₚ q) : q ≈ₚ p :=
  fun x => Q'.eqv_symm (h x)

theorem peqv_trans {p q r : Poly} (hpq : p ≈ₚ q) (hqr : q ≈ₚ r) :
    p ≈ₚ r :=
  fun x => Q'.eqv_trans _ _ _ (hpq x) (hqr x)

theorem padd_congr {p p' q q' : Poly} (hp : p ≈ₚ p') (hq : q ≈ₚ q') :
    padd p q ≈ₚ padd p' q' := by
  intro x
  exact Q'.eqv_trans _ _ _ (eval_padd p q x)
    (Q'.eqv_trans _ _ _ (q_add_congr (hp x) (hq x))
      (Q'.eqv_symm (eval_padd p' q' x)))

theorem pmul_congr {p p' q q' : Poly} (hp : p ≈ₚ p') (hq : q ≈ₚ q') :
    pmul p q ≈ₚ pmul p' q' := by
  intro x
  refine Q'.eqv_trans _ _ _ (eval_pmul p q x) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (hp x))
      (Q'.mul_eqv_congr_left _ _ _ (hq x))) ?_
  exact Q'.eqv_symm (eval_pmul p' q' x)

theorem padd_assoc (p q r : Poly) : padd (padd p q) r ≈ₚ padd p (padd q r) := by
  intro x
  refine Q'.eqv_trans _ _ _ (eval_padd (padd p q) r x) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ _ (eval_padd p q x)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_assoc_eqv (eval p x) (eval q x) (eval r x)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left _ _ _ (Q'.eqv_symm (eval_padd q r x))) ?_
  exact Q'.eqv_symm (eval_padd p (padd q r) x)

theorem padd_comm (p q : Poly) : padd p q ≈ₚ padd q p := by
  intro x
  exact Q'.eqv_trans _ _ _ (eval_padd p q x)
    (Q'.eqv_trans _ _ _ (Q'.add_comm_eqv (eval p x) (eval q x))
      (Q'.eqv_symm (eval_padd q p x)))

theorem pmul_assoc (p q r : Poly) : pmul (pmul p q) r ≈ₚ pmul p (pmul q r) := by
  intro x
  refine Q'.eqv_trans _ _ _ (eval_pmul (pmul p q) r x) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ (eval_pmul p q x)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_assoc_eqv (eval p x) (eval q x) (eval r x)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (eval_pmul q r x))) ?_
  exact Q'.eqv_symm (eval_pmul p (pmul q r) x)

theorem pmul_comm (p q : Poly) : pmul p q ≈ₚ pmul q p := by
  intro x
  exact Q'.eqv_trans _ _ _ (eval_pmul p q x)
    (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv (eval p x) (eval q x))
      (Q'.eqv_symm (eval_pmul q p x)))

theorem pmul_padd (p q r : Poly) :
    pmul p (padd q r) ≈ₚ padd (pmul p q) (pmul p r) := by
  intro x
  refine Q'.eqv_trans _ _ _ (eval_pmul p (padd q r) x) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left _ _ _ (eval_padd q r x)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_add_eqv (eval p x) (eval q x) (eval r x)) ?_
  refine Q'.eqv_trans _ _ _
    (q_add_congr (Q'.eqv_symm (eval_pmul p q x))
      (Q'.eqv_symm (eval_pmul p r x))) ?_
  exact Q'.eqv_symm (eval_padd (pmul p q) (pmul p r) x)

def pzero : Poly := []
def pone : Poly := [1]

theorem eval_pzero (x : Q') : (eval pzero x).eqv 0 :=
  Q'.eqv_refl 0

theorem eval_pone (x : Q') : (eval pone x).eqv 1 := by
  show ((1 : Q') + x * 0).eqv 1
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left 1 (x * 0) 0 (q_mul_zero x))
    (q_add_zero_eqv 1)

theorem pmul_pone (p : Poly) : pmul p pone ≈ₚ p := by
  intro x
  refine Q'.eqv_trans _ _ _ (eval_pmul p pone x) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left _ _ _ (eval_pone x)) ?_
  exact Q'.mul_one_eqv (eval p x)

theorem pone_pmul (p : Poly) : pmul pone p ≈ₚ p := by
  intro x
  refine Q'.eqv_trans _ _ _ (eval_pmul pone p x) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ (eval_pone x)) ?_
  exact Q'.one_mul_eqv (eval p x)

theorem pmul_pzero (p : Poly) : pmul p pzero ≈ₚ pzero := by
  intro x
  refine Q'.eqv_trans _ _ _ (eval_pmul p pzero x) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left _ _ _ (eval_pzero x)) ?_
  exact q_mul_zero (eval p x)

theorem pzero_pmul (p : Poly) : pmul pzero p ≈ₚ pzero := by
  intro x
  refine Q'.eqv_trans _ _ _ (eval_pmul pzero p x) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ (eval_pzero x)) ?_
  exact q_zero_mul (eval p x)

/-- Real SU(2) class polynomials have identity involution. -/
def pstar (p : Poly) : Poly := p

theorem pstar_involutive (p : Poly) : pstar (pstar p) ≈ₚ p :=
  peqv_refl p

theorem pstar_pmul (p q : Poly) : pstar (pmul p q) ≈ₚ pmul (pstar q) (pstar p) :=
  pmul_comm p q

/-! The first exact SU(2) character modes. -/

def chi0 : Poly := [1]
def chi1 : Poly := [0, 2]
def chi2 : Poly := [-1, 0, 4]
def chi3 : Poly := [0, -4, 0, 8]

/-- The polynomial vacuum mode is the genuine second-kind character `U₀`. -/
theorem eval_chi0 (x : Q') : (eval chi0 x).eqv (Cheb.U 0 x) := by
  rw [Cheb.U_zero]
  exact eval_pone x

/-- The retained fundamental mode is the genuine character `U₁ = 2x`. -/
theorem eval_chi1 (x : Q') : (eval chi1 x).eqv (Cheb.U 1 x) := by
  rw [Cheb.U_one]
  change ((0 : Q') + x * ((2 : Q') + x * 0)).eqv ((2 : Q') * x)
  refine Q'.eqv_trans _ _ _ (q_zero_add_eqv _) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left x _ _
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left 2 (x * 0) 0 (q_mul_zero x))
        (q_add_zero_eqv 2))) ?_
  exact Q'.mul_comm_eqv x 2

/-- The two retained physical character polynomials are distinct already at
the rational class point `x=0`. -/
theorem chi0_not_peqv_chi1 : ¬ (chi0 ≈ₚ chi1) := by
  intro h
  exact (by decide : ¬ (eval chi0 0).eqv (eval chi1 0)) (h 0)

/-- `U₁² = U₀ + U₂`, as a coefficient-checked polynomial identity. -/
theorem chi1_sq_fusion : pmul chi1 chi1 ≈ₚ padd chi0 chi2 := by
  intro x
  exact poly_eqv _ _ x (by decide)

/-- `U₁ U₂ = U₁ + U₃`, the next fusion identity. -/
theorem chi1_chi2_fusion : pmul chi1 chi2 ≈ₚ padd chi1 chi3 := by
  intro x
  exact poly_eqv _ _ x (by decide)

/-- The vacuum and quadratic character modes are genuinely distinct. -/
theorem chi0_not_peqv_chi2 : ¬ (chi0 ≈ₚ chi2) := by
  intro h
  exact (by decide : ¬ (eval chi0 0).eqv (eval chi2 0)) (h 0)

/-- The formerly failing three-factor expression is associative here. -/
theorem chi_triple_associative :
    pmul (pmul chi1 chi1) chi2 ≈ₚ pmul chi1 (pmul chi1 chi2) :=
  pmul_assoc chi1 chi1 chi2

/-! ## All character modes and the full fusion sum -/

/-- The coefficient-list representative of every second-kind character. -/
def chebPoly : Nat → Poly
  | 0 => chi0
  | 1 => chi1
  | n + 2 => psub (pmul chi1 (chebPoly (n + 1))) (chebPoly n)

/-- The recursive coefficient polynomial evaluates to the repository's
second-kind Chebyshev character at every rational class point. -/
theorem eval_chebPoly : ∀ n x, (eval (chebPoly n) x).eqv (Cheb.U n x)
  | 0, x => eval_chi0 x
  | 1, x => eval_chi1 x
  | n + 2, x => by
      rw [chebPoly, Cheb.U_succ_succ]
      refine Q'.eqv_trans _ _ _
        (eval_psub (pmul chi1 (chebPoly (n + 1))) (chebPoly n) x) ?_
      refine Q'.eqv_trans _ _ _
        (q_add_congr (eval_pmul chi1 (chebPoly (n + 1)) x)
          (Q'.eqv_refl (-(eval (chebPoly n) x)))) ?_
      refine q_add_congr ?_ (Q'.neg_eqv_congr _ _ (eval_chebPoly n x))
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ (eval_chi1 x)) ?_
      exact Q'.mul_eqv_congr_left _ _ _ (eval_chebPoly (n + 1) x)

/-- Finite sum in the polynomial carrier, with the same left fold as the
constructive rational `finSum`. -/
def polyFinSum (f : Nat → Poly) : Nat → Poly
  | 0 => pzero
  | n + 1 => padd (polyFinSum f n) (f n)

theorem eval_polyFinSum (f : Nat → Poly) (x : Q') : ∀ n,
    (eval (polyFinSum f n) x).eqv
      (RationalTail.finSum (fun i => eval (f i) x) n)
  | 0 => eval_pzero x
  | n + 1 => by
      refine Q'.eqv_trans _ _ _ (eval_padd (polyFinSum f n) (f n) x) ?_
      exact q_add_congr (eval_polyFinSum f x n) (Q'.eqv_refl _)

theorem finSum_congr_eqv {f g : Nat → Q'} (h : ∀ i, (f i).eqv (g i)) : ∀ n,
    (RationalTail.finSum f n).eqv (RationalTail.finSum g n)
  | 0 => Q'.eqv_refl 0
  | n + 1 => q_add_congr (finSum_congr_eqv h n) (h n)

/-- The full Clebsch--Gordan fusion sum as an actual polynomial. -/
def fusionPoly (c d : Nat) : Poly :=
  polyFinSum
    (fun r => chebPoly
      (ChebOrthogonality.fusionLow c d + 2 * r))
    (min c d + 1)

theorem eval_fusionPoly (c d : Nat) (x : Q') :
    (eval (fusionPoly c d) x).eqv
      (ChebOrthogonality.Ufusion c d x) := by
  unfold fusionPoly ChebOrthogonality.Ufusion
  refine Q'.eqv_trans _ _ _ (eval_polyFinSum _ x _) ?_
  exact finSum_congr_eqv
    (fun r => eval_chebPoly
      (ChebOrthogonality.fusionLow c d + 2 * r) x) _

/-- General SU(2) character multiplication is the complete linear fusion sum,
not the legacy lowest-channel projection. -/
theorem chebPoly_fusion (c d : Nat) :
    pmul (chebPoly c) (chebPoly d) ≈ₚ fusionPoly c d := by
  intro x
  refine Q'.eqv_trans _ _ _ (eval_pmul (chebPoly c) (chebPoly d) x) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (eval_chebPoly c x))
      (Q'.mul_eqv_congr_left _ _ _ (eval_chebPoly d x))) ?_
  refine Q'.eqv_trans _ _ _
    (ChebOrthoMatrix.chebU_fusion c d x) ?_
  exact Q'.eqv_symm (eval_fusionPoly c d x)

end YMGap.Continuum.SU2ClassPolynomialAlgebra

#print axioms YMGap.Continuum.SU2ClassPolynomialAlgebra.pmul_assoc
#print axioms YMGap.Continuum.SU2ClassPolynomialAlgebra.pmul_padd
#print axioms YMGap.Continuum.SU2ClassPolynomialAlgebra.chi1_sq_fusion
#print axioms YMGap.Continuum.SU2ClassPolynomialAlgebra.chi1_chi2_fusion
#print axioms YMGap.Continuum.SU2ClassPolynomialAlgebra.eval_chi0
#print axioms YMGap.Continuum.SU2ClassPolynomialAlgebra.eval_chi1
#print axioms YMGap.Continuum.SU2ClassPolynomialAlgebra.chi0_not_peqv_chi1
#print axioms YMGap.Continuum.SU2ClassPolynomialAlgebra.chi0_not_peqv_chi2
#print axioms YMGap.Continuum.SU2ClassPolynomialAlgebra.chi_triple_associative
#print axioms YMGap.Continuum.SU2ClassPolynomialAlgebra.eval_chebPoly
#print axioms YMGap.Continuum.SU2ClassPolynomialAlgebra.eval_fusionPoly
#print axioms YMGap.Continuum.SU2ClassPolynomialAlgebra.chebPoly_fusion
