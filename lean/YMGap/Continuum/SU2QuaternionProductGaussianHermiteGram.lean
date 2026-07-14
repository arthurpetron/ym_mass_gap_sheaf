/-
# Finite Hermite Gram witnesses for coordinate Gaussian kernels

For every finite `RatPoly`, each coordinate moment kernel on its term list is
given an explicit finite Hermite Gram representation.  The rank is computed
from the actual finite coefficient lists, so no degree bound or choice is
needed.  These coordinate witnesses are the inputs to the constructive Schur
product theorem used by the eight-variable square proof.
-/

import YMGap.Continuum.SU2QuaternionProductGaussianTensor
import YMGap.Continuum.SchurHadamardTransfer

namespace YMGap.Continuum.SU2QuaternionProductGaussianHermiteGram

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.RationalTail
open YMGap.Continuum.SU2ClassPolynomialAlgebra
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionGaussianPolynomialIBP
open YMGap.Continuum.SU2QuaternionGaussianHermiteOrthogonality
open YMGap.Continuum.SU2QuaternionGaussianHermiteSOS
open YMGap.Continuum.SU2QuaternionGaussianHermiteTriangular
open YMGap.Continuum.SchurHadamardTransfer

local infix:50 " ≈ " => Q'.eqv

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

private theorem zero_num_cast : (0 : Q').num = 0 := rfl
private theorem zero_den_cast : ((0 : Q').den : Int) = 1 := rfl
private theorem one_num_cast : (1 : Q').num = 1 := rfl
private theorem one_den_cast : ((1 : Q').den : Int) = 1 := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.ofNat_num_cast, Q'.ofNat_den_cast,
               zero_num_cast, zero_den_cast, one_num_cast, one_den_cast,
               Int.add_mul, Int.mul_add, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.zero_add, Int.add_zero];
             try ac_rfl))

theorem finSum_head (f : Nat → Q') : ∀ r : Nat,
    finSum f (r + 1) ≈ f 0 + finSum (fun k => f (k + 1)) r
  | 0 => by
      change (0 + f 0) ≈ f 0 + 0
      ring_qeqv
  | r + 1 => by
      change (finSum f (r + 1) + f (r + 1)) ≈
        f 0 + (finSum (fun k => f (k + 1)) r + f (r + 1))
      refine Q'.eqv_trans _
        ((f 0 + finSum (fun k => f (k + 1)) r) + f (r + 1)) _
        (Q'.add_eqv_congr_right _ _ _ (finSum_head f r)) ?_
      exact Q'.add_assoc_eqv _ _ _

private theorem finSum_zero_getD_left (ds : List Q') (n r : Nat) :
    finSum (fun k =>
      (([] : List Q').getD k 0 * ds.getD k 0) *
        Q'.ofNat (hermiteFactorial (n + k))) r ≈ 0 := by
  refine Q'.eqv_trans _ (finSum (fun _ => (0 : Q')) r) _ ?_ ?_
  · exact finSum_eqv_congr _ _ (fun k => by
      simp only [List.getD_nil]
      exact Q'.eqv_trans _ (0 * Q'.ofNat (hermiteFactorial (n + k))) _
        (Q'.mul_eqv_congr_right _ _ _ (QPoly.q_zero_mul _))
        (QPoly.q_zero_mul _)) r
  · rw [finSum_zero_seq]
    exact Q'.eqv_refl 0

private theorem finSum_zero_getD_right (cs : List Q') (n r : Nat) :
    finSum (fun k =>
      (cs.getD k 0 * ([] : List Q').getD k 0) *
        Q'.ofNat (hermiteFactorial (n + k))) r ≈ 0 := by
  refine Q'.eqv_trans _ (finSum (fun _ => (0 : Q')) r) _ ?_ ?_
  · exact finSum_eqv_congr _ _ (fun k => by
      simp only [List.getD_nil]
      exact Q'.eqv_trans _ (0 * Q'.ofNat (hermiteFactorial (n + k))) _
        (Q'.mul_eqv_congr_right _ _ _ (QPoly.q_mul_zero _))
        (QPoly.q_zero_mul _)) r
  · rw [finSum_zero_seq]
    exact Q'.eqv_refl 0

/-- A Hermite diagonal is a finite weighted dot product after padding both
coefficient lists by zero. -/
theorem hermiteDiagonalFrom_eq_finSum : ∀ (r n : Nat) (cs ds : List Q'),
    cs.length ≤ r → ds.length ≤ r →
    hermiteDiagonalFrom n cs ds ≈
      finSum (fun k => (cs.getD k 0 * ds.getD k 0) *
        Q'.ofNat (hermiteFactorial (n + k))) r
  | 0, _, cs, ds, hcs, hds => by
      have hcz : cs = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hcs)
      have hdz : ds = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hds)
      subst cs
      subst ds
      exact Q'.eqv_refl 0
  | r + 1, n, [], ds, _, _ =>
      Q'.eqv_symm (finSum_zero_getD_left ds n (r + 1))
  | r + 1, n, cs, [], _, _ =>
      by
        cases cs with
        | nil =>
            simpa [hermiteDiagonalFrom] using
              Q'.eqv_symm (finSum_zero_getD_right [] n (r + 1))
        | cons c cs =>
            simpa [hermiteDiagonalFrom] using
              Q'.eqv_symm (finSum_zero_getD_right (c :: cs) n (r + 1))
  | r + 1, n, c :: cs, d :: ds, hcs, hds => by
      have hcs' : cs.length ≤ r := by simpa using Nat.le_of_succ_le_succ hcs
      have hds' : ds.length ≤ r := by simpa using Nat.le_of_succ_le_succ hds
      have ih := hermiteDiagonalFrom_eq_finSum r (n + 1) cs ds hcs' hds'
      let f : Nat → Q' := fun k =>
        (((c :: cs).getD k 0) * ((d :: ds).getD k 0)) *
          Q'.ofNat (hermiteFactorial (n + k))
      refine Q'.eqv_trans _
        ((c * d) * Q'.ofNat (hermiteFactorial n) +
          finSum (fun k => (cs.getD k 0 * ds.getD k 0) *
            Q'.ofNat (hermiteFactorial ((n + 1) + k))) r) _
        (Q'.add_eqv_congr_left _ _ _ ih) ?_
      refine Q'.eqv_trans _ (f 0 + finSum (fun k => f (k + 1)) r) _ ?_ ?_
      · refine QPoly.q_add_congr ?_ ?_
        · exact Q'.eqv_refl _
        · exact finSum_eqv_congr _ _ (fun k => by
            change (cs.getD k 0 * ds.getD k 0) *
                Q'.ofNat (hermiteFactorial ((n + 1) + k)) ≈
              (cs.getD k 0 * ds.getD k 0) *
                Q'.ofNat (hermiteFactorial (n + (k + 1)))
            have hn : (n + 1) + k = n + (k + 1) := by omega
            rw [hn]
            exact Q'.eqv_refl _) r
      · exact Q'.eqv_symm (finSum_head f r)

/-- The monomial `x^n` in the repository's low-to-high coefficient format. -/
def monomialPoly (n : Nat) : Poly := basisCoeffs n 1

private theorem eval_monomialPoly (n : Nat) (z : Q') :
    eval (monomialPoly n) z ≈ (z ^ n) * 1 := by
  induction n with
  | zero =>
      change (1 + z * 0) ≈ 1 * 1
      ring_qeqv
  | succ n ih =>
      change (0 + z * eval (monomialPoly n) z) ≈ (z ^ (n + 1)) * 1
      refine Q'.eqv_trans _ (z * ((z ^ n) * 1)) _
        (Q'.eqv_trans _ (z * eval (monomialPoly n) z) _
          (QPoly.q_zero_add_eqv _)
          (Q'.mul_eqv_congr_left z _ _ ih)) ?_
      rw [Q'.pow_succ]
      exact Q'.eqv_symm (Q'.mul_assoc_eqv z (z ^ n) 1)

private theorem monomialPoly_mul (a b : Nat) :
    PolyEqv (pmul (monomialPoly a) (monomialPoly b))
      (monomialPoly (a + b)) := by
  intro z
  refine Q'.eqv_trans _
    (eval (monomialPoly a) z * eval (monomialPoly b) z) _
    (eval_pmul _ _ z) ?_
  refine Q'.eqv_trans _
    (((z ^ a) * 1) * ((z ^ b) * 1)) _
    (Q'.eqv_trans _
      (((z ^ a) * 1) * eval (monomialPoly b) z) _
      (Q'.mul_eqv_congr_right _ _ _ (eval_monomialPoly a z))
      (Q'.mul_eqv_congr_left _ _ _ (eval_monomialPoly b z))) ?_
  refine Q'.eqv_trans _ ((z ^ a) * (z ^ b)) _ (by ring_qeqv) ?_
  refine Q'.eqv_trans _ (z ^ (a + b)) _
    (Q'.eqv_symm (YMGap.Constructive.SU3CharFactor.pow_add_eqv z a b)) ?_
  exact Q'.eqv_symm (Q'.eqv_trans _ ((z ^ (a + b)) * 1) _
    (eval_monomialPoly (a + b) z) (Q'.mul_one_eqv _))

private theorem gaussianExpectationFrom_monomial (s n : Nat) :
    gaussianExpectationFrom s (monomialPoly n) ≈ gaussianMoment1 (s + n) := by
  induction n generalizing s with
  | zero =>
      change (1 * gaussianMoment1 s + 0) ≈ gaussianMoment1 (s + 0)
      refine Q'.eqv_trans _ (gaussianMoment1 s + 0) _
        (Q'.add_eqv_congr_right _ _ _ (Q'.one_mul_eqv _)) ?_
      exact QPoly.q_add_zero_eqv _
  | succ n ih =>
      change (0 * gaussianMoment1 s +
          gaussianExpectationFrom (s + 1) (monomialPoly n)) ≈
        gaussianMoment1 (s + (n + 1))
      refine Q'.eqv_trans _
        (0 + gaussianExpectationFrom (s + 1) (monomialPoly n)) _
        (Q'.add_eqv_congr_right _ _ _ (QPoly.q_zero_mul _)) ?_
      refine Q'.eqv_trans _
        (gaussianExpectationFrom (s + 1) (monomialPoly n)) _
        (QPoly.q_zero_add_eqv _) ?_
      have hi := ih (s + 1)
      have hs : (s + 1) + n = s + (n + 1) := by omega
      rw [hs] at hi
      exact hi

private theorem gaussianPair_monomial (a b : Nat) :
    gaussianPair (monomialPoly a) (monomialPoly b) ≈
      gaussianMoment1 (a + b) := by
  refine Q'.eqv_trans _ (gaussianExpectation (monomialPoly (a + b))) _
    (gaussianExpectation_polyEqv (monomialPoly_mul a b)) ?_
  simpa [gaussianExpectation] using gaussianExpectationFrom_monomial 0 (a + b)

/-- Explicit Hermite feature coordinates of a monomial. -/
def monomialHermiteCoeffs (n : Nat) : List Q' :=
  hermiteExpand (monomialPoly n)

/-- The Gaussian moment kernel is the exact finite Hermite diagonal. -/
theorem gaussianMoment1_add_eq_hermiteDiagonal (a b : Nat) :
    gaussianMoment1 (a + b) ≈
      hermiteDiagonalFrom 0 (monomialHermiteCoeffs a)
        (monomialHermiteCoeffs b) := by
  have ha := hermiteExpand_synthesis (monomialPoly a)
  have hb := hermiteExpand_synthesis (monomialPoly b)
  refine Q'.eqv_trans _
    (gaussianPair (monomialPoly a) (monomialPoly b)) _
    (Q'.eqv_symm (gaussianPair_monomial a b)) ?_
  refine Q'.eqv_trans _
    (gaussianPair (hermiteSynthesisFrom 0 (monomialHermiteCoeffs a))
      (hermiteSynthesisFrom 0 (monomialHermiteCoeffs b))) _
    (gaussianPair_polyEqv ha hb) ?_
  exact hermiteSynthesis_pair 0 _ _

def termAt (p : RatPoly) (i : Nat) : RatTerm :=
  p.getD i ([], 0)

def coordinateHermiteCoeffs (p : RatPoly) (coord i : Nat) : List Q' :=
  monomialHermiteCoeffs (exponentAt (termAt p i).1 coord)

/-- A computable rank which bounds the feature length of every term, including
the default term used outside the finite list. -/
def coordinateHermiteRank (coord : Nat) : RatPoly → Nat
  | [] => (monomialHermiteCoeffs 0).length
  | t :: p => (monomialHermiteCoeffs (exponentAt t.1 coord)).length +
      coordinateHermiteRank coord p

private theorem coordinateHermiteCoeffs_length_le (coord : Nat) :
    ∀ (p : RatPoly) (i : Nat),
      (coordinateHermiteCoeffs p coord i).length ≤ coordinateHermiteRank coord p
  | [], _ => Nat.le_refl _
  | t :: p, 0 => by
      unfold coordinateHermiteCoeffs termAt coordinateHermiteRank
      simp only [List.getD_cons_zero]
      omega
  | t :: p, i + 1 => by
      unfold coordinateHermiteCoeffs termAt coordinateHermiteRank
      simp only [List.getD_cons_succ]
      have ih := coordinateHermiteCoeffs_length_le coord p i
      unfold coordinateHermiteCoeffs termAt at ih
      omega

def coordinateGaussianKernel (p : RatPoly) (coord i j : Nat) : Q' :=
  gaussianMoment1
    (exponentAt (termAt p i).1 coord + exponentAt (termAt p j).1 coord)

private theorem zero_le_hermiteFactorial (n : Nat) :
    (0 : Q') ≤ Q'.ofNat (hermiteFactorial n) := by
  rw [Q'.zero_le_iff_num_nonneg]
  exact Int.natCast_nonneg _

/-- Every coordinate kernel on a finite term list carries an explicit finite
Hermite Gram representation. -/
def coordinateGaussianGramRep (p : RatPoly) (coord : Nat) :
    GramRep (coordinateGaussianKernel p coord) where
  r := coordinateHermiteRank coord p
  d := fun k => Q'.ofNat (hermiteFactorial k)
  hd := zero_le_hermiteFactorial
  v := fun k i => (coordinateHermiteCoeffs p coord i).getD k 0
  hM := by
    intro i j
    let cs := coordinateHermiteCoeffs p coord i
    let ds := coordinateHermiteCoeffs p coord j
    refine Q'.eqv_trans _ (hermiteDiagonalFrom 0 cs ds) _
      (gaussianMoment1_add_eq_hermiteDiagonal _ _) ?_
    refine Q'.eqv_trans _
      (finSum (fun k => (cs.getD k 0 * ds.getD k 0) *
        Q'.ofNat (hermiteFactorial (0 + k))) (coordinateHermiteRank coord p)) _
      (hermiteDiagonalFrom_eq_finSum _ _ _ _
        (coordinateHermiteCoeffs_length_le coord p i)
        (coordinateHermiteCoeffs_length_le coord p j)) ?_
    exact finSum_eqv_congr _ _ (fun k => by
      simpa [cs, ds] using Q'.mul_comm_eqv
        ((coordinateHermiteCoeffs p coord i).getD k 0 *
          (coordinateHermiteCoeffs p coord j).getD k 0)
        (Q'.ofNat (hermiteFactorial k))) (coordinateHermiteRank coord p)

end YMGap.Continuum.SU2QuaternionProductGaussianHermiteGram

#print axioms YMGap.Continuum.SU2QuaternionProductGaussianHermiteGram.gaussianMoment1_add_eq_hermiteDiagonal
#print axioms YMGap.Continuum.SU2QuaternionProductGaussianHermiteGram.coordinateGaussianGramRep
