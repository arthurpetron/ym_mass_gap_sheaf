/-
# The first missing Clebsch--Gordan channel in the plaquette carrier

`SU2PeterWeylPlaquetteTensorBlock` supplies the exact five-dimensional linear
carrier

    1 + (D00,D01,D10,D11)

and its double-Schur reflected form.  To serve as the carrier of an actual
`ReferenceWeight`, however, it must sit inside a multiplication-closed
observable algebra.  This file tests the strongest possible version of using
those five coordinates alone.

On diagonal conjugacy representatives, the trace `D00+D11` restricts to the
fundamental class character `chi_1`.  Therefore any pointwise multiplication
on the five-coordinate carrier compatible with restriction to class
functions would make the retained class span multiplication-closed.  The
already-proved exact character fence rules this out.  Equivalently, the
Clebsch--Gordan table says

    1 tensor 1 = 0 + 2

in doubled-spin labels: the square of the fundamental sector has a nonzero
spin-2 channel.  The five-coordinate `0+1` carrier contains no such channel.

This is the first exact obstruction encountered when constructing the
concrete algebra/functional requested by
`FundamentalMatrixTensorReferenceWeight`; it occurs before partition
normalization or weighted positivity.  A viable carrier must add at least the
nine matrix coefficients of the spin-2 sector, and iterated multiplication
then requires the full finite-support Peter--Weyl/spin-network algebra.

The result is a closure obstruction, not a claim that the existing linear GNS
block is incorrectly normalized.
-/

import YMGap.Continuum.SU2PeterWeylReferenceWeightCarrierFence
import YMGap.Continuum.TemperleyLiebRecoupling

namespace YMGap.Continuum.SU2PeterWeylPlaquetteAlgebraClosureFence

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SU2ClassPolynomialAlgebra
open YMGap.Continuum.SU2PeterWeylPlaquetteTensorBlock
open YMGap.Continuum.SU2PeterWeylReferenceWeightCarrierFence
open YMGap.Continuum.SU2PeterWeylWilsonBlock

local infix:50 " ≈ " => Q'.eqv
local infix:50 " ≈ₚ " => PolyEqv

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl
private theorem zero_num_cast : (0 : Q').num = 0 := rfl
private theorem zero_den_cast : ((0 : Q').den : Int) = 1 := rfl
private theorem one_num_cast : (1 : Q').num = 1 := rfl
private theorem one_den_cast : ((1 : Q').den : Int) = 1 := rfl
private theorem two_num_cast : (2 : Q').num = 2 := rfl
private theorem two_den_cast : ((2 : Q').den : Int) = 1 := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Q'.mkPos_num,
               Q'.mkPos_den, Q'.ofNat_num_cast, Q'.ofNat_den_cast,
               zero_num_cast, zero_den_cast, one_num_cast, one_den_cast,
               two_num_cast, two_den_cast, Int.add_mul, Int.mul_add,
               Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg,
               Int.one_mul, Int.mul_one, Int.zero_mul, Int.mul_zero,
               Int.zero_add, Int.add_zero] <;>
             ac_rfl))

def half : Q' := Q'.mkPos 1 2 (by decide)

/-- Class coordinates of a five-component matrix-coefficient vector.  The
off-diagonal matrix coefficients vanish under the central trace restriction;
the average of the two diagonal coefficients multiplies `chi_1`. -/
def plaquetteClassMode (a : PlaquetteVec) : ModeVec :=
  (a.1, half * (a.2.1 + a.2.2.2.2))

def plaquetteClassRestriction (a : PlaquetteVec) : Poly :=
  retainedCharacterPoly (plaquetteClassMode a)

/-- The cut-plaquette vacuum restricts to the trivial character. -/
theorem vacuum_class_restriction :
    plaquetteClassRestriction SU2PeterWeylPlaquetteTensorBlock.vacuumMode ≈ₚ
      chi0 := by
  intro x
  refine Q'.eqv_trans _ _ _
    (eval_retainedCharacterPoly
      (plaquetteClassMode SU2PeterWeylPlaquetteTensorBlock.vacuumMode) x) ?_
  refine Q'.eqv_trans _ (1 : Q') _ (by
    unfold plaquetteClassMode SU2PeterWeylPlaquetteTensorBlock.vacuumMode half
    ring_qeqv) ?_
  exact Q'.eqv_symm (Q'.eqv_trans _ _ _ (eval_chi0 x) (by
    rw [Cheb.U_zero]
    exact Q'.eqv_refl 1))

/-- The literal trace vector `D00+D11` restricts to `chi_1`. -/
theorem fundamentalCharacter_class_restriction :
    plaquetteClassRestriction fundamentalCharacterMode ≈ₚ chi1 := by
  intro x
  refine Q'.eqv_trans _ _ _
    (eval_retainedCharacterPoly
      (plaquetteClassMode fundamentalCharacterMode) x) ?_
  have hc : half * ((1 : Q') + 1) ≈ 1 := by decide
  refine Q'.eqv_trans _ (0 + ((2 : Q') * 1) * x) _ ?_ ?_
  · unfold plaquetteClassMode fundamentalCharacterMode
    exact QPoly.q_add_congr (Q'.eqv_refl 0)
      (Q'.mul_eqv_congr_right _ _ x
        (Q'.mul_eqv_congr_left 2 _ _ hc))
  · refine Q'.eqv_trans _ ((2 : Q') * x) _ ?_
      (Q'.eqv_symm (eval_chi1 x))
    refine Q'.eqv_trans _ (((2 : Q') * 1) * x) _
      (QPoly.q_zero_add_eqv _) ?_
    exact Q'.mul_eqv_congr_right _ _ x (Q'.mul_one_eqv 2)

/-- A proposed pointwise observable algebra structure on exactly the existing
five coordinates, together with the indispensable compatibility of
multiplication with restriction to class functions.  The algebraic laws are
not even requested: the weak multiplication compatibility already fails. -/
structure FiveCoordinateClassCompatibleProduct : Type where
  one : PlaquetteVec
  star : PlaquetteVec → PlaquetteVec
  mul : PlaquetteVec → PlaquetteVec → PlaquetteVec
  one_is_vacuum : one = SU2PeterWeylPlaquetteTensorBlock.vacuumMode
  class_mul : ∀ a b,
    plaquetteClassRestriction (mul a b) ≈ₚ
      pmul (plaquetteClassRestriction a) (plaquetteClassRestriction b)

/-- The five-coordinate plaquette tensor cannot itself be the multiplication
closed carrier of the physical `ReferenceWeight`. -/
theorem no_fiveCoordinate_classCompatible_product :
    ¬ Nonempty FiveCoordinateClassCompatibleProduct := by
  intro h
  obtain ⟨A⟩ := h
  apply fundamental_square_not_retained
    (plaquetteClassMode
      (A.mul fundamentalCharacterMode fundamentalCharacterMode))
  exact peqv_trans
    (A.class_mul fundamentalCharacterMode fundamentalCharacterMode)
    (pmul_congr fundamentalCharacter_class_restriction
      fundamentalCharacter_class_restriction)

/-! ## Exact first missing channel -/

/-- The complete fundamental self-fusion support through the first four
channels.  Both the vacuum and spin-2 channels occur with coefficient one;
the spin-1 and spin-3 channels vanish. -/
theorem fundamental_selfFusion_support :
    (fusionInd 1 1 0 ≈ 1) ∧ (fusionInd 1 1 2 ≈ 1) ∧
      (fusionInd 1 1 1 ≈ 0) ∧ (fusionInd 1 1 3 ≈ 0) := by
  decide

/-- Polynomial spelling of the same obstruction: the missing term is exactly
the nontrivial `chi_2` channel, not a normalization artefact. -/
theorem fundamental_square_exposes_spinTwo :
    pmul chi1 chi1 ≈ₚ padd chi0 chi2 :=
  chi1_sq_fusion

/-- Minimal dimension count for the first multiplication-closed enlargement:
one vacuum coefficient, four fundamental coefficients, and nine spin-2
matrix coefficients. -/
def firstCGClosedCoordinateCount : Nat := 1 + 4 + 9

theorem firstCGClosedCoordinateCount_exact :
    firstCGClosedCoordinateCount = 14 := by decide

end YMGap.Continuum.SU2PeterWeylPlaquetteAlgebraClosureFence

#print axioms YMGap.Continuum.SU2PeterWeylPlaquetteAlgebraClosureFence.vacuum_class_restriction
#print axioms YMGap.Continuum.SU2PeterWeylPlaquetteAlgebraClosureFence.fundamentalCharacter_class_restriction
#print axioms YMGap.Continuum.SU2PeterWeylPlaquetteAlgebraClosureFence.no_fiveCoordinate_classCompatible_product
#print axioms YMGap.Continuum.SU2PeterWeylPlaquetteAlgebraClosureFence.fundamental_selfFusion_support
#print axioms YMGap.Continuum.SU2PeterWeylPlaquetteAlgebraClosureFence.fundamental_square_exposes_spinTwo
#print axioms YMGap.Continuum.SU2PeterWeylPlaquetteAlgebraClosureFence.firstCGClosedCoordinateCount_exact
