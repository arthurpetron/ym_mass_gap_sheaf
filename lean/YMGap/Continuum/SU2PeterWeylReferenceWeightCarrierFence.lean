/-
# Carrier fences for a two-boundary SU(2) ReferenceWeight

This file attacks the first concrete inhabitant of
`TwoBoundaryReferenceWeightPositiveTimeRealization` using the existing
fundamental matrix-coefficient plaquette block.  Two independent exact
obstructions show why neither of the tempting class-character carriers is an
observable algebra for the required double-Haar kernel.

1. The retained class span `span{chi_0,chi_1}` is not closed under pointwise
   multiplication: `chi_1^2 = chi_0 + chi_2`, and no two retained coordinates
   represent that square even extensionally.

2. More fundamentally, the relative kernel `K(g h^{-1})` is not a function of
   the two individual conjugacy-class coordinates.  The rational unit
   quaternions `i,i` and `i,j` have identical individual class coordinates
   `(0,0)`, while their relative class coordinates are respectively `1` and
   `0`; the retained Wilson kernel therefore has exact values `3/2` and `1`.

So a genuine `ReferenceWeight` carrier must retain matrix coefficients (or an
equivalent spin-network tensor calculus), not only class characters.  The
final structure gives the smallest non-tautological next interface.  Its
input is an actual `ReferenceWeight`; its weight is required to be the
vacuum-plus-fundamental relative kernel, and its reflected form is required at
the *bare product-Haar numerator* before normalization.  From the separately
proved partition normalization, the interacting `E_Lambda` Schur form is then
derived.  No independent two-mode GNS is declared physical.

All values are exact rationals and all negative results have explicit finite
witnesses.
-/

import YMGap.Continuum.SU2PeterWeylReferenceWeightFidelityFence
import YMGap.Continuum.SU2PeterWeylPlaquetteTensorBlock
import YMGap.Continuum.SU2PeterWeylCharacterPlaquetteEmbedding

namespace YMGap.Continuum.SU2PeterWeylReferenceWeightCarrierFence

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.FiniteVolume
open YMGap.Continuum.ObservableMeasure
open YMGap.Continuum.PlaquetteReweight
open YMGap.Continuum.SU2ClassPolynomialAlgebra
open YMGap.Continuum.SU2PeterWeylWilsonBlock
open YMGap.Continuum.SU2PeterWeylPlaquetteTensorBlock
open YMGap.Continuum.WilsonGNS

local infix:50 " ≈ " => Q'.eqv
local infix:50 " ≈ₚ " => PolyEqv

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl
private theorem zero_num_cast : (0 : Q').num = 0 := rfl
private theorem zero_den_cast : ((0 : Q').den : Int) = 1 := rfl
private theorem one_num_cast : (1 : Q').num = 1 := rfl
private theorem one_den_cast : ((1 : Q').den : Int) = 1 := rfl
private theorem two_num_cast : (2 : Q').num = 2 := rfl
private theorem two_den_cast : ((2 : Q').den : Int) = 1 := rfl
private theorem four_num_cast : (4 : Q').num = 4 := rfl
private theorem four_den_cast : ((4 : Q').den : Int) = 1 := rfl
private theorem eight_num_cast : (8 : Q').num = 8 := rfl
private theorem eight_den_cast : ((8 : Q').den : Int) = 1 := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Q'.mkPos_num,
               Q'.mkPos_den, Q'.ofNat_num_cast, Q'.ofNat_den_cast,
               zero_num_cast, zero_den_cast, one_num_cast, one_den_cast,
               two_num_cast, two_den_cast, four_num_cast, four_den_cast,
               eight_num_cast, eight_den_cast, Int.add_mul, Int.mul_add,
               Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg,
               Int.one_mul, Int.mul_one, Int.zero_mul, Int.mul_zero,
               Int.zero_add, Int.add_zero] <;>
             ac_rfl))

/-! ## The two retained characters are not an algebra -/

/-- The literal class polynomial represented by retained coordinates
`(a_0,a_1)`. -/
def retainedCharacterPoly (a : ModeVec) : Poly :=
  padd (pscale a.1 chi0) (pscale a.2 chi1)

theorem eval_retainedCharacterPoly (a : ModeVec) (x : Q') :
    eval (retainedCharacterPoly a) x ≈ a.1 + (2 * a.2) * x := by
  refine Q'.eqv_trans _
    (eval (pscale a.1 chi0) x + eval (pscale a.2 chi1) x) _
    (eval_padd _ _ x) ?_
  refine Q'.eqv_trans _
    (a.1 * eval chi0 x + a.2 * eval chi1 x) _
    (QPoly.q_add_congr (eval_pscale a.1 chi0 x)
      (eval_pscale a.2 chi1 x)) ?_
  have h0 : eval chi0 x ≈ 1 := by
    refine Q'.eqv_trans _ (Cheb.U 0 x) _ (eval_chi0 x) ?_
    rw [Cheb.U_zero]
    exact Q'.eqv_refl 1
  have h1 : eval chi1 x ≈ 2 * x := by
    refine Q'.eqv_trans _ (Cheb.U 1 x) _ (eval_chi1 x) ?_
    rw [Cheb.U_one]
    exact Q'.eqv_refl (2 * x)
  refine Q'.eqv_trans _ (a.1 * 1 + a.2 * (2 * x)) _
    (QPoly.q_add_congr
      (Q'.mul_eqv_congr_left a.1 _ _ h0)
      (Q'.mul_eqv_congr_left a.2 _ _ h1)) ?_
  ring_qeqv

theorem eval_fundamental_square (x : Q') :
    eval (pmul chi1 chi1) x ≈ 4 * (x * x) := by
  refine Q'.eqv_trans _ (eval chi1 x * eval chi1 x) _
    (eval_pmul chi1 chi1 x) ?_
  have h1 : eval chi1 x ≈ 2 * x := by
    refine Q'.eqv_trans _ (Cheb.U 1 x) _ (eval_chi1 x) ?_
    rw [Cheb.U_one]
    exact Q'.eqv_refl (2 * x)
  refine Q'.eqv_trans _ ((2 * x) * (2 * x)) _
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ h1)
      (Q'.mul_eqv_congr_left (2 * x) _ _ h1)) ?_
  ring_qeqv

theorem retainedFundamental_is_chi1 :
    retainedCharacterPoly fundamentalMode ≈ₚ chi1 := by
  intro x
  refine Q'.eqv_trans _ _ _
    (eval_retainedCharacterPoly fundamentalMode x) ?_
  unfold fundamentalMode
  refine Q'.eqv_trans _ ((2 : Q') * x) _ (by ring_qeqv) ?_
  exact Q'.eqv_symm (eval_chi1 x)

/-- No retained coordinate pair represents the fundamental square, even as
an extensional polynomial.  The witnesses `x=0,1,-1` force the inconsistent
identity `0 = 8`. -/
theorem fundamental_square_not_retained (a : ModeVec) :
    ¬ (retainedCharacterPoly a ≈ₚ pmul chi1 chi1) := by
  intro h
  have hAt (x : Q') : a.1 + (2 * a.2) * x ≈ 4 * (x * x) :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (eval_retainedCharacterPoly a x))
      (Q'.eqv_trans _ _ _ (h x) (eval_fundamental_square x))
  have h0raw := hAt (0 : Q')
  have h1raw := hAt (1 : Q')
  have hm1raw := hAt (-1 : Q')
  have h0left : a.1 ≈ a.1 + (2 * a.2) * 0 := by ring_qeqv
  have h0right : 4 * ((0 : Q') * 0) ≈ 0 := by ring_qeqv
  have h0 : a.1 ≈ 0 :=
    Q'.eqv_trans _ _ _ h0left (Q'.eqv_trans _ _ _ h0raw h0right)
  have h1left : a.1 + 2 * a.2 ≈ a.1 + (2 * a.2) * 1 := by ring_qeqv
  have h1right : 4 * ((1 : Q') * 1) ≈ 4 := by ring_qeqv
  have h1 : a.1 + 2 * a.2 ≈ 4 :=
    Q'.eqv_trans _ _ _ h1left (Q'.eqv_trans _ _ _ h1raw h1right)
  have hm1left : a.1 + -(2 * a.2) ≈
      a.1 + (2 * a.2) * (-1 : Q') := by ring_qeqv
  have hm1right : 4 * ((-1 : Q') * (-1)) ≈ 4 := by ring_qeqv
  have hm1 : a.1 + -(2 * a.2) ≈ 4 :=
    Q'.eqv_trans _ _ _ hm1left (Q'.eqv_trans _ _ _ hm1raw hm1right)
  have hsum :
      (a.1 + 2 * a.2) + (a.1 + -(2 * a.2)) ≈ 4 + 4 :=
    Q'.add_eqv_congr' h1 hm1
  have hreplace :
      (a.1 + 2 * a.2) + (a.1 + -(2 * a.2)) ≈
        (0 + 2 * a.2) + (0 + -(2 * a.2)) :=
    Q'.add_eqv_congr'
      (Q'.add_eqv_congr' h0 (Q'.eqv_refl _))
      (Q'.add_eqv_congr' h0 (Q'.eqv_refl _))
  have hcancel :
      ((0 : Q') + 2 * a.2) + (0 + -(2 * a.2)) ≈ 0 := by
    refine Q'.eqv_trans _ ((2 : Q') * a.2 + -(2 * a.2)) _ ?_ ?_
    · exact Q'.add_eqv_congr'
        (QPoly.q_zero_add_eqv (2 * a.2))
        (QPoly.q_zero_add_eqv (-(2 * a.2)))
    · exact Q'.add_neg_self_eqv (2 * a.2)
  have hsumRight : (4 : Q') + 4 ≈ 8 := by ring_qeqv
  have hbad : (0 : Q') ≈ 8 :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm hcancel)
      (Q'.eqv_trans _ _ _ (Q'.eqv_symm hreplace)
        (Q'.eqv_trans _ _ _ hsum hsumRight))
  exact (by decide : ¬ ((0 : Q') ≈ 8)) hbad

/-- What would be needed to use the retained two-character coordinates as a
pointwise observable algebra. -/
structure RetainedCharacterPointwiseClosure : Type where
  mulCoordinate : ModeVec → ModeVec → ModeVec
  mul_correct : ∀ a b,
    retainedCharacterPoly (mulCoordinate a b) ≈ₚ
      pmul (retainedCharacterPoly a) (retainedCharacterPoly b)

/-- Kernel-checked closure obstruction: the retained two-character carrier
cannot inherit pointwise multiplication. -/
theorem no_retained_character_pointwise_closure :
    ¬ Nonempty RetainedCharacterPointwiseClosure := by
  intro h
  obtain ⟨C⟩ := h
  apply fundamental_square_not_retained
    (C.mulCoordinate fundamentalMode fundamentalMode)
  exact peqv_trans (C.mul_correct fundamentalMode fundamentalMode)
    (pmul_congr retainedFundamental_is_chi1 retainedFundamental_is_chi1)

/-! ## Individual class coordinates do not determine `K(g h^{-1})` -/

/-- Rational quaternion coordinates for the two exact SU(2) witnesses. -/
abbrev RationalSU2Point := Q' × (Q' × (Q' × Q'))

def quatNormSq (q : RationalSU2Point) : Q' :=
  q.1 * q.1 +
    (q.2.1 * q.2.1 +
      (q.2.2.1 * q.2.2.1 + q.2.2.2 * q.2.2.2))

/-- Conjugacy-class coordinate (`cos theta`), the scalar quaternion part. -/
def classCoordinate (q : RationalSU2Point) : Q' := q.1

/-- Scalar part of `g h^{-1}` for unit quaternions: the Euclidean dot
product of their four rational coordinates. -/
def relativeClassCoordinate (g h : RationalSU2Point) : Q' :=
  g.1 * h.1 +
    (g.2.1 * h.2.1 +
      (g.2.2.1 * h.2.2.1 + g.2.2.2 * h.2.2.2))

def quatI : RationalSU2Point := (0, (1, (0, 0)))
def quatJ : RationalSU2Point := (0, (0, (1, 0)))

theorem quatI_unit : quatNormSq quatI ≈ 1 := by decide
theorem quatJ_unit : quatNormSq quatJ ≈ 1 := by decide

theorem witness_individual_classes_same :
    classCoordinate quatI = classCoordinate quatJ ∧
      classCoordinate quatI = (0 : Q') := by
  exact ⟨rfl, rfl⟩

theorem relative_II_exact : relativeClassCoordinate quatI quatI ≈ 1 := by decide
theorem relative_IJ_exact : relativeClassCoordinate quatI quatJ ≈ 0 := by decide

def threeHalves : Q' := Q'.mkPos 3 2 (by decide)

theorem relativeKernel_II_exact :
    eval interactionKernel (relativeClassCoordinate quatI quatI) ≈
      threeHalves := by decide

theorem relativeKernel_IJ_exact :
    eval interactionKernel (relativeClassCoordinate quatI quatJ) ≈ 1 := by decide

/-- A proposed encoding of the relative Wilson kernel by only the two
individual class coordinates. -/
def ClassPairRepresentsRelativeKernel (F : Q' → Q' → Q') : Prop :=
  ∀ g h : RationalSU2Point,
    quatNormSq g ≈ 1 → quatNormSq h ≈ 1 →
      F (classCoordinate g) (classCoordinate h) ≈
        eval interactionKernel (relativeClassCoordinate g h)

/-- Exact quaternion witness that class-by-class carriers cannot encode
`K(g h^{-1})`.  Matrix coefficients or equivalent tensor data are necessary. -/
theorem no_individual_class_pair_kernel (F : Q' → Q' → Q') :
    ¬ ClassPairRepresentsRelativeKernel F := by
  intro h
  have hii := h quatI quatI quatI_unit quatI_unit
  have hij := h quatI quatJ quatI_unit quatJ_unit
  have hbad : threeHalves ≈ (1 : Q') :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm relativeKernel_II_exact)
      (Q'.eqv_trans _ _ _ (Q'.eqv_symm hii)
        (Q'.eqv_trans _ _ _ hij relativeKernel_IJ_exact))
  exact (by decide : ¬ (threeHalves ≈ (1 : Q'))) hbad

/-! ## Minimal matrix-coefficient/tensor ReferenceWeight interface -/

/-- The next honest carrier target after the two exact fences.

`boundary` realizes the five existing Peter--Weyl coordinates
`(1,D00,D01,D10,D11)` inside a genuine observable algebra.  `theta` is the
two-boundary reflection.  The weight is explicitly the retained relative
kernel `1 + (1/4) chi_1(g h^{-1})`; it is not defined from `plaquetteGNS`.
Finally `bare_doubleHaar_schur` is stated on `R.I0` before normalization, so
the physical form is derived from the same product-Haar numerator and weight.

The missing inhabitant must construct `A`, its full multiplication closure,
the product-Haar `I0`, the relative matrix coefficient, and the displayed
Schur identity. -/
structure FundamentalMatrixTensorReferenceWeight
    {A : ObsAlg} (R : ReferenceWeight A) (M : WilsonGNSData.CarrierModule A) : Type where
  theta : A.carrier → A.carrier
  boundary : PlaquetteVec → A.carrier
  D00 : A.carrier
  D01 : A.carrier
  D10 : A.carrier
  D11 : A.carrier
  relativeFundamentalCharacter : A.carrier
  boundary_vacuum : boundary SU2PeterWeylPlaquetteTensorBlock.vacuumMode = A.one
  boundary_D00 : boundary matrix00Mode = D00
  boundary_D01 : boundary matrix01Mode = D01
  boundary_D10 : boundary matrix10Mode = D10
  boundary_D11 : boundary matrix11Mode = D11
  boundary_map_veq : ∀ {a b}, plaquetteGNS.veq a b → M.veq (boundary a) (boundary b)
  boundary_map_add : ∀ a b, M.veq (boundary (plaquetteGNS.add a b))
    (M.add (boundary a) (boundary b))
  boundary_map_smul : ∀ s a, M.veq (boundary (plaquetteGNS.smul s a))
    (M.smul s (boundary a))
  retained_relative_weight :
    M.veq R.w
      (M.add A.one (M.smul quarter relativeFundamentalCharacter))
  partition_exact : R.Z = (1 : Q')
  bare_doubleHaar_schur : ∀ a b,
    R.I₀.E (A.mul R.w (A.mul (theta (boundary a)) (boundary b))) ≈
      plaquetteGram a b

namespace FundamentalMatrixTensorReferenceWeight

variable {A : ObsAlg} {R : ReferenceWeight A} {M : WilsonGNSData.CarrierModule A}
    (X : FundamentalMatrixTensorReferenceWeight R M)

/-- Once the explicit product-Haar numerator is constructed, partition
normalization derives the interacting reflected form. -/
theorem interacting_reflected_schur (a b : PlaquetteVec) :
    R.E_Λ (A.mul (X.theta (X.boundary a)) (X.boundary b)) ≈
      plaquetteGNS.B a b := by
  change
    (R.I₀.E (A.mul R.w (A.mul (X.theta (X.boundary a)) (X.boundary b))) *
      recip R.Z) ≈ plaquetteGNS.B a b
  rw [X.partition_exact, recip_one]
  refine Q'.eqv_trans _ _ _ (Q'.mul_one_eqv _) ?_
  exact Q'.eqv_trans _ _ _ (X.bare_doubleHaar_schur a b)
    (Q'.eqv_symm (plaquetteGNS_B_eq_gram a b))

end FundamentalMatrixTensorReferenceWeight

end YMGap.Continuum.SU2PeterWeylReferenceWeightCarrierFence

#print axioms YMGap.Continuum.SU2PeterWeylReferenceWeightCarrierFence.fundamental_square_not_retained
#print axioms YMGap.Continuum.SU2PeterWeylReferenceWeightCarrierFence.no_retained_character_pointwise_closure
#print axioms YMGap.Continuum.SU2PeterWeylReferenceWeightCarrierFence.quatI_unit
#print axioms YMGap.Continuum.SU2PeterWeylReferenceWeightCarrierFence.quatJ_unit
#print axioms YMGap.Continuum.SU2PeterWeylReferenceWeightCarrierFence.relativeKernel_II_exact
#print axioms YMGap.Continuum.SU2PeterWeylReferenceWeightCarrierFence.relativeKernel_IJ_exact
#print axioms YMGap.Continuum.SU2PeterWeylReferenceWeightCarrierFence.no_individual_class_pair_kernel
#print axioms YMGap.Continuum.SU2PeterWeylReferenceWeightCarrierFence.FundamentalMatrixTensorReferenceWeight.interacting_reflected_schur
