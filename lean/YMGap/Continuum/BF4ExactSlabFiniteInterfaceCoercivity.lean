/-
# Explicit finite-cutoff comparison for the ORIGINAL crossing interface

Keep the same lower polynomial p, the same shared link variables and the
same spin cutoff K. Only the crossing heat coefficients vary. If 0<w<=1,
the actual reflected Gram-interface forms obey
  w^(K*(K+2)*F) Q_1(p) <= Q_w(p) <= Q_1(p),
up to rational equivalence, where F is the actual crossing-face count.
The positive lower factor is computed, not opaque. Thus at finite K the
two forms have exactly the same null polynomials. Q_1 is the SAME finite
Gram expansion at nome one, NOT a normalized infinite heat law at w=1.

The observable may contain the actual lower bulk dressing, but it must
remain the SAME polynomial in both compared forms. This does not compare
two differently dressed Gibbs laws. The factor depends on K, w and slab
extent; no cutoff/volume/beta-uniform lower bound is claimed. Gluing this
interface to the actual completed T2 and controlling the limits remain
open, as do full original range density, time-zero continuity, physical
Hamiltonian identification, continuum and Clay.
-/

import YMGap.Continuum.BF4ExactSlabSquareWeightComparison
import YMGap.Continuum.BF4ExactSlabAllExtentSpatialGramPositivity
import YMGap.Continuum.HeatKernelRGStep

namespace YMGap.Continuum.BF4ExactSlabFiniteInterfaceCoercivity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelRGStep (qpow_antitone qpow_qpow)
open YMGap.Continuum.BondMovingStep (coeffW)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.BF4ExactSlabReflectedSquareAlgebra
open YMGap.Continuum.BF4ExactSlabAllCutoffReflectionPositivity
open YMGap.Continuum.BF4ExactSlabLocalSquareExpansion
open YMGap.Continuum.BF4ExactSlabLowerHaarFactorization
open YMGap.Continuum.BF4ExactSlabAllExtentSpatialGramPositivity
open YMGap.Continuum.BF4ExactSlabSquareWeightComparison
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState

local infix:50 " ≈ " => Q'.eqv

private theorem power_one : ∀ n, qpow (1 : Q') n ≈ 1
  | 0 => Q'.eqv_refl _
  | n+1 => Q'.eqv_trans _ _ _ (Q'.mul_one_eqv _) (power_one n)

private theorem power_positive (w : Q') (hw : (0 : Q') < w) : ∀ n, (0 : Q') < qpow w n
  | 0 => by change (0 : Q') < 1; decide
  | n+1 => Q'.mul_pos (power_positive w hw n) hw

def coefficientFloor (w : Q') (K : Nat) : Q' := qpow w (c4 K)

theorem coefficientFloor_positive (w : Q') (hw : (0 : Q') < w) (K : Nat) :
    (0 : Q') < coefficientFloor w K := power_positive w hw (c4 K)

theorem unit_coefficient (s : Nat) : coeffW 1 s ≈ dimQ s :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (power_one (c4 s))) (Q'.mul_one_eqv _)

theorem coefficient_lower (w : Q') (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (K s : Nat) (hs : s ≤ K) : coefficientFloor w K * coeffW 1 s ≤ coeffW w s := by
  have hc : c4 s ≤ c4 K := Nat.mul_le_mul hs (Nat.add_le_add_right hs 2)
  have he : coefficientFloor w K * coeffW 1 s ≈ dimQ s * coefficientFloor w K :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (unit_coefficient s)) (Q'.mul_comm_eqv _ _)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
    (Q'.mul_le_mul_of_nonneg_left _ _ (dimQ s) (qpow_antitone hw0 hw1 _ _ hc) (dimQ_nonneg s))

theorem coefficient_upper (w : Q') (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (s : Nat) : coeffW w s ≤ coeffW 1 s := by
  have hp : qpow w (c4 s) ≤ (1 : Q') := qpow_antitone hw0 hw1 0 (c4 s) (Nat.zero_le _)
  have h := Q'.mul_le_mul_of_nonneg_left _ _ (dimQ s) hp (dimQ_nonneg s)
  exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv
    (Q'.eqv_trans _ _ _ (Q'.mul_one_eqv _) (Q'.eqv_symm (unit_coefficient s))))

theorem face_weight_bound (a b c : Q') (ha : (0 : Q') ≤ a) (hb : (0 : Q') ≤ b)
    (K : Nat) {half id : Nat} (hi : id ∈ centralFixedFaceIds half)
    (hcoeff : ∀ s, s ≤ K → c * coeffW a s ≤ coeffW b s) :
    WeightBound c (faceExpansion ha K hi).tree (faceExpansion hb K hi).tree := by
  unfold faceExpansion
  apply WeightBound.finiteSum
  intro s hs
  apply WeightBound.scaled
  · exact gramSquares_nonnegative _ s
  · rw [coeffAt_heatKernelPacket (List.mem_range.mp hs), coeffAt_heatKernelPacket (List.mem_range.mp hs)]
    exact hcoeff s (by have h := List.mem_range.mp hs; omega)

theorem interface_weight_bound (a b c : Q') (ha : (0 : Q') ≤ a) (hb : (0 : Q') ≤ b)
    (hc : (0 : Q') ≤ c) (K half : Nat)
    (hcoeff : ∀ s, s ≤ K → c * coeffW a s ≤ coeffW b s) :
    WeightBound (qpow c (centralFixedFaceIds half).length)
      (interfaceExpansion ha K half).tree (interfaceExpansion hb K half).tree := by
  unfold interfaceExpansion
  apply WeightBound.finiteProduct c hc
  exact fun _ hi => face_weight_bound a b c ha hb K hi hcoeff

/-- The actual finite reflected crossing form; no partition normalization. -/
def interfaceForm (w : Q') (K half : Nat) (p : RatPoly) : Q' :=
  quaternionHaar (boundaryCompleteSlabLinks (centralExtent half)).length
    (reflectedInterfacePolynomial w K half p)

theorem interfaceForm_nonnegative (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks (centralExtent half)).length p)
    (hl : LowerLocal half p) : (0 : Q') ≤ interfaceForm w K half p :=
  reflectedInterface_nonnegative hw K half p hp hl

theorem interface_form_comparison (a b c : Q') (ha : (0 : Q') ≤ a) (hb : (0 : Q') ≤ b)
    (hc : (0 : Q') ≤ c) (K half : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks (centralExtent half)).length p)
    (hl : LowerLocal half p) (hcoeff : ∀ s, s ≤ K → c * coeffW a s ≤ coeffW b s) :
    qpow c (centralFixedFaceIds half).length * interfaceForm a K half p ≤ interfaceForm b K half p := by
  let A := reflectedInterfaceExpansion ha K half p hp hl
  let B := reflectedInterfaceExpansion hb K half p hp hl
  let R := LocalSquareExpansion.reflectedSquare half p hp hl
  have hI := interface_weight_bound a b c ha hb hc K half hcoeff
  have hprod := WeightBound.product (WeightBound.refl R.tree) hI
    (interfaceExpansion ha K half).weightsNonnegative R.weightsNonnegative
    (qpow_nonneg c hc (centralFixedFaceIds half).length)
  have htree : WeightBound (qpow c (centralFixedFaceIds half).length) A.tree B.tree :=
    hprod.change_factor (Q'.eqv_symm (Q'.one_mul_eqv _))
  have hvalue := htree.haar_bound (boundaryCompleteSlabLinks (centralExtent half)).length
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ A.haar_eq_squareValue))
    (Q'.le_trans' _ _ _ hvalue (Q'.ge_of_eqv B.haar_eq_squareValue))

def interfaceFloor (w : Q') (K half : Nat) : Q' :=
  qpow (coefficientFloor w K) (centralFixedFaceIds half).length

theorem interfaceFloor_positive (w : Q') (hw : (0 : Q') < w) (K half : Nat) :
    (0 : Q') < interfaceFloor w K half :=
  power_positive _ (coefficientFloor_positive w hw K) _

/-- Both the cutoff Casimir and the actual crossing-face count are explicit. -/
theorem interfaceFloor_exponent (w : Q') (K half : Nat) :
    interfaceFloor w K half ≈ qpow w (K*(K+2)*(centralFixedFaceIds half).length) :=
  qpow_qpow w (c4 K) (centralFixedFaceIds half).length

theorem interface_form_lower (w : Q') (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (K half : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks (centralExtent half)).length p)
    (hl : LowerLocal half p) :
    interfaceFloor w K half * interfaceForm 1 K half p ≤ interfaceForm w K half p :=
  interface_form_comparison 1 w (coefficientFloor w K) (by decide) hw0
    (qpow_nonneg w hw0 (c4 K)) K half p hp hl (coefficient_lower w hw0 hw1 K)

theorem interface_form_upper (w : Q') (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (K half : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks (centralExtent half)).length p)
    (hl : LowerLocal half p) : interfaceForm w K half p ≤ interfaceForm 1 K half p := by
  have h := interface_form_comparison w 1 1 hw0 (by decide) (by decide) K half p hp hl
    (fun s _ => Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.one_mul_eqv _)) (coefficient_upper w hw0 hw1 s))
  have he : qpow (1 : Q') (centralFixedFaceIds half).length * interfaceForm w K half p ≈
      interfaceForm w K half p := Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ (power_one _)) (Q'.one_mul_eqv _)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv he) h

/-- Finite-interface nullity is unchanged by strictly positive heat weights.
The polynomial and its bulk dressing, if any, stay fixed. -/
theorem interface_form_zero_iff (w : Q') (hw0 : (0 : Q') < w) (hw1 : w ≤ (1 : Q'))
    (K half : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks (centralExtent half)).length p)
    (hl : LowerLocal half p) : interfaceForm w K half p ≈ 0 ↔ interfaceForm 1 K half p ≈ 0 := by
  constructor
  · intro hz
    apply Q'.mul_eqv_zero_of_pos (interfaceFloor_positive w hw0 K half)
    apply TrigAdd.eqv_of_le_of_le
    · exact Q'.le_trans' _ _ _ (interface_form_lower w (Q'.le_of_lt hw0) hw1 K half p hp hl)
        (Q'.le_of_eqv hz)
    · exact Q'.mul_nonneg _ _ (Q'.le_of_lt (interfaceFloor_positive w hw0 K half))
        (interfaceForm_nonnegative 1 (by decide) K half p hp hl)
  · intro hz
    exact TrigAdd.eqv_of_le_of_le
      (Q'.le_trans' _ _ _ (interface_form_upper w (Q'.le_of_lt hw0) hw1 K half p hp hl) (Q'.le_of_eqv hz))
      (interfaceForm_nonnegative w (Q'.le_of_lt hw0) K half p hp hl)

/-- Both finite form bounds and the positive, explicit factor are retained. -/
def interfaceComparisonCertificate (w : Q') (hw0 : (0 : Q') < w) (hw1 : w ≤ (1 : Q'))
    (K half : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks (centralExtent half)).length p)
    (hl : LowerLocal half p) :
    Σ' rho : Q', ((0 : Q') < rho) ×'
      (rho * interfaceForm 1 K half p ≤ interfaceForm w K half p) ×'
      (interfaceForm w K half p ≤ interfaceForm 1 K half p) ×'
      (rho ≈ qpow w (K*(K+2)*(centralFixedFaceIds half).length)) :=
  ⟨interfaceFloor w K half, interfaceFloor_positive w hw0 K half,
    interface_form_lower w (Q'.le_of_lt hw0) hw1 K half p hp hl,
    interface_form_upper w (Q'.le_of_lt hw0) hw1 K half p hp hl,
    interfaceFloor_exponent w K half⟩

end YMGap.Continuum.BF4ExactSlabFiniteInterfaceCoercivity

#print axioms YMGap.Continuum.BF4ExactSlabFiniteInterfaceCoercivity.coefficientFloor
#print axioms YMGap.Continuum.BF4ExactSlabFiniteInterfaceCoercivity.coefficientFloor_positive
#print axioms YMGap.Continuum.BF4ExactSlabFiniteInterfaceCoercivity.unit_coefficient
#print axioms YMGap.Continuum.BF4ExactSlabFiniteInterfaceCoercivity.coefficient_lower
#print axioms YMGap.Continuum.BF4ExactSlabFiniteInterfaceCoercivity.coefficient_upper
#print axioms YMGap.Continuum.BF4ExactSlabFiniteInterfaceCoercivity.face_weight_bound
#print axioms YMGap.Continuum.BF4ExactSlabFiniteInterfaceCoercivity.interface_weight_bound
#print axioms YMGap.Continuum.BF4ExactSlabFiniteInterfaceCoercivity.interfaceForm
#print axioms YMGap.Continuum.BF4ExactSlabFiniteInterfaceCoercivity.interfaceForm_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFiniteInterfaceCoercivity.interface_form_comparison
#print axioms YMGap.Continuum.BF4ExactSlabFiniteInterfaceCoercivity.interfaceFloor
#print axioms YMGap.Continuum.BF4ExactSlabFiniteInterfaceCoercivity.interfaceFloor_positive
#print axioms YMGap.Continuum.BF4ExactSlabFiniteInterfaceCoercivity.interfaceFloor_exponent
#print axioms YMGap.Continuum.BF4ExactSlabFiniteInterfaceCoercivity.interface_form_lower
#print axioms YMGap.Continuum.BF4ExactSlabFiniteInterfaceCoercivity.interface_form_upper
#print axioms YMGap.Continuum.BF4ExactSlabFiniteInterfaceCoercivity.interface_form_zero_iff
#print axioms YMGap.Continuum.BF4ExactSlabFiniteInterfaceCoercivity.interfaceComparisonCertificate
