/-
# Computed remainder bounds for the ORIGINAL plaquette heat factors

Every original finite faceHeatPolynomial is literally its heat-character
prefix. Increasing the cutoff appends a computed polynomial remainder whose
coefficient L1 and exact Haar integral have a quantified tail bound for each
rational 0 < w < 1. The cutoff depends on w, extent, face and tolerance.

The small norm belongs to the remainder, not to the unreduced syntactic
difference of two prefixes: coefficient L1 is not invariant under polynomial
cancellation. The literal prefix-plus-remainder identity is therefore part
of the delivered certificate. Product bounds for the full heat-dressed unit,
its GNS Cauchy modulus and physical stationarity remain open.
-/

import YMGap.Continuum.BF4ExactSlabAllExtentHeatUnit
import YMGap.Continuum.SU2HeatCharacterPolynomialTail

namespace YMGap.Continuum.BF4ExactSlabAllExtentFaceHeatTail

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2HeatCharacterPolynomialMajorant
open YMGap.Continuum.SU2HeatCharacterPolynomialTail
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

private theorem sum_append {A : Type} (f : A → RatPoly) : ∀ xs ys : List A,
    finitePolySum f (xs ++ ys) = polyAdd (finitePolySum f xs) (finitePolySum f ys)
  | [], _ => rfl
  | _ :: xs, ys => by simp only [List.cons_append, finitePolySum, sum_append f xs ys, polyAdd, List.append_assoc]

private theorem sum_map {A B : Type} (f : B → RatPoly) (g : A → B) : ∀ xs : List A,
    finitePolySum f (xs.map g) = finitePolySum (fun a => f (g a)) xs
  | [] => rfl
  | _ :: xs => by simp only [List.map_cons, finitePolySum, sum_map f g xs]

private theorem sum_congr_on {A : Type} (f g : A → RatPoly) : ∀ xs : List A,
    (∀ a, a ∈ xs → f a = g a) → finitePolySum f xs = finitePolySum g xs
  | [], _ => rfl
  | a :: xs, h => by
    change polyAdd (f a) (finitePolySum f xs) = polyAdd (g a) (finitePolySum g xs)
    rw [h a List.mem_cons_self, sum_congr_on f g xs (fun b hb => h b (List.mem_cons_of_mem a hb))]

theorem coefficientL1_sum_range (f : Nat → RatPoly) : ∀ count : Nat,
    polynomialCoefficientL1 (finitePolySum f (List.range count)) ≈
      finSum (fun i => polynomialCoefficientL1 (f i)) count
  | 0 => Q'.eqv_refl 0
  | count + 1 => by
    rw [List.range_succ, sum_append]
    exact Q'.eqv_trans _ _ _ (coefficientL1_add _ _)
      (Q'.add_eqv_congr' (coefficientL1_sum_range f count)
        (by simp only [finitePolySum, polyAdd, polyZero, List.append_nil]; exact Q'.eqv_refl _))

def faceScalar (extent id : Nat) : RatPoly :=
  (correctedSlabPlaquettePolynomial extent (slabPlaquetteAt extent id)).scalar

def faceHeatTerm (w : Q') (extent id s : Nat) : RatPoly :=
  polySmul (coeffW w s) (characterPolynomial (faceScalar extent id) s)

theorem faceHeatPolynomial_eq_sum (w : Q') (K extent id : Nat) :
    faceHeatPolynomial w K extent id = finitePolySum (faceHeatTerm w extent id) (List.range (K + 1)) := by
  apply sum_congr_on
  intro s hs
  unfold localFaceTerm faceHeatTerm faceScalar
  rw [coeffAt_heatKernelPacket (List.mem_range.mp hs)]

/-- The actual omitted characters, with the original heat coefficients. -/
def faceHeatTail (w : Q') (extent id start count : Nat) : RatPoly :=
  finitePolySum (fun i => faceHeatTerm w extent id (start + i)) (List.range count)

theorem faceHeatPolynomial_cutoff_append (w : Q') (K L extent id : Nat) :
    faceHeatPolynomial w (K + L) extent id =
      polyAdd (faceHeatPolynomial w K extent id) (faceHeatTail w extent id (K + 1) L) := by
  rw [faceHeatPolynomial_eq_sum, faceHeatPolynomial_eq_sum,
    show K + L + 1 = (K + 1) + L by omega, List.range_add, sum_append, sum_map]
  rfl

theorem faceHeatTail_coefficientL1 {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (extent id M L : Nat) :
    polynomialCoefficientL1 (faceHeatTail w extent id
      (polynomialLabelCutoff w (faceScalar extent id) + M + 1) L) ≤
      polynomialClosedTail w (faceScalar extent id) (M + 1) := by
  have h := heatCharacter_coefficientL1_block hw0 hw1 (faceScalar extent id) (M + 1) L
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (coefficientL1_sum_range _ L))
    (by simpa only [faceHeatTerm, Nat.add_assoc] using h)

/-- Type-level cutoff for every later original face prefix at this tolerance. -/
def faceHeatCutoff (w : Q') (extent id : Nat) (ε : Q') : Nat :=
  polynomialLabelCutoff w (faceScalar extent id) + polynomialTailModulus w (faceScalar extent id) ε

theorem faceHeatTail_small {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (extent id : Nat) (ε : Q') (hε : (0 : Q') < ε) (K L : Nat) (hK : faceHeatCutoff w extent id ε ≤ K) :
    polynomialCoefficientL1 (faceHeatTail w extent id (K + 1) L) ≤ ε := by
  have hN : polynomialLabelCutoff w (faceScalar extent id) ≤ K := by unfold faceHeatCutoff at hK; omega
  have he : polynomialLabelCutoff w (faceScalar extent id) + (K - polynomialLabelCutoff w (faceScalar extent id)) = K :=
    Nat.add_sub_of_le hN
  have h := faceHeatTail_coefficientL1 hw0 hw1 extent id (K - polynomialLabelCutoff w (faceScalar extent id)) L
  rw [he] at h
  exact Q'.le_trans' _ _ _ h (polynomialClosedTail_small hw0 _ ε hε _ (by unfold faceHeatCutoff at hK; omega))

theorem faceHeatTail_haar_small {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (blocks extent id : Nat) (ε : Q') (hε : (0 : Q') < ε) (K L : Nat)
    (hK : faceHeatCutoff w extent id ε ≤ K) :
    Q'.abs (quaternionHaar blocks (faceHeatTail w extent id (K + 1) L)) ≤ ε :=
  Q'.le_trans' _ _ _ (quaternionHaar_abs_le_coefficientL1 _ _) (faceHeatTail_small hw0 hw1 extent id ε hε K L hK)

end YMGap.Continuum.BF4ExactSlabAllExtentFaceHeatTail

#print axioms YMGap.Continuum.BF4ExactSlabAllExtentFaceHeatTail.coefficientL1_sum_range
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentFaceHeatTail.faceScalar
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentFaceHeatTail.faceHeatTerm
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentFaceHeatTail.faceHeatPolynomial_eq_sum
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentFaceHeatTail.faceHeatTail
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentFaceHeatTail.faceHeatPolynomial_cutoff_append
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentFaceHeatTail.faceHeatTail_coefficientL1
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentFaceHeatTail.faceHeatCutoff
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentFaceHeatTail.faceHeatTail_small
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentFaceHeatTail.faceHeatTail_haar_small
