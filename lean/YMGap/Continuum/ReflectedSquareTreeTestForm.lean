/-
# Cauchy--Schwarz tests against whole retained reflected-square forests

The mixed form sums the actual channel amplitudes with their original
weights. Its pre-inner form is constructed from the nonnegative tree;
sharp Cauchy--Schwarz follows without enumerating channels or taking roots.
Pruning then bounds a whole-forest test by the ORIGINAL unpruned energy
times that test's own reference energy. Both energies remain explicit.

This is finite rational machinery for spectator-preserving local tests,
not a strictly positive minor, a volume-uniform floor or an excitation.
-/

import YMGap.Continuum.ReflectedSquareTreePruning
import YMGap.Continuum.BF4ExactSlabLocalBilinearChannels
import YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
import YMGap.Continuum.GNSQuotient
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.ReflectedSquareTreeTestForm

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.OSReconstructionProgress
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.BF4ExactSlabReflectedSquareAlgebra
open YMGap.Continuum.BF4ExactSlabAllCutoffReflectionPositivity
open YMGap.Continuum.BF4ExactSlabLocalBilinearChannels
open YMGap.Continuum.ReflectedSquareTreePruning
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential

local infix:50 " ≈ " => Q'.eqv

private theorem split_quad (a b c x y z X Y Z : Q') :
    (a*x+b*y+c*z)+(a*X+b*Y+c*Z) ≈ a*(x+X)+b*(y+Y)+c*(z+Z) :=
  RingNormaliser.poly_identity_of_normal_eq
    (.add (.add (.add (.mul (.var 0) (.var 3)) (.mul (.var 1) (.var 4))) (.mul (.var 2) (.var 5)))
      (.add (.add (.mul (.var 0) (.var 6)) (.mul (.var 1) (.var 7))) (.mul (.var 2) (.var 8))))
    (.add (.add (.mul (.var 0) (.add (.var 3) (.var 6))) (.mul (.var 1) (.add (.var 4) (.var 7))))
      (.mul (.var 2) (.add (.var 5) (.var 8)))) (by decide)
    (fun | 0 => a | 1 => b | 2 => c | 3 => x | 4 => y | 5 => z | 6 => X | 7 => Y | _ => Z)

private theorem nonnegQuad (blocks : Nat) (s r : Q') (p q : RatPoly) : ∀ t : SquareTree, t.Nonnegative →
    (0 : Q') ≤ s*s*channelBilinearValue blocks p p t + 2*(s*r)*channelBilinearValue blocks p q t +
      r*r*channelBilinearValue blocks q q t
  | .zero, _ => by
      change (0 : Q') ≤ s*s*0+2*(s*r)*0+r*r*0
      exact Q'.ge_of_eqv (RingNormaliser.poly_identity_of_normal_eq
        (.add (.add (.mul (.mul (.var 0) (.var 0)) (.const 0))
          (.mul (.mul (.const 2) (.mul (.var 0) (.var 1))) (.const 0)))
          (.mul (.mul (.var 1) (.var 1)) (.const 0))) (.const 0) (by decide) (fun | 0 => s | _ => r))
  | .term w c, h => (qWeightGNS w h).toPreInnerForm.nonnegQuad s r
      (quaternionHaar blocks (polyMul p c)) (quaternionHaar blocks (polyMul q c))
  | .add t u, h => Q'.le_trans' _ _ _
      (Q'.zero_le_add _ _ (nonnegQuad blocks s r p q t h.1) (nonnegQuad blocks s r p q u h.2))
      (Q'.le_of_eqv (split_quad _ _ _ _ _ _ _ _ _))

def treeForm (blocks : Nat) (t : SquareTree) (ht : t.Nonnegative) : PreInnerForm RatPoly where
  B := fun p q => channelBilinearValue blocks p q t
  nonnegQuad := fun s r p q => nonnegQuad blocks s r p q t ht

theorem cauchySchwarz (blocks : Nat) (t : SquareTree) (ht : t.Nonnegative) (p q : RatPoly) :
    channelBilinearValue blocks p q t * channelBilinearValue blocks p q t ≤
      channelBilinearValue blocks p p t * channelBilinearValue blocks q q t :=
  (treeForm blocks t ht).cauchy_schwarz p q

theorem diagonal_pin (blocks : Nat) (p : RatPoly) : ∀ t : SquareTree,
    channelBilinearValue blocks p p t ≈ haarSquareSum blocks (t.multiplyTerm 1 p)
  | .zero => Q'.eqv_refl _
  | .term _ _ => Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm (Q'.one_mul_eqv _))
  | .add s t => Q'.add_eqv_congr' (diagonal_pin blocks p s) (diagonal_pin blocks p t)

theorem pairing_coeff_left (blocks : Nat) {p p' : RatPoly} (h : RatPolyCoeffEqv p p') (q : RatPoly) :
    ∀ t : SquareTree, channelBilinearValue blocks p q t ≈ channelBilinearValue blocks p' q t
  | .zero => Q'.eqv_refl _
  | .term _ r => Q'.mul_eqv_congr_left _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (haar_of_coeff_eqv blocks (h.mul_right r)))
  | .add s t => Q'.add_eqv_congr' (pairing_coeff_left blocks h q s) (pairing_coeff_left blocks h q t)

theorem pairing_add_left (blocks : Nat) (p q r : RatPoly) : ∀ t : SquareTree,
    channelBilinearValue blocks (polyAdd p q) r t ≈
      channelBilinearValue blocks p r t + channelBilinearValue blocks q r t
  | .zero => by change (0 : Q') ≈ 0+0; decide
  | .term w c => by
      have h : quaternionHaar blocks (polyMul (polyAdd p q) c) ≈
          quaternionHaar blocks (polyMul p c)+quaternionHaar blocks (polyMul q c) := by
        rw [polyMul_add_left_exact]
        exact quaternionHaar_append blocks _ _
      exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_eqv_congr_right _ _ _ h))
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (RingNormaliser.q_add_mul _ _ _)) (Q'.mul_add_eqv _ _ _))
  | .add s t => Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (pairing_add_left blocks p q r s) (pairing_add_left blocks p q r t))
      (Q'.add_swap_inner _ _ _ _)

theorem pairing_smul_left (blocks : Nat) (c : Q') (p q : RatPoly) : ∀ t : SquareTree,
    channelBilinearValue blocks (polySmul c p) q t ≈ c*channelBilinearValue blocks p q t
  | .zero => Q'.eqv_symm (QPoly.q_mul_zero c)
  | .term w r => by
      have h : quaternionHaar blocks (polyMul (polySmul c p) r) ≈ c*quaternionHaar blocks (polyMul p r) :=
        Q'.eqv_trans _ _ _ (haar_of_coeff_eqv blocks (RatPolyCoeffEqv.polyMul_smul_left c p r))
          (quaternionHaar_polySmul blocks c _)
      exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_eqv_congr_right _ _ _ h))
        (RingNormaliser.poly_identity_of_normal_eq
          (.mul (.var 0) (.mul (.mul (.var 1) (.var 2)) (.var 3)))
          (.mul (.var 1) (.mul (.var 0) (.mul (.var 2) (.var 3)))) (by decide)
          (fun | 0 => w | 1 => c | 2 => quaternionHaar blocks (polyMul p r) | _ => quaternionHaar blocks (polyMul q r)))
  | .add s t => Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (pairing_smul_left blocks c p q s) (pairing_smul_left blocks c p q t))
      (Q'.eqv_symm (Q'.mul_add_eqv _ _ _))

/-- The reference remains a whole spectator forest; no leaf or representative is chosen. -/
theorem pruned_test_bound {s t : SquareTree} (h : Pruning s t) (ht : t.Nonnegative)
    (blocks : Nat) (p q : RatPoly) :
    channelBilinearValue blocks p q s * channelBilinearValue blocks p q s ≤
      haarSquareSum blocks (t.multiplyTerm 1 p) * channelBilinearValue blocks q q s := by
  have hp : channelBilinearValue blocks p p s ≤ haarSquareSum blocks (t.multiplyTerm 1 p) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (diagonal_pin blocks p s)) (h.dressed_value_le ht blocks p)
  exact Q'.le_trans' _ _ _ (cauchySchwarz blocks s (h.nonnegative ht) p q)
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hp ((treeForm blocks s (h.nonnegative ht)).self_nonneg q))

end YMGap.Continuum.ReflectedSquareTreeTestForm

#print axioms YMGap.Continuum.ReflectedSquareTreeTestForm.treeForm
#print axioms YMGap.Continuum.ReflectedSquareTreeTestForm.cauchySchwarz
#print axioms YMGap.Continuum.ReflectedSquareTreeTestForm.diagonal_pin
#print axioms YMGap.Continuum.ReflectedSquareTreeTestForm.pairing_coeff_left
#print axioms YMGap.Continuum.ReflectedSquareTreeTestForm.pairing_add_left
#print axioms YMGap.Continuum.ReflectedSquareTreeTestForm.pairing_smul_left
#print axioms YMGap.Continuum.ReflectedSquareTreeTestForm.pruned_test_bound
