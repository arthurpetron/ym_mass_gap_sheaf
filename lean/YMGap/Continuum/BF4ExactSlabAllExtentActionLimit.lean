/-
# Constructive limits of the ORIGINAL full slab action integrals

The full finite heat product is integrated on the original shared quaternion
carrier. Its explicit product remainder gives a rational Cauchy datum, then
a CReal with the library's computed cofinal reindex. Specializing to the
actual full slab face list constructs the original action-integral limit at
every odd extent and rational 0 < w < 1.

Finite nonnegativity comes from ORIGINAL reflection positivity and the full
heat-unit quadratic identity. No decoupled partition formula, pointwise heat
positivity premise, strict positive lower bound or physical vacuum is used.
-/

import YMGap.Continuum.BF4ExactSlabAllExtentHeatUnitCauchy

namespace YMGap.Continuum.BF4ExactSlabAllExtentActionLimit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentReflectionPositivity
open YMGap.Continuum.BF4ExactSlabAllExtentHeatUnit
open YMGap.Continuum.BF4ExactSlabAllExtentHeatProductTail
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

def heatProductHaar (w : Q') (blocks extent : Nat) (ids : List Nat) (K : Nat) : Q' :=
  quaternionHaar blocks (polynomialProduct (faceHeatPolynomial w K extent) ids)

theorem heatProductHaar_append (w : Q') (blocks extent : Nat) (ids : List Nat) (K L : Nat) :
    heatProductHaar w blocks extent ids (K + L) ≈ heatProductHaar w blocks extent ids K +
      quaternionHaar blocks (heatProductRemainder w extent K L ids) :=
  Q'.eqv_trans _ _ _ (haar_of_coeff_eqv blocks (heatProduct_cutoff_append w extent K L ids))
    (quaternionHaar_append blocks _ _)

private theorem cancel_prefix (a r : Q') : (a + r) + (-a) ≈ r :=
  Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ (Q'.add_comm_eqv a r))
    (Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv r a (-a))
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left r _ _ (Q'.add_neg_self_eqv a))
        (Q'.eqv_of_eq (Q'.add_zero' r))))

/-- Generic rational consequence of the original prefix-plus-remainder identity. -/
theorem close_of_add_remainder {a b r ε : Q'} (h : a ≈ b + r) (hr : Q'.abs r ≤ ε) :
    a ≤ b + ε ∧ b ≤ a + ε :=
  Q'.two_sided_of_abs_sub_le (Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr (Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ (-b) h) (cancel_prefix b r)))) hr)

theorem heatProductHaar_increment_close {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (blocks extent : Nat) (ids : List Nat) (ε : Q') (hε : (0 : Q') < ε) (K L : Nat)
    (hK : heatProductCutoff w extent ids ε ≤ K) :
    heatProductHaar w blocks extent ids (K + L) ≤ heatProductHaar w blocks extent ids K + ε ∧
      heatProductHaar w blocks extent ids K ≤ heatProductHaar w blocks extent ids (K + L) + ε :=
  close_of_add_remainder (heatProductHaar_append w blocks extent ids K L)
    (heatProductRemainder_haar_small hw0 hw1 blocks extent ids ε hε K L hK)

def heatProductHaarCauchy (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (blocks extent : Nat) (ids : List Nat) : CReal.QCauchy (heatProductHaar w blocks extent ids) where
  M := heatProductCutoff w extent ids
  bound := by
    intro ε hε p q hp hq
    by_cases hqp : q ≤ p
    · have h := heatProductHaar_increment_close hw0 hw1 blocks extent ids ε hε q (p - q) hq
      rw [Nat.add_sub_of_le hqp] at h
      exact h
    · have h := heatProductHaar_increment_close hw0 hw1 blocks extent ids ε hε p (q - p) hp
      rw [Nat.add_sub_of_le (by omega : p ≤ q)] at h
      exact ⟨h.2, h.1⟩

def heatProductHaarLimit (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (blocks extent : Nat) (ids : List Nat) : CReal :=
  CReal.ofQ'CauchySeq _ (heatProductHaarCauchy w hw0 hw1 blocks extent ids)

theorem heatProductHaarLimit_approx (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (blocks extent : Nat) (ids : List Nat) (n : Nat) :
    (heatProductHaarLimit w hw0 hw1 blocks extent ids).approx n =
      heatProductHaar w blocks extent ids (CReal.QMhat _ (heatProductHaarCauchy w hw0 hw1 blocks extent ids) n) :=
  CReal.ofQ'CauchySeq_approx _ _ n

theorem heatProductHaar_converges (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (blocks extent : Nat) (ids : List Nat) :
    CReal.ConvergesTo (fun K => CReal.ofQ' (heatProductHaar w blocks extent ids K))
      (heatProductHaarLimit w hw0 hw1 blocks extent ids) :=
  CReal.convergesTo_ofQ'CauchySeq _ _

def fullActionValue (w : Q') (K half : Nat) : Q' :=
  heatProductHaar w (boundaryCompleteSlabLinks (centralExtent half)).length
    (centralExtent half) (slabPhysicalFaceEdges (centralExtent half)) K

def fullActionLimit (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (half : Nat) : CReal :=
  heatProductHaarLimit w hw0 hw1 (boundaryCompleteSlabLinks (centralExtent half)).length
    (centralExtent half) (slabPhysicalFaceEdges (centralExtent half))

theorem fullActionValue_nonnegative {w : Q'} (hw : (0 : Q') ≤ w) (K half : Nat) :
    (0 : Q') ≤ fullActionValue w K half :=
  Q'.le_trans' _ _ _ (exact_quadratic_nonnegative hw K half (heatUnitCode K half).coefficient)
    (Q'.le_of_eqv (heatUnitCode_full_action w K half))

theorem fullActionLimit_nonnegative (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (half : Nat) :
    ExpPos.geRat (fullActionLimit w hw0 hw1 half) 0 := by
  apply ExpPos.geRat_of_eventually
  refine ⟨0, fun n _ => ?_⟩
  unfold fullActionLimit
  rw [heatProductHaarLimit_approx]
  exact fullActionValue_nonnegative (Q'.le_of_lt hw0) _ half

end YMGap.Continuum.BF4ExactSlabAllExtentActionLimit

#print axioms YMGap.Continuum.BF4ExactSlabAllExtentActionLimit.heatProductHaar
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentActionLimit.heatProductHaar_append
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentActionLimit.close_of_add_remainder
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentActionLimit.heatProductHaar_increment_close
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentActionLimit.heatProductHaarCauchy
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentActionLimit.heatProductHaarLimit
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentActionLimit.heatProductHaarLimit_approx
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentActionLimit.heatProductHaar_converges
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentActionLimit.fullActionValue
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentActionLimit.fullActionLimit
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentActionLimit.fullActionValue_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentActionLimit.fullActionLimit_nonnegative
