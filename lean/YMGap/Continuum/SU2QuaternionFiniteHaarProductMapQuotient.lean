/-
# Quotient descent of the finite product heat map

The finite ordinary-Haar carrier has a genuine radical quotient.  The
representative-level radical-annihilation theorem is enough, together with
coefficient linearity of `productMap`, to descend that map through the
quotient.  This module stops at the finite quotient: it does not define the
completed transfer operator or prove a spectral or continuum gap.
-/

import YMGap.Continuum.SU2QuaternionFiniteHaarProductMapRadical
import YMGap.Continuum.SU2QuaternionProductHeatConstant

namespace YMGap.Continuum.SU2QuaternionFiniteHaarProductMapQuotient

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.SU2HeatCutoffCasimirBound
open YMGap.Continuum.SU2QuaternionFiniteHaarGNSCarrier
open YMGap.Continuum.SU2QuaternionFiniteHaarProductMapRadical
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionProductHeatConstant
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatTensorization
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarPolynomialPositivity
open YMGap.Continuum.SU2QuaternionRelativeHeatContraction
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv

/-! ## Representatives -/

/-- The supported representative map induced by one finite product heat map. -/
def productMapRep
    (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (hids : ∀ i, i ∈ ids → i < n)
    (p : (finiteHaarGNSData n).V) : (finiteHaarGNSData n).V :=
  ⟨productMap n w K ids p.val,
    productMap_supported n w K ids hids p.property⟩

theorem productMapRep_rad_congr
    (n : Nat) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK : headCutoff w ≤ K)
    (ids : List Nat) (hnodup : ids.Nodup)
    (hids : ∀ i, i ∈ ids → i < n)
    (p q : (finiteHaarGNSData n).V)
    (hpq : (finiteHaarGNSData n).rad p q) :
    (finiteHaarGNSData n).rad
      (productMapRep n w K ids hids p)
      (productMapRep n w K ids hids q) := by
  have hrad : finiteHaarPair n
      (polyAdd p.val (polySmul (-1) q.val))
      (polyAdd p.val (polySmul (-1) q.val)) ≈ 0 := by
    change finiteHaarPair n
      ((finiteHaarGNSData n).sub p q).val
      ((finiteHaarGNSData n).sub p q).val ≈ 0
    exact hpq
  have hout := productMap_radical_zero n hw0 hw1 K hK ids hnodup hids
    ((finiteHaarGNSData n).sub p q).val
    ((finiteHaarGNSData n).sub p q).property hrad
  have hdiff : RatPolyCoeffEqv
      (productMap n w K ids
        (polyAdd p.val (polySmul (-1) q.val)))
      (polyAdd (productMap n w K ids p.val)
        (polySmul (-1) (productMap n w K ids q.val))) := by
    exact (productMap_add n w K ids p.val (polySmul (-1) q.val)).trans
      ((RatPolyCoeffEqv.refl (productMap n w K ids p.val)).add
        (productMap_smul n w K ids (-1) q.val))
  have hpair : finiteHaarPair n
      (polyAdd (productMap n w K ids p.val)
        (polySmul (-1) (productMap n w K ids q.val)))
      (polyAdd (productMap n w K ids p.val)
        (polySmul (-1) (productMap n w K ids q.val))) ≈
      finiteHaarPair n
        (productMap n w K ids
          (polyAdd p.val (polySmul (-1) q.val)))
        (productMap n w K ids
          (polyAdd p.val (polySmul (-1) q.val))) := by
    unfold finiteHaarPair
    exact Q'.eqv_symm (haar_of_coeff (hdiff.mul hdiff))
  change finiteHaarPair n
      (polyAdd (productMap n w K ids p.val)
        (polySmul (-1) (productMap n w K ids q.val)))
      (polyAdd (productMap n w K ids p.val)
        (polySmul (-1) (productMap n w K ids q.val))) ≈ 0
  exact Q'.eqv_trans _ _ _ hpair hout

/-! ## The quotient map -/

/-- The finite product heat map descended to the ordinary-Haar GNS quotient. -/
def productMapQuotient
    (n : Nat) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK : headCutoff w ≤ K)
    (ids : List Nat) (hnodup : ids.Nodup)
    (hids : ∀ i, i ∈ ids → i < n) :
    finiteHaarQuotient n → finiteHaarQuotient n :=
  Quotient.lift
    (fun p => (finiteHaarGNSData n).qmk
      (productMapRep n w K ids hids p))
    (by
      intro p q hpq
      exact Quotient.sound (productMapRep_rad_congr n hw0 hw1 K hK ids
        hnodup hids p q hpq))

theorem productMapQuotient_mk
    (n : Nat) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK : headCutoff w ≤ K)
    (ids : List Nat) (hnodup : ids.Nodup)
    (hids : ∀ i, i ∈ ids → i < n)
    (p : (finiteHaarGNSData n).V) :
    productMapQuotient n hw0 hw1 K hK ids hnodup hids
        ((finiteHaarGNSData n).qmk p) =
      (finiteHaarGNSData n).qmk (productMapRep n w K ids hids p) := rfl

private theorem rad_of_veq {D : GNSData} {a b : D.V}
    (h : D.veq a b) : D.rad a b := by
  have hz : D.veq (D.sub a b) D.zero :=
    D.veq_trans (D.add_congr h (D.veq_refl (D.neg b)))
      (D.veq_trans (D.add_comm b (D.neg b)) (D.neg_add b))
  exact Q'.eqv_trans _ _ _ (D.B_diag_congr hz) (D.B_zero_left D.zero)

theorem productMapQuotient_qAdd_mk
    (n : Nat) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK : headCutoff w ≤ K)
    (ids : List Nat) (hnodup : ids.Nodup)
    (hids : ∀ i, i ∈ ids → i < n)
    (p q : (finiteHaarGNSData n).V) :
    productMapQuotient n hw0 hw1 K hK ids hnodup hids
        ((finiteHaarGNSData n).qAdd
          ((finiteHaarGNSData n).qmk p) ((finiteHaarGNSData n).qmk q)) =
      (finiteHaarGNSData n).qAdd
        (productMapQuotient n hw0 hw1 K hK ids hnodup hids
          ((finiteHaarGNSData n).qmk p))
        (productMapQuotient n hw0 hw1 K hK ids hnodup hids
          ((finiteHaarGNSData n).qmk q)) := by
  apply Quotient.sound
  apply rad_of_veq
  change RatPolyCoeffEqv
    (productMap n w K ids (polyAdd p.val q.val))
    (polyAdd (productMap n w K ids p.val)
      (productMap n w K ids q.val))
  exact productMap_add n w K ids p.val q.val

theorem productMapQuotient_qNeg_mk
    (n : Nat) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK : headCutoff w ≤ K)
    (ids : List Nat) (hnodup : ids.Nodup)
    (hids : ∀ i, i ∈ ids → i < n)
    (p : (finiteHaarGNSData n).V) :
    productMapQuotient n hw0 hw1 K hK ids hnodup hids
        ((finiteHaarGNSData n).qNeg ((finiteHaarGNSData n).qmk p)) =
      (finiteHaarGNSData n).qNeg
        (productMapQuotient n hw0 hw1 K hK ids hnodup hids
          ((finiteHaarGNSData n).qmk p)) := by
  apply Quotient.sound
  apply rad_of_veq
  change RatPolyCoeffEqv
    (productMap n w K ids (polySmul (-1) p.val))
    (polySmul (-1) (productMap n w K ids p.val))
  exact productMap_smul n w K ids (-1) p.val

/-! ## Same-object pairing and finite centered estimate -/

theorem productMapQuotient_qInner_mk
    (n : Nat) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK : headCutoff w ≤ K)
    (ids : List Nat) (hnodup : ids.Nodup)
    (hids : ∀ i, i ∈ ids → i < n)
    (p q : (finiteHaarGNSData n).V) :
    (finiteHaarGNSData n).qInner
        (productMapQuotient n hw0 hw1 K hK ids hnodup hids
          ((finiteHaarGNSData n).qmk p))
        (productMapQuotient n hw0 hw1 K hK ids hnodup hids
          ((finiteHaarGNSData n).qmk q)) =
      Quotient.mk qSetoid
        (finiteHaarPair n
          (productMapRep n w K ids hids p).val
          (productMapRep n w K ids hids q).val) := by
  rfl

theorem productMapQuotient_qNormSq_mk
    (n : Nat) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK : headCutoff w ≤ K)
    (ids : List Nat) (hnodup : ids.Nodup)
    (hids : ∀ i, i ∈ ids → i < n)
    (p : (finiteHaarGNSData n).V) :
    (finiteHaarGNSData n).qNormSq
        (productMapQuotient n hw0 hw1 K hK ids hnodup hids
          ((finiteHaarGNSData n).qmk p)) =
      Quotient.mk qSetoid
          (finiteHaarPair n
          (productMapRep n w K ids hids p).val
          (productMapRep n w K ids hids p).val) := by
  rfl

theorem productMapQuotient_centered_square_bound
    (n : Nat) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK : headCutoff w ≤ K)
    (ids : List Nat) (hnodup : ids.Nodup)
    (hids : ∀ i, i ∈ ids → i < n)
    (p : (finiteHaarGNSData n).V)
    (hcenter : quaternionHaar n p.val ≈ 0) :
    finiteHaarPair n
        (productMapRep n w K ids hids p).val
        (productMapRep n w K ids hids p).val ≤
      squaredHeatRate w * finiteHaarPair n p.val p.val := by
  simpa only [productMapRep, finiteHaarPair] using
    (productMap_centered_square_bound n hw0 hw1 K hK ids hnodup hids
      p.property hcenter)

end YMGap.Continuum.SU2QuaternionFiniteHaarProductMapQuotient

#print axioms YMGap.Continuum.SU2QuaternionFiniteHaarProductMapQuotient.productMapRep
#print axioms YMGap.Continuum.SU2QuaternionFiniteHaarProductMapQuotient.productMapRep_rad_congr
#print axioms YMGap.Continuum.SU2QuaternionFiniteHaarProductMapQuotient.productMapQuotient
#print axioms YMGap.Continuum.SU2QuaternionFiniteHaarProductMapQuotient.productMapQuotient_mk
#print axioms YMGap.Continuum.SU2QuaternionFiniteHaarProductMapQuotient.productMapQuotient_qAdd_mk
#print axioms YMGap.Continuum.SU2QuaternionFiniteHaarProductMapQuotient.productMapQuotient_qNeg_mk
#print axioms YMGap.Continuum.SU2QuaternionFiniteHaarProductMapQuotient.productMapQuotient_qInner_mk
#print axioms YMGap.Continuum.SU2QuaternionFiniteHaarProductMapQuotient.productMapQuotient_qNormSq_mk
#print axioms YMGap.Continuum.SU2QuaternionFiniteHaarProductMapQuotient.productMapQuotient_centered_square_bound
