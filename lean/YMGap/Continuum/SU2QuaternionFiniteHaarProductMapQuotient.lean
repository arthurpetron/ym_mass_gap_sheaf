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
import YMGap.Continuum.SU2QuaternionProductHeatDualForm

namespace YMGap.Continuum.SU2QuaternionFiniteHaarProductMapQuotient

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.SU2HeatCutoffCasimirBound
open YMGap.Continuum.SU2QuaternionFiniteHaarGNSCarrier
open YMGap.Continuum.SU2QuaternionFiniteHaarProductMapRadical
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionProductHeatConstant
open YMGap.Continuum.SU2QuaternionProductHeatDualForm
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatTensorization
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarPolynomialPositivity
open YMGap.Continuum.SU2QuaternionRelativeHeatContraction
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv

private theorem support_smul_local {n : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks n p) (c : Q') :
    SupportedQuaternionBlocks n (polySmul c p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private theorem support_weaken_local {small large : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks small p) (hle : small ≤ large) :
    SupportedQuaternionBlocks large p := by
  intro t ht
  exact Nat.le_trans (hp t ht) (Nat.mul_le_mul_left 4 hle)

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

theorem productMapQuotient_unit
    (n : Nat) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK : headCutoff w ≤ K)
    (ids : List Nat) (hnodup : ids.Nodup)
    (hids : ∀ i, i ∈ ids → i < n) :
    productMapQuotient n hw0 hw1 K hK ids hnodup hids
        (finiteHaarUnitClass n) = finiteHaarUnitClass n := by
  apply Quotient.sound
  change finiteHaarPair n
      (polyAdd (productMap n w K ids polyOne)
        (polySmul (-1) polyOne))
      (polyAdd (productMap n w K ids polyOne)
        (polySmul (-1) polyOne)) ≈ 0
  let m : RatPoly := productMap n w K ids polyOne
  let d : RatPoly := polyAdd m (polySmul (-1) polyOne)
  have hm : SupportedQuaternionBlocks n m := by
    exact productMap_supported n w K ids hids (supported_one n)
  have hd : SupportedQuaternionBlocks n d := by
    exact supported_add hm (support_smul_local (supported_one n) (-1))
  have htested : SupportedHaarEqv n d
      (polyAdd polyOne (polySmul (-1) polyOne)) := by
    exact SupportedHaarEqv.add
      (productMap_one n w K ids hnodup hids)
      (SupportedHaarEqv.smul (SupportedHaarEqv.refl n polyOne) (-1))
  have hzero : RatPolyCoeffEqv
      (polyAdd polyOne (polySmul (-1) polyOne)) polyZero :=
    RatPolyCoeffEqv.add_neg_smul polyOne
  have hright : quaternionHaar n
      (polyMul d (polyAdd polyOne (polySmul (-1) polyOne))) ≈ 0 := by
    have hcoeff : RatPolyCoeffEqv
        (polyMul d (polyAdd polyOne (polySmul (-1) polyOne)))
        polyZero :=
      (hzero.mul_left d).trans (RatPolyCoeffEqv.mul_zero_right d)
    exact Q'.eqv_trans _ _ _ (haar_of_coeff hcoeff) (by rfl)
  have hdiag := htested d hd
  change finiteHaarPair n d d ≈ 0
  exact Q'.eqv_trans _ _ _ (by
    unfold finiteHaarPair
    exact hdiag) hright

theorem productMap_mean_preserved
    (n : Nat) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK : headCutoff w ≤ K)
    (ids : List Nat) (hnodup : ids.Nodup)
    (hids : ∀ i, i ∈ ids → i < n)
    (f : RatPoly) (hf : SupportedQuaternionBlocks n f) :
    quaternionHaar n (productMap n w K ids f) ≈ quaternionHaar n f := by
  have hpair := productMap_pairing n w K ids f polyOne
  have hleft : quaternionHaar n
      (polyMul polyOne (productMap n w K ids f)) ≈
      quaternionHaar n (productMap n w K ids f) :=
    haar_of_coeff (RatPolyCoeffEqv.one_mul (productMap n w K ids f))
  have hpad : PaddedPolynomialCoeffEqv (n+n)
      (polyMul f (liftBoundary n polyOne))
      (polyMul f polyOne) := by
    exact (PaddedPolynomialCoeffEqv.of_coeff (RatPolyCoeffEqv.refl f)).mul
      (lift_one (n+n) n)
  have hf_lift : SupportedQuaternionBlocks (n+n)
      (polyMul f (liftBoundary n polyOne)) :=
    supported_polyMul (support_weaken_local hf (by omega))
      (lift_supported (supported_one n) n)
  have hf_one : SupportedQuaternionBlocks (n+n) (polyMul f polyOne) :=
    supported_polyMul (support_weaken_local hf (by omega)) (supported_one (n+n))
  have hpad_haar : quaternionHaar (n+n)
      (polyMul f (liftBoundary n polyOne)) ≈
      quaternionHaar (n+n) (polyMul f polyOne) :=
    hpad.haar hf_lift hf_one
  have hheat_haar : quaternionHaar (n+n)
      (polyMul (productHeat n w K ids)
        (polyMul f (liftBoundary n polyOne))) ≈
      quaternionHaar (n+n)
        (polyMul (productHeat n w K ids) (polyMul f polyOne)) := by
    have hprod := (PaddedPolynomialCoeffEqv.of_coeff
      (RatPolyCoeffEqv.refl (productHeat n w K ids))).mul hpad
    exact hprod.haar
      (supported_polyMul (productHeat_supported n w K ids hids) hf_lift)
      (supported_polyMul (productHeat_supported n w K ids hids) hf_one)
  have hone : RatPolyCoeffEqv (polyMul f polyOne) f :=
    RatPolyCoeffEqv.mul_one f
  have hheat_f : quaternionHaar (n+n)
      (polyMul (productHeat n w K ids) (polyMul f polyOne)) ≈
      quaternionHaar (n+n) (polyMul (productHeat n w K ids) f) :=
    haar_of_coeff (hone.mul_left (productHeat n w K ids))
  have hmarg : quaternionHaar (n+n)
      (polyMul (productHeat n w K ids) f) ≈ quaternionHaar n f :=
    productHeat_lower_marginal n w K ids hnodup hids f hf
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hleft)
    (Q'.eqv_trans _ _ _ hpair
      (Q'.eqv_trans _ _ _ hheat_haar
      (Q'.eqv_trans _ _ _ hheat_f hmarg)))

theorem productMap_centered_preserved
    (n : Nat) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK : headCutoff w ≤ K)
    (ids : List Nat) (hnodup : ids.Nodup)
    (hids : ∀ i, i ∈ ids → i < n)
    (f : RatPoly) (hf : SupportedQuaternionBlocks n f)
    (hcenter : quaternionHaar n f ≈ 0) :
    quaternionHaar n (productMap n w K ids f) ≈ 0 :=
  Q'.eqv_trans _ _ _
    (productMap_mean_preserved n hw0 hw1 K hK ids hnodup hids f hf)
    hcenter

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

theorem productMapQuotient_transfer_pairing_mk
    (n : Nat) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK : headCutoff w ≤ K)
    (ids : List Nat) (hnodup : ids.Nodup)
    (hids : ∀ i, i ∈ ids → i < n)
    (p q : (finiteHaarGNSData n).V) :
    (finiteHaarGNSData n).qInner
        ((finiteHaarGNSData n).qmk p)
        (productMapQuotient n hw0 hw1 K hK ids hnodup hids
          ((finiteHaarGNSData n).qmk q)) =
      Quotient.mk qSetoid
        (kineticPair n w K ids p.val q.val) := by
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

theorem productMapQuotient_centered_strict_bound
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
      squaredHeatRate w * finiteHaarPair n p.val p.val ∧
      squaredHeatRate w < (1 : Q') := by
  exact ⟨productMapQuotient_centered_square_bound n hw0 hw1 K hK ids
      hnodup hids p hcenter, squaredHeatRate_lt_one hw0 hw1⟩

theorem productMapQuotient_transfer_form_squared_bound
    (n : Nat) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK : headCutoff w ≤ K)
    (ids : List Nat) (hnodup : ids.Nodup)
    (hids : ∀ i, i ∈ ids → i < n)
    (p : (finiteHaarGNSData n).V)
    (hcenter : quaternionHaar n p.val ≈ 0) :
    kineticPair n w K ids p.val p.val *
        kineticPair n w K ids p.val p.val ≤
      squaredHeatRate w *
        (finiteHaarPair n p.val p.val * finiteHaarPair n p.val p.val) := by
  have hm : SupportedQuaternionBlocks n
      (productMap n w K ids p.val) :=
    productMap_supported n w K ids hids p.property
  have hcs := finiteHaar_cauchySchwarz n p.val
    (productMap n w K ids p.val) p.property hm
  have hbound := productMapQuotient_centered_square_bound n hw0 hw1 K hK ids
    hnodup hids p hcenter
  have hpp : (0 : Q') ≤ finiteHaarPair n p.val p.val :=
    finiteHaarPair_nonnegative n p.val p.property
  have hmul := Q'.mul_le_mul_of_nonneg_left _ _ _ hbound hpp
  have htarget : finiteHaarPair n p.val p.val *
      (squaredHeatRate w * finiteHaarPair n p.val p.val) ≈
      squaredHeatRate w *
        (finiteHaarPair n p.val p.val * finiteHaarPair n p.val p.val) := by
    have h1 := Q'.eqv_symm (Q'.mul_assoc_eqv
      (finiteHaarPair n p.val p.val) (squaredHeatRate w)
      (finiteHaarPair n p.val p.val))
    have h2 := Q'.mul_eqv_congr_right
      (finiteHaarPair n p.val p.val * squaredHeatRate w)
      (squaredHeatRate w * finiteHaarPair n p.val p.val)
      (finiteHaarPair n p.val p.val)
      (Q'.mul_comm_eqv (finiteHaarPair n p.val p.val) (squaredHeatRate w))
    have h3 := Q'.mul_assoc_eqv (squaredHeatRate w)
      (finiteHaarPair n p.val p.val) (finiteHaarPair n p.val p.val)
    exact Q'.eqv_trans _ _ _ h1 (Q'.eqv_trans _ _ _ h2 h3)
  simpa only [kineticPair, finiteHaarPair] using
    (Q'.le_trans' _ _ _ hcs (Q'.le_trans' _ _ _ hmul
      (Q'.le_of_eqv htarget)))

end YMGap.Continuum.SU2QuaternionFiniteHaarProductMapQuotient

#print axioms YMGap.Continuum.SU2QuaternionFiniteHaarProductMapQuotient.productMapRep
#print axioms YMGap.Continuum.SU2QuaternionFiniteHaarProductMapQuotient.productMapRep_rad_congr
#print axioms YMGap.Continuum.SU2QuaternionFiniteHaarProductMapQuotient.productMapQuotient
#print axioms YMGap.Continuum.SU2QuaternionFiniteHaarProductMapQuotient.productMapQuotient_mk
#print axioms YMGap.Continuum.SU2QuaternionFiniteHaarProductMapQuotient.productMapQuotient_qAdd_mk
#print axioms YMGap.Continuum.SU2QuaternionFiniteHaarProductMapQuotient.productMapQuotient_qNeg_mk
#print axioms YMGap.Continuum.SU2QuaternionFiniteHaarProductMapQuotient.productMapQuotient_unit
#print axioms YMGap.Continuum.SU2QuaternionFiniteHaarProductMapQuotient.productMap_mean_preserved
#print axioms YMGap.Continuum.SU2QuaternionFiniteHaarProductMapQuotient.productMap_centered_preserved
#print axioms YMGap.Continuum.SU2QuaternionFiniteHaarProductMapQuotient.productMapQuotient_centered_strict_bound
#print axioms YMGap.Continuum.SU2QuaternionFiniteHaarProductMapQuotient.productMapQuotient_qInner_mk
#print axioms YMGap.Continuum.SU2QuaternionFiniteHaarProductMapQuotient.productMapQuotient_transfer_pairing_mk
#print axioms YMGap.Continuum.SU2QuaternionFiniteHaarProductMapQuotient.productMapQuotient_qNormSq_mk
#print axioms YMGap.Continuum.SU2QuaternionFiniteHaarProductMapQuotient.productMapQuotient_centered_square_bound
#print axioms YMGap.Continuum.SU2QuaternionFiniteHaarProductMapQuotient.productMapQuotient_transfer_form_squared_bound
