/-
Early ORIGINAL character-prefix positivity at 0 <= w <= 1/2.

The actual sharp character intervals and the proved label-two geometric
tail construct the floor 1055/2272 for EVERY inclusive cutoff K >= 1.
This is a polynomial Haar certificate, not an inference from scalar
pointwise positivity. Shared links and the original heat coefficients are
retained. No headCutoff consumer is changed. The consumer is bounded
original raw-moment positivity, not scaling, OS or continuum closure.
-/

import YMGap.Continuum.QuaternionHaarAllNomeHeatCertificate
import YMGap.Continuum.QuaternionHaarCertifiedPositiveWindowProduct

namespace YMGap.Continuum.QuaternionHaarSmallNomeHeatCertificate

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.BondMovingStep (coeffW coeffW_zero)
open YMGap.Continuum.RGTransport (c4)
open YMGap.Continuum.BondMovingScaledNorm (tailTerm)
open YMGap.Continuum.HeatKernelGap (qpow_mono)
open YMGap.Continuum.HeatKernelRGStep (zero_le_ofNat)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarCertifiedPositiveWindowProduct (positiveFromLowerWindow)
open YMGap.Continuum.QuaternionHaarHeatCertificate (heatPrefix)
open YMGap.Continuum.QuaternionHaarAllNomeHeatCertificate (heatTerm termInterval)
open YMGap.Continuum.SU2AllLabelPointwiseHeatCorridor
  (half pointwiseHeatMajorant allLabelTailBudget pointwiseHeatMajorant_tail_le)
open YMGap.Continuum.BF4ExactSlabAllExtentFaceHeatTail
  (faceScalar faceHeatTerm faceHeatPolynomial_eq_sum)
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm (faceHeatPolynomial)
open YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace (haarNorm_slabPlaquette)
open YMGap.Continuum.QuaternionHaarUnitScalarSquare (supported_slabPlaquette)
open YMGap.Continuum.Z4HalfTimeReflectionGeometry (boundaryCompleteSlabLinks)
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
  (slabPhysicalFaceEdges slabPlaquetteAt_mem)

local infix:50 " ≈ " => Q'.eqv

/-- The exact early-cutoff floor; it does not depend on the carrier size. -/
def floor : Q' := Q'.mkPos 1055 2272 (by decide)

theorem floor_positive : (0 : Q') < floor := by decide

private theorem labelOne_majorant_le {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw : w ≤ half) :
    pointwiseHeatMajorant w 1 ≤ half := by
  unfold pointwiseHeatMajorant tailTerm
  have hpower : qpow w (c4 1) ≤ qpow half (c4 1) :=
    qpow_mono hw0 hw (c4 1)
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ _ hpower
    (zero_le_ofNat ((1+1)^2))
  exact Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv (by decide))

/-- An actual tail certificate for labels 2 through count+1, including
the empty tail. The sharp finite majorant is already proved. -/
def higherLabelInterval {w : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ half)
    {blocks : Nat} {x : RatPoly} (P : SquareBound blocks x 1) (count : Nat) :
    Interval blocks
      (finitePolySum (fun j => heatTerm w x (2+j)) (List.range count))
      allLabelTailBudget :=
  (Interval.finiteRange (fun j => heatTerm w x (2+j))
    (fun j => pointwiseHeatMajorant w (2+j))
    (fun j => termInterval hw0 P (2+j)) count).weaken
      (pointwiseHeatMajorant_tail_le hw0 hw count)

private theorem sum_append {T : Type} (f : T → RatPoly) : ∀ xs ys : List T,
    finitePolySum f (xs++ys) = polyAdd (finitePolySum f xs) (finitePolySum f ys)
  | [], _ => rfl
  | t::ts, ys => by
      simp only [List.cons_append, finitePolySum, sum_append f ts ys,
        polyAdd, List.append_assoc]

private theorem sum_map {T U : Type} (f : U → RatPoly) (g : T → U) : ∀ xs : List T,
    finitePolySum f (xs.map g) = finitePolySum (fun x => f (g x)) xs
  | [] => rfl
  | t::ts => by simp only [List.map_cons, finitePolySum, sum_map f g ts]

private theorem prefix_head_tail (w : Q') (x : RatPoly) (count : Nat) :
    RatPolyCoeffEqv (heatPrefix w (count+1) x)
      (polyAdd (polyAdd polyOne (heatTerm w x 1))
        (finitePolySum (fun j => heatTerm w x (2+j)) (List.range count))) := by
  unfold heatPrefix
  rw [show count+1+1 = 2+count by omega, List.range_add, sum_append, sum_map]
  change RatPolyCoeffEqv
    (polyAdd (polyAdd (heatTerm w x 0) (polyAdd (heatTerm w x 1) polyZero))
      (finitePolySum (fun j => heatTerm w x (2+j)) (List.range count))) _
  simp only [polyAdd, polyZero, List.append_nil]
  have hzero : heatTerm w x 0 = polySmul 1 polyOne := by
    unfold heatTerm
    rw [coeffW_zero]
    rfl
  rw [hzero]
  exact ((RatPolyCoeffEqv.one_smul polyOne).add (RatPolyCoeffEqv.refl _)).add
    (RatPolyCoeffEqv.refl _)

/-- ORIGINAL heat-prefix floor at every inclusive K >= 1, constructed
from sharp term intervals rather than supplied positivity. -/
def prefixFloorCertificate {w : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ half)
    {blocks : Nat} {x : RatPoly} (P : SquareBound blocks x 1)
    (K : Nat) (hK : 1 ≤ K) :
    Certificate blocks (polyAdd (heatPrefix w K x) (polyNeg (cap floor))) := by
  cases K with
  | zero => omega
  | succ count =>
      let head := heatTerm w x 1
      let tail := finitePolySum (fun j => heatTerm w x (2+j)) (List.range count)
      let I := ((termInterval hw0 P 1).weaken (labelOne_majorant_le hw0 hw)).add
        (higherLabelInterval hw0 hw P count)
      have hsplit := prefix_head_tail w x count
      have hone := (((RatPolyCoeffEqv.one_smul polyOne).symm.add
        (RatPolyCoeffEqv.refl head)).add (RatPolyCoeffEqv.refl tail)).add
        (RatPolyCoeffEqv.refl (polyNeg (cap floor)))
      have hcapDifference : RatPolyCoeffEqv
          (polyAdd (cap 1) (polyNeg (cap floor))) (cap (1 + -floor)) :=
        RatPolyCoeffEqv.of_canon_termwise (by decide)
      have hcap : RatPolyCoeffEqv
          (polyAdd (cap 1) (polyNeg (cap floor))) (cap (half+allLabelTailBudget)) :=
        hcapDifference.trans (RatPolyCoeffEqv.smul_coefficient
          (by decide : (1 : Q') + -floor ≈ half+allLabelTailBudget) polyOne)
      have hregroup : RatPolyCoeffEqv
          (polyAdd (polyAdd (polyAdd (cap 1) head) tail) (polyNeg (cap floor)))
          (polyAdd (polyAdd (cap 1) (polyNeg (cap floor))) (polyAdd head tail)) :=
        coeffEvalExpr_eqv_of_normalize_eq
          (.add (.add (.add (.var 0) (.var 1)) (.var 2)) (.neg (.var 3)))
          (.add (.add (.var 0) (.neg (.var 3))) (.add (.var 1) (.var 2)))
          (by decide)
          (fun
            | 0 => cap 1
            | 1 => head
            | 2 => tail
            | _ => cap floor)
      exact .ofCoeff
        ((hsplit.add (RatPolyCoeffEqv.refl _)).trans
          (hone.trans (hregroup.trans (hcap.add (RatPolyCoeffEqv.refl _))))) I.lower

/-- Actual positivity of the SAME original prefix, with no late-cutoff guard. -/
def prefixCertificate {w : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ half)
    {blocks : Nat} {x : RatPoly} (P : SquareBound blocks x 1)
    (K : Nat) (hK : 1 ≤ K) : Certificate blocks (heatPrefix w K x) :=
  positiveFromLowerWindow (prefixFloorCertificate hw0 hw P K hK)
    (Q'.le_of_lt floor_positive)

/-- The literal original slab face factor has the same produced floor. -/
def faceFloorCertificate {w : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ half)
    (K extent id : Nat) (hi : id ∈ slabPhysicalFaceEdges extent) (hK : 1 ≤ K) :
    Certificate (boundaryCompleteSlabLinks extent).length
      (polyAdd (faceHeatPolynomial w K extent id) (polyNeg (cap floor))) := by
  rw [faceHeatPolynomial_eq_sum]
  exact prefixFloorCertificate hw0 hw
    (.scalar (supported_slabPlaquette _ _) (haarNorm_slabPlaquette (slabPlaquetteAt_mem hi)))
    K hK

/-- ORIGINAL slab face positivity; neither the action nor canonical
late-cutoff consumer has been replaced. -/
def faceCertificate {w : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ half)
    (K extent id : Nat) (hi : id ∈ slabPhysicalFaceEdges extent) (hK : 1 ≤ K) :
    Certificate (boundaryCompleteSlabLinks extent).length (faceHeatPolynomial w K extent id) := by
  rw [faceHeatPolynomial_eq_sum]
  exact prefixCertificate hw0 hw
    (.scalar (supported_slabPlaquette _ _) (haarNorm_slabPlaquette (slabPlaquetteAt_mem hi)))
    K hK

#print axioms floor
#print axioms floor_positive
#print axioms higherLabelInterval
#print axioms prefixFloorCertificate
#print axioms prefixCertificate
#print axioms faceFloorCertificate
#print axioms faceCertificate

end YMGap.Continuum.QuaternionHaarSmallNomeHeatCertificate
