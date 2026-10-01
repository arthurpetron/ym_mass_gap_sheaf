/-
# Signed second order on the ORIGINAL cyclic cutoff tree

Keep the mixed second Casimir coefficient before absolute estimates. The
remainder separates an explicit cubic budget from the EXACT heat coefficients
removed above the coordinatewise cutoff. In particular the cubic bound is
not asserted for the original cutoff remainder without its omitted-mode debt.
No changing-source, volume or SAME-variance uniformity is asserted.
-/

import YMGap.Continuum.SU2HeatProductCutoffDebt
import YMGap.Continuum.SU2QuaternionCyclicCasimirMixed
import YMGap.Continuum.SU2QuaternionProductHeatAngularTaylor

namespace YMGap.Continuum.SU2QuaternionCyclicSecondOrder

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionCyclicModeTaylor
open YMGap.Continuum.SU2QuaternionCyclicCasimirMixed
open YMGap.Continuum.SU2HeatProductTaylorRemainder
open YMGap.Continuum.SU2HeatProductCutoffDebt
open YMGap.Continuum.SU2HeatRetainedCubicTaylor
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.SU2QuaternionChannelCasimirSquare
open YMGap.Continuum.SU2QuaternionProductHeatSourceTaylor
open YMGap.Continuum.SU2QuaternionProductHeatAngularTaylor
open YMGap.Continuum.SU2QuaternionProductHeatProjectedSourceEnergy

local infix:50 " ≈ " => Q'.eqv

private theorem leafSum_neg (tail m : Nat) (p test : RatPoly)
    (weight : List Nat → Q') :
    leafSum tail m p test (fun ds => -(weight ds)) ≈
      -(leafSum tail m p test weight) := by
  exact Q'.eqv_trans _ _ _ (leafSum_congr tail m p test _ _ (fun ds _ =>
    poly_identity_of_normal_eq (.neg (.var 0)) (.mul (.neg (.const 1)) (.var 0))
      (by decide) (fun _ => weight ds)))
    (Q'.eqv_trans _ _ _ (leafSum_smul tail m p test (-1) weight)
      (poly_identity_of_normal_eq (.mul (.neg (.const 1)) (.var 0))
        (.neg (.var 0)) (by decide) (fun _ => leafSum tail m p test weight)))

private theorem leafSum_sub (tail m : Nat) (p test : RatPoly)
    (a b : List Nat → Q') :
    leafSum tail m p test (fun ds => a ds-b ds) ≈
      leafSum tail m p test a - leafSum tail m p test b :=
  Q'.eqv_trans _ _ _ (leafSum_add tail m p test a (fun ds => -(b ds)))
    (Q'.add_eqv_congr' (Q'.eqv_refl _) (leafSum_neg tail m p test b))

def pairSecondMoment (tail : Nat) (p test : RatPoly) : Q' :=
  leafSum tail (tail+1) p test (fun ds => totalCasimir ds*totalCasimir ds)

def pairCubic (tail : Nat) (w : Q') (p test : RatPoly) : Q' :=
  leafSum tail (tail+1) p test (fun ds => cubicRemainder w (totalCasimirNat ds))

def pairOmitted (tail : Nat) (w : Q') (K : Nat) (p test : RatPoly) : Q' :=
  leafSum tail (tail+1) p test (omittedDebt w K)

/-- The fixed-input cubic coefficient budget. It still depends on the COMPLETE
source/test tree; no bound relative to an interacting variance is supplied. -/
def pairCubicBudget (tail : Nat) (p test : RatPoly) : Q' :=
  leafAbsSum tail (tail+1) p test
    (fun ds => cubicBudget (totalCasimirNat ds))

def pairOmittedBudget (tail : Nat) (w : Q') (K : Nat) (p test : RatPoly) : Q' :=
  leafAbsSum tail (tail+1) p test (omittedDebt w K)

/-- The original signed pairing, including EVERY computed omitted path. -/
theorem pairRemainder_secondOrder (tail : Nat) (w : Q') (K : Nat)
    (p test : RatPoly) :
    pairRemainder tail w K p test ≈
      (HalfPow.half*(((1 : Q')-w)*((1 : Q')-w))) *
        (pairSecondMoment tail p test-pairCasimir tail p test) +
      pairCubic tail w p test - pairOmitted tail w K p test := by
  let c := HalfPow.half*(((1 : Q')-w)*((1 : Q')-w))
  let square := fun ds => totalCasimir ds*totalCasimir ds
  let cubic := fun ds => cubicRemainder w (totalCasimirNat ds)
  let debt := omittedDebt w K
  have hscalar := leafSum_congr tail (tail+1) p test _ _
    (fun ds _ => productRemainder_secondOrder w K ds)
  have hquad : leafSum tail (tail+1) p test
      (fun ds => c*(square ds-totalCasimir ds)) ≈
      c*(pairSecondMoment tail p test-pairCasimir tail p test) :=
    Q'.eqv_trans _ _ _ (leafSum_smul tail (tail+1) p test c _)
      (Q'.mul_eqv_congr_left c _ _ (leafSum_sub tail (tail+1) p test square totalCasimir))
  exact Q'.eqv_trans _ _ _ hscalar
    (Q'.eqv_trans _ _ _ (leafSum_sub tail (tail+1) p test
      (fun ds => c*(square ds-totalCasimir ds)+cubic ds) debt)
      (Q'.add_eqv_congr'
        (Q'.eqv_trans _ _ _ (leafSum_add tail (tail+1) p test _ cubic)
          (Q'.add_eqv_congr' hquad (Q'.eqv_refl _))) (Q'.eqv_refl _)))

/-- Identify the coefficient with the literal Casimir BEFORE bounding it. -/
theorem pairSecondMoment_literal (tail : Nat) (p test : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p)
    (ht : SupportedQuaternionBlocks (tail+1) test) :
    pairSecondMoment tail p test ≈ quaternionHaar (tail+1) (polyMul
      (activeCasimirPolynomial (List.range (tail+1)) p)
      (activeCasimirPolynomial (List.range (tail+1)) test)) :=
  full_mixedSecondMoment_eq_literal tail p test hp ht

/-- The omitted coefficient is nonnegative, but the ACTUAL leaf pairings
are signed: this theorem bounds their sum, not a supposed positive mass. -/
theorem pairOmitted_bounds (tail : Nat) {w : Q'} (hw0 : (0 : Q') ≤ w)
    (K : Nat) (p test : RatPoly) :
    -(pairOmittedBudget tail w K p test) ≤ pairOmitted tail w K p test ∧
      pairOmitted tail w K p test ≤ pairOmittedBudget tail w K p test :=
  leaf_two_sided_bound tail (tail+1) p test (omittedDebt w K) (omittedDebt w K)
    (fun ds _ => omittedDebt_nonnegative hw0 K ds)
    (fun _ _ => Q'.le_refl' _)
    (fun ds _ => omittedDebt_nonnegative hw0 K ds)

/-- The cubic coefficient is bounded only AFTER preserving the signed
quadratic mixed-minus-diagonal expression. No bound on the changing source
budget is asserted. -/
theorem pairCubic_bounds (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (p test : RatPoly) :
    -(((((1 : Q')-w)*((1 : Q')-w))*((1 : Q')-w))*pairCubicBudget tail p test) ≤
      pairCubic tail w p test ∧
    pairCubic tail w p test ≤
      ((((1 : Q')-w)*((1 : Q')-w))*((1 : Q')-w))*pairCubicBudget tail p test := by
  let h3 := (((1 : Q')-w)*((1 : Q')-w))*((1 : Q')-w)
  let weight := fun ds => -(cubicRemainder w (totalCasimirNat ds))
  let bound := fun ds => h3*cubicBudget (totalCasimirNat ds)
  have hh := Q'.sub_nonneg_of_le hw1
  have h30 : (0 : Q') ≤ h3 := Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ hh hh) hh
  have hw : ∀ ds : List Nat, (0 : Q') ≤ weight ds := by
    intro ds
    have h := Q'.neg_le_neg (cubicRemainder_nonpositive hw0 hw1 (totalCasimirNat ds))
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (by decide : (0 : Q') ≈ -0)) h
  have hb : ∀ ds : List Nat, weight ds ≤ bound ds := by
    intro ds
    have h := Q'.neg_le_neg (cubicRemainder_budget_lower hw0 hw1 (totalCasimirNat ds))
    exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (poly_identity_of_normal_eq
      (.neg (.neg (.mul (.var 0) (.var 1)))) (.mul (.var 1) (.var 0))
      (by decide) (fun | 0 => cubicBudget (totalCasimirNat ds) | _ => h3)))
  have hbounds := leaf_two_sided_bound tail (tail+1) p test weight bound
    (fun ds _ => hw ds) (fun ds _ => hb ds)
    (fun ds _ => Q'.mul_nonneg _ _ h30 (cubicBudget_nonnegative (totalCasimirNat ds)))
  have hneg : -(leafSum tail (tail+1) p test weight) ≈ pairCubic tail w p test :=
    Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _
      (leafSum_neg tail (tail+1) p test (fun ds => cubicRemainder w (totalCasimirNat ds))))
      (Q'.neg_neg_eqv _)
  have hbudget : leafAbsSum tail (tail+1) p test bound ≈ h3*pairCubicBudget tail p test :=
    leafAbsSum_smul tail (tail+1) p test h3 (fun ds => cubicBudget (totalCasimirNat ds))
  have hl := Q'.neg_le_neg hbounds.2
  have hu := Q'.neg_le_neg hbounds.1
  constructor
  · exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.neg_eqv_congr _ _ hbudget))
      (Q'.le_trans' _ _ _ hl (Q'.le_of_eqv hneg))
  · exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hneg)
      (Q'.le_trans' _ _ _ hu
        (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.neg_neg_eqv _) hbudget)))

/-- A computed cutoff tail factor times the original absolute leaf pairings.
Its input dependence remains explicit; this is NOT variance-normalized. -/
theorem pairOmitted_tail_bounds (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (K : Nat) (p test : RatPoly) :
    (let cap := RGTransport.qpow w ((K+1)*(K+3)) *
      leafAbsSum tail (tail+1) p test (fun _ => (1 : Q'));
      -cap ≤ pairOmitted tail w K p test ∧ pairOmitted tail w K p test ≤ cap) := by
  let c := RGTransport.qpow w ((K+1)*(K+3))
  have hc : (0 : Q') ≤ c := RGTransport.qpow_nonneg w hw0 _
  have h := leaf_two_sided_bound tail (tail+1) p test (omittedDebt w K) (fun _ => c*(1 : Q'))
    (fun ds _ => omittedDebt_nonnegative hw0 K ds)
    (fun ds _ => Q'.le_trans' _ _ _ (omittedDebt_le_tail hw0 hw1 K ds)
      (Q'.ge_of_eqv (Q'.mul_one_eqv c)))
    (fun _ _ => Q'.mul_nonneg _ _ hc Q'.zero_le_one)
  have he : leafAbsSum tail (tail+1) p test (fun _ => c*1) ≈
      c*leafAbsSum tail (tail+1) p test (fun _ => (1 : Q')) :=
    leafAbsSum_smul tail (tail+1) p test c (fun _ => (1 : Q'))
  exact ⟨Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.neg_eqv_congr _ _ he)) h.1,
    Q'.le_trans' _ _ _ h.2 (Q'.le_of_eqv he)⟩
/-- Keep the complete mixed-minus-diagonal coefficient, including all signed
cross terms of a source family. Its second term is the NEGATIVE Casimir square. -/
def sourceSecondMoment (tail : Nat) (a f : RatPoly) : Q' :=
  pairSecondMoment tail a (polyMul a (polyMul f f)) -
    pairSecondMoment tail (polyMul a f) (polyMul a f)

def sourceCubic (tail : Nat) (w : Q') (a f : RatPoly) : Q' :=
  pairCubic tail w a (polyMul a (polyMul f f)) -
    pairCubic tail w (polyMul a f) (polyMul a f)

def sourceOmitted (tail : Nat) (w : Q') (K : Nat) (a f : RatPoly) : Q' :=
  pairOmitted tail w K a (polyMul a (polyMul f f)) -
    pairOmitted tail w K (polyMul a f) (polyMul a f)

/-- Exact original source correction. The first-order difference has its
original sign, so the quadratic energy coefficient is D2+A, NOT D2-A. -/
theorem sourceRemainder_secondOrder (tail : Nat) (w : Q') (K : Nat)
    (a f : RatPoly) :
    pairRemainder tail w K a (polyMul a (polyMul f f)) -
      pairRemainder tail w K (polyMul a f) (polyMul a f) ≈
    (HalfPow.half*(((1 : Q')-w)*((1 : Q')-w))) *
      (sourceSecondMoment tail a f+sourceFirstOrder tail a f) +
      sourceCubic tail w a f-sourceOmitted tail w K a f := by
  have hm := pairRemainder_secondOrder tail w K a (polyMul a (polyMul f f))
  have hd := pairRemainder_secondOrder tail w K (polyMul a f) (polyMul a f)
  exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hm (Q'.neg_eqv_congr _ _ hd))
    (poly_identity_of_normal_eq
      (.add (.add (.add (.mul (.var 0) (.add (.var 1) (.neg (.var 2))))
          (.var 5)) (.neg (.var 7)))
        (.neg (.add (.add (.mul (.var 0) (.add (.var 3) (.neg (.var 4))))
          (.var 6)) (.neg (.var 8)))))
      (.add (.add (.mul (.var 0)
        (.add (.add (.var 1) (.neg (.var 3)))
          (.add (.var 4) (.neg (.var 2)))))
        (.add (.var 5) (.neg (.var 6))))
        (.neg (.add (.var 7) (.neg (.var 8)))))
      (by decide) (fun
        | 0 => HalfPow.half*(((1 : Q')-w)*((1 : Q')-w))
        | 1 => pairSecondMoment tail a (polyMul a (polyMul f f))
        | 2 => pairCasimir tail a (polyMul a (polyMul f f))
        | 3 => pairSecondMoment tail (polyMul a f) (polyMul a f)
        | 4 => pairCasimir tail (polyMul a f) (polyMul a f)
        | 5 => pairCubic tail w a (polyMul a (polyMul f f))
        | 6 => pairCubic tail w (polyMul a f) (polyMul a f)
        | 7 => pairOmitted tail w K a (polyMul a (polyMul f f))
        | _ => pairOmitted tail w K (polyMul a f) (polyMul a f)))

theorem sourceSecondMoment_literal (tail : Nat) (a f : RatPoly)
    (ha : SupportedQuaternionBlocks (tail+1) a)
    (hf : SupportedQuaternionBlocks (tail+1) f) :
    sourceSecondMoment tail a f ≈
      quaternionHaar (tail+1) (polyMul
        (activeCasimirPolynomial (List.range (tail+1)) a)
        (activeCasimirPolynomial (List.range (tail+1)) (polyMul a (polyMul f f)))) -
      quaternionHaar (tail+1) (polyMul
        (activeCasimirPolynomial (List.range (tail+1)) (polyMul a f))
        (activeCasimirPolynomial (List.range (tail+1)) (polyMul a f))) :=
  Q'.add_eqv_congr'
    (pairSecondMoment_literal tail a (polyMul a (polyMul f f)) ha
      (supported_polyMul ha (supported_polyMul hf hf)))
    (Q'.neg_eqv_congr _ _ (pairSecondMoment_literal tail (polyMul a f) (polyMul a f)
      (supported_polyMul ha hf) (supported_polyMul ha hf)))

/-- The ORIGINAL energy, not an untruncated surrogate: the omitted source
term is subtracted explicitly and is not assigned a favorable sign. -/
theorem sourceEnergy_secondOrder (tail : Nat) (w : Q') (K : Nat) (a f : RatPoly)
    (ha : SupportedQuaternionBlocks (tail+1) a)
    (hf : SupportedQuaternionBlocks (tail+1) f) :
    sourceEnergy (tail+1) w K (List.range (tail+1)) a f ≈
      ((1 : Q')-w)*weightedAngularEnergy tail a f +
      ((HalfPow.half*(((1 : Q')-w)*((1 : Q')-w))) *
        (sourceSecondMoment tail a f+weightedAngularEnergy tail a f) +
        sourceCubic tail w a f-sourceOmitted tail w K a f) :=
  Q'.eqv_trans _ _ _ (sourceEnergy_taylor_angular tail w K a f ha hf)
    (Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.eqv_trans _ _ _ (sourceRemainder_secondOrder tail w K a f)
        (Q'.add_eqv_congr'
          (Q'.add_eqv_congr'
            (Q'.mul_eqv_congr_left _ _ _ (Q'.add_eqv_congr' (Q'.eqv_refl _)
              (sourceFirstOrder_eq_weightedAngularEnergy tail a f ha hf)))
            (Q'.eqv_refl _)) (Q'.eqv_refl _))))

/-- Only the cubic and omitted-mode terms are absolutized. The quadratic
interaction coefficient and its negative diagonal square remain signed. -/
def sourceErrorBudget (tail : Nat) (w : Q') (K : Nat) (a f : RatPoly) : Q' :=
  ((((1 : Q')-w)*((1 : Q')-w))*((1 : Q')-w)) *
    (pairCubicBudget tail a (polyMul a (polyMul f f)) +
      pairCubicBudget tail (polyMul a f) (polyMul a f)) +
    (pairOmittedBudget tail w K a (polyMul a (polyMul f f)) +
      pairOmittedBudget tail w K (polyMul a f) (polyMul a f))

private theorem neg_lower_le {a b : Q'} (h : -b ≤ a) : -a ≤ b :=
  Q'.le_trans' _ _ _ (Q'.neg_le_neg h) (Q'.le_of_eqv (Q'.neg_neg_eqv b))

theorem sourceError_bound (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (K : Nat) (a f : RatPoly) :
    sourceCubic tail w a f-sourceOmitted tail w K a f ≤
      sourceErrorBudget tail w K a f := by
  have hm := pairCubic_bounds tail hw0 hw1 a (polyMul a (polyMul f f))
  have hd := pairCubic_bounds tail hw0 hw1 (polyMul a f) (polyMul a f)
  have hc := Q'.add_le_add hm.2 (neg_lower_le hd.1)
  have hom := pairOmitted_bounds tail hw0 K a (polyMul a (polyMul f f))
  have hod := pairOmitted_bounds tail hw0 K (polyMul a f) (polyMul a f)
  have ho := Q'.add_le_add (neg_lower_le hom.1) hod.2
  have hsum := Q'.add_le_add hc ho
  have hleft : sourceCubic tail w a f-sourceOmitted tail w K a f ≈
      sourceCubic tail w a f +
        (-(pairOmitted tail w K a (polyMul a (polyMul f f))) +
          pairOmitted tail w K (polyMul a f) (polyMul a f)) :=
    poly_identity_of_normal_eq
      (.add (.var 0) (.neg (.add (.var 1) (.neg (.var 2)))))
      (.add (.var 0) (.add (.neg (.var 1)) (.var 2))) (by decide)
      (fun | 0 => sourceCubic tail w a f
           | 1 => pairOmitted tail w K a (polyMul a (polyMul f f))
           | _ => pairOmitted tail w K (polyMul a f) (polyMul a f))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv (Q'.add_eqv_congr'
      (Q'.eqv_symm (Q'.mul_add_eqv _ _ _)) (Q'.eqv_refl _))))

/-- An actual finite energy estimate retaining the mixed quadratic
cancellation. Its explicit changing-source error budget still needs a
SAME-variance estimate before it can be used for physical scaling. -/
theorem sourceEnergy_le_secondOrder (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (K : Nat) (a f : RatPoly)
    (ha : SupportedQuaternionBlocks (tail+1) a)
    (hf : SupportedQuaternionBlocks (tail+1) f) :
    sourceEnergy (tail+1) w K (List.range (tail+1)) a f ≤
      ((1 : Q')-w)*weightedAngularEnergy tail a f +
        ((HalfPow.half*(((1 : Q')-w)*((1 : Q')-w))) *
          (sourceSecondMoment tail a f+weightedAngularEnergy tail a f) +
          sourceErrorBudget tail w K a f) := by
  have h := sourceError_bound tail hw0 hw1 K a f
  have hgroup :
      (HalfPow.half*(((1 : Q')-w)*((1 : Q')-w))) *
        (sourceSecondMoment tail a f+weightedAngularEnergy tail a f) +
        sourceCubic tail w a f-sourceOmitted tail w K a f ≈
      (HalfPow.half*(((1 : Q')-w)*((1 : Q')-w))) *
        (sourceSecondMoment tail a f+weightedAngularEnergy tail a f) +
        (sourceCubic tail w a f-sourceOmitted tail w K a f) :=
    Q'.add_assoc_eqv _ _ _
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (sourceEnergy_secondOrder tail w K a f ha hf))
    (Q'.add_le_add_left _ _ _ (Q'.le_trans' _ _ _ (Q'.le_of_eqv hgroup)
      (Q'.add_le_add_left _ _ _ h)))
#print axioms pairSecondMoment
#print axioms pairCubic
#print axioms pairOmitted
#print axioms pairCubicBudget
#print axioms pairOmittedBudget
#print axioms pairRemainder_secondOrder
#print axioms pairSecondMoment_literal
#print axioms pairOmitted_bounds
#print axioms pairCubic_bounds
#print axioms pairOmitted_tail_bounds
#print axioms sourceSecondMoment
#print axioms sourceCubic
#print axioms sourceOmitted
#print axioms sourceRemainder_secondOrder
#print axioms sourceSecondMoment_literal
#print axioms sourceEnergy_secondOrder
#print axioms sourceErrorBudget
#print axioms sourceError_bound
#print axioms sourceEnergy_le_secondOrder

end YMGap.Continuum.SU2QuaternionCyclicSecondOrder
