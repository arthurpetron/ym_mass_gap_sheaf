/-
# The actual negative cubic remainder as a positive form

The full cyclic tree depends on its source. Test linearity follows from its
actual polynomial mode fold; symmetry follows by identifying the same cubic
pairing with exact heat, omitted-mode and literal Casimir forms. The auxiliary
cutoff is a proof device only and does not enter the cubic form. Positive
diagonal path masses and the scalar cubic sign supply positivity, rather than
a supplied PSD assumption. These are finite Haar-form estimates, not an
interacting OWN-variance-relative or changing-family bound.
-/

import YMGap.Continuum.SU2QuaternionCyclicOmittedOperator
import YMGap.Continuum.SU2QuaternionExactRemainderForm

namespace YMGap.Continuum.SU2QuaternionCyclicCubicOperator

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionCyclicHeatModeExpansion
open YMGap.Continuum.SU2QuaternionCyclicModeTaylor
open YMGap.Continuum.SU2QuaternionCyclicDiagonalRemainder
open YMGap.Continuum.SU2QuaternionCyclicSecondOrder
open YMGap.Continuum.SU2QuaternionCyclicCasimirBilinear
open YMGap.Continuum.SU2QuaternionCyclicOmittedOperator
open YMGap.Continuum.SU2QuaternionExactRemainderForm
open YMGap.Continuum.SU2HeatRetainedCubicTaylor
open YMGap.Continuum.SU2HeatProductCutoffDebt (totalCasimirNat)
open YMGap.Continuum.SU2HeatCutoffCasimirBound
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.GNSQuotient

local infix:50 " ≈ " => Q'.eqv
local notation:max "H" n:arg => quaternionHaar n

/-- The original cubic pairing with its exact negative sign. -/
def cubicPair (tail : Nat) (w : Q') (p test : RatPoly) : Q' :=
  -(pairCubic tail w p test)

private theorem leafSum_neg (tail m : Nat) (p test : RatPoly)
    (weight : List Nat → Q') :
    leafSum tail m p test (fun ds => -(weight ds)) ≈
      -(leafSum tail m p test weight) :=
  Q'.eqv_trans _ _ _ (leafSum_congr tail m p test _ _ (fun ds _ =>
    poly_identity_of_normal_eq (.neg (.var 0)) (.mul (.neg (.const 1)) (.var 0))
      (by decide) (fun _ => weight ds)))
    (Q'.eqv_trans _ _ _ (leafSum_smul tail m p test (-1) weight)
      (poly_identity_of_normal_eq (.mul (.neg (.const 1)) (.var 0)) (.neg (.var 0))
        (by decide) (fun _ => leafSum tail m p test weight)))

/-- No source-degree or cutoff guard: every actual full path has a
nonnegative diagonal mass and a nonpositive scalar cubic coefficient. -/
theorem cubicPair_diagonal_nonnegative (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (p : RatPoly) (hp : SupportedQuaternionBlocks (tail+1) p) :
    (0 : Q') ≤ cubicPair tail w p p := by
  have hpos := full_leafSum_diagonal_nonnegative tail p hp
    (fun ds => -(cubicRemainder w (totalCasimirNat ds))) (fun ds _ =>
      Q'.le_trans' _ _ _ (Q'.le_of_eqv (by decide : (0 : Q') ≈ -0))
        (Q'.neg_le_neg (cubicRemainder_nonpositive hw0 hw1 (totalCasimirNat ds))))
  exact Q'.le_trans' _ _ _ hpos
    (Q'.le_of_eqv (leafSum_neg tail (tail+1) p p
      (fun ds => cubicRemainder w (totalCasimirNat ds))))

theorem cubicPair_test_congr (tail : Nat) (w : Q') (p : RatPoly)
    {left right : RatPoly} (h : RatPolyCoeffEqv left right) :
    cubicPair tail w p left ≈ cubicPair tail w p right :=
  Q'.neg_eqv_congr _ _ (Q'.eqv_trans _ _ _
    (leafSum_modeFold tail (tail+1) p left _).symm
    (Q'.eqv_trans _ _ _ (haar_of_coeff (h.mul_right _))
      (leafSum_modeFold tail (tail+1) p right _)))

theorem cubicPair_test_add (tail : Nat) (w : Q') (p f g : RatPoly) :
    cubicPair tail w p (polyAdd f g) ≈
      cubicPair tail w p f+cubicPair tail w p g := by
  have hs : H (tail+1) (polyMul (polyAdd f g)
      (modeFold tail (tail+1) p (fun ds => cubicRemainder w (totalCasimirNat ds)))) ≈
      H (tail+1) (polyMul f
        (modeFold tail (tail+1) p (fun ds => cubicRemainder w (totalCasimirNat ds))))+
      H (tail+1) (polyMul g
        (modeFold tail (tail+1) p (fun ds => cubicRemainder w (totalCasimirNat ds)))) := by
    rw [polyMul_add_left_exact]
    exact quaternionHaar_append _ _ _
  have h := Q'.eqv_trans _ _ _ (leafSum_modeFold tail (tail+1) p (polyAdd f g) _).symm
    (Q'.eqv_trans _ _ _ hs (Q'.add_eqv_congr'
      (leafSum_modeFold tail (tail+1) p f _) (leafSum_modeFold tail (tail+1) p g _)))
  exact Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ h) (Q'.neg_add_eqv_split _ _)

theorem cubicPair_test_smul (tail : Nat) (w : Q') (c : Q') (p f : RatPoly) :
    cubicPair tail w p (polySmul c f) ≈ c*cubicPair tail w p f := by
  have h := Q'.eqv_trans _ _ _ (leafSum_modeFold tail (tail+1) p (polySmul c f)
    (fun ds => cubicRemainder w (totalCasimirNat ds))).symm
    (Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.polyMul_smul_left c f _))
      (Q'.eqv_trans _ _ _ (quaternionHaar_polySmul (tail+1) c _)
        (Q'.mul_eqv_congr_left _ _ _ (leafSum_modeFold tail (tail+1) p f _))))
  exact Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ h)
    (poly_identity_of_normal_eq (.neg (.mul (.var 0) (.var 1)))
      (.mul (.var 0) (.neg (.var 1))) (by decide)
      (fun | 0 => c | _ => pairCubic tail w p f))

private theorem cubicPair_decomposition (tail : Nat) (w : Q') (K : Nat)
    (p test : RatPoly) (hp : SupportedQuaternionBlocks (tail+1) p) :
    cubicPair tail w p test ≈
      (HalfPow.half*(((1 : Q')-w)*((1 : Q')-w))) *
        (pairSecondMoment tail p test-pairCasimir tail p test) -
      exactRemainderPair tail w K p test-pairOmitted tail w K p test := by
  let c := HalfPow.half*(((1 : Q')-w)*((1 : Q')-w))
  have hr := Q'.eqv_trans _ _ _
    (exactRemainderPair_eq_pairRemainder tail w K p test hp)
    (pairRemainder_secondOrder tail w K p test)
  have hright : c*(pairSecondMoment tail p test-pairCasimir tail p test)-
      exactRemainderPair tail w K p test-pairOmitted tail w K p test ≈
      -(pairCubic tail w p test) :=
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr' (Q'.eqv_refl _) (Q'.neg_eqv_congr _ _ hr))
        (Q'.eqv_refl _))
      (poly_identity_of_normal_eq
        (.add (.add (.var 0) (.neg (.add (.add (.var 0) (.var 1)) (.neg (.var 2)))))
          (.neg (.var 2)))
        (.neg (.var 1)) (by decide)
        (fun | 0 => c*(pairSecondMoment tail p test-pairCasimir tail p test)
             | 1 => pairCubic tail w p test
             | _ => pairOmitted tail w K p test))
  exact hright.symm

/-- Symmetry derived at one auxiliary cutoff from actual same-operator
forms, not from linearity of the input-dependent ragged tree. -/
theorem cubicPair_symm (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (p test : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p)
    (ht : SupportedQuaternionBlocks (tail+1) test) :
    cubicPair tail w p test ≈ cubicPair tail w test p := by
  let K := sufficientCutoff w
  let R := exactRemainderGNSData tail w hw0 hw1 K (Nat.le_refl _)
  have hr : exactRemainderPair tail w K p test ≈ exactRemainderPair tail w K test p :=
    R.B_symm ⟨p,hp⟩ ⟨test,ht⟩
  have hs : pairSecondMoment tail p test ≈ pairSecondMoment tail test p :=
    Q'.eqv_trans _ _ _ (pairSecondMoment_literal tail p test hp ht)
      (Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
        (pairSecondMoment_literal tail test p ht hp).symm)
  exact Q'.eqv_trans _ _ _ (cubicPair_decomposition tail w K p test hp)
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_left _ _ _ (Q'.add_eqv_congr' hs
          (Q'.neg_eqv_congr _ _ (pairCasimir_symm tail p test hp ht))))
        (Q'.neg_eqv_congr _ _ hr))
      (Q'.neg_eqv_congr _ _ (pairOmitted_symm tail w K p test hp ht)))
      (cubicPair_decomposition tail w K test p ht).symm)

/-- Concrete positive bilinear data on the SAME supported-polynomial carrier.
The form uses the actual test-left pairing, with no supplied positivity input. -/
def cubicGNSData (tail : Nat) (w : Q') (hw0 : (0 : Q') ≤ w)
    (hw1 : w < (1 : Q')) : GNSData :=
  { omittedGNSData tail w hw0 0 with
    B := fun p q => cubicPair tail w q.val p.val
    B_congr_left := fun q h => cubicPair_test_congr tail w q.val h
    B_add_left := fun p q r => cubicPair_test_add tail w r.val p.val q.val
    B_smul_left := fun c p q => cubicPair_test_smul tail w c q.val p.val
    B_symm := fun p q => cubicPair_symm tail hw0 hw1 q.val p.val q.property p.property
    self_nonneg := fun p => cubicPair_diagonal_nonnegative tail hw0
      (Q'.le_of_lt hw1) p.val p.property }

/-- Sharp Cauchy--Schwarz for the exact negative cubic remainder. -/
theorem cubicPair_cauchySchwarz (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (p test : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p)
    (ht : SupportedQuaternionBlocks (tail+1) test) :
    cubicPair tail w p test*cubicPair tail w p test ≤
      cubicPair tail w p p*cubicPair tail w test test :=
  Q'.le_trans' _ _ _ ((cubicGNSData tail w hw0 hw1).cauchy_schwarz ⟨test,ht⟩ ⟨p,hp⟩)
    (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))

/-- The upper mixed sign is paid by actual diagonal norms, without absolute
leaf costs. The sharp squared estimate is separately available above. -/
theorem cubicPair_le_half_diagonals (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (p test : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p)
    (ht : SupportedQuaternionBlocks (tail+1) test) :
    cubicPair tail w p test ≤
      HalfPow.half*(cubicPair tail w p p+cubicPair tail w test test) := by
  let D := cubicGNSData tail w hw0 hw1
  let a : D.V := ⟨test,ht⟩
  let b : D.V := ⟨p,hp⟩
  let v := D.add (D.smul 1 a) (D.smul (-1) b)
  have hpos := Q'.mul_nonneg _ _ HalfPow.half_nonneg (D.self_nonneg v)
  have hexp := Q'.mul_eqv_congr_left HalfPow.half _ _ (D.diag_expand 1 (-1) a b)
  have hreg : HalfPow.half*D.B v v ≈
      HalfPow.half*(D.B b b+D.B a a) + -((HalfPow.half*2)*(D.B a b)) :=
    Q'.eqv_trans _ _ _ hexp (poly_identity_of_normal_eq
      (.mul (.var 3)
        (.add (.add (.mul (.const 1) (.mul (.const 1) (.var 0)))
                    (.mul (.const 1) (.mul (.neg (.const 1)) (.var 1))))
              (.add (.mul (.neg (.const 1)) (.mul (.const 1) (.var 1)))
                    (.mul (.neg (.const 1)) (.mul (.neg (.const 1)) (.var 2))))))
      (.add (.mul (.var 3) (.add (.var 2) (.var 0)))
        (.neg (.mul (.mul (.var 3) (.const 2)) (.var 1))))
      (by decide) (fun | 0 => D.B a a | 1 => D.B a b
                       | 2 => D.B b b | _ => HalfPow.half))
  have hcross : -((HalfPow.half*2)*(D.B a b)) ≈ -(D.B a b) :=
    Q'.neg_eqv_congr _ _ (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (by decide : HalfPow.half*2 ≈ (1 : Q')))
      (Q'.one_mul_eqv _))
  have hpin := Q'.eqv_trans _ _ _ hreg (Q'.add_eqv_congr' (Q'.eqv_refl _) hcross)
  exact OSReconstructionProgress.q_le_of_sub_nonneg
    (Q'.le_trans' _ _ _ hpos (Q'.le_of_eqv hpin))

/-- The COMPLETE source cubic correction, with its original mixed-minus-
diagonal signs, bounded by three actual cubic diagonals. No source positivity,
OWN-mean identification or absolute coefficient budget is used. -/
theorem sourceCubic_le_diagonalNorms (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (q f : RatPoly)
    (hq : SupportedQuaternionBlocks (tail+1) q)
    (hf : SupportedQuaternionBlocks (tail+1) f) :
    sourceCubic tail w q f ≤
      HalfPow.half*(cubicPair tail w q q+
        cubicPair tail w (polyMul q (polyMul f f)) (polyMul q (polyMul f f)))+
      cubicPair tail w (polyMul q f) (polyMul q f) := by
  have hqf2 := supported_polyMul hq (supported_polyMul hf hf)
  have hnegative := cubicPair_le_half_diagonals tail hw0 hw1 q
    (polySmul (-1) (polyMul q (polyMul f f))) hq (polySmul_supported hqf2 (-1))
  have hsmul := cubicPair_test_smul tail w (-1) q (polyMul q (polyMul f f))
  have hdiag : cubicPair tail w (polySmul (-1) (polyMul q (polyMul f f)))
      (polySmul (-1) (polyMul q (polyMul f f))) ≈
      cubicPair tail w (polyMul q (polyMul f f)) (polyMul q (polyMul f f)) := by
    let D := cubicGNSData tail w hw0 hw1
    let a : D.V := ⟨polyMul q (polyMul f f),hqf2⟩
    exact Q'.eqv_trans _ _ _ (D.B_smul_left (-1) a (D.smul (-1) a))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left (-1) _ _ (D.B_smul_right (-1) a a))
        (poly_identity_of_normal_eq (.mul (.neg (.const 1))
          (.mul (.neg (.const 1)) (.var 0))) (.var 0) (by decide)
          (fun _ => D.B a a)))
  have hleft : cubicPair tail w q (polySmul (-1) (polyMul q (polyMul f f))) ≈
      -(cubicPair tail w q (polyMul q (polyMul f f))) :=
    Q'.eqv_trans _ _ _ hsmul (poly_identity_of_normal_eq
      (.mul (.neg (.const 1)) (.var 0)) (.neg (.var 0)) (by decide)
      (fun _ => cubicPair tail w q (polyMul q (polyMul f f))))
  have hneg : -(cubicPair tail w q (polyMul q (polyMul f f))) ≤
      HalfPow.half*(cubicPair tail w q q+
        cubicPair tail w (polyMul q (polyMul f f)) (polyMul q (polyMul f f))) :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
      (Q'.le_trans' _ _ _ hnegative
        (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _
          (Q'.add_eqv_congr' (Q'.eqv_refl _) hdiag))))
  have hpin : sourceCubic tail w q f ≈
      -(cubicPair tail w q (polyMul q (polyMul f f)))+
        cubicPair tail w (polyMul q f) (polyMul q f) :=
    poly_identity_of_normal_eq (.add (.var 0) (.neg (.var 1)))
      (.add (.neg (.neg (.var 0))) (.neg (.var 1))) (by decide)
      (fun | 0 => pairCubic tail w q (polyMul q (polyMul f f))
           | _ => pairCubic tail w (polyMul q f) (polyMul q f))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hpin)
    (Q'.add_le_add_right _ _ _ hneg)

#print axioms cubicPair
#print axioms cubicPair_diagonal_nonnegative
#print axioms cubicPair_test_congr
#print axioms cubicPair_test_add
#print axioms cubicPair_test_smul
#print axioms cubicPair_symm
#print axioms cubicGNSData
#print axioms cubicPair_cauchySchwarz
#print axioms cubicPair_le_half_diagonals
#print axioms sourceCubic_le_diagonalNorms

end YMGap.Continuum.SU2QuaternionCyclicCubicOperator
