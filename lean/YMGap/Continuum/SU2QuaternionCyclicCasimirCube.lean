/-
# Actual third Casimir moment and a cubic diagonal norm cap

Full-path eigenaction identifies the SIGNED third moment with the literal
Haar pairing H[(C p)(C^2 p)]. Positivity comes from the actual path kernels,
not assumed joint orthogonality. Scalar cubic comparison then bounds the
negative cubic diagonal by h^3/6 times that SAME differential moment.

This is the full-carrier Casimir, not an active-only surrogate. No comparison
with interacting variance or useful changing-family estimate is asserted.
-/

import YMGap.Continuum.SU2QuaternionCyclicSecondOrder
import YMGap.Continuum.SU2QuaternionDiagonalRemainderMoment

namespace YMGap.Continuum.SU2QuaternionCyclicCasimirCube

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionCyclicHeatModeExpansion
open YMGap.Continuum.SU2QuaternionCyclicModeTaylor
open YMGap.Continuum.SU2QuaternionCyclicPathReassembly
open YMGap.Continuum.SU2QuaternionCyclicCasimirBilinear
open YMGap.Continuum.SU2QuaternionCyclicDiagonalRemainder
open YMGap.Continuum.SU2QuaternionCyclicPathCasimir
open YMGap.Continuum.SU2QuaternionChannelCasimirSquare
open YMGap.Continuum.SU2QuaternionLiteralCasimirPairing
open YMGap.Continuum.SU2QuaternionCyclicSecondOrder
open YMGap.Continuum.SU2QuaternionDiagonalRemainderMoment
open YMGap.Continuum.SU2HeatProductTaylorRemainder
open YMGap.Continuum.SU2HeatProductCutoffDebt (totalCasimirNat totalCasimirNat_pin)
open YMGap.Continuum.SU2HeatRetainedCubicTaylor
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv
local notation:max "H" n:arg => quaternionHaar n

/-- Exact rational coefficient, carried as computable data. -/
def sixth : Q' := Q'.mkPos 1 6 (by decide)

theorem sixth_nonnegative : (0 : Q') ≤ sixth := by decide

private theorem mul_congr {a b c d : Q'} (ha : a ≈ b) (hc : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hc)

/-- Denominator-free recurrence pays at most n^3/6, including n=0,1,2. -/
theorem cubicBudget_le_cube : ∀ n : Nat,
    cubicBudget n ≤ sixth*((Q'.ofNat n*Q'.ofNat n)*Q'.ofNat n)
  | 0 => by decide
  | n+1 => by
      let N := Q'.ofNat n
      have hN : Q'.ofNat (n+1) ≈ N+1 := Q'.ofNat_add_eqv n 1
      have hright : sixth*((Q'.ofNat (n+1)*Q'.ofNat (n+1))*Q'.ofNat (n+1)) ≈
          (sixth*((N*N)*N)+quadraticCoeff n)+(N+sixth) :=
        Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left sixth _ _
            (mul_congr (mul_congr hN hN) hN))
          (Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
            (.mul (.var 1) (.mul (.mul (.add (.var 0) (.const 1))
              (.add (.var 0) (.const 1))) (.add (.var 0) (.const 1))))
            (.add (.add (.mul (.var 1) (.mul (.mul (.var 0) (.var 0)) (.var 0)))
              (.mul (.mul (.const 3) (.var 1))
                (.add (.mul (.var 0) (.var 0)) (.neg (.var 0)))))
              (.add (.mul (.mul (.const 6) (.var 1)) (.var 0)) (.var 1)))
            (by decide) (fun | 0 => N | _ => sixth))
            (Q'.add_eqv_congr'
              (Q'.add_eqv_congr' (Q'.eqv_refl _)
                (Q'.mul_eqv_congr_right _ _ _ (by decide : 3*sixth ≈ HalfPow.half)))
              (Q'.add_eqv_congr' (Q'.eqv_trans _ _ _
                (Q'.mul_eqv_congr_right _ _ N (by decide : 6*sixth ≈ (1 : Q')))
                (Q'.one_mul_eqv N)) (Q'.eqv_refl _))))
      have hstep := Q'.add_le_add_right _ _ (quadraticCoeff n) (cubicBudget_le_cube n)
      have hpay : (0 : Q') ≤ N+sixth :=
        Q'.zero_le_add _ _ (CReal.ofNat_le_ofNat (Nat.zero_le n)) sixth_nonnegative
      exact Q'.le_trans' _ _ _ hstep
        (Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ _ hpay) (Q'.ge_of_eqv hright))

private theorem path_supported (tail : Nat) : ∀ (ds : List Nat) (p : RatPoly),
    SupportedQuaternionBlocks (tail+1) p →
    SupportedQuaternionBlocks (tail+1) (pathPiece tail p ds)
  | [], _, hp => hp
  | d::ds, p, _ => path_supported tail ds (nextPiece tail p d)
      (nextPiece_supported tail p d)

private theorem path_casimir_test (tail : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p) (ds : List Nat)
    (hlen : ds.length = tail+1) (hpath : ValidPath tail p ds) :
    H (tail+1) (polyMul (activeCasimirPolynomial (List.range (tail+1)) p)
      (pathPiece tail p ds)) ≈
      totalCasimir ds * H (tail+1) (polyMul p (pathPiece tail p ds)) := by
  let piece := pathPiece tail p ds
  let Cp := activeCasimirPolynomial (List.range (tail+1)) p
  have hs : SupportedQuaternionBlocks (tail+1) piece := path_supported tail ds p hp
  have he := full_path_activeCasimir_carrier tail p hp ds hlen hpath
  exact Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm Cp piece))
    (Q'.eqv_trans _ _ _ (pairCasimir_eq_literal tail p piece hp hs).symm
      (Q'.eqv_trans _ _ _ (pairCasimir_symm tail p piece hp hs)
        (Q'.eqv_trans _ _ _ (pairCasimir_eq_literal tail piece p hs hp)
          (Q'.eqv_trans _ _ _ (he p)
            (quaternionHaar_polyMul_smul_right (tail+1) (totalCasimir ds) p piece)))))

/-- SAME literal full-Casimir third moment, with all signed cross terms. -/
def thirdMoment (tail : Nat) (p : RatPoly) : Q' :=
  let Cp := activeCasimirPolynomial (List.range (tail+1)) p
  H (tail+1) (polyMul Cp (activeCasimirPolynomial (List.range (tail+1)) Cp))

/-- The path moment is computed by the existing differential operator. -/
theorem full_cubeMoment_eq_literal (tail : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p) :
    leafSum tail (tail+1) p p (fun ds => (totalCasimir ds*totalCasimir ds)*totalCasimir ds) ≈
      thirdMoment tail p := by
  let Cp := activeCasimirPolynomial (List.range (tail+1)) p
  have hCp : SupportedQuaternionBlocks (tail+1) Cp :=
    activeCasimirPolynomial_supported (List.range (tail+1))
      (fun i hi => List.mem_range.mp hi) hp
  have hsum : pairSecondMoment tail p Cp ≈
      leafSum tail (tail+1) p p (fun ds => (totalCasimir ds*totalCasimir ds)*totalCasimir ds) := by
    apply leafSum_pairing_congr
    intro ds hlen hpath
    exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (totalCasimir ds*totalCasimir ds) _ _
        (path_casimir_test tail p hp ds hlen hpath))
      (Q'.mul_assoc_eqv _ _ _).symm
  exact Q'.eqv_trans _ _ _ hsum.symm (pairSecondMoment_literal tail p Cp hp hCp)

private theorem totalCasimir_nonnegative : ∀ ds : List Nat, (0 : Q') ≤ totalCasimir ds
  | [] => Q'.le_refl' 0
  | _::ds => Q'.zero_le_add _ _ (CReal.ofNat_le_ofNat (Nat.zero_le _))
      (totalCasimir_nonnegative ds)

theorem thirdMoment_nonnegative (tail : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p) : (0 : Q') ≤ thirdMoment tail p :=
  Q'.le_trans' _ _ _
    (full_leafSum_diagonal_nonnegative tail p hp
      (fun ds => (totalCasimir ds*totalCasimir ds)*totalCasimir ds)
      (fun ds _ => Q'.mul_nonneg _ _
        (Q'.mul_nonneg _ _ (totalCasimir_nonnegative ds) (totalCasimir_nonnegative ds))
        (totalCasimir_nonnegative ds)))
    (Q'.le_of_eqv (full_cubeMoment_eq_literal tail p hp))

private theorem leafSum_neg (tail m : Nat) (p test : RatPoly) (weight : List Nat → Q') :
    leafSum tail m p test (fun ds => -(weight ds)) ≈ -(leafSum tail m p test weight) :=
  Q'.eqv_trans _ _ _ (leafSum_congr tail m p test _ _ (fun ds _ =>
    poly_identity_of_normal_eq (.neg (.var 0)) (.mul (.neg (.const 1)) (.var 0))
      (by decide) (fun _ => weight ds)))
    (Q'.eqv_trans _ _ _ (leafSum_smul tail m p test (-1) weight)
      (poly_identity_of_normal_eq (.mul (.neg (.const 1)) (.var 0)) (.neg (.var 0))
        (by decide) (fun _ => leafSum tail m p test weight)))

attribute [local irreducible] leafSum pairCubic thirdMoment totalCasimir

/-- Actual negative cubic diagonal, not an absolute path budget. -/
theorem neg_pairCubic_diagonal_le_thirdMoment (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (p : RatPoly) (hp : SupportedQuaternionBlocks (tail+1) p) :
    -(pairCubic tail w p p) ≤
      (sixth*((((1 : Q')-w)*((1 : Q')-w))*((1 : Q')-w)))*thirdMoment tail p := by
  let h3 := ((((1 : Q')-w)*((1 : Q')-w))*((1 : Q')-w))
  have hh : (0 : Q') ≤ (1 : Q')-w := Q'.sub_nonneg_of_le hw1
  have h30 : (0 : Q') ≤ h3 := Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ hh hh) hh
  have hs := full_leafSum_diagonal_mono tail p hp
    (fun ds => -(cubicRemainder w (totalCasimirNat ds)))
    (fun ds => (sixth*h3)*((totalCasimir ds*totalCasimir ds)*totalCasimir ds))
    (fun ds _ => by
      have hneg := Q'.neg_le_neg (cubicRemainder_budget_lower hw0 hw1 (totalCasimirNat ds))
      have hbudget := Q'.mul_le_mul_of_nonneg_right _ _ h3
        (cubicBudget_le_cube (totalCasimirNat ds)) h30
      have hpin : (sixth*((Q'.ofNat (totalCasimirNat ds)*Q'.ofNat (totalCasimirNat ds))*
          Q'.ofNat (totalCasimirNat ds)))*h3 ≈
          (sixth*h3)*((totalCasimir ds*totalCasimir ds)*totalCasimir ds) :=
        Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right _ _ h3
            (Q'.mul_eqv_congr_left sixth _ _
              (mul_congr (mul_congr
                (totalCasimirNat_pin ds) (totalCasimirNat_pin ds))
                (totalCasimirNat_pin ds))))
          (poly_identity_of_normal_eq
            (.mul (.mul (.var 0) (.var 2)) (.var 1))
            (.mul (.mul (.var 0) (.var 1)) (.var 2)) (by decide)
            (fun | 0 => sixth | 1 => h3 | _ => (totalCasimir ds*totalCasimir ds)*totalCasimir ds))
      exact Q'.le_trans' _ _ _ hneg
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.neg_neg_eqv _))
          (Q'.le_trans' _ _ _ hbudget (Q'.le_of_eqv hpin))))
  unfold pairCubic
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (leafSum_neg tail (tail+1) p p
      (fun ds => cubicRemainder w (totalCasimirNat ds))))
    (Q'.le_trans' _ _ _ hs (Q'.le_of_eqv (Q'.eqv_trans _ _ _
      (leafSum_smul tail (tail+1) p p (sixth*h3) _)
      (Q'.mul_eqv_congr_left (sixth*h3) _ _ (full_cubeMoment_eq_literal tail p hp)))))

#print axioms sixth
#print axioms sixth_nonnegative
#print axioms cubicBudget_le_cube
#print axioms thirdMoment
#print axioms full_cubeMoment_eq_literal
#print axioms thirdMoment_nonnegative
#print axioms neg_pairCubic_diagonal_le_thirdMoment

end YMGap.Continuum.SU2QuaternionCyclicCasimirCube
