/-
# Cleared terminal Rayleigh boundary drift, with the original spatial weight

The actual successive-message comparison controls the boundary correction
against an arbitrary supported squared test. No polynomial reciprocal,
stationary-source identification, relative-energy estimate, or scaling claim
is made. Both original terminal masses remain in the literal insertion.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalComparison
import YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
import YMGap.Constructive.AbsQ
import YMGap.Constructive.CRealAdd

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalRayleighDrift

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich
  (weightedMass weightedMass_nonnegative)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWeightedMass
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracket (Bracket)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalComparison
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow (terminalMessage_next)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks weightedMass terminalMessage transferStep

/-- The literal original insertion; its mass factors are scalars, not a
reciprocal of the terminal polynomial. -/
def clearedDrift (w : Q') (K width s : Nat) (psi : RatPoly) : Q' :=
  let A := terminalMessage w K width (s+1)
  let TA := transferStep w K width A
  let Z0 := weightedMass w K width (polyMul A A)
  let Z1 := weightedMass w K width (polyMul A TA)
  weightedMass w K width
    (polyMul (polyMul A (polyMul psi psi))
      (polyAdd (polySmul Z1 A) (polySmul (-Z0) TA)))

/-- Exact expansion preserves both masses and the signed correction. -/
theorem clearedDrift_pin (w : Q') (K width s : Nat) (psi : RatPoly) :
    let A := terminalMessage w K width (s+1)
    let TA := transferStep w K width A
    let Z0 := weightedMass w K width (polyMul A A)
    let Z1 := weightedMass w K width (polyMul A TA)
    let Epsi := weightedMass w K width (polyMul (polyMul A A) (polyMul psi psi))
    let Mpsi := weightedMass w K width (polyMul (polyMul A TA) (polyMul psi psi))
    clearedDrift w K width s psi ≈ Z1*Epsi + -(Z0*Mpsi) := by
  dsimp only
  let A := terminalMessage w K width (s+1)
  let TA := transferStep w K width A
  let Z0 := weightedMass w K width (polyMul A A)
  let Z1 := weightedMass w K width (polyMul A TA)
  have hAA : RatPolyCoeffEqv (polyMul (polyMul A (polyMul psi psi)) A)
      (polyMul (polyMul A A) (polyMul psi psi)) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.mul (.var 1) (.var 1))) (.var 0))
      (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1)))
      (by decide) (fun | 0 => A | _ => psi)
  have hAT : RatPolyCoeffEqv (polyMul (polyMul A (polyMul psi psi)) TA)
      (polyMul (polyMul A TA) (polyMul psi psi)) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.mul (.var 1) (.var 1))) (.var 2))
      (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 1)))
      (by decide) (fun | 0 => A | 1 => psi | _ => TA)
  have he : RatPolyCoeffEqv
      (polyMul (polyMul A (polyMul psi psi))
        (polyAdd (polySmul Z1 A) (polySmul (-Z0) TA)))
      (polyAdd (polySmul Z1 (polyMul (polyMul A A) (polyMul psi psi)))
        (polySmul (-Z0) (polyMul (polyMul A TA) (polyMul psi psi)))) :=
    (RatPolyCoeffEqv.mul_add_right _ _ _).trans
      (((RatPolyCoeffEqv.polyMul_smul_right Z1 _ _).trans (hAA.smul Z1)).add
        ((RatPolyCoeffEqv.polyMul_smul_right (-Z0) _ _).trans (hAT.smul (-Z0))))
  exact Q'.eqv_trans _ _ _ (weightedMass_congr w K width he)
    (Q'.eqv_trans _ _ _ (weightedMass_add w K width _ _)
      (Q'.add_eqv_congr' (weightedMass_smul w K width Z1 _)
        (Q'.eqv_trans _ _ _ (weightedMass_smul w K width (-Z0) _)
          (Q'.neg_mul_eqv Z0 _))))

private theorem bracket_mass {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : headCutoff w ≤ K) {p q : RatPoly}
    (B : Bracket width p q) :
    B.lower*weightedMass w K width q ≤ weightedMass w K width p ∧
      weightedMass w K width p ≤ B.upper*weightedMass w K width q := by
  let P := weightedMass w K width p
  let Q := weightedMass w K width q
  have hl : B.lower*Q ≤ P := Q'.le_of_sub_nonneg
    (Q'.le_trans' _ _ _ (weightedMass_nonnegative hw0 hw1 K width hK B.lowerCertificate)
      (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (weightedMass_add w K width _ _)
        (Q'.add_eqv_congr_left _ _ _ (Q'.eqv_trans _ _ _ (weightedMass_smul w K width _ _)
          (Q'.neg_mul_eqv B.lower Q))))))
  have hu : P ≤ B.upper*Q := Q'.le_of_sub_nonneg
    (Q'.le_trans' _ _ _ (weightedMass_nonnegative hw0 hw1 K width hK B.upperCertificate)
      (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (weightedMass_add w K width _ _)
        (Q'.add_eqv_congr' (weightedMass_smul w K width _ _)
          (Q'.eqv_trans _ _ _ (weightedMass_smul w K width _ _)
            (Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 P)
              (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv P))))))))
  exact ⟨hl,hu⟩

private theorem difference_upper (Z E J M l u : Q')
    (hZ : (0 : Q') ≤ Z) (hE : (0 : Q') ≤ E)
    (hJ : J ≤ u*Z) (hM : l*E ≤ M) :
    J*E + -(Z*M) ≤ ((u + -l)*Z)*E := by
  have h := Q'.add_le_add
    (Q'.mul_le_mul_of_nonneg_right _ _ E hJ hE)
    (Q'.neg_le_neg (Q'.mul_le_mul_of_nonneg_left _ _ Z hM hZ))
  exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv
    (poly_identity_of_normal_eq
      (.add (.mul (.mul (.var 4) (.var 0)) (.var 1))
        (.neg (.mul (.var 0) (.mul (.var 3) (.var 1)))))
      (.mul (.mul (.add (.var 4) (.neg (.var 3))) (.var 0)) (.var 1))
      (by decide) (fun
        | 0 => Z
        | 1 => E
        | 3 => l
        | _ => u)))

/-- Both signed orders, on the actual terminal source and original V.
Only the test is arbitrary; no estimate or source identification is supplied. -/
theorem clearedDrift_bounds {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : headCutoff w ≤ K) (s : Nat) {psi : RatPoly}
    (hpsi : SupportedQuaternionBlocks (N width) psi) :
    let A := terminalMessage w K width (s+1)
    let Z1 := weightedMass w K width (polyMul A (transferStep w K width A))
    let Epsi := weightedMass w K width (polyMul (polyMul A A) (polyMul psi psi))
    let paid := comparisonEta hw0 hw1 width s * Z1 * Epsi
    (-paid ≤ clearedDrift w K width s psi ∧ clearedDrift w K width s psi ≤ paid) := by
  dsimp only
  let A := terminalMessage w K width (s+1)
  let TA := transferStep w K width A
  let Z := weightedMass w K width (polyMul A A)
  let J := weightedMass w K width (polyMul A TA)
  let E := weightedMass w K width (polyMul (polyMul A A) (polyMul psi psi))
  let M := weightedMass w K width (polyMul (polyMul A TA) (polyMul psi psi))
  let eta := comparisonEta hw0 hw1 width s
  let B0 := terminalComparison hw0 hw1 K width hK s 1 0
  have hnext : RatPolyCoeffEqv TA (terminalMessage w K width (s+1+1)) := by
    change RatPolyCoeffEqv (transferStep w K width (terminalMessage w K width (s+1))) _
    rw [terminalMessage_next w K width (s+1)]
    exact RatPolyCoeffEqv.refl _
  let B : Bracket width TA A := {
    lower := B0.lower
    upper := B0.upper
    lowerCertificate := Certificate.ofCoeff
      (hnext.add (RatPolyCoeffEqv.refl (polySmul (-B0.lower) A))) B0.lowerCertificate
    upperCertificate := Certificate.ofCoeff
      ((RatPolyCoeffEqv.refl (polySmul B0.upper A)).add (hnext.smul (-1))) B0.upperCertificate
  }
  let CA := terminalMessage_certificate hw0 hw1 K width hK (s+1)
  let S := Certificate.square psi hpsi
  have hZ : (0 : Q') ≤ Z := Q'.le_of_lt (terminalPair_positive hw0 hw1 K width hK (s+1) (s+1))
  have hE : (0 : Q') ≤ E := weightedMass_nonnegative hw0 hw1 K width hK ((CA.mul CA).mul S)
  have hJ := bracket_mass hw0 hw1 K width hK (multiplyBracket B CA)
  have hME := bracket_mass hw0 hw1 K width hK (multiplyBracket B (CA.mul S))
  have hMpin : weightedMass w K width (polyMul (polyMul A (polyMul psi psi)) TA) ≈ M :=
    weightedMass_congr w K width (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.mul (.var 1) (.var 1))) (.var 2))
      (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 1)))
      (by decide) (fun | 0 => A | 1 => psi | _ => TA))
  have hEpin : weightedMass w K width (polyMul (polyMul A (polyMul psi psi)) A) ≈ E :=
    weightedMass_congr w K width (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.mul (.var 1) (.var 1))) (.var 0))
      (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1)))
      (by decide) (fun | 0 => A | _ => psi))
  have hlM : B.lower*E ≤ M := Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (Q'.mul_eqv_congr_left B.lower _ _ hEpin))
    (Q'.le_trans' _ _ _ hME.1 (Q'.le_of_eqv hMpin))
  have huM : M ≤ B.upper*E := Q'.le_trans' _ _ _ (Q'.ge_of_eqv hMpin)
    (Q'.le_trans' _ _ _ hME.2 (Q'.le_of_eqv (Q'.mul_eqv_congr_left B.upper _ _ hEpin)))
  have hwidth : B.upper + -B.lower ≤ eta*B.lower :=
    terminalComparison_relative_width hw0 hw1 K width hK s 1 0
  have heta : (0 : Q') ≤ eta := comparisonEta_nonnegative hw0 hw1 width s
  have hpay : ((B.upper + -B.lower)*Z)*E ≤ eta*J*E := by
    have h1 := Q'.mul_le_mul_of_nonneg_right _ _ Z hwidth hZ
    have h2 := Q'.mul_le_mul_of_nonneg_left _ _ eta hJ.1 heta
    have hshuffle : (eta*B.lower)*Z ≈ eta*(B.lower*Z) := Q'.mul_assoc_eqv _ _ _
    exact Q'.mul_le_mul_of_nonneg_right _ _ E
      (Q'.le_trans' _ _ _ h1 (Q'.le_trans' _ _ _ (Q'.le_of_eqv hshuffle) h2)) hE
  have hu : J*E + -(Z*M) ≤ eta*J*E := Q'.le_trans' _ _ _
    (difference_upper Z E J M B.lower B.upper hZ hE hJ.2 hlM) hpay
  have hn0 := difference_upper E Z M J B.lower B.upper hE hZ huM hJ.1
  have hn : -(J*E + -(Z*M)) ≤ eta*J*E := by
    have hleft : -(J*E + -(Z*M)) ≈ M*Z + -(E*J) :=
      poly_identity_of_normal_eq
        (.neg (.add (.mul (.var 2) (.var 1)) (.neg (.mul (.var 0) (.var 3)))))
        (.add (.mul (.var 3) (.var 0)) (.neg (.mul (.var 1) (.var 2))))
        (by decide) (fun | 0 => Z | 1 => E | 2 => J | _ => M)
    have hright : ((B.upper + -B.lower)*E)*Z ≈ ((B.upper + -B.lower)*Z)*E :=
      poly_identity_of_normal_eq (.mul (.mul (.var 0) (.var 1)) (.var 2))
        (.mul (.mul (.var 0) (.var 2)) (.var 1))
        (by decide) (fun | 0 => B.upper + -B.lower | 1 => E | _ => Z)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
      (Q'.le_trans' _ _ _ hn0 (Q'.le_trans' _ _ _ (Q'.le_of_eqv hright) hpay))
  have hl : -(eta*J*E) ≤ J*E + -(Z*M) := Q'.le_trans' _ _ _ (Q'.neg_le_neg hn)
    (Q'.le_of_eqv (Q'.neg_neg_eqv _))
  have hd := clearedDrift_pin w K width s psi
  exact ⟨Q'.le_trans' _ _ _ hl (Q'.ge_of_eqv hd), Q'.le_trans' _ _ _ (Q'.le_of_eqv hd) hu⟩

/-- Absolute cleared boundary drift paid by the computed relative width.
No inverse terminal polynomial and no relative Rayleigh estimate occur. -/
theorem clearedDrift_abs_le {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : headCutoff w ≤ K) (s : Nat) {psi : RatPoly}
    (hpsi : SupportedQuaternionBlocks (N width) psi) :
    let A := terminalMessage w K width (s+1)
    let Z1 := weightedMass w K width (polyMul A (transferStep w K width A))
    let Epsi := weightedMass w K width (polyMul (polyMul A A) (polyMul psi psi))
    Q'.abs (clearedDrift w K width s psi) ≤ comparisonEta hw0 hw1 width s * Z1 * Epsi :=
  Q'.abs_le (clearedDrift_bounds hw0 hw1 K width hK s hpsi).1
    (clearedDrift_bounds hw0 hw1 K width hK s hpsi).2

#print axioms clearedDrift
#print axioms clearedDrift_pin
#print axioms clearedDrift_bounds
#print axioms clearedDrift_abs_le

end YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalRayleighDrift
