/-
# Constant-shift cancellation in the ORIGINAL signed source corrections

The mixed-minus-diagonal expression of a symmetric bilinear form is unchanged
by a constant observable shift. Apply this exact algebra to the constructed
cubic and omitted forms on the SAME supported polynomial carrier. Sources may
be signed. No centered Casimir eigenpin, norm inverse, favorable debt sign or
variance/scaling estimate is inferred; the absolute diagonal budgets need not
share this cancellation.
-/

import YMGap.Continuum.SU2QuaternionCyclicCubicOperator
import YMGap.Continuum.QuaternionHaarDensityVariance

namespace YMGap.Continuum.SU2QuaternionCyclicSourceShift

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularSupport (polySmul_supported)
open YMGap.Continuum.SU2QuaternionCyclicSecondOrder
open YMGap.Continuum.SU2QuaternionCyclicOmittedOperator
open YMGap.Continuum.SU2QuaternionCyclicCubicOperator
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul_left cap_mul)
open YMGap.Continuum.QuaternionHaarDensityVariance (shifted shifted_supported)
open YMGap.Continuum.GNSQuotient

local infix:50 " ≈ " => Q'.eqv

private theorem shifted_coeff (f : RatPoly) (c : Q') :
    RatPolyCoeffEqv (shifted f c) (polyAdd f (cap (-c))) :=
  (RatPolyCoeffEqv.one_smul f).add (RatPolyCoeffEqv.refl _)

private theorem source_shift_coeff (q f : RatPoly) (c : Q') :
    RatPolyCoeffEqv (polyMul q (shifted f c))
      (polyAdd (polyMul q f) (polySmul (-c) q)) := by
  refine ((RatPolyCoeffEqv.refl q).mul (shifted_coeff f c)).trans ?_
  refine (coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.var 0) (.add (.var 1) (.var 2)))
    (.add (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 0)))
    (by decide) (fun | 0 => q | 1 => f | _ => cap (-c))).trans ?_
  exact (RatPolyCoeffEqv.refl _).add (cap_mul_left (-c) q)

private theorem source_shift_square_coeff (q f : RatPoly) (c : Q') :
    RatPolyCoeffEqv (polyMul q (polyMul (shifted f c) (shifted f c)))
      (polyAdd (polyMul q (polyMul f f))
        (polyAdd (polySmul (-2*c) (polyMul q f)) (polySmul (c*c) q))) := by
  have hcross : RatPolyCoeffEqv
      (polyMul (cap 2) (polyMul (cap (-c)) (polyMul q f)))
      (polySmul (-2*c) (polyMul q f)) :=
    (cap_mul_left 2 _).trans (((cap_mul_left (-c) _).smul 2).trans
      ((RatPolyCoeffEqv.smul_assoc 2 (-c) _).trans
        (RatPolyCoeffEqv.smul_coefficient
          (poly_identity_of_normal_eq (.mul (.const 2) (.neg (.var 0)))
            (.mul (.const (-2)) (.var 0)) (by decide) (fun _ => c)) _)))
  have hconstant : RatPolyCoeffEqv
      (polyMul (polyMul (cap (-c)) (cap (-c))) q) (polySmul (c*c) q) :=
    ((cap_mul (-c) (-c)).mul_right q).trans ((cap_mul_left _ q).trans
      (RatPolyCoeffEqv.smul_coefficient
        (poly_identity_of_normal_eq (.mul (.neg (.var 0)) (.neg (.var 0)))
          (.mul (.var 0) (.var 0)) (by decide) (fun _ => c)) q))
  refine ((RatPolyCoeffEqv.refl q).mul
    ((shifted_coeff f c).mul (shifted_coeff f c))).trans ?_
  refine (coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.var 0) (.mul (.add (.var 1) (.var 2)) (.add (.var 1) (.var 2))))
    (.add (.mul (.var 0) (.mul (.var 1) (.var 1)))
      (.add (.mul (.const 2) (.mul (.var 2) (.mul (.var 0) (.var 1))))
        (.mul (.mul (.var 2) (.var 2)) (.var 0))))
    (by decide) (fun | 0 => q | 1 => f | _ => cap (-c))).trans ?_
  exact (RatPolyCoeffEqv.refl _).add (hcross.add hconstant)

/- Only symmetry and bilinearity of the EXISTING finite form are used. -/
private theorem form_shift (D : GNSData) (q v z : D.V) (c : Q') :
    D.B (D.add z (D.add (D.smul (-2*c) v) (D.smul (c*c) q))) q -
      D.B (D.add v (D.smul (-c) q)) (D.add v (D.smul (-c) q)) ≈
        D.B z q-D.B v v := by
  have hm : D.B (D.add z (D.add (D.smul (-2*c) v) (D.smul (c*c) q))) q ≈
      D.B z q+((-2*c)*D.B v q+(c*c)*D.B q q) :=
    Q'.eqv_trans _ _ _ (D.B_add_left _ _ q)
      (Q'.add_eqv_congr' (Q'.eqv_refl _)
        (Q'.eqv_trans _ _ _ (D.B_add_left _ _ q)
          (Q'.add_eqv_congr' (D.B_smul_left _ v q) (D.B_smul_left _ q q))))
  have hd : D.B (D.add v (D.smul (-c) q)) (D.add v (D.smul (-c) q)) ≈
      (D.B v v+(-c)*D.B v q)+(-c)*(D.B v q+(-c)*D.B q q) :=
    Q'.eqv_trans _ _ _ (D.B_add_left _ _ _)
      (Q'.add_eqv_congr'
        (Q'.eqv_trans _ _ _ (D.B_add_right v _ _)
          (Q'.add_eqv_congr' (Q'.eqv_refl _) (D.B_smul_right (-c) v q)))
        (Q'.eqv_trans _ _ _ (D.B_smul_left (-c) q _)
          (Q'.mul_eqv_congr_left (-c) _ _
            (Q'.eqv_trans _ _ _ (D.B_add_right q _ _)
              (Q'.add_eqv_congr' (D.B_symm q v) (D.B_smul_right (-c) q q))))))
  exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hm (Q'.neg_eqv_congr _ _ hd))
    (poly_identity_of_normal_eq
      (.add
        (.add (.var 0) (.add (.mul (.mul (.const (-2)) (.var 3)) (.var 2))
          (.mul (.mul (.var 3) (.var 3)) (.var 4))))
        (.neg (.add (.add (.var 1) (.mul (.neg (.var 3)) (.var 2)))
          (.mul (.neg (.var 3)) (.add (.var 2) (.mul (.neg (.var 3)) (.var 4)))))))
      (.add (.var 0) (.neg (.var 1))) (by decide)
      (fun | 0 => D.B z q | 1 => D.B v v | 2 => D.B v q | 3 => c | _ => D.B q q))

private theorem cubic_source_pin (tail : Nat) (w : Q') (q f : RatPoly) :
    sourceCubic tail w q f ≈
      -(cubicPair tail w q (polyMul q (polyMul f f))-
        cubicPair tail w (polyMul q f) (polyMul q f)) :=
  poly_identity_of_normal_eq (.add (.var 0) (.neg (.var 1)))
    (.neg (.add (.neg (.var 0)) (.neg (.neg (.var 1)))))
    (by decide) (fun
      | 0 => pairCubic tail w q (polyMul q (polyMul f f))
      | _ => pairCubic tail w (polyMul q f) (polyMul q f))

/-- Exact ORIGINAL cubic source debt is independent of a constant observable shift.
The constructed source is allowed to be signed; the OWN mean can be inserted as c. -/
theorem sourceCubic_shifted (tail : Nat) {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw1 : w < (1 : Q')) (q f : RatPoly)
    (hq : SupportedQuaternionBlocks (tail+1) q)
    (hf : SupportedQuaternionBlocks (tail+1) f) (c : Q') :
    sourceCubic tail w q (shifted f c) ≈ sourceCubic tail w q f := by
  let D := cubicGNSData tail w hw0 hw1
  let Q : D.V := ⟨q,hq⟩
  let V : D.V := ⟨polyMul q f,supported_polyMul hq hf⟩
  let Z : D.V := ⟨polyMul q (polyMul f f),supported_polyMul hq (supported_polyMul hf hf)⟩
  let Vs : D.V := ⟨polyMul q (shifted f c),supported_polyMul hq (shifted_supported hf c)⟩
  let Zs : D.V := ⟨polyMul q (polyMul (shifted f c) (shifted f c)),
    supported_polyMul hq (supported_polyMul (shifted_supported hf c) (shifted_supported hf c))⟩
  have hv : D.veq Vs (D.add V (D.smul (-c) Q)) := source_shift_coeff q f c
  have hz : D.veq Zs (D.add Z (D.add (D.smul (-2*c) V) (D.smul (c*c) Q))) :=
    source_shift_square_coeff q f c
  have htransport : D.B Zs Q-D.B Vs Vs ≈
      D.B (D.add Z (D.add (D.smul (-2*c) V) (D.smul (c*c) Q))) Q-
        D.B (D.add V (D.smul (-c) Q)) (D.add V (D.smul (-c) Q)) :=
    Q'.add_eqv_congr' (D.B_congr_left Q hz) (Q'.neg_eqv_congr _ _ (D.B_diag_congr hv))
  have h := Q'.eqv_trans _ _ _ htransport (form_shift D Q V Z c)
  exact Q'.eqv_trans _ _ _ (cubic_source_pin tail w q (shifted f c))
    (Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ h) (cubic_source_pin tail w q f).symm)

/-- BOTH signed original omitted terms cancel their constant-shift contributions.
No comparison between projected and unprojected source norms is used. -/
theorem sourceOmitted_shifted (tail : Nat) {w : Q'} (hw0 : (0 : Q') ≤ w)
    (_hw1 : w < (1 : Q')) (K : Nat) (q f : RatPoly)
    (hq : SupportedQuaternionBlocks (tail+1) q)
    (hf : SupportedQuaternionBlocks (tail+1) f) (c : Q') :
    sourceOmitted tail w K q (shifted f c) ≈ sourceOmitted tail w K q f := by
  let D := omittedGNSData tail w hw0 K
  let Q : D.V := ⟨q,hq⟩
  let V : D.V := ⟨polyMul q f,supported_polyMul hq hf⟩
  let Z : D.V := ⟨polyMul q (polyMul f f),supported_polyMul hq (supported_polyMul hf hf)⟩
  let Vs : D.V := ⟨polyMul q (shifted f c),supported_polyMul hq (shifted_supported hf c)⟩
  let Zs : D.V := ⟨polyMul q (polyMul (shifted f c) (shifted f c)),
    supported_polyMul hq (supported_polyMul (shifted_supported hf c) (shifted_supported hf c))⟩
  have hv : D.veq Vs (D.add V (D.smul (-c) Q)) := source_shift_coeff q f c
  have hz : D.veq Zs (D.add Z (D.add (D.smul (-2*c) V) (D.smul (c*c) Q))) :=
    source_shift_square_coeff q f c
  have htransport : D.B Zs Q-D.B Vs Vs ≈
      D.B (D.add Z (D.add (D.smul (-2*c) V) (D.smul (c*c) Q))) Q-
        D.B (D.add V (D.smul (-c) Q)) (D.add V (D.smul (-c) Q)) :=
    Q'.add_eqv_congr' (D.B_congr_left Q hz) (Q'.neg_eqv_congr _ _ (D.B_diag_congr hv))
  exact Q'.eqv_trans _ _ _ htransport (form_shift D Q V Z c)

end YMGap.Continuum.SU2QuaternionCyclicSourceShift

#print axioms YMGap.Continuum.SU2QuaternionCyclicSourceShift.sourceCubic_shifted
#print axioms YMGap.Continuum.SU2QuaternionCyclicSourceShift.sourceOmitted_shifted
