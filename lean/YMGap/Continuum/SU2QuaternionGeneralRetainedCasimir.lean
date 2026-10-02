/-
# Retain the actual Casimir square for arbitrary signed observables

The angular Gram certificate and one completed square give
`comm(q,f)^2 + 2 Gamma(q,q) Gamma(f,f) >= (q C f)^2 / 3`.
No Casimir eigenpin, source positivity or observable centering is assumed.
The original second-order curvature remains signed. These are finite Haar
estimates; no interacting variance or scaling estimate is asserted.
-/

import YMGap.Continuum.SU2QuaternionSecondOrderRetainedSquare

namespace YMGap.Continuum.SU2QuaternionGeneralRetainedCasimir

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
open YMGap.Continuum.SU2QuaternionActiveCasimirProduct
open YMGap.Continuum.SU2QuaternionChannelCasimirSquare
open YMGap.Continuum.SU2QuaternionSecondOrderCancellation
open YMGap.Continuum.SU2QuaternionCyclicSecondOrder (sourceSecondMoment)
open YMGap.Continuum.SU2QuaternionSecondOrderRetainedSquare (angularGramCertificate)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul_left)

local infix:50 " ≈ " => Q'.eqv
local notation:max "H" n:arg => quaternionHaar n

/-- The explicit retained fraction of the actual Casimir square. -/
def oneThird : Q' := Q'.mkPos 1 3 (by decide)

private theorem supported_smul {n : Nat} (c : Q') {p : RatPoly}
    (hp : SupportedQuaternionBlocks n p) : SupportedQuaternionBlocks n (polySmul c p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

/-- Constructed square evidence for the original `q * C f`, with no eigenpin. -/
def generalRetainedCasimirCertificate {n : Nat} (active : List Nat)
    (hactive : ∀ b, b ∈ active → b < n) (q f : RatPoly)
    (hq : SupportedQuaternionBlocks n q) (hf : SupportedQuaternionBlocks n f) :
    Certificate n (polyAdd
      (polyAdd
        (polyMul (commutatorPolynomial active q f) (commutatorPolynomial active q f))
        (polySmul 2 (polyMul (activeGamma active q q) (activeGamma active f f))))
      (polySmul (-oneThird)
        (polyMul (polyMul q (activeCasimirPolynomial active f))
          (polyMul q (activeCasimirPolynomial active f))))) := by
  let v := polyMul q (activeCasimirPolynomial active f)
  let x := activeGamma active q f
  let y := activeGamma active q q
  let g := activeGamma active f f
  let b := polyAdd v (polySmul (-2) x)
  let s := polyAdd v (polySmul (-3) x)
  have hs : SupportedQuaternionBlocks n s :=
    supported_add
      (supported_polyMul hq (activeCasimirPolynomial_supported active hactive hf))
      (supported_smul (-3) (activeGamma_supported active hactive hq hf))
  let target := polyAdd (polyAdd (polyMul b b) (polySmul 2 (polyMul y g)))
    (polySmul (-oneThird) (polyMul v v))
  have hring : RatPolyCoeffEqv (polySmul 3 target)
      (polyAdd (polySmul 2 (polyMul s s))
        (polySmul 6 (polyAdd (polyMul y g) (polyNeg (polyMul x x))))) := by
    have hb' := (RatPolyCoeffEqv.refl v).add (cap_mul_left (-2) x).symm
    have hs' := (RatPolyCoeffEqv.refl v).add (cap_mul_left (-3) x).symm
    have hclear : RatPolyCoeffEqv (polySmul 3 target)
        (polyAdd
          (polySmul 3 (polyAdd (polyMul b b) (polySmul 2 (polyMul y g))))
          (polySmul (-1) (polyMul v v))) :=
      (RatPolyCoeffEqv.smul_add 3 _ _).trans
        ((RatPolyCoeffEqv.refl _).add
          ((RatPolyCoeffEqv.smul_assoc 3 (-oneThird) _).trans
            (RatPolyCoeffEqv.smul_coefficient
              (by decide : (3 : Q') * (-oneThird) ≈ (-1 : Q')) _)))
    refine hclear.trans ?_
    refine (((cap_mul_left 3 _).symm.trans
      ((RatPolyCoeffEqv.refl (cap 3)).mul
        ((hb'.mul hb').add (cap_mul_left 2 (polyMul y g)).symm))).add
      (cap_mul_left (-1) (polyMul v v)).symm).trans ?_
    refine (coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.const 3)
        (.add
          (.mul (.add (.var 0) (.mul (.const (-2)) (.var 1)))
            (.add (.var 0) (.mul (.const (-2)) (.var 1))))
          (.mul (.const 2) (.mul (.var 2) (.var 3)))))
        (.mul (.const (-1)) (.mul (.var 0) (.var 0))))
      (.add
        (.mul (.const 2)
          (.mul (.add (.var 0) (.mul (.const (-3)) (.var 1)))
            (.add (.var 0) (.mul (.const (-3)) (.var 1)))))
        (.mul (.const 6) (.add (.mul (.var 2) (.var 3))
          (.neg (.mul (.var 1) (.var 1))))))
      (by decide) (fun | 0 => v | 1 => x | 2 => y | _ => g)).trans ?_
    exact ((cap_mul_left 2 _).trans
      ((hs'.symm.mul hs'.symm).smul 2)).add (cap_mul_left 6 _)
  have hcancel : RatPolyCoeffEqv (polySmul oneThird (polySmul 3 target)) target :=
    (RatPolyCoeffEqv.smul_assoc oneThird 3 target).trans
      ((RatPolyCoeffEqv.smul_coefficient
        (by decide : oneThird * 3 ≈ (1 : Q')) target).trans
        (RatPolyCoeffEqv.one_smul target))
  exact Certificate.ofCoeff hcancel.symm
    (Certificate.smul oneThird (by decide)
      (Certificate.ofCoeff hring
        (Certificate.add (Certificate.smul 2 (by decide) (Certificate.square s hs))
          (Certificate.smul 6 (by decide)
            (angularGramCertificate active hactive hq hf)))))

/-- The retained square differentiates the actual observable, even when centered. -/
theorem general_retained_casimir_bound {n : Nat} (active : List Nat)
    (hactive : ∀ b, b ∈ active → b < n) (q f : RatPoly)
    (hq : SupportedQuaternionBlocks n q) (hf : SupportedQuaternionBlocks n f) :
    oneThird * H n (polyMul (polyMul q (activeCasimirPolynomial active f))
        (polyMul q (activeCasimirPolynomial active f))) ≤
      H n (polyMul (commutatorPolynomial active q f) (commutatorPolynomial active q f)) +
        2 * H n (polyMul (activeGamma active q q) (activeGamma active f f)) := by
  have hn := (generalRetainedCasimirCertificate active hactive q f hq hf).haar_nonnegative
  have he : H n (polyAdd
      (polyAdd
        (polyMul (commutatorPolynomial active q f) (commutatorPolynomial active q f))
        (polySmul 2 (polyMul (activeGamma active q q) (activeGamma active f f))))
      (polySmul (-oneThird)
        (polyMul (polyMul q (activeCasimirPolynomial active f))
          (polyMul q (activeCasimirPolynomial active f))))) ≈
      (H n (polyMul (commutatorPolynomial active q f) (commutatorPolynomial active q f)) +
        2 * H n (polyMul (activeGamma active q q) (activeGamma active f f))) +
        -(oneThird * H n (polyMul (polyMul q (activeCasimirPolynomial active f))
          (polyMul q (activeCasimirPolynomial active f)))) :=
    Q'.eqv_trans _ _ _ (quaternionHaar_append n _ _)
      (Q'.add_eqv_congr'
        (Q'.eqv_trans _ _ _ (quaternionHaar_append n _ _)
          (Q'.add_eqv_congr' (Q'.eqv_refl _) (quaternionHaar_polySmul n 2 _)))
        (Q'.eqv_trans _ _ _ (quaternionHaar_polySmul n (-oneThird) _)
          (poly_identity_of_normal_eq (.mul (.neg (.var 0)) (.var 1))
            (.neg (.mul (.var 0) (.var 1))) (by decide)
            (fun | 0 => oneThird
                 | _ => H n (polyMul (polyMul q (activeCasimirPolynomial active f))
                    (polyMul q (activeCasimirPolynomial active f)))))))
  exact Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _ hn (Q'.le_of_eqv he))

/-- The original quadratic correction retains the raw full-Casimir square. -/
theorem sourceSecondMoment_le_retainedCasimir (tail : Nat) (q f : RatPoly)
    (hq : SupportedQuaternionBlocks (tail+1) q)
    (hf : SupportedQuaternionBlocks (tail+1) f) :
    sourceSecondMoment tail q f ≤
      -(H (tail+1) (polyMul (polyMul q q)
        (activeCasimirPolynomial (List.range (tail+1))
          (activeGamma (List.range (tail+1)) f f)))) -
        oneThird * H (tail+1)
          (polyMul (polyMul q (activeCasimirPolynomial (List.range (tail+1)) f))
            (polyMul q (activeCasimirPolynomial (List.range (tail+1)) f))) := by
  let active := List.range (tail+1)
  let S := H (tail+1) (polyMul (commutatorPolynomial active q f) (commutatorPolynomial active q f))
  let P := H (tail+1) (polyMul (activeGamma active q q) (activeGamma active f f))
  let R := H (tail+1) (polyMul (polyMul q q)
    (activeCasimirPolynomial active (activeGamma active f f)))
  let F := H (tail+1) (polyMul (polyMul q (activeCasimirPolynomial active f))
    (polyMul q (activeCasimirPolynomial active f)))
  have hsq := general_retained_casimir_bound active
    (fun i hi => List.mem_range.mp hi) q f hq hf
  have hr := Q'.add_le_add_right _ _ (-R) (Q'.neg_le_neg hsq)
  have hleft : sourceSecondMoment tail q f ≈ -(S+2*P)+ -R :=
    Q'.eqv_trans _ _ _ (sourceSecondMoment_curvature tail q f hq hf)
      (poly_identity_of_normal_eq
        (.add (.add (.neg (.var 0)) (.neg (.mul (.const 2) (.var 1)))) (.neg (.var 2)))
        (.add (.neg (.add (.var 0) (.mul (.const 2) (.var 1)))) (.neg (.var 2)))
        (by decide) (fun | 0 => S | 1 => P | _ => R))
  have hright : -(oneThird*F)+ -R ≈ -R-oneThird*F := Q'.add_comm_eqv _ _
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _ hr (Q'.le_of_eqv hright))

#print axioms oneThird
#print axioms generalRetainedCasimirCertificate
#print axioms general_retained_casimir_bound
#print axioms sourceSecondMoment_le_retainedCasimir

end YMGap.Continuum.SU2QuaternionGeneralRetainedCasimir
