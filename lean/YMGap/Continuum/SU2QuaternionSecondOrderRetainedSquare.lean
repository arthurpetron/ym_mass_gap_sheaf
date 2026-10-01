/-
# Retain a quantitative source square in the original quadratic correction

The finite angular Gram determinant is a constructed sum of squares.
Completing one more square retains 48 H[(q*f)^2] whenever the SAME
observable has literal Casimir 12. No source positivity, reciprocal,
stationarity or variance comparison is assumed. This is a finite bound;
the original first-order Ward and weight corrections remain separate.
-/

import YMGap.Continuum.QuaternionHaarPolynomialGramDeterminant
import YMGap.Continuum.SU2QuaternionSecondOrderCancellation

namespace YMGap.Continuum.SU2QuaternionSecondOrderRetainedSquare

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularReindex
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionActiveCasimirProduct
open YMGap.Continuum.SU2QuaternionChannelCasimirSquare
open YMGap.Continuum.SU2QuaternionSecondOrderCancellation
open YMGap.Continuum.SU2QuaternionCyclicSecondOrder (sourceSecondMoment)
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy (six)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul_left)
open YMGap.Continuum.QuaternionHaarPolynomialGramDeterminant

local infix:50 " ≈ " => Q'.eqv
local notation:max "H" n:arg => quaternionHaar n

private def blockPairs (block : Nat) (p q : RatPoly) : List (RatPoly × RatPoly) :=
  [(blockAngularDerivative block 0 1 p, blockAngularDerivative block 0 1 q),
   (blockAngularDerivative block 0 2 p, blockAngularDerivative block 0 2 q),
   (blockAngularDerivative block 0 3 p, blockAngularDerivative block 0 3 q),
   (blockAngularDerivative block 1 2 p, blockAngularDerivative block 1 2 q),
   (blockAngularDerivative block 1 3 p, blockAngularDerivative block 1 3 q),
   (blockAngularDerivative block 2 3 p, blockAngularDerivative block 2 3 q)]

/-- Exactly six original directions per listed block, including multiplicity. -/
def angularPairs (active : List Nat) (p q : RatPoly) : List (RatPoly × RatPoly) :=
  active.flatMap (fun block => blockPairs block p q)

private theorem angularPairs_supported {n : Nat} (active : List Nat)
    (hactive : ∀ b, b ∈ active → b < n) {p q : RatPoly}
    (hp : SupportedQuaternionBlocks n p) (hq : SupportedQuaternionBlocks n q) :
    ∀ r, r ∈ angularPairs active p q →
      SupportedQuaternionBlocks n r.1 ∧ SupportedQuaternionBlocks n r.2 := by
  intro r hr
  obtain ⟨b, hb, hr⟩ := List.mem_flatMap.mp hr
  have hbn := hactive b hb
  have hd (i j : Nat) (hi : i < 4) (hj : j < 4) :
      SupportedQuaternionBlocks n (blockAngularDerivative b i j p) ∧
        SupportedQuaternionBlocks n (blockAngularDerivative b i j q) :=
    ⟨angularDerivative_supported_at (by omega) (by omega) hp,
     angularDerivative_supported_at (by omega) (by omega) hq⟩
  simp only [blockPairs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hd 0 1 (by decide) (by decide)
  · exact hd 0 2 (by decide) (by decide)
  · exact hd 0 3 (by decide) (by decide)
  · exact hd 1 2 (by decide) (by decide)
  · exact hd 1 3 (by decide) (by decide)
  · exact hd 2 3 (by decide) (by decide)

private theorem mixedSum_angularPairs (active : List Nat) (p q : RatPoly) :
    RatPolyCoeffEqv (mixedSum (angularPairs active p q)) (activeGamma active p q) := by
  rw [mixedSum_eq]
  induction active with
  | nil => exact RatPolyCoeffEqv.refl _
  | cons b bs ih =>
      have hblock : RatPolyCoeffEqv
          (polySum ((blockPairs b p q).map fun r => polyMul r.1 r.2))
          (blockGamma b p q) := by
        dsimp only [blockPairs, List.map_cons, List.map_nil, polySum, blockGamma, six]
        exact (RatPolyCoeffEqv.refl _).add
          ((RatPolyCoeffEqv.refl _).add
            ((RatPolyCoeffEqv.refl _).add
              ((RatPolyCoeffEqv.refl _).add
                ((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.add_zero _)))))
      change RatPolyCoeffEqv
        (polySum (((blockPairs b p q) ++ angularPairs bs p q).map
          fun r => polyMul r.1 r.2))
        (polyAdd (blockGamma b p q) (activeGamma bs p q))
      rw [List.map_append]
      exact (RatPolyCoeffEqv.polySum_append _ _).symm.trans (hblock.add ih)

/-- The original angular Gram determinant has explicit polynomial square data. -/
def angularGramCertificate {n : Nat} (active : List Nat)
    (hactive : ∀ b, b ∈ active → b < n) {p q : RatPoly}
    (hp : SupportedQuaternionBlocks n p) (hq : SupportedQuaternionBlocks n q) :
    Certificate n (polyAdd
      (polyMul (activeGamma active p p) (activeGamma active q q))
      (polyNeg (polyMul (activeGamma active p q) (activeGamma active p q)))) := by
  let ps := angularPairs active p q
  have hfirst : RatPolyCoeffEqv (squareFirst ps) (activeGamma active p p) := by
    have he : squareFirst ps = mixedSum (angularPairs active p p) := by
      rw [squareFirst_eq, mixedSum_eq]
      simp only [ps, angularPairs, List.map_flatMap, blockPairs, List.map_cons,
        List.map_nil]
    rw [he]
    exact mixedSum_angularPairs active p p
  have hsecond : RatPolyCoeffEqv (squareSecond ps) (activeGamma active q q) := by
    have he : squareSecond ps = mixedSum (angularPairs active q q) := by
      rw [squareSecond_eq, mixedSum_eq]
      simp only [ps, angularPairs, List.map_flatMap, blockPairs, List.map_cons,
        List.map_nil]
    rw [he]
    exact mixedSum_angularPairs active q q
  have hmixed := mixedSum_angularPairs active p q
  have hdet : RatPolyCoeffEqv (gramDeterminant ps)
      (polyAdd (polyMul (activeGamma active p p) (activeGamma active q q))
        (polyNeg (polyMul (activeGamma active p q) (activeGamma active p q)))) :=
    (hfirst.mul hsecond).add (RatPolyCoeffEqv.neg (hmixed.mul hmixed))
  exact Certificate.ofCoeff hdet.symm
    (gramDeterminantCertificate (blocks := n) ps
      (angularPairs_supported active hactive hp hq))

private theorem supported_smul {n : Nat} (c : Q') {p : RatPoly}
    (hp : SupportedQuaternionBlocks n p) : SupportedQuaternionBlocks n (polySmul c p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private def oneThird : Q' := Q'.mkPos 1 3 (by decide)

/-- Completing the actual commutator square keeps a quantitative part of it.
The eigenpin is carrier equality, not an assumption on source derivatives. -/
def retainedSquareCertificate {n : Nat} (active : List Nat)
    (hactive : ∀ b, b ∈ active → b < n) (q f : RatPoly)
    (hq : SupportedQuaternionBlocks n q) (hf : SupportedQuaternionBlocks n f)
    (hCf : HaarCarrierEqv n (activeCasimirPolynomial active f) (polySmul 12 f)) :
    Certificate n (polyAdd
      (polyAdd
        (polyMul (commutatorPolynomial active q f) (commutatorPolynomial active q f))
        (polySmul 2 (polyMul (activeGamma active q q) (activeGamma active f f))))
      (polySmul (-48) (polyMul (polyMul q f) (polyMul q f)))) := by
  let v := polyMul q f
  let x := activeGamma active q f
  let y := activeGamma active q q
  let g := activeGamma active f f
  let b := polyAdd (polySmul 12 v) (polySmul (-2) x)
  let s := polyAdd (polySmul 12 v) (polySmul (-3) x)
  have hb : HaarCarrierEqv n (commutatorPolynomial active q f) b :=
    (HaarCarrierEqv.add (HaarCarrierEqv.mul_left q hCf) (HaarCarrierEqv.refl n _)).trans
      (RatPolyCoeffEqv.haarCarrier
        ((RatPolyCoeffEqv.polyMul_smul_right 12 q f).add (RatPolyCoeffEqv.refl _)))
  have hs : SupportedQuaternionBlocks n s :=
    supported_add (supported_smul 12 (supported_polyMul hq hf))
      (supported_smul (-3) (activeGamma_supported active hactive hq hf))
  have htransport : HaarCarrierEqv n
      (polyAdd
        (polyAdd (polyMul (commutatorPolynomial active q f) (commutatorPolynomial active q f))
          (polySmul 2 (polyMul y g)))
        (polySmul (-48) (polyMul v v)))
      (polyAdd (polyAdd (polyMul b b) (polySmul 2 (polyMul y g)))
        (polySmul (-48) (polyMul v v))) :=
    HaarCarrierEqv.add
      (HaarCarrierEqv.add (HaarCarrierEqv.mul hb hb) (HaarCarrierEqv.refl n _))
      (HaarCarrierEqv.refl n _)
  let target := polyAdd (polyAdd (polyMul b b) (polySmul 2 (polyMul y g)))
    (polySmul (-48) (polyMul v v))
  have hring : RatPolyCoeffEqv (polySmul 3 target)
      (polyAdd (polySmul 2 (polyMul s s))
        (polySmul 6 (polyAdd (polyMul y g) (polyNeg (polyMul x x))))) := by
    have hb' := (cap_mul_left 12 v).symm.add (cap_mul_left (-2) x).symm
    have hs' := (cap_mul_left 12 v).symm.add (cap_mul_left (-3) x).symm
    refine (cap_mul_left 3 target).symm.trans ?_
    refine ((RatPolyCoeffEqv.refl (cap 3)).mul
      (((hb'.mul hb').add (cap_mul_left 2 (polyMul y g)).symm).add
        (cap_mul_left (-48) (polyMul v v)).symm)).trans ?_
    refine (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.const 3) (.add
        (.add
          (.mul (.add (.mul (.const 12) (.var 0)) (.mul (.const (-2)) (.var 1)))
            (.add (.mul (.const 12) (.var 0)) (.mul (.const (-2)) (.var 1))))
          (.mul (.const 2) (.mul (.var 2) (.var 3))))
        (.mul (.const (-48)) (.mul (.var 0) (.var 0)))))
      (.add
        (.mul (.const 2)
          (.mul (.add (.mul (.const 12) (.var 0)) (.mul (.const (-3)) (.var 1)))
            (.add (.mul (.const 12) (.var 0)) (.mul (.const (-3)) (.var 1)))))
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
  exact Certificate.transport htransport
    (Certificate.ofCoeff hcancel.symm
      (Certificate.smul oneThird (by decide)
        (Certificate.ofCoeff hring
          (Certificate.add (Certificate.smul 2 (by decide) (Certificate.square s hs))
            (Certificate.smul 6 (by decide)
              (angularGramCertificate active hactive hq hf))))))

/-- Literal retained-square inequality, with no source or variance inverse. -/
theorem retained_square_bound {n : Nat} (active : List Nat)
    (hactive : ∀ b, b ∈ active → b < n) (q f : RatPoly)
    (hq : SupportedQuaternionBlocks n q) (hf : SupportedQuaternionBlocks n f)
    (hCf : HaarCarrierEqv n (activeCasimirPolynomial active f) (polySmul 12 f)) :
    48 * H n (polyMul (polyMul q f) (polyMul q f)) ≤
      H n (polyMul (commutatorPolynomial active q f) (commutatorPolynomial active q f)) +
        2 * H n (polyMul (activeGamma active q q) (activeGamma active f f)) := by
  have hn := (retainedSquareCertificate active hactive q f hq hf hCf).haar_nonnegative
  have he :
      H n (polyAdd
        (polyAdd
          (polyMul (commutatorPolynomial active q f) (commutatorPolynomial active q f))
          (polySmul 2 (polyMul (activeGamma active q q) (activeGamma active f f))))
        (polySmul (-48) (polyMul (polyMul q f) (polyMul q f)))) ≈
      (H n (polyMul (commutatorPolynomial active q f) (commutatorPolynomial active q f)) +
        2 * H n (polyMul (activeGamma active q q) (activeGamma active f f))) +
        -(48 * H n (polyMul (polyMul q f) (polyMul q f))) :=
    Q'.eqv_trans _ _ _ (quaternionHaar_append n _ _)
    (Q'.add_eqv_congr'
      (Q'.eqv_trans _ _ _ (quaternionHaar_append n _ _)
        (Q'.add_eqv_congr' (Q'.eqv_refl _) (quaternionHaar_polySmul n 2 _)))
      (Q'.eqv_trans _ _ _ (quaternionHaar_polySmul n (-48) _)
        (poly_identity_of_normal_eq (.mul (.const (-48)) (.var 0))
          (.neg (.mul (.const 48) (.var 0))) (by decide)
          (fun _ => H n (polyMul (polyMul q f) (polyMul q f))))))
  exact Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _ hn (Q'.le_of_eqv he))

/-- A quantitative improvement over dropping both negative squares: the original
quadratic coefficient retains 48 times the original source-observable square. -/
theorem sourceSecondMoment_le_retainedSquare (tail : Nat) (q f : RatPoly)
    (hq : SupportedQuaternionBlocks (tail+1) q)
    (hf : SupportedQuaternionBlocks (tail+1) f)
    (hCf : HaarCarrierEqv (tail+1)
      (activeCasimirPolynomial (List.range (tail+1)) f) (polySmul 12 f)) :
    sourceSecondMoment tail q f ≤
      -(H (tail+1) (polyMul (polyMul q q)
        (activeCasimirPolynomial (List.range (tail+1))
          (activeGamma (List.range (tail+1)) f f)))) -
        48 * H (tail+1) (polyMul (polyMul q f) (polyMul q f)) := by
  let active := List.range (tail+1)
  let S := H (tail+1) (polyMul (commutatorPolynomial active q f) (commutatorPolynomial active q f))
  let P := H (tail+1) (polyMul (activeGamma active q q) (activeGamma active f f))
  let R := H (tail+1) (polyMul (polyMul q q)
    (activeCasimirPolynomial active (activeGamma active f f)))
  let F := H (tail+1) (polyMul (polyMul q f) (polyMul q f))
  have hsq := retained_square_bound active (fun i hi => List.mem_range.mp hi) q f hq hf hCf
  have hr := Q'.add_le_add_right _ _ (-R) (Q'.neg_le_neg hsq)
  have hleft : sourceSecondMoment tail q f ≈ -(S+2*P)+ -R :=
    Q'.eqv_trans _ _ _ (sourceSecondMoment_curvature tail q f hq hf)
      (poly_identity_of_normal_eq
        (.add (.add (.neg (.var 0)) (.neg (.mul (.const 2) (.var 1)))) (.neg (.var 2)))
        (.add (.neg (.add (.var 0) (.mul (.const 2) (.var 1)))) (.neg (.var 2)))
        (by decide) (fun | 0 => S | 1 => P | _ => R))
  have hright : -(48*F)+ -R ≈ -R-48*F := Q'.add_comm_eqv _ _
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _ hr (Q'.le_of_eqv hright))

#print axioms angularPairs
#print axioms angularGramCertificate
#print axioms retainedSquareCertificate
#print axioms retained_square_bound
#print axioms sourceSecondMoment_le_retainedSquare

end YMGap.Continuum.SU2QuaternionSecondOrderRetainedSquare
