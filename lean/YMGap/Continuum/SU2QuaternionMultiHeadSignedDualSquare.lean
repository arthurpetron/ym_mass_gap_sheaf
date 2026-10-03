/-
# Conditional signed-dual Cauchy--Schwarz without a normalizer inverse

The two ACTUAL positive weights U=L*W+d and V=L*W-d produce
  4*(L^2*I(W)*I(W*f^2)-I(d*f)^2)
as the sum of their variance determinants and the mixed replica
I_x I_y[U_x*V_y*(f_x+f_y)^2]. Only the heads are copied; the entire
surviving tail and its action remain shared. No score d/W, normalizer
floor, positivity-to-certificate oracle, or variance-relative rate is used.
-/

import YMGap.Continuum.SU2QuaternionMultiHeadVarianceReplica
import YMGap.Continuum.SU2QuaternionHaarTailDerivative
import YMGap.Continuum.QuaternionHaarPolynomialSquareBound

namespace YMGap.Continuum.SU2QuaternionMultiHeadSignedDualSquare

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionHaarCertificateLift
open YMGap.Continuum.SU2QuaternionHaarCertificateIntegration
open YMGap.Continuum.SU2QuaternionHaarTailDerivative
open YMGap.Continuum.SU2QuaternionMultiHeadVarianceReplica
  (copy copy_mul copySupported copyCertificate replica_product determinant determinant_certificate)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul cap_mul_left)

local notation "I" heads:arg p:arg => partialHaarHeads heads p
local infix:50 " ≈ " => Q'.eqv

/-- Cross-channel Gram term with an ACTUAL plus-square witness. -/
def mixedPlusGram (heads : Nat) (U V f : RatPoly) : RatPoly :=
  polyAdd
    (polyAdd (polyMul (I heads U) (I heads (polyMul V (polyMul f f))))
      (polyMul (I heads (polyMul U (polyMul f f))) (I heads V)))
    (polyAdd (polyMul (I heads (polyMul U f)) (I heads (polyMul V f)))
      (polyMul (I heads (polyMul U f)) (I heads (polyMul V f))))

private def mixedReplica (heads : Nat) (U V f : RatPoly) : RatPoly :=
  let s := polyAdd (copy heads f) (liftBoundary heads f)
  polyMul (polyMul (copy heads U) (liftBoundary heads V)) (polyMul s s)

private theorem mixedReplica_identity (heads : Nat) (U V f : RatPoly) :
    RatPolyCoeffEqv (I (heads+heads) (mixedReplica heads U V f))
      (mixedPlusGram heads U V f) := by
  let e := polyAdd
    (polyAdd
      (polyMul (copy heads U) (liftBoundary heads (polyMul V (polyMul f f))))
      (polyMul (copy heads (polyMul U (polyMul f f))) (liftBoundary heads V)))
    (polyAdd
      (polyMul (copy heads (polyMul U f)) (liftBoundary heads (polyMul V f)))
      (polyMul (copy heads (polyMul U f)) (liftBoundary heads (polyMul V f))))
  have he : RatPolyCoeffEqv (mixedReplica heads U V f) e := by
    dsimp only [mixedReplica, e]
    simp only [copy_mul, lift_product]
    exact coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.var 1))
        (.mul (.add (.var 2) (.var 3)) (.add (.var 2) (.var 3))))
      (.add
        (.add (.mul (.var 0) (.mul (.var 1) (.mul (.var 3) (.var 3))))
          (.mul (.mul (.var 0) (.mul (.var 2) (.var 2))) (.var 1)))
        (.add (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3)))
          (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3)))))
      (by decide) (fun
        | 0 => copy heads U
        | 1 => liftBoundary heads V
        | 2 => copy heads f
        | _ => liftBoundary heads f)
  refine (partialHaarHeads_congr (heads+heads) he).trans ?_
  dsimp only [e, mixedPlusGram]
  simp only [partialHaarHeads_add]
  exact ((replica_product heads U (polyMul V (polyMul f f))).add
    (replica_product heads (polyMul U (polyMul f f)) V)).add
      ((replica_product heads (polyMul U f) (polyMul V f)).add
        (replica_product heads (polyMul U f) (polyMul V f)))

/-- Two DIFFERENT original positive laws, with every tail coordinate shared. -/
def mixedPlusGram_certificate (tail heads : Nat) (U V f : RatPoly)
    (hU : SupportedQuaternionBlocks (tail+heads) U)
    (_hV : SupportedQuaternionBlocks (tail+heads) V)
    (hf : SupportedQuaternionBlocks (tail+heads) f)
    (P : Certificate (tail+heads) U) (Q : Certificate (tail+heads) V) :
    Certificate tail (mixedPlusGram heads U V f) := by
  have QL : Certificate (tail+(heads+heads)) (liftBoundary heads V) := by
    simpa only [Nat.add_assoc] using lift_certificate heads Q
  have hfL : SupportedQuaternionBlocks (tail+(heads+heads)) (liftBoundary heads f) := by
    simpa only [Nat.add_assoc] using lift_supported hf heads
  have R : Certificate (tail+(heads+heads)) (mixedReplica heads U V f) :=
    ((copyCertificate tail heads U hU P).mul QL).mul
      (Certificate.square _ (supported_add (copySupported tail heads hf) hfL))
  exact Certificate.ofCoeff (mixedReplica_identity heads U V f).symm
    (partialHaarHeads_certificate tail (heads+heads) R)

private def dualGram (heads : Nat) (U V f : RatPoly) : RatPoly :=
  let s := polyAdd (I heads (polyMul U f)) (polyNeg (I heads (polyMul V f)))
  polyAdd
    (polyMul (polyAdd (I heads U) (I heads V))
      (polyAdd (I heads (polyMul U (polyMul f f))) (I heads (polyMul V (polyMul f f)))))
    (polyNeg (polyMul s s))

private def dualGram_certificate (tail heads : Nat) (U V f : RatPoly)
    (hU : SupportedQuaternionBlocks (tail+heads) U)
    (hV : SupportedQuaternionBlocks (tail+heads) V)
    (hf : SupportedQuaternionBlocks (tail+heads) f)
    (P : Certificate (tail+heads) U) (Q : Certificate (tail+heads) V) :
    Certificate tail (dualGram heads U V f) := by
  have h : RatPolyCoeffEqv (dualGram heads U V f)
      (polyAdd (polyAdd (determinant heads U f) (determinant heads V f))
        (mixedPlusGram heads U V f)) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.add (.var 0) (.var 1)) (.add (.var 2) (.var 3)))
        (.neg (.mul (.add (.var 4) (.neg (.var 5))) (.add (.var 4) (.neg (.var 5))))))
      (.add
        (.add (.add (.mul (.var 0) (.var 2)) (.neg (.mul (.var 4) (.var 4))))
          (.add (.mul (.var 1) (.var 3)) (.neg (.mul (.var 5) (.var 5)))))
        (.add (.add (.mul (.var 0) (.var 3)) (.mul (.var 2) (.var 1)))
          (.add (.mul (.var 4) (.var 5)) (.mul (.var 4) (.var 5)))))
      (by decide) (fun
        | 0 => I heads U
        | 1 => I heads V
        | 2 => I heads (polyMul U (polyMul f f))
        | 3 => I heads (polyMul V (polyMul f f))
        | 4 => I heads (polyMul U f)
        | _ => I heads (polyMul V f))
  exact Certificate.ofCoeff h
    (((determinant_certificate tail heads U f hU hf P).add
      (determinant_certificate tail heads V f hV hf Q)).add
      (mixedPlusGram_certificate tail heads U V f hU hV hf P Q))

private theorem integral_cap (heads : Nat) (L : Q') (p : RatPoly) :
    RatPolyCoeffEqv (I heads (polyMul (cap L) p)) (polyMul (cap L) (I heads p)) :=
  (partialHaarHeads_congr heads (cap_mul_left L p)).trans
    ((partialHaarHeads_smul heads L p).trans (cap_mul_left L _).symm)

private theorem signed_moment (heads : Nat) (L : Q') (W d r : RatPoly) :
    RatPolyCoeffEqv (I heads (polyMul (polyAdd (polyMul (cap L) W) d) r))
      (polyAdd (polyMul (cap L) (I heads (polyMul W r))) (I heads (polyMul d r))) := by
  have h : RatPolyCoeffEqv (polyMul (polyAdd (polyMul (cap L) W) d) r)
      (polyAdd (polyMul (cap L) (polyMul W r)) (polyMul d r)) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.add (.mul (.var 0) (.var 1)) (.var 2)) (.var 3))
      (.add (.mul (.var 0) (.mul (.var 1) (.var 3))) (.mul (.var 2) (.var 3)))
      (by decide) (fun | 0 => cap L | 1 => W | 2 => d | _ => r)
  refine (partialHaarHeads_congr heads h).trans ?_
  rw [partialHaarHeads_add]
  exact (integral_cap heads L (polyMul W r)).add (RatPolyCoeffEqv.refl _)

private theorem signed_moment_neg (heads : Nat) (L : Q') (W d r : RatPoly) :
    RatPolyCoeffEqv (I heads (polyMul (polyAdd (polyMul (cap L) W) (polyNeg d)) r))
      (polyAdd (polyMul (cap L) (I heads (polyMul W r))) (polyNeg (I heads (polyMul d r)))) :=
  (signed_moment heads L W (polyNeg d) r).trans
    ((RatPolyCoeffEqv.refl _).add
      ((partialHaarHeads_congr heads
        (coeffEvalExpr_eqv_of_normalize_eq (.mul (.neg (.var 0)) (.var 1))
          (.neg (.mul (.var 0) (.var 1))) (by decide) (fun | 0 => d | _ => r))).trans
        (partialHaarHeads_neg heads (polyMul d r))))

private theorem quarter_four (p : RatPoly) :
    RatPolyCoeffEqv (polySmul (Q'.invSucc 3) (polySmul 4 p)) p := by
  intro weight
  exact Q'.eqv_trans _ _ _ (ratWeightedSum_smul weight _ _)
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _ (ratWeightedSum_smul weight _ _))
      (Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right _ _ _ (by decide : Q'.invSucc 3*4 ≈ 1))
          (Q'.one_mul_eqv _))))

/-- Signed conditional dual-square bound, as data in the ORIGINAL cone.
There is no division by W or its polynomial-valued conditional mass. -/
def relativeDualSquare_certificate (tail heads : Nat) (W d f : RatPoly) (L : Q')
    (hW : SupportedQuaternionBlocks (tail+heads) W)
    (hd : SupportedQuaternionBlocks (tail+heads) d)
    (hf : SupportedQuaternionBlocks (tail+heads) f)
    (Pplus : Certificate (tail+heads) (polyAdd (polyMul (cap L) W) d))
    (Pminus : Certificate (tail+heads) (polyAdd (polyMul (cap L) W) (polyNeg d))) :
    Certificate tail (polyAdd
      (polyMul (cap (L*L)) (polyMul (I heads W) (I heads (polyMul W (polyMul f f)))))
      (polyNeg (polyMul (I heads (polyMul d f)) (I heads (polyMul d f))))) := by
  let U := polyAdd (polyMul (cap L) W) d
  let V := polyAdd (polyMul (cap L) W) (polyNeg d)
  let p := polyAdd
    (polyMul (cap (L*L)) (polyMul (I heads W) (I heads (polyMul W (polyMul f f)))))
    (polyNeg (polyMul (I heads (polyMul d f)) (I heads (polyMul d f))))
  have hbase := supported_polyMul
    (QuaternionHaarPolynomialSquareBound.SquareBound.constant (tail+heads) L).support hW
  have hneg : SupportedQuaternionBlocks (tail+heads) (polyNeg d) := by
    intro term ht
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
    exact hd s hs
  have P := dualGram_certificate tail heads U V f
    (supported_add hbase hd) (supported_add hbase hneg) hf Pplus Pminus
  have hmU : RatPolyCoeffEqv (I heads U)
      (polyAdd (polyMul (cap L) (I heads W)) (I heads d)) := by
    change RatPolyCoeffEqv (I heads (polyAdd _ _)) _
    rw [partialHaarHeads_add]
    exact (integral_cap heads L W).add (RatPolyCoeffEqv.refl _)
  have hmV : RatPolyCoeffEqv (I heads V)
      (polyAdd (polyMul (cap L) (I heads W)) (polyNeg (I heads d))) := by
    change RatPolyCoeffEqv (I heads (polyAdd _ _)) _
    rw [partialHaarHeads_add]
    exact (integral_cap heads L W).add (partialHaarHeads_neg heads d)
  have hmom := (((hmU.add hmV).mul
    ((signed_moment heads L W d (polyMul f f)).add
      (signed_moment_neg heads L W d (polyMul f f)))).add
    (RatPolyCoeffEqv.neg
      (((signed_moment heads L W d f).add
        (RatPolyCoeffEqv.neg (signed_moment_neg heads L W d f))).mul
        ((signed_moment heads L W d f).add
          (RatPolyCoeffEqv.neg (signed_moment_neg heads L W d f))))))
  have hpin : RatPolyCoeffEqv (dualGram heads U V f) (polySmul 4 p) := by
    refine hmom.trans ?_
    have hn := coeffEvalExpr_eqv_of_normalize_eq
      (.add
        (.mul (.add (.add (.mul (.var 0) (.var 1)) (.var 2))
          (.add (.mul (.var 0) (.var 1)) (.neg (.var 2))))
          (.add (.add (.mul (.var 0) (.var 3)) (.var 4))
            (.add (.mul (.var 0) (.var 3)) (.neg (.var 4)))))
        (.neg (.mul
          (.add (.add (.mul (.var 0) (.var 5)) (.var 6))
            (.neg (.add (.mul (.var 0) (.var 5)) (.neg (.var 6)))))
          (.add (.add (.mul (.var 0) (.var 5)) (.var 6))
            (.neg (.add (.mul (.var 0) (.var 5)) (.neg (.var 6))))))))
      (.mul (.const 4) (.add (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 3)))
        (.neg (.mul (.var 6) (.var 6)))))
      (by decide) (fun
        | 0 => cap L
        | 1 => I heads W
        | 2 => I heads d
        | 3 => I heads (polyMul W (polyMul f f))
        | 4 => I heads (polyMul d (polyMul f f))
        | 5 => I heads (polyMul W f)
        | _ => I heads (polyMul d f))
    exact hn.trans
      (((((cap_mul L L).mul_right _).add (RatPolyCoeffEqv.refl _)).mul_left (cap 4)).trans
        (cap_mul_left 4 p))
  exact Certificate.ofCoeff
    (((hpin.smul (Q'.invSucc 3)).trans (quarter_four p)).symm)
    (P.smul (Q'.invSucc 3) (by decide))

/-- Center BEFORE estimating: the actual signed covariance is controlled
by the actual conditional variance determinant. All normalizers are kept
as polynomials, including their zeros; no normalizer inverse is introduced. -/
def conditionalCovarianceSquare_certificate (tail heads : Nat) (W d f : RatPoly) (L : Q')
    (hW : SupportedQuaternionBlocks (tail+heads) W)
    (hd : SupportedQuaternionBlocks (tail+heads) d)
    (hf : SupportedQuaternionBlocks (tail+heads) f)
    (Pplus : Certificate (tail+heads) (polyAdd (polyMul (cap L) W) d))
    (Pminus : Certificate (tail+heads) (polyAdd (polyMul (cap L) W) (polyNeg d))) :
    let A := I heads W
    let b := I heads (polyMul W f)
    let s := polyAdd (polyMul A (I heads (polyMul d f)))
      (polyNeg (polyMul b (I heads d)))
    Certificate tail (polyAdd
      (polyMul (cap (L*L)) (polyMul (polyMul A A) (determinant heads W f)))
      (polyNeg (polyMul s s))) := by
  dsimp only
  let A := I heads W
  let b := I heads (polyMul W f)
  let H := I heads (polyMul W (polyMul f f))
  let x := polyAdd (polyMul f (liftBoundary heads A)) (polyNeg (liftBoundary heads b))
  have hA := partialHaarHeads_supported tail heads W hW
  have hb := partialHaarHeads_supported tail heads (polyMul W f) (supported_polyMul hW hf)
  have hn : SupportedQuaternionBlocks (tail+heads) (polyNeg (liftBoundary heads b)) := by
    intro term ht
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
    exact lift_supported hb heads s hs
  have hx : SupportedQuaternionBlocks (tail+heads) x :=
    supported_add (supported_polyMul hf (lift_supported hA heads)) hn
  have P := relativeDualSquare_certificate tail heads W d x L hW hd hx Pplus Pminus
  have hdx : RatPolyCoeffEqv (I heads (polyMul d x))
      (polyAdd (polyMul A (I heads (polyMul d f))) (polyNeg (polyMul b (I heads d)))) := by
    have he : RatPolyCoeffEqv (polyMul d x)
        (polyAdd (polyMul (polyMul d f) (liftBoundary heads A))
          (polyNeg (polyMul d (liftBoundary heads b)))) :=
      coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.var 0) (.add (.mul (.var 1) (.var 2)) (.neg (.var 3))))
        (.add (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.neg (.mul (.var 0) (.var 3))))
        (by decide) (fun | 0 => d | 1 => f | 2 => liftBoundary heads A | _ => liftBoundary heads b)
    refine (partialHaarHeads_congr heads he).trans ?_
    rw [partialHaarHeads_add]
    exact ((partialHaarHeads_mul_lift heads (polyMul d f) A).trans
      (RatPolyCoeffEqv.mul_comm _ A)).add
      ((partialHaarHeads_neg heads _).trans (RatPolyCoeffEqv.neg
        ((partialHaarHeads_mul_lift heads d b).trans (RatPolyCoeffEqv.mul_comm _ b))))
  have hwx : RatPolyCoeffEqv (I heads (polyMul W (polyMul x x)))
      (polyMul A (determinant heads W f)) := by
    let e := polyAdd
      (polyAdd (polyMul (polyMul W (polyMul f f)) (liftBoundary heads (polyMul A A)))
        (polyNeg (polyMul (polyMul W f) (liftBoundary heads (polyMul A b)))))
      (polyAdd (polyNeg (polyMul (polyMul W f) (liftBoundary heads (polyMul A b))))
        (polyMul W (liftBoundary heads (polyMul b b))))
    have he : RatPolyCoeffEqv (polyMul W (polyMul x x)) e := by
      dsimp only [e, x]
      simp only [lift_product]
      exact coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.var 0) (.mul (.add (.mul (.var 1) (.var 2)) (.neg (.var 3)))
          (.add (.mul (.var 1) (.var 2)) (.neg (.var 3)))))
        (.add
          (.add (.mul (.mul (.var 0) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2)))
            (.neg (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))))
          (.add (.neg (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3))))
            (.mul (.var 0) (.mul (.var 3) (.var 3)))))
        (by decide) (fun | 0 => W | 1 => f | 2 => liftBoundary heads A | _ => liftBoundary heads b)
    refine (partialHaarHeads_congr heads he).trans ?_
    dsimp only [e]
    rw [partialHaarHeads_add, partialHaarHeads_add, partialHaarHeads_add]
    have hcross := (partialHaarHeads_neg heads _).trans
      (RatPolyCoeffEqv.neg (partialHaarHeads_mul_lift heads (polyMul W f) (polyMul A b)))
    refine (((partialHaarHeads_mul_lift heads (polyMul W (polyMul f f)) (polyMul A A)).add hcross).add
      (hcross.add (partialHaarHeads_mul_lift heads W (polyMul b b)))).trans ?_
    exact coeffEvalExpr_eqv_of_normalize_eq
      (.add (.add (.mul (.var 2) (.mul (.var 0) (.var 0)))
        (.neg (.mul (.var 1) (.mul (.var 0) (.var 1)))))
        (.add (.neg (.mul (.var 1) (.mul (.var 0) (.var 1))))
          (.mul (.var 0) (.mul (.var 1) (.var 1)))))
      (.mul (.var 0) (.add (.mul (.var 0) (.var 2)) (.neg (.mul (.var 1) (.var 1)))))
      (by decide) (fun | 0 => A | 1 => b | _ => H)
  have hp := (((RatPolyCoeffEqv.refl A).mul hwx).mul_left (cap (L*L))).add
    (RatPolyCoeffEqv.neg (hdx.mul hdx))
  have hassoc := (RatPolyCoeffEqv.mul_assoc A A (determinant heads W f)).symm
  exact Certificate.ofCoeff
    ((hp.trans (((hassoc.mul_left (cap (L*L))).add (RatPolyCoeffEqv.refl _)))).symm) P

#print axioms mixedPlusGram
#print axioms mixedPlusGram_certificate
#print axioms relativeDualSquare_certificate
#print axioms conditionalCovarianceSquare_certificate

end YMGap.Continuum.SU2QuaternionMultiHeadSignedDualSquare
