/-
# Conditional score covariance with the mean-derivative correction retained

For the ACTUAL positive densities U=L*W+d and V=L*W-d, their variance
determinants give the sharper polynomial certificate
  (L^2*A^2-D^2)*det(W,f) - (A*I(d*f)-I(W*f)*D)^2 >= 0,
where A=I(W), D=I(d). The subtracted mean derivative is not discarded.

Only the positive rational auxiliary L is inverted. No density, conditional
mass, terminal source or observable norm is inverted, including at their zeros.
This is finite shared-tail Haar algebra, not a scaling or mass-gap estimate.
-/

import YMGap.Continuum.SU2QuaternionMultiHeadSignedDualSquare

namespace YMGap.Continuum.SU2QuaternionConditionalGrussSquare

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
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.SU2QuaternionHaarCertificateIntegration
open YMGap.Continuum.SU2QuaternionHaarTailDerivative
open YMGap.Continuum.SU2QuaternionMultiHeadVarianceReplica (determinant determinant_certificate)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul cap_mul_left SquareBound)

local notation "I" heads:arg p:arg => partialHaarHeads heads p

private theorem integral_cap (heads : Nat) (L : Q') (p : RatPoly) :
    RatPolyCoeffEqv (I heads (polyMul (cap L) p)) (polyMul (cap L) (I heads p)) :=
  (partialHaarHeads_congr heads (cap_mul_left L p)).trans
    ((partialHaarHeads_smul heads L p).trans (cap_mul_left L _).symm)

private theorem plus_moment (heads : Nat) (L : Q') (W d r : RatPoly) :
    RatPolyCoeffEqv (I heads (polyMul (polyAdd (polyMul (cap L) W) d) r))
      (polyAdd (polyMul (cap L) (I heads (polyMul W r))) (I heads (polyMul d r))) := by
  have he : RatPolyCoeffEqv
      (polyMul (polyAdd (polyMul (cap L) W) d) r)
      (polyAdd (polyMul (cap L) (polyMul W r)) (polyMul d r)) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.add (.mul (.var 0) (.var 1)) (.var 2)) (.var 3))
      (.add (.mul (.var 0) (.mul (.var 1) (.var 3))) (.mul (.var 2) (.var 3)))
      (by decide) (fun | 0 => cap L | 1 => W | 2 => d | _ => r)
  refine (partialHaarHeads_congr heads he).trans ?_
  rw [partialHaarHeads_add]
  exact (integral_cap heads L (polyMul W r)).add (RatPolyCoeffEqv.refl _)

private theorem minus_moment (heads : Nat) (L : Q') (W d r : RatPoly) :
    RatPolyCoeffEqv (I heads (polyMul (polyAdd (polyMul (cap L) W) (polyNeg d)) r))
      (polyAdd (polyMul (cap L) (I heads (polyMul W r)))
        (polyNeg (I heads (polyMul d r)))) :=
  (plus_moment heads L W (polyNeg d) r).trans
    ((RatPolyCoeffEqv.refl _).add
      ((partialHaarHeads_congr heads
        (coeffEvalExpr_eqv_of_normalize_eq (.mul (.neg (.var 0)) (.var 1))
          (.neg (.mul (.var 0) (.var 1))) (by decide) (fun | 0 => d | _ => r))).trans
        (partialHaarHeads_neg heads (polyMul d r))))

/-- The corrected polynomial coefficient, with the original conditional
mass and mean signed derivative kept separately. -/
def centeredRelativeCoefficient (heads : Nat) (W d : RatPoly) (L : Q') : RatPoly :=
  polyAdd (polyMul (cap (L*L)) (polyMul (I heads W) (I heads W)))
    (polyNeg (polyMul (I heads d) (I heads d)))

/-- The improvement is produced by two ACTUAL positive conditional laws.
No conditional Poincare, Fisher-information or normalization premise is used. -/
def conditionalGrussSquare_certificate (tail heads : Nat) (W d f : RatPoly)
    (L : Q') (hL : (0 : Q') < L)
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
      (polyMul (centeredRelativeCoefficient heads W d L) (determinant heads W f))
      (polyNeg (polyMul s s))) := by
  dsimp only
  let U := polyAdd (polyMul (cap L) W) d
  let V := polyAdd (polyMul (cap L) W) (polyNeg d)
  have hbase := supported_polyMul (SquareBound.constant (tail+heads) L).support hW
  have hneg : SupportedQuaternionBlocks (tail+heads) (polyNeg d) := by
    intro t ht
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ht
    exact hd r hr
  have hU := supported_add hbase hd
  have hV := supported_add hbase hneg
  let u := I heads U
  let v := I heads V
  let Du := determinant heads U f
  let Dv := determinant heads V f
  have Pu : Certificate tail u := partialHaarHeads_certificate tail heads Pplus
  have Pv : Certificate tail v := partialHaarHeads_certificate tail heads Pminus
  have PD := (Pu.add Pv).mul
    ((Pv.mul (determinant_certificate tail heads U f hU hf Pplus)).add
      (Pu.mul (determinant_certificate tail heads V f hV hf Pminus)))
  let A := I heads W
  let D := I heads d
  let b := I heads (polyMul W f)
  let e := I heads (polyMul d f)
  let H := I heads (polyMul W (polyMul f f))
  let J := I heads (polyMul d (polyMul f f))
  let s := polyAdd (polyMul A e) (polyNeg (polyMul b D))
  let p := polyAdd
    (polyMul (centeredRelativeCoefficient heads W d L) (determinant heads W f))
    (polyNeg (polyMul s s))
  have hu : RatPolyCoeffEqv u (polyAdd (polyMul (cap L) A) D) := by
    change RatPolyCoeffEqv (I heads (polyAdd _ _)) _
    rw [partialHaarHeads_add]
    exact (integral_cap heads L W).add (RatPolyCoeffEqv.refl _)
  have hv : RatPolyCoeffEqv v (polyAdd (polyMul (cap L) A) (polyNeg D)) := by
    change RatPolyCoeffEqv (I heads (polyAdd _ _)) _
    rw [partialHaarHeads_add]
    exact (integral_cap heads L W).add (partialHaarHeads_neg heads d)
  have hDu := (hu.mul (plus_moment heads L W d (polyMul f f))).add
    (RatPolyCoeffEqv.neg ((plus_moment heads L W d f).mul (plus_moment heads L W d f)))
  have hDv := (hv.mul (minus_moment heads L W d (polyMul f f))).add
    (RatPolyCoeffEqv.neg ((minus_moment heads L W d f).mul (minus_moment heads L W d f)))
  have hpin := (hu.add hv).mul ((hv.mul hDu).add (hu.mul hDv))
  let ua : PolyExpr := .add (.mul (.var 0) (.var 1)) (.var 2)
  let va : PolyExpr := .add (.mul (.var 0) (.var 1)) (.neg (.var 2))
  let ub : PolyExpr := .add (.mul (.var 0) (.var 3)) (.var 4)
  let vb : PolyExpr := .add (.mul (.var 0) (.var 3)) (.neg (.var 4))
  let uh : PolyExpr := .add (.mul (.var 0) (.var 5)) (.var 6)
  let vh : PolyExpr := .add (.mul (.var 0) (.var 5)) (.neg (.var 6))
  let du : PolyExpr := .add (.mul ua uh) (.neg (.mul ub ub))
  let dv : PolyExpr := .add (.mul va vh) (.neg (.mul vb vb))
  let score : PolyExpr := .add (.mul (.var 1) (.var 4))
    (.neg (.mul (.var 3) (.var 2)))
  let coefficient : PolyExpr := .add
    (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1)))
    (.neg (.mul (.var 2) (.var 2)))
  let variance : PolyExpr := .add (.mul (.var 1) (.var 5))
    (.neg (.mul (.var 3) (.var 3)))
  have hring := coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.add ua va) (.add (.mul va du) (.mul ua dv)))
    (.mul (.mul (.const 4) (.mul (.var 0) (.var 0)))
      (.add (.mul coefficient variance) (.neg (.mul score score))))
    (by decide) (fun | 0 => cap L | 1 => A | 2 => D | 3 => b | 4 => e | 5 => H | _ => J)
  have hc := cap_mul L L
  have htarget := ((hc.mul_right (polyMul A A)).add
    (RatPolyCoeffEqv.refl (polyNeg (polyMul D D)))).mul
    (RatPolyCoeffEqv.refl (determinant heads W f))
  have hscale := (hc.mul_left (cap 4)).trans (cap_mul 4 (L*L))
  have hfinal : RatPolyCoeffEqv (polyMul (polyAdd u v) (polyAdd (polyMul v Du) (polyMul u Dv)))
      (polySmul (4*(L*L)) p) :=
    hpin.trans (hring.trans
      (((hscale.mul (htarget.add (RatPolyCoeffEqv.refl _))).trans
        (cap_mul_left (4*(L*L)) p))))
  let m := 4*(L*L)
  have hm : (0 : Q') < m := Q'.mul_pos (by decide) (Q'.mul_pos hL hL)
  let inv := Q'.recipPos m hm
  have hcancel : RatPolyCoeffEqv (polySmul inv (polySmul m p)) p :=
    (RatPolyCoeffEqv.smul_assoc inv m p).trans
      ((RatPolyCoeffEqv.smul_coefficient
        (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv inv m) (Q'.mul_recipPos_eqv m hm)) p).trans
        (RatPolyCoeffEqv.one_smul p))
  exact Certificate.ofCoeff hcancel.symm
    (.smul inv (Q'.le_of_lt (Q'.recipPos_pos m hm)) (.ofCoeff hfinal.symm PD))

end YMGap.Continuum.SU2QuaternionConditionalGrussSquare

#print axioms YMGap.Continuum.SU2QuaternionConditionalGrussSquare.centeredRelativeCoefficient
#print axioms YMGap.Continuum.SU2QuaternionConditionalGrussSquare.conditionalGrussSquare_certificate
