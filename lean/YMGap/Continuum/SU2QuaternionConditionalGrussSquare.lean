/-
# Conditional score covariance with the mean-derivative correction retained

For the ACTUAL positive densities U=L*W+d and V=L*W-d, their variance
determinants give the sharper polynomial certificate
  (L^2*A^2-D^2)*det(W,f) - (A*I(d*f)-I(W*f)*D)^2 >= 0,
where A=I(W), D=I(d). The subtracted mean derivative is not discarded.

Only the positive rational auxiliary L is inverted. No density, conditional
mass, terminal source or observable norm is inverted, including at their zeros.
This is finite shared-tail Haar algebra, not a scaling or mass-gap estimate.
An actual source square cap also pays the variance of its squared cleared
residual, retaining the negative noise square, without any inverse.
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
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionCoordinateColumnLift (lift_neg)
open YMGap.Continuum.SU2QuaternionHaarCertificateLift (lift_certificate)
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex (carrier_of_supported)
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

private theorem support_neg {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) : SupportedQuaternionBlocks blocks (polyNeg p) := by
  intro t ht
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ht
  exact hp r hr

private theorem lifted_cap (tail heads : Nat) (c : Q') :
    HaarCarrierEqv (tail+heads) (liftBoundary heads (cap c)) (cap c) := by
  have hp := lift_supported (SquareBound.constant tail c).support heads
  have hq := (SquareBound.constant (tail+heads) c).support
  apply carrier_of_supported hp hq
  intro r hr
  apply PaddedPolynomialCoeffEqv.haar_insert ?_ hp hq r hr
  unfold cap
  rw [lift_smul]
  exact (lift_one (tail+heads) heads).smul c

/-- Both actual signed tilts produce the corrected mass coefficient itself;
no sign or lower bound on either conditional mass is supplied. -/
def centeredRelativeCoefficient_certificate (tail heads : Nat) (W d : RatPoly) (L : Q')
    (Pplus : Certificate (tail+heads) (polyAdd (polyMul (cap L) W) d))
    (Pminus : Certificate (tail+heads) (polyAdd (polyMul (cap L) W) (polyNeg d))) :
    Certificate tail (centeredRelativeCoefficient heads W d L) := by
  have hp : RatPolyCoeffEqv
      (I heads (polyAdd (polyMul (cap L) W) d))
      (polyAdd (polyMul (cap L) (I heads W)) (I heads d)) := by
    rw [partialHaarHeads_add]
    exact (integral_cap heads L W).add (.refl _)
  have hm : RatPolyCoeffEqv
      (I heads (polyAdd (polyMul (cap L) W) (polyNeg d)))
      (polyAdd (polyMul (cap L) (I heads W)) (polyNeg (I heads d))) := by
    rw [partialHaarHeads_add]
    exact (integral_cap heads L W).add (partialHaarHeads_neg heads d)
  have h := (hp.mul hm).trans
    ((coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.add (.mul (.var 0) (.var 1)) (.var 2))
        (.add (.mul (.var 0) (.var 1)) (.neg (.var 2))))
      (.add (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.neg (.mul (.var 2) (.var 2))))
      (by decide) (fun | 0 => cap L | 1 => I heads W | _ => I heads d)).trans
      (((cap_mul L L).mul_right _).add (.refl _)))
  exact Certificate.ofCoeff h.symm
    ((partialHaarHeads_certificate tail heads Pplus).mul
      (partialHaarHeads_certificate tail heads Pminus))

/-- Exact second moment of the cleared conditional residual; zero heads,
zero mass and arbitrary surviving variables are included. -/
theorem residual_square_pin (heads : Nat) (W phi : RatPoly) :
    let A := I heads W
    let b := I heads (polyMul W phi)
    let X := polyAdd (polyMul (liftBoundary heads A) phi) (polyNeg (liftBoundary heads b))
    RatPolyCoeffEqv (I heads (polyMul W (polyMul X X)))
      (polyMul A (determinant heads W phi)) := by
  dsimp only
  let A := I heads W
  let b := I heads (polyMul W phi)
  let H := I heads (polyMul W (polyMul phi phi))
  have hex : RatPolyCoeffEqv
      (polyMul W (polyMul
        (polyAdd (polyMul (liftBoundary heads A) phi) (polyNeg (liftBoundary heads b)))
        (polyAdd (polyMul (liftBoundary heads A) phi) (polyNeg (liftBoundary heads b)))))
      (polyAdd (polyAdd
        (polyMul (polyMul W (polyMul phi phi)) (liftBoundary heads (polyMul A A)))
        (polyMul (polyMul W phi) (liftBoundary heads
          (polyNeg (polyAdd (polyMul A b) (polyMul A b))))))
        (polyMul W (liftBoundary heads (polyMul b b)))) := by
    simp only [lift_product, lift_neg, lift_add]
    exact coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.mul (.add (.mul (.var 2) (.var 1)) (.neg (.var 3)))
        (.add (.mul (.var 2) (.var 1)) (.neg (.var 3)))))
      (.add (.add (.mul (.mul (.var 0) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2)))
        (.mul (.mul (.var 0) (.var 1)) (.neg (.add (.mul (.var 2) (.var 3))
          (.mul (.var 2) (.var 3)))))) (.mul (.var 0) (.mul (.var 3) (.var 3))))
      (by decide) (fun | 0 => W | 1 => phi | 2 => liftBoundary heads A | _ => liftBoundary heads b)
  refine (partialHaarHeads_congr heads hex).trans ?_
  rw [partialHaarHeads_add, partialHaarHeads_add]
  exact (((partialHaarHeads_mul_lift heads _ _).add
    (partialHaarHeads_mul_lift heads _ _)).add (partialHaarHeads_mul_lift heads _ _)).trans
    (coeffEvalExpr_eqv_of_normalize_eq
      (.add (.add (.mul (.var 2) (.mul (.var 0) (.var 0)))
        (.mul (.var 1) (.neg (.add (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1))))))
        (.mul (.var 0) (.mul (.var 1) (.var 1))))
      (.mul (.var 0) (.add (.mul (.var 0) (.var 2)) (.neg (.mul (.var 1) (.var 1)))))
      (by decide) (fun | 0 => A | 1 => b | _ => H))

/-- Produced fourth-moment variance payment from the actual source square
cap. Neither C nor the conditional mass is inverted or required nonzero. -/
def squaredResidualVariance_certificate (tail heads : Nat) (W phi : RatPoly) (C : Q')
    (hW : SupportedQuaternionBlocks (tail+heads) W)
    (hphi : SupportedQuaternionBlocks (tail+heads) phi)
    (PW : Certificate (tail+heads) W)
    (Pphi : Certificate (tail+heads) (polyAdd (cap (C*C)) (polyNeg (polyMul phi phi)))) :
    let A := I heads W
    let b := I heads (polyMul W phi)
    let nu := determinant heads W phi
    let X := polyAdd (polyMul (liftBoundary heads A) phi) (polyNeg (liftBoundary heads b))
    Certificate tail (polyAdd
      (polyAdd (polyMul (polyMul (cap (4*(C*C))) (polyMul (polyMul A A) (polyMul A A))) nu)
        (polyNeg (polyMul (polyMul A A) (polyMul nu nu))))
      (polyNeg (determinant heads W (polyMul X X)))) := by
  dsimp only
  let A := I heads W
  let b := I heads (polyMul W phi)
  let H := I heads (polyMul W (polyMul phi phi))
  let nu := determinant heads W phi
  let LA := liftBoundary heads A
  let Lb := liftBoundary heads b
  let X := polyAdd (polyMul LA phi) (polyNeg Lb)
  have hA := partialHaarHeads_supported tail heads W hW
  have hb := partialHaarHeads_supported tail heads _ (supported_polyMul hW hphi)
  have hLA := lift_supported hA heads
  have hLb := lift_supported hb heads
  have hX := supported_add (supported_polyMul hLA hphi) (support_neg hLb)
  let PA := partialHaarHeads_certificate tail heads PW
  let Pnu := determinant_certificate tail heads W phi hW hphi PW
  have hcapMoment : RatPolyCoeffEqv
      (I heads (polyMul W (polyAdd (cap (C*C)) (polyNeg (polyMul phi phi)))))
      (polyAdd (polyMul (cap (C*C)) A) (polyNeg H)) := by
    refine (partialHaarHeads_congr heads
      (coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.var 0) (.add (.var 1) (.neg (.var 2))))
        (.add (.mul (.var 1) (.var 0)) (.neg (.mul (.var 0) (.var 2))))
        (by decide) (fun | 0 => W | 1 => cap (C*C) | _ => polyMul phi phi))).trans ?_
    change RatPolyCoeffEqv
      (I heads (polyAdd (polyMul (cap (C*C)) W) (polyNeg (polyMul W (polyMul phi phi)))))
      (polyAdd (polyMul (cap (C*C)) A) (polyNeg H))
    rw [partialHaarHeads_add]
    exact (integral_cap heads (C*C) W).add (partialHaarHeads_neg heads _)
  let Pmoment : Certificate tail (polyAdd (polyMul (cap (C*C)) A) (polyNeg H)) :=
    Certificate.ofCoeff hcapMoment.symm (partialHaarHeads_certificate tail heads (PW.mul Pphi))
  have hmeanCap : RatPolyCoeffEqv
      (polyAdd (polyMul (cap (C*C)) (polyMul A A)) (polyNeg (polyMul b b)))
      (polyAdd (polyMul A (polyAdd (polyMul (cap (C*C)) A) (polyNeg H))) nu) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.var 0) (.mul (.var 1) (.var 1))) (.neg (.mul (.var 2) (.var 2))))
      (.add (.mul (.var 1) (.add (.mul (.var 0) (.var 1)) (.neg (.var 3))))
        (.add (.mul (.var 1) (.var 3)) (.neg (.mul (.var 2) (.var 2)))))
      (by decide) (fun | 0 => cap (C*C) | 1 => A | 2 => b | _ => H)
  let Pmean := Certificate.ofCoeff hmeanCap ((PA.mul Pmoment).add Pnu)
  have hliftMean : HaarCarrierEqv (tail+heads)
      (liftBoundary heads (polyAdd (polyMul (cap (C*C)) (polyMul A A)) (polyNeg (polyMul b b))))
      (polyAdd (polyMul (cap (C*C)) (polyMul LA LA)) (polyNeg (polyMul Lb Lb))) := by
    simp only [lift_add, lift_product, lift_neg]
    exact HaarCarrierEqv.add (HaarCarrierEqv.mul_right _ (lifted_cap tail heads (C*C)))
      (HaarCarrierEqv.refl _ _)
  let PliftMean := Certificate.transport hliftMean.symm (lift_certificate heads Pmean)
  let Pbound := (((Certificate.square LA hLA).mul Pphi).smul 2 (by decide)).add
    ((PliftMean.smul 2 (by decide)).add
      (Certificate.square (polyAdd (polyMul LA phi) Lb)
        (supported_add (supported_polyMul hLA hphi) hLb)))
  have hbound : RatPolyCoeffEqv
      (polyAdd (polyMul (cap (4*(C*C))) (polyMul LA LA)) (polyNeg (polyMul X X)))
      (polyAdd (polySmul 2 (polyMul (polyMul LA LA)
        (polyAdd (cap (C*C)) (polyNeg (polyMul phi phi)))))
        (polyAdd (polySmul 2 (polyAdd (polyMul (cap (C*C)) (polyMul LA LA)) (polyNeg (polyMul Lb Lb))))
          (polyMul (polyAdd (polyMul LA phi) Lb) (polyAdd (polyMul LA phi) Lb)))) := by
    have hc := cap_mul 4 (C*C)
    refine ((hc.symm.mul_right _).add (.refl _)).trans ?_
    exact (coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.mul (.const 4) (.var 0)) (.mul (.var 1) (.var 1)))
        (.neg (.mul (.add (.mul (.var 1) (.var 2)) (.neg (.var 3)))
          (.add (.mul (.var 1) (.var 2)) (.neg (.var 3))))))
      (.add (.mul (.const 2) (.mul (.mul (.var 1) (.var 1))
        (.add (.var 0) (.neg (.mul (.var 2) (.var 2))))))
        (.add (.mul (.const 2) (.add (.mul (.var 0) (.mul (.var 1) (.var 1))) (.neg (.mul (.var 3) (.var 3)))))
          (.mul (.add (.mul (.var 1) (.var 2)) (.var 3)) (.add (.mul (.var 1) (.var 2)) (.var 3)))))
      (by decide) (fun | 0 => cap (C*C) | 1 => LA | 2 => phi | _ => Lb)).trans
      ((cap_mul_left 2 _).add ((cap_mul_left 2 _).add (.refl _)))
  let PX := Certificate.ofCoeff hbound Pbound
  let PF := partialHaarHeads_certificate tail heads
    ((PW.mul PX).mul (Certificate.square X hX))
  let F := I heads (polyMul W (polyMul (polyMul X X) (polyMul X X)))
  have hfourth : RatPolyCoeffEqv
      (I heads (polyMul (polyMul W
        (polyAdd (polyMul (cap (4*(C*C))) (polyMul LA LA)) (polyNeg (polyMul X X)))) (polyMul X X)))
      (polyAdd (polyMul (polyMul (cap (4*(C*C))) (polyMul A A)) (polyMul A nu)) (polyNeg F)) := by
    have hex : RatPolyCoeffEqv
        (polyMul (polyMul W (polyAdd (polyMul (cap (4*(C*C))) (polyMul LA LA)) (polyNeg (polyMul X X)))) (polyMul X X))
        (polyAdd (polyMul (cap (4*(C*C)))
          (polyMul (polyMul W (polyMul X X)) (liftBoundary heads (polyMul A A))))
          (polyNeg (polyMul W (polyMul (polyMul X X) (polyMul X X))))) := by
      rw [lift_product]
      exact coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.mul (.var 0) (.add (.mul (.var 3) (.mul (.var 2) (.var 2))) (.neg (.mul (.var 1) (.var 1)))))
          (.mul (.var 1) (.var 1)))
        (.add (.mul (.var 3) (.mul (.mul (.var 0) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))))
          (.neg (.mul (.var 0) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 1) (.var 1))))))
        (by decide) (fun | 0 => W | 1 => X | 2 => LA | _ => cap (4*(C*C)))
    refine (partialHaarHeads_congr heads hex).trans ?_
    rw [partialHaarHeads_add]
    exact (((integral_cap heads (4*(C*C)) _).trans
      (((partialHaarHeads_mul_lift heads _ _).trans ((residual_square_pin heads W phi).mul_right _)).mul_left _)).add
      (partialHaarHeads_neg heads _)).trans
      (coeffEvalExpr_eqv_of_normalize_eq
        (.add (.mul (.var 0) (.mul (.mul (.var 1) (.var 2)) (.mul (.var 1) (.var 1)))) (.neg (.var 3)))
        (.add (.mul (.mul (.var 0) (.mul (.var 1) (.var 1))) (.mul (.var 1) (.var 2))) (.neg (.var 3)))
        (by decide) (fun | 0 => cap (4*(C*C)) | 1 => A | 2 => nu | _ => F))
  let Pfinal := PA.mul (Certificate.ofCoeff hfourth.symm PF)
  have hdet := (RatPolyCoeffEqv.refl A).mul (RatPolyCoeffEqv.refl F)
  have hnoise := residual_square_pin heads W phi
  have hd : RatPolyCoeffEqv (determinant heads W (polyMul X X))
      (polyAdd (polyMul A F) (polyNeg (polyMul (polyMul A nu) (polyMul A nu)))) :=
    hdet.add (RatPolyCoeffEqv.neg (hnoise.mul hnoise))
  exact Certificate.ofCoeff
    ((((RatPolyCoeffEqv.refl _).add (.refl _)).add (RatPolyCoeffEqv.neg hd)).trans
      (coeffEvalExpr_eqv_of_normalize_eq
        (.add (.add (.mul (.mul (.var 0) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 1) (.var 1)))) (.var 2))
          (.neg (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2)))))
          (.neg (.add (.mul (.var 1) (.var 3)) (.neg (.mul (.mul (.var 1) (.var 2)) (.mul (.var 1) (.var 2)))))))
        (.mul (.var 1) (.add (.mul (.mul (.var 0) (.mul (.var 1) (.var 1))) (.mul (.var 1) (.var 2))) (.neg (.var 3))))
        (by decide) (fun | 0 => cap (4*(C*C)) | 1 => A | 2 => nu | _ => F))) Pfinal

end YMGap.Continuum.SU2QuaternionConditionalGrussSquare

#print axioms YMGap.Continuum.SU2QuaternionConditionalGrussSquare.centeredRelativeCoefficient
#print axioms YMGap.Continuum.SU2QuaternionConditionalGrussSquare.conditionalGrussSquare_certificate
#print axioms YMGap.Continuum.SU2QuaternionConditionalGrussSquare.centeredRelativeCoefficient_certificate
#print axioms YMGap.Continuum.SU2QuaternionConditionalGrussSquare.residual_square_pin
#print axioms YMGap.Continuum.SU2QuaternionConditionalGrussSquare.squaredResidualVariance_certificate
