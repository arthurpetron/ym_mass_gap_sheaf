/-
# Complete centered source energy and the SAME source heat loss

The affine heat image of a shifted eigenobservable is retained literally.
The signed cross term and moment mismatch are never dropped in the identity.
The optional cap estimate tests an explicit doubled-carrier certificate;
it requires no independence, source sign or stationary-source premise.
-/

import YMGap.Continuum.SU2QuaternionProductHeatMomentDefect
import YMGap.Continuum.SU2QuaternionProductHeatSourceYoungMoments
import YMGap.Continuum.SU2QuaternionProductHeatSumTest
import YMGap.Continuum.SU2QuaternionProductHeatSourceCentering

namespace YMGap.Continuum.SU2QuaternionProductHeatCenteredEnergyLoss

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularSupport (polySmul_supported)
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionCoordinateColumnLift (lift_neg)
open YMGap.Continuum.SU2QuaternionReplicaPairBounds (lift_cap_carrier)
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatConstant
open YMGap.Continuum.SU2QuaternionProductHeatDualForm
open YMGap.Continuum.SU2QuaternionProductHeatMomentDefect
open YMGap.Continuum.SU2QuaternionProductHeatContraction (productHeatCertificate)
open YMGap.Continuum.SU2QuaternionProductHeatProjectedSourceEnergy (sourceMoment sourceEnergy)
open YMGap.Continuum.SU2QuaternionWeightedProductDualEnergy (jump jump_supported)
open YMGap.Continuum.SU2QuaternionHaarCertificateExtension (certificate_extend)
open YMGap.Continuum.SU2QuaternionHaarCertificateLift (lift_certificate)
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction (HaarCarrierEqv)
open YMGap.Continuum.QuaternionHaarDensityVariance (shifted)
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz (weightedPair)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)

local infix:50 " ≈ " => Q'.eqv
local notation:max "H" n:arg => quaternionHaar n

private theorem support_neg {n : Nat} {p : RatPoly} (hp : SupportedQuaternionBlocks n p) :
    SupportedQuaternionBlocks n (polyNeg p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private theorem haar_neg (n : Nat) (p : RatPoly) : H n (polyNeg p) ≈ -(H n p) :=
  Q'.eqv_trans _ _ _ (haar_of_coeff (QuaternionHaarAngularCarrier.neg_smul p))
    (Q'.eqv_trans _ _ _ (quaternionHaar_polySmul n (-1) p)
      (poly_identity_of_normal_eq (.mul (.const (-1)) (.var 0)) (.neg (.var 0))
        (by decide) (fun _ => H n p)))

/-- Twice the signed source-increment cross term, under the ORIGINAL heat. -/
def sourceHeatCrossTwice (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (q psi : RatPoly) : Q' :=
  H (n+n) (polyMul (productHeat n w K ids)
    (polyMul (polyMul psi (liftBoundary n psi))
      (polyMul (jump n q) (jump n q))))

/-- Signed cross term; this definition makes no positivity assertion. -/
def sourceHeatCross (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (q psi : RatPoly) : Q' :=
  HalfPow.half*sourceHeatCrossTwice n w K ids q psi

/-- Exact doubled-carrier polarization before applying the affine image. -/
theorem sourceHeatCross_pin (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (hids : ∀ i, i ∈ ids → i < n) (q psi : RatPoly)
    (hq : SupportedQuaternionBlocks n q) (hp : SupportedQuaternionBlocks n psi) :
    sourceHeatCross n w K ids q psi ≈
      H n (polyMul (polyMul (polyMul q q) psi) (productMap n w K ids psi))-
        kineticPair n w K ids (polyMul q psi) (polyMul q psi) := by
  let r := polyMul (polyMul q q) psi
  let v := polyMul q psi
  let W := productHeat n w K ids
  let B := H n (polyMul r (productMap n w K ids psi))
  let C := kineticPair n w K ids v v
  have hx : sourceHeatCrossTwice n w K ids q psi ≈
      H (n+n) (polyMul W (polyMul r (liftBoundary n psi)))+
      (H (n+n) (polyMul W (polyMul psi (liftBoundary n r)))+
        -(2*H (n+n) (polyMul W (polyMul v (liftBoundary n v))))) := by
    unfold sourceHeatCrossTwice jump
    simp only [r, v, lift_product]
    have he := coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 4) (.mul (.mul (.var 2) (.var 3))
        (.mul (.add (.var 0) (.neg (.var 1))) (.add (.var 0) (.neg (.var 1))))))
      (.add (.mul (.var 4) (.mul (.mul (.mul (.var 0) (.var 0)) (.var 2)) (.var 3)))
        (.add (.mul (.var 4) (.mul (.var 2) (.mul (.mul (.var 1) (.var 1)) (.var 3))))
          (.neg (.mul (.const 2) (.mul (.var 4)
            (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3))))))))
      (by decide) (fun
        | 0 => q
        | 1 => liftBoundary n q
        | 2 => psi
        | 3 => liftBoundary n psi
        | _ => W)
    exact Q'.eqv_trans _ _ _ (haar_of_coeff he)
      (Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _)
        (Q'.add_eqv_congr' (Q'.eqv_refl _)
          (Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _)
            (Q'.add_eqv_congr' (Q'.eqv_refl _)
              (Q'.eqv_trans _ _ _ (haar_neg _ _)
                (Q'.neg_eqv_congr _ _ (Q'.eqv_trans _ _ _
                  (haar_of_coeff (cap_mul_left 2 _)) (quaternionHaar_polySmul _ 2 _))))))))
  have hlow := Q'.eqv_trans _ _ _ (productMap_pairing n w K ids r psi).symm
    (kineticPair_symm n w K ids hids psi r hp (supported_polyMul (supported_polyMul hq hq) hp))
  have hupp := (productMap_pairing n w K ids psi r).symm
  have hmid := (productMap_pairing n w K ids v v).symm
  have htwice : sourceHeatCrossTwice n w K ids q psi ≈ 2*(B-C) :=
    Q'.eqv_trans _ _ _ hx (Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' hlow (Q'.add_eqv_congr' hupp
        (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left 2 _ _ hmid))))
      (poly_identity_of_normal_eq
        (.add (.var 0) (.add (.var 0) (.neg (.mul (.const 2) (.var 1)))))
        (.mul (.const 2) (.add (.var 0) (.neg (.var 1))))
        (by decide) (fun | 0 => B | _ => C)))
  exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left HalfPow.half _ _ htwice)
    (Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv HalfPow.half 2 (B-C)).symm
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ (B-C)
        (by decide : HalfPow.half*2 ≈ 1)) (Q'.one_mul_eqv _)))

/-- The shifted eigenimage is affine, NOT an eigenpin for the centered test. -/
theorem productMap_shifted_affine (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (hnd : ids.Nodup) (hids : ∀ i, i ∈ ids → i < n)
    (f : RatPoly) (a mu : Q')
    (heig : SupportedHaarEqv n (productMap n w K ids f) (polySmul a f)) :
    SupportedHaarEqv n (productMap n w K ids (shifted f mu))
      (polyAdd (polySmul a (shifted f mu)) (cap (-(1-a)*mu))) := by
  unfold shifted
  have hmap := (productMap_add n w K ids (polySmul 1 f) (polySmul (-mu) polyOne)).trans
    ((productMap_smul n w K ids 1 f).add (productMap_smul n w K ids (-mu) polyOne))
  have hp : SupportedHaarEqv n
      (polyAdd (polySmul 1 (productMap n w K ids f))
        (polySmul (-mu) (productMap n w K ids polyOne)))
      (polyAdd (polySmul 1 (polySmul a f)) (polySmul (-mu) polyOne)) :=
    (heig.smul 1).add ((productMap_one n w K ids hnd hids).smul (-mu))
  have hr : RatPolyCoeffEqv
      (polyAdd (polySmul a (polyAdd (polySmul 1 f) (polySmul (-mu) polyOne)))
        (cap (-(1-a)*mu)))
      (polyAdd (polySmul a f) (polySmul (-mu) polyOne)) := by
    unfold cap
    have h1 := (RatPolyCoeffEqv.smul_add a (polySmul 1 f) (polySmul (-mu) polyOne)).add
      (RatPolyCoeffEqv.refl (polySmul (-(1-a)*mu) polyOne))
    have h2 := (((RatPolyCoeffEqv.smul_assoc a 1 f).trans
      (RatPolyCoeffEqv.smul_coefficient (Q'.mul_one_eqv a) f)).add
      (RatPolyCoeffEqv.smul_assoc a (-mu) polyOne)).add
      (RatPolyCoeffEqv.refl (polySmul (-(1-a)*mu) polyOne))
    have h3 := (RatPolyCoeffEqv.add_assoc _ _ _).trans
      ((RatPolyCoeffEqv.refl (polySmul a f)).add
        ((RatPolyCoeffEqv.add_smul_same _ _ polyOne).trans
          (RatPolyCoeffEqv.smul_coefficient
            (poly_identity_of_normal_eq
              (.add (.mul (.var 0) (.neg (.var 1)))
                (.mul (.neg (.add (.const 1) (.neg (.var 0)))) (.var 1)))
              (.neg (.var 1)) (by decide) (fun | 0 => a | _ => mu)) polyOne)))
    exact h1.trans (h2.trans h3)
  exact (SupportedHaarEqv.of_carrier (RatPolyCoeffEqv.haarCarrier hmap)).trans
    (hp.trans (SupportedHaarEqv.of_carrier (RatPolyCoeffEqv.haarCarrier
      (((RatPolyCoeffEqv.one_smul (polySmul a f)).add (RatPolyCoeffEqv.refl _)).trans hr.symm))))

/-- Complete signed source energy: original mean correction, cross term and
moment defect are all retained. -/
theorem sourceEnergy_centered_polarization (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (hids : ∀ i, i ∈ ids → i < n) (q psi : RatPoly)
    (hq : SupportedQuaternionBlocks n q) (hp : SupportedQuaternionBlocks n psi)
    (a mu : Q')
    (haff : SupportedHaarEqv n (productMap n w K ids psi)
      (polyAdd (polySmul a psi) (cap (-(1-a)*mu)))) :
    sourceEnergy n w K ids q psi ≈
      (1-a)*(rawSourceMoment n q (polyMul psi psi)+mu*rawSourceMoment n q psi)+
      sourceHeatCross n w K ids q psi-
      (rawSourceMoment n q (polyMul psi psi)-sourceMoment n w K ids q (polyMul psi psi)) := by
  let r := polyMul (polyMul q q) psi
  let A := rawSourceMoment n q (polyMul psi psi)
  let J := rawSourceMoment n q psi
  let S := sourceMoment n w K ids q (polyMul psi psi)
  let C := kineticPair n w K ids (polyMul q psi) (polyMul q psi)
  have hW : H n (polyMul r (productMap n w K ids psi)) ≈ a*A-(1-a)*mu*J := by
    have he := haff r (supported_polyMul (supported_polyMul hq hq) hp)
    exact Q'.eqv_trans _ _ _ he (Q'.eqv_trans _ _ _
      (quaternionHaar_polyMul_add_right n r _ _)
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr'
          (Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_smul_right n a r psi)
            (Q'.mul_eqv_congr_left a _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_assoc (polyMul q q) psi psi))))
          (Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_smul_right n (-(1-a)*mu) r polyOne)
            (Q'.mul_eqv_congr_left _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_one r)))))
        (poly_identity_of_normal_eq
          (.add (.mul (.var 0) (.var 1))
            (.mul (.mul (.neg (.add (.const 1) (.neg (.var 0)))) (.var 2)) (.var 3)))
          (.add (.mul (.var 0) (.var 1))
            (.neg (.mul (.mul (.add (.const 1) (.neg (.var 0))) (.var 2)) (.var 3))))
          (by decide) (fun | 0 => a | 1 => A | 2 => mu | _ => J))))
  have ht := Q'.eqv_trans _ _ _ (sourceHeatCross_pin n w K ids hids q psi hq hp)
    (Q'.add_eqv_congr' hW (Q'.eqv_refl (-C)))
  apply Q'.eqv_symm
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (Q'.add_eqv_congr' (Q'.eqv_refl _) ht) (Q'.eqv_refl _))
    (poly_identity_of_normal_eq
      (.add (.add (.mul (.add (.const 1) (.neg (.var 0)))
        (.add (.var 1) (.mul (.var 2) (.var 3))))
        (.add (.add (.mul (.var 0) (.var 1))
          (.neg (.mul (.mul (.add (.const 1) (.neg (.var 0))) (.var 2)) (.var 3))))
          (.neg (.var 4)))) (.neg (.add (.var 1) (.neg (.var 5)))))
      (.add (.var 5) (.neg (.var 4))) (by decide)
      (fun | 0 => a | 1 => A | 2 => mu | 3 => J | 4 => C | _ => S))

/-- A cap on the actual centered test bounds ONLY the signed cross term. -/
theorem sourceHeatCross_le_cap_loss (n : Nat) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat)
    (hK : headCutoff w ≤ K) (ids : List Nat) (hnd : ids.Nodup)
    (hids : ∀ i, i ∈ ids → i < n) (q psi : RatPoly)
    (hq : SupportedQuaternionBlocks n q) (C : Q') (P : SquareBound n psi C) :
    sourceHeatCross n w K ids q psi ≤ C*heatLossPair n w K ids q q := by
  have hgap : SupportedQuaternionBlocks n (gap C psi) :=
    supported_add (polySmul_supported (supported_one n) C)
      (support_neg (supported_polyMul P.support P.support))
  let Pl := certificate_extend n hgap P.certificate
  have hc : HaarCarrierEqv (n+n) (liftBoundary n (gap C psi))
      (gap C (liftBoundary n psi)) := by
    unfold gap
    rw [lift_add, lift_neg, lift_product]
    exact HaarCarrierEqv.add (lift_cap_carrier n C) (HaarCarrierEqv.refl _ _)
  let Pu : Certificate (n+n) (gap C (liftBoundary n psi)) :=
    .transport hc.symm (lift_certificate n P.certificate)
  let G := polyAdd (cap C) (polyNeg (polyMul psi (liftBoundary n psi)))
  have hg : Certificate (n+n) G := by
    have hdouble : RatPolyCoeffEqv (polyAdd G G)
        (polyAdd (gap C psi) (polyAdd (gap C (liftBoundary n psi))
          (polyMul (jump n psi) (jump n psi)))) := by
      unfold G gap jump
      exact coeffEvalExpr_eqv_of_normalize_eq
        (.add (.add (.var 0) (.neg (.mul (.var 1) (.var 2))))
          (.add (.var 0) (.neg (.mul (.var 1) (.var 2)))))
        (.add (.add (.var 0) (.neg (.mul (.var 1) (.var 1))))
          (.add (.add (.var 0) (.neg (.mul (.var 2) (.var 2))))
            (.mul (.add (.var 1) (.neg (.var 2))) (.add (.var 1) (.neg (.var 2))))))
        (by decide) (fun | 0 => cap C | 1 => psi | _ => liftBoundary n psi)
    have hhalf : RatPolyCoeffEqv (polySmul HalfPow.half (polyAdd G G)) G :=
      (RatPolyCoeffEqv.smul_add _ _ _).trans
        ((RatPolyCoeffEqv.add_smul_same _ _ _).trans
          ((RatPolyCoeffEqv.smul_coefficient (by decide) G).trans (RatPolyCoeffEqv.one_smul G)))
    exact Certificate.ofCoeff hhalf.symm (.smul HalfPow.half (by decide)
      (Certificate.ofCoeff hdouble (.add Pl (.add Pu (.square _ (jump_supported P.support))))))
  let W := productHeat n w K ids
  have hn := ((productHeatCertificate n hw0 hw1 K hK ids hids).mul hg).square_insertion_nonnegative
    (jump n q) (jump_supported hq)
  have he : H (n+n) (polyMul (polyMul (jump n q) (jump n q)) (polyMul W G)) ≈
      C*weightedPair (n+n) W (jump n q) (jump n q)-sourceHeatCrossTwice n w K ids q psi := by
    unfold G weightedPair sourceHeatCrossTwice cap
    have hr := coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.var 0))
        (.mul (.var 1) (.add (.var 2) (.neg (.mul (.var 3) (.var 4))))))
      (.add (.mul (.var 2) (.mul (.mul (.var 0) (.var 0)) (.var 1)))
        (.neg (.mul (.var 1) (.mul (.mul (.var 3) (.var 4)) (.mul (.var 0) (.var 0))))))
      (by decide) (fun
        | 0 => jump n q
        | 1 => W
        | 2 => cap C
        | 3 => psi
        | _ => liftBoundary n psi)
    exact Q'.eqv_trans _ _ _ (haar_of_coeff hr)
      (Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _)
        (Q'.add_eqv_congr' (Q'.eqv_trans _ _ _ (haar_of_coeff (cap_mul_left C _))
          (quaternionHaar_polySmul _ C _))
          (haar_neg _ _)))
  have hbound := Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _ hn (Q'.le_of_eqv he))
  have hj := jump_heatLoss_pin n w K ids hnd hids q q hq hq
  have hm := Q'.mul_le_mul_of_nonneg_left _ _ HalfPow.half hbound (by decide)
  exact Q'.le_trans' _ _ _ hm (Q'.le_of_eqv (Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left HalfPow.half _ _ (Q'.mul_eqv_congr_left C _ _ hj))
    (Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq
        (.mul (.var 0) (.mul (.var 1) (.mul (.const 2) (.var 2))))
        (.mul (.mul (.var 0) (.const 2)) (.mul (.var 1) (.var 2)))
        (by decide) (fun | 0 => HalfPow.half | 1 => C | _ => heatLossPair n w K ids q q))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _
        (by decide : HalfPow.half*2 ≈ 1)) (Q'.one_mul_eqv _)))))

#print axioms sourceHeatCrossTwice
#print axioms sourceHeatCross
#print axioms sourceHeatCross_pin
#print axioms productMap_shifted_affine
#print axioms sourceEnergy_centered_polarization
#print axioms sourceHeatCross_le_cap_loss

end YMGap.Continuum.SU2QuaternionProductHeatCenteredEnergyLoss
