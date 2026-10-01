/-
# A local source band controls the SAME interacting centered response

The source q is compared to a positive spectator R by constructed polynomial
certificates l*R <= q <= u*R.  A tested spectator eigenimage and its zero
first moment supply the dual R*(f-lambda*c), where c is ANY rational center.
Sharp kinetic Cauchy--Schwarz gives

  lambda*l^2 * H[q*(Pq)*(f-c)^2] <= u^2 * H[(q*(f-c))*P(q*(f-c))].

No source, spectator mass or variance is inverted.  The zero-mass case is
included.  The BF4 consumer must supply its ORIGINAL endpoint band and
eigenimage; no spacing-small coefficient is asserted by this finite lemma.
-/

import YMGap.Continuum.SU2QuaternionProductHeatDualForm
import YMGap.Continuum.SU2QuaternionProductHeatLocalBand
import YMGap.Continuum.SU2QuaternionProductHeatConstant
import YMGap.Continuum.SU2QuaternionProductHeatProjectedSourceEnergy
import YMGap.Continuum.QuaternionHaarDensityVariance
import YMGap.Continuum.PositiveDualBandScalar
import YMGap.Continuum.SU2QuaternionAngularSupport

namespace YMGap.Continuum.SU2QuaternionProductHeatBandResponse

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularSupport (polySmul_supported)
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatConstant
open YMGap.Continuum.SU2QuaternionProductHeatLocalBand
open YMGap.Continuum.SU2QuaternionProductHeatDualForm
open YMGap.Continuum.SU2QuaternionProductHeatProjectedSourceEnergy (sourceMoment)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul_left cap_mul)
open YMGap.Continuum.QuaternionHaarDensityVariance (shifted shifted_supported)
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz

local infix:50 " ≈ " => Q'.eqv
local notation:max "H" n:arg => quaternionHaar n

private theorem haar_neg (n : Nat) : ∀ p : RatPoly, H n (polyNeg p) ≈ -(H n p)
  | [] => by change (0 : Q') ≈ -0; decide
  | t::p => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.neg_mul_eqv t.2 (quaternionHaarMono n t.1)) (haar_neg n p))
      (Q'.eqv_symm (Q'.neg_add_eqv_split _ _))

private theorem supported_neg {n : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks n p) : SupportedQuaternionBlocks n (polyNeg p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

/-- A positive polynomial difference orders every supported square insertion. -/
theorem square_moment_order {n : Nat} {a b f : RatPoly}
    (C : Certificate n (polyAdd b (polyNeg a)))
    (hf : SupportedQuaternionBlocks n f) :
    H n (polyMul a (polyMul f f)) ≤ H n (polyMul b (polyMul f f)) := by
  have h := C.square_insertion_nonnegative f hf
  have he : H n (polyMul (polyMul f f) (polyAdd b (polyNeg a))) ≈
      H n (polyMul b (polyMul f f)) + -(H n (polyMul a (polyMul f f))) :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.add (.var 1) (.neg (.var 2))))
      (.add (.mul (.var 1) (.var 0)) (.neg (.mul (.var 2) (.var 0))))
      (by decide) (fun | 0 => polyMul f f | 1 => b | _ => a)))
      (Q'.eqv_trans _ _ _ (quaternionHaar_append n _ _)
        (Q'.add_eqv_congr' (Q'.eqv_refl _) (haar_neg n _)))
  exact Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _ h (Q'.le_of_eqv he))

private theorem smul_square_moment (n : Nat) (c : Q') (W f : RatPoly) :
    H n (polyMul (polySmul c W) (polyMul f f)) ≈
      c * H n (polyMul W (polyMul f f)) :=
  Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.polyMul_smul_left c W _))
    (quaternionHaar_polySmul n c _)

/-- Positivity of the actual heat transports the upper band, with the SAME
source and spectator retained in both endpoint factors. -/
def sourceProductUpper {n : Nat} {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K : Nat) (hK : BF4ExactSlabRetainedHeatHeadComparison.headCutoff w ≤ K)
    (ids : List Nat) (hids : ∀ i, i ∈ ids → i < n)
    {q R : RatPoly} (hq : SupportedQuaternionBlocks n q)
    (hR : SupportedQuaternionBlocks n R) (Q : Certificate n q) (CR : Certificate n R)
    {u : Q'} (hu : (0 : Q') ≤ u)
    (U : Certificate n (polyAdd (polySmul u R) (polyNeg q))) :
    Certificate n (polyAdd
      (polySmul (u*u) (polyMul R (productMap n w K ids R)))
      (polyNeg (polyMul q (productMap n w K ids q)))) := by
  let Pq := productMap n w K ids q
  let PR := productMap n w K ids R
  have CPq := erasedCertificate n hw0 hw1 K hK ids hids hq Q
  have CU := erasedCertificate n hw0 hw1 K hK ids hids
    (supported_add (polySmul_supported hR u) (supported_neg hq)) U
  have hmap : RatPolyCoeffEqv
      (productMap n w K ids (polyAdd (polySmul u R) (polyNeg q)))
      (polyAdd (polySmul u PR) (polyNeg Pq)) :=
    (productMap_add n w K ids _ _).trans
      ((productMap_smul n w K ids u R).add (productMap_neg n w K ids q))
  have CUP : Certificate n (polyAdd (polySmul u PR) (polyNeg Pq)) :=
    .ofCoeff hmap.symm CU
  have C := (U.mul CPq).add ((CR.smul u hu).mul CUP)
  have he : RatPolyCoeffEqv
      (polyAdd (polySmul (u*u) (polyMul R PR)) (polyNeg (polyMul q Pq)))
      (polyAdd (polyMul (polyAdd (polySmul u R) (polyNeg q)) Pq)
        (polyMul (polySmul u R) (polyAdd (polySmul u PR) (polyNeg Pq)))) := by
    have hs := (cap_mul_left (u*u) (polyMul R PR)).symm.trans
      ((cap_mul u u).symm.mul_right (polyMul R PR))
    exact (hs.add (.refl _)).trans
      ((coeffEvalExpr_eqv_of_normalize_eq
        (.add (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 2)))
          (.neg (.mul (.var 3) (.var 4))))
        (.add (.mul (.add (.mul (.var 0) (.var 1)) (.neg (.var 3))) (.var 4))
          (.mul (.mul (.var 0) (.var 1))
            (.add (.mul (.var 0) (.var 2)) (.neg (.var 4)))))
        (by decide) (fun | 0 => cap u | 1 => R | 2 => PR | 3 => q | _ => Pq)).trans
        ((((cap_mul_left u R).add (.refl _)).mul_right Pq).add
          ((cap_mul_left u R).mul ((cap_mul_left u PR).add (.refl _)))))
  exact .ofCoeff he C

/-- No division by lambda: the dual uses R*(f-lambda*c). -/
theorem dual_image (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (R f : RatPoly) (lambda c : Q')
    (heig : SupportedHaarEqv n (productMap n w K ids (polyMul R f))
      (polySmul lambda (polyMul (productMap n w K ids R) f))) :
    SupportedHaarEqv n
      (productMap n w K ids (polyMul R (shifted f (lambda*c))))
      (polySmul lambda (polyMul (productMap n w K ids R) (shifted f c))) := by
  let PR := productMap n w K ids R
  have hex (S : RatPoly) (a : Q') : RatPolyCoeffEqv (polyMul S (shifted f a))
      (polyAdd (polySmul 1 (polyMul S f)) (polySmul (-a) S)) := by
    unfold shifted
    exact (RatPolyCoeffEqv.mul_add_right S _ _).trans
      ((RatPolyCoeffEqv.polyMul_smul_right 1 S f).add
        ((RatPolyCoeffEqv.polyMul_smul_right (-a) S polyOne).trans
          ((RatPolyCoeffEqv.mul_one S).smul (-a))))
  have hleft := (productMap_congr n w K ids (hex R (lambda*c))).trans
    ((productMap_add n w K ids _ _).trans
      ((productMap_smul n w K ids 1 _).add (productMap_smul n w K ids (-(lambda*c)) R)))
  have hout : RatPolyCoeffEqv
      (polyAdd (polySmul 1 (polySmul lambda (polyMul PR f)))
        (polySmul (-(lambda*c)) PR))
      (polySmul lambda (polyMul PR (shifted f c))) := by
    have h1 := RatPolyCoeffEqv.one_smul (polySmul lambda (polyMul PR f))
    have hc : Q'.eqv (-(lambda*c)) (lambda*(-c)) :=
      poly_identity_of_normal_eq (.neg (.mul (.var 0) (.var 1)))
        (.mul (.var 0) (.neg (.var 1))) (by decide)
        (fun | 0 => lambda | _ => c)
    exact (h1.add ((RatPolyCoeffEqv.smul_coefficient hc PR).trans
      (RatPolyCoeffEqv.smul_assoc lambda (-c) PR).symm)).trans
      ((RatPolyCoeffEqv.smul_add _ _ _).symm.trans
        (((RatPolyCoeffEqv.one_smul (polyMul PR f)).symm.add (.refl _)).smul lambda |>.trans
          ((hex PR c).smul lambda).symm))
  exact (SupportedHaarEqv.of_carrier (RatPolyCoeffEqv.haarCarrier hleft)).trans
    (((heig.smul 1).add
      (SupportedHaarEqv.of_carrier (RatPolyCoeffEqv.haarCarrier (.refl _)))).trans
        (SupportedHaarEqv.of_carrier (RatPolyCoeffEqv.haarCarrier hout)))

private theorem weighted_add_right (n : Nat) (W a b d : RatPoly) :
    weightedPair n W a (polyAdd b d) ≈ weightedPair n W a b + weightedPair n W a d :=
  Q'.eqv_trans _ _ _ (weighted_symm n W a _)
    (Q'.eqv_trans _ _ _ (weighted_add_left n W b d a)
      (Q'.add_eqv_congr' (weighted_symm n W b a) (weighted_symm n W d a)))

private theorem weighted_smul_right (n : Nat) (W : RatPoly) (c : Q') (a b : RatPoly) :
    weightedPair n W a (polySmul c b) ≈ c*weightedPair n W a b :=
  Q'.eqv_trans _ _ _ (weighted_symm n W a _)
    (Q'.eqv_trans _ _ _ (weighted_smul_left n W c b a)
      (Q'.mul_eqv_congr_left c _ _ (weighted_symm n W b a)))

/-- Exact affine pair under a zero first moment. The observable can be the
complete signed family, so no off-diagonal term is discarded. -/
theorem shifted_pair_zero (n : Nat) (W f : RatPoly) (a b : Q')
    (hzero : H n (polyMul W f) ≈ 0) :
    H n (polyMul W (polyMul (shifted f a) (shifted f b))) ≈
      H n (polyMul W (polyMul f f)) + (a*b)*H n W := by
  let ff := weightedPair n W f f
  let fo := weightedPair n W f polyOne
  let oo := weightedPair n W polyOne polyOne
  have hff : ff ≈ H n (polyMul W (polyMul f f)) :=
    haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _)
  have hfo : fo ≈ 0 := Q'.eqv_trans _ _ _
    (haar_of_coeff (((RatPolyCoeffEqv.mul_one f).mul_right W).trans
      (RatPolyCoeffEqv.mul_comm _ _))) hzero
  have hof : weightedPair n W polyOne f ≈ 0 :=
    Q'.eqv_trans _ _ _ (weighted_symm n W polyOne f) hfo
  have hoo : oo ≈ H n W :=
    haar_of_coeff (((RatPolyCoeffEqv.one_mul polyOne).mul_right W).trans
      (RatPolyCoeffEqv.one_mul W))
  have row (p : RatPoly) : weightedPair n W p (shifted f b) ≈
      weightedPair n W p f + (-b)*weightedPair n W p polyOne := by
    exact Q'.eqv_trans _ _ _ (weighted_add_right n W p _ _)
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
        (weighted_smul_right n W 1 p f) (weighted_smul_right n W (-b) p polyOne))
        (Q'.add_eqv_congr' (Q'.one_mul_eqv _) (Q'.eqv_refl _)))
  have hpair := Q'.eqv_trans _ _ _
    (weighted_add_left n W (polySmul 1 f) (polySmul (-a) polyOne) (shifted f b))
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
      (weighted_smul_left n W 1 f (shifted f b))
      (weighted_smul_left n W (-a) polyOne (shifted f b)))
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
        (Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _) (row f))
        (Q'.mul_eqv_congr_left (-a) _ _ (row polyOne)))
        (Q'.add_eqv_congr'
          (Q'.add_eqv_congr' hff (Q'.mul_eqv_congr_left (-b) _ _ hfo))
          (Q'.mul_eqv_congr_left (-a) _ _
            (Q'.add_eqv_congr' hof (Q'.mul_eqv_congr_left (-b) _ _ hoo))))))
  exact Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
    (Q'.eqv_trans _ _ _ hpair
      (poly_identity_of_normal_eq
        (.add (.add (.var 0) (.mul (.neg (.var 1)) (.const 0)))
          (.mul (.neg (.var 2)) (.add (.const 0) (.mul (.neg (.var 1)) (.var 3)))))
        (.add (.var 0) (.mul (.mul (.var 2) (.var 1)) (.var 3)))
        (by decide) (fun
          | 0 => quaternionHaar n (polyMul W (polyMul f f))
          | 1 => b
          | 2 => a
          | _ => quaternionHaar n W)))

private theorem image_pairing (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (x t PR psi : RatPoly) (hx : SupportedQuaternionBlocks n x) (lambda : Q')
    (ht : SupportedHaarEqv n (productMap n w K ids t)
      (polySmul lambda (polyMul PR psi))) :
    kineticPair n w K ids x t ≈ lambda*H n (polyMul (polyMul x PR) psi) := by
  exact Q'.eqv_trans _ _ _ (ht x hx)
    (Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_smul_right n lambda x (polyMul PR psi))
      (Q'.mul_eqv_congr_left lambda _ _
        (haar_of_coeff (RatPolyCoeffEqv.mul_assoc x PR psi).symm)))

/-- The nonstationary source retains a quantitative fraction of the SAME
centered interacting moment. All cross terms are kept and no zero mass is
cancelled. Actual local band producers supply the polynomial certificates. -/
theorem response_band_cleared {n : Nat} {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K : Nat) (hK : BF4ExactSlabRetainedHeatHeadComparison.headCutoff w ≤ K)
    (ids : List Nat) (hids : ∀ i, i ∈ ids → i < n)
    {q R f : RatPoly} (hq : SupportedQuaternionBlocks n q)
    (hR : SupportedQuaternionBlocks n R) (hf : SupportedQuaternionBlocks n f)
    (Q : Certificate n q) (CR : Certificate n R)
    (lambda l u c : Q') (hlambda0 : (0 : Q') < lambda) (hlambda1 : lambda ≤ 1)
    (hl : (0 : Q') ≤ l) (hu : (0 : Q') ≤ u)
    (L : Certificate n (polyAdd q (polyNeg (polySmul l R))))
    (U : Certificate n (polyAdd (polySmul u R) (polyNeg q)))
    (heig : SupportedHaarEqv n (productMap n w K ids (polyMul R f))
      (polySmul lambda (polyMul (productMap n w K ids R) f)))
    (hzero : H n (polyMul (polyMul R (productMap n w K ids R)) f) ≈ 0) :
    lambda*(l*l)*sourceMoment n w K ids q (polyMul (shifted f c) (shifted f c)) ≤
      (u*u)*kineticPair n w K ids (polyMul q (shifted f c)) (polyMul q (shifted f c)) := by
  let PR := productMap n w K ids R
  let W := polyMul R PR
  let psi := shifted f c
  let tau := shifted f (lambda*c)
  let x := polyMul q psi
  let t := polyMul R tau
  let F := H n (polyMul W (polyMul psi psi))
  let M := sourceMoment n w K ids q (polyMul psi psi)
  let C := kineticPair n w K ids x t
  let B := kineticPair n w K ids x x
  let D := kineticPair n w K ids t t
  have hpsi := shifted_supported hf c
  have htau := shifted_supported hf (lambda*c)
  have hx := supported_polyMul hq hpsi
  have hts := supported_polyMul hR htau
  have CPR := erasedCertificate n hw0 hw1 K hK ids hids hR CR
  have CW := CR.mul CPR
  have hF : (0 : Q') ≤ F := Q'.le_trans' _ _ _
    (CW.square_insertion_nonnegative psi hpsi)
    (Q'.le_of_eqv (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _)))
  have hB : (0 : Q') ≤ B := kineticPair_nonnegative n w (Q'.le_of_lt hw0) K ids hids x hx
  have hD0 : (0 : Q') ≤ D := kineticPair_nonnegative n w (Q'.le_of_lt hw0) K ids hids t hts
  have hPt := dual_image n w K ids R f lambda c heig
  have hCpin : C ≈ lambda*H n (polyMul (polyMul q PR) (polyMul psi psi)) :=
    Q'.eqv_trans _ _ _ (image_pairing n w K ids x t PR psi hx lambda hPt)
      (Q'.mul_eqv_congr_left lambda _ _ (haar_of_coeff
        (coeffEvalExpr_eqv_of_normalize_eq
          (.mul (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.var 1))
          (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 1)))
          (by decide) (fun | 0 => q | 1 => psi | _ => PR))))
  have CL : Certificate n (polyAdd (polyMul q PR) (polyNeg (polySmul l W))) := by
    have he : RatPolyCoeffEqv
        (polyAdd (polyMul q PR) (polyNeg (polySmul l W)))
        (polyMul (polyAdd q (polyNeg (polySmul l R))) PR) :=
      ((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.neg (cap_mul_left l W).symm)).trans
        ((coeffEvalExpr_eqv_of_normalize_eq
          (.add (.mul (.var 0) (.var 1))
            (.neg (.mul (.var 2) (.mul (.var 3) (.var 1)))))
          (.mul (.add (.var 0) (.neg (.mul (.var 2) (.var 3)))) (.var 1))
          (by decide) (fun | 0 => q | 1 => PR | 2 => cap l | _ => R)).trans
          (((RatPolyCoeffEqv.refl q).add (RatPolyCoeffEqv.neg (cap_mul_left l R))).mul_right PR))
    exact .ofCoeff he (L.mul CPR)
  have hCF : l*F ≤ H n (polyMul (polyMul q PR) (polyMul psi psi)) :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv (smul_square_moment n l W psi))
      (square_moment_order CL hpsi)
  have hC : lambda*l*F ≤ C := Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.mul_assoc_eqv lambda l F))
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ lambda hCF (Q'.le_of_lt hlambda0))
      (Q'.ge_of_eqv hCpin))
  have hMpin : M ≈ H n (polyMul (polyMul q (productMap n w K ids q)) (polyMul psi psi)) :=
    haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.var 1)) (.var 2))
      (.mul (.mul (.var 0) (.var 2)) (.var 1))
      (by decide) (fun | 0 => q | 1 => polyMul psi psi | _ => productMap n w K ids q))
  have hM : M ≤ (u*u)*F := Q'.le_trans' _ _ _ (Q'.le_of_eqv hMpin)
    (Q'.le_trans' _ _ _
      (square_moment_order (sourceProductUpper hw0 hw1 K hK ids hids hq hR Q CR hu U) hpsi)
      (Q'.le_of_eqv (smul_square_moment n (u*u) W psi)))
  have hM0 : (0 : Q') ≤ M := Q'.le_trans' _ _ _
    (((Q.mul (erasedCertificate n hw0 hw1 K hK ids hids hq Q)).mul
      (Certificate.square psi hpsi)).haar_nonnegative)
    (Q'.ge_of_eqv hMpin)
  have hDpin : D ≈ lambda*H n (polyMul W (polyMul tau psi)) :=
    Q'.eqv_trans _ _ _ (image_pairing n w K ids t t PR psi hts lambda hPt)
      (Q'.mul_eqv_congr_left lambda _ _ (haar_of_coeff
        (coeffEvalExpr_eqv_of_normalize_eq
          (.mul (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.var 3))
          (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3)))
          (by decide) (fun | 0 => R | 1 => tau | 2 => PR | _ => psi))))
  have hW0 : (0 : Q') ≤ H n W := CW.haar_nonnegative
  have hc : (lambda*c)*c ≤ c*c := Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.mul_assoc_eqv lambda c c))
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ (c*c) hlambda1 (SumOfSquares.q_mul_self_nonneg c))
      (Q'.le_of_eqv (Q'.one_mul_eqv _)))
  have haff : H n (polyMul W (polyMul tau psi)) ≤ F :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (shifted_pair_zero n W f (lambda*c) c hzero))
      (Q'.le_trans' _ _ _
        (Q'.add_le_add_left _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ (H n W) hc hW0))
        (Q'.ge_of_eqv (shifted_pair_zero n W f c c hzero)))
  have hD : D ≤ lambda*F := Q'.le_trans' _ _ _ (Q'.le_of_eqv hDpin)
    (Q'.mul_le_mul_of_nonneg_left _ _ lambda haff (Q'.le_of_lt hlambda0))
  have hCS := kineticPair_cauchySchwarz n w (Q'.le_of_lt hw0) K ids hids x t hx hts
  exact PositiveDualBandScalar.response_cleared hlambda0 hlambda1 hl hu hF hM0 hB hD0 hC hCS hD hM

end YMGap.Continuum.SU2QuaternionProductHeatBandResponse

#print axioms YMGap.Continuum.SU2QuaternionProductHeatBandResponse.square_moment_order
#print axioms YMGap.Continuum.SU2QuaternionProductHeatBandResponse.sourceProductUpper
#print axioms YMGap.Continuum.SU2QuaternionProductHeatBandResponse.dual_image
#print axioms YMGap.Continuum.SU2QuaternionProductHeatBandResponse.shifted_pair_zero
#print axioms YMGap.Continuum.SU2QuaternionProductHeatBandResponse.response_band_cleared
