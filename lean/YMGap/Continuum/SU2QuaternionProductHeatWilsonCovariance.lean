/-
# Sharp scalar Wilson covariance under the ORIGINAL product heat

The actual joint kernel, not a coordinate telescope or vector amplification,
gives a squared signed pairing bound with coefficient 1-w^(8*perimeter).
The entire signed source and arbitrary certified upper action are retained.
The upper test costs its SAME weighted square, not a raw Haar square.
Conditional source loss remains an explicit cost; it is not interacting OWN
variance, a lag-one reserve, or a proved changing-family survival budget.
-/

import YMGap.Continuum.SU2QuaternionProductHeatWilsonSpinTwo
import YMGap.Continuum.SU2QuaternionProductHeatMultiplicationDefect
import YMGap.Continuum.SU2QuaternionProductHeatContraction
import YMGap.Continuum.SU2QuaternionHaarCertificateLift
import YMGap.Continuum.HeatKernelGap

namespace YMGap.Continuum.SU2QuaternionProductHeatWilsonCovariance

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularSupport (polySmul_supported)
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPlaquetteHeatPropagation
open YMGap.Continuum.SU2QuaternionSpinTwoConditionalHaar (orientedCoordinateQuaternion)
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry (character_supported)
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatWilsonWord (wordAt productMap_fundamental_word)
open YMGap.Continuum.SU2QuaternionProductHeatWilsonSpinTwo (productMap_fundamental_square)
open YMGap.Continuum.SU2QuaternionProductHeatPlaquetteSquare (first_character_square)
open YMGap.Continuum.SU2QuaternionProductHeatContraction (productHeatCertificate)
open YMGap.Continuum.SU2QuaternionProductHeatMultiplicationDefect
open YMGap.Continuum.SU2QuaternionHaarCertificateLift
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz

local infix:50 " ≈ " => Q'.eqv
local notation:max "H" n:arg => quaternionHaar n

/-- Literal conditional loss under the SAME selected product map. -/
def fullSourceLoss (n : Nat) (w : Q') (K : Nat) (ids : List Nat) (q : RatPoly) : RatPoly :=
  let Q := productMap n w K ids q
  polyAdd (productMap n w K ids (polyMul q q)) (polySmul (-1) (polyMul Q Q))

def wordCovarianceRate (w : Q') (perimeter : Nat) : Q' := 1-qpow w (8*perimeter)

private def centered (n : Nat) (w : Q') (K : Nat) (ids : List Nat) (q : RatPoly) : RatPoly :=
  polyAdd q (polySmul (-1) (liftBoundary n (productMap n w K ids q)))

private theorem support_mono {n : Nat} {q : RatPoly} (hq : SupportedQuaternionBlocks n q) :
    SupportedQuaternionBlocks (n+n) q :=
  fun term hm => Nat.le_trans (hq term hm) (Nat.mul_le_mul_left 4 (by omega))

private theorem word_supported (n : Nat) (block : OrientedBF4Link → Nat) :
    ∀ es, (∀ e, e ∈ es → block e < n) → QuaternionSupported n (wordAt block es)
  | [], _ =>
      ⟨supported_one n, (fun _ h => False.elim (List.not_mem_nil h)),
        (fun _ h => False.elim (List.not_mem_nil h)), (fun _ h => False.elim (List.not_mem_nil h))⟩
  | e::es, h => by
      have he : QuaternionSupported n (orientedCoordinateQuaternion (block e) e.reverse) := by
        cases e.reverse
        · exact QuaternionSupported.coordinate (h e List.mem_cons_self)
        · exact (QuaternionSupported.coordinate (h e List.mem_cons_self)).conj
      exact he.mul (word_supported n block es (fun f hf => h f (List.mem_cons_of_mem e hf)))

private theorem centered_supported (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (hids : ∀ i, i ∈ ids → i < n) {q : RatPoly} (hq : SupportedQuaternionBlocks n q) :
    SupportedQuaternionBlocks (n+n) (centered n w K ids q) :=
  supported_add (support_mono hq)
    (polySmul_supported (lift_supported (productMap_supported n w K ids hids hq) n) (-1))

private theorem haar_sub (n : Nat) (p q : RatPoly) :
    H n (polyAdd p (polySmul (-1) q)) ≈ H n p-H n q :=
  Q'.eqv_trans _ _ _ (quaternionHaar_append n _ _)
    (Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.eqv_trans _ _ _ (quaternionHaar_polySmul n (-1) q)
        (Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 _) (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv _)))))

private theorem weighted_difference (n : Nat) (W x y X Y : RatPoly) :
    weightedPair n W (polyAdd x (polySmul (-1) X)) (polyAdd y (polySmul (-1) Y)) ≈
      (weightedPair n W x y-weightedPair n W x Y)-
        (weightedPair n W X y-weightedPair n W X Y) := by
  have right (p : RatPoly) : weightedPair n W p (polyAdd y (polySmul (-1) Y)) ≈
      weightedPair n W p y-weightedPair n W p Y :=
    Q'.eqv_trans _ _ _ (weighted_symm n W _ _)
      (Q'.eqv_trans _ _ _ (weighted_add_left n W _ _ p)
        (Q'.add_eqv_congr' (weighted_symm n W y p)
          (Q'.eqv_trans _ _ _ (weighted_smul_left n W (-1) Y p)
            (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (weighted_symm n W Y p))
              (Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 _)
                (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv _)))))))
  exact Q'.eqv_trans _ _ _ (weighted_add_left n W _ _ _)
    (Q'.add_eqv_congr' (right x)
      (Q'.eqv_trans _ _ _ (weighted_smul_left n W (-1) X _)
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (right X))
          (Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 _)
            (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv _))))))

private theorem lower_pair (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (D x y : RatPoly) :
    weightedPair (n+n) (polyMul (productHeat n w K ids) (liftBoundary n D)) x y ≈
      H n (polyMul D (productMap n w K ids (polyMul x y))) :=
  Q'.eqv_trans _ _ _
    (haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
      (.mul (.var 2) (.mul (.mul (.var 0) (.var 1)) (.var 3))) (by decide)
      (fun | 0 => x | 1 => y | 2 => productHeat n w K ids | _ => liftBoundary n D)))
    (Q'.eqv_symm (productMap_pairing n w K ids (polyMul x y) D))

private theorem mixed_pair (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (D x Y : RatPoly) :
    weightedPair (n+n) (polyMul (productHeat n w K ids) (liftBoundary n D)) x (liftBoundary n Y) ≈
      H n (polyMul D (polyMul Y (productMap n w K ids x))) := by
  have hr : RatPolyCoeffEqv
      (polyMul (polyMul x (liftBoundary n Y))
        (polyMul (productHeat n w K ids) (liftBoundary n D)))
      (polyMul (productHeat n w K ids) (polyMul x (liftBoundary n (polyMul D Y)))) := by
    rw [lift_product]
    exact coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
      (.mul (.var 2) (.mul (.var 0) (.mul (.var 3) (.var 1)))) (by decide)
      (fun | 0 => x | 1 => liftBoundary n Y | 2 => productHeat n w K ids | _ => liftBoundary n D)
  exact Q'.eqv_trans _ _ _ (haar_of_coeff hr)
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm (productMap_pairing n w K ids x (polyMul D Y)))
      (haar_of_coeff (RatPolyCoeffEqv.mul_assoc D Y _)))

private theorem upper_pair (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (hnd : ids.Nodup) (hids : ∀ i, i ∈ ids → i < n) (D X Y : RatPoly)
    (hD : SupportedQuaternionBlocks n D) (hX : SupportedQuaternionBlocks n X)
    (hY : SupportedQuaternionBlocks n Y) :
    weightedPair (n+n) (polyMul (productHeat n w K ids) (liftBoundary n D))
      (liftBoundary n X) (liftBoundary n Y) ≈ H n (polyMul D (polyMul X Y)) := by
  have hr : RatPolyCoeffEqv
      (polyMul (polyMul (liftBoundary n X) (liftBoundary n Y))
        (polyMul (productHeat n w K ids) (liftBoundary n D)))
      (polyMul (productHeat n w K ids) (liftBoundary n (polyMul D (polyMul X Y)))) := by
    rw [lift_product, lift_product]
    exact coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
      (.mul (.var 2) (.mul (.var 3) (.mul (.var 0) (.var 1)))) (by decide)
      (fun
        | 0 => liftBoundary n X
        | 1 => liftBoundary n Y
        | 2 => productHeat n w K ids
        | _ => liftBoundary n D)
  exact Q'.eqv_trans _ _ _ (haar_of_coeff hr)
    (productHeat_upper_marginal n w K ids hnd hids _
      (supported_polyMul hD (supported_polyMul hX hY)))

private theorem centered_pair (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (hnd : ids.Nodup) (hids : ∀ i, i ∈ ids → i < n) (D q f : RatPoly)
    (hD : SupportedQuaternionBlocks n D) (hq : SupportedQuaternionBlocks n q)
    (hf : SupportedQuaternionBlocks n f) :
    weightedPair (n+n) (polyMul (productHeat n w K ids) (liftBoundary n D))
      (centered n w K ids q) (centered n w K ids f) ≈
      H n (polyMul D (polyAdd (productMap n w K ids (polyMul q f))
        (polySmul (-1) (polyMul (productMap n w K ids q) (productMap n w K ids f))))) := by
  let W := polyMul (productHeat n w K ids) (liftBoundary n D)
  let Q := productMap n w K ids q
  let F := productMap n w K ids f
  have hQ := productMap_supported n w K ids hids hq
  have hF := productMap_supported n w K ids hids hf
  have hxy := lower_pair n w K ids D q f
  have hxY := mixed_pair n w K ids D q F
  have hXy := Q'.eqv_trans _ _ _ (weighted_symm (n+n) W _ _)
    (mixed_pair n w K ids D f Q)
  have hXY := upper_pair n w K ids hnd hids D Q F hD hQ hF
  have hcommon : H n (polyMul D (polyMul F Q)) ≈ H n (polyMul D (polyMul Q F)) :=
    haar_of_coeff ((RatPolyCoeffEqv.mul_comm F Q).mul_left D)
  have hdiff := weighted_difference (n+n) W q f (liftBoundary n Q) (liftBoundary n F)
  have hs : weightedPair (n+n) W (centered n w K ids q) (centered n w K ids f) ≈
      (H n (polyMul D (productMap n w K ids (polyMul q f)))-H n (polyMul D (polyMul Q F)))-
        (H n (polyMul D (polyMul Q F))-H n (polyMul D (polyMul Q F))) :=
    Q'.eqv_trans _ _ _ hdiff
      (Q'.add_eqv_congr' (Q'.add_eqv_congr' hxy
        (Q'.neg_eqv_congr _ _ (Q'.eqv_trans _ _ _ hxY hcommon)))
        (Q'.neg_eqv_congr _ _ (Q'.add_eqv_congr' hXy (Q'.neg_eqv_congr _ _ hXY))))
  have hreorder : RatPolyCoeffEqv
      (polyMul D (polyAdd (productMap n w K ids (polyMul q f)) (polySmul (-1) (polyMul Q F))))
      (polyAdd (polyMul D (productMap n w K ids (polyMul q f)))
        (polySmul (-1) (polyMul D (polyMul Q F)))) :=
    (RatPolyCoeffEqv.mul_add_right _ _ _).trans
      ((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.polyMul_smul_right (-1) D _))
  exact Q'.eqv_trans _ _ _ hs
    (Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
      (.add (.add (.var 0) (.neg (.var 1))) (.neg (.add (.var 1) (.neg (.var 1)))))
      (.add (.var 0) (.neg (.var 1))) (by decide)
      (fun
        | 0 => H n (polyMul D (productMap n w K ids (polyMul q f)))
        | _ => H n (polyMul D (polyMul Q F))))
      (Q'.eqv_symm (Q'.eqv_trans _ _ _ (haar_of_coeff hreorder) (haar_sub n _ _))))

/-- The retained ORIGINAL loss is the norm of the actual conditionally
centered source under the original joint kernel. No output independence. -/
theorem fullSourceLoss_retained_nonnegative (n : Nat) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat) (hhead : headCutoff w ≤ K)
    (ids : List Nat) (hnd : ids.Nodup) (hids : ∀ i, i ∈ ids → i < n)
    (q : RatPoly) (hq : SupportedQuaternionBlocks n q)
    (R : RatPoly) (hR : SupportedQuaternionBlocks n R) (PR : Certificate n R) :
    (0 : Q') ≤ H n (polyMul R (fullSourceLoss n w K ids q)) := by
  let W := polyMul (productHeat n w K ids) (liftBoundary n R)
  have PW : Certificate (n+n) W :=
    (productHeatCertificate n hw0 hw1 K hhead ids hids).mul (lift_certificate n PR)
  have hn := PW.square_insertion_nonnegative _ (centered_supported n w K ids hids hq)
  exact Q'.le_trans' _ _ _ hn
    (Q'.le_of_eqv (centered_pair n w K ids hnd hids R q q hR hq hq))

private theorem qpow_rg (w : Q') : ∀ k, qpow w k = RGTransport.qpow w k
  | 0 => rfl
  | k+1 => congrArg (fun z : Q' => z*w) (qpow_rg w k)

private theorem square_rate_difference_nonnegative {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (P : Nat) :
    (0 : Q') ≤ qpow w (3*P)*qpow w (3*P)-qpow w (8*P) := by
  have h6 : (0 : Q') ≤ qpow w (6*P) := by
    rw [qpow_rg]; exact RGTransport.qpow_nonneg w (Q'.le_of_lt hw0) _
  have h2 : qpow w (2*P) ≤ (1 : Q') := by
    rw [qpow_rg]; exact HeatKernelGap.qpow_le_one (Q'.le_of_lt hw0) (Q'.le_of_lt hw1) _
  have hh := Q'.mul_nonneg _ _ h6 (Q'.sub_nonneg_of_le h2)
  have h33 : qpow w (6*P) ≈ qpow w (3*P)*qpow w (3*P) := by
    rw [show 6*P = 3*P+3*P by omega]
    exact qpow_add w (3*P) (3*P)
  have h62 : qpow w (8*P) ≈ qpow w (6*P)*qpow w (2*P) := by
    rw [show 8*P = 6*P+2*P by omega]
    exact qpow_add w (6*P) (2*P)
  have he : qpow w (6*P)*(1-qpow w (2*P)) ≈
      qpow w (3*P)*qpow w (3*P)-qpow w (8*P) :=
    Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
      (.mul (.var 0) (.add (.const 1) (.neg (.var 1))))
      (.add (.var 0) (.neg (.mul (.var 0) (.var 1)))) (by decide)
      (fun | 0 => qpow w (6*P) | _ => qpow w (2*P)))
      (Q'.add_eqv_congr' h33 (Q'.neg_eqv_congr _ _ (Q'.eqv_symm h62)))
  exact Q'.le_trans' _ _ _ hh (Q'.le_of_eqv he)

private theorem insert_test (n : Nat) (W R b x y : RatPoly) :
    weightedPair (n+n) (polyMul W (liftBoundary n R)) x (polyMul (liftBoundary n b) y) ≈
      weightedPair (n+n) (polyMul W (liftBoundary n (polyMul R b))) x y := by
  unfold weightedPair
  rw [lift_product]
  exact haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.mul (.var 0) (.mul (.var 1) (.var 2))) (.mul (.var 3) (.var 4)))
    (.mul (.mul (.var 0) (.var 2)) (.mul (.var 3) (.mul (.var 4) (.var 1))))
    (by decide) (fun | 0 => x | 1 => liftBoundary n b | 2 => y | 3 => W | _ => liftBoundary n R))

private theorem insert_test_square (n : Nat) (W R b y : RatPoly) :
    weightedPair (n+n) (polyMul W (liftBoundary n R))
      (polyMul (liftBoundary n b) y) (polyMul (liftBoundary n b) y) ≈
      weightedPair (n+n) (polyMul W (liftBoundary n (polyMul R (polyMul b b)))) y y := by
  unfold weightedPair
  rw [lift_product, lift_product]
  exact haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1))) (.mul (.var 2) (.var 3)))
    (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.mul (.var 3) (.mul (.var 0) (.var 0)))))
    (by decide) (fun | 0 => liftBoundary n b | 1 => y | 2 => W | _ => liftBoundary n R))

private theorem neg_one_mul (a : Q') : (-1)*a ≈ -a :=
  Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 a) (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv a))

private theorem covariance_variance_coeff (D f : RatPoly) (a d : Q') :
    RatPolyCoeffEqv
      (polyMul D (polyAdd
        (polyAdd polyOne (polySmul d (polyAdd (polyMul f f) (polySmul (-1) polyOne))))
        (polySmul (-1) (polyMul (polySmul a f) (polySmul a f)))))
      (polyAdd (polySmul (1-d) D) (polySmul (d-a*a) (polyMul D (polyMul f f)))) := by
  let ff := polyMul f f
  have hd : RatPolyCoeffEqv (polySmul d (polyAdd ff (polySmul (-1) polyOne)))
      (polyAdd (polySmul d ff) (polySmul (-d) polyOne)) :=
    (RatPolyCoeffEqv.smul_add d ff _).trans
      ((RatPolyCoeffEqv.refl _).add
        ((RatPolyCoeffEqv.smul_assoc d (-1) polyOne).trans
          (RatPolyCoeffEqv.smul_coefficient
            (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv d (-1)) (neg_one_mul d)) polyOne)))
  have ha : RatPolyCoeffEqv (polySmul (-1) (polyMul (polySmul a f) (polySmul a f)))
      (polySmul (-(a*a)) ff) :=
    ((((RatPolyCoeffEqv.polyMul_smul_left a f (polySmul a f)).trans
      ((RatPolyCoeffEqv.polyMul_smul_right a f f).smul a)).trans
      (RatPolyCoeffEqv.smul_assoc a a ff)).smul (-1)).trans
        ((RatPolyCoeffEqv.smul_assoc (-1) (a*a) ff).trans
          (RatPolyCoeffEqv.smul_coefficient (neg_one_mul (a*a)) ff))
  have hr : RatPolyCoeffEqv
      (polyAdd (polyAdd polyOne (polyAdd (polySmul d ff) (polySmul (-d) polyOne)))
        (polySmul (-(a*a)) ff))
      (polyAdd (polyAdd polyOne (polySmul (-d) polyOne))
        (polyAdd (polySmul d ff) (polySmul (-(a*a)) ff))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.add (.add (.var 0) (.add (.var 1) (.var 2))) (.var 3))
      (.add (.add (.var 0) (.var 2)) (.add (.var 1) (.var 3))) (by decide)
      (fun
        | 0 => polyOne
        | 1 => polySmul d ff
        | 2 => polySmul (-d) polyOne
        | _ => polySmul (-(a*a)) ff)
  have hcollect : RatPolyCoeffEqv
      (polyAdd (polyAdd polyOne (polySmul (-d) polyOne))
        (polyAdd (polySmul d ff) (polySmul (-(a*a)) ff)))
      (polyAdd (polySmul (1-d) polyOne) (polySmul (d-a*a) ff)) :=
    (((RatPolyCoeffEqv.one_smul polyOne).symm.add (RatPolyCoeffEqv.refl _)).trans
      (RatPolyCoeffEqv.add_smul_same 1 (-d) polyOne)).add
        (RatPolyCoeffEqv.add_smul_same d (-(a*a)) ff)
  have hc := (((RatPolyCoeffEqv.refl polyOne).add hd).add ha).trans (hr.trans hcollect)
  exact (hc.mul_left D).trans
    ((RatPolyCoeffEqv.mul_add_right D _ _).trans
      (((RatPolyCoeffEqv.polyMul_smul_right (1-d) D polyOne).trans
        ((RatPolyCoeffEqv.mul_one D).smul (1-d))).add
        (RatPolyCoeffEqv.polyMul_smul_right (d-a*a) D ff)))

/-- Sharp derivative-free signed full-word pairing estimate. The coefficient
is the spin-TWO rate, not a squared spin-one rate or perimeter-square cost.
The entire source and original retained action stay in the actual integrals. -/
theorem fundamental_word_covariance_pair_retained_bound (n : Nat) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat)
    (hhead : headCutoff w ≤ K) (htwo : 2 ≤ K)
    (ids : List Nat) (hnd : ids.Nodup) (hids : ∀ i, i ∈ ids → i < n)
    (block : OrientedBF4Link → Nat) (es : List OrientedBF4Link)
    (hword : (es.map block).Nodup) (hselected : ∀ e, e ∈ es → block e ∈ ids)
    (q : RatPoly) (hq : SupportedQuaternionBlocks n q)
    (R : RatPoly) (hR : SupportedQuaternionBlocks n R) (PR : Certificate n R)
    (b : RatPoly) (hb : SupportedQuaternionBlocks n b) :
    let f := characterPolynomial (wordAt block es).scalar 1
    let C := multiplicationDefect n w K ids q f (qpow w (3*es.length))
    H n (polyMul R (polyMul b C))*H n (polyMul R (polyMul b C)) ≤
      H n (polyMul R (fullSourceLoss n w K ids q)) *
        (wordCovarianceRate w es.length * H n (polyMul R (polyMul b b)) -
          (qpow w (3*es.length)*qpow w (3*es.length)-qpow w (8*es.length)) *
            H n (polyMul R (polyMul (polyMul b b) (polyMul f f)))) := by
  dsimp only
  let f := characterPolynomial (wordAt block es).scalar 1
  let Q := productMap n w K ids q
  let F := productMap n w K ids f
  let a := qpow w (3*es.length)
  let d := qpow w (8*es.length)
  let W := polyMul (productHeat n w K ids) (liftBoundary n R)
  let u := centered n w K ids q
  let v := polyMul (liftBoundary n b) (centered n w K ids f)
  have hfs := word_supported n block es (fun e he => hids _ (hselected e he))
  have hf : SupportedQuaternionBlocks n f := character_supported hfs.scalar 1
  have hQ := productMap_supported n w K ids hids hq
  have hF := productMap_supported n w K ids hids hf
  have hu := centered_supported n w K ids hids hq
  have hv := supported_polyMul (lift_supported hb n) (centered_supported n w K ids hids hf)
  have PW : Certificate (n+n) W :=
    (productHeatCertificate n hw0 hw1 K hhead ids hids).mul (lift_certificate n PR)
  have hcs := weighted_cauchySchwarz (n+n) W u v PW hu hv
  have huv0 := Q'.eqv_trans _ _ _ (insert_test n (productHeat n w K ids) R b u _)
    (centered_pair n w K ids hnd hids (polyMul R b) q f (supported_polyMul hR hb) hq hf)
  have himage := productMap_fundamental_word n w K (by omega : 1 ≤ K) block es
    ids hnd hids hword hselected
  have hmul := (SupportedHaarEqv.refl n Q).mul himage hF hQ
  have he : RatPolyCoeffEqv (polySmul (-1) (polyMul Q (polySmul a f)))
      (polySmul (-a) (polyMul Q f)) :=
    ((RatPolyCoeffEqv.polyMul_smul_right a Q f).smul (-1)).trans
      ((RatPolyCoeffEqv.smul_assoc (-1) a _).trans
        (RatPolyCoeffEqv.smul_coefficient (Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 a)
          (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv a))) _))
  have hcov := (SupportedHaarEqv.refl n (productMap n w K ids (polyMul q f))).add
    ((hmul.smul (-1)).trans (SupportedHaarEqv.of_carrier (RatPolyCoeffEqv.haarCarrier he)))
  have huv : weightedPair (n+n) W u v ≈ H n (polyMul R (polyMul b
      (multiplicationDefect n w K ids q f a))) :=
    Q'.eqv_trans _ _ _ huv0
      (Q'.eqv_trans _ _ _ (hcov (polyMul R b) (supported_polyMul hR hb))
        (haar_of_coeff (RatPolyCoeffEqv.mul_assoc R b _)))
  have huu := centered_pair n w K ids hnd hids R q q hR hq hq
  let D := polyMul R (polyMul b b)
  have hD := supported_polyMul hR (supported_polyMul hb hb)
  have hvv0 := Q'.eqv_trans _ _ _ (insert_test_square n (productHeat n w K ids) R b _)
    (centered_pair n w K ids hnd hids D f f hD hf hf)
  have hF2 := himage.mul himage hF (polySmul_supported hf a)
  have hsquare := productMap_fundamental_square n w K htwo block es ids hnd hids hword hselected
  have hpin := hsquare.add (hF2.smul (-1))
  have hquad := hpin D hD
  have hnorm : weightedPair (n+n) W v v ≈
      wordCovarianceRate w es.length*H n D + (d-a*a)*H n (polyMul D (polyMul f f)) := by
    have heq : RatPolyCoeffEqv
        (polyMul D (polyAdd (polyAdd polyOne (polySmul d (characterPolynomial (wordAt block es).scalar 2)))
          (polySmul (-1) (polyMul (polySmul a f) (polySmul a f)))))
        (polyAdd (polySmul (1-d) D) (polySmul (d-a*a) (polyMul D (polyMul f f)))) := by
      have hchar : RatPolyCoeffEqv (characterPolynomial (wordAt block es).scalar 2)
          (polyAdd (polyMul f f) (polySmul (-1) polyOne)) := RatPolyCoeffEqv.refl _
      refine ((RatPolyCoeffEqv.refl D).mul
        ((((RatPolyCoeffEqv.refl polyOne).add (hchar.smul d)).add (RatPolyCoeffEqv.refl _)))).trans ?_
      exact covariance_variance_coeff D f a d
    exact Q'.eqv_trans _ _ _ hvv0
      (Q'.eqv_trans _ _ _ hquad
        (Q'.eqv_trans _ _ _ (haar_of_coeff heq)
          (Q'.eqv_trans _ _ _ (quaternionHaar_append n _ _)
            (Q'.add_eqv_congr' (quaternionHaar_polySmul n (1-d) D)
              (quaternionHaar_polySmul n (d-a*a) _)))))
  have hmoment : H n (polyMul D (polyMul f f)) ≈
      H n (polyMul R (polyMul (polyMul b b) (polyMul f f))) :=
    haar_of_coeff (RatPolyCoeffEqv.mul_assoc R (polyMul b b) (polyMul f f))
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ huv)
      (Q'.mul_eqv_congr_left _ _ _ huv)))
    (Q'.le_trans' _ _ _ hcs (Q'.le_of_eqv (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ huu)
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _
        (Q'.eqv_trans _ _ _ hnorm (Q'.add_eqv_congr' (Q'.eqv_refl _)
          (Q'.mul_eqv_congr_left _ _ _ hmoment))))
        (poly_identity_of_normal_eq
          (.mul (.var 0) (.add (.mul (.var 1) (.var 2))
            (.mul (.add (.var 4) (.neg (.mul (.var 3) (.var 3)))) (.var 5))))
          (.mul (.var 0) (.add (.mul (.var 1) (.var 2))
            (.neg (.mul (.add (.mul (.var 3) (.var 3)) (.neg (.var 4))) (.var 5)))))
          (by decide)
          (fun
            | 0 => H n (polyMul R (fullSourceLoss n w K ids q))
            | 1 => wordCovarianceRate w es.length
            | 2 => H n D
            | 3 => a
            | 4 => d
            | _ => H n (polyMul R (polyMul (polyMul b b) (polyMul f f)))))))))

/-- Coarse corollary only: discards the proved nonpositive spin-two correction.
The retained theorem above is stronger and makes no radial-concentration claim. -/
theorem fundamental_word_covariance_pair_bound (n : Nat) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat)
    (hhead : headCutoff w ≤ K) (htwo : 2 ≤ K)
    (ids : List Nat) (hnd : ids.Nodup) (hids : ∀ i, i ∈ ids → i < n)
    (block : OrientedBF4Link → Nat) (es : List OrientedBF4Link)
    (hword : (es.map block).Nodup) (hselected : ∀ e, e ∈ es → block e ∈ ids)
    (q : RatPoly) (hq : SupportedQuaternionBlocks n q)
    (R : RatPoly) (hR : SupportedQuaternionBlocks n R) (PR : Certificate n R)
    (b : RatPoly) (hb : SupportedQuaternionBlocks n b) :
    let f := characterPolynomial (wordAt block es).scalar 1
    let C := multiplicationDefect n w K ids q f (qpow w (3*es.length))
    H n (polyMul R (polyMul b C))*H n (polyMul R (polyMul b C)) ≤
      wordCovarianceRate w es.length *
        (H n (polyMul R (polyMul b b))*H n (polyMul R (fullSourceLoss n w K ids q))) := by
  dsimp only
  let f := characterPolynomial (wordAt block es).scalar 1
  have hf : SupportedQuaternionBlocks n f :=
    character_supported (word_supported n block es (fun e he => hids _ (hselected e he))).scalar 1
  have hnon : (0 : Q') ≤ H n (polyMul R (polyMul (polyMul b b) (polyMul f f))) :=
    (PR.mul ((Certificate.square b hb).mul (Certificate.square f hf))).haar_nonnegative
  have hpaid := Q'.mul_nonneg _ _
    (square_rate_difference_nonnegative hw0 hw1 es.length) hnon
  have hbracket : wordCovarianceRate w es.length * H n (polyMul R (polyMul b b)) -
      (qpow w (3*es.length)*qpow w (3*es.length)-qpow w (8*es.length)) *
        H n (polyMul R (polyMul (polyMul b b) (polyMul f f))) ≤
      wordCovarianceRate w es.length * H n (polyMul R (polyMul b b)) := by
    have hn := Q'.le_trans' _ _ _ (Q'.neg_le_neg hpaid)
      (Q'.le_of_eqv (by decide : -(0 : Q') ≈ 0))
    exact Q'.le_trans' _ _ _ (Q'.add_le_add_left _ _ _ hn)
      (Q'.le_of_eqv (Q'.eqv_of_eq (Q'.add_zero' _)))
  have hL := fullSourceLoss_retained_nonnegative n hw0 hw1 K hhead ids hnd hids q hq R hR PR
  have hbound := fundamental_word_covariance_pair_retained_bound n hw0 hw1 K hhead htwo
    ids hnd hids block es hword hselected q hq R hR PR b hb
  exact Q'.le_trans' _ _ _ hbound
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hbracket hL)
      (Q'.le_of_eqv (poly_identity_of_normal_eq
        (.mul (.var 0) (.mul (.var 1) (.var 2)))
        (.mul (.var 1) (.mul (.var 2) (.var 0))) (by decide)
        (fun
          | 0 => H n (polyMul R (fullSourceLoss n w K ids q))
          | 1 => wordCovarianceRate w es.length
          | _ => H n (polyMul R (polyMul b b))))))

end YMGap.Continuum.SU2QuaternionProductHeatWilsonCovariance

#print axioms YMGap.Continuum.SU2QuaternionProductHeatWilsonCovariance.fullSourceLoss
#print axioms YMGap.Continuum.SU2QuaternionProductHeatWilsonCovariance.wordCovarianceRate
#print axioms YMGap.Continuum.SU2QuaternionProductHeatWilsonCovariance.fullSourceLoss_retained_nonnegative
#print axioms YMGap.Continuum.SU2QuaternionProductHeatWilsonCovariance.fundamental_word_covariance_pair_retained_bound
#print axioms YMGap.Continuum.SU2QuaternionProductHeatWilsonCovariance.fundamental_word_covariance_pair_bound
