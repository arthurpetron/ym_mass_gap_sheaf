/-
# The retained source budget approaches the norm of the actual finite seed

For the original odd marginal nu, M=P_i nu, the actual finite polynomial
inverse J, and P_i tau=0, put q=M*J*tau-P_i(nu*J*tau). Two conditional
orthogonality identities give
  H[(M*J)*tau^2] - H[nu*q^2] = H[(1-nu*M*J)*tau*q].
The existing inverse interval and Haar Cauchy--Schwarz therefore bound this
nonnegative difference by rho^k*H[tau^2]/ell. All parameters in rho and ell
are the original finite regulators. No inverse function or limit is used.
This identifies the retained budget with the actual norm up to a computable
finite-degree error; it does not bound either quantity uniformly in volume.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialActualSeedReciprocalNorm
import YMGap.Continuum.QuaternionHaarPositiveFloorCancellation
import YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz
import YMGap.Constructive.CubeRoot

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialActualSeedBudgetError

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (PolyExpr poly_identity_of_normal_eq)
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual
  (marginalWeight marginalPair)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualSeedWindow (denominator)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualSeed
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualSeedReciprocalNorm
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHaarBlockProjection
open YMGap.Continuum.SU2QuaternionWeightedBlockCentering (weightedResidual)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv
attribute [local irreducible] baseLinks

private theorem mul_congr {a b c d : Q'} (h : a ≈ b) (h' : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h)
    (Q'.mul_eqv_congr_left _ _ _ h')

private theorem haar_neg (blocks : Nat) : ∀ p : RatPoly,
    quaternionHaar blocks (polyNeg p) ≈ -(quaternionHaar blocks p)
  | [] => by change Q'.eqv (0 : Q') (-0); decide
  | t::rest => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.neg_mul_eqv t.2 (quaternionHaarMono blocks t.1))
        (haar_neg blocks rest)) (Q'.eqv_symm (Q'.neg_add_eqv_split _ _))

private theorem haar_sub (blocks : Nat) (p q : RatPoly) :
    quaternionHaar blocks (polyAdd p (polyNeg q)) ≈
      quaternionHaar blocks p + -(quaternionHaar blocks q) :=
  Q'.eqv_trans _ _ _ (quaternionHaar_append blocks _ _)
    (Q'.add_eqv_congr' (Q'.eqv_refl _) (haar_neg blocks q))

private theorem centered_project_pair_zero (blocks i : Nat) (hi : i < blocks)
    (p s : RatPoly) (hc : RatPolyCoeffEqv (project i p) polyZero) :
    quaternionHaar blocks (polyMul p (project i s)) ≈ 0 :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (project_selfAdjoint blocks i hi p s))
    (haar_of_coeff ((hc.mul_right s).trans (RatPolyCoeffEqv.mul_zero_left s)))

/-- Squaring reflects an upper bound on the nonnegative cone, including zero. -/
private theorem square_reflect {a b : Q'} (hb : (0 : Q') ≤ b)
    (h : a*a ≤ b*b) : a ≤ b := by
  show a.num * (b.den : Int) ≤ b.num * (a.den : Int)
  apply Int.not_lt.mp
  intro hba
  have hba' : b < a := hba
  have ha : (0 : Q') < a := Q'.lt_of_le_of_lt hb hba'
  have h1 : b*b ≤ a*b :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ (Q'.le_of_lt hba') hb
  have h2 : a*b < a*a := Q'.mul_lt_mul_of_pos_left ha hba'
  have h3 : b*b < a*a := Q'.lt_of_le_of_lt h1 h2
  exact (Int.not_lt.mpr h) h3

private theorem cancel_floor {a c ell : Q'} (hell : (0 : Q') < ell)
    (h : ell*a ≤ c) : a ≤ Q'.recipPos ell hell*c := by
  have hi : ell*(Q'.recipPos ell hell*c) ≈ c :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ c (Q'.mul_recipPos_eqv ell hell))
        (Q'.one_mul_eqv c))
  exact Q'.le_of_mul_le_mul_left
    (Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.eqv_symm hi))) hell

private theorem haar_cauchySchwarz {blocks : Nat} {p q : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) (hq : SupportedQuaternionBlocks blocks q) :
    quaternionHaar blocks (polyMul p q) * quaternionHaar blocks (polyMul p q) ≤
      quaternionHaar blocks (polyMul p p) * quaternionHaar blocks (polyMul q q) := by
  have pin (u v : RatPoly) : weightedPair blocks polyOne u v ≈
      quaternionHaar blocks (polyMul u v) := haar_of_coeff (RatPolyCoeffEqv.mul_one _)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (mul_congr (pin p q) (pin p q))))
    (Q'.le_trans' _ _ _ (weighted_cauchySchwarz blocks polyOne p q (.one blocks) hp hq)
      (Q'.le_of_eqv (mul_congr (pin p p) (pin q q))))

private theorem add_neg_zero (B : Q') : B + -(0 : Q') ≈ B :=
  poly_identity_of_normal_eq (.add (.var 0) (.neg (.const 0))) (.var 0)
    (by decide) (fun _ => B)

private theorem sub_add_cancel (B C : Q') : (B + -C) + C ≈ B :=
  poly_identity_of_normal_eq (.add (.add (.var 0) (.neg (.var 1))) (.var 1)) (.var 0)
    (by decide) (fun | 0 => B | _ => C)

private theorem scalar_error_bound {ell r S Q V delta : Q'}
    (hell : (0 : Q') < ell) (hr : (0 : Q') ≤ r)
    (hS : (0 : Q') ≤ S) (hV : (0 : Q') ≤ V)
    (hQ : (ell*ell)*Q ≤ S) (hVbound : V ≤ (r*r)*S)
    (hcs : delta*delta ≤ V*Q) :
    delta ≤ r*(Q'.recipPos ell hell*S) := by
  have hsquare : (ell*delta)*(ell*delta) ≤ (r*S)*(r*S) := by
    have h1 : (ell*ell)*(delta*delta) ≤ (ell*ell)*(V*Q) :=
      Q'.mul_le_mul_of_nonneg_left _ _ _ hcs
        (Q'.mul_nonneg _ _ (Q'.le_of_lt hell) (Q'.le_of_lt hell))
    have h2 : (ell*ell)*(V*Q) ≈ V*((ell*ell)*Q) :=
      poly_identity_of_normal_eq
        (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 2)))
        (.mul (.var 1) (.mul (.mul (.var 0) (.var 0)) (.var 2)))
        (by decide) (fun | 0 => ell | 1 => V | _ => Q)
    have h3 : V*((ell*ell)*Q) ≤ V*S := Q'.mul_le_mul_of_nonneg_left _ _ _ hQ hV
    have h4 : V*S ≤ ((r*r)*S)*S := Q'.mul_le_mul_of_nonneg_right _ _ _ hVbound hS
    have hleft : (ell*delta)*(ell*delta) ≈ (ell*ell)*(delta*delta) :=
      poly_identity_of_normal_eq
        (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))
        (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1)))
        (by decide) (fun | 0 => ell | _ => delta)
    have hright : ((r*r)*S)*S ≈ (r*S)*(r*S) :=
      poly_identity_of_normal_eq
        (.mul (.mul (.mul (.var 0) (.var 0)) (.var 1)) (.var 1))
        (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))
        (by decide) (fun | 0 => r | _ => S)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
      (Q'.le_trans' _ _ _ h1 (Q'.le_trans' _ _ _ (Q'.le_of_eqv h2)
        (Q'.le_trans' _ _ _ h3 (Q'.le_trans' _ _ _ h4 (Q'.le_of_eqv hright)))))
  have hd : delta ≤ Q'.recipPos ell hell*(r*S) :=
    cancel_floor hell (square_reflect (Q'.mul_nonneg _ _ hr hS) hsquare)
  have hreorder : Q'.recipPos ell hell*(r*S) ≈ r*(Q'.recipPos ell hell*S) :=
    poly_identity_of_normal_eq
      (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
      (fun | 0 => Q'.recipPos ell hell | 1 => r | _ => S)
  exact Q'.le_trans' _ _ _ hd (Q'.le_of_eqv hreorder)

private theorem square_product_reorder (tau e : RatPoly) :
    RatPolyCoeffEqv (polyMul (polyMul tau tau) (polyMul e e))
      (polyMul (polyMul e tau) (polyMul e tau)) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1)))
    (.mul (.mul (.var 1) (.var 0)) (.mul (.var 1) (.var 0))) (by decide)
    (fun | 0 => tau | _ => e)

private theorem residual_pairing_pin (blocks i : Nat) (hi : i < blocks) (a J tau : RatPoly)
    (hc : RatPolyCoeffEqv (project i tau) polyZero) :
    quaternionHaar blocks (polyMul (polyMul (project i a) J) (polyMul tau tau)) ≈
      quaternionHaar blocks (polyMul tau (weightedResidual i a (polyMul J tau))) := by
  let m := project i a
  let c := project i (polyMul a (polyMul J tau))
  have hz := centered_project_pair_zero blocks i hi tau (polyMul a (polyMul J tau)) hc
  have hp : RatPolyCoeffEqv (polyMul tau (weightedResidual i a (polyMul J tau)))
      (polyAdd (polyMul (polyMul m J) (polyMul tau tau)) (polyNeg (polyMul tau c))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 2) (.add (.mul (.var 0) (.mul (.var 1) (.var 2))) (.neg (.var 3))))
      (.add (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 2)))
        (.neg (.mul (.var 2) (.var 3)))) (by decide)
      (fun | 0 => m | 1 => J | 2 => tau | _ => c)
  exact Q'.eqv_symm (Q'.eqv_trans _ _ _ (haar_of_coeff hp)
    (Q'.eqv_trans _ _ _ (haar_sub blocks _ _)
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (Q'.eqv_refl _) (Q'.neg_eqv_congr _ _ hz))
        (add_neg_zero _))))

private theorem residual_error_pin (blocks i : Nat) (hi : i < blocks) (a J tau : RatPoly)
    (hc : RatPolyCoeffEqv (project i tau) polyZero) :
    let q := weightedResidual i a (polyMul J tau)
    let e := polyAdd polyOne (polyNeg (polyMul (polyMul a (project i a)) J))
    quaternionHaar blocks (polyMul (polyMul (project i a) J) (polyMul tau tau)) +
      -(quaternionHaar blocks (polyMul a (polyMul q q))) ≈
      quaternionHaar blocks (polyMul (polyMul e tau) q) := by
  let m := project i a
  let c := project i (polyMul a (polyMul J tau))
  let q := weightedResidual i a (polyMul J tau)
  let e := polyAdd polyOne (polyNeg (polyMul (polyMul a m) J))
  let qe : PolyExpr := .add (.mul (.var 1) (.mul (.var 2) (.var 3))) (.neg (.var 4))
  have hz := centered_project_pair_zero blocks i hi (polyMul a q)
    (polyMul a (polyMul J tau))
    (SU2QuaternionWeightedBlockCentering.project_weightedResidual_zero i a (polyMul J tau))
  have hp : RatPolyCoeffEqv
      (polyAdd (polyMul tau q) (polyNeg (polyMul a (polyMul q q))))
      (polyAdd (polyMul (polyMul e tau) q) (polyMul (polyMul a q) c)) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.var 3) qe) (.neg (.mul (.var 0) (.mul qe qe))))
      (.add (.mul (.mul
        (.add (.const 1) (.neg (.mul (.mul (.var 0) (.var 1)) (.var 2)))) (.var 3)) qe)
        (.mul (.mul (.var 0) qe) (.var 4))) (by decide)
      (fun | 0 => a | 1 => m | 2 => J | 3 => tau | _ => c)
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (residual_pairing_pin blocks i hi a J tau hc) (Q'.eqv_refl _))
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm (haar_sub blocks _ _))
      (Q'.eqv_trans _ _ _ (haar_of_coeff hp)
        (Q'.eqv_trans _ _ _ (quaternionHaar_append blocks _ _)
          (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.eqv_refl _) hz)
            (Q'.eqv_of_eq (Q'.add_zero' _))))))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat)

/-- The retained source is the actual mixed pairing with tau at every degree. -/
theorem budget_pairing_pin (i : Nat) (hi : i < N width) (k : Nat) (tau : RatPoly)
    (hc : RatPolyCoeffEqv (project i tau) polyZero) :
    quaternionHaar (N width) (polyMul
      (polyMul (project i (marginalWeight w K width n)) (inverse hw0 hw1 K width hK n i k))
      (polyMul tau tau)) ≈
      quaternionHaar (N width) (polyMul tau (test hw0 hw1 K width hK n i k tau)) :=
  residual_pairing_pin (N width) i hi (marginalWeight w K width n)
    (inverse hw0 hw1 K width hK n i k) tau hc

/-- Both conditional orthogonalities keep the same actual inverse residual. -/
theorem budget_error_pin (i : Nat) (hi : i < N width) (k : Nat) (tau : RatPoly)
    (hc : RatPolyCoeffEqv (project i tau) polyZero) :
    quaternionHaar (N width) (polyMul
      (polyMul (project i (marginalWeight w K width n)) (inverse hw0 hw1 K width hK n i k))
      (polyMul tau tau)) + -(marginalPair w K width n
        (test hw0 hw1 K width hK n i k tau) (test hw0 hw1 K width hK n i k tau)) ≈
      quaternionHaar (N width) (polyMul
        (polyMul (inverseError hw0 hw1 K width hK n i k) tau)
        (test hw0 hw1 K width hK n i k tau)) :=
  residual_error_pin (N width) i hi (marginalWeight w K width n)
    (inverse hw0 hw1 K width hK n i k) tau hc

/-- Explicit finite-regulator error prefactor; no polynomial presentation cap. -/
def errorPrefactor (tau : RatPoly) : Q' :=
  Q'.recipPos (lower w K width n) (lower_positive hw0 hw1 K width hK n) *
    quaternionHaar (N width) (polyMul tau tau)

theorem errorPrefactor_nonnegative {tau : RatPoly}
    (ht : SupportedQuaternionBlocks (N width) tau) :
    (0 : Q') ≤ errorPrefactor hw0 hw1 K width hK n tau :=
  Q'.mul_nonneg _ _ (Q'.le_of_lt (Q'.recipPos_pos _ _)) (Certificate.square tau ht).haar_nonnegative

/-- The finite retained source budget differs from the actual norm by a
geometric error. Zero sources and zero geometric factors are included. -/
theorem budget_error_le_geometric (i : Nat) (hi : i < N width) (k : Nat)
    {tau : RatPoly} (ht : SupportedQuaternionBlocks (N width) tau)
    (hc : RatPolyCoeffEqv (project i tau) polyZero) :
    quaternionHaar (N width) (polyMul
      (polyMul (project i (marginalWeight w K width n)) (inverse hw0 hw1 K width hK n i k))
      (polyMul tau tau)) + -(marginalPair w K width n
        (test hw0 hw1 K width hK n i k tau) (test hw0 hw1 K width hK n i k tau)) ≤
      (rate hw0 hw1 K width hK n)^k * errorPrefactor hw0 hw1 K width hK n tau := by
  let ell := lower w K width n
  let r := (rate hw0 hw1 K width hK n)^k
  let S := quaternionHaar (N width) (polyMul tau tau)
  let q := test hw0 hw1 K width hK n i k tau
  let e := inverseError hw0 hw1 K width hK n i k
  let v := polyMul e tau
  let Q := quaternionHaar (N width) (polyMul q q)
  let V := quaternionHaar (N width) (polyMul v v)
  let delta := quaternionHaar (N width) (polyMul v q)
  have hell := lower_positive hw0 hw1 K width hK n
  have hq := test_supported hw0 hw1 K width hK n i k ht
  have I := inverseErrorInterval hw0 hw1 K width hK n i hi k
  have hv := supported_polyMul I.support ht
  have hS : (0 : Q') ≤ S := (Certificate.square tau ht).haar_nonnegative
  have hV : (0 : Q') ≤ V := (Certificate.square v hv).haar_nonnegative
  have hfloor : ell*Q ≤ marginalPair w K width n q q :=
    Q'.le_trans' _ _ _ (QuaternionHaarPositiveFloorCancellation.floor_insertion
      (.square q hq) (lowerCertificate hw0 hw1 K width hK n))
      (Q'.le_of_eqv (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _)))
  have hQ : (ell*ell)*Q ≤ S :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_assoc_eqv _ _ _))
      (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hfloor (Q'.le_of_lt hell))
        (BF4ExactSlabFixedSpatialActualSeedNorm.test_norm_le hw0 hw1 K width hK n i hi k ht))
  have hVbound : V ≤ (r*r)*S := by
    have hp : quaternionHaar (N width) (polyMul (polyMul tau tau) (polyMul e e)) ≈ V :=
      haar_of_coeff (square_product_reorder tau e)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm hp))
      (Q'.le_trans' _ _ _ (Q'.le_abs_self _)
        ((I.mul I).weighted_haar_bound (.square tau ht)))
  have hcs : delta*delta ≤ V*Q := haar_cauchySchwarz hv hq
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (budget_error_pin hw0 hw1 K width hK n i hi k tau hc))
    (scalar_error_bound hell I.nonnegative hS hV hQ hVbound hcs)

/-- Direct form for the actual finite-family sum consumer. -/
theorem budget_le_norm_add_geometric (i : Nat) (hi : i < N width) (k : Nat)
    {tau : RatPoly} (ht : SupportedQuaternionBlocks (N width) tau)
    (hc : RatPolyCoeffEqv (project i tau) polyZero) :
    quaternionHaar (N width) (polyMul
      (polyMul (project i (marginalWeight w K width n)) (inverse hw0 hw1 K width hK n i k))
      (polyMul tau tau)) ≤ marginalPair w K width n
        (test hw0 hw1 K width hK n i k tau) (test hw0 hw1 K width hK n i k tau) +
      (rate hw0 hw1 K width hK n)^k * errorPrefactor hw0 hw1 K width hK n tau := by
  let B := quaternionHaar (N width) (polyMul
    (polyMul (project i (marginalWeight w K width n)) (inverse hw0 hw1 K width hK n i k))
    (polyMul tau tau))
  let C := marginalPair w K width n
    (test hw0 hw1 K width hK n i k tau) (test hw0 hw1 K width hK n i k tau)
  have h := Q'.add_le_add_right _ _ C
    (budget_error_le_geometric hw0 hw1 K width hK n i hi k ht hc)
  have he : (B + -C) + C ≈ B := sub_add_cancel B C
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm he))
    (Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.add_comm_eqv _ _)))

end YMGap.Continuum.BF4ExactSlabFixedSpatialActualSeedBudgetError

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialActualSeedBudgetError.budget_pairing_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialActualSeedBudgetError.budget_error_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialActualSeedBudgetError.errorPrefactor
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialActualSeedBudgetError.errorPrefactor_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialActualSeedBudgetError.budget_error_le_geometric
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialActualSeedBudgetError.budget_le_norm_add_geometric
