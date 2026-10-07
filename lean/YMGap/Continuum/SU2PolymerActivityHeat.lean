/-
# Heat-kernel instance of the multi-plaquette activity bound

ADDITIVE.  Connects `SU2PolymerActivityBound` to the Prover's centred factor
`fPoly w links N p M = Σ_{s=1}^{M} coeffW w s · χ_s(U_p)` (`SU2HaarL1Activity`) and to the
true activity `z γ = quaternionHaar n (prodPoly (fun p => fPoly w links N p M) γ)` of
`SU2PolymerIdentity.polyPartition_eq_Xi`.

* `fPoly_eq_charSum` : `fPoly p ≅ charSum links N p (heatList w M)`.
* `bSum_heatList`    : `bSum (heatList w M) ≈ charEnv w M` (for `0 ≤ w`).
* `heatList_pos`     : every coefficient in the list has `0 < |c|` (for `0 < w`), so no filtering is needed.
* `z_abs_le`         : `−charEnv w M ^ |γ| ≤ z γ ≤ charEnv w M ^ |γ|`.
-/

import YMGap.Continuum.SU2PolymerActivityBound
import YMGap.Continuum.SU2HaarL1Activity

namespace YMGap.Continuum.SU2PolymerActivityHeat

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.SU2QuaternionGlobalFaceRatPolySupport
open YMGap.Continuum.SU2CharacterSquareIdentity
open YMGap.Continuum.SU2CharacterCauchySchwarz (haar_pull haar_cs_pos)
open YMGap.Continuum.SU2PlaqWeightedCharacterBound
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricHaarMehlerProjection (quaternionHaar)
open YMGap.Continuum.RingNormaliser (PolyExpr poly_identity_of_normal_eq)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2CharacterHaarBound (H haar_coeff)
open YMGap.Continuum.SU2PolymerActivityBound
open YMGap.Continuum.SU2TorusMultiLinkPolyGibbs (coeffW plaqCharacter multiLinkHaar)
open YMGap.Continuum.SU2HaarL1Activity (fPoly prodPoly qpow_eqv)
open YMGap.Continuum.HeatKernelPolymerActivityR1 (charEnv envTerm)

local instance : Mul PolyExpr := ⟨PolyExpr.mul⟩

private theorem abs_nn {c : Q'} (hc : (0 : Q') ≤ c) : Q'.abs c = c := if_pos hc

/-- `[(coeffW w M, M), …, (coeffW w 1, 1)]`: the centred heat-kernel character list (s = 0 dropped). -/
def heatList (w : Q') : Nat → List (Q' × Nat)
  | 0 => []
  | M + 1 => (coeffW w (M + 1), M + 1) :: heatList w M

theorem fPoly_eq_charSum (w : Q') (links : List Z4Link) (N : Nat) (p : Z4Plaq) :
    ∀ M, RatPolyCoeffEqv (fPoly w links N p M) (charSum links N p (heatList w M))
  | 0 => RatPolyCoeffEqv.refl _
  | M + 1 => (RatPolyCoeffEqv.add (fPoly_eq_charSum w links N p M) (RatPolyCoeffEqv.refl _)).trans
      (RatPolyCoeffEqv.add_comm _ _)

private theorem ofNat_mul_eqv' (a b : Nat) : (Q'.ofNat a * Q'.ofNat b).eqv (Q'.ofNat (a * b)) := by
  show (Q'.ofNat a * Q'.ofNat b).num * ((Q'.ofNat (a * b)).den : Int) =
    (Q'.ofNat (a * b)).num * ((Q'.ofNat a * Q'.ofNat b).den : Int)
  rw [Q'.mul_den_cast]
  show ((Int.ofNat a) * (Int.ofNat b)) * 1 = (Int.ofNat (a * b)) * (1 * 1)
  simp only [Int.ofNat_eq_natCast, Int.natCast_mul]
  omega

theorem term_eqv {w : Q'} (hw : (0 : Q') ≤ w) (s : Nat) :
    (Q'.abs (coeffW w s) * Q'.ofInt ((s : Int) + 1)).eqv (envTerm w s) := by
  rw [abs_nn (YMGap.Continuum.BondMovingStep.coeffW_nonneg hw s)]
  show (Q'.ofNat (s + 1) * YMGap.Continuum.RGTransport.qpow w (s * (s + 2)) * Q'.ofNat (s + 1)).eqv
    (Q'.ofNat ((s + 1) * (s + 1)) * w ^ (s * (s + 2)))
  let V := PolyExpr.var
  refine Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq (V 0 * V 1 * V 0) (V 0 * V 0 * V 1) (by decide)
    (fun | 0 => Q'.ofNat (s + 1) | _ => YMGap.Continuum.RGTransport.qpow w (s * (s + 2)))) ?_
  exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (ofNat_mul_eqv' _ _))
    (Q'.mul_eqv_congr_left _ _ _ (qpow_eqv w _))

theorem bSum_heatList {w : Q'} (hw : (0 : Q') ≤ w) : ∀ M, (bSum (heatList w M)).eqv (charEnv w M)
  | 0 => Q'.eqv_refl _
  | M + 1 => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (term_eqv hw (M + 1)) (bSum_heatList hw M)) (Q'.add_comm_eqv _ _)

private theorem qpow_pos' {w : Q'} (hw : (0 : Q') < w) : ∀ n, (0 : Q') < YMGap.Continuum.RGTransport.qpow w n
  | 0 => show (0 : Q') < 1 by decide
  | n + 1 => Q'.mul_pos (qpow_pos' hw n) hw

private theorem ofNat_succ_pos (s : Nat) : (0 : Q') < Q'.ofNat (s + 1) := by
  show (0 : Int) * ((0 + 1 : Nat) : Int) < (Int.ofNat (s + 1)) * ((0 + 1 : Nat) : Int)
  simp only [Int.ofNat_eq_natCast]
  omega

theorem heatList_pos {w : Q'} (hw : (0 : Q') < w) : ∀ M, ∀ t ∈ heatList w M, (0 : Q') < Q'.abs t.1
  | 0, _, ht => nomatch ht
  | M + 1, _, .head _ => by
      have hc : (0 : Q') < coeffW w (M + 1) := Q'.mul_pos (ofNat_succ_pos (M + 1)) (qpow_pos' hw _)
      rw [abs_nn (Q'.le_of_lt hc)]; exact hc
  | M + 1, t, .tail _ h => heatList_pos hw M t h

/-- The polymer as an `SU2PolymerActivityBound` input list. -/
def heatPolymer (w : Q') (M : Nat) : List Z4Plaq → List (Z4Plaq × List (Q' × Nat))
  | [] => []
  | p :: ps => (p, heatList w M) :: heatPolymer w M ps

theorem heatPolymer_ok {w : Q'} (hw : (0 : Q') < w) (M : Nat) (links : List Z4Link) (N : Nat) :
    ∀ γ : List Z4Plaq, (∀ p ∈ γ, YMGap.Continuum.SU2PlaqWordHolonomy.LinksCover links N p) →
      PolymerOK links N (heatPolymer w M γ)
  | [], _ => fun _ hq => nomatch hq
  | p :: ps, hc => fun q hq => by
    cases hq with
    | head => exact ⟨hc p (.head _), heatList_pos hw M⟩
    | tail _ h => exact heatPolymer_ok hw M links N ps (fun r hr => hc r (.tail _ hr)) q h

theorem prodPoly_eqv (w : Q') (M : Nat) (links : List Z4Link) (N : Nat) :
    ∀ γ, RatPolyCoeffEqv (prodPoly (fun p => fPoly w links N p M) γ)
      (polyProd links N (heatPolymer w M γ))
  | [] => RatPolyCoeffEqv.refl _
  | p :: ps => RatPolyCoeffEqv.mul (fPoly_eq_charSum w links N p M) (prodPoly_eqv w M links N ps)

theorem bProd_heatPolymer {w : Q'} (hw : (0 : Q') ≤ w) (M : Nat) :
    ∀ γ : List Z4Plaq, (bProd (heatPolymer w M γ)).eqv (charEnv w M ^ γ.length)
  | [] => Q'.eqv_refl _
  | _ :: ps => Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (bSum_heatList hw M))
      (Q'.mul_eqv_congr_left _ _ _ (bProd_heatPolymer hw M ps))

/-- **Heat-kernel activity bound** in the gas's own terms: for the true activity
`z γ = quaternionHaar n (Π_{p∈γ} fPoly p)` (`n = links.length`, equal to
`(multiLinkHaar n).h` by definition), `−charEnv w M ^ |γ| ≤ z γ ≤ charEnv w M ^ |γ|`. -/
theorem z_abs_le {w : Q'} (hw : (0 : Q') < w) (M : Nat) (links : List Z4Link) (N : Nat)
    (γ : List Z4Plaq) (hc : ∀ p ∈ γ, YMGap.Continuum.SU2PlaqWordHolonomy.LinksCover links N p) :
    let z := quaternionHaar links.length (prodPoly (fun p => fPoly w links N p M) γ)
    (-(charEnv w M ^ γ.length)) ≤ z ∧ z ≤ charEnv w M ^ γ.length := by
  intro z
  have hab := polymer_activity_abs_le (heatPolymer w M γ) (heatPolymer_ok hw M links N γ hc)
  have hz : z.eqv (H links.length (polyProd links N (heatPolymer w M γ))) :=
    haar_coeff (prodPoly_eqv w M links N γ) _
  have hB := bProd_heatPolymer (Q'.le_of_lt hw) M γ
  refine ⟨Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.neg_eqv_congr _ _ (Q'.eqv_symm hB)))
      (Q'.le_trans' _ _ _ hab.1 (Q'.le_of_eqv (Q'.eqv_symm hz))), ?_⟩
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hz) (Q'.le_trans' _ _ _ hab.2 (Q'.le_of_eqv hB))

end YMGap.Continuum.SU2PolymerActivityHeat

#print axioms YMGap.Continuum.SU2PolymerActivityHeat.fPoly_eq_charSum
#print axioms YMGap.Continuum.SU2PolymerActivityHeat.bSum_heatList
#print axioms YMGap.Continuum.SU2PolymerActivityHeat.z_abs_le
