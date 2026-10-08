/-
# Torus RP, K → ∞ step 3: `RPKCauchy` for the torus `T_K` form (strong coupling)

**PROVED** (`rpK_cauchy`). For `0 ≤ β` and `2·(β·256) ≤ 1`, and ANY polynomials `F G`:

  `|rpB_{K+j} F G − rpB_K F G| ≤ l1(Θ F · G) · eb 2 (2 (256 β)^{K+1}) |torusPlaquettes (2M)|`   for all `K, j`.

This is `RPKCauchy hM β F G r`. The rate `r K` is explicit and independent of `j`, and decays like `(256β)^{K+1}`
at fixed volume. It is NOT volume-uniform: `eb 2 δ n` grows like `n·2^n·δ`.

Combined with `SU2TorusRPKLimit.rp_closed` / `cs_closed`, any rationals that the `rpB_K` approximate at this rate
satisfy RP / Cauchy–Schwarz up to `2 r K`. **No limit object is defined.** The untruncated Wilson weight is not
constructed here; "passing to the limit" means exactly the closed-inequality statements in `SU2TorusRPKLimit`.
-/

import YMGap.Continuum.SU2TorusRPKProd

namespace YMGap.Continuum.SU2TorusRPKCauchy

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.Z4TorusGeometry
open YMGap.Continuum.ClusterCount4DProgress (Z4Plaq)
open YMGap.Continuum.SU2HaarL1Activity (l1 l1_nonneg l1_add_le l1_smul)
open YMGap.Continuum.SU2WilsonActivity (wilsonA)
open YMGap.Continuum.SU2TorusRPKTail (wtail wilsonPoly_add tsum_le l1_wtail_le l1_U_plaq)
open YMGap.Continuum.SU2TorusRPKProd (eb haar_diff)
open YMGap.Continuum.SU2TorusRPCSShape (rpB)
open YMGap.Continuum.SU2TorusRPKLimit (RPKCauchy)

/-- Plaquette scalar `x_p`. -/
def xp (M : Nat) (p : Z4Plaq) : RatPoly :=
  (YMGap.Continuum.SU2TorusMultiLinkPolyGibbs.plaqWord (torusLinks (2 * M)) (2 * M) p).scalar

variable {M : Nat} (hM : 1 ≤ M) {β : Q'} (hβ : (0 : Q') ≤ β) (h2 : 2 * (β * Q'.ofNat 256) ≤ 1)

local notation "TKf" => YMGap.Continuum.SU2WilsonPolymerIdentity.TK (torusLinks (2 * M)) (2 * M) β

theorem tk_add (K j : Nat) (p : Z4Plaq) :
    TKf (K + j) p = polyAdd (TKf K p) (wtail (xp M p) (wilsonA β) K j) :=
  wilsonPoly_add _ _ K j

include hβ h2 in
theorem l1_tail (K j : Nat) (p : Z4Plaq) :
    l1 (wtail (xp M p) (wilsonA β) K j) ≤ 2 * (β * Q'.ofNat 256) ^ (K + 1) :=
  Q'.le_trans' _ _ _ (l1_wtail_le _ hβ (by decide) (l1_U_plaq _ _ p) K j)
    (tsum_le (Q'.mul_nonneg _ _ hβ (by decide)) h2 K j)

include hβ h2 in
theorem l1_tk (K : Nat) (p : Z4Plaq) : l1 (TKf K p) ≤ 2 := by
  have e : TKf K p = TKf (0 + K) p := by rw [Nat.zero_add]
  rw [e, tk_add]
  refine Q'.le_trans' _ _ _ (l1_add_le _ _) ?_
  have h0 : l1 (TKf 0 p) ≤ 1 := by
    show l1 (polySmul 1 polyOne) ≤ 1
    decide
  have ht : l1 (wtail (xp M p) (wilsonA β) 0 K) ≤ 1 :=
    Q'.le_trans' _ _ _ (l1_tail hβ h2 0 K p)
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_one_eqv _))) h2)
  exact Q'.le_trans' _ _ _ (YMGap.Constructive.ExpNeg.add_le_add2 h0 ht) (by decide)

include hβ h2 in
/-- **Uniform-in-`j` Cauchy bound in `K` for the torus RP form (PROVED, strong coupling, fixed volume).** -/
theorem rpK_cauchy (F G : RatPoly) :
    RPKCauchy hM β F G (fun K => l1 (polyMul (YMGap.Continuum.SU2TorusRPObs.thetaT hM F) G) *
      eb 2 (2 * (β * Q'.ofNat 256) ^ (K + 1)) (torusPlaquettes (2 * M)).length) := fun K j => by
  have hd : (0 : Q') ≤ 2 * (β * Q'.ofNat 256) ^ (K + 1) :=
    Q'.mul_nonneg _ _ (by decide) (Q'.pow_nonneg _ (Q'.mul_nonneg _ _ hβ (by decide)) _)
  have hprod : YMGap.Continuum.SU2HaarL1Activity.prodPoly (TKf (K + j)) (torusPlaquettes (2 * M)) =
      YMGap.Continuum.SU2HaarL1Activity.prodPoly (fun q => polyAdd (TKf K q) (wtail (xp M q) (wilsonA β) K j))
        (torusPlaquettes (2 * M)) := by
    rw [show TKf (K + j) = fun q => polyAdd (TKf K q) (wtail (xp M q) (wilsonA β) K j) from funext (tk_add K j)]
  show Q'.abs (YMGap.Continuum.BF4GeometricHaarMehlerProjection.quaternionHaar _
      (polyMul (polyMul (YMGap.Continuum.SU2TorusRPObs.thetaT hM F) G)
        (YMGap.Continuum.SU2HaarL1Activity.prodPoly (TKf (K + j)) (torusPlaquettes (2 * M)))) + -_) ≤ _
  rw [hprod]
  exact haar_diff _ _ _ _ (by decide) hd (l1_tk hβ h2 K)
    (fun q => by rw [← tk_add]; exact l1_tk hβ h2 (K + j) q) (l1_tail hβ h2 K j) _

end YMGap.Continuum.SU2TorusRPKCauchy

#print axioms YMGap.Continuum.SU2TorusRPKCauchy.rpK_cauchy
