/-
# Torus RP (g8): the correlator identity on link observables

`corr_obs`: for `e : Obs` on torus links, with `F = eval e` and `τ_t` the time shift on `torusLinks (2M)`,

  `rpB (τ_x F) (τ_z F) ≈ rpB F (τ_{x+z} F)`   (truncated T_K weight, fixed K; every `β`).

Writing `G n := rpB F (τ_n F)`, this is `⟨Θ τ_x F · τ_z F⟩ ≈ G(x+z)`. The proof chains `theta_tau_obs`, the shift
composition `τ_y τ_{x+z} F ≡ τ_z F` (`y = 2M − x % 2M`), and `shift_inv`. **OPEN**: the `PtSup` extension, and
`PtSup` of `τ_x F` (needed before `torus_cs_poly` can be applied to `(τ_a F, τ_{a+1} F)`).
-/

import YMGap.Continuum.SU2TorusThetaTau

namespace YMGap.Continuum.SU2TorusCorrelator

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.Z4TorusGeometry
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2TorusMultiLinkPolyGibbs (linkVar)
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.SU2HaarAlgebra (PE pe_refl pe_trans pe_symm pe_haar)
open YMGap.Continuum.SU2TorusRPSubst (QPE qsub pe_mul2)
open YMGap.Continuum.SU2TorusRPObs (Obs evalI eval OnLinks thetaT)
open YMGap.Continuum.SU2TorusTau (tau)
open YMGap.Continuum.SU2TimeShift (shv vs)
open YMGap.Continuum.SU2HaarL1Activity (prodPoly)
open YMGap.Continuum.SU2TorusRPCSShape (rpB)

theorem evalI_ext {P : Z4Link → Prop} {f g : Z4Link → PolyQuaternion} (h : ∀ ℓ, P ℓ → f ℓ = g ℓ) :
    ∀ e : Obs, OnLinks P e → evalI f e = evalI g e
  | .const _, _ => rfl
  | .var ℓ k, hl => by show YMGap.Continuum.SU2TorusRPObs.comp _ k = _; rw [h ℓ hl]; rfl
  | .add a b, hl => by show polyAdd _ _ = polyAdd _ _; rw [evalI_ext h a hl.1, evalI_ext h b hl.2]
  | .mul a b, hl => by show polyMul _ _ = polyMul _ _; rw [evalI_ext h a hl.1, evalI_ext h b hl.2]
  | .neg a, hl => by show polyNeg _ = polyNeg _; rw [evalI_ext h a hl]

theorem shv_shv (N x z : Nat) (hN : 0 < N) (ℓ : Z4Link) :
    shv N (N - x % N) (shv N (x + z) ℓ) = shv N z ℓ := by
  obtain ⟨⟨a, b, c, d⟩, e⟩ := ℓ
  show ((((a + (x + z)) % N + (N - x % N)) % N, b, c, d), e) = (((a + z) % N, b, c, d), e)
  have hx := Nat.mod_lt x hN
  have hd := Nat.div_add_mod x N
  rw [Nat.mod_add_mod, show a + (x + z) + (N - x % N) = (a + z) + N * (x / N + 1) by
    rw [Nat.mul_add, Nat.mul_one]; omega, Nat.add_mul_mod_self_left]

theorem tau_congr (N t : Nat) (hN : 0 < N) {X Y : RatPoly} (hX : YMGap.Continuum.SU2TorusRPCore.Sup (torusLinks N).length X)
    (hY : YMGap.Continuum.SU2TorusRPCore.Sup (torusLinks N).length Y) (h : PE (torusLinks N).length X Y) :
    PE (torusLinks N).length (tau N t hN X) (tau N t hN Y) :=
  YMGap.Continuum.SU2TorusRPReindexCongr.reindex_peCongrOn _
    (fun s hs => YMGap.Continuum.SU2QuaternionHaarCertificateReindex.reindex_supported _ _ s hs)
    (fun s hs => YMGap.Continuum.SU2QuaternionHaarCertificateReindex.reindex_supported _ _ s hs)
    (YMGap.Continuum.SU2TorusRPReindexCongr.reindex_peCongrOn _ hX hY h)

variable {M : Nat} (hM : 1 ≤ M)

include hM in
theorem tau_obs (t : Nat) (e : Obs) (he : OnLinks (· ∈ torusLinks (2 * M)) e) :
    PE (torusLinks (2 * M)).length (tau (2 * M) t (by omega) (eval (torusLinks (2 * M)) e))
      (evalI (fun ℓ => linkVar (torusLinks (2 * M)) (shv (2 * M) t ℓ)) e) :=
  YMGap.Continuum.SU2TorusRPObs.sub_evalI (YMGap.Continuum.SU2TorusTauTK.tau_ringSub _ _ _) _ _ _
    (fun ℓ h => YMGap.Continuum.SU2TorusTauVar.tau_lv _ _ _ ℓ h) e he

include hM in
theorem tau_tau_obs (x z : Nat) (e : Obs) (he : OnLinks (· ∈ torusLinks (2 * M)) e) :
    PE (torusLinks (2 * M)).length
      (tau (2 * M) (2 * M - x % (2 * M)) (by omega) (tau (2 * M) (x + z) (by omega) (eval (torusLinks (2 * M)) e)))
      (tau (2 * M) z (by omega) (eval (torusLinks (2 * M)) e)) := by
  have hN : 0 < 2 * M := by omega
  have he' : OnLinks (fun ℓ => ℓ ∈ torusLinks (2 * M) ∧ shv (2 * M) (x + z) ℓ ∈ torusLinks (2 * M)) e :=
    YMGap.Continuum.SU2TorusRPHW.onLinks_mono (fun ℓ h => ⟨h, YMGap.Continuum.SU2TorusThetaTau.shv_mem hM _ ℓ h⟩) e he
  have s1 : YMGap.Continuum.SU2TorusRPCore.Sup (torusLinks (2 * M)).length (evalI (fun ℓ => linkVar (torusLinks (2 * M)) (shv (2 * M) (x + z) ℓ)) e) :=
    YMGap.Continuum.SU2TorusRPMatch.sup_evalI _ _ (fun ℓ h => YMGap.Continuum.SU2TorusRPHW.supQ_lv _ _ h.2 rfl) e he'
  have c := tau_congr (2 * M) (2 * M - x % (2 * M)) hN
    (fun s hs => YMGap.Continuum.SU2QuaternionHaarCertificateReindex.reindex_supported _ _ s hs) s1 (tau_obs hM (x + z) e he)
  have r := YMGap.Continuum.SU2TorusRPObs.sub_evalI (YMGap.Continuum.SU2TorusTauTK.tau_ringSub _ (2 * M - x % (2 * M)) hN)
    (fun ℓ => ℓ ∈ torusLinks (2 * M) ∧ shv (2 * M) (x + z) ℓ ∈ torusLinks (2 * M)) _ _
    (fun ℓ h => YMGap.Continuum.SU2TorusTauVar.tau_lv _ _ hN _ h.2) e he'
  refine pe_trans _ c (pe_trans _ r ?_)
  rw [evalI_ext (P := (· ∈ torusLinks (2 * M))) (g := fun ℓ => linkVar (torusLinks (2 * M)) (shv (2 * M) z ℓ))
    (fun ℓ _ => by rw [shv_shv _ _ _ hN]) e he]
  exact pe_symm _ (tau_obs hM z e he)

/-- **Correlator identity (link observables):** `rpB (τ_x F) (τ_z F) ≈ rpB F (τ_{x+z} F)`. -/
theorem corr_obs (β : Q') (K x z : Nat) (e : Obs) (he : OnLinks (· ∈ torusLinks (2 * M)) e) :
    (rpB hM β K (tau (2 * M) x (by omega) (eval (torusLinks (2 * M)) e)) (tau (2 * M) z (by omega) (eval (torusLinks (2 * M)) e))).eqv
      (rpB hM β K (eval (torusLinks (2 * M)) e) (tau (2 * M) (x + z) (by omega) (eval (torusLinks (2 * M)) e))) := by
  have hN : 0 < 2 * M := by omega
  have H1 := YMGap.Continuum.SU2TorusThetaTau.theta_tau_obs hM x e he
  have H2 := tau_tau_obs hM x z e he
  have sPi : YMGap.Continuum.SU2TorusRPCore.Sup (torusLinks (2 * M)).length (prodPoly (YMGap.Continuum.SU2WilsonPolymerIdentity.TK
      (torusLinks (2 * M)) (2 * M) β K) (torusPlaquettes (2 * M))) :=
    YMGap.Continuum.SU2TorusRPSupTK.sup_prodTK _ _ β K _ fun p hp =>
      YMGap.Continuum.SU2TorusRPSwap.plaqIdx_lt _ _ p (YMGap.Continuum.SU2TorusRPTorusZ.plaqL_mem hM p hp)
  have sT : YMGap.Continuum.SU2TorusRPCore.Sup (torusLinks (2 * M)).length (tau (2 * M) (x + z) hN (eval (torusLinks (2 * M)) e)) :=
    fun s hs => YMGap.Continuum.SU2QuaternionHaarCertificateReindex.reindex_supported _ _ s hs
  have hP := YMGap.Continuum.SU2TorusRPCore.sup_mul (YMGap.Continuum.SU2TorusRPCore.sup_mul
    (YMGap.Continuum.SU2TorusRPSym.thetaT_sup hM (eval (torusLinks (2 * M)) e)) sT) sPi
  have hPE := pe_mul2 (torusLinks (2 * M)).length (pe_mul2 _ H1 (pe_symm _ H2)) (pe_refl _
    (prodPoly (YMGap.Continuum.SU2WilsonPolymerIdentity.TK (torusLinks (2 * M)) (2 * M) β K) (torusPlaquettes (2 * M))))
  exact Q'.eqv_trans _ _ _ (pe_haar _ hPE)
    (YMGap.Continuum.SU2TorusTauTK.shift_inv (2 * M) (2 * M - x % (2 * M)) hN β K _ _ hP)

end YMGap.Continuum.SU2TorusCorrelator

#print axioms YMGap.Continuum.SU2TorusCorrelator.tau_tau_obs
#print axioms YMGap.Continuum.SU2TorusCorrelator.corr_obs
