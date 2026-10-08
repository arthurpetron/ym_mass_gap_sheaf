/-
# Torus RP (g7): `Θ∘τ_x ≡ τ_{−x}∘Θ` on link observables (polynomial level)

`theta_tau_obs`: for `e : Obs` on torus links, `Θ (τ_x (eval e)) ≡PE τ_y (Θ (eval e))` with `y = 2M − x % 2M`.
Both sides are `≡ evalI (imgR ∘ shv x) e`. Uses `tau_lv`, `like_img` (via `sub_evalI`), and `refl_shift`.
**OPEN**: the `PtSup` extension (via `obsOf`) and the correlator identity `rpB (τ_x F) (τ_y F) ≈ G(x+y)`.
-/

import YMGap.Continuum.SU2TorusTauTK
import YMGap.Continuum.SU2TorusLinksTimeShift
import YMGap.Continuum.SU2TorusReflShift
import YMGap.Continuum.SU2TorusRPSym

namespace YMGap.Continuum.SU2TorusThetaTau

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.Z4TorusGeometry
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2TorusMultiLinkPolyGibbs (linkVar)
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.SU2HaarAlgebra (PE pe_refl pe_trans pe_symm)
open YMGap.Continuum.SU2TorusRPSubst (QPE qsub)
open YMGap.Continuum.SU2TorusRPObs (Obs evalI eval OnLinks thetaT)
open YMGap.Continuum.SU2TorusRPMatch (imgR)
open YMGap.Continuum.SU2TorusTau (tau)
open YMGap.Continuum.SU2TimeShift (shv)

variable {M : Nat} (hM : 1 ≤ M) (x : Nat)

theorem tau_imgR (ℓ : Z4Link) (h : ℓ ∈ torusLinks (2 * M)) :
    QPE (torusLinks (2 * M)).length (qsub (tau (2 * M) (2 * M - x % (2 * M)) (by omega)) (imgR (torusLinks (2 * M)) M ℓ))
      (imgR (torusLinks (2 * M)) M (shv (2 * M) x ℓ)) := by
  have hr := YMGap.Continuum.SU2TorusRPObs.tl_cl hM ℓ h
  have hl := YMGap.Continuum.SU2TorusTauVar.tau_lv (2 * M) (2 * M - x % (2 * M)) (by omega) _ hr
  rw [← YMGap.Continuum.SU2TorusReflShift.refl_shift M x hM ℓ (YMGap.Continuum.SU2TorusRPObs.tl_box ℓ h)] at hl
  unfold imgR
  show QPE _ (qsub _ (if YMGap.Continuum.SU2TorusRPThetaTK.isT ℓ.2 then _ else _))
    (if YMGap.Continuum.SU2TorusRPThetaTK.isT ℓ.2 then _ else _)
  cases YMGap.Continuum.SU2TorusRPThetaTK.isT ℓ.2
  · exact hl
  · exact YMGap.Continuum.SU2TorusRPSubst.qpe_trans
      (YMGap.Continuum.SU2TorusRPSubst.qconj_sub (YMGap.Continuum.SU2TorusTauTK.tau_ringSub _ _ _) _)
      (YMGap.Continuum.SU2TorusRPSubst.qpe_conj hl)

theorem theta_tau_obs (e : Obs) (he : OnLinks (· ∈ torusLinks (2 * M)) e) :
    PE (torusLinks (2 * M)).length (thetaT hM (tau (2 * M) x (by omega) (eval (torusLinks (2 * M)) e)))
      (tau (2 * M) (2 * M - x % (2 * M)) (by omega) (thetaT hM (eval (torusLinks (2 * M)) e))) := by
  have hN : 0 < 2 * M := by omega
  let n := (torusLinks (2 * M)).length
  have hT := YMGap.Continuum.SU2TorusRPMatch.thetaT_like hM
  have he' : OnLinks (fun ℓ => ℓ ∈ torusLinks (2 * M) ∧ shv (2 * M) x ℓ ∈ torusLinks (2 * M)) e :=
    YMGap.Continuum.SU2TorusRPHW.onLinks_mono (fun ℓ h => ⟨h, YMGap.Continuum.SU2TorusLinksTimeShift.shv_mem_torusLinks hN x ℓ h⟩) e he
  -- left: τ_x (eval e) ≡ evalI (lv ∘ shv x) e
  have l1 : PE n (tau (2 * M) x hN (eval (torusLinks (2 * M)) e)) (evalI (fun ℓ => linkVar (torusLinks (2 * M)) (shv (2 * M) x ℓ)) e) :=
    YMGap.Continuum.SU2TorusRPObs.sub_evalI (YMGap.Continuum.SU2TorusTauTK.tau_ringSub _ _ hN) _ _ _
      (fun ℓ h => YMGap.Continuum.SU2TorusTauVar.tau_lv _ _ hN ℓ h) e he
  have sA : YMGap.Continuum.SU2TorusRPCore.Sup n (tau (2 * M) x hN (eval (torusLinks (2 * M)) e)) :=
    fun s hs => YMGap.Continuum.SU2QuaternionHaarCertificateReindex.reindex_supported _ _ s hs
  have sB : YMGap.Continuum.SU2TorusRPCore.Sup n (evalI (fun ℓ => linkVar (torusLinks (2 * M)) (shv (2 * M) x ℓ)) e) :=
    YMGap.Continuum.SU2TorusRPMatch.sup_evalI _ _ (fun ℓ h => YMGap.Continuum.SU2TorusRPHW.supQ_lv _ _ h.2 rfl) e he'
  have l2 : PE n (thetaT hM (evalI (fun ℓ => linkVar (torusLinks (2 * M)) (shv (2 * M) x ℓ)) e))
      (evalI (fun ℓ => imgR (torusLinks (2 * M)) M (shv (2 * M) x ℓ)) e) :=
    YMGap.Continuum.SU2TorusRPObs.sub_evalI hT.ring _ _ _
      (fun ℓ h => YMGap.Continuum.SU2TorusRPMatch.like_img hT _ h.2) e he'
  have L := pe_trans _ (YMGap.Continuum.SU2TorusRPSym.thetaT_pe hM sA sB l1) l2
  -- right: τ_y (Θ (eval e)) ≡ evalI (imgR ∘ shv x) e
  have r1 := YMGap.Continuum.SU2TorusRPMatch.like_obs hT e he
  have sC := YMGap.Continuum.SU2TorusRPSym.thetaT_sup hM (eval (torusLinks (2 * M)) e)
  have sD : YMGap.Continuum.SU2TorusRPCore.Sup n (evalI (imgR (torusLinks (2 * M)) M) e) :=
    YMGap.Continuum.SU2TorusRPMatch.sup_evalI _ _
      (fun ℓ h => YMGap.Continuum.SU2TorusRPHW.supQ_imgR _ ℓ (YMGap.Continuum.SU2TorusRPObs.tl_cl hM ℓ h) rfl) e he
  have congr : PE n (tau (2 * M) (2 * M - x % (2 * M)) hN (thetaT hM (eval (torusLinks (2 * M)) e)))
      (tau (2 * M) (2 * M - x % (2 * M)) hN (evalI (imgR (torusLinks (2 * M)) M) e)) :=
    YMGap.Continuum.SU2TorusRPReindexCongr.reindex_peCongrOn _
      (fun s hs => YMGap.Continuum.SU2QuaternionHaarCertificateReindex.reindex_supported _ _ s hs)
      (fun s hs => YMGap.Continuum.SU2QuaternionHaarCertificateReindex.reindex_supported _ _ s hs)
      (YMGap.Continuum.SU2TorusRPReindexCongr.reindex_peCongrOn _ sC sD r1)
  have r2 := YMGap.Continuum.SU2TorusRPObs.sub_evalI (YMGap.Continuum.SU2TorusTauTK.tau_ringSub _ (2 * M - x % (2 * M)) hN)
    _ _ _ (fun ℓ h => tau_imgR hM x ℓ h) e he
  exact pe_trans _ L (pe_symm _ (pe_trans _ congr r2))

end YMGap.Continuum.SU2TorusThetaTau

#print axioms YMGap.Continuum.SU2TorusThetaTau.theta_tau_obs
