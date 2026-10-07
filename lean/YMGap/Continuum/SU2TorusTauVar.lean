/-
# Torus RP (g4): `τ_t` on link variables

`tau_lv`: `qsub τ_t (linkVar ℓ) ≡ linkVar (shv t ℓ)` for `ℓ ∈ torusLinks N`. It composes `reindex_linkVar` for
`σ_0` and `σ_t` with `reindex_peCongrOn` and `rl_comp`. **OPEN**: `τ_t (Π T_K) ≡ Π T_K` and `Θ∘τ_x ≡ τ_{−x}∘Θ`.
-/

import YMGap.Continuum.SU2TorusTau
import YMGap.Continuum.SU2TorusRPHW

namespace YMGap.Continuum.SU2TorusTauVar

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.Z4TorusGeometry
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2TorusMultiLinkPolyGibbs (linkVar)
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.SU2TorusRPSubst (QPE qsub)
open YMGap.Continuum.SU2TorusTimeRefl (rl rl_mem rl_inv rl_comp sigma)
open YMGap.Continuum.SU2TorusTau (tau)

theorem qpe_reindex {N : Nat} (σ : YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection.QuaternionBlockInvolution N)
    {q r : PolyQuaternion} (hq : YMGap.Continuum.SU2TorusRPKernel.SupQ N q) (hr : YMGap.Continuum.SU2TorusRPKernel.SupQ N r)
    (h : QPE N q r) :
    QPE N (qsub (YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection.reindexQuaternionPolynomial σ) q)
      (qsub (YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection.reindexQuaternionPolynomial σ) r) :=
  ⟨YMGap.Continuum.SU2TorusRPReindexCongr.reindex_peCongrOn σ hq.1 hr.1 h.s,
   YMGap.Continuum.SU2TorusRPReindexCongr.reindex_peCongrOn σ hq.2.1 hr.2.1 h.i,
   YMGap.Continuum.SU2TorusRPReindexCongr.reindex_peCongrOn σ hq.2.2.1 hr.2.2.1 h.j,
   YMGap.Continuum.SU2TorusRPReindexCongr.reindex_peCongrOn σ hq.2.2.2 hr.2.2.2 h.k⟩

theorem supQ_reindex {N : Nat} (σ : YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection.QuaternionBlockInvolution N)
    (q : PolyQuaternion) :
    YMGap.Continuum.SU2TorusRPKernel.SupQ N
      (qsub (YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection.reindexQuaternionPolynomial σ) q) :=
  ⟨fun s hs => YMGap.Continuum.SU2QuaternionHaarCertificateReindex.reindex_supported σ _ s hs,
   fun s hs => YMGap.Continuum.SU2QuaternionHaarCertificateReindex.reindex_supported σ _ s hs,
   fun s hs => YMGap.Continuum.SU2QuaternionHaarCertificateReindex.reindex_supported σ _ s hs,
   fun s hs => YMGap.Continuum.SU2QuaternionHaarCertificateReindex.reindex_supported σ _ s hs⟩

theorem tau_lv (N t : Nat) (hN : 0 < N) (ℓ : Z4Link) (h : ℓ ∈ torusLinks N) :
    QPE (torusLinks N).length (qsub (tau N t hN) (linkVar (torusLinks N) ℓ))
      (linkVar (torusLinks N) (YMGap.Continuum.SU2TimeShift.shv N t ℓ)) := by
  have h0 := YMGap.Continuum.SU2TorusRPThetaPoly.reindex_linkVar (torusLinks N) (rl N 0) (torusLinks_nodup N)
    (rl_mem N 0 hN) (rl_inv N 0 hN) h
  have h1 := YMGap.Continuum.SU2TorusRPThetaPoly.reindex_linkVar (torusLinks N) (rl N t) (torusLinks_nodup N)
    (rl_mem N t hN) (rl_inv N t hN) (rl_mem N 0 hN ℓ h)
  rw [rl_comp N t hN ℓ h] at h1
  exact YMGap.Continuum.SU2TorusRPSubst.qpe_trans
    (qpe_reindex (sigma N t hN) (supQ_reindex _ _)
      (YMGap.Continuum.SU2TorusRPHW.supQ_lv _ _ (rl_mem N 0 hN ℓ h) rfl) h0) h1

end YMGap.Continuum.SU2TorusTauVar

#print axioms YMGap.Continuum.SU2TorusTauVar.tau_lv
