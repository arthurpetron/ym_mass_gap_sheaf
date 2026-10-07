/-
# Torus RP (g5): `τ_t` is a ring substitution and shifts the `T_K` plaquette weight

* `tau_ringSub`: `τ_t` is a `RingSub`. `mul`/`add`/`smul`/`neg` hold literally; `one` holds up to padding.
* `tau_TK`: `τ_t (T_K p) ≡PE T_K (shv t p)` for `p` in the box. This uses the Prover's `tk_shift` (read-only) and
  `tau_lv`.

**OPEN**: `τ_t (Π_p T_K) ≡ Π_p T_K` (from `prodPoly_sub`, `tau_TK` and `tp_shift_perm`), `Θ∘τ_x ≡ τ_{−x}∘Θ`, and the
correlator identity.
-/

import YMGap.Continuum.SU2TorusTauVar

namespace YMGap.Continuum.SU2TorusTauTK

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.Z4TorusGeometry
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2TorusMultiLinkPolyGibbs (linkVar)
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2HaarAlgebra (PE pe_refl pe_trans pe_symm)
open YMGap.Continuum.SU2TorusRPSubst (QPE qsub RingSub)
open YMGap.Continuum.SU2TorusTimeRefl (sigma)
open YMGap.Continuum.SU2TorusTau (tau)
open YMGap.Continuum.SU2TimeShift (shv)

variable (N t : Nat) (hN : 0 < N)

theorem tau_ringSub : RingSub (torusLinks N).length (tau N t hN) where
  mul p q := by unfold tau; rw [reindexQuaternionPolynomial_mul, reindexQuaternionPolynomial_mul]; exact pe_refl _ _
  add p q := by unfold tau; rw [reindexQuaternionPolynomial_add, reindexQuaternionPolynomial_add]; exact pe_refl _ _
  smul c p := by unfold tau; rw [reindexQuaternionPolynomial_smul, reindexQuaternionPolynomial_smul]; exact pe_refl _ _
  neg p := by unfold tau; rw [reindexQuaternionPolynomial_neg, reindexQuaternionPolynomial_neg]; exact pe_refl _ _
  one := pe_trans _ (YMGap.Continuum.SU2TorusRPReindexCongr.reindex_peCongrOn (sigma N t hN)
      (fun s hs => YMGap.Continuum.SU2QuaternionHaarCertificateReindex.reindex_supported (sigma N 0 hN) _ s hs)
      (YMGap.Continuum.SU2TorusRPCore.sup_one _) (YMGap.Continuum.SU2TorusRPReindex.reindex_ringSub (sigma N 0 hN)).one)
    (YMGap.Continuum.SU2TorusRPReindex.reindex_ringSub (sigma N t hN)).one

theorem tau_TK (β : Q') (K : Nat) (p : Z4Plaq) (hp : InBox N p.1) :
    PE (torusLinks N).length (tau N t hN (YMGap.Continuum.SU2WilsonPolymerIdentity.TK (torusLinks N) N β K p))
      (YMGap.Continuum.SU2WilsonPolymerIdentity.TK (torusLinks N) N β K (shv N t p)) := by
  rw [YMGap.Continuum.SU2TimeShift.tk_shift]
  have m : ∀ v d, InBox N v → (v, d) ∈ torusLinks N := fun v d h => (mem_torusLinks N v d).2 h
  have l := fun v d (h : InBox N v) => YMGap.Continuum.SU2TorusTauVar.tau_lv N t hN (v, d) (m v d h)
  have h1 := tAdd_inBox hN hp
  refine pe_trans _ (YMGap.Continuum.SU2TorusRPSubst.TK_word_sub (tau_ringSub N t hN) _ _ _ _ _ K)
    (YMGap.Continuum.SU2TorusRPSubst.wilsonPoly_pe _ ?_ _ K)
  exact (YMGap.Continuum.SU2TorusRPSubst.qpe_mul (YMGap.Continuum.SU2TorusRPSubst.qpe_mul (l _ _ hp) (l _ _ (h1 _)))
    (YMGap.Continuum.SU2TorusRPSubst.qpe_mul (YMGap.Continuum.SU2TorusRPSubst.qpe_conj (l _ _ (h1 _)))
      (YMGap.Continuum.SU2TorusRPSubst.qpe_conj (l _ _ hp)))).s

end YMGap.Continuum.SU2TorusTauTK

#print axioms YMGap.Continuum.SU2TorusTauTK.tau_TK
