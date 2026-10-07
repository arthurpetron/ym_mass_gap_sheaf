/-
# Torus RP (g5): `τ_t` is a ring substitution and shifts the `T_K` plaquette weight

* `tau_ringSub`: `τ_t` is a `RingSub`. `mul`/`add`/`smul`/`neg` hold literally; `one` holds up to padding.
* `tau_TK`: `τ_t (T_K p) ≡PE T_K (shv t p)` for `p` in the box. This uses the Prover's `tk_shift` (read-only) and
  `tau_lv`.
* `tau_prod`: `τ_t (Π_{torusPlaquettes} T_K) ≡PE Π T_K`. It uses HEAD's `torusPlaquettes_timeShift_perm` and
  `SU2TorusRPSplitTK.prod_congr`.
* `shift_inv`: `∫ τA·τB·Π T_K ≈ ∫ A·B·Π T_K` (supported integrand).

`Θ∘τ_x ≡ τ_{−x}∘Θ` and the correlator identity are not in this file.
-/

import YMGap.Continuum.SU2TorusTauVar
import YMGap.Continuum.SU2TorusLinksTimeShift

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

open YMGap.Continuum.SU2HaarL1Activity (prodPoly)

theorem prod_map (F : Z4Plaq → RatPoly) (f : Z4Plaq → Z4Plaq) : ∀ ps : List Z4Plaq,
    prodPoly F (ps.map f) = prodPoly (fun p => F (f p)) ps
  | [] => rfl
  | p :: ps => by rw [List.map_cons]; show polyMul _ _ = polyMul _ _; rw [prod_map F f ps]

/-- **`Π T_K` is invariant under `τ_t`** (PE, whole torus). -/
theorem tau_prod (β : Q') (K : Nat) :
    PE (torusLinks N).length
      (tau N t hN (prodPoly (YMGap.Continuum.SU2WilsonPolymerIdentity.TK (torusLinks N) N β K) (torusPlaquettes N)))
      (prodPoly (YMGap.Continuum.SU2WilsonPolymerIdentity.TK (torusLinks N) N β K) (torusPlaquettes N)) := by
  refine pe_trans _ (YMGap.Continuum.SU2TorusRPSubst.prodPoly_sub (tau_ringSub N t hN) _ _) ?_
  refine pe_trans _ (YMGap.Continuum.SU2TorusRPSplitTK.prod_congr _ fun p hp => tau_TK N t hN β K p ?_) ?_
  · obtain ⟨v, P⟩ := p; exact (mem_torusPlaquettes N v P).1 hp
  · rw [← prod_map]
    exact YMGap.Continuum.SU2TorusRPFactor.prod_perm _ _ (YMGap.Continuum.SU2TorusLinksTimeShift.torusPlaquettes_timeShift_perm hN t)

/-- **The torus `T_K` integral is invariant under the time shift:** `∫ τA·τB·Π T_K ≈ ∫ A·B·Π T_K`. -/
theorem shift_inv (β : Q') (K : Nat) (A B : RatPoly)
    (hP : YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity.SupportedQuaternionBlocks (torusLinks N).length
      (polyMul (polyMul A B) (prodPoly (YMGap.Continuum.SU2WilsonPolymerIdentity.TK (torusLinks N) N β K) (torusPlaquettes N)))) :
    (YMGap.Continuum.BF4GeometricHaarMehlerProjection.quaternionHaar (torusLinks N).length
      (polyMul (polyMul (tau N t hN A) (tau N t hN B))
        (prodPoly (YMGap.Continuum.SU2WilsonPolymerIdentity.TK (torusLinks N) N β K) (torusPlaquettes N)))).eqv
    (YMGap.Continuum.BF4GeometricHaarMehlerProjection.quaternionHaar (torusLinks N).length
      (polyMul (polyMul A B) (prodPoly (YMGap.Continuum.SU2WilsonPolymerIdentity.TK (torusLinks N) N β K) (torusPlaquettes N)))) := by
  have hR := tau_ringSub N t hN
  have hPE := pe_trans _ (hR.mul (polyMul A B) _) (YMGap.Continuum.SU2TorusRPSubst.pe_mul2 _ (hR.mul A B) (tau_prod N t hN β K))
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (YMGap.Continuum.SU2HaarAlgebra.pe_haar _ hPE))
    (YMGap.Continuum.SU2TorusTau.haar_tau N t hN _ hP)

end YMGap.Continuum.SU2TorusTauTK

#print axioms YMGap.Continuum.SU2TorusTauTK.tau_TK
#print axioms YMGap.Continuum.SU2TorusTauTK.tau_prod
#print axioms YMGap.Continuum.SU2TorusTauTK.shift_inv
