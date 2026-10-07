/-
# Torus RP assembly (d2b): Θpoly on time-plaquettes

* `theta_time_word`: `Re((A*·B)·(C**·D*)) ≅ Re((A·D)·(C*·B*))`, from `refl_word` plus cyclicity of `Re`.
* `rt_shift`: `rv v = rv(v+e0) + e0` on the box, i.e. `rt a = rt(a+1) + 1 (mod 2M)`.
* `theta_temporal_link`: a temporal link variable goes to the conjugate of its Θ-image's variable.
* `theta_TK_time`: for a time-plaquette `p = (v,P)` (plane `(x0,d)`) whose links lie in `links`,
  `thetaPoly (TK p) ≈PE TK (rv(v+e0), P)`. This covers every time-plaquette, crossing ones included.
With `theta_TK_spatial`, Θpoly maps every plaquette weight to the weight of its mirror plaquette.

**RP FOR THE ACTUAL TORUS MEASURE IS OPEN** (still to do: the `haar_step` chain over the full product, the
`plaq_*` factorisation, the crossing-link split, and `wilson_rp_qfull`).
-/

import YMGap.Continuum.SU2TorusRPThetaTK
import YMGap.Continuum.SU2TorusRPWord

namespace YMGap.Continuum.SU2TorusRPThetaTime

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricSpinNetworkMehler.PolyQuaternion (mul conj)
open YMGap.Continuum.SU2TorusRPSubst (QPE qsub TK_word_sub wilsonPoly_pe)
open YMGap.Continuum.SU2HaarAlgebra (PE pe_trans)
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4TorusGeometry
open YMGap.Continuum.SU2TorusMultiLinkPolyGibbs (linkVar)
open YMGap.Continuum.SU2PlaqSupport (plaqLinks)
open YMGap.Continuum.SU2TorusRPGeom (reflLink rv rt)
open YMGap.Continuum.SU2TorusRPThetaPoly (d0 getD_idxOf)
open YMGap.Continuum.SU2TorusRPThetaTK (thetaPoly theta_ringSub theta_spatial_link theta_word tSel isT)
open YMGap.Continuum.SU2TorusRPWord (refl_word scalar_comm conj_conj qmul qrefl qsymm)

local infix:50 " ≅ " => RatPolyCoeffEqv

theorem theta_time_word (A B C D : PolyQuaternion) :
    (mul (mul (conj A) B) (mul (conj (conj C)) (conj D))).scalar ≅ (mul (mul A D) (mul (conj C) (conj B))).scalar :=
  (scalar_comm _ _).trans
    ((qmul (qmul (conj_conj C) (qrefl _)) (qmul (qrefl _) (qsymm (conj_conj B)))).scalar.trans (refl_word A D C B))

variable {M : Nat} (hM : 1 ≤ M)
include hM

theorem rt_shift {a : Nat} (ha : a < 2 * M) : rt M a = wrapSucc (2 * M) (rt M (wrapSucc (2 * M) a)) := by
  unfold rt; geo

theorem rv_shift (v : Z4Vertex) (hv : v.1 < 2 * M) : rv M v = tAdd (2 * M) (rv M (tAdd (2 * M) v .x0)) .x0 := by
  obtain ⟨a, b, c, e⟩ := v
  show (rt M a, b, c, e) = (wrapSucc (2 * M) (rt M (wrapSucc (2 * M) a)), b, c, e)
  rw [← rt_shift hM hv]

variable (links : List Z4Link) (hnd : links.Nodup)
  (hbox : ∀ ℓ ∈ links, InBox (2 * M) ℓ.1) (hcl : ∀ ℓ ∈ links, reflLink M ℓ ∈ links)

theorem theta_temporal_link (v : Z4Vertex) (h : (v, .x0) ∈ links) :
    QPE links.length (qsub (thetaPoly hM links hnd hbox hcl) (linkVar links (v, .x0)))
      (conj (linkVar links (reflLink M (v, .x0)))) := by
  have := SU2TorusRPThetaConj.theta_linkVar links (reflLink M) hnd hcl
    (fun ℓ h => SU2TorusRPGeom.refl_invol hM ℓ (hbox ℓ h)) (tSel links) h
  have ht : tSel links (links.idxOf (reflLink M (v, .x0))) = true := by
    unfold tSel; rw [getD_idxOf (hcl _ h)]; rfl
  rw [ht, if_pos rfl] at this
  exact this

/-- Θ maps `T_K` of a time-plaquette `(v,P)` to `T_K` of its mirror `(rv(v+e0), P)`. -/
theorem theta_TK_time (β : Q') (K : Nat) (v : Z4Vertex) (hv : v.1 < 2 * M) (P : Z4Plane)
    (hP : isT (dirsOf P).1 = true) (hL : ∀ ℓ ∈ plaqLinks (2 * M) (v, P), ℓ ∈ links) :
    PE links.length (thetaPoly hM links hnd hbox hcl (SU2WilsonPolymerIdentity.TK links (2 * M) β K (v, P)))
      (SU2WilsonPolymerIdentity.TK links (2 * M) β K (rv M (tAdd (2 * M) v .x0), P)) := by
  have hm : ∀ i, i < 4 → (plaqLinks (2 * M) (v, P)).getD i d0 ∈ links := fun i hi =>
    hL _ (SU2TorusRPThetaPoly.getD_mem (by simp [plaqLinks]; omega))
  have hrv := rv_shift hM v hv
  obtain ⟨a, b, c, e⟩ := v
  cases P <;> simp only [isT, dirsOf] at hP <;> (try exact absurd hP (by decide)) <;>
  · refine pe_trans _ (TK_word_sub (theta_ringSub hM links hnd hbox hcl) _ _ _ _ _ K) ?_
    refine pe_trans _ (wilsonPoly_pe _ (theta_word links
      (theta_temporal_link hM links hnd hbox hcl _ (hm 0 (by decide)))
      (theta_spatial_link hM links hnd hbox hcl (hm 1 (by decide)) rfl)
      (theta_temporal_link hM links hnd hbox hcl _ (hm 2 (by decide)))
      (theta_spatial_link hM links hnd hbox hcl (hm 3 (by decide)) rfl)).s _ K) ?_
    refine SU2TorusRPKernel.pe_of_coeff _ (SU2TorusRPKernel.wilsonPoly_congr ?_ _ K)
    simp only [plaqLinks, dirsOf, List.getD_cons_succ, List.getD_cons_zero]
    (try rw [show reflLink M ((a, b, c, e), Dir4.x1) = (rv M (a, b, c, e), Dir4.x1) from rfl])
    (try rw [show reflLink M ((a, b, c, e), Dir4.x2) = (rv M (a, b, c, e), Dir4.x2) from rfl])
    (try rw [show reflLink M ((a, b, c, e), Dir4.x3) = (rv M (a, b, c, e), Dir4.x3) from rfl])
    rw [hrv]
    exact theta_time_word _ _ _ _

end YMGap.Continuum.SU2TorusRPThetaTime

#print axioms YMGap.Continuum.SU2TorusRPThetaTime.theta_time_word
#print axioms YMGap.Continuum.SU2TorusRPThetaTime.theta_TK_time
#print axioms YMGap.Continuum.SU2TorusRPThetaTime.rt_shift
