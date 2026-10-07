/-
# Torus RP (d7a): Θ on plaquette weights for any Θ-like substitution

`ThetaLike n S links M D`: `S` is a RingSub on `n` blocks sending each spatial link `ℓ` with `D ℓ` to
`U_{Θℓ}` and each temporal link to `U_{Θℓ}*`. Then `S (T_K p) ≈PE T_K (mir p)` and
`S (Π_ps T_K) ≈PE Π_{mir ps} T_K` whenever the links of the plaquettes satisfy `D` (`thetaL_TK`, `thetaL_prod`).
This frees `theta_TK`/`theta_prod` from `thetaPoly` on `links.length` blocks, so they apply to the split carrier
`a + a` with the half-swap involution.

**RP FOR THE ACTUAL TORUS MEASURE IS OPEN.**
-/

import YMGap.Continuum.SU2TorusRPMaster
import YMGap.Continuum.SU2TorusRPThetaProd

namespace YMGap.Continuum.SU2TorusRPThetaAbs

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricSpinNetworkMehler.PolyQuaternion (mul conj)
open YMGap.Continuum.SU2TorusRPSubst (RingSub QPE qsub TK_word_sub wilsonPoly_pe prodPoly_sub pe_mul2)
open YMGap.Continuum.SU2HaarAlgebra (PE pe_trans pe_refl)
open YMGap.Continuum.SU2HaarL1Activity (prodPoly)
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4TorusGeometry
open YMGap.Continuum.SU2TorusMultiLinkPolyGibbs (linkVar)
open YMGap.Continuum.SU2PlaqSupport (plaqLinks)
open YMGap.Continuum.SU2TorusRPGeom (reflLink rv rt)
open YMGap.Continuum.SU2TorusRPThetaPoly (d0)
open YMGap.Continuum.SU2TorusRPThetaTK (isT)
open YMGap.Continuum.SU2TorusRPThetaProd (mir)

structure ThetaLike (n : Nat) (S : RatPoly → RatPoly) (links : List Z4Link) (M : Nat) (D : Z4Link → Prop) : Prop where
  ring : RingSub n S
  spatial : ∀ ℓ, D ℓ → isT ℓ.2 = false → QPE n (qsub S (linkVar links ℓ)) (linkVar links (reflLink M ℓ))
  temporal : ∀ v, D (v, .x0) → QPE n (qsub S (linkVar links (v, .x0))) (conj (linkVar links (reflLink M (v, .x0))))

variable {n : Nat} {S : RatPoly → RatPoly} {links : List Z4Link} {M : Nat} {D : Z4Link → Prop}
  (hM : 1 ≤ M) (hS : ThetaLike n S links M D) (β : Q') (K : Nat)

theorem word {l1 l2 l3 l4 r1 r2 r3 r4 : PolyQuaternion}
    (h1 : QPE n (qsub S l1) r1) (h2 : QPE n (qsub S l2) r2)
    (h3 : QPE n (qsub S l3) r3) (h4 : QPE n (qsub S l4) r4) :
    QPE n (mul (mul (qsub S l1) (qsub S l2)) (mul (conj (qsub S l3)) (conj (qsub S l4))))
      (mul (mul r1 r2) (mul (conj r3) (conj r4))) :=
  YMGap.Continuum.SU2TorusRPSubst.qpe_mul (YMGap.Continuum.SU2TorusRPSubst.qpe_mul h1 h2)
    (YMGap.Continuum.SU2TorusRPSubst.qpe_mul (YMGap.Continuum.SU2TorusRPSubst.qpe_conj h3)
      (YMGap.Continuum.SU2TorusRPSubst.qpe_conj h4))

include hS in
theorem thetaL_TK_spatial (v : Z4Vertex) (P : Z4Plane) (hP : isT (dirsOf P).1 = false)
    (hL : ∀ ℓ ∈ plaqLinks (2 * M) (v, P), D ℓ) :
    PE n (S (YMGap.Continuum.SU2WilsonPolymerIdentity.TK links (2 * M) β K (v, P)))
      (YMGap.Continuum.SU2WilsonPolymerIdentity.TK links (2 * M) β K (rv M v, P)) := by
  have hm : ∀ i, i < 4 → D ((plaqLinks (2 * M) (v, P)).getD i d0) := fun i hi =>
    hL _ (YMGap.Continuum.SU2TorusRPThetaPoly.getD_mem (by simp [plaqLinks]; omega))
  obtain ⟨a, b, c, e⟩ := v
  cases P <;> simp only [isT, dirsOf] at hP <;> (try exact absurd hP (by decide)) <;>
  · refine pe_trans _ (TK_word_sub hS.ring _ _ _ _ _ K) ?_
    refine wilsonPoly_pe _ (word
      (hS.spatial _ (hm 0 (by decide)) rfl)
      (hS.spatial _ (hm 1 (by decide)) rfl)
      (hS.spatial _ (hm 2 (by decide)) rfl)
      (hS.spatial _ (hm 3 (by decide)) rfl)).s _ K

include hM hS in
theorem thetaL_TK_time (v : Z4Vertex) (hv : v.1 < 2 * M) (P : Z4Plane)
    (hP : isT (dirsOf P).1 = true) (hL : ∀ ℓ ∈ plaqLinks (2 * M) (v, P), D ℓ) :
    PE n (S (YMGap.Continuum.SU2WilsonPolymerIdentity.TK links (2 * M) β K (v, P)))
      (YMGap.Continuum.SU2WilsonPolymerIdentity.TK links (2 * M) β K (rv M (tAdd (2 * M) v .x0), P)) := by
  have hm : ∀ i, i < 4 → D ((plaqLinks (2 * M) (v, P)).getD i d0) := fun i hi =>
    hL _ (YMGap.Continuum.SU2TorusRPThetaPoly.getD_mem (by simp [plaqLinks]; omega))
  have hrv := YMGap.Continuum.SU2TorusRPThetaTime.rv_shift hM v hv
  obtain ⟨a, b, c, e⟩ := v
  cases P <;> simp only [isT, dirsOf] at hP <;> (try exact absurd hP (by decide)) <;>
  · refine pe_trans _ (TK_word_sub hS.ring _ _ _ _ _ K) ?_
    refine pe_trans _ (wilsonPoly_pe _ (word
      (hS.temporal _ (hm 0 (by decide)))
      (hS.spatial _ (hm 1 (by decide)) rfl)
      (hS.temporal _ (hm 2 (by decide)))
      (hS.spatial _ (hm 3 (by decide)) rfl)).s _ K) ?_
    refine YMGap.Continuum.SU2TorusRPKernel.pe_of_coeff _ (YMGap.Continuum.SU2TorusRPKernel.wilsonPoly_congr ?_ _ K)
    simp only [plaqLinks, dirsOf, List.getD_cons_succ, List.getD_cons_zero]
    (try rw [show reflLink M ((a, b, c, e), Dir4.x1) = (rv M (a, b, c, e), Dir4.x1) from rfl])
    (try rw [show reflLink M ((a, b, c, e), Dir4.x2) = (rv M (a, b, c, e), Dir4.x2) from rfl])
    (try rw [show reflLink M ((a, b, c, e), Dir4.x3) = (rv M (a, b, c, e), Dir4.x3) from rfl])
    rw [hrv]
    exact YMGap.Continuum.SU2TorusRPThetaTime.theta_time_word _ _ _ _

include hM hS in
theorem thetaL_TK (p : Z4Plaq) (hp : p.1.1 < 2 * M) (hL : ∀ ℓ ∈ plaqLinks (2 * M) p, D ℓ) :
    PE n (S (YMGap.Continuum.SU2WilsonPolymerIdentity.TK links (2 * M) β K p))
      (YMGap.Continuum.SU2WilsonPolymerIdentity.TK links (2 * M) β K (mir M p)) := by
  obtain ⟨v, P⟩ := p
  unfold mir
  cases h : isT (dirsOf P).1
  · exact thetaL_TK_spatial hS β K v P h hL
  · exact thetaL_TK_time hM hS β K v hp P h hL

include hM hS in
theorem thetaL_prod (ps : List Z4Plaq) (h : ∀ p ∈ ps, p.1.1 < 2 * M ∧ ∀ ℓ ∈ plaqLinks (2 * M) p, D ℓ) :
    PE n (S (prodPoly (YMGap.Continuum.SU2WilsonPolymerIdentity.TK links (2 * M) β K) ps))
      (prodPoly (YMGap.Continuum.SU2WilsonPolymerIdentity.TK links (2 * M) β K) (ps.map (mir M))) := by
  refine pe_trans _ (prodPoly_sub hS.ring _ ps) ?_
  induction ps with
  | nil => exact pe_refl _ _
  | cons p ps ih =>
    have hp := h p (List.mem_cons_self ..)
    exact pe_mul2 _ (thetaL_TK hM hS β K p hp.1 hp.2) (ih fun q hq => h q (List.mem_cons_of_mem _ hq))

end YMGap.Continuum.SU2TorusRPThetaAbs

#print axioms YMGap.Continuum.SU2TorusRPThetaAbs.thetaL_prod
