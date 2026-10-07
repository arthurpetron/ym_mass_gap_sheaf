/-
# Torus RP assembly (d2c): Θpoly on the full Wilson product, and Haar invariance

* `mir M p`: the mirror plaquette, `(rv v, P)` for spatial `P` and `(rv(v+e0), P)` for time-like `P`.
* `theta_TK`: `thetaPoly (TK p) ≈PE TK (mir p)` for every in-box plaquette whose links lie in `links`.
* `theta_prod`: `thetaPoly (Π_{p∈ps} TK p) ≈PE Π_{p∈ps} TK (mir p)`.
* `theta_haar`: `∫ thetaPoly X ≈ ∫ X` for supported `X` (reindex invariance, then conj invariance).
* `torus_mirror`: `∫ Π_{p∈ps} TK p ≈ ∫ Π_{p∈ps} TK (mir p)` (by `haar_step`), given the product is supported.

**RP FOR THE ACTUAL TORUS MEASURE IS OPEN** (still to do: the pos/neg/cross factorisation and the crossing split).
-/

import YMGap.Continuum.SU2TorusRPThetaTime

namespace YMGap.Continuum.SU2TorusRPThetaProd

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricHaarMehlerProjection (quaternionHaar)
open YMGap.Continuum.SU2HaarAlgebra (PE pe_trans pe_refl)
open YMGap.Continuum.SU2TorusRPSubst (prodPoly_sub pe_mul2)
open YMGap.Continuum.SU2HaarL1Activity (prodPoly)
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4TorusGeometry
open YMGap.Continuum.SU2PlaqSupport (plaqLinks)
open YMGap.Continuum.SU2TorusRPGeom (reflLink rv)
open YMGap.Continuum.SU2TorusRPThetaTK (thetaPoly theta_ringSub isT)
open YMGap.Continuum.SU2TorusRPCore (Sup)

def mir (M : Nat) (p : Z4Plaq) : Z4Plaq :=
  if isT (dirsOf p.2).1 then (rv M (tAdd (2 * M) p.1 .x0), p.2) else (rv M p.1, p.2)

variable {M : Nat} (hM : 1 ≤ M) (links : List Z4Link) (hnd : links.Nodup)
  (hbox : ∀ ℓ ∈ links, InBox (2 * M) ℓ.1) (hcl : ∀ ℓ ∈ links, reflLink M ℓ ∈ links) (β : Q') (K : Nat)

theorem theta_TK (p : Z4Plaq) (hp : p.1.1 < 2 * M) (hL : ∀ ℓ ∈ plaqLinks (2 * M) p, ℓ ∈ links) :
    PE links.length (thetaPoly hM links hnd hbox hcl (SU2WilsonPolymerIdentity.TK links (2 * M) β K p))
      (SU2WilsonPolymerIdentity.TK links (2 * M) β K (mir M p)) := by
  obtain ⟨v, P⟩ := p
  unfold mir
  cases h : isT (dirsOf P).1
  · exact SU2TorusRPThetaTK.theta_TK_spatial hM links hnd hbox hcl β K v P h hL
  · exact SU2TorusRPThetaTime.theta_TK_time hM links hnd hbox hcl β K v hp P h hL

theorem theta_prod : ∀ ps : List Z4Plaq, (∀ p ∈ ps, p.1.1 < 2 * M ∧ ∀ ℓ ∈ plaqLinks (2 * M) p, ℓ ∈ links) →
    PE links.length (thetaPoly hM links hnd hbox hcl (prodPoly (SU2WilsonPolymerIdentity.TK links (2 * M) β K) ps))
      (prodPoly (SU2WilsonPolymerIdentity.TK links (2 * M) β K) (ps.map (mir M)))
  | ps, h => by
    refine pe_trans _ (prodPoly_sub (theta_ringSub hM links hnd hbox hcl) _ ps) ?_
    induction ps with
    | nil => exact pe_refl _ _
    | cons p ps ih =>
      have hp := h p (List.mem_cons_self ..)
      exact pe_mul2 _ (theta_TK hM links hnd hbox hcl β K p hp.1 hp.2)
        (ih fun q hq => h q (List.mem_cons_of_mem _ hq))

theorem theta_haar (X : RatPoly) (hX : Sup links.length X) :
    (quaternionHaar links.length (thetaPoly hM links hnd hbox hcl X)).eqv (quaternionHaar links.length X) :=
  Q'.eqv_trans _ _ _ (SU2TorusRPHaar.conj_haar _ _ _)
    (YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection.quaternionHaar_reindex _ X hX)

include hM hnd hbox hcl in
theorem torus_mirror (ps : List Z4Plaq) (h : ∀ p ∈ ps, p.1.1 < 2 * M ∧ ∀ ℓ ∈ plaqLinks (2 * M) p, ℓ ∈ links)
    (hS : Sup links.length (prodPoly (SU2WilsonPolymerIdentity.TK links (2 * M) β K) ps)) :
    (quaternionHaar links.length (prodPoly (SU2WilsonPolymerIdentity.TK links (2 * M) β K) ps)).eqv
      (quaternionHaar links.length (prodPoly (SU2WilsonPolymerIdentity.TK links (2 * M) β K) (ps.map (mir M)))) :=
  SU2TorusRPCompOn.haar_step _ (theta_haar hM links hnd hbox hcl _ hS) (theta_prod hM links hnd hbox hcl β K ps h)

end YMGap.Continuum.SU2TorusRPThetaProd

#print axioms YMGap.Continuum.SU2TorusRPThetaProd.theta_prod
#print axioms YMGap.Continuum.SU2TorusRPThetaProd.torus_mirror
