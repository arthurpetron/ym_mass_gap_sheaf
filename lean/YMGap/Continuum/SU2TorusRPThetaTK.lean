/-
# Torus RP assembly (d2a): Θpoly is a `RingSub`, and it maps `T_K` of a spatial plaquette to `T_K` of its mirror image

* `tSel links k`: block `k` is a temporal link.
* `thetaPoly`: `sign(conjSel tSel) ∘ reindex(thetaInv)`.
* `theta_ringSub`: `thetaPoly` is a `RingSub` (via `ringSub_comp`; the outer conj flip is `PECongr`, support-free).
* `theta_spatial_link`: a spatial link variable goes to the variable of its Θ-image, with no conjugation.
* `theta_TK_spatial`: for a spatial plaquette `p = (v,P)` whose links all lie in `links`,
  `thetaPoly (TK p) ≈PE TK (rv v, P)`. Θ maps the positive-half spatial weights onto the negative-half ones.

Time-plaquettes (reflected word, `refl_word`) and the full `haar_step` chain remain. **RP FOR THE ACTUAL TORUS
MEASURE IS OPEN.**
-/

import YMGap.Continuum.SU2TorusRPThetaConj
import YMGap.Continuum.SU2WilsonPolymerIdentity

namespace YMGap.Continuum.SU2TorusRPThetaTK

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
  (signSelectedPolynomial reindexQuaternionPolynomial)
open YMGap.Continuum.SU2TorusRPHaar (conjSel)
open YMGap.Continuum.SU2TorusRPSubst (QPE qsub qpe_trans qpe_mul qpe_conj RingSub TK_word_sub wilsonPoly_pe)
open YMGap.Continuum.SU2HaarAlgebra (PE pe_trans)
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4TorusGeometry
open YMGap.Continuum.SU2TorusMultiLinkPolyGibbs (linkVar plaqWord)
open YMGap.Continuum.SU2PlaqSupport (plaqLinks)
open YMGap.Continuum.SU2TorusRPGeom (reflLink rv)
open YMGap.Continuum.SU2TorusRPThetaPoly (thetaInv linkInv d0 getD_idxOf)

def isT : Dir4 → Bool | .x0 => true | _ => false

def tSel (links : List Z4Link) (k : Nat) : Bool := isT (links.getD k d0).2

variable {M : Nat} (hM : 1 ≤ M) (links : List Z4Link) (hnd : links.Nodup)
  (hbox : ∀ ℓ ∈ links, InBox (2 * M) ℓ.1) (hcl : ∀ ℓ ∈ links, reflLink M ℓ ∈ links)

def thetaPoly (p : RatPoly) : RatPoly :=
  signSelectedPolynomial (4 * links.length) (conjSel (tSel links))
    (reindexQuaternionPolynomial (thetaInv hM links hnd hbox hcl) p)

theorem theta_ringSub : RingSub links.length (thetaPoly hM links hnd hbox hcl) :=
  SU2TorusRPConj.ringSub_comp (S := signSelectedPolynomial (4 * links.length) (conjSel (tSel links)))
    (R := reindexQuaternionPolynomial (thetaInv hM links hnd hbox hcl)) (SU2TorusRPConj.conj_ringSub _ _ _)
    (SU2TorusRPConjCongr.conj_peCongr _ _ _) (SU2TorusRPReindex.reindex_ringSub _)

theorem theta_spatial_link {ℓ : Z4Link} (h : ℓ ∈ links) (hs : isT ℓ.2 = false) :
    QPE links.length (qsub (thetaPoly hM links hnd hbox hcl) (linkVar links ℓ)) (linkVar links (reflLink M ℓ)) := by
  have := SU2TorusRPThetaConj.theta_linkVar links (reflLink M) hnd hcl
    (fun ℓ h => SU2TorusRPGeom.refl_invol hM ℓ (hbox ℓ h)) (tSel links) h
  have ht : tSel links (links.idxOf (reflLink M ℓ)) = false := by
    unfold tSel; rw [getD_idxOf (hcl ℓ h)]
    obtain ⟨v, d⟩ := ℓ
    cases d
    · simp only [isT] at hs; exact absurd hs (by decide)
    all_goals rfl
  rw [ht, if_neg (by decide)] at this
  exact this

theorem theta_word {l1 l2 l3 l4 r1 r2 r3 r4 : PolyQuaternion} {S : RatPoly → RatPoly}
    (h1 : QPE links.length (qsub S l1) r1) (h2 : QPE links.length (qsub S l2) r2)
    (h3 : QPE links.length (qsub S l3) r3) (h4 : QPE links.length (qsub S l4) r4) :
    QPE links.length (PolyQuaternion.mul (PolyQuaternion.mul (qsub S l1) (qsub S l2))
        (PolyQuaternion.mul (PolyQuaternion.conj (qsub S l3)) (PolyQuaternion.conj (qsub S l4))))
      (PolyQuaternion.mul (PolyQuaternion.mul r1 r2) (PolyQuaternion.mul (PolyQuaternion.conj r3)
        (PolyQuaternion.conj r4))) :=
  qpe_mul (qpe_mul h1 h2) (qpe_mul (qpe_conj h3) (qpe_conj h4))

/-- Θ maps `T_K` of a spatial plaquette to `T_K` of its mirror plaquette `(rv v, P)`. -/
theorem theta_TK_spatial (β : Q') (K : Nat) (v : Z4Vertex) (P : Z4Plane) (hP : isT (dirsOf P).1 = false)
    (hL : ∀ ℓ ∈ plaqLinks (2 * M) (v, P), ℓ ∈ links) :
    PE links.length (thetaPoly hM links hnd hbox hcl (SU2WilsonPolymerIdentity.TK links (2 * M) β K (v, P)))
      (SU2WilsonPolymerIdentity.TK links (2 * M) β K (rv M v, P)) := by
  have hm : ∀ i, i < 4 → (plaqLinks (2 * M) (v, P)).getD i d0 ∈ links := fun i hi =>
    hL _ (SU2TorusRPThetaPoly.getD_mem (by simp [plaqLinks]; omega))
  obtain ⟨a, b, c, e⟩ := v
  cases P <;> simp only [isT, dirsOf] at hP <;> (try exact absurd hP (by decide)) <;>
  · refine pe_trans _ (TK_word_sub (theta_ringSub hM links hnd hbox hcl) _ _ _ _ _ K) ?_
    refine wilsonPoly_pe _ (theta_word links
      (theta_spatial_link hM links hnd hbox hcl (hm 0 (by decide)) rfl)
      (theta_spatial_link hM links hnd hbox hcl (hm 1 (by decide)) rfl)
      (theta_spatial_link hM links hnd hbox hcl (hm 2 (by decide)) rfl)
      (theta_spatial_link hM links hnd hbox hcl (hm 3 (by decide)) rfl)).s _ K

end YMGap.Continuum.SU2TorusRPThetaTK

#print axioms YMGap.Continuum.SU2TorusRPThetaTK.theta_ringSub
#print axioms YMGap.Continuum.SU2TorusRPThetaTK.theta_TK_spatial
