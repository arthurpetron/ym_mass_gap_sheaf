/-
# Reflection of the fundamental spatial plaquette observable

`theta_chi_spatial` transports the actual polynomial `chi = plaqCharacter ... 1`
through the existing torus reflection. It is a finite `PE` identity on the same
link coordinates, with link coverage, box membership and reflection closure
explicit. This supplies one algebraic input to `SU2ClusterBridge`'s open
`hcov`: the reflection of the observable itself.

Centering, insertion-factor extraction, equality of one-point means, positive
half support and translated RP pairings remain separate obligations. No
clustering estimate, operator, volume limit or physical mass gap is proved here.
-/

import YMGap.Continuum.SU2TorusRPThetaTK
import YMGap.Continuum.SU2WilsonObsActivity

namespace YMGap.Continuum.SU2TorusRPObservableReflection

set_option autoImplicit false

open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricSpinNetworkMehler (characterPolynomial PolyQuaternion)
open YMGap.Continuum.SU2HaarAlgebra (PE pe_trans)
open YMGap.Continuum.SU2TorusRPSubst (RingSub qsub word_sub pe_smul)
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4TorusGeometry
open YMGap.Continuum.SU2TorusMultiLinkPolyGibbs (plaqCharacter)
open YMGap.Continuum.SU2PlaqSupport (plaqLinks)
open YMGap.Continuum.SU2TorusRPGeom (rv reflLink)
open YMGap.Continuum.SU2TorusRPThetaPoly (d0)
open YMGap.Continuum.SU2TorusRPThetaTK
  (thetaPoly theta_ringSub theta_spatial_link theta_word isT)
open YMGap.Continuum.SU2WilsonObsActivity (chi)

/-- A ring substitution transports the fundamental character of a plaquette
word. Its factor two is the defining `characterPolynomial ... 1`. -/
theorem chi_word_sub {n : Nat} {S : RatPoly → RatPoly} (hS : RingSub n S)
    (l1 l2 l3 l4 : PolyQuaternion) :
    PE n
      (S (characterPolynomial
        (PolyQuaternion.mul (PolyQuaternion.mul l1 l2)
          (PolyQuaternion.mul (PolyQuaternion.conj l3) (PolyQuaternion.conj l4))).scalar 1))
      (characterPolynomial
        (PolyQuaternion.mul (PolyQuaternion.mul (qsub S l1) (qsub S l2))
          (PolyQuaternion.mul (PolyQuaternion.conj (qsub S l3))
            (PolyQuaternion.conj (qsub S l4)))).scalar 1) :=
  pe_trans n (hS.smul 2 _) (pe_smul n 2 (word_sub hS l1 l2 l3 l4).s)

variable {M : Nat} (hM : 1 ≤ M) (links : List Z4Link) (hnd : links.Nodup)
  (hbox : ∀ ℓ ∈ links, InBox (2 * M) ℓ.1)
  (hcl : ∀ ℓ ∈ links, reflLink M ℓ ∈ links)

/-- Reflection sends the genuine fundamental spatial plaquette character to
the character of its mirror plaquette, in Haar-context equivalence. -/
theorem theta_chi_spatial (v : Z4Vertex) (P : Z4Plane)
    (hP : isT (dirsOf P).1 = false)
    (hL : ∀ ℓ ∈ plaqLinks (2 * M) (v, P), ℓ ∈ links) :
    PE links.length
      (thetaPoly hM links hnd hbox hcl (chi links (2 * M) (v, P)))
      (chi links (2 * M) (rv M v, P)) := by
  have hm : ∀ i, i < 4 → (plaqLinks (2 * M) (v, P)).getD i d0 ∈ links := fun i hi =>
    hL _ (YMGap.Continuum.SU2TorusRPThetaPoly.getD_mem (by simp [plaqLinks]; omega))
  obtain ⟨a, b, c, e⟩ := v
  cases P <;> simp only [isT, dirsOf] at hP <;> (try exact absurd hP (by decide)) <;>
  · refine pe_trans _ (chi_word_sub (theta_ringSub hM links hnd hbox hcl) _ _ _ _) ?_
    exact pe_smul _ 2 (theta_word links
      (theta_spatial_link hM links hnd hbox hcl (hm 0 (by decide)) rfl)
      (theta_spatial_link hM links hnd hbox hcl (hm 1 (by decide)) rfl)
      (theta_spatial_link hM links hnd hbox hcl (hm 2 (by decide)) rfl)
      (theta_spatial_link hM links hnd hbox hcl (hm 3 (by decide)) rfl)).s

end YMGap.Continuum.SU2TorusRPObservableReflection

#print axioms YMGap.Continuum.SU2TorusRPObservableReflection.chi_word_sub
#print axioms YMGap.Continuum.SU2TorusRPObservableReflection.theta_chi_spatial
