/-
# Torus RP assembly (d1): Θ on links as a quaternion-block involution, and its action on `linkVar`

For a nodup link list `links` closed under an involution `f` (e.g. `SU2TorusRPGeom.reflLink M`):
* `linkInv links f : QuaternionBlockInvolution links.length`, where block `k` maps to the block of `f (links[k])`.
* `reindex_linkVar`: `reindexQuaternionPolynomial (linkInv …)` sends `linkVar links ℓ` to `linkVar links (f ℓ)`
  (componentwise `PE`).
* `thetaInv M`: the instance with `f = reflLink M`, for any box link list closed under Θ.

**RP FOR THE ACTUAL TORUS MEASURE IS OPEN**: still to do are the conjugation of reversed temporal links, the
`haar_step` chain, and factorising `Π TK` into the two halves times the crossing words.
-/

import YMGap.Continuum.SU2TorusRPGeom
import YMGap.Continuum.SU2TorusRPCompOn

namespace YMGap.Continuum.SU2TorusRPThetaPoly

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4TorusGeometry
open YMGap.Continuum.SU2TorusMultiLinkPolyGibbs (linkVar)
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
  (QuaternionBlockInvolution reindexQuaternionPolynomial)
open YMGap.Continuum.SU2TorusRPSubst (QPE qsub)
open YMGap.Continuum.SU2PlaqWordHolonomy (getElem?_idxOf)

def d0 : Z4Link := ((0, 0, 0, 0), .x0)

theorem getD_idxOf {ℓ : Z4Link} {l : List Z4Link} (h : ℓ ∈ l) : l.getD (l.idxOf ℓ) d0 = ℓ := by
  rw [List.getD_eq_getElem?_getD, getElem?_idxOf h]; rfl

theorem getD_mem : ∀ {l : List Z4Link} {k : Nat}, k < l.length → l.getD k d0 ∈ l
  | [], _, hk => absurd hk (Nat.not_lt_zero _)
  | x :: _, 0, _ => List.mem_cons_self ..
  | _ :: l, k + 1, hk => List.mem_cons_of_mem _ (getD_mem (l := l) (k := k) (Nat.lt_of_succ_lt_succ hk))

theorem idxOf_getD : ∀ (l : List Z4Link), l.Nodup → ∀ k, k < l.length → l.idxOf (l.getD k d0) = k
  | [], _, k, hk => absurd hk (Nat.not_lt_zero _)
  | x :: l, _, 0, _ => by
    show (x :: l).idxOf x = 0
    rw [List.idxOf_cons, show (x == x) = true from beq_iff_eq.mpr rfl]; rfl
  | x :: l, hnd, k + 1, hk => by
    have hnd' := List.nodup_cons.mp hnd
    have hk' : k < l.length := Nat.lt_of_succ_lt_succ hk
    have hmem : l.getD k d0 ∈ l := getD_mem hk'
    have hne : (x == l.getD k d0) = false := by
      cases hb : (x == l.getD k d0) with
      | false => rfl
      | true => exact absurd ((beq_iff_eq.mp hb) ▸ hmem) hnd'.1
    show (x :: l).idxOf (l.getD k d0) = k + 1
    rw [List.idxOf_cons, hne, cond_false, idxOf_getD l hnd'.2 k hk']

section
variable (links : List Z4Link) (f : Z4Link → Z4Link) (hnd : links.Nodup) (hcl : ∀ ℓ ∈ links, f ℓ ∈ links)
  (hinv : ∀ ℓ ∈ links, f (f ℓ) = ℓ)

def linkInv : QuaternionBlockInvolution links.length where
  map k := if k < links.length then links.idxOf (f (links.getD k d0)) else k
  map_lt k hk := by
    rw [if_pos hk]; exact List.idxOf_lt_length_of_mem (hcl _ (getD_mem hk))
  involutive k hk := by
    have h1 : links.idxOf (f (links.getD k d0)) < links.length :=
      List.idxOf_lt_length_of_mem (hcl _ (getD_mem hk))
    simp only [if_pos hk, if_pos h1]
    rw [getD_idxOf (hcl _ (getD_mem hk)), hinv _ (getD_mem hk), idxOf_getD links hnd k hk]

theorem linkInv_map {ℓ : Z4Link} (h : ℓ ∈ links) :
    (linkInv links f hnd hcl hinv).map (links.idxOf ℓ) = links.idxOf (f ℓ) := by
  show (if links.idxOf ℓ < links.length then _ else _) = _
  rw [if_pos (List.idxOf_lt_length_of_mem h), getD_idxOf h]

theorem reindex_linkVar {ℓ : Z4Link} (h : ℓ ∈ links) :
    QPE links.length (qsub (reindexQuaternionPolynomial (linkInv links f hnd hcl hinv)) (linkVar links ℓ))
      (linkVar links (f ℓ)) := by
  have := YMGap.Continuum.SU2TorusRPReindex.reindex_coord (linkInv links f hnd hcl hinv) (links.idxOf ℓ)
    (List.idxOf_lt_length_of_mem h)
  rw [linkInv_map links f hnd hcl hinv h] at this
  exact this

end

open YMGap.Continuum.SU2TorusRPGeom (reflLink refl_invol)

/-- Θ as a block involution of any box link list that is closed under Θ. -/
def thetaInv {M : Nat} (hM : 1 ≤ M) (links : List Z4Link) (hnd : links.Nodup)
    (hbox : ∀ ℓ ∈ links, InBox (2 * M) ℓ.1) (hcl : ∀ ℓ ∈ links, reflLink M ℓ ∈ links) :
    QuaternionBlockInvolution links.length :=
  linkInv links (reflLink M) hnd hcl fun ℓ h => refl_invol hM ℓ (hbox ℓ h)

end YMGap.Continuum.SU2TorusRPThetaPoly

#print axioms YMGap.Continuum.SU2TorusRPThetaPoly.linkInv
#print axioms YMGap.Continuum.SU2TorusRPThetaPoly.reindex_linkVar
#print axioms YMGap.Continuum.SU2TorusRPThetaPoly.thetaInv
