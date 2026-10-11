/-
# Literal link-occurrence recoding of the localized ORIGINAL action

Only scalar kernel BASES commute in these recodings; the plaquette word is
the unchanged nonabelian word already pinned in the original heat bound.
Every four-edge slot and every supplied face multiplicity remains in
faceLinks. The original carrier's index enumerates its SAME assigned units.
These finite identities supply the incidence/integration join; they do not
assert a uniform partition estimate, entropy bound, response or mass gap.
-/

import YMGap.Continuum.BF4ExactSlabPolynomialActionLocalization
import YMGap.Continuum.BF4ExactSlabFaceLinkLocality
import YMGap.Continuum.SU2TorusRPThetaPoly

namespace YMGap.Continuum.BF4ExactSlabKernelProductRecoding

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.HalfPow (half)
open YMGap.RepTheory.RationalQuaternion (UnitNorm)
open YMGap.RepTheory.RationalQuaternionFourKernelProduct (base product base_bounds)
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.BF4ExactSlabPlaquetteDeficit (linkValue)
open YMGap.Continuum.BF4ExactSlabPolynomialHeatLocalization (faceKernelProduct localizationDegree)
open YMGap.Continuum.BF4ExactSlabPolynomialActionLocalization (scalarProduct localizedProduct scalarProduct_nonnegative)
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality (faceLinks)
open YMGap.Continuum.RGTransport (qpow qpow_nonneg)
open YMGap.Continuum.RingNormaliser (PolyExpr poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv

private theorem mc {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h) (Q'.mul_eqv_congr_left _ _ _ k)

private theorem power_congr {a b : Q'} (h : a ≈ b) : ∀ k, qpow a k ≈ qpow b k
  | 0 => Q'.eqv_refl 1
  | k+1 => mc (power_congr h k) h

private theorem power_one : ∀ k, qpow (1 : Q') k ≈ 1
  | 0 => Q'.eqv_refl 1
  | k+1 => Q'.eqv_trans _ _ _ (Q'.mul_one_eqv _) (power_one k)

private theorem power_mul (a b : Q') : ∀ k, qpow (a*b) k ≈ qpow a k*qpow b k
  | 0 => by change (1 : Q') ≈ 1*1; decide
  | k+1 => Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (power_mul a b k))
      (poly_identity_of_normal_eq
        (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
        (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3)))
        (by decide) (fun | 0 => qpow a k | 1 => qpow b k | 2 => a | _ => b))

private theorem scalar_append {A : Type} (f : A → Q') : ∀ xs ys : List A,
    scalarProduct f (xs++ys) ≈ scalarProduct f xs*scalarProduct f ys
  | [], _ => Q'.eqv_symm (Q'.one_mul_eqv _)
  | _::xs, ys => Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _ (scalar_append f xs ys))
      (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))

private theorem scalar_map {A B : Type} (g : A → B) (f : B → Q') : ∀ xs,
    scalarProduct f (xs.map g) = scalarProduct (fun a => f (g a)) xs
  | [] => rfl
  | _::xs => by simp only [List.map_cons,scalarProduct,scalar_map g f xs]

private theorem scalar_congr {A : Type} {f g : A → Q'} : ∀ xs : List A,
    (∀ a, a ∈ xs → f a ≈ g a) → scalarProduct f xs ≈ scalarProduct g xs
  | [], _ => Q'.eqv_refl 1
  | a::xs, h => mc (h a List.mem_cons_self)
      (scalar_congr xs (fun b hb => h b (List.mem_cons_of_mem a hb)))

private theorem scalar_power {A : Type} (f : A → Q') (M : Nat) : ∀ xs : List A,
    scalarProduct (fun a => qpow (f a) M) xs ≈ qpow (scalarProduct f xs) M
  | [] => Q'.eqv_symm (power_one M)
  | _::xs => Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (scalar_power f M xs))
      (Q'.eqv_symm (power_mul _ _ M))

/-- All supplied link occurrences, not a distinct-link approximation. -/
def linkPowerProduct (extent : Nat) (qs : Nat → UnitNorm) (M : Nat) (links : List Z4Link) : Q' :=
  scalarProduct (fun link => qpow (base (linkValue extent qs link)) M) links

theorem linkPowerProduct_nonnegative (extent : Nat) (qs : Nat → UnitNorm)
    (M : Nat) (links : List Z4Link) : (0 : Q') ≤ linkPowerProduct extent qs M links :=
  scalarProduct_nonnegative _ (fun _ => qpow_nonneg _ (base_bounds _).1 M) links

private theorem face_base_pin (extent id : Nat) (qs : Nat → UnitNorm) :
    scalarProduct (fun link => base (linkValue extent qs link))
      (edgesOf (slabPlaquetteAt extent id)) ≈ faceKernelProduct extent id qs := by
  let face := slabPlaquetteAt extent id
  let a := (dirsOf face.2).1
  let b := (dirsOf face.2).2
  let t0 := base (linkValue extent qs (face.1,a))
  let t1 := base (linkValue extent qs (addE face.1 a,b))
  let t2 := base (linkValue extent qs (addE face.1 b,a))
  let t3 := base (linkValue extent qs (face.1,b))
  change t0*(t3*(t2*(t1*1))) ≈ (t0*t1)*(t2*t3)
  exact poly_identity_of_normal_eq
    (.mul (.var 0) (.mul (.var 3) (.mul (.var 2) (.mul (.var 1) (.const 1)))))
    (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3))) (by decide)
    (fun | 0 => t0 | 1 => t1 | 2 => t2 | _ => t3)

private theorem face_power_pin (extent id : Nat) (qs : Nat → UnitNorm) (M : Nat) :
    linkPowerProduct extent qs M (edgesOf (slabPlaquetteAt extent id)) ≈
      qpow (faceKernelProduct extent id qs) M :=
  Q'.eqv_trans _ _ _ (scalar_power _ M _) (power_congr (face_base_pin extent id qs) M)

/-- Exact split of the scalar half-per-face cost and ALL four-edge powers. -/
theorem localizedProduct_recoding {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (qs : Nat → UnitNorm) : ∀ ids : List Nat,
    localizedProduct w hw0 hw1 K extent qs ids ≈ half^ids.length*
      linkPowerProduct extent qs (localizationDegree w hw0 hw1 K) (faceLinks extent ids)
  | [] => by change (1 : Q') ≈ 1*1; decide
  | id::ids => by
      refine Q'.eqv_trans _ _ _ (mc (Q'.eqv_refl _) (localizedProduct_recoding hw0 hw1 K extent qs ids))
        (Q'.eqv_trans _ _ _ ?_ (Q'.mul_eqv_congr_left _ _ _
          (Q'.eqv_symm (scalar_append _ _ _))))
      refine Q'.eqv_trans _ _ _ ?_ (Q'.mul_eqv_congr_left _ _ _
        (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm (face_power_pin extent id qs _))))
      exact poly_identity_of_normal_eq
        (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
        (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3))) (by decide)
        (fun | 0 => half | 1 => qpow (faceKernelProduct extent id qs) (localizationDegree w hw0 hw1 K)
             | 2 => half^ids.length | _ => linkPowerProduct extent qs (localizationDegree w hw0 hw1 K) (faceLinks extent ids))

private theorem map_range_getD {A : Type} (xs : List A) (fallback : A) :
    (List.range xs.length).map (fun k => xs.getD k fallback) = xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      simp only [List.length_cons]
      rw [List.range_succ_eq_map]
      simp only [List.map_cons,List.map_map]
      change a :: (List.range xs.length).map (fun k => xs.getD k fallback) = a::xs
      rw [ih]

private theorem indexed_product {A : Type} (links : List A) (fallback : A)
    (f : A → Q') (g : Nat → Q')
    (h : ∀ b, b ∈ List.range links.length → f (links.getD b fallback) ≈ g b) :
    scalarProduct f links ≈ scalarProduct g (List.range links.length) := by
  have hm := scalar_map (fun b => links.getD b fallback) f (List.range links.length)
  rw [map_range_getD] at hm
  rw [hm]
  exact scalar_congr _ h

private theorem indexed_value (links : List Z4Link) (hn : links.Nodup)
    (qs : Nat → UnitNorm) (b : Nat) (hb : b ∈ List.range links.length) :
    (if links.getD b SU2TorusRPThetaPoly.d0 ∈ links then
      qs (links.idxOf (links.getD b SU2TorusRPThetaPoly.d0)) else
      YMGap.RepTheory.RationalQuaternion.unitOne) = qs b := by
  have hb' := List.mem_range.mp hb
  have hm := SU2TorusRPThetaPoly.getD_mem (l := links) hb'
  rw [if_pos hm,SU2TorusRPThetaPoly.idxOf_getD links hn b hb']

/-- The literal ORIGINAL distinct carrier is exactly its indexed unit row,
not a newly selected family of independently assigned links. -/
theorem carrierProduct_index_pin (extent : Nat) (qs : Nat → UnitNorm) (M : Nat) :
    linkPowerProduct extent qs M (boundaryCompleteSlabLinks extent) ≈
      scalarProduct (fun b => qpow (base (qs b)) M)
        (List.range (boundaryCompleteSlabLinks extent).length) := by
  apply indexed_product _ SU2TorusRPThetaPoly.d0
  intro b hb
  have he := indexed_value (boundaryCompleteSlabLinks extent)
    (boundaryCompleteSlabLinks_nodup extent) qs b hb
  change linkValue extent qs _ = qs b at he
  exact Q'.eqv_of_eq (congrArg (fun q => qpow (base q) M) he)

/-- Physical selected face slots all belong to the original carrier. -/
theorem faceLinks_physical (extent : Nat) (ids : List Nat)
    (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent) :
    ∀ link, link ∈ faceLinks extent ids → link ∈ boundaryCompleteSlabLinks extent := by
  intro link hl
  obtain ⟨id,hid,hedge⟩ := List.mem_flatMap.mp hl
  exact (mem_boundaryCompleteSlabLinks_iff extent link).mpr
    ⟨slabPlaquetteAt extent id,slabPlaquetteAt_mem (hids id hid),hedge⟩

#print axioms linkPowerProduct
#print axioms linkPowerProduct_nonnegative
#print axioms localizedProduct_recoding
#print axioms carrierProduct_index_pin
#print axioms faceLinks_physical

end YMGap.Continuum.BF4ExactSlabKernelProductRecoding
