/-
# Torus RP assembly (d3d), item 3 step 2: factorising the Wilson product into the two halves and the crossing part

* `prod_append`: `Π_{xs++ys} F ≈PE Π_xs F · Π_ys F`.
* `prod_perm`: `Π F` is invariant under list permutation, up to PE.
* `torus_factor`: if the plaquettes `ps` are a permutation of `pos ++ pos.map mir ++ cross`, then
  `Π_{ps} TK ≈PE (Wp · thetaPoly Wp) · Wc`, where `Wp = Π_{pos} TK` and `Wc = Π_{cross} TK`.
  This is the `hW` shape, with the geometric Θpoly in place of `shiftPoly`.

**RP FOR THE ACTUAL TORUS MEASURE IS OPEN** (still to do: replacing Θpoly by `shiftPoly` on the full layout, which
needs the crossing split and the half-only conj; showing the crossing part is RPK; and the final `hW`).
-/

import YMGap.Continuum.SU2TorusRPThetaShift

namespace YMGap.Continuum.SU2TorusRPFactor

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2HaarAlgebra (PE pe_trans pe_symm pe_refl pe_mulL pe_mulR pe_comm pe_assoc)
open YMGap.Continuum.SU2HaarL1Activity (prodPoly)
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4TorusGeometry
open YMGap.Continuum.SU2PlaqSupport (plaqLinks)
open YMGap.Continuum.SU2TorusRPGeom (reflLink)
open YMGap.Continuum.SU2TorusRPThetaTK (thetaPoly)
open YMGap.Continuum.SU2TorusRPThetaProd (mir theta_prod)

section
variable (n : Nat) (F : Z4Plaq → RatPoly)

theorem prod_append : ∀ xs ys : List Z4Plaq,
    PE n (prodPoly F (xs ++ ys)) (polyMul (prodPoly F xs) (prodPoly F ys))
  | [], ys => pe_symm n (SU2TorusRPHeadSub.pe_one_mul n _)
  | x :: xs, ys => pe_trans n (pe_mulL n (F x) (prod_append xs ys)) (pe_symm n (pe_assoc n _ _ _))

theorem pe_swap3 (A B C : RatPoly) : PE n (polyMul A (polyMul B C)) (polyMul B (polyMul A C)) :=
  pe_trans n (pe_symm n (pe_assoc n _ _ _)) (pe_trans n (pe_mulR n _ (pe_comm n _ _)) (pe_assoc n _ _ _))

theorem prod_perm {xs ys : List Z4Plaq} (h : xs.Perm ys) : PE n (prodPoly F xs) (prodPoly F ys) := by
  induction h with
  | nil => exact pe_refl n _
  | cons x _ ih => exact pe_mulL n (F x) ih
  | swap x y l => exact pe_swap3 n _ _ _
  | trans _ _ ih1 ih2 => exact pe_trans n ih1 ih2
end

variable {M : Nat} (hM : 1 ≤ M) (links : List Z4Link) (hnd : links.Nodup)
  (hbox : ∀ ℓ ∈ links, InBox (2 * M) ℓ.1) (hcl : ∀ ℓ ∈ links, reflLink M ℓ ∈ links) (β : Q') (K : Nat)

/-- **Factorisation** of the torus Wilson product into the positive half, its Θ-image, and the crossing part. -/
theorem torus_factor (ps pos cross : List Z4Plaq) (hperm : ps.Perm (pos ++ pos.map (mir M) ++ cross))
    (hpos : ∀ p ∈ pos, p.1.1 < 2 * M ∧ ∀ ℓ ∈ plaqLinks (2 * M) p, ℓ ∈ links) :
    PE links.length (prodPoly (SU2WilsonPolymerIdentity.TK links (2 * M) β K) ps)
      (polyMul (polyMul (prodPoly (SU2WilsonPolymerIdentity.TK links (2 * M) β K) pos)
          (thetaPoly hM links hnd hbox hcl (prodPoly (SU2WilsonPolymerIdentity.TK links (2 * M) β K) pos)))
        (prodPoly (SU2WilsonPolymerIdentity.TK links (2 * M) β K) cross)) := by
  refine pe_trans _ (prod_perm _ _ hperm) (pe_trans _ (prod_append _ _ _ _) (pe_mulR _ _ ?_))
  refine pe_trans _ (prod_append _ _ _ _) (pe_mulL _ _ ?_)
  exact pe_symm _ (theta_prod hM links hnd hbox hcl β K pos hpos)

end YMGap.Continuum.SU2TorusRPFactor

#print axioms YMGap.Continuum.SU2TorusRPFactor.prod_perm
#print axioms YMGap.Continuum.SU2TorusRPFactor.torus_factor
