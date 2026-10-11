/-
# Complete ORIGINAL action pays selected face defects by its own entropy

Multiply each selected original one-face payment by ALL other original
factor occurrences. Unselected boundary factors remain in the complete
weight, but do not incur the selected log(3) or one-face error cost.
The literal finite entropy product defect then pays length(ids)/(N+1).

The weight is the existing identity-normalized original heat product, not
a new action or normalization by its partition. Repetitions, shared variables
and empty selections are allowed. This is pointwise finite coercivity, not
selected-Haar Jensen, OLD-centered relative payment, physical scaling or gap.
-/

import YMGap.Continuum.RegularizedLogFiniteProductCoercivity
import YMGap.Continuum.RegularizedLogDyadicFiniteDefect
import YMGap.Continuum.BF4ExactSlabHeatEntropyCoercivity
import YMGap.Continuum.BF4ExactSlabPolynomialActionLocalization

namespace YMGap.Continuum.BF4ExactSlabOriginalProductEntropyCoercivity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.RepTheory.RationalQuaternion (UnitNorm)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier (evalRatPoly)
open YMGap.Continuum.QuaternionHaarFiniteProductOrder (environment)
open YMGap.Continuum.BF4ExactSlabAllExtentFaceHeatTail (faceScalar)
open YMGap.Continuum.BF4ExactSlabNormalizedHeatBounds (normalizedHeatProduct)
open YMGap.Continuum.BF4ExactSlabPolynomialHeatLocalization
open YMGap.Continuum.BF4ExactSlabPolynomialActionLocalization
  (scalarProduct normalized_product_pin)
open YMGap.Continuum.BF4ExactSlabHeatEntropyCoercivity
open YMGap.Continuum.SU2HeatJacobiOriginalCoercivity (coercivityCutoff)
open YMGap.Continuum.SU2HeatJacobiActiveFactorCount (activeFactorCount)
open YMGap.Continuum.RegularizedLogPolynomial (partialSum)
open YMGap.Continuum.RegularizedLogFiniteCoercivity (third)
open YMGap.Continuum.RegularizedLogFiniteProduct (product)
open YMGap.Continuum.RegularizedLogFiniteProductCoercivity
  (selectedCount selectedDefectSum selected_product_payment)
open YMGap.Continuum.RegularizedLogDyadicFiniteDefect (partial_congr)
open YMGap.Continuum.RingNormaliser (PolyExpr poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv
private abbrev PE := PolyExpr
local instance : Add PE := ⟨.add⟩
local instance : Mul PE := ⟨.mul⟩
local instance : Neg PE := ⟨.neg⟩
local instance (n : Nat) : OfNat PE n := ⟨.const (Int.ofNat n)⟩

private theorem qr (a b : PE) (h : RingNormaliser.normalize a = RingNormaliser.normalize b)
    (rho : Nat → Q') : RingNormaliser.eval rho a ≈ RingNormaliser.eval rho b :=
  poly_identity_of_normal_eq a b h rho

private theorem tc {a b c : Q'} (h : a ≈ b) (k : b ≈ c) : a ≈ c :=
  Q'.eqv_trans _ _ _ h k

/-- Literal original plaquette defect on the SAME shared assignment. -/
def faceDefect (extent : Nat) (qs : Nat → UnitNorm) (id : Nat) : Q' :=
  1-evalRatPoly (environment qs) (faceScalar extent id)

private theorem map_product_eq {A : Type} (f : A → Q') : ∀ ids : List A,
    product (ids.map f) = scalarProduct f ids
  | [] => rfl
  | a::ids => by simp only [List.map_cons, product, scalarProduct, map_product_eq f ids]

/-- The weighted finite-product producer uses the literal complete ORIGINAL
identity-normalized action, with every supplied occurrence retained. -/
theorem normalized_product_map_pin {q : Q'} (hq0 : (0 : Q') < q)
    (K extent : Nat) (ids : List Nat) (qs : Nat → UnitNorm) :
    product (ids.map (fun id => normalizedFace q hq0 K extent id qs)) ≈
      evalRatPoly (environment qs) (normalizedHeatProduct q hq0 K extent ids) := by
  rw [map_product_eq]
  exact normalized_product_pin hq0 K extent ids qs

/-- Complete-action finite entropy payment. Only selected occurrences incur
the log(3) and one-face error terms; ALL occurrences remain in the density.
N is the independent entropy cutoff, and its count-dependent error is explicit. -/
theorem original_selected_product_coercivity_finite {q : Q'}
    (hq0 : (0 : Q') < q) (hq : Q'.mkPos 16 17 (by decide) ≤ q)
    (hq1 : q < (1 : Q')) (K extent : Nat) (ids : List Nat)
    (selected : Nat → Bool) (qs : Nat → UnitNorm)
    (hK : coercivityCutoff q ≤ K+1) (N : Nat) (hN : 1 ≤ N) :
    evalRatPoly (environment qs) (normalizedHeatProduct q hq0 K extent ids)*
        selectedDefectSum (faceDefect extent qs) selected ids ≤
      (256*(1-q))*(
        partialSum (evalRatPoly (environment qs) (normalizedHeatProduct q hq0 K extent ids)) N+
        (3*partialSum third N)*Q'.ofNat (selectedCount selected ids)*
          evalRatPoly (environment qs) (normalizedHeatProduct q hq0 K extent ids)+
        (Q'.ofNat ids.length+3*Q'.ofNat (activeFactorCount q-1)*
          Q'.ofNat (selectedCount selected ids))*Q'.invSucc N) := by
  let f := fun id => normalizedFace q hq0 K extent id qs
  let W := evalRatPoly (environment qs) (normalizedHeatProduct q hq0 K extent ids)
  let c := (256 : Q')*(1-q)
  let b := (3 : Q')*partialSum third N
  let e := (3*Q'.ofNat (activeFactorCount q-1))*Q'.invSucc N
  let F := Q'.ofNat (selectedCount selected ids)
  have hKf : SU2PointwiseHeatStrictFloor.finiteCutoff q ≤ K+1 :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hK
  have hf : ∀ id, id ∈ ids → (0 : Q') ≤ f id ∧ f id ≤ 1 := by
    intro id _
    exact ⟨Q'.le_trans' _ _ _ (Q'.le_of_lt (eta_positive hq0 hq1 K))
      (normalizedFace_floor hq0 hq1 K extent id qs hKf),
      normalizedFace_upper hq0 K extent id qs⟩
  have hc : (0 : Q') ≤ c := Q'.mul_nonneg _ _ (by decide)
    (Q'.le_of_lt (HKPos.one_sub_pos hq1))
  have he : (0 : Q') ≤ e := Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _ (by decide) (ClusterCount.ofNat_nonneg _)) (Q'.invSucc_nonneg N)
  have hlocal : ∀ id, id ∈ ids → selected id = true →
      f id*faceDefect extent qs id ≤ c*(partialSum (f id) N+b*f id+e) := by
    intro id _ _
    have hh := original_face_coercivity_finite hq0 hq hq1 K extent id qs hK N hN
    have hpin : c*(partialSum (f id) N+3*f id*partialSum third N+e) ≈
        c*(partialSum (f id) N+b*f id+e) :=
      Q'.mul_eqv_congr_left _ _ _
        (qr ((.var 0+(3*.var 1)*.var 2)+.var 3)
          ((.var 0+(3*.var 2)*.var 1)+.var 3) (by decide)
          (fun | 0 => partialSum (f id) N | 1 => f id | 2 => partialSum third N | _ => e))
    exact Q'.le_trans' _ _ _ hh (Q'.le_of_eqv hpin)
  have hj := selected_product_payment f (faceDefect extent qs) selected N ids hf c b e hc he hlocal
  have hP := normalized_product_map_pin hq0 K extent ids qs
  have hpN := partial_congr hP N
  have hweighted := Q'.mul_eqv_congr_left (b*F) _ _ hP
  have hR : c*(partialSum (product (ids.map f)) N+Q'.ofNat ids.length*Q'.invSucc N+
        b*F*product (ids.map f)+e*F) ≈
      c*(partialSum W N+Q'.ofNat ids.length*Q'.invSucc N+b*F*W+e*F) :=
    Q'.mul_eqv_congr_left _ _ _
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr' (Q'.add_eqv_congr' hpN (Q'.eqv_refl _)) hweighted)
        (Q'.eqv_refl _))
  have hcollect : c*(partialSum W N+Q'.ofNat ids.length*Q'.invSucc N+b*F*W+e*F) ≈
      c*(partialSum W N+b*F*W+
        (Q'.ofNat ids.length+3*Q'.ofNat (activeFactorCount q-1)*F)*Q'.invSucc N) :=
    Q'.mul_eqv_congr_left _ _ _
      (qr (((.var 0+.var 1*.var 2)+.var 3*.var 4*.var 5)+
          ((3*.var 6)*.var 2)*.var 4)
        ((.var 0+.var 3*.var 4*.var 5)+(.var 1+(3*.var 6)*.var 4)*.var 2)
        (by decide)
        (fun | 0 => partialSum W N | 1 => Q'.ofNat ids.length | 2 => Q'.invSucc N
             | 3 => b | 4 => F | 5 => W | _ => Q'.ofNat (activeFactorCount q-1)))
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (Q'.mul_eqv_congr_right _ _ _ hP))
    (Q'.le_trans' _ _ _ hj (Q'.le_of_eqv (tc hR hcollect)))

end YMGap.Continuum.BF4ExactSlabOriginalProductEntropyCoercivity

#print axioms YMGap.Continuum.BF4ExactSlabOriginalProductEntropyCoercivity.faceDefect
#print axioms YMGap.Continuum.BF4ExactSlabOriginalProductEntropyCoercivity.normalized_product_map_pin
#print axioms YMGap.Continuum.BF4ExactSlabOriginalProductEntropyCoercivity.original_selected_product_coercivity_finite
