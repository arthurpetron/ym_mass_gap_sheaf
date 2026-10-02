/-
# Fixed-cutoff block degree of the ORIGINAL kinetic layer

Each original temporal face couples one distinct lower spatial link to its
upper copy. Its retained heat polynomial has degree at most the spin cutoff
in either link block. Consequently the complete original kinetic factor has
degree at most K in EVERY physical lower/upper block, independently of width
and terminal depth. This is a syntactic degree ceiling, not a coefficient-count,
runtime, scaling, or useful-margin estimate.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals
import YMGap.Continuum.SU2QuaternionBlockDegreeBound

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialKineticDegree

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricSpinNetworkMehler (characterPolynomial)
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation (finitePolySum)
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization (polynomialProduct)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals
  (activeBlocks activeBlocks_lt activeBlocks_nodup kineticWeight_eq_indexedProduct)
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
  (scalarAt heatAt heat_independent)
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
  (HasQuaternionBlockDegree hasPolyQuaternionBlockDegree_coordinateVariable)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionBlockDegreeBound

local notation:max "N" width:arg => List.length (baseLinks width)

private theorem exact_degree_le {block d : Nat} {p : RatPoly}
    (hp : HasQuaternionBlockDegree block d p) : DegreeLE block d p :=
  fun term ht => Nat.le_of_eq (hp term ht)

private theorem scalarAt_left_degree (a b : Nat) (hab : a ≠ b) :
    DegreeLE a 1 (scalarAt a b) := by
  have h := ((hasPolyQuaternionBlockDegree_coordinateVariable a a).mul
    ((hasPolyQuaternionBlockDegree_coordinateVariable b a).conj)).scalar
  exact exact_degree_le (by simpa [scalarAt, hab] using h)

private theorem scalarAt_right_degree (a b : Nat) (hab : a ≠ b) :
    DegreeLE b 1 (scalarAt a b) := by
  have h := ((hasPolyQuaternionBlockDegree_coordinateVariable a b).mul
    ((hasPolyQuaternionBlockDegree_coordinateVariable b b).conj)).scalar
  exact exact_degree_le (by simpa [scalarAt, Ne.symm hab] using h)

/-- A degree-one scalar produces at most spin degree in each character.
Chebyshev's lower-degree summand is retained, not homogenized away. -/
theorem characterPolynomial_degree_le (block : Nat) (scalar : RatPoly)
    (hs : DegreeLE block 1 scalar) : ∀ spin : Nat,
    DegreeLE block spin (characterPolynomial scalar spin)
  | 0 => DegreeLE.one block 0
  | 1 => by simpa only [characterPolynomial] using hs.smul 2
  | spin + 2 => by
      have hhigh := (hs.smul 2).mul
        (characterPolynomial_degree_le block scalar hs (spin+1))
      have hlow := (characterPolynomial_degree_le block scalar hs spin).smul (-1)
      simpa only [characterPolynomial] using
        (hhigh.mono (by omega : 1+(spin+1) ≤ spin+2)).add
          (hlow.mono (by omega : spin ≤ spin+2))

private theorem finitePolySum_degree_le {A : Type} (block d : Nat)
    (f : A → RatPoly) : ∀ xs : List A,
      (∀ x, x ∈ xs → DegreeLE block d (f x)) →
      DegreeLE block d (finitePolySum f xs)
  | [], _ => by
      intro term ht
      exact False.elim (List.not_mem_nil ht)
  | x :: xs, h => by
      change DegreeLE block d (polyAdd (f x) (finitePolySum f xs))
      exact (h x List.mem_cons_self).add
        (finitePolySum_degree_le block d f xs
          (fun y hy => h y (List.mem_cons_of_mem x hy)))

/-- One retained heat factor has no more than K powers in its lower link. -/
theorem heatAt_degree_left (a b : Nat) (hab : a ≠ b) (w : Q') (K : Nat) :
    DegreeLE a K (heatAt a b w K) := by
  unfold heatAt
  apply finitePolySum_degree_le
  intro spin hspin
  have hs : spin ≤ K := by have := List.mem_range.mp hspin; omega
  exact ((characterPolynomial_degree_le a (scalarAt a b)
    (scalarAt_left_degree a b hab) spin).smul _).mono hs

/-- The same cutoff bounds the upper link block. -/
theorem heatAt_degree_right (a b : Nat) (hab : a ≠ b) (w : Q') (K : Nat) :
    DegreeLE b K (heatAt a b w K) := by
  unfold heatAt
  apply finitePolySum_degree_le
  intro spin hspin
  have hs : spin ≤ K := by have := List.mem_range.mp hspin; omega
  exact ((characterPolynomial_degree_le b (scalarAt a b)
    (scalarAt_right_degree a b hab) spin).smul _).mono hs

private theorem heatAt_degree_off (block a b : Nat) (ha : block ≠ a)
    (hb : block ≠ b) (w : Q') (K : Nat) :
    DegreeLE block 0 (heatAt a b w K) :=
  exact_degree_le (heat_independent block a b ha hb w K)

private theorem indexed_off_degree (n block : Nat) (w : Q') (K : Nat) :
    ∀ ids : List Nat,
      (∀ i, i ∈ ids → block ≠ i ∧ block ≠ n+i) →
      DegreeLE block 0
        (polynomialProduct (fun i => heatAt i (n+i) w K) ids)
  | [], _ => DegreeLE.one block 0
  | i :: ids, h => by
      change DegreeLE block 0
        (polyMul (heatAt i (n+i) w K)
          (polynomialProduct (fun j => heatAt j (n+j) w K) ids))
      have hi := h i List.mem_cons_self
      have hrest := indexed_off_degree n block w K ids
        (fun j hj => h j (List.mem_cons_of_mem i hj))
      simpa only [Nat.zero_add] using
        (heatAt_degree_off block i (n+i) hi.1 hi.2 w K).mul hrest

private theorem indexed_upper_degree (n : Nat) (w : Q') (K : Nat) :
    ∀ ids : List Nat, ids.Nodup → (∀ i, i ∈ ids → i < n) →
      ∀ slot, slot < n →
      DegreeLE (n+slot) K
        (polynomialProduct (fun i => heatAt i (n+i) w K) ids)
  | [], _, _, _, _ => DegreeLE.one _ _
  | i :: ids, hnd, hit, slot, hslot => by
      have hi : i < n := hit i List.mem_cons_self
      have hndi := List.nodup_cons.mp hnd
      have hitail (j : Nat) (hj : j ∈ ids) : j < n :=
        hit j (List.mem_cons_of_mem i hj)
      change DegreeLE (n+slot) K
        (polyMul (heatAt i (n+i) w K)
          (polynomialProduct (fun j => heatAt j (n+j) w K) ids))
      by_cases hsi : slot = i
      · subst slot
        have hrest : ∀ j, j ∈ ids → n+i ≠ j ∧ n+i ≠ n+j := by
          intro j hj
          have hjlt := hitail j hj
          have hneq : i ≠ j := by
            intro he
            subst j
            exact hndi.1 hj
          constructor <;> omega
        have ht := indexed_off_degree n (n+i) w K ids hrest
        simpa only [Nat.add_zero] using
          (heatAt_degree_right i (n+i) (by omega) w K).mul ht
      · have hhead : DegreeLE (n+slot) 0 (heatAt i (n+i) w K) :=
          heatAt_degree_off (n+slot) i (n+i) (by omega) (by omega) w K
        have ht := indexed_upper_degree n w K ids hndi.2 hitail slot hslot
        simpa only [Nat.zero_add] using hhead.mul ht

private theorem indexed_lower_degree (n : Nat) (w : Q') (K : Nat) :
    ∀ ids : List Nat, ids.Nodup → (∀ i, i ∈ ids → i < n) →
      ∀ slot, slot < n →
      DegreeLE slot K
        (polynomialProduct (fun i => heatAt i (n+i) w K) ids)
  | [], _, _, _, _ => DegreeLE.one _ _
  | i :: ids, hnd, hit, slot, hslot => by
      have hi : i < n := hit i List.mem_cons_self
      have hndi := List.nodup_cons.mp hnd
      have hitail (j : Nat) (hj : j ∈ ids) : j < n :=
        hit j (List.mem_cons_of_mem i hj)
      change DegreeLE slot K
        (polyMul (heatAt i (n+i) w K)
          (polynomialProduct (fun j => heatAt j (n+j) w K) ids))
      by_cases hsi : slot = i
      · subst slot
        have hrest : ∀ j, j ∈ ids → i ≠ j ∧ i ≠ n+j := by
          intro j hj
          have hjlt := hitail j hj
          have hneq : i ≠ j := by
            intro he
            subst j
            exact hndi.1 hj
          constructor <;> omega
        have ht := indexed_off_degree n i w K ids hrest
        simpa only [Nat.add_zero] using
          (heatAt_degree_left i (n+i) (by omega) w K).mul ht
      · have hhead : DegreeLE slot 0 (heatAt i (n+i) w K) :=
          heatAt_degree_off slot i (n+i) hsi (by omega) w K
        have ht := indexed_lower_degree n w K ids hndi.2 hitail slot hslot
        simpa only [Nat.zero_add] using hhead.mul ht

/-- At every original lower physical block, the complete kinetic product
retains degree at most the finite spin cutoff. -/
theorem kineticWeight_lower_degree (w : Q') (K width : Nat) (slot : Nat)
    (hslot : slot < N width) :
    DegreeLE slot K (kineticWeight w K width) := by
  rw [kineticWeight_eq_indexedProduct]
  exact indexed_lower_degree (N width) w K (activeBlocks width)
    (activeBlocks_nodup width) (activeBlocks_lt width) slot hslot

/-- The analogous sharp bound in the upper copy, used by the original
terminal-message degree reset. -/
theorem kineticWeight_upper_degree (w : Q') (K width : Nat) (slot : Nat)
    (hslot : slot < N width) :
    DegreeLE (N width+slot) K (kineticWeight w K width) := by
  rw [kineticWeight_eq_indexedProduct]
  exact indexed_upper_degree (N width) w K (activeBlocks width)
    (activeBlocks_nodup width) (activeBlocks_lt width) slot hslot

#print axioms characterPolynomial_degree_le
#print axioms heatAt_degree_left
#print axioms heatAt_degree_right
#print axioms kineticWeight_lower_degree
#print axioms kineticWeight_upper_degree

end YMGap.Continuum.BF4ExactSlabFixedSpatialKineticDegree
