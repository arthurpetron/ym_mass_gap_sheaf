/-
# The SAME spectator partition fourth power in an original face response

Both probes and the inserted face lie on the core side of an explicit
disjoint split. The original response acquires exactly Z_spectator^4,
and its original two-endpoint denominator acquires the SAME factor.
Finite inclusion-exclusion factors with that original partition polynomial.

The statement is valid at every rational nome and cutoff, before positivity
or division. It is an exact signed factorization, not a bound on the rooted
response, spatial decay, or a physical spectral gap.
-/

import YMGap.Continuum.BF4ExactSlabThreeMarkResponseExpansion
import YMGap.Continuum.BF4ExactSlabSpectatorResummation

namespace YMGap.Continuum.BF4ExactSlabResponseSpectatorFactorization

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabAllExtentActionLimit
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabSelectionSeparation
open YMGap.Continuum.BF4ExactSlabDisconnectedHaarCancellation
open YMGap.Continuum.BF4ExactSlabConnectedSelectionExpansion
open YMGap.Continuum.BF4ExactSlabSpectatorResummation
open YMGap.Continuum.BF4ExactSlabConnectedFaceResponse
open YMGap.Continuum.BF4ExactSlabThreeMarkResponseExpansion
open YMGap.Continuum.FinitePolynomialSubsetExpansion
open YMGap.Continuum.FiniteSelectionMobius
open YMGap.Continuum.FiniteSelectionMobiusFactorization
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv
local notation:max "blocks" extent:max => List.length (boundaryCompleteSlabLinks extent)

def partitionFourth (w : Q') (K extent : Nat) (ids : List Nat) : Q' :=
  let Z := heatProductHaar w (blocks extent) extent ids K
  (Z*Z)*(Z*Z)

private theorem qmul {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h) (Q'.mul_eqv_congr_left _ _ _ k)

private theorem partition_perm (w : Q') (K extent : Nat) {xs ys : List Nat} (h : xs.Perm ys) :
    heatProductHaar w (blocks extent) extent xs K ≈ heatProductHaar w (blocks extent) extent ys K :=
  haar_of_coeff (polynomialProduct_perm (faceHeatPolynomial w K extent) h)

/-- Permutation preserves the actual response, including the two partitions. -/
theorem response_perm (w : Q') (K extent : Nat) {xs ys : List Nat}
    (h : xs.Perm ys) (id : Nat) (p q : RatPoly) :
    response w K extent xs id p q ≈ response w K extent ys id p q := by
  have hz := partition_perm w K extent h
  have hr := partition_perm w K extent (h.append_right [id])
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (response_identity w K extent xs id p q))
    (Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr'
        (qmul (connectedNumerator_perm w K extent (h.append_right [id]) p q) (qmul hz hz))
        (Q'.neg_eqv_congr _ _ (qmul (connectedNumerator_perm w K extent h p q) (qmul hr hr))))
      (response_identity w K extent ys id p q))

private theorem insertion_perm (core spectators : List Nat) (id : Nat) :
    ((core++spectators)++[id]).Perm ((core++[id])++spectators) := by
  simpa only [List.append_assoc] using
    (List.perm_append_comm (l₁ := spectators) (l₂ := [id])).append_left core

private theorem inserted_core_disjoint (extent : Nat) (roots : List Z4Link)
    (core spectators : List Nat) (id : Nat)
    (hface : ∀ link, link ∈ edgesOf (slabPlaquetteAt extent id) → link ∈ roots)
    (hd : LinksDisjoint (roots++faceLinks extent core) (faceLinks extent spectators)) :
    LinksDisjoint (roots++faceLinks extent (core++[id])) (faceLinks extent spectators) := by
  intro link hleft hright
  apply hd link _ hright
  rcases List.mem_append.mp hleft with hroot | hfaces
  · exact List.mem_append.mpr (Or.inl hroot)
  · obtain ⟨face, hfaceMem, hedge⟩ := List.mem_flatMap.mp hfaces
    rcases List.mem_append.mp hfaceMem with hcore | hnew
    · exact List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr ⟨face, hcore, hedge⟩))
    · have heq : face = id := List.mem_singleton.mp hnew
      subst face
      exact List.mem_append.mpr (Or.inl (hface link hedge))

private theorem endpoint_partitions (w : Q') (K extent : Nat) (roots : List Z4Link)
    (core spectators : List Nat) (id : Nat)
    (hface : ∀ link, link ∈ edgesOf (slabPlaquetteAt extent id) → link ∈ roots)
    (hd : LinksDisjoint (roots++faceLinks extent core) (faceLinks extent spectators)) :
    (heatProductHaar w (blocks extent) extent (core++spectators) K ≈
      heatProductHaar w (blocks extent) extent core K * heatProductHaar w (blocks extent) extent spectators K) ∧
    (heatProductHaar w (blocks extent) extent ((core++spectators)++[id]) K ≈
      heatProductHaar w (blocks extent) extent (core++[id]) K * heatProductHaar w (blocks extent) extent spectators K) := by
  have hnew := inserted_core_disjoint extent roots core spectators id hface hd
  exact ⟨partition_factorizes w K extent core spectators
      (fun link hl hr => hd link (List.mem_append.mpr (Or.inr hl)) hr),
    Q'.eqv_trans _ _ _ (partition_perm w K extent (insertion_perm core spectators id))
      (partition_factorizes w K extent (core++[id]) spectators
        (fun link hl hr => hnew link (List.mem_append.mpr (Or.inr hl)) hr))⟩

/-- Both endpoint connected numerators carry the spectator square; together
with their partition squares this is exactly the original fourth power. -/
theorem response_spectator_factorizes (w : Q') (K extent : Nat) (p q : RatPoly)
    (roots : List Z4Link)
    (hp : SupportedQuaternionBlocks (blocks extent) p)
    (hq : SupportedQuaternionBlocks (blocks extent) q)
    (hlp : LinkLocal extent roots p) (hlq : LinkLocal extent roots q)
    (core spectators : List Nat) (id : Nat)
    (hface : ∀ link, link ∈ edgesOf (slabPlaquetteAt extent id) → link ∈ roots)
    (hd : LinksDisjoint (roots++faceLinks extent core) (faceLinks extent spectators)) :
    response w K extent (core++spectators) id p q ≈
      response w K extent core id p q * partitionFourth w K extent spectators := by
  have hnew := inserted_core_disjoint extent roots core spectators id hface hd
  have hcold := numerator_spectator_factorizes w K extent p q roots hp hq hlp hlq core spectators hd
  have hcnew := Q'.eqv_trans _ _ _
    (connectedNumerator_perm w K extent (insertion_perm core spectators id) p q)
    (numerator_spectator_factorizes w K extent p q roots hp hq hlp hlq (core++[id]) spectators hnew)
  have hz := endpoint_partitions w K extent roots core spectators id hface hd
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (response_identity w K extent (core++spectators) id p q)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (qmul hcnew (qmul hz.1 hz.1))
      (Q'.neg_eqv_congr _ _ (qmul hcold (qmul hz.2 hz.2)))) ?_
  refine Q'.eqv_trans _ _ _ ?_
    (Q'.mul_eqv_congr_right _ _ _ (response_identity w K extent core id p q))
  exact poly_identity_of_normal_eq
    (.add
      (.mul (.mul (.var 0) (.mul (.var 4) (.var 4)))
        (.mul (.mul (.var 2) (.var 4)) (.mul (.var 2) (.var 4))))
      (.neg (.mul (.mul (.var 1) (.mul (.var 4) (.var 4)))
        (.mul (.mul (.var 3) (.var 4)) (.mul (.var 3) (.var 4))))))
    (.mul
      (.add (.mul (.var 0) (.mul (.var 2) (.var 2)))
        (.neg (.mul (.var 1) (.mul (.var 3) (.var 3)))))
      (.mul (.mul (.var 4) (.var 4)) (.mul (.var 4) (.var 4))))
    (by decide) (fun
      | 0 => connectedNumerator w K extent (core++[id]) p q
      | 1 => connectedNumerator w K extent core p q
      | 2 => heatProductHaar w (blocks extent) extent core K
      | 3 => heatProductHaar w (blocks extent) extent (core++[id]) K
      | _ => heatProductHaar w (blocks extent) extent spectators K)

/-- The two DIFFERENT endpoint partitions retain the SAME spectator factor. -/
theorem denominator_spectator_factorizes (w : Q') (K extent : Nat) (roots : List Z4Link)
    (core spectators : List Nat) (id : Nat)
    (hface : ∀ link, link ∈ edgesOf (slabPlaquetteAt extent id) → link ∈ roots)
    (hd : LinksDisjoint (roots++faceLinks extent core) (faceLinks extent spectators)) :
    responseDenominator w K extent (core++spectators) id ≈
      responseDenominator w K extent core id * partitionFourth w K extent spectators := by
  have hz := endpoint_partitions w K extent roots core spectators id hface hd
  refine Q'.eqv_trans _ _ _ (qmul (qmul hz.2 hz.2) (qmul hz.1 hz.1)) ?_
  exact poly_identity_of_normal_eq
    (.mul (.mul (.mul (.var 0) (.var 2)) (.mul (.var 0) (.var 2)))
      (.mul (.mul (.var 1) (.var 2)) (.mul (.var 1) (.var 2))))
    (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1)))
      (.mul (.mul (.var 2) (.var 2)) (.mul (.var 2) (.var 2))))
    (by decide) (fun
      | 0 => heatProductHaar w (blocks extent) extent (core++[id]) K
      | 1 => heatProductHaar w (blocks extent) extent core K
      | _ => heatProductHaar w (blocks extent) extent spectators K)

/-- Exact finite differences factor before any absolute value is taken. -/
theorem responseCoefficient_spectator_factorizes (w : Q') (K extent : Nat) (p q : RatPoly)
    (roots : List Z4Link)
    (hp : SupportedQuaternionBlocks (blocks extent) p)
    (hq : SupportedQuaternionBlocks (blocks extent) q)
    (hlp : LinkLocal extent roots p) (hlq : LinkLocal extent roots q)
    (core spectators : List Nat) (id : Nat)
    (hface : ∀ link, link ∈ edgesOf (slabPlaquetteAt extent id) → link ∈ roots)
    (hd : LinksDisjoint (roots++faceLinks extent core) (faceLinks extent spectators)) :
    responseCoefficient w K extent id p q (core++spectators) ≈
      responseCoefficient w K extent id p q core * coefficient (partitionFourth w K extent) spectators :=
  coefficient_factorizes _ _ _ core spectators (fun a ha b hb =>
    response_spectator_factorizes w K extent p q roots hp hq hlp hlq a b id hface
      (disjoint_subfaces hd (fun i hi => selected_mem ha i hi) (fun i hi => selected_mem hb i hi)))

end YMGap.Continuum.BF4ExactSlabResponseSpectatorFactorization

#print axioms YMGap.Continuum.BF4ExactSlabResponseSpectatorFactorization.partitionFourth
#print axioms YMGap.Continuum.BF4ExactSlabResponseSpectatorFactorization.response_perm
#print axioms YMGap.Continuum.BF4ExactSlabResponseSpectatorFactorization.response_spectator_factorizes
#print axioms YMGap.Continuum.BF4ExactSlabResponseSpectatorFactorization.denominator_spectator_factorizes
#print axioms YMGap.Continuum.BF4ExactSlabResponseSpectatorFactorization.responseCoefficient_spectator_factorizes
