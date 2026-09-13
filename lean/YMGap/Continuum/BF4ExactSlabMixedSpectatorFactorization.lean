/-
# Mixed ORIGINAL spectator factorization rooted only at the probe

Both original moment products split across the SAME literal disjoint-link
cut. The determinant keeps the mixed spectator factor Z_all * Z_inside.
Exterior spectator faces occur in the first factor only; they do not enlarge
the probe root. Finite differences inherit the exact factorization.
-/

import YMGap.Continuum.BF4ExactSlabMixedAction
import YMGap.Continuum.BF4ExactSlabRootedSelection

namespace YMGap.Continuum.BF4ExactSlabMixedSpectatorFactorization

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (PolyExpr poly_identity_of_normal_eq)
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabAllExtentActionLimit
open YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabDisconnectedHaarCancellation
open YMGap.Continuum.BF4ExactSlabSpectatorResummation
open YMGap.Continuum.BF4ExactSlabMixedAction
open YMGap.Continuum.BF4ExactSlabRootedSelection
open YMGap.Continuum.FinitePolynomialSubsetExpansion
open YMGap.Continuum.FiniteSelectionMobiusFactorization
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

private theorem qmul {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h) (Q'.mul_eqv_congr_left _ _ _ k)

section Local

variable (w : Q') (K extent : Nat) (keep : Nat → Bool) (p : RatPoly) (links : List Z4Link)
  (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length p)
  (hl : LinkLocal extent links p)

include hp hl

theorem mixedNumerator_factorizes (anchor extra : List Nat)
    (hd : LinksDisjoint (links++faceLinks extent anchor) (faceLinks extent extra)) :
    mixedNumerator w K extent keep p (anchor++extra) ≈
      mixedNumerator w K extent keep p anchor * mixedPartition w K extent keep extra := by
  have hi : LinksDisjoint (links++faceLinks extent (inside keep anchor)) (faceLinks extent (inside keep extra)) :=
    disjoint_subfaces hd (fun _ h => (List.mem_filter.mp h).1) (fun _ h => (List.mem_filter.mp h).1)
  have hn := left_moment_factorizes w K extent anchor extra links [] hd p hp hl
  have hni := left_moment_factorizes w K extent (inside keep anchor) (inside keep extra) links [] hi p hp hl
  have hz := partition_factorizes w K extent anchor extra (fun link ha he => hd link (List.mem_append.mpr (Or.inr ha)) he)
  have hzi := partition_factorizes w K extent (inside keep anchor) (inside keep extra)
    (fun link ha he => hi link (List.mem_append.mpr (Or.inr ha)) he)
  simp only [mixedNumerator, inside, List.filter_append]
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (qmul hn hzi) (Q'.neg_eqv_congr _ _ (qmul hni hz))) ?_
  exact poly_identity_of_normal_eq
    (.add (.mul (.mul (.var 0) (.var 4)) (.mul (.var 1) (.var 5)))
      (.neg (.mul (.mul (.var 2) (.var 5)) (.mul (.var 3) (.var 4)))))
    (.mul (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 2) (.var 3)))) (.mul (.var 4) (.var 5))) (by decide)
    (fun i => if i = 0 then numerator w (boundaryCompleteSlabLinks extent).length extent anchor p K
      else if i = 1 then heatProductHaar w (boundaryCompleteSlabLinks extent).length extent (inside keep anchor) K
      else if i = 2 then numerator w (boundaryCompleteSlabLinks extent).length extent (inside keep anchor) p K
      else if i = 3 then heatProductHaar w (boundaryCompleteSlabLinks extent).length extent anchor K
      else if i = 4 then heatProductHaar w (boundaryCompleteSlabLinks extent).length extent extra K
      else heatProductHaar w (boundaryCompleteSlabLinks extent).length extent (inside keep extra) K)

theorem mixedCoefficient_factorizes (anchor extra : List Nat)
    (hd : LinksDisjoint (links++faceLinks extent anchor) (faceLinks extent extra)) :
    mixedCoefficient w K extent keep p (anchor++extra) ≈
      mixedCoefficient w K extent keep p anchor * mixedPartitionCoefficient w K extent keep extra :=
  coefficient_factorizes _ _ _ anchor extra (fun a ha b hb =>
    mixedNumerator_factorizes w K extent keep p links hp hl a b
      (disjoint_subfaces hd (fun id hi => selected_mem ha id hi) (fun id hi => selected_mem hb id hi)))

theorem mixedCoefficient_rooted_pin (ids : List Nat) :
    mixedCoefficient w K extent keep p ids ≈ mixedCoefficient w K extent keep p (core extent links ids) *
      mixedPartitionCoefficient w K extent keep (spectators extent links ids) :=
  Q'.eqv_trans _ _ _ (mixedCoefficient_perm w K extent keep p (split_perm extent links ids).symm)
    (mixedCoefficient_factorizes w K extent keep p links hp hl _ _ (split_disjoint extent links ids))

end Local

end YMGap.Continuum.BF4ExactSlabMixedSpectatorFactorization

#print axioms YMGap.Continuum.BF4ExactSlabMixedSpectatorFactorization.mixedNumerator_factorizes
#print axioms YMGap.Continuum.BF4ExactSlabMixedSpectatorFactorization.mixedCoefficient_factorizes
#print axioms YMGap.Continuum.BF4ExactSlabMixedSpectatorFactorization.mixedCoefficient_rooted_pin
