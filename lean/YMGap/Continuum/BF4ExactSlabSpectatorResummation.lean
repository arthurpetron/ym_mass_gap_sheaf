/-
# Exact ORIGINAL spectator partition-square resummation

When both probes lie on the anchor side of a supplied disjoint split,
the original connected numerator factors as anchor numerator times the
spectator partition square. Finite inclusion-exclusion factors too, and
summing ALL spectator selections returns the SAME original partition square.
No absolute value is taken before this resummation.

This is an anchored family identity, not yet a partition of the full
boundary expansion into such families. No volume-uniform decay is claimed.
-/

import YMGap.Continuum.FiniteSelectionMobiusFactorization
import YMGap.Continuum.BF4ExactSlabConnectedSelectionExpansion

namespace YMGap.Continuum.BF4ExactSlabSpectatorResummation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (PolyExpr poly_identity_of_normal_eq)
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentActionLimit
open YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabSelectionSeparation
open YMGap.Continuum.BF4ExactSlabDisconnectedHaarCancellation
open YMGap.Continuum.BF4ExactSlabConnectedSelectionExpansion
open YMGap.Continuum.FinitePolynomialSubsetExpansion
open YMGap.Continuum.FiniteSelectionMobius
open YMGap.Continuum.FiniteSelectionMobiusFactorization
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionBlockLocality
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

def partitionSquare (w : Q') (K extent : Nat) (ids : List Nat) : Q' :=
  let Z := heatProductHaar w (boundaryCompleteSlabLinks extent).length extent ids K
  Z*Z

def partitionSquareCoefficient (w : Q') (K extent : Nat) (ids : List Nat) : Q' :=
  coefficient (partitionSquare w K extent) ids

theorem partitionSquareCoefficient_sum (w : Q') (K extent : Nat) (ids : List Nat) :
    listQSum (partitionSquareCoefficient w K extent) (selections ids) ≈ partitionSquare w K extent ids :=
  reconstruct _ _

theorem disjoint_subfaces {extent : Nat} {links : List Z4Link} {core spectators a b : List Nat}
    (hd : LinksDisjoint (links++faceLinks extent core) (faceLinks extent spectators))
    (ha : ∀ id, id ∈ a → id ∈ core) (hb : ∀ id, id ∈ b → id ∈ spectators) :
    LinksDisjoint (links++faceLinks extent a) (faceLinks extent b) := by
  intro link hl hr
  apply hd link
  · rcases List.mem_append.mp hl with hl | hl
    · exact List.mem_append.mpr (Or.inl hl)
    · exact List.mem_append.mpr (Or.inr (faceLinks_mono ha link hl))
  · exact faceLinks_mono hb link hr

private theorem qmul {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h) (Q'.mul_eqv_congr_left _ _ _ k)

section Local

variable (w : Q') (K extent : Nat) (p q : RatPoly) (links : List Z4Link)
  (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length p)
  (hq : SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length q)
  (hlp : LinkLocal extent links p) (hlq : LinkLocal extent links q)

include hp hq hlp hlq

theorem numerator_spectator_factorizes (core spectators : List Nat)
    (hd : LinksDisjoint (links++faceLinks extent core) (faceLinks extent spectators)) :
    connectedNumerator w K extent (core++spectators) p q ≈
      connectedNumerator w K extent core p q * partitionSquare w K extent spectators := by
  have hn (r : RatPoly) (hr : SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length r)
      (hl : LinkLocal extent links r) := left_moment_factorizes w K extent core spectators links [] hd r hr hl
  have hz := partition_factorizes w K extent core spectators
    (fun link hcore hs => hd link (List.mem_append.mpr (Or.inr hcore)) hs)
  have he := Q'.add_eqv_congr'
    (qmul (hn (polyMul p q) (supported_polyMul hp hq) (BlockLocal.mul hlp hlq)) hz)
    (Q'.neg_eqv_congr _ _ (qmul (hn p hp hlp) (hn q hq hlq)))
  exact Q'.eqv_trans _ _ _ he (poly_identity_of_normal_eq
    (.add (.mul (.mul (.var 0) (.var 4)) (.mul (.var 1) (.var 4)))
      (.neg (.mul (.mul (.var 2) (.var 4)) (.mul (.var 3) (.var 4)))))
    (.mul (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 2) (.var 3)))) (.mul (.var 4) (.var 4))) (by decide)
    (fun i => if i = 0 then numerator w (boundaryCompleteSlabLinks extent).length extent core (polyMul p q) K
      else if i = 1 then heatProductHaar w (boundaryCompleteSlabLinks extent).length extent core K
      else if i = 2 then numerator w (boundaryCompleteSlabLinks extent).length extent core p K
      else if i = 3 then numerator w (boundaryCompleteSlabLinks extent).length extent core q K
      else heatProductHaar w (boundaryCompleteSlabLinks extent).length extent spectators K))

theorem coefficient_spectator_factorizes (core spectators : List Nat)
    (hd : LinksDisjoint (links++faceLinks extent core) (faceLinks extent spectators)) :
    connectedCoefficient w K extent p q (core++spectators) ≈
      connectedCoefficient w K extent p q core * partitionSquareCoefficient w K extent spectators :=
  coefficient_factorizes _ _ _ core spectators (fun a ha b hb =>
    numerator_spectator_factorizes w K extent p q links hp hq hlp hlq a b
      (disjoint_subfaces hd (fun id hi => selected_mem ha id hi) (fun id hi => selected_mem hb id hi)))

end Local

def spectatorSum (w : Q') (K extent : Nat) (p q : RatPoly) (core spectators : List Nat) : Q' :=
  listQSum (fun selected => connectedCoefficient w K extent p q (core++selected)) (selections spectators)

/-- Sum signed spectator coefficients FIRST: their exact original Z^2 returns. -/
theorem spectatorSum_pin (w : Q') (K extent : Nat) (p q : RatPoly) (links : List Z4Link)
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length p)
    (hq : SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length q)
    (hlp : LinkLocal extent links p) (hlq : LinkLocal extent links q) (core spectators : List Nat)
    (hd : LinksDisjoint (links++faceLinks extent core) (faceLinks extent spectators)) :
    spectatorSum w K extent p q core spectators ≈
      connectedCoefficient w K extent p q core * partitionSquare w K extent spectators :=
  Q'.eqv_trans _ _ _ (listQSum_congr_on _ _ _ (fun selected hs =>
    coefficient_spectator_factorizes w K extent p q links hp hq hlp hlq core selected
      (disjoint_subfaces hd (fun _ h => h) (fun id hi => selected_mem hs id hi))))
    (Q'.eqv_trans _ _ _ (listQSum_mul_left _ _ _)
      (Q'.mul_eqv_congr_left _ _ _ (partitionSquareCoefficient_sum w K extent spectators)))

end YMGap.Continuum.BF4ExactSlabSpectatorResummation

#print axioms YMGap.Continuum.BF4ExactSlabSpectatorResummation.partitionSquare
#print axioms YMGap.Continuum.BF4ExactSlabSpectatorResummation.partitionSquareCoefficient
#print axioms YMGap.Continuum.BF4ExactSlabSpectatorResummation.partitionSquareCoefficient_sum
#print axioms YMGap.Continuum.BF4ExactSlabSpectatorResummation.disjoint_subfaces
#print axioms YMGap.Continuum.BF4ExactSlabSpectatorResummation.numerator_spectator_factorizes
#print axioms YMGap.Continuum.BF4ExactSlabSpectatorResummation.coefficient_spectator_factorizes
#print axioms YMGap.Continuum.BF4ExactSlabSpectatorResummation.spectatorSum
#print axioms YMGap.Continuum.BF4ExactSlabSpectatorResummation.spectatorSum_pin
