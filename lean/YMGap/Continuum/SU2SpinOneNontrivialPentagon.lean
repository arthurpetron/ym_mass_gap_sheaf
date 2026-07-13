/-
# A five-nonidentity-edge spin-one pentagon coordinate

The unit-extended pentagon in `SU2SpinOneLabelWiredPentagon` checks the typed
source/target embeddings, but each route contains only one nonidentity edge.
Here all nine fixed labels in the Biedenharn--Elliott identity are spin one
(twice-spin label `2`).  The internal channel is summed over `0,2,4`.

For the dimension-rescaled entry

  F(e,f) = dim(f) * {1 1 e; 1 1 f},

the signed 6j pentagon, after clearing the common target dimensions, becomes

  sum_x (-1)^((18+x)/2) dim(x) F(x,2)^3 = dim(2) F(2,2)^2.

Thus the long route contains three nonidentity F entries and the short route
contains two.  The channel weights are `1,3,5`; retaining them is essential.
The two sides evaluate exactly to `3/4`.  Dividing the common rescaling back
out recovers the raw signed-6j value `1/36` on both sides.

Every entry is the finite factorial Racah value defined upstream.  No matrix is
reused as a label-independent endomorphism, and the constant-block failure
remains imported as a checked fence.
-/

import YMGap.Continuum.SU2SpinOneLabelWiredPentagon

namespace YMGap.Continuum.SU2SpinOneNontrivialPentagon

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.SixJKernel
open YMGap.Continuum.SU2SpinOneLabelWiredPentagon
open YMGap.Continuum.SU2TrivalentThetaRecoupling
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

local infix:50 " ≈ " => Q'.eqv

def phaseQ (n : Nat) : Q' := if n % 2 = 0 then 1 else Q'.ofInt (-1)

def cubeQ (q : Q') : Q' := (q * q) * q

/-- One long-route channel summand.  The three F entries occupy distinct
pentagon edges even though symmetry gives them the same numeric entry here. -/
def spinOneFLongTerm (x : Nat) : Q' :=
  phaseQ ((18 + x) / 2) * Q'.ofNat (dimRep x) *
    cubeQ (equalExternalFEntry 2 x 2)

/-- The three-F long route, summed over the complete spin-one fusion window. -/
def spinOneFLong : Q' := finSum spinOneFLongTerm 5

/-- The two-F short route.  `dimRep 2 = 3` is the residual dimension factor
after the common target dimensions have been cleared. -/
def spinOneFShort : Q' :=
  Q'.ofNat (dimRep 2) *
    (equalExternalFEntry 2 2 2 * equalExternalFEntry 2 2 2)

def threeEighths : Q' := Q'.mkPos 3 8 (by decide)
def fiveEighths : Q' := Q'.mkPos 5 8 (by decide)

/-- The channel ledger exposes the nonconstant dimensions and signs. -/
theorem spinOneFLong_terms_exact :
    spinOneFLongTerm 0 ≈ 1 ∧
    spinOneFLongTerm 1 ≈ 0 ∧
    spinOneFLongTerm 2 ≈ threeEighths ∧
    spinOneFLongTerm 3 ≈ 0 ∧
    spinOneFLongTerm 4 ≈ (-fiveEighths) := by decide

theorem spinOne_channel_dimensions_exact :
    dimRep 0 = 1 ∧ dimRep 2 = 3 ∧ dimRep 4 = 5 := by decide

/-- Exactly the even channels in the cutoff-five window are physical. -/
theorem spinOne_channel_guards_exact :
    valid6 2 2 2 2 0 2 = true ∧
    valid6 2 2 2 2 1 2 = false ∧
    valid6 2 2 2 2 2 2 = true ∧
    valid6 2 2 2 2 3 2 = false ∧
    valid6 2 2 2 2 4 2 = true := by decide

/-- Exact value of the three-edge route. -/
theorem spinOneFLong_exact : spinOneFLong ≈ threeQuarters := by decide

/-- Exact value of the two-edge route. -/
theorem spinOneFShort_exact : spinOneFShort ≈ threeQuarters := by decide

/-- The first pentagon coordinate here with at least two nonidentity F edges on
each side.  This is the all-spin-one Biedenharn--Elliott identity in the
dimension-rescaled basis. -/
theorem spinOne_five_edge_pentagon : spinOneFLong ≈ spinOneFShort :=
  Q'.eqv_trans _ _ _ spinOneFLong_exact (Q'.eqv_symm spinOneFShort_exact)

/-! ## Explicit edge labels and nonidentity audit -/

inductive PentagonPosition where
  | long1
  | long2
  | long3
  | short1
  | short2
deriving DecidableEq

structure WiredFEdge where
  position : PentagonPosition
  a : Nat
  b : Nat
  c : Nat
  d : Nat
  sourceChannel : Nat
  targetChannel : Nat

def longEdge1 (x : Nat) : WiredFEdge := ⟨.long1, 2, 2, 2, 2, x, 2⟩
def longEdge2 (x : Nat) : WiredFEdge := ⟨.long2, 2, 2, 2, 2, x, 2⟩
def longEdge3 (x : Nat) : WiredFEdge := ⟨.long3, 2, 2, 2, 2, x, 2⟩
def shortEdge1 : WiredFEdge := ⟨.short1, 2, 2, 2, 2, 2, 2⟩
def shortEdge2 : WiredFEdge := ⟨.short2, 2, 2, 2, 2, 2, 2⟩

def edgeValue (edge : WiredFEdge) : Q' :=
  equalExternalFEntry edge.a edge.sourceChannel edge.targetChannel

/-- The five edge positions are distinct even in this maximally symmetric
label instance. -/
theorem five_edge_positions_exact :
    (longEdge1 2).position = .long1 ∧
    (longEdge2 2).position = .long2 ∧
    (longEdge3 2).position = .long3 ∧
    shortEdge1.position = .short1 ∧
    shortEdge2.position = .short2 := by decide

/-- At the central channel all five edge values are the derived fraction
`1/2`, hence neither zero nor the identity scalar. -/
theorem five_edges_fractional_at_center :
    edgeValue (longEdge1 2) ≈ oneHalf ∧
    edgeValue (longEdge2 2) ≈ oneHalf ∧
    edgeValue (longEdge3 2) ≈ oneHalf ∧
    edgeValue shortEdge1 ≈ oneHalf ∧
    edgeValue shortEdge2 ≈ oneHalf ∧
    ¬ oneHalf ≈ 0 ∧ ¬ oneHalf ≈ 1 := by decide

/-- The dimension-rescaling is exact at the central edge:
`F(2,2) = dim(2) * signedSixJ(2,2) = 3 * (1/6) = 1/2`. -/
theorem center_dimension_rescaling_exact :
    equalExternalSignedSixJ 2 2 2 ≈ oneSixth ∧
    equalExternalFEntry 2 2 2 ≈
      Q'.ofNat (dimRep 2) * equalExternalSignedSixJ 2 2 2 ∧
    equalExternalFEntry 2 2 2 ≈ oneHalf := by decide

/-! ## Raw signed-6j form and the rescaling bridge -/

def spinOneRawLongTerm (x : Nat) : Q' :=
  phaseQ ((18 + x) / 2) * Q'.ofNat (dimRep x) *
    cubeQ (equalExternalSignedSixJ 2 x 2)

def spinOneRawLong : Q' := finSum spinOneRawLongTerm 5

def spinOneRawShort : Q' :=
  equalExternalSignedSixJ 2 2 2 * equalExternalSignedSixJ 2 2 2

def oneThirtySixth : Q' := Q'.mkPos 1 36 (by decide)

theorem spinOneRawLong_exact : spinOneRawLong ≈ oneThirtySixth := by decide
theorem spinOneRawShort_exact : spinOneRawShort ≈ oneThirtySixth := by decide

/-- The underlying signed-6j Biedenharn--Elliott coordinate. -/
theorem spinOne_raw_five_edge_pentagon : spinOneRawLong ≈ spinOneRawShort :=
  Q'.eqv_trans _ _ _ spinOneRawLong_exact (Q'.eqv_symm spinOneRawShort_exact)

/-- Clearing the three common target dimensions multiplies both raw sides by
`27`; this derives the dimension-rescaled identity rather than changing its
normalization. -/
theorem dimension_rescaled_matches_raw :
    spinOneFLong ≈ Q'.ofNat 27 * spinOneRawLong ∧
    spinOneFShort ≈ Q'.ofNat 27 * spinOneRawShort := by decide

/-- The old constant-block counterexample is still available verbatim. -/
theorem constantBlock_failure_still_fenced :
    ¬ RecoupleEq (constantPentagonShort singletChannel)
      (constantPentagonLong singletChannel) :=
  constant_fundamental_pentagon_fails

end YMGap.Continuum.SU2SpinOneNontrivialPentagon

#print axioms YMGap.Continuum.SU2SpinOneNontrivialPentagon.spinOneFLong_terms_exact
#print axioms YMGap.Continuum.SU2SpinOneNontrivialPentagon.spinOneFLong_exact
#print axioms YMGap.Continuum.SU2SpinOneNontrivialPentagon.spinOneFShort_exact
#print axioms YMGap.Continuum.SU2SpinOneNontrivialPentagon.spinOne_five_edge_pentagon
#print axioms YMGap.Continuum.SU2SpinOneNontrivialPentagon.five_edges_fractional_at_center
#print axioms YMGap.Continuum.SU2SpinOneNontrivialPentagon.center_dimension_rescaling_exact
#print axioms YMGap.Continuum.SU2SpinOneNontrivialPentagon.spinOne_raw_five_edge_pentagon
#print axioms YMGap.Continuum.SU2SpinOneNontrivialPentagon.dimension_rescaled_matches_raw
#print axioms YMGap.Continuum.SU2SpinOneNontrivialPentagon.constantBlock_failure_still_fenced
