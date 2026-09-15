/-
# Literal one-step preimages for ORIGINAL interior plaquette observables

The maximum time vertex of a lower face is at most half. If every generator
in an expression has maximum time strictly below half, shifting it inward
one unit stays lower. A computed larger base accommodates the spatial edges.
The existing outward translation then recovers the SAME original polynomial
at every sufficiently large common volume, not just its mean or norm.

This constructs an exact geometric T1 preimage, hence approximate T2 preimages
and the existing positive-real-time zero modulus for these original dense
states. No action or exterior interaction is changed. Ordinary zero-lag box
enlargement preserves the interior criterion and cannot manufacture this margin.

The criterion is syntactic support, not a characterization of all range states:
a failed test is not a proof of non-membership. Boundary-touching expressions,
density of the geometric range, full-space time zero, T1 positivity/root
identification, physical Hamiltonian and continuum/Clay remain open.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicGeometricRangeContinuity

namespace YMGap.Continuum.BF4ExactSlabThermodynamicInteriorTimePreimage

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquetteBulkEmbedding
open YMGap.Continuum.BF4ExactSlabThermodynamicBaseCompatibility (enlarge)
open YMGap.Continuum.BF4ExactSlabThermodynamicPresentation
open YMGap.Continuum.BF4ExactSlabThermodynamicTimeGeometry
open YMGap.Continuum.BF4ExactSlabThermodynamicTimeAlgebra (sameOfPolynomial)
open YMGap.Continuum.BF4ExactSlabThermodynamicLowerFunctional (embed)
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry
open YMGap.Continuum.BF4ExactSlabThermodynamicTimeStates (timeState_pin)
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimePins
open YMGap.Continuum.BF4ExactSlabThermodynamicGeometricRangeContinuity
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier

local notation "point" X => Quotient.mk seminorm.completionSetoid X
local notation "rat" q => Quotient.mk crealSetoid (ofQ' q)

def faceTopTime : Z4Plaq → Nat
  | ((_,_,_,t), .p01) | ((_,_,_,t), .p02) | ((_,_,_,t), .p12) => t
  | ((_,_,_,t), .p03) | ((_,_,_,t), .p13) | ((_,_,_,t), .p23) => t+1

theorem faceTopTime_shift (space time : Nat) (p : Z4Plaq) :
    faceTopTime (shiftFace space time p) = faceTopTime p + time := by
  obtain ⟨⟨a,b,c,t⟩,plane⟩ := p
  cases plane <;> simp only [faceTopTime, shiftFace, shiftVertex] <;> omega

theorem lower_top_le {half : Nat} {p : Z4Plaq} (hp : plaquetteHalfSide half p = .lower) :
    faceTopTime p ≤ half := by
  obtain ⟨⟨a,b,c,t⟩,plane⟩ := p
  cases plane <;>
    simp only [plaquetteHalfSide, spatialHalfSide, temporalHalfSide, faceTopTime] at hp ⊢
  all_goals
    split at hp
    · omega
    · first | contradiction | (split at hp <;> contradiction)

theorem boundary_top {half : Nat} {p : Z4Plaq} (hp : plaquetteHalfSide half p = .lower)
    (hi : ¬ faceTopTime p < half) : faceTopTime p = half := by
  have h := lower_top_le hp
  omega

def Interior {half : Nat} : PlaquetteExpression half → Prop
  | .unit => True
  | .character id _ _ => faceTopTime (slabPlaquetteAt (centralExtent half) id) < half
  | .add e f | .mul e f => Interior e ∧ Interior f
  | .smul _ e => Interior e

/-- A finite geometric decision, not an assumed analytic range predicate. -/
def interiorDecision {half : Nat} : (e : PlaquetteExpression half) → Decidable (Interior e)
  | .unit => isTrue True.intro
  | .character id _ _ => inferInstanceAs
      (Decidable (faceTopTime (slabPlaquetteAt (centralExtent half) id) < half))
  | .add e f | .mul e f => by
      letI := interiorDecision e
      letI := interiorDecision f
      exact inferInstanceAs (Decidable (Interior e ∧ Interior f))
  | .smul _ e => interiorDecision e

/-- Changing the base box does not move the source away from the reflection plane. -/
theorem interior_enlarge {half : Nat} (padding : Nat) : ∀ e : PlaquetteExpression half,
    Interior (enlarge padding e) ↔ Interior e
  | .unit => Iff.rfl
  | .character id hi spin => by
      change faceTopTime (slabPlaquetteAt (centralExtent (half+padding))
        (bulkFaceId half padding 0 id)) < half+padding ↔
          faceTopTime (slabPlaquetteAt (centralExtent half) id) < half
      rw [bulkFaceId_pin (mem_centralLowerFaceIds.mp hi).1, faceTopTime_shift, Nat.sub_zero]
      constructor <;> intro h <;> omega
  | .add e f | .mul e f => and_congr (interior_enlarge padding e) (interior_enlarge padding f)
  | .smul _ e => interior_enlarge padding e

private theorem inward_lower {half : Nat} {p : Z4Plaq} (hp : faceTopTime p < half) :
    plaquetteHalfSide (half+1) (shiftFace 1 2 p) = .lower := by
  obtain ⟨⟨a,b,c,t⟩,plane⟩ := p
  cases plane <;>
    simp only [faceTopTime, shiftFace, shiftVertex, plaquetteHalfSide, spatialHalfSide, temporalHalfSide] at hp ⊢
  all_goals rw [if_pos (by omega)]

def inwardFaceId (half id : Nat) : Nat :=
  shiftFaceId (centralExtent half) (centralExtent (half+1)) 1 2 id

theorem inwardFaceId_pin {half id : Nat} (hi : id ∈ centralLowerFaceIds half) :
    slabPlaquetteAt (centralExtent (half+1)) (inwardFaceId half id) =
      shiftFace 1 2 (slabPlaquetteAt (centralExtent half) id) :=
  shiftFaceId_pin (by unfold centralExtent; omega) (by unfold centralExtent; omega)
    (mem_centralLowerFaceIds.mp hi).1

theorem inwardFaceId_lower {half id : Nat} (hi : id ∈ centralLowerFaceIds half)
    (hp : faceTopTime (slabPlaquetteAt (centralExtent half) id) < half) :
    inwardFaceId half id ∈ centralLowerFaceIds (half+1) := by
  apply mem_centralLowerFaceIds.mpr
  refine ⟨shiftFaceId_physical (by unfold centralExtent; omega) (by unfold centralExtent; omega)
    (mem_centralLowerFaceIds.mp hi).1, ?_⟩
  rw [inwardFaceId_pin hi]
  exact inward_lower hp

def inward {half : Nat} : (e : PlaquetteExpression half) → Interior e → PlaquetteExpression (half+1)
  | .unit, _ => .unit
  | .character id hi spin, h => .character (inwardFaceId half id) (inwardFaceId_lower hi h) spin
  | .add e f, h => .add (inward e h.1) (inward f h.2)
  | .mul e f, h => .mul (inward e h.1) (inward f h.2)
  | .smul c e, h => .smul c (inward e h)

theorem placed_inward {half : Nat} (space time : Nat) (f : Z4Plaq → Nat → RatPoly) :
    ∀ (e : PlaquetteExpression half) (hi : Interior e),
      placed space time f (inward e hi) = placed (1+space) (2+time) f e
  | .unit, _ => rfl
  | .character id hi spin, _ => by
      change f (shiftFace space time (slabPlaquetteAt (centralExtent (half+1)) (inwardFaceId half id))) spin = _
      rw [inwardFaceId_pin hi, shiftFace_comp]
      rfl
  | .add e q, h => by
      change polyAdd (placed space time f (inward e h.1)) (placed space time f (inward q h.2)) = _
      rw [placed_inward space time f e h.1, placed_inward space time f q h.2]
      rfl
  | .mul e q, h => by
      change polyMul (placed space time f (inward e h.1)) (placed space time f (inward q h.2)) = _
      rw [placed_inward space time f e h.1, placed_inward space time f q h.2]
      rfl
  | .smul c e, h => congrArg (polySmul c) (placed_inward space time f e h)

def preimage (p : Presentation) (hi : Interior p.expression) : Presentation :=
  ⟨p.base+1, inward p.expression hi⟩

/-- Literal equality on the original target link variables, before any measure or quotient. -/
theorem polynomial_translate_preimage (p : Presentation) (hi : Interior p.expression)
    (volume : Nat) (hv : p.base+2 ≤ volume) :
    polynomial (translate 1 (preimage p hi)) volume = polynomial p volume := by
  rw [polynomial_translate 1 (preimage p hi) volume (by change p.base+1+1 ≤ volume; omega)]
  change placed (volume-(p.base+1)) (volume-(p.base+1)-1) (faceCharacter volume)
    (inward p.expression hi) = polynomial p volume
  rw [placed_inward,
    show 1+(volume-(p.base+1))=volume-p.base by omega,
    show 2+(volume-(p.base+1)-1)=volume-p.base by omega]
  unfold polynomial
  rw [shiftedExpression_placed, show p.base+(volume-p.base)=volume by omega]

def samePreimage (p : Presentation) (hi : Interior p.expression) :
    SameObservable (translate 1 (preimage p hi)) p :=
  sameOfPolynomial _ _ (p.base+2) (by change p.base+1+1 ≤ p.base+2; omega)
    (by omega) (polynomial_translate_preimage p hi)

theorem completed_preimage (p : Presentation) (hi : Interior p.expression) :
    completedTime 1 (embedPresentation (preimage p hi)) = embedPresentation p := by
  rw [completedTime_embedPresentation, timeState_pin]
  exact congrArg embedObservable (show embed (translate 1 (preimage p hi)) = embed p from
    Quotient.sound ⟨samePreimage p hi⟩)

def interiorApproximationCertificate (p : Presentation) (hi : Interior p.expression)
    (epsilon : Q') (he : (0 : Q') < epsilon) :
    Σ' Y : seminorm.Cauchy,
      RCle (completedDist (embedPresentation p) (twoStepTransfer (point Y))) (rat epsilon) := by
  let C := oneStepApproximationCertificate (seminorm.constant (preimage p hi)) epsilon he
  refine ⟨C.1, ?_⟩
  have h := C.2
  change RCle (completedDist (completedTime 1 (embedPresentation (preimage p hi)))
    (twoStepTransfer (point C.1))) (rat epsilon) at h
  rw [completed_preimage] at h
  exact h

def interiorZeroContinuityCertificate (p : Presentation) (hi : Interior p.expression)
    (epsilon : Q') (he : (0 : Q') < epsilon) :
    Σ' delta : Q', ((0 : Q') < delta) ×'
      (∀ t : PositiveTimeValue, RCle (realValue t) (rat delta) →
        RCle (completedDist (realTimeAction t (embedPresentation p)) (embedPresentation p)) (rat epsilon)) := by
  let C := oneStepZeroContinuityCertificate (seminorm.constant (preimage p hi)) epsilon he
  refine ⟨C.1, C.2.1, ?_⟩
  intro t ht
  have h := C.2.2 t ht
  change RCle (completedDist (realTimeAction t (completedTime 1 (embedPresentation (preimage p hi))))
    (completedTime 1 (embedPresentation (preimage p hi)))) (rat epsilon) at h
  rw [completed_preimage] at h
  exact h

end YMGap.Continuum.BF4ExactSlabThermodynamicInteriorTimePreimage

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicInteriorTimePreimage.faceTopTime
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicInteriorTimePreimage.faceTopTime_shift
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicInteriorTimePreimage.lower_top_le
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicInteriorTimePreimage.boundary_top
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicInteriorTimePreimage.Interior
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicInteriorTimePreimage.interiorDecision
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicInteriorTimePreimage.interior_enlarge
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicInteriorTimePreimage.inwardFaceId
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicInteriorTimePreimage.inwardFaceId_pin
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicInteriorTimePreimage.inwardFaceId_lower
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicInteriorTimePreimage.inward
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicInteriorTimePreimage.placed_inward
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicInteriorTimePreimage.preimage
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicInteriorTimePreimage.polynomial_translate_preimage
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicInteriorTimePreimage.samePreimage
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicInteriorTimePreimage.completed_preimage
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicInteriorTimePreimage.interiorApproximationCertificate
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicInteriorTimePreimage.interiorZeroContinuityCertificate
