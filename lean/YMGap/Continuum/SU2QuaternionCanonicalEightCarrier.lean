/-
# Canonical eight-coordinate quaternion polynomial carrier

The literal `List Nat` monomials admit trailing-zero aliases, so a coordinate
permutation cannot be a strict involution on that representation.  This file
introduces the corrected finite-coordinate carrier: a monomial is a function
`Fin 8 -> Nat`.  Boundary exchange is therefore a genuine coordinate
permutation, preserves the polynomial unit literally, is multiplicative, and
squares to the identity.

The next file transports the already-derived product-Haar and Wilson-weighted
positivity theorems to this strict carrier.  No positivity is postulated here.
-/

import YMGap.Continuum.SU2QuaternionBoundarySwapCarrierFence

namespace YMGap.Continuum.SU2QuaternionCanonicalEightCarrier

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.ObservableMeasure

abbrev Mono8 := Fin 8 → Nat
abbrev Term8 := Mono8 × Q'
abbrev Poly8 := List Term8

def monoZero8 : Mono8 := fun _ => 0
def monoMul8 (a b : Mono8) : Mono8 := fun i => a i + b i

def polyZero8 : Poly8 := []
def polyOne8 : Poly8 := [(monoZero8, 1)]
def polyAdd8 (p q : Poly8) : Poly8 := p ++ q
def polyNeg8 (p : Poly8) : Poly8 := p.map fun t => (t.1, -t.2)
def polySmul8 (c : Q') (p : Poly8) : Poly8 :=
  p.map fun t => (t.1, c * t.2)
def termMul8 (a b : Term8) : Term8 :=
  (monoMul8 a.1 b.1, a.2 * b.2)
def polyMul8 (p q : Poly8) : Poly8 :=
  p.flatMap fun a => q.map fun b => termMul8 a b

/-- Exchange coordinate blocks `0..3` and `4..7`. -/
def swapBoundaryIndex8 (i : Fin 8) : Fin 8 :=
  if h : i.val < 4 then
    ⟨i.val + 4, by omega⟩
  else
    ⟨i.val - 4, by omega⟩

theorem swapBoundaryIndex8_involutive (i : Fin 8) :
    swapBoundaryIndex8 (swapBoundaryIndex8 i) = i := by
  apply Fin.ext
  unfold swapBoundaryIndex8
  split <;> rename_i h
  · have hnot : ¬ (i.val + 4 < 4) := by omega
    simp [hnot]
  · have hge : 4 ≤ i.val := by omega
    have hlt : i.val - 4 < 4 := by omega
    simp [hlt]
    omega

def swapMono8 (m : Mono8) : Mono8 :=
  fun i => m (swapBoundaryIndex8 i)

def swapTerm8 (t : Term8) : Term8 := (swapMono8 t.1, t.2)

def swapPoly8 (p : Poly8) : Poly8 := p.map swapTerm8

theorem swapMono8_involutive (m : Mono8) : swapMono8 (swapMono8 m) = m := by
  funext i
  unfold swapMono8
  rw [swapBoundaryIndex8_involutive]

theorem swapTerm8_involutive (t : Term8) :
    swapTerm8 (swapTerm8 t) = t := by
  apply Prod.ext
  · exact swapMono8_involutive t.1
  · rfl

theorem swapPoly8_involutive (p : Poly8) :
    swapPoly8 (swapPoly8 p) = p := by
  induction p with
  | nil => rfl
  | cons t p ih =>
      change swapTerm8 (swapTerm8 t) :: swapPoly8 (swapPoly8 p) = t :: p
      rw [swapTerm8_involutive, ih]

theorem swapMono8_zero : swapMono8 monoZero8 = monoZero8 := by
  rfl

theorem swapPoly8_one : swapPoly8 polyOne8 = polyOne8 := by
  simp [swapPoly8, swapTerm8, swapMono8_zero, polyOne8]

theorem swapMono8_mul (a b : Mono8) :
    swapMono8 (monoMul8 a b) = monoMul8 (swapMono8 a) (swapMono8 b) := by
  rfl

theorem swapTerm8_mul (a b : Term8) :
    swapTerm8 (termMul8 a b) = termMul8 (swapTerm8 a) (swapTerm8 b) := by
  apply Prod.ext
  · exact swapMono8_mul a.1 b.1
  · rfl

private theorem swapTerm8_map_mul (a : Term8) (q : Poly8) :
    List.map swapTerm8 (q.map fun b => termMul8 a b) =
      ((q.map swapTerm8).map fun b => termMul8 (swapTerm8 a) b) := by
  induction q with
  | nil => rfl
  | cons b q ih =>
      simp only [List.map_cons]
      rw [swapTerm8_mul, ih]

theorem swapPoly8_mul (p q : Poly8) :
    swapPoly8 (polyMul8 p q) = polyMul8 (swapPoly8 p) (swapPoly8 q) := by
  induction p with
  | nil => rfl
  | cons a p ih =>
      change
        List.map swapTerm8
            ((q.map fun b => termMul8 a b) ++ polyMul8 p q) =
          ((swapPoly8 q).map fun b => termMul8 (swapTerm8 a) b) ++
            polyMul8 (swapPoly8 p) (swapPoly8 q)
      rw [List.map_append, swapTerm8_map_mul]
      change
        ((swapPoly8 q).map fun b => termMul8 (swapTerm8 a) b) ++
            swapPoly8 (polyMul8 p q) =
          ((swapPoly8 q).map fun b => termMul8 (swapTerm8 a) b) ++
            polyMul8 (swapPoly8 p) (swapPoly8 q)
      rw [ih]

/-- The canonical polynomial carrier is a literal observable algebra. -/
def canonicalQuaternionPairAlg : ObsAlg where
  carrier := Poly8
  one := polyOne8
  mul := polyMul8
  star := fun p => p

/-- Boundary exchange is now a strict unital observable endomorphism. -/
def canonicalBoundarySwapHom :
    ObsHom canonicalQuaternionPairAlg canonicalQuaternionPairAlg where
  map := swapPoly8
  map_one := swapPoly8_one
  map_mul := swapPoly8_mul
  map_star := fun _ => rfl

theorem canonicalBoundarySwapHom_involutive (p : Poly8) :
    canonicalBoundarySwapHom.map (canonicalBoundarySwapHom.map p) = p :=
  swapPoly8_involutive p

end YMGap.Continuum.SU2QuaternionCanonicalEightCarrier

#print axioms YMGap.Continuum.SU2QuaternionCanonicalEightCarrier.swapBoundaryIndex8_involutive
#print axioms YMGap.Continuum.SU2QuaternionCanonicalEightCarrier.swapPoly8_involutive
#print axioms YMGap.Continuum.SU2QuaternionCanonicalEightCarrier.swapPoly8_mul
#print axioms YMGap.Continuum.SU2QuaternionCanonicalEightCarrier.canonicalBoundarySwapHom
#print axioms YMGap.Continuum.SU2QuaternionCanonicalEightCarrier.canonicalBoundarySwapHom_involutive
