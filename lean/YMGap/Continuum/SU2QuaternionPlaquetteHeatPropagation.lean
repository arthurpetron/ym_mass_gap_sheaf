/-
# Propagate the four ordered plaquette links through their full heat kernels

Quaternion multiplication is kept in its original order. One linear slot is
replaced at a time; every multiplier is supported and independent only of
that slot. The four resulting identities retain arbitrary other insertions.
-/

import YMGap.Continuum.SU2QuaternionLinearHeatPropagation
import YMGap.Continuum.SU2QuaternionFundamentalPlaquetteTube

namespace YMGap.Continuum.SU2QuaternionPlaquetteHeatPropagation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.SU2QuaternionLinearHeatPropagation
open YMGap.Continuum.SU2QuaternionFundamentalPlaquetteTube

structure QuaternionSupported (blocks : Nat) (q : PolyQuaternion) : Prop where
  scalar : SupportedQuaternionBlocks blocks q.scalar
  iPart : SupportedQuaternionBlocks blocks q.iPart
  jPart : SupportedQuaternionBlocks blocks q.jPart
  kPart : SupportedQuaternionBlocks blocks q.kPart

private theorem support_add {blocks : Nat} {p q : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) (hq : SupportedQuaternionBlocks blocks q) :
    SupportedQuaternionBlocks blocks (polyAdd p q) := fun t ht => (List.mem_append.mp ht).elim (hp t) (hq t)

private theorem support_neg {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) : SupportedQuaternionBlocks blocks (polyNeg p) := by
  intro t ht
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp ht
  exact hp s hs

theorem QuaternionSupported.coordinate {blocks j : Nat} (hj : j < blocks) :
    QuaternionSupported blocks (PolyQuaternion.coordinateVariable j) :=
  ⟨coordinate_supported hj 0, coordinate_supported hj 1, coordinate_supported hj 2, coordinate_supported hj 3⟩

theorem QuaternionSupported.conj {blocks : Nat} {q : PolyQuaternion} (h : QuaternionSupported blocks q) :
    QuaternionSupported blocks (PolyQuaternion.conj q) :=
  ⟨h.scalar, support_neg h.iPart, support_neg h.jPart, support_neg h.kPart⟩

theorem QuaternionSupported.mul {blocks : Nat} {p q : PolyQuaternion}
    (hp : QuaternionSupported blocks p) (hq : QuaternionSupported blocks q) :
    QuaternionSupported blocks (PolyQuaternion.mul p q) := by
  constructor <;> simp only [PolyQuaternion.mul]
  all_goals repeat' first
    | exact hp.scalar | exact hp.iPart | exact hp.jPart | exact hp.kPart
    | exact hq.scalar | exact hq.iPart | exact hq.jPart | exact hq.kPart
    | apply support_add | apply support_neg | apply supported_polyMul

structure QuaternionPropagates (blocks a b : Nat) (w : Q') (K : Nat) (p q : PolyQuaternion) : Prop where
  scalar : Propagates blocks a b w K p.scalar q.scalar
  iPart : Propagates blocks a b w K p.iPart q.iPart
  jPart : Propagates blocks a b w K p.jPart q.jPart
  kPart : Propagates blocks a b w K p.kPart q.kPart

theorem QuaternionPropagates.coordinate (tailBlocks : Nat) (hb : 0 < tailBlocks)
    (a b : Fin (tailBlocks+1)) (hab : a.val ≠ b.val) (w : Q') (K : Nat) (hK : 1 ≤ K) :
    QuaternionPropagates (tailBlocks+1) a.val b.val w K
      (PolyQuaternion.coordinateVariable a.val) (PolyQuaternion.coordinateVariable b.val) :=
  ⟨Propagates.coordinate tailBlocks hb a b hab w K hK 0,
   Propagates.coordinate tailBlocks hb a b hab w K hK 1,
   Propagates.coordinate tailBlocks hb a b hab w K hK 2,
   Propagates.coordinate tailBlocks hb a b hab w K hK 3⟩

theorem QuaternionPropagates.conj {blocks a b : Nat} {w : Q'} {K : Nat} {p q : PolyQuaternion}
    (h : QuaternionPropagates blocks a b w K p q) :
    QuaternionPropagates blocks a b w K (PolyQuaternion.conj p) (PolyQuaternion.conj q) :=
  ⟨h.scalar, h.iPart.neg, h.jPart.neg, h.kPart.neg⟩

theorem QuaternionPropagates.mul_right {blocks a b : Nat} {w : Q'} {K : Nat} {p p' : PolyQuaternion}
    (h : QuaternionPropagates blocks a b w K p p') (q : PolyQuaternion)
    (hs : QuaternionSupported blocks q) (hd : HasPolyQuaternionBlockDegree a 0 q) :
    QuaternionPropagates blocks a b w K (PolyQuaternion.mul p q) (PolyQuaternion.mul p' q) := by
  constructor <;> simp only [PolyQuaternion.mul]
  all_goals repeat' first
    | exact h.scalar | exact h.iPart | exact h.jPart | exact h.kPart
    | exact hs.scalar | exact hs.iPart | exact hs.jPart | exact hs.kPart
    | exact hd.scalar | exact hd.iPart | exact hd.jPart | exact hd.kPart
    | apply Propagates.add | apply Propagates.neg | apply Propagates.mul_right

theorem QuaternionPropagates.mul_left {blocks a b : Nat} {w : Q'} {K : Nat} {p p' : PolyQuaternion}
    (h : QuaternionPropagates blocks a b w K p p') (q : PolyQuaternion)
    (hs : QuaternionSupported blocks q) (hd : HasPolyQuaternionBlockDegree a 0 q) :
    QuaternionPropagates blocks a b w K (PolyQuaternion.mul q p) (PolyQuaternion.mul q p') := by
  constructor <;> simp only [PolyQuaternion.mul]
  all_goals repeat' first
    | exact h.scalar | exact h.iPart | exact h.jPart | exact h.kPart
    | exact hs.scalar | exact hs.iPart | exact hs.jPart | exact hs.kPart
    | exact hd.scalar | exact hd.iPart | exact hd.jPart | exact hd.kPart
    | apply Propagates.add | apply Propagates.neg | apply Propagates.mul_left

/-- Successive literal words at any offset, preserving their ordering. -/
def stagedPlaquette (offset : Nat) : Nat → RatPoly
  | 0 => plaquette offset (offset+1) (offset+2) (offset+3)
  | 1 => plaquette (offset+4) (offset+1) (offset+2) (offset+3)
  | 2 => plaquette (offset+4) (offset+5) (offset+2) (offset+3)
  | 3 => plaquette (offset+4) (offset+5) (offset+6) (offset+3)
  | _ => plaquette (offset+4) (offset+5) (offset+6) (offset+7)

private theorem coordinate_independent (a j : Nat) (h : a ≠ j) :
    HasPolyQuaternionBlockDegree a 0 (PolyQuaternion.coordinateVariable j) := by
  have hd := hasPolyQuaternionBlockDegree_coordinateVariable j a
  rw [if_neg h] at hd
  exact hd

/-- Four exact substitutions in the original ordered plaquette. -/
theorem plaquette_step (tailBlocks offset : Nat) (hb : offset+7 < tailBlocks+1) (w : Q') (K : Nat) (hK : 1 ≤ K)
    (i : Fin 4) : Propagates (tailBlocks+1) (offset+i.val) (offset+(i.val+4)) w K
      (stagedPlaquette offset i.val) (stagedPlaquette offset (i.val+1)) := by
  let C (j : Nat) := PolyQuaternion.coordinateVariable (offset+j)
  have hs (j : Nat) (hj : offset+j < tailBlocks+1) : QuaternionSupported (tailBlocks+1) (C j) := QuaternionSupported.coordinate hj
  have hd (a j : Nat) (h : a ≠ j) : HasPolyQuaternionBlockDegree (offset+a) 0 (C j) :=
    coordinate_independent (offset+a) (offset+j) (by omega)
  have step (a : Nat) (ha : a < 4) : QuaternionPropagates (tailBlocks+1) (offset+a) (offset+(a+4)) w K (C a) (C (a+4)) :=
    QuaternionPropagates.coordinate tailBlocks (by omega) ⟨offset+a,by omega⟩ ⟨offset+(a+4),by omega⟩
      (by change offset+a ≠ offset+(a+4); omega) w K hK
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by simp only [Fin.ext_iff]; omega
  rcases hi with rfl | rfl | rfl | rfl
  · have h1 := (step 0 (by decide)).mul_right (C 1) (hs 1 (by omega)) (hd 0 1 (by decide))
    have h2 := h1.mul_right (PolyQuaternion.conj (C 2)) (hs 2 (by omega)).conj (hd 0 2 (by decide)).conj
    exact (h2.mul_right (PolyQuaternion.conj (C 3)) (hs 3 (by omega)).conj (hd 0 3 (by decide)).conj).scalar.smul 2
  · have h1 := (step 1 (by decide)).mul_left (C 4) (hs 4 (by omega)) (hd 1 4 (by decide))
    have h2 := h1.mul_right (PolyQuaternion.conj (C 2)) (hs 2 (by omega)).conj (hd 1 2 (by decide)).conj
    exact (h2.mul_right (PolyQuaternion.conj (C 3)) (hs 3 (by omega)).conj (hd 1 3 (by decide)).conj).scalar.smul 2
  · have h1 := (step 2 (by decide)).conj.mul_left (PolyQuaternion.mul (C 4) (C 5))
      ((hs 4 (by omega)).mul (hs 5 (by omega))) ((hd 2 4 (by decide)).mul (hd 2 5 (by decide)))
    exact (h1.mul_right (PolyQuaternion.conj (C 3)) (hs 3 (by omega)).conj (hd 2 3 (by decide)).conj).scalar.smul 2
  · exact ((step 3 (by decide)).conj.mul_left
      (PolyQuaternion.mul (PolyQuaternion.mul (C 4) (C 5)) (PolyQuaternion.conj (C 6)))
      (((hs 4 (by omega)).mul (hs 5 (by omega))).mul (hs 6 (by omega)).conj)
      (((hd 3 4 (by decide)).mul (hd 3 5 (by decide))).mul (hd 3 6 (by decide)).conj)).scalar.smul 2

end YMGap.Continuum.SU2QuaternionPlaquetteHeatPropagation

#print axioms YMGap.Continuum.SU2QuaternionPlaquetteHeatPropagation.QuaternionSupported.coordinate
#print axioms YMGap.Continuum.SU2QuaternionPlaquetteHeatPropagation.QuaternionSupported.conj
#print axioms YMGap.Continuum.SU2QuaternionPlaquetteHeatPropagation.QuaternionSupported.mul
#print axioms YMGap.Continuum.SU2QuaternionPlaquetteHeatPropagation.QuaternionPropagates.coordinate
#print axioms YMGap.Continuum.SU2QuaternionPlaquetteHeatPropagation.QuaternionPropagates.conj
#print axioms YMGap.Continuum.SU2QuaternionPlaquetteHeatPropagation.QuaternionPropagates.mul_right
#print axioms YMGap.Continuum.SU2QuaternionPlaquetteHeatPropagation.QuaternionPropagates.mul_left
#print axioms YMGap.Continuum.SU2QuaternionPlaquetteHeatPropagation.stagedPlaquette
#print axioms YMGap.Continuum.SU2QuaternionPlaquetteHeatPropagation.plaquette_step
