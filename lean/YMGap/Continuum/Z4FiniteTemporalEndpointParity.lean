/-
# Finite temporal parity conserves the two endpoint charges

An explicit ceiling of the finite face times supplies an empty terminal
cut. With no spatial faces, the temporal decoder sums the two endpoint
impulses modulo two. Thus their total charge is even. No slab-size,
three-layer-window, spin or weight assumption enters this argument.
-/

import YMGap.Continuum.Z4SpatialDefectTemporalDecoder

namespace YMGap.Continuum.Z4FiniteTemporalEndpointParity

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4TemporalSpatialIncidence
open YMGap.Continuum.Z4TemporalCutParityMinimum
open YMGap.Continuum.Z4UnitCubeIncidenceParity
open YMGap.Continuum.Z4SpatialDefectTemporalDecoder

def timeCeiling : List Z4Plaq → Nat
  | [] => 0
  | face::faces => max (face.1.2.2.2+1) (timeCeiling faces)

theorem cut_above_ceiling (time : Nat) : ∀ faces : List Z4Plaq,
    timeCeiling faces ≤ time → cut time faces = []
  | [] => fun _ => rfl
  | face::faces => by
    intro ht
    have hf : face.1.2.2.2 < time := by
      have h := Nat.le_max_left (face.1.2.2.2+1) (timeCeiling faces)
      change max (face.1.2.2.2+1) (timeCeiling faces) ≤ time at ht
      omega
    have hs : timeCeiling faces ≤ time := Nat.le_trans (Nat.le_max_right _ _) ht
    have hx : crosses time face = false := by
      simp only [crosses, Nat.ne_of_lt hf, and_false, decide_false]
    simpa only [cut, List.filter_cons, hx, Bool.false_eq_true, ↓reduceIte] using
      cut_above_ceiling time faces hs

def twoImpulses (lower upper a b time : Nat) : Nat :=
  (if time = lower then a else 0) + (if time = upper then b else 0)

theorem impulse_step (lower a time : Nat) :
    (if time+1 = lower then a else 0) + (if lower ≤ time then a else 0) =
      (if lower ≤ time+1 then a else 0) := by
  by_cases he : time+1 = lower <;> by_cases hl : lower ≤ time <;>
    by_cases hn : lower ≤ time+1
  all_goals simp only [he, hl, hn, Nat.le_refl, ↓reduceIte]
  all_goals omega

theorem two_impulses_decode (lower upper a b : Nat) : ∀ time,
    temporalBit (twoImpulses lower upper a b) (fun _ => 0) time =
      ((if lower ≤ time then a else 0) + (if upper ≤ time then b else 0)) % 2
  | 0 => by
    simp only [temporalBit, twoImpulses, Nat.add_zero, Nat.le_zero_eq, eq_comm]
  | time+1 => by
    rw [temporalBit, two_impulses_decode lower upper a b time]
    simp only [twoImpulses, Nat.add_zero]
    have hl := impulse_step lower a time
    have hu := impulse_step upper b time
    omega

theorem endpoint_sum_even (lower upper a b : Nat) (link : Z4Link)
    (hd : link.2 ≠ Dir4.x3) (faces : List Z4Plaq) (hn : faces.Nodup)
    (hs : spatialFaces faces = [])
    (hp : ∀ time, (twoImpulses lower upper a b time +
      faceIncidenceCount (atTime time link) faces) % 2 = 0) :
    (a+b) % 2 = 0 := by
  let time := max (timeCeiling faces) (max lower upper)
  have hc := cutCount_decode (twoImpulses lower upper a b) link hd faces hn hp time
  have hz : cutCount time link faces = 0 := by
    rw [cutCount, cut_above_ceiling time faces (Nat.le_max_left _ _)]
    rfl
  have hl : lower ≤ time := Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  have hu : upper ≤ time := Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  rw [hs] at hc
  change cutCount time link faces = temporalBit (twoImpulses lower upper a b) (fun _ => 0) time at hc
  rw [two_impulses_decode, if_pos hl, if_pos hu, hz] at hc
  exact hc.symm

end YMGap.Continuum.Z4FiniteTemporalEndpointParity

#print axioms YMGap.Continuum.Z4FiniteTemporalEndpointParity.timeCeiling
#print axioms YMGap.Continuum.Z4FiniteTemporalEndpointParity.cut_above_ceiling
#print axioms YMGap.Continuum.Z4FiniteTemporalEndpointParity.twoImpulses
#print axioms YMGap.Continuum.Z4FiniteTemporalEndpointParity.impulse_step
#print axioms YMGap.Continuum.Z4FiniteTemporalEndpointParity.two_impulses_decode
#print axioms YMGap.Continuum.Z4FiniteTemporalEndpointParity.endpoint_sum_even
