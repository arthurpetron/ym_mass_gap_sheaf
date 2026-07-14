/-
# A constructive balanced four-factor CG coordinate basis

The balanced chart first applies the actual all-label CG coordinates
independently to `(a,b)` and `(c,d)`, then couples the two output forms.  Its
dependent channel records both pair contraction orders and the final physical
channel.  Explicit nested Hahn reconstruction proves both round trips on the
complete four-factor coefficient box without any cyclic-normalization bridge.
-/

import YMGap.Continuum.SU2GeneralHahnLeftCombFourCoordinateBases

namespace YMGap.Continuum.SU2GeneralHahnBalancedFourCoordinateBases

open YMGap.Constructive
open YMGap.Continuum.TransvectantCG
open YMGap.Continuum.SU2GeneralHahnGlobalSourceReconstruction
open YMGap.Continuum.SU2GeneralHahnGlobalCoordinateEquivalence
open YMGap.Continuum.SU2GeneralHahnPhysicalRectangleProjection
open YMGap.Continuum.SU2GeneralHahnGlobalTransvectantCoordinates
open YMGap.Continuum.SU2GeneralHahnGlobalCoordinateBases
open YMGap.Continuum.SU2GeneralHahnLeftCombFourCoordinateBases
open YMGap.Continuum.PentagonFromCoordinateBases

local infix:50 " ≈ " => Q'.eqv

/-- A balanced four-factor channel: one order for each input pair, followed by
an arbitrary physical channel between the two output forms. -/
structure Balanced4Channel (a b c d : Nat) where
  kL : Nat
  kL_le : kL ≤ min a b
  kR : Nat
  kR_le : kR ≤ min c d
  outer : PhysicalCGChannel (a + b - 2 * kL) (c + d - 2 * kR)

/-- At fixed left-pair order and output coefficient, retain the `(c,d)`
coefficient tensor. -/
def leftPairCoefficient (a b : Nat) (x : QuadForm)
    (kL u : Nat) : BForm2 :=
  fun l r => transvect a b kL
    (rectProject a b (fun i j => x i j l r)) u

/-- The two independently transformed pair outputs as one coefficient tensor. -/
def pairPairOutput (a b c d : Nat) (x : QuadForm)
    (kL kR : Nat) : BForm2 :=
  fun u v => transvect c d kR
    (rectProject c d (leftPairCoefficient a b x kL u)) v

/-- Extract final-channel data at fixed pair orders. -/
def balancedOuterData {a b c d : Nat}
    (coeff : Balanced4Channel a b c d → Q')
    (kL : Nat) (hkL : kL ≤ min a b)
    (kR : Nat) (hkR : kR ≤ min c d) :
    PhysicalCGChannel (a + b - 2 * kL) (c + d - 2 * kR) → Q' :=
  fun q => coeff ⟨kL, hkL, kR, hkR, q⟩

/-- Reconstruct the two output forms at fixed pair orders. -/
def balancedOuterReconstruct {a b c d : Nat}
    (coeff : Balanced4Channel a b c d → Q')
    (kL : Nat) (hkL : kL ≤ min a b)
    (kR : Nat) (hkR : kR ≤ min c d) : BForm2 :=
  globalHahnReconstruct (a + b - 2 * kL) (c + d - 2 * kR)
    (balancedOuterData coeff kL hkL kR hkR)

/-- For one complete left-pair channel, collect every right-pair channel. -/
def balancedRightData {a b c d : Nat}
    (coeff : Balanced4Channel a b c d → Q')
    (qL : PhysicalCGChannel a b) : PhysicalCGChannel c d → Q' :=
  fun qR => balancedOuterReconstruct coeff
    qL.k qL.k_le qR.k qR.k_le qL.s qR.s

/-- Reconstruct the right pair for every left-pair channel. -/
def balancedLeftData {a b c d : Nat}
    (coeff : Balanced4Channel a b c d → Q') (l r : Nat) :
    PhysicalCGChannel a b → Q' :=
  fun qL => globalHahnReconstruct c d (balancedRightData coeff qL) l r

/-- Explicit synthesis for the balanced chart. -/
def balanced4Reconstruct (a b c d : Nat)
    (coeff : Balanced4Channel a b c d → Q') : QuadForm :=
  fun i j l r => globalHahnReconstruct a b
    (balancedLeftData coeff l r) i j

/-- Actual three-stage coordinates for the balanced chart. -/
def balanced4Coordinates (a b c d : Nat) (x : QuadForm) :
    Balanced4Channel a b c d → Q' :=
  fun q => globalTransvectCoordinates
    (a + b - 2 * q.kL) (c + d - 2 * q.kR)
    (pairPairOutput a b c d x q.kL q.kR) q.outer

private def leftChannel (a b k u : Nat) (hk : k ≤ min a b)
    (hu : u ≤ a + b - 2 * k) : PhysicalCGChannel a b :=
  { k := k, k_le := hk, s := u, s_le := hu }

private def rightChannel (c d k v : Nat) (hk : k ≤ min c d)
    (hv : v ≤ c + d - 2 * k) : PhysicalCGChannel c d :=
  { k := k, k_le := hk, s := v, s_le := hv }

/-- The synthesized tensor's left-pair coordinate is the reconstructed right
pair associated to that left channel. -/
theorem leftPairCoefficient_reconstruct (a b c d : Nat)
    (coeff : Balanced4Channel a b c d → Q')
    (kL : Nat) (hkL : kL ≤ min a b) (u l r : Nat)
    (hu : u ≤ a + b - 2 * kL) :
    leftPairCoefficient a b (balanced4Reconstruct a b c d coeff) kL u l r ≈
      globalHahnReconstruct c d
        (balancedRightData coeff (leftChannel a b kL u hkL hu)) l r := by
  let qL := leftChannel a b kL u hkL hu
  have hright := Q'.eqv_trans _ _ _
    (globalTransvectCoordinates_eq_hahn a b
      (globalHahnReconstruct a b (balancedLeftData coeff l r)) qL)
    (globalHahnCoordinates_reconstruct a b (balancedLeftData coeff l r) qL)
  simpa only [leftPairCoefficient, balanced4Reconstruct, balancedLeftData,
    qL, leftChannel, globalTransvectCoordinates] using hright

/-- After full synthesis, the independently transformed pair tensor is the
corresponding reconstructed outer tensor. -/
theorem pairPairOutput_reconstruct (a b c d : Nat)
    (coeff : Balanced4Channel a b c d → Q')
    (kL : Nat) (hkL : kL ≤ min a b)
    (kR : Nat) (hkR : kR ≤ min c d)
    (u v : Nat) (hu : u ≤ a + b - 2 * kL)
    (hv : v ≤ c + d - 2 * kR) :
    pairPairOutput a b c d (balanced4Reconstruct a b c d coeff)
        kL kR u v ≈
      balancedOuterReconstruct coeff kL hkL kR hkR u v := by
  let qL := leftChannel a b kL u hkL hu
  let qR := rightChannel c d kR v hkR hv
  have hrel : PhysicalRectangleEqv c d
      (leftPairCoefficient a b (balanced4Reconstruct a b c d coeff) kL u)
      (globalHahnReconstruct c d (balancedRightData coeff qL)) := by
    intro l r hl hr
    exact leftPairCoefficient_reconstruct a b c d coeff kL hkL u l r hu
  have hcongr := globalTransvectCoordinates_congr c d
    (leftPairCoefficient a b (balanced4Reconstruct a b c d coeff) kL u)
    (globalHahnReconstruct c d (balancedRightData coeff qL)) hrel qR
  have hright := Q'.eqv_trans _ _ _
    (globalTransvectCoordinates_eq_hahn c d
      (globalHahnReconstruct c d (balancedRightData coeff qL)) qR)
    (globalHahnCoordinates_reconstruct c d (balancedRightData coeff qL) qR)
  exact Q'.eqv_trans _ _ _
    (by simpa only [pairPairOutput, qR, rightChannel,
      globalTransvectCoordinates] using hcongr)
    (by simpa only [balancedRightData, qL, qR, leftChannel, rightChannel]
      using hright)

/-- Independent pair output respects equality of the physical four-box. -/
theorem pairPairOutput_congr (a b c d : Nat) (x z : QuadForm)
    (hxz : PhysicalQuadBoxEqv a b c d x z)
    (kL : Nat) (hkL : kL ≤ min a b)
    (kR : Nat) (hkR : kR ≤ min c d) :
    PhysicalRectangleEqv (a + b - 2 * kL) (c + d - 2 * kR)
      (pairPairOutput a b c d x kL kR)
      (pairPairOutput a b c d z kL kR) := by
  intro u v hu hv
  let qL := leftChannel a b kL u hkL hu
  let qR := rightChannel c d kR v hkR hv
  have hleft : PhysicalRectangleEqv c d
      (leftPairCoefficient a b x kL u)
      (leftPairCoefficient a b z kL u) := by
    intro l r hl hr
    have hs : PhysicalRectangleEqv a b
        (fun i j => x i j l r) (fun i j => z i j l r) := by
      intro i j hi hj
      exact hxz i j l r hi hj hl hr
    have hc := globalTransvectCoordinates_congr a b
      (fun i j => x i j l r) (fun i j => z i j l r) hs qL
    simpa only [leftPairCoefficient, qL, leftChannel,
      globalTransvectCoordinates] using hc
  have hc := globalTransvectCoordinates_congr c d
    (leftPairCoefficient a b x kL u)
    (leftPairCoefficient a b z kL u) hleft qR
  simpa only [pairPairOutput, qR, rightChannel,
    globalTransvectCoordinates] using hc

/-- Balanced coordinates respect equality of the source box. -/
theorem balanced4Coordinates_congr (a b c d : Nat) (x z : QuadForm)
    (hxz : PhysicalQuadBoxEqv a b c d x z)
    (q : Balanced4Channel a b c d) :
    balanced4Coordinates a b c d x q ≈ balanced4Coordinates a b c d z q := by
  exact globalTransvectCoordinates_congr
    (a + b - 2 * q.kL) (c + d - 2 * q.kR)
    (pairPairOutput a b c d x q.kL q.kR)
    (pairPairOutput a b c d z q.kL q.kR)
    (pairPairOutput_congr a b c d x z hxz
      q.kL q.kL_le q.kR q.kR_le) q.outer

/-- **Balanced coordinate right inverse.** -/
theorem balanced4Coordinates_reconstruct (a b c d : Nat)
    (coeff : Balanced4Channel a b c d → Q')
    (q : Balanced4Channel a b c d) :
    balanced4Coordinates a b c d (balanced4Reconstruct a b c d coeff) q ≈
      coeff q := by
  cases q with
  | mk kL hkL kR hkR outer =>
      have hrel : PhysicalRectangleEqv
          (a + b - 2 * kL) (c + d - 2 * kR)
          (pairPairOutput a b c d (balanced4Reconstruct a b c d coeff)
            kL kR)
          (balancedOuterReconstruct coeff kL hkL kR hkR) := by
        intro u v hu hv
        exact pairPairOutput_reconstruct a b c d coeff
          kL hkL kR hkR u v hu hv
      have hcongr := globalTransvectCoordinates_congr
        (a + b - 2 * kL) (c + d - 2 * kR)
        (pairPairOutput a b c d (balanced4Reconstruct a b c d coeff) kL kR)
        (balancedOuterReconstruct coeff kL hkL kR hkR) hrel outer
      have hright := Q'.eqv_trans _ _ _
        (globalTransvectCoordinates_eq_hahn
          (a + b - 2 * kL) (c + d - 2 * kR)
          (balancedOuterReconstruct coeff kL hkL kR hkR) outer)
        (globalHahnCoordinates_reconstruct
          (a + b - 2 * kL) (c + d - 2 * kR)
          (balancedOuterData coeff kL hkL kR hkR) outer)
      exact Q'.eqv_trans _ _ _ hcongr
        (by simpa only [balancedOuterReconstruct, balancedOuterData] using hright)

/-- Reconstructing the right pair from analyzed balanced data recovers the
left-pair coefficient tensor. -/
theorem balancedLeftData_coordinates (a b c d : Nat) (x : QuadForm)
    (l r : Nat) (hl : l ≤ c) (hr : r ≤ d)
    (qL : PhysicalCGChannel a b) :
    balancedLeftData (balanced4Coordinates a b c d x) l r qL ≈
      leftPairCoefficient a b x qL.k qL.s l r := by
  let direct : PhysicalCGChannel c d → Q' :=
    globalTransvectCoordinates c d (leftPairCoefficient a b x qL.k qL.s)
  have hdata : ∀ qR : PhysicalCGChannel c d,
      balancedRightData (balanced4Coordinates a b c d x) qL qR ≈
        direct qR := by
    intro qR
    have hout := globalHahnReconstruct_transvectCoordinates
      (a + b - 2 * qL.k) (c + d - 2 * qR.k)
      (pairPairOutput a b c d x qL.k qR.k)
      qL.s qR.s qL.s_le qR.s_le
    simpa only [balancedRightData, balancedOuterReconstruct,
      balancedOuterData, balanced4Coordinates, direct, pairPairOutput,
      globalTransvectCoordinates] using hout
  have hcongr := globalHahnReconstruct_congr c d
    (balancedRightData (balanced4Coordinates a b c d x) qL) direct hdata
    l r hl hr
  have hright := globalHahnReconstruct_transvectCoordinates c d
    (leftPairCoefficient a b x qL.k qL.s) l r hl hr
  exact Q'.eqv_trans _ _ _
    (by simpa only [balancedLeftData] using hcongr)
    (by simpa only [direct] using hright)

/-- **Balanced semantic left inverse.** -/
theorem balanced4Reconstruct_coordinates (a b c d : Nat) (x : QuadForm)
    (i j l r : Nat) (hi : i ≤ a) (hj : j ≤ b)
    (hl : l ≤ c) (hr : r ≤ d) :
    balanced4Reconstruct a b c d (balanced4Coordinates a b c d x)
        i j l r ≈ x i j l r := by
  let direct : PhysicalCGChannel a b → Q' :=
    globalTransvectCoordinates a b (fun i j => x i j l r)
  have hdata : ∀ qL : PhysicalCGChannel a b,
      balancedLeftData (balanced4Coordinates a b c d x) l r qL ≈
        direct qL := by
    intro qL
    have hleft := balancedLeftData_coordinates a b c d x l r hl hr qL
    exact Q'.eqv_trans _ _ _ hleft (Q'.eqv_refl _)
  have hcongr := globalHahnReconstruct_congr a b
    (balancedLeftData (balanced4Coordinates a b c d x) l r) direct hdata
    i j hi hj
  have hright := globalHahnReconstruct_transvectCoordinates a b
    (fun i j => x i j l r) i j hi hj
  exact Q'.eqv_trans _ _ _
    (by simpa only [balanced4Reconstruct] using hcongr)
    (by simpa only [direct] using hright)

/-- The actual balanced four-factor coordinate basis. -/
def balanced4CoordinateBases (a b c d : Nat) :
    CoordinateBases Unit QuadForm where
  Index := fun _ => Balanced4Channel a b c d
  Rel := PhysicalQuadBoxEqv a b c d
  rel_refl := fun x i j l r hi hj hl hr => Q'.eqv_refl _
  rel_symm := fun h i j l r hi hj hl hr =>
    Q'.eqv_symm (h i j l r hi hj hl hr)
  rel_trans := fun h₁ h₂ i j l r hi hj hl hr =>
    Q'.eqv_trans _ _ _ (h₁ i j l r hi hj hl hr)
      (h₂ i j l r hi hj hl hr)
  synth := fun _ coeff => balanced4Reconstruct a b c d coeff
  coords := fun _ x => balanced4Coordinates a b c d x
  coords_congr := by
    intro T x z hxz q
    exact balanced4Coordinates_congr a b c d x z hxz q
  synth_coords := by
    intro T x i j l r hi hj hl hr
    exact balanced4Reconstruct_coordinates a b c d x i j l r hi hj hl hr
  coords_synth := by
    intro T coeff q
    exact balanced4Coordinates_reconstruct a b c d coeff q

end YMGap.Continuum.SU2GeneralHahnBalancedFourCoordinateBases

#print axioms YMGap.Continuum.SU2GeneralHahnBalancedFourCoordinateBases.leftPairCoefficient_reconstruct
#print axioms YMGap.Continuum.SU2GeneralHahnBalancedFourCoordinateBases.pairPairOutput_reconstruct
#print axioms YMGap.Continuum.SU2GeneralHahnBalancedFourCoordinateBases.pairPairOutput_congr
#print axioms YMGap.Continuum.SU2GeneralHahnBalancedFourCoordinateBases.balanced4Coordinates_congr
#print axioms YMGap.Continuum.SU2GeneralHahnBalancedFourCoordinateBases.balanced4Coordinates_reconstruct
#print axioms YMGap.Continuum.SU2GeneralHahnBalancedFourCoordinateBases.balancedLeftData_coordinates
#print axioms YMGap.Continuum.SU2GeneralHahnBalancedFourCoordinateBases.balanced4Reconstruct_coordinates
#print axioms YMGap.Continuum.SU2GeneralHahnBalancedFourCoordinateBases.balanced4CoordinateBases
