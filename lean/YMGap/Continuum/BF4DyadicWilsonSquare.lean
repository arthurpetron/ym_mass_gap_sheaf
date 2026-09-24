/-
# A geometrically scaled family of ORIGINAL Wilson squares

The literal square has side 2^s links and assigned lattice spacing 2^(-s),
so its geometric side is exactly one and perimeter exactly four. The spacing
has an explicit modulus. Every member is an actual SourceLoop; strict spatial
padding activates all its links in the ORIGINAL action.

The existing all-nome Wilson scalar limit bounds its squared increment at
2^s time steps by 384*(2^s)^3*(1-w). This exposes, rather than removes, the
scale cost. The assigned spacing is geometric data, NOT a proved Yang--Mills
coupling trajectory or a physical Hamiltonian calibration. No centered norm
floor, common completed carrier, cross-scale limit or survival is asserted.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSquare
import YMGap.Continuum.BF4WilsonAllNomeTimeIncrement
import YMGap.Continuum.BF4ExactSlabThermodynamicDyadicEnergy

namespace YMGap.Continuum.BF4DyadicWilsonSquare

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.HalfPow
open YMGap.Constructive.SU3CharFactor (ofNat_mul_eqv)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe (SourceLoop)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSquare
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonRecenter (recenterLoop)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonBaseInclusion (includeLoop_edges)
open YMGap.Continuum.BF4WilsonAllNomeTimeIncrement

local infix:50 " ≈ " => Q'.eqv

def side (scale : Nat) : Nat := 2^scale

/-- Assigned geometric spacing, not an inferred relation to the coupling. -/
def spacing (scale : Nat) : Q' := half^scale

def square (scale : Nat) : SourceLoop (side scale) := squareLoop (side scale)

theorem side_positive (scale : Nat) : 0 < side scale := Nat.pow_pos (by decide)

theorem spacing_positive (scale : Nat) : (0 : Q') < spacing scale := by
  induction scale with
  | zero => decide
  | succ scale ih => exact Q'.mul_pos (by decide : (0 : Q') < half) ih

def spacingModulus (epsilon : Q') : Nat := epsilon.den

theorem spacing_small (epsilon : Q') (he : (0 : Q') < epsilon)
    (scale : Nat) (hscale : spacingModulus epsilon ≤ scale) :
    spacing scale ≤ epsilon := by
  change epsilon.den ≤ scale at hscale
  have h := ExpNeg.pow_half_antitone epsilon.den (scale-epsilon.den)
  rw [Nat.add_sub_of_le hscale] at h
  exact Q'.le_trans' _ _ _ h (pow_half_le epsilon he)

/-- Reuse only the existing scalar normalization lemma, not its old carrier. -/
theorem unit_side (scale : Nat) : spacing scale * Q'.ofNat (side scale) ≈ 1 :=
  BF4ExactSlabThermodynamicDyadicEnergy.half_power_normalizes scale

theorem square_length (scale : Nat) : (square scale).edges.length = 4*side scale :=
  squareLoop_length (side scale)

theorem unit_perimeter (scale : Nat) :
    spacing scale * Q'.ofNat (square scale).edges.length ≈ 4 := by
  rw [square_length]
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left _ _ _ (ofNat_mul_eqv 4 (side scale))) ?_
  refine Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
    (.mul (.var 0) (.mul (.const 4) (.var 1)))
    (.mul (.const 4) (.mul (.var 0) (.var 1))) (by decide)
    (fun | 0 => spacing scale | _ => Q'.ofNat (side scale))) ?_
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (4 : Q') _ _ (unit_side scale)) (Q'.mul_one_eqv 4)

/-- The actual word is unchanged; only its room witness is enlarged. -/
def paddedSquare (scale width : Nat) (hwidth : side scale < width) : SourceLoop width :=
  recenterLoop (space := 0) (by omega : side scale+0 ≤ width) (square scale)

theorem paddedSquare_edges (scale width : Nat) (hwidth : side scale < width) :
    (paddedSquare scale width hwidth).edges = (square scale).edges :=
  includeLoop_edges (Nat.le_of_lt hwidth) (square scale)

/-- This is the existing ORIGINAL Wilson expectation after cutoff/time-depth
removal at each fixed width and nome. It is not a new completed state. -/
def unitTimeIncrement {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (scale width : Nat) (hwidth : side scale < width) : CReal :=
  timeIncrement hw0 hw1 (paddedSquare scale width hwidth) (side scale)

private theorem length_budget (scale : Nat) (w : Q') :
    Q'.ofNat (side scale) *
        (24*(Q'.ofNat (square scale).edges.length *
          Q'.ofNat (square scale).edges.length)*(1 + -w)) ≈
      (384 : Q') * (Q'.ofNat (side scale) *
        (Q'.ofNat (side scale)*Q'.ofNat (side scale))) * (1 + -w) := by
  rw [square_length]
  have hlen := ofNat_mul_eqv 4 (side scale)
  have hsquare := Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ hlen) (Q'.mul_eqv_congr_left _ _ _ hlen)
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _
    (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_eqv_congr_left _ _ _ hsquare))) ?_
  exact poly_identity_of_normal_eq
    (.mul (.var 0) (.mul (.mul (.const 24)
      (.mul (.mul (.const 4) (.var 0)) (.mul (.const 4) (.var 0)))) (.var 1)))
    (.mul (.mul (.const 384) (.mul (.var 0) (.mul (.var 0) (.var 0)))) (.var 1))
    (by decide) (fun | 0 => Q'.ofNat (side scale) | _ => 1 + -w)

/-- The spatial loop and time separation both have assigned geometric size
one. Their ORIGINAL squared-increment bound retains the cubic inverse-spacing
cost. No nome/spacing relation or surviving norm is supplied. -/
theorem unitTimeIncrement_bound {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (scale width : Nat) (hwidth : side scale < width) :
    leEv (unitTimeIncrement hw0 hw1 scale width hwidth)
      (ofQ' ((384 : Q') * (Q'.ofNat (side scale) *
        (Q'.ofNat (side scale)*Q'.ofNat (side scale))) * (1 + -w))) :=
  leEv_trans (padded_timeIncrement_nome_bound hw0 hw1 hwidth (square scale) (side scale))
    (leEv_ofQ'_of_approx_ge (fun _ => Q'.le_of_eqv (length_budget scale w)))

/-- Exact scalar exposure of the known bound's scale dependence. This is not
a spacetime limit theorem or a renormalization prescription. -/
theorem cubic_spacing_calibration (scale : Nat) (w : Q') :
    (spacing scale*(spacing scale*spacing scale)) *
        ((384 : Q') * (Q'.ofNat (side scale) *
          (Q'.ofNat (side scale)*Q'.ofNat (side scale))) * (1 + -w)) ≈
      (384 : Q') * (1 + -w) := by
  let a := spacing scale
  let L := Q'.ofNat (side scale)
  have h := unit_side scale
  have hcube : (a*L)*((a*L)*(a*L)) ≈ 1 := by
    have hsq := Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ h) (Q'.mul_eqv_congr_left _ _ _ h)
    exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h)
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hsq) (by decide))
  refine Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
    (.mul (.mul (.var 0) (.mul (.var 0) (.var 0)))
      (.mul (.mul (.const 384) (.mul (.var 1) (.mul (.var 1) (.var 1)))) (.var 2)))
    (.mul (.mul (.const 384)
      (.mul (.mul (.var 0) (.var 1))
        (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1))))) (.var 2))
    (by decide) (fun | 0 => a | 1 => L | _ => 1 + -w)) ?_
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_eqv_congr_left _ _ _ hcube))
    (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_one_eqv (384 : Q')))

#print axioms square
#print axioms side_positive
#print axioms spacing_positive
#print axioms spacingModulus
#print axioms spacing_small
#print axioms unit_side
#print axioms square_length
#print axioms unit_perimeter
#print axioms paddedSquare
#print axioms paddedSquare_edges
#print axioms unitTimeIncrement
#print axioms unitTimeIncrement_bound
#print axioms cubic_spacing_calibration

end YMGap.Continuum.BF4DyadicWilsonSquare
