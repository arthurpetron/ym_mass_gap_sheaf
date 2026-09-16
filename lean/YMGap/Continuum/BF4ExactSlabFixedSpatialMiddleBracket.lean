/-
# Two-sided forgetting for the actual finite interior ratio

Multiply the signed probe's certified interval by the actual left message,
then iterate the resulting relative bracket. Weighted symmetry identifies
its mass ratio with the interior pairing, not an evolved endpoint probe.
Nested right-boundary brackets give a geometric comparison independent of
the left length. Swapping the two messages gives the other comparison.

Two hops control every pair of interior ratios whose four boundary lengths
exceed the same threshold. Nome and spatial width remain fixed; the rate is
independent of late heat cutoff, not of width or physical lattice spacing.
No stationary law, physical OS identification or mass gap is asserted.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialMiddleRatioPins

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialMiddleBracket

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactSlabTemporalSweep (FaceFactor)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracketDecay
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracketNesting
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddleRatioPins
open YMGap.Continuum.BF4ExactSlabFixedSpatialProbe
open YMGap.Continuum.BF4ExactSlabFixedSpatialProbeInterval
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv

attribute [local irreducible] weightedMass kineticWeight spatialWeight baseLinks mixRate middleRatio

/-- The initial comparison retains the whole left message and its shared
coordinates. Its endpoints are exactly -c and c. -/
def intervalTimesMessage {width : Nat} {p g : RatPoly} {c : Q'}
    (I : Interval (N width) p c) (G : Certificate (N width) g) :
    Bracket width (polyMul g p) g :=
  let B := multiplyBracket (ofInterval I) G
  { lower := B.lower
    upper := B.upper
    lowerCertificate := Certificate.ofCoeff
      ((RatPolyCoeffEqv.refl _).add ((RatPolyCoeffEqv.mul_one g).symm.smul (-B.lower)))
      B.lowerCertificate
    upperCertificate := Certificate.ofCoeff
      (((RatPolyCoeffEqv.mul_one g).symm.smul B.upper).add (RatPolyCoeffEqv.refl _))
      B.upperCertificate }

/-- Inhabited n-step bracket for the middle probe multiplied by u_m,
compared against the SAME u_m. No positivity of the signed probe is needed. -/
def middleBracket {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (m n : Nat) (fs : List FaceFactor) :
    Bracket width
      (iterateStep (N width) (kineticWeight w K width) (spatialWeight w K width) n
        (polyMul (terminalMessage w K width m) (sourceProbe width fs)))
      (iterateStep (N width) (kineticWeight w K width) (spatialWeight w K width) n
        (terminalMessage w K width m)) :=
  iterateBracket hw0 hw1 K width hK n
    (supported_polyMul (terminalMessage_supported w K width m) (sourceProbe_supported width fs))
    (terminalMessage_supported w K width m)
    (terminalMessage_certificate hw0 hw1 K width hK m)
    (terminalMessage_mass_positive hw0 hw1 K width hK m)
    (intervalTimesMessage (sourceProbe_interval width fs)
      (terminalMessage_certificate hw0 hw1 K width hK m))

/-- The width is independent of the left-message length m. -/
theorem middleBracket_width {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (m n : Nat) (fs : List FaceFactor) :
    (middleBracket hw0 hw1 K width hK m n fs).upper +
        -(middleBracket hw0 hw1 K width hK m n fs).lower ≈
      mixRate hw0 hw1 width ^ n * (probeCap fs + probeCap fs) :=
  Q'.eqv_trans _ _ _
    (iterateBracket_width hw0 hw1 K width hK n
      (supported_polyMul (terminalMessage_supported w K width m) (sourceProbe_supported width fs))
      (terminalMessage_supported w K width m)
      (terminalMessage_certificate hw0 hw1 K width hK m)
      (terminalMessage_mass_positive hw0 hw1 K width hK m)
      (intervalTimesMessage (sourceProbe_interval width fs)
        (terminalMessage_certificate hw0 hw1 K width hK m)))
    (Q'.mul_eqv_congr_left _ _ _ (Q'.add_eqv_congr'
      (Q'.eqv_refl _) (Q'.neg_neg_eqv (probeCap fs))))

/-- Actual interior ratio, not terminalProbeRatio, is in this computed bracket. -/
theorem middleRatio_bounds {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (m n : Nat) (fs : List FaceFactor) :
    (middleBracket hw0 hw1 K width hK m n fs).lower ≤
        middleRatio hw0 hw1 K width hK m n (sourceProbe width fs) ∧
      middleRatio hw0 hw1 K width hK m n (sourceProbe width fs) ≤
        (middleBracket hw0 hw1 K width hK m n fs).upper := by
  have he := middleRatio_iterate hw0 hw1 K width hK m n (sourceProbe_supported width fs)
  have hb := massRatio_bounds hw0 hw1 K width hK
    (iterateWeightedMass_positive hw0 hw1 K width hK n
      (terminalMessage_supported w K width m)
      (terminalMessage_certificate hw0 hw1 K width hK m)
      (terminalMessage_mass_positive hw0 hw1 K width hK m))
    (middleBracket hw0 hw1 K width hK m n fs)
  exact ⟨Q'.le_trans' _ _ _ hb.1 (Q'.ge_of_eqv he),
    Q'.le_trans' _ _ _ (Q'.le_of_eqv he) hb.2⟩

/-- Retaining the same initial left message gives nested right-boundary intervals. -/
theorem middleBracket_nested {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (m n j : Nat) (fs : List FaceFactor) (hnj : n ≤ j) :
    (middleBracket hw0 hw1 K width hK m n fs).lower ≤
        (middleBracket hw0 hw1 K width hK m j fs).lower ∧
      (middleBracket hw0 hw1 K width hK m j fs).upper ≤
        (middleBracket hw0 hw1 K width hK m n fs).upper :=
  iterateBracket_nested hw0 hw1 K width hK n j hnj
    (supported_polyMul (terminalMessage_supported w K width m) (sourceProbe_supported width fs))
    (terminalMessage_supported w K width m)
    (terminalMessage_certificate hw0 hw1 K width hK m)
    (terminalMessage_mass_positive hw0 hw1 K width hK m)
    (intervalTimesMessage (sourceProbe_interval width fs)
      (terminalMessage_certificate hw0 hw1 K width hK m))

theorem middleRatio_later_bounds {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (m n j : Nat) (fs : List FaceFactor) (hnj : n ≤ j) :
    (middleBracket hw0 hw1 K width hK m n fs).lower ≤
        middleRatio hw0 hw1 K width hK m j (sourceProbe width fs) ∧
      middleRatio hw0 hw1 K width hK m j (sourceProbe width fs) ≤
        (middleBracket hw0 hw1 K width hK m n fs).upper := by
  have hn := middleBracket_nested hw0 hw1 K width hK m n j fs hnj
  have hb := middleRatio_bounds hw0 hw1 K width hK m j fs
  exact ⟨Q'.le_trans' _ _ _ hn.1 hb.1, Q'.le_trans' _ _ _ hb.2 hn.2⟩

private theorem common_interval (l u x y C : Q')
    (hx : l ≤ x ∧ x ≤ u) (hy : l ≤ y ∧ y ≤ u) (hc : u + -l ≈ C) :
    x ≤ y+C ∧ y ≤ x+C := by
  have hcancel : l + (u + -l) ≈ u := poly_identity_of_normal_eq
    (.add (.var 0) (.add (.var 1) (.neg (.var 0)))) (.var 1) (by decide)
    (fun | 0 => l | _ => u)
  have hup (z : Q') (hz : l ≤ z) : u ≤ z+C :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hcancel)
      (Q'.le_trans' _ _ _ (Q'.add_le_add_right l z (u + -l) hz)
        (Q'.le_of_eqv (Q'.add_eqv_congr' (Q'.eqv_refl z) hc)))
  exact ⟨Q'.le_trans' _ _ _ hx.2 (hup y hy.1), Q'.le_trans' _ _ _ hy.2 (hup x hx.1)⟩

/-- Every two later right boundaries are compared uniformly in the left length. -/
theorem middleRatio_right_commonTail {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (m s n j : Nat) (fs : List FaceFactor)
    (hsn : s ≤ n) (hsj : s ≤ j) :
    middleRatio hw0 hw1 K width hK m n (sourceProbe width fs) ≤
        middleRatio hw0 hw1 K width hK m j (sourceProbe width fs) +
          mixRate hw0 hw1 width ^ s * (probeCap fs + probeCap fs) ∧
      middleRatio hw0 hw1 K width hK m j (sourceProbe width fs) ≤
        middleRatio hw0 hw1 K width hK m n (sourceProbe width fs) +
          mixRate hw0 hw1 width ^ s * (probeCap fs + probeCap fs) :=
  common_interval _ _ _ _ _
    (middleRatio_later_bounds hw0 hw1 K width hK m s n fs hsn)
    (middleRatio_later_bounds hw0 hw1 K width hK m s j fs hsj)
    (middleBracket_width hw0 hw1 K width hK m s fs)

private theorem two_hops (x y z r c : Q') (hxy : x ≤ y+r*c) (hyz : y ≤ z+r*c) :
    x ≤ z+r*(c+c) :=
  Q'.le_trans' _ _ _ hxy
    (Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ (r*c) hyz)
      (Q'.le_of_eqv (poly_identity_of_normal_eq
        (.add (.add (.var 0) (.mul (.var 1) (.var 2))) (.mul (.var 1) (.var 2)))
        (.add (.var 0) (.mul (.var 1) (.add (.var 2) (.var 2)))) (by decide)
        (fun | 0 => z | 1 => r | _ => c))))

/-- Quantitative control for independently receding left AND right boundaries.
All four lengths exceed s; no order relation between the two pairs is needed. -/
theorem middleRatio_commonTail {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (s m n i j : Nat) (fs : List FaceFactor)
    (hsm : s ≤ m) (hsn : s ≤ n) (hsi : s ≤ i) (hsj : s ≤ j) :
    middleRatio hw0 hw1 K width hK m n (sourceProbe width fs) ≤
        middleRatio hw0 hw1 K width hK i j (sourceProbe width fs) +
          mixRate hw0 hw1 width ^ s * ((probeCap fs + probeCap fs) + (probeCap fs + probeCap fs)) ∧
      middleRatio hw0 hw1 K width hK i j (sourceProbe width fs) ≤
        middleRatio hw0 hw1 K width hK m n (sourceProbe width fs) +
          mixRate hw0 hw1 width ^ s * ((probeCap fs + probeCap fs) + (probeCap fs + probeCap fs)) := by
  have hr := middleRatio_right_commonTail hw0 hw1 K width hK m s n j fs hsn hsj
  have hl := middleRatio_right_commonTail hw0 hw1 K width hK j s m i fs hsm hsi
  have hm := middleRatio_swap hw0 hw1 K width hK m j (sourceProbe width fs)
  have hi := middleRatio_swap hw0 hw1 K width hK i j (sourceProbe width fs)
  have hforward := Q'.le_trans' _ _ _ (Q'.le_of_eqv hm)
    (Q'.le_trans' _ _ _ hl.1 (Q'.add_le_add_right _ _ _ (Q'.ge_of_eqv hi)))
  have hback := Q'.le_trans' _ _ _ (Q'.le_of_eqv hi)
    (Q'.le_trans' _ _ _ hl.2 (Q'.add_le_add_right _ _ _ (Q'.ge_of_eqv hm)))
  exact ⟨two_hops _ _ _ _ _ hr.1 hforward, two_hops _ _ _ _ _ hback hr.2⟩

end YMGap.Continuum.BF4ExactSlabFixedSpatialMiddleBracket

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialMiddleBracket.intervalTimesMessage
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialMiddleBracket.middleBracket
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialMiddleBracket.middleBracket_width
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialMiddleBracket.middleRatio_bounds
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialMiddleBracket.middleBracket_nested
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialMiddleBracket.middleRatio_later_bounds
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialMiddleBracket.middleRatio_right_commonTail
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialMiddleBracket.middleRatio_commonTail
