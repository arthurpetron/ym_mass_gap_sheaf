/-
# Whole Wilson-word quartic correction in the ORIGINAL edge measure

Every active link has a supplied fourth-moment estimate. The ordered word
telescope lifts it with a fourth power of the literal path length. Feeding
this into the radial trace bound leaves just the mixed radial/chordal moment
unestimated. All spatial and terminal factors and the original odd partition
remain. This is not a centered-variance estimate or a physical scaling theorem.
-/

import YMGap.Continuum.QuaternionHaarWordQuartic
import YMGap.Continuum.BF4ExactSlabFixedSpatialLinkQuartic
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonRadialIncrement

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonQuarticIncrement

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RGTransport (qpow)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics (polyQuaternionNorm)
open YMGap.Continuum.BF4ExactSlabTemporalGaugeWilsonWord (wordWith)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (orientedLink)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonKineticIncrement (upperOriented)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialLinkQuartic
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonRadialIncrement
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHeatQuarticBound (quarticBudget)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap)
open YMGap.Continuum.QuaternionHaarWordDifference (difference weighted_scale)
open YMGap.Continuum.QuaternionHaarWordQuartic
open YMGap.Continuum.QuaternionHaarFamilySquare (haar_weighted_add)
open YMGap.Continuum.QuaternionHaarRadialChordalIncrement (radialBudget_pin)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks terminalMessage oddMass

/-- Squared chordal distance between the SAME ordered lower and upper words. -/
def wordChordal (width : Nat) (loop : SourceLoop width) : RatPoly :=
  polyQuaternionNorm (difference (sourceWord width loop.edges)
    (wordWith (upperOriented width) loop.edges))

/-- Explicit path-length dependence; nome and spin-split dependence is in
`quarticBudget`. There is no hidden volume or depth constant. -/
def wordQuarticRate (w : Q') (S : Nat) {width : Nat} (loop : SourceLoop width) : Q' :=
  wordFourthFactor loop.edges.length * quarticBudget w S

/-- Whole-word fourth moment, with every original measure input supplied.
The active-link condition excludes uncoupled fringe links. -/
theorem word_quartic_bound {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (S K width depth : Nat) (hS : 1 ≤ S) (hK : S+3 ≤ K)
    (hhead : headCutoff w ≤ K) (hhalf : (1 : Q') ≤ 2*w^(4*(S+2)))
    (hq : qpow w (S*S) ≤ Q'.mkPos 1 8 (by decide)) (loop : SourceLoop width)
    (hactive : ∀ e, e ∈ loop.edges → (baseLinks width).idxOf e.link ∈ activeBlocks width) :
    quaternionHaar (N width+N width)
      (polyMul (edgeDensity w K width (terminalMessage w K width depth))
        (polyMul (wordChordal width loop) (wordChordal width loop))) ≤
      wordQuarticRate w S loop * oddMass w K width depth := by
  have h := word_norm_quartic_bound
    (edgeCertificate hw0 hw1 K width hhead (terminalMessage_supported w K width depth)
      (terminalMessage_certificate hw0 hw1 K width hhead depth))
    (orientedLink width) (upperOriented width) loop.edges
    (fun e he => lower_supported (loop.physical e he))
    (fun e he => upper_supported (loop.physical e he))
    (fun e he => lower_unit (loop.physical e he))
    (fun e he => upper_unit (loop.physical e he)) _
    (fun e he => selected_quartic_bound hw0 hw1 S K width depth hS hK hhead hhalf hq e
      (loop.physical e he) (hactive e he))
  exact Q'.le_trans' _ _ _ h (Q'.ge_of_eqv (Q'.mul_assoc_eqv _ _ _))

/-- The remaining mixed moment is kept under the COMPLETE original edge
weight; it is not replaced by a product of expectations. -/
def mixedRadialMoment (w : Q') (K width depth : Nat) (loop : SourceLoop width) : Q' :=
  let f := sourceCharacter width loop.edges 1
  quaternionHaar (N width+N width)
    (polyMul (edgeDensity w K width (terminalMessage w K width depth))
      (polyMul (wordChordal width loop) (polyAdd (cap 4) (polyNeg (polyMul f f)))))

/-- Exact split into the original mixed moment and whole-word fourth moment. -/
theorem radial_moment_split (w : Q') (K width depth : Nat) (loop : SourceLoop width) :
    quaternionHaar (N width+N width)
      (polyMul (edgeDensity w K width (terminalMessage w K width depth))
        (wilsonRadialBudget width loop)) ≈
      2*mixedRadialMoment w K width depth loop +
        2*quaternionHaar (N width+N width)
          (polyMul (edgeDensity w K width (terminalMessage w K width depth))
            (polyMul (wordChordal width loop) (wordChordal width loop))) := by
  let W := edgeDensity w K width (terminalMessage w K width depth)
  exact Q'.eqv_trans _ _ _
    (haar_of_coeff ((radialBudget_pin (sourceWord width loop.edges)
      (wordWith (upperOriented width) loop.edges)).mul_left W))
    (Q'.eqv_trans _ _ _ (haar_weighted_add _ W _ _)
      (Q'.add_eqv_congr' (weighted_scale _ W _ 2) (weighted_scale _ W _ 2)))

/-- The quartic correction is now paid explicitly; the mixed radial moment
and its comparison with SAME centered variance remain an open analytic task. -/
theorem wilson_energy_radial_quartic_cleared {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (S K width depth : Nat) (hS : 1 ≤ S) (hK : S+3 ≤ K)
    (hhead : headCutoff w ≤ K) (hhalf : (1 : Q') ≤ 2*w^(4*(S+2)))
    (hq : qpow w (S*S) ≤ Q'.mkPos 1 8 (by decide)) (loop : SourceLoop width)
    (hactive : ∀ e, e ∈ loop.edges → (baseLinks width).idxOf e.link ∈ activeBlocks width) :
    (2 : Q') * energy w K width (terminalMessage w K width depth)
        (sourceCharacter width loop.edges 1) ≤
      2*mixedRadialMoment w K width depth loop +
        2*(wordQuarticRate w S loop * oddMass w K width depth) := by
  exact Q'.le_trans' _ _ _ (wilson_energy_radial_cleared hw0 hw1 K width hhead depth loop)
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (radial_moment_split w K width depth loop))
      (Q'.add_le_add (Q'.le_refl' _)
        (Q'.mul_le_mul_of_nonneg_left _ _ 2
          (word_quartic_bound hw0 hw1 S K width depth hS hK hhead hhalf hq loop hactive)
          (by decide))))

#print axioms wordQuarticRate
#print axioms word_quartic_bound
#print axioms radial_moment_split
#print axioms wilson_energy_radial_quartic_cleared

end YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonQuarticIncrement
