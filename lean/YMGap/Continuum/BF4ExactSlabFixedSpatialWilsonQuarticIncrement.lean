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
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity (SupportedQuaternionBlocks)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
  (polyQuaternionNorm coeffEvalExpr_eqv_of_normalize_eq)
open YMGap.Continuum.BF4ExactSlabTemporalGaugeWilsonWord (wordWith)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (orientedLink)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonKineticIncrement (upperOriented)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonKineticIncrement
  (fundamental_jump_scalar_pin)
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
open YMGap.Continuum.QuaternionHaarUnitScalarSquare (Supported)
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul_left)
open YMGap.Continuum.QuaternionHaarWordDifference
  (difference difference_supported word_supported weighted_scale)
open YMGap.Continuum.QuaternionHaarWordQuartic
open YMGap.Continuum.QuaternionHaarFamilySquare (haar_weighted_add)
open YMGap.Continuum.QuaternionHaarRadialChordalIncrement (radialBudget_pin)
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra (supported_smul)
open YMGap.Continuum.QuaternionHaarWordComponents (component)

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

private def fourth (p : RatPoly) : RatPoly :=
  polyMul (polyMul p p) (polyMul p p)

private theorem fourth_supported {n : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks n p) : SupportedQuaternionBlocks n (fourth p) :=
  supported_polyMul (supported_polyMul hp hp) (supported_polyMul hp hp)

private theorem fourth_double (p : RatPoly) :
    RatPolyCoeffEqv (fourth (polySmul 2 p)) (polySmul 16 (fourth p)) := by
  have h : RatPolyCoeffEqv
      (fourth (polyMul (cap 2) p)) (polyMul (cap 16) (fourth p)) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.mul (.const 2) (.var 0)) (.mul (.const 2) (.var 0)))
        (.mul (.mul (.const 2) (.var 0)) (.mul (.const 2) (.var 0))))
      (.mul (.const 16) (.mul (.mul (.var 0) (.var 0))
        (.mul (.var 0) (.var 0)))) (by decide) (fun _ => p)
  have hc := cap_mul_left 2 p
  exact (((hc.mul hc).mul (hc.mul hc)).symm.trans h).trans
    (cap_mul_left 16 (fourth p))

/-- Actual fourth moment of the fundamental trace jump in the ORIGINAL
two-slice edge law, before normalization. -/
def jumpFourthMoment (w : Q') (K width depth : Nat) (loop : SourceLoop width) : Q' :=
  quaternionHaar (N width+N width)
    (polyMul (edgeDensity w K width (terminalMessage w K width depth))
      (fourth (jump width (sourceCharacter width loop.edges 1))))

/-- The literal trace fourth moment is at most sixteen times the whole-word
chordal fourth moment, under the SAME complete weight. No independence,
active-link estimate or centering substitution is used by this kinematic step. -/
theorem jump_fourth_le_word_square {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (K width depth : Nat)
    (hhead : headCutoff w ≤ K) (loop : SourceLoop width) :
    jumpFourthMoment w K width depth loop ≤
      16*quaternionHaar (N width+N width)
        (polyMul (edgeDensity w K width (terminalMessage w K width depth))
          (polyMul (wordChordal width loop) (wordChordal width loop))) := by
  let W := edgeDensity w K width (terminalMessage w K width depth)
  let d := difference (sourceWord width loop.edges)
    (wordWith (upperOriented width) loop.edges)
  have hd : Supported (N width+N width) d :=
    difference_supported
      (word_supported (orientedLink width) loop.edges
        (fun e he => lower_supported (loop.physical e he)))
      (word_supported (upperOriented width) loop.edges
        (fun e he => upper_supported (loop.physical e he)))
  have hj := jump_supported width (sourceCharacter_supported width loop.edges 1)
  have hp := fundamental_jump_scalar_pin width loop
  have hpin := ((hp.mul hp).mul (hp.mul hp)).haar_insert
    (fourth_supported hj) (fourth_supported (supported_smul hd.scalar 2)) W
    (edgeDensity_supported w K width (terminalMessage_supported w K width depth))
  have hscale : jumpFourthMoment w K width depth loop ≈
      16*quaternionHaar (N width+N width) (polyMul W (fourth d.scalar)) :=
    Q'.eqv_trans _ _ _ hpin
      (Q'.eqv_trans _ _ _ (haar_of_coeff ((fourth_double d.scalar).mul_left W))
        (weighted_scale _ W _ 16))
  have hc := component_fourth_le_norm_square
    (edgeCertificate hw0 hw1 K width hhead (terminalMessage_supported w K width depth)
      (terminalMessage_certificate hw0 hw1 K width hhead depth)) d hd 0
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hscale)
    (Q'.mul_le_mul_of_nonneg_left _ _ 16 hc (by decide))

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
#print axioms jumpFourthMoment
#print axioms jump_fourth_le_word_square
#print axioms radial_moment_split
#print axioms wilson_energy_radial_quartic_cleared

end YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonQuarticIncrement
