/-
# Monomial-exact ambient channel sections and Schur reconstruction

Projected Clebsch--Gordan coordinates agree with raw transvectants on the
physical finite-degree source space, but need not agree on arbitrary
coefficient functions with leakage outside that space.  `TriMapEqv` checks
only the complete physical monomial basis, so the ambient F-row theorem needs
the channel-identification hypothesis only there.  This module records that
strictly weaker and projection-compatible interface.
-/

import YMGap.Continuum.SU2ChannelAmbientSectionSchurReconstruction

namespace YMGap.Continuum.SU2ChannelAmbientMonomialSectionSchurReconstruction

open YMGap.Constructive
open YMGap.Continuum.BinaryForms
open YMGap.Continuum.SU2TransvectantLinearity
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2TransvectantCentralChannelEquation
open YMGap.Continuum.SU2ChannelSectionSchurReconstruction
open YMGap.Continuum.SU2ChannelAmbientSectionSchurReconstruction

local infix:50 " ≈ " => Q'.eqv

/-- **Projection-compatible ambient right-channel F-row theorem.**

Unlike the earlier all-form wrapper, channel analysis is identified with
raw `triRight` only on the physical monomial basis actually quantified by
`TriMapEqv`.  No statement about arbitrary off-degree coefficient functions
is required. -/
theorem triMapEqv_rightChannels_of_ambient_sections_schur_on_monomials
    (Carrier : Type) (a b c d N : Nat)
    (L : BForm → BForm → BForm → BForm)
    (col : Nat → Nat)
    (pack : BForm → BForm → BForm → Carrier)
    (evalL : Carrier → BForm)
    (analysis : Nat → Carrier → BForm)
    (embed : Nat → BForm → Carrier)
    (coeff : Nat → Nat → Q')
    (hdiag : ∀ q, q < N → HasDiagonalModel
      (ambientInduced evalL (embed q)) (coeff q))
    (hF : ∀ q, q < N → EndomorphismLoweringCovariant d
      (ambientInduced evalL (embed q)))
    (hpack : ∀ i, i < a + 1 → ∀ j, j < b + 1 →
      ∀ l, l < c + 1 →
        BFormEqv (L (mono i) (mono j) (mono l))
          (evalL (pack (mono i) (mono j) (mono l))))
    (hreconstruct : ∀ i, i < a + 1 → ∀ j, j < b + 1 →
      ∀ l, l < c + 1 →
        BFormEqv (evalL (pack (mono i) (mono j) (mono l)))
          (formPrefix N (fun q => ambientInduced evalL (embed q)
            (analysis q (pack (mono i) (mono j) (mono l))))))
    (hanalysis : ∀ q, q < N →
      ∀ i, i < a + 1 → ∀ j, j < b + 1 →
      ∀ l, l < c + 1 →
        FormEqv (d + 1)
          (analysis q (pack (mono i) (mono j) (mono l)))
          (triRight a b c d (rightChannelLabel b c (col q))
            (mono i) (mono j) (mono l))) :
    TriMapEqv a b c d L
      (rightChannelPrefix a b c d N col (fun q => coeff q 0)) := by
  have hgeneric := triMapEqv_of_ambient_channelSections_schur Carrier
    a b c d N L pack evalL analysis embed coeff
    hdiag hF hpack hreconstruct
  intro i hi j hj l hl s hs
  have hanalyzed : FormEqv (d + 1)
      (formPrefix N (fun q => scaleForm (coeff q 0)
        (analysis q (pack (mono i) (mono j) (mono l)))))
      (formPrefix N (fun q => scaleForm (coeff q 0)
        (triRight a b c d (rightChannelLabel b c (col q))
          (mono i) (mono j) (mono l)))) := by
    exact formPrefix_congr_window N (d + 1) _ _ (fun q hq t ht =>
      Q'.mul_eqv_congr_left (coeff q 0) _ _
        (hanalysis q hq i hi j hj l hl t ht))
  exact Q'.eqv_trans _ _ _ (hgeneric i hi j hj l hl s hs)
    (Q'.eqv_trans _ _ _ (hanalyzed s hs)
      (formPrefix_rightChannels a b c d N col
        (fun q => coeff q 0) ⟨mono i, mono j, mono l⟩ s))

end YMGap.Continuum.SU2ChannelAmbientMonomialSectionSchurReconstruction

#print axioms YMGap.Continuum.SU2ChannelAmbientMonomialSectionSchurReconstruction.triMapEqv_rightChannels_of_ambient_sections_schur_on_monomials
