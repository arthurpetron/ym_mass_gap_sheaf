/-
# Carrier-polymorphic channel sections and constructive Schur reconstruction

A section of a Clebsch--Gordan channel normally lands in a finite sum of pure
threefold tensors.  The product carrier `TripleForm` from the first abstract
section theorem contains only a single pure tensor, so it is too small for
that concrete construction.

This module leaves the earlier theorem untouched and proves its correct
successor over an arbitrary ambient carrier.  No additive or tensor structure
on the carrier is needed by the Schur argument: only a pure-input packing map,
an evaluation map, channel analyses, and channel sections are used.  A small
constructor fence records that adjoining formal sums really does create
elements outside the pure-product carrier.
-/

import YMGap.Continuum.SU2ChannelSectionSchurReconstruction

namespace YMGap.Continuum.SU2ChannelAmbientSectionSchurReconstruction

open YMGap.Constructive
open YMGap.Continuum.BinaryForms
open YMGap.Continuum.SU2TransvectantLinearity
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2TransvectantCentralChannelEquation
open YMGap.Continuum.SU2ChannelSectionSchurReconstruction

local infix:50 " ≈ " => Q'.eqv

/-! ## A machine-checked carrier fence -/

/-- The smallest syntactic enlargement of pure triples by a formal binary
sum.  It is only a carrier fence; concrete tensor evaluation comes later. -/
inductive FormalTripleCarrier where
  | pure : TripleForm → FormalTripleCarrier
  | sum : TripleForm → TripleForm → FormalTripleCarrier

/-- Package three forms as one pure element of the formal ambient carrier. -/
def formalPurePack (x y z : BForm) : FormalTripleCarrier :=
  FormalTripleCarrier.pure ⟨x, y, z⟩

/-- **Pure-product insufficiency fence.**  Once formal sums are admitted, the
map packaging a single product triple is not surjective.  Hence a concrete CG
section whose value is a sum cannot in general be typed as `TripleForm`. -/
theorem formal_sum_outside_pure_products :
    ∃ u : FormalTripleCarrier,
      ∀ x y z : BForm, formalPurePack x y z ≠ u := by
  let w : TripleForm := ⟨zeroF, zeroF, zeroF⟩
  refine ⟨FormalTripleCarrier.sum w w, ?_⟩
  intro x y z h
  cases h

/-! ## Carrier-polymorphic Schur reconstruction -/

/-- The output endomorphism obtained by evaluating one ambient channel
section. -/
def ambientInduced {Carrier : Type}
    (evalL : Carrier → BForm) (embed : BForm → Carrier) :
    BForm → BForm :=
  fun v => evalL (embed v)

/-- An ambient induced map satisfying the same diagonal and lowering
hypotheses is scalar on the complete physical output window. -/
theorem ambientInduced_eq_scalar {Carrier : Type} (d : Nat)
    (evalL : Carrier → BForm) (embed : BForm → Carrier)
    (coeff : Nat → Q')
    (hdiag : HasDiagonalModel (ambientInduced evalL embed) coeff)
    (hF : EndomorphismLoweringCovariant d
      (ambientInduced evalL embed)) (v : BForm) :
    FormEqv (d + 1) (ambientInduced evalL embed v)
      (scaleForm (coeff 0) v) := by
  exact inducedEndomorphism_eq_scalar d (ambientInduced evalL embed)
    coeff hdiag hF v

/-- Apply the carrier-polymorphic Schur lemma to every term of a finite
channel expansion. -/
theorem ambient_formPrefix_induced_eq_scalar {Carrier : Type}
    (d N : Nat) (evalL : Carrier → BForm)
    (analysis : Nat → Carrier → BForm)
    (embed : Nat → BForm → Carrier)
    (coeff : Nat → Nat → Q')
    (hdiag : ∀ q, q < N → HasDiagonalModel
      (ambientInduced evalL (embed q)) (coeff q))
    (hF : ∀ q, q < N → EndomorphismLoweringCovariant d
      (ambientInduced evalL (embed q))) (u : Carrier) :
    FormEqv (d + 1)
      (formPrefix N (fun q =>
        ambientInduced evalL (embed q) (analysis q u)))
      (formPrefix N (fun q =>
        scaleForm (coeff q 0) (analysis q u))) := by
  exact formPrefix_congr_window N (d + 1) _ _ (fun q hq =>
    ambientInduced_eq_scalar d evalL (embed q) (coeff q)
      (hdiag q hq) (hF q hq) (analysis q u))

/-- **Ambient section-to-Schur reconstruction theorem.**

`pack` includes pure triples in an arbitrary carrier, `evalL` extends the
trilinear map to that carrier, `analysis` extracts channel outputs, and
`embed` is a channel section.  The proof uses no further carrier operations.
The two reconstruction hypotheses are deliberately separated: first pure
evaluation agrees with `L`, then the evaluated packed input is reconstructed
through the analyzed channel sections. -/
theorem triMapEqv_of_ambient_channelSections_schur
    (Carrier : Type) (a b c d N : Nat)
    (L : BForm → BForm → BForm → BForm)
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
            (analysis q (pack (mono i) (mono j) (mono l)))))) :
    TriMapEqv a b c d L
      (fun x y z => formPrefix N (fun q =>
        scaleForm (coeff q 0) (analysis q (pack x y z)))) := by
  intro i hi j hj l hl s hs
  exact Q'.eqv_trans _ _ _ (hpack i hi j hj l hl s)
    (Q'.eqv_trans _ _ _ (hreconstruct i hi j hj l hl s)
      (ambient_formPrefix_induced_eq_scalar d N evalL analysis embed
        coeff hdiag hF (pack (mono i) (mono j) (mono l)) s hs))

/-- Scaling respects unbounded pointwise equality of output forms. -/
theorem scaleForm_congr (q : Q') {x y : BForm} (hxy : BFormEqv x y) :
    BFormEqv (scaleForm q x) (scaleForm q y) := by
  intro s
  exact Q'.mul_eqv_congr_left _ _ _ (hxy s)

/-- **Carrier-polymorphic right-channel F-row theorem.**  The only
specialization of the abstract analysis is its value on packed pure inputs;
the carrier and all section values may contain arbitrary finite sums. -/
theorem triMapEqv_rightChannels_of_ambient_sections_schur
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
    (hanalysis : ∀ q, q < N → ∀ x y z,
      BFormEqv (analysis q (pack x y z))
        (triRight a b c d (rightChannelLabel b c (col q)) x y z)) :
    TriMapEqv a b c d L
      (rightChannelPrefix a b c d N col (fun q => coeff q 0)) := by
  have hgeneric := triMapEqv_of_ambient_channelSections_schur Carrier
    a b c d N L pack evalL analysis embed coeff
    hdiag hF hpack hreconstruct
  intro i hi j hj l hl s hs
  have hanalyzed : BFormEqv
      (formPrefix N (fun q => scaleForm (coeff q 0)
        (analysis q (pack (mono i) (mono j) (mono l)))))
      (formPrefix N (fun q => scaleForm (coeff q 0)
        (triRight a b c d (rightChannelLabel b c (col q))
          (mono i) (mono j) (mono l)))) := by
    exact formPrefix_congr N _ _ (fun q hq =>
      scaleForm_congr (coeff q 0)
        (hanalysis q hq (mono i) (mono j) (mono l)))
  exact Q'.eqv_trans _ _ _ (hgeneric i hi j hj l hl s hs)
    (Q'.eqv_trans _ _ _ (hanalyzed s)
      (formPrefix_rightChannels a b c d N col
        (fun q => coeff q 0) ⟨mono i, mono j, mono l⟩ s))

end YMGap.Continuum.SU2ChannelAmbientSectionSchurReconstruction

#print axioms YMGap.Continuum.SU2ChannelAmbientSectionSchurReconstruction.formal_sum_outside_pure_products
#print axioms YMGap.Continuum.SU2ChannelAmbientSectionSchurReconstruction.ambientInduced_eq_scalar
#print axioms YMGap.Continuum.SU2ChannelAmbientSectionSchurReconstruction.ambient_formPrefix_induced_eq_scalar
#print axioms YMGap.Continuum.SU2ChannelAmbientSectionSchurReconstruction.triMapEqv_of_ambient_channelSections_schur
#print axioms YMGap.Continuum.SU2ChannelAmbientSectionSchurReconstruction.triMapEqv_rightChannels_of_ambient_sections_schur
