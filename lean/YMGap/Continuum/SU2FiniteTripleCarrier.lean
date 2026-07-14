/-
# A finite-sum carrier for threefold binary-form tensors

Clebsch--Gordan sections are finite linear combinations of pure threefold
tensors.  This module instantiates the carrier-polymorphic Schur theorem with
an explicit list of rationally weighted pure triples.  Evaluation and every
channel analysis fold the same finite list, while a packed pure input is the
singleton list of weight one.
-/

import YMGap.Continuum.SU2ChannelAmbientSectionSchurReconstruction
import YMGap.Continuum.SU2GeneralHahnGlobalCoordinateBases

namespace YMGap.Continuum.SU2FiniteTripleCarrier

open YMGap.Constructive
open YMGap.Continuum.BinaryForms
open YMGap.Continuum.SU2TransvectantLinearity
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2TransvectantCentralChannelEquation
open YMGap.Continuum.SU2ChannelSectionSchurReconstruction
open YMGap.Continuum.SU2ChannelAmbientSectionSchurReconstruction

local infix:50 " ≈ " => Q'.eqv

/-- One rationally weighted pure threefold tensor. -/
structure WeightedTriple where
  weight : Q'
  tensor : TripleForm

/-- Concrete ambient carrier: a finite formal sum of weighted pure triples. -/
abbrev FiniteTripleCarrier := List WeightedTriple

/-- Include a pure product as a singleton formal sum of weight one. -/
def finiteTriplePack (x y z : BForm) : FiniteTripleCarrier :=
  [⟨1, ⟨x, y, z⟩⟩]

/-- Extend any trilinear output map over a finite weighted carrier. -/
def finiteTripleEval
    (M : BForm → BForm → BForm → BForm) :
    FiniteTripleCarrier → BForm
  | [] => zeroF
  | term :: tail => addForm
      (scaleForm term.weight (evalTriple M term.tensor))
      (finiteTripleEval M tail)

/-- Evaluation of a packed pure triple is the original trilinear value. -/
theorem finiteTripleEval_pack
    (M : BForm → BForm → BForm → BForm) (x y z : BForm) :
    BFormEqv (finiteTripleEval M (finiteTriplePack x y z)) (M x y z) := by
  intro s
  simp only [finiteTriplePack, finiteTripleEval, evalTriple, scaleForm,
    addForm, zeroF]
  refine Q'.eqv_trans _ (M x y z s + 0) _
    (Q'.add_eqv_congr_right _ _ _ (Q'.one_mul_eqv _)) ?_
  exact Q'.eqv_of_eq (Q'.add_zero' _)

/-- Analyze a finite triple carrier in an enumerated actual right channel. -/
def finiteRightAnalysis (a b c d : Nat) (col : Nat → Nat)
    (q : Nat) : FiniteTripleCarrier → BForm :=
  finiteTripleEval
    (triRight a b c d (rightChannelLabel b c (col q)))

/-- Right-channel analysis of a packed pure input is the actual nested
transvectant, without a product-carrier approximation. -/
theorem finiteRightAnalysis_pack
    (a b c d : Nat) (col : Nat → Nat) (q : Nat) (x y z : BForm) :
    BFormEqv (finiteRightAnalysis a b c d col q
      (finiteTriplePack x y z))
      (triRight a b c d (rightChannelLabel b c (col q)) x y z) := by
  exact finiteTripleEval_pack _ x y z

/-- **Finite-sum section-to-F theorem.**  This is the concrete ambient
interface: each `embed q v` may be an arbitrary finite weighted list of pure
triples.  The only remaining obligations are reconstruction and the two
constructive Schur hypotheses for the induced maps. -/
theorem triMapEqv_rightChannels_of_finiteTriple_sections_schur
    (a b c d N : Nat)
    (L : BForm → BForm → BForm → BForm)
    (col : Nat → Nat)
    (embed : Nat → BForm → FiniteTripleCarrier)
    (coeff : Nat → Nat → Q')
    (hdiag : ∀ q, q < N → HasDiagonalModel
      (ambientInduced (finiteTripleEval L) (embed q)) (coeff q))
    (hF : ∀ q, q < N → EndomorphismLoweringCovariant d
      (ambientInduced (finiteTripleEval L) (embed q)))
    (hreconstruct : ∀ i, i < a + 1 → ∀ j, j < b + 1 →
      ∀ l, l < c + 1 →
        BFormEqv (L (mono i) (mono j) (mono l))
          (formPrefix N (fun q =>
            ambientInduced (finiteTripleEval L) (embed q)
              (finiteRightAnalysis a b c d col q
                (finiteTriplePack (mono i) (mono j) (mono l)))))) :
    TriMapEqv a b c d L
      (rightChannelPrefix a b c d N col (fun q => coeff q 0)) := by
  apply triMapEqv_rightChannels_of_ambient_sections_schur
    FiniteTripleCarrier a b c d N L col finiteTriplePack
      (finiteTripleEval L) (finiteRightAnalysis a b c d col)
      embed coeff hdiag hF
  · intro i hi j hj l hl
    intro s
    exact Q'.eqv_symm
      (finiteTripleEval_pack L (mono i) (mono j) (mono l) s)
  · intro i hi j hj l hl s
    exact Q'.eqv_trans _ _ _
      (finiteTripleEval_pack L (mono i) (mono j) (mono l) s)
      (hreconstruct i hi j hj l hl s)
  · intro q hq x y z
    exact finiteRightAnalysis_pack a b c d col q x y z

end YMGap.Continuum.SU2FiniteTripleCarrier

#print axioms YMGap.Continuum.SU2FiniteTripleCarrier.finiteTripleEval_pack
#print axioms YMGap.Continuum.SU2FiniteTripleCarrier.finiteRightAnalysis_pack
#print axioms YMGap.Continuum.SU2FiniteTripleCarrier.triMapEqv_rightChannels_of_finiteTriple_sections_schur
