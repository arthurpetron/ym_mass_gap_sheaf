/-
# Channel sections, constructive Schur scalars, and finite reconstruction

A right Clebsch--Gordan decomposition supplies two pieces of data for every
channel: an analysis map from the triple tensor product to the output
irreducible, and a section back into the triple tensor product.  Composing a
fixed equivariant trilinear map with one section gives an endomorphism of the
output irreducible.  Total-weight support makes that endomorphism diagonal;
lowering covariance and the constructive diagonal Schur lemma then force one
scalar on the whole channel.

This module packages the remaining argument abstractly.  Once a finite
post-section reconstruction identity is supplied, the channelwise Schur
scalars assemble into a complete `TriMapEqv` certificate.  Thus the concrete
residual is precisely the construction and covariance of the global CG
sections, rather than another shellwise coefficient inversion.
-/

import YMGap.Continuum.SU2DiagonalSchurUniqueness
import YMGap.Continuum.SU2TransvectantCentralChannelEquation
import YMGap.Continuum.SU2TransvectantLinearity

namespace YMGap.Continuum.SU2ChannelSectionSchurReconstruction

open YMGap.Constructive
open YMGap.Continuum.BinaryForms
open YMGap.Continuum.SU2DiagonalSchurUniqueness
open YMGap.Continuum.SU2TransvectantCentralChannelEquation
open YMGap.Continuum.SU2TransvectantLinearity
open YMGap.Continuum.SU2TransvectantMixedPentagon

local infix:50 " ≈ " => Q'.eqv

/-- A concrete element of the threefold binary-form tensor substrate. -/
structure TripleForm where
  left : BForm
  middle : BForm
  right : BForm

/-- Evaluate a trilinear map on a packaged triple. -/
def evalTriple (L : BForm → BForm → BForm → BForm)
    (u : TripleForm) : BForm :=
  L u.left u.middle u.right

/-- The endomorphism of the output channel obtained by following a section
with the fixed trilinear map. -/
def inducedEndomorphism
    (L : BForm → BForm → BForm → BForm)
    (embed : BForm → TripleForm) : BForm → BForm :=
  fun v => evalTriple L (embed v)

/-- An induced endomorphism is represented by a diagonal coefficient sequence
on the complete binary-form coefficient substrate. -/
def HasDiagonalModel (M : BForm → BForm) (coeff : Nat → Q') : Prop :=
  ∀ v, BFormEqv (M v) (diagonalMap coeff v)

/-- Lowering covariance of an arbitrary output endomorphism, tested on the
complete monomial basis of degree `d`. -/
def EndomorphismLoweringCovariant (d : Nat) (M : BForm → BForm) : Prop :=
  ∀ k, k < d + 1 →
    BFormEqv (M (Fop d (mono k))) (Fop d (M (mono k)))

/-- Lowering respects unbounded pointwise rational equality. -/
theorem Fop_congr (d : Nat) {x y : BForm} (hxy : BFormEqv x y) :
    BFormEqv (Fop d x) (Fop d y) := by
  intro s
  exact Q'.mul_eqv_congr_left _ _ _ (hxy (s + 1))

/-- A diagonal model of a lowering-covariant endomorphism satisfies the exact
diagonal covariance hypothesis used by the constructive Schur lemma. -/
theorem diagonalModel_loweringCovariant (d : Nat)
    (M : BForm → BForm) (coeff : Nat → Q')
    (hdiag : HasDiagonalModel M coeff)
    (hF : EndomorphismLoweringCovariant d M) :
    DiagonalLoweringCovariant d coeff := by
  intro k hk s hs
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (hdiag (Fop d (mono k)) s))
    (Q'.eqv_trans _ _ _ (hF k hk s)
      (Fop_congr d (hdiag (mono k)) s))

/-- **Sectionwise constructive Schur lemma.**  A diagonal, lowering-covariant
induced endomorphism is the scalar `coeff 0` on the full degree window. -/
theorem inducedEndomorphism_eq_scalar (d : Nat)
    (M : BForm → BForm) (coeff : Nat → Q')
    (hdiag : HasDiagonalModel M coeff)
    (hF : EndomorphismLoweringCovariant d M) (v : BForm) :
    FormEqv (d + 1) (M v) (scaleForm (coeff 0) v) := by
  intro s hs
  exact Q'.eqv_trans _ _ _ (hdiag v s)
    (diagonalMap_eq_scalar_identity d coeff
      (diagonalModel_loweringCovariant d M coeff hdiag hF) v s hs)

/-- Finite sum of a family of output forms. -/
def formPrefix : Nat → (Nat → BForm) → BForm
  | 0, _ => zeroF
  | N + 1, term => addForm (term 0)
      (formPrefix N (fun q => term (q + 1)))

/-- A finite form sum respects pointwise equality of every enumerated term. -/
theorem formPrefix_congr (N : Nat) (term term' : Nat → BForm)
    (hterm : ∀ q, q < N → BFormEqv (term q) (term' q)) :
    BFormEqv (formPrefix N term) (formPrefix N term') := by
  induction N generalizing term term' with
  | zero => exact fun _ => Q'.eqv_refl _
  | succ N ih =>
      intro s
      simp only [formPrefix, addForm]
      exact Q'.add_eqv_congr'
        (hterm 0 (by omega) s)
        (ih (fun q => term (q + 1)) (fun q => term' (q + 1))
          (fun q hq => hterm (q + 1) (by omega)) s)

/-- Bounded version used when Schur uniqueness is known only on the physical
degree window. -/
theorem formPrefix_congr_window (N W : Nat) (term term' : Nat → BForm)
    (hterm : ∀ q, q < N → FormEqv W (term q) (term' q)) :
    FormEqv W (formPrefix N term) (formPrefix N term') := by
  induction N generalizing term term' with
  | zero => exact FormEqv.refl W _
  | succ N ih =>
      intro s hs
      simp only [formPrefix, addForm]
      exact Q'.add_eqv_congr'
        (hterm 0 (by omega) s hs)
        (ih (fun q => term (q + 1)) (fun q => term' (q + 1))
          (fun q hq => hterm (q + 1) (by omega)) s hs)

/-- Channelwise Schur uniqueness transports an analyzed output through every
section and hence through their finite sum. -/
theorem formPrefix_induced_eq_scalar
    (d N : Nat) (L : BForm → BForm → BForm → BForm)
    (analysis : Nat → TripleForm → BForm)
    (embed : Nat → BForm → TripleForm)
    (coeff : Nat → Nat → Q')
    (hdiag : ∀ q, q < N → HasDiagonalModel
      (inducedEndomorphism L (embed q)) (coeff q))
    (hF : ∀ q, q < N → EndomorphismLoweringCovariant d
      (inducedEndomorphism L (embed q)))
    (u : TripleForm) :
    FormEqv (d + 1)
      (formPrefix N (fun q =>
        inducedEndomorphism L (embed q) (analysis q u)))
      (formPrefix N (fun q =>
        scaleForm (coeff q 0) (analysis q u))) := by
  exact formPrefix_congr_window N (d + 1) _ _ (fun q hq =>
    inducedEndomorphism_eq_scalar d
      (inducedEndomorphism L (embed q)) (coeff q)
      (hdiag q hq) (hF q hq) (analysis q u))

/-- **Abstract section-to-F reconstruction theorem.**

Suppose a finite right-channel analysis/section family reconstructs a fixed
trilinear map after applying that map to the section expansion.  If each
induced output endomorphism is degree-diagonal and lowering-covariant, then
the reconstruction coefficients are constant on the output irreducible and
are exactly the Schur scalars `coeff q 0`. -/
theorem triMapEqv_of_channelSections_schur
    (a b c d N : Nat)
    (L : BForm → BForm → BForm → BForm)
    (analysis : Nat → TripleForm → BForm)
    (embed : Nat → BForm → TripleForm)
    (coeff : Nat → Nat → Q')
    (hdiag : ∀ q, q < N → HasDiagonalModel
      (inducedEndomorphism L (embed q)) (coeff q))
    (hF : ∀ q, q < N → EndomorphismLoweringCovariant d
      (inducedEndomorphism L (embed q)))
    (hreconstruct : ∀ i, i < a + 1 → ∀ j, j < b + 1 →
      ∀ l, l < c + 1 →
        BFormEqv (L (mono i) (mono j) (mono l))
          (formPrefix N (fun q => inducedEndomorphism L (embed q)
            (analysis q ⟨mono i, mono j, mono l⟩)))) :
    TriMapEqv a b c d L
      (fun x y z => formPrefix N (fun q =>
        scaleForm (coeff q 0) (analysis q ⟨x, y, z⟩))) := by
  intro i hi j hj l hl s hs
  exact Q'.eqv_trans _ _ _ (hreconstruct i hi j hj l hl s)
    (formPrefix_induced_eq_scalar d N L analysis embed coeff
      hdiag hF ⟨mono i, mono j, mono l⟩ s hs)

/-! ## Specialization to the actual right-associated transvectant channels -/

/-- The right-channel analysis map with an explicitly enumerated contraction
order. -/
def rightChannelAnalysis (a b c d : Nat) (col : Nat → Nat)
    (q : Nat) (u : TripleForm) : BForm :=
  triRight a b c d (rightChannelLabel b c (col q))
    u.left u.middle u.right

/-- The generic finite form sum is exactly the existing packaged finite sum
of actual right-associated channels. -/
theorem formPrefix_rightChannels (a b c d N : Nat)
    (col : Nat → Nat) (coeff : Nat → Q') (u : TripleForm) :
    BFormEqv
      (formPrefix N (fun q =>
        scaleForm (coeff q) (rightChannelAnalysis a b c d col q u)))
      (rightChannelPrefix a b c d N col coeff
        u.left u.middle u.right) := by
  induction N generalizing col coeff with
  | zero => exact fun _ => Q'.eqv_refl _
  | succ N ih =>
      intro s
      simp only [formPrefix, rightChannelPrefix, addForm]
      exact Q'.add_eqv_congr' (Q'.eqv_refl _)
        (ih (fun q => col (q + 1)) (fun q => coeff (q + 1)) s)

/-- **Right-channel F-row from global CG sections.**  This is the concrete
target interface for the forthcoming global source reconstruction: its
conclusion is already the repository's packaged constant-coefficient
right-channel map, not merely an abstract finite sum. -/
theorem triMapEqv_rightChannels_of_sections_schur
    (a b c d N : Nat)
    (L : BForm → BForm → BForm → BForm)
    (col : Nat → Nat)
    (embed : Nat → BForm → TripleForm)
    (coeff : Nat → Nat → Q')
    (hdiag : ∀ q, q < N → HasDiagonalModel
      (inducedEndomorphism L (embed q)) (coeff q))
    (hF : ∀ q, q < N → EndomorphismLoweringCovariant d
      (inducedEndomorphism L (embed q)))
    (hreconstruct : ∀ i, i < a + 1 → ∀ j, j < b + 1 →
      ∀ l, l < c + 1 →
        BFormEqv (L (mono i) (mono j) (mono l))
          (formPrefix N (fun q => inducedEndomorphism L (embed q)
            (rightChannelAnalysis a b c d col q
              ⟨mono i, mono j, mono l⟩)))) :
    TriMapEqv a b c d L
      (rightChannelPrefix a b c d N col (fun q => coeff q 0)) := by
  have hgeneric := triMapEqv_of_channelSections_schur a b c d N L
    (rightChannelAnalysis a b c d col) embed coeff hdiag hF hreconstruct
  intro i hi j hj l hl s hs
  exact Q'.eqv_trans _ _ _ (hgeneric i hi j hj l hl s hs)
    (formPrefix_rightChannels a b c d N col (fun q => coeff q 0)
      ⟨mono i, mono j, mono l⟩ s)

end YMGap.Continuum.SU2ChannelSectionSchurReconstruction

#print axioms YMGap.Continuum.SU2ChannelSectionSchurReconstruction.Fop_congr
#print axioms YMGap.Continuum.SU2ChannelSectionSchurReconstruction.diagonalModel_loweringCovariant
#print axioms YMGap.Continuum.SU2ChannelSectionSchurReconstruction.inducedEndomorphism_eq_scalar
#print axioms YMGap.Continuum.SU2ChannelSectionSchurReconstruction.formPrefix_induced_eq_scalar
#print axioms YMGap.Continuum.SU2ChannelSectionSchurReconstruction.triMapEqv_of_channelSections_schur
#print axioms YMGap.Continuum.SU2ChannelSectionSchurReconstruction.formPrefix_rightChannels
#print axioms YMGap.Continuum.SU2ChannelSectionSchurReconstruction.triMapEqv_rightChannels_of_sections_schur
