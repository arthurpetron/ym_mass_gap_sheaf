/-
# Exact geometric decay of actual transfer comparison brackets

Signed linearity of the ORIGINAL V-weighted mass makes the two residual
gains add to mixFraction times the old bracket width. Consequently refresh
multiplies that width by the actual mixRate, exactly in rational semantics.

The bracket recursion follows the existing iterateStep on the actual K/V
polynomials. Supportedness, certified positivity of the comparison message,
and its positive V-weighted mass are propagated by the proved transfer laws.
The signed sourceProbe specialization has an explicit inhabited initial
interval and uses the proved positive mass of one. No additional mass
premise, strict positivity of mixRate, or finite-state replacement is needed.

The rate is cutoff-independent at fixed nome and width, not uniform in
nome or width. Physical sourceProbe placement still requires its existing
face-membership and geometry guards. No normalized boundary law, stationary
state, OS identification, continuum estimate or physical gap is asserted.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracket
import YMGap.Continuum.BF4ExactSlabFixedSpatialProbeInterval

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracketDecay

set_option autoImplicit false
-- The concrete K/V iteration unfolds more than the scalar algebra alone.
-- This is an elaboration budget only; the monitored 20 GiB ceiling is unchanged.
set_option maxHeartbeats 2000000

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabTemporalSweep (FaceFactor)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferOrder
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate
open YMGap.Continuum.BF4ExactSlabFixedSpatialWeightedMass
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialProbe
open YMGap.Continuum.BF4ExactSlabFixedSpatialProbeInterval
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.QuaternionHaarSquareCertificate

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv

private theorem residual_mass_sum (w : Q') (K width : Nat) (f g : RatPoly) (l u : Q') :
    weightedMass w K width (polyAdd f (polySmul (-l) g)) +
        weightedMass w K width (polyAdd (polySmul u g) (polySmul (-1) f)) ≈
      (u + -l) * weightedMass w K width g :=
  Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
    (Q'.eqv_trans _ _ _ (weightedMass_add w K width f (polySmul (-l) g))
      (Q'.add_eqv_congr' (Q'.eqv_refl _) (weightedMass_smul w K width (-l) g)))
    (Q'.eqv_trans _ _ _ (weightedMass_add w K width (polySmul u g) (polySmul (-1) f))
      (Q'.add_eqv_congr' (weightedMass_smul w K width u g)
        (weightedMass_smul w K width (-1) f))))
    (poly_identity_of_normal_eq
      (.add (.add (.var 0) (.mul (.neg (.var 2)) (.var 1)))
        (.add (.mul (.var 3) (.var 1)) (.mul (.const (-1)) (.var 0))))
      (.mul (.add (.var 3) (.neg (.var 2))) (.var 1)) (by decide)
      (fun
        | 0 => weightedMass w K width f
        | 1 => weightedMass w K width g
        | 2 => l
        | _ => u))

private theorem residual_gain_sum {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (f g : RatPoly) (l u : Q')
    (hmass : (0 : Q') < weightedMass w K width g) :
    gain hw0 hw1 K width g (polyAdd f (polySmul (-l) g)) hmass +
        gain hw0 hw1 K width g (polyAdd (polySmul u g) (polySmul (-1) f)) hmass ≈
      mixFraction hw0 hw1 width * (u + -l) := by
  let a := mixFraction hw0 hw1 width
  let r := Q'.recipPos (weightedMass w K width g) hmass
  have hsum := residual_mass_sum w K width f g l u
  refine Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
    (.add (.mul (.var 0) (.mul (.var 1) (.var 3)))
      (.mul (.var 0) (.mul (.var 2) (.var 3))))
    (.mul (.var 0) (.mul (.add (.var 1) (.var 2)) (.var 3))) (by decide)
    (fun
      | 0 => a
      | 1 => weightedMass w K width (polyAdd f (polySmul (-l) g))
      | 2 => weightedMass w K width (polyAdd (polySmul u g) (polySmul (-1) f))
      | _ => r)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left a _ _ (Q'.mul_eqv_congr_right _ _ r hsum)) ?_
  refine Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
    (.mul (.var 0) (.mul (.mul (.var 1) (.var 2)) (.var 3)))
    (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3))) (by decide)
    (fun | 0 => a | 1 => u + -l | 2 => weightedMass w K width g | _ => r)) ?_
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_recipPos_eqv _ hmass)) (Q'.mul_one_eqv _)

/-- The two actual residual gains cancel the same comparison mass exactly. -/
theorem refresh_width {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) {f g : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f) (hg : SupportedQuaternionBlocks (N width) g)
    (G : Certificate (N width) g) (hmass : (0 : Q') < weightedMass w K width g)
    (B : Bracket width f g) :
    (refresh hw0 hw1 K width hK hf hg G hmass B).upper +
        -(refresh hw0 hw1 K width hK hf hg G hmass B).lower ≈
      mixRate hw0 hw1 width * (B.upper + -B.lower) := by
  let lo := gain hw0 hw1 K width g (polyAdd f (polySmul (-B.lower) g)) hmass
  let hi := gain hw0 hw1 K width g (polyAdd (polySmul B.upper g) (polySmul (-1) f)) hmass
  have hsum : lo + hi ≈ mixFraction hw0 hw1 width * (B.upper + -B.lower) :=
    residual_gain_sum hw0 hw1 K width f g B.lower B.upper hmass
  change (B.upper + -hi) + -(B.lower + lo) ≈
    (1 + -mixFraction hw0 hw1 width) * (B.upper + -B.lower)
  refine Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
    (.add (.add (.var 0) (.neg (.var 3))) (.neg (.add (.var 1) (.var 2))))
    (.add (.add (.var 0) (.neg (.var 1))) (.neg (.add (.var 2) (.var 3))))
    (by decide) (fun | 0 => B.upper | 1 => B.lower | 2 => lo | _ => hi)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (Q'.eqv_refl _) (Q'.neg_eqv_congr _ _ hsum)) ?_
  exact poly_identity_of_normal_eq
    (.add (.var 0) (.neg (.mul (.var 1) (.var 0))))
    (.mul (.add (.const 1) (.neg (.var 1))) (.var 0)) (by decide)
    (fun | 0 => B.upper + -B.lower | _ => mixFraction hw0 hw1 width)

-- Iterate through proved APIs; do not expand concrete face lists or Haar
-- arithmetic while matching the recursive message types.
attribute [local irreducible] weightedMass kineticWeight spatialWeight baseLinks

/-- Strict mass positivity is propagated, not supplied afresh at each step. -/
theorem iterateWeightedMass_positive {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) :
    (steps : Nat) → {g : RatPoly} → SupportedQuaternionBlocks (N width) g →
      Certificate (N width) g → (0 : Q') < weightedMass w K width g →
      (0 : Q') < weightedMass w K width
        (iterateStep (N width) (kineticWeight w K width) (spatialWeight w K width) steps g) := by
  intro steps
  induction steps with
  | zero =>
      intro g hg G hmass
      exact hmass
  | succ steps ih =>
      intro g hg G hmass
      exact ih (g := transferStep w K width g)
          (transferStep_supported w K width (input := g) hg)
          (transferStep_certificate hw0 hw1 K width hK (f := g) hg G)
          (weightedMass_transfer_positive hw0 hw1 K width hK (f := g) hg G hmass)

/-- Computed brackets follow the existing actual iterate, including zero steps. -/
def iterateBracket {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) :
    (steps : Nat) → {f g : RatPoly} →
      SupportedQuaternionBlocks (N width) f → SupportedQuaternionBlocks (N width) g →
      Certificate (N width) g → (0 : Q') < weightedMass w K width g → Bracket width f g →
      Bracket width
        (iterateStep (N width) (kineticWeight w K width) (spatialWeight w K width) steps f)
        (iterateStep (N width) (kineticWeight w K width) (spatialWeight w K width) steps g) := by
  intro steps
  induction steps with
  | zero =>
      intro f g hf hg G hmass B
      exact B
  | succ steps ih =>
      intro f g hf hg G hmass B
      exact ih
        (f := transferStep w K width f) (g := transferStep w K width g)
        (transferStep_supported w K width (input := f) hf) (transferStep_supported w K width (input := g) hg)
        (transferStep_certificate hw0 hw1 K width hK (f := g) hg G)
        (weightedMass_transfer_positive hw0 hw1 K width hK (f := g) hg G hmass)
        (refresh hw0 hw1 K width hK (f := f) (g := g) hf hg G hmass B)

/-- Exact width q^steps times the initial width; q=0 is included without division. -/
theorem iterateBracket_width {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (steps : Nat) {f g : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f) (hg : SupportedQuaternionBlocks (N width) g)
    (G : Certificate (N width) g) (hmass : (0 : Q') < weightedMass w K width g)
    (B : Bracket width f g) :
    (iterateBracket hw0 hw1 K width hK steps hf hg G hmass B).upper +
        -(iterateBracket hw0 hw1 K width hK steps hf hg G hmass B).lower ≈
      mixRate hw0 hw1 width ^ steps * (B.upper + -B.lower) := by
  induction steps generalizing f g with
  | zero => exact Q'.eqv_symm (Q'.one_mul_eqv _)
  | succ steps ih =>
      refine Q'.eqv_trans _ _ _
        (ih (f := transferStep w K width f) (g := transferStep w K width g)
          (transferStep_supported w K width hf) (transferStep_supported w K width hg)
          (transferStep_certificate hw0 hw1 K width hK hg G)
          (weightedMass_transfer_positive hw0 hw1 K width hK hg G hmass)
          (refresh hw0 hw1 K width hK hf hg G hmass B)) ?_
      refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _
        (refresh_width hw0 hw1 K width hK hf hg G hmass B)) ?_
      exact poly_identity_of_normal_eq
        (.mul (.var 0) (.mul (.var 1) (.var 2)))
        (.mul (.mul (.var 1) (.var 0)) (.var 2)) (by decide)
        (fun
          | 0 => mixRate hw0 hw1 width ^ steps
          | 1 => mixRate hw0 hw1 width
          | _ => B.upper + -B.lower)

/-- An inhabited bracket for each actual signed spatial probe against the
actual iterate of one. Physical placement uses the existing sourceProbe guards. -/
def sourceProbeBracket {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (steps : Nat) (fs : List FaceFactor) :
    Bracket width
      (iterateStep (N width) (kineticWeight w K width) (spatialWeight w K width) steps
        (sourceProbe width fs))
      (iterateStep (N width) (kineticWeight w K width) (spatialWeight w K width) steps polyOne) :=
  iterateBracket hw0 hw1 K width hK steps (f := sourceProbe width fs) (g := polyOne)
    (sourceProbe_supported width fs)
    (supported_one (N width)) (Certificate.one (N width))
    (weightedMass_one_positive hw0 hw1 K width hK) (ofInterval (sourceProbe_interval width fs))

/-- Explicit signed-probe decay, with no input positivity or extra mass premise. -/
theorem sourceProbeBracket_width {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (steps : Nat) (fs : List FaceFactor) :
    (sourceProbeBracket hw0 hw1 K width hK steps fs).upper +
        -(sourceProbeBracket hw0 hw1 K width hK steps fs).lower ≈
      mixRate hw0 hw1 width ^ steps * (probeCap fs + probeCap fs) :=
  Q'.eqv_trans _ _ _
    (iterateBracket_width hw0 hw1 K width hK steps (f := sourceProbe width fs) (g := polyOne)
      (sourceProbe_supported width fs)
      (supported_one (N width)) (Certificate.one (N width))
      (weightedMass_one_positive hw0 hw1 K width hK) (ofInterval (sourceProbe_interval width fs)))
    (Q'.mul_eqv_congr_left _ _ _ (Q'.add_eqv_congr'
      (Q'.eqv_refl _) (Q'.neg_neg_eqv (probeCap fs))))

/-- Actual normalized original-message scalar, with its denominator positivity
constructed by iteration from one. The terminal spatial weight remains present. -/
def sourceProbeMassRatio {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (steps : Nat) (fs : List FaceFactor) : Q' :=
  massRatio w K width
    (iterateStep (N width) (kineticWeight w K width) (spatialWeight w K width) steps
      (sourceProbe width fs))
    (iterateStep (N width) (kineticWeight w K width) (spatialWeight w K width) steps polyOne)
    (iterateWeightedMass_positive hw0 hw1 K width hK steps (g := polyOne) (supported_one (N width))
      (Certificate.one (N width)) (weightedMass_one_positive hw0 hw1 K width hK))

/-- The same shrinking interval bounds an inhabited normalized scalar, not an
unnormalized transfer power. The interval centre may still depend on time. -/
theorem sourceProbeMassRatio_bounds {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (steps : Nat) (fs : List FaceFactor) :
    (sourceProbeBracket hw0 hw1 K width hK steps fs).lower ≤
        sourceProbeMassRatio hw0 hw1 K width hK steps fs ∧
      sourceProbeMassRatio hw0 hw1 K width hK steps fs ≤
        (sourceProbeBracket hw0 hw1 K width hK steps fs).upper :=
  massRatio_bounds hw0 hw1 K width hK
    (iterateWeightedMass_positive hw0 hw1 K width hK steps (g := polyOne) (supported_one (N width))
      (Certificate.one (N width)) (weightedMass_one_positive hw0 hw1 K width hK))
    (sourceProbeBracket hw0 hw1 K width hK steps fs)

end YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracketDecay

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracketDecay.refresh_width
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracketDecay.iterateWeightedMass_positive
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracketDecay.iterateBracket
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracketDecay.iterateBracket_width
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracketDecay.sourceProbeBracket
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracketDecay.sourceProbeBracket_width
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracketDecay.sourceProbeMassRatio
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracketDecay.sourceProbeMassRatio_bounds
