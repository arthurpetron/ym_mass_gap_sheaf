/-
# Factorized 32-link evaluator for the cutoff-one BF4 surfaces

The literal active-carrier theorem deletes 84 normalized Haar variables from
each certified surface.  This module keeps the remaining 72 plaquette factors
separate while applying the same checked permutation and prefix trim.  It
therefore exposes a fused bivalent contractor with only 32 integration steps,
without changing the exact five-cycle Haar value.

## Axiom gate

Finite lists and the existing constructive factorized Haar theorem only.  No
Classical.*, native_decide, sorry, custom axiom, choice, or noncomputable
declaration.
-/

import YMGap.Continuum.BF4ExactCutoffOneSurfaceActiveCarrier

namespace YMGap.Continuum.BF4ExactCutoffOneSurfaceActiveFactorizedHaar

set_option maxRecDepth 200000
set_option maxHeartbeats 12000000

open YMGap.Constructive
open YMGap.Continuum.BF4CutoffOneBinarySurfaceCertificate
open YMGap.Continuum.BF4CutoffOneBinarySurfaceEmbedding
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactCutoffOneHaarFiveEvaluation
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceActiveCarrier
open YMGap.Continuum.BF4ExactCutoffOneSurfaceFactorizedHaar
open YMGap.Continuum.BF4ExactSpatialTreeGaugeRawCarrier
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionArbitraryHaarHomogenization
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionBivalentHaarContraction
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

abbrev SurfacePlaq := YMGap.Continuum.ClusterCount4DProgress.Z4Plaq

private theorem monoMul_right_nil_local : ∀ monomial : List Nat,
    monoMul monomial [] = monomial
  | [] => rfl
  | _ :: _ => by simp only [monoMul]

private theorem polyMul_right_one_local : ∀ polynomial : RatPoly,
    polyMul polynomial polyOne = polynomial
  | [] => rfl
  | (monomial, coefficient) :: rest => by
      change
        [(monoMul monomial [], coefficient * 1)] ++
            polyMul rest polyOne =
          (monomial, coefficient) :: rest
      have hcoefficient : coefficient * 1 = coefficient := by
        cases coefficient with
        | mk num denPred =>
            change Q'.mul ⟨num, denPred⟩ (Q'.ofInt 1) =
              ⟨num, denPred⟩
            unfold Q'.mul Q'.ofInt Q'.den
            simp
      rw [monoMul_right_nil_local, polyMul_right_one_local rest]
      rw [hcoefficient]
      rfl

private theorem take_monoMul_local :
    ∀ (count : Nat) (left right : List Nat),
      (monoMul left right).take count =
        monoMul (left.take count) (right.take count)
  | 0, _, _ => rfl
  | count + 1, [], right => by simp [monoMul]
  | count + 1, left, [] => by
      rw [monoMul_right_nil_local, List.take_nil,
        monoMul_right_nil_local]
  | count + 1, _ :: left, _ :: right => by
      simp only [monoMul, List.take_succ_cons]
      rw [take_monoMul_local count left right]

theorem trimQuaternionPolynomial_polyMul
    (blocks : Nat) (left right : RatPoly) :
    trimQuaternionPolynomial blocks (polyMul left right) =
      polyMul (trimQuaternionPolynomial blocks left)
        (trimQuaternionPolynomial blocks right) := by
  induction left with
  | nil => rfl
  | cons source rest induction =>
      unfold trimQuaternionPolynomial at induction ⊢
      simp only [polyMul, List.flatMap_cons, List.map_append,
        List.map_cons, List.map_map]
      congr 1
      · apply List.map_congr_left
        intro target _
        simp [take_monoMul_local]
      · simpa only [polyMul, List.map_map] using induction

private theorem applyQuaternionBlockSwapChain_polyMul_local
    {blocks : Nat} :
    ∀ (swaps : List (QuaternionBlockInvolution blocks))
      (left right : RatPoly),
      applyQuaternionBlockSwapChain swaps (polyMul left right) =
        polyMul (applyQuaternionBlockSwapChain swaps left)
          (applyQuaternionBlockSwapChain swaps right)
  | [], _, _ => rfl
  | swap :: rest, left, right => by
      simp only [applyQuaternionBlockSwapChain]
      rw [reindexQuaternionPolynomial_mul,
        applyQuaternionBlockSwapChain_polyMul_local rest]

private theorem reindex_factorProduct_nonempty :
    ∀ (first : RatPoly) (rest : List RatPoly),
      reindexBF4SurfaceActiveCarrier (factorProduct (first :: rest)) =
        factorProduct
          ((first :: rest).map reindexBF4SurfaceActiveCarrier)
  | first, [] => by
      simp only [factorProduct, List.map_cons, List.map_nil]
      rw [polyMul_right_one_local, polyMul_right_one_local]
  | first, next :: rest => by
      simp only [factorProduct, List.map_cons]
      unfold reindexBF4SurfaceActiveCarrier
      rw [applyQuaternionBlockSwapChain_polyMul_local]
      congr 1
      exact reindex_factorProduct_nonempty next rest

private theorem trim_factorProduct_nonempty (blocks : Nat) :
    ∀ (first : RatPoly) (rest : List RatPoly),
      trimQuaternionPolynomial blocks (factorProduct (first :: rest)) =
        factorProduct
          ((first :: rest).map (trimQuaternionPolynomial blocks))
  | first, [] => by
      simp only [factorProduct, List.map_cons, List.map_nil]
      rw [polyMul_right_one_local, polyMul_right_one_local]
  | first, next :: rest => by
      simp only [factorProduct, List.map_cons]
      rw [trimQuaternionPolynomial_polyMul]
      congr 1
      exact trim_factorProduct_nonempty blocks next rest

private theorem factorProduct_trim_reindex_nonempty
    (factors : List RatPoly) (hfactors : factors ≠ []) :
    factorProduct
        (factors.map fun factor =>
          trimQuaternionPolynomial 32
            (reindexBF4SurfaceActiveCarrier factor)) =
      trimQuaternionPolynomial 32
        (reindexBF4SurfaceActiveCarrier (factorProduct factors)) := by
  cases factors with
  | nil => exact False.elim (hfactors rfl)
  | cons first rest =>
      rw [reindex_factorProduct_nonempty first rest]
      symm
      simpa only [List.map_cons, List.map_map, Function.comp_apply] using
        (trim_factorProduct_nonempty 32
          (reindexBF4SurfaceActiveCarrier first)
          (rest.map reindexBF4SurfaceActiveCarrier))

/-- The 72 literal face factors after the checked active-block permutation
and deletion of the 84 zero tails.  Spin-zero faces remain `polyOne` and are
removed automatically by the compact contractor. -/
def embeddedSurfaceActiveFactors (compactMask : Nat) : List RatPoly :=
  (correctedSlabSpinNetworkFactors 1
      (embeddedSurfaceLabelling compactMask)).map fun factor =>
    trimQuaternionPolynomial 32
      (reindexBF4SurfaceActiveCarrier factor)

theorem factorProduct_embeddedSurfaceActiveFactors
    (compactMask : Nat) :
    factorProduct (embeddedSurfaceActiveFactors compactMask) =
      embeddedSurfaceActivePolynomial compactMask := by
  let factors := correctedSlabSpinNetworkFactors 1
    (embeddedSurfaceLabelling compactMask)
  have hlength : factors.length = 72 := by
    unfold factors correctedSlabSpinNetworkFactors
    simp only [List.length_map]
    exact correctedSlabPlaquettes_extent_one_length
  have hnonempty : factors ≠ [] := by
    intro hnil
    rw [hnil] at hlength
    simp at hlength
  unfold embeddedSurfaceActiveFactors embeddedSurfaceActivePolynomial
  change factorProduct
      (factors.map fun factor =>
        trimQuaternionPolynomial 32
          (reindexBF4SurfaceActiveCarrier factor)) = _
  rw [factorProduct_trim_reindex_nonempty factors hnonempty]
  rw [factorProduct_correctedSlabSpinNetworkFactors]

/-- Executable 32-step fused factorized contraction of one actual embedded
surface. -/
def embeddedSurfaceActiveBivalentHaar (compactMask : Nat) : Q' :=
  compactBivalentFactorizedHaar 32
    (embeddedSurfaceActiveFactors compactMask)

theorem embeddedSurfaceActiveHaar_eq_bivalent
    (compactMask : Nat) :
    embeddedSurfaceActiveHaar compactMask ≈
      embeddedSurfaceActiveBivalentHaar compactMask := by
  unfold embeddedSurfaceActiveHaar embeddedSurfaceActiveBivalentHaar
  rw [← factorProduct_embeddedSurfaceActiveFactors]
  exact quaternionHaar_eq_compactBivalentFactorizedHaar 32 _

/-! ## 3. Remove literal spin-zero faces before evaluation -/

/-- The selected physical faces of one embedded binary surface.  Filtering
before block reindexing is important: at this stage every omitted spin-zero
factor is literally `polyOne`, rather than a padded constant monomial. -/
def embeddedSurfaceSelectedFaces (compactMask : Nat) : List SurfacePlaq :=
  (boundaryCompleteSlabPlaquettes 1).filter fun face =>
    decide
      (embeddedSurfaceLabelling compactMask
          ((boundaryCompleteSlabPlaquettes 1).idxOf face) = 1)

/-- The source-carrier product containing only selected faces. -/
def embeddedSurfaceSelectedPolynomial (compactMask : Nat) : RatPoly :=
  (embeddedSurfaceSelectedFaces compactMask).foldr
    (fun face total =>
      polyMul
        (correctedSlabPlaquetteSpinFactor 1
          (embeddedSurfaceLabelling compactMask) face)
        total)
    polyOne

/-- Selected face factors after the checked active-block permutation and
deletion of the 84 inactive coordinate blocks. -/
def embeddedSurfaceSelectedActiveFactors
    (compactMask : Nat) : List RatPoly :=
  (embeddedSurfaceSelectedFaces compactMask).map fun face =>
    trimQuaternionPolynomial 32
      (reindexBF4SurfaceActiveCarrier
        (correctedSlabPlaquetteSpinFactor 1
          (embeddedSurfaceLabelling compactMask) face))

/-- The production evaluator: at most sixteen nonunit face factors and 32
link eliminations, instead of 72 padded factors and 32 eliminations. -/
def embeddedSurfaceSelectedActiveBivalentHaar
    (compactMask : Nat) : Q' :=
  compactBivalentFactorizedHaar 32
    (embeddedSurfaceSelectedActiveFactors compactMask)

private theorem factorProduct_map_local (factor : α → RatPoly) :
    ∀ items : List α,
      factorProduct (items.map factor) =
        items.foldr (fun item total => polyMul (factor item) total) polyOne
  | [] => rfl
  | _ :: rest => by
      simp only [List.map_cons, factorProduct, List.foldr]
      rw [factorProduct_map_local factor rest]

private theorem quaternionHaar_polyOne_left_local
    (blocks : Nat) (polynomial : RatPoly) :
    quaternionHaar blocks (polyMul polyOne polynomial) ≈
      quaternionHaar blocks polynomial := by
  exact Q'.eqv_trans _ _ _
    (quaternionHaar_polyMul_comm blocks polyOne polynomial)
    (quaternionHaar_polyMul_one_right blocks polynomial)

private theorem selectedFaceFold_carrier (compactMask : Nat) :
    ∀ faces : List SurfacePlaq,
      HaarCarrierEqv 116
        (faces.foldr
          (fun face total =>
            polyMul
              (correctedSlabPlaquetteSpinFactor 1
                (embeddedSurfaceLabelling compactMask) face)
              total)
          polyOne)
        ((faces.filter fun face =>
          decide
            (embeddedSurfaceLabelling compactMask
                ((boundaryCompleteSlabPlaquettes 1).idxOf face) = 1)).foldr
          (fun face total =>
            polyMul
              (correctedSlabPlaquetteSpinFactor 1
                (embeddedSurfaceLabelling compactMask) face)
              total)
          polyOne)
  | [] => HaarCarrierEqv.refl 116 polyOne
  | face :: rest => by
      simp only [List.foldr, List.filter_cons]
      let spin := embeddedSurfaceLabelling compactMask
        ((boundaryCompleteSlabPlaquettes 1).idxOf face)
      by_cases hone : spin = 1
      · have hdecide : decide (spin = 1) = true := decide_eq_true hone
        rw [show decide
            (embeddedSurfaceLabelling compactMask
              ((boundaryCompleteSlabPlaquettes 1).idxOf face) = 1) = true by
          exact hdecide]
        simp only [if_true]
        exact HaarCarrierEqv.mul_left _
          (selectedFaceFold_carrier compactMask rest)
      · have hdecide : decide (spin = 1) = false := decide_eq_false hone
        rw [show decide
            (embeddedSurfaceLabelling compactMask
              ((boundaryCompleteSlabPlaquettes 1).idxOf face) = 1) = false by
          exact hdecide]
        simp only [Bool.false_eq_true, if_false]
        have hspin : spin ≤ 1 :=
          embeddedSurfaceLabelling_le_one compactMask
            ((boundaryCompleteSlabPlaquettes 1).idxOf face)
        have hzero : spin = 0 := by omega
        have hfactor :
            correctedSlabPlaquetteSpinFactor 1
                (embeddedSurfaceLabelling compactMask) face = polyOne := by
          unfold correctedSlabPlaquetteSpinFactor
          change characterPolynomial
            (correctedSlabPlaquettePolynomial 1 face).scalar spin = polyOne
          rw [hzero]
          rfl
        rw [hfactor]
        exact HaarCarrierEqv.trans
          (haarCarrier_polyOne_left 116 _)
          (selectedFaceFold_carrier compactMask rest)

/-- Removing the unselected spin-zero faces changes no normalized Haar
value on the original 116-link carrier. -/
theorem embeddedSurfaceIntegrand_haar_eq_selected
    (compactMask : Nat) :
    quaternionHaar 116
        (exactCorrectedSlabSpinNetworkIntegrand 1
          (embeddedSurfaceLabelling compactMask)) ≈
      quaternionHaar 116
        (embeddedSurfaceSelectedPolynomial compactMask) := by
  have hcarrier := selectedFaceFold_carrier compactMask
    (boundaryCompleteSlabPlaquettes 1)
  unfold exactCorrectedSlabSpinNetworkIntegrand
    embeddedSurfaceSelectedPolynomial embeddedSurfaceSelectedFaces
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (quaternionHaar_polyOne_left_local 116 _))
    (Q'.eqv_trans _ _ _ (hcarrier polyOne)
      (quaternionHaar_polyOne_left_local 116 _))

def embeddedSurfaceSelectedFacesNonemptyCheck : Bool :=
  binarySurfaceMasks.all fun compactMask =>
    decide
      (compactMask = 0 ∨
        embeddedSurfaceSelectedFaces compactMask ≠ [])

theorem embeddedSurfaceSelectedFacesNonemptyCheck_true :
    embeddedSurfaceSelectedFacesNonemptyCheck = true := by
  decide

theorem embeddedSurfaceSelectedFaces_nonempty
    (compactMask : Nat) (hmask : compactMask ∈ binarySurfaceMasks)
    (hnonzero : compactMask ≠ 0) :
    embeddedSurfaceSelectedFaces compactMask ≠ [] := by
  have hcheck := of_decide_eq_true
    (List.all_eq_true.mp
      embeddedSurfaceSelectedFacesNonemptyCheck_true compactMask hmask)
  rcases hcheck with hzero | hnonempty
  · exact False.elim (hnonzero hzero)
  · exact hnonempty

theorem factorProduct_embeddedSurfaceSelectedActiveFactors
    (compactMask : Nat)
    (hnonempty : embeddedSurfaceSelectedFaces compactMask ≠ []) :
    factorProduct
        (embeddedSurfaceSelectedActiveFactors compactMask) =
      trimQuaternionPolynomial 32
        (reindexBF4SurfaceActiveCarrier
          (embeddedSurfaceSelectedPolynomial compactMask)) := by
  let sourceFactors := (embeddedSurfaceSelectedFaces compactMask).map
    (correctedSlabPlaquetteSpinFactor 1
      (embeddedSurfaceLabelling compactMask))
  have hsourceNonempty : sourceFactors ≠ [] := by
    cases hfaces : embeddedSurfaceSelectedFaces compactMask with
    | nil => exact False.elim (hnonempty hfaces)
    | cons face rest => simp [sourceFactors, hfaces]
  rw [show embeddedSurfaceSelectedActiveFactors compactMask =
      sourceFactors.map fun factor =>
        trimQuaternionPolynomial 32
          (reindexBF4SurfaceActiveCarrier factor) by
    unfold embeddedSurfaceSelectedActiveFactors sourceFactors
    rw [List.map_map]
    rfl]
  rw [factorProduct_trim_reindex_nonempty sourceFactors hsourceNonempty]
  unfold embeddedSurfaceSelectedPolynomial
  unfold sourceFactors
  rw [factorProduct_map_local]

/-- Exact bridge from the literal 116-link coefficient to the compact
selected-face 32-link evaluator for every nonempty certified surface. -/
theorem exactEmbeddedSurfaceHaarCoefficient_eq_selectedActiveBivalent
    (compactMask : Nat) (hmask : compactMask ∈ binarySurfaceMasks)
    (hnonzero : compactMask ≠ 0) :
    exactCorrectedSlabHaarCoefficient 1
        (embeddedSurfaceLabelling compactMask) ≈
      embeddedSurfaceSelectedActiveBivalentHaar compactMask := by
  let selected := embeddedSurfaceSelectedPolynomial compactMask
  have hsupport : SupportedQuaternionBlocks 116 selected := by
    unfold selected embeddedSurfaceSelectedPolynomial
    simpa only [correctedSlabLinks_extent_one_length] using
      (correctedSlabSpinNetworkFaces_support 1
        (embeddedSurfaceLabelling compactMask)
        (embeddedSurfaceSelectedFaces compactMask))
  have hreindex := reindexBF4SurfaceActiveCarrier_haar selected hsupport
  have htail : QuaternionTailZeroAfter 32
      (reindexBF4SurfaceActiveCarrier selected) := by
    unfold selected embeddedSurfaceSelectedPolynomial
    exact reindexBF4SurfaceFactorProduct_tailZero compactMask hmask
      (embeddedSurfaceSelectedFaces compactMask) (fun face hface =>
        (List.mem_filter.mp hface).1)
  have htrim := quaternionHaar_trim_inactive 32 84
    (reindexBF4SurfaceActiveCarrier selected)
    (fun term hterm => by
      simpa using
        reindexBF4SurfaceActiveCarrier_term_length selected term hterm)
    htail
  have hnonempty := embeddedSurfaceSelectedFaces_nonempty
    compactMask hmask hnonzero
  have hproduct := factorProduct_embeddedSurfaceSelectedActiveFactors
    compactMask hnonempty
  have hevaluator :
      quaternionHaar 32
          (trimQuaternionPolynomial 32
            (reindexBF4SurfaceActiveCarrier selected)) ≈
        embeddedSurfaceSelectedActiveBivalentHaar compactMask := by
    rw [← hproduct]
    exact quaternionHaar_eq_compactBivalentFactorizedHaar 32 _
  unfold exactCorrectedSlabHaarCoefficient
  exact Q'.eqv_trans _ _ _
    (embeddedSurfaceIntegrand_haar_eq_selected compactMask)
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm hreindex)
      (Q'.eqv_trans _ _ _ htrim hevaluator))

/-! ## 4. Kernel-evaluated selected-face amplitudes -/

/-- The empty surface is the normalized Haar unit. -/
theorem emptySurfaceActiveHaar_exact :
    embeddedSurfaceActiveHaar 0 ≈
      surfaceTopologicalHaarAmplitude 0 := by
  decide

/-- The final finite obligation after all literal carrier, gauge, inactive-link,
and spin-zero reductions.  Only the 127 nonempty certified masks occur here;
the empty normalized Haar unit is already closed above. -/
def CutoffOneSelectedActiveBivalentAmplitude : Prop :=
  ∀ compactMask : Nat, compactMask ∈ binarySurfaceMasks →
    compactMask ≠ 0 →
    embeddedSurfaceSelectedActiveBivalentHaar compactMask ≈
      surfaceTopologicalHaarAmplitude compactMask

/-- The compact selected-face campaign implies the original literal
116-link pointwise surface-amplitude bridge. -/
theorem cutoffOneClosedSurfaceTopologicalAmplitude_of_selectedActiveBivalent
    (hselected : CutoffOneSelectedActiveBivalentAmplitude) :
    CutoffOneClosedSurfaceTopologicalAmplitude := by
  apply cutoffOneClosedSurfaceTopologicalAmplitude_of_active
  intro compactMask hmask
  by_cases hzero : compactMask = 0
  · subst compactMask
    exact emptySurfaceActiveHaar_exact
  · exact Q'.eqv_trans _ _ _
      (Q'.eqv_symm
        (exactEmbeddedSurfaceHaarCoefficient_eq_active compactMask hmask))
      (Q'.eqv_trans _ _ _
        (exactEmbeddedSurfaceHaarCoefficient_eq_selectedActiveBivalent
          compactMask hmask hzero)
        (hselected compactMask hmask hzero))

/-- Conversely, the original pointwise bridge supplies every compact
selected-face value.  Thus the 127-case campaign is an exact reformulation,
not a strengthened assumption. -/
theorem selectedActiveBivalentAmplitude_of_cutoffOneClosedSurface
    (surface : CutoffOneClosedSurfaceTopologicalAmplitude) :
    CutoffOneSelectedActiveBivalentAmplitude := by
  intro compactMask hmask hnonzero
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (exactEmbeddedSurfaceHaarCoefficient_eq_selectedActiveBivalent
        compactMask hmask hnonzero))
    (surface.amplitude compactMask hmask)

end YMGap.Continuum.BF4ExactCutoffOneSurfaceActiveFactorizedHaar

#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceActiveFactorizedHaar.trimQuaternionPolynomial_polyMul
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceActiveFactorizedHaar.factorProduct_embeddedSurfaceActiveFactors
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceActiveFactorizedHaar.embeddedSurfaceActiveHaar_eq_bivalent
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceActiveFactorizedHaar.embeddedSurfaceIntegrand_haar_eq_selected
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceActiveFactorizedHaar.exactEmbeddedSurfaceHaarCoefficient_eq_selectedActiveBivalent
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceActiveFactorizedHaar.cutoffOneClosedSurfaceTopologicalAmplitude_of_selectedActiveBivalent
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceActiveFactorizedHaar.selectedActiveBivalentAmplitude_of_cutoffOneClosedSurface
