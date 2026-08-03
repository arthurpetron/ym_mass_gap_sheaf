/-
# Exact cutoff-one evaluation frontier for the two five-cycle BF4 Haar moments

The 116-link-to-five-cycle theorem reduces the two moments to fivefold Haar
integrals.  `BF4CutoffOneBinarySurfaceCertificate` independently evaluates
the finite 128-surface sum, while `BF4CutoffOneBinarySurfaceEmbedding` checks
those surfaces against the literal 72-face/116-link slab incidence kernel.
This module states the remaining geometric bridge explicitly and proves the
closed forms conditional on that bridge.

The bridge is deliberately not inhabited here.  It packages the still-open
constructive proof that (1) cutoff-one character expansion reindexes the
fivefold Haar integral by the rank-seven closed surfaces and (2) each closed
surface has the topological amplitude used by the finite certificate.

## Axiom gate

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
`noncomputable` declaration.  The uninhabited bridge is an explicit theorem
hypothesis, not an axiom or an assumed global instance.
-/

import YMGap.Continuum.BF4ExactCutoffOneTransmittedDegree
import YMGap.Continuum.BF4CutoffOneBinarySurfaceEmbedding

namespace YMGap.Continuum.BF4ExactCutoffOneHaarFiveEvaluation

set_option maxRecDepth 200000
set_option maxHeartbeats 12000000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum.BF4CutoffOneBinarySurfaceCertificate
open YMGap.Continuum.BF4CutoffOneBinarySurfaceEmbedding
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactCutoffOneTransmittedDegree
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumMomentExpansion
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactSpatialTreeGaugeRawCarrier
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionSelectedHaarTranslationDegree
open YMGap.Continuum.SU2QuaternionSpinTwoConditionalHaar
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Two explicit residual halves of the surface bridge -/

/-- Exact corrected-slab dual sum over a supplied finite compact-mask list.
Every summand uses the literal 72-face labelling and the normalized Haar
contraction over all 116 corrected-slab links. -/
def exactEmbeddedSurfaceDualSum (w : Q') (masks : List Nat) : Q' :=
  listQSum
    (fun compactMask =>
      exactCorrectedSlabDualTerm w 1 1
        (embeddedSurfaceLabelling compactMask))
    masks

/-- First residual half: reindex the two actual fivefold Haar expressions as
finite sums of literal corrected-slab dual terms.  Closure/list completeness
is already proved in `BF4CutoffOneBinarySurfaceEmbedding`. -/
structure CutoffOneCharacterExpansionReindex : Prop where
  vacuumRowReindex : ∀ w : Q',
    quaternionHaar 5
        (exactVacuumRowBasedCycleFivePolynomialCutoffOne w) ≈
      exactEmbeddedSurfaceDualSum w vacuumRowSurfaceMasks
  constantReindex : ∀ w : Q',
    quaternionHaar 5
        (exactConstantMomentBasedCycleFivePolynomialCutoffOne w) ≈
      exactEmbeddedSurfaceDualSum w binarySurfaceMasks

/-- The predicted normalized Haar contraction of a closed fundamental
surface.  Its denominator is `2^(E-V)`; the already-proved face factor
contributes `(2*w^3)^F`. -/
def surfaceTopologicalHaarAmplitude (compactMask : Nat) : Q' :=
  Q'.mkPos 1
    (2 ^ (surfaceEdgeCount compactMask - surfaceVertexCount compactMask))
    (Nat.two_pow_pos _)

/-- Pointwise second residual half: the signed 116-link Haar contraction of
each certified closed surface has the expected topological value `2^(V-E)`.
This deliberately remains uninhabited. -/
structure CutoffOneClosedSurfaceTopologicalAmplitude : Prop where
  amplitude : ∀ compactMask : Nat, compactMask ∈ binarySurfaceMasks →
    exactCorrectedSlabHaarCoefficient 1
        (embeddedSurfaceLabelling compactMask) ≈
      surfaceTopologicalHaarAmplitude compactMask

/-- The literal five-based-cycle marginal of one embedded binary surface.
The output blocks are ordered by the already-checked cycle list
`[0,4,5,6,10]`. -/
def embeddedSurfaceBasedCycleFivePolynomial
    (compactMask : Nat) : RatPoly :=
  exactRawTreeGaugeBasedCycleFiveHaarMarginal
    (exactCorrectedSlabSpinNetworkIntegrand 1
      (embeddedSurfaceLabelling compactMask))

/-- Every embedded cutoff-one surface meets the degree-five hypothesis of
the constructive 116-link-to-five-cycle gauge bridge. -/
theorem adaptedEmbeddedSurfaceIntegrand_degree_five
    (compactMask : Nat) :
    QuaternionBlocksDegreeAtMost bf4TransmittedAdaptedChordBlocks 5
      (adaptBF4RawCarrier
        (exactCorrectedSlabSpinNetworkIntegrand 1
          (embeddedSurfaceLabelling compactMask))) := by
  intro block hblock
  apply applyQuaternionBlockSwapChain_degreeAtMost
    bf4RawCarrierAdaptationSteps
  · rw [bf4TransmittedAdaptedChordBlocks_eq] at hblock
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hblock
    omega
  · apply (exactCorrectedSlabSpinNetworkIntegrand_cutoffOne_degreeAtMost
      (quaternionBlockSwapChainSource
        bf4RawCarrierAdaptationSteps block)
      (embeddedSurfaceLabelling compactMask)
      (embeddedSurfaceLabelling_le_one compactMask)).mono
    apply bf4TransmittedRawChordIncidenceDegree_le_five
    rw [← bf4TransmittedRawChordBlocks_eq_adaptation_sources]
    exact List.mem_map.mpr ⟨block, hblock, rfl⟩

/-- **Pointwise 116-link-to-five-cycle bridge.**  Each literal embedded
surface coefficient is already exactly a Haar integral over the five based
cycles `[0,4,5,6,10]`; no surface-amplitude assumption is used here. -/
theorem exactEmbeddedSurfaceHaarCoefficient_eq_basedCycleFive
    (compactMask : Nat) :
    exactCorrectedSlabHaarCoefficient 1
        (embeddedSurfaceLabelling compactMask) ≈
      quaternionHaar 5
        (embeddedSurfaceBasedCycleFivePolynomial compactMask) := by
  unfold exactCorrectedSlabHaarCoefficient
  exact quaternionHaar_116_eq_rawTreeGaugeBasedCycleFiveHaarMarginal _
    (exactCorrectedSlabSpinNetworkIntegrand_supported 1
      (embeddedSurfaceLabelling compactMask))
    (adaptedEmbeddedSurfaceIntegrand_degree_five compactMask)

/-- It now suffices to evaluate the fivefold marginal of every one of the
128 certified surfaces.  This constructor turns those finite Haar values
into the original pointwise topological-amplitude bridge. -/
theorem cutoffOneClosedSurfaceTopologicalAmplitude_of_basedCycleFive
    (hfive : ∀ compactMask : Nat, compactMask ∈ binarySurfaceMasks →
      quaternionHaar 5
          (embeddedSurfaceBasedCycleFivePolynomial compactMask) ≈
        surfaceTopologicalHaarAmplitude compactMask) :
    CutoffOneClosedSurfaceTopologicalAmplitude := by
  constructor
  intro compactMask hmem
  exact Q'.eqv_trans _ _ _
    (exactEmbeddedSurfaceHaarCoefficient_eq_basedCycleFive compactMask)
    (hfive compactMask hmem)

/-! ### The six-face sphere in its five-chord cube gauge -/

/-- Literal raw-block words of the six slab faces selected by compact mask
`2167232`, in the physical 72-face ordering. -/
def sixFaceSphereSelectedRawWords : List (List (Nat × Bool)) :=
  ((enumerateSlabFacesFrom 0
      (boundaryCompleteSlabPlaquettes 1)).filter fun indexed =>
    decide (embeddedSurfaceLabelling 2167232 indexed.1 = 1)).map fun indexed =>
      (orientedPlaquetteBoundary indexed.2).map fun entry =>
        ((boundaryCompleteSlabLinks 1).idxOf entry.link, entry.reverse)

/-- The literal geometry selects face ids `[6,7,8,15,25,44]` and these six
oriented raw-block words. -/
theorem sixFaceSphereSelectedRawWords_exact :
    sixFaceSphereSelectedRawWords =
      [[(8, false), (17, false), (16, true), (12, true)],
       [(8, false), (19, false), (18, true), (14, true)],
       [(12, false), (21, false), (20, true), (14, true)],
       [(18, false), (34, false), (33, true), (20, true)],
       [(16, false), (50, false), (33, true), (21, true)],
       [(17, false), (50, false), (34, true), (19, true)]] := by
  decide

/-- Seven local tree blocks and five complementary chord blocks in the raw
116-link ordering. -/
def sixFaceSphereLocalTreeRawBlocks : List Nat :=
  [8, 12, 14, 21, 17, 19, 50]

def sixFaceSphereLocalChordRawBlocks : List Nat :=
  [18, 20, 16, 33, 34]

def sixFaceSphereRawBlockSupport : List Nat :=
  (sixFaceSphereSelectedRawWords.flatten.map Prod.fst).eraseDups

/-- The six faces use exactly twelve raw links, partitioned without
duplication into the displayed seven tree and five chord blocks. -/
theorem sixFaceSphereLocalTreeChordPartition :
    sixFaceSphereLocalTreeRawBlocks.length = 7 ∧
    sixFaceSphereLocalChordRawBlocks.length = 5 ∧
    (sixFaceSphereLocalTreeRawBlocks ++
      sixFaceSphereLocalChordRawBlocks).Nodup ∧
    sixFaceSphereRawBlockSupport.length = 12 ∧
    sixFaceSphereRawBlockSupport.all (fun block =>
      decide (block ∈ sixFaceSphereLocalTreeRawBlocks ∨
        block ∈ sixFaceSphereLocalChordRawBlocks)) = true := by
  decide

/-- Delete a local tree incidence and compactly renumber a chord incidence. -/
def pruneSixFaceSphereLocalTree :
    List (Nat × Bool) → List (Nat × Bool)
  | [] => []
  | entry :: rest =>
      if entry.1 ∈ sixFaceSphereLocalChordRawBlocks then
        (sixFaceSphereLocalChordRawBlocks.idxOf entry.1, entry.2) ::
          pruneSixFaceSphereLocalTree rest
      else pruneSixFaceSphereLocalTree rest

/-- Multiply a finite oriented word in compact quaternion blocks. -/
def compactOrientedQuaternionWord
    (word : List (Nat × Bool)) : PolyQuaternion :=
  word.foldl
    (fun total entry =>
      PolyQuaternion.mul total
        (orientedCoordinateQuaternion entry.1 entry.2))
    PolyQuaternion.one

/-- The fundamental character of one compact oriented quaternion word. -/
def compactFundamentalWordFactor
    (word : List (Nat × Bool)) : RatPoly :=
  characterPolynomial (compactOrientedQuaternionWord word).scalar 1

/-- The local seven-tree substitution on the six plaquettes bounding the
certified vacuum-row cube leaves five chords. -/
def sixFaceSphereFiveChordWords : List (List (Nat × Bool)) :=
  [[(2, true)],
   [(0, true)],
   [(1, true)],
   [(0, false), (4, false), (3, true), (1, true)],
   [(2, false), (3, true)],
   [(4, true)]]

/-- The compact five-chord words are obtained by the checked local
tree/chord substitution on the literal six raw slab words. -/
theorem sixFaceSphereFiveChordWords_from_raw :
    sixFaceSphereSelectedRawWords.map pruneSixFaceSphereLocalTree =
      sixFaceSphereFiveChordWords := by
  decide

def sixFaceSphereFiveChordPolynomial : RatPoly :=
  sixFaceSphereFiveChordWords.foldr
    (fun word total =>
      polyMul (compactFundamentalWordFactor word) total)
    polyOne

/-- The pruned five-chord contraction is a small exact certificate: its 256
raw monomials integrate to `1/16`, exactly the predicted `2^(V-E)` for the
`(V,E,F) = (8,12,6)` sphere. -/
theorem sixFaceSphereFiveChordHaar_exact :
    quaternionHaar 5 sixFaceSphereFiveChordPolynomial ≈
      surfaceTopologicalHaarAmplitude 2167232 := by
  decide

/-- The explicit term left after substituting the proved face factor and the
predicted topological Haar amplitude. -/
def topologicalEmbeddedSurfaceDualTerm
    (w : Q') (compactMask : Nat) : Q' :=
  (Q'.ofNat 2 * RingNormaliser.qpow w 3) ^
      surfaceFaceCount compactMask *
    surfaceTopologicalHaarAmplitude compactMask

def topologicalEmbeddedSurfaceDualSum
    (w : Q') (masks : List Nat) : Q' :=
  listQSum (topologicalEmbeddedSurfaceDualTerm w) masks

/-- The two checked vacuum-row masks are members of the complete 128-surface
family, so the same pointwise amplitude theorem applies to them. -/
theorem vacuumRowSurfaceMasks_subset_binarySurfaceMasks
    (compactMask : Nat) (hmem : compactMask ∈ vacuumRowSurfaceMasks) :
    compactMask ∈ binarySurfaceMasks := by
  have hsurface : compactMask = 0 ∨ compactMask = 2167232 := by
    simpa [vacuumRowSurfaceMasks] using hmem
  rcases hsurface with rfl | rfl <;> decide

/-- The proved `(2*w^3)^F` face factor reduces each exact dual summand to the
topological target, conditional only on the pointwise Haar amplitude. -/
theorem exactEmbeddedSurfaceDualTerm_eq_topological
    (surface : CutoffOneClosedSurfaceTopologicalAmplitude)
    (w : Q') (compactMask : Nat)
    (hmem : compactMask ∈ binarySurfaceMasks) :
    exactCorrectedSlabDualTerm w 1 1
        (embeddedSurfaceLabelling compactMask) ≈
      topologicalEmbeddedSurfaceDualTerm w compactMask := by
  unfold exactCorrectedSlabDualTerm topologicalEmbeddedSurfaceDualTerm
  exact Q'.eqv_trans _
    ((Q'.ofNat 2 * RingNormaliser.qpow w 3) ^
        surfaceFaceCount compactMask *
      exactCorrectedSlabHaarCoefficient 1
        (embeddedSurfaceLabelling compactMask)) _
    (Q'.mul_eqv_congr_right _ _ _
      (embeddedSurfaceFaceFactor_exact w hmem))
    (Q'.mul_eqv_congr_left _ _ _
      (surface.amplitude compactMask hmem))

private theorem listQSum_congr_mem {A : Type} {f g : A → Q'} :
    ∀ xs : List A, (∀ x, x ∈ xs → f x ≈ g x) →
      listQSum f xs ≈ listQSum g xs
  | [], _ => Q'.eqv_refl _
  | x :: xs, hagree =>
      Q'.add_eqv_congr'
        (hagree x List.mem_cons_self)
        (listQSum_congr_mem xs
          (fun item hitem =>
            hagree item (List.mem_cons_of_mem x hitem)))

/-- Pointwise topological amplitudes reduce the full 128-surface exact dual
sum to the explicit topological sum. -/
theorem exactEmbeddedConstantSurfaceDualSum_eq_topological
    (surface : CutoffOneClosedSurfaceTopologicalAmplitude) (w : Q') :
    exactEmbeddedSurfaceDualSum w binarySurfaceMasks ≈
      topologicalEmbeddedSurfaceDualSum w binarySurfaceMasks := by
  apply listQSum_congr_mem
  intro compactMask hmem
  exact exactEmbeddedSurfaceDualTerm_eq_topological
    surface w compactMask hmem

/-- The same reduction holds for the two-term vacuum-row surface list. -/
theorem exactEmbeddedVacuumRowSurfaceDualSum_eq_topological
    (surface : CutoffOneClosedSurfaceTopologicalAmplitude) (w : Q') :
    exactEmbeddedSurfaceDualSum w vacuumRowSurfaceMasks ≈
      topologicalEmbeddedSurfaceDualSum w vacuumRowSurfaceMasks := by
  apply listQSum_congr_mem
  intro compactMask hmem
  exact exactEmbeddedSurfaceDualTerm_eq_topological
    surface w compactMask
    (vacuumRowSurfaceMasks_subset_binarySurfaceMasks compactMask hmem)

/-! ## 2. Close the finite topological-sum / QPoly assembly -/

private theorem pow_eqv_congr_local {left right : Q'}
    (hbase : left ≈ right) : ∀ exponent : Nat,
    left ^ exponent ≈ right ^ exponent
  | 0 => Q'.eqv_refl 1
  | exponent + 1 => by
      simp only [Q'.pow_succ]
      exact Q'.eqv_trans _
        (right * left ^ exponent) _
        (Q'.mul_eqv_congr_right _ _ _ hbase)
        (Q'.mul_eqv_congr_left _ _ _
          (pow_eqv_congr_local hbase exponent))

private theorem qpow_eqv_pow_local (value : Q') : ∀ exponent : Nat,
    RingNormaliser.qpow value exponent ≈ value ^ exponent
  | 0 => Q'.eqv_refl 1
  | exponent + 1 => by
      show RingNormaliser.qpow value exponent * value ≈
        value * value ^ exponent
      exact Q'.eqv_trans _
        (value ^ exponent * value) _
        (Q'.mul_eqv_congr_right _ _ _
          (qpow_eqv_pow_local value exponent))
        (Q'.mul_comm_eqv _ _)

private theorem pow_mul_base_eqv (left right : Q') : ∀ exponent : Nat,
    (left * right) ^ exponent ≈
      left ^ exponent * right ^ exponent
  | 0 => by
      simp only [Q'.pow_zero]
      exact Q'.eqv_symm (Q'.one_mul_eqv _)
  | exponent + 1 => by
      simp only [Q'.pow_succ]
      exact Q'.eqv_trans _
        ((left * right) *
          (left ^ exponent * right ^ exponent)) _
        (Q'.mul_eqv_congr_left _ _ _
          (pow_mul_base_eqv left right exponent))
        (RingNormaliser.q_mul4_swap
          left right (left ^ exponent) (right ^ exponent))

private theorem mul_three_swap_middle (left middle right : Q') :
    (left * middle) * right ≈ (left * right) * middle := by
  exact Q'.eqv_trans _ (left * (middle * right)) _
    (Q'.mul_assoc_eqv left middle right)
    (Q'.eqv_trans _ (left * (right * middle)) _
      (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_comm_eqv middle right))
      (Q'.eqv_symm (Q'.mul_assoc_eqv left right middle)))

def surfacePhysicalCoefficientCheck (compactMask : Nat) : Bool :=
  decide
    (((Q'.ofNat 2) ^ surfaceFaceCount compactMask *
        surfaceTopologicalHaarAmplitude compactMask) ≈
      Q'.ofNat (surfacePhysicalCoefficient compactMask))

theorem binarySurfaceMasks_surfacePhysicalCoefficientCheck :
    binarySurfaceMasks.all surfacePhysicalCoefficientCheck = true := by
  decide

theorem surfacePhysicalCoefficient_eqv
    (compactMask : Nat) (hmem : compactMask ∈ binarySurfaceMasks) :
    (Q'.ofNat 2) ^ surfaceFaceCount compactMask *
        surfaceTopologicalHaarAmplitude compactMask ≈
      Q'.ofNat (surfacePhysicalCoefficient compactMask) := by
  exact of_decide_eq_true
    (List.all_eq_true.mp
      binarySurfaceMasks_surfacePhysicalCoefficientCheck
      compactMask hmem)

/-- After the topological amplitude is inserted, one surface term is exactly
its integer physical coefficient times the heat monomial `w^(3F)`. -/
theorem topologicalEmbeddedSurfaceDualTerm_eq_physicalMonomial
    (w : Q') (compactMask : Nat)
    (hmem : compactMask ∈ binarySurfaceMasks) :
    topologicalEmbeddedSurfaceDualTerm w compactMask ≈
      Q'.ofNat (surfacePhysicalCoefficient compactMask) *
        w ^ (3 * surfaceFaceCount compactMask) := by
  unfold topologicalEmbeddedSurfaceDualTerm
  have hbase :
      Q'.ofNat 2 * RingNormaliser.qpow w 3 ≈
        Q'.ofNat 2 * w ^ 3 :=
    Q'.mul_eqv_congr_left _ _ _ (qpow_eqv_pow_local w 3)
  have hdistributed :
      (Q'.ofNat 2 * RingNormaliser.qpow w 3) ^
          surfaceFaceCount compactMask ≈
        (Q'.ofNat 2) ^ surfaceFaceCount compactMask *
          (w ^ 3) ^ surfaceFaceCount compactMask :=
    Q'.eqv_trans _ _ _
      (pow_eqv_congr_local hbase (surfaceFaceCount compactMask))
      (pow_mul_base_eqv (Q'.ofNat 2) (w ^ 3)
        (surfaceFaceCount compactMask))
  have hpower :
      (w ^ 3) ^ surfaceFaceCount compactMask ≈
        w ^ (3 * surfaceFaceCount compactMask) :=
    YMGap.Continuum.FiveHolonomyPerronCutoff.pow_mul_eqv
      w 3 (surfaceFaceCount compactMask)
  refine Q'.eqv_trans _
    (((Q'.ofNat 2) ^ surfaceFaceCount compactMask *
        (w ^ 3) ^ surfaceFaceCount compactMask) *
      surfaceTopologicalHaarAmplitude compactMask) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _ hdistributed
  · refine Q'.eqv_trans _
      (((Q'.ofNat 2) ^ surfaceFaceCount compactMask *
          surfaceTopologicalHaarAmplitude compactMask) *
        (w ^ 3) ^ surfaceFaceCount compactMask) _ ?_ ?_
    · exact mul_three_swap_middle _ _ _
    · exact Q'.eqv_trans _
        (Q'.ofNat (surfacePhysicalCoefficient compactMask) *
          (w ^ 3) ^ surfaceFaceCount compactMask) _
        (Q'.mul_eqv_congr_right _ _ _
          (surfacePhysicalCoefficient_eqv compactMask hmem))
        (Q'.mul_eqv_congr_left _ _ _ hpower)

def surfaceHeatMonomialPolynomial (compactMask : Nat) : QPoly.Poly :=
  List.replicate (3 * surfaceFaceCount compactMask) (0 : Q') ++
    [Q'.ofNat (surfacePhysicalCoefficient compactMask)]

private theorem eval_replicate_zero_append_singleton
    (coefficient w : Q') : ∀ degree : Nat,
    QPoly.eval
        (List.replicate degree (0 : Q') ++ [coefficient]) w ≈
      w ^ degree * coefficient
  | 0 => by
      simp only [List.replicate_zero, List.nil_append, QPoly.eval,
        Q'.pow_zero]
      exact Q'.eqv_trans _ (coefficient + 0) _
        (QPoly.q_add_congr (Q'.eqv_refl coefficient)
          (QPoly.q_mul_zero w))
        (Q'.eqv_trans _ coefficient _
          (QPoly.q_add_zero_eqv coefficient)
          (Q'.eqv_symm (Q'.one_mul_eqv coefficient)))
  | degree + 1 => by
      simp only [List.replicate_succ, List.cons_append, QPoly.eval,
        Q'.pow_succ]
      exact Q'.eqv_trans _
        (w * QPoly.eval
          (List.replicate degree (0 : Q') ++ [coefficient]) w) _
        (QPoly.q_zero_add_eqv _)
        (Q'.eqv_trans _ (w * (w ^ degree * coefficient)) _
          (Q'.mul_eqv_congr_left _ _ _
            (eval_replicate_zero_append_singleton coefficient w degree))
          (Q'.eqv_symm (Q'.mul_assoc_eqv w (w ^ degree) coefficient)))

def singletonSurfaceHeatPolynomialCheck (compactMask : Nat) : Bool :=
  decide (QPoly.allZero
    (QPoly.psub
      (surfaceHeatPolynomial [compactMask])
      (surfaceHeatMonomialPolynomial compactMask)))

theorem binarySurfaceMasks_singletonSurfaceHeatPolynomialCheck :
    binarySurfaceMasks.all singletonSurfaceHeatPolynomialCheck = true := by
  decide

theorem surfaceHeatPolynomial_singleton_eqv_monomial
    (w : Q') (compactMask : Nat)
    (hmem : compactMask ∈ binarySurfaceMasks) :
    QPoly.eval (surfaceHeatPolynomial [compactMask]) w ≈
      QPoly.eval (surfaceHeatMonomialPolynomial compactMask) w := by
  apply QPoly.poly_eqv
  exact of_decide_eq_true
    (List.all_eq_true.mp
      binarySurfaceMasks_singletonSurfaceHeatPolynomialCheck
      compactMask hmem)

theorem topologicalEmbeddedSurfaceDualTerm_eq_singletonPolynomial
    (w : Q') (compactMask : Nat)
    (hmem : compactMask ∈ binarySurfaceMasks) :
    topologicalEmbeddedSurfaceDualTerm w compactMask ≈
      QPoly.eval (surfaceHeatPolynomial [compactMask]) w := by
  refine Q'.eqv_trans _
    (Q'.ofNat (surfacePhysicalCoefficient compactMask) *
      w ^ (3 * surfaceFaceCount compactMask)) _
    (topologicalEmbeddedSurfaceDualTerm_eq_physicalMonomial
      w compactMask hmem) ?_
  refine Q'.eqv_trans _
    (w ^ (3 * surfaceFaceCount compactMask) *
      Q'.ofNat (surfacePhysicalCoefficient compactMask)) _
    (Q'.mul_comm_eqv _ _) ?_
  refine Q'.eqv_trans _
    (QPoly.eval (surfaceHeatMonomialPolynomial compactMask) w) _
    (Q'.eqv_symm
      (eval_replicate_zero_append_singleton
        (Q'.ofNat (surfacePhysicalCoefficient compactMask)) w
        (3 * surfaceFaceCount compactMask))) ?_
  exact Q'.eqv_symm
    (surfaceHeatPolynomial_singleton_eqv_monomial w compactMask hmem)

def singletonSurfaceHeatPolynomialSum : List Nat → QPoly.Poly
  | [] => []
  | compactMask :: rest =>
      QPoly.padd (surfaceHeatPolynomial [compactMask])
        (singletonSurfaceHeatPolynomialSum rest)

theorem eval_singletonSurfaceHeatPolynomialSum (w : Q') : ∀ masks,
    QPoly.eval (singletonSurfaceHeatPolynomialSum masks) w ≈
      listQSum (fun compactMask =>
        QPoly.eval (surfaceHeatPolynomial [compactMask]) w) masks
  | [] => Q'.eqv_refl 0
  | compactMask :: rest => by
      exact Q'.eqv_trans _ _ _
        (QPoly.eval_padd
          (surfaceHeatPolynomial [compactMask])
          (singletonSurfaceHeatPolynomialSum rest) w)
        (Q'.add_eqv_congr'
          (Q'.eqv_refl _)
          (eval_singletonSurfaceHeatPolynomialSum w rest))

def surfaceHeatPolynomialAssemblyCheck (masks : List Nat) : Bool :=
  decide (QPoly.allZero
    (QPoly.psub
      (singletonSurfaceHeatPolynomialSum masks)
      (surfaceHeatPolynomial masks)))

theorem constantSurfaceHeatPolynomialAssemblyCheck :
    surfaceHeatPolynomialAssemblyCheck binarySurfaceMasks = true := by
  decide

theorem vacuumRowSurfaceHeatPolynomialAssemblyCheck :
    surfaceHeatPolynomialAssemblyCheck vacuumRowSurfaceMasks = true := by
  decide

/-- The explicit 128-term topological sum is exactly the checked constant
surface polynomial.  No Haar hypothesis remains in this finite assembly. -/
theorem topologicalEmbeddedConstantSurfaceDualSum_eq_surfaceHeatPolynomial
    (w : Q') :
    topologicalEmbeddedSurfaceDualSum w binarySurfaceMasks ≈
      QPoly.eval constantSurfaceHeatPolynomial w := by
  refine Q'.eqv_trans _
    (listQSum (fun compactMask =>
      QPoly.eval (surfaceHeatPolynomial [compactMask]) w)
      binarySurfaceMasks) _ ?_ ?_
  · apply listQSum_congr_mem
    intro compactMask hmem
    exact topologicalEmbeddedSurfaceDualTerm_eq_singletonPolynomial
      w compactMask hmem
  · refine Q'.eqv_trans _
      (QPoly.eval
        (singletonSurfaceHeatPolynomialSum binarySurfaceMasks) w) _
      (Q'.eqv_symm
        (eval_singletonSurfaceHeatPolynomialSum w binarySurfaceMasks)) ?_
    apply QPoly.poly_eqv
    exact of_decide_eq_true constantSurfaceHeatPolynomialAssemblyCheck

/-- The explicit two-term topological vacuum-row sum is exactly the checked
vacuum-row surface polynomial. -/
theorem topologicalEmbeddedVacuumRowSurfaceDualSum_eq_surfaceHeatPolynomial
    (w : Q') :
    topologicalEmbeddedSurfaceDualSum w vacuumRowSurfaceMasks ≈
      QPoly.eval vacuumRowSurfaceHeatPolynomial w := by
  refine Q'.eqv_trans _
    (listQSum (fun compactMask =>
      QPoly.eval (surfaceHeatPolynomial [compactMask]) w)
      vacuumRowSurfaceMasks) _ ?_ ?_
  · apply listQSum_congr_mem
    intro compactMask hmem
    exact topologicalEmbeddedSurfaceDualTerm_eq_singletonPolynomial
      w compactMask
      (vacuumRowSurfaceMasks_subset_binarySurfaceMasks compactMask hmem)
  · refine Q'.eqv_trans _
      (QPoly.eval
        (singletonSurfaceHeatPolynomialSum vacuumRowSurfaceMasks) w) _
      (Q'.eqv_symm
        (eval_singletonSurfaceHeatPolynomialSum w vacuumRowSurfaceMasks)) ?_
    apply QPoly.poly_eqv
    exact of_decide_eq_true vacuumRowSurfaceHeatPolynomialAssemblyCheck

/-- Finite-sum form of the second residual half.  In combination with
`embeddedSurfaceFaceFactor_exact`, its two fields are the exact algebraic
targets generated by the pointwise topological amplitude. -/
structure CutoffOneClosedSurfaceSumEvaluation : Prop where
  vacuumRowEvaluation : ∀ w : Q',
    exactEmbeddedSurfaceDualSum w vacuumRowSurfaceMasks ≈
      QPoly.eval vacuumRowSurfaceHeatPolynomial w
  constantEvaluation : ∀ w : Q',
    exactEmbeddedSurfaceDualSum w binarySurfaceMasks ≈
      QPoly.eval constantSurfaceHeatPolynomial w

/-- The pointwise `2^(V-E)` Haar contraction is now the only input needed for
the entire closed-surface sum evaluation; all heat and QPoly assembly has been
proved constructively. -/
theorem cutoffOneClosedSurfaceSumEvaluation_of_topologicalAmplitude
    (surface : CutoffOneClosedSurfaceTopologicalAmplitude) :
    CutoffOneClosedSurfaceSumEvaluation where
  vacuumRowEvaluation w :=
    Q'.eqv_trans _ _ _
      (exactEmbeddedVacuumRowSurfaceDualSum_eq_topological surface w)
      (topologicalEmbeddedVacuumRowSurfaceDualSum_eq_surfaceHeatPolynomial w)
  constantEvaluation w :=
    Q'.eqv_trans _ _ _
      (exactEmbeddedConstantSurfaceDualSum_eq_topological surface w)
      (topologicalEmbeddedConstantSurfaceDualSum_eq_surfaceHeatPolynomial w)

/-- Summary residual interface between the fivefold Haar expressions and the
independently checked binary-surface sum.  The theorem below constructs it
from the two named halves, preventing the remaining work from being described
as one undifferentiated equality. -/
structure CutoffOneBinarySurfaceHaarBridge : Prop where
  vacuumRowSurfaceExpansion : ∀ w : Q',
    quaternionHaar 5
        (exactVacuumRowBasedCycleFivePolynomialCutoffOne w) ≈
      QPoly.eval vacuumRowSurfaceHeatPolynomial w
  constantSurfaceExpansion : ∀ w : Q',
    quaternionHaar 5
        (exactConstantMomentBasedCycleFivePolynomialCutoffOne w) ≈
      QPoly.eval constantSurfaceHeatPolynomial w

/-- Character-expansion reindexing plus closed-surface sum evaluation implies
the original summary bridge. -/
theorem cutoffOneBinarySurfaceHaarBridge_of_parts
    (reindex : CutoffOneCharacterExpansionReindex)
    (surface : CutoffOneClosedSurfaceSumEvaluation) :
    CutoffOneBinarySurfaceHaarBridge where
  vacuumRowSurfaceExpansion w :=
    Q'.eqv_trans _ _ _
      (reindex.vacuumRowReindex w)
      (surface.vacuumRowEvaluation w)
  constantSurfaceExpansion w :=
    Q'.eqv_trans _ _ _
      (reindex.constantReindex w)
      (surface.constantEvaluation w)

/-- Under the explicit surface-expansion bridge, the cutoff-one vacuum row is
exactly `R(w) = 1 + 4w^18`. -/
theorem exactVacuumRightConstantCrossMoment_cutoffOne_closedForm
    (bridge : CutoffOneBinarySurfaceHaarBridge) (w : Q') :
    exactVacuumRightConstantCrossMoment w 1 ≈
      QPoly.eval expectedVacuumRowHeatPolynomial w := by
  have hsurface := bridge.vacuumRowSurfaceExpansion w
  rw [vacuumRowSurfaceHeatPolynomial_closedForm] at hsurface
  exact Q'.eqv_trans _ _ _
    (exactVacuumRightConstantCrossMoment_cutoffOne_eq_basedCycleFiveHaar w)
    hsurface

/-- Under the explicit surface-expansion bridge, the cutoff-one constant
moment is
`C(w) = 1 + 32w^18 + 96w^30 + 224w^36 + 192w^42 + 3w^48`. -/
theorem exactConstantQuadraticMoment_cutoffOne_closedForm
    (bridge : CutoffOneBinarySurfaceHaarBridge) (w : Q') :
    exactConstantQuadraticMoment w 1 ≈
      QPoly.eval expectedConstantHeatPolynomial w := by
  have hsurface := bridge.constantSurfaceExpansion w
  rw [constantSurfaceHeatPolynomial_closedForm] at hsurface
  exact Q'.eqv_trans _ _ _
    (exactConstantQuadraticMoment_cutoffOne_eq_basedCycleFiveHaar w)
    hsurface

private theorem q_num_pos_of_pos {value : Q'} (hvalue : (0 : Q') < value) :
    0 < value.num := by
  have h :
      (0 : Int) * (value.den : Int) < value.num * (1 : Int) := hvalue
  simpa using h

private theorem q_lt_of_sub_pos {left right : Q'}
    (hsub : (0 : Q') < right + (-left)) : left < right := by
  have hnum : (0 : Int) < (right + (-left)).num :=
    q_num_pos_of_pos hsub
  show left.num * (right.den : Int) < right.num * (left.den : Int)
  change (0 : Int) <
    right.num * (left.den : Int) + (-left.num) * (right.den : Int) at hnum
  rw [Int.neg_mul] at hnum
  omega

/-- Conditional on the one honest surface-expansion bridge, the constant
Haar-five value is strictly larger than the vacuum-row value for every
positive heat coordinate. -/
theorem exactVacuumRow_lt_exactConstant_cutoffOne
    (bridge : CutoffOneBinarySurfaceHaarBridge)
    (w : Q') (hw : (0 : Q') < w) :
    exactVacuumRightConstantCrossMoment w 1 <
      exactConstantQuadraticMoment w 1 := by
  have hrow :=
    exactVacuumRightConstantCrossMoment_cutoffOne_closedForm bridge w
  have hconstant :=
    exactConstantQuadraticMoment_cutoffOne_closedForm bridge w
  have hclosed := haarFiveDifferenceHeatPolynomial_closedForm w
  have hpositiveExpected :=
    expectedHaarFiveDifferenceHeatPolynomial_positive w hw
  have hpositiveDifference :
      (0 : Q') < QPoly.eval haarFiveDifferenceHeatPolynomial w :=
    Q'.pos_of_lt_of_le hpositiveExpected (Q'.ge_of_eqv hclosed)
  have hsub := QPoly.eval_psub
    expectedConstantHeatPolynomial expectedVacuumRowHeatPolynomial w
  have hmomentSub :
      (QPoly.eval haarFiveDifferenceHeatPolynomial w).eqv
        (exactConstantQuadraticMoment w 1 +
          (-exactVacuumRightConstantCrossMoment w 1)) :=
    Q'.eqv_trans _ _ _ hsub
      (QPoly.q_add_congr
        (Q'.eqv_symm hconstant)
        (Q'.neg_eqv_congr _ _ (Q'.eqv_symm hrow)))
  exact q_lt_of_sub_pos
    (Q'.pos_of_lt_of_le hpositiveDifference (Q'.le_of_eqv hmomentSub))

/-- Conditional on the surface bridge, the centered cutoff-one numerator is
the exact five-term polynomial `C(w) - R(w)^2`. -/
theorem exactCenteredVacuumNumerator_cutoffOne_closedForm
    (bridge : CutoffOneBinarySurfaceHaarBridge) (w : Q') :
    (exactConstantQuadraticMoment w 1 +
      -(exactVacuumRightConstantCrossMoment w 1 *
        exactVacuumRightConstantCrossMoment w 1)).eqv
      (QPoly.eval expectedCenteredNumeratorHeatPolynomial w) := by
  have hrow :=
    exactVacuumRightConstantCrossMoment_cutoffOne_closedForm bridge w
  have hconstant :=
    exactConstantQuadraticMoment_cutoffOne_closedForm bridge w
  have hrowSquare :
      (exactVacuumRightConstantCrossMoment w 1 *
        exactVacuumRightConstantCrossMoment w 1).eqv
      (QPoly.eval expectedVacuumRowHeatPolynomial w *
        QPoly.eval expectedVacuumRowHeatPolynomial w) :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ hrow)
      (Q'.mul_eqv_congr_left _ _ _ hrow)
  have hactual :
      (exactConstantQuadraticMoment w 1 +
        -(exactVacuumRightConstantCrossMoment w 1 *
          exactVacuumRightConstantCrossMoment w 1)).eqv
      (QPoly.eval expectedConstantHeatPolynomial w +
        -(QPoly.eval expectedVacuumRowHeatPolynomial w *
          QPoly.eval expectedVacuumRowHeatPolynomial w)) :=
    QPoly.q_add_congr hconstant
      (Q'.neg_eqv_congr _ _ hrowSquare)
  have hpolynomial :
      (QPoly.eval centeredNumeratorHeatPolynomial w).eqv
      (QPoly.eval expectedConstantHeatPolynomial w +
        -(QPoly.eval expectedVacuumRowHeatPolynomial w *
          QPoly.eval expectedVacuumRowHeatPolynomial w)) :=
    Q'.eqv_trans _ _ _
      (QPoly.eval_psub expectedConstantHeatPolynomial
        (QPoly.pmul expectedVacuumRowHeatPolynomial
          expectedVacuumRowHeatPolynomial) w)
      (QPoly.q_add_congr (Q'.eqv_refl _)
        (Q'.neg_eqv_congr _ _
          (QPoly.eval_pmul expectedVacuumRowHeatPolynomial
            expectedVacuumRowHeatPolynomial w)))
  exact Q'.eqv_trans _ _ _ hactual
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm hpolynomial)
      (centeredNumeratorHeatPolynomial_closedForm w))

/-- Hence the actual centered cutoff-one numerator is strictly positive at
every positive heat coordinate, conditional only on the explicit bridge. -/
theorem exactCenteredVacuumNumerator_cutoffOne_positive
    (bridge : CutoffOneBinarySurfaceHaarBridge)
    (w : Q') (hw : (0 : Q') < w) :
    (0 : Q') <
      exactConstantQuadraticMoment w 1 +
        -(exactVacuumRightConstantCrossMoment w 1 *
          exactVacuumRightConstantCrossMoment w 1) := by
  have hclosed :=
    exactCenteredVacuumNumerator_cutoffOne_closedForm bridge w
  exact Q'.pos_of_lt_of_le
    (expectedCenteredNumeratorHeatPolynomial_positive w hw)
    (Q'.le_of_eqv (Q'.eqv_symm hclosed))

/-- The exact centered numerator polynomial forced by the two closed forms. -/
theorem cutoffOne_centeredNumerator_closedForm (w : Q') :
    (QPoly.eval
      (QPoly.psub expectedConstantHeatPolynomial
        (QPoly.pmul expectedVacuumRowHeatPolynomial
          expectedVacuumRowHeatPolynomial)) w).eqv
      (QPoly.eval expectedCenteredNumeratorHeatPolynomial w) :=
  centeredNumeratorHeatPolynomial_closedForm w

/-- The cross-multiplied discrepancy between the signed and physically
normalized centered moments is exactly `(C - 1)(C - R²)`, with its checked
ten-term nonnegative polynomial expansion. -/
theorem cutoffOne_centeredNormalizationDefect_closedForm (w : Q') :
    (QPoly.eval
      (QPoly.pmul
        (QPoly.psub expectedConstantHeatPolynomial [1])
        expectedCenteredNumeratorHeatPolynomial) w).eqv
      (QPoly.eval expectedCenteredNormalizationDefectHeatPolynomial w) :=
  centeredNormalizationDefectHeatPolynomial_closedForm w

end YMGap.Continuum.BF4ExactCutoffOneHaarFiveEvaluation

#print axioms YMGap.Continuum.BF4ExactCutoffOneHaarFiveEvaluation.cutoffOneBinarySurfaceHaarBridge_of_parts
#print axioms YMGap.Continuum.BF4ExactCutoffOneHaarFiveEvaluation.exactEmbeddedSurfaceHaarCoefficient_eq_basedCycleFive
#print axioms YMGap.Continuum.BF4ExactCutoffOneHaarFiveEvaluation.cutoffOneClosedSurfaceTopologicalAmplitude_of_basedCycleFive
#print axioms YMGap.Continuum.BF4ExactCutoffOneHaarFiveEvaluation.sixFaceSphereSelectedRawWords_exact
#print axioms YMGap.Continuum.BF4ExactCutoffOneHaarFiveEvaluation.sixFaceSphereFiveChordWords_from_raw
#print axioms YMGap.Continuum.BF4ExactCutoffOneHaarFiveEvaluation.sixFaceSphereFiveChordHaar_exact
#print axioms YMGap.Continuum.BF4ExactCutoffOneHaarFiveEvaluation.exactEmbeddedSurfaceDualTerm_eq_topological
#print axioms YMGap.Continuum.BF4ExactCutoffOneHaarFiveEvaluation.exactEmbeddedConstantSurfaceDualSum_eq_topological
#print axioms YMGap.Continuum.BF4ExactCutoffOneHaarFiveEvaluation.exactEmbeddedVacuumRowSurfaceDualSum_eq_topological
#print axioms YMGap.Continuum.BF4ExactCutoffOneHaarFiveEvaluation.topologicalEmbeddedConstantSurfaceDualSum_eq_surfaceHeatPolynomial
#print axioms YMGap.Continuum.BF4ExactCutoffOneHaarFiveEvaluation.topologicalEmbeddedVacuumRowSurfaceDualSum_eq_surfaceHeatPolynomial
#print axioms YMGap.Continuum.BF4ExactCutoffOneHaarFiveEvaluation.cutoffOneClosedSurfaceSumEvaluation_of_topologicalAmplitude
#print axioms YMGap.Continuum.BF4ExactCutoffOneHaarFiveEvaluation.exactVacuumRightConstantCrossMoment_cutoffOne_closedForm
#print axioms YMGap.Continuum.BF4ExactCutoffOneHaarFiveEvaluation.exactConstantQuadraticMoment_cutoffOne_closedForm
#print axioms YMGap.Continuum.BF4ExactCutoffOneHaarFiveEvaluation.exactVacuumRow_lt_exactConstant_cutoffOne
#print axioms YMGap.Continuum.BF4ExactCutoffOneHaarFiveEvaluation.exactCenteredVacuumNumerator_cutoffOne_closedForm
#print axioms YMGap.Continuum.BF4ExactCutoffOneHaarFiveEvaluation.exactCenteredVacuumNumerator_cutoffOne_positive
#print axioms YMGap.Continuum.BF4ExactCutoffOneHaarFiveEvaluation.cutoffOne_centeredNumerator_closedForm
#print axioms YMGap.Continuum.BF4ExactCutoffOneHaarFiveEvaluation.cutoffOne_centeredNormalizationDefect_closedForm
