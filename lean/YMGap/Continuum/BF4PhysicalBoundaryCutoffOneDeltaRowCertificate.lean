/-
# Proof-carrying cutoff-one delta rows

A cutoff-one physical source row can be compressed completely once it is
proved to be a scalar multiple of the Boolean vacuum delta on the decoded
boundary-word carrier.  This file packages that statement as a constructive
certificate and proves, once and for all, that:

* the certificate supplies an exact width-one variable-elimination trace;
* the exact physical row mass is the certified scalar;
* any two certified rows have zero cross-multiplied residual; and
* every finite block of certified rows has zero pairwise residual budget.

The vacuum and central lower-cube rows furnish the first two instances.  The
interface is deliberately independent of how a future surface instance is
certified: a hand proof, generated finite trace, or external computation may
propose the word theorem, but Lean rechecks the theorem and every consequence.

This remains a finite `K = 1`, half-extent-zero statement.  It neither says
that every retained physical source has such a certificate nor supplies any
cutoff-, volume-, or continuum-uniform estimate.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCubeStatistics

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffOneDeltaRowCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCubeEntry
open YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCubeStatistics
open YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumElimination
open YMGap.Continuum.BF4PhysicalBoundaryRegularizedRankOne
open YMGap.Continuum.BF4PhysicalBoundaryRegularizedRankOneStatistics
open YMGap.Continuum.BF4PhysicalBoundaryVariableElimination
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.FiniteBoundedEdgeLabellingVariableElimination
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteRegularizedRankOneStatistics
open YMGap.Continuum.FiniteVariableEliminationCertificate
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

private theorem qmul_congr
    {a a' b b' : Q'} (ha : a ≈ a') (hb : b ≈ b') :
    a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

/-! ## 1. Generic proof-carrying interface -/

/-- A compact, replayable proof that one genuine cutoff-one physical row is a
scalar multiple of the Boolean vacuum delta on all `2^24` decoded words. -/
structure CutoffOneBoundaryDeltaRowCertificate
    (w : Q') (source : EdgeLabelling) : Type where
  scale : Q'
  word_eqv_delta :
    ∀ word,
      word ∈ allSeqs 2 (centralFixedFaceIds 0).length →
        centralHalfAmplitude w 1 0 source
            (wordToEdgeLabelling (centralFixedFaceIds 0) word) ≈
          binaryVacuumWordWeight word * scale

namespace CutoffOneBoundaryDeltaRowCertificate

/-- The certified delta semantics induces the standard exact width-one
elimination trace, regardless of how the certificate itself was produced. -/
def exactEliminationCertificate
    {w : Q'} {source : EdgeLabelling}
    (certificate : CutoffOneBoundaryDeltaRowCertificate w source) :
    ExactVariableEliminationCertificate
      2 (centralFixedFaceIds 0).length
      (fun word =>
        centralHalfAmplitude w 1 0 source
          (wordToEdgeLabelling (centralFixedFaceIds 0) word)) where
  table := (binaryVacuumScaledEliminationCertificate
    (centralFixedFaceIds 0).length certificate.scale).table
  initial := certificate.word_eqv_delta
  step := (binaryVacuumScaledEliminationCertificate
    (centralFixedFaceIds 0).length certificate.scale).step

/-- The bottom of the checked elimination trace is exactly the certificate's
scalar, hence so is the genuine physical boundary-row mass. -/
theorem rowMass_eqv_scale
    {w : Q'} {source : EdgeLabelling}
    (certificate : CutoffOneBoundaryDeltaRowCertificate w source) :
    centralHalfAmplitudeBoundaryRowMass w 1 0 source ≈
      certificate.scale := by
  refine Q'.eqv_trans _
    (certificate.exactEliminationCertificate.table 0 []) _
    (centralHalfAmplitudeBoundaryRowMass_eqv_certificateBottom
      certificate.exactEliminationCertificate) ?_
  change binaryVacuumWordWeight [] * certificate.scale ≈
    certificate.scale
  exact Q'.one_mul_eqv _

/-- Any two certified delta rows are exactly proportional after clearing
their independently checked row masses. -/
theorem pairwiseRowCrossTerm_eqv_zero
    {w : Q'} {source other : EdgeLabelling}
    (sourceCertificate :
      CutoffOneBoundaryDeltaRowCertificate w source)
    (otherCertificate :
      CutoffOneBoundaryDeltaRowCertificate w other)
    (word : List Nat)
    (hword : word ∈ allSeqs 2 (centralFixedFaceIds 0).length) :
    centralBoundaryPairwiseRowCrossTerm
        w 1 0 source other
        (wordToEdgeLabelling (centralFixedFaceIds 0) word) ≈
      0 := by
  unfold centralBoundaryPairwiseRowCrossTerm finitePairwiseRowCrossTerm
  refine Q'.eqv_trans _
    (otherCertificate.scale *
          (binaryVacuumWordWeight word * sourceCertificate.scale) +
      -(sourceCertificate.scale *
          (binaryVacuumWordWeight word * otherCertificate.scale))) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (qmul_congr
        (otherCertificate.rowMass_eqv_scale)
        (sourceCertificate.word_eqv_delta word hword))
      (Q'.neg_eqv_congr _ _
        (qmul_congr
          (sourceCertificate.rowMass_eqv_scale)
          (otherCertificate.word_eqv_delta word hword)))
  · have hproduct :
        otherCertificate.scale *
              (binaryVacuumWordWeight word * sourceCertificate.scale) ≈
            sourceCertificate.scale *
              (binaryVacuumWordWeight word * otherCertificate.scale) := by
        refine Q'.eqv_trans _
          ((otherCertificate.scale * binaryVacuumWordWeight word) *
            sourceCertificate.scale) _
          (Q'.eqv_symm
            (Q'.mul_assoc_eqv otherCertificate.scale
              (binaryVacuumWordWeight word) sourceCertificate.scale)) ?_
        refine Q'.eqv_trans _
          (sourceCertificate.scale *
            (otherCertificate.scale * binaryVacuumWordWeight word)) _
          (Q'.mul_comm_eqv _ _) ?_
        exact Q'.mul_eqv_congr_left _ _ _
          (Q'.mul_comm_eqv otherCertificate.scale
            (binaryVacuumWordWeight word))
    exact Q'.eqv_trans _
      (sourceCertificate.scale *
            (binaryVacuumWordWeight word * otherCertificate.scale) +
        -(sourceCertificate.scale *
            (binaryVacuumWordWeight word * otherCertificate.scale))) _
      (Q'.add_eqv_congr_right _ _ _ hproduct)
      (Q'.add_neg_self_eqv _)

/-- A source paired with its proof-carrying cutoff-one delta certificate. -/
abbrev CertifiedDeltaRow (w : Q') :=
  Sigma fun source : EdgeLabelling =>
    CutoffOneBoundaryDeltaRowCertificate w source

/-- Forget the certificates while retaining their physical source rows. -/
def certifiedSources {w : Q'}
    (rows : List (CertifiedDeltaRow w)) : List EdgeLabelling :=
  rows.map fun row => row.1

/-- A finite list of proof-carrying delta rows contributes exactly zero
absolute pairwise residual budget to any certified source row.  Keeping the
witnesses in `Type` avoids extracting computational data from a mere
membership proposition. -/
theorem finiteBlockPairwiseResidualBudget_eqv_zero
    {w : Q'} (source : CertifiedDeltaRow w)
    (rows : List (CertifiedDeltaRow w))
    (word : List Nat)
    (hword : word ∈ allSeqs 2 (centralFixedFaceIds 0).length) :
    finitePairwiseRowResidualBudget
        (certifiedSources rows) (centralBoundaryChannels 1 0)
        (centralHalfAmplitude w 1 0) source.1
        (wordToEdgeLabelling (centralFixedFaceIds 0) word) ≈
      0 := by
  induction rows with
  | nil =>
      unfold certifiedSources finitePairwiseRowResidualBudget listQSum
      exact Q'.eqv_refl 0
  | cons other rest ih =>
      unfold certifiedSources finitePairwiseRowResidualBudget listQSum
      refine Q'.eqv_trans _ (0 + 0) _ ?_ ?_
      · exact Q'.add_eqv_congr'
          (Q'.eqv_trans _ (Q'.abs 0) _
            (Q'.abs_eqv_congr
              (source.2.pairwiseRowCrossTerm_eqv_zero
                other.2 word hword)) (by decide))
          ih
      · exact Q'.eqv_of_eq (Q'.zero_add' 0)

end CutoffOneBoundaryDeltaRowCertificate

/-! ## 2. Physical vacuum and lower-cube instances -/

def cutoffOneVacuumDeltaRowCertificate (w : Q') :
    CutoffOneBoundaryDeltaRowCertificate w zeroEdgeLabelling where
  scale := 1
  word_eqv_delta := by
    intro word hword
    exact Q'.eqv_trans _ (binaryVacuumWordWeight word) _
      (centralHalfAmplitude_cutoffOne_vacuum_word_eqv_delta
        w word hword)
      (Q'.eqv_symm (Q'.mul_one_eqv _))

def cutoffOneCubeDeltaRowCertificate (w : Q') :
    CutoffOneBoundaryDeltaRowCertificate w centralLowerCubeState where
  scale := (coeffW w 1) ^ 6
  word_eqv_delta :=
    centralHalfAmplitude_cutoffOne_cube_word_eqv_delta w

/-- The vacuum source paired with its checked delta-row witness. -/
def cutoffOneVacuumCertifiedDeltaRow (w : Q') :
    CutoffOneBoundaryDeltaRowCertificate.CertifiedDeltaRow w :=
  ⟨zeroEdgeLabelling, cutoffOneVacuumDeltaRowCertificate w⟩

/-- The lower-cube source paired with its checked delta-row witness. -/
def cutoffOneCubeCertifiedDeltaRow (w : Q') :
    CutoffOneBoundaryDeltaRowCertificate.CertifiedDeltaRow w :=
  ⟨centralLowerCubeState, cutoffOneCubeDeltaRowCertificate w⟩

/-- The proof-carrying version of the displayed vacuum/cube source block. -/
def cutoffOneVacuumCubeCertifiedBlock (w : Q') :
    List (CutoffOneBoundaryDeltaRowCertificate.CertifiedDeltaRow w) :=
  [cutoffOneVacuumCertifiedDeltaRow w, cutoffOneCubeCertifiedDeltaRow w]

theorem cutoffOneVacuumCubeCertifiedBlock_sources (w : Q') :
    CutoffOneBoundaryDeltaRowCertificate.certifiedSources
        (cutoffOneVacuumCubeCertifiedBlock w) =
      cutoffOneVacuumCubeSourceBlock :=
  rfl

/-! ## 3. Exact two-row block statistic -/

/-- The complete absolute pairwise residual budget against the genuine
vacuum/cube block is zero for every proof-carrying cutoff-one delta source and
every decoded binary boundary word. -/
theorem cutoffOneVacuumCubeSourceBlock_pairwiseResidualBudget_eqv_zero
    {w : Q'}
    (source :
      CutoffOneBoundaryDeltaRowCertificate.CertifiedDeltaRow w)
    (word : List Nat)
    (hword : word ∈ allSeqs 2 (centralFixedFaceIds 0).length) :
    finitePairwiseRowResidualBudget
        cutoffOneVacuumCubeSourceBlock
        (centralBoundaryChannels 1 0)
        (centralHalfAmplitude w 1 0) source.1
        (wordToEdgeLabelling (centralFixedFaceIds 0) word) ≈
      0 := by
  rw [← cutoffOneVacuumCubeCertifiedBlock_sources w]
  exact CutoffOneBoundaryDeltaRowCertificate.finiteBlockPairwiseResidualBudget_eqv_zero
    source (cutoffOneVacuumCubeCertifiedBlock w) word hword

end YMGap.Continuum.BF4PhysicalBoundaryCutoffOneDeltaRowCertificate

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneDeltaRowCertificate.CutoffOneBoundaryDeltaRowCertificate.rowMass_eqv_scale
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneDeltaRowCertificate.CutoffOneBoundaryDeltaRowCertificate.pairwiseRowCrossTerm_eqv_zero
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneDeltaRowCertificate.CutoffOneBoundaryDeltaRowCertificate.finiteBlockPairwiseResidualBudget_eqv_zero
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneDeltaRowCertificate.cutoffOneVacuumCubeSourceBlock_pairwiseResidualBudget_eqv_zero
