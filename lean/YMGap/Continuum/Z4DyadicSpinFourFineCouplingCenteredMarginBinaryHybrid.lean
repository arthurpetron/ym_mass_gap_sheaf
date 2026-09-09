/-
# Binary occupied-face form of the cutoff-one centered coupling score

The local-insertion expansion retains an ordered prefix heat weight.  On the
actual spin-four dyadic schedule the fine cutoff is one, so every physical
face label is exactly zero or one.  Consequently every face Casimir is zero
or three.

This module performs that reduction without an estimate.  It defines the
binary hybrid response fold

  empty face    : tail,
  occupied face : geomSum(w, 3) * response(face) + w^3 * tail,

and proves that it is exactly the response-weighted sum of the previous
face-labelled margin contributions.  It then identifies the complete
centered score-event moment with the sum of these binary hybrid folds over
the literal fine physical source carrier.

Because that centered response is face-independent at fixed source, the
module goes further: it redistributes the global geometric quotient equally
among the source's occupied faces.  The resulting symmetric carrier has no
prefix weights, contains only faces with spin one, and gives exactly the same
centered score-event moment.  Its one remaining nonlocal datum is the total
number of occupied faces in the source.

The result exposes both an occupation-chain observable and an order-free
occupied-face carrier, but does not prove that the latter's global count
dependence is local or mixing.  In particular, it establishes
no cutoff- or volume-uniform estimate, continuum measure, OS/GNS
reconstruction, Hamiltonian gap, or Yang--Mills mass gap.

Constructive contract: finite recursion and exact rational setoid algebra
only; no `Classical`, choice, `native_decide`, proof hole, noncomputable
declaration, or new axiom.
-/

import YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginLocalInsertion

namespace YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginBinaryHybrid

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabObservablePhysicalBlockingDefect
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginLocalInsertion
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginOneReplica
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingNormalizedMarginFactorization
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingReferencePerturbation

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The cutoff-one physical spin is binary -/

/-- Every listed physical face of a cutoff-one fine source has spin zero or
one.  This is extracted from the literal bounded-labelling enumeration. -/
theorem finePhysicalFaceSpin_zero_or_one
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (source : EdgeLabelling) (hsource : source ∈ S.fine.physicalLabellings)
    (faceId : Nat) (hface : faceId ∈ slabPhysicalFaceEdges S.fine.extent) :
    source faceId = 0 ∨ source faceId = 1 := by
  have hbounded :
      source faceId < S.fine.cutoff + 1 :=
    (boundedEdgeLabellings_sound S.fine.cutoff S.fine.faceEdges
      source (by
        simpa only [SlabPhysicalData.physicalLabellings] using hsource)).1
      faceId (by
        simpa only [SlabPhysicalData.faceEdges] using hface)
  rw [hfineCutoff] at hbounded
  omega

/-- A zero spin contributes zero to the geometric coupling quotient. -/
theorem geomSum_c4_eqv_zero_of_spin_zero
    (w : Q') (physical : EdgeLabelling) (faceId : Nat)
    (hzero : physical faceId = 0) :
    geomSum w (c4 (physical faceId)) ≈ 0 := by
  rw [hzero]
  exact Q'.eqv_refl 0

/-- A zero spin leaves the ordered prefix heat weight unchanged. -/
theorem qpow_c4_eqv_one_of_spin_zero
    (w : Q') (physical : EdgeLabelling) (faceId : Nat)
    (hzero : physical faceId = 0) :
    qpow w (c4 (physical faceId)) ≈ 1 := by
  rw [hzero]
  exact Q'.eqv_refl 1

/-- An occupied cutoff-one face has the exact SU(2) exponent `C4(1)=3`. -/
theorem geomSum_c4_eqv_three_of_spin_one
    (w : Q') (physical : EdgeLabelling) (faceId : Nat)
    (hone : physical faceId = 1) :
    geomSum w (c4 (physical faceId)) ≈ geomSum w 3 := by
  rw [hone]
  exact Q'.eqv_refl _

/-- An occupied cutoff-one face attenuates every later insertion by `w^3`. -/
theorem qpow_c4_eqv_three_of_spin_one
    (w : Q') (physical : EdgeLabelling) (faceId : Nat)
    (hone : physical faceId = 1) :
    qpow w (c4 (physical faceId)) ≈ qpow w 3 := by
  rw [hone]
  exact Q'.eqv_refl _

/-! ## 2. Response-weighted local contributions and their binary fold -/

/-- Apply an arbitrary face response to the face-labelled margin
contributions. -/
def slabPhysicalMarginFaceResponseSum
    (w : Q') (physical : EdgeLabelling) (response : Nat → Q')
    (faces : List Nat) : Q' :=
  listQSum
    (fun contribution : PhysicalMarginFaceContribution =>
      contribution.2 * response contribution.1)
    (slabPhysicalMarginFaceContributions w physical faces)

/-- One head face splits the response sum into its local insertion and its
prefix-weighted tail. -/
theorem slabPhysicalMarginFaceResponseSum_cons
    (w : Q') (physical : EdgeLabelling) (response : Nat → Q')
    (faceId : Nat) (rest : List Nat) :
    slabPhysicalMarginFaceResponseSum w physical response (faceId :: rest) ≈
      geomSum w (c4 (physical faceId)) * response faceId +
        qpow w (c4 (physical faceId)) *
          slabPhysicalMarginFaceResponseSum w physical response rest := by
  let exponent := c4 (physical faceId)
  let tail := slabPhysicalMarginFaceContributions w physical rest
  simp only [slabPhysicalMarginFaceResponseSum,
    slabPhysicalMarginFaceContributions, listQSum, listQSum_map]
  change
    geomSum w exponent * response faceId +
        listQSum
          (fun contribution : PhysicalMarginFaceContribution =>
            (qpow w exponent * contribution.2) *
              response contribution.1) tail ≈
      geomSum w exponent * response faceId +
        qpow w exponent *
          listQSum
            (fun contribution : PhysicalMarginFaceContribution =>
              contribution.2 * response contribution.1) tail
  apply Q'.add_eqv_congr_left
  refine Q'.eqv_trans _
    (listQSum
      (fun contribution : PhysicalMarginFaceContribution =>
        qpow w exponent *
          (contribution.2 * response contribution.1)) tail) _ ?_ ?_
  · exact listQSum_congr
      (fun contribution =>
        Q'.mul_assoc_eqv (qpow w exponent)
          contribution.2 (response contribution.1)) tail
  · exact listQSum_mul_left (qpow w exponent)
      (fun contribution : PhysicalMarginFaceContribution =>
        contribution.2 * response contribution.1) tail

/-- The exact cutoff-one occupied-face hybrid fold.  Only a face labelled
one inserts a response; each such occupied prefix multiplies the remaining
tail by `w^3`. -/
def slabCutoffOneBinaryHybridResponse
    (w : Q') (physical : EdgeLabelling) (response : Nat → Q') :
    List Nat → Q'
  | [] => 0
  | faceId :: rest =>
      if physical faceId = 1 then
        geomSum w 3 * response faceId +
          qpow w 3 *
            slabCutoffOneBinaryHybridResponse w physical response rest
      else
        slabCutoffOneBinaryHybridResponse w physical response rest

/-- An empty binary face leaves the hybrid response tail unchanged. -/
theorem slabCutoffOneBinaryHybridResponse_cons_of_zero
    (w : Q') (physical : EdgeLabelling) (response : Nat → Q')
    (faceId : Nat) (rest : List Nat) (hzero : physical faceId = 0) :
    slabCutoffOneBinaryHybridResponse w physical response (faceId :: rest) =
      slabCutoffOneBinaryHybridResponse w physical response rest := by
  have hnotOne : physical faceId ≠ 1 := by omega
  simp only [slabCutoffOneBinaryHybridResponse, hnotOne, if_false]

/-- An occupied binary face inserts `1+w+w^2` and attenuates the tail by
`w^3`.  The displayed `geomSum w 3` is definitionally the former factor. -/
theorem slabCutoffOneBinaryHybridResponse_cons_of_one
    (w : Q') (physical : EdgeLabelling) (response : Nat → Q')
    (faceId : Nat) (rest : List Nat) (hone : physical faceId = 1) :
    slabCutoffOneBinaryHybridResponse w physical response (faceId :: rest) =
      geomSum w 3 * response faceId +
        qpow w 3 *
          slabCutoffOneBinaryHybridResponse w physical response rest := by
  simp only [slabCutoffOneBinaryHybridResponse, hone, if_true]

/-- On any binary-labelled face list, the original prefix-weighted local
contributions are exactly the occupied-face hybrid fold. -/
theorem slabPhysicalMarginFaceResponseSum_eqv_binaryHybrid
    (w : Q') (physical : EdgeLabelling) (response : Nat → Q') :
    ∀ faces : List Nat,
      (∀ faceId, faceId ∈ faces →
        physical faceId = 0 ∨ physical faceId = 1) →
      slabPhysicalMarginFaceResponseSum w physical response faces ≈
        slabCutoffOneBinaryHybridResponse w physical response faces
  | [], _ => Q'.eqv_refl 0
  | faceId :: rest, hbinary => by
      have hhead := hbinary faceId List.mem_cons_self
      have htail : ∀ tailFace, tailFace ∈ rest →
          physical tailFace = 0 ∨ physical tailFace = 1 := by
        intro tailFace htailMem
        exact hbinary tailFace (List.mem_cons_of_mem faceId htailMem)
      have hinduction :=
        slabPhysicalMarginFaceResponseSum_eqv_binaryHybrid
          w physical response rest htail
      refine Q'.eqv_trans _
        (geomSum w (c4 (physical faceId)) * response faceId +
          qpow w (c4 (physical faceId)) *
            slabPhysicalMarginFaceResponseSum w physical response rest) _
        (slabPhysicalMarginFaceResponseSum_cons
          w physical response faceId rest) ?_
      rcases hhead with hzero | hone
      · rw [slabCutoffOneBinaryHybridResponse_cons_of_zero
          w physical response faceId rest hzero]
        refine Q'.eqv_trans _
          ((0 : Q') +
            slabPhysicalMarginFaceResponseSum
              w physical response rest) _ ?_ ?_
        · apply Q'.add_eqv_congr'
          · exact Q'.eqv_trans _ _ _
              (Q'.mul_eqv_congr_right _ _ _
                (geomSum_c4_eqv_zero_of_spin_zero
                  w physical faceId hzero))
              (Q'.zero_mul_eqv (response faceId))
          · exact Q'.eqv_trans _ _ _
              (Q'.mul_eqv_congr_right _ _ _
                (qpow_c4_eqv_one_of_spin_zero
                  w physical faceId hzero))
              (Q'.one_mul_eqv
                (slabPhysicalMarginFaceResponseSum
                  w physical response rest))
        · exact Q'.eqv_trans _ _ _
            (Q'.eqv_of_eq
              (Q'.zero_add'
                (slabPhysicalMarginFaceResponseSum
                  w physical response rest)))
            hinduction
      · rw [slabCutoffOneBinaryHybridResponse_cons_of_one
          w physical response faceId rest hone]
        apply Q'.add_eqv_congr'
        · exact Q'.mul_eqv_congr_right _ _ _
            (geomSum_c4_eqv_three_of_spin_one
              w physical faceId hone)
        · exact Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_right _ _ _
              (qpow_c4_eqv_three_of_spin_one
                w physical faceId hone))
            (Q'.mul_eqv_congr_left _ _ _ hinduction)

/-- The literal cutoff-one physical carrier supplies the binary hypothesis
for every face in the corrected slab. -/
theorem slabPhysicalMarginFaceResponseSum_eqv_cutoffOneBinaryHybrid
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (source : EdgeLabelling) (hsource : source ∈ S.fine.physicalLabellings)
    (response : Nat → Q') :
    slabPhysicalMarginFaceResponseSum S.fine.coupling source response
        (slabPhysicalFaceEdges S.fine.extent) ≈
      slabCutoffOneBinaryHybridResponse S.fine.coupling source response
        (slabPhysicalFaceEdges S.fine.extent) := by
  apply slabPhysicalMarginFaceResponseSum_eqv_binaryHybrid
  intro faceId hface
  exact finePhysicalFaceSpin_zero_or_one
    S hfineCutoff source hsource faceId hface

/-! ## 3. Remove the arbitrary face order by equal occupied-face sharing -/

/-- The ordered list of precisely those displayed faces whose spin is one. -/
def slabCutoffOneOccupiedFaces (physical : EdgeLabelling) :
    List Nat → List Nat
  | [] => []
  | faceId :: rest =>
      if physical faceId = 1 then
        faceId :: slabCutoffOneOccupiedFaces physical rest
      else
        slabCutoffOneOccupiedFaces physical rest

/-- Every face retained by the occupied-face selector really has spin one. -/
theorem mem_slabCutoffOneOccupiedFaces_spin_one
    (physical : EdgeLabelling) : ∀ (faces : List Nat) (faceId : Nat),
    faceId ∈ slabCutoffOneOccupiedFaces physical faces →
      physical faceId = 1
  | [], faceId, hmem => by
      cases hmem
  | head :: rest, faceId, hmem => by
      by_cases hhead : physical head = 1
      · simp only [slabCutoffOneOccupiedFaces, hhead, if_true,
          List.mem_cons] at hmem
        rcases hmem with heq | htail
        · subst faceId
          exact hhead
        · exact mem_slabCutoffOneOccupiedFaces_spin_one
            physical rest faceId htail
      · simp only [slabCutoffOneOccupiedFaces, hhead, if_false] at hmem
        exact mem_slabCutoffOneOccupiedFaces_spin_one
          physical rest faceId hmem

/-- On a binary face list, its total SU(2) Casimir exponent is exactly three
times its number of occupied faces. -/
theorem slabPhysicalCasimirExponentOn_eq_three_mul_occupiedCount
    (physical : EdgeLabelling) : ∀ faces : List Nat,
    (∀ faceId, faceId ∈ faces →
      physical faceId = 0 ∨ physical faceId = 1) →
    slabPhysicalCasimirExponentOn physical faces =
      3 * (slabCutoffOneOccupiedFaces physical faces).length
  | [], _ => rfl
  | faceId :: rest, hbinary => by
      have hhead := hbinary faceId List.mem_cons_self
      have htail : ∀ tailFace, tailFace ∈ rest →
          physical tailFace = 0 ∨ physical tailFace = 1 := by
        intro tailFace htailMem
        exact hbinary tailFace (List.mem_cons_of_mem faceId htailMem)
      have hinduction :=
        slabPhysicalCasimirExponentOn_eq_three_mul_occupiedCount
          physical rest htail
      rcases hhead with hzero | hone
      · simp only [slabPhysicalCasimirExponentOn,
          slabCutoffOneOccupiedFaces, hzero, c4_zero,
          Nat.zero_add]
        exact hinduction
      · simp only [slabPhysicalCasimirExponentOn,
          slabCutoffOneOccupiedFaces, hone, if_true, List.length_cons, c4]
        rw [hinduction]
        omega

private theorem listQSum_const_local {A : Type} (constant : Q') :
    ∀ items : List A,
      listQSum (fun _item => constant) items ≈
        Q'.ofNat items.length * constant
  | [] => Q'.eqv_symm (Q'.zero_mul_eqv constant)
  | _first :: rest => by
      refine Q'.eqv_trans _
        (constant + Q'.ofNat rest.length * constant) _ ?_ ?_
      · exact Q'.add_eqv_congr_left constant _ _
          (listQSum_const_local constant rest)
      refine Q'.eqv_symm ?_
      refine Q'.eqv_trans _
        ((Q'.ofNat rest.length + 1) * constant) _ ?_ ?_
      · exact Q'.mul_eqv_congr_right _ _ constant
          (Q'.ofNat_add_eqv rest.length 1)
      refine Q'.eqv_trans _
        (Q'.ofNat rest.length * constant + (1 : Q') * constant) _
        (Q'.add_mul_eqv (Q'.ofNat rest.length) 1 constant) ?_
      exact Q'.eqv_trans _
        (Q'.ofNat rest.length * constant + constant) _
        (Q'.add_eqv_congr_left _ _ _ (Q'.one_mul_eqv constant))
        (Q'.add_comm_eqv
          (Q'.ofNat rest.length * constant) constant)

/-- The order-free share assigned to every occupied face.  In the nonempty
branch it is the global binary geometric quotient divided by the number of
occupied faces. -/
def slabCutoffOneSymmetricMarginShare
    (w : Q') (physical : EdgeLabelling) (faces : List Nat) : Q' :=
  match slabCutoffOneOccupiedFaces physical faces with
  | [] => 0
  | _first :: rest =>
      Q'.divPos
        (geomSum w (3 * (rest.length + 1)))
        (Q'.ofNat (rest.length + 1))
        (Q'.ofNat_succ_pos rest.length)

/-- Order-free face-labelled contributions: every occupied face receives
the same share and empty faces are absent. -/
def slabCutoffOneSymmetricMarginFaceContributions
    (w : Q') (physical : EdgeLabelling) (faces : List Nat) :
    List PhysicalMarginFaceContribution :=
  (slabCutoffOneOccupiedFaces physical faces).map fun faceId =>
    (faceId, slabCutoffOneSymmetricMarginShare w physical faces)

/-- The symmetric occupied-face shares sum exactly to the same global
geometric quotient as the ordered-prefix contributions. -/
theorem slabCutoffOneSymmetricMarginFaceContributions_sum_eqv_geomSum
    (w : Q') (physical : EdgeLabelling) (faces : List Nat)
    (hbinary : ∀ faceId, faceId ∈ faces →
      physical faceId = 0 ∨ physical faceId = 1) :
    listQSum
        (fun contribution : PhysicalMarginFaceContribution =>
          contribution.2)
        (slabCutoffOneSymmetricMarginFaceContributions
          w physical faces) ≈
      geomSum w (slabPhysicalCasimirExponentOn physical faces) := by
  have hexponent :=
    slabPhysicalCasimirExponentOn_eq_three_mul_occupiedCount
      physical faces hbinary
  cases hoccupied : slabCutoffOneOccupiedFaces physical faces with
  | nil =>
      rw [hexponent, hoccupied]
      simp only [List.length_nil, Nat.mul_zero, geomSum_zero,
        slabCutoffOneSymmetricMarginFaceContributions,
        slabCutoffOneSymmetricMarginShare, hoccupied, List.map,
        listQSum]
      exact Q'.eqv_refl 0
  | cons first rest =>
      rw [hexponent, hoccupied]
      unfold slabCutoffOneSymmetricMarginFaceContributions
      rw [hoccupied, listQSum_map]
      simp only [List.length_cons]
      unfold slabCutoffOneSymmetricMarginShare
      rw [hoccupied]
      change
        listQSum
            (fun _faceId =>
              Q'.divPos
                (geomSum w (3 * (rest.length + 1)))
                (Q'.ofNat (rest.length + 1))
                (Q'.ofNat_succ_pos rest.length))
            (first :: rest) ≈
          geomSum w (3 * (rest.length + 1))
      refine Q'.eqv_trans _
        (Q'.ofNat (rest.length + 1) *
          Q'.divPos
            (geomSum w (3 * (rest.length + 1)))
            (Q'.ofNat (rest.length + 1))
            (Q'.ofNat_succ_pos rest.length)) _ ?_ ?_
      · exact listQSum_const_local _ (first :: rest)
      · refine Q'.eqv_trans _
          (Q'.divPos
              (geomSum w (3 * (rest.length + 1)))
              (Q'.ofNat (rest.length + 1))
              (Q'.ofNat_succ_pos rest.length) *
            Q'.ofNat (rest.length + 1)) _ ?_ ?_
        · exact Q'.mul_comm_eqv _ _
        · exact Q'.divPos_mul_eqv _ _ _

/-- On the literal cutoff-one physical source carrier, the symmetric
occupied-face contributions recover the complete source margin quotient. -/
theorem slabCutoffOneSymmetricMarginFaceContributions_sum_eqv_cutoffOne
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (source : EdgeLabelling) (hsource : source ∈ S.fine.physicalLabellings) :
    listQSum
        (fun contribution : PhysicalMarginFaceContribution =>
          contribution.2)
        (slabCutoffOneSymmetricMarginFaceContributions S.fine.coupling
          source (slabPhysicalFaceEdges S.fine.extent)) ≈
      geomSum S.fine.coupling
        (slabPhysicalCasimirExponentOn source
          (slabPhysicalFaceEdges S.fine.extent)) := by
  apply slabCutoffOneSymmetricMarginFaceContributions_sum_eqv_geomSum
  intro faceId hface
  exact finePhysicalFaceSpin_zero_or_one
    S hfineCutoff source hsource faceId hface

/-- Multiplying by one face-independent response makes the ordered-prefix
and symmetric occupied-face decompositions exactly equivalent. -/
theorem slabPhysicalMarginFaceResponseSum_const_eqv_symmetric
    (w : Q') (physical : EdgeLabelling) (faces : List Nat)
    (constant : Q')
    (hbinary : ∀ faceId, faceId ∈ faces →
      physical faceId = 0 ∨ physical faceId = 1) :
    slabPhysicalMarginFaceResponseSum w physical
        (fun _ => constant) faces ≈
      listQSum
        (fun contribution : PhysicalMarginFaceContribution =>
          contribution.2 * constant)
        (slabCutoffOneSymmetricMarginFaceContributions
          w physical faces) := by
  unfold slabPhysicalMarginFaceResponseSum
  refine Q'.eqv_trans _
    (listQSum
        (fun contribution : PhysicalMarginFaceContribution =>
          contribution.2)
        (slabPhysicalMarginFaceContributions w physical faces) *
      constant) _ ?_ ?_
  · exact listQSum_mul_right _ constant _
  refine Q'.eqv_trans _
    (geomSum w (slabPhysicalCasimirExponentOn physical faces) *
      constant) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ constant
      (slabPhysicalMarginFaceContributions_sum_eqv_geomSum
        w physical faces)
  apply Q'.eqv_symm
  refine Q'.eqv_trans _
    (listQSum
        (fun contribution : PhysicalMarginFaceContribution =>
          contribution.2)
        (slabCutoffOneSymmetricMarginFaceContributions
          w physical faces) * constant) _ ?_ ?_
  · exact listQSum_mul_right _ constant _
  · exact Q'.mul_eqv_congr_right _ _ constant
      (slabCutoffOneSymmetricMarginFaceContributions_sum_eqv_geomSum
        w physical faces hbinary)

/-! ## 4. The centered score is exactly the binary hybrid source sum -/

/-- The centered coarse-event response paired with every local coupling
insertion from a fixed fine source. -/
def fineCouplingPhysicalCenteredEventResponse
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (event : EdgeLabelling → Bool) (source : EdgeLabelling) : Q' :=
  S.fine.physicalPartition *
      fineCouplingKernelOutputEventMass K source event -
    fineCouplingPhysicalActualKernelEventRawMass K event

/-- The cutoff-one binary hybrid insertion fold associated with one fine
physical source. -/
def fineCouplingPhysicalSourceBinaryHybridCenteredInsertionSum
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (event : EdgeLabelling → Bool) (source : EdgeLabelling) : Q' :=
  slabCutoffOneBinaryHybridResponse S.fine.coupling source
    (fun _ =>
      fineUnitCouplingPhysicalTerm S source *
        fineCouplingPhysicalCenteredEventResponse K event source)
    (slabPhysicalFaceEdges S.fine.extent)

/-- Sum the exact binary hybrid insertion folds over all fine physical
sources. -/
def fineCouplingPhysicalCenteredMarginBinaryHybridInsertionSum
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (event : EdgeLabelling → Bool) : Q' :=
  listQSum
    (fineCouplingPhysicalSourceBinaryHybridCenteredInsertionSum K event)
    S.fine.physicalLabellings

/-- The order-free fine source--face carrier.  Unlike the original
prefix-weighted carrier, it contains only occupied physical faces and gives
all occupied faces of one source the same coefficient. -/
def fineCouplingPhysicalSymmetricSourceFaceContributionCarrier
    (S : SlabScalePair) :
    List FineCouplingPhysicalSourceFaceContribution :=
  S.fine.physicalLabellings.flatMap fun source =>
    (slabCutoffOneSymmetricMarginFaceContributions S.fine.coupling source
      (slabPhysicalFaceEdges S.fine.extent)).map fun contribution =>
        (source, contribution)

/-- Every entry of the symmetric carrier retains its physical source and an
actually occupied inserted face. -/
theorem fineCouplingPhysicalSymmetricSourceFaceContributionCarrier_mem
    (S : SlabScalePair)
    (entry : FineCouplingPhysicalSourceFaceContribution)
    (hentry : entry ∈
      fineCouplingPhysicalSymmetricSourceFaceContributionCarrier S) :
    entry.1 ∈ S.fine.physicalLabellings ∧
      entry.1 entry.2.1 = 1 := by
  unfold fineCouplingPhysicalSymmetricSourceFaceContributionCarrier at hentry
  rw [List.mem_flatMap] at hentry
  rcases hentry with ⟨source, hsource, hcontribution⟩
  rw [List.mem_map] at hcontribution
  rcases hcontribution with ⟨contribution, hcontribution, rfl⟩
  unfold slabCutoffOneSymmetricMarginFaceContributions at hcontribution
  rw [List.mem_map] at hcontribution
  rcases hcontribution with ⟨faceId, hface, rfl⟩
  exact ⟨hsource,
    mem_slabCutoffOneOccupiedFaces_spin_one source
      (slabPhysicalFaceEdges S.fine.extent) faceId hface⟩

/-- The centered insertion sum on the order-free occupied-face carrier. -/
def fineCouplingPhysicalCenteredMarginSymmetricInsertionSum
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (event : EdgeLabelling → Bool) : Q' :=
  listQSum
    (fineCouplingPhysicalSourceFaceCenteredEventInsertion K event)
    (fineCouplingPhysicalSymmetricSourceFaceContributionCarrier S)

/-- One centered source--face insertion is its face coefficient times a
source-dependent response that is constant across the face list. -/
theorem fineCouplingPhysicalSourceFaceCenteredEventInsertion_eqv_response
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (event : EdgeLabelling → Bool) (source : EdgeLabelling)
    (contribution : PhysicalMarginFaceContribution) :
    fineCouplingPhysicalSourceFaceCenteredEventInsertion K event
        (source, contribution) ≈
      contribution.2 *
        (fineUnitCouplingPhysicalTerm S source *
          fineCouplingPhysicalCenteredEventResponse K event source) := by
  unfold fineCouplingPhysicalSourceFaceCenteredEventInsertion
    fineCouplingPhysicalSourceFaceMarginRawMass
    fineCouplingPhysicalCenteredEventResponse
  exact Q'.mul_assoc_eqv contribution.2
    (fineUnitCouplingPhysicalTerm S source)
    (S.fine.physicalPartition *
        fineCouplingKernelOutputEventMass K source event -
      fineCouplingPhysicalActualKernelEventRawMass K event)

/-- For one cutoff-one physical source, replacing its ordered-prefix face
carrier by the symmetric occupied-face carrier preserves its complete
centered insertion sum. -/
theorem fineCouplingPhysicalSourceLocalInsertionSum_eqv_symmetric
    {S : SlabScalePair} (hfineCutoff : S.fine.cutoff = 1)
    (K : S.FiniteSlabKernel) (event : EdgeLabelling → Bool)
    (source : EdgeLabelling) (hsource : source ∈ S.fine.physicalLabellings) :
    listQSum
        (fineCouplingPhysicalSourceFaceCenteredEventInsertion K event)
        ((slabPhysicalMarginFaceContributions S.fine.coupling source
          (slabPhysicalFaceEdges S.fine.extent)).map
            (fun contribution => (source, contribution))) ≈
      listQSum
        (fineCouplingPhysicalSourceFaceCenteredEventInsertion K event)
        ((slabCutoffOneSymmetricMarginFaceContributions
            S.fine.coupling source
            (slabPhysicalFaceEdges S.fine.extent)).map
          (fun contribution => (source, contribution))) := by
  rw [listQSum_map, listQSum_map]
  let constant :=
    fineUnitCouplingPhysicalTerm S source *
      fineCouplingPhysicalCenteredEventResponse K event source
  refine Q'.eqv_trans _
    (slabPhysicalMarginFaceResponseSum S.fine.coupling source
      (fun _ => constant) (slabPhysicalFaceEdges S.fine.extent)) _ ?_ ?_
  · unfold slabPhysicalMarginFaceResponseSum
    apply listQSum_congr
    intro contribution
    exact fineCouplingPhysicalSourceFaceCenteredEventInsertion_eqv_response
      K event source contribution
  refine Q'.eqv_trans _
    (listQSum
      (fun contribution : PhysicalMarginFaceContribution =>
        contribution.2 * constant)
      (slabCutoffOneSymmetricMarginFaceContributions S.fine.coupling source
        (slabPhysicalFaceEdges S.fine.extent))) _ ?_ ?_
  · apply slabPhysicalMarginFaceResponseSum_const_eqv_symmetric
    intro faceId hface
    exact finePhysicalFaceSpin_zero_or_one
      S hfineCutoff source hsource faceId hface
  · apply Q'.eqv_symm
    apply listQSum_congr
    intro contribution
    exact fineCouplingPhysicalSourceFaceCenteredEventInsertion_eqv_response
      K event source contribution

/-- The full cutoff-one local-insertion sum admits an exactly equivalent
order-free carrier containing only occupied inserted faces. -/
theorem fineCouplingPhysicalCenteredMarginLocalInsertionSum_eqv_symmetric
    {S : SlabScalePair} (hfineCutoff : S.fine.cutoff = 1)
    (K : S.FiniteSlabKernel) (event : EdgeLabelling → Bool) :
    fineCouplingPhysicalCenteredMarginLocalInsertionSum K event ≈
      fineCouplingPhysicalCenteredMarginSymmetricInsertionSum K event := by
  unfold fineCouplingPhysicalCenteredMarginLocalInsertionSum
    fineCouplingPhysicalSourceFaceContributionCarrier
    fineCouplingPhysicalCenteredMarginSymmetricInsertionSum
    fineCouplingPhysicalSymmetricSourceFaceContributionCarrier
  refine Q'.eqv_trans _
    (listQSum
      (fun source =>
        listQSum
          (fineCouplingPhysicalSourceFaceCenteredEventInsertion K event)
          ((slabPhysicalMarginFaceContributions S.fine.coupling source
            (slabPhysicalFaceEdges S.fine.extent)).map
              (fun contribution => (source, contribution))))
      S.fine.physicalLabellings) _ ?_ ?_
  · exact listQSum_flatMap _ _ _
  refine Q'.eqv_trans _
    (listQSum
      (fun source =>
        listQSum
          (fineCouplingPhysicalSourceFaceCenteredEventInsertion K event)
          ((slabCutoffOneSymmetricMarginFaceContributions
              S.fine.coupling source
              (slabPhysicalFaceEdges S.fine.extent)).map
            (fun contribution => (source, contribution))))
      S.fine.physicalLabellings) _ ?_ ?_
  · apply listQSum_congr_on
    intro source hsource
    exact fineCouplingPhysicalSourceLocalInsertionSum_eqv_symmetric
      hfineCutoff K event source hsource
  · exact Q'.eqv_symm (listQSum_flatMap _ _ _)

/-- The cutoff-one centered score-event moment is exactly an order-free sum
of insertions at actually occupied physical faces. -/
theorem fineCouplingPhysicalSourceCenteredMarginEventMoment_eqv_symmetric
    {S : SlabScalePair} (hfineCutoff : S.fine.cutoff = 1)
    (K : S.FiniteSlabKernel) (event : EdgeLabelling → Bool) :
    fineCouplingPhysicalSourceKernelEventMoment K
        (fineCouplingPhysicalSourceCenteredMarginRawDebt S) event ≈
      fineCouplingPhysicalCenteredMarginSymmetricInsertionSum K event := by
  exact Q'.eqv_trans _ _ _
    (fineCouplingPhysicalSourceCenteredMarginEventMoment_eqv_localInsertions
      K event)
    (fineCouplingPhysicalCenteredMarginLocalInsertionSum_eqv_symmetric
      hfineCutoff K event)

/-- At cutoff one, the face-labelled local-insertion sum is exactly the
binary occupied-face hybrid sum. -/
theorem fineCouplingPhysicalCenteredMarginLocalInsertionSum_eqv_binaryHybrid
    {S : SlabScalePair} (hfineCutoff : S.fine.cutoff = 1)
    (K : S.FiniteSlabKernel) (event : EdgeLabelling → Bool) :
    fineCouplingPhysicalCenteredMarginLocalInsertionSum K event ≈
      fineCouplingPhysicalCenteredMarginBinaryHybridInsertionSum K event := by
  unfold fineCouplingPhysicalCenteredMarginLocalInsertionSum
    fineCouplingPhysicalSourceFaceContributionCarrier
    fineCouplingPhysicalCenteredMarginBinaryHybridInsertionSum
  refine Q'.eqv_trans _
    (listQSum
      (fun source =>
        listQSum
          (fineCouplingPhysicalSourceFaceCenteredEventInsertion K event)
          ((slabPhysicalMarginFaceContributions S.fine.coupling source
            (slabPhysicalFaceEdges S.fine.extent)).map
              (fun contribution => (source, contribution))))
      S.fine.physicalLabellings) _ ?_ ?_
  · exact listQSum_flatMap _ _ _
  · apply listQSum_congr_on
    intro source hsource
    rw [listQSum_map]
    refine Q'.eqv_trans _
      (slabPhysicalMarginFaceResponseSum S.fine.coupling source
        (fun _ =>
          fineUnitCouplingPhysicalTerm S source *
            fineCouplingPhysicalCenteredEventResponse K event source)
        (slabPhysicalFaceEdges S.fine.extent)) _ ?_ ?_
    · unfold slabPhysicalMarginFaceResponseSum
      apply listQSum_congr
      intro contribution
      unfold fineCouplingPhysicalSourceFaceCenteredEventInsertion
        fineCouplingPhysicalSourceFaceMarginRawMass
        fineCouplingPhysicalCenteredEventResponse
      exact Q'.mul_assoc_eqv contribution.2
        (fineUnitCouplingPhysicalTerm S source)
        (S.fine.physicalPartition *
            fineCouplingKernelOutputEventMass K source event -
          fineCouplingPhysicalActualKernelEventRawMass K event)
    · exact slabPhysicalMarginFaceResponseSum_eqv_cutoffOneBinaryHybrid
        S hfineCutoff source hsource
          (fun _ =>
            fineUnitCouplingPhysicalTerm S source *
              fineCouplingPhysicalCenteredEventResponse K event source)

/-- The one-replica centered score-event moment on the actual cutoff-one
schedule is exactly a sum of binary occupied-face hybrid responses. -/
theorem fineCouplingPhysicalSourceCenteredMarginEventMoment_eqv_binaryHybrid
    {S : SlabScalePair} (hfineCutoff : S.fine.cutoff = 1)
    (K : S.FiniteSlabKernel) (event : EdgeLabelling → Bool) :
    fineCouplingPhysicalSourceKernelEventMoment K
        (fineCouplingPhysicalSourceCenteredMarginRawDebt S) event ≈
      fineCouplingPhysicalCenteredMarginBinaryHybridInsertionSum K event := by
  exact Q'.eqv_trans _ _ _
    (fineCouplingPhysicalSourceCenteredMarginEventMoment_eqv_localInsertions
      K event)
    (fineCouplingPhysicalCenteredMarginLocalInsertionSum_eqv_binaryHybrid
      hfineCutoff K event)

#print axioms finePhysicalFaceSpin_zero_or_one
#print axioms geomSum_c4_eqv_zero_of_spin_zero
#print axioms qpow_c4_eqv_one_of_spin_zero
#print axioms geomSum_c4_eqv_three_of_spin_one
#print axioms qpow_c4_eqv_three_of_spin_one
#print axioms slabPhysicalMarginFaceResponseSum
#print axioms slabPhysicalMarginFaceResponseSum_cons
#print axioms slabCutoffOneBinaryHybridResponse
#print axioms slabCutoffOneBinaryHybridResponse_cons_of_zero
#print axioms slabCutoffOneBinaryHybridResponse_cons_of_one
#print axioms slabPhysicalMarginFaceResponseSum_eqv_binaryHybrid
#print axioms slabPhysicalMarginFaceResponseSum_eqv_cutoffOneBinaryHybrid
#print axioms slabCutoffOneOccupiedFaces
#print axioms mem_slabCutoffOneOccupiedFaces_spin_one
#print axioms slabPhysicalCasimirExponentOn_eq_three_mul_occupiedCount
#print axioms slabCutoffOneSymmetricMarginShare
#print axioms slabCutoffOneSymmetricMarginFaceContributions
#print axioms slabCutoffOneSymmetricMarginFaceContributions_sum_eqv_geomSum
#print axioms slabCutoffOneSymmetricMarginFaceContributions_sum_eqv_cutoffOne
#print axioms slabPhysicalMarginFaceResponseSum_const_eqv_symmetric
#print axioms fineCouplingPhysicalCenteredEventResponse
#print axioms fineCouplingPhysicalSourceBinaryHybridCenteredInsertionSum
#print axioms fineCouplingPhysicalCenteredMarginBinaryHybridInsertionSum
#print axioms fineCouplingPhysicalSymmetricSourceFaceContributionCarrier
#print axioms fineCouplingPhysicalSymmetricSourceFaceContributionCarrier_mem
#print axioms fineCouplingPhysicalCenteredMarginSymmetricInsertionSum
#print axioms fineCouplingPhysicalSourceFaceCenteredEventInsertion_eqv_response
#print axioms fineCouplingPhysicalSourceLocalInsertionSum_eqv_symmetric
#print axioms fineCouplingPhysicalCenteredMarginLocalInsertionSum_eqv_symmetric
#print axioms fineCouplingPhysicalSourceCenteredMarginEventMoment_eqv_symmetric
#print axioms fineCouplingPhysicalCenteredMarginLocalInsertionSum_eqv_binaryHybrid
#print axioms fineCouplingPhysicalSourceCenteredMarginEventMoment_eqv_binaryHybrid

end YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginBinaryHybrid
