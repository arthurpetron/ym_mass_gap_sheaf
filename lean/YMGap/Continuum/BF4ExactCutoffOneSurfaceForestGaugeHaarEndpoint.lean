/-
# BF4 forest-gauge Haar endpoint

This module closes the finite Haar endpoint after the checked selected-face
word compiler.  Two explicit block permutations separate the bookkeeping:
one changes the physical 32-edge ordering to the active-carrier ordering,
and one places the surviving mask-dependent chord order in a compact prefix.

## Axiom gate

Finite list induction, checked block swaps, and normalized quaternion Haar
invariance only.  No `Classical.*`, `native_decide`, `sorry`, custom axiom,
choice, or noncomputable declaration.
-/

import YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeHaarEndpointPermutationInterface

namespace YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeHaarEndpoint

set_option maxRecDepth 300000
set_option maxHeartbeats 12000000

open YMGap.Constructive
open YMGap.Continuum.BF4CutoffOneBinarySurfaceCertificate
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneHaarFiveEvaluation
open YMGap.Continuum.BF4ExactCutoffOneSurfaceActiveCarrier
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGauge
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeFaceProductBridge
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeHaarEndpointPermutation
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeHaarEndpointPermutationInterface
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugePolynomialSemantics
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeStepCoordinateCheck
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeTranslation
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordSemantics
open YMGap.Continuum.BF4ExactSlabSelectedFaceCanonicalWord
open YMGap.Continuum.BF4ExactSpatialTreeGaugeRawCarrier
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionArbitraryHaarHomogenization
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionBivalentHaarContraction
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionSpinTwoConditionalHaar

local infix:50 " ≈ " => Q'.eqv

/-! ## Physical, active, and padded selected-face products -/

/-- A rooted-path-substituted face in the original physical edge blocks. -/
def physicalSubstitutedSurfaceGaugeFaceFactor
    (mask faceId : Nat) : RatPoly :=
  compactFundamentalWordFactor
    (substituteSurfaceGaugeWord mask
      (hypercubeFaceWords.getD faceId []))

/-- The same substituted face after the fixed physical-to-active relabeling,
before the harmless 32-block identity padding. -/
def activeSubstitutedSurfaceGaugeFaceFactor
    (mask faceId : Nat) : RatPoly :=
  compactFundamentalWordFactor
    ((substituteSurfaceGaugeWord mask
      (hypercubeFaceWords.getD faceId [])).map fun entry =>
        (surfaceActiveBlock entry.1, entry.2))

def physicalSubstitutedSurfaceGaugeFactors (mask : Nat) : List RatPoly :=
  (surfaceSelectedCompactFaceIds mask).map
    (physicalSubstitutedSurfaceGaugeFaceFactor mask)

def activeSubstitutedSurfaceGaugeFactors (mask : Nat) : List RatPoly :=
  (surfaceSelectedCompactFaceIds mask).map
    (activeSubstitutedSurfaceGaugeFaceFactor mask)

/-- The unrenumbered physical-chord factor left after the tree variables in
one selected face have been eliminated. -/
def physicalSurfaceGaugeFaceFactor (mask faceId : Nat) : RatPoly :=
  compactFundamentalWordFactor
    (surfaceForestGaugePhysicalWord mask
      (hypercubeFaceWords.getD faceId []))

def physicalSurfaceGaugeFactors (mask : Nat) : List RatPoly :=
  (surfaceSelectedCompactFaceIds mask).map
    (physicalSurfaceGaugeFaceFactor mask)

private theorem paddedActiveSubstitutedSurfaceGaugeFaceFactor_prefix
    (mask faceId : Nat) :
    QuaternionPrefixPolynomialEqv 32
      (paddedActiveSubstitutedSurfaceGaugeFaceFactor mask faceId)
      (activeSubstitutedSurfaceGaugeFaceFactor mask faceId) := by
  unfold paddedActiveSubstitutedSurfaceGaugeFaceFactor
    activeSubstitutedSurfaceGaugeFaceFactor
    compactFundamentalWordFactor
  exact
    (identityReindexPolyQuaternion_prefix 32
      (compactOrientedQuaternionWord
        ((substituteSurfaceGaugeWord mask
          (hypercubeFaceWords.getD faceId [])).map fun entry =>
            (surfaceActiveBlock entry.1, entry.2)))).scalar.character 1

private theorem paddedActiveSubstitutedSurfaceGaugeFactorProduct_prefix
    (mask : Nat) :
    QuaternionPrefixPolynomialEqv 32
      (factorProduct (paddedActiveSubstitutedSurfaceGaugeFactors mask))
      (factorProduct (activeSubstitutedSurfaceGaugeFactors mask)) := by
  have go : ∀ ids : List Nat,
      QuaternionPrefixPolynomialEqv 32
        (factorProduct (ids.map
          (paddedActiveSubstitutedSurfaceGaugeFaceFactor mask)))
        (factorProduct (ids.map
          (activeSubstitutedSurfaceGaugeFaceFactor mask))) := by
    intro ids
    induction ids with
    | nil => exact QuaternionPrefixPolynomialEqv.refl 32 polyOne
    | cons faceId rest induction =>
        exact
          (paddedActiveSubstitutedSurfaceGaugeFaceFactor_prefix
            mask faceId).mul induction
  simpa [paddedActiveSubstitutedSurfaceGaugeFactors,
    activeSubstitutedSurfaceGaugeFactors] using
    go (surfaceSelectedCompactFaceIds mask)

private theorem applyQuaternionBlockSwapChain_polyMul_local
    {blocks : Nat} :
    ∀ (swaps : List (QuaternionBlockInvolution blocks))
      (left right : RatPoly),
      applyQuaternionBlockSwapChain swaps (polyMul left right) =
        polyMul
          (applyQuaternionBlockSwapChain swaps left)
          (applyQuaternionBlockSwapChain swaps right)
  | [], _, _ => rfl
  | _ :: rest, left, right => by
      simp only [applyQuaternionBlockSwapChain,
        reindexQuaternionPolynomial_mul]
      exact applyQuaternionBlockSwapChain_polyMul_local rest _ _

/-- Pair-word version of the production swap-chain fold theorem. -/
private theorem applyQuaternionBlockSwapChain_pairFold_prefix
    {blocks : Nat}
    (swaps : List (QuaternionBlockInvolution blocks))
    (entries : List (Nat × Bool))
    (target : Nat → Nat)
    (hentry : ∀ entry, entry ∈ entries →
      target entry.1 < blocks ∧
        quaternionBlockSwapChainSource swaps (target entry.1) = entry.1) :
    QuaternionPrefixPolyQuaternionEqv blocks
      (applyQuaternionBlockSwapChainQuaternion swaps
        (compactOrientedQuaternionWord entries))
      (compactOrientedQuaternionWord
        (entries.map fun entry => (target entry.1, entry.2))) := by
  have go : ∀ (remaining : List (Nat × Bool))
      (sourceInitial targetInitial : PolyQuaternion),
      QuaternionPrefixPolyQuaternionEqv blocks
        (applyQuaternionBlockSwapChainQuaternion swaps sourceInitial)
        targetInitial →
      (∀ entry, entry ∈ remaining →
        target entry.1 < blocks ∧
          quaternionBlockSwapChainSource swaps (target entry.1) = entry.1) →
      QuaternionPrefixPolyQuaternionEqv blocks
        (applyQuaternionBlockSwapChainQuaternion swaps
          (remaining.foldl
            (fun total entry => PolyQuaternion.mul total
              (orientedCoordinateQuaternion entry.1 entry.2))
            sourceInitial))
        ((remaining.map fun entry => (target entry.1, entry.2)).foldl
          (fun total entry => PolyQuaternion.mul total
            (orientedCoordinateQuaternion entry.1 entry.2))
          targetInitial) := by
    intro remaining
    induction remaining with
    | nil =>
        intro sourceInitial targetInitial hinitial _
        simpa using hinitial
    | cons entry rest induction =>
        intro sourceInitial targetInitial hinitial hremaining
        simp only [List.foldl_cons, List.map_cons]
        apply induction
        · rw [applyQuaternionBlockSwapChainQuaternion_mul]
          exact hinitial.mul
            (applyQuaternionBlockSwapChain_orientedCoordinate_prefix
              swaps
              (hremaining entry List.mem_cons_self).1
              (hremaining entry List.mem_cons_self).2 entry.2)
        · intro other hother
          exact hremaining other
            (List.mem_cons_of_mem entry hother)
  exact go entries PolyQuaternion.one PolyQuaternion.one
    (applyQuaternionBlockSwapChainQuaternion_one_prefix swaps) hentry

private theorem physicalToActive_word_prefix
    (word : List (Nat × Bool))
    (hword : ∀ entry, entry ∈ word → entry.1 < 32) :
    QuaternionPrefixPolyQuaternionEqv 32
      (applyQuaternionBlockSwapChainQuaternion
        physicalToActiveSwapCertificate.steps
        (compactOrientedQuaternionWord word))
      (compactOrientedQuaternionWord
        (word.map fun entry => (surfaceActiveBlock entry.1, entry.2))) := by
  exact applyQuaternionBlockSwapChain_pairFold_prefix
    physicalToActiveSwapCertificate.steps word surfaceActiveBlock
      fun entry hentry =>
      ⟨surfaceActiveBlock_lt_of_lt entry.1 (hword entry hentry),
        physicalToActiveSwapCertificate.coordinate
          entry.1 (hword entry hentry)⟩

private theorem physicalToActive_faceFactor_prefix
    (mask : Nat) (hmask : mask ∈ binarySurfaceMasks)
    (faceId : Nat) (hface : faceId ∈ surfaceSelectedCompactFaceIds mask) :
    QuaternionPrefixPolynomialEqv 32
      (applyQuaternionBlockSwapChain
        physicalToActiveSwapCertificate.steps
        (physicalSubstitutedSurfaceGaugeFaceFactor mask faceId))
      (activeSubstitutedSurfaceGaugeFaceFactor mask faceId) := by
  unfold physicalSubstitutedSurfaceGaugeFaceFactor
    activeSubstitutedSurfaceGaugeFaceFactor compactFundamentalWordFactor
  have hword :=
    (physicalToActive_word_prefix
      (substituteSurfaceGaugeWord mask
        (hypercubeFaceWords.getD faceId []))
      (substitutedSurfaceGaugeWord_block_lt
        mask hmask faceId hface)).scalar
  rw [applyQuaternionBlockSwapChainQuaternion_scalar] at hword
  exact QuaternionPrefixPolynomialEqv.trans
    (applyQuaternionBlockSwapChain_character_prefix
      physicalToActiveSwapCertificate.steps
      (compactOrientedQuaternionWord
        (substituteSurfaceGaugeWord mask
          (hypercubeFaceWords.getD faceId []))).scalar 1)
    (hword.character 1)

private theorem physicalToActive_factorProduct_prefix
    (mask : Nat) (hmask : mask ∈ binarySurfaceMasks) :
    QuaternionPrefixPolynomialEqv 32
      (applyQuaternionBlockSwapChain
        physicalToActiveSwapCertificate.steps
        (factorProduct (physicalSubstitutedSurfaceGaugeFactors mask)))
      (factorProduct (activeSubstitutedSurfaceGaugeFactors mask)) := by
  have go : ∀ ids : List Nat,
      (∀ faceId, faceId ∈ ids →
        faceId ∈ surfaceSelectedCompactFaceIds mask) →
      QuaternionPrefixPolynomialEqv 32
        (applyQuaternionBlockSwapChain
          physicalToActiveSwapCertificate.steps
          (factorProduct (ids.map
            (physicalSubstitutedSurfaceGaugeFaceFactor mask))))
        (factorProduct (ids.map
          (activeSubstitutedSurfaceGaugeFaceFactor mask))) := by
    intro ids
    induction ids with
    | nil =>
        intro _
        simp only [List.map_nil, factorProduct]
        change QuaternionPrefixPolynomialEqv 32
          (applyQuaternionBlockSwapChain
            physicalToActiveSwapCertificate.steps
            PolyQuaternion.one.scalar)
          PolyQuaternion.one.scalar
        rw [← applyQuaternionBlockSwapChainQuaternion_scalar
          physicalToActiveSwapCertificate.steps PolyQuaternion.one]
        exact
          (applyQuaternionBlockSwapChainQuaternion_one_prefix
            physicalToActiveSwapCertificate.steps).scalar
    | cons faceId rest induction =>
        intro hids
        simp only [List.map_cons, factorProduct,
          applyQuaternionBlockSwapChain_polyMul_local]
        exact (physicalToActive_faceFactor_prefix mask hmask faceId
          (hids faceId List.mem_cons_self)).mul
          (induction fun other hother =>
            hids other (List.mem_cons_of_mem faceId hother))
  simpa [physicalSubstitutedSurfaceGaugeFactors,
    activeSubstitutedSurfaceGaugeFactors] using
    go (surfaceSelectedCompactFaceIds mask) (fun _ hface => hface)

/-! ## Supported 32-block products and fixed-permutation Haar transport -/

private theorem supported_polyZero_endpoint (blocks : Nat) :
    SupportedQuaternionBlocks blocks polyZero := by
  intro term hterm
  simp [polyZero] at hterm

private theorem supported_polyOne_endpoint (blocks : Nat) :
    SupportedQuaternionBlocks blocks polyOne := by
  intro term hterm
  simp only [polyOne, List.mem_cons, List.not_mem_nil, or_false] at hterm
  subst term
  simp

private theorem supported_polyVar_endpoint
    {blocks coordinate : Nat} (hcoordinate : coordinate < 4 * blocks) :
    SupportedQuaternionBlocks blocks (polyVar coordinate) := by
  intro term hterm
  simp only [polyVar, List.mem_cons, List.not_mem_nil, or_false] at hterm
  subst term
  simp [RingNormaliser.varMono]
  omega

private theorem supported_polyAdd_endpoint
    {blocks : Nat} {left right : RatPoly}
    (hleft : SupportedQuaternionBlocks blocks left)
    (hright : SupportedQuaternionBlocks blocks right) :
    SupportedQuaternionBlocks blocks (polyAdd left right) := by
  intro term hterm
  rcases List.mem_append.mp hterm with hterm | hterm
  · exact hleft term hterm
  · exact hright term hterm

private theorem supported_polyNeg_endpoint
    {blocks : Nat} {polynomial : RatPoly}
    (hsupport : SupportedQuaternionBlocks blocks polynomial) :
    SupportedQuaternionBlocks blocks (polyNeg polynomial) := by
  intro term hterm
  obtain ⟨source, hsource, hsourceEq⟩ := List.mem_map.mp hterm
  rw [← hsourceEq]
  exact hsupport source hsource

private theorem supported_polySmul_endpoint
    {blocks : Nat} {scale : Q'} {polynomial : RatPoly}
    (hsupport : SupportedQuaternionBlocks blocks polynomial) :
    SupportedQuaternionBlocks blocks (polySmul scale polynomial) := by
  intro term hterm
  obtain ⟨source, hsource, hsourceEq⟩ := List.mem_map.mp hterm
  rw [← hsourceEq]
  exact hsupport source hsource

private structure SupportedPolyQuaternionEndpoint
    (blocks : Nat) (quaternion : PolyQuaternion) : Prop where
  scalar : SupportedQuaternionBlocks blocks quaternion.scalar
  iPart : SupportedQuaternionBlocks blocks quaternion.iPart
  jPart : SupportedQuaternionBlocks blocks quaternion.jPart
  kPart : SupportedQuaternionBlocks blocks quaternion.kPart

private theorem supportedPolyQuaternion_one_endpoint (blocks : Nat) :
    SupportedPolyQuaternionEndpoint blocks PolyQuaternion.one :=
  ⟨supported_polyOne_endpoint blocks, supported_polyZero_endpoint blocks,
    supported_polyZero_endpoint blocks, supported_polyZero_endpoint blocks⟩

private theorem supportedPolyQuaternion_coordinateVariable_endpoint
    {blocks block : Nat} (hblock : block < blocks) :
    SupportedPolyQuaternionEndpoint blocks
      (PolyQuaternion.coordinateVariable block) := by
  constructor <;> apply supported_polyVar_endpoint <;> omega

private theorem supportedPolyQuaternion_conj_endpoint
    {blocks : Nat} {quaternion : PolyQuaternion}
    (hsupport : SupportedPolyQuaternionEndpoint blocks quaternion) :
    SupportedPolyQuaternionEndpoint blocks (PolyQuaternion.conj quaternion) :=
  ⟨hsupport.scalar, supported_polyNeg_endpoint hsupport.iPart,
    supported_polyNeg_endpoint hsupport.jPart,
    supported_polyNeg_endpoint hsupport.kPart⟩

private theorem supportedPolyQuaternion_mul_endpoint
    {blocks : Nat} {left right : PolyQuaternion}
    (hleft : SupportedPolyQuaternionEndpoint blocks left)
    (hright : SupportedPolyQuaternionEndpoint blocks right) :
    SupportedPolyQuaternionEndpoint blocks (PolyQuaternion.mul left right) := by
  constructor
  · exact supported_polyAdd_endpoint
      (supported_polyMul hleft.scalar hright.scalar)
      (supported_polyNeg_endpoint (supported_polyAdd_endpoint
        (supported_polyMul hleft.iPart hright.iPart)
        (supported_polyAdd_endpoint
          (supported_polyMul hleft.jPart hright.jPart)
          (supported_polyMul hleft.kPart hright.kPart))))
  · exact supported_polyAdd_endpoint
      (supported_polyMul hleft.scalar hright.iPart)
      (supported_polyAdd_endpoint
        (supported_polyMul hleft.iPart hright.scalar)
        (supported_polyAdd_endpoint
          (supported_polyMul hleft.jPart hright.kPart)
          (supported_polyNeg_endpoint
            (supported_polyMul hleft.kPart hright.jPart))))
  · exact supported_polyAdd_endpoint
      (supported_polyMul hleft.scalar hright.jPart)
      (supported_polyAdd_endpoint
        (supported_polyMul hleft.jPart hright.scalar)
        (supported_polyAdd_endpoint
          (supported_polyMul hleft.kPart hright.iPart)
          (supported_polyNeg_endpoint
            (supported_polyMul hleft.iPart hright.kPart))))
  · exact supported_polyAdd_endpoint
      (supported_polyMul hleft.scalar hright.kPart)
      (supported_polyAdd_endpoint
        (supported_polyMul hleft.kPart hright.scalar)
        (supported_polyAdd_endpoint
          (supported_polyMul hleft.iPart hright.jPart)
          (supported_polyNeg_endpoint
            (supported_polyMul hleft.jPart hright.iPart))))

private theorem orientedCoordinateQuaternion_supported_endpoint
    {blocks block : Nat} (hblock : block < blocks) (reverse : Bool) :
    SupportedPolyQuaternionEndpoint blocks
      (orientedCoordinateQuaternion block reverse) := by
  cases reverse with
  | false =>
      simpa [orientedCoordinateQuaternion] using
        (supportedPolyQuaternion_coordinateVariable_endpoint hblock)
  | true =>
      simpa [orientedCoordinateQuaternion] using
        (supportedPolyQuaternion_conj_endpoint
          (supportedPolyQuaternion_coordinateVariable_endpoint hblock))

private theorem compactOrientedQuaternionWord_supported_endpoint
    {blocks : Nat} (word : List (Nat × Bool))
    (hword : ∀ entry, entry ∈ word → entry.1 < blocks) :
    SupportedPolyQuaternionEndpoint blocks
      (compactOrientedQuaternionWord word) := by
  have go : ∀ (entries : List (Nat × Bool)) (total : PolyQuaternion),
      (∀ entry, entry ∈ entries → entry.1 < blocks) →
      SupportedPolyQuaternionEndpoint blocks total →
      SupportedPolyQuaternionEndpoint blocks
        (entries.foldl
          (fun current entry => PolyQuaternion.mul current
            (orientedCoordinateQuaternion entry.1 entry.2)) total) := by
    intro entries
    induction entries with
    | nil =>
        intro total _ htotal
        exact htotal
    | cons entry rest induction =>
        intro total hentries htotal
        simp only [List.foldl_cons]
        exact induction _
          (fun other hother =>
            hentries other (List.mem_cons_of_mem entry hother))
          (supportedPolyQuaternion_mul_endpoint htotal
            (orientedCoordinateQuaternion_supported_endpoint
              (hentries entry List.mem_cons_self) entry.2))
  exact go word PolyQuaternion.one hword
    (supportedPolyQuaternion_one_endpoint blocks)

private theorem compactFundamentalWordFactor_supported_endpoint
    {blocks : Nat} (word : List (Nat × Bool))
    (hword : ∀ entry, entry ∈ word → entry.1 < blocks) :
    SupportedQuaternionBlocks blocks (compactFundamentalWordFactor word) := by
  unfold compactFundamentalWordFactor
  change SupportedQuaternionBlocks blocks
    (polySmul 2 (compactOrientedQuaternionWord word).scalar)
  exact supported_polySmul_endpoint
    (compactOrientedQuaternionWord_supported_endpoint word hword).scalar

private theorem factorProduct_supported_endpoint
    {blocks : Nat} : ∀ factors : List RatPoly,
    (∀ factor, factor ∈ factors →
      SupportedQuaternionBlocks blocks factor) →
    SupportedQuaternionBlocks blocks (factorProduct factors)
  | [], _ => supported_polyOne_endpoint blocks
  | factor :: rest, hfactors =>
      supported_polyMul
        (hfactors factor List.mem_cons_self)
        (factorProduct_supported_endpoint rest fun other hother =>
          hfactors other (List.mem_cons_of_mem factor hother))

private theorem physicalSubstitutedSurfaceGaugeFactorProduct_supported
    (mask : Nat) (hmask : mask ∈ binarySurfaceMasks) :
    SupportedQuaternionBlocks 32
      (factorProduct (physicalSubstitutedSurfaceGaugeFactors mask)) := by
  apply factorProduct_supported_endpoint
  intro factor hfactor
  obtain ⟨faceId, hface, rfl⟩ := List.mem_map.mp hfactor
  exact compactFundamentalWordFactor_supported_endpoint _
    (substitutedSurfaceGaugeWord_block_lt mask hmask faceId hface)

private theorem activeSubstitutedSurfaceGaugeFactorProduct_supported
    (mask : Nat) (hmask : mask ∈ binarySurfaceMasks) :
    SupportedQuaternionBlocks 32
      (factorProduct (activeSubstitutedSurfaceGaugeFactors mask)) := by
  apply factorProduct_supported_endpoint
  intro factor hfactor
  obtain ⟨faceId, hface, rfl⟩ := List.mem_map.mp hfactor
  apply compactFundamentalWordFactor_supported_endpoint
  intro entry hentry
  obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hentry
  exact surfaceActiveBlock_lt_of_lt source.1
    (substitutedSurfaceGaugeWord_block_lt
      mask hmask faceId hface source hsource)

private theorem paddedActiveSubstitutedSurfaceGaugeFactorProduct_supported
    (mask : Nat) :
    SupportedQuaternionBlocks 32
      (factorProduct (paddedActiveSubstitutedSurfaceGaugeFactors mask)) := by
  apply factorProduct_supported_endpoint
  intro factor hfactor
  obtain ⟨faceId, _, rfl⟩ := List.mem_map.mp hfactor
  unfold paddedActiveSubstitutedSurfaceGaugeFaceFactor
  change SupportedQuaternionBlocks 32
    (polySmul 2
      (reindexPolyQuaternion (identityQuaternionBlockInvolution 32)
        (compactOrientedQuaternionWord
          ((substituteSurfaceGaugeWord mask
            (hypercubeFaceWords.getD faceId [])).map fun entry =>
              (surfaceActiveBlock entry.1, entry.2)))).scalar)
  exact supported_polySmul_endpoint
    (reindexQuaternionPolynomial_supported
      (identityQuaternionBlockInvolution 32) _)

/-- The padded active rooted-path product and the physical substituted product
have exactly the same normalized 32-block Haar integral. -/
theorem paddedActiveSubstitutedSurfaceGaugeFactorProduct_haar_physical
    (mask : Nat) (hmask : mask ∈ binarySurfaceMasks) :
    quaternionHaar 32
        (factorProduct (paddedActiveSubstitutedSurfaceGaugeFactors mask)) ≈
      quaternionHaar 32
        (factorProduct (physicalSubstitutedSurfaceGaugeFactors mask)) := by
  have hphysical :=
    physicalSubstitutedSurfaceGaugeFactorProduct_supported mask hmask
  have hactive :=
    activeSubstitutedSurfaceGaugeFactorProduct_supported mask hmask
  have hpadded :=
    paddedActiveSubstitutedSurfaceGaugeFactorProduct_supported mask
  have hchain := applyQuaternionBlockSwapChain_supported
    physicalToActiveSwapCertificate.steps _ hphysical
  exact Q'.eqv_trans _ _ _
    (quaternionHaar_prefixPolynomialEqv 32
      (paddedActiveSubstitutedSurfaceGaugeFactorProduct_prefix mask)
      hpadded hactive)
    (Q'.eqv_trans _ _ _
      (Q'.eqv_symm (quaternionHaar_prefixPolynomialEqv 32
        (physicalToActive_factorProduct_prefix mask hmask)
        hchain hactive))
      (quaternionHaar_applyQuaternionBlockSwapChain
        physicalToActiveSwapCertificate.steps _ hphysical))

/-! ## Facewise tree reduction lifted to the whole physical product -/

private theorem physicalSurfaceGaugeFactorProducts_carrier
    (mask : Nat) (hmask : mask ∈ binarySurfaceMasks) :
    HaarCarrierEqv 32
      (factorProduct (physicalSubstitutedSurfaceGaugeFactors mask))
      (factorProduct (physicalSurfaceGaugeFactors mask)) := by
  have go : ∀ ids : List Nat,
      (∀ faceId, faceId ∈ ids →
        faceId ∈ surfaceSelectedCompactFaceIds mask) →
      HaarCarrierListEqv 32
        (ids.map (physicalSubstitutedSurfaceGaugeFaceFactor mask))
        (ids.map (physicalSurfaceGaugeFaceFactor mask)) := by
    intro ids
    induction ids with
    | nil =>
        intro _
        exact HaarCarrierListEqv.nil
    | cons faceId rest induction =>
        intro hids
        exact HaarCarrierListEqv.cons
          (substitutedSurfaceGaugeFaceFactor_carrier
            mask hmask faceId (hids faceId List.mem_cons_self))
          (induction fun other hother =>
            hids other (List.mem_cons_of_mem faceId hother))
  exact factorProduct_carrier_of_listEqv
    (by simpa [physicalSubstitutedSurfaceGaugeFactors,
        physicalSurfaceGaugeFactors,
        physicalSubstitutedSurfaceGaugeFaceFactor,
        physicalSurfaceGaugeFaceFactor] using
      go (surfaceSelectedCompactFaceIds mask) (fun _ hface => hface))

private theorem quaternionHaar_polyOne_left_endpoint
    (blocks : Nat) (polynomial : RatPoly) :
    quaternionHaar blocks (polyMul polyOne polynomial) ≈
      quaternionHaar blocks polynomial := by
  exact Q'.eqv_trans _ _ _
    (quaternionHaar_polyMul_comm blocks polyOne polynomial)
    (quaternionHaar_polyMul_one_right blocks polynomial)

theorem physicalSubstitutedSurfaceGaugeFactorProduct_haar_chords
    (mask : Nat) (hmask : mask ∈ binarySurfaceMasks) :
    quaternionHaar 32
        (factorProduct (physicalSubstitutedSurfaceGaugeFactors mask)) ≈
      quaternionHaar 32
        (factorProduct (physicalSurfaceGaugeFactors mask)) := by
  have hcarrier := physicalSurfaceGaugeFactorProducts_carrier mask hmask
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm (quaternionHaar_polyOne_left_endpoint 32 _))
    (Q'.eqv_trans _ _ _
      (hcarrier polyOne)
      (quaternionHaar_polyOne_left_endpoint 32 _))

/-- The padded active selected-face product has the same 32-block Haar value
as the unrenumbered physical chord product. -/
theorem paddedActiveSubstitutedSurfaceGaugeFactorProduct_haar_chords
    (mask : Nat) (hmask : mask ∈ binarySurfaceMasks) :
    quaternionHaar 32
        (factorProduct (paddedActiveSubstitutedSurfaceGaugeFactors mask)) ≈
      quaternionHaar 32
        (factorProduct (physicalSurfaceGaugeFactors mask)) :=
  Q'.eqv_trans _ _ _
    (paddedActiveSubstitutedSurfaceGaugeFactorProduct_haar_physical
      mask hmask)
    (physicalSubstitutedSurfaceGaugeFactorProduct_haar_chords mask hmask)

/-! ## Mask-dependent chord-prefix compaction -/

theorem pruneSurfacePrimalForest_eq_physical_map
    (mask : Nat) : ∀ word : List (Nat × Bool),
    pruneSurfacePrimalForest mask word =
      (surfaceForestGaugePhysicalWord mask word).map fun entry =>
        (natListIndexOf entry.1 (surfaceForestGaugeChordEdgeIds mask), entry.2)
  | [] => rfl
  | entry :: rest => by
      by_cases hentry : entry.1 ∈ surfaceForestGaugeChordEdgeIds mask
      · simp [pruneSurfacePrimalForest, surfaceForestGaugePhysicalWord,
          hentry, pruneSurfacePrimalForest_eq_physical_map mask rest]
      · simp [pruneSurfacePrimalForest, surfaceForestGaugePhysicalWord,
          hentry, pruneSurfacePrimalForest_eq_physical_map mask rest]

private theorem physicalWord_entry_chord
    (mask : Nat) (word : List (Nat × Bool))
    (entry : Nat × Bool)
    (hentry : entry ∈ surfaceForestGaugePhysicalWord mask word) :
    entry.1 ∈ surfaceForestGaugeChordEdgeIds mask := by
  exact of_decide_eq_true (List.mem_filter.mp hentry).2

private theorem surfaceChordCarrier_coordinate_explicit
    (mask : Nat) (hmask : mask ∈ binarySurfaceMasks)
    (edgeId : Nat) (hedge : edgeId ∈ surfaceForestGaugeChordEdgeIds mask) :
    natListIndexOf edgeId (surfaceForestGaugeChordEdgeIds mask) < 32 ∧
      quaternionBlockSwapChainSource
        (surfaceChordCarrierSwapCertificate.steps mask hmask)
        (natListIndexOf edgeId (surfaceForestGaugeChordEdgeIds mask)) = edgeId := by
  exact surfaceChordCarrier_coordinate mask hmask edgeId hedge

private theorem physicalChordToCompact_word_prefix
    (mask : Nat) (hmask : mask ∈ binarySurfaceMasks)
    (word : List (Nat × Bool)) :
    QuaternionPrefixPolyQuaternionEqv 32
      (applyQuaternionBlockSwapChainQuaternion
        (surfaceChordCarrierSwapCertificate.steps mask hmask)
        (compactOrientedQuaternionWord
          (surfaceForestGaugePhysicalWord mask word)))
      (compactOrientedQuaternionWord
        (pruneSurfacePrimalForest mask word)) := by
  rw [pruneSurfacePrimalForest_eq_physical_map]
  exact applyQuaternionBlockSwapChain_pairFold_prefix
    (surfaceChordCarrierSwapCertificate.steps mask hmask)
    (surfaceForestGaugePhysicalWord mask word)
    (fun edgeId => natListIndexOf edgeId
      (surfaceForestGaugeChordEdgeIds mask))
    fun entry hentry =>
      surfaceChordCarrier_coordinate_explicit mask hmask entry.1
        (physicalWord_entry_chord mask word entry hentry)

private theorem physicalChordToCompact_faceFactor_prefix
    (mask : Nat) (hmask : mask ∈ binarySurfaceMasks) (faceId : Nat) :
    QuaternionPrefixPolynomialEqv 32
      (applyQuaternionBlockSwapChain
        (surfaceChordCarrierSwapCertificate.steps mask hmask)
        (physicalSurfaceGaugeFaceFactor mask faceId))
      (compactFundamentalWordFactor
        (pruneSurfacePrimalForest mask
          (hypercubeFaceWords.getD faceId []))) := by
  unfold physicalSurfaceGaugeFaceFactor compactFundamentalWordFactor
  have hword :=
    (physicalChordToCompact_word_prefix mask hmask
      (hypercubeFaceWords.getD faceId [])).scalar
  rw [applyQuaternionBlockSwapChainQuaternion_scalar] at hword
  exact QuaternionPrefixPolynomialEqv.trans
    (applyQuaternionBlockSwapChain_character_prefix
      (surfaceChordCarrierSwapCertificate.steps mask hmask)
      (compactOrientedQuaternionWord
        (surfaceForestGaugePhysicalWord mask
          (hypercubeFaceWords.getD faceId []))).scalar 1)
    (hword.character 1)

private theorem physicalChordToCompact_factorProduct_prefix
    (mask : Nat) (hmask : mask ∈ binarySurfaceMasks) :
    QuaternionPrefixPolynomialEqv 32
      (applyQuaternionBlockSwapChain
        (surfaceChordCarrierSwapCertificate.steps mask hmask)
        (factorProduct (physicalSurfaceGaugeFactors mask)))
      (factorProduct (surfaceForestGaugeFactors mask)) := by
  have go : ∀ ids : List Nat,
      QuaternionPrefixPolynomialEqv 32
        (applyQuaternionBlockSwapChain
          (surfaceChordCarrierSwapCertificate.steps mask hmask)
          (factorProduct (ids.map
            (physicalSurfaceGaugeFaceFactor mask))))
        (factorProduct (ids.map fun faceId =>
          compactFundamentalWordFactor
            (pruneSurfacePrimalForest mask
              (hypercubeFaceWords.getD faceId [])))) := by
    intro ids
    induction ids with
    | nil =>
        simp only [List.map_nil, factorProduct]
        change QuaternionPrefixPolynomialEqv 32
          (applyQuaternionBlockSwapChain
            (surfaceChordCarrierSwapCertificate.steps mask hmask)
            PolyQuaternion.one.scalar)
          PolyQuaternion.one.scalar
        rw [← applyQuaternionBlockSwapChainQuaternion_scalar
          (surfaceChordCarrierSwapCertificate.steps mask hmask)
          PolyQuaternion.one]
        exact
          (applyQuaternionBlockSwapChainQuaternion_one_prefix
            (surfaceChordCarrierSwapCertificate.steps mask hmask)).scalar
    | cons faceId rest induction =>
        simp only [List.map_cons, factorProduct,
          applyQuaternionBlockSwapChain_polyMul_local]
        exact
          (physicalChordToCompact_faceFactor_prefix
            mask hmask faceId).mul induction
  simpa [physicalSurfaceGaugeFactors, surfaceForestGaugeFactors,
    surfaceForestGaugeWords] using
    go (surfaceSelectedCompactFaceIds mask)

def hypercubeFaceWordBlockBoundCheck : Bool :=
  hypercubeFaceWords.all fun word =>
    word.all fun entry => decide (entry.1 < 32)

theorem hypercubeFaceWordBlockBoundCheck_true :
    hypercubeFaceWordBlockBoundCheck = true := by
  decide

private theorem hypercubeFaceWord_block_lt
    (faceId : Nat) (hfaceId : faceId < 24)
    (entry : Nat × Bool)
    (hentry : entry ∈ hypercubeFaceWords.getD faceId []) :
    entry.1 < 32 := by
  have hwordsLength : hypercubeFaceWords.length = 24 := by decide
  have hfaceMem : hypercubeFaceWords.getD faceId [] ∈ hypercubeFaceWords := by
    have hindex : faceId < hypercubeFaceWords.length := by omega
    have hget := List.getElem_eq_getD
      (l := hypercubeFaceWords) (i := faceId) (h := hindex) []
    rw [← hget]
    exact List.getElem_mem hindex
  have hrow := List.all_eq_true.mp
    hypercubeFaceWordBlockBoundCheck_true _ hfaceMem
  exact of_decide_eq_true (List.all_eq_true.mp hrow entry hentry)

private theorem selectedFaceId_lt
    (mask faceId : Nat)
    (hface : faceId ∈ surfaceSelectedCompactFaceIds mask) :
    faceId < 24 := by
  exact List.mem_range.mp (List.mem_filter.mp hface).1

private theorem physicalSurfaceGaugeFactorProduct_supported
    (mask : Nat) :
    SupportedQuaternionBlocks 32
      (factorProduct (physicalSurfaceGaugeFactors mask)) := by
  apply factorProduct_supported_endpoint
  intro factor hfactor
  obtain ⟨faceId, hface, rfl⟩ := List.mem_map.mp hfactor
  apply compactFundamentalWordFactor_supported_endpoint
  intro entry hentry
  exact hypercubeFaceWord_block_lt faceId
    (selectedFaceId_lt mask faceId hface) entry
    (List.mem_filter.mp hentry).1

private theorem pruneSurfacePrimalForest_block_lt
    (mask : Nat) (word : List (Nat × Bool)) (entry : Nat × Bool)
    (hentry : entry ∈ pruneSurfacePrimalForest mask word) :
    entry.1 < (surfaceForestGaugeChordEdgeIds mask).length := by
  rw [pruneSurfacePrimalForest_eq_physical_map] at hentry
  obtain ⟨physicalEntry, hphysical, rfl⟩ := List.mem_map.mp hentry
  exact natListIndexOf_lt_length_of_mem physicalEntry.1
    (surfaceForestGaugeChordEdgeIds mask)
    (physicalWord_entry_chord mask word physicalEntry hphysical)

private theorem surfaceForestGaugeFactorProduct_supported
    (mask : Nat) :
    SupportedQuaternionBlocks
      (surfaceForestGaugeChordEdgeIds mask).length
      (factorProduct (surfaceForestGaugeFactors mask)) := by
  apply factorProduct_supported_endpoint
  intro factor hfactor
  obtain ⟨word, hword, rfl⟩ := List.mem_map.mp hfactor
  apply compactFundamentalWordFactor_supported_endpoint
  intro entry hentry
  unfold surfaceForestGaugeWords at hword
  obtain ⟨faceId, hface, rfl⟩ := List.mem_map.mp hword
  exact pruneSurfacePrimalForest_block_lt mask _ entry hentry

private theorem surfaceForestGaugeFactorProduct_supported_32
    (mask : Nat) (hmask : mask ∈ binarySurfaceMasks) :
    SupportedQuaternionBlocks 32
      (factorProduct (surfaceForestGaugeFactors mask)) := by
  apply factorProduct_supported_endpoint
  intro factor hfactor
  obtain ⟨word, hword, rfl⟩ := List.mem_map.mp hfactor
  apply compactFundamentalWordFactor_supported_endpoint
  intro entry hentry
  unfold surfaceForestGaugeWords at hword
  obtain ⟨faceId, hface, rfl⟩ := List.mem_map.mp hword
  exact Nat.lt_of_lt_of_le
    (pruneSurfacePrimalForest_block_lt mask _ entry hentry)
    (surfaceChordCarrier_length_le mask hmask)

theorem physicalSurfaceGaugeFactorProduct_haar_compact32
    (mask : Nat) (hmask : mask ∈ binarySurfaceMasks) :
    quaternionHaar 32
        (factorProduct (physicalSurfaceGaugeFactors mask)) ≈
      quaternionHaar 32
        (factorProduct (surfaceForestGaugeFactors mask)) := by
  have hphysical := physicalSurfaceGaugeFactorProduct_supported mask
  have hcompact := surfaceForestGaugeFactorProduct_supported_32 mask hmask
  have hchain := applyQuaternionBlockSwapChain_supported
    (surfaceChordCarrierSwapCertificate.steps mask hmask) _ hphysical
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (quaternionHaar_applyQuaternionBlockSwapChain
        (surfaceChordCarrierSwapCertificate.steps mask hmask) _ hphysical))
    (quaternionHaar_prefixPolynomialEqv 32
      (physicalChordToCompact_factorProduct_prefix mask hmask)
      hchain hcompact)

/-! ## Constructive deletion of the unused chord-carrier tail -/

private theorem supported_weaken_endpoint
    {small large : Nat} {polynomial : RatPoly}
    (hle : small ≤ large)
    (hsupport : SupportedQuaternionBlocks small polynomial) :
    SupportedQuaternionBlocks large polynomial := by
  intro term hterm
  have hlength := hsupport term hterm
  omega

private theorem exponentAt_eq_zero_of_length_le_endpoint :
    ∀ (values : List Nat) (coordinate : Nat),
      values.length ≤ coordinate → exponentAt values coordinate = 0
  | [], coordinate, _ => by simp [exponentAt]
  | value :: rest, 0, hlength => by simp at hlength
  | value :: rest, coordinate + 1, hlength => by
      simp only [exponentAt, List.getD_cons_succ]
      apply exponentAt_eq_zero_of_length_le_endpoint rest coordinate
      simp only [List.length_cons] at hlength
      omega

private theorem allZero_of_exponentAt_zero_endpoint
    (values : List Nat)
    (hzero : ∀ coordinate, coordinate < values.length →
      exponentAt values coordinate = 0) :
    allZero values = true := by
  induction values with
  | nil => rfl
  | cons value rest induction =>
      have hhead := hzero 0 (by simp)
      have htail : ∀ coordinate, coordinate < rest.length →
          exponentAt rest coordinate = 0 := by
        intro coordinate hcoordinate
        simpa [exponentAt] using
          hzero (coordinate + 1) (by simp [hcoordinate])
      simp [exponentAt] at hhead
      simp [allZero, hhead, induction htail]

private theorem identityReindexQuaternionPolynomial_tailZero_endpoint
    {active large : Nat} (hle : active ≤ large)
    (polynomial : RatPoly)
    (hsupport : SupportedQuaternionBlocks active polynomial) :
    QuaternionTailZeroAfter active
      (reindexQuaternionPolynomial
        (identityQuaternionBlockInvolution large) polynomial) := by
  intro term hterm
  unfold reindexQuaternionPolynomial at hterm
  obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hterm
  let padded := reindexQuaternionExponents
    (identityQuaternionBlockInvolution large) source.1
  apply allZero_of_exponentAt_zero_endpoint
  intro coordinate hcoordinate
  rw [exponentAt_drop]
  have hpaddedLength : padded.length = 4 * large := by
    exact reindexQuaternionExponents_length
      (identityQuaternionBlockInvolution large) source.1
  have hglobal : 4 * active + coordinate < 4 * large := by
    change coordinate < (padded.drop (4 * active)).length at hcoordinate
    rw [List.length_drop, hpaddedLength] at hcoordinate
    omega
  change exponentAt padded (4 * active + coordinate) = 0
  rw [exponentAt_reindexQuaternionExponents
    (identityQuaternionBlockInvolution large) source.1 hglobal]
  change exponentAt source.1
      (4 * ((4 * active + coordinate) / 4) +
        (4 * active + coordinate) % 4) = 0
  rw [show
    4 * ((4 * active + coordinate) / 4) +
        (4 * active + coordinate) % 4 = 4 * active + coordinate by omega]
  exact exponentAt_eq_zero_of_length_le_endpoint source.1
    (4 * active + coordinate)
    (Nat.le_trans (hsupport source hsource) (by omega))

/-- Normalized Haar variables beyond a syntactically supported prefix
integrate to one.  The proof pads every term to the larger exact carrier,
uses the constructive inactive-tail theorem, and removes that padding by
prefix equivalence. -/
theorem quaternionHaar_extend_supported_endpoint
    {active large : Nat} (hle : active ≤ large)
    (polynomial : RatPoly)
    (hsupport : SupportedQuaternionBlocks active polynomial) :
    quaternionHaar large polynomial ≈
      quaternionHaar active polynomial := by
  let identity := identityQuaternionBlockInvolution large
  let padded := reindexQuaternionPolynomial identity polynomial
  have hlarge : SupportedQuaternionBlocks large polynomial :=
    supported_weaken_endpoint hle hsupport
  have hreindex : quaternionHaar large padded ≈
      quaternionHaar large polynomial := by
    exact quaternionHaar_reindex identity polynomial hlarge
  have hlength : ∀ term, term ∈ padded →
      term.1.length = 4 * large := by
    intro term hterm
    unfold padded reindexQuaternionPolynomial at hterm
    obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hterm
    exact reindexQuaternionExponents_length identity source.1
  have htail : QuaternionTailZeroAfter active padded := by
    exact identityReindexQuaternionPolynomial_tailZero_endpoint
      hle polynomial hsupport
  have htrim : quaternionHaar large padded ≈
      quaternionHaar active
        (trimQuaternionPolynomial active padded) := by
    simpa [Nat.add_sub_of_le hle] using
      (quaternionHaar_trim_inactive active (large - active)
        padded (by simpa [Nat.add_sub_of_le hle] using hlength) htail)
  have hprefix : QuaternionPrefixPolynomialEqv active
      (trimQuaternionPolynomial active padded) polynomial := by
    exact QuaternionPrefixPolynomialEqv.trans
      (trimQuaternionPolynomial_prefix_equiv hle
        (identityReindexQuaternionPolynomial_prefix large polynomial))
      (trimQuaternionPolynomial_prefix_self active polynomial)
  have htrimSupport : SupportedQuaternionBlocks active
      (trimQuaternionPolynomial active padded) :=
    trimQuaternionPolynomial_supported active padded
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hreindex)
    (Q'.eqv_trans _ _ _ htrim
      (quaternionHaar_prefixPolynomialEqv active hprefix
        htrimSupport hsupport))

/-- The compact chord product has the same 32-block Haar value as the exact
factorized evaluator on precisely its mask-dependent chord count. -/
theorem surfaceForestGaugeFactorProduct_haar_endpoint
    (mask : Nat) (hmask : mask ∈ binarySurfaceMasks) :
    quaternionHaar 32
        (factorProduct (surfaceForestGaugeFactors mask)) ≈
      surfaceForestGaugeHaar mask := by
  have hdrop := quaternionHaar_extend_supported_endpoint
    (surfaceChordCarrier_length_le mask hmask)
    (factorProduct (surfaceForestGaugeFactors mask))
    (surfaceForestGaugeFactorProduct_supported mask)
  exact Q'.eqv_trans _ _ _ hdrop
    (quaternionHaar_eq_compactBivalentFactorizedHaar
      (surfaceForestGaugeChordEdgeIds mask).length
      (surfaceForestGaugeFactors mask))

/-- Complete Haar endpoint: the actual padded selected-face product reduces
constructively to the concrete mask-dependent forest-gauge evaluator. -/
theorem paddedActiveSubstitutedSurfaceGaugeFactorProduct_haar_endpoint
    (mask : Nat) (hmask : mask ∈ binarySurfaceMasks) :
    quaternionHaar 32
        (factorProduct (paddedActiveSubstitutedSurfaceGaugeFactors mask)) ≈
      surfaceForestGaugeHaar mask := by
  exact Q'.eqv_trans _ _ _
    (paddedActiveSubstitutedSurfaceGaugeFactorProduct_haar_chords mask hmask)
    (Q'.eqv_trans _ _ _
      (physicalSurfaceGaugeFactorProduct_haar_compact32 mask hmask)
      (surfaceForestGaugeFactorProduct_haar_endpoint mask hmask))

end YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeHaarEndpoint

#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeHaarEndpointPermutation.physicalToActive_source_order
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeHaarEndpointPermutation.physicalToActiveCoordinateCheck_true
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeHaarEndpointPermutation.surfaceChordCarrier_source_order
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeHaarEndpoint.paddedActiveSubstitutedSurfaceGaugeFactorProduct_haar_physical
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeHaarEndpoint.paddedActiveSubstitutedSurfaceGaugeFactorProduct_haar_chords
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeHaarEndpoint.physicalSurfaceGaugeFactorProduct_haar_compact32
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeHaarEndpoint.quaternionHaar_extend_supported_endpoint
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeHaarEndpoint.surfaceForestGaugeFactorProduct_haar_endpoint
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeHaarEndpoint.paddedActiveSubstitutedSurfaceGaugeFactorProduct_haar_endpoint
