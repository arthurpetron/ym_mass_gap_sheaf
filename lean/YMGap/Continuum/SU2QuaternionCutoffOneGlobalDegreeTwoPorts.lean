/-
# Exact global degree-two ports of the cutoff-one channel network

The positive local Haar resolution has two tensor factors at every touched
physical link: its semantic target factor and its semantic source factor.
This file records those factors and their Boolean-coordinate ports before any
channel is selected.

The main result is an exact constructive incidence certificate.  Regrouping
the literal face-major endpoint ports first by physical link and then by
target/source half is a finite permutation of a list of fresh corner pairs.
The pair tags are exactly `0, ..., 4 * |support| - 1`; every pair joins two
distinct factor keys; and every tag occurs exactly twice in the expanded port
word.  Thus this is the degree-two graph required by graphical
Cauchy--Schwarz, including the target--target caps and source--source cups
which prevent a global target/source bipartition.

No Boolean assignment list or channel Cartesian product is formed.

# Axiom gate

No `Classical`, choice, `sorry`/`admit`, `native_decide`, or custom axiom.
-/

import YMGap.Continuum.SU2QuaternionCutoffOneEndpointChannelPorts

namespace YMGap.Continuum.SU2QuaternionCutoffOneGlobalDegreeTwoPorts

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4UnitCubeIncidenceParity
open YMGap.Continuum.SU2QuaternionCutoffOneOrientedFaceRows
open YMGap.Continuum.SU2QuaternionCutoffOneNamedTraceExpansionProduct
open YMGap.Continuum.SU2QuaternionCutoffOneLinkBucketWords
open YMGap.Continuum.SU2QuaternionCutoffOneEndpointChannelPorts

/-- Constructive no-duplicates proof for the initial natural-number segment.
Kept local because the ambient library theorem currently carries a stronger
axiom footprint than this finite incidence argument requires. -/
private theorem cutoffOneRangeNodup (n : Nat) : (List.range n).Nodup := by
  induction n with
  | zero => exact List.nodup_nil
  | succ k ih =>
      rw [List.range_succ]
      refine List.nodup_append.mpr
        ⟨ih, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
      intro x hx b hb heq
      have hbk : b = k := List.mem_singleton.mp hb
      rw [heq, hbk] at hx
      exact absurd (List.mem_range.mp hx) (Nat.lt_irrefl k)

/-! ## 1. Factor keys and literal descriptor ports -/

/-- The two positive-channel tensor factors attached to one physical link. -/
inductive CutoffOneEndpointHalf where
  | target
  | source
  deriving DecidableEq

/-- A tensor factor is determined by a physical link and one endpoint half. -/
structure CutoffOneEndpointFactorKey where
  physicalLink : Z4Link
  half : CutoffOneEndpointHalf
  deriving DecidableEq

/-- One Boolean coordinate port of a target/source tensor factor. -/
structure CutoffOneEndpointPort where
  key : CutoffOneEndpointFactorKey
  tag : Nat
  deriving DecidableEq

def cutoffOneTargetFactorKey (link : Z4Link) :
    CutoffOneEndpointFactorKey :=
  ⟨link, .target⟩

def cutoffOneSourceFactorKey (link : Z4Link) :
    CutoffOneEndpointFactorKey :=
  ⟨link, .source⟩

theorem cutoffOneTargetFactorKey_ne_sourceFactorKey (link : Z4Link) :
    cutoffOneTargetFactorKey link ≠ cutoffOneSourceFactorKey link := by
  intro h
  have hhalf := congrArg CutoffOneEndpointFactorKey.half h
  cases hhalf

theorem cutoffOneEndpointFactorKey_ne_of_physicalLink_ne
    {left right : Z4Link} (hne : left ≠ right)
    (leftHalf rightHalf : CutoffOneEndpointHalf) :
    (⟨left, leftHalf⟩ : CutoffOneEndpointFactorKey) ≠
      ⟨right, rightHalf⟩ := by
  intro h
  exact hne (congrArg CutoffOneEndpointFactorKey.physicalLink h)

def cutoffOneDescriptorTargetPort
    (descriptor : CutoffOneLinkOccurrenceDescriptor) :
    CutoffOneEndpointPort :=
  ⟨cutoffOneTargetFactorKey descriptor.physicalLink,
    CutoffOneLinkOccurrenceDescriptor.baseTag descriptor⟩

def cutoffOneDescriptorSourcePort
    (descriptor : CutoffOneLinkOccurrenceDescriptor) :
    CutoffOneEndpointPort :=
  ⟨cutoffOneSourceFactorKey descriptor.physicalLink,
    CutoffOneLinkOccurrenceDescriptor.endTag descriptor⟩

/-- Literal target-then-source ports of one occurrence descriptor. -/
def cutoffOneDescriptorEndpointPorts
    (descriptor : CutoffOneLinkOccurrenceDescriptor) :
    List CutoffOneEndpointPort :=
  [cutoffOneDescriptorTargetPort descriptor,
   cutoffOneDescriptorSourcePort descriptor]

/-- Literal descriptor-order endpoint ports of one oriented face. -/
def CutoffOneOrientedFaceRow.literalEndpointPorts
    (row : CutoffOneOrientedFaceRow) : List CutoffOneEndpointPort :=
  row.coefficientDescriptors.flatMap cutoffOneDescriptorEndpointPorts

/-! ## 2. The four fresh degree-two pairs of one face -/

/-- A corner variable together with the two factor keys which consume it. -/
structure CutoffOneDegreeTwoPortPair where
  tag : Nat
  firstKey : CutoffOneEndpointFactorKey
  secondKey : CutoffOneEndpointFactorKey
  deriving DecidableEq

def CutoffOneDegreeTwoPortPair.firstPort
    (pair : CutoffOneDegreeTwoPortPair) : CutoffOneEndpointPort :=
  ⟨pair.firstKey, pair.tag⟩

def CutoffOneDegreeTwoPortPair.secondPort
    (pair : CutoffOneDegreeTwoPortPair) : CutoffOneEndpointPort :=
  ⟨pair.secondKey, pair.tag⟩

def CutoffOneDegreeTwoPortPair.ports
    (pair : CutoffOneDegreeTwoPortPair) : List CutoffOneEndpointPort :=
  [pair.firstPort, pair.secondPort]

/-- The first trace corner is a target--target cap. -/
def CutoffOneOrientedFaceRow.firstCornerPortPair
    (row : CutoffOneOrientedFaceRow) : CutoffOneDegreeTwoPortPair :=
  match row.orientation with
  | .standard =>
      ⟨row.firstTag, cutoffOneTargetFactorKey row.link0,
        cutoffOneTargetFactorKey row.link1⟩
  | .reversed =>
      ⟨row.firstTag, cutoffOneTargetFactorKey row.link1,
        cutoffOneTargetFactorKey row.link0⟩

/-- The second trace corner joins a source half to a target half. -/
def CutoffOneOrientedFaceRow.secondCornerPortPair
    (row : CutoffOneOrientedFaceRow) : CutoffOneDegreeTwoPortPair :=
  match row.orientation with
  | .standard =>
      ⟨row.secondTag, cutoffOneSourceFactorKey row.link0,
        cutoffOneTargetFactorKey row.link3⟩
  | .reversed =>
      ⟨row.secondTag, cutoffOneSourceFactorKey row.link1,
        cutoffOneTargetFactorKey row.link2⟩

/-- The third trace corner is a source--source cup. -/
def CutoffOneOrientedFaceRow.thirdCornerPortPair
    (row : CutoffOneOrientedFaceRow) : CutoffOneDegreeTwoPortPair :=
  match row.orientation with
  | .standard =>
      ⟨row.thirdTag, cutoffOneSourceFactorKey row.link3,
        cutoffOneSourceFactorKey row.link2⟩
  | .reversed =>
      ⟨row.thirdTag, cutoffOneSourceFactorKey row.link2,
        cutoffOneSourceFactorKey row.link3⟩

/-- The fourth trace corner joins a target half to a source half. -/
def CutoffOneOrientedFaceRow.fourthCornerPortPair
    (row : CutoffOneOrientedFaceRow) : CutoffOneDegreeTwoPortPair :=
  match row.orientation with
  | .standard =>
      ⟨row.fourthTag, cutoffOneTargetFactorKey row.link2,
        cutoffOneSourceFactorKey row.link1⟩
  | .reversed =>
      ⟨row.fourthTag, cutoffOneTargetFactorKey row.link3,
        cutoffOneSourceFactorKey row.link0⟩

def CutoffOneOrientedFaceRow.degreeTwoPortPairs
    (row : CutoffOneOrientedFaceRow) : List CutoffOneDegreeTwoPortPair :=
  [CutoffOneOrientedFaceRow.firstCornerPortPair row,
   CutoffOneOrientedFaceRow.secondCornerPortPair row,
   CutoffOneOrientedFaceRow.thirdCornerPortPair row,
   CutoffOneOrientedFaceRow.fourthCornerPortPair row]

theorem CutoffOneOrientedFaceRow.degreeTwoPortPairTags_exact
    (row : CutoffOneOrientedFaceRow) :
    (CutoffOneOrientedFaceRow.degreeTwoPortPairs row).map
        CutoffOneDegreeTwoPortPair.tag = row.tags := by
  obtain ⟨supportPosition, physicalFaceId, plaquette, orientation⟩ := row
  cases orientation <;> rfl

/-- The concrete descriptor-order to corner-pair-order permutation. -/
private theorem literalEndpointOrder_perm_degreeTwoOrder {A : Type}
    (aFirst aSecond bFirst bSecond cFirst cSecond dFirst dSecond : A) :
    [aFirst, bFirst, bSecond, cFirst,
      dFirst, cSecond, aSecond, dSecond].Perm
    [aFirst, aSecond, bFirst, bSecond,
      cFirst, cSecond, dFirst, dSecond] := by
  refine List.Perm.cons aFirst ?_
  refine List.Perm.trans
    (List.perm_middle
      (l₁ := [bFirst, bSecond, cFirst, dFirst, cSecond])
      (a := aSecond) (l₂ := [dSecond])) ?_
  refine List.Perm.cons aSecond ?_
  refine List.Perm.cons bFirst ?_
  refine List.Perm.cons bSecond ?_
  refine List.Perm.cons cFirst ?_
  refine List.Perm.trans
    (List.perm_middle (l₁ := [dFirst]) (a := cSecond)
      (l₂ := [dSecond])) ?_
  refine List.Perm.cons cSecond ?_
  exact List.Perm.refl _

/-- The literal face ports and the four adjacent degree-two pairs carry
exactly the same keyed incidences. -/
theorem CutoffOneOrientedFaceRow.literalEndpointPorts_perm_degreeTwoPorts
    (row : CutoffOneOrientedFaceRow) :
    (CutoffOneOrientedFaceRow.literalEndpointPorts row).Perm
      ((CutoffOneOrientedFaceRow.degreeTwoPortPairs row).flatMap
        CutoffOneDegreeTwoPortPair.ports) := by
  obtain ⟨supportPosition, physicalFaceId, plaquette, orientation⟩ := row
  cases orientation <;>
    exact literalEndpointOrder_perm_degreeTwoOrder _ _ _ _ _ _ _ _

/-! ## 3. Distinctness of the two factors at every corner -/

private theorem CutoffOneOrientedFaceRow.boundaryLinkInequalities
    (row : CutoffOneOrientedFaceRow) :
    row.link0 ≠ row.link1 ∧ row.link0 ≠ row.link2 ∧
    row.link0 ≠ row.link3 ∧ row.link1 ≠ row.link2 ∧
    row.link1 ≠ row.link3 ∧ row.link2 ≠ row.link3 := by
  have hnodup : [row.link0, row.link1, row.link2, row.link3].Nodup := by
    change row.boundaryLinks.Nodup
    rw [row.boundaryLinks_eq_edgesOf]
    exact edgesOf_nodup row.plaquette
  have h0 := (List.nodup_cons.mp hnodup).1
  have htail := (List.nodup_cons.mp hnodup).2
  have h1 := (List.nodup_cons.mp htail).1
  have htail' := (List.nodup_cons.mp htail).2
  have h2 := (List.nodup_cons.mp htail').1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    exact h0 (by simp [h])
  · intro h
    exact h0 (by simp [h])
  · intro h
    exact h0 (by simp [h])
  · intro h
    exact h1 (by simp [h])
  · intro h
    exact h1 (by simp [h])
  · intro h
    exact h2 (by simp [h])

theorem CutoffOneOrientedFaceRow.firstCornerPortPair_keys_ne
    (row : CutoffOneOrientedFaceRow) :
    (CutoffOneOrientedFaceRow.firstCornerPortPair row).firstKey ≠
      (CutoffOneOrientedFaceRow.firstCornerPortPair row).secondKey := by
  rcases CutoffOneOrientedFaceRow.boundaryLinkInequalities row with
    ⟨h01, h02, h03, h12, h13, h23⟩
  obtain ⟨supportPosition, physicalFaceId, plaquette, orientation⟩ := row
  cases orientation
  · exact cutoffOneEndpointFactorKey_ne_of_physicalLink_ne h01 _ _
  · exact cutoffOneEndpointFactorKey_ne_of_physicalLink_ne
      (fun h => h01 h.symm) _ _

theorem CutoffOneOrientedFaceRow.secondCornerPortPair_keys_ne
    (row : CutoffOneOrientedFaceRow) :
    (CutoffOneOrientedFaceRow.secondCornerPortPair row).firstKey ≠
      (CutoffOneOrientedFaceRow.secondCornerPortPair row).secondKey := by
  rcases CutoffOneOrientedFaceRow.boundaryLinkInequalities row with
    ⟨h01, h02, h03, h12, h13, h23⟩
  obtain ⟨supportPosition, physicalFaceId, plaquette, orientation⟩ := row
  cases orientation
  · exact cutoffOneEndpointFactorKey_ne_of_physicalLink_ne h03 _ _
  · exact cutoffOneEndpointFactorKey_ne_of_physicalLink_ne h12 _ _

theorem CutoffOneOrientedFaceRow.thirdCornerPortPair_keys_ne
    (row : CutoffOneOrientedFaceRow) :
    (CutoffOneOrientedFaceRow.thirdCornerPortPair row).firstKey ≠
      (CutoffOneOrientedFaceRow.thirdCornerPortPair row).secondKey := by
  rcases CutoffOneOrientedFaceRow.boundaryLinkInequalities row with
    ⟨h01, h02, h03, h12, h13, h23⟩
  obtain ⟨supportPosition, physicalFaceId, plaquette, orientation⟩ := row
  cases orientation
  · exact cutoffOneEndpointFactorKey_ne_of_physicalLink_ne
      (fun h => h23 h.symm) _ _
  · exact cutoffOneEndpointFactorKey_ne_of_physicalLink_ne h23 _ _

theorem CutoffOneOrientedFaceRow.fourthCornerPortPair_keys_ne
    (row : CutoffOneOrientedFaceRow) :
    (CutoffOneOrientedFaceRow.fourthCornerPortPair row).firstKey ≠
      (CutoffOneOrientedFaceRow.fourthCornerPortPair row).secondKey := by
  rcases CutoffOneOrientedFaceRow.boundaryLinkInequalities row with
    ⟨h01, h02, h03, h12, h13, h23⟩
  obtain ⟨supportPosition, physicalFaceId, plaquette, orientation⟩ := row
  cases orientation
  · exact cutoffOneEndpointFactorKey_ne_of_physicalLink_ne
      (fun h => h12 h.symm) _ _
  · exact cutoffOneEndpointFactorKey_ne_of_physicalLink_ne
      (fun h => h03 h.symm) _ _

theorem CutoffOneOrientedFaceRow.degreeTwoPortPair_keys_ne
    (row : CutoffOneOrientedFaceRow)
    {pair : CutoffOneDegreeTwoPortPair}
    (hpair : pair ∈ CutoffOneOrientedFaceRow.degreeTwoPortPairs row) :
    pair.firstKey ≠ pair.secondKey := by
  simp only [CutoffOneOrientedFaceRow.degreeTwoPortPairs,
    List.mem_cons, List.not_mem_nil, or_false] at hpair
  rcases hpair with rfl | rfl | rfl | rfl
  · exact CutoffOneOrientedFaceRow.firstCornerPortPair_keys_ne row
  · exact CutoffOneOrientedFaceRow.secondCornerPortPair_keys_ne row
  · exact CutoffOneOrientedFaceRow.thirdCornerPortPair_keys_ne row
  · exact CutoffOneOrientedFaceRow.fourthCornerPortPair_keys_ne row

/-! ## 4. Exact global factors and their port word -/

/-- A concrete target/source tensor factor and the ordered tags in its local
occurrence word. -/
structure CutoffOneEndpointFactor where
  key : CutoffOneEndpointFactorKey
  tags : List Nat
  deriving DecidableEq

def CutoffOneEndpointFactor.ports
    (factor : CutoffOneEndpointFactor) : List CutoffOneEndpointPort :=
  factor.tags.map (fun tag => ⟨factor.key, tag⟩)

def cutoffOneLinkTargetFactor
    (orientationAt : CutoffOneFaceOrientationChoice)
    (n : Nat) (support : List Nat) (link : Z4Link) :
    CutoffOneEndpointFactor :=
  { key := cutoffOneTargetFactorKey link
    tags := (cutoffOneLinkOccurrenceBucket orientationAt n support link).map
      CutoffOneLinkOccurrenceDescriptor.baseTag }

def cutoffOneLinkSourceFactor
    (orientationAt : CutoffOneFaceOrientationChoice)
    (n : Nat) (support : List Nat) (link : Z4Link) :
    CutoffOneEndpointFactor :=
  { key := cutoffOneSourceFactorKey link
    tags := (cutoffOneLinkOccurrenceBucket orientationAt n support link).map
      CutoffOneLinkOccurrenceDescriptor.endTag }

/-- Exact factor order: touched-link order, target half before source half. -/
def cutoffOneEndpointFactors
    (orientationAt : CutoffOneFaceOrientationChoice)
    (n : Nat) (support : List Nat) : List CutoffOneEndpointFactor :=
  (cutoffOneTouchedLinks n support).flatMap (fun link =>
    [cutoffOneLinkTargetFactor orientationAt n support link,
     cutoffOneLinkSourceFactor orientationAt n support link])

def cutoffOneEndpointFactorKeyWord (links : List Z4Link) :
    List CutoffOneEndpointFactorKey :=
  links.flatMap (fun link =>
    [cutoffOneTargetFactorKey link, cutoffOneSourceFactorKey link])

theorem mem_cutoffOneEndpointFactorKeyWord
    {links : List Z4Link} {key : CutoffOneEndpointFactorKey} :
    key ∈ cutoffOneEndpointFactorKeyWord links ↔
      key.physicalLink ∈ links := by
  rcases key with ⟨link, half⟩
  cases half <;>
    simp [cutoffOneEndpointFactorKeyWord,
      cutoffOneTargetFactorKey, cutoffOneSourceFactorKey]

theorem cutoffOneEndpointFactorKeyWord_nodup
    (links : List Z4Link) (hnodup : links.Nodup) :
    (cutoffOneEndpointFactorKeyWord links).Nodup := by
  induction links with
  | nil => exact List.nodup_nil
  | cons link links ih =>
      have hparts := List.nodup_cons.mp hnodup
      change
        (cutoffOneTargetFactorKey link ::
          cutoffOneSourceFactorKey link ::
          cutoffOneEndpointFactorKeyWord links).Nodup
      refine List.nodup_cons.mpr ⟨?_, ?_⟩
      · intro hmem
        rcases List.mem_cons.mp hmem with hhead | htail
        · exact cutoffOneTargetFactorKey_ne_sourceFactorKey link hhead
        · exact hparts.1
            (mem_cutoffOneEndpointFactorKeyWord.mp htail)
      · refine List.nodup_cons.mpr ⟨?_, ih hparts.2⟩
        intro hmem
        exact hparts.1
          (mem_cutoffOneEndpointFactorKeyWord.mp hmem)

theorem cutoffOneEndpointFactors_keys_exact
    (orientationAt : CutoffOneFaceOrientationChoice)
    (n : Nat) (support : List Nat) :
    (cutoffOneEndpointFactors orientationAt n support).map
        CutoffOneEndpointFactor.key =
      cutoffOneEndpointFactorKeyWord (cutoffOneTouchedLinks n support) := by
  unfold cutoffOneEndpointFactors cutoffOneEndpointFactorKeyWord
  rw [List.map_flatMap]
  rfl

theorem cutoffOneEndpointFactors_keys_nodup
    (orientationAt : CutoffOneFaceOrientationChoice)
    (n : Nat) (support : List Nat) :
    ((cutoffOneEndpointFactors orientationAt n support).map
      CutoffOneEndpointFactor.key).Nodup := by
  rw [cutoffOneEndpointFactors_keys_exact]
  exact cutoffOneEndpointFactorKeyWord_nodup _
    (cutoffOneTouchedLinks_nodup n support)

/-- The factor-grouped global keyed port word. -/
def cutoffOneEndpointFactorPorts
    (orientationAt : CutoffOneFaceOrientationChoice)
    (n : Nat) (support : List Nat) : List CutoffOneEndpointPort :=
  (cutoffOneEndpointFactors orientationAt n support).flatMap
    CutoffOneEndpointFactor.ports

private theorem targetPorts_append_sourcePorts_perm_descriptorPorts :
    ∀ descriptors : List CutoffOneLinkOccurrenceDescriptor,
      (descriptors.map cutoffOneDescriptorTargetPort ++
          descriptors.map cutoffOneDescriptorSourcePort).Perm
        (descriptors.flatMap cutoffOneDescriptorEndpointPorts)
  | [] => List.Perm.refl []
  | descriptor :: descriptors => by
      simp only [List.map_cons, List.flatMap_cons]
      refine List.Perm.cons (cutoffOneDescriptorTargetPort descriptor) ?_
      refine List.Perm.trans
        (List.perm_middle
          (l₁ := descriptors.map cutoffOneDescriptorTargetPort)
          (a := cutoffOneDescriptorSourcePort descriptor)
          (l₂ := descriptors.map cutoffOneDescriptorSourcePort)) ?_
      exact List.Perm.cons (cutoffOneDescriptorSourcePort descriptor)
        (targetPorts_append_sourcePorts_perm_descriptorPorts descriptors)

private theorem cutoffOneLinkTargetFactor_ports_eq_descriptorTargetPorts
    (orientationAt : CutoffOneFaceOrientationChoice)
    (n : Nat) (support : List Nat) (link : Z4Link) :
    (cutoffOneLinkTargetFactor orientationAt n support link).ports =
      (cutoffOneLinkOccurrenceBucket orientationAt n support link).map
        cutoffOneDescriptorTargetPort := by
  unfold cutoffOneLinkTargetFactor CutoffOneEndpointFactor.ports
  rw [List.map_map]
  apply List.map_congr_left
  intro descriptor hdescriptor
  simp only [Function.comp_apply, cutoffOneDescriptorTargetPort]
  rw [(mem_cutoffOneLinkOccurrenceBucket.mp hdescriptor).2]

private theorem cutoffOneLinkSourceFactor_ports_eq_descriptorSourcePorts
    (orientationAt : CutoffOneFaceOrientationChoice)
    (n : Nat) (support : List Nat) (link : Z4Link) :
    (cutoffOneLinkSourceFactor orientationAt n support link).ports =
      (cutoffOneLinkOccurrenceBucket orientationAt n support link).map
        cutoffOneDescriptorSourcePort := by
  unfold cutoffOneLinkSourceFactor CutoffOneEndpointFactor.ports
  rw [List.map_map]
  apply List.map_congr_left
  intro descriptor hdescriptor
  simp only [Function.comp_apply, cutoffOneDescriptorSourcePort]
  rw [(mem_cutoffOneLinkOccurrenceBucket.mp hdescriptor).2]

private theorem endpointFactorPorts_perm_linkMajorDescriptorPorts_aux
    (orientationAt : CutoffOneFaceOrientationChoice)
    (n : Nat) (support : List Nat) : ∀ links : List Z4Link,
    ((links.flatMap (fun link =>
        [cutoffOneLinkTargetFactor orientationAt n support link,
         cutoffOneLinkSourceFactor orientationAt n support link])).flatMap
      CutoffOneEndpointFactor.ports).Perm
    ((links.flatMap (cutoffOneLinkOccurrenceBucket
        orientationAt n support)).flatMap
      cutoffOneDescriptorEndpointPorts)
  | [] => List.Perm.refl []
  | link :: links => by
      simp only [List.flatMap_cons, List.flatMap_append,
        List.map_cons, List.map_nil]
      rw [cutoffOneLinkTargetFactor_ports_eq_descriptorTargetPorts,
        cutoffOneLinkSourceFactor_ports_eq_descriptorSourcePorts]
      simpa only [List.append_nil, List.nil_append, List.append_assoc] using
        (((targetPorts_append_sourcePorts_perm_descriptorPorts
          (cutoffOneLinkOccurrenceBucket
            orientationAt n support link)).append_right
          ((links.flatMap (fun current =>
            [cutoffOneLinkTargetFactor orientationAt n support current,
             cutoffOneLinkSourceFactor orientationAt n support current])).flatMap
              CutoffOneEndpointFactor.ports)).trans
          ((endpointFactorPorts_perm_linkMajorDescriptorPorts_aux
            orientationAt n support links).append_left
            ((cutoffOneLinkOccurrenceBucket
              orientationAt n support link).flatMap
                cutoffOneDescriptorEndpointPorts)))

private theorem endpointFactorPorts_perm_linkMajorDescriptorPorts
    (orientationAt : CutoffOneFaceOrientationChoice)
    (n : Nat) (support : List Nat) :
    (cutoffOneEndpointFactorPorts orientationAt n support).Perm
      ((cutoffOneLinkMajorOccurrenceDescriptors orientationAt n support).flatMap
        cutoffOneDescriptorEndpointPorts) := by
  change
    (((cutoffOneTouchedLinks n support).flatMap (fun link =>
        [cutoffOneLinkTargetFactor orientationAt n support link,
         cutoffOneLinkSourceFactor orientationAt n support link])).flatMap
      CutoffOneEndpointFactor.ports).Perm
    (((cutoffOneTouchedLinks n support).flatMap
        (cutoffOneLinkOccurrenceBucket orientationAt n support)).flatMap
      cutoffOneDescriptorEndpointPorts)
  exact endpointFactorPorts_perm_linkMajorDescriptorPorts_aux
    orientationAt n support (cutoffOneTouchedLinks n support)

/-! ## 5. The global fresh pair carrier -/

def cutoffOneGlobalDegreeTwoPortPairs
    (orientationAt : CutoffOneFaceOrientationChoice)
    (n : Nat) (support : List Nat) : List CutoffOneDegreeTwoPortPair :=
  (cutoffOneOrientedFaceRows orientationAt n support).flatMap
    CutoffOneOrientedFaceRow.degreeTwoPortPairs

def cutoffOneGlobalDegreeTwoPorts
    (orientationAt : CutoffOneFaceOrientationChoice)
    (n : Nat) (support : List Nat) : List CutoffOneEndpointPort :=
  (cutoffOneGlobalDegreeTwoPortPairs orientationAt n support).flatMap
    CutoffOneDegreeTwoPortPair.ports

theorem cutoffOneGlobalDegreeTwoPortPairTags_exact
    (orientationAt : CutoffOneFaceOrientationChoice)
    (n : Nat) (support : List Nat) :
    (cutoffOneGlobalDegreeTwoPortPairs orientationAt n support).map
        CutoffOneDegreeTwoPortPair.tag =
      cutoffOneCornerTags support := by
  unfold cutoffOneGlobalDegreeTwoPortPairs
  rw [List.map_flatMap]
  change
    (cutoffOneOrientedFaceRows orientationAt n support).flatMap
        (fun row => (CutoffOneOrientedFaceRow.degreeTwoPortPairs row).map
          CutoffOneDegreeTwoPortPair.tag) = _
  simp only [CutoffOneOrientedFaceRow.degreeTwoPortPairTags_exact]
  exact cutoffOneFaceMajorCornerTags_eq_cornerTags
    orientationAt n support

/-- The canonical one-copy corner ledger is duplicate-free. -/
theorem cutoffOneCornerTags_nodup (support : List Nat) :
    (cutoffOneCornerTags support).Nodup := by
  unfold cutoffOneCornerTags
  exact cutoffOneRangeNodup _

theorem cutoffOneGlobalDegreeTwoPortPairTags_nodup
    (orientationAt : CutoffOneFaceOrientationChoice)
    (n : Nat) (support : List Nat) :
    ((cutoffOneGlobalDegreeTwoPortPairs orientationAt n support).map
      CutoffOneDegreeTwoPortPair.tag).Nodup := by
  rw [cutoffOneGlobalDegreeTwoPortPairTags_exact]
  exact cutoffOneCornerTags_nodup support

theorem cutoffOneGlobalDegreeTwoPortPair_keys_ne
    (orientationAt : CutoffOneFaceOrientationChoice)
    (n : Nat) (support : List Nat)
    {pair : CutoffOneDegreeTwoPortPair}
    (hpair : pair ∈
      cutoffOneGlobalDegreeTwoPortPairs orientationAt n support) :
    pair.firstKey ≠ pair.secondKey := by
  unfold cutoffOneGlobalDegreeTwoPortPairs at hpair
  obtain ⟨row, hrow, hlocal⟩ := List.mem_flatMap.mp hpair
  exact CutoffOneOrientedFaceRow.degreeTwoPortPair_keys_ne row hlocal

private theorem cutoffOneMemDegreeTwoPairPorts_tag_eq
    {pair : CutoffOneDegreeTwoPortPair}
    {port : CutoffOneEndpointPort}
    (hport : port ∈ pair.ports) :
    port.tag = pair.tag := by
  unfold CutoffOneDegreeTwoPortPair.ports at hport
  rcases List.mem_cons.mp hport with hfirst | hsecond
  · cases hfirst
    rfl
  · have hsecond' : port = pair.secondPort :=
      List.mem_singleton.mp hsecond
    cases hsecond'
    rfl

/-- Distinct pair tags and distinct endpoints inside each pair make the full
keyed port word duplicate-free.  This is the load-bearing strengthening of
the degree-two multiplicity statement: the two copies of one tag belong to
different endpoint-factor keys. -/
private theorem cutoffOneDegreeTwoPorts_nodup_of_pair_data :
    ∀ pairs : List CutoffOneDegreeTwoPortPair,
      (pairs.map CutoffOneDegreeTwoPortPair.tag).Nodup →
      (∀ pair, pair ∈ pairs → pair.firstKey ≠ pair.secondKey) →
      (pairs.flatMap CutoffOneDegreeTwoPortPair.ports).Nodup
  | [], _, _ => List.nodup_nil
  | pair :: pairs, htags, hkeys => by
      have htagParts := List.nodup_cons.mp htags
      have hpairKeys : pair.firstKey ≠ pair.secondKey :=
        hkeys pair List.mem_cons_self
      have hpairPorts : pair.ports.Nodup := by
        unfold CutoffOneDegreeTwoPortPair.ports
        refine List.nodup_cons.mpr ⟨?_, ?_⟩
        · intro hmem
          have hportEq : pair.firstPort = pair.secondPort :=
            List.mem_singleton.mp hmem
          exact hpairKeys
            (congrArg CutoffOneEndpointPort.key hportEq)
        · exact List.nodup_cons.mpr
            ⟨List.not_mem_nil, List.nodup_nil⟩
      have htailPorts :
          (pairs.flatMap CutoffOneDegreeTwoPortPair.ports).Nodup :=
        cutoffOneDegreeTwoPorts_nodup_of_pair_data pairs htagParts.2
          (fun tailPair htailPair =>
            hkeys tailPair (List.mem_cons_of_mem pair htailPair))
      rw [List.flatMap_cons]
      refine List.nodup_append.mpr
        ⟨hpairPorts, htailPorts, ?_⟩
      intro firstPort hfirstPort secondPort hsecondPort hportEq
      obtain ⟨tailPair, htailPair, hsecondLocal⟩ :=
        List.mem_flatMap.mp hsecondPort
      have hfirstTag : firstPort.tag = pair.tag :=
        cutoffOneMemDegreeTwoPairPorts_tag_eq hfirstPort
      have hsecondTag : secondPort.tag = tailPair.tag :=
        cutoffOneMemDegreeTwoPairPorts_tag_eq hsecondLocal
      have htagEq : pair.tag = tailPair.tag := by
        rw [← hfirstTag, hportEq, hsecondTag]
      exact htagParts.1
        (List.mem_map.mpr ⟨tailPair, htailPair, htagEq.symm⟩)

/-- The pair-major global keyed port word has no duplicate port.  Equal tags
occur twice only across the two distinct factor keys certified for that
pair. -/
theorem cutoffOneGlobalDegreeTwoPorts_nodup
    (orientationAt : CutoffOneFaceOrientationChoice)
    (n : Nat) (support : List Nat) :
    (cutoffOneGlobalDegreeTwoPorts orientationAt n support).Nodup := by
  unfold cutoffOneGlobalDegreeTwoPorts
  exact cutoffOneDegreeTwoPorts_nodup_of_pair_data
    (cutoffOneGlobalDegreeTwoPortPairs orientationAt n support)
    (cutoffOneGlobalDegreeTwoPortPairTags_nodup
      orientationAt n support)
    (fun pair hpair =>
      cutoffOneGlobalDegreeTwoPortPair_keys_ne
        orientationAt n support hpair)

private theorem faceRowsLiteralPorts_perm_degreeTwoPorts :
    ∀ rows : List CutoffOneOrientedFaceRow,
      (rows.flatMap CutoffOneOrientedFaceRow.literalEndpointPorts).Perm
        ((rows.flatMap CutoffOneOrientedFaceRow.degreeTwoPortPairs).flatMap
          CutoffOneDegreeTwoPortPair.ports)
  | [] => List.Perm.refl []
  | row :: rows => by
      simp only [List.flatMap_cons, List.flatMap_append]
      exact
        ((CutoffOneOrientedFaceRow.literalEndpointPorts_perm_degreeTwoPorts
          row).append_right
          (rows.flatMap CutoffOneOrientedFaceRow.literalEndpointPorts)).trans
        ((faceRowsLiteralPorts_perm_degreeTwoPorts rows).append_left
          ((CutoffOneOrientedFaceRow.degreeTwoPortPairs row).flatMap
            CutoffOneDegreeTwoPortPair.ports))

private theorem faceMajorDescriptorPorts_eq_faceRowsLiteralPorts
    (orientationAt : CutoffOneFaceOrientationChoice)
    (n : Nat) (support : List Nat) :
    (cutoffOneFaceMajorOccurrenceDescriptors orientationAt n support).flatMap
        cutoffOneDescriptorEndpointPorts =
      (cutoffOneOrientedFaceRows orientationAt n support).flatMap
        CutoffOneOrientedFaceRow.literalEndpointPorts := by
  unfold cutoffOneFaceMajorOccurrenceDescriptors
  induction cutoffOneOrientedFaceRows orientationAt n support with
  | nil => rfl
  | cons row rows ih =>
      simp only [List.flatMap_cons, List.flatMap_append,
        CutoffOneOrientedFaceRow.literalEndpointPorts]
      rw [ih]

/-- **Exact global factor/pair incidence.**  Factor grouping changes only the
order of the literal keyed ports.  Its corner-pair normal form is the fresh
degree-two graph used by the contraction bound. -/
theorem cutoffOneEndpointFactorPorts_perm_globalDegreeTwoPorts
    (orientationAt : CutoffOneFaceOrientationChoice)
    (n : Nat) (support : List Nat) :
    (cutoffOneEndpointFactorPorts orientationAt n support).Perm
      (cutoffOneGlobalDegreeTwoPorts orientationAt n support) := by
  refine (endpointFactorPorts_perm_linkMajorDescriptorPorts
    orientationAt n support).trans ?_
  refine (List.Perm.flatMap_right cutoffOneDescriptorEndpointPorts
    (cutoffOneLinkMajorOccurrenceDescriptors_perm_faceMajor
      orientationAt n support)).trans ?_
  rw [faceMajorDescriptorPorts_eq_faceRowsLiteralPorts]
  exact faceRowsLiteralPorts_perm_degreeTwoPorts
    (cutoffOneOrientedFaceRows orientationAt n support)

/-- Regrouping the pair-major word by endpoint factor preserves the stronger
keyed-port no-duplicates property. -/
theorem cutoffOneEndpointFactorPorts_nodup
    (orientationAt : CutoffOneFaceOrientationChoice)
    (n : Nat) (support : List Nat) :
    (cutoffOneEndpointFactorPorts orientationAt n support).Nodup := by
  exact
    (cutoffOneEndpointFactorPorts_perm_globalDegreeTwoPorts
      orientationAt n support).symm.nodup
      (cutoffOneGlobalDegreeTwoPorts_nodup
        orientationAt n support)

private theorem cutoffOneFactorPorts_nodup_of_mem_flatMap
    {factors : List CutoffOneEndpointFactor}
    {factor : CutoffOneEndpointFactor}
    (hfactor : factor ∈ factors)
    (hall :
      (factors.flatMap CutoffOneEndpointFactor.ports).Nodup) :
    factor.ports.Nodup := by
  induction factors with
  | nil => cases hfactor
  | cons head tail ih =>
      rw [List.flatMap_cons] at hall
      have hparts := List.nodup_append.mp hall
      rcases List.mem_cons.mp hfactor with hhead | htail
      · rw [hhead]
        exact hparts.1
      · exact ih htail hparts.2.1

private theorem cutoffOneNodup_of_mappedPorts_nodup
    (key : CutoffOneEndpointFactorKey) :
    ∀ tags : List Nat,
      (tags.map (fun tag =>
        (⟨key, tag⟩ : CutoffOneEndpointPort))).Nodup →
      tags.Nodup
  | [], _ => List.nodup_nil
  | tag :: tags, hports => by
      have hparts := List.nodup_cons.mp hports
      refine List.nodup_cons.mpr ⟨?_, ?_⟩
      · intro htag
        exact hparts.1
          (List.mem_map.mpr ⟨tag, htag, rfl⟩)
      · exact cutoffOneNodup_of_mappedPorts_nodup key tags hparts.2

/-- Every actual endpoint factor has a duplicate-free local tag word.  The
proof is transferred from the global keyed-port word, so it detects and
excludes a would-be self-loop rather than merely counting the tag twice. -/
theorem cutoffOneEndpointFactor_tags_nodup
    (orientationAt : CutoffOneFaceOrientationChoice)
    (n : Nat) (support : List Nat)
    {factor : CutoffOneEndpointFactor}
    (hfactor : factor ∈
      cutoffOneEndpointFactors orientationAt n support) :
    factor.tags.Nodup := by
  have hfactorPorts : factor.ports.Nodup :=
    cutoffOneFactorPorts_nodup_of_mem_flatMap hfactor
      (cutoffOneEndpointFactorPorts_nodup
        orientationAt n support)
  unfold CutoffOneEndpointFactor.ports at hfactorPorts
  exact cutoffOneNodup_of_mappedPorts_nodup
    factor.key factor.tags hfactorPorts

/-- Factorwise form consumed by the constructive degree-two compiler. -/
theorem cutoffOneEndpointFactorTagWords_factorwise_nodup
    (orientationAt : CutoffOneFaceOrientationChoice)
    (n : Nat) (support : List Nat) :
    ∀ word, word ∈
        (cutoffOneEndpointFactors orientationAt n support).map
          CutoffOneEndpointFactor.tags →
      word.Nodup := by
  intro word hword
  obtain ⟨factor, hfactor, hwordEq⟩ := List.mem_map.mp hword
  rw [← hwordEq]
  exact cutoffOneEndpointFactor_tags_nodup
    orientationAt n support hfactor

/-! ## 6. Every fresh tag occurs exactly twice -/

/-- Constructive multiplicity counter specialized to the fresh natural tags. -/
def cutoffOneTagMultiplicity (tag : Nat) : List Nat → Nat
  | [] => 0
  | head :: tail =>
      (if head = tag then 1 else 0) + cutoffOneTagMultiplicity tag tail

theorem cutoffOneTagMultiplicity_eq_zero_of_not_mem (tag : Nat) :
    ∀ tags : List Nat, tag ∉ tags →
      cutoffOneTagMultiplicity tag tags = 0
  | [], _ => rfl
  | head :: tail, hnot => by
      have hhead : head ≠ tag := by
        intro h
        apply hnot
        rw [h]
        exact List.mem_cons_self
      have htail : tag ∉ tail := by
        intro h
        exact hnot (List.mem_cons_of_mem head h)
      simp only [cutoffOneTagMultiplicity, if_neg hhead, Nat.zero_add]
      exact cutoffOneTagMultiplicity_eq_zero_of_not_mem tag tail htail

theorem cutoffOneTagMultiplicity_eq_one_of_mem_nodup (tag : Nat) :
    ∀ tags : List Nat, tags.Nodup → tag ∈ tags →
      cutoffOneTagMultiplicity tag tags = 1
  | [], _, hmem => by cases hmem
  | head :: tail, hnodup, hmem => by
      have hparts := List.nodup_cons.mp hnodup
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst head
        simp only [cutoffOneTagMultiplicity, if_pos rfl]
        have hzero : cutoffOneTagMultiplicity tag tail = 0 :=
          cutoffOneTagMultiplicity_eq_zero_of_not_mem tag tail hparts.1
        rw [hzero]
        rfl
      · have hne : head ≠ tag := by
          intro h
          subst head
          exact hparts.1 htail
        simp only [cutoffOneTagMultiplicity, if_neg hne, Nat.zero_add]
        exact cutoffOneTagMultiplicity_eq_one_of_mem_nodup
          tag tail hparts.2 htail

theorem cutoffOneTagMultiplicity_perm (tag : Nat) :
    ∀ {left right : List Nat}, left.Perm right →
      cutoffOneTagMultiplicity tag left =
        cutoffOneTagMultiplicity tag right
  | _, _, List.Perm.nil => rfl
  | _, _, List.Perm.cons _ hperm => by
      simp only [cutoffOneTagMultiplicity]
      rw [cutoffOneTagMultiplicity_perm tag hperm]
  | _, _, List.Perm.swap first second rest => by
      simp only [cutoffOneTagMultiplicity]
      omega
  | _, _, List.Perm.trans hleft hright =>
      (cutoffOneTagMultiplicity_perm tag hleft).trans
        (cutoffOneTagMultiplicity_perm tag hright)

def cutoffOneDegreeTwoTagExpansion
    : List CutoffOneDegreeTwoPortPair → List Nat
  | [] => []
  | pair :: pairs =>
      pair.tag :: pair.tag :: cutoffOneDegreeTwoTagExpansion pairs

/-- The pair expansion is exactly the structural word obtained by replacing
each one-copy pair tag by its two adjacent copies. -/
theorem cutoffOneDegreeTwoTagExpansion_eq_flatMap_pairTags :
    ∀ pairs : List CutoffOneDegreeTwoPortPair,
      cutoffOneDegreeTwoTagExpansion pairs =
        (pairs.map CutoffOneDegreeTwoPortPair.tag).flatMap
          (fun tag => [tag, tag])
  | [] => rfl
  | pair :: pairs => by
      change
        pair.tag :: pair.tag :: cutoffOneDegreeTwoTagExpansion pairs =
          pair.tag :: pair.tag ::
            ((pairs.map CutoffOneDegreeTwoPortPair.tag).flatMap
              (fun tag => [tag, tag]))
      exact congrArg (fun tags => pair.tag :: pair.tag :: tags)
        (cutoffOneDegreeTwoTagExpansion_eq_flatMap_pairTags pairs)

theorem cutoffOneTagMultiplicity_degreeTwoTagExpansion
    (tag : Nat) : ∀ pairs : List CutoffOneDegreeTwoPortPair,
    cutoffOneTagMultiplicity tag (cutoffOneDegreeTwoTagExpansion pairs) =
      2 * cutoffOneTagMultiplicity tag
        (pairs.map CutoffOneDegreeTwoPortPair.tag)
  | [] => rfl
  | pair :: pairs => by
      simp only [cutoffOneDegreeTwoTagExpansion, List.map_cons,
        cutoffOneTagMultiplicity]
      rw [cutoffOneTagMultiplicity_degreeTwoTagExpansion tag pairs]
      by_cases htag : pair.tag = tag
      · rw [if_pos htag]
        omega
      · rw [if_neg htag]
        omega

theorem cutoffOneGlobalDegreeTwoPortTags_eq_expansion
    (orientationAt : CutoffOneFaceOrientationChoice)
    (n : Nat) (support : List Nat) :
    (cutoffOneGlobalDegreeTwoPorts orientationAt n support).map
        CutoffOneEndpointPort.tag =
      cutoffOneDegreeTwoTagExpansion
        (cutoffOneGlobalDegreeTwoPortPairs orientationAt n support) := by
  unfold cutoffOneGlobalDegreeTwoPorts
  induction cutoffOneGlobalDegreeTwoPortPairs orientationAt n support with
  | nil => rfl
  | cons pair pairs ih =>
      simp only [List.flatMap_cons, List.map_append,
        CutoffOneDegreeTwoPortPair.ports,
        CutoffOneDegreeTwoPortPair.firstPort,
        CutoffOneDegreeTwoPortPair.secondPort,
        List.map_cons, List.map_nil, List.append_nil,
        cutoffOneDegreeTwoTagExpansion]
      exact congrArg (fun tags => pair.tag :: pair.tag :: tags) ih

/-- The erased global port-tag word is literally two adjacent copies of each
canonical fresh corner tag. -/
theorem cutoffOneGlobalDegreeTwoPortTags_eq_doubledCornerTags
    (orientationAt : CutoffOneFaceOrientationChoice)
    (n : Nat) (support : List Nat) :
    (cutoffOneGlobalDegreeTwoPorts orientationAt n support).map
        CutoffOneEndpointPort.tag =
      (cutoffOneCornerTags support).flatMap (fun tag => [tag, tag]) := by
  rw [cutoffOneGlobalDegreeTwoPortTags_eq_expansion,
    cutoffOneDegreeTwoTagExpansion_eq_flatMap_pairTags,
    cutoffOneGlobalDegreeTwoPortPairTags_exact]

private theorem cutoffOneFlattenFactorTags_eq_flatMapPortTags :
    ∀ factors : List CutoffOneEndpointFactor,
      (factors.map CutoffOneEndpointFactor.tags).flatten =
        (factors.flatMap CutoffOneEndpointFactor.ports).map
          CutoffOneEndpointPort.tag
  | [] => rfl
  | factor :: factors => by
      simp only [List.map_cons, List.flatten_cons, List.flatMap_cons,
        List.map_append]
      rw [cutoffOneFlattenFactorTags_eq_flatMapPortTags factors]
      unfold CutoffOneEndpointFactor.ports
      have hmap :
          (factor.tags.map (fun tag =>
              (⟨factor.key, tag⟩ : CutoffOneEndpointPort))).map
              CutoffOneEndpointPort.tag = factor.tags := by
        induction factor.tags with
        | nil => rfl
        | cons tag tags ih =>
            change tag ::
                ((tags.map (fun entry =>
                  (⟨factor.key, entry⟩ : CutoffOneEndpointPort))).map
                    CutoffOneEndpointPort.tag) = tag :: tags
            exact congrArg (List.cons tag) ih
      rw [hmap]

/-- Erasing the factor keys from the factor-grouped port word recovers
exactly the flattened local factor tag words. -/
theorem cutoffOneEndpointFactorTagWords_flatten_eq_portTags
    (orientationAt : CutoffOneFaceOrientationChoice)
    (n : Nat) (support : List Nat) :
    ((cutoffOneEndpointFactors orientationAt n support).map
        CutoffOneEndpointFactor.tags).flatten =
      (cutoffOneEndpointFactorPorts orientationAt n support).map
        CutoffOneEndpointPort.tag := by
  unfold cutoffOneEndpointFactorPorts
  exact cutoffOneFlattenFactorTags_eq_flatMapPortTags
    (cutoffOneEndpointFactors orientationAt n support)

/-- **Compiler-ready cutoff-one incidence ledger.**  The concatenated local
factor tag words are a permutation of the word containing two adjacent
copies of every canonical corner tag.  This theorem is proof-only incidence
data; it does not extract a port-reordering program from the permutation. -/
theorem cutoffOneEndpointFactorTagWords_flatten_perm_doubledCornerTags
    (orientationAt : CutoffOneFaceOrientationChoice)
    (n : Nat) (support : List Nat) :
    ((cutoffOneEndpointFactors orientationAt n support).map
        CutoffOneEndpointFactor.tags).flatten.Perm
      ((cutoffOneCornerTags support).flatMap (fun tag => [tag, tag])) := by
  rw [cutoffOneEndpointFactorTagWords_flatten_eq_portTags]
  have hperm :=
    (cutoffOneEndpointFactorPorts_perm_globalDegreeTwoPorts
      orientationAt n support).map CutoffOneEndpointPort.tag
  rw [cutoffOneGlobalDegreeTwoPortTags_eq_doubledCornerTags] at hperm
  exact hperm

/-- Every canonical fresh trace coordinate occurs in exactly two factor
ports, with no assignment enumeration and no decidable bulk permutation. -/
theorem cutoffOneGlobalDegreeTwoPort_tagMultiplicity_eq_two
    (orientationAt : CutoffOneFaceOrientationChoice)
    (n : Nat) (support : List Nat) {tag : Nat}
    (htag : tag ∈ cutoffOneCornerTags support) :
    cutoffOneTagMultiplicity tag
        ((cutoffOneGlobalDegreeTwoPorts orientationAt n support).map
          CutoffOneEndpointPort.tag) = 2 := by
  rw [cutoffOneGlobalDegreeTwoPortTags_eq_expansion,
    cutoffOneTagMultiplicity_degreeTwoTagExpansion,
    cutoffOneGlobalDegreeTwoPortPairTags_exact]
  rw [cutoffOneTagMultiplicity_eq_one_of_mem_nodup
    tag (cutoffOneCornerTags support)
    (by
      unfold cutoffOneCornerTags
      exact cutoffOneRangeNodup _) htag]

/-- The same exact degree-two law in the actual link-major,
target-before-source factor grouping. -/
theorem cutoffOneEndpointFactorPort_tagMultiplicity_eq_two
    (orientationAt : CutoffOneFaceOrientationChoice)
    (n : Nat) (support : List Nat) {tag : Nat}
    (htag : tag ∈ cutoffOneCornerTags support) :
    cutoffOneTagMultiplicity tag
        ((cutoffOneEndpointFactorPorts orientationAt n support).map
          CutoffOneEndpointPort.tag) = 2 := by
  have hperm :=
    (cutoffOneEndpointFactorPorts_perm_globalDegreeTwoPorts
      orientationAt n support).map CutoffOneEndpointPort.tag
  exact (cutoffOneTagMultiplicity_perm tag hperm).trans
    (cutoffOneGlobalDegreeTwoPort_tagMultiplicity_eq_two
      orientationAt n support htag)

/-! ## 7. Both ends of every pair are genuine global factors -/

private theorem endpointPort_key_mem_factorKeys_of_mem
    {factors : List CutoffOneEndpointFactor}
    {port : CutoffOneEndpointPort}
    (hport : port ∈ factors.flatMap CutoffOneEndpointFactor.ports) :
    port.key ∈ factors.map CutoffOneEndpointFactor.key := by
  obtain ⟨factor, hfactor, hlocal⟩ := List.mem_flatMap.mp hport
  unfold CutoffOneEndpointFactor.ports at hlocal
  obtain ⟨tag, htag, hportEq⟩ := List.mem_map.mp hlocal
  rw [← hportEq]
  exact List.mem_map.mpr ⟨factor, hfactor, rfl⟩

private theorem degreeTwoPair_firstPort_mem_globalPorts
    {orientationAt : CutoffOneFaceOrientationChoice}
    {n : Nat} {support : List Nat}
    {pair : CutoffOneDegreeTwoPortPair}
    (hpair : pair ∈
      cutoffOneGlobalDegreeTwoPortPairs orientationAt n support) :
    pair.firstPort ∈
      cutoffOneGlobalDegreeTwoPorts orientationAt n support := by
  unfold cutoffOneGlobalDegreeTwoPorts
  exact List.mem_flatMap.mpr ⟨pair, hpair, by
    simp [CutoffOneDegreeTwoPortPair.ports,
      CutoffOneDegreeTwoPortPair.firstPort]⟩

private theorem degreeTwoPair_secondPort_mem_globalPorts
    {orientationAt : CutoffOneFaceOrientationChoice}
    {n : Nat} {support : List Nat}
    {pair : CutoffOneDegreeTwoPortPair}
    (hpair : pair ∈
      cutoffOneGlobalDegreeTwoPortPairs orientationAt n support) :
    pair.secondPort ∈
      cutoffOneGlobalDegreeTwoPorts orientationAt n support := by
  unfold cutoffOneGlobalDegreeTwoPorts
  exact List.mem_flatMap.mpr ⟨pair, hpair, by
    simp [CutoffOneDegreeTwoPortPair.ports,
      CutoffOneDegreeTwoPortPair.secondPort]⟩

theorem cutoffOneGlobalDegreeTwoPortPair_firstKey_mem_factors
    (orientationAt : CutoffOneFaceOrientationChoice)
    (n : Nat) (support : List Nat)
    {pair : CutoffOneDegreeTwoPortPair}
    (hpair : pair ∈
      cutoffOneGlobalDegreeTwoPortPairs orientationAt n support) :
    pair.firstKey ∈
      (cutoffOneEndpointFactors orientationAt n support).map
        CutoffOneEndpointFactor.key := by
  have hport : pair.firstPort ∈
      cutoffOneEndpointFactorPorts orientationAt n support :=
    (cutoffOneEndpointFactorPorts_perm_globalDegreeTwoPorts
      orientationAt n support).mem_iff.mpr
        (degreeTwoPair_firstPort_mem_globalPorts hpair)
  exact endpointPort_key_mem_factorKeys_of_mem hport

theorem cutoffOneGlobalDegreeTwoPortPair_secondKey_mem_factors
    (orientationAt : CutoffOneFaceOrientationChoice)
    (n : Nat) (support : List Nat)
    {pair : CutoffOneDegreeTwoPortPair}
    (hpair : pair ∈
      cutoffOneGlobalDegreeTwoPortPairs orientationAt n support) :
    pair.secondKey ∈
      (cutoffOneEndpointFactors orientationAt n support).map
        CutoffOneEndpointFactor.key := by
  have hport : pair.secondPort ∈
      cutoffOneEndpointFactorPorts orientationAt n support :=
    (cutoffOneEndpointFactorPorts_perm_globalDegreeTwoPorts
      orientationAt n support).mem_iff.mpr
        (degreeTwoPair_secondPort_mem_globalPorts hpair)
  exact endpointPort_key_mem_factorKeys_of_mem hport

#print axioms CutoffOneOrientedFaceRow.literalEndpointPorts_perm_degreeTwoPorts
#print axioms CutoffOneOrientedFaceRow.degreeTwoPortPair_keys_ne
#print axioms cutoffOneEndpointFactors_keys_nodup
#print axioms cutoffOneGlobalDegreeTwoPortPairTags_exact
#print axioms cutoffOneCornerTags_nodup
#print axioms cutoffOneGlobalDegreeTwoPortPair_keys_ne
#print axioms cutoffOneGlobalDegreeTwoPorts_nodup
#print axioms cutoffOneEndpointFactorPorts_perm_globalDegreeTwoPorts
#print axioms cutoffOneEndpointFactorPorts_nodup
#print axioms cutoffOneEndpointFactor_tags_nodup
#print axioms cutoffOneEndpointFactorTagWords_factorwise_nodup
#print axioms cutoffOneGlobalDegreeTwoPortTags_eq_doubledCornerTags
#print axioms cutoffOneEndpointFactorTagWords_flatten_perm_doubledCornerTags
#print axioms cutoffOneGlobalDegreeTwoPort_tagMultiplicity_eq_two
#print axioms cutoffOneEndpointFactorPort_tagMultiplicity_eq_two
#print axioms cutoffOneGlobalDegreeTwoPortPair_firstKey_mem_factors
#print axioms cutoffOneGlobalDegreeTwoPortPair_secondKey_mem_factors

end YMGap.Continuum.SU2QuaternionCutoffOneGlobalDegreeTwoPorts
