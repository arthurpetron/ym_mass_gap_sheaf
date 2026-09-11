/-
# Endpoint ports of the cutoff-one plaquette network

This geometry leaf records where the semantic target/source coordinate of an
oriented fundamental occurrence lives on its canonical physical link.  For a
positive descriptor the base/end tags are its stored row/column tags.  For a
negative descriptor they are its stored column/row tags.  Consequently the
semantic target is always the base-endpoint tag and the semantic source is
always the far-endpoint tag, independently of the plaquette orientation.

For either orientation of one face with fresh corner tags `[a,b,c,d]`, the
four target ports are `[a,b,d,a]` and the four source ports are `[b,c,c,d]`.
This formally exposes the target-target cap at `a` and source-source cup at
`c`; neither half is a permutation of the corner packet.  The combined eight
ports still contain exactly the two incidences of every trace corner.  This is
the local geometry consumed by a subsequent vertex-network/Finner bound.

# Axiom gate

No `Classical`, choice, `sorry`/`admit`, `native_decide`, or custom axiom.
-/

import YMGap.Continuum.SU2QuaternionCutoffOneLinkBucketWords
import YMGap.Continuum.SU2QuaternionOccurrenceBoolTensorTransport

namespace YMGap.Continuum.SU2QuaternionCutoffOneEndpointChannelPorts

open YMGap.Continuum.SU2QuaternionFundamentalSelfDuality
open YMGap.Continuum.SU2QuaternionCutoffOneOrientedFaceRows
open YMGap.Continuum.SU2QuaternionCutoffOneLinkBucketWords

/-! ## 1. Canonical physical-link endpoint tags -/

/-- Tag carried at the canonical base endpoint of a physical link. -/
def CutoffOneLinkOccurrenceDescriptor.baseTag
    (descriptor : CutoffOneLinkOccurrenceDescriptor) : Nat :=
  if descriptor.positive then descriptor.rowTag else descriptor.columnTag

/-- Tag carried at the far endpoint of the same canonical physical link. -/
def CutoffOneLinkOccurrenceDescriptor.endTag
    (descriptor : CutoffOneLinkOccurrenceDescriptor) : Nat :=
  if descriptor.positive then descriptor.columnTag else descriptor.rowTag

/-- The semantic operator target coordinate is always read at the canonical
base endpoint of the physical link. -/
theorem cutoffOneDescriptorOccurrence_operatorTarget
    (environment : Nat → Bool)
    (descriptor : CutoffOneLinkOccurrenceDescriptor) :
    (cutoffOneDescriptorOccurrence environment descriptor).operatorTarget =
      environment
        (CutoffOneLinkOccurrenceDescriptor.baseTag descriptor) := by
  rcases descriptor with ⟨physicalLink, positive, rowTag, columnTag⟩
  cases positive <;> rfl

/-- The semantic operator source coordinate is always read at the canonical
far endpoint of the physical link. -/
theorem cutoffOneDescriptorOccurrence_operatorSource
    (environment : Nat → Bool)
    (descriptor : CutoffOneLinkOccurrenceDescriptor) :
    (cutoffOneDescriptorOccurrence environment descriptor).operatorSource =
      environment
        (CutoffOneLinkOccurrenceDescriptor.endTag descriptor) := by
  rcases descriptor with ⟨physicalLink, positive, rowTag, columnTag⟩
  cases positive <;> rfl

/-! ## 2. Exact one-face endpoint port words -/

/-- Base-endpoint/operator-target ports in literal coefficient order. -/
def CutoffOneOrientedFaceRow.targetTags
    (row : CutoffOneOrientedFaceRow) : List Nat :=
  row.coefficientDescriptors.map
    CutoffOneLinkOccurrenceDescriptor.baseTag

/-- Far-endpoint/operator-source ports in literal coefficient order. -/
def CutoffOneOrientedFaceRow.sourceTags
    (row : CutoffOneOrientedFaceRow) : List Nat :=
  row.coefficientDescriptors.map
    CutoffOneLinkOccurrenceDescriptor.endTag

/-- Both standard and reversed face words induce the same cap-bearing target
tag pattern. -/
theorem CutoffOneOrientedFaceRow.targetTags_exact
    (row : CutoffOneOrientedFaceRow) :
    CutoffOneOrientedFaceRow.targetTags row =
      [row.firstTag, row.secondTag, row.fourthTag, row.firstTag] := by
  obtain ⟨supportPosition, physicalFaceId, plaquette, orientation⟩ := row
  cases orientation <;> rfl

/-- Both face orientations induce the same cup-bearing source tag pattern. -/
theorem CutoffOneOrientedFaceRow.sourceTags_exact
    (row : CutoffOneOrientedFaceRow) :
    CutoffOneOrientedFaceRow.sourceTags row =
      [row.secondTag, row.thirdTag, row.thirdTag, row.fourthTag] := by
  obtain ⟨supportPosition, physicalFaceId, plaquette, orientation⟩ := row
  cases orientation <;> rfl

/-- The target word is genuinely not duplicate-free: the first corner closes
as a target-target cap. -/
theorem CutoffOneOrientedFaceRow.not_nodup_targetTags
    (row : CutoffOneOrientedFaceRow) :
    ¬ (CutoffOneOrientedFaceRow.targetTags row).Nodup := by
  rw [CutoffOneOrientedFaceRow.targetTags_exact row]
  intro h
  exact (List.nodup_cons.mp h).1 (by simp)

/-- The source word is likewise not duplicate-free: the third corner closes
as a source-source cup. -/
theorem CutoffOneOrientedFaceRow.not_nodup_sourceTags
    (row : CutoffOneOrientedFaceRow) :
    ¬ (CutoffOneOrientedFaceRow.sourceTags row).Nodup := by
  rw [CutoffOneOrientedFaceRow.sourceTags_exact row]
  intro h
  have htail := (List.nodup_cons.mp h).2
  exact (List.nodup_cons.mp htail).1 (by simp)

/-- Before regrouping, the combined endpoint word displays both occurrences
of every one of the four fresh trace tags. -/
theorem CutoffOneOrientedFaceRow.targetTags_append_sourceTags_exact
    (row : CutoffOneOrientedFaceRow) :
    CutoffOneOrientedFaceRow.targetTags row ++
        CutoffOneOrientedFaceRow.sourceTags row =
      [row.firstTag, row.secondTag, row.fourthTag, row.firstTag,
       row.secondTag, row.thirdTag, row.thirdTag, row.fourthTag] := by
  rw [CutoffOneOrientedFaceRow.targetTags_exact row,
    CutoffOneOrientedFaceRow.sourceTags_exact row]
  rfl

#print axioms cutoffOneDescriptorOccurrence_operatorTarget
#print axioms cutoffOneDescriptorOccurrence_operatorSource
#print axioms CutoffOneOrientedFaceRow.targetTags_exact
#print axioms CutoffOneOrientedFaceRow.sourceTags_exact
#print axioms CutoffOneOrientedFaceRow.not_nodup_targetTags
#print axioms CutoffOneOrientedFaceRow.not_nodup_sourceTags
#print axioms CutoffOneOrientedFaceRow.targetTags_append_sourceTags_exact

end YMGap.Continuum.SU2QuaternionCutoffOneEndpointChannelPorts
