/-
# Exact fibre fence for strict canonicalization

Construction-order validity removes parent-later histories, but it does not
recover the old distinction between a trunk `prepend` edge and a later
`attach` edge.  The two certified trees below have the same strict canonical
code and different old cores.  Consequently no decoder from the strict
canonical code alone can recover the `OccTreeCode.core` datum used by the
existing exceptional-source fibre proof.
-/

import YMGap.Continuum.XiExceptionalCanonicalStrictCarrier

namespace YMGap.Continuum.XiExceptionalCanonicalStrictFiberFence

open YMGap.Continuum.PolymerModel
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalDistinctInjection
open YMGap.Continuum.XiExceptionalRecoveredBackground
open YMGap.Continuum.XiExceptionalOccurrenceTreeCarrier
open YMGap.Continuum.XiExceptionalOccurrenceTreeCodes
open YMGap.Continuum.XiExceptionalSourceTreeFiber
open YMGap.Continuum.XiExceptionalCanonicalRootAttachmentCarrier
open YMGap.Continuum.XiExceptionalCanonicalStrictCarrier

private abbrev TL := toyLattice

private instance instDecidableEqTLPlaquette : DecidableEq TL.Plaquette :=
  show DecidableEq (Nat × Nat) from inferInstance

private def p : TL.Plaquette := (0, 0)
private def q : TL.Plaquette := (1, 0)
private def X : Polymer TL := [p]
private def Y : Polymer TL := [p, q]
private def Gamma : List (Polymer TL) := [X, Y]

private def trunkTree : OTree (incAtDistinct Gamma) 0 :=
  .prepend (root := 0) (next := 1) (by decide) (.single 1)

private def attachedTree : OTree (incAtDistinct Gamma) 0 :=
  .attach (.single 0) 0 1 (by decide)

private def trunkOldCode : OccTreeCode Gamma.length :=
  OTree.toCode (N := Gamma.length) trunkTree

private def attachedOldCode : OccTreeCode Gamma.length :=
  OTree.toCode (N := Gamma.length) attachedTree

private def trunkCanonical : RootAttachmentTreeCode Gamma.length :=
  oTreeToRootAttachmentCode (N := Gamma.length) trunkTree

private def attachedCanonical : RootAttachmentTreeCode Gamma.length :=
  oTreeToRootAttachmentCode (N := Gamma.length) attachedTree

theorem trunk_and_attach_canonical_equal :
    trunkCanonical = attachedCanonical := by
  decide

theorem trunk_and_attach_old_codes_distinct :
    trunkOldCode ≠ attachedOldCode := by
  decide

theorem trunk_and_attach_cores_distinct :
    OccTreeCode.core trunkOldCode ≠
      OccTreeCode.core attachedOldCode := by
  decide

theorem trunk_strict_build_valid :
    strictAttachmentBuildValidB Gamma [trunkCanonical.root]
      trunkCanonical.attachments = true := by
  decide

theorem attached_strict_build_valid :
    strictAttachmentBuildValidB Gamma [attachedCanonical.root]
      attachedCanonical.attachments = true := by
  decide

theorem trunk_tree_valid : trunkTree.Valid := by
  trivial

theorem attached_tree_valid : attachedTree.Valid := by
  exact ⟨trivial, List.mem_cons_self⟩

theorem trunk_vertices_nodup : trunkTree.vertices.Nodup := by
  decide

theorem attached_vertices_nodup : attachedTree.vertices.Nodup := by
  decide

theorem no_strict_canonical_old_code_decoder :
    ¬ ∃ decode : RootAttachmentTreeCode Gamma.length →
        OccTreeCode Gamma.length,
      decode trunkCanonical = trunkOldCode ∧
        decode attachedCanonical = attachedOldCode := by
  rintro ⟨decode, htrunk, hattach⟩
  apply trunk_and_attach_old_codes_distinct
  rw [← htrunk, ← hattach, trunk_and_attach_canonical_equal]

theorem no_strict_canonical_core_decoder :
    ¬ ∃ decode : RootAttachmentTreeCode Gamma.length →
        OccTreeCode Gamma.length,
      OccTreeCode.core (decode trunkCanonical) =
          OccTreeCode.core trunkOldCode ∧
        OccTreeCode.core (decode attachedCanonical) =
          OccTreeCode.core attachedOldCode := by
  rintro ⟨decode, htrunk, hattach⟩
  apply trunk_and_attach_cores_distinct
  rw [← htrunk, ← hattach, trunk_and_attach_canonical_equal]

#print axioms trunk_and_attach_canonical_equal
#print axioms trunk_and_attach_old_codes_distinct
#print axioms trunk_and_attach_cores_distinct
#print axioms trunk_strict_build_valid
#print axioms attached_strict_build_valid
#print axioms no_strict_canonical_old_code_decoder
#print axioms no_strict_canonical_core_decoder

end YMGap.Continuum.XiExceptionalCanonicalStrictFiberFence
