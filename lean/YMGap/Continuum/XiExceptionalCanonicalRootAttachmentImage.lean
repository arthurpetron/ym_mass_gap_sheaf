/-
# Exact mapped images in the canonical root-attachment carrier

The canonical carrier has exact pointwise source weight.  Mapping either the
routed-incompatible source or the full exceptional source into it therefore
gives an explicit finite carrier list with exactly the original q-list sum.
This is the source-shaped summation target used before replacing the mapped
list by a source-independent duplicate-free enumeration.
-/

import YMGap.Continuum.XiExceptionalCanonicalRootAttachmentCarrier

namespace YMGap.Continuum.XiExceptionalCanonicalRootAttachmentImage

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiExceptionalWeightedInjection
open YMGap.Continuum.XiExceptionalCarrierCode
open YMGap.Continuum.XiExceptionalBranchPacking
open YMGap.Continuum.XiExceptionalSourceWeight
open YMGap.Continuum.XiExceptionalFullSourceBound
open YMGap.Continuum.XiExceptionalRoutedExternalSplit
open YMGap.Continuum.XiExceptionalCanonicalRootAttachmentCarrier

variable {L : Lattice} [DecidableEq L.Plaquette]

local infix:50 " ≈ " => Q'.eqv

def routedIncompatibleRootAttachmentImage
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool) :
    List (RootAttachmentCarrierCode Gamma.length) :=
  (routedExternalIncompatibleSource Gamma qP b1 b2).map
    (entryRootAttachmentCarrierCode Gamma qP b1 b2)

def fullExceptionalRootAttachmentImage
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool) :
    List (RootAttachmentCarrierCode Gamma.length) :=
  (fullExceptionalSource Gamma qP b1 b2).map
    (entryRootAttachmentCarrierCode Gamma qP b1 b2)

theorem routedIncompatibleRootAttachmentImage_sum_eqv_source
    (w : Q') (Gamma : List (Polymer L))
    (qP b1 b2 : Polymer L → Bool) (label : L.Plaquette → Rep) :
    qListSum
        (rootAttachmentCarrierCodeWeight w Gamma qP b1 b2 label)
        (routedIncompatibleRootAttachmentImage Gamma qP b1 b2) ≈
      qListSum
        (fun entry => occurrencePairWeight w qP b1 b2 Gamma label entry.1)
        (routedExternalIncompatibleSource Gamma qP b1 b2) := by
  unfold routedIncompatibleRootAttachmentImage
  rw [qListSum_map]
  apply qListSum_eqv_congr
  intro entry _
  exact entryRootAttachmentCarrierCode_weight_eqv_source
    w Gamma qP b1 b2 label entry

theorem fullExceptionalRootAttachmentImage_sum_eqv_source
    (w : Q') (Gamma : List (Polymer L))
    (qP b1 b2 : Polymer L → Bool) (label : L.Plaquette → Rep) :
    qListSum
        (rootAttachmentCarrierCodeWeight w Gamma qP b1 b2 label)
        (fullExceptionalRootAttachmentImage Gamma qP b1 b2) ≈
      qListSum
        (fun entry => occurrencePairWeight w qP b1 b2 Gamma label entry.1)
        (fullExceptionalSource Gamma qP b1 b2) := by
  unfold fullExceptionalRootAttachmentImage
  rw [qListSum_map]
  apply qListSum_eqv_congr
  intro entry _
  exact entryRootAttachmentCarrierCode_weight_eqv_source
    w Gamma qP b1 b2 label entry

theorem routedIncompatibleSource_le_mappedRootAttachmentImage
    (w : Q') (Gamma : List (Polymer L))
    (qP b1 b2 : Polymer L → Bool) (label : L.Plaquette → Rep) :
    qListSum
        (fun entry => occurrencePairWeight w qP b1 b2 Gamma label entry.1)
        (routedExternalIncompatibleSource Gamma qP b1 b2) ≤
      qListSum
        (rootAttachmentCarrierCodeWeight w Gamma qP b1 b2 label)
        (routedIncompatibleRootAttachmentImage Gamma qP b1 b2) :=
  Q'.le_of_eqv (Q'.eqv_symm
    (routedIncompatibleRootAttachmentImage_sum_eqv_source
      w Gamma qP b1 b2 label))

#print axioms routedIncompatibleRootAttachmentImage_sum_eqv_source
#print axioms fullExceptionalRootAttachmentImage_sum_eqv_source
#print axioms routedIncompatibleSource_le_mappedRootAttachmentImage

end YMGap.Continuum.XiExceptionalCanonicalRootAttachmentImage
