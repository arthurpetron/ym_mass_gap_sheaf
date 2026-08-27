/-
# The physical SU(2) Schur matrix on canonical finite carriers

The pointwise column theorem is initially indexed by the reversed problem's
right-channel enumeration.  Here we identify that explicit reversed carrier
with the canonical complete list of left channels and package the resulting
matrix with both normalization laws.

This is a finite representation-theoretic recoupling matrix.  It is not a
Gibbs conditional kernel and not an Osterwalder--Schrader transfer operator.

Constructive contract: finite exact `Q'` algebra and explicit list maps only;
no choice, `Classical`, `sorry`, or new axiom.
-/

import YMGap.Continuum.FiniteBistochasticQKernel
import YMGap.Continuum.SU2DirectLeftFixedOutputEnumeration
import YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
import YMGap.Continuum.SU2PhysicalSchurColumnNormalization
import YMGap.Continuum.SU2PhysicalSchurTwoReplicaTransport

namespace YMGap.Continuum.SU2PhysicalSchurBistochasticKernel

open YMGap.Constructive
open YMGap.Continuum.FiniteBistochasticQKernel
open YMGap.Continuum.SU2DirectLeftFixedOutputEnumeration
open YMGap.Continuum.SU2DirectRightFixedOutputSections
open YMGap.Continuum.SU2DirectRightFixedOutputEnumeration
open YMGap.Continuum.SU2FixedLeftTransvectantEvaluation
open YMGap.Continuum.SU2FixedLeftRightAssociatorSchur
open YMGap.Continuum.SU2OrderedRacahInteriorSchurBridge
open YMGap.Continuum.SU2PhysicalSchurRecouplingKernel
open YMGap.Continuum.SU2PhysicalSchurColumnNormalization
open YMGap.Continuum.SU2PhysicalSchurTwoReplicaTransport
open YMGap.Continuum.SU2SchurReversalSymmetry
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.FiniteWeightedCartesianInjection

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The reversed canonical source carrier -/

/-- Reverse the canonical right-channel list for `(c,b,a,d)` into a complete
list of left channels for `(a,b,c,d)`. -/
def reversedPhysicalSchurLeftSources (a b c d : Nat) :
    List (FixedLeftCGChannel a b c d) :=
  (fixedRightChannels c b a d).map reverseRightAsLeft

private theorem nodup_map_of_injective {A B : Type} (f : A → B)
    (hf : ∀ x y, f x = f y → x = y) :
    ∀ {items : List A}, items.Nodup → (items.map f).Nodup
  | [], _ => List.nodup_nil
  | head :: tail, hitems => by
      have hparts := List.nodup_cons.mp hitems
      refine List.nodup_cons.mpr ⟨?_, nodup_map_of_injective f hf hparts.2⟩
      intro hmem
      obtain ⟨item, hitem, heq⟩ := List.mem_map.mp hmem
      exact hparts.1 (by
        have : head = item := hf head item heq.symm
        simpa only [this] using hitem)

theorem reversedPhysicalSchurLeftSources_nodup (a b c d : Nat) :
    (reversedPhysicalSchurLeftSources a b c d).Nodup := by
  unfold reversedPhysicalSchurLeftSources
  apply nodup_map_of_injective reverseRightAsLeft
  · intro left right heq
    have h := congrArg reverseLeftAsRight heq
    simpa only [reverseLeftAsRight_reverseRightAsLeft] using h
  · exact fixedRightChannels_nodup c b a d

theorem mem_reversedPhysicalSchurLeftSources_iff {a b c d : Nat}
    (qL : FixedLeftCGChannel a b c d) :
    qL ∈ reversedPhysicalSchurLeftSources a b c d ↔
      qL ∈ fixedLeftChannels a b c d := by
  constructor
  · intro _
    exact fixedLeftChannels_complete qL
  · intro _
    apply List.mem_map.mpr
    refine ⟨reverseLeftAsRight qL,
      fixedRightChannels_complete (reverseLeftAsRight qL), ?_⟩
    exact reverseRightAsLeft_reverseLeftAsRight qL

/-! ## 2. Exact transport from the indexed column to the canonical list -/

private instance fixedLeftChannelDecidableEq (a b c d : Nat) :
    DecidableEq (FixedLeftCGChannel a b c d) := fun left right =>
  match decEq left.k right.k with
  | isTrue heq => isTrue (fixedLeftChannel_eq_of_k_eq left right heq)
  | isFalse hne => isFalse (fun h => hne (congrArg FixedLeftCGChannel.k h))

private theorem listQSum_eqv_of_nodup_same_members_nonnegative
    {State : Type} [DecidableEq State]
    (value : State → Q') (left right : List State)
    (hleft : left.Nodup) (hright : right.Nodup)
    (hmembers : ∀ state, state ∈ left ↔ state ∈ right)
    (hnonnegative : ∀ state, (0 : Q') ≤ value state) :
    listQSum value left ≈ listQSum value right := by
  have hleftRight : listQSum value left ≤ listQSum value right :=
    listQSum_le_of_injective left right value value (fun state => state)
      hleft
      (fun state hstate => (hmembers state).mp hstate)
      (fun _ _ _ _ heq => heq)
      (fun _ _ => Q'.le_refl' _)
      (fun state _ => hnonnegative state)
  have hrightLeft : listQSum value right ≤ listQSum value left :=
    listQSum_le_of_injective right left value value (fun state => state)
      hright
      (fun state hstate => (hmembers state).mpr hstate)
      (fun _ _ _ _ heq => heq)
      (fun _ _ => Q'.le_refl' _)
      (fun state _ => hnonnegative state)
  exact Int.le_antisymm hleftRight hrightLeft

theorem physicalSchurRecoupling_reversed_list_column_normalized
    {a b c d : Nat} (qR : FixedRightCGChannel a b c d) :
    listQSum (fun qL => physicalSchurRecouplingKernelAt qL qR)
      (reversedPhysicalSchurLeftSources a b c d) ≈ 1 := by
  let qLr := reverseRightAsLeft qR
  let value := fun qRr : FixedRightCGChannel c b a d =>
    physicalSchurRecouplingKernelAt (reverseRightAsLeft qRr) qR
  have hbridge := finiteHeadSum_fixedRightChannelAt_eq_listQSum
    (fixedRightFallbackOfFixedLeft qLr) value
    (fixedRightChannels c b a d)
  have hmass : physicalSchurRecouplingColumnMass qR ≈
      listQSum (fun qL => physicalSchurRecouplingKernelAt qL qR)
        (reversedPhysicalSchurLeftSources a b c d) := by
    refine Q'.eqv_trans _ (listQSum value (fixedRightChannels c b a d)) _ ?_ ?_
    · simpa only [physicalSchurRecouplingColumnMass,
        enumeratedRightChannel, qLr, value] using hbridge
    · exact Q'.eqv_symm (Q'.eqv_of_eq (by
        unfold reversedPhysicalSchurLeftSources
        rw [listQSum_map]))
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hmass)
    (physicalSchurRecouplingKernel_column_normalized qR)

/-- **Every canonical physical Schur column has exact mass one.** -/
theorem physicalSchurRecoupling_list_column_normalized
    {a b c d : Nat} (qR : FixedRightCGChannel a b c d) :
    listQSum (fun qL => physicalSchurRecouplingKernelAt qL qR)
      (fixedLeftChannels a b c d) ≈ 1 := by
  refine Q'.eqv_trans _
    (listQSum (fun qL => physicalSchurRecouplingKernelAt qL qR)
      (reversedPhysicalSchurLeftSources a b c d)) _ ?_ ?_
  · exact Q'.eqv_symm
      (listQSum_eqv_of_nodup_same_members_nonnegative
        (fun qL => physicalSchurRecouplingKernelAt qL qR)
        (reversedPhysicalSchurLeftSources a b c d)
        (fixedLeftChannels a b c d)
        (reversedPhysicalSchurLeftSources_nodup a b c d)
        (fixedLeftChannels_nodup a b c d)
        (fun qL => mem_reversedPhysicalSchurLeftSources_iff qL)
        (fun qL => physicalSchurRecouplingKernelAt_nonnegative qL qR))
  · exact physicalSchurRecoupling_reversed_list_column_normalized qR

/-! ## 3. The canonical finite bistochastic object -/

/-- The complete physical SU(2) associator matrix at four fixed external
labels, with canonical proof-carrying source and target carriers. -/
def physicalSchurBistochasticKernel (a b c d : Nat) :
    FiniteBistochasticQKernel
      (FixedLeftCGChannel a b c d) (FixedRightCGChannel a b c d) where
  sources := fixedLeftChannels a b c d
  targets := fixedRightChannels a b c d
  weight := physicalSchurRecouplingKernelAt
  weight_nonnegative := physicalSchurRecouplingKernelAt_nonnegative
  row_normalized := by
    intro qL
    simpa only [physicalSchurRightTargets] using
      physicalSchurRecoupling_list_row_normalized qL
  column_normalized := physicalSchurRecoupling_list_column_normalized

end YMGap.Continuum.SU2PhysicalSchurBistochasticKernel

#print axioms YMGap.Continuum.SU2PhysicalSchurBistochasticKernel.reversedPhysicalSchurLeftSources_nodup
#print axioms YMGap.Continuum.SU2PhysicalSchurBistochasticKernel.mem_reversedPhysicalSchurLeftSources_iff
#print axioms YMGap.Continuum.SU2PhysicalSchurBistochasticKernel.physicalSchurRecoupling_reversed_list_column_normalized
#print axioms YMGap.Continuum.SU2PhysicalSchurBistochasticKernel.physicalSchurRecoupling_list_column_normalized
#print axioms YMGap.Continuum.SU2PhysicalSchurBistochasticKernel.physicalSchurBistochasticKernel
