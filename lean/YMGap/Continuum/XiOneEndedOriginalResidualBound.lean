/-
# One-ended influence bound from the injective original residual carrier

The original-right-residual carrier is injective once the original left
residual is empty.  Thus the full exceptional source, the restriction
product, and the public one-ended influence bound need no separate residual
mask injectivity premise.
-/

import YMGap.Continuum.XiExceptionalOriginalResidualInjection
import YMGap.Continuum.XiNonexceptionalSummation

namespace YMGap.Continuum.XiOneEndedOriginalResidualBound

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiAvoidanceChainBound
open YMGap.Continuum.XiOneEndedInfluence
open YMGap.Continuum.XiExceptionalWeightedInjection
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalSourceWeight
open YMGap.Continuum.XiExceptionalBranchPacking
open YMGap.Continuum.XiExceptionalPathSafeSummation
open YMGap.Continuum.XiExceptionalFullSourceBound
open YMGap.Continuum.XiExceptionalSourcePartition
open YMGap.Continuum.XiExceptionalTargetBlocks
open YMGap.Continuum.XiExceptionalParallelExternalFamily
open YMGap.Continuum.XiExceptionalParallelResidualBlock
open YMGap.Continuum.XiExceptionalOneAttachedResidualConsumer
open YMGap.Continuum.XiExceptionalOriginalResidualInjection
open YMGap.Continuum.XiNonexceptionalSummation

variable {L : Lattice} [DecidableEq L.Plaquette]

private theorem flatMap_singleton_eq_map {alpha beta : Type}
    (f : alpha → beta) : ∀ xs : List alpha,
    xs.flatMap (fun x => [f x]) = xs.map f
  | [] => rfl
  | x :: xs => by
      simp only [List.flatMap_cons, List.map_cons, List.singleton_append]
      rw [flatMap_singleton_eq_map f xs]

/-- Any duplicate-free source region with empty original left residual embeds
through the injective original-right-residual code. -/
theorem originalRightResidual_region_global_bound
    {w : Q'} (hw : (0 : Q') ≤ w)
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (label : L.Plaquette → Rep)
    (source : List (ExceptionalSourceEntry Gamma qP b1 b2))
    (hsource : source.Nodup)
    (hleftEmpty : ∀ entry, entry ∈ source →
      selectByBits Gamma (leftPathResidual Gamma qP b1 b2 entry) = []) :
    qListSum (fun entry => occurrencePairWeight w qP b1 b2 Gamma label
        entry.1) source ≤
      qListSum (occurrenceCarrierXiCodeWeight w qP b1 b2 Gamma label)
        (occurrenceCarrierXiCodes Gamma) := by
  apply qListSum_le_of_disjoint_blocks source
    (occurrenceCarrierXiCodes Gamma)
    (fun entry => occurrencePairWeight w qP b1 b2 Gamma label entry.1)
    (occurrenceCarrierXiCodeWeight w qP b1 b2 Gamma label)
    (fun entry => [originalRightResidualCarrierCode Gamma qP b1 b2 entry])
  · rw [flatMap_singleton_eq_map]
    apply nodup_map_of_injOn _ source hsource
    intro a ha b hb hcode
    exact originalRightResidualCarrierCode_injective Gamma qP b1 b2 a b
      (hleftEmpty a ha) (hleftEmpty b hb) hcode
  · intro code hcode
    obtain ⟨entry, _, hsingleton⟩ := List.mem_flatMap.mp hcode
    rw [List.mem_singleton] at hsingleton
    subst code
    exact parallelExternalCarrierCode_mem Gamma qP b1 b2 entry
      (rightPathResidual Gamma qP b1 b2 entry)
  · intro entry hentry
    simp only [qListSum_cons, qListSum_nil, Q'.add_zero']
    change occurrencePairWeight w qP b1 b2 Gamma label entry.1 ≤
      occurrenceCarrierXiCodeWeight w qP b1 b2 Gamma label
        (parallelExternalCarrierCode Gamma qP b1 b2 entry
          (rightPathResidual Gamma qP b1 b2 entry))
    exact Q'.le_of_eqv (Q'.eqv_symm
      (rightOnlyResidualCode_weight_eqv_source w qP b1 b2 Gamma label
        entry (hleftEmpty entry hentry)))
  · intro code _
    exact occurrenceCarrierXiCodeWeight_nonnegative hw
      qP b1 b2 Gamma label code

/-- Full exceptional source closure with only the left-residual exhaustion
premise. -/
theorem full_exceptional_source_le_chain_mul_XiR_of_emptyLeftResidual
    {w : Q'} (hw : (0 : Q') ≤ w)
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (label : L.Plaquette → Rep)
    (hleftEmpty : ∀ entry,
      entry ∈ fullExceptionalSource Gamma qP b1 b2 →
      selectByBits Gamma (leftPathResidual Gamma qP b1 b2 entry) = []) :
    qListSum (occurrencePairWeight w qP b1 b2 Gamma label)
        (exceptionalSourceCodes Gamma qP b1 b2) ≤
      connectingChainMajorant w qP b1 b2 Gamma label *
        XiR w qP Gamma label := by
  have hglobal := originalRightResidual_region_global_bound hw Gamma
    qP b1 b2 label (fullExceptionalSource Gamma qP b1 b2)
    (fullExceptionalSource_nodup Gamma qP b1 b2) hleftEmpty
  change qListSum (pathSafeSourceWeight w qP b1 b2 Gamma label)
      (fullExceptionalSource Gamma qP b1 b2) ≤ _ at hglobal
  rw [fullExceptionalSource_weight_eq] at hglobal
  exact Q'.le_trans' _ _ _ hglobal
    (Q'.le_of_eqv
      (occurrenceCarrierXiCodes_sum_eqv_carrier_mul_XiR
        w qP b1 b2 Gamma label))

theorem restriction_product_le_opposite_add_carrier_of_emptyLeftResidual
    {w : Q'} (hw : (0 : Q') ≤ w)
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (label : L.Plaquette → Rep)
    (hleftEmpty : ∀ entry,
      entry ∈ fullExceptionalSource Gamma qP b1 b2 →
      selectByBits Gamma (leftPathResidual Gamma qP b1 b2 entry) = []) :
    XiR w (fun X => qP X && !(b1 X)) Gamma label *
        XiR w (fun X => qP X && !(b2 X)) Gamma label ≤
      XiR w (fun X => qP X && !((fun X => b1 X || b2 X) X))
          Gamma label *
        XiR w (fun X => qP X && !((fun _ : Polymer L => false) X))
          Gamma label +
      connectingChainMajorant w qP b1 b2 Gamma label *
        XiR w qP Gamma label := by
  let exceptional := qListSum
    (occurrencePairWeight w qP b1 b2 Gamma label)
    (exceptionalSourceCodes Gamma qP b1 b2)
  let nonexceptional := qListSum
    (occurrencePairWeight w qP b1 b2 Gamma label)
    (nonexceptionalSourceCodes Gamma qP b1 b2)
  let opposite :=
    XiR w (fun X => qP X && !((fun X => b1 X || b2 X) X))
        Gamma label *
      XiR w (fun X => qP X && !((fun _ : Polymer L => false) X))
        Gamma label
  let carrier := connectingChainMajorant w qP b1 b2 Gamma label *
    XiR w qP Gamma label
  have hpartition :=
    restriction_product_eqv_exceptional_add_nonexceptional
      w qP b1 b2 Gamma label
  have hexceptional : exceptional ≤ carrier := by
    exact full_exceptional_source_le_chain_mul_XiR_of_emptyLeftResidual
      hw Gamma qP b1 b2 label hleftEmpty
  have hnonexceptional : nonexceptional ≤ opposite := by
    exact nonexceptional_source_le_opposite_product hw Gamma qP b1 b2 label
  have hsum : exceptional + nonexceptional ≤ carrier + opposite :=
    Q'.add_le_add hexceptional hnonexceptional
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hpartition) ?_
  exact Q'.le_trans' _ _ _ hsum
    (Q'.le_of_eqv (Q'.add_comm_eqv carrier opposite))

private theorem source_second_predicate_eq
    (qP : Polymer L → Bool) (head : Polymer L) :
    (fun X => qP X && !(!(compatibleB head X))) =
      (fun X => qP X && compatibleB head X) := by
  funext X
  cases qP X <;> cases compatibleB head X <;> rfl

private theorem opposite_first_predicate_eq
    (qP b : Polymer L → Bool) (head : Polymer L) :
    (fun X => qP X && !(b X || !(compatibleB head X))) =
      (fun X => qP X && (!(b X) && compatibleB head X)) := by
  funext X
  cases qP X <;> cases b X <;> cases compatibleB head X <;> rfl

private theorem opposite_second_predicate_eq
    (qP : Polymer L → Bool) :
    (fun X => qP X && !false) = (fun X => qP X && true) := by
  funext X
  cases qP X <;> rfl

/-- Public one-ended inequality with the injective original residual carrier;
only exhaustion of the original left residual remains. -/
theorem oneEndedLeft_le_right_add_influence_of_emptyLeftResidual
    {w : Q'} (hw : (0 : Q') ≤ w)
    (qP b : Polymer L → Bool) (head : Polymer L)
    (Gamma : List (Polymer L)) (label : L.Plaquette → Rep)
    (hleftEmpty : ∀ entry,
      entry ∈ fullExceptionalSource Gamma qP b
        (fun X => !(compatibleB head X)) →
      selectByBits Gamma
        (leftPathResidual Gamma qP b
          (fun X => !(compatibleB head X)) entry) = []) :
    oneEndedLeft w qP b head Gamma label ≤
      oneEndedRight w qP b head Gamma label +
        oneEndedInfluenceCarrier w qP b head Gamma label *
          XiR w qP Gamma label := by
  have hbound :=
    restriction_product_le_opposite_add_carrier_of_emptyLeftResidual
      hw Gamma qP b (fun X => !(compatibleB head X)) label hleftEmpty
  unfold oneEndedLeft oneEndedRight restrictionPair
    oneEndedInfluenceCarrier
  rw [← source_second_predicate_eq qP head]
  rw [← opposite_first_predicate_eq qP b head]
  rw [← opposite_second_predicate_eq qP]
  exact hbound

#print axioms originalRightResidual_region_global_bound
#print axioms full_exceptional_source_le_chain_mul_XiR_of_emptyLeftResidual
#print axioms restriction_product_le_opposite_add_carrier_of_emptyLeftResidual
#print axioms oneEndedLeft_le_right_add_influence_of_emptyLeftResidual

end YMGap.Continuum.XiOneEndedOriginalResidualBound
