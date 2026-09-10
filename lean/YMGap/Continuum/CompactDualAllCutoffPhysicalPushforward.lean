/-
# The all-cutoff physical pushforward split by coherence

The arbitrary-cutoff total slab kernel is exact recoupling on positive Gibbs
rows whose raw recoupling partition is positive, and an explicit stochastic
fallback elsewhere.  This module pushes the normalized fine Gibbs law through
that kernel and separates those two contributions exactly.

The fallback is not counted by a carrier cardinality.  Its complete target
mass is exactly `positiveIncoherentRecouplingMass`, the normalized fine Gibbs
probability of positive rows with no positive raw recoupling partition.  Thus
the remaining higher-cutoff obligation is probability weighted.

No estimate on that mass, no comparison with the coarse Gibbs law, no
posterior variance, spectral gap, continuum limit, or Clay theorem is claimed.

## Axiom gate

Finite dependent recursion, finite Fubini, and exact rational algebra only.
No classical choice, placeholder, trusted external computation,
computability escape, heartbeat increase, or new axiom.
-/

import YMGap.Continuum.CompactDualAllCutoffTotalKernel
import YMGap.Continuum.CompactDualCutoffOnePhysicalPushforward

namespace YMGap.Continuum.CompactDualAllCutoffPhysicalPushforward

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualAllCutoffTotalKernel
open YMGap.Continuum.CompactDualCutoffOnePhysicalPushforward
open YMGap.Continuum.CompactDualCutoffOneTotalKernel
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.CompactDualWholeSlabRecouplingRawKernel
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The two probability-weighted pushed contributions -/

/-- Exact recoupling contribution from the coherent positive rows.  The
membership argument supplies the witness required by the conditional row
without choice. -/
def coherentRecouplingBlockedMassAux
    (S : SlabScalePair) (target : EdgeLabelling) :
    (sources : List EdgeLabelling) →
      (∀ source, source ∈ sources →
        source ∈ S.fine.physicalLabellings) → Q'
  | [], _ => 0
  | source :: tail, hphysical =>
      if _hpositive : (0 : Q') < S.fine.physicalTerm source then
        if hpartition : (0 : Q') <
            wholeSlabRawRowPartition S source then
          S.fine.normalizedMass source *
              wholeSlabRecouplingConditionalKernel
                (coherentSlabRecouplingSourceOfRawPartitionPos
                  S source
                  (hphysical source List.mem_cons_self)
                  hpartition)
                target +
            coherentRecouplingBlockedMassAux S target tail
              (fun item hitem =>
                hphysical item (List.mem_cons_of_mem source hitem))
        else
          coherentRecouplingBlockedMassAux S target tail
            (fun item hitem =>
              hphysical item (List.mem_cons_of_mem source hitem))
      else
        coherentRecouplingBlockedMassAux S target tail
          (fun item hitem =>
            hphysical item (List.mem_cons_of_mem source hitem))

def coherentRecouplingBlockedMass
    (S : SlabScalePair) (target : EdgeLabelling) : Q' :=
  coherentRecouplingBlockedMassAux S target
    S.fine.physicalLabellings (fun _ hsource => hsource)

/-- Target column of the pushed fallback law.  Its source coefficient is the
literal normalized Gibbs mass of the positive incoherent row. -/
def positiveIncoherentFallbackBlockedMass
    (S : SlabScalePair) (target : EdgeLabelling) : Q' :=
  listQSum
    (fun source =>
      positiveIncoherentRecouplingRowWeight S source *
        nullCompletionKernel S source target)
    S.fine.physicalLabellings

def allCutoffPhysicalKernel
    (S : SlabScalePair) (hfineCutoff : 1 <= S.fine.cutoff) :
    S.FiniteSlabKernel :=
  allCutoffWholeSlabFiniteKernel S hfineCutoff

/-! ## 2. Exact row-by-row and pushed-law splitting -/

private theorem kernelSum_eq_coherent_add_incoherent
    (S : SlabScalePair) (target : EdgeLabelling) :
    ∀ (sources : List EdgeLabelling)
      (hphysical : ∀ source, source ∈ sources →
        source ∈ S.fine.physicalLabellings),
      listQSum
          (fun source =>
            S.fine.normalizedMass source *
              allCutoffWholeSlabKernel S source target)
          sources ≈
        coherentRecouplingBlockedMassAux S target sources hphysical +
          listQSum
            (fun source =>
              positiveIncoherentRecouplingRowWeight S source *
                nullCompletionKernel S source target)
            sources
  | [], _ => Q'.eqv_symm (Q'.eqv_of_eq (Q'.zero_add' 0))
  | source :: tail, hphysical => by
      let hsource := hphysical source List.mem_cons_self
      let htail : ∀ item, item ∈ tail →
          item ∈ S.fine.physicalLabellings :=
        fun item hitem =>
          hphysical item (List.mem_cons_of_mem source hitem)
      by_cases hpositive :
          (0 : Q') < S.fine.physicalTerm source
      · by_cases hpartition :
            (0 : Q') < wholeSlabRawRowPartition S source
        · simp only [listQSum, coherentRecouplingBlockedMassAux,
            dif_pos hpositive, dif_pos hpartition,
            positiveIncoherentRecouplingRowWeight,
            if_pos hpositive, if_pos hpartition]
          refine Q'.eqv_trans _
            (S.fine.normalizedMass source *
                wholeSlabRecouplingConditionalKernel
                  (coherentSlabRecouplingSourceOfRawPartitionPos
                    S source hsource hpartition) target +
              (coherentRecouplingBlockedMassAux S target tail htail +
                listQSum
                  (fun item =>
                    positiveIncoherentRecouplingRowWeight S item *
                      nullCompletionKernel S item target)
                  tail)) _ ?_ ?_
          · exact Q'.add_eqv_congr'
              (Q'.mul_eqv_congr_left
                (S.fine.normalizedMass source) _ _
                (Q'.eqv_of_eq
                  (allCutoffWholeSlabKernel_eq_recoupling
                    S hsource hpositive hpartition target)))
              (kernelSum_eq_coherent_add_incoherent
                S target tail htail)
          refine Q'.eqv_trans _
            ((S.fine.normalizedMass source *
                wholeSlabRecouplingConditionalKernel
                  (coherentSlabRecouplingSourceOfRawPartitionPos
                    S source hsource hpartition) target +
              coherentRecouplingBlockedMassAux S target tail htail) +
              listQSum
                (fun item =>
                  positiveIncoherentRecouplingRowWeight S item *
                    nullCompletionKernel S item target)
                tail) _
            (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)) ?_
          exact Q'.add_eqv_congr_left _ _ _
            (Q'.eqv_trans _
              (0 + listQSum
                (fun item =>
                  positiveIncoherentRecouplingRowWeight S item *
                    nullCompletionKernel S item target)
                tail) _
              (Q'.eqv_symm (Q'.eqv_of_eq (Q'.zero_add' _)))
              (Q'.add_eqv_congr_right _ _ _
                (Q'.eqv_symm (Q'.zero_mul_eqv
                  (nullCompletionKernel S source target)))))
        · simp only [listQSum, coherentRecouplingBlockedMassAux,
            dif_pos hpositive, dif_neg hpartition,
            positiveIncoherentRecouplingRowWeight,
            if_pos hpositive, if_neg hpartition]
          refine Q'.eqv_trans _
            (S.fine.normalizedMass source *
                nullCompletionKernel S source target +
              (coherentRecouplingBlockedMassAux S target tail htail +
                listQSum
                  (fun item =>
                    positiveIncoherentRecouplingRowWeight S item *
                      nullCompletionKernel S item target)
                  tail)) _ ?_ ?_
          · exact Q'.add_eqv_congr'
              (Q'.mul_eqv_congr_left
                (S.fine.normalizedMass source) _ _
                (Q'.eqv_of_eq
                  (allCutoffWholeSlabKernel_eq_null_of_raw_partition_not_positive
                    S hsource hpositive hpartition target)))
              (kernelSum_eq_coherent_add_incoherent
                S target tail htail)
          refine Q'.eqv_trans _
            ((S.fine.normalizedMass source *
                nullCompletionKernel S source target +
              coherentRecouplingBlockedMassAux S target tail htail) +
              listQSum
                (fun item =>
                  positiveIncoherentRecouplingRowWeight S item *
                    nullCompletionKernel S item target)
                tail) _
            (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)) ?_
          refine Q'.eqv_trans _
            ((coherentRecouplingBlockedMassAux S target tail htail +
              S.fine.normalizedMass source *
                nullCompletionKernel S source target) +
              listQSum
                (fun item =>
                  positiveIncoherentRecouplingRowWeight S item *
                    nullCompletionKernel S item target)
                tail) _ ?_ ?_
          · exact Q'.add_eqv_congr_right _ _ _
              (Q'.add_comm_eqv _ _)
          exact Q'.add_assoc_eqv _ _ _
      · simp only [listQSum, coherentRecouplingBlockedMassAux,
          dif_neg hpositive, positiveIncoherentRecouplingRowWeight,
          if_neg hpositive]
        refine Q'.eqv_trans _
          (0 +
            (coherentRecouplingBlockedMassAux S target tail htail +
              listQSum
                (fun item =>
                  positiveIncoherentRecouplingRowWeight S item *
                    nullCompletionKernel S item target)
                tail)) _ ?_ ?_
        · exact Q'.add_eqv_congr'
            (Q'.eqv_trans _
              (0 * allCutoffWholeSlabKernel S source target) _
              (Q'.mul_eqv_congr_right _ _ _
                (normalizedMass_eqv_zero_of_not_positive
                  S.fine source hpositive))
              (Q'.zero_mul_eqv _))
            (kernelSum_eq_coherent_add_incoherent
              S target tail htail)
        refine Q'.eqv_trans _
          (coherentRecouplingBlockedMassAux S target tail htail +
            listQSum
              (fun item =>
                positiveIncoherentRecouplingRowWeight S item *
                  nullCompletionKernel S item target)
              tail) _
          (Q'.eqv_of_eq (Q'.zero_add' _)) ?_
        exact Q'.add_eqv_congr_left _ _ _
          (Q'.eqv_trans _
            (0 + listQSum
              (fun item =>
                positiveIncoherentRecouplingRowWeight S item *
                  nullCompletionKernel S item target)
              tail) _
            (Q'.eqv_symm (Q'.eqv_of_eq (Q'.zero_add' _)))
            (Q'.add_eqv_congr_right _ _ _
              (Q'.eqv_symm (Q'.zero_mul_eqv
                (nullCompletionKernel S source target)))))

/-- The complete normalized fine law is exactly the sum of the coherent
recoupling pushforward and the positive-incoherent fallback pushforward. -/
theorem blockedMass_eq_coherent_add_incoherent
    (S : SlabScalePair) (hfineCutoff : 1 <= S.fine.cutoff)
    (target : EdgeLabelling) :
    (allCutoffPhysicalKernel S hfineCutoff).blockedMass target ≈
      coherentRecouplingBlockedMass S target +
        positiveIncoherentFallbackBlockedMass S target := by
  unfold SlabScalePair.FiniteSlabKernel.blockedMass
    allCutoffPhysicalKernel coherentRecouplingBlockedMass
    positiveIncoherentFallbackBlockedMass
  exact kernelSum_eq_coherent_add_incoherent
    S target S.fine.physicalLabellings (fun _ hsource => hsource)

/-! ## 3. The fallback column has exactly the incoherent probability mass -/

theorem positiveIncoherentFallbackBlockedMass_nonnegative
    (S : SlabScalePair) (target : EdgeLabelling) :
    (0 : Q') <= positiveIncoherentFallbackBlockedMass S target := by
  unfold positiveIncoherentFallbackBlockedMass
  apply listQSum_nonnegative_on
  intro source _hsource
  exact Q'.mul_nonneg _ _
    (positiveIncoherentRecouplingRowWeight_nonnegative S source)
    (nullCompletionKernel_nonnegative S source target)

/-- Row normalization turns the total fallback pushforward mass into the
source probability of the positive incoherent sector, with no multiplicity
or carrier-size loss. -/
theorem positiveIncoherentFallbackBlockedMass_total
    (S : SlabScalePair) (hfineCutoff : 1 <= S.fine.cutoff) :
    listQSum
        (positiveIncoherentFallbackBlockedMass S)
        S.coarse.physicalLabellings ≈
      positiveIncoherentRecouplingMass S := by
  unfold positiveIncoherentFallbackBlockedMass
    positiveIncoherentRecouplingMass
  refine Q'.eqv_trans _
    (listQSum
      (fun source =>
        listQSum
          (fun target =>
            positiveIncoherentRecouplingRowWeight S source *
              nullCompletionKernel S source target)
          S.coarse.physicalLabellings)
      S.fine.physicalLabellings) _ ?_ ?_
  · exact listQSum_swap
      (fun source target =>
        positiveIncoherentRecouplingRowWeight S source *
          nullCompletionKernel S source target)
      S.fine.physicalLabellings S.coarse.physicalLabellings
  apply listQSum_congr_on
  intro source _hsource
  refine Q'.eqv_trans _
    (positiveIncoherentRecouplingRowWeight S source *
      listQSum (nullCompletionKernel S source)
        S.coarse.physicalLabellings) _ ?_ ?_
  · exact listQSum_mul_left
      (positiveIncoherentRecouplingRowWeight S source)
      (nullCompletionKernel S source)
      S.coarse.physicalLabellings
  refine Q'.eqv_trans _
    (positiveIncoherentRecouplingRowWeight S source * 1) _
    (Q'.mul_eqv_congr_left
      (positiveIncoherentRecouplingRowWeight S source) _ _
      (allCutoffNullCompletionKernel_row_normalized
        S hfineCutoff source)) ?_
  exact Q'.mul_one_eqv _

/-- The targetwise difference between the full pushed law and its coherent
recoupling part is exactly the nonnegative fallback column. -/
theorem blockedMass_sub_coherent_eqv_incoherent
    (S : SlabScalePair) (hfineCutoff : 1 <= S.fine.cutoff)
    (target : EdgeLabelling) :
    (allCutoffPhysicalKernel S hfineCutoff).blockedMass target +
        -(coherentRecouplingBlockedMass S target) ≈
      positiveIncoherentFallbackBlockedMass S target := by
  let coherent := coherentRecouplingBlockedMass S target
  let fallback := positiveIncoherentFallbackBlockedMass S target
  refine Q'.eqv_trans _
    ((coherent + fallback) + -coherent) _
    (Q'.add_eqv_congr_right _ _ _
      (blockedMass_eq_coherent_add_incoherent
        S hfineCutoff target)) ?_
  refine Q'.eqv_trans _
    (coherent + (fallback + -coherent)) _
    (Q'.add_assoc_eqv _ _ _) ?_
  refine Q'.eqv_trans _
    (coherent + (-coherent + fallback)) _
    (Q'.add_eqv_congr_left _ _ _
      (Q'.add_comm_eqv _ _)) ?_
  refine Q'.eqv_trans _
    ((coherent + -coherent) + fallback) _
    (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)) ?_
  refine Q'.eqv_trans _
    (0 + fallback) _
    (Q'.add_eqv_congr_right _ _ _
      (Q'.add_neg_self_eqv coherent)) ?_
  exact Q'.eqv_of_eq (Q'.zero_add' fallback)

/-- Exact total-variation size of replacing the total kernel pushforward by
its coherent recoupling part. -/
def coherenceFallbackL1
    (S : SlabScalePair) (hfineCutoff : 1 <= S.fine.cutoff) : Q' :=
  listQSum
    (fun target =>
      Q'.abs
        ((allCutoffPhysicalKernel S hfineCutoff).blockedMass target +
          -(coherentRecouplingBlockedMass S target)))
    S.coarse.physicalLabellings

/-- The complete `L1` cost of the fallback is not merely bounded by the
incoherent source probability: it is exactly that probability. -/
theorem coherenceFallbackL1_eqv_positiveIncoherentRecouplingMass
    (S : SlabScalePair) (hfineCutoff : 1 <= S.fine.cutoff) :
    coherenceFallbackL1 S hfineCutoff ≈
      positiveIncoherentRecouplingMass S := by
  unfold coherenceFallbackL1
  refine Q'.eqv_trans _
    (listQSum
      (positiveIncoherentFallbackBlockedMass S)
      S.coarse.physicalLabellings) _ ?_ ?_
  · exact listQSum_congr_on _ _ S.coarse.physicalLabellings
      (fun target _htarget =>
        Q'.eqv_trans _
          (Q'.abs (positiveIncoherentFallbackBlockedMass S target)) _
          (ExpNeg.abs_eqv_congr
            (blockedMass_sub_coherent_eqv_incoherent
              S hfineCutoff target))
          (Q'.eqv_of_eq
            (ExpNeg.abs_of_nonneg
              (positiveIncoherentFallbackBlockedMass_nonnegative
                S target))))
  · exact positiveIncoherentFallbackBlockedMass_total
      S hfineCutoff

theorem positiveIncoherentFallbackBlockedMass_eqv_zero_at_cutoffOne
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (target : EdgeLabelling) :
    positiveIncoherentFallbackBlockedMass S target ≈ 0 := by
  unfold positiveIncoherentFallbackBlockedMass
  refine Q'.eqv_trans _
    (listQSum (fun _source => (0 : Q'))
      S.fine.physicalLabellings) _ ?_ ?_
  · exact listQSum_congr_on _ _ S.fine.physicalLabellings
      (fun source hsource =>
        Q'.eqv_trans _
          (0 * nullCompletionKernel S source target) _
          (Q'.mul_eqv_congr_right _ _ _
            (Q'.eqv_of_eq
              (positiveIncoherentRecouplingRowWeight_eq_zero_at_cutoffOne
                S hfineCutoff hcoarseCoupling hsource)))
          (Q'.zero_mul_eqv _))
  · exact listQSum_zero S.fine.physicalLabellings

/-! ## Axiom audit -/

#print axioms coherentRecouplingBlockedMass
#print axioms blockedMass_eq_coherent_add_incoherent
#print axioms positiveIncoherentFallbackBlockedMass_nonnegative
#print axioms positiveIncoherentFallbackBlockedMass_total
#print axioms blockedMass_sub_coherent_eqv_incoherent
#print axioms coherenceFallbackL1_eqv_positiveIncoherentRecouplingMass
#print axioms positiveIncoherentFallbackBlockedMass_eqv_zero_at_cutoffOne

end YMGap.Continuum.CompactDualAllCutoffPhysicalPushforward
