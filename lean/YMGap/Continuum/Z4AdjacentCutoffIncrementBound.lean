/-
# A derived adjacent-cutoff bound for the interacting Z4 partition

`Z4PhysicalCutoffPartitionMonotonicity` identifies the exact cutoff error with
a nonnegative sum over new physical labellings.  Here we bound one adjacent
increment, from `K` to `K+1`, without replacing the interacting partition by
an assumed envelope.

Every new labelling has an explicitly extracted plaquette of spin `K+1`.
Its face product is therefore at most the first omitted heat-kernel
coefficient, because every other retained face coefficient is nonnegative and
at most one.  The already-derived cubic local fusion-count bound controls the
link product.  Finally, the exact Cartesian-list length pays the number of new
labellings.  The result is intentionally crude but entirely in-substrate; its
subsequent resummation is a quantitative task rather than a missing assembly
axiom.
-/

import YMGap.Continuum.Z4ExplicitSupportMultiplicityBound
import YMGap.Continuum.Z4FixedCutoffNaiveTailFence
import YMGap.Continuum.Z4PhysicalCutoffPartitionMonotonicity

namespace YMGap.Continuum.Z4AdjacentCutoffIncrementBound

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.PinnedCluster
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphCutoffCoherence
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2PeterWeylWilsonBlock
open YMGap.Continuum.Z4ExplicitLinkSpinFoamFormula
open YMGap.Continuum.Z4ExplicitPhysicalCutoffReduction
open YMGap.Continuum.Z4ExplicitSpinFoamBounds
open YMGap.Continuum.Z4ExplicitSupportFaceBound
open YMGap.Continuum.Z4ExplicitSupportMultiplicityBound
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4FixedCutoffNaiveTailFence
open YMGap.Continuum.Z4PhysicalCutoffPartitionMonotonicity

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Elementary finite-product bounds -/

private theorem eliminateLinks_nonnegative_local
    (value : Nat → Q') :
    ∀ edges : List Nat,
      (∀ edge, edge ∈ edges → (0 : Q') ≤ value edge) →
      (0 : Q') ≤ eliminateLinks value edges
  | [], _ => Q'.zero_le_one
  | head :: tail, hvalue =>
      Q'.mul_nonneg _ _
        (hvalue head List.mem_cons_self)
        (eliminateLinks_nonnegative_local value tail
          (fun edge hedge =>
            hvalue edge (List.mem_cons_of_mem head hedge)))

private theorem eliminateLinks_le_one_local
    (value : Nat → Q') :
    ∀ edges : List Nat,
      (∀ edge, edge ∈ edges → (0 : Q') ≤ value edge) →
      (∀ edge, edge ∈ edges → value edge ≤ (1 : Q')) →
      eliminateLinks value edges ≤ (1 : Q')
  | [], _, _ => Q'.le_refl' 1
  | head :: tail, hnonneg, hle => by
      have htail0 := eliminateLinks_nonnegative_local value tail
        (fun edge hedge =>
          hnonneg edge (List.mem_cons_of_mem head hedge))
      have htail1 := eliminateLinks_le_one_local value tail
        (fun edge hedge =>
          hnonneg edge (List.mem_cons_of_mem head hedge))
        (fun edge hedge => hle edge (List.mem_cons_of_mem head hedge))
      have hfirst : value head * eliminateLinks value tail ≤
          (1 : Q') * eliminateLinks value tail :=
        Q'.mul_le_mul_of_nonneg_right _ _ _
          (hle head List.mem_cons_self) htail0
      have hsecond : (1 : Q') * eliminateLinks value tail ≤
          (1 : Q') * (1 : Q') :=
        Q'.mul_le_mul_of_nonneg_left _ _ _ htail1 Q'.zero_le_one
      exact Q'.le_trans' _ _ _ hfirst
        (Q'.le_trans' _ _ _ hsecond
          (Q'.le_of_eqv (Q'.one_mul_eqv 1)))

/-- If all factors lie in `[0,1]`, a finite product is bounded by any selected
factor which actually occurs in the product list. -/
private theorem eliminateLinks_le_selected_local
    (value : Nat → Q') :
    ∀ (edges : List Nat) (selected : Nat),
      selected ∈ edges →
      (∀ edge, edge ∈ edges → (0 : Q') ≤ value edge) →
      (∀ edge, edge ∈ edges → value edge ≤ (1 : Q')) →
      eliminateLinks value edges ≤ value selected
  | [], _, hmem, _, _ => by cases hmem
  | head :: tail, selected, hmem, hnonneg, hle => by
      rcases List.mem_cons.mp hmem with hselected | htail
      · subst selected
        have htail1 := eliminateLinks_le_one_local value tail
          (fun edge hedge =>
            hnonneg edge (List.mem_cons_of_mem head hedge))
          (fun edge hedge => hle edge (List.mem_cons_of_mem head hedge))
        have hmul : value head * eliminateLinks value tail ≤
            value head * (1 : Q') :=
          Q'.mul_le_mul_of_nonneg_left _ _ _ htail1
            (hnonneg head List.mem_cons_self)
        exact Q'.le_trans' _ _ _ hmul
          (Q'.le_of_eqv (Q'.mul_one_eqv (value head)))
      · have htail0 := eliminateLinks_nonnegative_local value tail
          (fun edge hedge =>
            hnonneg edge (List.mem_cons_of_mem head hedge))
        have hind := eliminateLinks_le_selected_local value tail selected htail
          (fun edge hedge =>
            hnonneg edge (List.mem_cons_of_mem head hedge))
          (fun edge hedge => hle edge (List.mem_cons_of_mem head hedge))
        have hfirst : value head * eliminateLinks value tail ≤
            (1 : Q') * eliminateLinks value tail :=
          Q'.mul_le_mul_of_nonneg_right _ _ _
            (hle head List.mem_cons_self) htail0
        have hsecond : (1 : Q') * eliminateLinks value tail ≤
            (1 : Q') * value selected :=
          Q'.mul_le_mul_of_nonneg_left _ _ _ hind Q'.zero_le_one
        exact Q'.le_trans' _ _ _ hfirst
          (Q'.le_trans' _ _ _ hsecond
            (Q'.le_of_eqv (Q'.one_mul_eqv (value selected))))

/-! ## 2. A new adjacent label has a maximal-spin witness -/

theorem adjacentCutoffNewLabel_has_max_spin
    {K n : Nat} {physical : EdgeLabelling}
    (hphysical : physical ∈
      (boundedEdgeLabellings (K + 1)
        (List.range (plaquetteEdgeCount n))).filter
        (fun label =>
          !(labelWithinB K (List.range (plaquetteEdgeCount n)) label))) :
    ∃ edge, edge ∈ List.range (plaquetteEdgeCount n) ∧
      physical edge = K + 1 := by
  have hparts := List.mem_filter.mp hphysical
  have hsupport := hparts.1
  have hnew := hparts.2
  have holdFalse : labelWithinB K
      (List.range (plaquetteEdgeCount n)) physical = false := by
    cases h : labelWithinB K
        (List.range (plaquetteEdgeCount n)) physical <;>
      simp [h] at hnew ⊢
  obtain ⟨edge, hedge, hlarge⟩ := labelWithinB_false_exists K
    (List.range (plaquetteEdgeCount n)) physical holdFalse
  have hsound := boundedEdgeLabellings_sound (K + 1)
    (List.range (plaquetteEdgeCount n)) physical hsupport
  have hupper := hsound.1 edge hedge
  exact ⟨edge, hedge, by omega⟩

private theorem adjacentFaceCoefficient_le_one
    {K n : Nat} {physical : EdgeLabelling}
    (hphysical : physical ∈ boundedEdgeLabellings (K + 1)
      (List.range (plaquetteEdgeCount n))) :
    ∀ edge, edge ∈ List.range (plaquetteEdgeCount n) →
      coeffAt (heatKernelPacket (K + 1) coupling) (physical edge) ≤
        (1 : Q') := by
  intro edge hedge
  have hphysical' : physical ∈ explicitPhysicalLabellings (K + 1) n := by
    simpa [explicitPhysicalLabellings, physicalFaceEdges] using hphysical
  by_cases hzero : physical edge = 0
  · have hspin : physical edge < (K + 1) + 1 := by omega
    rw [coeffAt_heatKernelPacket hspin, hzero, coeffW_zero]
    exact Q'.le_refl' 1
  · have hpositive : 1 ≤ physical edge := by omega
    have hquarter := excitedFaceCoefficient_le_quarter
      hphysical' (by simpa [physicalFaceEdges] using hedge) hpositive
    exact Q'.le_trans' _ _ _ hquarter (by decide)

theorem adjacentNewPhysicalFaceFactor_le_firstOmitted
    {K n : Nat} {physical : EdgeLabelling}
    (hphysical : physical ∈
      (boundedEdgeLabellings (K + 1)
        (List.range (plaquetteEdgeCount n))).filter
        (fun label =>
          !(labelWithinB K (List.range (plaquetteEdgeCount n)) label))) :
    explicitPhysicalFaceFactor (K + 1) n physical ≤
      firstOmittedCoefficient K := by
  have hsupport := (List.mem_filter.mp hphysical).1
  obtain ⟨selected, hselected, hspin⟩ :=
    adjacentCutoffNewLabel_has_max_spin hphysical
  unfold explicitPhysicalFaceFactor
  have hproduct := eliminateLinks_le_selected_local
    (fun edge => coeffAt (heatKernelPacket (K + 1) coupling)
      (physical edge))
    (List.range (plaquetteEdgeCount n)) selected hselected
    (fun edge _ =>
      heatKernelPacketCoefficient_nonnegative (K + 1) (physical edge))
    (adjacentFaceCoefficient_le_one hsupport)
  have hselectedCoefficient :
      coeffAt (heatKernelPacket (K + 1) coupling) (physical selected) =
        firstOmittedCoefficient K := by
    have hbound : physical selected < (K + 1) + 1 := by omega
    rw [coeffAt_heatKernelPacket hbound, hspin]
    rfl
  dsimp only at hproduct
  rw [hselectedCoefficient] at hproduct
  exact hproduct

/-! ## 3. Uniform adjacent summand and sum bounds -/

def adjacentCutoffTermBound (K n : Nat) : Q' :=
  firstOmittedCoefficient K *
    linkMultiplicityBound (K + 1) ^
      (enumerate (distinctBoxLinks n)).length

def adjacentCutoffIncrementMajorant (K n : Nat) : Q' :=
  Q'.ofNat ((K + 2) ^ plaquetteEdgeCount n) *
    adjacentCutoffTermBound K n

/-- A geometry-only version of the adjacent majorant, replacing the exact
distinct-link count by four boundary-link occurrences per plaquette. -/
def adjacentCutoffVolumeMajorant (K n : Nat) : Q' :=
  Q'.ofNat ((K + 2) ^ plaquetteEdgeCount n) *
    (firstOmittedCoefficient K *
      linkMultiplicityBound (K + 1) ^ (plaquetteEdgeCount n * 4))

theorem adjacentCutoffTermBound_nonnegative (K n : Nat) :
    (0 : Q') ≤ adjacentCutoffTermBound K n := by
  unfold adjacentCutoffTermBound
  exact Q'.mul_nonneg _ _
    (Q'.le_of_lt (firstOmittedCoefficient_pos K))
    (Q'.pow_nonneg _
      (Q'.le_trans' _ _ _ Q'.zero_le_one
        (one_le_linkMultiplicityBound (K + 1))) _)

theorem adjacentNewPhysicalTerm_le
    {K n : Nat} {physical : EdgeLabelling}
    (hphysical : physical ∈
      (boundedEdgeLabellings (K + 1)
        (List.range (plaquetteEdgeCount n))).filter
        (fun label =>
          !(labelWithinB K (List.range (plaquetteEdgeCount n)) label))) :
    fusionCompletePhysicalTerm (K + 1) n physical ≤
      adjacentCutoffTermBound K n := by
  have hface := adjacentNewPhysicalFaceFactor_le_firstOmitted hphysical
  have hlink := explicitLinkMultiplicityProduct_le_pow
    (K + 1) n physical (enumerate (distinctBoxLinks n))
  have hlink0 : (0 : Q') ≤ explicitLinkMultiplicityProduct (K + 1) n
      physical (enumerate (distinctBoxLinks n)) :=
    explicitLinkMultiplicityProduct_nonnegative _ _ _ _
  have hfirst0 : (0 : Q') ≤ firstOmittedCoefficient K :=
    Q'.le_of_lt (firstOmittedCoefficient_pos K)
  unfold fusionCompletePhysicalTerm adjacentCutoffTermBound
  have hstep1 : explicitPhysicalFaceFactor (K + 1) n physical *
      explicitLinkMultiplicityProduct (K + 1) n physical
        (enumerate (distinctBoxLinks n)) ≤
      firstOmittedCoefficient K *
        explicitLinkMultiplicityProduct (K + 1) n physical
          (enumerate (distinctBoxLinks n)) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hface hlink0
  have hstep2 : firstOmittedCoefficient K *
      explicitLinkMultiplicityProduct (K + 1) n physical
        (enumerate (distinctBoxLinks n)) ≤
      firstOmittedCoefficient K *
        linkMultiplicityBound (K + 1) ^
          (enumerate (distinctBoxLinks n)).length :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hlink hfirst0
  exact Q'.le_trans' _ _ _ hstep1 hstep2

private theorem listQSum_le_length_mul_local {A : Type}
    (f : A → Q') {bound : Q'} (hbound0 : (0 : Q') ≤ bound) :
    ∀ xs : List A,
      (∀ x, x ∈ xs → f x ≤ bound) →
      listQSum f xs ≤ Q'.ofNat xs.length * bound
  | [], _ => by
      exact Q'.le_of_eqv (Q'.eqv_symm (Q'.zero_mul_eqv bound))
  | head :: tail, hbound => by
      have hhead := hbound head List.mem_cons_self
      have htail := listQSum_le_length_mul_local f hbound0 tail
        (fun x hx => hbound x (List.mem_cons_of_mem head hx))
      have hsum : f head + listQSum f tail ≤
          bound + Q'.ofNat tail.length * bound :=
        Q'.le_trans' _ _ _
          (Q'.add_le_add_right _ _ _ hhead)
          (Q'.add_le_add_left _ _ _ htail)
      have htarget :
          Q'.ofNat (tail.length + 1) * bound ≈
            bound + Q'.ofNat tail.length * bound := by
        refine Q'.eqv_trans _ ((Q'.ofNat tail.length + 1) * bound) _
          (Q'.mul_eqv_congr_right _ _ bound
            (Q'.ofNat_add_eqv tail.length 1)) ?_
        refine Q'.eqv_trans _
          (Q'.ofNat tail.length * bound + (1 : Q') * bound) _
          (Q'.add_mul_eqv _ _ _) ?_
        refine Q'.eqv_trans _
          (Q'.ofNat tail.length * bound + bound) _
          (Q'.add_eqv_congr_left _ _ _ (Q'.one_mul_eqv bound)) ?_
        exact Q'.add_comm_eqv _ _
      exact Q'.le_trans' _ _ _ hsum (Q'.ge_of_eqv htarget)

private theorem boundedEdgeLabellings_length_local (K : Nat) :
    ∀ edges : List Nat,
      (boundedEdgeLabellings K edges).length =
        (K + 1) ^ edges.length
  | [] => rfl
  | head :: tail => by
      unfold boundedEdgeLabellings
      have hflat := length_flatMap_fixed
        (List.range (K + 1))
        (fun spin =>
          (boundedEdgeLabellings K tail).map
            (fun label => setEdgeLabel label head spin))
        ((K + 1) ^ tail.length)
        (fun _ => by simp [boundedEdgeLabellings_length_local K tail])
      rw [hflat, List.length_range, List.length_cons, Nat.pow_succ]
      exact Nat.mul_comm _ _

theorem adjacentCutoffIncrement_le_majorant (K n : Nat) :
    fusionCompleteCutoffIncrement K (K + 1) n ≤
      adjacentCutoffIncrementMajorant K n := by
  let support :=
    (boundedEdgeLabellings (K + 1)
      (List.range (plaquetteEdgeCount n))).filter
      (fun label =>
        !(labelWithinB K (List.range (plaquetteEdgeCount n)) label))
  have hsum : listQSum (fusionCompletePhysicalTerm (K + 1) n) support ≤
      Q'.ofNat support.length * adjacentCutoffTermBound K n := by
    apply listQSum_le_length_mul_local _
      (adjacentCutoffTermBound_nonnegative K n)
    intro physical hphysical
    exact adjacentNewPhysicalTerm_le hphysical
  have hlength : support.length ≤
      (K + 2) ^ plaquetteEdgeCount n := by
    have hfilterLength : support.length ≤
        (boundedEdgeLabellings (K + 1)
          (List.range (plaquetteEdgeCount n))).length := by
      dsimp only [support]
      exact List.length_filter_le _ _
    refine Nat.le_trans hfilterLength ?_
    have hcartesian := boundedEdgeLabellings_length_local (K + 1)
      (List.range (plaquetteEdgeCount n))
    rw [List.length_range] at hcartesian
    have hbase : K + 1 + 1 = K + 2 := by omega
    rw [hbase] at hcartesian
    exact Nat.le_of_eq hcartesian
  have hcount : Q'.ofNat support.length ≤
      Q'.ofNat ((K + 2) ^ plaquetteEdgeCount n) :=
    Q'.ofNat_le_ofNat hlength
  have hcountMul : Q'.ofNat support.length * adjacentCutoffTermBound K n ≤
      Q'.ofNat ((K + 2) ^ plaquetteEdgeCount n) *
        adjacentCutoffTermBound K n :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hcount
      (adjacentCutoffTermBound_nonnegative K n)
  unfold fusionCompleteCutoffIncrement adjacentCutoffIncrementMajorant
  dsimp only [support] at hsum hcountMul ⊢
  exact Q'.le_trans' _ _ _ hsum hcountMul

/-! ## 4. Eliminate the residual exact-link count -/

private theorem eraseDups_length_le_local {A : Type}
    [BEq A] (xs : List A) :
    xs.eraseDups.length ≤ xs.length := by
  cases xs with
  | nil => simp
  | cons head tail =>
      rw [List.eraseDups_cons]
      simp only [List.length_cons]
      have hfilter := List.length_filter_le
        (fun item : A => !item == head) tail
      have ih := eraseDups_length_le_local
        (tail.filter fun item => !item == head)
      omega
termination_by xs.length
decreasing_by
  simp_wf
  omega

theorem distinctBoxLinks_length_le_four_plaquettes (n : Nat) :
    (enumerate (distinctBoxLinks n)).length ≤
      plaquetteEdgeCount n * 4 := by
  rw [enumerate_length]
  have herase : (distinctBoxLinks n).length ≤ (boxLinks n).length := by
    unfold distinctBoxLinks
    exact eraseDups_length_le_local (boxLinks n)
  have hbox : (boxLinks n).length = plaquetteEdgeCount n * 4 := by
    unfold boxLinks plaquetteEdgeCount
    exact length_flatMap_fixed (boxPlaquettes n) edgesOf 4
      (fun _ => rfl)
  rw [hbox] at herase
  exact herase

private theorem pow_succ_le_local {B : Q'} (hB : (1 : Q') ≤ B)
    (s : Nat) : B ^ s ≤ B ^ (s + 1) := by
  have hpow0 : (0 : Q') ≤ B ^ s :=
    Q'.pow_nonneg B (Q'.le_trans' _ _ _ Q'.zero_le_one hB) s
  show B ^ s ≤ B * B ^ s
  exact Q'.le_trans' _ ((1 : Q') * B ^ s) _
    (Q'.ge_of_eqv (Q'.one_mul_eqv _))
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hB hpow0)

private theorem pow_add_le_local {B : Q'} (hB : (1 : Q') ≤ B)
    (s : Nat) : ∀ d, B ^ s ≤ B ^ (s + d)
  | 0 => Q'.le_refl' _
  | d + 1 => by
      have hindex : s + (d + 1) = (s + d) + 1 := by omega
      rw [hindex]
      exact Q'.le_trans' _ _ _ (pow_add_le_local hB s d)
        (pow_succ_le_local hB (s + d))

private theorem pow_mono_exponent_local {B : Q'} (hB : (1 : Q') ≤ B)
    {s t : Nat} (hst : s ≤ t) : B ^ s ≤ B ^ t := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hst
  exact pow_add_le_local hB s d

theorem adjacentCutoffIncrementMajorant_le_volumeMajorant (K n : Nat) :
    adjacentCutoffIncrementMajorant K n ≤
      adjacentCutoffVolumeMajorant K n := by
  let count := Q'.ofNat ((K + 2) ^ plaquetteEdgeCount n)
  let first := firstOmittedCoefficient K
  let multiplicity := linkMultiplicityBound (K + 1)
  have hpow : multiplicity ^ (enumerate (distinctBoxLinks n)).length ≤
      multiplicity ^ (plaquetteEdgeCount n * 4) :=
    pow_mono_exponent_local (one_le_linkMultiplicityBound (K + 1))
      (distinctBoxLinks_length_le_four_plaquettes n)
  have hfirst0 : (0 : Q') ≤ first :=
    Q'.le_of_lt (firstOmittedCoefficient_pos K)
  have hinner : first *
      multiplicity ^ (enumerate (distinctBoxLinks n)).length ≤
      first * multiplicity ^ (plaquetteEdgeCount n * 4) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hpow hfirst0
  have hcount0 : (0 : Q') ≤ count := by
    dsimp only [count]
    rw [Q'.zero_le_iff_num_nonneg]
    exact Int.natCast_nonneg _
  unfold adjacentCutoffIncrementMajorant adjacentCutoffTermBound
    adjacentCutoffVolumeMajorant
  dsimp only [count, first, multiplicity] at hinner hcount0 ⊢
  exact Q'.mul_le_mul_of_nonneg_left _ _ _ hinner hcount0

theorem adjacentCutoffIncrement_le_volumeMajorant (K n : Nat) :
    fusionCompleteCutoffIncrement K (K + 1) n ≤
      adjacentCutoffVolumeMajorant K n :=
  Q'.le_trans' _ _ _
    (adjacentCutoffIncrement_le_majorant K n)
    (adjacentCutoffIncrementMajorant_le_volumeMajorant K n)

end YMGap.Continuum.Z4AdjacentCutoffIncrementBound

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4AdjacentCutoffIncrementBound.adjacentCutoffNewLabel_has_max_spin
#print axioms YMGap.Continuum.Z4AdjacentCutoffIncrementBound.adjacentNewPhysicalFaceFactor_le_firstOmitted
#print axioms YMGap.Continuum.Z4AdjacentCutoffIncrementBound.adjacentNewPhysicalTerm_le
#print axioms YMGap.Continuum.Z4AdjacentCutoffIncrementBound.adjacentCutoffIncrement_le_majorant
#print axioms YMGap.Continuum.Z4AdjacentCutoffIncrementBound.distinctBoxLinks_length_le_four_plaquettes
#print axioms YMGap.Continuum.Z4AdjacentCutoffIncrementBound.adjacentCutoffIncrement_le_volumeMajorant
