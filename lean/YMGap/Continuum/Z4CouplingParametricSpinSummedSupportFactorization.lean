/-
# Coupling-parametric factorization of arbitrary-cutoff support activity

For every nonnegative rational heat-kernel coupling, the complete finite spin
sum on one excited-face support factors exactly into the product of the spin
sums on its canonical connected components.  The support geometry and the
two finite weighted injections are independent of the coupling; only their
exact rational weights are parameterized here.

The factorization is then carried through the coupling-independent support
fiber and compatible-family permutations.  Thus the physical arbitrary-
cutoff partition at the same coupling is exactly the corresponding hard-core
gas partition.
-/

import YMGap.Continuum.Z4CouplingParametricSpinSummedPinnedLayer
import YMGap.Continuum.Z4SpinSummedCompatibleGas

namespace YMGap.Continuum.Z4CouplingParametricSpinSummedSupportFactorization

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.CayleyInjection
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4AllSpinLinkSeparatedFamilyFactorization
open YMGap.Continuum.Z4AllSpinLinkSeparatedFactorization
open YMGap.Continuum.Z4AllSpinSurfaceComponentLabels
open YMGap.Continuum.Z4BoundedEdgeLabellingNodup
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalDecoratedConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CouplingParametricSpinSummedPinnedLayer
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4ExplicitSupportFaceBound
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4LinkSeparatedFamilyFactorization
open YMGap.Continuum.Z4ParametricPhysicalCutoffPartition
open YMGap.Continuum.Z4PhysicalSurfaceComponentLabels
open YMGap.Continuum.Z4PhysicalSurfaceComponents
open YMGap.Continuum.Z4SpinSummedFaceActivityBound
open YMGap.Continuum.Z4SpinSummedSupportComponentLower
open YMGap.Continuum.Z4SpinSummedSupportComponentUpper
open YMGap.Continuum.Z4SpinSummedSupportPartition

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Coupling-parametric Cartesian component activity -/

/-- Product of complete fixed-support spin sums over an ordered support
family, at one common coupling and representation cutoff. -/
def couplingParametricKSupportFamilyActivity
    (coupling : Q') (cutoff n : Nat) : List (List Nat) → Q'
  | [] => 1
  | support :: supports =>
      couplingParametricKSupportActivity coupling cutoff n support *
        couplingParametricKSupportFamilyActivity coupling cutoff n supports

private theorem physicalTermProduct_nonnegative
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff n : Nat) : ∀ labels : List EdgeLabelling,
    (0 : Q') ≤ parametricKPhysicalTermProduct coupling cutoff n labels
  | [] => Q'.zero_le_one
  | label :: labels =>
      Q'.mul_nonneg _ _
        (parametricKPhysicalTerm_nonnegative hcoupling cutoff n label)
        (physicalTermProduct_nonnegative hcoupling cutoff n labels)

theorem couplingParametricKSupportFamilyActivity_nonnegative
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff n : Nat) : ∀ family : List (List Nat),
    (0 : Q') ≤
      couplingParametricKSupportFamilyActivity coupling cutoff n family
  | [] => Q'.zero_le_one
  | support :: family =>
      Q'.mul_nonneg _ _
        (couplingParametricKSupportActivity_nonnegative
          hcoupling cutoff n support)
        (couplingParametricKSupportFamilyActivity_nonnegative
          hcoupling cutoff n family)

/-- Expanding a Cartesian product of independently decorated supports gives
the product of their complete spin sums.  This identity is algebraic and does
not require a sign assumption on the coupling. -/
theorem couplingParametricSupportFamilyLabellings_weight_sum
    (coupling : Q') (cutoff n : Nat) :
    ∀ supports : List (List Nat),
      listQSum (parametricKPhysicalTermProduct coupling cutoff n)
          (supportFamilyLabellings cutoff n supports) ≈
        couplingParametricKSupportFamilyActivity
          coupling cutoff n supports
  | [] => by
      change (1 : Q') + 0 ≈ 1
      exact Q'.eqv_of_eq (Q'.add_zero' 1)
  | support :: supports => by
      unfold supportFamilyLabellings
      rw [listQSum_map]
      change listQSum
          (fun pair =>
            parametricKPhysicalTerm coupling cutoff n pair.1 *
              parametricKPhysicalTermProduct coupling cutoff n pair.2)
          (cartesian (physicalLabellingsWithSupport cutoff n support)
            (supportFamilyLabellings cutoff n supports)) ≈
        couplingParametricKSupportFamilyActivity coupling cutoff n
          (support :: supports)
      refine Q'.eqv_trans _ _ _
        (listQSum_cartesian_product
          (parametricKPhysicalTerm coupling cutoff n)
          (parametricKPhysicalTermProduct coupling cutoff n)
          (physicalLabellingsWithSupport cutoff n support)
          (supportFamilyLabellings cutoff n supports)) ?_
      unfold couplingParametricKSupportFamilyActivity
        couplingParametricKSupportActivity
      exact Q'.mul_eqv_congr_left _ _ _
        (couplingParametricSupportFamilyLabellings_weight_sum
          coupling cutoff n supports)

/-! ## 2. Restriction to canonical connected components -/

private def couplingCodedSupportFamilyLabellings
    (coupling : Q') (cutoff n : Nat) (supports : List (List Nat)) :
    List (List (List Nat) × Q') :=
  (supportFamilyLabellings cutoff n supports).map
    (fun labels =>
      (supportFamilySpinCode n labels,
        parametricKPhysicalTermProduct coupling cutoff n labels))

private theorem couplingCodedSupportFamilyLabellings_nodup
    (coupling : Q') (cutoff n : Nat) (supports : List (List Nat)) :
    (couplingCodedSupportFamilyLabellings
      coupling cutoff n supports).Nodup := by
  unfold couplingCodedSupportFamilyLabellings
  apply nodup_map_of_injOn
  · exact supportFamilyLabellings_nodup cutoff n supports
  · intro left hleft right hright heq
    apply supportFamilySpinCode_injective_on_kPhysical
      (supportMatched_kPhysicalFamily
        ((mem_supportFamilyLabellings_iff
          cutoff n supports left).1 hleft))
      (supportMatched_kPhysicalFamily
        ((mem_supportFamilyLabellings_iff
          cutoff n supports right).1 hright))
    exact congrArg Prod.fst heq

theorem couplingParametricKSupportActivity_le_componentFamilyActivity
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff n : Nat) (support : List Nat) :
    couplingParametricKSupportActivity coupling cutoff n support ≤
      couplingParametricKSupportFamilyActivity coupling cutoff n
        (canonicalSurfaceFamily n support) := by
  let source := physicalLabellingsWithSupport cutoff n support
  let families := supportFamilyLabellings cutoff n
    (canonicalSurfaceFamily n support)
  let target := couplingCodedSupportFamilyLabellings coupling cutoff n
    (canonicalSurfaceFamily n support)
  let encodeFamily : EdgeLabelling → List EdgeLabelling :=
    fun physical => decoratedSurfaceComponentLabels n physical
  let encode : EdgeLabelling → List (List Nat) × Q' :=
    fun physical =>
      (supportFamilySpinCode n (encodeFamily physical),
        parametricKPhysicalTermProduct coupling cutoff n
          (encodeFamily physical))
  have hinjection :
      listQSum (parametricKPhysicalTerm coupling cutoff n) source ≤
        listQSum Prod.snd target := by
    apply listQSum_le_of_injective source target
      (parametricKPhysicalTerm coupling cutoff n) Prod.snd encode
    · exact physicalLabellingsWithSupport_nodup cutoff n support
    · intro physical hphysical
      unfold target couplingCodedSupportFamilyLabellings
      apply List.mem_map.mpr
      exact ⟨encodeFamily physical,
        decoratedSurfaceComponentLabels_mem_familyLabellings hphysical,
        rfl⟩
    · intro left hleft right hright heq
      have hleftParts := mem_physicalLabellingsWithSupport_iff.mp hleft
      have hrightParts := mem_physicalLabellingsWithSupport_iff.mp hright
      apply decoratedSurfaceComponentLabels_injective_on_bounded
        hleftParts.1 hrightParts.1
      apply supportFamilySpinCode_injective_on_kPhysical
        (decoratedSurfaceComponentLabels_kPhysicalFamily
          cutoff n left hleftParts.1)
        (decoratedSurfaceComponentLabels_kPhysicalFamily
          cutoff n right hrightParts.1)
      exact congrArg Prod.fst heq
    · intro physical hphysical
      have hparts := mem_physicalLabellingsWithSupport_iff.mp hphysical
      exact Q'.le_of_eqv
        (parametricKPhysicalTerm_surfaceComponent_factor
          (w := coupling) hparts.1)
    · intro coded hcoded
      unfold target couplingCodedSupportFamilyLabellings at hcoded
      obtain ⟨family, _, heq⟩ := List.mem_map.mp hcoded
      rw [← heq]
      exact physicalTermProduct_nonnegative
        hcoupling cutoff n family
  have htarget : listQSum Prod.snd target ≈
      listQSum (parametricKPhysicalTermProduct coupling cutoff n)
        families := by
    unfold target couplingCodedSupportFamilyLabellings families
    rw [listQSum_map]
    exact Q'.eqv_refl _
  unfold couplingParametricKSupportActivity
  exact Q'.le_trans' _ _ _ hinjection
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv htarget)
      (Q'.le_of_eqv
        (couplingParametricSupportFamilyLabellings_weight_sum
          coupling cutoff n (canonicalSurfaceFamily n support))))

/-! ## 3. Recombination of independently decorated components -/

private def couplingCodedPhysicalSupportLabellings
    (coupling : Q') (cutoff n : Nat) (support : List Nat) :
    List (List Nat × Q') :=
  (physicalLabellingsWithSupport cutoff n support).map
    (fun physical =>
      (fullPhysicalSpinCode n physical,
        parametricKPhysicalTerm coupling cutoff n physical))

theorem couplingParametricKComponentFamilyActivity_le_supportActivity
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff n : Nat) (support : List Nat)
    (hsupport : support ∈ cutoffOneFaceSupports n) :
    couplingParametricKSupportFamilyActivity coupling cutoff n
        (canonicalSurfaceFamily n support) ≤
      couplingParametricKSupportActivity coupling cutoff n support := by
  let source := supportFamilyLabellings cutoff n
    (canonicalSurfaceFamily n support)
  let target := couplingCodedPhysicalSupportLabellings
    coupling cutoff n support
  let recombine : List EdgeLabelling → EdgeLabelling :=
    fun family => binaryUnionLabels family
  let encode : List EdgeLabelling → List Nat × Q' :=
    fun family =>
      (fullPhysicalSpinCode n (recombine family),
        parametricKPhysicalTerm coupling cutoff n (recombine family))
  have hinjection :
      listQSum (parametricKPhysicalTermProduct coupling cutoff n) source ≤
        listQSum Prod.snd target := by
    apply listQSum_le_of_injective source target
      (parametricKPhysicalTermProduct coupling cutoff n)
      Prod.snd encode
    · exact supportFamilyLabellings_nodup cutoff n
        (canonicalSurfaceFamily n support)
    · intro family hfamily
      have hmatched :=
        (mem_supportFamilyLabellings_iff cutoff n
          (canonicalSurfaceFamily n support) family).mp hfamily
      have hphysical := canonicalSupportFamily_union_mem hsupport hmatched
      unfold target couplingCodedPhysicalSupportLabellings
      apply List.mem_map.mpr
      exact ⟨recombine family, hphysical, rfl⟩
    · intro left hleft right hright heq
      have hleftMatched :=
        (mem_supportFamilyLabellings_iff cutoff n
          (canonicalSurfaceFamily n support) left).mp hleft
      have hrightMatched :=
        (mem_supportFamilyLabellings_iff cutoff n
          (canonicalSurfaceFamily n support) right).mp hright
      have hleftPhysical :=
        canonicalSupportFamily_union_mem hsupport hleftMatched
      have hrightPhysical :=
        canonicalSupportFamily_union_mem hsupport hrightMatched
      have hunion : recombine left = recombine right :=
        fullPhysicalSpinCode_injective_on_bounded
          (mem_physicalLabellingsWithSupport_iff.mp hleftPhysical).1
          (mem_physicalLabellingsWithSupport_iff.mp hrightPhysical).1
          (congrArg Prod.fst heq)
      exact supportMatched_union_injective
        hleftMatched hrightMatched
        (canonicalSurfaceFamily_nodup n support)
        (canonicalSurfaceFamily_distinctDisjoint n support)
        hunion
    · intro family hfamily
      have hmatched :=
        (mem_supportFamilyLabellings_iff cutoff n
          (canonicalSurfaceFamily n support) family).mp hfamily
      have hseparated := supportMatched_linkSeparatedFamily hmatched
        (canonicalSurfaceFamily_nodup n support)
        (canonicalSurfaceFamily_distinctDisjoint n support)
        (canonicalSurfaceFamily_distinctSeparated n support)
      change parametricKPhysicalTermProduct coupling cutoff n family ≤
        parametricKPhysicalTerm coupling cutoff n
          (binaryUnionLabels family)
      exact Q'.ge_of_eqv
        (parametricKPhysicalTerm_unionLabels_factor
          coupling cutoff n family
          (supportMatched_kPhysicalFamily hmatched) hseparated)
    · intro coded hcoded
      unfold target couplingCodedPhysicalSupportLabellings at hcoded
      obtain ⟨physical, _, heq⟩ := List.mem_map.mp hcoded
      rw [← heq]
      exact parametricKPhysicalTerm_nonnegative
        hcoupling cutoff n physical
  have htarget : listQSum Prod.snd target ≈
      couplingParametricKSupportActivity
        coupling cutoff n support := by
    unfold target couplingCodedPhysicalSupportLabellings
      couplingParametricKSupportActivity
    rw [listQSum_map]
    exact Q'.eqv_refl _
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv
      (couplingParametricSupportFamilyLabellings_weight_sum
        coupling cutoff n (canonicalSurfaceFamily n support)))
    (Q'.le_trans' _ _ _ hinjection (Q'.le_of_eqv htarget))

private theorem eqv_of_le_of_ge_local {left right : Q'}
    (hle : left ≤ right) (hge : right ≤ left) : left ≈ right := by
  unfold Q'.eqv
  change left.num * (right.den : Int) ≤
    right.num * (left.den : Int) at hle
  change right.num * (left.den : Int) ≤
    left.num * (right.den : Int) at hge
  exact Int.le_antisymm hle hge

/-- Exact coupling-parametric component factorization of the complete finite
spin sum on one support. -/
theorem couplingParametricKSupportActivity_eqv_componentFamilyActivity
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff n : Nat) (support : List Nat)
    (hsupport : support ∈ cutoffOneFaceSupports n) :
    couplingParametricKSupportActivity coupling cutoff n support ≈
      couplingParametricKSupportFamilyActivity coupling cutoff n
        (canonicalSurfaceFamily n support) :=
  eqv_of_le_of_ge_local
    (couplingParametricKSupportActivity_le_componentFamilyActivity
      hcoupling cutoff n support)
    (couplingParametricKComponentFamilyActivity_le_supportActivity
      hcoupling cutoff n support hsupport)

/-! ## 4. Exact arbitrary-coupling support and compatible-gas reindexing -/

def couplingParametricKSupportPartition
    (coupling : Q') (cutoff n : Nat) : Q' :=
  listQSum (couplingParametricKSupportActivity coupling cutoff n)
    (cutoffOneFaceSupports n)

theorem couplingParametricKPhysicalPartition_eqv_supportPartition
    (coupling : Q') (cutoff n : Nat) :
    parametricKPhysicalPartition coupling cutoff n ≈
      couplingParametricKSupportPartition coupling cutoff n := by
  unfold parametricKPhysicalPartition couplingParametricKSupportPartition
  refine Q'.eqv_trans _ _ _
    (listQSum_perm _
      (boundedEdgeLabellings_perm_supportFibers cutoff n)) ?_
  unfold parametricKSupportFibers couplingParametricKSupportActivity
  exact listQSum_flatMap _ _ _

def couplingParametricKConnectedSupportGasPartition
    (coupling : Q') (cutoff n : Nat) : Q' :=
  listQSum (couplingParametricKSupportFamilyActivity coupling cutoff n)
    (canonicalConnectedSurfaceGas n)

def couplingParametricKAmbientOrderedSupportGasPartition
    (coupling : Q') (cutoff n : Nat) : Q' :=
  listQSum (couplingParametricKSupportFamilyActivity coupling cutoff n)
    (ambientOrderedExactGas n)

def couplingParametricKCompatibleSupportGasPartition
    (coupling : Q') (cutoff n : Nat) : Q' :=
  listQSum (couplingParametricKSupportFamilyActivity coupling cutoff n)
    (canonicalCompatibleAmbientFamilies n)

private theorem listQSum_map_eqv_local {A B : Type}
    (value : A → Q') (mappedValue : B → Q') (reindex : A → B) :
    ∀ source : List A,
      (∀ item, item ∈ source →
        value item ≈ mappedValue (reindex item)) →
      listQSum value source ≈
        listQSum mappedValue (source.map reindex)
  | [], _ => Q'.eqv_refl 0
  | head :: tail, h => by
      change value head + listQSum value tail ≈
        mappedValue (reindex head) +
          listQSum mappedValue (tail.map reindex)
      exact Q'.add_eqv_congr'
        (h head List.mem_cons_self)
        (listQSum_map_eqv_local value mappedValue reindex tail
          (fun item hitem =>
            h item (List.mem_cons_of_mem head hitem)))

theorem couplingParametricKSupportFamilyActivity_perm
    (coupling : Q') (cutoff n : Nat) :
    ∀ {left right : List (List Nat)}, left.Perm right →
      couplingParametricKSupportFamilyActivity coupling cutoff n left ≈
        couplingParametricKSupportFamilyActivity coupling cutoff n right
  | _, _, List.Perm.nil => Q'.eqv_refl 1
  | _, _, List.Perm.cons _ hperm =>
      Q'.mul_eqv_congr_left _ _ _
        (couplingParametricKSupportFamilyActivity_perm
          coupling cutoff n hperm)
  | _, _, List.Perm.swap first second rest => by
      change couplingParametricKSupportActivity coupling cutoff n second *
          (couplingParametricKSupportActivity coupling cutoff n first *
            couplingParametricKSupportFamilyActivity
              coupling cutoff n rest) ≈
        couplingParametricKSupportActivity coupling cutoff n first *
          (couplingParametricKSupportActivity coupling cutoff n second *
            couplingParametricKSupportFamilyActivity
              coupling cutoff n rest)
      refine Q'.eqv_trans _
        ((couplingParametricKSupportActivity coupling cutoff n second *
            couplingParametricKSupportActivity coupling cutoff n first) *
          couplingParametricKSupportFamilyActivity coupling cutoff n rest) _
        (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
      refine Q'.eqv_trans _
        ((couplingParametricKSupportActivity coupling cutoff n first *
            couplingParametricKSupportActivity coupling cutoff n second) *
          couplingParametricKSupportFamilyActivity coupling cutoff n rest) _
        (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv _ _)) ?_
      exact Q'.mul_assoc_eqv _ _ _
  | _, _, List.Perm.trans first second =>
      Q'.eqv_trans _ _ _
        (couplingParametricKSupportFamilyActivity_perm
          coupling cutoff n first)
        (couplingParametricKSupportFamilyActivity_perm
          coupling cutoff n second)

theorem couplingParametricKSupportPartition_eqv_connectedSupportGas
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff n : Nat) :
    couplingParametricKSupportPartition coupling cutoff n ≈
      couplingParametricKConnectedSupportGasPartition
        coupling cutoff n := by
  unfold couplingParametricKSupportPartition
    couplingParametricKConnectedSupportGasPartition
    canonicalConnectedSurfaceGas
  apply listQSum_map_eqv_local
  intro support hsupport
  exact couplingParametricKSupportActivity_eqv_componentFamilyActivity
    hcoupling cutoff n support hsupport

theorem couplingParametricKConnectedSupportGas_eqv_ambientOrdered
    (coupling : Q') (cutoff n : Nat) :
    couplingParametricKConnectedSupportGasPartition coupling cutoff n ≈
      couplingParametricKAmbientOrderedSupportGasPartition
        coupling cutoff n := by
  unfold couplingParametricKConnectedSupportGasPartition
    couplingParametricKAmbientOrderedSupportGasPartition
    ambientOrderedExactGas
  apply listQSum_map_eqv_local
  intro family hfamily
  exact couplingParametricKSupportFamilyActivity_perm
    coupling cutoff n (gasFamily_perm_ambientOrdered hfamily)

theorem couplingParametricKAmbientOrderedSupportGas_eqv_compatible
    (coupling : Q') (cutoff n : Nat) :
    couplingParametricKAmbientOrderedSupportGasPartition
        coupling cutoff n ≈
      couplingParametricKCompatibleSupportGasPartition
        coupling cutoff n := by
  unfold couplingParametricKAmbientOrderedSupportGasPartition
    couplingParametricKCompatibleSupportGasPartition
  exact listQSum_perm
    (couplingParametricKSupportFamilyActivity coupling cutoff n)
    (ambientOrderedExactGas_perm_compatibleFamilies n)

/-- Exact normalized-partition bridge from the arbitrary-coupling physical
spin foam to the coupling-parametric compatible support gas. -/
theorem couplingParametricKPhysicalPartition_eqv_compatibleSupportGas
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff n : Nat) :
    parametricKPhysicalPartition coupling cutoff n ≈
      couplingParametricKCompatibleSupportGasPartition
        coupling cutoff n :=
  Q'.eqv_trans _ _ _
    (couplingParametricKPhysicalPartition_eqv_supportPartition
      coupling cutoff n)
    (Q'.eqv_trans _ _ _
      (couplingParametricKSupportPartition_eqv_connectedSupportGas
        hcoupling cutoff n)
      (Q'.eqv_trans _ _ _
        (couplingParametricKConnectedSupportGas_eqv_ambientOrdered
          coupling cutoff n)
        (couplingParametricKAmbientOrderedSupportGas_eqv_compatible
          coupling cutoff n)))

#print axioms couplingParametricKSupportFamilyActivity_nonnegative
#print axioms couplingParametricSupportFamilyLabellings_weight_sum
#print axioms couplingParametricKSupportActivity_le_componentFamilyActivity
#print axioms couplingParametricKComponentFamilyActivity_le_supportActivity
#print axioms couplingParametricKSupportActivity_eqv_componentFamilyActivity
#print axioms couplingParametricKPhysicalPartition_eqv_supportPartition
#print axioms couplingParametricKSupportFamilyActivity_perm
#print axioms couplingParametricKSupportPartition_eqv_connectedSupportGas
#print axioms couplingParametricKConnectedSupportGas_eqv_ambientOrdered
#print axioms couplingParametricKAmbientOrderedSupportGas_eqv_compatible
#print axioms couplingParametricKPhysicalPartition_eqv_compatibleSupportGas

end YMGap.Continuum.Z4CouplingParametricSpinSummedSupportFactorization
