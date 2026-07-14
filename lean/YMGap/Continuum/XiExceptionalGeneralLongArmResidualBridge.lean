/-
# Aggregate normalization and residual bridge for the uniform long-arm block

This file aligns the uniform algebraic payer list with the occurrence-indexed
sharp carrier family.  It proves aggregate payment from pointwise exact
carrier normalizations, then packages any such paid block as a source-keyed
singleton mixed-repair allocator.  Consequently an entry already in the
three-branch residual is removed by the fourth (mixed-repair) partition.
-/

import YMGap.Continuum.XiExceptionalGeneralLongArmCarriers
import YMGap.Continuum.XiExceptionalFourthMixedRepair
import YMGap.Continuum.XiExceptionalBranchPacking

namespace YMGap.Continuum.XiExceptionalGeneralLongArmResidualBridge

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiExceptionalWeightedInjection
open YMGap.Continuum.XiExceptionalCarrierCode
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalSourceWeight
open YMGap.Continuum.XiExceptionalBranchPacking
open YMGap.Continuum.XiExceptionalFourthMixedRepair
open YMGap.Continuum.XiExceptionalThreeBranchClassificationFence
open YMGap.Continuum.XiExceptionalMultiReserveAlgebra
open YMGap.Continuum.XiExceptionalGeneralLongArmAlgebra
open YMGap.Continuum.XiExceptionalGeneralLongArmCarriers

local infix:50 " ≈ " => Q'.eqv

def indexValues (n : Nat) (f : Nat → Q') : List Q' :=
  (occurrenceIndices n).map f

theorem indexValues_length (n : Nat) (f : Nat → Q') :
    (indexValues n f).length = n := by
  simp [indexValues, occurrenceIndices_length]

theorem tagPrefix_indexValues (tag : Q') : ∀ (k n : Nat), k ≤ n →
    ∀ f : Nat → Q',
      tagPrefix tag k (indexValues n f) =
        indexValues n (fun i =>
          if decide (i < k) then tag * f i else f i)
  | 0, n, _, f => by
      unfold indexValues
      simp only [tagPrefix]
      apply List.map_congr_left
      intro i hi
      have hib := occurrenceIndices_bound hi
      simp
  | _ + 1, 0, h, _ => by omega
  | k + 1, n + 1, hkn, f => by
      unfold indexValues
      simp only [occurrenceIndices, List.map_cons, tagPrefix,
        List.map_map]
      have hzero : decide (0 < k + 1) = true := decide_eq_true (by omega)
      rw [hzero]
      simp only [if_true]
      apply congrArg (List.cons (tag * f 0))
      have ih := tagPrefix_indexValues tag k n (by omega)
        (fun i => f (i + 1))
      unfold indexValues at ih
      change tagPrefix tag k
          (List.map (fun i => f (i + 1)) (occurrenceIndices n)) =
        List.map (fun i =>
          if decide (i + 1 < k + 1) then tag * f (i + 1) else f (i + 1))
          (occurrenceIndices n)
      rw [ih]
      apply List.map_congr_left
      intro i hi
      have hdec : decide (i + 1 < k + 1) = decide (i < k) := by
        by_cases hik : i < k
        · rw [decide_eq_true hik, decide_eq_true (by omega)]
        · rw [decide_eq_false hik, decide_eq_false (by omega)]
      rw [hdec]

def rawPayerAt (E O : Q') (side : LongParity) (i : Nat)
    (evenAt oddAt : Nat → Q') : Q' :=
  match side with
  | .even => (E * O) * (O * qCube (evenAt i))
  | .odd => (E * O) * (E * qCube (oddAt i))

def indexedPayerAt (k : Nat) (a1 a2 E O : Q')
    (side : LongParity) (i : Nat) (evenAt oddAt : Nat → Q') : Q' :=
  let raw := rawPayerAt E O side i evenAt oddAt
  match side with
  | .even => if decide (i < k) then a1 * raw else raw
  | .odd => if decide (i < k) then a2 * raw else raw

theorem taggedSidePayers_eq_indexValues
    (k n : Nat) (hkn : k ≤ n) (a1 a2 E O : Q')
    (evenAt oddAt : Nat → Q') (side : LongParity) :
    (match side with
      | .even => tagPrefix a1 k
          (sidePayers (E * O) O (indexValues n evenAt))
      | .odd => tagPrefix a2 k
          (sidePayers (E * O) E (indexValues n oddAt))) =
      indexValues n (fun i =>
        indexedPayerAt k a1 a2 E O side i evenAt oddAt) := by
  cases side
  · have heven :
        sidePayers (E * O) O (indexValues n evenAt) =
          indexValues n (fun i => (E * O) * (O * qCube (evenAt i))) := by
        simp [sidePayers, indexValues, Function.comp_def]
    rw [heven]
    simp only [indexedPayerAt, rawPayerAt]
    exact tagPrefix_indexValues a1 k n hkn _
  · have hodd :
        sidePayers (E * O) E (indexValues n oddAt) =
          indexValues n (fun i => (E * O) * (E * qCube (oddAt i))) := by
        simp [sidePayers, indexValues, Function.comp_def]
    rw [hodd]
    simp only [indexedPayerAt, rawPayerAt]
    exact tagPrefix_indexValues a2 k n hkn _

theorem uniformPayers_eq_indexed
    (k : Nat) (a1 a2 : Q') (evenAt oddAt : Nat → Q') :
    uniformPayers k a1 a2
        (indexValues (longCount k) evenAt)
        (indexValues (longCount k) oddAt) =
      shortSquare a1 a2 ::
        (indexValues (longCount k) (fun i =>
            indexedPayerAt k a1 a2
              (qProd (indexValues (longCount k) evenAt))
              (qProd (indexValues (longCount k) oddAt))
              .even i evenAt oddAt) ++
          indexValues (longCount k) (fun i =>
            indexedPayerAt k a1 a2
              (qProd (indexValues (longCount k) evenAt))
              (qProd (indexValues (longCount k) oddAt))
              .odd i evenAt oddAt)) := by
  unfold uniformPayers
  have heven := taggedSidePayers_eq_indexValues k (longCount k) (by
      unfold longCount; omega) a1 a2
      (qProd (indexValues (longCount k) evenAt))
      (qProd (indexValues (longCount k) oddAt)) evenAt oddAt .even
  have hodd := taggedSidePayers_eq_indexValues k (longCount k) (by
      unfold longCount; omega) a1 a2
      (qProd (indexValues (longCount k) evenAt))
      (qProd (indexValues (longCount k) oddAt)) evenAt oddAt .odd
  simp only at heven hodd
  rw [heven, hodd]

variable {L : Lattice} [DecidableEq L.Plaquette]

def uniformRepairBlock (Gamma : List (Polymer L)) (k : Nat)
    (hGamma : Gamma.length = ambientCount k)
    (shortCode : OccCarrierXiCodeAt Gamma) :
    List (OccCarrierXiCodeAt Gamma) :=
  shortCode :: longCarrierFamily Gamma k hGamma

omit [DecidableEq L.Plaquette] in
theorem uniformRepairBlock_nodup
    (Gamma : List (Polymer L)) (k : Nat)
    (hGamma : Gamma.length = ambientCount k)
    (shortCode : OccCarrierXiCodeAt Gamma)
    (hshortFresh : shortCode ∉ longCarrierFamily Gamma k hGamma) :
    (uniformRepairBlock Gamma k hGamma shortCode).Nodup := by
  exact List.nodup_cons.mpr
    ⟨hshortFresh, longCarrierFamily_nodup Gamma k hGamma⟩

omit [DecidableEq L.Plaquette] in
theorem uniformRepairBlock_mem
    (Gamma : List (Polymer L)) (k : Nat)
    (hGamma : Gamma.length = ambientCount k)
    (shortCode : OccCarrierXiCodeAt Gamma)
    (hshortMem : shortCode ∈ occurrenceCarrierXiCodes Gamma)
    (code : OccCarrierXiCodeAt Gamma)
    (hcode : code ∈ uniformRepairBlock Gamma k hGamma shortCode) :
    code ∈ occurrenceCarrierXiCodes Gamma := by
  rcases List.mem_cons.mp hcode with rfl | hlong
  · exact hshortMem
  · exact longCarrierFamily_mem Gamma k hGamma code hlong

omit [DecidableEq L.Plaquette] in
theorem uniformRepairBlock_canonical
    (Gamma : List (Polymer L)) (k : Nat)
    (hGamma : Gamma.length = ambientCount k) :
    uniformRepairBlock Gamma k hGamma (shortCarrierCode Gamma k hGamma) =
      repairCarrierFamily Gamma k hGamma := rfl

omit [DecidableEq L.Plaquette] in
private theorem side_sum_eqv
    (Gamma : List (Polymer L)) (k : Nat)
    (hGamma : Gamma.length = ambientCount k)
    (weight : OccCarrierXiCodeAt Gamma → Q')
    (common a1 a2 E O : Q') (evenAt oddAt : Nat → Q')
    (side : LongParity)
    (hcode : ∀ i, i < longCount k →
      weight (longCarrierCode Gamma k hGamma side i) ≈
        common * indexedPayerAt k a1 a2 E O side i evenAt oddAt) :
    qListSum weight (sideCarrierCodes Gamma k hGamma side) ≈
      qListSum (fun i => common *
        indexedPayerAt k a1 a2 E O side i evenAt oddAt)
        (occurrenceIndices (longCount k)) := by
  unfold sideCarrierCodes
  rw [qListSum_map]
  apply qListSum_eqv_congr
  intro i hi
  exact hcode i (occurrenceIndices_bound hi)

omit [DecidableEq L.Plaquette] in
theorem uniformRepairBlock_weight_eqv
    (Gamma : List (Polymer L)) (k : Nat)
    (hGamma : Gamma.length = ambientCount k)
    (shortCode : OccCarrierXiCodeAt Gamma)
    (weight : OccCarrierXiCodeAt Gamma → Q')
    (common a1 a2 : Q') (evenAt oddAt : Nat → Q')
    (hshort : weight shortCode ≈ common * shortSquare a1 a2)
    (hlong : ∀ side i, i < longCount k →
      weight (longCarrierCode Gamma k hGamma side i) ≈
        common * indexedPayerAt k a1 a2
          (qProd (indexValues (longCount k) evenAt))
          (qProd (indexValues (longCount k) oddAt))
          side i evenAt oddAt) :
    qListSum weight (uniformRepairBlock Gamma k hGamma shortCode) ≈
      common * qListSum id
        (uniformPayers k a1 a2
          (indexValues (longCount k) evenAt)
          (indexValues (longCount k) oddAt)) := by
  let E := qProd (indexValues (longCount k) evenAt)
  let O := qProd (indexValues (longCount k) oddAt)
  let evenP := indexValues (longCount k) (fun i =>
    indexedPayerAt k a1 a2 E O .even i evenAt oddAt)
  let oddP := indexValues (longCount k) (fun i =>
    indexedPayerAt k a1 a2 E O .odd i evenAt oddAt)
  have heven := side_sum_eqv Gamma k hGamma weight common a1 a2 E O
    evenAt oddAt .even (fun i hi => hlong .even i hi)
  have hodd := side_sum_eqv Gamma k hGamma weight common a1 a2 E O
    evenAt oddAt .odd (fun i hi => hlong .odd i hi)
  have hlongSum :
      qListSum weight (longCarrierFamily Gamma k hGamma) ≈
        common * qListSum id (evenP ++ oddP) := by
    refine Q'.eqv_trans _ _ _
      (qListSum_append weight
        (sideCarrierCodes Gamma k hGamma .even)
        (sideCarrierCodes Gamma k hGamma .odd)) ?_
    refine Q'.eqv_trans _
      (qListSum (fun i => common *
          indexedPayerAt k a1 a2 E O .even i evenAt oddAt)
          (occurrenceIndices (longCount k)) +
        qListSum (fun i => common *
          indexedPayerAt k a1 a2 E O .odd i evenAt oddAt)
          (occurrenceIndices (longCount k))) _
      (add_eqv_congr_both _ _ _ _ heven hodd) ?_
    refine Q'.eqv_trans _
      (common * qListSum id evenP + common * qListSum id oddP) _ ?_ ?_
    · exact add_eqv_congr_both _ _ _ _
        (by
          simpa only [evenP, indexValues, qListSum_map, id_eq,
            Function.comp_apply] using
            (qListSum_const_mul common id evenP))
        (by
          simpa only [oddP, indexValues, qListSum_map, id_eq,
            Function.comp_apply] using
            (qListSum_const_mul common id oddP))
    refine Q'.eqv_trans _
      (common * (qListSum id evenP + qListSum id oddP)) _
      (Q'.eqv_symm (Q'.mul_add_eqv common _ _)) ?_
    exact Q'.mul_eqv_congr_left common _ _
      (Q'.eqv_symm (qListSum_append id evenP oddP))
  simp only [uniformRepairBlock, qListSum_cons]
  refine Q'.eqv_trans _
    (common * shortSquare a1 a2 + common * qListSum id (evenP ++ oddP)) _
    (add_eqv_congr_both _ _ _ _ hshort hlongSum) ?_
  refine Q'.eqv_trans _
    (common * (shortSquare a1 a2 + qListSum id (evenP ++ oddP))) _
    (Q'.eqv_symm (Q'.mul_add_eqv common _ _)) ?_
  apply Q'.mul_eqv_congr_left common
  rw [uniformPayers_eq_indexed k a1 a2 evenAt oddAt]
  simp only [qListSum_cons, id_eq]
  exact Q'.eqv_refl _

omit [DecidableEq L.Plaquette] in
theorem source_le_uniformRepairBlock
    (Gamma : List (Polymer L)) (k : Nat)
    (hGamma : Gamma.length = ambientCount k)
    (shortCode : OccCarrierXiCodeAt Gamma)
    (weight : OccCarrierXiCodeAt Gamma → Q')
    (source common a1 a2 : Q') (evenAt oddAt : Nat → Q')
    (hsource : source ≈ common *
      uniformSource a1 a2
        (indexValues (longCount k) evenAt)
        (indexValues (longCount k) oddAt))
    (hblock : qListSum weight
        (uniformRepairBlock Gamma k hGamma shortCode) ≈
      common * qListSum id
        (uniformPayers k a1 a2
          (indexValues (longCount k) evenAt)
          (indexValues (longCount k) oddAt)))
    (hcommon : (0 : Q') ≤ common)
    (ha1 : (0 : Q') ≤ a1) (ha2 : (0 : Q') ≤ a2)
    (heven : ∀ i, i < longCount k → (0 : Q') ≤ evenAt i)
    (hodd : ∀ i, i < longCount k → (0 : Q') ≤ oddAt i) :
    source ≤ qListSum weight
      (uniformRepairBlock Gamma k hGamma shortCode) := by
  have hevenLength := indexValues_length (longCount k) evenAt
  have hoddLength := indexValues_length (longCount k) oddAt
  have hpay := uniformPayers_pay k a1 a2
    (indexValues (longCount k) evenAt)
    (indexValues (longCount k) oddAt)
    (by rw [hevenLength]; rfl) (by rw [hoddLength]; rfl)
    ha1 ha2
    (by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      exact heven i (occurrenceIndices_bound hi))
    (by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      exact hodd i (occurrenceIndices_bound hi))
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ common hpay hcommon
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hsource)
    (Q'.le_trans' _ _ _ hscaled (Q'.ge_of_eqv hblock))

/-! ## Generic source-keyed residual connection -/

structure PaidResidualBlock
    (qP b1 b2 : Polymer L → Bool)
    (Gamma : List (Polymer L))
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) where
  block : List (OccCarrierXiCodeAt Gamma)
  block_nodup : block.Nodup
  block_mem : ∀ code, code ∈ block →
    code ∈ occurrenceCarrierXiCodes Gamma
  source_le : ∀ (w : Q'), (0 : Q') ≤ w →
    ∀ label : L.Plaquette → Rep,
      occurrencePairWeight w qP b1 b2 Gamma label entry.1 ≤
        qListSum
          (occurrenceCarrierXiCodeWeight w qP b1 b2 Gamma label) block

/-- All local normalization facts needed to turn the canonical uniform carrier
family into an actual paid residual block.  Concrete ear geometries discharge
these fields by reduction of their finite compatibility and activity words;
the global exponent and target accounting are supplied by the preceding
uniform theorems. -/
structure UniformLongArmNormalization
    (qP b1 b2 : Polymer L → Bool)
    (Gamma : List (Polymer L)) (k : Nat)
    (hGamma : Gamma.length = ambientCount k)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) where
  common : Q' → (L.Plaquette → Rep) → Q'
  a1 : Q' → (L.Plaquette → Rep) → Q'
  a2 : Q' → (L.Plaquette → Rep) → Q'
  evenAt : Q' → (L.Plaquette → Rep) → Nat → Q'
  oddAt : Q' → (L.Plaquette → Rep) → Nat → Q'
  source_eqv : ∀ w label,
    occurrencePairWeight w qP b1 b2 Gamma label entry.1 ≈
      common w label *
        uniformSource (a1 w label) (a2 w label)
          (indexValues (longCount k) (evenAt w label))
          (indexValues (longCount k) (oddAt w label))
  short_eqv : ∀ w label,
    occurrenceCarrierXiCodeWeight w qP b1 b2 Gamma label
        (shortCarrierCode Gamma k hGamma) ≈
      common w label * shortSquare (a1 w label) (a2 w label)
  long_eqv : ∀ w label side i, i < longCount k →
    occurrenceCarrierXiCodeWeight w qP b1 b2 Gamma label
        (longCarrierCode Gamma k hGamma side i) ≈
      common w label *
        indexedPayerAt k (a1 w label) (a2 w label)
          (qProd (indexValues (longCount k) (evenAt w label)))
          (qProd (indexValues (longCount k) (oddAt w label)))
          side i (evenAt w label) (oddAt w label)
  common_nonneg : ∀ {w}, (0 : Q') ≤ w → ∀ label,
    (0 : Q') ≤ common w label
  a1_nonneg : ∀ {w}, (0 : Q') ≤ w → ∀ label,
    (0 : Q') ≤ a1 w label
  a2_nonneg : ∀ {w}, (0 : Q') ≤ w → ∀ label,
    (0 : Q') ≤ a2 w label
  even_nonneg : ∀ {w}, (0 : Q') ≤ w → ∀ label i,
    i < longCount k → (0 : Q') ≤ evenAt w label i
  odd_nonneg : ∀ {w}, (0 : Q') ≤ w → ∀ label i,
    i < longCount k → (0 : Q') ≤ oddAt w label i

def uniformPaidResidualBlock
    {qP b1 b2 : Polymer L → Bool} {Gamma : List (Polymer L)} {k : Nat}
    {hGamma : Gamma.length = ambientCount k}
    {entry : ExceptionalSourceEntry Gamma qP b1 b2}
    (norm : UniformLongArmNormalization qP b1 b2 Gamma k hGamma entry) :
    PaidResidualBlock qP b1 b2 Gamma entry where
  block := repairCarrierFamily Gamma k hGamma
  block_nodup := repairCarrierFamily_nodup Gamma k hGamma
  block_mem := fun code hcode =>
    repairCarrierFamily_mem Gamma k hGamma code hcode
  source_le := by
    intro w hw label
    have hblock := uniformRepairBlock_weight_eqv Gamma k hGamma
      (shortCarrierCode Gamma k hGamma)
      (occurrenceCarrierXiCodeWeight w qP b1 b2 Gamma label)
      (norm.common w label) (norm.a1 w label) (norm.a2 w label)
      (norm.evenAt w label) (norm.oddAt w label)
      (norm.short_eqv w label)
      (fun side i hi => norm.long_eqv w label side i hi)
    exact source_le_uniformRepairBlock Gamma k hGamma
      (shortCarrierCode Gamma k hGamma)
      (occurrenceCarrierXiCodeWeight w qP b1 b2 Gamma label)
      (occurrencePairWeight w qP b1 b2 Gamma label entry.1)
      (norm.common w label) (norm.a1 w label) (norm.a2 w label)
      (norm.evenAt w label) (norm.oddAt w label)
      (norm.source_eqv w label) hblock
      (norm.common_nonneg hw label)
      (norm.a1_nonneg hw label) (norm.a2_nonneg hw label)
      (norm.even_nonneg hw label) (norm.odd_nonneg hw label)

def residualSourceKey
    {qP b1 b2 : Polymer L → Bool} {Gamma : List (Polymer L)}
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    OccCarrierXiCodeAt Gamma :=
  exceptionalBranchCarrierCode Gamma qP b1 b2 entry

theorem residualSourceKey_injective
    {qP b1 b2 : Polymer L → Bool} {Gamma : List (Polymer L)}
    {a b : ExceptionalSourceEntry Gamma qP b1 b2}
    (h : residualSourceKey a = residualSourceKey b) : a = b :=
  exceptionalBranchCarrierCode_injective Gamma qP b1 b2 a b h

def paidResidualTestB
    {qP b1 b2 : Polymer L → Bool} {Gamma : List (Polymer L)}
    (entry other : ExceptionalSourceEntry Gamma qP b1 b2) : Bool :=
  decide (residualSourceKey other = residualSourceKey entry)

theorem paidResidualTestB_true_iff
    {qP b1 b2 : Polymer L → Bool} {Gamma : List (Polymer L)}
    (entry other : ExceptionalSourceEntry Gamma qP b1 b2) :
    paidResidualTestB entry other = true ↔ other = entry := by
  constructor
  · intro h
    exact residualSourceKey_injective (of_decide_eq_true h)
  · intro h
    subst other
    exact decide_eq_true rfl

def paidResidualAllocator
    {qP b1 b2 : Polymer L → Bool} {Gamma : List (Polymer L)}
    {entry : ExceptionalSourceEntry Gamma qP b1 b2}
    (cert : PaidResidualBlock qP b1 b2 Gamma entry) :
    MixedRepairAllocator Gamma qP b1 b2 where
  test := paidResidualTestB entry
  block := fun _ => cert.block
  block_nodup := by intro _ _; exact cert.block_nodup
  block_mem := by intro _ _ code hc; exact cert.block_mem code hc
  blocks_disjoint := by
    intro a ha b hb hab
    have hae := (paidResidualTestB_true_iff entry a).mp ha
    have hbe := (paidResidualTestB_true_iff entry b).mp hb
    exact False.elim (hab (hae.trans hbe.symm))
  source_le_block := by
    intro w hw label other ht
    have he := (paidResidualTestB_true_iff entry other).mp ht
    subst other
    exact cert.source_le w hw label

theorem paid_entry_mem_mixedRepairSource
    {qP b1 b2 : Polymer L → Bool} {Gamma : List (Polymer L)}
    {entry : ExceptionalSourceEntry Gamma qP b1 b2}
    (cert : PaidResidualBlock qP b1 b2 Gamma entry)
    (hresidual : entry ∈ threeBranchResidualSource Gamma qP b1 b2) :
    entry ∈ mixedRepairSource (paidResidualAllocator cert) := by
  apply List.mem_filter.mpr
  exact ⟨hresidual, (paidResidualTestB_true_iff entry entry).mpr rfl⟩

theorem paid_entry_not_mem_fourBranchResidual
    {qP b1 b2 : Polymer L → Bool} {Gamma : List (Polymer L)}
    {entry : ExceptionalSourceEntry Gamma qP b1 b2}
    (cert : PaidResidualBlock qP b1 b2 Gamma entry) :
    entry ∉ fourBranchResidualSource (paidResidualAllocator cert) := by
  intro h
  have ht := (fourBranchResidualSource_tests Gamma qP b1 b2
    (paidResidualAllocator cert) entry h).2.2.2
  have hone : (paidResidualAllocator cert).test entry = true :=
    (paidResidualTestB_true_iff entry entry).mpr rfl
  rw [hone] at ht
  cases ht

def uniformResidualAllocator
    {qP b1 b2 : Polymer L → Bool} {Gamma : List (Polymer L)} {k : Nat}
    {hGamma : Gamma.length = ambientCount k}
    {entry : ExceptionalSourceEntry Gamma qP b1 b2}
    (norm : UniformLongArmNormalization qP b1 b2 Gamma k hGamma entry) :
    MixedRepairAllocator Gamma qP b1 b2 :=
  paidResidualAllocator (uniformPaidResidualBlock norm)

theorem normalized_entry_mem_mixedRepairSource
    {qP b1 b2 : Polymer L → Bool} {Gamma : List (Polymer L)} {k : Nat}
    {hGamma : Gamma.length = ambientCount k}
    {entry : ExceptionalSourceEntry Gamma qP b1 b2}
    (norm : UniformLongArmNormalization qP b1 b2 Gamma k hGamma entry)
    (hresidual : entry ∈ threeBranchResidualSource Gamma qP b1 b2) :
    entry ∈ mixedRepairSource (uniformResidualAllocator norm) :=
  paid_entry_mem_mixedRepairSource (uniformPaidResidualBlock norm) hresidual

theorem normalized_entry_not_mem_fourBranchResidual
    {qP b1 b2 : Polymer L → Bool} {Gamma : List (Polymer L)} {k : Nat}
    {hGamma : Gamma.length = ambientCount k}
    {entry : ExceptionalSourceEntry Gamma qP b1 b2}
    (norm : UniformLongArmNormalization qP b1 b2 Gamma k hGamma entry) :
    entry ∉ fourBranchResidualSource (uniformResidualAllocator norm) :=
  paid_entry_not_mem_fourBranchResidual (uniformPaidResidualBlock norm)

#print axioms tagPrefix_indexValues
#print axioms uniformPayers_eq_indexed
#print axioms uniformRepairBlock_nodup
#print axioms uniformRepairBlock_weight_eqv
#print axioms source_le_uniformRepairBlock
#print axioms uniformPaidResidualBlock
#print axioms residualSourceKey_injective
#print axioms paidResidualTestB_true_iff
#print axioms paid_entry_mem_mixedRepairSource
#print axioms paid_entry_not_mem_fourBranchResidual
#print axioms normalized_entry_mem_mixedRepairSource
#print axioms normalized_entry_not_mem_fourBranchResidual

end YMGap.Continuum.XiExceptionalGeneralLongArmResidualBridge
