/-
# Kernel-checked finite rational LDL certificates

An external exact-arithmetic program may propose a factorization

  matrix i j = sum k, diagonal k * (lower i k * lower j k).

This module turns the finite Boolean check of that equation, together with
nonnegativity of every diagonal entry, into nonnegativity of the complete
rational quadratic form.  The soundness proof is the already verified finite
weighted-Gram-to-sum-of-squares theorem; the external producer is untrusted.

This is finite exact linear-algebra infrastructure.  It makes no spectral,
cutoff-uniform, infinite-volume, or continuum assertion by itself.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.FiniteClearedRationalSumCertificate

namespace YMGap.Continuum.FiniteRationalLDLCertificate

set_option maxRecDepth 300000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteClearedRationalSumCertificate
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

private theorem listQSum_id_map {A : Type} (value : A → Q') :
    ∀ items : List A,
    listQSum id (items.map value) = listQSum value items
  | [] => rfl
  | _ :: tail => by
      simp only [List.map, listQSum]
      rw [listQSum_id_map value tail]
      rfl

private theorem listQSum_append_local {A : Type} (value : A → Q') :
    ∀ left right,
    listQSum value (left ++ right) ≈
      listQSum value left + listQSum value right
  | [], right => Q'.eqv_symm (Q'.eqv_of_eq (Q'.zero_add' _))
  | head :: tail, right => by
      simp only [List.cons_append, listQSum]
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left _ _ _
          (listQSum_append_local value tail right))
        (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _))

private theorem listQSum_range_prefix_of_zero
    (value : Nat → Q') : ∀ (n m : Nat),
    m ≤ n →
    (∀ k, m ≤ k → k < n → value k ≈ 0) →
    listQSum value (List.range n) ≈
      listQSum value (List.range m)
  | 0, m, hm, _ => by
      have hmzero : m = 0 := Nat.eq_zero_of_le_zero hm
      subst m
      exact Q'.eqv_refl _
  | n + 1, m, hm, hzero => by
      have hdecision : Decidable (m = n + 1) := inferInstance
      cases hdecision with
      | isTrue heq =>
        subst m
        exact Q'.eqv_refl _
      | isFalse hne =>
        have hmn : m ≤ n := by omega
        rw [List.range_succ]
        refine Q'.eqv_trans _
          (listQSum value (List.range n) + listQSum value [n]) _
          (listQSum_append_local value (List.range n) [n]) ?_
        simp only [listQSum]
        refine Q'.eqv_trans _
          (listQSum value (List.range m) + (0 : Q')) _
          (Q'.add_eqv_congr'
            (listQSum_range_prefix_of_zero value n m hmn
              (fun k hmk hkn => hzero k hmk (Nat.lt.step hkn)))
            (Q'.eqv_trans _ _ _
              (Q'.eqv_of_eq (Q'.add_zero' (value n)))
              (hzero n hmn (Nat.lt_add_one n)))) ?_
        exact Q'.eqv_of_eq (Q'.add_zero' _)

/-- A literal finite rational matrix quadratic on coordinates `0, ..., n-1`. -/
def finiteMatrixQuadratic
    (n : Nat) (matrix : Nat → Nat → Q')
    (coefficient : Nat → Q') : Q' :=
  listQSum
    (fun i => listQSum
      (fun j => (coefficient i * coefficient j) * matrix i j)
      (List.range n))
    (List.range n)

/-- The matrix entry reconstructed from a proposed `L D Lᵀ` certificate. -/
def finiteLDLGram
    (n : Nat) (lower : Nat → Nat → Q')
    (diagonal : Nat → Q') (i j : Nat) : Q' :=
  listQSum
    (fun k => diagonal k * (lower i k * lower j k))
    (List.range n)

/-- The literal summand list underlying one reconstructed LDL entry. -/
def finiteLDLTerms
    (n : Nat) (lower : Nat → Nat → Q')
    (diagonal : Nat → Q') (i j : Nat) : List Q' :=
  (List.range n).map fun k =>
    diagonal k * (lower i k * lower j k)

/-- Only columns that can be nonzero in a lower-triangular LDL factor. -/
def finiteLDLPrefixTerms
    (lower : Nat → Nat → Q') (diagonal : Nat → Q')
    (i j : Nat) : List Q' :=
  (List.range (Nat.min (i + 1) (j + 1))).map fun k =>
    diagonal k * (lower i k * lower j k)

/-- Executable exact validation of one complete matrix row. -/
def finiteLDLRowCheck
    (n : Nat) (matrix lower : Nat → Nat → Q')
    (diagonal : Nat → Q') (row : Nat) : Bool :=
  (List.range n).all fun column =>
    decide (matrix row column ≈
      finiteLDLGram n lower diagonal row column)

/-- Executable exact validation of all matrix rows. -/
def finiteLDLRowsCheck
    (n : Nat) (matrix lower : Nat → Nat → Q')
    (diagonal : Nat → Q') : Bool :=
  (List.range n).all fun row =>
    finiteLDLRowCheck n matrix lower diagonal row

/-- Executable exact validation of all pivot signs. -/
def finiteLDLDiagonalCheck
    (n : Nat) (diagonal : Nat → Q') : Bool :=
  (List.range n).all fun k =>
    decide ((0 : Q') ≤ diagonal k)

/-- One exact LDL row checked with per-entry common denominators. -/
def finiteLDLClearedRowCheck
    (n : Nat) (matrix lower : Nat → Nat → Q')
    (diagonal : Nat → Q') (common : Nat → Nat → Nat)
    (row : Nat) : Bool :=
  (List.range n).all fun column =>
    decide (ClearedSumValid
      (matrix row column)
      (finiteLDLPrefixTerms lower diagonal row column)
      (common row column))

/-- All exact LDL rows checked with cleared integer arithmetic. -/
def finiteLDLClearedRowsCheck
    (n : Nat) (matrix lower : Nat → Nat → Q')
    (diagonal : Nat → Q') (common : Nat → Nat → Nat) : Bool :=
  (List.range n).all fun row =>
    finiteLDLClearedRowCheck n matrix lower diagonal common row

/-- Executable exact validation of all entries and all pivot signs. -/
def finiteLDLCheck
    (n : Nat) (matrix lower : Nat → Nat → Q')
    (diagonal : Nat → Q') : Bool :=
  finiteLDLRowsCheck n matrix lower diagonal &&
    finiteLDLDiagonalCheck n diagonal

theorem finiteLDLCheck_entries
    {n : Nat} {matrix lower : Nat → Nat → Q'}
    {diagonal : Nat → Q'}
    (hcheck : finiteLDLCheck n matrix lower diagonal = true)
    {i j : Nat} (hi : i < n) (hj : j < n) :
    matrix i j ≈ finiteLDLGram n lower diagonal i j := by
  have hall := (Bool.and_eq_true _ _).mp hcheck |>.1
  have hrow :=
    List.all_eq_true.mp hall i (List.mem_range.mpr hi)
  unfold finiteLDLRowCheck at hrow
  exact of_decide_eq_true
    (List.all_eq_true.mp hrow j (List.mem_range.mpr hj))

theorem finiteLDLCheck_diagonal_nonnegative
    {n : Nat} {matrix lower : Nat → Nat → Q'}
    {diagonal : Nat → Q'}
    (hcheck : finiteLDLCheck n matrix lower diagonal = true)
    {k : Nat} (hk : k < n) :
    (0 : Q') ≤ diagonal k := by
  have hall := (Bool.and_eq_true _ _).mp hcheck |>.2
  unfold finiteLDLDiagonalCheck at hall
  exact of_decide_eq_true
    (List.all_eq_true.mp hall k (List.mem_range.mpr hk))

theorem finiteLDLClearedRowsCheck_entries
    {n : Nat} {matrix lower : Nat → Nat → Q'}
    {diagonal : Nat → Q'} {common : Nat → Nat → Nat}
    (hcheck :
      finiteLDLClearedRowsCheck n matrix lower diagonal common = true)
    (htriangular : ∀ i k, i < k → lower i k = 0)
    {i j : Nat} (hi : i < n) (hj : j < n) :
    matrix i j ≈ finiteLDLGram n lower diagonal i j := by
  have hrow :=
    List.all_eq_true.mp hcheck i (List.mem_range.mpr hi)
  unfold finiteLDLClearedRowCheck at hrow
  have hvalid := of_decide_eq_true
    (List.all_eq_true.mp hrow j (List.mem_range.mpr hj))
  have hsound := ClearedSumValid.sound hvalid
  unfold finiteLDLPrefixTerms at hsound
  rw [listQSum_id_map] at hsound
  refine Q'.eqv_trans _ _ _ hsound ?_
  apply Q'.eqv_symm
  apply listQSum_range_prefix_of_zero
  · exact Nat.le_trans (Nat.min_le_left _ _)
      (Nat.succ_le_of_lt hi)
  · intro k hwidth hkn
    have hside : i < k ∨ j < k := by
      by_cases hij : i ≤ j
      · have hmin : Nat.min (i + 1) (j + 1) = i + 1 :=
          Nat.min_eq_left (by omega)
        rw [hmin] at hwidth
        exact Or.inl (by omega)
      · have hmin : Nat.min (i + 1) (j + 1) = j + 1 :=
          Nat.min_eq_right (by omega)
        rw [hmin] at hwidth
        exact Or.inr (by omega)
    rcases hside with hiUpper | hjUpper
    · have hinner : lower i k * lower j k ≈ 0 := by
        rw [htriangular i k hiUpper]
        exact Q'.zero_mul_eqv _
      exact Q'.eqv_trans _ (diagonal k * 0) _
        (Q'.mul_eqv_congr_left _ _ _ hinner)
        (Q'.mul_zero_eqv _)
    · have hinner : lower i k * lower j k ≈ 0 := by
        rw [htriangular j k hjUpper]
        exact Q'.mul_zero_eqv _
      exact Q'.eqv_trans _ (diagonal k * 0) _
        (Q'.mul_eqv_congr_left _ _ _ hinner)
        (Q'.mul_zero_eqv _)

theorem finiteMatrixQuadratic_eq_weightedGram
    {n : Nat} {matrix lower : Nat → Nat → Q'}
    {diagonal : Nat → Q'}
    (hentries : ∀ {i j : Nat}, i < n → j < n →
      matrix i j ≈ finiteLDLGram n lower diagonal i j)
    (coefficient : Nat → Q') :
    finiteMatrixQuadratic n matrix coefficient ≈
      weightedGramQuadratic
        (List.range n) (List.range n)
        diagonal lower coefficient := by
  unfold finiteMatrixQuadratic weightedGramQuadratic
  apply listQSum_congr_on
  intro i hi
  apply listQSum_congr_on
  intro j hj
  apply Q'.mul_eqv_congr_left
  exact hentries (List.mem_range.mp hi) (List.mem_range.mp hj)

/-- Soundness of an exact finite rational LDL certificate.  Every arithmetic
identity and every pivot sign is re-evaluated by Lean's kernel. -/
theorem finiteMatrixQuadratic_nonnegative_of_ldl_check
    {n : Nat} {matrix lower : Nat → Nat → Q'}
    {diagonal : Nat → Q'}
    (hcheck : finiteLDLCheck n matrix lower diagonal = true)
    (coefficient : Nat → Q') :
    (0 : Q') ≤ finiteMatrixQuadratic n matrix coefficient := by
  have hgram : (0 : Q') ≤
      weightedGramQuadratic
        (List.range n) (List.range n)
        diagonal lower coefficient :=
    weightedGramQuadratic_nonnegative
      (List.range n) (List.range n)
      diagonal lower coefficient
      (fun k hk =>
        finiteLDLCheck_diagonal_nonnegative hcheck
          (List.mem_range.mp hk))
  exact Q'.le_trans' _ _ _ hgram
    (Q'.ge_of_eqv
      (finiteMatrixQuadratic_eq_weightedGram
      (fun hi hj => finiteLDLCheck_entries hcheck hi hj)
        coefficient))

/-- Soundness from separately supplied entry and pivot certificates.  This is
the composition point used by independently compiled row shards. -/
theorem finiteMatrixQuadratic_nonnegative_of_ldl_entries
    {n : Nat} {matrix lower : Nat → Nat → Q'}
    {diagonal : Nat → Q'}
    (hentries : ∀ {i j : Nat}, i < n → j < n →
      matrix i j ≈ finiteLDLGram n lower diagonal i j)
    (hdiagonal : ∀ {k : Nat}, k < n → (0 : Q') ≤ diagonal k)
    (coefficient : Nat → Q') :
    (0 : Q') ≤ finiteMatrixQuadratic n matrix coefficient := by
  have hgram : (0 : Q') ≤
      weightedGramQuadratic
        (List.range n) (List.range n)
        diagonal lower coefficient :=
    weightedGramQuadratic_nonnegative
      (List.range n) (List.range n)
      diagonal lower coefficient
      (fun k hk => hdiagonal (List.mem_range.mp hk))
  exact Q'.le_trans' _ _ _ hgram
    (Q'.ge_of_eqv
      (finiteMatrixQuadratic_eq_weightedGram hentries coefficient))

/-- Soundness of cleared-denominator LDL rows plus the ordinary pivot-sign
check. -/
theorem finiteMatrixQuadratic_nonnegative_of_cleared_ldl_check
    {n : Nat} {matrix lower : Nat → Nat → Q'}
    {diagonal : Nat → Q'} {common : Nat → Nat → Nat}
    (hrows :
      finiteLDLClearedRowsCheck n matrix lower diagonal common = true)
    (htriangular : ∀ i k, i < k → lower i k = 0)
    (hdiagonal : finiteLDLDiagonalCheck n diagonal = true)
    (coefficient : Nat → Q') :
    (0 : Q') ≤ finiteMatrixQuadratic n matrix coefficient := by
  apply finiteMatrixQuadratic_nonnegative_of_ldl_entries
    (fun hi hj =>
      finiteLDLClearedRowsCheck_entries hrows htriangular hi hj)
    (fun hk => of_decide_eq_true
      (List.all_eq_true.mp hdiagonal _ (List.mem_range.mpr hk)))
    coefficient

end YMGap.Continuum.FiniteRationalLDLCertificate

#print axioms
  YMGap.Continuum.FiniteRationalLDLCertificate.finiteLDLCheck_entries
#print axioms
  YMGap.Continuum.FiniteRationalLDLCertificate.finiteMatrixQuadratic_nonnegative_of_ldl_check
