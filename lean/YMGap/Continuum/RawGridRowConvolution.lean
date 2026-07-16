/-
# Row-wise Cauchy products for raw-polynomial certificates

Dense raw products are expensive to normalize as one polynomial.  This file
keeps a graded polynomial as a list of exponent rows and forms its Cauchy
product without ever joining or canonicalizing the complete product.  Each
output row can therefore be checked independently, while the theorem below
recovers the exact product semantics of the whole row family.
-/

import YMGap.Continuum.RawGridSemanticTransport

namespace YMGap.Continuum.RawGridRowConvolution

open YMGap.Constructive
open YMGap.Continuum.RawGridSemanticTransport

local infix:50 " ≈ " => Q'.eqv

abbrev RawPoly := RingNormaliser.RawPoly

/-- Erase syntactic zero-coefficient terms before bucketing a generated grid.
This is semantic preprocessing only; no measured or approximate value enters. -/
def removeZeroRaw : RawPoly → RawPoly
  | [] => []
  | (monomial, coefficient) :: rest =>
      if coefficient = 0 then removeZeroRaw rest
      else (monomial, coefficient) :: removeZeroRaw rest

theorem evalRaw_removeZeroRaw (rho : Nat → Q') : ∀ raw,
    RingNormaliser.evalRaw rho (removeZeroRaw raw) ≈
      RingNormaliser.evalRaw rho raw
  | [] => Q'.eqv_refl 0
  | (monomial, coefficient) :: rest => by
      by_cases hzero : coefficient = 0
      · subst coefficient
        simp only [removeZeroRaw, ↓reduceIte]
        have ih := evalRaw_removeZeroRaw rho rest
        have hzeroMul :
            (0 : Q') * RingNormaliser.evalMono rho monomial ≈ 0 :=
          Q'.zero_mul_eqv _
        have hzeroAdd :
            (0 : Q') * RingNormaliser.evalMono rho monomial +
                RingNormaliser.evalRaw rho rest ≈
              RingNormaliser.evalRaw rho rest := by
          refine Q'.eqv_trans _
            ((0 : Q') + RingNormaliser.evalRaw rho rest) _
            (Q'.add_eqv_congr_right _ _ _ hzeroMul) ?_
          exact RingNormaliser.eqv_of_eq
            (Q'.zero_add' (RingNormaliser.evalRaw rho rest))
        exact Q'.eqv_trans _ _ _ ih (Q'.eqv_symm hzeroAdd)
      · simp only [removeZeroRaw, hzero, ↓reduceIte]
        exact Q'.add_eqv_congr_left
          (Q'.ofInt coefficient * RingNormaliser.evalMono rho monomial)
          _ _ (evalRaw_removeZeroRaw rho rest)

/-- A constant raw row, used to scale every row of a certificate family. -/
def scalarRawRow (coefficient : Int) : RawPoly := [([], coefficient)]

theorem evalRaw_scalarRawRow (rho : Nat → Q') (coefficient : Int) :
    RingNormaliser.evalRaw rho (scalarRawRow coefficient) ≈
      Q'.ofInt coefficient := by
  exact Q'.eqv_trans _ (Q'.ofInt coefficient * 1) _
    (evalRaw_singleton rho [] coefficient)
    (Q'.mul_one_eqv (Q'.ofInt coefficient))

/-- Multiply one raw row by every row in a graded family. -/
def rawMulRows (left : RawPoly) : List RawPoly → List RawPoly
  | [] => []
  | right :: rights =>
      RingNormaliser.rawMul left right :: rawMulRows left rights

theorem rawMulRows_length (left : RawPoly) : ∀ rows,
    (rawMulRows left rows).length = rows.length
  | [] => rfl
  | _ :: rows => by
      change Nat.succ (rawMulRows left rows).length = Nat.succ rows.length
      rw [rawMulRows_length left rows]

/-- Cauchy product of two row families.  The head row has grade zero, so the
recursive tail contribution is shifted by one empty row. -/
def rawRowsConvolution : List RawPoly → List RawPoly → List RawPoly
  | [], _ => []
  | _, [] => []
  | left :: lefts, right =>
      appendRawRows (rawMulRows left right)
        ([] :: rawRowsConvolution lefts right)

theorem appendRawRows_length : ∀ left right,
    (appendRawRows left right).length = Nat.max left.length right.length
  | [], right => by
      change right.length = Nat.max 0 right.length
      exact (Nat.max_eq_right (Nat.zero_le _)).symm
  | _ :: lefts, [] => by
      change Nat.succ lefts.length = Nat.max (Nat.succ lefts.length) 0
      exact (Nat.max_eq_left (Nat.zero_le _)).symm
  | _ :: lefts, _ :: rights => by
      change Nat.succ (appendRawRows lefts rights).length =
        Nat.max (Nat.succ lefts.length) (Nat.succ rights.length)
      rw [appendRawRows_length lefts rights]
      exact (Nat.succ_max_succ lefts.length rights.length).symm

theorem rawRowsConvolution_length_of_nonempty : ∀ left right,
    left ≠ [] → right ≠ [] →
      (rawRowsConvolution left right).length =
        left.length + right.length - 1 := by
  intro left
  induction left with
  | nil =>
      intro right hleft
      exact False.elim (hleft rfl)
  | cons left lefts ih =>
      intro right hleft hright
      cases right with
      | nil => exact False.elim (hright rfl)
      | cons right rights =>
          cases lefts with
          | nil =>
              change
                (appendRawRows
                  (rawMulRows left (right :: rights)) [[]]).length =
                Nat.succ 0 + Nat.succ rights.length - 1
              rw [appendRawRows_length, rawMulRows_length]
              change Nat.max (Nat.succ rights.length) 1 =
                Nat.succ 0 + Nat.succ rights.length - 1
              have hmax : Nat.max (Nat.succ rights.length) 1 =
                  Nat.succ rights.length := Nat.max_eq_left (by omega)
              rw [hmax]
              omega
          | cons next nexts =>
              have htail := ih (right :: rights)
                (by simp) (by simp)
              change
                (appendRawRows
                  (rawMulRows left (right :: rights))
                  ([] :: rawRowsConvolution
                    (next :: nexts) (right :: rights))).length =
                  Nat.succ (Nat.succ nexts.length) +
                    Nat.succ rights.length - 1
              rw [appendRawRows_length, rawMulRows_length]
              change Nat.max (Nat.succ rights.length)
                  (Nat.succ
                    (rawRowsConvolution
                      (next :: nexts) (right :: rights)).length) =
                Nat.succ (Nat.succ nexts.length) +
                  Nat.succ rights.length - 1
              rw [htail]
              change Nat.max (Nat.succ rights.length)
                  (Nat.succ
                    (Nat.succ nexts.length + Nat.succ rights.length - 1)) =
                Nat.succ (Nat.succ nexts.length) +
                  Nat.succ rights.length - 1
              have hmax : Nat.max (Nat.succ rights.length)
                    (Nat.succ
                      (Nat.succ nexts.length + Nat.succ rights.length - 1)) =
                  Nat.succ
                    (Nat.succ nexts.length + Nat.succ rights.length - 1) :=
                Nat.max_eq_right (by omega)
              rw [hmax]
              omega

theorem evalRawRows_rawMulRows (rho : Nat → Q') (left : RawPoly) :
    ∀ rows,
      evalRawRows rho (rawMulRows left rows) ≈
        RingNormaliser.evalRaw rho left * evalRawRows rho rows
  | [] => Q'.eqv_symm (Q'.mul_zero_eqv _)
  | right :: rights => by
      have hhead := RingNormaliser.evalRaw_rawMul rho left right
      have htail := evalRawRows_rawMulRows rho left rights
      refine Q'.eqv_trans _
        (RingNormaliser.evalRaw rho left *
            RingNormaliser.evalRaw rho right +
          RingNormaliser.evalRaw rho left * evalRawRows rho rights) _
        (Q'.add_eqv_congr' hhead htail) ?_
      exact Q'.eqv_symm
        (Q'.mul_add_eqv
          (RingNormaliser.evalRaw rho left)
          (RingNormaliser.evalRaw rho right)
          (evalRawRows rho rights))

theorem evalRawRows_empty_cons (rho : Nat → Q') (rows : List RawPoly) :
    evalRawRows rho ([] :: rows) ≈ evalRawRows rho rows := by
  exact RingNormaliser.eqv_of_eq (Q'.zero_add' (evalRawRows rho rows))

/-- Evaluation of the row-wise convolution is exactly the product of the two
row-family evaluations. -/
theorem evalRawRows_rawRowsConvolution (rho : Nat → Q') :
    ∀ left right,
      evalRawRows rho (rawRowsConvolution left right) ≈
        evalRawRows rho left * evalRawRows rho right
  | [], right => Q'.eqv_symm (Q'.zero_mul_eqv _)
  | _ :: _, [] => Q'.eqv_symm (Q'.mul_zero_eqv _)
  | left :: lefts, rightHead :: rightTail => by
      let right := rightHead :: rightTail
      have happend := evalRawRows_appendRawRows rho
        (rawMulRows left right)
        ([] :: rawRowsConvolution lefts right)
      have hleft := evalRawRows_rawMulRows rho left right
      have hshift := evalRawRows_empty_cons rho
        (rawRowsConvolution lefts right)
      have htail := evalRawRows_rawRowsConvolution rho lefts right
      refine Q'.eqv_trans _
        (evalRawRows rho (rawMulRows left right) +
          evalRawRows rho ([] :: rawRowsConvolution lefts right)) _
        happend ?_
      refine Q'.eqv_trans _
        (RingNormaliser.evalRaw rho left * evalRawRows rho right +
          evalRawRows rho lefts * evalRawRows rho right) _
        (Q'.add_eqv_congr' hleft
          (Q'.eqv_trans _ _ _ hshift htail)) ?_
      exact Q'.eqv_symm
        (RingNormaliser.q_add_mul
          (RingNormaliser.evalRaw rho left)
          (evalRawRows rho lefts)
          (evalRawRows rho right))

/-- Bucketing two supported raw polynomials and convolving their rows retains
the semantics of their ordinary raw product. -/
theorem evalRawRows_bucketConvolution
    (rho : Nat → Q') (leftCount rightCount : Nat)
    (left right : RawPoly)
    (hleft : rawFirstExponentBound leftCount left = true)
    (hright : rawFirstExponentBound rightCount right = true) :
    evalRawRows rho
        (rawRowsConvolution
          (bucketRaw leftCount left) (bucketRaw rightCount right)) ≈
      RingNormaliser.evalRaw rho left * RingNormaliser.evalRaw rho right := by
  have hconv := evalRawRows_rawRowsConvolution rho
    (bucketRaw leftCount left) (bucketRaw rightCount right)
  have hl := evalRawRows_bucketRaw rho leftCount left hleft
  have hr := evalRawRows_bucketRaw rho rightCount right hright
  exact Q'.eqv_trans _ _ _ hconv
    (Q'.eqv_trans _
      (RingNormaliser.evalRaw rho left *
        evalRawRows rho (bucketRaw rightCount right)) _
      (Q'.mul_eqv_congr_right _ _ _ hl)
      (Q'.mul_eqv_congr_left _ _ _ hr))

/-! ## Proof-carrying row shards -/

/-- A non-computational witness for a sequence of canonical row checks.  Each
head chunk can live in its own Lean module, so assembling the semantic theorem
does not re-run any expensive normalizations. -/
def CanonRowsChunksWitness (chunkSize : Nat) :
    Nat → List RawPoly → List RawPoly → Prop
  | 0, left, right => canonRowsRelation left right = true
  | chunks + 1, left, right =>
      canonRowsRelation (left.take chunkSize) (right.take chunkSize) = true ∧
        CanonRowsChunksWitness chunkSize chunks
          (left.drop chunkSize) (right.drop chunkSize)

theorem evalRawRows_eqv_of_CanonRowsChunksWitness
    (rho : Nat → Q') (chunkSize : Nat) : ∀ chunks left right,
    CanonRowsChunksWitness chunkSize chunks left right →
      evalRawRows rho left ≈ evalRawRows rho right
  | 0, left, right, h =>
      evalRawRows_eqv_of_canonRowsRelation_true rho left right h
  | chunks + 1, left, right, h => by
      have hhead := evalRawRows_eqv_of_canonRowsRelation_true rho
        (left.take chunkSize) (right.take chunkSize) h.1
      have htail := evalRawRows_eqv_of_CanonRowsChunksWitness
        rho chunkSize chunks (left.drop chunkSize) (right.drop chunkSize) h.2
      have hleft := evalRawRows_append rho
        (left.take chunkSize) (left.drop chunkSize)
      have hright := evalRawRows_append rho
        (right.take chunkSize) (right.drop chunkSize)
      rw [List.take_append_drop] at hleft hright
      exact Q'.eqv_trans _ _ _ hleft
        (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hhead htail)
          (Q'.eqv_symm hright))

/-- Pointwise canonical equality, together with equal row-family lengths,
implies the ordinary recursive row relation. -/
theorem canonRowsRelation_true_of_pointwise : ∀ left right,
    left.length = right.length →
    (∀ index, index < left.length →
      RingNormaliser.canon (rawRowAt left index) =
        RingNormaliser.canon (rawRowAt right index)) →
    canonRowsRelation left right = true
  | [], [], _, _ => rfl
  | [], _ :: _, hlength, _ => by
      change 0 = Nat.succ _ at hlength
      omega
  | _ :: _, [], hlength, _ => by
      change Nat.succ _ = 0 at hlength
      omega
  | left :: lefts, right :: rights, hlength, hpoint => by
      have hhead : RingNormaliser.canon left = RingNormaliser.canon right := by
        have hzero := hpoint 0 (by
          change 0 < Nat.succ lefts.length
          omega)
        change RingNormaliser.canon left = RingNormaliser.canon right at hzero
        exact hzero
      have htailLength : lefts.length = rights.length := by
        change Nat.succ lefts.length = Nat.succ rights.length at hlength
        omega
      have htailPoint : ∀ index, index < lefts.length →
          RingNormaliser.canon (rawRowAt lefts index) =
            RingNormaliser.canon (rawRowAt rights index) := by
        intro index hindex
        have hnext := hpoint (index + 1) (by
          change index + 1 < Nat.succ lefts.length
          omega)
        change RingNormaliser.canon (rawRowAt lefts index) =
          RingNormaliser.canon (rawRowAt rights index) at hnext
        exact hnext
      have htail := canonRowsRelation_true_of_pointwise
        lefts rights htailLength htailPoint
      simp only [canonRowsRelation, hhead, decide_true, htail, Bool.and_self]

/-- A closed `allRowOffsets` table is a compact way to assemble independently
checked one-row modules without re-running their normalizations. -/
theorem evalRawRows_eqv_of_allRowOffsets
    (rho : Nat → Q') (count : Nat) (left right : List RawPoly)
    (hleftLength : left.length = count)
    (hrightLength : right.length = count)
    (hall : allRowOffsets count (fun index =>
      decide
        (RingNormaliser.canon (rawRowAt left index) =
          RingNormaliser.canon (rawRowAt right index))) = true) :
    evalRawRows rho left ≈ evalRawRows rho right := by
  have hlength : left.length = right.length :=
    hleftLength.trans hrightLength.symm
  apply evalRawRows_eqv_of_canonRowsRelation_true rho left right
  apply canonRowsRelation_true_of_pointwise left right hlength
  intro index hindex
  have hindexCount : index < count := by simpa [hleftLength] using hindex
  exact of_decide_eq_true
    (allRowOffsets_true_at hall hindexCount)

#print axioms evalRaw_removeZeroRaw
#print axioms evalRaw_scalarRawRow
#print axioms evalRawRows_rawMulRows
#print axioms evalRawRows_rawRowsConvolution
#print axioms evalRawRows_bucketConvolution
#print axioms evalRawRows_eqv_of_CanonRowsChunksWitness
#print axioms canonRowsRelation_true_of_pointwise
#print axioms evalRawRows_eqv_of_allRowOffsets

end YMGap.Continuum.RawGridRowConvolution
