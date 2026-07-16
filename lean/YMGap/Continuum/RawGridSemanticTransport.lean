/-
# Semantic transport for finite raw-polynomial grids

This module separates two inexpensive, reusable facts from every generated
coefficient certificate:

* a rectangular coefficient grid can be emitted as an appended raw polynomial
  and evaluated as the corresponding nested finite sum; and
* equality after canonicalization transports raw evaluation, including to a
  `PolyExpr` checked by `fastNormalize`.

The monomial map is arbitrary.  Diagonal, residual-degree, and quadratic
projective charts therefore share the same proof and differ only in data.
-/

import YMGap.Continuum.CoreBResidualSimplex
import YMGap.Continuum.TensorBernsteinHomogeneousCertificate

namespace YMGap.Continuum.RawGridSemanticTransport

set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.CoreBResidualSimplex
open YMGap.Continuum.TensorBernsteinHomogeneousCertificate

local infix:50 " ≈ " => Q'.eqv

abbrev RawPoly := RingNormaliser.RawPoly

/-- Append the first `count` entries of one coefficient-grid row. -/
def rawGridRow
    (monomial : Nat → Nat → List Nat)
    (coefficient : Nat → Nat → Int) (row : Nat) : Nat → RawPoly
  | 0 => []
  | column + 1 =>
      rawGridRow monomial coefficient row column ++
        [(monomial row column, coefficient row column)]

/-- Append the first `count` rows, each with `width` entries. -/
def rawGrid
    (monomial : Nat → Nat → List Nat)
    (coefficient : Nat → Nat → Int) (width : Nat) : Nat → RawPoly
  | 0 => []
  | row + 1 =>
      rawGrid monomial coefficient width row ++
        rawGridRow monomial coefficient row width

theorem evalRaw_singleton (rho : Nat → Q')
    (monomial : List Nat) (coefficient : Int) :
    RingNormaliser.evalRaw rho [(monomial, coefficient)] ≈
      Q'.ofInt coefficient * RingNormaliser.evalMono rho monomial := by
  change Q'.ofInt coefficient * RingNormaliser.evalMono rho monomial + 0 ≈
    Q'.ofInt coefficient * RingNormaliser.evalMono rho monomial
  exact QPoly.q_add_zero_eqv _

theorem evalRaw_rawGridRow (rho : Nat → Q')
    (monomial : Nat → Nat → List Nat)
    (coefficient : Nat → Nat → Int) (row : Nat) : ∀ count,
    RingNormaliser.evalRaw rho
        (rawGridRow monomial coefficient row count) ≈
      RationalTail.finSum (fun column =>
        Q'.ofInt (coefficient row column) *
          RingNormaliser.evalMono rho (monomial row column)) count
  | 0 => Q'.eqv_refl 0
  | column + 1 => by
      have happ := RingNormaliser.evalRaw_append rho
        (rawGridRow monomial coefficient row column)
        [(monomial row column, coefficient row column)]
      have ih := evalRaw_rawGridRow rho monomial coefficient row column
      have hterm := evalRaw_singleton rho
        (monomial row column) (coefficient row column)
      exact Q'.eqv_trans _ _ _ happ (Q'.add_eqv_congr' ih hterm)

theorem evalRaw_rawGrid (rho : Nat → Q')
    (monomial : Nat → Nat → List Nat)
    (coefficient : Nat → Nat → Int) (width : Nat) : ∀ count,
    RingNormaliser.evalRaw rho
        (rawGrid monomial coefficient width count) ≈
      RationalTail.finSum (fun row =>
        RationalTail.finSum (fun column =>
          Q'.ofInt (coefficient row column) *
            RingNormaliser.evalMono rho (monomial row column)) width) count
  | 0 => Q'.eqv_refl 0
  | row + 1 => by
      have happ := RingNormaliser.evalRaw_append rho
        (rawGrid monomial coefficient width row)
        (rawGridRow monomial coefficient row width)
      have ih := evalRaw_rawGrid rho monomial coefficient width row
      have hrow := evalRaw_rawGridRow rho monomial coefficient row width
      exact Q'.eqv_trans _ _ _ happ (Q'.add_eqv_congr' ih hrow)

/-- Canonical raw equality is enough for semantic equality. -/
theorem evalRaw_eqv_of_canon_eq (rho : Nat → Q')
    {left right : RawPoly}
    (h : RingNormaliser.canon left = RingNormaliser.canon right) :
    RingNormaliser.evalRaw rho left ≈ RingNormaliser.evalRaw rho right := by
  refine Q'.eqv_trans _
    (RingNormaliser.evalRaw rho (RingNormaliser.canon left)) _
    (Q'.eqv_symm (RingNormaliser.evalRaw_canon rho left)) ?_
  rw [h]
  exact RingNormaliser.evalRaw_canon rho right

/-- Canonical equality with a fast normal form transports a raw certificate to
the reflected polynomial expression without expanding that expression again. -/
theorem evalRaw_eqv_eval_of_canon_fastNormalize_eq
    (rho : Nat → Q') (raw : RawPoly) (expression : RingNormaliser.PolyExpr)
    (h : RingNormaliser.canon raw = fastNormalize expression) :
    RingNormaliser.evalRaw rho raw ≈ RingNormaliser.eval rho expression := by
  refine Q'.eqv_trans _
    (RingNormaliser.evalRaw rho (RingNormaliser.canon raw)) _
    (Q'.eqv_symm (RingNormaliser.evalRaw_canon rho raw)) ?_
  rw [h]
  exact evalRaw_fastNormalize rho expression

/-! ## Sparse bivariate term lists -/

def bivariateMonomial (xExponent yExponent : Nat) : List Nat :=
  if yExponent = 0 then
    if xExponent = 0 then [] else [xExponent]
  else [xExponent, yExponent]

def bivariateTermsRaw : List (Nat × Nat × Int) → RawPoly
  | [] => []
  | (xExponent, yExponent, coefficient) :: rest =>
      (bivariateMonomial xExponent yExponent, coefficient) ::
        bivariateTermsRaw rest

theorem evalMono_bivariateMonomial (rho : Nat → Q')
    (xExponent yExponent : Nat) :
    RingNormaliser.evalMono rho (bivariateMonomial xExponent yExponent) ≈
      RingNormaliser.qpow (rho 0) xExponent *
        RingNormaliser.qpow (rho 1) yExponent := by
  by_cases hy : yExponent = 0
  · subst yExponent
    by_cases hx : xExponent = 0
    · subst xExponent
      simp only [bivariateMonomial, if_pos]
      change (1 : Q') ≈ (1 : Q') * 1
      exact Q'.eqv_symm (Q'.mul_one_eqv 1)
    · simp only [bivariateMonomial, if_pos, if_neg hx]
      change RingNormaliser.qpow (rho 0) xExponent * 1 ≈
        RingNormaliser.qpow (rho 0) xExponent * 1
      exact Q'.eqv_refl _
  · simp only [bivariateMonomial, if_neg hy]
    change RingNormaliser.qpow (rho 0) xExponent *
        (RingNormaliser.qpow (rho 1) yExponent * 1) ≈
      RingNormaliser.qpow (rho 0) xExponent *
        RingNormaliser.qpow (rho 1) yExponent
    exact Q'.mul_eqv_congr_left _ _ _ (Q'.mul_one_eqv _)

theorem evalRaw_bivariateTermsRaw (rho : Nat → Q') : ∀ terms,
    RingNormaliser.evalRaw rho (bivariateTermsRaw terms) ≈
      RingNormaliser.eval rho (bivariatePowerExpr terms)
  | [] => Q'.eqv_refl 0
  | (xExponent, yExponent, coefficient) :: rest => by
      change
        Q'.ofInt coefficient *
            RingNormaliser.evalMono rho
              (bivariateMonomial xExponent yExponent) +
          RingNormaliser.evalRaw rho (bivariateTermsRaw rest) ≈
        Q'.ofInt coefficient *
            (RingNormaliser.qpow (rho 0) xExponent *
              RingNormaliser.qpow (rho 1) yExponent) +
          RingNormaliser.eval rho (bivariatePowerExpr rest)
      exact Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_left _ _ _
          (evalMono_bivariateMonomial rho xExponent yExponent))
        (evalRaw_bivariateTermsRaw rho rest)

/-! ## Row-sharded reconciliation

Large exact identities should be checked one sparse exponent row at a time.
The following folds turn a list of raw rows into either one appended raw
polynomial or its semantic sum. -/

def joinRawRows : List RawPoly → RawPoly
  | [] => []
  | row :: rows => row ++ joinRawRows rows

def evalRawRows (rho : Nat → Q') : List RawPoly → Q'
  | [] => 0
  | row :: rows => RingNormaliser.evalRaw rho row + evalRawRows rho rows

theorem evalRaw_joinRawRows (rho : Nat → Q') : ∀ rows,
    RingNormaliser.evalRaw rho (joinRawRows rows) ≈ evalRawRows rho rows
  | [] => Q'.eqv_refl 0
  | row :: rows => by
      exact Q'.eqv_trans _ _ _
        (RingNormaliser.evalRaw_append rho row (joinRawRows rows))
        (Q'.add_eqv_congr_left _ _ _ (evalRaw_joinRawRows rho rows))

def canonRawRows : List RawPoly → List RawPoly
  | [] => []
  | row :: rows => RingNormaliser.canon row :: canonRawRows rows

theorem evalRawRows_canon (rho : Nat → Q') : ∀ rows,
    evalRawRows rho (canonRawRows rows) ≈ evalRawRows rho rows
  | [] => Q'.eqv_refl 0
  | row :: rows =>
      Q'.add_eqv_congr'
        (RingNormaliser.evalRaw_canon rho row)
        (evalRawRows_canon rho rows)

/-- Merge two equally positioned row families by raw append.  If one family
ends first, the remaining rows of the other family are retained. -/
def appendRawRows : List RawPoly → List RawPoly → List RawPoly
  | [], right => right
  | left, [] => left
  | leftRow :: leftRows, rightRow :: rightRows =>
      (leftRow ++ rightRow) :: appendRawRows leftRows rightRows

theorem evalRawRows_appendRawRows (rho : Nat → Q') : ∀ left right,
    evalRawRows rho (appendRawRows left right) ≈
      evalRawRows rho left + evalRawRows rho right
  | [], right =>
      RingNormaliser.eqv_of_eq (Q'.zero_add' (evalRawRows rho right)).symm
  | leftRow :: leftRows, [] =>
      Q'.eqv_symm
        (QPoly.q_add_zero_eqv
          (RingNormaliser.evalRaw rho leftRow + evalRawRows rho leftRows))
  | leftRow :: leftRows, rightRow :: rightRows => by
      have hrow := RingNormaliser.evalRaw_append rho leftRow rightRow
      have htail := evalRawRows_appendRawRows rho leftRows rightRows
      refine Q'.eqv_trans _
        ((RingNormaliser.evalRaw rho leftRow +
            RingNormaliser.evalRaw rho rightRow) +
          (evalRawRows rho leftRows + evalRawRows rho rightRows)) _
        (Q'.add_eqv_congr' hrow htail) ?_
      exact Q'.add_swap_inner
        (RingNormaliser.evalRaw rho leftRow)
        (RingNormaliser.evalRaw rho rightRow)
        (evalRawRows rho leftRows)
        (evalRawRows rho rightRows)

theorem evalRawRows_eqv_of_canonRows_eq (rho : Nat → Q')
    {left right : List RawPoly} (h : canonRawRows left = canonRawRows right) :
    evalRawRows rho left ≈ evalRawRows rho right := by
  refine Q'.eqv_trans _ (evalRawRows rho (canonRawRows left)) _
    (Q'.eqv_symm (evalRawRows_canon rho left)) ?_
  rw [h]
  exact evalRawRows_canon rho right

/-! ## Single-pass bucketing by the first variable exponent -/

def rawFirstExponent (term : List Nat × Int) : Nat :=
  match term.1 with
  | [] => 0
  | exponent :: _ => exponent

def insertRawRow (index : Nat) (term : List Nat × Int) :
    List RawPoly → List RawPoly
  | [] => []
  | row :: rows =>
      match index with
      | 0 => (term :: row) :: rows
      | next + 1 => row :: insertRawRow next term rows

theorem insertRawRow_length (index : Nat) (term : List Nat × Int) :
    ∀ rows, (insertRawRow index term rows).length = rows.length
  | [] => by simp [insertRawRow]
  | _ :: rows => by
      cases index with
      | zero => rfl
      | succ index =>
          simp only [insertRawRow, List.length_cons]
          rw [insertRawRow_length index term rows]

private def rawTermEval (rho : Nat → Q') (term : List Nat × Int) : Q' :=
  Q'.ofInt term.2 * RingNormaliser.evalMono rho term.1

theorem evalRawRows_insertRawRow (rho : Nat → Q')
    (term : List Nat × Int) : ∀ index rows,
    index < rows.length →
    evalRawRows rho (insertRawRow index term rows) ≈
      rawTermEval rho term + evalRawRows rho rows
  | _, [], h => by simp at h
  | 0, row :: rows, _ => by
      change
        (rawTermEval rho term + RingNormaliser.evalRaw rho row) +
            evalRawRows rho rows ≈
          rawTermEval rho term +
            (RingNormaliser.evalRaw rho row + evalRawRows rho rows)
      exact Q'.add_assoc_eqv _ _ _
  | index + 1, row :: rows, h => by
      have htail : index < rows.length := by
        simp only [List.length_cons] at h
        omega
      have ih := evalRawRows_insertRawRow rho term index rows htail
      refine Q'.eqv_trans _
        (RingNormaliser.evalRaw rho row +
          (rawTermEval rho term + evalRawRows rho rows)) _
        (Q'.add_eqv_congr_left _ _ _ ih) ?_
      refine Q'.eqv_trans _
        ((RingNormaliser.evalRaw rho row + rawTermEval rho term) +
          evalRawRows rho rows) _
        (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)) ?_
      refine Q'.eqv_trans _
        ((rawTermEval rho term + RingNormaliser.evalRaw rho row) +
          evalRawRows rho rows) _
        (Q'.add_eqv_congr_right _ _ _
          (Q'.add_comm_eqv _ _)) ?_
      exact Q'.add_assoc_eqv _ _ _

def bucketRaw (count : Nat) : RawPoly → List RawPoly
  | [] => List.replicate count []
  | term :: rest =>
      insertRawRow (rawFirstExponent term) term (bucketRaw count rest)

theorem bucketRaw_length (count : Nat) : ∀ raw,
    (bucketRaw count raw).length = count
  | [] => List.length_replicate
  | term :: rest => by
      rw [bucketRaw, insertRawRow_length, bucketRaw_length count rest]

def rawFirstExponentBound (count : Nat) : RawPoly → Bool
  | [] => true
  | term :: rest =>
      decide (rawFirstExponent term < count) &&
        rawFirstExponentBound count rest

private theorem evalRawRows_replicate_empty (rho : Nat → Q') : ∀ count,
    evalRawRows rho (List.replicate count []) ≈ 0
  | 0 => Q'.eqv_refl 0
  | count + 1 => by
      change (0 : Q') + evalRawRows rho (List.replicate count []) ≈ 0
      exact Q'.eqv_trans _ _ _
        (RingNormaliser.eqv_of_eq
          (Q'.zero_add' (evalRawRows rho (List.replicate count []))))
        (evalRawRows_replicate_empty rho count)

theorem evalRawRows_bucketRaw (rho : Nat → Q') (count : Nat) : ∀ raw,
    rawFirstExponentBound count raw = true →
    evalRawRows rho (bucketRaw count raw) ≈ RingNormaliser.evalRaw rho raw
  | [], _ => evalRawRows_replicate_empty rho count
  | term :: rest, h => by
      have hsplit := (Bool.and_eq_true _ _).mp h
      have hindex : rawFirstExponent term < count :=
        of_decide_eq_true hsplit.1
      have hinsert := evalRawRows_insertRawRow rho term
        (rawFirstExponent term) (bucketRaw count rest)
        (by simpa [bucketRaw_length count rest] using hindex)
      have ih := evalRawRows_bucketRaw rho count rest hsplit.2
      exact Q'.eqv_trans _ _ _ hinsert
        (Q'.add_eqv_congr_left _ _ _ ih)

def canonRowsRelation : List RawPoly → List RawPoly → Bool
  | [], [] => true
  | left :: leftRows, right :: rightRows =>
      decide (RingNormaliser.canon left = RingNormaliser.canon right) &&
        canonRowsRelation leftRows rightRows
  | _, _ => false

theorem evalRawRows_eqv_of_canonRowsRelation_true (rho : Nat → Q') :
    ∀ left right, canonRowsRelation left right = true →
      evalRawRows rho left ≈ evalRawRows rho right
  | [], [], _ => Q'.eqv_refl 0
  | [], _ :: _, h => by simp [canonRowsRelation] at h
  | _ :: _, [], h => by simp [canonRowsRelation] at h
  | left :: leftRows, right :: rightRows, h => by
      have hsplit := (Bool.and_eq_true _ _).mp h
      have hrow : RingNormaliser.canon left = RingNormaliser.canon right :=
        of_decide_eq_true hsplit.1
      exact Q'.add_eqv_congr'
        (evalRaw_eqv_of_canon_eq rho hrow)
        (evalRawRows_eqv_of_canonRowsRelation_true rho
          leftRows rightRows hsplit.2)

theorem evalRawRows_append (rho : Nat → Q') : ∀ left right,
    evalRawRows rho (left ++ right) ≈
      evalRawRows rho left + evalRawRows rho right
  | [], right =>
      RingNormaliser.eqv_of_eq (Q'.zero_add' (evalRawRows rho right)).symm
  | row :: rows, right => by
      refine Q'.eqv_trans _
        (RingNormaliser.evalRaw rho row +
          (evalRawRows rho rows + evalRawRows rho right)) _
        (Q'.add_eqv_congr_left _ _ _
          (evalRawRows_append rho rows right)) ?_
      exact Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)

/-- Check canonical equality in short consecutive chunks.  `chunks = 6` and
`chunkSize = 4`, for example, checks 23 rows without ever constructing a
23-row equality expression. -/
def canonRowsRelationChunks (chunkSize : Nat) :
    Nat → List RawPoly → List RawPoly → Bool
  | 0, left, right => canonRowsRelation left right
  | chunks + 1, left, right =>
      canonRowsRelation (left.take chunkSize) (right.take chunkSize) &&
        canonRowsRelationChunks chunkSize chunks
          (left.drop chunkSize) (right.drop chunkSize)

theorem evalRawRows_eqv_of_canonRowsRelationChunks_true
    (rho : Nat → Q') (chunkSize : Nat) : ∀ chunks left right,
    canonRowsRelationChunks chunkSize chunks left right = true →
      evalRawRows rho left ≈ evalRawRows rho right
  | 0, left, right, h =>
      evalRawRows_eqv_of_canonRowsRelation_true rho left right h
  | chunks + 1, left, right, h => by
      have hsplit := (Bool.and_eq_true _ _).mp h
      have hhead := evalRawRows_eqv_of_canonRowsRelation_true rho
        (left.take chunkSize) (right.take chunkSize) hsplit.1
      have htail := evalRawRows_eqv_of_canonRowsRelationChunks_true
        rho chunkSize chunks (left.drop chunkSize) (right.drop chunkSize)
        hsplit.2
      have hleft := evalRawRows_append rho
        (left.take chunkSize) (left.drop chunkSize)
      have hright := evalRawRows_append rho
        (right.take chunkSize) (right.drop chunkSize)
      rw [List.take_append_drop] at hleft hright
      exact Q'.eqv_trans _ _ _ hleft
        (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hhead htail)
          (Q'.eqv_symm hright))

def allRowOffsets : Nat → (Nat → Bool) → Bool
  | 0, _ => true
  | count + 1, predicate =>
      allRowOffsets count predicate && predicate count

theorem allRowOffsets_true_at {count : Nat} {predicate : Nat → Bool}
    (h : allRowOffsets count predicate = true) {offset : Nat}
    (hoffset : offset < count) : predicate offset = true := by
  induction count with
  | zero => omega
  | succ count ih =>
      have hsplit := (Bool.and_eq_true _ _).mp h
      by_cases heq : offset = count
      · simpa [heq] using hsplit.2
      · exact ih hsplit.1 (by omega)

def rawRowAt (rows : List RawPoly) (index : Nat) : RawPoly :=
  rows.getD index []

/-- Closed checker for a short consecutive block of canonical row equalities.
Using slices avoids constructing one very deep equality expression for a
large generated polynomial. -/
def canonRowsRelationSlice (start count : Nat)
    (left right : List RawPoly) : Bool :=
  allRowOffsets count (fun offset =>
    decide
      (RingNormaliser.canon (rawRowAt left (start + offset)) =
        RingNormaliser.canon (rawRowAt right (start + offset))))

theorem canonRowsRelationSlice_true_at
    {start count : Nat} {left right : List RawPoly}
    (h : canonRowsRelationSlice start count left right = true)
    {offset : Nat} (hoffset : offset < count) :
    RingNormaliser.canon (rawRowAt left (start + offset)) =
      RingNormaliser.canon (rawRowAt right (start + offset)) := by
  exact of_decide_eq_true (allRowOffsets_true_at h hoffset)

#print axioms evalRaw_rawGridRow
#print axioms evalRaw_rawGrid
#print axioms evalRaw_eqv_of_canon_eq
#print axioms evalRaw_eqv_eval_of_canon_fastNormalize_eq
#print axioms evalRaw_bivariateTermsRaw
#print axioms evalRaw_joinRawRows
#print axioms evalRawRows_appendRawRows
#print axioms evalRawRows_eqv_of_canonRows_eq
#print axioms evalRawRows_bucketRaw
#print axioms evalRawRows_eqv_of_canonRowsRelation_true
#print axioms evalRawRows_eqv_of_canonRowsRelationChunks_true
#print axioms canonRowsRelationSlice_true_at

end YMGap.Continuum.RawGridSemanticTransport
