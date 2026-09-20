/-
# Base inclusion syntax for the chronological Wilson kernel

Finite program, timed-word, term-list and compiler inclusion commute with the
existing base inclusion.  This is literal syntax only; no completed-operator
or physical statement is made here.
-/

import YMGap.Continuum.BF4WilsonChronologicalKernel
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonBaseInclusion

namespace YMGap.Continuum.BF4WilsonKernelInclusionSyntax

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4WilsonChronologicalProgram
open YMGap.Continuum.BF4WilsonChronologicalOperator
open YMGap.Continuum.BF4WilsonChronologicalKernel
open YMGap.Continuum.BF4WilsonChronologicalCompositionSyntax
open YMGap.Continuum.BF4WilsonTimedWord
open YMGap.Continuum.BF4WilsonTimedWordOrder
open YMGap.Continuum.BF4WilsonExpressionExpansion
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonBaseInclusion
open YMGap.Continuum.BF4WilsonSpatialUnionTimeZeroMultiplier

def includeProgram {base larger : Nat} (h : base ≤ larger) :
    Program base → Program larger
  | .vacuum => .vacuum
  | .zero => .zero
  | .add p q => .add (includeProgram h p) (includeProgram h q)
  | .smul c p => .smul c (includeProgram h p)
  | .time n p => .time n (includeProgram h p)
  | .multiply L spin p =>
      .multiply (loopAt L h) spin (includeProgram h p)

def includeTimedLoop {base larger : Nat} (h : base ≤ larger)
    (a : TimedLoop base) : TimedLoop larger :=
  ⟨a.offset, loopAt a.loop h, a.spin⟩

def includeTerms {base larger : Nat} (h : base ≤ larger) :
    List (Q' × List (TimedLoop base)) → List (Q' × List (TimedLoop larger)) :=
  List.map (fun a => (a.1, a.2.map (includeTimedLoop h)))

private theorem includeTimedLoop_offset {base larger : Nat} (h : base ≤ larger)
    (a : TimedLoop base) : (includeTimedLoop h a).offset = a.offset := rfl

private theorem includeTimedLoop_insert {base larger : Nat} (h : base ≤ larger)
    (a : TimedLoop base) (xs : List (TimedLoop base)) :
    (insertWord a xs).map (includeTimedLoop h) =
      insertWord (includeTimedLoop h a) (xs.map (includeTimedLoop h)) := by
  induction xs with
  | nil => rfl
  | cons b rest ih =>
      by_cases hab : b.offset ≤ a.offset
      · simp only [insertWord, includeTimedLoop_offset, if_pos hab, List.map_cons]
      · simp only [insertWord, includeTimedLoop_offset, if_neg hab, List.map_cons, ih]

private theorem includeTimedLoop_order {base larger : Nat} (h : base ≤ larger)
    (xs : List (TimedLoop base)) :
    (orderWord xs).map (includeTimedLoop h) =
      orderWord (xs.map (includeTimedLoop h)) := by
  induction xs with
  | nil => rfl
  | cons a rest ih =>
      simp only [orderWord, List.map_cons, includeTimedLoop_insert, ih]

private theorem includeProgram_orderedKernel {base larger : Nat} (h : base ≤ larger)
    (H : Nat) (xs : List (TimedLoop base)) :
    includeProgram h (orderedKernel H xs) =
      orderedKernel H (xs.map (includeTimedLoop h)) := by
  induction xs generalizing H with
  | nil => rfl
  | cons a rest ih =>
      simp only [orderedKernel, includeProgram, List.map_cons, includeTimedLoop, ih]

private theorem includeProgram_wordKernel {base larger : Nat} (h : base ≤ larger)
    (H : Nat) (xs : List (TimedLoop base)) :
    includeProgram h (wordKernel H xs) =
      wordKernel H (xs.map (includeTimedLoop h)) := by
  unfold wordKernel
  rw [includeProgram_orderedKernel, includeTimedLoop_order]

private theorem includeProgram_termsKernel {base larger : Nat} (h : base ≤ larger)
    (H : Nat) (xs : List (Q' × List (TimedLoop base))) :
    includeProgram h (termsKernel H xs) =
      termsKernel H (includeTerms h xs) := by
  induction xs with
  | nil => rfl
  | cons a rest ih =>
      simp only [termsKernel, includeProgram, includeTerms, List.map_cons,
        includeProgram_wordKernel, ih]

private theorem includeTerms_multiplyTerms {base larger : Nat} (h : base ≤ larger)
    (xs ys : List (Q' × List (TimedLoop base))) :
    includeTerms h (multiplyTerms xs ys) =
      multiplyTerms (includeTerms h xs) (includeTerms h ys) := by
  induction xs with
  | nil => rfl
  | cons a rest ih =>
      change includeTerms h
        (ys.map (fun b => (a.1*b.1, a.2++b.2)) ++ multiplyTerms rest ys) = _
      simp only [includeTerms, List.map_append, List.map_map, List.map_cons,
        multiplyTerms] at ih ⊢
      rw [ih]
      apply congrArg (fun row => row ++ multiplyTerms (includeTerms h rest) (includeTerms h ys))
      apply List.map_congr_left
      intro b _
      change (a.1*b.1, (a.2++b.2).map (includeTimedLoop h)) = _
      rw [List.map_append]
      rfl

private theorem includeTerms_expand {base larger : Nat} (h : base ≤ larger)
    (e : WindowExpression base) :
    includeTerms h (expand e) = expand (includeExpression h e) := by
  induction e with
  | one => rfl
  | loop offset L spin => rfl
  | add e f ihe ihf =>
      change includeTerms h (expand e ++ expand f) = expand (includeExpression h e) ++ expand (includeExpression h f)
      change (expand e ++ expand f).map _ = _
      rw [List.map_append]
      change includeTerms h (expand e) ++ includeTerms h (expand f) = _
      rw [ihe, ihf]
  | mul e f ihe ihf =>
      change includeTerms h (multiplyTerms (expand e) (expand f)) =
        multiplyTerms (expand (includeExpression h e)) (expand (includeExpression h f))
      rw [includeTerms_multiplyTerms h (expand e) (expand f), ihe, ihf]
  | smul c e ihe =>
      change includeTerms h ((expand e).map (fun a => (c*a.1, a.2))) =
        (expand (includeExpression h e)).map (fun a => (c*a.1, a.2))
      rw [← ihe]
      simp only [includeTerms, List.map_map]
      apply List.map_congr_left
      intro a _
      rfl

theorem includeProgram_compileKernel {base larger : Nat} (h : base ≤ larger)
    (H : Nat) (e : WindowExpression base) :
    includeProgram h (compileKernel H e) =
      compileKernel H (includeExpression h e) := by
  unfold compileKernel
  rw [includeProgram_termsKernel, includeTerms_expand]

theorem includeProgram_squaredCap {base larger : Nat} (h : base ≤ larger)
    (p : Program base) :
    squaredCap (includeProgram h p) = squaredCap p := by
  induction p <;> simp only [includeProgram, squaredCap, *]

#print axioms includeProgram
#print axioms includeTimedLoop
#print axioms includeTerms
#print axioms includeProgram_compileKernel
#print axioms includeProgram_squaredCap

end YMGap.Continuum.BF4WilsonKernelInclusionSyntax
