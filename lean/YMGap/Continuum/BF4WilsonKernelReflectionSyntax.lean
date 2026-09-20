/-
# Finite reflection syntax for original Wilson kernels

This file records only bounded offset reflection, insertion-sort syntax, and
the finite expansion of a word.  Loop order, orientations, and spins are not
changed.  No adjoint, Haar identity, or completed-operator statement is made
here; those are consumers of these finite identities.
-/

import YMGap.Continuum.BF4WilsonExpressionExpansion
import YMGap.Continuum.BF4WilsonTimedWordOrder
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredWindow

namespace YMGap.Continuum.BF4WilsonKernelReflectionSyntax

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredWindow
open YMGap.Continuum.BF4WilsonTimedWord
open YMGap.Continuum.BF4WilsonTimedWordOrder
open YMGap.Continuum.BF4WilsonExpressionExpansion
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential

def reverseWindow {base : Nat} (H : Nat) (e : WindowExpression base) :
    WindowExpression base :=
  mapOffsets (fun t => H-t) e

def mapTimedLoop {base : Nat} (phi : Nat → Nat) (a : TimedLoop base) :
    TimedLoop base :=
  { offset := phi a.offset, loop := a.loop, spin := a.spin }

def mapTerms {base : Nat} (phi : Nat → Nat)
    (terms : List (Q' × List (TimedLoop base))) :
    List (Q' × List (TimedLoop base)) :=
  terms.map (fun term => (term.1, term.2.map (mapTimedLoop phi)))

theorem wordExpression_mapOffsets {base : Nat} (phi : Nat → Nat)
    (word : List (TimedLoop base)) :
    wordExpression (word.map (mapTimedLoop phi)) =
      mapOffsets phi (wordExpression word) := by
  induction word with
  | nil => rfl
  | cons a rest ih =>
      simp only [wordExpression, mapTimedLoop, List.map_cons, mapOffsets]
      rw [ih]

private theorem multiplyTerms_mapTerms {base : Nat} (phi : Nat → Nat)
    (left right : List (Q' × List (TimedLoop base))) :
    mapTerms phi (multiplyTerms left right) =
      multiplyTerms (mapTerms phi left) (mapTerms phi right) := by
  induction left with
  | nil => rfl
  | cons a rest ih =>
      change mapTerms phi
        (right.map (fun b => (a.1*b.1, a.2++b.2)) ++ multiplyTerms rest right) = _
      simp only [mapTerms, List.map_append, List.map_map, List.map_cons,
        multiplyTerms] at ih ⊢
      rw [ih]
      apply congrArg (fun row => row ++ multiplyTerms (mapTerms phi rest)
        (mapTerms phi right))
      apply List.map_congr_left
      intro b _
      change (a.1*b.1, (a.2++b.2).map (mapTimedLoop phi)) = _
      rw [List.map_append]
      rfl

theorem expand_mapOffsets {base : Nat} (phi : Nat → Nat)
    (e : WindowExpression base) :
    expand (mapOffsets phi e) = mapTerms phi (expand e) := by
  induction e with
  | one => rfl
  | loop offset loop spin => rfl
  | add e f ihe ihf =>
      change expand (mapOffsets phi e) ++ expand (mapOffsets phi f) =
        mapTerms phi (expand e ++ expand f)
      rw [ihe, ihf]
      simp only [mapTerms, List.map_append]
  | mul e f ihe ihf =>
      change multiplyTerms (expand (mapOffsets phi e)) (expand (mapOffsets phi f)) =
        mapTerms phi (multiplyTerms (expand e) (expand f))
      rw [ihe, ihf, multiplyTerms_mapTerms]
  | smul c e ihe =>
      change (expand (mapOffsets phi e)).map (fun a => (c*a.1, a.2)) =
        mapTerms phi ((expand e).map (fun a => (c*a.1, a.2)))
      rw [ihe]
      simp only [mapTerms, List.map_map]
      apply List.map_congr_left
      intro a _
      rfl

theorem reverseWindow_within {base : Nat} (H : Nat)
    (e : WindowExpression base) :
    Within H (reverseWindow H e) := by
  induction e with
  | one => exact True.intro
  | loop offset loop spin =>
      change H-offset ≤ H
      omega
  | add e f ihe ihf => exact ⟨ihe, ihf⟩
  | mul e f ihe ihf => exact ⟨ihe, ihf⟩
  | smul c e ihe => exact ihe

private theorem reverseWindow_offset_involutive {H t : Nat} (ht : t ≤ H) :
    H - (H - t) = t := by omega

theorem reverseWindow_involutive {base : Nat} (H : Nat)
    (e : WindowExpression base) (he : Within H e) :
    reverseWindow H (reverseWindow H e) = e := by
  induction e with
  | one => rfl
  | loop offset loop spin =>
      change WindowExpression.loop (H-(H-offset)) loop spin = _
      rw [reverseWindow_offset_involutive he]
  | add e f ihe ihf =>
      change WindowExpression.add (reverseWindow H (reverseWindow H e))
          (reverseWindow H (reverseWindow H f)) = WindowExpression.add e f
      rw [ihe he.1, ihf he.2]
  | mul e f ihe ihf =>
      change WindowExpression.mul (reverseWindow H (reverseWindow H e))
          (reverseWindow H (reverseWindow H f)) = WindowExpression.mul e f
      rw [ihe he.1, ihf he.2]
  | smul c e ihe =>
      exact congrArg (WindowExpression.smul c) (ihe he)

theorem reverseWindow_shift {base : Nat} (H a : Nat) (hHa : a ≤ H)
    (e : WindowExpression base) (he : Within a e) :
    shift (H-a) (reverseWindow a e) = reverseWindow H e := by
  induction e with
  | one => rfl
  | loop offset loop spin =>
      change WindowExpression.loop ((a-offset)+(H-a)) loop spin =
        WindowExpression.loop (H-offset) loop spin
      have ho : offset ≤ a := he
      rw [show (a-offset)+(H-a)=H-offset by omega]
  | add e f ihe ihf =>
      change WindowExpression.add (shift (H-a) (reverseWindow a e))
          (shift (H-a) (reverseWindow a f)) =
        WindowExpression.add (reverseWindow H e) (reverseWindow H f)
      rw [ihe he.1, ihf he.2]
  | mul e f ihe ihf =>
      change WindowExpression.mul (shift (H-a) (reverseWindow a e))
          (shift (H-a) (reverseWindow a f)) =
        WindowExpression.mul (reverseWindow H e) (reverseWindow H f)
      rw [ihe he.1, ihf he.2]
  | smul c e ihe =>
      exact congrArg (WindowExpression.smul c) (ihe he)

theorem reverseWindow_to_mirror {base : Nat} (H : Nat)
    (e : WindowExpression base) (he : Within H e) :
    shift H (reverseWindow H e) = mirror H e := by
  induction e with
  | one => rfl
  | loop offset loop spin =>
      change WindowExpression.loop ((H-offset)+H) loop spin =
        WindowExpression.loop (2*H-offset) loop spin
      have ho : offset ≤ H := he
      rw [show (H-offset)+H=2*H-offset by omega]
  | add e f ihe ihf =>
      change WindowExpression.add (shift H (reverseWindow H e))
          (shift H (reverseWindow H f)) = WindowExpression.add (mirror H e)
          (mirror H f)
      rw [ihe he.1, ihf he.2]
  | mul e f ihe ihf =>
      change WindowExpression.mul (shift H (reverseWindow H e))
          (shift H (reverseWindow H f)) = WindowExpression.mul (mirror H e)
          (mirror H f)
      rw [ihe he.1, ihf he.2]
  | smul c e ihe =>
      exact congrArg (WindowExpression.smul c) (ihe he)

private theorem swap_scalar_factors (a b c : RatPoly) :
    RatPolyCoeffEqv (polyMul b (polyMul a c)) (polyMul a (polyMul b c)) :=
  (RatPolyCoeffEqv.mul_assoc b a c).symm.trans
    (((RatPolyCoeffEqv.mul_comm b a).mul_right c).trans
      (RatPolyCoeffEqv.mul_assoc a b c))

private theorem insertWord_mapped_source {base : Nat} (phi : Nat → Nat)
    (a : TimedLoop base) (xs : List (TimedLoop base)) :
    RatPolyCoeffEqv
      (sourcePolynomial
        (wordExpression ((insertWord a xs).map (mapTimedLoop phi))))
      (polyMul
        (sourcePolynomial (.loop (phi a.offset) a.loop a.spin))
        (sourcePolynomial (wordExpression (xs.map (mapTimedLoop phi))))) := by
  induction xs with
  | nil => exact RatPolyCoeffEqv.refl _
  | cons b rest ih =>
      by_cases hab : b.offset ≤ a.offset
      · simp only [insertWord, if_pos hab, List.map_cons, mapTimedLoop,
          wordExpression]
        exact RatPolyCoeffEqv.refl _
      · simp only [insertWord, if_neg hab, List.map_cons, mapTimedLoop,
          wordExpression]
        exact (RatPolyCoeffEqv.mul_left
          (sourcePolynomial (.loop (phi b.offset) b.loop b.spin)) (ih)).trans
          (swap_scalar_factors
            (sourcePolynomial (.loop (phi a.offset) a.loop a.spin))
            (sourcePolynomial (.loop (phi b.offset) b.loop b.spin))
            (sourcePolynomial (wordExpression (rest.map (mapTimedLoop phi)))))

theorem orderWord_mapped_source {base : Nat} (phi : Nat → Nat)
    (word : List (TimedLoop base)) :
    RatPolyCoeffEqv
      (sourcePolynomial
        (wordExpression ((orderWord word).map (mapTimedLoop phi))))
      (sourcePolynomial (wordExpression (word.map (mapTimedLoop phi)))) := by
  induction word with
  | nil => exact RatPolyCoeffEqv.refl _
  | cons a rest ih =>
      simp only [orderWord, List.map_cons]
      exact (insertWord_mapped_source phi a (orderWord rest)).trans
        (RatPolyCoeffEqv.mul_left
          (sourcePolynomial (.loop (phi a.offset) a.loop a.spin)) ih)

theorem expand_wordExpression {base : Nat} (word : List (TimedLoop base)) :
    expand (wordExpression word) = [(1, word)] := by
  induction word with
  | nil => rfl
  | cons a rest ih =>
      simp only [wordExpression, expand, ih, multiplyTerms, List.map]
      rfl

#print axioms reverseWindow
#print axioms mapTimedLoop
#print axioms mapTerms
#print axioms wordExpression_mapOffsets
#print axioms expand_mapOffsets
#print axioms reverseWindow_within
#print axioms reverseWindow_involutive
#print axioms reverseWindow_shift
#print axioms reverseWindow_to_mirror
#print axioms orderWord_mapped_source
#print axioms expand_wordExpression

end YMGap.Continuum.BF4WilsonKernelReflectionSyntax
