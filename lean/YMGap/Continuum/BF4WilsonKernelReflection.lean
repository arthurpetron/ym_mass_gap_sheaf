/-
# Original-window time reflection is the SAME kernel adjoint

Reverse the actual offsets in a window of duration H, retaining its SU(2)
loops, real characters and signed coefficients. Interval concatenation and
source-polynomial descent identify the resulting kernel with the adjoint on
EVERY input of the existing completion. No vacuum-only argument is used.

The consumer is the literal original reflected product: its duration-2H
kernel is K* K, hence its pairing is a squared norm on every completed input.
This joins original reflection syntax to the checked operator calculus. It
does not construct the separate canonical OS/GNS map, continuum scaling,
full observable coverage, physical mass, or an every-group QFT.
-/

import YMGap.Continuum.BF4WilsonKernelReflectionSyntax
import YMGap.Continuum.BF4WilsonKernelHaarIdentity

namespace YMGap.Continuum.BF4WilsonKernelReflection

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe (SourceLoop)
open YMGap.Continuum.BF4WilsonTimedWord
open YMGap.Continuum.BF4WilsonTimedWordOrder
open YMGap.Continuum.BF4WilsonExpressionExpansion
open YMGap.Continuum.BF4WilsonKernelReflectionSyntax
open YMGap.Continuum.BF4WilsonChronologicalProgram
open YMGap.Continuum.BF4WilsonChronologicalOperator
open YMGap.Continuum.BF4WilsonChronologicalOperatorAlgebra
open YMGap.Continuum.BF4WilsonChronologicalKernel
open YMGap.Continuum.BF4WilsonKernelConcatenation
open YMGap.Continuum.BF4WilsonKernelHaarIdentity
open YMGap.Continuum.BF4WilsonSpatialUnionSeminorm
open YMGap.Continuum.BF4WilsonSpatialUnionLinear
open YMGap.Continuum.BF4WilsonSpatialUnionLinearLaws
open YMGap.Continuum.BF4WilsonSpatialUnionBilinear
open YMGap.Continuum.BF4WilsonSpatialUnionPairingData
open YMGap.Continuum.BF4WilsonSpatialUnionTimeZeroMultiplier (completedMultiply)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)

local notation "V" => UnionCompletion hw0 hw1 hsmall hd hs
local notation "B" => completedInner hw0 hw1 hsmall hd hs
local notation "Op" => act hw0 hw1 hsmall hd hs
local notation "Adj" => adjointAct hw0 hw1 hsmall hd hs
local notation "T" => completedTime hw0 hw1 hsmall hd hs
local notation "M" => completedMultiply hw0 hw1 hsmall hd hs

private theorem kernel_coeff_congr {base : Nat} (H : Nat) (e f : WindowExpression base)
    (he : Within H e) (hf : Within H f)
    (h : RatPolyCoeffEqv (sourcePolynomial e) (sourcePolynomial f)) (x : V) :
    Op (compileKernel H e) x = Op (compileKernel H f) x :=
  compileKernel_padded_congr hw0 hw1 hsmall hd hs H e f he hf
    (PaddedPolynomialCoeffEqv.of_coeff h) x

private theorem kernel_word {base : Nat} (H : Nat) (word : List (TimedLoop base)) (x : V) :
    Op (compileKernel H (wordExpression word)) x = Op (wordKernel H word) x := by
  simp only [compileKernel, expand_wordExpression, termsKernel, act,
    completedSmul_one, completedAdd_zero]

private theorem kernel_loop_zero {base : Nat} (L : SourceLoop base) (spin : Nat) (x : V) :
    Op (compileKernel 0 (.loop 0 L spin)) x = M L spin x := by
  simp only [compileKernel, expand, termsKernel, wordKernel, orderWord,
    insertWord, orderedKernel, act, Nat.sub_zero, completedTime_zero,
    completedSmul_one, completedAdd_zero]

private theorem reflected_cons_source {base : Nat} (H : Nat) (a : TimedLoop base)
    (rest : List (TimedLoop base)) (ha : a.offset ≤ H) (hr : WordWithin a.offset rest) :
    RatPolyCoeffEqv
      (sourcePolynomial (graft (H-a.offset)
        (.mul (reverseWindow a.offset (wordExpression rest)) (.loop 0 a.loop a.spin)) .one))
      (sourcePolynomial (reverseWindow H (wordExpression (a :: rest)))) := by
  have hshift := reverseWindow_shift H a.offset ha (wordExpression rest)
    ((wordExpression_within a.offset rest).mpr hr)
  change RatPolyCoeffEqv
    (polyMul (polyMul (sourcePolynomial (shift (H-a.offset) (reverseWindow a.offset (wordExpression rest))))
      (sourcePolynomial (.loop (0+(H-a.offset)) a.loop a.spin))) polyOne)
    (polyMul (sourcePolynomial (.loop (H-a.offset) a.loop a.spin))
      (sourcePolynomial (reverseWindow H (wordExpression rest))))
  rw [hshift, Nat.zero_add]
  exact (RatPolyCoeffEqv.mul_one _).trans (RatPolyCoeffEqv.mul_comm _ _)

/-- The reversed finite interval, including empty propagation, is the adjoint.
The proof uses the original graft/concatenation theorem, not vacuum equality. -/
theorem orderedKernel_adjoint {base : Nat} (word : List (TimedLoop base))
    (hdsc : Descending word) (H : Nat) (hword : WordWithin H word) (x : V) :
    Adj (orderedKernel H word) x =
      Op (compileKernel H (reverseWindow H (wordExpression word))) x := by
  induction word generalizing H x with
  | nil =>
      simpa only [orderedKernel, adjointAct, wordExpression, reverseWindow, mapOffsets] using
        (compileKernel_one hw0 hw1 hsmall hd hs (base := base) H x).symm
  | cons a rest ih =>
      have ha := ((wordWithin_cons H a rest).mp hword).1
      have hrev := reverseWindow_within a.offset (wordExpression rest)
      have hmul : Within a.offset
          (.mul (reverseWindow a.offset (wordExpression rest)) (.loop 0 a.loop a.spin)) :=
        ⟨hrev, Nat.zero_le _⟩
      simp only [orderedKernel, adjointAct]
      rw [ih hdsc.2 a.offset hdsc.1]
      rw [← kernel_loop_zero hw0 hw1 hsmall hd hs a.loop a.spin]
      have hfirst := compileKernel_concat hw0 hw1 hsmall hd hs a.offset 0
        (reverseWindow a.offset (wordExpression rest)) (.loop 0 a.loop a.spin)
        hrev (Nat.le_refl 0) (T (H-a.offset) x)
      simp only [Nat.add_zero, graft, shift_zero] at hfirst
      refine hfirst.trans ?_
      have hsecond := compileKernel_concat hw0 hw1 hsmall hd hs a.offset (H-a.offset)
        (.mul (reverseWindow a.offset (wordExpression rest)) (.loop 0 a.loop a.spin)) .one
        hmul True.intro x
      have hH : a.offset+(H-a.offset) = H := by omega
      simp only [compileKernel_one, hH] at hsecond
      refine hsecond.trans ?_
      apply kernel_coeff_congr hw0 hw1 hsmall hd hs H _ _
        (by
          have hg := graft_within _ (.one : WindowExpression base) hmul
            (show Within (H-a.offset) (.one : WindowExpression base) from True.intro)
          simpa only [hH] using hg)
        (reverseWindow_within H (wordExpression (a :: rest)))
      exact reflected_cons_source H a rest ha hdsc.1

private theorem wordKernel_adjoint {base : Nat} (H : Nat) (word : List (TimedLoop base))
    (hword : WordWithin H word) (x : V) :
    Adj (wordKernel H word) x =
      Op (wordKernel H (word.map (mapTimedLoop (fun t => H-t)))) x := by
  refine (orderedKernel_adjoint hw0 hw1 hsmall hd hs (orderWord word)
    (orderWord_descending word) H (orderWord_within H word hword) x).trans ?_
  have h := kernel_coeff_congr hw0 hw1 hsmall hd hs H
    (reverseWindow H (wordExpression (orderWord word)))
    (reverseWindow H (wordExpression word))
    (reverseWindow_within _ _) (reverseWindow_within _ _)
    (by simpa only [wordExpression_mapOffsets] using
      orderWord_mapped_source (fun t => H-t) word) x
  refine h.trans ?_
  unfold reverseWindow
  rw [← wordExpression_mapOffsets]
  exact kernel_word hw0 hw1 hsmall hd hs H _ x

private theorem termsKernel_adjoint {base : Nat} (H : Nat)
    (terms : List (Q' × List (TimedLoop base)))
    (hterms : ∀ term, term ∈ terms → WordWithin H term.2) (x : V) :
    Adj (termsKernel H terms) x =
      Op (termsKernel H (mapTerms (fun t => H-t) terms)) x := by
  induction terms with
  | nil => rfl
  | cons a rest ih =>
      have ha := hterms a List.mem_cons_self
      have hr : ∀ term, term ∈ rest → WordWithin H term.2 :=
        fun term ht => hterms term (List.mem_cons_of_mem a ht)
      change completedAdd hw0 hw1 hsmall hd hs
        (completedSmul hw0 hw1 hsmall hd hs a.1 (Adj (wordKernel H a.2) x))
        (Adj (termsKernel H rest) x) =
        completedAdd hw0 hw1 hsmall hd hs
          (completedSmul hw0 hw1 hsmall hd hs a.1
            (Op (wordKernel H (a.2.map (mapTimedLoop (fun t => H-t)))) x))
          (Op (termsKernel H (mapTerms (fun t => H-t) rest)) x)
      rw [wordKernel_adjoint hw0 hw1 hsmall hd hs H a.2 ha, ih hr]

/-- Time reversal of the ORIGINAL bounded window, not just reversed program
syntax, gives the adjoint on the SAME completed carrier. -/
theorem compileKernel_adjoint {base : Nat} (H : Nat) (e : WindowExpression base)
    (he : Within H e) (x : V) :
    Adj (compileKernel H e) x = Op (compileKernel H (reverseWindow H e)) x := by
  simp only [compileKernel, reverseWindow, expand_mapOffsets]
  exact termsKernel_adjoint hw0 hw1 hsmall hd hs H (expand e) (expand_within H e he) x

/-- Literal source reflection and concatenation become the actual mixed
adjoint product. No replacement of the original observable or action occurs. -/
theorem kernel_reflected_product {base : Nat} (H : Nat) (e f : WindowExpression base)
    (he : Within H e) (hf : Within H f) (x : V) :
    Op (compileKernel (2*H) (.mul (mirror H e) f)) x =
      Adj (compileKernel H e) (Op (compileKernel H f) x) := by
  rw [compileKernel_adjoint hw0 hw1 hsmall hd hs H e he]
  have h := compileKernel_concat hw0 hw1 hsmall hd hs H H
    (reverseWindow H e) f (reverseWindow_within H e) hf x
  simpa only [graft, reverseWindow_to_mirror H e he,
    show H+H=2*H by omega] using h.symm

/-- Every original reflected mixed window has its SAME-operator Gram pin,
with arbitrary completed left and right inputs. -/
theorem kernel_reflected_pairing {base : Nat} (H : Nat) (e f : WindowExpression base)
    (he : Within H e) (hf : Within H f) (x y : V) :
    B x (Op (compileKernel (2*H) (.mul (mirror H e) f)) y) =
      B (Op (compileKernel H e) x) (Op (compileKernel H f) y) := by
  rw [kernel_reflected_product hw0 hw1 hsmall hd hs H e f he hf,
    ← adjoint_balance]

/-- Positivity belongs to the kernel of the actual reflected original
window, not merely to an abstract formal star-square. -/
theorem kernel_reflected_square_nonnegative {base : Nat} (H : Nat)
    (e : WindowExpression base) (he : Within H e) (x : V) :
    RCnonneg (B x (Op (compileKernel (2*H) (.mul (mirror H e) e)) x)) := by
  rw [kernel_reflected_pairing hw0 hw1 hsmall hd hs H e e he he]
  exact completedInner_nonnegative hw0 hw1 hsmall hd hs _

end YMGap.Continuum.BF4WilsonKernelReflection

#print axioms YMGap.Continuum.BF4WilsonKernelReflection.orderedKernel_adjoint
#print axioms YMGap.Continuum.BF4WilsonKernelReflection.compileKernel_adjoint
#print axioms YMGap.Continuum.BF4WilsonKernelReflection.kernel_reflected_product
#print axioms YMGap.Continuum.BF4WilsonKernelReflection.kernel_reflected_pairing
#print axioms YMGap.Continuum.BF4WilsonKernelReflection.kernel_reflected_square_nonnegative
