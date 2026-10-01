/-
The actual represented norm limit of the ORIGINAL dyadic resolvent sequence.
The sharp adjacent error gives an h^2 tail and a 4h^2 two-sided tail bound.
All original representatives, inner moduli and outer rates are computed.
This constructs the limit map, not yet its sector or generator identification.
No physical spacing, continuum, OS or mass-gap conclusion is asserted.
-/

import YMGap.Continuum.BF4WilsonAllNomeDyadicResolvent
import YMGap.Continuum.BF4WilsonAllNomeDyadicContinuity
import YMGap.Continuum.BF4WilsonAllNomeCauchyRows
import YMGap.Continuum.BF4ExactSlabThermodynamicResolventPartial
import YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinFactorialMoments

namespace YMGap.Continuum.BF4WilsonAllNomeResolventLimit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.HalfPow (half half_nonneg)
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeDistance
open YMGap.Continuum.BF4WilsonAllNomeCauchyRows
open YMGap.Continuum.BF4WilsonAllNomeDyadicResolvent
open YMGap.Continuum.BF4WilsonAllNomeDyadicContinuity (rangeModulus scaled_norm_small)
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedApproximation (quarter quarter_pos)
open YMGap.Continuum.BF4ExactSlabThermodynamicResolventPartial
  (scale_congr four_copies four_quarter_scale)
open YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinFactorialMoments (scale_add)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "d" => completedDist hw0 hw1
local notation "D" => seminorm hw0 hw1 (width := width)
local notation "R" => dyadic hw0 hw1
local notation "half" => HalfPow.half
local notation "Class" => Quotient.mk
  (CRealSeminormCompletion.SquaredSeminorm.completionSetoid
    (seminorm hw0 hw1 (width := width)))
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)

private theorem tail_budget (a : Q') :
    Q'.eqv ((a*a*(half*half)+a*a*(half*half))+
      ((half*a)*(half*a)+(half*a)*(half*a))) (a*a) := by
  have h : Q'.eqv ((a*a*(half*half)+a*a*(half*half))+
      ((half*a)*(half*a)+(half*a)*(half*a))) ((4*half*half)*(a*a)) :=
    poly_identity_of_normal_eq
      (.add
        (.add (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1)))
          (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))))
        (.add (.mul (.mul (.var 1) (.var 0)) (.mul (.var 1) (.var 0)))
          (.mul (.mul (.var 1) (.var 0)) (.mul (.var 1) (.var 0)))))
      (.mul (.mul (.mul (.const 4) (.var 1)) (.var 1)) (.mul (.var 0) (.var 0)))
      (by decide) (fun | 0 => a | _ => half)
  exact Q'.eqv_trans _ _ _ h (Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ (by decide : Q'.eqv (4*half*half) 1))
    (Q'.one_mul_eqv _))

/-- The whole forward tail retains the sharp h^2 squared-norm budget. -/
theorem tail_bound (lambda : Q') (hl : (0 : Q') < lambda)
    (start length : Nat) (x : V) :
    RCle (d (R start lambda hl x) (R (start+length) lambda hl x))
      (RCscale (half^start*half^start) (B x x)) := by
  induction length generalizing start with
  | zero =>
      rw [Nat.add_zero, (completedDist_zero_iff hw0 hw1 _ _).mpr rfl]
      have h := RCscale_mono (SumOfSquares.q_mul_self_nonneg (half^start))
        (completedInner_nonnegative hw0 hw1 x)
      rw [RCscale_RCzero] at h
      exact h
  | succ length ih =>
      have hs := dyadic_step_bound hw0 hw1 start lambda hl x
      change RCle (d (R start lambda hl x) (R (start+1) lambda hl x)) _ at hs
      have ht := ih (start+1)
      have h := RCle_trans (completedDist_triangle hw0 hw1
        (R start lambda hl x) (R (start+1) lambda hl x)
        (R ((start+1)+length) lambda hl x))
        (RCadd_le_add (RCadd_le_add hs hs) (RCadd_le_add ht ht))
      rw [← scale_add, ← scale_add, ← scale_add] at h
      have budget : Q'.eqv
          ((half^start*half^start*(half*half)+half^start*half^start*(half*half))+
            (half^(start+1)*half^(start+1)+half^(start+1)*half^(start+1)))
          (half^start*half^start) := tail_budget (half^start)
      rw [scale_congr budget] at h
      simpa only [Nat.add_assoc, Nat.add_comm 1 length] using h

theorem pair_bound (lambda : Q') (hl : (0 : Q') < lambda)
    (start m n : Nat) (hm : start ≤ m) (hn : start ≤ n) (x : V) :
    RCle (d (R m lambda hl x) (R n lambda hl x))
      (RCscale (4*(half^start*half^start)) (B x x)) := by
  have hm' := tail_bound hw0 hw1 lambda hl start (m-start) x
  have hn' := tail_bound hw0 hw1 lambda hl start (n-start) x
  rw [Nat.add_sub_of_le hm, completedDist_symm] at hm'
  rw [Nat.add_sub_of_le hn] at hn'
  have h := RCle_trans (completedDist_triangle hw0 hw1
    (R m lambda hl x) (R start lambda hl x) (R n lambda hl x))
    (RCadd_le_add (RCadd_le_add hm' hm') (RCadd_le_add hn' hn'))
  rw [four_copies, RCscale_RCscale] at h
  exact h

/-- Computed from the supplied original norm ceiling, independent of lambda. -/
def cauchyModulus (X : (D).Cauchy) (epsilon : Q') : Nat :=
  rangeModulus hw0 hw1 X (quarter epsilon)

theorem dyadic_cauchy (lambda : Q') (hl : (0 : Q') < lambda)
    (X : (D).Cauchy) (epsilon : Q') (he : (0 : Q') < epsilon)
    (m n : Nat) (hm : cauchyModulus hw0 hw1 X epsilon ≤ m)
    (hn : cauchyModulus hw0 hw1 X epsilon ≤ n) :
    RCle (d (R m lambda hl (Class X)) (R n lambda hl (Class X))) (rat epsilon) := by
  let k := cauchyModulus hw0 hw1 X epsilon
  have hk : (0 : Q') ≤ half^k := Q'.pow_nonneg half half_nonneg k
  have hk1 : half^k ≤ 1 := HKPos.pow_le_one half_nonneg (by decide) k
  have hsq : half^k*half^k ≤ half^k := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hk1 hk) (Q'.le_of_eqv (Q'.one_mul_eqv _))
  have h := RCle_trans (pair_bound hw0 hw1 lambda hl k m n hm hn (Class X))
    (RCscale_scalar_mono (Q'.mul_le_mul_of_nonneg_left _ _ _ hsq
      (by decide : (0 : Q') ≤ 4)) (completedInner_nonnegative hw0 hw1 (Class X)))
  have hs := RCscale_mono (by decide : (0 : Q') ≤ 4)
    (scaled_norm_small hw0 hw1 X (quarter epsilon) (quarter_pos he) k (Nat.le_refl k))
  rw [RCscale_RCscale, four_quarter_scale] at hs
  exact RCle_trans h hs

def resolventRows (lambda : Q') (hl : (0 : Q') < lambda) (X : (D).Cauchy) :
    RepresentedCauchy hw0 hw1 (width := width) where
  row := fun depth => dyadicRepresentative hw0 hw1 depth lambda hl X
  modulus := cauchyModulus hw0 hw1 X
  isCauchy := by
    intro epsilon he m n hm hn
    change RCle (d (Class (dyadicRepresentative hw0 hw1 m lambda hl X))
      (Class (dyadicRepresentative hw0 hw1 n lambda hl X))) _
    rw [dyadicRepresentative_pin, dyadicRepresentative_pin]
    exact dyadic_cauchy hw0 hw1 lambda hl X epsilon he m n hm hn

theorem resolventRows_pin (lambda : Q') (hl : (0 : Q') < lambda)
    (X : (D).Cauchy) (depth : Nat) :
    rowPoint hw0 hw1 (resolventRows hw0 hw1 lambda hl X) depth =
      R depth lambda hl (Class X) := dyadicRepresentative_pin hw0 hw1 depth lambda hl X

def representedLimit (lambda : Q') (hl : (0 : Q') < lambda) (X : (D).Cauchy) : V :=
  limit hw0 hw1 (resolventRows hw0 hw1 lambda hl X)

/-- The diagonal construction's explicit epsilon/16 rate. -/
def convergenceModulus (lambda : Q') (hl : (0 : Q') < lambda)
    (X : (D).Cauchy) : Q' → Nat := limitRate hw0 hw1 (resolventRows hw0 hw1 lambda hl X)

theorem approximation (lambda : Q') (hl : (0 : Q') < lambda)
    (X : (D).Cauchy) (epsilon : Q') (he : (0 : Q') < epsilon)
    (n : Nat) (hn : convergenceModulus hw0 hw1 lambda hl X epsilon ≤ n) :
    RCle (d (R n lambda hl (Class X)) (representedLimit hw0 hw1 lambda hl X))
      (rat epsilon) := by
  have h := limit_bound hw0 hw1 (resolventRows hw0 hw1 lambda hl X) epsilon he n hn
  rw [resolventRows_pin] at h
  exact h

theorem representedLimit_congr (lambda : Q') (hl : (0 : Q') < lambda)
    (X Y : (D).Cauchy) (h : Class X = Class Y) :
    representedLimit hw0 hw1 lambda hl X = representedLimit hw0 hw1 lambda hl Y := by
  apply limit_independent hw0 hw1
  intro n
  rw [resolventRows_pin, resolventRows_pin, h]

/-- Actual original-carrier limit; its generator/sector identification is separate. -/
def resolvent (lambda : Q') (hl : (0 : Q') < lambda) : V → V :=
  Quotient.lift (representedLimit hw0 hw1 lambda hl)
    (fun X Y h => representedLimit_congr hw0 hw1 lambda hl X Y (Quotient.sound h))

theorem resolvent_pin (lambda : Q') (hl : (0 : Q') < lambda) (X : (D).Cauchy) :
    resolvent hw0 hw1 lambda hl (Class X) = representedLimit hw0 hw1 lambda hl X := rfl

def outputRepresentative (lambda : Q') (hl : (0 : Q') < lambda)
    (X : (D).Cauchy) : (D).Cauchy :=
  CRealSeminormCauchyRows.diagonalCauchy (distanceData hw0 hw1 (width := width))
    (resolventRows hw0 hw1 lambda hl X)

theorem outputRepresentative_pin (lambda : Q') (hl : (0 : Q') < lambda)
    (X : (D).Cauchy) :
    Class (outputRepresentative hw0 hw1 lambda hl X) =
      resolvent hw0 hw1 lambda hl (Class X) := rfl

/-- Both original output stream and outer modulus remain extractable data. -/
def resolventCertificate (lambda : Q') (hl : (0 : Q') < lambda) (X : (D).Cauchy) :
    Σ' Y : (D).Cauchy, Σ' rate : Q' → Nat,
      (Class Y = resolvent hw0 hw1 lambda hl (Class X)) ×'
      (∀ epsilon : Q', (0 : Q') < epsilon → ∀ n, rate epsilon ≤ n →
        RCle (d (R n lambda hl (Class X)) (Class Y)) (rat epsilon)) :=
  ⟨outputRepresentative hw0 hw1 lambda hl X, convergenceModulus hw0 hw1 lambda hl X,
    rfl, approximation hw0 hw1 lambda hl X⟩

#print axioms tail_bound
#print axioms pair_bound
#print axioms cauchyModulus
#print axioms dyadic_cauchy
#print axioms resolventRows
#print axioms resolventRows_pin
#print axioms representedLimit
#print axioms convergenceModulus
#print axioms approximation
#print axioms representedLimit_congr
#print axioms resolvent
#print axioms resolvent_pin
#print axioms outputRepresentative
#print axioms outputRepresentative_pin
#print axioms resolventCertificate

end YMGap.Continuum.BF4WilsonAllNomeResolventLimit
