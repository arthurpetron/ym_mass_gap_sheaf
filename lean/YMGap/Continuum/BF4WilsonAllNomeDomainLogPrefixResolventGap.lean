/-
# Computed log-prefix caps for the EXISTING original sector inverses

Every nonempty rational log prefix sharpens the norm cap of the existing
positive-parameter resolvent and existing zero-shift inverse. The domain
points, range witnesses, original unit, nome, width and ambient fringe
kernel are unchanged. No new inverse or scalar infinite logarithm is built.
The coefficients remain fixed-parameter data: no physical normalization,
spacing-uniform gap or canonical continuum OS realization follows.
-/

import YMGap.Continuum.BF4WilsonAllNomeDomainLogPrefixGap
import YMGap.Continuum.BF4WilsonAllNomeSectorResolventGap
import YMGap.Continuum.BF4WilsonAllNomeSectorZeroResolventEquation

namespace YMGap.Continuum.BF4WilsonAllNomeDomainLogPrefixResolventGap

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate
  (mixFraction mixFraction_positive)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeDomainLogPrefixGap
  (prefixGap domain_log_prefix_gap)
open YMGap.Continuum.BF4WilsonAllNomeSectorResolvent (state)
open YMGap.Continuum.BF4WilsonAllNomeSectorResolventGap
  (state_orthogonal norm_from_coercivity)
open YMGap.Continuum.BF4WilsonAllNomeSectorZeroResolventLimit
  (zeroShift zeroShift_orthogonal)

private theorem scale_add (s t : Q') (a : RC) :
    RCscale (s+t) a = RCadd (RCscale s a) (RCscale t a) := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.add_mul_eqv s t (A.approx n)))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "Sector" => BF4WilsonAllNomeTimeSector.State hw0 hw1 (width := width)
local notation "B" => completedInner hw0 hw1
local notation "U" => unitState hw0 hw1 width
local notation "r" => mixFraction hw0 hw1 width
local notation "gamma" n:arg => prefixGap hw0 hw1 (width := width) n

/-- All computed prefixes are nonnegative, including the empty prefix. -/
theorem prefixGap_nonnegative (n : Nat) : (0 : Q') ≤ gamma n := by
  induction n with
  | zero => change (0 : Q') ≤ 0; decide
  | succ n ih =>
      exact Q'.zero_le_add _ _ ih
        (Q'.mul_nonneg _ _ (Q'.invSucc_nonneg n)
          (Q'.pow_nonneg r (Q'.le_of_lt (mixFraction_positive hw0 hw1 width)) (n+1)))

private theorem prefix_step (n : Nat) : gamma n ≤ gamma (n+1) :=
  Q'.add_le_self_of_nonneg _ _
    (Q'.mul_nonneg _ _ (Q'.invSucc_nonneg n)
      (Q'.pow_nonneg r (Q'.le_of_lt (mixFraction_positive hw0 hw1 width)) (n+1)))

private theorem first_prefix : Q'.eqv (gamma 1) r := by
  change Q'.eqv (0+1*(r*1)) r
  exact poly_identity_of_normal_eq
    (.add (.const 0) (.mul (.const 1) (.mul (.var 0) (.const 1))))
    (.var 0) (by decide) (fun _ => r)

private theorem margin_le_prefix (n : Nat) (hn : 1 ≤ n) : r ≤ gamma n := by
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases hz : n = 0
      · subst n
        exact Q'.ge_of_eqv (first_prefix hw0 hw1 (width := width))
      · exact Q'.le_trans' _ _ _ (ih (by omega)) (prefix_step hw0 hw1 n)

/-- Positivity is constructed from the first actual margin, not assumed. -/
theorem prefixGap_positive (n : Nat) (hn : 1 ≤ n) : (0 : Q') < gamma n :=
  Q'.pos_of_lt_of_le (mixFraction_positive hw0 hw1 width)
    (margin_le_prefix hw0 hw1 n hn)

attribute [local irreducible] prefixGap state zeroShift

private theorem shifted_prefix_coercivity (lambda : Q') (hl : (0 : Q') < lambda)
    (x : Sector) (hx : B U x.val = RCzero) (n : Nat) :
    RCle (RCscale (lambda+gamma n)
      (B (state hw0 hw1 lambda hl x).val (state hw0 hw1 lambda hl x).val))
      (B (state hw0 hw1 lambda hl x).val x.val) := by
  let p := BF4WilsonAllNomeSectorResolvent.domainPoint hw0 hw1 lambda hl x
  have hp : B p.input.val U = RCzero :=
    (completedInner_symm hw0 hw1 p.input.val U).trans
      (state_orthogonal hw0 hw1 lambda hl x hx)
  have hg := domain_log_prefix_gap hw0 hw1 p hp n
  have hi := congrArg (B p.input.val)
    (BF4WilsonAllNomeSectorResolvent.inverse_right hw0 hw1 lambda hl x)
  change B p.input.val
    (completedAdd hw0 hw1 (completedSmul hw0 hw1 lambda p.input.val) p.output.val) =
      B p.input.val x.val at hi
  rw [completedInner_add_right, completedInner_smul_right] at hi
  change RCle (RCscale (lambda+gamma n) (B p.input.val p.input.val)) (B p.input.val x.val)
  rw [scale_add, ← hi]
  exact RCadd_le_add (RCle_refl _) hg

/-- Stronger norm cap for the EXISTING positive-shift original resolvent.
Both the rational prefix and the inverse denominator retain the actual
nome/width. No norm of the unknown vector is inverted. -/
theorem positive_resolvent_prefix_norm_bound (lambda : Q') (hl : (0 : Q') < lambda)
    (x : Sector) (hx : B U x.val = RCzero) (n : Nat) (hn : 1 ≤ n) :
    let hpos := Q'.add_pos hl (prefixGap_positive hw0 hw1 (width := width) n hn)
    let inv := Q'.recipPos (lambda+gamma n) hpos
    RCle (B (state hw0 hw1 lambda hl x).val (state hw0 hw1 lambda hl x).val)
      (RCscale (inv*inv) (B x.val x.val)) := by
  exact norm_from_coercivity hw0 hw1 (lambda+gamma n)
    (Q'.add_pos hl (prefixGap_positive hw0 hw1 (width := width) n hn))
    (state hw0 hw1 lambda hl x).val x.val
    (shifted_prefix_coercivity hw0 hw1 lambda hl x hx n)

/-- Stronger norm cap for the SAME already constructed zero-shift inverse.
The supplied sector input is exactly the output of its existing domain point. -/
theorem zeroShift_prefix_norm_bound (x : Sector) (hx : B U x.val = RCzero)
    (n : Nat) (hn : 1 ≤ n) :
    let inv := Q'.recipPos (gamma n) (prefixGap_positive hw0 hw1 (width := width) n hn)
    RCle (B (zeroShift hw0 hw1 x hx).val (zeroShift hw0 hw1 x hx).val)
      (RCscale (inv*inv) (B x.val x.val)) := by
  let p := BF4WilsonAllNomeSectorZeroResolventEquation.domainPoint hw0 hw1 x hx
  have hp : B p.input.val U = RCzero :=
    (completedInner_symm hw0 hw1 p.input.val U).trans
      (zeroShift_orthogonal hw0 hw1 x hx)
  have hg := domain_log_prefix_gap hw0 hw1 p hp n
  change RCle (RCscale (gamma n)
    (B (zeroShift hw0 hw1 x hx).val (zeroShift hw0 hw1 x hx).val))
    (B (zeroShift hw0 hw1 x hx).val x.val) at hg
  exact norm_from_coercivity hw0 hw1 (gamma n)
    (prefixGap_positive hw0 hw1 (width := width) n hn)
    (zeroShift hw0 hw1 x hx).val x.val hg

#print axioms prefixGap_nonnegative
#print axioms prefixGap_positive
#print axioms positive_resolvent_prefix_norm_bound
#print axioms zeroShift_prefix_norm_bound

end YMGap.Continuum.BF4WilsonAllNomeDomainLogPrefixResolventGap
