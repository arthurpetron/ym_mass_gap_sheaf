/-
The actual zero-shift inverse, restricted to the original witnessed vacuum
complement, is rational-linear. Scaling it by the fixed-nome, fixed-width
form margin gives a contraction on that same sector. This is an algebraic
input for a represented Neumann construction, not a physical Hamiltonian or
a nome/width-uniform spectral assertion.
-/

import YMGap.Continuum.BF4WilsonAllNomeSectorZeroResolvent
import YMGap.Continuum.BF4WilsonAllNomeSectorZeroResolventLimit
import YMGap.Continuum.BF4WilsonAllNomeDerivativeGraphLinear

namespace YMGap.Continuum.BF4WilsonAllNomeSectorVacuumInverse

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeLinearLaws
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomeDistance
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime (completedTime_smul)
open YMGap.Continuum.BF4WilsonAllNomeDyadicDerivativeLaws (derivativeAction_smul)
open YMGap.Continuum.BF4WilsonAllNomeLogCoreGap (coreMargin coreMargin_positive)
open YMGap.Continuum.BF4WilsonAllNomeSectorDerivative (DomainPoint)
open YMGap.Continuum.BF4WilsonAllNomeSectorZeroResolventLimit
  (zeroShift zeroShift_orthogonal zeroShift_norm_bound)
open YMGap.Continuum.RCSignedPairBudget (scale_congr)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "U" => unitState hw0 hw1 width
local notation "S" => completedSmul hw0 hw1
local notation "A" => completedAdd hw0 hw1
local notation "Sub" => completedSub hw0 hw1
local notation "Z" => completedZero hw0 hw1 width
local notation "Sector" => BF4WilsonAllNomeTimeSector.State hw0 hw1 (width := width)
local notation "Point" => DomainPoint hw0 hw1 (width := width)

/-- Witnessed original time-range state, with the SAME original unit removed. -/
structure Centered where
  state : Sector
  orthogonal : B U state.val = RCzero

def val (x : Centered hw0 hw1 (width := width)) : V := x.state.val

private theorem rc_zero_add : RCadd RCzero RCzero = RCzero := by
  refine Quotient.sound (SumOfSquares.Equiv_of_approx_eqv ?_)
  exact fun _ => (by decide : Q'.eqv ((0 : Q')+0) 0)

private theorem rc_zero_sub : RCsub RCzero RCzero = RCzero := by
  refine Quotient.sound (SumOfSquares.Equiv_of_approx_eqv ?_)
  exact fun _ => (by decide : Q'.eqv ((0 : Q')+-0) 0)

private def sectorSmul (c : Q') (x : Sector) : Sector where
  val := S c x.val
  range := BF4WilsonAllNomeTimeRangeLinear.rationalSmul hw0 hw1 c x.range

def zero : Centered hw0 hw1 (width := width) where
  state := BF4WilsonAllNomeTimeSector.zero hw0 hw1
  orthogonal := completedInner_zero_right hw0 hw1 U

def add (x y : Centered hw0 hw1 (width := width)) : Centered hw0 hw1 (width := width) where
  state := BF4WilsonAllNomeTimeSector.add hw0 hw1 x.state y.state
  orthogonal := by
    change B U (A x.state.val y.state.val) = RCzero
    rw [completedInner_add_right, x.orthogonal, y.orthogonal]
    exact rc_zero_add

def smul (c : Q') (x : Centered hw0 hw1 (width := width)) :
    Centered hw0 hw1 (width := width) where
  state := sectorSmul hw0 hw1 c x.state
  orthogonal := by
    change B U (S c x.state.val) = RCzero
    rw [completedInner_smul_right, x.orthogonal, RCscale_RCzero]

def subtract (x y : Centered hw0 hw1 (width := width)) :
    Centered hw0 hw1 (width := width) :=
  add hw0 hw1 x (smul hw0 hw1 (-1) y)

theorem val_zero : val hw0 hw1 (zero hw0 hw1 (width := width)) = Z := rfl

theorem val_add (x y : Centered hw0 hw1 (width := width)) :
    val hw0 hw1 (add hw0 hw1 x y) = A (val hw0 hw1 x) (val hw0 hw1 y) := rfl

theorem val_smul (c : Q') (x : Centered hw0 hw1 (width := width)) :
    val hw0 hw1 (smul hw0 hw1 c x) = S c (val hw0 hw1 x) := rfl

theorem val_subtract (x y : Centered hw0 hw1 (width := width)) :
    val hw0 hw1 (subtract hw0 hw1 x y) = Sub (val hw0 hw1 x) (val hw0 hw1 y) := rfl

/-- The actual original zero-shift inverse, with its original range data. -/
def inverse (x : Centered hw0 hw1 (width := width)) :
    Centered hw0 hw1 (width := width) where
  state := zeroShift hw0 hw1 x.state x.orthogonal
  orthogonal := zeroShift_orthogonal hw0 hw1 x.state x.orthogonal

theorem inverse_congr (x y : Centered hw0 hw1 (width := width))
    (h : val hw0 hw1 x = val hw0 hw1 y) :
    val hw0 hw1 (inverse hw0 hw1 x) = val hw0 hw1 (inverse hw0 hw1 y) :=
  BF4WilsonAllNomeSectorZeroResolvent.inverse_congr hw0 hw1
    x.state y.state x.orthogonal y.orthogonal h

private def domainSmul (c : Q') (p : Point) : Point where
  input := sectorSmul hw0 hw1 c p.input
  output := sectorSmul hw0 hw1 c p.output
  equation := by
    change BF4WilsonAllNomeDyadicDerivative.derivativeAction hw0 hw1 (S c p.input.val) =
      BF4WilsonAllNomeCompletedTime.completedTime hw0 hw1 1 (S c p.output.val)
    rw [derivativeAction_smul, completedTime_smul, p.equation]

private theorem domainSmul_input_pin (c : Q') (p : Point) :
    (domainSmul hw0 hw1 c p).input.val = S c p.input.val := rfl

private theorem domainSmul_output_pin (c : Q') (p : Point) :
    (domainSmul hw0 hw1 c p).output.val = S c p.output.val := rfl

/-- Additivity follows from the actual sector-domain graph and zero-output
uniqueness, not from a total-carrier inverse axiom. -/
theorem inverse_add (x y : Centered hw0 hw1 (width := width)) :
    val hw0 hw1 (inverse hw0 hw1 (add hw0 hw1 x y)) =
      A (val hw0 hw1 (inverse hw0 hw1 x))
        (val hw0 hw1 (inverse hw0 hw1 y)) := by
  let px := BF4WilsonAllNomeSectorZeroResolventEquation.domainPoint hw0 hw1
    x.state x.orthogonal
  let py := BF4WilsonAllNomeSectorZeroResolventEquation.domainPoint hw0 hw1
    y.state y.orthogonal
  let p := BF4WilsonAllNomeSectorDerivative.add hw0 hw1 px py
  let z := add hw0 hw1 x y
  let q := BF4WilsonAllNomeSectorZeroResolventEquation.domainPoint hw0 hw1
    z.state z.orthogonal
  have hp : B U p.input.val = RCzero :=
    (add hw0 hw1 (inverse hw0 hw1 x) (inverse hw0 hw1 y)).orthogonal
  have hq : B U q.input.val = RCzero := (inverse hw0 hw1 z).orthogonal
  have ho : q.output.val = p.output.val := rfl
  exact BF4WilsonAllNomeSectorZeroInjective.input_injective hw0 hw1 q p hq hp ho

/-- Rational homogeneity is witnessed by scaling BOTH original domain
coordinates and then applying centered zero-output uniqueness. -/
theorem inverse_smul (c : Q') (x : Centered hw0 hw1 (width := width)) :
    val hw0 hw1 (inverse hw0 hw1 (smul hw0 hw1 c x)) =
      S c (val hw0 hw1 (inverse hw0 hw1 x)) := by
  let px : Point := BF4WilsonAllNomeSectorZeroResolventEquation.domainPoint hw0 hw1
    x.state x.orthogonal
  let p : Point := domainSmul hw0 hw1 c px
  let z : Centered hw0 hw1 (width := width) := smul hw0 hw1 c x
  let q : Point := BF4WilsonAllNomeSectorZeroResolventEquation.domainPoint hw0 hw1
    z.state z.orthogonal
  have hp : B U p.input.val = RCzero := by
    rw [domainSmul_input_pin]
    exact (smul hw0 hw1 c (inverse hw0 hw1 x)).orthogonal
  have hq : B U q.input.val = RCzero := (inverse hw0 hw1 z).orthogonal
  have ho : q.output.val = p.output.val := by
    rw [domainSmul_output_pin]
    rfl
  have huniq := BF4WilsonAllNomeSectorZeroInjective.input_injective
    hw0 hw1 q p hq hp ho
  change (zeroShift hw0 hw1 z.state z.orthogonal).val =
    S c (zeroShift hw0 hw1 x.state x.orthogonal).val at huniq
  exact huniq

private theorem smul_zero_element (c : Q') : S c Z = Z := by
  calc
    S c Z = S c (S 0 Z) := congrArg (S c) (completedSmul_zero hw0 hw1 Z).symm
    _ = S (c*0) Z := completedSmul_mul hw0 hw1 c 0 Z
    _ = S 0 Z := completedSmul_congr hw0 hw1 (Q'.mul_zero_eqv c) Z
    _ = Z := completedSmul_zero hw0 hw1 Z

theorem inverse_zero : val hw0 hw1 (inverse hw0 hw1 (zero hw0 hw1)) = Z := by
  have h : val hw0 hw1 (zero hw0 hw1 (width := width)) =
      val hw0 hw1 (smul hw0 hw1 0 (zero hw0 hw1 (width := width))) := by
    rw [val_zero, val_smul, val_zero, completedSmul_zero]
  rw [inverse_congr hw0 hw1 _ _ h, inverse_smul,
    completedSmul_zero]

theorem inverse_subtract (x y : Centered hw0 hw1 (width := width)) :
    val hw0 hw1 (inverse hw0 hw1 (subtract hw0 hw1 x y)) =
      Sub (val hw0 hw1 (inverse hw0 hw1 x))
        (val hw0 hw1 (inverse hw0 hw1 y)) := by
  unfold subtract
  rw [inverse_add, inverse_smul]
  rfl

/-- The fixed-margin normalization stays within the original sector. -/
def contraction (x : Centered hw0 hw1 (width := width)) :
    Centered hw0 hw1 (width := width) :=
  smul hw0 hw1 (coreMargin hw0 hw1 width) (inverse hw0 hw1 x)

theorem contraction_congr (x y : Centered hw0 hw1 (width := width))
    (h : val hw0 hw1 x = val hw0 hw1 y) :
    val hw0 hw1 (contraction hw0 hw1 x) =
      val hw0 hw1 (contraction hw0 hw1 y) := by
  unfold contraction
  rw [val_smul, val_smul, inverse_congr hw0 hw1 x y h]

theorem contraction_zero :
    val hw0 hw1 (contraction hw0 hw1 (zero hw0 hw1 (width := width))) = Z := by
  rw [contraction, val_smul, inverse_zero, smul_zero_element]

theorem contraction_add (x y : Centered hw0 hw1 (width := width)) :
    val hw0 hw1 (contraction hw0 hw1 (add hw0 hw1 x y)) =
      A (val hw0 hw1 (contraction hw0 hw1 x))
        (val hw0 hw1 (contraction hw0 hw1 y)) := by
  rw [contraction, val_smul, inverse_add, completedSmul_add]
  rfl

theorem contraction_smul (c : Q') (x : Centered hw0 hw1 (width := width)) :
    val hw0 hw1 (contraction hw0 hw1 (smul hw0 hw1 c x)) =
      S c (val hw0 hw1 (contraction hw0 hw1 x)) := by
  rw [contraction, val_smul, inverse_smul, contraction, val_smul,
    completedSmul_mul, completedSmul_mul]
  exact completedSmul_congr hw0 hw1
    (Q'.mul_comm_eqv (coreMargin hw0 hw1 width) c) _

theorem contraction_subtract (x y : Centered hw0 hw1 (width := width)) :
    val hw0 hw1 (contraction hw0 hw1 (subtract hw0 hw1 x y)) =
      Sub (val hw0 hw1 (contraction hw0 hw1 x))
        (val hw0 hw1 (contraction hw0 hw1 y)) := by
  change val hw0 hw1 (contraction hw0 hw1
    (add hw0 hw1 x (smul hw0 hw1 (-1) y))) = _
  rw [contraction_add, contraction_smul]
  rfl

/-- The zero-shift inverse's reciprocal margin cancels exactly against the
margin scaling. The cap depends on nome and width only through this margin. -/
theorem contraction_norm_bound (x : Centered hw0 hw1 (width := width)) :
    RCle (B (val hw0 hw1 (contraction hw0 hw1 x))
        (val hw0 hw1 (contraction hw0 hw1 x)))
      (B (val hw0 hw1 x) (val hw0 hw1 x)) := by
  let d := coreMargin hw0 hw1 width
  let r := Q'.recipPos d (coreMargin_positive hw0 hw1)
  have h := zeroShift_norm_bound hw0 hw1 x.state x.orthogonal
  have hs := RCscale_mono (SumOfSquares.q_mul_self_nonneg d) h
  change RCle (B (S d (val hw0 hw1 (inverse hw0 hw1 x)))
    (S d (val hw0 hw1 (inverse hw0 hw1 x))))
    (B (val hw0 hw1 x) (val hw0 hw1 x))
  rw [completedInner_smul_left, completedInner_smul_right,
    RCscale_RCscale]
  rw [RCscale_RCscale] at hs
  have hc : Q'.eqv ((d*d)*(r*r)) 1 := by
    have hcr : Q'.eqv (d*r) 1 := Q'.mul_recipPos_eqv d (coreMargin_positive hw0 hw1)
    exact Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq
        (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1)))
        (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))
        (by decide) (fun | 0 => d | _ => r))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hcr)
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hcr)
          (Q'.one_mul_eqv 1)))
  rwa [scale_congr hc, RCscale_one] at hs

theorem contraction_dist_bound (x y : Centered hw0 hw1 (width := width)) :
    RCle (completedDist hw0 hw1
      (val hw0 hw1 (contraction hw0 hw1 x))
      (val hw0 hw1 (contraction hw0 hw1 y)))
      (completedDist hw0 hw1 (val hw0 hw1 x) (val hw0 hw1 y)) := by
  unfold completedDist
  rw [← contraction_subtract hw0 hw1 x y, ← val_subtract hw0 hw1 x y]
  exact contraction_norm_bound hw0 hw1 (subtract hw0 hw1 x y)

#print axioms Centered
#print axioms zero
#print axioms add
#print axioms smul
#print axioms subtract
#print axioms inverse
#print axioms inverse_add
#print axioms inverse_smul
#print axioms inverse_zero
#print axioms inverse_subtract
#print axioms contraction
#print axioms contraction_zero
#print axioms contraction_add
#print axioms contraction_smul
#print axioms contraction_subtract
#print axioms contraction_congr
#print axioms contraction_norm_bound
#print axioms contraction_dist_bound

end YMGap.Continuum.BF4WilsonAllNomeSectorVacuumInverse
