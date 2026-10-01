/-
# Constructed rational subgap resolvents on the original vacuum complement

For every rational 0 <= a < delta, a normalized geometric iteration of the
actual zero-shift inverse produces an original domain point solving
(H-a I)u=x. Both inverse identities and the sharp cap 1/(delta-a) concern
the existing witnessed domain and its original vacuum complement.

This is at fixed nome and width. No physical OS identification, real or
complex spectral calculus, spacing-uniform mass, or ambient inverse is
asserted. Every series and range witness is computed on the SAME carrier.
-/

import YMGap.Continuum.BF4WilsonAllNomeSectorNeumannLimit
import YMGap.Continuum.BF4WilsonAllNomeSectorSubgapInjective

namespace YMGap.Continuum.BF4WilsonAllNomeSectorSubgapResolvent

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeLinearLaws
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomeCompletedRealScalar (completed_eq_of_pairings)
open YMGap.Continuum.BF4WilsonAllNomeLogCoreGap (coreMargin coreMargin_positive)
open YMGap.Continuum.BF4WilsonAllNomeSectorDerivative (DomainPoint)
open YMGap.Continuum.BF4WilsonAllNomeSectorResolvent (shifted)
open YMGap.Continuum.BF4WilsonAllNomeSectorVacuumInverse
  (Centered val val_smul inverse inverse_smul contraction)
open YMGap.Continuum.BF4WilsonAllNomeSectorNeumannLimit (normalized fixed_point)
open YMGap.Continuum.RCSignedPairBudget (scale_congr)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "C" => Centered hw0 hw1 (width := width)
local notation "v" => val hw0 hw1
local notation "B" => completedInner hw0 hw1
local notation "U" => unitState hw0 hw1 width
local notation "A" => completedAdd hw0 hw1
local notation "S" => completedSmul hw0 hw1
local notation "delta" => coreMargin hw0 hw1 width
local notation "Point" => DomainPoint hw0 hw1 (width := width)

/-- The actual geometric ratio retains the original margin dependence. -/
def ratio (width : Nat) (a : Q') : Q' :=
  a * Q'.recipPos (coreMargin hw0 hw1 width) (coreMargin_positive hw0 hw1)

theorem ratio_nonnegative (a : Q') (ha0 : (0 : Q') ≤ a) :
    (0 : Q') ≤ ratio hw0 hw1 width a :=
  Q'.mul_nonneg _ _ ha0 (Q'.le_of_lt (Q'.recipPos_pos _ _))

theorem ratio_lt_one (a : Q') (ha : a < delta) :
    ratio hw0 hw1 width a < (1 : Q') := by
  let r := Q'.recipPos delta (coreMargin_positive hw0 hw1)
  have h := Q'.mul_lt_mul_of_pos_left (Q'.recipPos_pos delta
    (coreMargin_positive hw0 hw1)) ha
  have hc : Q'.eqv (r*delta) 1 := Q'.eqv_trans _ _ _
    (Q'.mul_comm_eqv _ _) (Q'.mul_recipPos_eqv _ _)
  exact ContinuumClosureProgram.q'_lt_of_lt_of_le
    (Q'.lt_of_le_of_lt (Q'.le_of_eqv (Q'.mul_comm_eqv _ _)) h)
    (Q'.le_of_eqv hc)

private theorem ratio_cancel (a : Q') : Q'.eqv (ratio hw0 hw1 width a * delta) a :=
  Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _)
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _
      (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.mul_recipPos_eqv _ _)))
      (Q'.mul_one_eqv _))

private def factor (a : Q') (ha : a < delta) : Q' :=
  Q'.recipPos (1-ratio hw0 hw1 width a)
    (HKPos.one_sub_pos (ratio_lt_one hw0 hw1 a ha))

/-- The source is constructed by the convergent original-sector iteration. -/
def source (a : Q') (ha0 : (0 : Q') ≤ a) (ha : a < delta) (x : C) : C :=
  BF4WilsonAllNomeSectorVacuumInverse.smul hw0 hw1 (factor hw0 hw1 a ha)
    (normalized hw0 hw1 (ratio hw0 hw1 width a)
      (ratio_nonnegative hw0 hw1 a ha0) (ratio_lt_one hw0 hw1 a ha) x)

/-- Actual original domain point with output equal to the computed source. -/
def domainPoint (a : Q') (ha0 : (0 : Q') ≤ a) (ha : a < delta) (x : C) : Point :=
  BF4WilsonAllNomeSectorZeroResolventEquation.domainPoint hw0 hw1
    (source hw0 hw1 a ha0 ha x).state (source hw0 hw1 a ha0 ha x).orthogonal

theorem input_orthogonal (a : Q') (ha0 : (0 : Q') ≤ a) (ha : a < delta) (x : C) :
    B U (domainPoint hw0 hw1 a ha0 ha x).input.val = RCzero :=
  (inverse hw0 hw1 (source hw0 hw1 a ha0 ha x)).orthogonal

/-- The negative rational shift of the original derivative reaches x exactly. -/
theorem inverse_right (a : Q') (ha0 : (0 : Q') ≤ a) (ha : a < delta) (x : C) :
    (shifted hw0 hw1 (-a) (domainPoint hw0 hw1 a ha0 ha x)).val = v x := by
  let q := ratio hw0 hw1 width a
  let t := normalized hw0 hw1 q (ratio_nonnegative hw0 hw1 a ha0)
    (ratio_lt_one hw0 hw1 a ha) x
  let c := factor hw0 hw1 a ha
  have ht : v t = A (S (1-q) (v x)) (S a (v (inverse hw0 hw1 t))) := by
    have h := fixed_point hw0 hw1 q (ratio_nonnegative hw0 hw1 a ha0)
      (ratio_lt_one hw0 hw1 a ha) x
    change v t = A (S (1-q) (v x))
      (S q (v (contraction hw0 hw1 t))) at h
    rw [contraction, val_smul, completedSmul_mul,
      completedSmul_congr hw0 hw1 (ratio_cancel hw0 hw1 a)] at h
    exact h
  have hi : (domainPoint hw0 hw1 a ha0 ha x).input.val =
      S c (v (inverse hw0 hw1 t)) :=
    inverse_smul hw0 hw1 c t
  have ho : (domainPoint hw0 hw1 a ha0 ha x).output.val = S c (v t) := rfl
  have hc : Q'.eqv (c*(1-q)) 1 := Q'.eqv_trans _ _ _
    (Q'.mul_comm_eqv _ _) (Q'.mul_recipPos_eqv _ _)
  apply completed_eq_of_pairings hw0 hw1
  intro z
  change B (A (S (-a) (domainPoint hw0 hw1 a ha0 ha x).input.val)
    (domainPoint hw0 hw1 a ha0 ha x).output.val) z = B (v x) z
  rw [hi, ho, ht]
  simp only [completedInner_add_left, completedInner_smul_left,
    RCscale_RCadd, RCscale_RCscale]
  rw [scale_congr hc, RCscale_one]
  refine Quotient.inductionOn₂ (B (v (inverse hw0 hw1 t)) z) (B (v x) z) ?_
  intro X Y
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.mul (.mul (.neg (.var 2)) (.var 3)) (.var 0))
        (.add (.var 1) (.mul (.mul (.var 3) (.var 2)) (.var 0))))
      (.var 1) (by decide)
      (fun | 0 => X.approx n | 1 => Y.approx n | 2 => a | _ => c)))

/-- Every centered domain point has a centered shifted value in the SAME sector. -/
def shiftedCentered (a : Q') (p : Point) (hp : B U p.input.val = RCzero) : C where
  state := shifted hw0 hw1 (-a) p
  orthogonal := by
    change B U (A (S (-a) p.input.val) p.output.val) = RCzero
    rw [completedInner_add_right, completedInner_smul_right, hp,
      BF4WilsonAllNomeSectorZeroResolvent.output_orthogonal,
      RCscale_RCzero]
    exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
      (fun _ => (by decide : Q'.eqv ((0 : Q')+0) 0)))

/-- The constructed inverse recovers EVERY original centered domain input. -/
theorem inverse_left (a : Q') (ha0 : (0 : Q') ≤ a) (ha : a < delta)
    (p : Point) (hp : B U p.input.val = RCzero) :
    (domainPoint hw0 hw1 a ha0 ha (shiftedCentered hw0 hw1 a p hp)).input.val =
      p.input.val := by
  apply BF4WilsonAllNomeSectorSubgapInjective.input_injective hw0 hw1 a ha
    _ p (input_orthogonal hw0 hw1 a ha0 ha _) hp
  exact inverse_right hw0 hw1 a ha0 ha (shiftedCentered hw0 hw1 a p hp)

/-- Sharp bound on the ACTUAL constructed inverse. The reciprocal distance
to the original form margin remains explicit; no spacing uniformity follows. -/
theorem norm_bound (a : Q') (ha0 : (0 : Q') ≤ a) (ha : a < delta) (x : C) :
    let d := delta-a
    let r := Q'.recipPos d (ClusteringImpliesGap.sub_pos_of_lt ha)
    RCle (B (domainPoint hw0 hw1 a ha0 ha x).input.val
        (domainPoint hw0 hw1 a ha0 ha x).input.val)
      (RCscale (r*r) (B (v x) (v x))) := by
  have h := BF4WilsonAllNomeSectorSubgapInjective.norm_bound hw0 hw1 a ha
    (domainPoint hw0 hw1 a ha0 ha x) (input_orthogonal hw0 hw1 a ha0 ha x)
  rw [inverse_right] at h
  exact h

#print axioms ratio_nonnegative
#print axioms ratio_lt_one
#print axioms source
#print axioms domainPoint
#print axioms input_orthogonal
#print axioms inverse_right
#print axioms shiftedCentered
#print axioms inverse_left
#print axioms norm_bound

end YMGap.Continuum.BF4WilsonAllNomeSectorSubgapResolvent
