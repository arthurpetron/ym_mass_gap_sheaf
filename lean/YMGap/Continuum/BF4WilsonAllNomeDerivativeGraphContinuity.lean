/-
# Small dyadic-time continuity at witnessed derivative-graph outputs

An output limit of actual derivative images inherits continuity under the
original dyadic time action from one supplied source representative and its
own modulus. No uniform bound or convergence of the preimage sequence is
assumed or selected.
-/

import YMGap.Continuum.BF4WilsonAllNomeDerivativeGraph
import YMGap.Continuum.BF4WilsonAllNomeDyadicContinuity
import YMGap.Continuum.BF4WilsonAllNomeDyadicDerivativeContinuity

namespace YMGap.Continuum.BF4WilsonAllNomeDerivativeGraphContinuity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeDistance
open YMGap.Continuum.BF4WilsonAllNomeGraphDistance
open YMGap.Continuum.BF4WilsonAllNomeCauchyRows
open YMGap.Continuum.BF4WilsonAllNomeDyadicSemigroup (meshAction)
open YMGap.Continuum.BF4WilsonAllNomeDyadicEnergy (mesh_distance_bound)
open YMGap.Continuum.BF4WilsonAllNomeDyadicContinuity (rangeModulus range_smallTime)
open YMGap.Continuum.BF4WilsonAllNomeDyadicDerivative (derivativeAction)
open YMGap.Continuum.BF4WilsonAllNomeDyadicDerivativeContinuity
  (derivativeContinuityModulus derivative_smallTime)
open YMGap.Continuum.BF4WilsonAllNomeDerivativeGraph (GraphLimit)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "D" => seminorm hw0 hw1 (width := width)
local notation "V" => Completion hw0 hw1 width
local notation "d" => completedDist hw0 hw1
local notation "S" => meshAction hw0 hw1
local notation "F" => derivativeAction hw0 hw1
local notation "Class" => Quotient.mk
  (CRealSeminormCompletion.SquaredSeminorm.completionSetoid
    (seminorm hw0 hw1 (width := width)))
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)

private def tenth (e : Q') : Q' := Q'.invSucc 9 * e

private theorem tenth_positive {e : Q'} (he : (0 : Q') < e) :
    (0 : Q') < tenth e := Q'.mul_pos (Q'.invSucc_pos 9) he

private theorem ten_tenths (e : Q') :
    RCadd (RCadd (rat (tenth e)) (rat (tenth e)))
      (RCadd
        (RCadd (RCadd (rat (tenth e)) (rat (tenth e)))
          (RCadd (rat (tenth e)) (rat (tenth e))))
        (RCadd (RCadd (rat (tenth e)) (rat (tenth e)))
          (RCadd (rat (tenth e)) (rat (tenth e))))) = rat e := by
  apply Quotient.sound
  apply SumOfSquares.Equiv_of_approx_eqv
  intro n
  change Q'.eqv
    ((tenth e+tenth e)+(((tenth e+tenth e)+(tenth e+tenth e))+((tenth e+tenth e)+(tenth e+tenth e)))) e
  have hsum : Q'.eqv
      ((tenth e+tenth e)+(((tenth e+tenth e)+(tenth e+tenth e))+((tenth e+tenth e)+(tenth e+tenth e))))
      (10*tenth e) :=
    RingNormaliser.poly_identity_of_normal_eq
      (.add (.add (.var 0) (.var 0))
        (.add (.add (.add (.var 0) (.var 0)) (.add (.var 0) (.var 0)))
          (.add (.add (.var 0) (.var 0)) (.add (.var 0) (.var 0)))))
      (.mul (.const 10) (.var 0)) (by decide) (fun _ => tenth e)
  exact Q'.eqv_trans _ _ _ hsum
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _
          (by decide : Q'.eqv (10*Q'.invSucc 9) (1 : Q')))
        (Q'.one_mul_eqv e)))

/-- Use the one supplied source at the graph's tenth-epsilon output cutoff;
its own derivative continuity threshold then controls all fine dyadic steps. -/
def outputModulus {input output : V} (G : GraphLimit hw0 hw1 input output)
    (preimages : Nat → (D).Cauchy)
    (_hpin : ∀ n, Class (preimages n) = G.source n) (epsilon : Q') : Nat :=
  derivativeContinuityModulus hw0 hw1
    (preimages (G.modulus (tenth epsilon))) (tenth epsilon)

/-- The actual derivative-graph output is continuous at zero for the original
small dyadic time action, with a retained Type-level modulus. -/
theorem output_smallTime {input output : V} (G : GraphLimit hw0 hw1 input output)
    (preimages : Nat → (D).Cauchy)
    (hpin : ∀ n, Class (preimages n) = G.source n)
    (epsilon : Q') (he : (0 : Q') < epsilon) (depth steps : Nat)
    (hsmall : steps*2^(outputModulus hw0 hw1 G preimages hpin epsilon) ≤ 2^depth) :
    RCle (d (S depth steps output) output) (rat epsilon) := by
  let delta := tenth epsilon
  have hd : (0 : Q') < delta := tenth_positive he
  let n := G.modulus delta
  let a := F (Class (preimages n))
  have hclose : RCle (d a output) (rat delta) := by
    dsimp only [a]
    rw [hpin n]
    exact (G.bound delta hd n (Nat.le_refl n)).2
  have hleft : RCle (d (S depth steps output) (S depth steps a)) (rat delta) :=
    RCle_trans (mesh_distance_bound hw0 hw1 depth steps output a)
      (by rw [completedDist_symm]; exact hclose)
  have hmiddle : RCle (d (S depth steps a) a) (rat delta) := by
    exact derivative_smallTime hw0 hw1 (preimages n) delta hd depth steps hsmall
  have hright := RCle_trans
    (completedDist_triangle hw0 hw1 (S depth steps a) a output)
    (RCadd_le_add (RCadd_le_add hmiddle hmiddle) (RCadd_le_add hclose hclose))
  have h := RCle_trans
    (completedDist_triangle hw0 hw1 (S depth steps output) (S depth steps a) output)
    (RCadd_le_add (RCadd_le_add hleft hleft) (RCadd_le_add hright hright))
  rwa [ten_tenths] at h

/-- The computed small-dyadic continuity data for a graph output. -/
def outputContinuityCertificate {input output : V}
    (G : GraphLimit hw0 hw1 input output)
    (preimages : Nat → (D).Cauchy)
    (hpin : ∀ n, Class (preimages n) = G.source n)
    (epsilon : Q') (he : (0 : Q') < epsilon) :
    {k : Nat // ∀ depth steps, steps*2^k ≤ 2^depth →
      RCle (d (S depth steps output) output) (rat epsilon)} :=
  ⟨outputModulus hw0 hw1 G preimages hpin epsilon,
    output_smallTime hw0 hw1 G preimages hpin epsilon he⟩

/-- Input continuity is inherited in the same way from its supplied original
preimages, using the range estimate rather than the derivative estimate. -/
def inputModulus {input output : V} (G : GraphLimit hw0 hw1 input output)
    (preimages : Nat → (D).Cauchy)
    (_hpin : ∀ n, Class (preimages n) = G.source n) (epsilon : Q') : Nat :=
  rangeModulus hw0 hw1 (preimages (G.modulus (tenth epsilon))) (tenth epsilon)

theorem input_smallTime {input output : V} (G : GraphLimit hw0 hw1 input output)
    (preimages : Nat → (D).Cauchy)
    (hpin : ∀ n, Class (preimages n) = G.source n)
    (epsilon : Q') (he : (0 : Q') < epsilon) (depth steps : Nat)
    (hsmall : steps*2^(inputModulus hw0 hw1 G preimages hpin epsilon) ≤ 2^depth) :
    RCle (d (S depth steps input) input) (rat epsilon) := by
  let delta := tenth epsilon
  have hd : (0 : Q') < delta := tenth_positive he
  let n := G.modulus delta
  let a := completedTime hw0 hw1 1 (Class (preimages n))
  have hclose : RCle (d a input) (rat delta) := by
    dsimp only [a]
    rw [hpin n]
    exact (G.bound delta hd n (Nat.le_refl n)).1
  have hleft : RCle (d (S depth steps input) (S depth steps a)) (rat delta) :=
    RCle_trans (mesh_distance_bound hw0 hw1 depth steps input a)
      (by rw [completedDist_symm]; exact hclose)
  have hmiddle : RCle (d (S depth steps a) a) (rat delta) := by
    exact range_smallTime hw0 hw1 (preimages n) delta hd depth steps hsmall
  have hright := RCle_trans
    (completedDist_triangle hw0 hw1 (S depth steps a) a input)
    (RCadd_le_add (RCadd_le_add hmiddle hmiddle) (RCadd_le_add hclose hclose))
  have h := RCle_trans
    (completedDist_triangle hw0 hw1 (S depth steps input) (S depth steps a) input)
    (RCadd_le_add (RCadd_le_add hleft hleft) (RCadd_le_add hright hright))
  rwa [ten_tenths] at h

/-- The computed small-dyadic continuity data for a graph input. -/
def inputContinuityCertificate {input output : V}
    (G : GraphLimit hw0 hw1 input output)
    (preimages : Nat → (D).Cauchy)
    (hpin : ∀ n, Class (preimages n) = G.source n)
    (epsilon : Q') (he : (0 : Q') < epsilon) :
    {k : Nat // ∀ depth steps, steps*2^k ≤ 2^depth →
      RCle (d (S depth steps input) input) (rat epsilon)} :=
  ⟨inputModulus hw0 hw1 G preimages hpin epsilon,
    input_smallTime hw0 hw1 G preimages hpin epsilon he⟩

#print axioms outputModulus
#print axioms output_smallTime
#print axioms outputContinuityCertificate
#print axioms inputModulus
#print axioms input_smallTime
#print axioms inputContinuityCertificate

end YMGap.Continuum.BF4WilsonAllNomeDerivativeGraphContinuity
