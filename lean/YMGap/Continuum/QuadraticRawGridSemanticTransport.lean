/-
# Raw-grid semantics for quadratically homogeneous certificates

This module connects the dense quadratic evaluator used by the E8/E9
Bernstein consumers to `RingNormaliser.RawPoly`.  It is the small semantic
interface needed to compare a generated coefficient grid with a structured
production polynomial by canonical raw equality.
-/

import YMGap.Continuum.RawGridSemanticTransport
import YMGap.Continuum.TensorBernsteinQuadraticProjectiveReconstruction

namespace YMGap.Continuum.QuadraticRawGridSemanticTransport

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.RawGridSemanticTransport
open YMGap.Continuum.TensorBernsteinQuadraticProjectiveReconstruction

local infix:50 " ≈ " => Q'.eqv

/-- Environment order used by the canonical raw normalizer: mode first,
harmonic denominator second. -/
def quadraticRawRho (D n : Q') : Nat → Q'
  | 0 => n
  | 1 => D
  | _ => 0

/-- The residual-degree monomial belonging to row `u` and D-power `i`.
The zero-D branch is emitted in trailing-zero-trimmed form, matching the
canonical monomial invariant of `RingNormaliser`. -/
def quadraticRawMonomial (totalDegree u i : Nat) : List Nat :=
  let modeExponent := totalDegree - u - 2 * i
  if i = 0 then
    if modeExponent = 0 then [] else [modeExponent]
  else
    [modeExponent, i]

/-- Rectangular raw representation of a quadratically homogeneous grid. -/
def quadraticRawGrid
    (degreeU degreeR totalDegree : Nat)
    (raw : Nat → Nat → Int) : RingNormaliser.RawPoly :=
  rawGrid (quadraticRawMonomial totalDegree)
    (quadraticRawLift totalDegree raw) (degreeR + 1) (degreeU + 1)

theorem ringQpow_eqv_pow (value : Q') : ∀ exponent,
    RingNormaliser.qpow value exponent ≈ value ^ exponent
  | 0 => Q'.eqv_refl 1
  | exponent + 1 => by
      have ih := ringQpow_eqv_pow value exponent
      change RingNormaliser.qpow value exponent * value ≈
        value * value ^ exponent
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ value ih) ?_
      exact Q'.mul_comm_eqv (value ^ exponent) value

theorem evalMono_quadraticRawMonomial
    (D n : Q') (totalDegree u i : Nat) :
    RingNormaliser.evalMono (quadraticRawRho D n)
        (quadraticRawMonomial totalDegree u i) ≈
      D ^ i * n ^ (totalDegree - u - 2 * i) := by
  by_cases hi : i = 0
  · subst i
    by_cases hm : totalDegree - u = 0
    · simp only [quadraticRawMonomial, Nat.mul_zero, Nat.sub_zero,
        hm, ↓reduceIte, RingNormaliser.evalMono,
        RingNormaliser.evalMonoFrom, Q'.pow_zero]
      exact Q'.eqv_symm (Q'.one_mul_eqv (1 : Q'))
    · simp only [quadraticRawMonomial, Nat.mul_zero, Nat.sub_zero,
        hm, ↓reduceIte, RingNormaliser.evalMono,
        RingNormaliser.evalMonoFrom, Q'.pow_zero]
      have hn := ringQpow_eqv_pow n (totalDegree - u)
      exact Q'.eqv_trans _ (n ^ (totalDegree - u) * 1) _
        (Q'.mul_eqv_congr_right _ _ 1 hn)
        (Q'.eqv_trans _ (n ^ (totalDegree - u)) _
          (Q'.mul_one_eqv (n ^ (totalDegree - u)))
          (Q'.eqv_symm (Q'.one_mul_eqv (n ^ (totalDegree - u)))))
  · simp only [quadraticRawMonomial, hi, ↓reduceIte]
    let modeExponent := totalDegree - u - 2 * i
    change RingNormaliser.qpow n modeExponent *
        (RingNormaliser.qpow D i * 1) ≈ D ^ i * n ^ modeExponent
    have hn := ringQpow_eqv_pow n modeExponent
    have hD := ringQpow_eqv_pow D i
    have hinner : RingNormaliser.qpow D i * 1 ≈ D ^ i := by
      refine Q'.eqv_trans _ (D ^ i * 1) _ ?_ ?_
      · exact Q'.mul_eqv_congr_right _ _ 1 hD
      · exact Q'.mul_one_eqv (D ^ i)
    refine Q'.eqv_trans _
      (n ^ modeExponent * (RingNormaliser.qpow D i * 1)) _ ?_ ?_
    · exact Q'.mul_eqv_congr_right _ _
        (RingNormaliser.qpow D i * 1) hn
    · refine Q'.eqv_trans _ (n ^ modeExponent * D ^ i) _ ?_ ?_
      · exact Q'.mul_eqv_congr_left (n ^ modeExponent) _ _ hinner
      · exact Q'.mul_comm_eqv (n ^ modeExponent) (D ^ i)

theorem evalRaw_quadraticRawGrid
    (degreeU degreeR totalDegree : Nat)
    (raw : Nat → Nat → Int) (D n : Q') :
    RingNormaliser.evalRaw (quadraticRawRho D n)
        (quadraticRawGrid degreeU degreeR totalDegree raw) ≈
      quadraticPowerEval degreeU degreeR totalDegree raw D n := by
  have hgrid := evalRaw_rawGrid (quadraticRawRho D n)
    (quadraticRawMonomial totalDegree)
    (quadraticRawLift totalDegree raw) (degreeR + 1) (degreeU + 1)
  refine Q'.eqv_trans _
    (finSum (fun u =>
      finSum (fun i =>
        Q'.ofInt (quadraticRawLift totalDegree raw u i) *
          RingNormaliser.evalMono (quadraticRawRho D n)
            (quadraticRawMonomial totalDegree u i))
        (degreeR + 1)) (degreeU + 1)) _ hgrid ?_
  unfold quadraticPowerEval
  refine finSum_eqv_congr_lt _ _ (degreeU + 1) ?_
  intro u hu
  refine finSum_eqv_congr_lt _ _ (degreeR + 1) ?_
  intro i hi
  exact Q'.mul_eqv_congr_left
    (Q'.ofInt (quadraticRawLift totalDegree raw u i)) _ _
    (evalMono_quadraticRawMonomial D n totalDegree u i)

theorem quadraticPowerEval_eqv_evalRawGrid
    (degreeU degreeR totalDegree : Nat)
    (raw : Nat → Nat → Int) (D n : Q') :
    quadraticPowerEval degreeU degreeR totalDegree raw D n ≈
      RingNormaliser.evalRaw (quadraticRawRho D n)
        (quadraticRawGrid degreeU degreeR totalDegree raw) :=
  Q'.eqv_symm
    (evalRaw_quadraticRawGrid degreeU degreeR totalDegree raw D n)

#print axioms quadraticRawRho
#print axioms quadraticRawMonomial
#print axioms quadraticRawGrid
#print axioms ringQpow_eqv_pow
#print axioms evalMono_quadraticRawMonomial
#print axioms evalRaw_quadraticRawGrid
#print axioms quadraticPowerEval_eqv_evalRawGrid

end YMGap.Continuum.QuadraticRawGridSemanticTransport
