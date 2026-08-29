/-
# Composition of finite weighted-fiber estimates

Suppose a first deterministic code has every weighted inverse fiber bounded
by `factor` times an intermediate weight.  Pushing those intermediate fibers
through a second deterministic code preserves the same factor: the complete
inverse fiber of the composite is bounded by `factor` times the second-stage
weighted inverse fiber.

This is finite Fubini with an inequality inserted at the intermediate fiber.
It is the exact algebra needed to compose target-component peeling with a
second local guard-peeling pass.

Constructive contract: exact finite fibers, duplicate-free intermediate
enumeration, and rational finite-sum monotonicity only; no `Classical`, choice,
`native_decide`, `sorry`, new axiom, noncomputable declaration, or unbounded
heartbeat option.
-/

import YMGap.Continuum.Z4HalfTimeReflectionLocalPairConditionalLaw

namespace YMGap.Continuum.FiniteWeightedFiberComposition

set_option autoImplicit false
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionLocalPairConditionalLaw

local infix:50 " ≈ " => Q'.eqv

private theorem listQSum_le_termwise_local
    {A : Type} (left right : A → Q') : ∀ items : List A,
    (∀ item, item ∈ items → left item ≤ right item) →
      listQSum left items ≤ listQSum right items
  | [], _ => Q'.le_refl' 0
  | head :: tail, hle =>
      Q'.add_le_add
        (hle head List.mem_cons_self)
        (listQSum_le_termwise_local left right tail
          (fun item hitem => hle item (List.mem_cons_of_mem head hitem)))

/-- **Weighted-fiber composition.**  A uniform first-stage amplification
factor survives deterministic postprocessing of the intermediate code. -/
theorem fiberWeight_comp_le_factor_mul
    {Source Middle Target : Type}
    [DecidableEq Middle] [DecidableEq Target]
    (sources : List Source) (sourceWeight : Source → Q')
    (first : Source → Middle)
    (middles : List Middle) (hmiddles : middles.Nodup)
    (hcoverage : ∀ source, source ∈ sources → first source ∈ middles)
    (middleWeight : Middle → Q')
    (factor : Q')
    (hfirst : ∀ middle, middle ∈ middles →
      fiberWeight sources sourceWeight first middle ≤
        factor * middleWeight middle)
    (second : Middle → Target) (target : Target) :
    fiberWeight sources sourceWeight (fun source => second (first source))
        target ≤
      factor * fiberWeight middles middleWeight second target := by
  have hcompose := fiberWeight_comp_eqv
    sources sourceWeight first middles hmiddles hcoverage second target
  have htermwise :
      fiberWeight middles
          (fiberWeight sources sourceWeight first) second target ≤
        fiberWeight middles
          (fun middle => factor * middleWeight middle) second target := by
    unfold fiberWeight
    apply listQSum_le_termwise_local
    intro middle hmiddle
    exact hfirst middle (List.mem_filter.mp hmiddle).1
  have hfactor :
      fiberWeight middles
          (fun middle => factor * middleWeight middle) second target ≈
        factor * fiberWeight middles middleWeight second target := by
    unfold fiberWeight
    exact listQSum_mul_left factor middleWeight
      (middles.filter fun middle => decide (target = second middle))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_symm hcompose))
    (Q'.le_trans' _ _ _ htermwise (Q'.le_of_eqv hfactor))

#print axioms fiberWeight_comp_le_factor_mul

end YMGap.Continuum.FiniteWeightedFiberComposition
