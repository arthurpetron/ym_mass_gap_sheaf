/-
# Associativity and depth decomposition for finite weighted density powers

This is finite algebra only.  It exposes the exact bridge between the direct
power factorization produced by a compatible time step and the endpoint/middle
power gluing shape consumed by the sector-local contraction compiler.

No Yang--Mills estimate, cofinal family, thermodynamic limit, or continuum
claim is constructed here.
-/

import YMGap.Continuum.BF4StationaryDensityBufferSplit

namespace YMGap.Continuum.BF4PhysicalVacuumSectorDensityPowerDecomposition

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.BF4StationaryDensityBufferSplit

local infix:50 " ≈ " => Q'.eqv

private theorem four_factor_reorder
    (a b c d : Q') :
    a * ((b * c) * d) ≈ b * ((a * c) * d) := by
  refine Q'.eqv_trans _ ((a * (b * c)) * d) _
    (Q'.eqv_symm (Q'.mul_assoc_eqv a (b * c) d)) ?_
  refine Q'.eqv_trans _ ((b * (a * c)) * d) _ ?_
    (Q'.mul_assoc_eqv b (a * c) d)
  apply Q'.mul_eqv_congr_right _ _ d
  refine Q'.eqv_trans _ ((a * b) * c) _
    (Q'.eqv_symm (Q'.mul_assoc_eqv a b c)) ?_
  exact Q'.eqv_trans _ ((b * a) * c) _
    (Q'.mul_eqv_congr_right _ _ c (Q'.mul_comm_eqv a b))
    (Q'.mul_assoc_eqv b a c)

private theorem finiteWeightedDensityCompose_right_congr
    {State : Type}
    (states : List State) (weight : State → Q')
    (left right right' : State → State → Q')
    (source target : State)
    (h : ∀ middle, right middle target ≈ right' middle target) :
    finiteWeightedDensityCompose states weight left right source target ≈
      finiteWeightedDensityCompose states weight left right' source target := by
  unfold finiteWeightedDensityCompose
  apply listQSum_congr_on
  intro middle hmiddle
  exact Q'.mul_eqv_congr_left
    (weight middle * left source middle) _ _ (h middle)

private theorem listQSum_mul_right {A : Type} (f : A → Q') (a : Q') :
    ∀ xs : List A,
      listQSum (fun x => f x * a) xs ≈ listQSum f xs * a
  | [] => Q'.eqv_symm (Q'.zero_mul_eqv a)
  | _ :: xs => by
      unfold listQSum
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr'
          (Q'.eqv_refl _) (listQSum_mul_right f a xs)) ?_
      exact Q'.eqv_symm
        (Q'.add_mul_eqv (f _) (listQSum f xs) a)

/-- Weighted kernel composition is associative up to the exact rational
equivalence carried by `Q'`. -/
theorem finiteWeightedDensityCompose_assoc
    {State : Type}
    (states : List State) (weight : State → Q')
    (left middle right : State → State → Q')
    (source target : State) :
    finiteWeightedDensityCompose states weight
        (finiteWeightedDensityCompose states weight left middle) right
        source target ≈
      finiteWeightedDensityCompose states weight left
        (finiteWeightedDensityCompose states weight middle right)
        source target := by
  unfold finiteWeightedDensityCompose
  let leftTerm := fun inner =>
    weight inner * left source inner
  let middleTerm := fun inner outer =>
    middle inner outer
  let rightTerm := fun outer =>
    right outer target
  have houter : ∀ outer, outer ∈ states →
      ((weight outer * listQSum
          (fun inner => leftTerm inner * middleTerm inner outer) states) *
          rightTerm outer) ≈
        listQSum
          (fun inner =>
            weight outer *
              ((leftTerm inner * middleTerm inner outer) *
                rightTerm outer)) states := by
    intro outer houter
    refine Q'.eqv_trans _
      (weight outer *
        (listQSum
          (fun inner => leftTerm inner * middleTerm inner outer) states *
          rightTerm outer)) _ ?_ ?_
    · exact Q'.mul_assoc_eqv _ _ _
    refine Q'.eqv_trans _
      (weight outer *
        listQSum
          (fun inner =>
            (leftTerm inner * middleTerm inner outer) * rightTerm outer)
          states) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left (weight outer) _ _
        (Q'.eqv_symm
          (listQSum_mul_right
            (fun inner => leftTerm inner * middleTerm inner outer)
            (rightTerm outer) states))
    exact Q'.eqv_symm
      (listQSum_mul_left (weight outer)
        (fun inner =>
          (leftTerm inner * middleTerm inner outer) * rightTerm outer)
        states)
  have houterSum :
      listQSum
          (fun outer =>
            (weight outer * listQSum
              (fun inner => leftTerm inner * middleTerm inner outer) states) *
              rightTerm outer) states ≈
        listQSum
          (fun outer =>
            listQSum
              (fun inner =>
                weight outer *
                  ((leftTerm inner * middleTerm inner outer) *
                    rightTerm outer)) states) states := by
    apply listQSum_congr_on
    exact houter
  refine Q'.eqv_trans _
    (listQSum
      (fun outer =>
        listQSum
          (fun inner =>
            weight outer *
              ((leftTerm inner * middleTerm inner outer) *
                rightTerm outer)) states) states) _ houterSum ?_
  refine Q'.eqv_trans _ _ _
    (listQSum_swap
      (fun inner outer =>
        weight outer *
          ((leftTerm inner * middleTerm inner outer) *
            rightTerm outer)) states states) ?_
  apply listQSum_congr_on
  intro inner hinner
  refine Q'.eqv_trans _ _ _
    ?_
    (listQSum_mul_left (leftTerm inner)
      (fun outer =>
        (weight outer * middleTerm inner outer) * rightTerm outer)
      states)
  apply listQSum_congr_on
  intro outer houter
  exact four_factor_reorder (weight outer) (leftTerm inner)
    (middleTerm inner outer) (rightTerm outer)

/-! The power recurrence can be reassociated without any analytic input. -/

theorem finiteWeightedDensityPower_succ_right
    {State : Type}
    (states : List State) (weight : State → Q')
    (kernel : State → State → Q')
    (steps : Nat) (source target : State) :
    finiteWeightedDensityPower states weight kernel (steps + 1) source target ≈
      finiteWeightedDensityCompose states weight
        (finiteWeightedDensityPower states weight kernel steps) kernel
        source target := by
  induction steps generalizing source target with
  | zero =>
      exact Q'.eqv_refl _
  | succ steps ih =>
      unfold finiteWeightedDensityPower
      refine Q'.eqv_trans _ _ _
        (finiteWeightedDensityCompose_right_congr states weight kernel
          (finiteWeightedDensityPower states weight kernel (steps + 1))
          (finiteWeightedDensityCompose states weight
            (finiteWeightedDensityPower states weight kernel steps) kernel)
          source target
          (fun middle => ih middle target))
        (Q'.eqv_symm
        (finiteWeightedDensityCompose_assoc states weight kernel
          (finiteWeightedDensityPower states weight kernel steps) kernel
          source target))

/-- A depth-`d` direct power is exactly the two-endpoint/middle-power
decomposition used by the local contraction compiler, for `d >= 3`. -/
theorem finiteWeightedDensityPower_depth_decomposition
    {State : Type}
    (states : List State) (weight : State → Q')
    (kernel : State → State → Q')
    (depth : Nat) (hdepth : 3 ≤ depth)
    (source target : State) :
    finiteWeightedDensityPower states weight kernel (depth - 1) source target ≈
      finiteWeightedDensityCompose states weight kernel
        (finiteWeightedDensityCompose states weight
          (finiteWeightedDensityPower states weight kernel (depth - 3))
          kernel)
        source target := by
  have hsteps : (depth - 3 + 1) + 1 = depth - 1 := by omega
  have hpower := finiteWeightedDensityPower_succ_right
    states weight kernel (depth - 3 + 1) source target
  rw [← hsteps]
  change finiteWeightedDensityPower states weight kernel
      ((depth - 3 + 1) + 1) source target ≈
    finiteWeightedDensityCompose states weight
      (finiteWeightedDensityCompose states weight kernel
        (finiteWeightedDensityPower states weight kernel (depth - 3)))
      kernel source target at hpower
  exact Q'.eqv_trans _ _ _ hpower
    (finiteWeightedDensityCompose_assoc states weight kernel
      (finiteWeightedDensityPower states weight kernel (depth - 3)) kernel
      source target)

end YMGap.Continuum.BF4PhysicalVacuumSectorDensityPowerDecomposition

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorDensityPowerDecomposition.finiteWeightedDensityCompose_assoc
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorDensityPowerDecomposition.finiteWeightedDensityPower_succ_right
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorDensityPowerDecomposition.finiteWeightedDensityPower_depth_decomposition
