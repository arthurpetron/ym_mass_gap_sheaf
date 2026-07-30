/-
# The canonical stationary density of the physical BF4 Choi law

The normalized reflected BF4 kernel is a symmetric joint probability `J`
on the finite positive carrier, with marginal `pi`.  Its conditional Markov
kernel is `P(x,y) = J(x,y) / pi(x)`.  This file performs the second
normalization

    k(x,y) = P(x,y) / pi(y) = J(x,y) / (pi(x) pi(y))

without ever dividing at a zero row.  Thus `k` is the canonical kernel
density relative to `pi`.

Constructively, on the literal positive carrier:

* every weighted row of `k` is one;
* every weighted column of `k` is one;
* `pi(x) k(x,y) = P(y,x)` by detailed balance; and
* `J(x,y) = pi(x) pi(y) k(x,y)` exactly.

This is the correct one-slab stationary density.  It does not assert that a
slab of physical depth `m` is the `m`-fold convolution of a unit-depth
Yang--Mills density; that is the remaining geometric gluing theorem.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov

namespace YMGap.Continuum.BF4PhysicalConditionalDensity

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

local infix:50 " ≈ " => Q'.eqv

/-- Conditional kernel density relative to the physical stationary
marginal.  It is set to zero away from positive target rows. -/
def centralPhysicalConditionalDensity
    (w : Q') (hw : (0 : Q') ≤ w)
    (K half : Nat)
    (source target : EdgeLabelling) : Q' :=
  if htarget :
      (0 : Q') <
        centralPhysicalRowMarginal
          w hw K half target then
    Q'.divPos
      (centralPhysicalConditionalKernel
        w hw K half source target)
      (centralPhysicalRowMarginal
        w hw K half target)
      htarget
  else 0

theorem centralPhysicalConditionalDensity_eq_divPos
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat} {source target : EdgeLabelling}
    (htarget :
      (0 : Q') <
        centralPhysicalRowMarginal
          w hw K half target) :
    centralPhysicalConditionalDensity
        w hw K half source target =
      Q'.divPos
        (centralPhysicalConditionalKernel
          w hw K half source target)
        (centralPhysicalRowMarginal
          w hw K half target)
        htarget := by
  unfold centralPhysicalConditionalDensity
  rw [dif_pos htarget]

theorem centralPhysicalConditionalDensity_nonnegative
    {w : Q'} (hw : (0 : Q') ≤ w)
    (K half : Nat) (source target : EdgeLabelling) :
    (0 : Q') ≤
      centralPhysicalConditionalDensity
        w hw K half source target := by
  unfold centralPhysicalConditionalDensity
  split
  · unfold Q'.divPos
    exact Q'.mul_nonneg _ _
      (centralPhysicalConditionalKernel_nonnegative
        hw K half source target)
      (Q'.le_of_lt
        (Q'.recipPos_pos _ (by assumption)))
  · exact Q'.le_refl' 0

private theorem marginal_mul_divPos_eqv
    (marginal value : Q')
    (hmarginal : (0 : Q') < marginal) :
    marginal * Q'.divPos value marginal hmarginal ≈
      value := by
  unfold Q'.divPos
  refine Q'.eqv_trans _
    ((marginal * value) *
      Q'.recipPos marginal hmarginal) _ ?_ ?_
  · exact Q'.eqv_symm
      (Q'.mul_assoc_eqv marginal value
        (Q'.recipPos marginal hmarginal))
  refine Q'.eqv_trans _
    ((value * marginal) *
      Q'.recipPos marginal hmarginal) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _
      (Q'.mul_comm_eqv marginal value)
  refine Q'.eqv_trans _
    (value *
      (marginal *
        Q'.recipPos marginal hmarginal)) _ ?_ ?_
  · exact Q'.mul_assoc_eqv value marginal
      (Q'.recipPos marginal hmarginal)
  exact Q'.eqv_trans _ (value * 1) _
    (Q'.mul_eqv_congr_left value _ _
      (Q'.mul_recipPos_eqv marginal hmarginal))
    (Q'.mul_one_eqv value)

/-- Multiplication by the target marginal recovers the conditional
transition entry. -/
theorem targetMarginal_mul_density_eq_conditional
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat} {source target : EdgeLabelling}
    (htarget :
      target ∈
        centralPositiveHalfStates w hw K half) :
    centralPhysicalRowMarginal w hw K half target *
        centralPhysicalConditionalDensity
          w hw K half source target ≈
      centralPhysicalConditionalKernel
        w hw K half source target := by
  have hpositive :=
    (mem_centralPositiveHalfStates_iff).1 htarget
  rw [centralPhysicalConditionalDensity_eq_divPos
    hpositive.2]
  exact marginal_mul_divPos_eqv
    (centralPhysicalRowMarginal
      w hw K half target)
    (centralPhysicalConditionalKernel
      w hw K half source target)
    hpositive.2

/-- Every retained source row of the canonical density is normalized with
respect to the physical marginal. -/
theorem centralPhysicalConditionalDensity_row_normalized
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat} {source : EdgeLabelling}
    (hsource :
      source ∈
        centralPositiveHalfStates w hw K half) :
    listQSum
        (fun target =>
          centralPhysicalRowMarginal
              w hw K half target *
            centralPhysicalConditionalDensity
              w hw K half source target)
        (centralPositiveHalfStates w hw K half) ≈
      1 := by
  refine Q'.eqv_trans _
    (listQSum
      (centralPhysicalConditionalKernel
        w hw K half source)
      (centralPositiveHalfStates
        w hw K half)) _ ?_ ?_
  · apply listQSum_congr_on
    intro target htarget
    exact targetMarginal_mul_density_eq_conditional
      htarget
  · exact centralPhysicalConditionalKernel_row_normalized
      hsource

/-- Detailed balance turns source-marginal times density into the reversed
conditional transition. -/
theorem sourceMarginal_mul_density_eq_reverseConditional
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat} {source target : EdgeLabelling}
    (hsource :
      source ∈
        centralPositiveHalfStates w hw K half)
    (htarget :
      target ∈
        centralPositiveHalfStates w hw K half) :
    centralPhysicalRowMarginal w hw K half source *
        centralPhysicalConditionalDensity
          w hw K half source target ≈
      centralPhysicalConditionalKernel
        w hw K half target source := by
  have htargetPositive :=
    (mem_centralPositiveHalfStates_iff).1 htarget
  rw [centralPhysicalConditionalDensity_eq_divPos
    htargetPositive.2]
  unfold Q'.divPos
  refine Q'.eqv_trans _
    ((centralPhysicalRowMarginal w hw K half source *
        centralPhysicalConditionalKernel
          w hw K half source target) *
      Q'.recipPos
        (centralPhysicalRowMarginal w hw K half target)
        htargetPositive.2) _ ?_ ?_
  · exact Q'.eqv_symm
      (Q'.mul_assoc_eqv
        (centralPhysicalRowMarginal w hw K half source)
        (centralPhysicalConditionalKernel
          w hw K half source target)
        (Q'.recipPos
          (centralPhysicalRowMarginal
            w hw K half target)
          htargetPositive.2))
  refine Q'.eqv_trans _
    ((centralPhysicalRowMarginal w hw K half target *
        centralPhysicalConditionalKernel
          w hw K half target source) *
      Q'.recipPos
        (centralPhysicalRowMarginal w hw K half target)
        htargetPositive.2) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _
      (centralPhysicalConditionalKernel_detailed_balance
        hsource htarget)
  refine Q'.eqv_trans _
    (centralPhysicalConditionalKernel
        w hw K half target source *
      (centralPhysicalRowMarginal w hw K half target *
        Q'.recipPos
          (centralPhysicalRowMarginal
            w hw K half target)
          htargetPositive.2)) _ ?_ ?_
  · refine Q'.eqv_trans _
      ((centralPhysicalConditionalKernel
          w hw K half target source *
        centralPhysicalRowMarginal w hw K half target) *
        Q'.recipPos
          (centralPhysicalRowMarginal
            w hw K half target)
          htargetPositive.2) _ ?_ ?_
    · exact Q'.mul_eqv_congr_right _ _ _
        (Q'.mul_comm_eqv
          (centralPhysicalRowMarginal
            w hw K half target)
          (centralPhysicalConditionalKernel
            w hw K half target source))
    · exact Q'.mul_assoc_eqv
        (centralPhysicalConditionalKernel
          w hw K half target source)
        (centralPhysicalRowMarginal
          w hw K half target)
        (Q'.recipPos
          (centralPhysicalRowMarginal
            w hw K half target)
          htargetPositive.2)
  exact Q'.eqv_trans _
    (centralPhysicalConditionalKernel
      w hw K half target source * 1) _
    (Q'.mul_eqv_congr_left _ _ _
      (Q'.mul_recipPos_eqv
        (centralPhysicalRowMarginal
          w hw K half target)
        htargetPositive.2))
    (Q'.mul_one_eqv _)

/-- Every retained target column is normalized with respect to the same
physical marginal. -/
theorem centralPhysicalConditionalDensity_column_normalized
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat} {target : EdgeLabelling}
    (htarget :
      target ∈
        centralPositiveHalfStates w hw K half) :
    listQSum
        (fun source =>
          centralPhysicalRowMarginal
              w hw K half source *
            centralPhysicalConditionalDensity
              w hw K half source target)
        (centralPositiveHalfStates w hw K half) ≈
      1 := by
  refine Q'.eqv_trans _
    (listQSum
      (centralPhysicalConditionalKernel
        w hw K half target)
      (centralPositiveHalfStates
        w hw K half)) _ ?_ ?_
  · apply listQSum_congr_on
    intro source hsource
    exact sourceMarginal_mul_density_eq_reverseConditional
      hsource htarget
  · exact centralPhysicalConditionalKernel_row_normalized
      htarget

/-- Exact reconstruction of the normalized physical Choi entry from its
stationary density. -/
theorem normalizedJoint_eq_marginals_mul_density
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat} {source target : EdgeLabelling}
    (hsource :
      source ∈
        centralPositiveHalfStates w hw K half)
    (htarget :
      target ∈
        centralPositiveHalfStates w hw K half) :
    centralNormalizedPhysicalReflectedKernel
        w hw K half source target ≈
      (centralPhysicalRowMarginal w hw K half source *
        centralPhysicalRowMarginal w hw K half target) *
          centralPhysicalConditionalDensity
            w hw K half source target := by
  have hsourcePositive :=
    (mem_centralPositiveHalfStates_iff).1 hsource
  refine Q'.eqv_trans _
    (centralPhysicalRowMarginal w hw K half source *
      centralPhysicalConditionalKernel
        w hw K half source target) _ ?_ ?_
  · rw [centralPhysicalConditionalKernel_eq_divPos
      hsourcePositive.2]
    exact Q'.eqv_symm
      (marginal_mul_divPos_eqv
        (centralPhysicalRowMarginal
          w hw K half source)
        (centralNormalizedPhysicalReflectedKernel
          w hw K half source target)
        hsourcePositive.2)
  refine Q'.eqv_trans _
    (centralPhysicalRowMarginal w hw K half source *
      (centralPhysicalRowMarginal w hw K half target *
        centralPhysicalConditionalDensity
          w hw K half source target)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left _ _ _
      (Q'.eqv_symm
        (targetMarginal_mul_density_eq_conditional
          htarget))
  exact Q'.eqv_symm
    (Q'.mul_assoc_eqv
      (centralPhysicalRowMarginal
        w hw K half source)
      (centralPhysicalRowMarginal
        w hw K half target)
      (centralPhysicalConditionalDensity
        w hw K half source target))

end YMGap.Continuum.BF4PhysicalConditionalDensity

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.BF4PhysicalConditionalDensity.targetMarginal_mul_density_eq_conditional
#print axioms YMGap.Continuum.BF4PhysicalConditionalDensity.centralPhysicalConditionalDensity_row_normalized
#print axioms YMGap.Continuum.BF4PhysicalConditionalDensity.sourceMarginal_mul_density_eq_reverseConditional
#print axioms YMGap.Continuum.BF4PhysicalConditionalDensity.centralPhysicalConditionalDensity_column_normalized
#print axioms YMGap.Continuum.BF4PhysicalConditionalDensity.normalizedJoint_eq_marginals_mul_density
