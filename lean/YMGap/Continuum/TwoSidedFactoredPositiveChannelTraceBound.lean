/-
Two-sided square-root-free positive-channel domination.

The cutoff-one tensor network naturally produces coefficients of the form

  <U v, V v>

with two (generally different) Gram isometries.  This module extends the
one-sided trace estimate without pretending that either isometry has a
constructively available inverse.  Young's inequality gives

  2 |<U v, V v>| <= <U v, U v> + <V v, V v>
                      = 2 <v, v>,

and cancellation of the positive rational factor `2` gives the sharp
one-channel bound.  The factored theorem then folds that estimate through
the existing nested local-channel sums, so no Cartesian product of global
channel choices is formed.

# Axiom gate

No `Classical`, choice, `sorry`/`admit`, `native_decide`, or custom axiom.
-/

import YMGap.Continuum.FactoredPositiveChannelTraceBound

namespace YMGap.Continuum.TwoSidedFactoredPositiveChannelTraceBound

open YMGap.Constructive
open YMGap.Continuum.OSReconstructionProgress
open YMGap.Continuum.PositiveChannelTraceBound
open YMGap.Continuum.FactoredPositiveChannelTraceBound

local infix:50 " ≈ " => Q'.eqv

variable {V A : Type}

/-! ## 1. One-channel two-sided domination -/

/-- The weighted contribution of one positive channel when the two tensor
legs are transported by independently specified Gram isometries. -/
def twoSidedChannelTraceTerm (F : PreInnerForm V)
    (leftIso rightIso : GramIsometry F) (c : PositiveChannel V) : Q' :=
  c.weight * F.B (leftIso.map c.vector) (rightIso.map c.vector)

/-- The elementary lower half of the absolute-value interval. -/
private theorem neg_abs_le_self (x : Q') : -(Q'.abs x) <= x := by
  have h := Q'.neg_le_neg (Q'.neg_le_abs x)
  exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.neg_neg_eqv x))

/-- A nonnegative channel weight preserves an absolute majorant. -/
private theorem abs_mul_le_mul_of_nonneg_left {w x m : Q'}
    (hw : (0 : Q') <= w) (hx : Q'.abs x <= m) :
    Q'.abs (w * x) <= w * m := by
  refine Q'.abs_le ?_ ?_
  · have hNegMass : -m <= -(Q'.abs x) := Q'.neg_le_neg hx
    have hLower : -m <= x :=
      Q'.le_trans' _ _ _ hNegMass (neg_abs_le_self x)
    have hWeighted : w * (-m) <= w * x :=
      Q'.mul_le_mul_of_nonneg_left (-m) x w hLower hw
    exact le_of_eqv_le (Q'.eqv_symm (Q'.mul_neg_eqv w m)) hWeighted
  · have hUpper : x <= m :=
      Q'.le_trans' _ _ _ (Q'.le_abs_self x) hx
    exact Q'.mul_le_mul_of_nonneg_left x m w hUpper hw

/-- **Two-sided one-channel Young bound.**  Both diagonal terms reduce to the
same original Gram norm, one through each isometry. -/
theorem abs_twoSidedChannelTraceTerm_le_mass (F : PreInnerForm V)
    (leftIso rightIso : GramIsometry F) (c : PositiveChannel V) :
    Q'.abs (twoSidedChannelTraceTerm F leftIso rightIso c) <=
      channelTraceMass F c := by
  have hYoung := F.two_mul_abs_inner_le
    (leftIso.map c.vector) (rightIso.map c.vector)
  have hDiagonal :
      (F.B (leftIso.map c.vector) (leftIso.map c.vector) +
          F.B (rightIso.map c.vector) (rightIso.map c.vector)).eqv
        (2 * F.B c.vector c.vector) :=
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right
        (F.B (leftIso.map c.vector) (leftIso.map c.vector))
        (F.B c.vector c.vector)
        (F.B (rightIso.map c.vector) (rightIso.map c.vector))
        (leftIso.gram_eqv c.vector c.vector))
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left
          (F.B c.vector c.vector)
          (F.B (rightIso.map c.vector) (rightIso.map c.vector))
          (F.B c.vector c.vector)
          (rightIso.gram_eqv c.vector c.vector))
        (q_two_mul (F.B c.vector c.vector)))
  have hTwice :
      2 * Q'.abs
          (F.B (leftIso.map c.vector) (rightIso.map c.vector)) <=
        2 * F.B c.vector c.vector :=
    le_of_le_eqv hYoung hDiagonal
  have hInner :
      Q'.abs (F.B (leftIso.map c.vector) (rightIso.map c.vector)) <=
        F.B c.vector c.vector :=
    q_cancel_left (c := (2 : Q')) (by decide) hTwice
  unfold twoSidedChannelTraceTerm channelTraceMass
  exact abs_mul_le_mul_of_nonneg_left c.weight_nonneg hInner

/-! ## 2. Nested factored domination -/

/-- The two-sided contraction summed through the local channel lists.  The
definition is structurally nested and never materializes global choices. -/
def twoSidedFactoredResolvedTrace (F : PreInnerForm V)
    (R : FactoredPositiveChannelResolution (A := A) F)
    (leftIso rightIso : GramIsometry F) : Q' :=
  nestedListQSum R.channelChoices (fun selected =>
    twoSidedChannelTraceTerm F leftIso rightIso
      (selectedPositiveChannel F R selected))

/-- **Factored two-sided square-root-free trace domination.** -/
theorem abs_twoSidedFactoredResolvedTrace_le_mass (F : PreInnerForm V)
    (R : FactoredPositiveChannelResolution (A := A) F)
    (leftIso rightIso : GramIsometry F) :
    Q'.abs (twoSidedFactoredResolvedTrace F R leftIso rightIso) <=
      factoredResolvedTraceMass F R := by
  unfold twoSidedFactoredResolvedTrace factoredResolvedTraceMass
  exact abs_nestedListQSum_le R.channelChoices _ _ (fun selected =>
    abs_twoSidedChannelTraceTerm_le_mass F leftIso rightIso
      (selectedPositiveChannel F R selected))

/-! ## 3. Reuse of the existing tensor-mass factorization -/

/-- If the global selected-channel norm factors into local norms, the same
two-sided contraction is bounded directly by the product of local weighted
masses.  The factorization proof is exactly the existing one: the two
isometries change the signed contraction, not its positive mass ledger. -/
theorem abs_twoSidedFactoredResolvedTrace_le_productLocalTraceMass
    (F : PreInnerForm V)
    (R : FactoredPositiveChannelResolution (A := A) F)
    (leftIso rightIso : GramIsometry F)
    (localNorm : A -> Q')
    (hTensorNorm : forall selected,
      F.B (R.vector selected) (R.vector selected) ≈
        listQProduct localNorm selected) :
    Q'.abs (twoSidedFactoredResolvedTrace F R leftIso rightIso) <=
      productLocalTraceMass F R localNorm := by
  exact le_of_le_eqv
    (abs_twoSidedFactoredResolvedTrace_le_mass F R leftIso rightIso)
    (factoredResolvedTraceMass_eqv_productLocalTraceMass
      F R localNorm hTensorNorm)

#print axioms abs_twoSidedChannelTraceTerm_le_mass
#print axioms abs_twoSidedFactoredResolvedTrace_le_mass
#print axioms abs_twoSidedFactoredResolvedTrace_le_productLocalTraceMass

end YMGap.Continuum.TwoSidedFactoredPositiveChannelTraceBound
