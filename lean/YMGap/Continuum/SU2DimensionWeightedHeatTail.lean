/-
# Dimension-weighted SU(2) heat-channel tail

The nonlinear fivefold character product is not controlled by the unweighted
coefficient mass: Clebsch--Gordan fusion sees the representation dimension.
This file supplies the missing stronger tail layer.  For

  b_j(q) = (j+1)(2j+1) q^{j(j+1)}

the extra factor `(j+1)` costs at most another factor two in one ratio step.
Consequently, past `N`,

  b_{j+1} <= (4 q^{2(N+1)}) b_j.

An explicit constructive cutoff obtained from `powBaseCutoff q (1/8)` makes
this ratio at most `1/2`.  The existing finite geometric-series engine then
gives a spacing-dependent but tail-length-uniform estimate

  sum_{l<M} b_{N+l} <= 2 b_N.

No infinite sum, choice principle, or classical convergence theorem is hidden
in the statement: every cutoff and every partial-sum bound is explicit
`Nat`/`Q'` data.

Honest scope: this is the dimension-weighted linear heat tail needed for the
nonlinear fusion estimate.  The fivefold Cauchy estimate itself is downstream.

# Axiom gate

Constructive `Q'` arithmetic only.  No `Classical.*`, `native_decide`, `sorry`,
custom axiom, or noncomputable witness.
-/

import YMGap.Continuum.FiveHolonomyPerronCutoff

namespace YMGap.Continuum.SU2DimensionWeightedHeatTail

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.TruncationTailChannelBound
open YMGap.Continuum.FiveHolonomyPerronCutoff

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Dimension-weighted coefficients and their ratio -/

/-- The dimension of the SU(2) character indexed by the doubled-spin label
`j`, in the convention used by the repository's Chebyshev-U packets. -/
def representationDimension (j : Nat) : Q' := Q'.ofNat (j + 1)

/-- Heat-channel coefficient with one additional representation-dimension
weight. -/
def weightedChanCoeff (q : Q') (j : Nat) : Q' :=
  representationDimension j * chanCoeff q j

/-- The uniform geometric ratio available past the label `N`. -/
def weightedDiscardedRatio (q : Q') (N : Nat) : Q' :=
  Q'.ofNat 4 * q ^ (2 * (N + 1))

theorem representationDimension_nonneg (j : Nat) :
    (0 : Q') ≤ representationDimension j :=
  SU3CharFactor.ofNat_nonneg _

theorem weightedChanCoeff_nonneg {q : Q'} (hq0 : (0 : Q') ≤ q) (j : Nat) :
    (0 : Q') ≤ weightedChanCoeff q j :=
  Q'.mul_nonneg _ _ (representationDimension_nonneg j)
    (chanCoeff_nonneg hq0 j)

theorem representationDimension_pos (j : Nat) :
    (0 : Q') < representationDimension j := by
  exact Q'.ofNat_succ_pos j

theorem weightedChanCoeff_pos
    {q : Q'} (hq0 : (0 : Q') < q) (j : Nat) :
    (0 : Q') < weightedChanCoeff q j := by
  unfold weightedChanCoeff chanCoeff
  have hdim : (0 : Q') < representationDimension j :=
    representationDimension_pos j
  have hmult :
      (0 : Q') < Q'.ofNat (2 * j + 1) :=
    Q'.ofNat_succ_pos (2 * j)
  have hpow : (0 : Q') < q ^ (j * (j + 1)) :=
    HKPos.pow_pos hq0 _
  exact Q'.mul_pos hdim (Q'.mul_pos hmult hpow)

theorem weightedDiscardedRatio_nonneg {q : Q'} (hq0 : (0 : Q') ≤ q)
    (N : Nat) :
    (0 : Q') ≤ weightedDiscardedRatio q N :=
  Q'.mul_nonneg _ _ (by decide) (Q'.pow_nonneg q hq0 _)

/-- The dimension grows by at most a factor two in one label step. -/
theorem representationDimension_succ_le_two (j : Nat) :
    representationDimension (j + 1)
      ≤ Q'.ofNat 2 * representationDimension j := by
  have hnat : j + 2 ≤ 2 * (j + 1) := by omega
  have hqnat :
      Q'.ofNat (j + 2) ≤ Q'.ofNat (2 * (j + 1)) :=
    CReal.ofNat_le_ofNat hnat
  exact Q'.le_trans' _ _ _ hqnat
    (Q'.le_of_eqv
      (SU3CharFactor.ofNat_mul_eqv 2 (j + 1)))

/-- **Dimension-weighted super-geometric ratio.**  The ordinary heat
coefficient costs a factor `2 q^(2(N+1))`; the extra representation dimension
costs one further factor two. -/
theorem weightedChanCoeff_ratio
    {q : Q'} (hq0 : (0 : Q') ≤ q) (hq1 : q ≤ 1)
    (N j : Nat) (hNj : N ≤ j) (hj1 : 1 ≤ j) :
    weightedChanCoeff q (j + 1)
      ≤ weightedDiscardedRatio q N * weightedChanCoeff q j := by
  have hdim :
      representationDimension (j + 1)
        ≤ Q'.ofNat 2 * representationDimension j :=
    representationDimension_succ_le_two j
  have hchan :
      chanCoeff q (j + 1)
        ≤ (Q'.ofNat 2 * q ^ (2 * (N + 1))) * chanCoeff q j :=
    chanCoeff_ratio hq0 hq1 N j hNj hj1
  have hchanNextNonneg : (0 : Q') ≤ chanCoeff q (j + 1) :=
    chanCoeff_nonneg hq0 (j + 1)
  have htwoDimNonneg :
      (0 : Q') ≤ Q'.ofNat 2 * representationDimension j :=
    Q'.mul_nonneg _ _ (by decide) (representationDimension_nonneg j)
  have hstep1 :
      representationDimension (j + 1) * chanCoeff q (j + 1)
        ≤ (Q'.ofNat 2 * representationDimension j) * chanCoeff q (j + 1) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hdim hchanNextNonneg
  have hstep2 :
      (Q'.ofNat 2 * representationDimension j) * chanCoeff q (j + 1)
        ≤ (Q'.ofNat 2 * representationDimension j)
            * ((Q'.ofNat 2 * q ^ (2 * (N + 1))) * chanCoeff q j) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hchan htwoDimNonneg
  refine Q'.le_trans' _ _ _ (Q'.le_trans' _ _ _ hstep1 hstep2)
    (Q'.le_of_eqv ?_)
  -- `(2*d) * ((2*r)*c) = (4*r) * (d*c)`.
  let d := representationDimension j
  let r := q ^ (2 * (N + 1))
  let c := chanCoeff q j
  change
    (Q'.ofNat 2 * d) * ((Q'.ofNat 2 * r) * c)
      ≈ (Q'.ofNat 4 * r) * (d * c)
  have hfour : (Q'.ofNat 2 * Q'.ofNat 2) ≈ Q'.ofNat 4 := by
    exact Q'.eqv_trans _ _ _
      (Q'.eqv_symm (SU3CharFactor.ofNat_mul_eqv 2 2))
      (Q'.eqv_refl _)
  have hleft :
      (Q'.ofNat 2 * d) * ((Q'.ofNat 2 * r) * c)
        ≈ (Q'.ofNat 2 * Q'.ofNat 2) * (r * (d * c)) := by
    -- Pure commutative-semiring regrouping.
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm
        (Q'.mul_assoc_eqv (Q'.ofNat 2 * d) (Q'.ofNat 2 * r) c)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right
        ((Q'.ofNat 2 * d) * (Q'.ofNat 2 * r))
        ((Q'.ofNat 2 * Q'.ofNat 2) * (d * r)) c ?_) ?_
    · exact
        SU2HeatChannelHilbertSchmidtCompletion.mul_four_regroup
          (Q'.ofNat 2) d (Q'.ofNat 2) r
    · refine Q'.eqv_trans _ _ _
        (Q'.mul_assoc_eqv (Q'.ofNat 2 * Q'.ofNat 2) (d * r) c) ?_
      refine Q'.mul_eqv_congr_left (Q'.ofNat 2 * Q'.ofNat 2)
        ((d * r) * c) (r * (d * c)) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_assoc_eqv d r c) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_comm_eqv d (r * c)) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_assoc_eqv r c d) ?_
      exact Q'.mul_eqv_congr_left r (c * d) (d * c)
        (Q'.mul_comm_eqv c d)
  refine Q'.eqv_trans _ _ _ hleft ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right
      (Q'.ofNat 2 * Q'.ofNat 2) (Q'.ofNat 4)
      (r * (d * c)) hfour) ?_
  exact Q'.eqv_symm
    (Q'.mul_assoc_eqv (Q'.ofNat 4) r (d * c))

/-! ## 2. Geometric domination and a uniform finite tail -/

theorem weightedChanCoeff_geoDom
    {q : Q'} (hq0 : (0 : Q') ≤ q) (hq1 : q ≤ 1)
    (N : Nat) (hN1 : 1 ≤ N) :
    ∀ l, weightedChanCoeff q (N + l)
      ≤ weightedChanCoeff q N * weightedDiscardedRatio q N ^ l
  | 0 =>
      Q'.le_of_eqv
        (Q'.eqv_symm (Q'.mul_one_eqv (weightedChanCoeff q N)))
  | l + 1 => by
      have ih := weightedChanCoeff_geoDom hq0 hq1 N hN1 l
      have hratio :
          weightedChanCoeff q ((N + l) + 1)
            ≤ weightedDiscardedRatio q N *
                weightedChanCoeff q (N + l) :=
        weightedChanCoeff_ratio hq0 hq1 N (N + l)
          (Nat.le_add_right N l)
          (Nat.le_trans hN1 (Nat.le_add_right N l))
      have hrnonneg :
          (0 : Q') ≤ weightedDiscardedRatio q N :=
        weightedDiscardedRatio_nonneg hq0 N
      have hchain :
          weightedChanCoeff q ((N + l) + 1)
            ≤ weightedDiscardedRatio q N *
                (weightedChanCoeff q N *
                  weightedDiscardedRatio q N ^ l) :=
        Q'.le_trans' _ _ _ hratio
          (Q'.mul_le_mul_of_nonneg_left _ _ _ ih hrnonneg)
      refine Q'.le_trans' _ _ _ hchain (Q'.le_of_eqv ?_)
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_symm
          (Q'.mul_assoc_eqv (weightedDiscardedRatio q N)
            (weightedChanCoeff q N)
            (weightedDiscardedRatio q N ^ l))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right
          (weightedDiscardedRatio q N * weightedChanCoeff q N)
          (weightedChanCoeff q N * weightedDiscardedRatio q N)
          (weightedDiscardedRatio q N ^ l)
          (Q'.mul_comm_eqv _ _)) ?_
      exact Q'.mul_assoc_eqv (weightedChanCoeff q N)
        (weightedDiscardedRatio q N)
        (weightedDiscardedRatio q N ^ l)

/-- A finite window of dimension-weighted labels starting at `N`. -/
def weightedDiscardedPartial (q : Q') (N M : Nat) : Q' :=
  finSum (fun l => weightedChanCoeff q (N + l)) M

/-- The dimension-weighted analogue of the ordinary coefficient ceiling. -/
def weightedOnePlaquetteCeiling (q : Q') (N : Nat) : Q' :=
  finSum (weightedChanCoeff q) N +
    weightedChanCoeff q N * Q'.ofNat 2

/-- **Uniform dimension-weighted tail.**  Once the weighted ratio is at most
`1/2`, every finite tail window is bounded by twice its first term. -/
theorem weightedDiscardedPartial_le_twoLead
    {q : Q'} (hq0 : (0 : Q') ≤ q) (hq1 : q ≤ 1)
    (N : Nat) (hN1 : 1 ≤ N)
    (hratioHalf :
      weightedDiscardedRatio q N ≤ Q'.mkPos 1 2 (by decide))
    (M : Nat) :
    weightedDiscardedPartial q N M
      ≤ weightedChanCoeff q N * Q'.ofNat 2 := by
  have hterm :
      ∀ l, weightedChanCoeff q (N + l)
        ≤ weightedChanCoeff q N * weightedDiscardedRatio q N ^ l :=
    weightedChanCoeff_geoDom hq0 hq1 N hN1
  have hsum :
      weightedDiscardedPartial q N M
        ≤ finSum
          (fun l =>
            weightedChanCoeff q N * weightedDiscardedRatio q N ^ l) M :=
    YMGap.Constructive.CharacterTail.finSum_le_termwise _ _ hterm M
  have hgeom :
      finSum (fun l => weightedDiscardedRatio q N ^ l) M
        ≤ Q'.ofNat 2 :=
    geometricPartial_le_two
      (weightedDiscardedRatio_nonneg hq0 N) hratioHalf M
  have hpull :
      finSum
          (fun l =>
            weightedChanCoeff q N * weightedDiscardedRatio q N ^ l) M
        ≤ weightedChanCoeff q N * Q'.ofNat 2 := by
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.eqv_symm
          (RationalTail.const_mul_finSum
            (fun l => weightedDiscardedRatio q N ^ l)
            (weightedChanCoeff q N) M)))
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hgeom
        (weightedChanCoeff_nonneg hq0 N))
  exact Q'.le_trans' _ _ _ hsum hpull

/-- Every partial weighted sum extending beyond `N` obeys the computable
ceiling. -/
theorem weightedExtendedPartial_le_ceiling
    {q : Q'} (hq0 : (0 : Q') ≤ q) (hq1 : q ≤ 1)
    (N : Nat) (hN1 : 1 ≤ N)
    (hratioHalf :
      weightedDiscardedRatio q N ≤ Q'.mkPos 1 2 (by decide))
    (M : Nat) :
    finSum (weightedChanCoeff q) (N + M)
      ≤ weightedOnePlaquetteCeiling q N := by
  have hsplit :=
    FiveHolonomyPerronCutoff.finSum_split
      (weightedChanCoeff q) N M
  have htail :=
    weightedDiscardedPartial_le_twoLead
      hq0 hq1 N hN1 hratioHalf M
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv hsplit)
    (Q'.add_le_add_left _ _ _ htail)

theorem weightedAllLabelPartial_le_ceiling
    {q : Q'} (hq0 : (0 : Q') ≤ q) (hq1 : q ≤ 1)
    (N : Nat) (hN1 : 1 ≤ N)
    (hratioHalf :
      weightedDiscardedRatio q N ≤ Q'.mkPos 1 2 (by decide)) :
    ∀ K, finSum (weightedChanCoeff q) K
      ≤ weightedOnePlaquetteCeiling q N := by
  intro K
  by_cases hKN : K ≤ N
  · have hprefix :
        finSum (weightedChanCoeff q) K
          ≤ finSum (weightedChanCoeff q) N :=
      RationalTail.finSum_monotone_of_nonneg
        (weightedChanCoeff q) (weightedChanCoeff_nonneg hq0) K N hKN
    have htailNonneg :
        (0 : Q') ≤ weightedChanCoeff q N * Q'.ofNat 2 :=
      Q'.mul_nonneg _ _ (weightedChanCoeff_nonneg hq0 N) (by decide)
    exact Q'.le_trans' _ _ _ hprefix
      (Q'.add_le_self_of_nonneg _ _ htailNonneg)
  · have hNK : N ≤ K := by omega
    obtain ⟨M, rfl⟩ := Nat.exists_eq_add_of_le hNK
    exact weightedExtendedPartial_le_ceiling
      hq0 hq1 N hN1 hratioHalf M

/-! ## 3. Explicit spacing-dependent cutoff -/

/-- The stronger moving cutoff uses target `1/8`, exactly compensating the
factor four in the weighted ratio. -/
def explicitWeightedLabelCutoff (q : Q') : Nat :=
  HKConvGen.powBaseCutoff q (Q'.mkPos 1 8 (by decide)) + 1

theorem explicitWeightedLabelCutoff_pos (q : Q') :
    1 ≤ explicitWeightedLabelCutoff q := by
  unfold explicitWeightedLabelCutoff
  omega

theorem explicitWeightedLabelCutoff_ratio_le_half
    {q : Q'} (hq0 : (0 : Q') < q) (hq1 : q < 1) :
    weightedDiscardedRatio q (explicitWeightedLabelCutoff q)
      ≤ Q'.mkPos 1 2 (by decide) := by
  let n₀ :=
    HKConvGen.powBaseCutoff q (Q'.mkPos 1 8 (by decide))
  have heighth :
      q ^ n₀ ≤ Q'.mkPos 1 8 (by decide) :=
    HKConvGen.pow_base_le_cutoff hq0 hq1 (by decide)
  have hexponent :
      n₀ ≤ 2 * (explicitWeightedLabelCutoff q + 1) := by
    unfold explicitWeightedLabelCutoff
    dsimp [n₀]
    omega
  have hpower :
      q ^ (2 * (explicitWeightedLabelCutoff q + 1))
        ≤ q ^ n₀ :=
    HKConvGen.pow_base_antitone
      (Q'.le_of_lt hq0) (Q'.le_of_lt hq1) hexponent
  have hscaled :
      Q'.ofNat 4 *
          q ^ (2 * (explicitWeightedLabelCutoff q + 1))
        ≤ Q'.ofNat 4 * Q'.mkPos 1 8 (by decide) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _
      (Q'.le_trans' _ _ _ hpower heighth) (by decide)
  exact Q'.le_trans' _ _ _ hscaled
    (Q'.le_of_eqv (by decide))

/-- Once the moving label cutoff has been reached, the weighted ratio remains
at most one half at every later label. -/
theorem weightedDiscardedRatio_le_half_of_cutoff
    {q : Q'} (hq0 : (0 : Q') < q) (hq1 : q < 1)
    {N : Nat}
    (hcut : explicitWeightedLabelCutoff q ≤ N) :
    weightedDiscardedRatio q N
      ≤ Q'.mkPos 1 2 (by decide) := by
  have hexponent :
      2 * (explicitWeightedLabelCutoff q + 1)
        ≤ 2 * (N + 1) := by
    omega
  have hpower :
      q ^ (2 * (N + 1))
        ≤ q ^ (2 * (explicitWeightedLabelCutoff q + 1)) :=
    HKConvGen.pow_base_antitone
      (Q'.le_of_lt hq0) (Q'.le_of_lt hq1) hexponent
  have hscaled :
      weightedDiscardedRatio q N
        ≤ weightedDiscardedRatio q
            (explicitWeightedLabelCutoff q) := by
    exact Q'.mul_le_mul_of_nonneg_left _ _ _ hpower (by decide)
  exact Q'.le_trans' _ _ _ hscaled
    (explicitWeightedLabelCutoff_ratio_le_half hq0 hq1)

/-- **Spacing-dependent, all-label, dimension-weighted bound.**  For every
genuine heat nome, the explicit cutoff gives one rational ceiling for every
finite label partial sum. -/
theorem weightedAllLabelPartial_le_explicitCeiling
    {q : Q'} (hq0 : (0 : Q') < q) (hq1 : q < 1) :
    ∀ K, finSum (weightedChanCoeff q) K
      ≤ weightedOnePlaquetteCeiling q
          (explicitWeightedLabelCutoff q) := by
  exact weightedAllLabelPartial_le_ceiling
    (Q'.le_of_lt hq0)
    (Q'.le_trans' _ _ _ (Q'.le_of_lt hq1) (Q'.le_refl' 1))
    (explicitWeightedLabelCutoff q)
    (explicitWeightedLabelCutoff_pos q)
    (explicitWeightedLabelCutoff_ratio_le_half hq0 hq1)

end YMGap.Continuum.SU2DimensionWeightedHeatTail

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.SU2DimensionWeightedHeatTail.weightedChanCoeff_ratio
#print axioms YMGap.Continuum.SU2DimensionWeightedHeatTail.weightedChanCoeff_pos
#print axioms YMGap.Continuum.SU2DimensionWeightedHeatTail.weightedDiscardedPartial_le_twoLead
#print axioms YMGap.Continuum.SU2DimensionWeightedHeatTail.weightedDiscardedRatio_le_half_of_cutoff
#print axioms YMGap.Continuum.SU2DimensionWeightedHeatTail.weightedAllLabelPartial_le_explicitCeiling
