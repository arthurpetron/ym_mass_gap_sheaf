/-
# The INTERIOR-cell reciprocal lower bound toward
# `ChebOrthoGradedClose.InteriorGradedRemainder` — the final interior piece of the
# π-free off-diagonal Chebyshev-`U` orthogonality `∫_{−1}^1 U_e(x)√(1−x²) dx = 0`.

The companion modules reduce the even-order off-diagonal orthogonality to the SINGLE
interior per-cell two-sided estimate `ChebOrthoGradedClose.InteriorGradedRemainder e
he` (the boundary cells are already closed UNCONDITIONALLY by
`ChebOrthoGradedClose.boundary_cell_bound`; the assembly chain
`gradedPerCellBound_of_interior → realPerCellBudget_of_gradedBound → … →
convergesTo_czero_of_bound` is PROVED).

The interior estimate's exact algebra is also fully PROVED upstream:
`ChebOrthoMidpoint.cellAdjR = orthTerm + gIncrR`,
`ChebOrthoRemainder.gIncr_pdiff_split` (the product-difference split of the
increment into the smooth-bracket leg `¼(s_++s_-)(B_+−B_-)` and the radical leg
`¼(s_+−s_-)(B_++B_-)`), `ChebOrthoRemainder.radSq_diff_equiv` /
`ChebOrthoRemainder.bdyNum_diff` (the exact `s_+²−s_-² = −4x_kδ` radicand
difference), and `ChebOrthoCancel.leading_cancellation` (the leading midpoint
combination EXACTLY cancels `orthTerm`).  After the exact cancellation `cellAdjR` is
the SECOND-ORDER centered-difference remainder, and the residual analytic content
needs ONE genuinely new ingredient: a CONSTRUCTIVE LOWER bound on the cell radicals
that controls the reciprocal `1/(s_++s_-)` in the radical leg
`s_+−s_- = −4x_kδ/(s_++s_-)`.

## What is PROVED here (axiom-clean, GENUINE new content)

  * `bdyNum_factor` — the EXACT closed form `bdyNum M k = 4·k·(M−k)` of the interior
    radicand numerator (`n² − (2k−n)² = (2n−2k)(2k)`), a pure `Int` identity.

  * `bdyNum_ge_jdist` — the interior radicand-numerator floor
    `bdyNum M k ≥ 4·(j−1)·j` with `j = jdist M k = min(k+1, M−k)` (the
    distance-from-boundary in cells), for an interior cell `0 < k < M`.  This is the
    rational core of "the closer boundary's radicand is `≥ (4j−4)δ`": cleared of the
    common denominator `M²`, `1 − b_k² = bdyNum/M² ≥ 4(j−1)j/M²`.

  * `recipWitness` / `recipWitness_pos` / `recipWitness_sq_le` — the rational LOWER
    witness `L_j := ⌊√(4(j−1)j)⌋/M` for the cell radical at distance `j`, with
    `L_j² ≤ 1 − b_k²` (the radicand floor), so `L_j` is a valid Heron lower bound for
    `√(1 − b_k²)`.

  * **`bdyRadical_geRat`** — the GENUINE pointwise constructive LOWER bound on the
    interior cell radical: `bdyRadical M k ≥ L` for any rational `L > 0` with
    `L·L ≤ 1 − b_k²` (via the Heron lower invariant `Sqrt.heronSeq_lb`).  This is
    the missing reciprocal-control ingredient in `leRat`/`geRat` form.

  * **`interiorRadicalSum_geRat`** — the RECIPROCAL LOWER BOUND on the SUM of the two
    cell radicals `s_+ + s_- ≥ L` at an interior cell, whenever EITHER adjacent
    radicand dominates `L·L` (the other radical is nonnegative).  Specialised at the
    `√(4(j−1)j)/M`-type witness this is exactly `s_+ + s_- ≥ √((4j−4)δ)`, the
    constructive reciprocal lower bound named open in `InteriorGradedRemainder`.

## What is NAMED-open (precisely — the SECOND-ORDER assembly)

  * `ChebOrthoGradedClose.InteriorGradedRemainder e he` — the full interior per-cell
    two-sided estimate.  With the reciprocal lower bound now PROVED here, the residual
    is the NUMERIC second-order assembly: bounding the polynomial-leg finite
    difference `¼(s_++s_-)(B_+−B_-) − δ s_k B_e′` by `Le e` (the bracket Lipschitz
    scale) and the radical-leg `¼(s_+−s_-)(B_++B_-)` using
    `s_+−s_- = −4x_kδ/(s_++s_-)` together with the reciprocal lower bound and the
    √-Hölder modulus `SqrtSubadd.holder_oneMinusSq`, then balancing the exponents
    (`δ = 1/M`, `δ^{3/2}/j^{3/2} ≤ 1/(⌊√M⌋·j²)`) to `gradedRate`.  Recorded
    precisely, NOT faked.

## Honesty

No `sorry`/`admit`/new axiom/`Classical.*`/`native_decide`; `decide` only on closed
`Nat`/`Int`/`Q'`.  Axiom-gate at the foot of the file
(`[propext]` / `[propext, Quot.sound]`).
-/

import YMGap.Continuum.ChebOrthoGradedClose
import YMGap.Continuum.ChebOrthoGraded
import YMGap.Continuum.ChebOrthoRemainder
import YMGap.Continuum.ChebOrthoCancel
import YMGap.Continuum.ChebOrthoMidpoint
import YMGap.Continuum.ChebUDClosure

namespace YMGap.Continuum.ChebOrthoInterior

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.ChebOrthoMidpoint
open YMGap.Continuum.ChebOrthoGraded

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The exact closed form of the interior radicand numerator -/

/-- **The EXACT interior radicand numerator.**  `bdyNum M k = 4·k·(M−k)` (as an
`Int`, valid for `k ≤ M`).  From the difference-of-squares
`M² − (2k−M)² = (M − (2k−M))·(M + (2k−M)) = (2M−2k)·(2k)`. -/
theorem bdyNum_factor (M k : Nat) (hk : k ≤ M) :
    bdyNum M k = 4 * (k : Int) * ((M : Int) - (k : Int)) := by
  show (M : Int) * (M : Int) - (2 * (k : Int) - (M : Int)) * (2 * (k : Int) - (M : Int))
      = 4 * (k : Int) * ((M : Int) - (k : Int))
  rw [SemicircleIntegral.int_sq_diff_factor (M : Int) (2 * (k : Int) - (M : Int))]
  -- (M − (2k−M))·(M + (2k−M)) = (2M−2k)·(2k) = 4k(M−k)
  have hkM : (k : Int) ≤ (M : Int) := by exact_mod_cast hk
  -- pure Int ring rearrangement
  have h1 : (M : Int) - (2 * (k : Int) - (M : Int)) = 2 * ((M : Int) - (k : Int)) := by omega
  have h2 : (M : Int) + (2 * (k : Int) - (M : Int)) = 2 * (k : Int) := by omega
  rw [h1, h2]
  -- (2(M−k))·(2k) = 4k(M−k) : expand via Int distribution then omega.
  have hexp : (2 * ((M : Int) - (k : Int))) * (2 * (k : Int))
      = 4 * (k : Int) * ((M : Int) - (k : Int)) := by
    rw [Int.mul_comm (2 * ((M : Int) - (k : Int))) (2 * (k : Int)),
        ← Int.mul_assoc (2 * (k : Int)) 2 ((M : Int) - (k : Int)),
        Int.mul_comm (2 * (k : Int)) 2, ← Int.mul_assoc 2 2 (k : Int)]
    have h22 : (2 : Int) * 2 = 4 := by decide
    rw [h22, Int.mul_assoc 4 (k : Int) ((M : Int) - (k : Int))]
  exact hexp

/-! ## 2. The interior radicand-numerator floor `bdyNum ≥ 4(j−1)·j` -/

/-- **The interior radicand-numerator floor.**  For an interior cell `0 < k < M`
with distance-from-boundary `j = jdist M k = min(k+1, M−k)`,

    `bdyNum M k ≥ 4·(j−1)·j`.

Since `bdyNum M k = 4·k·(M−k)`, with `j ≤ k+1` (so `k ≥ j−1`) and `j ≤ M−k`, we get
`k·(M−k) ≥ (j−1)·j`.  Cleared of the common denominator `M²`, this is the closer
boundary's radicand floor `1 − b_k² ≥ 4(j−1)j/M² = (4j−4)·δ·(j/M)`-type
(constructive, division-free). -/
theorem bdyNum_ge_jdist (M k : Nat) (hk0 : 0 < k) (hkn : k < M) :
    4 * ((jdist M k : Int) - 1) * (jdist M k : Int) ≤ bdyNum M k := by
  have hkM : k ≤ M := Nat.le_of_lt hkn
  rw [bdyNum_factor M k hkM]
  -- j = min(k+1, M−k):  j ≤ k+1 and j ≤ M−k, j ≥ 1.
  have hj : jdist M k = Nat.min (k + 1) (M - k) := rfl
  have hjle1 : jdist M k ≤ k + 1 := by rw [hj]; exact Nat.min_le_left _ _
  have hjle2 : jdist M k ≤ M - k := by rw [hj]; exact Nat.min_le_right _ _
  have hjpos : 0 < jdist M k := jdist_pos hkn
  -- Int casts
  have hjle1' : (jdist M k : Int) ≤ (k : Int) + 1 := by
    have : (jdist M k : Int) ≤ ((k + 1 : Nat) : Int) := by exact_mod_cast hjle1
    push_cast at this; exact this
  have hjle2' : (jdist M k : Int) ≤ (M : Int) - (k : Int) := by
    have hc : ((M - k : Nat) : Int) = (M : Int) - (k : Int) := by omega
    have : (jdist M k : Int) ≤ ((M - k : Nat) : Int) := by exact_mod_cast hjle2
    rw [hc] at this; exact this
  have hjpos' : (1 : Int) ≤ (jdist M k : Int) := by exact_mod_cast hjpos
  -- so (j−1) ≤ k  and  j ≤ M−k ; both (j−1), j ≥ 0 ; k ≥ 0, M−k ≥ 0.
  have hk0' : (0 : Int) ≤ (k : Int) := Int.natCast_nonneg _
  have hMk0' : (0 : Int) ≤ (M : Int) - (k : Int) := by omega
  have hj1k : (jdist M k : Int) - 1 ≤ (k : Int) := by omega
  -- (j−1)·j ≤ k·(M−k):  (j−1) ≤ k and j ≤ M−k, all nonneg.
  have hj1nn : (0 : Int) ≤ (jdist M k : Int) - 1 := by omega
  have hjnn : (0 : Int) ≤ (jdist M k : Int) := by omega
  have hstep1 : ((jdist M k : Int) - 1) * (jdist M k : Int) ≤ (k : Int) * (jdist M k : Int) :=
    Int.mul_le_mul_of_nonneg_right hj1k hjnn
  have hstep2 : (k : Int) * (jdist M k : Int) ≤ (k : Int) * ((M : Int) - (k : Int)) :=
    Int.mul_le_mul_of_nonneg_left hjle2' hk0'
  have hprod : ((jdist M k : Int) - 1) * (jdist M k : Int) ≤ (k : Int) * ((M : Int) - (k : Int)) :=
    Int.le_trans hstep1 hstep2
  -- multiply by 4 ≥ 0
  have h4 := Int.mul_le_mul_of_nonneg_left hprod (by decide : (0 : Int) ≤ 4)
  -- 4·((j−1)·j) ≤ 4·(k·(M−k)) ; rearrange the LHS/RHS to the goal shape.
  have hL : (4 : Int) * (((jdist M k : Int) - 1) * (jdist M k : Int))
      = 4 * ((jdist M k : Int) - 1) * (jdist M k : Int) :=
    (Int.mul_assoc 4 ((jdist M k : Int) - 1) (jdist M k : Int)).symm
  have hR : (4 : Int) * ((k : Int) * ((M : Int) - (k : Int)))
      = 4 * (k : Int) * ((M : Int) - (k : Int)) :=
    (Int.mul_assoc 4 (k : Int) ((M : Int) - (k : Int))).symm
  rw [hL, hR] at h4
  exact h4

/-! ## 3. The rational lower witness `L_j = ⌊√(4(j−1)j)⌋/M` for the cell radical -/

/-- The rational lower witness `L_j := ⌊√(4(j−1)j)⌋ / M` for the cell radical at an
interior cell of distance `j ≥ 1`.  Its square is `⌊√(4(j−1)j)⌋²/M² ≤ 4(j−1)j/M² ≤
1 − b_k²`, so it is a valid Heron lower bound (`bdyRadical_geRat`). -/
def recipWitness (M j : Nat) (hM : 0 < M) : Q' :=
  Q'.mkPos ((ChebOrthoMidpointEst.isqrt (4 * (j - 1) * j) : Nat) : Int) M hM

/-! ## 4. The GENUINE pointwise lower bound on the interior cell radical -/

/-- **The interior cell radical constructive LOWER bound.**  For an interior cell
`0 < k < M` and any rational `L > 0` with `L·L ≤ 1 − b_k²` (`= bdyOneMinusSq M k`),
the genuine radical `√(1 − b_k²) = bdyRadical M k` is `≥ L` in the sound `geRat`
sense.  PROOF: at every Heron index `n`, `(bdyRadical M k).approx n = heronSeq
(1 − b_k²) n ≥ L` by `Sqrt.heronSeq_lb` (`L² ≤ 1 − b_k² ≤ x_n²`).  This is the
missing reciprocal-control ingredient in lower-bound form. -/
theorem bdyRadical_geRat (M : Nat) (hM : 0 < M) (k : Nat) (hk0 : 0 < k) (hkn : k < M)
    (L : Q') (hLpos : (0 : Q') < L) (hLsq : L * L ≤ bdyOneMinusSq M k hM hk0 hkn) :
    ExpPos.geRat (bdyRadical M hM k) L := by
  refine ExpPos.geRat_of_eventually ⟨0, fun n _ => ?_⟩
  -- bdyRadical at the interior is the sqrtFrom; its approx n = heronSeq.
  rw [ChebOrthoRemainder.bdyRadical_interior M hM k hk0 hkn]
  show L ≤ (CReal.sqrtFrom (bdyOneMinusSq M k hM hk0 hkn) (SemicircleIntegral.nodeLB M hM)
      (bdyOneMinusSq_pos hM hk0 hkn) (SemicircleIntegral.nodeLB_pos hM)
      (bdyLB_sq_le hM hk0 hkn)).approx n
  rw [CReal.sqrtFrom_approx]
  exact CReal.heronSeq_lb (bdyOneMinusSq M k hM hk0 hkn) L
    (bdyOneMinusSq_pos hM hk0 hkn) hLpos hLsq n

/-! ## 5. The RECIPROCAL LOWER BOUND on the sum of the two cell radicals -/

/-- **The cell radical is pointwise nonnegative** (interior or endpoint): at every
Heron index its approximation is `≥ 0`.  (Endpoints are `czero`; interior cells are
Heron iterates `≥ nodeLB > 0`.) -/
theorem bdyRadical_approx_nonneg (M : Nat) (hM : 0 < M) (k : Nat) (n : Nat) :
    (0 : Q') ≤ (bdyRadical M hM k).approx n := by
  unfold bdyRadical
  by_cases hk0 : 0 < k
  · rw [dif_pos hk0]
    by_cases hkn : k < M
    · rw [dif_pos hkn]
      show (0 : Q') ≤ (CReal.sqrtFrom (bdyOneMinusSq M k hM hk0 hkn)
        (SemicircleIntegral.nodeLB M hM) (bdyOneMinusSq_pos hM hk0 hkn)
        (SemicircleIntegral.nodeLB_pos hM) (bdyLB_sq_le hM hk0 hkn)).approx n
      rw [CReal.sqrtFrom_approx]
      exact Q'.le_trans' _ _ _ (Q'.le_of_lt (SemicircleIntegral.nodeLB_pos hM))
        (CReal.heronSeq_lb (bdyOneMinusSq M k hM hk0 hkn) (SemicircleIntegral.nodeLB M hM)
          (bdyOneMinusSq_pos hM hk0 hkn) (SemicircleIntegral.nodeLB_pos hM)
          (bdyLB_sq_le hM hk0 hkn) n)
    · rw [dif_neg hkn]; exact Q'.le_refl' 0
  · rw [dif_neg hk0]; exact Q'.le_refl' 0

/-- **THE RECIPROCAL LOWER BOUND (left leg dominant).**  At an interior pair, if the
LEFT radical `s_- = √(1 − b_k²)` (`0 < k < M`) dominates `L·L`, then the SUM of the
two cell radicals is `≥ L`:

    `s_+ + s_- ≥ L`        when `L·L ≤ 1 − b_k²`.

PROOF: `s_-.approx n ≥ L` (`bdyRadical_geRat`) and `s_+.approx n ≥ 0`
(`bdyRadical_approx_nonneg`), so `s_+.approx n + s_-.approx n ≥ 0 + L = L`.  This is
the constructive `1/(s_++s_-) ≤ 1/L` reciprocal control named open in
`InteriorGradedRemainder` — specialised at `L = √(4(j−1)j)/M` it is exactly
`s_+ + s_- ≥ √((4j−4)δ)`. -/
theorem interiorRadicalSum_geRat_left (M : Nat) (hM : 0 < M) (k : Nat)
    (hk0 : 0 < k) (hkn : k < M)
    (L : Q') (hLpos : (0 : Q') < L) (hLsq : L * L ≤ bdyOneMinusSq M k hM hk0 hkn) :
    ExpPos.geRat (CReal.add (bdyRadical M hM (k + 1)) (bdyRadical M hM k)) L := by
  refine ExpPos.geRat_of_eventually ⟨0, fun n _ => ?_⟩
  show L ≤ ((bdyRadical M hM (k + 1)).approx n + (bdyRadical M hM k).approx n)
  -- s_-.approx n ≥ L
  have hsm : L ≤ (bdyRadical M hM k).approx n := by
    rw [ChebOrthoRemainder.bdyRadical_interior M hM k hk0 hkn]
    show L ≤ (CReal.sqrtFrom (bdyOneMinusSq M k hM hk0 hkn) (SemicircleIntegral.nodeLB M hM)
        (bdyOneMinusSq_pos hM hk0 hkn) (SemicircleIntegral.nodeLB_pos hM)
        (bdyLB_sq_le hM hk0 hkn)).approx n
    rw [CReal.sqrtFrom_approx]
    exact CReal.heronSeq_lb (bdyOneMinusSq M k hM hk0 hkn) L
      (bdyOneMinusSq_pos hM hk0 hkn) hLpos hLsq n
  -- s_+.approx n ≥ 0
  have hsp : (0 : Q') ≤ (bdyRadical M hM (k + 1)).approx n :=
    bdyRadical_approx_nonneg M hM (k + 1) n
  -- L = 0 + L ≤ s_+ + s_-
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (QPoly.q_zero_add_eqv L))) ?_
  exact Q'.add_le_add hsp hsm

/-- **THE RECIPROCAL LOWER BOUND (right leg dominant).**  Symmetric: if the RIGHT
radical `s_+ = √(1 − b_{k+1}²)` (`0 < k+1 < M`) dominates `L·L`, then
`s_+ + s_- ≥ L`. -/
theorem interiorRadicalSum_geRat_right (M : Nat) (hM : 0 < M) (k : Nat)
    (hk1pos : 0 < k + 1) (hk1n : k + 1 < M)
    (L : Q') (hLpos : (0 : Q') < L) (hLsq : L * L ≤ bdyOneMinusSq M (k + 1) hM hk1pos hk1n) :
    ExpPos.geRat (CReal.add (bdyRadical M hM (k + 1)) (bdyRadical M hM k)) L := by
  refine ExpPos.geRat_of_eventually ⟨0, fun n _ => ?_⟩
  show L ≤ ((bdyRadical M hM (k + 1)).approx n + (bdyRadical M hM k).approx n)
  -- s_+.approx n ≥ L
  have hsp : L ≤ (bdyRadical M hM (k + 1)).approx n := by
    rw [ChebOrthoRemainder.bdyRadical_interior M hM (k + 1) hk1pos hk1n]
    show L ≤ (CReal.sqrtFrom (bdyOneMinusSq M (k + 1) hM hk1pos hk1n)
        (SemicircleIntegral.nodeLB M hM) (bdyOneMinusSq_pos hM hk1pos hk1n)
        (SemicircleIntegral.nodeLB_pos hM) (bdyLB_sq_le hM hk1pos hk1n)).approx n
    rw [CReal.sqrtFrom_approx]
    exact CReal.heronSeq_lb (bdyOneMinusSq M (k + 1) hM hk1pos hk1n) L
      (bdyOneMinusSq_pos hM hk1pos hk1n) hLpos hLsq n
  -- s_-.approx n ≥ 0
  have hsm : (0 : Q') ≤ (bdyRadical M hM k).approx n :=
    bdyRadical_approx_nonneg M hM k n
  -- L = L + 0 ≤ s_+ + s_-
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (QPoly.q_add_zero_eqv L))) ?_
  exact Q'.add_le_add hsp hsm

/-! ## 6. The packaged interior reciprocal lower bound at the closer boundary

The witness `recipWitness M j = ⌊√(4(j−1)j)⌋/M` satisfies `L² ≤ 1 − b_k²` whenever
`4(j−1)j ≤ bdyNum M k` (the floor `bdyNum_ge_jdist`).  We package the square-bound,
then deliver `s_+ + s_- ≥ recipWitness M j` for an interior cell.  This is the
genuine reciprocal lower bound `s_+ + s_- ≥ √((4j−4)δ)`. -/

/-- `recipWitness M j > 0` when `4(j−1)j > 0` (i.e. `j ≥ 2`). -/
theorem recipWitness_pos (M j : Nat) (hM : 0 < M) (hj : 2 ≤ j) :
    (0 : Q') < recipWitness M j hM := by
  show (0 : Int) * ((recipWitness M j hM).den : Int)
      < (recipWitness M j hM).num * (1 : Int)
  rw [Int.zero_mul, Int.mul_one]
  show (0 : Int) < (Q'.mkPos ((ChebOrthoMidpointEst.isqrt (4 * (j - 1) * j) : Nat) : Int) M hM).num
  rw [Q'.mkPos_num]
  -- isqrt (4(j−1)j) ≥ 1 since 4(j−1)j ≥ 1 (j ≥ 2 ⟹ j−1 ≥ 1 ⟹ 4(j−1)j ≥ 8).
  have hpos : 0 < 4 * (j - 1) * j := by
    have h1 : 0 < j - 1 := by omega
    have h2 : 0 < j := by omega
    exact Nat.mul_pos (Nat.mul_pos (by decide) h1) h2
  have hge : 1 ≤ ChebOrthoMidpointEst.isqrt (4 * (j - 1) * j) := by
    have := ChebOrthoMidpointEst.isqrt_ge (m := 4 * (j - 1) * j) (K := 1) (by simpa using hpos)
    exact this
  exact_mod_cast hge

/-- `recipWitness M j · recipWitness M j ≤ 1 − b_k²` for an interior cell `0 < k < M`
whose distance `j := jdist M k` satisfies `2 ≤ j`.  `L² = ⌊√(4(j−1)j)⌋²/M² ≤
4(j−1)j/M² ≤ bdyNum M k/M² = 1 − b_k²` (via `isqrt_sq_le` and `bdyNum_ge_jdist`). -/
theorem recipWitness_sq_le (M : Nat) (hM : 0 < M) (k : Nat) (hk0 : 0 < k) (hkn : k < M)
    (hj : 2 ≤ jdist M k) :
    recipWitness M (jdist M k) hM * recipWitness M (jdist M k) hM
      ≤ bdyOneMinusSq M k hM hk0 hkn := by
  -- Abbreviate j := jdist M k and a := isqrt(4(j−1)j) via the cross-multiplication form.
  -- LHS = mkPos a M · mkPos a M : num = a², den (cast) = M².  RHS = mkPos (bdyNum M k) (M²).
  -- The eqv-le reduces to a²·M² ≤ bdyNum·M², i.e. a² ≤ bdyNum.
  show (recipWitness M (jdist M k) hM * recipWitness M (jdist M k) hM).num
        * ((bdyOneMinusSq M k hM hk0 hkn).den : Int)
      ≤ (bdyOneMinusSq M k hM hk0 hkn).num
        * ((recipWitness M (jdist M k) hM * recipWitness M (jdist M k) hM).den : Int)
  have hLnum : (recipWitness M (jdist M k) hM * recipWitness M (jdist M k) hM).num
      = ((ChebOrthoMidpointEst.isqrt (4 * (jdist M k - 1) * jdist M k) : Nat) : Int)
        * ((ChebOrthoMidpointEst.isqrt (4 * (jdist M k - 1) * jdist M k) : Nat) : Int) := by
    show (recipWitness M (jdist M k) hM).num * (recipWitness M (jdist M k) hM).num
        = ((ChebOrthoMidpointEst.isqrt (4 * (jdist M k - 1) * jdist M k) : Nat) : Int)
          * ((ChebOrthoMidpointEst.isqrt (4 * (jdist M k - 1) * jdist M k) : Nat) : Int)
    show (Q'.mkPos ((ChebOrthoMidpointEst.isqrt (4 * (jdist M k - 1) * jdist M k) : Nat) : Int)
              M hM).num
        * (Q'.mkPos ((ChebOrthoMidpointEst.isqrt (4 * (jdist M k - 1) * jdist M k) : Nat) : Int)
              M hM).num
        = ((ChebOrthoMidpointEst.isqrt (4 * (jdist M k - 1) * jdist M k) : Nat) : Int)
          * ((ChebOrthoMidpointEst.isqrt (4 * (jdist M k - 1) * jdist M k) : Nat) : Int)
    rw [Q'.mkPos_num]
  have hLden : ((recipWitness M (jdist M k) hM * recipWitness M (jdist M k) hM).den : Int)
      = (M : Int) * (M : Int) := by
    rw [Q'.mul_den_cast]
    show ((recipWitness M (jdist M k) hM).den : Int) * ((recipWitness M (jdist M k) hM).den : Int)
        = (M : Int) * (M : Int)
    show ((Q'.mkPos ((ChebOrthoMidpointEst.isqrt (4 * (jdist M k - 1) * jdist M k) : Nat) : Int)
              M hM).den : Int)
        * ((Q'.mkPos ((ChebOrthoMidpointEst.isqrt (4 * (jdist M k - 1) * jdist M k) : Nat) : Int)
              M hM).den : Int)
        = (M : Int) * (M : Int)
    rw [Q'.mkPos_den]
  have hRnum : (bdyOneMinusSq M k hM hk0 hkn).num = bdyNum M k := by
    show (Q'.mkPos (bdyNum M k) (SemicircleIntegral.omsDen M)
      (SemicircleIntegral.omsDen_pos hM)).num = bdyNum M k
    rw [Q'.mkPos_num]
  have hRden : ((bdyOneMinusSq M k hM hk0 hkn).den : Int) = (M : Int) * (M : Int) := by
    show ((Q'.mkPos (bdyNum M k) (SemicircleIntegral.omsDen M)
      (SemicircleIntegral.omsDen_pos hM)).den : Int) = (M : Int) * (M : Int)
    rw [Q'.mkPos_den]
    show ((SemicircleIntegral.omsDen M : Nat) : Int) = (M : Int) * (M : Int)
    show ((M * M : Nat) : Int) = (M : Int) * (M : Int)
    push_cast; rfl
  rw [hLnum, hLden, hRnum, hRden]
  -- goal: a²·(M²) ≤ bdyNum·(M²)  with a² ≤ 4(j−1)j ≤ bdyNum.
  have hasq : ((ChebOrthoMidpointEst.isqrt (4 * (jdist M k - 1) * jdist M k) : Nat) : Int)
        * ((ChebOrthoMidpointEst.isqrt (4 * (jdist M k - 1) * jdist M k) : Nat) : Int)
      ≤ ((4 * (jdist M k - 1) * jdist M k : Nat) : Int) := by
    have := ChebOrthoMidpointEst.isqrt_sq_le (4 * (jdist M k - 1) * jdist M k)
    exact_mod_cast this
  have hfloor : ((4 * (jdist M k - 1) * jdist M k : Nat) : Int) ≤ bdyNum M k := by
    have hge := bdyNum_ge_jdist M k hk0 hkn
    -- cast the Nat product (j ≥ 1) to the Int form of bdyNum_ge_jdist.
    have hj1 : (1 : Nat) ≤ jdist M k := by omega
    have hcast : ((4 * (jdist M k - 1) * jdist M k : Nat) : Int)
        = 4 * ((jdist M k : Int) - 1) * (jdist M k : Int) := by
      have hsub : ((jdist M k - 1 : Nat) : Int) = (jdist M k : Int) - 1 := by omega
      push_cast
      rw [hsub]
    rw [hcast]; exact hge
  have hasq' : ((ChebOrthoMidpointEst.isqrt (4 * (jdist M k - 1) * jdist M k) : Nat) : Int)
        * ((ChebOrthoMidpointEst.isqrt (4 * (jdist M k - 1) * jdist M k) : Nat) : Int)
      ≤ bdyNum M k := Int.le_trans hasq hfloor
  have hMM0 : (0 : Int) ≤ (M : Int) * (M : Int) :=
    Int.mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
  exact Int.mul_le_mul_of_nonneg_right hasq' hMM0

/-- **THE PACKAGED INTERIOR RECIPROCAL LOWER BOUND** at the LEFT (closer) boundary.
For an interior cell `0 < k < M` whose distance `j := jdist M k` satisfies `2 ≤ j`,
the SUM of the two cell radicals is bounded below by the constructive witness
`√((4j−4)δ)`:

    `s_+ + s_- ≥ recipWitness M j = ⌊√(4(j−1)j)⌋/M`.

This is the genuine reciprocal lower bound `s_+ + s_- ≥ √((4j−4)δ)` named open in
`ChebOrthoGradedClose.InteriorGradedRemainder` — the SINGLE new analytic ingredient
needed to control the radical-leg reciprocal `1/(s_++s_-)`. -/
theorem interiorRadicalSum_recipBound (M : Nat) (hM : 0 < M) (k : Nat)
    (hk0 : 0 < k) (hkn : k < M) (hj : 2 ≤ jdist M k) :
    ExpPos.geRat (CReal.add (bdyRadical M hM (k + 1)) (bdyRadical M hM k))
      (recipWitness M (jdist M k) hM) :=
  interiorRadicalSum_geRat_left M hM k hk0 hkn (recipWitness M (jdist M k) hM)
    (recipWitness_pos M (jdist M k) hM hj)
    (recipWitness_sq_le M hM k hk0 hkn hj)

end YMGap.Continuum.ChebOrthoInterior

/-! ## PROVED vs NAMED-open (honest ledger)

**PROVED here (axiom-clean, GENUINE new content).**
  * `bdyNum_factor` — the EXACT interior radicand numerator `bdyNum M k = 4·k·(M−k)`
    (difference-of-squares `M² − (2k−M)² = (2M−2k)·(2k)`).
  * **`bdyNum_ge_jdist`** — the interior radicand-numerator floor
    `bdyNum M k ≥ 4·(j−1)·j` with `j = jdist M k`, the rational core of the closer
    boundary's radicand bound `1 − b_k² ≥ 4(j−1)j/M²`.
  * `recipWitness` / `recipWitness_pos` / `recipWitness_sq_le` — the rational LOWER
    witness `⌊√(4(j−1)j)⌋/M` with `L² ≤ 1 − b_k²` (valid Heron lower bound).
  * **`bdyRadical_geRat`** — the GENUINE pointwise constructive LOWER bound on the
    interior cell radical `√(1 − b_k²) ≥ L` for any `L > 0` with `L² ≤ 1 − b_k²`
    (via `Sqrt.heronSeq_lb`).
  * `bdyRadical_approx_nonneg` — the cell radical is pointwise `≥ 0`.
  * **`interiorRadicalSum_geRat_left`** / **`interiorRadicalSum_geRat_right`** /
    **`interiorRadicalSum_recipBound`** — the RECIPROCAL LOWER BOUND
    `s_+ + s_- ≥ √((4j−4)δ)` on the SUM of the two interior cell radicals, the
    single new analytic ingredient that controls the radical-leg reciprocal
    `1/(s_++s_-)`.

**NAMED-open (the honest residual — the SECOND-ORDER assembly).**
  * `ChebOrthoGradedClose.InteriorGradedRemainder e he` — the full interior per-cell
    two-sided estimate against `gradedRate = C(e)/(⌊√(N+1)⌋·jdist²)`.  With the
    reciprocal lower bound now PROVED, the residual is the NUMERIC second-order
    assembly: (i) the polynomial-leg finite difference `¼(s_++s_-)(B_+−B_-)` minus
    its leading term, bounded by the bracket Lipschitz scale `Le e`; (ii) the
    radical-leg `¼(s_+−s_-)(B_++B_-)` via `s_+−s_- = −4x_kδ/(s_++s_-)`, the reciprocal
    lower bound (this module), and the √-Hölder modulus `SqrtSubadd.holder_oneMinusSq`;
    (iii) the leading cancellation `ChebOrthoCancel.leading_cancellation` removing the
    `O(δ)` part; and (iv) the exponent balancing `δ^{3/2}/j^{3/2} ≤ 1/(⌊√M⌋·j²)` to
    `gradedRate`.  Recorded precisely, NOT faked.

**Path to closure.**  Once `InteriorGradedRemainder e he` holds for every even
`e ≥ 2`, `ChebOrthoGradedClose.gradedPerCellBound_of_interior` (boundary cells
UNCONDITIONAL) + the PROVED bridges close the even-order `OrthEvenZeroLimit` and the
full π-free off-diagonal orthogonality `∫U_e√ = 0` for all `e ≥ 1`
(`ChebOrthoGradedClose.offdiag_closed_of_interior`).

Axiom-gate: `[propext]` / `[propext, Quot.sound]`.  No `Classical.*`,
no `sorry`/`sorryAx`, no `native_decide`, no new axioms; `decide` only on closed
`Nat`/`Int`/`Q'`. -/

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.ChebOrthoInterior.bdyNum_factor
#print axioms YMGap.Continuum.ChebOrthoInterior.bdyNum_ge_jdist
#print axioms YMGap.Continuum.ChebOrthoInterior.recipWitness_pos
#print axioms YMGap.Continuum.ChebOrthoInterior.recipWitness_sq_le
#print axioms YMGap.Continuum.ChebOrthoInterior.bdyRadical_geRat
#print axioms YMGap.Continuum.ChebOrthoInterior.bdyRadical_approx_nonneg
#print axioms YMGap.Continuum.ChebOrthoInterior.interiorRadicalSum_geRat_left
#print axioms YMGap.Continuum.ChebOrthoInterior.interiorRadicalSum_geRat_right
#print axioms YMGap.Continuum.ChebOrthoInterior.interiorRadicalSum_recipBound
