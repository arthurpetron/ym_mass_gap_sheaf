/-
# Finite check: can the two-block margin meet the shifted H1 `side_j·θ_j ≤ c0`?

**Label: NO-GO / consistency check. NOT gap evidence.**

The two-block route (`TwoBlockSchurMarginGap.twoBlock_gap`) bounds the per-scale lattice gap
from below by `(1 - s_j)·a_j`. The shifted H1 (r44, via `path_shiftedEps_forces_rate`)
forces `side_j·(1 - r_j) ≤ c0` for `j ≥ 1`. Combining them:

* `twoBlock_fixedMargin_noGo` (PROVED): a scale-independent margin `s < 1` together with a
  scale-independent interface-gap floor `a > 0` contradicts the shifted H1, because
  `side_j·(1-s)·a = 2^j·(1-s)·a` passes `c0` (explicit Archimedean witness from r40
  `exists_side_mul_gt`). This reproduces the r40 no-go for this route.
* `twoBlock_margin_must_shrink` (PROVED): at every scale `j ≥ 1` the margin must satisfy
  `side_j·(1 - s_j)·a_j ≤ c0`, i.e. `1 - s_j ≲ c0/(side_j·a_j)`. The margin itself must carry
  the dimensional transmutation; the two-block assembly does not supply it.
* `fixedMargin_instance` (decide): `s = 1/2`, `a = 1/100`, `j = 10`: `1024·(1/2)·(1/100) > 1`.

Nothing here bounds any of the OPEN inputs. Abelian-valid.
-/

import YMGap.Continuum.BF4WilsonAllNomeShiftedH1UniformRateNoGo

namespace YMGap.RG.TwoBlockMarginShiftedH1Check

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4DyadicWilsonSquare (side)
open YMGap.Continuum.BF4WilsonAllNomeShiftedH1UniformRateNoGo (exists_side_mul_gt sub_pos_of_lt)

private theorem ofNat_nonneg_c (n : Nat) : (0 : Q') ≤ Q'.ofNat n := by
  rw [Q'.zero_le_iff_num_nonneg]; exact Int.natCast_nonneg _

/-- **Necessary margin bound (PROVED):** two-block gap `(1-s_j)a_j ≤ 1 - r_j` and the shifted-H1
consequence `side_j·(1 - r_j) ≤ c0` give `side_j·((1-s_j)·a_j) ≤ c0`. -/
theorem twoBlock_margin_must_shrink (c0 : Q') (s a r : Nat → Q')
    (hgap_OPEN : ∀ j, ((1 : Q') - s j) * a j ≤ (1 : Q') - r j)
    (hshift : ∀ j, 1 ≤ j → Q'.ofNat (side j) * ((1 : Q') - r j) ≤ c0)
    (j : Nat) (hj : 1 ≤ j) : Q'.ofNat (side j) * (((1 : Q') - s j) * a j) ≤ c0 :=
  Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ (hgap_OPEN j) (ofNat_nonneg_c _)) (hshift j hj)

/-- **NO-GO (PROVED):** fixed margin `s < 1` and fixed interface-gap floor `a > 0` are
incompatible with the shifted H1 along the two-block route. -/
theorem twoBlock_fixedMargin_noGo (c0 s a : Q') (aj r : Nat → Q') (hs : s < (1 : Q'))
    (ha : (0 : Q') < a) (haj : ∀ j, a ≤ aj j)
    (hgap_OPEN : ∀ j, ((1 : Q') - s) * aj j ≤ (1 : Q') - r j)
    (hshift : ∀ j, 1 ≤ j → Q'.ofNat (side j) * ((1 : Q') - r j) ≤ c0) : False := by
  have hs0 : (0 : Q') ≤ (1 : Q') - s := Q'.le_of_lt (sub_pos_of_lt hs)
  obtain ⟨j, hj, hgt⟩ := exists_side_mul_gt c0 (((1 : Q') - s) * a)
    (Q'.mul_pos (sub_pos_of_lt hs) ha)
  have h1 : ((1 : Q') - s) * a ≤ ((1 : Q') - s) * aj j :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ (haj j) hs0
  have h2 : (((1 : Q') - s) * a) * Q'.ofNat (side j) ≤ Q'.ofNat (side j) * (((1 : Q') - s) * aj j) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))
      (Q'.mul_le_mul_of_nonneg_left _ _ _ h1 (ofNat_nonneg_c _))
  have h3 := twoBlock_margin_must_shrink c0 (fun _ => s) aj r hgap_OPEN hshift j hj
  exact Int.lt_irrefl _ (Q'.lt_of_le_of_lt (Q'.le_trans' _ _ _ h2 h3) hgt)

/-- Concrete finite instance (decide): `s = 1/2`, `a = 1/100`, `c0 = 1`, `j = 10`. -/
theorem fixedMargin_instance :
    (1 : Q') < (((1 : Q') - Q'.mkPos 1 2 (by decide)) * Q'.mkPos 1 100 (by decide)) *
      Q'.ofNat (side 10) := by decide

end YMGap.RG.TwoBlockMarginShiftedH1Check
