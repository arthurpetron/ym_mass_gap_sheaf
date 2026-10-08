/-
# Torus RP, K → ∞ step 4: Cauchy–Schwarz closed under approximation, from per-value rates (Q'; NO limit object)

* `prod_pert`: `|b − b'| ≤ r`, `|c − c'| ≤ r`, `|b'|, |c'| ≤ C` ⟹ `|b·c − b'·c'| ≤ (C + r)·r + C·r`.
* `cs_limit`: rationals `a, b, c` approximated by `rpB_K F G`, `rpB_K F F`, `rpB_K G G` within `r K`, with
  `|rpB_K| ≤ C`, satisfy `a·a ≤ (b·c + s K) + s K`, where `s K = (C + r K)·r K + C·r K`.
  The rate `r` can be the `SU2TorusRPKCauchy.rpK_cauchy` rate.

This only says that any rationals the truncations approximate at the given rate satisfy the inequality up to
`2 s K`. No limit object is defined, and nothing is claimed about the untruncated measure itself.
-/

import YMGap.Continuum.SU2TorusRPKCauchy

namespace YMGap.Continuum.SU2TorusRPKClosed

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (PolyExpr poly_identity_of_normal_eq)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2TorusRPCSShape (rpB PtSup)

local instance : Add PolyExpr := ⟨PolyExpr.add⟩
local instance : Mul PolyExpr := ⟨PolyExpr.mul⟩
local instance : Neg PolyExpr := ⟨PolyExpr.neg⟩

theorem prod_pert {b b' c c' r C : Q'} (hb : Q'.abs (b + -b') ≤ r) (hc : Q'.abs (c + -c') ≤ r)
    (hb' : Q'.abs b' ≤ C) (hc' : Q'.abs c' ≤ C) :
    Q'.abs (b * c + -(b' * c')) ≤ (C + r) * r + C * r := by
  let V := PolyExpr.var
  have e : (b * c + -(b' * c')).eqv (b * (c + -c') + c' * (b + -b')) :=
    poly_identity_of_normal_eq (V 0 * V 1 + -(V 2 * V 3)) (V 0 * (V 1 + -V 3) + V 3 * (V 0 + -V 2)) (by decide)
      (fun | 0 => b | 1 => c | 2 => b' | _ => c')
  have hbabs : Q'.abs b ≤ C + r :=
    Q'.le_trans' _ _ _ (Q'.abs_le_abs_add_abs_sub b b') (YMGap.Constructive.ExpNeg.add_le_add2 hb' hb)
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (YMGap.Constructive.ExpNeg.abs_eqv_congr e)) ?_
  refine Q'.le_trans' _ _ _ (YMGap.Constructive.ExpNeg.abs_add_le _ _) (YMGap.Constructive.ExpNeg.add_le_add2 ?_ ?_)
  · exact Q'.le_trans' _ _ _ (YMGap.Constructive.ExpNeg.abs_mul_le _ _)
      (Q'.mul_le_mul_of_nonneg hbabs hc (Q'.le_trans' _ _ _ (Q'.abs_nonneg b) hbabs) (Q'.abs_nonneg _))
  · exact Q'.le_trans' _ _ _ (YMGap.Constructive.ExpNeg.abs_mul_le _ _)
      (Q'.mul_le_mul_of_nonneg hc' hb (Q'.le_trans' _ _ _ (Q'.abs_nonneg c') hc') (Q'.abs_nonneg _))

variable {M : Nat} (hM : 1 ≤ M)

/-- **CS passes to any rational approximants (PROVED; no limit object).** -/
theorem cs_limit {β : Q'} (hβ : (0 : Q') ≤ β) {F G : RatPoly} (hF : PtSup (M := M) F) (hG : PtSup (M := M) G)
    {a b c C : Q'} {r : Nat → Q'}
    (ha : ∀ K, Q'.abs (a + -rpB hM β K F G) ≤ r K) (hb : ∀ K, Q'.abs (b + -rpB hM β K F F) ≤ r K)
    (hc : ∀ K, Q'.abs (c + -rpB hM β K G G) ≤ r K)
    (hCa : ∀ K, Q'.abs (rpB hM β K F G) ≤ C) (hCb : ∀ K, Q'.abs (rpB hM β K F F) ≤ C)
    (hCc : ∀ K, Q'.abs (rpB hM β K G G) ≤ C) (K : Nat) :
    a * a ≤ (b * c + ((C + r K) * r K + C * r K)) + ((C + r K) * r K + C * r K) :=
  YMGap.Continuum.SU2TorusRPKLimit.cs_closed hM hβ hF hG (r := fun K => (C + r K) * r K + C * r K)
    (fun K => prod_pert (ha K) (ha K) (hCa K) (hCa K)) (fun K => prod_pert (hb K) (hc K) (hCb K) (hCc K)) K

end YMGap.Continuum.SU2TorusRPKClosed

#print axioms YMGap.Continuum.SU2TorusRPKClosed.prod_pert
#print axioms YMGap.Continuum.SU2TorusRPKClosed.cs_limit
