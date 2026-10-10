/-
A scalar signed-pair budget.  All form comparisons and mixed-error estimates
are explicit inputs; this file supplies only constructive rational/real order
algebra for their final combination.

The two-sector budget retains a squared mixed estimate, rather than paying
the mixed term by a linear absolute error. With sector separation g>0 the
computed extra cost is eta^2/g. Zero sector norms and margins need no split,
square root or division. This constructs neither an OS projection nor a
Yang--Mills sector/cross estimate.
-/

import YMGap.Continuum.BoundedTransferCalculus
import YMGap.Continuum.FCLimitContinuity
import YMGap.Continuum.RingNormaliser
import YMGap.Continuum.RCNonnegativeSquareReflection
import YMGap.Constructive.RegularCRealArith
import YMGap.Constructive.CRealMulMono

namespace YMGap.Continuum.RCSignedPairBudget

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser

local infix:50 " ≈ " => Q'.eqv

/-- The two-sided quarter-error coefficient. -/
def quarter (d : Q') : Q' := HalfPow.half * (HalfPow.half * d)

/-- Exactly the rational ratio d/(2L), written as (d/2)/L so the
constructive reciprocal cancellation has a direct normal form. -/
def coefficient (d L : Q') (hL : (0 : Q') < L) : Q' :=
  Q'.divPos (HalfPow.half * d) L hL

theorem coefficient_nonnegative (d L : Q') (hL : (0 : Q') < L)
    (hd : (0 : Q') ≤ d) : (0 : Q') ≤ coefficient d L hL := by
  unfold coefficient Q'.divPos
  exact Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _ HalfPow.half_nonneg hd)
    (Q'.le_of_lt (Q'.recipPos_pos L hL))

theorem coefficient_mul_L (d L : Q') (hL : (0 : Q') < L) :
    coefficient d L hL * L ≈ HalfPow.half * d :=
  Q'.divPos_mul_eqv _ _ hL

/-- Order reversal on the actual real quotient. -/
theorem neg_mono {a b : RC} (h : RCle a b) : RCle (RCneg b) (RCneg a) := by
  revert h
  refine Quotient.inductionOn₂ a b ?_
  intro A B h
  intro epsilon hepsilon
  obtain ⟨N, hN⟩ := h epsilon hepsilon
  exact ⟨N, fun n hn => Q'.neg_le_neg_add' (hN n hn)⟩

theorem scale_congr {s t : Q'} (h : s ≈ t) (a : RC) :
    RCscale s a = RCscale t a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.mul_eqv_congr_right s t (A.approx n) h))

private theorem sub_mono {a a' b b' : RC}
    (ha : RCle a a') (hb : RCle b' b) :
    RCle (RCsub a b) (RCsub a' b') :=
  RCadd_le_add ha (neg_mono hb)

private theorem zero_add (a : RC) : RCadd RCzero a = a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.eqv_of_eq (Q'.zero_add' (A.approx n))))

private theorem neg_add_same (a : RC) :
    RCsub (RCneg a) a = RCneg (RCadd a a) := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.neg (.var 0)) (.neg (.var 0)))
      (.neg (.add (.var 0) (.var 0))) (by decide)
      (fun _ => A.approx n)))

private theorem scale_double (q : Q') (a : RC) :
    RCadd (RCscale q a) (RCscale q a) = RCscale (q + q) a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))
      (.mul (.add (.var 0) (.var 0)) (.var 1)) (by decide)
      (fun | 0 => q | _ => A.approx n)))

private theorem quarter_boundary (d L : Q') (hL : (0 : Q') < L) (S : RC) :
    RCsub (RCneg (RCscale (quarter d) S)) (RCscale (quarter d) S) =
      RCneg (RCscale (coefficient d L hL) (RCscale L S)) := by
  rw [neg_add_same, scale_double, RCscale_RCscale]
  have hq : quarter d + quarter d ≈ HalfPow.half * d :=
    ExpNeg.two_halves (HalfPow.half * d)
  rw [scale_congr hq S, scale_congr (Q'.eqv_symm (coefficient_mul_L d L hL)) S]

/-- If two signed corrections each cost at most a quarter of d*S, then
the positive reference contribution can be dropped and the full signed
term loses at most d/(2L) times the original energy E. -/
theorem signed_pair_lower (L d c : Q') (hL : (0 : Q') < L)
    (hd : (0 : Q') ≤ d) (hc : (0 : Q') ≤ c)
    (e0 a b S E t : RC)
    (he0 : RCnonneg e0)
    (ha : RCle (RCneg (RCscale (quarter d) S)) a)
    (hb : RCle b (RCscale (quarter d) S))
    (hE : RCle (RCscale L S) E)
    (ht : t = RCadd (RCscale c e0) (RCsub a b)) :
    RCle (RCneg (RCscale (coefficient d L hL) E)) t := by
  have hcoeff : (0 : Q') ≤ coefficient d L hL := coefficient_nonnegative d L hL hd
  have hscaled : RCle (RCscale (coefficient d L hL) (RCscale L S))
      (RCscale (coefficient d L hL) E) := RCscale_mono hcoeff hE
  have hbase : RCle (RCneg (RCscale (coefficient d L hL) E))
      (RCsub (RCneg (RCscale (quarter d) S)) (RCscale (quarter d) S)) := by
    rw [quarter_boundary d L hL S]
    exact neg_mono hscaled
  have herror := sub_mono ha hb
  have hpositive : RCle RCzero (RCscale c e0) := by
    rw [← RCscale_RCzero c]
    exact RCscale_mono hc he0
  rw [ht]
  exact RCle_trans hbase (RCle_trans herror
    (by simpa only [zero_add] using RCadd_le_add hpositive (RCle_refl (RCsub a b))))

/-! ## Sharp two-sector absorption, including degenerate sectors -/

local instance : Add PolyExpr := ⟨PolyExpr.add⟩
local instance : Mul PolyExpr := ⟨PolyExpr.mul⟩

private theorem four_product_le_sum_square (a b : RC) :
    RCle (RCscale 4 (RCmul a b))
      (RCmul (RCadd a b) (RCadd a b)) := by
  refine Quotient.inductionOn₂ a b ?_
  intro A B
  intro epsilon hepsilon
  refine ⟨0, fun n _ => ?_⟩
  let V := PolyExpr.var
  have h : (0 : Q') ≤
      (A.approx n + B.approx n) * (A.approx n + B.approx n) +
        -(4 * (A.approx n * B.approx n)) :=
    Q'.le_trans' _ _ _
      (SumOfSquares.q_mul_self_nonneg (A.approx n + -(B.approx n)))
      (Q'.le_of_eqv (poly_identity_of_normal_eq
        ((V 0 + .neg (V 1)) * (V 0 + .neg (V 1)))
        ((V 0 + V 1) * (V 0 + V 1) + .neg (.const 4 * (V 0 * V 1)))
        (by decide) (fun | 0 => A.approx n | _ => B.approx n)))
  exact Q'.le_trans' _ _ _ (Q'.le_of_sub_nonneg h)
    (Q'.add_le_self_of_nonneg _ epsilon (Q'.le_of_lt hepsilon))

private theorem double_square (m : RC) :
    RCmul (RCscale 2 m) (RCscale 2 m) = RCscale 4 (RCmul m m) := by
  refine Quotient.inductionOn m ?_
  intro M
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.mul (.mul (.const 2) (.var 0)) (.mul (.const 2) (.var 0)))
      (.mul (.const 4) (.mul (.var 0) (.var 0)))
      (by decide) (fun _ => M.approx n)))

/-- Sharp root-free absorption: m^2<=a*b and a,b>=0 imply 2m<=a+b.
Signed m and zero budgets are included; no positive norm is a premise. -/
theorem two_cross_le_add_of_square_le_product (m a b : RC)
    (ha : RCnonneg a) (hb : RCnonneg b)
    (hm : RCle (RCmul m m) (RCmul a b)) :
    RCle (RCscale 2 m) (RCadd a b) := by
  have hnonnegative : RCnonneg (RCadd a b) := by
    have h := RCadd_le_add ha hb
    simpa only [zero_add] using h
  have hsquare := RCle_trans (RCscale_mono (by decide : (0 : Q') ≤ 4) hm)
    (four_product_le_sum_square a b)
  rw [← double_square] at hsquare
  exact RCsquare_le_reflect_right_nonnegative hnonnegative hsquare

private theorem product_nonnegative {a b : RC}
    (ha : RCnonneg a) (hb : RCnonneg b) : RCnonneg (RCmul a b) := by
  revert ha hb
  refine Quotient.inductionOn₂ a b ?_
  intro A B ha hb
  exact CReal.mul_nonneg ha hb

private theorem scaled_product (s t : Q') (a b : RC) :
    RCmul (RCscale s a) (RCscale t b) = RCscale (s*t) (RCmul a b) := by
  refine Quotient.inductionOn₂ a b ?_
  intro A B
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3)))
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
      (by decide) (fun | 0 => s | 1 => t | 2 => A.approx n | _ => B.approx n)))

/-- Combine diagonal sector caps and a squared mixed cap at its Schur
threshold. For an orthogonal input split, a+b is the SAME total squared norm.
The theorem does not supply that split or any of these physical estimates. -/
theorem twoSector_upper_of_squared_cross (alpha beta q eta : Q')
    (halpha : alpha ≤ q) (hbeta : beta ≤ q)
    (heta : eta*eta ≤ (q-alpha)*(q-beta))
    (a b x y m : RC) (ha : RCnonneg a) (hb : RCnonneg b)
    (hx : RCle x (RCscale alpha a)) (hy : RCle y (RCscale beta b))
    (hm : RCle (RCmul m m) (RCscale (eta*eta) (RCmul a b))) :
    RCle (RCadd (RCadd x (RCscale 2 m)) y) (RCscale q (RCadd a b)) := by
  have hA : RCnonneg (RCscale (q-alpha) a) := by
    have h := RCscale_mono (Q'.sub_nonneg_of_le halpha) ha
    simpa only [RCscale_RCzero] using h
  have hB : RCnonneg (RCscale (q-beta) b) := by
    have h := RCscale_mono (Q'.sub_nonneg_of_le hbeta) hb
    simpa only [RCscale_RCzero] using h
  have hprod := RCle_trans hm (RCscale_mono_scalar heta (product_nonnegative ha hb))
  rw [← scaled_product] at hprod
  have hcross := two_cross_le_add_of_square_le_product m _ _ hA hB hprod
  have hsum := RCadd_le_add (RCadd_le_add hx hcross) hy
  have he : RCadd (RCadd (RCscale alpha a)
      (RCadd (RCscale (q-alpha) a) (RCscale (q-beta) b))) (RCscale beta b) =
        RCscale q (RCadd a b) := by
    refine Quotient.inductionOn₂ a b ?_
    intro A B
    let V := PolyExpr.var
    exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
      poly_identity_of_normal_eq
        (V 0 * V 3 + ((V 2 + .neg (V 0)) * V 3 +
          (V 2 + .neg (V 1)) * V 4) + V 1 * V 4)
        (V 2 * (V 3 + V 4)) (by decide)
        (fun | 0 => alpha | 1 => beta | 2 => q | 3 => A.approx n | _ => B.approx n)))
  rwa [he] at hsum

/-- Computed rational mixed-sector cost. The only divided quantity is the
supplied positive rational separation, never a state norm or real quotient. -/
def twoSectorCost (eta g : Q') (hg : (0 : Q') < g) : Q' :=
  Q'.divPos (eta*eta) g hg

theorem twoSectorCost_nonnegative (eta g : Q') (hg : (0 : Q') < g) :
    (0 : Q') ≤ twoSectorCost eta g hg :=
  Q'.mul_nonneg _ _ (SumOfSquares.q_mul_self_nonneg eta)
    (Q'.le_of_lt (Q'.recipPos_pos g hg))

theorem twoSectorCost_mul_gap (eta g : Q') (hg : (0 : Q') < g) :
    twoSectorCost eta g hg * g ≈ eta*eta := Q'.divPos_mul_eqv _ _ hg

/-- A positive separation gives a full computed Schur budget with quadratic
cost eta^2/g, including eta=0. Strictness q<1 is NOT asserted without a further
smallness estimate on this cost. -/
theorem twoSectorCost_cap_criteria (alpha beta eta g : Q')
    (hg : (0 : Q') < g) (hgap : g ≤ alpha-beta) :
    let q := alpha + twoSectorCost eta g hg
    alpha ≤ q ∧ beta ≤ q ∧ eta*eta ≤ (q-alpha)*(q-beta) := by
  let e := twoSectorCost eta g hg
  have he : (0 : Q') ≤ e := twoSectorCost_nonnegative eta g hg
  have hab : beta ≤ alpha :=
    Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _ (Q'.le_of_lt hg) hgap)
  have haq : alpha ≤ alpha+e := Q'.add_le_self_of_nonneg _ _ he
  refine ⟨haq, Q'.le_trans' _ _ _ hab haq, ?_⟩
  have hge : g ≤ (alpha-beta)+e :=
    Q'.le_trans' _ _ _ hgap (Q'.add_le_self_of_nonneg _ _ he)
  have hmul : e*g ≤ e*((alpha-beta)+e) :=
    Q'.mul_le_mul_of_nonneg_left _ _ e hge he
  let V := PolyExpr.var
  have hid : e*((alpha-beta)+e) ≈ ((alpha+e)-alpha)*((alpha+e)-beta) :=
    poly_identity_of_normal_eq
      (V 2 * ((V 0 + .neg (V 1)) + V 2))
      (((V 0 + V 2) + .neg (V 0)) * ((V 0 + V 2) + .neg (V 1)))
      (by decide) (fun | 0 => alpha | 1 => beta | _ => e)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (twoSectorCost_mul_gap eta g hg))
    (Q'.le_trans' _ _ _ hmul (Q'.le_of_eqv hid))

#print axioms quarter
#print axioms coefficient
#print axioms coefficient_nonnegative
#print axioms coefficient_mul_L
#print axioms neg_mono
#print axioms scale_congr
#print axioms signed_pair_lower
#print axioms two_cross_le_add_of_square_le_product
#print axioms twoSector_upper_of_squared_cross
#print axioms twoSectorCost
#print axioms twoSectorCost_nonnegative
#print axioms twoSectorCost_mul_gap
#print axioms twoSectorCost_cap_criteria

end YMGap.Continuum.RCSignedPairBudget
