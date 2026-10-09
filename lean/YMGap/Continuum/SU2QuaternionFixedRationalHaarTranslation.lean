/-
# Fixed rational left/right translations preserve every polynomial Haar moment

The multiplier is a supplied rational unit quaternion, not a second Haar
variable.  The coefficient-valued head-moment theorem is specialized at that
multiplier before the remaining scalar evaluation.  The source polynomial is
supported on ONE quaternion block; this hypothesis is essential.

The evaluation theorem identifies the resulting polynomial with the original
Hamilton action, in both orders and at every degree.  This supplies finite
polynomial Haar invariance, not a compact-group measure on arbitrary functions,
an interacting change of physical action, or any spectral-gap assertion.
-/

import YMGap.Continuum.SU2QuaternionTranslationHaarMoments
import YMGap.Continuum.SU2QuaternionTailEvaluation
import YMGap.Continuum.SU2QuaternionHeadLinearHaar
import YMGap.Continuum.RatPolySubstitution
import YMGap.RepTheory.RationalQuaternionAlgebra

namespace YMGap.Continuum.SU2QuaternionFixedRationalHaarTranslation

open YMGap.Constructive
open YMGap.RepTheory
open YMGap.RepTheory.RationalQuaternion
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionWilsonWeightSOS
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarSphereIdeal
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionPartialSphereGaussian
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionHeadLinearHaar
open YMGap.Continuum.SU2QuaternionPolynomialHaarTranslation
open YMGap.Continuum.SU2QuaternionTranslationHaarMoments
open YMGap.Continuum.SU2QuaternionTailEvaluation

local infix:50 " ≈ " => Q'.eqv
private abbrev PE := PolyExpr
local instance : Add PE := ⟨.add⟩
local instance : Mul PE := ⟨.mul⟩
local instance : Neg PE := ⟨.neg⟩
local instance (n : Nat) : OfNat PE n := ⟨.const (Int.ofNat n)⟩

private theorem ac {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a+c ≈ b+d :=
  Q'.add_eqv_congr' h k
private theorem mc {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h)
    (Q'.mul_eqv_congr_left _ _ _ k)
private theorem nc {a b : Q'} (h : a ≈ b) : -a ≈ -b :=
  Q'.neg_eqv_congr _ _ h
private theorem weighted_eval (rho : Nat → Q') : ∀ p : RatPoly,
    ratWeightedSum (evalMono rho) p = evalRatPoly rho p
  | [] => rfl
  | t::p => congrArg (fun z => t.2*evalMono rho t.1+z) (weighted_eval rho p)
private theorem weighted_haar (blocks : Nat) : ∀ p : RatPoly,
    ratWeightedSum (quaternionHaarMono blocks) p = quaternionHaar blocks p
  | [] => rfl
  | t::p => congrArg (fun z => t.2*quaternionHaarMono blocks t.1+z) (weighted_haar blocks p)
private theorem ev_congr (rho : Nat → Q') {p q : RatPoly}
    (h : RatPolyCoeffEqv p q) : evalRatPoly rho p ≈ evalRatPoly rho q := by
  simpa only [weighted_eval] using h (evalMono rho)
private theorem haar_congr (blocks : Nat) {p q : RatPoly}
    (h : RatPolyCoeffEqv p q) : quaternionHaar blocks p ≈ quaternionHaar blocks q := by
  simpa only [weighted_haar] using h (quaternionHaarMono blocks)

/-- Scalar-first coordinates, with zero outside the actual four coordinates. -/
def quaternionCoordinates (a : RationalQuaternion) : Nat → Q'
  | 0 => a.r | 1 => a.i | 2 => a.j | 3 => a.k | _ => 0

private def translatedQuaternion (right : Bool) : PolyQuaternion :=
  if right then rightTranslatedHeadQuaternion else leftTranslatedHeadQuaternion

/-- Literal fixed-tail specialization; also defined for nonunit sanity tests. -/
def rawFixedTranslatedPolynomial (right : Bool) (g : RationalQuaternion) (p : RatPoly) : RatPoly :=
  evaluateTail 4 (quaternionCoordinates g)
    (translatedHeadPolynomial (translatedQuaternion right) p)

/-- False means `g*x`; true means `x*g`. -/
def fixedTranslatedPolynomial (right : Bool) (g : UnitNorm) (p : RatPoly) : RatPoly :=
  rawFixedTranslatedPolynomial right g.val p

theorem fixedTranslatedPolynomial_supported (right : Bool) (g : UnitNorm) (p : RatPoly) :
    SupportedQuaternionBlocks 1 (fixedTranslatedPolynomial right g p) := by
  intro t ht
  obtain ⟨s, _, rfl⟩ := List.mem_map.mp ht
  change (s.1.take 4).length ≤ 4
  exact List.length_take_le _ _

private theorem eval_power (rho : Nat → Q') (p : RatPoly) : ∀ n,
    evalRatPoly rho (ratPolyPow p n) ≈ qpow (evalRatPoly rho p) n
  | 0 => evalRatPoly_one rho
  | n+1 => Q'.eqv_trans _ _ _ (evalRatPoly_mul rho _ _)
      (mc (eval_power rho p n) (Q'.eqv_refl _))

private theorem power_one : ∀ n, qpow (1 : Q') n ≈ 1
  | 0 => Q'.eqv_refl _
  | n+1 => Q'.eqv_trans _ _ _ (Q'.mul_one_eqv _) (power_one n)

private theorem square_monomial_eval (rho : Nat → Q') : ∀ i start,
    evalMonoFrom rho start (coordinateSquareMono i) ≈ rho (start+i)*rho (start+i)
  | 0, start => by
      change ((1*rho start)*rho start)*1 ≈ rho start*rho start
      exact Q'.eqv_trans _ _ _ (Q'.mul_one_eqv _)
        (mc (Q'.one_mul_eqv _) (Q'.eqv_refl _))
  | i+1, start => by
      change 1 * evalMonoFrom rho (start+1) (coordinateSquareMono i) ≈ _
      exact Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _)
        (by simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          using square_monomial_eval rho i (start+1))

private theorem radius_eval (a : RationalQuaternion) :
    evalRatPoly (quaternionCoordinates a) (quaternionRadiusPolynomial 0) ≈ normSq a := by
  let rho := quaternionCoordinates a
  have hs (i : Nat) : 1*evalMono rho (coordinateSquareMono i) ≈ rho i*rho i :=
    Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _)
      (by simpa only [evalMono, Nat.zero_add] using square_monomial_eval rho i 0)
  have h0 : 1*evalMono rho (coordinateSquareMono 0) ≈ a.r*a.r := hs 0
  have h1 : 1*evalMono rho (coordinateSquareMono 1) ≈ a.i*a.i := hs 1
  have h2 : 1*evalMono rho (coordinateSquareMono 2) ≈ a.j*a.j := hs 2
  have h3 : 1*evalMono rho (coordinateSquareMono 3) ≈ a.k*a.k := hs 3
  have hsum : evalRatPoly rho (quaternionRadiusPolynomial 0) ≈
      a.r*a.r+(a.i*a.i+(a.j*a.j+(a.k*a.k+0))) :=
    ac h0 (ac h1 (ac h2 (ac h3 (Q'.eqv_refl 0))))
  have hzero : a.r*a.r+(a.i*a.i+(a.j*a.j+(a.k*a.k+0))) ≈
      a.r*a.r+(a.i*a.i+(a.j*a.j+a.k*a.k)) :=
    ac (Q'.eqv_refl _) (ac (Q'.eqv_refl _)
      (ac (Q'.eqv_refl _) (QPoly.q_add_zero_eqv _)))
  exact Q'.eqv_trans _ _ _ hsum (Q'.eqv_trans _ _ _ hzero
    (Q'.eqv_symm (Q'.add_assoc_eqv (a.r*a.r) (a.i*a.i) (a.j*a.j+a.k*a.k))))

private theorem radius_power_eval (g : UnitNorm) (n : Nat) :
    evalRatPoly (quaternionCoordinates g.val) (ratPolyPow (quaternionRadiusPolynomial 0) n) ≈ 1 :=
  Q'.eqv_trans _ _ _ (eval_power _ _ n)
    (Q'.eqv_trans _ _ _ (qpow_eqv_congr
      (Q'.eqv_trans _ _ _ (radius_eval g.val) g.unitNorm) n) (power_one n))

private theorem haar_zero_evaluate (rho : Nat → Q') : ∀ p : RatPoly,
    quaternionHaar 0 (evaluateTail 0 rho p) ≈ evalRatPoly rho p
  | [] => Q'.eqv_refl _
  | t::p => by
      change (t.2*evalMono rho t.1)*1 + quaternionHaar 0 (evaluateTail 0 rho p) ≈ _
      exact ac (Q'.mul_one_eqv _) (haar_zero_evaluate rho p)

private theorem fixed_head_integral (rho : Nat → Q') (p : RatPoly) :
    quaternionHaar 1 (evaluateTail 4 rho p) ≈ evalRatPoly rho (partialHaarHead p) :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (quaternionHaar_partialHaarHead 0 _))
    (Q'.eqv_trans _ _ _ (haar_congr 0 (partialHaarHead_evaluate 0 rho p))
      (haar_zero_evaluate rho _))

private theorem fixed_term_haar (right : Bool) (g : UnitNorm) (t : RatTerm)
    (ht : t.1.length ≤ 4) :
    quaternionHaar 1 (evaluateTail 4 (quaternionCoordinates g.val)
      (translatedHeadTerm (translatedQuaternion right) t)) ≈
      t.2 * quaternionHaarMono 1 t.1 := by
  have hd : t.1.drop 4 = [] := List.drop_eq_nil_iff.mpr ht
  let m := translatedHeadMonomial (translatedQuaternion right)
    (exponentAt t.1 0) (exponentAt t.1 1) (exponentAt t.1 2) (exponentAt t.1 3)
  let tail : RatPoly := [(t.1.drop 4,t.2)]
  have h : RatPolyCoeffEqv
      (partialHaarHead (translatedHeadTerm (translatedQuaternion right) t))
      (polyMul (polySmul (headQuaternionMoment t.1)
        (ratPolyPow (quaternionRadiusPolynomial 0)
          ((exponentAt t.1 0+exponentAt t.1 1+exponentAt t.1 2+exponentAt t.1 3)/2))) tail) :=
    (partialHaarHead_mul_lift m tail).trans
      ((translatedHeadMonomial_haar_closed right _ _ _ _).mul_right tail)
  refine Q'.eqv_trans _ _ _ (fixed_head_integral _ _) ?_
  refine Q'.eqv_trans _ _ _ (ev_congr _ h) ?_
  refine Q'.eqv_trans _ _ _ (evalRatPoly_mul _ _ _) ?_
  have hleft : evalRatPoly (quaternionCoordinates g.val)
      (polySmul (headQuaternionMoment t.1)
        (ratPolyPow (quaternionRadiusPolynomial 0)
          ((exponentAt t.1 0+exponentAt t.1 1+exponentAt t.1 2+exponentAt t.1 3)/2))) ≈
      headQuaternionMoment t.1 :=
    Q'.eqv_trans _ _ _ (evalRatPoly_smul _ _ _)
      (Q'.eqv_trans _ _ _ (mc (Q'.eqv_refl _) (radius_power_eval g _)) (Q'.mul_one_eqv _))
  have htail : evalRatPoly (quaternionCoordinates g.val) tail ≈ t.2 := by
    simp only [tail, hd, evalRatPoly, evalMono, evalMonoFrom]
    exact Q'.eqv_trans _ _ _ (QPoly.q_add_zero_eqv _) (Q'.mul_one_eqv _)
  have hm : quaternionHaarMono 1 t.1 ≈ headQuaternionMoment t.1 := by
    simp only [quaternionHaarMono, show 4*1=4 from rfl, hd, allZero,
      if_true, quaternionHaarPrefix]
    exact Q'.mul_one_eqv _
  exact Q'.eqv_trans _ _ _ (mc hleft htail)
    (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (mc (Q'.eqv_refl _) (Q'.eqv_symm hm)))

/-- Every degree, with a FIXED multiplier and the original one-block Haar. -/
theorem fixedTranslatedPolynomial_haar (right : Bool) (g : UnitNorm) :
    ∀ p : RatPoly, SupportedQuaternionBlocks 1 p →
      quaternionHaar 1 (fixedTranslatedPolynomial right g p) ≈ quaternionHaar 1 p
  | [], _ => Q'.eqv_refl _
  | t::p, hp => by
      change quaternionHaar 1 (evaluateTail 4 (quaternionCoordinates g.val)
        (polyAdd (translatedHeadTerm _ t) (translatedHeadPolynomial _ p))) ≈ _
      rw [evaluate_add]
      exact Q'.eqv_trans _ _ _ (quaternionHaar_append 1 _ _)
        (ac (fixed_term_haar right g t (hp t List.mem_cons_self))
          (fixedTranslatedPolynomial_haar right g p
            (fun s hs => hp s (List.mem_cons_of_mem t hs))))

/-! The specialization is the literal Hamilton action, not only a moment pin. -/

private def splice (keep : Nat) (head tail : Nat → Q') (i : Nat) : Q' :=
  if i < keep then head i else tail (i-keep)

private theorem mono_shift (rho : Nat → Q') (s : Nat) : ∀ (m : List Nat) (i : Nat),
    evalMonoFrom rho (s+i) m = evalMonoFrom (fun j => rho (s+j)) i m
  | [], _ => rfl
  | _::m, i => by
      simp only [evalMonoFrom]
      rw [show s+i+1=s+(i+1) from Nat.add_assoc _ _ _, mono_shift rho s m (i+1)]

private theorem mono_cons (rho : Nat → Q') (e : Nat) (m : List Nat) :
    evalMono rho (e::m) = qpow (rho 0) e * evalMono (fun j => rho (j+1)) m := by
  unfold evalMono
  simp only [evalMonoFrom]
  congr 1
  simpa only [Nat.add_zero, Nat.add_comm] using mono_shift rho 1 m 0

private theorem mono_splice : ∀ (keep : Nat) (head tail : Nat → Q') (m : List Nat),
    evalMono (splice keep head tail) m ≈
      evalMono head (m.take keep) * evalMono tail (m.drop keep)
  | 0, head, tail, m => by
      simpa only [splice, Nat.not_lt_zero, if_false, Nat.sub_zero, List.take_zero,
        List.drop_zero, evalMono, evalMonoFrom] using
        Q'.eqv_symm (Q'.one_mul_eqv (evalMono tail m))
  | keep+1, head, tail, [] => by
      change (1 : Q') ≈ 1*1
      decide
  | keep+1, head, tail, e::m => by
      rw [mono_cons, List.take_succ_cons, List.drop_succ_cons, mono_cons]
      have hshift : (fun j => splice (keep+1) head tail (j+1)) =
          splice keep (fun j => head (j+1)) tail := by
        funext j
        unfold splice
        by_cases hj : j < keep
        · simp only [hj, Nat.succ_lt_succ_iff, if_true]
        · simp only [hj, Nat.succ_lt_succ_iff, if_false, Nat.add_sub_add_right]
      rw [hshift]
      have hzero : splice (keep+1) head tail 0 = head 0 := by simp [splice]
      rw [hzero]
      exact Q'.eqv_trans _ _ _ (mc (Q'.eqv_refl _)
        (mono_splice keep (fun j => head (j+1)) tail m))
        (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))

private theorem evaluate_eval (keep : Nat) (head tail : Nat → Q') : ∀ p : RatPoly,
    evalRatPoly head (evaluateTail keep tail p) ≈ evalRatPoly (splice keep head tail) p
  | [] => Q'.eqv_refl _
  | t::p => by
      refine ac ?_ (evaluate_eval keep head tail p)
      change (t.2*evalMono tail (t.1.drop keep))*evalMono head (t.1.take keep) ≈ _
      refine Q'.eqv_trans _ (t.2*(evalMono head (t.1.take keep)*evalMono tail (t.1.drop keep))) _ ?_ ?_
      · exact poly_identity_of_normal_eq ((.var 0*.var 1)*.var 2)
          (.var 0*(.var 2*.var 1)) (by decide)
          (fun | 0 => t.2 | 1 => evalMono tail (t.1.drop keep) | _ => evalMono head (t.1.take keep))
      · exact mc (Q'.eqv_refl _) (Q'.eqv_symm (mono_splice keep head tail t.1))

private def value (a : RationalQuaternion) : QuaternionValue := ⟨a.r,a.i,a.j,a.k⟩

private theorem value_mul (a b : RationalQuaternion) :
    QuaternionValue.Eqv (QuaternionValue.mul (value a) (value b)) (value (mul a b)) := by
  constructor
  · exact poly_identity_of_normal_eq
      (.var 0 + -(.var 1+(.var 2+.var 3))) ((.var 0 + -(.var 1))+(-(.var 2)+ -(.var 3)))
      (by decide) (fun | 0 => a.r*b.r | 1 => a.i*b.i | 2 => a.j*b.j | _ => a.k*b.k)
  · exact Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)
  · exact poly_identity_of_normal_eq
      (.var 0+(.var 1+(.var 2 + -(.var 3)))) ((.var 0 + -(.var 3))+(.var 1+.var 2))
      (by decide) (fun | 0 => a.r*b.j | 1 => a.j*b.r | 2 => a.k*b.i | _ => a.i*b.k)
  · exact poly_identity_of_normal_eq
      (.var 0+(.var 1+(.var 2 + -(.var 3)))) ((.var 0+.var 2)+(-(.var 3)+.var 1))
      (by decide) (fun | 0 => a.r*b.k | 1 => a.k*b.r | 2 => a.i*b.j | _ => a.j*b.i)

private theorem value_mul_congr {a b c d : QuaternionValue}
    (h : QuaternionValue.Eqv a b) (k : QuaternionValue.Eqv c d) :
    QuaternionValue.Eqv (QuaternionValue.mul a c) (QuaternionValue.mul b d) :=
  ⟨ac (mc h.scalar k.scalar) (nc (ac (mc h.iPart k.iPart)
      (ac (mc h.jPart k.jPart) (mc h.kPart k.kPart)))),
   ac (mc h.scalar k.iPart) (ac (mc h.iPart k.scalar)
      (ac (mc h.jPart k.kPart) (nc (mc h.kPart k.jPart)))),
   ac (mc h.scalar k.jPart) (ac (mc h.jPart k.scalar)
      (ac (mc h.kPart k.iPart) (nc (mc h.iPart k.kPart)))),
   ac (mc h.scalar k.kPart) (ac (mc h.kPart k.scalar)
      (ac (mc h.iPart k.jPart) (nc (mc h.jPart k.iPart))))⟩

private theorem value_trans {a b c : QuaternionValue}
    (h : QuaternionValue.Eqv a b) (k : QuaternionValue.Eqv b c) : QuaternionValue.Eqv a c :=
  ⟨Q'.eqv_trans _ _ _ h.scalar k.scalar, Q'.eqv_trans _ _ _ h.iPart k.iPart,
   Q'.eqv_trans _ _ _ h.jPart k.jPart, Q'.eqv_trans _ _ _ h.kPart k.kPart⟩

private theorem translated_value (right : Bool) (g x : RationalQuaternion) :
    QuaternionValue.Eqv
      (evalPolyQuaternion (splice 4 (quaternionCoordinates x) (quaternionCoordinates g))
        (translatedQuaternion right))
      (value (if right then mul x g else mul g x)) := by
  let rho := splice 4 (quaternionCoordinates x) (quaternionCoordinates g)
  have hx : QuaternionValue.Eqv (evalPolyQuaternion rho (PolyQuaternion.coordinateVariable 0)) (value x) :=
    ⟨evalRatPoly_var rho 0, evalRatPoly_var rho 1, evalRatPoly_var rho 2, evalRatPoly_var rho 3⟩
  have hg : QuaternionValue.Eqv (evalPolyQuaternion rho (PolyQuaternion.coordinateVariable 1)) (value g) :=
    ⟨evalRatPoly_var rho 4, evalRatPoly_var rho 5, evalRatPoly_var rho 6, evalRatPoly_var rho 7⟩
  cases right
  · exact value_trans (evalPolyQuaternion_mul rho _ _) (value_trans (value_mul_congr hg hx) (value_mul g x))
  · exact value_trans (evalPolyQuaternion_mul rho _ _) (value_trans (value_mul_congr hx hg) (value_mul x g))

private theorem monomial_value (rho : Nat → Q') (q : PolyQuaternion) (a : RationalQuaternion)
    (h : QuaternionValue.Eqv (evalPolyQuaternion rho q) (value a)) (e0 e1 e2 e3 : Nat) :
    evalRatPoly rho (translatedHeadMonomial q e0 e1 e2 e3) ≈
      qpow a.r e0*(qpow a.i e1*(qpow a.j e2*qpow a.k e3)) := by
  have power (p : RatPoly) (v : Q') (hv : evalRatPoly rho p ≈ v) (e : Nat) :=
    Q'.eqv_trans _ _ _ (eval_power rho p e) (qpow_eqv_congr hv e)
  exact Q'.eqv_trans _ _ _ (evalRatPoly_mul rho _ _)
    (mc (power _ _ h.scalar e0) (Q'.eqv_trans _ _ _ (evalRatPoly_mul rho _ _)
      (mc (power _ _ h.iPart e1) (Q'.eqv_trans _ _ _ (evalRatPoly_mul rho _ _)
        (mc (power _ _ h.jPart e2) (power _ _ h.kPart e3))))))

private theorem four_monomial (a : RationalQuaternion) (m : List Nat) (hm : m.length ≤ 4) :
    evalMono (quaternionCoordinates a) m ≈
      qpow a.r (exponentAt m 0)*(qpow a.i (exponentAt m 1)*
        (qpow a.j (exponentAt m 2)*qpow a.k (exponentAt m 3))) := by
  cases m with
  | nil => change (1 : Q') ≈ 1*(1*(1*1)); decide
  | cons e0 m => cases m with
    | nil => exact mc (Q'.eqv_refl _) (by decide : (1:Q') ≈ 1*(1*1))
    | cons e1 m => cases m with
      | nil => exact mc (Q'.eqv_refl _) (mc (Q'.eqv_refl _) (by decide : (1:Q') ≈ 1*1))
      | cons e2 m => cases m with
        | nil => exact Q'.eqv_refl _
        | cons e3 m =>
          have hlen : m.length = 0 := by simp only [List.length_cons] at hm; omega
          have he : m = [] := List.length_eq_zero_iff.mp hlen
          subst m
          exact mc (Q'.eqv_refl _) (mc (Q'.eqv_refl _) (mc (Q'.eqv_refl _) (Q'.mul_one_eqv _)))

private theorem translated_term_eval (right : Bool) (g x : RationalQuaternion)
    (t : RatTerm) (ht : t.1.length ≤ 4) :
    evalRatPoly (splice 4 (quaternionCoordinates x) (quaternionCoordinates g))
      (translatedHeadTerm (translatedQuaternion right) t) ≈
      t.2 * evalMono (quaternionCoordinates (if right then mul x g else mul g x)) t.1 := by
  let rho := splice 4 (quaternionCoordinates x) (quaternionCoordinates g)
  have hd : t.1.drop 4 = [] := List.drop_eq_nil_iff.mpr ht
  have htval : evalRatPoly rho (headTailLiftTerm t) ≈ t.2 := by
    simp only [headTailLiftTerm, hd, List.append_nil, evalRatPoly, evalMono, evalMonoFrom, qpow]
    exact Q'.eqv_trans _ _ _ (QPoly.q_add_zero_eqv _)
      (Q'.eqv_trans _ _ _
        (mc (Q'.eqv_refl _) (by decide : (1:Q')*(1*(1*(1*1))) ≈ 1))
        (Q'.mul_one_eqv _))
  refine Q'.eqv_trans _ _ _ (evalRatPoly_mul rho _ _) ?_
  refine Q'.eqv_trans _ _ _
    (mc (monomial_value rho _ _ (translated_value right g x) _ _ _ _) htval) ?_
  exact Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _)
    (mc (Q'.eqv_refl _) (Q'.eqv_symm (four_monomial _ t.1 ht)))

private theorem translated_eval (right : Bool) (g x : RationalQuaternion) :
    ∀ p : RatPoly, SupportedQuaternionBlocks 1 p →
    evalRatPoly (splice 4 (quaternionCoordinates x) (quaternionCoordinates g))
      (translatedHeadPolynomial (translatedQuaternion right) p) ≈
    evalRatPoly (quaternionCoordinates (if right then mul x g else mul g x)) p
  | [], _ => Q'.eqv_refl _
  | t::p, hp => Q'.eqv_trans _ _ _ (evalRatPoly_add _ _ _)
      (ac (translated_term_eval right g x t (hp t List.mem_cons_self))
        (translated_eval right g x p (fun s hs => hp s (List.mem_cons_of_mem t hs))))

/-- Evaluation is exactly the original Hamilton action at the supplied point. -/
theorem fixedTranslatedPolynomial_eval (right : Bool) (g x : UnitNorm)
    (p : RatPoly) (hp : SupportedQuaternionBlocks 1 p) :
    evalRatPoly (quaternionCoordinates x.val) (fixedTranslatedPolynomial right g p) ≈
      evalRatPoly (quaternionCoordinates (if right then mul x.val g.val else mul g.val x.val)) p :=
  Q'.eqv_trans _ _ _ (evaluate_eval 4 _ _ _) (translated_eval right g.val x.val p hp)

/-- The equatorial quaternion is an actual supplied rational unit point. -/
def equatorialUnit : UnitNorm := ⟨basisI, by unfold IsUnitNorm normSq basisI; decide⟩

/-- Both central signs are retained, for both multiplication orders. -/
theorem central_signs_evaluation (right : Bool) :
    (evalRatPoly (quaternionCoordinates unitOne.val)
      (fixedTranslatedPolynomial right unitOne (polyVar 0)) ≈ 1) ∧
    (evalRatPoly (quaternionCoordinates unitOne.val)
      (fixedTranslatedPolynomial right unitNegativeOne (polyVar 0)) ≈ -1) := by
  cases right <;> decide

/-- No hemisphere assumption is used at an equatorial multiplier. -/
theorem equatorial_evaluation (right : Bool) :
    evalRatPoly (quaternionCoordinates unitOne.val)
      (fixedTranslatedPolynomial right equatorialUnit (polyVar 1)) ≈ 1 := by
  cases right <;> decide

/-- Unit norm is necessary: scalar multiplication by two changes the actual
one-block second moment from one quarter to one. -/
theorem nonunit_scalar_two_failure (right : Bool) :
    (quaternionHaar 1 (rawFixedTranslatedPolynomial right (scalar 2)
      (polyMul (polyVar 0) (polyVar 0))) ≈ 1) ∧
    (quaternionHaar 1 (polyMul (polyVar 0) (polyVar 0)) ≈ Q'.mkPos 1 4 (by decide)) ∧
    ¬ (quaternionHaar 1 (rawFixedTranslatedPolynomial right (scalar 2)
      (polyMul (polyVar 0) (polyVar 0))) ≈
        quaternionHaar 1 (polyMul (polyVar 0) (polyVar 0))) := by
  cases right <;> decide

end YMGap.Continuum.SU2QuaternionFixedRationalHaarTranslation

#print axioms YMGap.Continuum.SU2QuaternionFixedRationalHaarTranslation.fixedTranslatedPolynomial_supported
#print axioms YMGap.Continuum.SU2QuaternionFixedRationalHaarTranslation.fixedTranslatedPolynomial_haar
#print axioms YMGap.Continuum.SU2QuaternionFixedRationalHaarTranslation.fixedTranslatedPolynomial_eval
#print axioms YMGap.Continuum.SU2QuaternionFixedRationalHaarTranslation.central_signs_evaluation
#print axioms YMGap.Continuum.SU2QuaternionFixedRationalHaarTranslation.equatorial_evaluation
#print axioms YMGap.Continuum.SU2QuaternionFixedRationalHaarTranslation.nonunit_scalar_two_failure
