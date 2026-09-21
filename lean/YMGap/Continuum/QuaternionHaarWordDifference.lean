/-
# Exact ordered-word differences and their original weighted Haar cost

Replace one factor at a time without commuting quaternion products. The
resulting finite telescope keeps its literal prefix and suffix. Haar-unit
norms remove those factors only from the squared norm of each increment,
under arbitrary insertions. The consumer is a Wilson time-increment bound
in the original edge measure, not a spectral or continuum theorem.
-/

import YMGap.Continuum.BF4ExactSlabTemporalGaugeWilsonWord
import YMGap.Continuum.QuaternionHaarUnitScalarSquare
import YMGap.Continuum.QuaternionHaarFamilySquare
import YMGap.Continuum.QuaternionHaarFiniteCauchyCertificate

namespace YMGap.Continuum.QuaternionHaarWordDifference

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabTemporalGaugeWilsonWord (wordWith)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.QuaternionHaarUnitScalarSquare
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarFamilySquare
open YMGap.Continuum.QuaternionHaarFiniteCauchyCertificate

local infix:50 " ≈ " => Q'.eqv
local infixl:70 " ⋄ " => PolyQuaternion.mul

/-- Literal componentwise difference; no quotient or pointwise replacement. -/
def difference (p q : PolyQuaternion) : PolyQuaternion :=
  ⟨polyAdd p.scalar (polyNeg q.scalar), polyAdd p.iPart (polyNeg q.iPart),
    polyAdd p.jPart (polyNeg q.jPart), polyAdd p.kPart (polyNeg q.kPart)⟩

private theorem support_neg {n : Nat} {p : RatPoly} (hp : SupportedQuaternionBlocks n p) :
    SupportedQuaternionBlocks n (polyNeg p) := by
  intro t ht
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp ht
  exact hp s hs

theorem difference_supported {n : Nat} {p q : PolyQuaternion}
    (hp : Supported n p) (hq : Supported n q) : Supported n (difference p q) :=
  ⟨supported_add hp.scalar (support_neg hq.scalar),
    supported_add hp.iPart (support_neg hq.iPart),
    supported_add hp.jPart (support_neg hq.jPart),
    supported_add hp.kPart (support_neg hq.kPart)⟩

private def env (p q r : PolyQuaternion) : Nat → RatPoly
  | 0 => p.scalar | 1 => p.iPart | 2 => p.jPart | 3 => p.kPart
  | 4 => q.scalar | 5 => q.iPart | 6 => q.jPart | 7 => q.kPart
  | 8 => r.scalar | 9 => r.iPart | 10 => r.jPart | _ => r.kPart

private def subExpr (p q : PolyQuaternionExpr) : PolyQuaternionExpr :=
  ⟨.add p.scalar (.neg q.scalar), .add p.iPart (.neg q.iPart),
    .add p.jPart (.neg q.jPart), .add p.kPart (.neg q.kPart)⟩

theorem difference_mul (p q r : PolyQuaternion) :
    PolyQuaternionCoeffEqv (difference p q ⋄ r) (difference (p ⋄ r) (q ⋄ r)) := by
  let l := PolyQuaternionExpr.mul
    (subExpr (.coordinate 0) (.coordinate 4)) (.coordinate 8)
  let r' := subExpr (PolyQuaternionExpr.mul (.coordinate 0) (.coordinate 8))
    (PolyQuaternionExpr.mul (.coordinate 4) (.coordinate 8))
  exact ⟨coeffEvalExpr_eqv_of_normalize_eq l.scalar r'.scalar (by decide) (env p q r),
    coeffEvalExpr_eqv_of_normalize_eq l.iPart r'.iPart (by decide) (env p q r),
    coeffEvalExpr_eqv_of_normalize_eq l.jPart r'.jPart (by decide) (env p q r),
    coeffEvalExpr_eqv_of_normalize_eq l.kPart r'.kPart (by decide) (env p q r)⟩

theorem mul_difference (p q r : PolyQuaternion) :
    PolyQuaternionCoeffEqv (p ⋄ difference q r) (difference (p ⋄ q) (p ⋄ r)) := by
  let l := PolyQuaternionExpr.mul (.coordinate 0)
    (subExpr (.coordinate 4) (.coordinate 8))
  let r' := subExpr (PolyQuaternionExpr.mul (.coordinate 0) (.coordinate 4))
    (PolyQuaternionExpr.mul (.coordinate 0) (.coordinate 8))
  exact ⟨coeffEvalExpr_eqv_of_normalize_eq l.scalar r'.scalar (by decide) (env p q r),
    coeffEvalExpr_eqv_of_normalize_eq l.iPart r'.iPart (by decide) (env p q r),
    coeffEvalExpr_eqv_of_normalize_eq l.jPart r'.jPart (by decide) (env p q r),
    coeffEvalExpr_eqv_of_normalize_eq l.kPart r'.kPart (by decide) (env p q r)⟩

/-- Original ordered one-factor increments, retaining every prefix/suffix. -/
def terms (left right : OrientedBF4Link → PolyQuaternion) :
    PolyQuaternion → List OrientedBF4Link → List PolyQuaternion
  | _, [] => []
  | p, e::es => ((p ⋄ difference (left e) (right e)) ⋄ wordWith right es) ::
      terms left right (p ⋄ left e) es

theorem terms_length (left right : OrientedBF4Link → PolyQuaternion) :
    ∀ (p : PolyQuaternion) (es : List OrientedBF4Link), (terms left right p es).length = es.length
  | _, [] => rfl
  | p, e::es => congrArg Nat.succ (terms_length left right (p ⋄ left e) es)

/-- Exact telescoping of the scalar component; no commutativity of factors. -/
theorem terms_scalar (left right : OrientedBF4Link → PolyQuaternion) :
    ∀ (p : PolyQuaternion) (es : List OrientedBF4Link),
      RatPolyCoeffEqv (polySum ((terms left right p es).map PolyQuaternion.scalar))
        (difference (p ⋄ wordWith left es) (p ⋄ wordWith right es)).scalar
  | p, [] => ((coeffEvalExpr_eqv_of_normalize_eq
      (.add (.var 0) (.neg (.var 0))) (.const 0) (by decide)
      (fun _ => (p ⋄ PolyQuaternion.one).scalar)).trans (RatPolyCoeffEqv.zero_smul polyOne)).symm
  | p, e::es => by
      have hh := (((mul_difference p (left e) (right e)).mul
        (PolyQuaternionCoeffEqv.refl (wordWith right es))).trans
        (difference_mul (p ⋄ left e) (p ⋄ right e) (wordWith right es))).scalar
      have hc : RatPolyCoeffEqv
          (polyAdd (difference ((p ⋄ left e) ⋄ wordWith right es)
            ((p ⋄ right e) ⋄ wordWith right es)).scalar
            (difference ((p ⋄ left e) ⋄ wordWith left es)
              ((p ⋄ left e) ⋄ wordWith right es)).scalar)
          (difference ((p ⋄ left e) ⋄ wordWith left es)
            ((p ⋄ right e) ⋄ wordWith right es)).scalar :=
        coeffEvalExpr_eqv_of_normalize_eq
          (.add (.add (.var 0) (.neg (.var 1))) (.add (.var 2) (.neg (.var 0))))
          (.add (.var 2) (.neg (.var 1))) (by decide)
          (fun | 0 => ((p ⋄ left e) ⋄ wordWith right es).scalar
               | 1 => ((p ⋄ right e) ⋄ wordWith right es).scalar
               | _ => ((p ⋄ left e) ⋄ wordWith left es).scalar)
      exact (hh.add (terms_scalar left right (p ⋄ left e) es)).trans
        (hc.trans ((PolyQuaternionCoeffEqv.mul_assoc p (left e) (wordWith left es)).scalar.add
          (RatPolyCoeffEqv.neg (PolyQuaternionCoeffEqv.mul_assoc p (right e) (wordWith right es)).scalar)))

theorem word_supported {n : Nat} (value : OrientedBF4Link → PolyQuaternion) :
    ∀ es, (∀ e, e ∈ es → Supported n (value e)) → Supported n (wordWith value es)
  | [], _ => Supported.one n
  | e::es, h => (h e List.mem_cons_self).mul
      (word_supported value es (fun f hf => h f (List.mem_cons_of_mem e hf)))

theorem word_unit {n : Nat} (value : OrientedBF4Link → PolyQuaternion) :
    ∀ es, (∀ e, e ∈ es → HaarCarrierEqv n (polyQuaternionNorm (value e)) polyOne) →
      HaarCarrierEqv n (polyQuaternionNorm (wordWith value es)) polyOne
  | [], _ => RatPolyCoeffEqv.haarCarrier polyQuaternionNorm_one
  | e::es, h => haarNorm_mul (h e List.mem_cons_self)
      (word_unit value es (fun f hf => h f (List.mem_cons_of_mem e hf)))

theorem terms_supported {n : Nat} (left right : OrientedBF4Link → PolyQuaternion) :
    ∀ (p : PolyQuaternion) (es : List OrientedBF4Link), Supported n p →
      (∀ e, e ∈ es → Supported n (left e)) → (∀ e, e ∈ es → Supported n (right e)) →
      ∀ q, q ∈ terms left right p es → Supported n q
  | _, [], _, _, _, _, h => False.elim (List.not_mem_nil h)
  | p, e::es, hp, hl, hr, q, hq => by
      rcases List.mem_cons.mp hq with h | h
      · subst q
        exact (hp.mul (difference_supported (hl e List.mem_cons_self) (hr e List.mem_cons_self))).mul
          (word_supported right es (fun f hf => hr f (List.mem_cons_of_mem e hf)))
      · exact terms_supported left right (p ⋄ left e) es (hp.mul (hl e List.mem_cons_self))
          (fun f hf => hl f (List.mem_cons_of_mem e hf))
          (fun f hf => hr f (List.mem_cons_of_mem e hf)) q h

/-- Unit prefix/suffix cancel only in the norm, under every Haar insertion. -/
theorem unit_sandwich_norm {n : Nat} {p r : PolyQuaternion}
    (hp : HaarCarrierEqv n (polyQuaternionNorm p) polyOne)
    (hr : HaarCarrierEqv n (polyQuaternionNorm r) polyOne) (q : PolyQuaternion) :
    HaarCarrierEqv n (polyQuaternionNorm ((p ⋄ q) ⋄ r)) (polyQuaternionNorm q) :=
  HaarCarrierEqv.trans (RatPolyCoeffEqv.haarCarrier (polyQuaternionNorm_mul _ _))
    (HaarCarrierEqv.trans
      (HaarCarrierEqv.mul
        (HaarCarrierEqv.trans (RatPolyCoeffEqv.haarCarrier (polyQuaternionNorm_mul _ _))
          (HaarCarrierEqv.mul hp (HaarCarrierEqv.refl n _))) hr)
      (RatPolyCoeffEqv.haarCarrier ((RatPolyCoeffEqv.mul_one _).trans (RatPolyCoeffEqv.one_mul _))))

/-- Each telescope norm has exactly its one-link displacement norm, so the
full original insertion W can remain present throughout. -/
theorem terms_norm_bound {n : Nat} (W : RatPoly) (B : Q')
    (left right : OrientedBF4Link → PolyQuaternion) :
    ∀ (p : PolyQuaternion) (es : List OrientedBF4Link),
      HaarCarrierEqv n (polyQuaternionNorm p) polyOne →
      (∀ e, e ∈ es → HaarCarrierEqv n (polyQuaternionNorm (left e)) polyOne) →
      (∀ e, e ∈ es → HaarCarrierEqv n (polyQuaternionNorm (right e)) polyOne) →
      (∀ e, e ∈ es → quaternionHaar n (polyMul W (polyQuaternionNorm (difference (left e) (right e)))) ≤ B) →
      ∀ q, q ∈ terms left right p es → quaternionHaar n (polyMul W (polyQuaternionNorm q)) ≤ B
  | _, [], _, _, _, _, _, h => False.elim (List.not_mem_nil h)
  | p, e::es, hp, hl, hr, hb, q, hq => by
      rcases List.mem_cons.mp hq with h | h
      · subst q
        exact Q'.le_trans' _ _ _ (Q'.le_of_eqv
          (unit_sandwich_norm hp (word_unit right es (fun f hf => hr f (List.mem_cons_of_mem e hf))) _ W))
          (hb e List.mem_cons_self)
      · exact terms_norm_bound W B left right (p ⋄ left e) es
          (haarNorm_mul hp (hl e List.mem_cons_self))
          (fun f hf => hl f (List.mem_cons_of_mem e hf))
          (fun f hf => hr f (List.mem_cons_of_mem e hf))
          (fun f hf => hb f (List.mem_cons_of_mem e hf)) q h

private theorem haar_neg (n : Nat) : ∀ p : RatPoly,
    quaternionHaar n (polyNeg p) ≈ -(quaternionHaar n p)
  | [] => by change (0 : Q') ≈ -0; decide
  | t::ps => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.neg_mul_eqv t.2 _) (haar_neg n ps))
      (Q'.eqv_symm (Q'.neg_add_eqv_split _ _))

theorem weighted_difference (n : Nat) (W p q : RatPoly) :
    quaternionHaar n (polyMul W (polyAdd p (polyNeg q))) ≈
      quaternionHaar n (polyMul W p) + -(quaternionHaar n (polyMul W q)) :=
  Q'.eqv_trans _ _ _ (haar_weighted_add n W p (polyNeg q))
    (Q'.add_eqv_congr_left _ _ _ (Q'.eqv_trans _ _ _
      (haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.var 0) (.neg (.var 1))) (.neg (.mul (.var 0) (.var 1)))
        (by decide) (fun | 0 => W | _ => q))) (haar_neg n _)))

/-- A constructed polynomial order certificate may be multiplied by the
entire original positive weight, including all overlapping variables. -/
theorem weighted_order {n : Nat} {W p q : RatPoly} (R : Certificate n W)
    (C : Certificate n (polyAdd p (polyNeg q))) :
    quaternionHaar n (polyMul W q) ≤ quaternionHaar n (polyMul W p) :=
  Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _ (R.mul C).haar_nonnegative
    (Q'.le_of_eqv (weighted_difference n W p q)))

theorem weighted_scale (n : Nat) (W p : RatPoly) (c : Q') :
    quaternionHaar n (polyMul W (polySmul c p)) ≈ c*quaternionHaar n (polyMul W p) :=
  Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.polyMul_smul_right c W p))
    (quaternionHaar_polySmul _ _ _)

private theorem sum_bound (B : Q') : ∀ xs : List Q',
    (∀ x, x ∈ xs → x ≤ B) → qListSum xs ≤ Q'.ofNat xs.length * B
  | [], _ => Q'.ge_of_eqv (Q'.zero_mul_eqv B)
  | x::xs, h => by
      have hs := Q'.le_trans' _ _ _
        (Q'.add_le_add_right _ _ _ (h x List.mem_cons_self))
        (Q'.add_le_add_left _ _ _ (sum_bound B xs (fun y hy => h y (List.mem_cons_of_mem x hy))))
      have he : Q'.ofNat (xs.length+1)*B ≈ B+Q'.ofNat xs.length*B :=
        Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (Q'.ofNat_add_eqv _ _))
          (Q'.eqv_trans _ _ _ (Q'.add_mul_eqv _ _ _)
            (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ (Q'.one_mul_eqv B))
              (Q'.add_comm_eqv _ _)))
      exact Q'.le_trans' _ _ _ hs (Q'.ge_of_eqv he)

/-- Each summand has budget B under the SAME weight. Finite Cauchy gives
the squared list length, not an exponential bound. -/
theorem finite_square_bound {n : Nat} {W : RatPoly} (R : Certificate n W)
    (ps : List RatPoly) (hs : ∀ p, p ∈ ps → SupportedQuaternionBlocks n p)
    (B : Q') (hb : ∀ p, p ∈ ps → quaternionHaar n (polyMul W (polyMul p p)) ≤ B) :
    quaternionHaar n (polyMul W (polyMul (polySum ps) (polySum ps))) ≤
      (Q'.ofNat ps.length * Q'.ofNat ps.length)*B := by
  have h := weighted_order R (sum_square_certificate ps hs)
  have he := Q'.eqv_trans _ _ _ (weighted_scale n W _ (Q'.ofNat ps.length))
    (Q'.mul_eqv_congr_left _ _ _ (haar_weighted_sum_indexed n W (fun p => polyMul p p) ps))
  have hsum := sum_bound B (ps.map (fun p => quaternionHaar n (polyMul W (polyMul p p))))
    (by intro x hx; obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hx; exact hb p hp)
  rw [List.length_map] at hsum
  exact Q'.le_trans' _ _ _ (Q'.le_trans' _ _ _ h (Q'.le_of_eqv he))
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hsum (Q'.ofNat_nonneg _))
      (Q'.ge_of_eqv (Q'.mul_assoc_eqv _ _ _)))

theorem scalar_square_le_norm {n : Nat} {W : RatPoly} (R : Certificate n W)
    {p : PolyQuaternion} (hp : Supported n p) :
    quaternionHaar n (polyMul W (polyMul p.scalar p.scalar)) ≤
      quaternionHaar n (polyMul W (polyQuaternionNorm p)) := by
  apply weighted_order R
  have hc : Certificate n (polyAdd (polyMul p.iPart p.iPart)
      (polyAdd (polyMul p.jPart p.jPart) (polyMul p.kPart p.kPart))) :=
    (Certificate.square p.iPart hp.iPart).add
      ((Certificate.square p.jPart hp.jPart).add (.square p.kPart hp.kPart))
  exact .ofCoeff (coeffEvalExpr_eqv_of_normalize_eq
    (.add (.add (.var 0) (.var 1)) (.neg (.var 0))) (.var 1) (by decide)
    (fun | 0 => polyMul p.scalar p.scalar
         | _ => polyAdd (polyMul p.iPart p.iPart) (polyAdd (polyMul p.jPart p.jPart) (polyMul p.kPart p.kPart)))) hc

/-- Original ordered word increment controlled by its one-link norm costs.
No independence, disjointness, or change of the supplied positive weight. -/
theorem word_scalar_square_bound {n : Nat} {W : RatPoly} (R : Certificate n W)
    (left right : OrientedBF4Link → PolyQuaternion) (es : List OrientedBF4Link)
    (hl : ∀ e, e ∈ es → Supported n (left e)) (hr : ∀ e, e ∈ es → Supported n (right e))
    (hlu : ∀ e, e ∈ es → HaarCarrierEqv n (polyQuaternionNorm (left e)) polyOne)
    (hru : ∀ e, e ∈ es → HaarCarrierEqv n (polyQuaternionNorm (right e)) polyOne)
    (B : Q') (hb : ∀ e, e ∈ es →
      quaternionHaar n (polyMul W (polyQuaternionNorm (difference (left e) (right e)))) ≤ B) :
    quaternionHaar n (polyMul W
      (polyMul (difference (wordWith left es) (wordWith right es)).scalar
        (difference (wordWith left es) (wordWith right es)).scalar)) ≤
      (Q'.ofNat es.length * Q'.ofNat es.length)*B := by
  let ts := terms left right PolyQuaternion.one es
  have hs := terms_supported left right PolyQuaternion.one es (Supported.one n) hl hr
  have ht := terms_norm_bound W B left right PolyQuaternion.one es
    (RatPolyCoeffEqv.haarCarrier polyQuaternionNorm_one) hlu hru hb
  have h := finite_square_bound R (ts.map PolyQuaternion.scalar)
    (by intro p hp; obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp; exact (hs q hq).scalar) B
    (by intro p hp; obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
        exact Q'.le_trans' _ _ _ (scalar_square_le_norm R (hs q hq)) (ht q hq))
  have he := (terms_scalar left right PolyQuaternion.one es).trans
    ((PolyQuaternionCoeffEqv.one_mul _).scalar.add (RatPolyCoeffEqv.neg (PolyQuaternionCoeffEqv.one_mul _).scalar))
  rw [List.length_map, terms_length] at h
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (haar_of_coeff ((he.mul he).mul_left W))) h

end YMGap.Continuum.QuaternionHaarWordDifference

#print axioms YMGap.Continuum.QuaternionHaarWordDifference.difference
#print axioms YMGap.Continuum.QuaternionHaarWordDifference.difference_supported
#print axioms YMGap.Continuum.QuaternionHaarWordDifference.difference_mul
#print axioms YMGap.Continuum.QuaternionHaarWordDifference.mul_difference
#print axioms YMGap.Continuum.QuaternionHaarWordDifference.terms
#print axioms YMGap.Continuum.QuaternionHaarWordDifference.terms_length
#print axioms YMGap.Continuum.QuaternionHaarWordDifference.terms_scalar
#print axioms YMGap.Continuum.QuaternionHaarWordDifference.word_supported
#print axioms YMGap.Continuum.QuaternionHaarWordDifference.word_unit
#print axioms YMGap.Continuum.QuaternionHaarWordDifference.terms_supported
#print axioms YMGap.Continuum.QuaternionHaarWordDifference.unit_sandwich_norm
#print axioms YMGap.Continuum.QuaternionHaarWordDifference.terms_norm_bound
#print axioms YMGap.Continuum.QuaternionHaarWordDifference.weighted_difference
#print axioms YMGap.Continuum.QuaternionHaarWordDifference.weighted_order
#print axioms YMGap.Continuum.QuaternionHaarWordDifference.weighted_scale
#print axioms YMGap.Continuum.QuaternionHaarWordDifference.finite_square_bound
#print axioms YMGap.Continuum.QuaternionHaarWordDifference.scalar_square_le_norm
#print axioms YMGap.Continuum.QuaternionHaarWordDifference.word_scalar_square_bound
