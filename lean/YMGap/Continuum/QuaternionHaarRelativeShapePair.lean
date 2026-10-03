/-
# Small relative Haar shape under shared-variable insertions

Two supported signed polynomials are centered at their own Haar masses.
Their actual centered squares and a constructed interval for the insertion
bound the single and paired insertion errors, without roots, independence,
or replacement of an interacting measure. The constants are explicit even
when the radius or insertion cap is zero. The original terminal-shape
consumer supplies the shape inequalities; no overlap floor is assumed here.
-/

import YMGap.Continuum.QuaternionHaarIntervalSecondMoment
import YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz
import YMGap.Constructive.CRealExp

namespace YMGap.Continuum.QuaternionHaarRelativeShapePair

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz

local infix:50 " ≈ " => Q'.eqv

private def center (p : RatPoly) (a : Q') : RatPoly :=
  polyAdd p (polyNeg (cap a))

private theorem center_supported {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) (a : Q') :
    SupportedQuaternionBlocks blocks (center p a) := by
  apply supported_add hp
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact (SquareBound.constant blocks a).support s hs

private theorem haar_neg (blocks : Nat) : ∀ p : RatPoly,
    quaternionHaar blocks (polyNeg p) ≈ -quaternionHaar blocks p
  | [] => by change (0 : Q') ≈ -0; decide
  | t::rest => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.neg_mul_eqv t.2 (quaternionHaarMono blocks t.1))
        (haar_neg blocks rest))
      (Q'.eqv_symm (Q'.neg_add_eqv_split _ _))

private theorem haar_one (blocks : Nat) : quaternionHaar blocks polyOne ≈ 1 :=
  Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
    (Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _) (quaternionHaarMono_one blocks))
    (Q'.eqv_refl _)) (Q'.eqv_of_eq (Q'.add_zero' 1))

private theorem haar_cap_mul (blocks : Nat) (a : Q') (p : RatPoly) :
    quaternionHaar blocks (polyMul (cap a) p) ≈ a*quaternionHaar blocks p :=
  Q'.eqv_trans _ _ _ (haar_of_coeff (blocks := blocks) (cap_mul_left a p))
    (quaternionHaar_polySmul blocks a p)

private theorem qmul {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h)
    (Q'.mul_eqv_congr_left _ _ _ k)

private theorem raw_cs {blocks : Nat} {p g : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) (hg : SupportedQuaternionBlocks blocks g) :
    quaternionHaar blocks (polyMul p g)*quaternionHaar blocks (polyMul p g) ≤
      quaternionHaar blocks (polyMul p p)*quaternionHaar blocks (polyMul g g) := by
  have pin (u v : RatPoly) : weightedPair blocks polyOne u v ≈
      quaternionHaar blocks (polyMul u v) :=
    haar_of_coeff (blocks := blocks) (RatPolyCoeffEqv.mul_one _)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (qmul (pin p g) (pin p g)))
    (Q'.le_trans' _ _ _
      (weighted_cauchySchwarz blocks polyOne p g (Certificate.one blocks) hp hg)
      (Q'.le_of_eqv (qmul (pin p p) (pin g g))))

private theorem square_insertion_le {blocks : Nat} {p g : RatPoly} {c : Q'}
    (P : SquareBound blocks p c) (hg : SupportedQuaternionBlocks blocks g) :
    quaternionHaar blocks (polyMul (polyMul p g) (polyMul p g)) ≤
      c*quaternionHaar blocks (polyMul g g) := by
  let B := polyMul g g
  have hpos := ((Certificate.square g hg).mul P.certificate).haar_nonnegative
  have he : quaternionHaar blocks (polyMul B (gap c p)) ≈
      c*quaternionHaar blocks B -
        quaternionHaar blocks (polyMul (polyMul p g) (polyMul p g)) :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (blocks := blocks)
      (coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.mul (.var 1) (.var 1)) (.add (.var 2) (.neg (.mul (.var 0) (.var 0)))))
        (.add (.mul (.var 2) (.mul (.var 1) (.var 1)))
          (.neg (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))))
        (by decide) (fun
          | 0 => p
          | 1 => g
          | _ => cap c)))
      (Q'.eqv_trans _ _ _ (quaternionHaar_append blocks _ _)
        (Q'.add_eqv_congr' (haar_cap_mul blocks c B) (haar_neg blocks _)))
  exact Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _ hpos (Q'.le_of_eqv he))

private theorem square_reflect {a b : Q'} (hb : (0 : Q') ≤ b)
    (h : a*a ≤ b*b) : a ≤ b := by
  show a.num * (b.den : Int) ≤ b.num * (a.den : Int)
  apply Int.not_lt.mp
  intro hba
  have hba' : b < a := hba
  have ha : (0 : Q') < a := Q'.lt_of_le_of_lt hb hba'
  have h1 : b*b ≤ a*b :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ (Q'.le_of_lt hba') hb
  have h2 : a*b < a*a := Q'.mul_lt_mul_of_pos_left ha hba'
  exact (Int.not_lt.mpr h) (Q'.lt_of_le_of_lt h1 h2)

private theorem abs_square (a : Q') : Q'.abs a*Q'.abs a ≈ a*a := by
  unfold Q'.abs
  split
  · exact Q'.eqv_refl _
  · exact poly_identity_of_normal_eq
      (.mul (.neg (.var 0)) (.neg (.var 0))) (.mul (.var 0) (.var 0))
      (by decide) (fun _ => a)

private theorem bounded_pair_abs {blocks : Nat} {p g T : RatPoly} {A B C : Q'}
    (hp : SupportedQuaternionBlocks blocks p) (hg : SupportedQuaternionBlocks blocks g)
    (I : Interval blocks T C) (hA : (0 : Q') ≤ A) (hB : (0 : Q') ≤ B)
    (hpn : quaternionHaar blocks (polyMul p p) ≤ A*A)
    (hgn : quaternionHaar blocks (polyMul g g) ≤ B*B) :
    Q'.abs (quaternionHaar blocks (polyMul T (polyMul p g))) ≤ C*A*B := by
  let x := quaternionHaar blocks (polyMul (polyMul T p) g)
  have hg0 := (Certificate.square g hg).haar_nonnegative
  have hTpn : quaternionHaar blocks (polyMul (polyMul T p) (polyMul T p)) ≤
      (C*C)*(A*A) :=
    Q'.le_trans' _ _ _
      (square_insertion_le
        (QuaternionHaarIntervalSecondMoment.Interval.squareBound I) hp)
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hpn
        (Q'.mul_nonneg _ _ I.nonnegative I.nonnegative))
  have hs : x*x ≤ ((C*C)*(A*A))*(B*B) :=
    Q'.le_trans' _ _ _ (raw_cs (supported_polyMul I.support hp) hg)
      (Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right _ _ _ hTpn hg0)
        (Q'.mul_le_mul_of_nonneg_left _ _ _ hgn
          (Q'.mul_nonneg _ _ (SumOfSquares.q_mul_self_nonneg C)
            (SumOfSquares.q_mul_self_nonneg A))))
  have hr : ((C*C)*(A*A))*(B*B) ≈ (C*A*B)*(C*A*B) :=
    poly_identity_of_normal_eq
      (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1)))
        (.mul (.var 2) (.var 2)))
      (.mul (.mul (.mul (.var 0) (.var 1)) (.var 2))
        (.mul (.mul (.var 0) (.var 1)) (.var 2)))
      (by decide) (fun
        | 0 => C
        | 1 => A
        | _ => B)
  have hb : Q'.abs x ≤ C*A*B := square_reflect
    (Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ I.nonnegative hA) hB)
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (abs_square x))
      (Q'.le_trans' _ _ _ hs (Q'.le_of_eqv hr)))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (ExpNeg.abs_eqv_congr
      (haar_of_coeff (blocks := blocks) (RatPolyCoeffEqv.mul_assoc T p g).symm))) hb

private theorem center_square_ceiling {blocks : Nat} {p : RatPoly} {r : Q'}
    (h : quaternionHaar blocks (polyMul (center p (quaternionHaar blocks p))
      (center p (quaternionHaar blocks p))) ≤
        (r*r)*(quaternionHaar blocks p*quaternionHaar blocks p)) :
    quaternionHaar blocks (polyMul (center p (quaternionHaar blocks p))
      (center p (quaternionHaar blocks p))) ≤
        (r*quaternionHaar blocks p)*(r*quaternionHaar blocks p) :=
  Q'.le_trans' _ _ _ h (Q'.le_of_eqv
    (poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1)))
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))
      (by decide) (fun
        | 0 => r
        | _ => quaternionHaar blocks p)))

private theorem single_center_pin (blocks : Nat) (T p : RatPoly) (a : Q') :
    quaternionHaar blocks (polyMul T p)-a*quaternionHaar blocks T ≈
      quaternionHaar blocks (polyMul T (center p a)) := by
  have h : RatPolyCoeffEqv (polyMul T (center p a))
      (polyAdd (polyMul T p) (polyNeg (polyMul (cap a) T))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.add (.var 1) (.neg (.var 2))))
      (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 2) (.var 0))))
      (by decide) (fun
        | 0 => T
        | 1 => p
        | _ => cap a)
  exact Q'.eqv_symm (Q'.eqv_trans _ _ _ (haar_of_coeff (blocks := blocks) h)
    (Q'.eqv_trans _ _ _ (quaternionHaar_append blocks _ _)
      (Q'.add_eqv_congr' (Q'.eqv_refl _)
        (Q'.eqv_trans _ _ _ (haar_neg blocks _)
          (Q'.neg_eqv_congr _ _ (haar_cap_mul blocks a T))))))

/-- Single literal insertion error from the SAME positive Haar mass and
the actual centered square. All insertion/source coordinates may be shared. -/
theorem single_shape_insertion_bound {blocks : Nat} {p T : RatPoly} {r C : Q'}
    (hp : SupportedQuaternionBlocks blocks p) (I : Interval blocks T C)
    (ha : (0 : Q') < quaternionHaar blocks p) (hr : (0 : Q') ≤ r)
    (hshape : quaternionHaar blocks
      (polyMul (polyAdd p (polyNeg (cap (quaternionHaar blocks p))))
        (polyAdd p (polyNeg (cap (quaternionHaar blocks p))))) ≤
          (r*r)*(quaternionHaar blocks p*quaternionHaar blocks p)) :
    Q'.abs (quaternionHaar blocks (polyMul T p)-
      quaternionHaar blocks p*quaternionHaar blocks T) ≤
        C*r*quaternionHaar blocks p := by
  have h1 : quaternionHaar blocks (polyMul polyOne polyOne) ≤ (1 : Q')*1 :=
    Q'.le_of_eqv (Q'.eqv_trans _ _ _
      (haar_of_coeff (blocks := blocks) (RatPolyCoeffEqv.one_mul polyOne))
      (Q'.eqv_trans _ _ _ (haar_one blocks) (Q'.eqv_symm (Q'.one_mul_eqv 1))))
  have hb := bounded_pair_abs (center_supported hp (quaternionHaar blocks p))
    (supported_one blocks) I (Q'.mul_nonneg _ _ hr (Q'.le_of_lt ha)) Q'.zero_le_one
    (center_square_ceiling hshape) h1
  have he : quaternionHaar blocks (polyMul T (polyMul (center p (quaternionHaar blocks p)) polyOne)) ≈
      quaternionHaar blocks (polyMul T (center p (quaternionHaar blocks p))) :=
    haar_of_coeff (blocks := blocks)
      ((RatPolyCoeffEqv.refl T).mul (RatPolyCoeffEqv.mul_one _))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (ExpNeg.abs_eqv_congr (Q'.eqv_trans _ _ _
      (single_center_pin blocks T p _) (Q'.eqv_symm he))))
    (Q'.le_trans' _ _ _ hb (Q'.le_of_eqv (Q'.eqv_trans _ _ _
      (Q'.mul_one_eqv _) (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)))))

private theorem pair_center_pin (blocks : Nat) (T p g : RatPoly) (a b : Q') :
    quaternionHaar blocks (polyMul T (polyMul p g))-(a*b)*quaternionHaar blocks T ≈
      b*quaternionHaar blocks (polyMul T (center p a)) +
        (a*quaternionHaar blocks (polyMul T (center g b)) +
          quaternionHaar blocks (polyMul T (polyMul (center p a) (center g b)))) := by
  let L := polyAdd (polyMul T (polyMul p g))
    (polyNeg (polyMul (cap a) (polyMul (cap b) T)))
  let R := polyAdd (polyMul (cap b) (polyMul T (center p a)))
    (polyAdd (polyMul (cap a) (polyMul T (center g b)))
      (polyMul T (polyMul (center p a) (center g b))))
  have hc : RatPolyCoeffEqv L R := coeffEvalExpr_eqv_of_normalize_eq
    (.add (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.neg (.mul (.var 3) (.mul (.var 4) (.var 0)))))
    (.add (.mul (.var 4) (.mul (.var 0) (.add (.var 1) (.neg (.var 3)))))
      (.add (.mul (.var 3) (.mul (.var 0) (.add (.var 2) (.neg (.var 4)))))
        (.mul (.var 0) (.mul (.add (.var 1) (.neg (.var 3)))
          (.add (.var 2) (.neg (.var 4)))))))
    (by decide) (fun
      | 0 => T
      | 1 => p
      | 2 => g
      | 3 => cap a
      | _ => cap b)
  have hl : quaternionHaar blocks L ≈
      quaternionHaar blocks (polyMul T (polyMul p g))-(a*b)*quaternionHaar blocks T :=
    Q'.eqv_trans _ _ _ (quaternionHaar_append blocks _ _)
      (Q'.add_eqv_congr' (Q'.eqv_refl _)
        (Q'.eqv_trans _ _ _ (haar_neg blocks _)
          (Q'.neg_eqv_congr _ _ (Q'.eqv_trans _ _ _
            (haar_cap_mul blocks a _)
            (Q'.eqv_trans _ _ _
              (Q'.mul_eqv_congr_left a _ _ (haar_cap_mul blocks b T))
              (Q'.eqv_symm (Q'.mul_assoc_eqv a b _)))))))
  have hh : quaternionHaar blocks R ≈
      b*quaternionHaar blocks (polyMul T (center p a)) +
        (a*quaternionHaar blocks (polyMul T (center g b)) +
          quaternionHaar blocks (polyMul T (polyMul (center p a) (center g b)))) :=
    Q'.eqv_trans _ _ _ (quaternionHaar_append blocks _ _)
      (Q'.add_eqv_congr' (haar_cap_mul blocks b _)
        (Q'.eqv_trans _ _ _ (quaternionHaar_append blocks _ _)
          (Q'.add_eqv_congr' (haar_cap_mul blocks a _) (Q'.eqv_refl _))))
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hl)
    (Q'.eqv_trans _ _ _ (haar_of_coeff (blocks := blocks) hc) hh)

private theorem scale_abs_le {x c B : Q'} (hc : (0 : Q') ≤ c)
    (h : Q'.abs x ≤ B) : Q'.abs (c*x) ≤ c*B := by
  have hmul := ExpNeg.abs_mul_le c x
  rw [ExpNeg.abs_of_nonneg hc] at hmul
  exact Q'.le_trans' _ _ _ hmul (Q'.mul_le_mul_of_nonneg_left _ _ _ h hc)

/-- Paired insertion error at the two actual Haar masses. The exact
coefficient is `C*(2*r+r*r)`, not an independence/factorization assertion. -/
theorem pair_shape_insertion_bound {blocks : Nat} {p g T : RatPoly} {r C : Q'}
    (hp : SupportedQuaternionBlocks blocks p) (hg : SupportedQuaternionBlocks blocks g)
    (I : Interval blocks T C) (ha : (0 : Q') < quaternionHaar blocks p)
    (hb : (0 : Q') < quaternionHaar blocks g) (hr : (0 : Q') ≤ r)
    (hps : quaternionHaar blocks
      (polyMul (polyAdd p (polyNeg (cap (quaternionHaar blocks p))))
        (polyAdd p (polyNeg (cap (quaternionHaar blocks p))))) ≤
          (r*r)*(quaternionHaar blocks p*quaternionHaar blocks p))
    (hgs : quaternionHaar blocks
      (polyMul (polyAdd g (polyNeg (cap (quaternionHaar blocks g))))
        (polyAdd g (polyNeg (cap (quaternionHaar blocks g))))) ≤
          (r*r)*(quaternionHaar blocks g*quaternionHaar blocks g)) :
    Q'.abs (quaternionHaar blocks (polyMul T (polyMul p g))-
      (quaternionHaar blocks p*quaternionHaar blocks g)*quaternionHaar blocks T) ≤
        C*(2*r+r*r)*(quaternionHaar blocks p*quaternionHaar blocks g) := by
  let a := quaternionHaar blocks p
  let b := quaternionHaar blocks g
  let d := center p a
  let e := center g b
  have hdp : Q'.abs (quaternionHaar blocks (polyMul T d)) ≤ C*r*a :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv (ExpNeg.abs_eqv_congr
      (single_center_pin blocks T p a))) (single_shape_insertion_bound hp I ha hr hps)
  have hge : Q'.abs (quaternionHaar blocks (polyMul T e)) ≤ C*r*b :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv (ExpNeg.abs_eqv_congr
      (single_center_pin blocks T g b))) (single_shape_insertion_bound hg I hb hr hgs)
  have hcross := bounded_pair_abs (center_supported hp a) (center_supported hg b) I
    (Q'.mul_nonneg _ _ hr (Q'.le_of_lt ha))
    (Q'.mul_nonneg _ _ hr (Q'.le_of_lt hb))
    (center_square_ceiling hps) (center_square_ceiling hgs)
  have hsum : Q'.abs
      (b*quaternionHaar blocks (polyMul T d) +
        (a*quaternionHaar blocks (polyMul T e) +
          quaternionHaar blocks (polyMul T (polyMul d e)))) ≤
      b*(C*r*a)+(a*(C*r*b)+(C*(r*a))*(r*b)) :=
    Q'.le_trans' _ _ _ (ExpNeg.abs_add_le _ _)
      (Q'.add_le_add (scale_abs_le (Q'.le_of_lt hb) hdp)
        (Q'.le_trans' _ _ _ (ExpNeg.abs_add_le _ _)
          (Q'.add_le_add (scale_abs_le (Q'.le_of_lt ha) hge) hcross)))
  have he : b*(C*r*a)+(a*(C*r*b)+(C*(r*a))*(r*b)) ≈
      C*(2*r+r*r)*(a*b) :=
    poly_identity_of_normal_eq
      (.add (.mul (.var 1) (.mul (.mul (.var 2) (.var 3)) (.var 0)))
        (.add (.mul (.var 0) (.mul (.mul (.var 2) (.var 3)) (.var 1)))
          (.mul (.mul (.var 2) (.mul (.var 3) (.var 0))) (.mul (.var 3) (.var 1)))))
      (.mul (.mul (.var 2) (.add (.mul (.const 2) (.var 3))
        (.mul (.var 3) (.var 3)))) (.mul (.var 0) (.var 1)))
      (by decide) (fun
        | 0 => a
        | 1 => b
        | 2 => C
        | _ => r)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (ExpNeg.abs_eqv_congr (pair_center_pin blocks T p g a b)))
    (Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv he))

#print axioms single_shape_insertion_bound
#print axioms pair_shape_insertion_bound

end YMGap.Continuum.QuaternionHaarRelativeShapePair
