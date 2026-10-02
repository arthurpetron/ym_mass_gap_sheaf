/-
# One ORIGINAL cutoff modulus for a bounded two-face coefficient square

Three actual original margins, at (1,0), (1,1), and (0,1), polarize the
entire two-face plane. Their constructed fixed-depth cutoff moduli give one
cutoff valid for EVERY rational |x|,|y|<=B. The mixed anchor keeps both ordered
cross entries, the complete temporal jump, and both original endpoint means.

The explicit tolerance is epsilon/(1+5*B^2). No positivity of a margin is
assumed in constructing its modulus. A supplied finite positive margin past
this cutoff feeds the EXISTING original completed-carrier ratio theorem.
It does not assert acceptance by the old per-direction finite checker.

Nome, width, faces, depth, and reference coefficient remain fixed. This is
not a useful positive Yang--Mills instance, a changing-family estimate, a
physical mass bound, an EVERY-state gap, or continuum survival.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialTwoFaceMarginSearch
import YMGap.Constructive.CRealAbs

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialTwoFaceMarginCutoff

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser (PolyExpr poly_identity_of_normal_eq)
open YMGap.Continuum.ClusterCount4DProgress (Z4Plaq)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier (polyOne)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBaseInclusion (spatialFaces_mono)
open YMGap.Continuum.BF4WilsonPlaquetteFamilySourcePin (familyExpression family_within)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow (WindowExpression Within)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCollectedFamilyMargin
  (pairing mass_positive finite_margin_pin)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyMarginPencil
  (pencilEntry pencil_pin)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTwoFaceMarginSearch
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4WilsonAllNomeFiniteReferenceMargin
  (referenceMargin referenceMarginCauchy)
open YMGap.Continuum.BF4WilsonAllNomeTemporalEnergyLimit (finiteEnergy)
open YMGap.Continuum.BF4WilsonAllNomeMarginalVarianceLimit (finiteVariance)
open YMGap.Continuum.BF4WilsonAllNomeTerminalReferenceEnergyRatio
  (referenceCoefficient completed_reference_ratio)
open YMGap.Continuum.BF4WilsonAllNomeZeroRadiusIncrement (state)
open YMGap.Continuum.BF4WilsonAllNomeCenteredVector (centeredVector)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner (completedInner)
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime (completedTime)

local infix:50 " ≈ " => Q'.eqv

/-- Signed polarization weights, not three separately centered observables. -/
def weighted (x y a b d : Q') : Q' :=
  (x*x-x*y)*a+(x*y)*b+(y*y-x*y)*d

private theorem binary_polarization (a b d x y : Q') :
    Binary.value a b d x y ≈ weighted x y
      (Binary.value a b d 1 0) (Binary.value a b d 1 1) (Binary.value a b d 0 1) := by
  let V (u v : PolyExpr) : PolyExpr :=
    .add (.add (.mul (.var 0) (.mul u u))
      (.mul (.const 2) (.mul (.var 1) (.mul u v)))) (.mul (.var 2) (.mul v v))
  exact poly_identity_of_normal_eq (V (.var 3) (.var 4))
    (.add (.add
      (.mul (.add (.mul (.var 3) (.var 3)) (.neg (.mul (.var 3) (.var 4))))
        (V (.const 1) (.const 0)))
      (.mul (.mul (.var 3) (.var 4)) (V (.const 1) (.const 1))))
      (.mul (.add (.mul (.var 4) (.var 4)) (.neg (.mul (.var 3) (.var 4))))
        (V (.const 0) (.const 1))))
    (by decide) (fun | 0 => a | 1 => b | 2 => d | 3 => x | _ => y)

private theorem weighted_scale (z x y a b d : Q') :
    z*weighted x y a b d ≈ weighted x y (z*a) (z*b) (z*d) := by
  let W (a b d : PolyExpr) : PolyExpr :=
    .add (.add
      (.mul (.add (.mul (.var 1) (.var 1)) (.neg (.mul (.var 1) (.var 2)))) a)
      (.mul (.mul (.var 1) (.var 2)) b))
      (.mul (.add (.mul (.var 2) (.var 2)) (.neg (.mul (.var 1) (.var 2)))) d)
  exact poly_identity_of_normal_eq
    (.mul (.var 0) (W (.var 3) (.var 4) (.var 5)))
    (W (.mul (.var 0) (.var 3)) (.mul (.var 0) (.var 4)) (.mul (.var 0) (.var 5)))
    (by decide) (fun | 0 => z | 1 => x | 2 => y | 3 => a | 4 => b | _ => d)

private theorem weighted_congr (x y : Q') {a b d a' b' d' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') (hd : d ≈ d') :
    weighted x y a b d ≈ weighted x y a' b' d' :=
  Q'.add_eqv_congr' (Q'.add_eqv_congr'
    (Q'.mul_eqv_congr_left _ _ _ ha) (Q'.mul_eqv_congr_left _ _ _ hb))
    (Q'.mul_eqv_congr_left _ _ _ hd)

section Original

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  {base width : Nat} (hwidth : base < width) (p q : Z4Plaq)
  (hfaces : ∀ r, r ∈ [p,q] → r ∈ spatialFaces base)

/-- Actual original family expression; the density uses the SAME list [p,q]. -/
def expression (x y : Q') : WindowExpression width :=
  familyExpression width [p,q] (profile p q x y)
    (fun r hr => spatialFaces_mono (Nat.le_of_lt hwidth) (hfaces r hr))

theorem expression_within (x y : Q') : Within 0 (expression hwidth p q hfaces x y) :=
  family_within width [p,q] (profile p q x y)
    (fun r hr => spatialFaces_mono (Nat.le_of_lt hwidth) (hfaces r hr))

/-- The EXISTING reference margin, not a replacement quadratic surrogate. -/
def margin (c : Q') (k depth : Nat) (x y : Q') : Q' :=
  referenceMargin hw0 hw1 (expression hwidth p q hfaces x y) c k depth

attribute [local irreducible] pairing referenceMargin

private theorem cleared_margin (hpq : p ≠ q) (c : Q') (k depth : Nat) (x y : Q') :
    let K := headCutoff w+k
    let Z := pairing w K width depth [p,q] polyOne
    Z*Z*margin hw0 hw1 hwidth p q hfaces c k depth x y ≈
      Binary.value (pencilEntry w K width depth [p,q] c p p)
        (crossEntry w K width depth p q c)
        (pencilEntry w K width depth [p,q] c q q) x y := by
  dsimp only
  have hm := finite_margin_pin hw0 hw1 hwidth [p,q] (profile p q x y) hfaces k depth c
  have hb := pencil_two_faces w (headCutoff w+k) width depth p q (profile p q x y) c
  rw [profile_at_first, profile_at_second hpq] at hb
  exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hm))
    (Q'.eqv_trans _ _ _
      (pencil_pin hw0 hw1 (headCutoff w+k) width (Nat.le_add_right _ _) depth
        [p,q] (profile p q x y) c) hb)

include hw0 hw1 hwidth hfaces in
/-- Exact normalized polarization, preserving BOTH ordered mixed entries. -/
theorem polarization (hpq : p ≠ q) (c : Q') (k depth : Nat) (x y : Q') :
    margin hw0 hw1 hwidth p q hfaces c k depth x y ≈
      weighted x y (margin hw0 hw1 hwidth p q hfaces c k depth 1 0)
        (margin hw0 hw1 hwidth p q hfaces c k depth 1 1)
        (margin hw0 hw1 hwidth p q hfaces c k depth 0 1) := by
  let Z := pairing w (headCutoff w+k) width depth [p,q] polyOne
  have hZ := mass_positive hw0 hw1 (headCutoff w+k) width
    (Nat.le_add_right _ _) depth [p,q]
  have hZZ : (0 : Q') < Z*Z := Q'.mul_pos hZ hZ
  have hscaled := Q'.eqv_trans _ _ _
    (weighted_scale (Z*Z) x y
      (margin hw0 hw1 hwidth p q hfaces c k depth 1 0)
      (margin hw0 hw1 hwidth p q hfaces c k depth 1 1)
      (margin hw0 hw1 hwidth p q hfaces c k depth 0 1))
    (weighted_congr x y
      (cleared_margin hw0 hw1 hwidth p q hfaces hpq c k depth 1 0)
      (cleared_margin hw0 hw1 hwidth p q hfaces hpq c k depth 1 1)
      (cleared_margin hw0 hw1 hwidth p q hfaces hpq c k depth 0 1))
  have hid := Q'.eqv_trans _ _ _
    (cleared_margin hw0 hw1 hwidth p q hfaces hpq c k depth x y)
    (Q'.eqv_trans _ _ _ (binary_polarization _ _ _ x y) (Q'.eqv_symm hscaled))
  exact ExpNeg.eqv_of_le_le
    (Q'.le_of_mul_le_mul_left (Q'.le_of_eqv hid) hZZ)
    (Q'.le_of_mul_le_mul_left (Q'.ge_of_eqv hid) hZZ)

end Original

/-- Sum of explicit absolute polarization-weight bounds on [-B,B]^2. -/
def weightCap (B : Q') : Q' := 5*(B*B)

private theorem weightCap_nonnegative (B : Q') : (0 : Q') ≤ weightCap B :=
  Q'.mul_nonneg _ _ (by decide) (SumOfSquares.q_mul_self_nonneg B)

private theorem denominator_positive (B : Q') : (0 : Q') < 1+weightCap B :=
  Q'.pos_of_lt_of_le (by decide : (0 : Q') < 1)
    (Q'.add_le_self_of_nonneg _ _ (weightCap_nonnegative B))

/-- Defined even at B=0, without dividing by a variance or coefficient. -/
def anchorTolerance (B epsilon : Q') : Q' :=
  Q'.divPos epsilon (1+weightCap B) (denominator_positive B)

theorem anchorTolerance_positive (B : Q') {epsilon : Q'} (hp : (0 : Q') < epsilon) :
    (0 : Q') < anchorTolerance B epsilon := Q'.divPos_pos _ _ _ hp

private theorem product_abs_bound {B x y : Q'} (hB : (0 : Q') ≤ B)
    (hx : Q'.abs x ≤ B) (hy : Q'.abs y ≤ B) : Q'.abs (x*y) ≤ B*B :=
  Q'.le_trans' _ _ _ (ExpNeg.abs_mul_le x y)
    (Q'.mul_le_mul_of_nonneg hx hy hB (Q'.abs_nonneg y))

private theorem difference_abs_bound {B a b : Q'}
    (ha : Q'.abs a ≤ B*B) (hb : Q'.abs b ≤ B*B) : Q'.abs (a-b) ≤ B*B+B*B :=
  Q'.le_trans' _ _ _ (ExpNeg.abs_add_le a (-b))
    (Q'.add_le_add ha (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_neg' b)) hb))

private theorem weighted_close (B epsilon : Q') (hp : (0 : Q') < epsilon)
    {x y : Q'} (hB : (0 : Q') ≤ B) (hx : Q'.abs x ≤ B) (hy : Q'.abs y ≤ B)
    {a b d a' b' d' : Q'}
    (ha : a ≤ a'+anchorTolerance B epsilon ∧ a' ≤ a+anchorTolerance B epsilon)
    (hb : b ≤ b'+anchorTolerance B epsilon ∧ b' ≤ b+anchorTolerance B epsilon)
    (hd : d ≤ d'+anchorTolerance B epsilon ∧ d' ≤ d+anchorTolerance B epsilon) :
    weighted x y a b d ≤ weighted x y a' b' d'+epsilon := by
  let delta := anchorTolerance B epsilon
  let U := B*B+B*B
  have hd0 : (0 : Q') ≤ delta := Q'.le_of_lt (anchorTolerance_positive B hp)
  have hbb : (0 : Q') ≤ B*B := SumOfSquares.q_mul_self_nonneg B
  have hU : (0 : Q') ≤ U := Q'.zero_le_add _ _ hbb hbb
  have hxy := product_abs_bound hB hx hy
  have hxx := difference_abs_bound (product_abs_bound hB hx hx) hxy
  have hyy := difference_abs_bound (product_abs_bound hB hy hy) hxy
  have low {u C : Q'} (h : Q'.abs u ≤ C) : -C ≤ u :=
    Q'.le_trans' _ _ _ (Q'.neg_le_neg h) (ExpNeg.neg_abs_le u)
  have h1 := Q'.mul_close_of_two_sided (x*x-x*y) a a' U delta hU hd0
    (low hxx) (Q'.le_trans' _ _ _ (Q'.le_abs_self _) hxx) ha.1 ha.2
  have h2 := Q'.mul_close_of_two_sided (x*y) b b' (B*B) delta hbb hd0
    (low hxy) (Q'.le_trans' _ _ _ (Q'.le_abs_self _) hxy) hb.1 hb.2
  have h3 := Q'.mul_close_of_two_sided (y*y-x*y) d d' U delta hU hd0
    (low hyy) (Q'.le_trans' _ _ _ (Q'.le_abs_self _) hyy) hd.1 hd.2
  have hsum := Q'.add_le_add (Q'.add_le_add h1 h2) h3
  have heq : ((x*x-x*y)*a'+U*delta)+((x*y)*b'+(B*B)*delta)+
      ((y*y-x*y)*d'+U*delta) ≈ weighted x y a' b' d'+weightCap B*delta :=
    poly_identity_of_normal_eq
      (.add (.add (.add (.var 0) (.mul (.add (.var 3) (.var 3)) (.var 4)))
        (.add (.var 1) (.mul (.var 3) (.var 4))))
        (.add (.var 2) (.mul (.add (.var 3) (.var 3)) (.var 4))))
      (.add (.add (.add (.var 0) (.var 1)) (.var 2))
        (.mul (.mul (.const 5) (.var 3)) (.var 4)))
      (by decide) (fun
        | 0 => (x*x-x*y)*a'
        | 1 => (x*y)*b'
        | 2 => (y*y-x*y)*d'
        | 3 => B*B
        | _ => delta)
  have budget : weightCap B*delta ≤ epsilon := by
    have hid : weightCap B*delta+delta ≈ epsilon :=
      Q'.eqv_trans _ _ _
        (poly_identity_of_normal_eq
          (.add (.mul (.var 0) (.var 1)) (.var 1))
          (.mul (.var 1) (.add (.const 1) (.var 0)))
          (by decide) (fun | 0 => weightCap B | _ => delta))
        (Q'.divPos_mul_eqv _ _ _)
    exact Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ _ hd0) (Q'.le_of_eqv hid)
  exact Q'.le_trans' _ _ _ hsum (Q'.le_trans' _ _ _ (Q'.le_of_eqv heq)
    (Q'.add_le_add_left _ _ _ budget))

section Uniform

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  {base width : Nat} (hwidth : base < width) (p q : Z4Plaq)
  (hfaces : ∀ r, r ∈ [p,q] → r ∈ spatialFaces base)

local notation "M10" => referenceMarginCauchy hw0 hw1
  (expression hwidth p q hfaces 1 0) (expression_within hwidth p q hfaces 1 0)
local notation "M11" => referenceMarginCauchy hw0 hw1
  (expression hwidth p q hfaces 1 1) (expression_within hwidth p q hfaces 1 1)
local notation "M01" => referenceMarginCauchy hw0 hw1
  (expression hwidth p q hfaces 0 1) (expression_within hwidth p q hfaces 0 1)

/-- ONE Type-level cutoff, independent of the chosen direction (x,y). -/
def cutoff (c : Q') (depth : Nat) (B epsilon : Q') : Nat :=
  let delta := anchorTolerance B epsilon
  max ((M10 c depth).M delta)
    (max ((M11 c depth).M delta) ((M01 c depth).M delta))

include hw0 hw1 hwidth hfaces in
/-- Every bounded signed direction shares the constructed original cutoff.
Only direction uniformity is asserted; all physical parameters remain named. -/
theorem uniform_bound (hpq : p ≠ q) (c : Q') (depth : Nat) (B epsilon : Q')
    (hp : (0 : Q') < epsilon) (hB : (0 : Q') ≤ B) (x y : Q')
    (hx : Q'.abs x ≤ B) (hy : Q'.abs y ≤ B) (i j : Nat)
    (hi : cutoff hw0 hw1 hwidth p q hfaces c depth B epsilon ≤ i)
    (hj : cutoff hw0 hw1 hwidth p q hfaces c depth B epsilon ≤ j) :
    margin hw0 hw1 hwidth p q hfaces c i depth x y ≤
      margin hw0 hw1 hwidth p q hfaces c j depth x y+epsilon ∧
    margin hw0 hw1 hwidth p q hfaces c j depth x y ≤
      margin hw0 hw1 hwidth p q hfaces c i depth x y+epsilon := by
  let delta := anchorTolerance B epsilon
  have hdelta := anchorTolerance_positive B hp
  have h10 := (M10 c depth).bound delta hdelta i j
    (Nat.le_trans (Nat.le_max_left _ _) hi) (Nat.le_trans (Nat.le_max_left _ _) hj)
  have h11 := (M11 c depth).bound delta hdelta i j
    (Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hi)
    (Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hj)
  have h01 := (M01 c depth).bound delta hdelta i j
    (Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hi)
    (Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hj)
  have forward := weighted_close B epsilon hp hB hx hy h10 h11 h01
  have backward := weighted_close B epsilon hp hB hx hy h10.symm h11.symm h01.symm
  have pi := polarization hw0 hw1 hwidth p q hfaces hpq c i depth x y
  have pj := polarization hw0 hw1 hwidth p q hfaces hpq c j depth x y
  exact ⟨Q'.le_trans' _ _ _ (Q'.le_of_eqv pi)
    (Q'.le_trans' _ _ _ forward (Q'.ge_of_eqv (Q'.add_eqv_congr_right _ _ epsilon pj))),
    Q'.le_trans' _ _ _ (Q'.le_of_eqv pj)
      (Q'.le_trans' _ _ _ backward (Q'.ge_of_eqv (Q'.add_eqv_congr_right _ _ epsilon pi)))⟩

private theorem cancel_right {a b d : Q'} (h : a+d ≤ b+d) : a ≤ b := by
  have h' := Q'.add_le_add_right _ _ (-d) h
  have hc (z : Q') : (z+d)+(-d) ≈ z :=
    Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv _ _ _)
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ (Q'.add_neg_self_eqv _))
        (Q'.eqv_of_eq (Q'.add_zero' _)))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (hc a))
    (Q'.le_trans' _ _ _ h' (Q'.le_of_eqv (hc b)))

/-- A SUPPLIED useful pivot margin survives the common cutoff allowance. -/
theorem margin_floor (hpq : p ≠ q) (c : Q') (depth : Nat) (B epsilon : Q')
    (hp : (0 : Q') < epsilon) (hB : (0 : Q') ≤ B) (x y : Q')
    (hx : Q'.abs x ≤ B) (hy : Q'.abs y ≤ B) (pivot : Nat)
    (hpivot : cutoff hw0 hw1 hwidth p q hfaces c depth B epsilon ≤ pivot)
    (hmargin : epsilon+epsilon ≤ margin hw0 hw1 hwidth p q hfaces c pivot depth x y)
    (k : Nat) (hk : cutoff hw0 hw1 hwidth p q hfaces c depth B epsilon ≤ k) :
    epsilon ≤ margin hw0 hw1 hwidth p q hfaces c k depth x y := by
  have hb := uniform_bound hw0 hw1 hwidth p q hfaces hpq c depth B epsilon hp hB
    x y hx hy pivot k hpivot hk
  exact cancel_right (Q'.le_trans' _ _ _ hmargin hb.1)

/-- Direct use of the EXISTING completed consumer, with its original loss.
No claim about the old checker's DIFFERENT per-direction cutoff is made. -/
theorem completed_ratio (hpq : p ≠ q) (s : Nat) (c B epsilon : Q')
    (hc : (0 : Q') ≤ c) (hp : (0 : Q') < epsilon) (hB : (0 : Q') ≤ B)
    (x y : Q') (hx : Q'.abs x ≤ B) (hy : Q'.abs y ≤ B) (pivot : Nat)
    (hpivot : cutoff hw0 hw1 hwidth p q hfaces c (s+1) B epsilon ≤ pivot)
    (hmargin : epsilon+epsilon ≤ margin hw0 hw1 hwidth p q hfaces c pivot (s+1) x y) :
    let e := expression hwidth p q hfaces x y
    let he := expression_within hwidth p q hfaces x y
    RCle
      (RCsub
        (completedInner hw0 hw1 (centeredVector hw0 hw1 (state e he))
          (centeredVector hw0 hw1 (state e he)))
        (completedInner hw0 hw1 (centeredVector hw0 hw1 (state e he))
          (completedTime hw0 hw1 1 (centeredVector hw0 hw1 (state e he)))))
      (RCscale (referenceCoefficient hw0 hw1 width s c)
        (completedInner hw0 hw1 (centeredVector hw0 hw1 (state e he))
          (centeredVector hw0 hw1 (state e he)))) := by
  dsimp only
  apply completed_reference_ratio hw0 hw1
    (expression hwidth p q hfaces x y) (expression_within hwidth p q hfaces x y)
    s (cutoff hw0 hw1 hwidth p q hfaces c (s+1) B epsilon) hc
  intro k hk
  have hf := margin_floor hw0 hw1 hwidth p q hfaces hpq c (s+1) B epsilon hp hB
    x y hx hy pivot hpivot hmargin k hk
  have hn := Q'.le_trans' _ _ _ (Q'.le_of_lt hp) hf
  have h := Q'.add_le_add_right _ _
    (finiteEnergy hw0 hw1 (expression hwidth p q hfaces x y) k (s+1)) hn
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.eqv_of_eq (Q'.zero_add' _)))
    (Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.sub_add_cancel_eqv _ _)))

end Uniform

#print axioms weighted
#print axioms expression
#print axioms expression_within
#print axioms margin
#print axioms polarization
#print axioms weightCap
#print axioms anchorTolerance
#print axioms anchorTolerance_positive
#print axioms cutoff
#print axioms uniform_bound
#print axioms margin_floor
#print axioms completed_ratio

end YMGap.Continuum.BF4ExactSlabFixedSpatialTwoFaceMarginCutoff
