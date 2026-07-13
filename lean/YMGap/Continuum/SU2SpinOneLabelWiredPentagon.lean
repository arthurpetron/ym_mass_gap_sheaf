/-
# The exact spin-one F-block and a first label-wired pentagon

For four equal external SU(2) labels the square roots in the signed Racah
formula occur in equal pairs.  The signed 6j symbol is therefore rational:

  {j j e; j j f} = triSq(j,j,e) * triSq(j,j,f) * racahSum(j,j,e,j,j,f).

Multiplication by `dim(f)` gives the dimension-rescaled F-entry.  This file
defines that equal-external family directly from the finite factorial Racah
sum.  Its first non-fundamental member has four spin-one external labels and
channels `0,2,4`; exact evaluation gives the 3-by-3 matrix

  [  1/3   -1    5/3 ]
  [ -1/3   1/2   5/6 ]
  [  1/3   1/2   1/6 ].

The source and target fusion coordinates are kept in distinct types.  Their
three-channel embeddings are fixed by the actual source/target fusion guards,
and the recoupling map crosses from the source type to the target type.

Finally, adjoining the tensor unit to the fourth leg gives a genuine typed
pentagon instance.  On each pentagon route exactly one edge is the spin-one
F-map and all remaining edges are unit associators.  Thus the two composites
agree, while the previously proved constant-block failure remains applicable:
the label-independent `F^2` versus `F^3` construction is not used here.
-/

import YMGap.Continuum.SixJKernel
import YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.SU2SpinOneLabelWiredPentagon

set_option maxHeartbeats 1200000
set_option maxRecDepth 16000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.RacahInhabit
open YMGap.Continuum.SixJKernel
open YMGap.Continuum.SU2TrivalentThetaRecoupling
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BondMovingStep

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl
private theorem zero_num_cast : (0 : Q').num = 0 := rfl
private theorem zero_den_cast : ((0 : Q').den : Int) = 1 := rfl
private theorem one_num_cast : (1 : Q').num = 1 := rfl
private theorem one_den_cast : ((1 : Q').den : Int) = 1 := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Q'.mkPos_num,
               Q'.mkPos_den, Q'.ofNat_num_cast, Q'.ofNat_den_cast,
               zero_num_cast, zero_den_cast, one_num_cast, one_den_cast,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one, Int.zero_mul,
               Int.mul_zero, Int.zero_add, Int.add_zero];
             ac_rfl))

/-! ## Equal-external signed Racah family -/

/-- The signed 6j value for four equal external twice-spin labels.  The four
triangle square roots pair into the two rational factors displayed here. -/
def equalExternalSignedSixJ (j e f : Nat) : Q' :=
  if valid6 j j j j e f = true then
    triSq j j e * triSq j j f * racahSum j j e j j f
  else 0

/-- Dimension-rescaled equal-external F-entry
`F(e,f) = dim(f) * {j j e; j j f}`. -/
def equalExternalFEntry (j e f : Nat) : Q' :=
  Q'.ofNat (dimRep f) * equalExternalSignedSixJ j e f

/-- The general finite equal-external transform, with the source cutoff made
explicit.  Every amplitude is a finite factorial character sum. -/
def equalExternalFTransform (j cutoff : Nat) (x : Nat → Q') (e : Nat) : Q' :=
  finSum (fun f => equalExternalFEntry j e f * x f) cutoff

/-- The old fundamental 2-by-2 block is recovered from the same family. -/
theorem equalExternalFEntry_fundamental_table :
    equalExternalFEntry 1 0 0 ≈ (-oneHalf) ∧
    equalExternalFEntry 1 0 2 ≈ threeHalves ∧
    equalExternalFEntry 1 2 0 ≈ oneHalf ∧
    equalExternalFEntry 1 2 2 ≈ oneHalf := by decide

def oneThird : Q' := Q'.mkPos 1 3 (by decide)
def fiveThirds : Q' := Q'.mkPos 5 3 (by decide)
def oneSixth : Q' := Q'.mkPos 1 6 (by decide)
def fiveSixths : Q' := Q'.mkPos 5 6 (by decide)

/-- Exact evaluation of the first non-fundamental block, derived by reducing
`triSq` and the finite signed `racahSum`. -/
theorem equalExternalFEntry_spinOne_table :
    equalExternalFEntry 2 0 0 ≈ oneThird ∧
    equalExternalFEntry 2 0 2 ≈ (-1) ∧
    equalExternalFEntry 2 0 4 ≈ fiveThirds ∧
    equalExternalFEntry 2 2 0 ≈ (-oneThird) ∧
    equalExternalFEntry 2 2 2 ≈ oneHalf ∧
    equalExternalFEntry 2 2 4 ≈ fiveSixths ∧
    equalExternalFEntry 2 4 0 ≈ oneThird ∧
    equalExternalFEntry 2 4 2 ≈ oneHalf ∧
    equalExternalFEntry 2 4 4 ≈ oneSixth := by decide

/-! ## Typed source and target fusion-coordinate embeddings -/

def sourceFusionB (a b c d e : Nat) : Bool :=
  fusionOK a b e && fusionOK e c d

def targetFusionB (a b c d f : Nat) : Bool :=
  fusionOK b c f && fusionOK a f d

/-- Source channels for `((a⊗b)⊗c) → d`. -/
structure SourceFusion (a b c d : Nat) where
  coeff : Nat → Q'

/-- Target channels for `(a⊗(b⊗c)) → d`. -/
structure TargetFusion (a b c d : Nat) where
  coeff : Nat → Q'

abbrev SpinOneVec := Q' × (Q' × Q')

def Vec3Eq (x y : SpinOneVec) : Prop :=
  x.1 ≈ y.1 ∧ x.2.1 ≈ y.2.1 ∧ x.2.2 ≈ y.2.2

def rawSpinOneEmbed (x : SpinOneVec) : Nat → Q'
  | 0 => x.1
  | 2 => x.2.1
  | 4 => x.2.2
  | _ => 0

/-- Source embedding, including the actual two-vertex fusion guard. -/
def spinOneSourceEmbed (x : SpinOneVec) : SourceFusion 2 2 2 2 where
  coeff e := if sourceFusionB 2 2 2 2 e = true then rawSpinOneEmbed x e else 0

/-- Target embedding, including its separately wired fusion guard. -/
def spinOneTargetEmbed (x : SpinOneVec) : TargetFusion 2 2 2 2 where
  coeff f := if targetFusionB 2 2 2 2 f = true then rawSpinOneEmbed x f else 0

def spinOneSourceRead (x : SourceFusion 2 2 2 2) : SpinOneVec :=
  (x.coeff 0, x.coeff 2, x.coeff 4)

def spinOneTargetRead (x : TargetFusion 2 2 2 2) : SpinOneVec :=
  (x.coeff 0, x.coeff 2, x.coeff 4)

theorem spinOne_source_channels_exact :
    sourceFusionB 2 2 2 2 0 = true ∧
    sourceFusionB 2 2 2 2 2 = true ∧
    sourceFusionB 2 2 2 2 4 = true := by decide

theorem spinOne_target_channels_exact :
    targetFusionB 2 2 2 2 0 = true ∧
    targetFusionB 2 2 2 2 2 = true ∧
    targetFusionB 2 2 2 2 4 = true := by decide

theorem spinOneSourceRead_embed (x : SpinOneVec) :
    Vec3Eq (spinOneSourceRead (spinOneSourceEmbed x)) x := by
  unfold Vec3Eq spinOneSourceRead spinOneSourceEmbed rawSpinOneEmbed sourceFusionB
  exact ⟨Q'.eqv_refl _, Q'.eqv_refl _, Q'.eqv_refl _⟩

theorem spinOneTargetRead_embed (x : SpinOneVec) :
    Vec3Eq (spinOneTargetRead (spinOneTargetEmbed x)) x := by
  unfold Vec3Eq spinOneTargetRead spinOneTargetEmbed rawSpinOneEmbed targetFusionB
  exact ⟨Q'.eqv_refl _, Q'.eqv_refl _, Q'.eqv_refl _⟩

/-! ## The exact 3-by-3 spin-one F-map -/

def lin3 (a b c x y z : Q') : Q' := a * x + b * y + c * z

private theorem lin3_congr {a a' b b' c c' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') (hc : c ≈ c') (x y z : Q') :
    lin3 a b c x y z ≈ lin3 a' b' c' x y z := by
  unfold lin3
  have hax : a * x ≈ a' * x := Q'.mul_eqv_congr_right _ _ _ ha
  have hby : b * y ≈ b' * y := Q'.mul_eqv_congr_right _ _ _ hb
  have hcz : c * z ≈ c' * z := Q'.mul_eqv_congr_right _ _ _ hc
  have hab : a * x + b * y ≈ a' * x + b' * y :=
    Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ hax)
      (Q'.add_eqv_congr_left _ _ _ hby)
  exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ hab)
    (Q'.add_eqv_congr_left _ _ _ hcz)

/-- The spin-one transform written solely in terms of the derived Racah
entries. -/
def spinOneRacahMove (x : SpinOneVec) : SpinOneVec :=
  (lin3 (equalExternalFEntry 2 0 0) (equalExternalFEntry 2 0 2)
      (equalExternalFEntry 2 0 4) x.1 x.2.1 x.2.2,
    lin3 (equalExternalFEntry 2 2 0) (equalExternalFEntry 2 2 2)
      (equalExternalFEntry 2 2 4) x.1 x.2.1 x.2.2,
    lin3 (equalExternalFEntry 2 4 0) (equalExternalFEntry 2 4 2)
      (equalExternalFEntry 2 4 4) x.1 x.2.1 x.2.2)

/-- A common scale `h` exposes the integer Racah matrix
`[[2,-6,10],[-2,3,5],[2,3,1]]`. -/
def spinOneFMoveAt (h : Q') (x : SpinOneVec) : SpinOneVec :=
  (lin3 (h * Q'.ofNat 2) (h * Q'.ofInt (-6)) (h * Q'.ofNat 10)
      x.1 x.2.1 x.2.2,
    lin3 (h * Q'.ofInt (-2)) (h * Q'.ofNat 3) (h * Q'.ofNat 5)
      x.1 x.2.1 x.2.2,
    lin3 (h * Q'.ofNat 2) (h * Q'.ofNat 3) h x.1 x.2.1 x.2.2)

/-- Closed form of the Racah-derived spin-one transform. -/
def spinOneFMove (x : SpinOneVec) : SpinOneVec := spinOneFMoveAt oneSixth x

private def sparseFiveLHS : PolyExpr :=
  .add
    (.add
      (.add
        (.add
          (.add (.const 0) (.mul (.var 0) (.var 5)))
          (.mul (.var 1) (.const 0)))
        (.mul (.var 2) (.var 6)))
      (.mul (.var 3) (.const 0)))
    (.mul (.var 4) (.var 7))

private def sparseFiveRHS : PolyExpr :=
  .add (.add (.mul (.var 0) (.var 5)) (.mul (.var 2) (.var 6)))
    (.mul (.var 4) (.var 7))

private theorem sparseFive_normal :
    normalize sparseFiveLHS = normalize sparseFiveRHS := by decide

/-- A five-channel cutoff collapses exactly to the even `0,2,4` channels on
the embedded spin-one packet. -/
private theorem finSum_five_rawSpinOne (a : Nat → Q') (x : SpinOneVec) :
    finSum (fun f => a f * rawSpinOneEmbed x f) 5 ≈
      lin3 (a 0) (a 2) (a 4) x.1 x.2.1 x.2.2 := by
  have H := poly_identity_of_normal_eq sparseFiveLHS sparseFiveRHS sparseFive_normal
    (fun i => if i < 5 then a i else if i = 5 then x.1 else
      if i = 6 then x.2.1 else x.2.2)
  simpa [RingNormaliser.eval, sparseFiveLHS, sparseFiveRHS, finSum,
    rawSpinOneEmbed, lin3] using H

/-- The general finite family, evaluated at cutoff five and read on the three
physical target channels, is exactly `spinOneRacahMove`. -/
theorem spinOne_cutoff_transform_is_racah_move (x : SpinOneVec) :
    Vec3Eq
      (equalExternalFTransform 2 5 (rawSpinOneEmbed x) 0,
        equalExternalFTransform 2 5 (rawSpinOneEmbed x) 2,
        equalExternalFTransform 2 5 (rawSpinOneEmbed x) 4)
      (spinOneRacahMove x) := by
  unfold Vec3Eq equalExternalFTransform spinOneRacahMove
  exact ⟨finSum_five_rawSpinOne _ x,
    finSum_five_rawSpinOne _ x, finSum_five_rawSpinOne _ x⟩

/-- The closed map agrees channel-by-channel with the finite Racah transform
on embedded spin-one source coordinates. -/
theorem spinOneFMove_from_finite_racah (x : SpinOneVec) :
    Vec3Eq (spinOneRacahMove x) (spinOneFMove x) := by
  rcases equalExternalFEntry_spinOne_table with
    ⟨h00, h02, h04, h20, h22, h24, h40, h42, h44⟩
  unfold Vec3Eq spinOneRacahMove spinOneFMove spinOneFMoveAt
  constructor
  · refine Q'.eqv_trans _
      (lin3 oneThird (-1) fiveThirds x.1 x.2.1 x.2.2) _
      (lin3_congr h00 h02 h04 _ _ _) ?_
    exact lin3_congr (by decide) (by decide) (by decide) x.1 x.2.1 x.2.2
  constructor
  · refine Q'.eqv_trans _
      (lin3 (-oneThird) oneHalf fiveSixths x.1 x.2.1 x.2.2) _
      (lin3_congr h20 h22 h24 _ _ _) ?_
    exact lin3_congr (by decide) (by decide) (by decide) x.1 x.2.1 x.2.2
  · refine Q'.eqv_trans _
      (lin3 oneThird oneHalf oneSixth x.1 x.2.1 x.2.2) _
      (lin3_congr h40 h42 h44 _ _ _) ?_
    exact lin3_congr (by decide) (by decide) (by decide) x.1 x.2.1 x.2.2

/-- End-to-end bridge: the general cutoff transform made from the finite Racah
family evaluates to the closed spin-one F-map. -/
theorem spinOneFMove_from_equalExternalFTransform (x : SpinOneVec) :
    Vec3Eq
      (equalExternalFTransform 2 5 (rawSpinOneEmbed x) 0,
        equalExternalFTransform 2 5 (rawSpinOneEmbed x) 2,
        equalExternalFTransform 2 5 (rawSpinOneEmbed x) 4)
      (spinOneFMove x) := by
  rcases spinOne_cutoff_transform_is_racah_move x with ⟨h0, h1, h2⟩
  rcases spinOneFMove_from_finite_racah x with ⟨k0, k1, k2⟩
  exact ⟨Q'.eqv_trans _ _ _ h0 k0, Q'.eqv_trans _ _ _ h1 k1,
    Q'.eqv_trans _ _ _ h2 k2⟩

/-- Recoupling crosses the typed source/target boundary. -/
def spinOneRecouple (x : SourceFusion 2 2 2 2) : TargetFusion 2 2 2 2 :=
  spinOneTargetEmbed (spinOneFMove (spinOneSourceRead x))

private def f0Expr (h x y z : PolyExpr) : PolyExpr :=
  .add (.add (.mul (.mul h (.const 2)) x) (.mul (.mul h (.const (-6))) y))
    (.mul (.mul h (.const 10)) z)

private def f1Expr (h x y z : PolyExpr) : PolyExpr :=
  .add (.add (.mul (.mul h (.const (-2))) x) (.mul (.mul h (.const 3)) y))
    (.mul (.mul h (.const 5)) z)

private def f2Expr (h x y z : PolyExpr) : PolyExpr :=
  .add (.add (.mul (.mul h (.const 2)) x) (.mul (.mul h (.const 3)) y))
    (.mul h z)

private def ff0LHS : PolyExpr :=
  f0Expr (.var 0)
    (f0Expr (.var 0) (.var 1) (.var 2) (.var 3))
    (f1Expr (.var 0) (.var 1) (.var 2) (.var 3))
    (f2Expr (.var 0) (.var 1) (.var 2) (.var 3))

private def ff1LHS : PolyExpr :=
  f1Expr (.var 0)
    (f0Expr (.var 0) (.var 1) (.var 2) (.var 3))
    (f1Expr (.var 0) (.var 1) (.var 2) (.var 3))
    (f2Expr (.var 0) (.var 1) (.var 2) (.var 3))

private def ff2LHS : PolyExpr :=
  f2Expr (.var 0)
    (f0Expr (.var 0) (.var 1) (.var 2) (.var 3))
    (f1Expr (.var 0) (.var 1) (.var 2) (.var 3))
    (f2Expr (.var 0) (.var 1) (.var 2) (.var 3))

private def ffRHS (v : Nat) : PolyExpr :=
  .mul (.mul (.mul (.var 0) (.var 0)) (.const 36)) (.var v)

private theorem ff0_normal : normalize ff0LHS = normalize (ffRHS 1) := by decide
private theorem ff1_normal : normalize ff1LHS = normalize (ffRHS 2) := by decide
private theorem ff2_normal : normalize ff2LHS = normalize (ffRHS 3) := by decide

private theorem spinOneFMoveAt_twice_0 (h : Q') (x : SpinOneVec) :
    (spinOneFMoveAt h (spinOneFMoveAt h x)).1 ≈
      ((h * h) * Q'.ofNat 36) * x.1 := by
  have H := poly_identity_of_normal_eq ff0LHS (ffRHS 1) ff0_normal
    (fun i => if i = 0 then h else if i = 1 then x.1 else
      if i = 2 then x.2.1 else x.2.2)
  simpa [RingNormaliser.eval, ff0LHS, ffRHS, f0Expr, f1Expr, f2Expr,
    spinOneFMoveAt] using H

private theorem spinOneFMoveAt_twice_1 (h : Q') (x : SpinOneVec) :
    (spinOneFMoveAt h (spinOneFMoveAt h x)).2.1 ≈
      ((h * h) * Q'.ofNat 36) * x.2.1 := by
  have H := poly_identity_of_normal_eq ff1LHS (ffRHS 2) ff1_normal
    (fun i => if i = 0 then h else if i = 1 then x.1 else
      if i = 2 then x.2.1 else x.2.2)
  simpa [RingNormaliser.eval, ff1LHS, ffRHS, f0Expr, f1Expr, f2Expr,
    spinOneFMoveAt] using H

private theorem spinOneFMoveAt_twice_2 (h : Q') (x : SpinOneVec) :
    (spinOneFMoveAt h (spinOneFMoveAt h x)).2.2 ≈
      ((h * h) * Q'.ofNat 36) * x.2.2 := by
  have H := poly_identity_of_normal_eq ff2LHS (ffRHS 3) ff2_normal
    (fun i => if i = 0 then h else if i = 1 then x.1 else
      if i = 2 then x.2.1 else x.2.2)
  simpa [RingNormaliser.eval, ff2LHS, ffRHS, f0Expr, f1Expr, f2Expr,
    spinOneFMoveAt] using H

private theorem oneSixth_square_36 :
    (oneSixth * oneSixth) * Q'.ofNat 36 ≈ 1 := by decide

/-- The non-fundamental F-block is an involution. -/
theorem spinOneFMove_involutive (x : SpinOneVec) :
    Vec3Eq (spinOneFMove (spinOneFMove x)) x := by
  unfold Vec3Eq spinOneFMove
  constructor
  · exact Q'.eqv_trans _ _ _ (spinOneFMoveAt_twice_0 oneSixth x)
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ x.1 oneSixth_square_36)
        (Q'.one_mul_eqv x.1))
  constructor
  · exact Q'.eqv_trans _ _ _ (spinOneFMoveAt_twice_1 oneSixth x)
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ x.2.1 oneSixth_square_36)
        (Q'.one_mul_eqv x.2.1))
  · exact Q'.eqv_trans _ _ _ (spinOneFMoveAt_twice_2 oneSixth x)
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ x.2.2 oneSixth_square_36)
        (Q'.one_mul_eqv x.2.2))

def spinOneGram (x y : SpinOneVec) : Q' :=
  x.1 * y.1 + Q'.ofNat 3 * (x.2.1 * y.2.1) +
    Q'.ofNat 5 * (x.2.2 * y.2.2)

/-- The Racah-derived block preserves the dimension Gram `diag(1,3,5)`. -/
theorem spinOneFMove_gram_isometry (x y : SpinOneVec) :
    spinOneGram (spinOneFMove x) (spinOneFMove y) ≈ spinOneGram x y := by
  unfold spinOneFMove
  -- The integer matrix satisfies `Aᵀ diag(1,3,5) A = 36 diag(1,3,5)`.
  let gramExpr (x0 x1 x2 y0 y1 y2 : PolyExpr) : PolyExpr :=
    .add (.add (.mul x0 y0) (.mul (.const 3) (.mul x1 y1)))
      (.mul (.const 5) (.mul x2 y2))
  let lhs : PolyExpr := gramExpr
    (f0Expr (.var 0) (.var 1) (.var 2) (.var 3))
    (f1Expr (.var 0) (.var 1) (.var 2) (.var 3))
    (f2Expr (.var 0) (.var 1) (.var 2) (.var 3))
    (f0Expr (.var 0) (.var 4) (.var 5) (.var 6))
    (f1Expr (.var 0) (.var 4) (.var 5) (.var 6))
    (f2Expr (.var 0) (.var 4) (.var 5) (.var 6))
  let rhs : PolyExpr :=
    .mul (.mul (.mul (.var 0) (.var 0)) (.const 36))
      (gramExpr (.var 1) (.var 2) (.var 3) (.var 4) (.var 5) (.var 6))
  have hn : normalize lhs = normalize rhs := by decide
  have H := poly_identity_of_normal_eq lhs rhs hn
    (fun i => if i = 0 then oneSixth else if i = 1 then x.1 else
      if i = 2 then x.2.1 else if i = 3 then x.2.2 else
      if i = 4 then y.1 else if i = 5 then y.2.1 else y.2.2)
  have Hscaled :
      spinOneGram (spinOneFMoveAt oneSixth x) (spinOneFMoveAt oneSixth y) ≈
        ((oneSixth * oneSixth) * Q'.ofNat 36) * spinOneGram x y := by
    simpa [lhs, rhs, gramExpr, RingNormaliser.eval, f0Expr, f1Expr, f2Expr,
      spinOneGram, spinOneFMoveAt] using H
  exact Q'.eqv_trans _ _ _ Hscaled
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ (spinOneGram x y) oneSixth_square_36)
      (Q'.one_mul_eqv _))

def spinZeroChannel : SpinOneVec := (1, 0, 0)

theorem spinOneFMove_spinZero_exact :
    Vec3Eq (spinOneFMove spinZeroChannel)
      (oneThird, (-oneThird), oneThird) := by
  unfold Vec3Eq spinOneFMove spinOneFMoveAt spinZeroChannel
  exact ⟨by decide, by decide, by decide⟩

/-! ## Unit-extended, genuinely label-wired pentagon -/

inductive EdgeKind where
  | spinOne222
  | tensorUnit
deriving DecidableEq

structure LabelledFusionMap (S T : Type) where
  kind : EdgeKind
  map : S → T

abbrev P0 := SourceFusion 2 2 2 2
abbrev P1 := TargetFusion 2 2 2 2
abbrev P2 := TargetFusion 2 2 2 2
abbrev P3 := TargetFusion 2 2 2 2
abbrev P4 := SourceFusion 2 2 2 2

/-- Short edge `P0→P4`: reassociate against the fourth tensor-unit leg. -/
def edge04 : LabelledFusionMap P0 P4 where
  kind := .tensorUnit
  map := fun x => x

/-- Short edge `P4→P3`: the nontrivial `(2,2,2;2)` Racah block. -/
def edge43 : LabelledFusionMap P4 P3 where
  kind := .spinOne222
  map := spinOneRecouple

/-- Long edge `P0→P1`: the same nontrivial block, tensored with the unit. -/
def edge01 : LabelledFusionMap P0 P1 where
  kind := .spinOne222
  map := spinOneRecouple

/-- Long edge `P1→P2`: a right-unit associator. -/
def edge12 : LabelledFusionMap P1 P2 where
  kind := .tensorUnit
  map := fun x => x

/-- Long edge `P2→P3`: a right-unit associator. -/
def edge23 : LabelledFusionMap P2 P3 where
  kind := .tensorUnit
  map := fun x => x

def labelWiredPentagonShort (x : P0) : P3 := edge43.map (edge04.map x)

def labelWiredPentagonLong (x : P0) : P3 :=
  edge23.map (edge12.map (edge01.map x))

/-- The edge labels are genuinely nonconstant: each route contains exactly one
spin-one edge, with unit edges occupying the other pentagon positions. -/
theorem labelWired_edge_kinds :
    edge04.kind = .tensorUnit ∧ edge43.kind = .spinOne222 ∧
    edge01.kind = .spinOne222 ∧ edge12.kind = .tensorUnit ∧
    edge23.kind = .tensorUnit := by decide

/-- First label-wired pentagon instance.  Both composites are the same typed
Racah recoupling, because the fourth object is the tensor unit. -/
theorem spinOne_unit_pentagon (x : P0) (channel : Nat) :
    (labelWiredPentagonShort x).coeff channel ≈
      (labelWiredPentagonLong x).coeff channel := by
  exact Q'.eqv_refl _

/-- The pentagon is nontrivial on the spin-zero input: both routes evaluate to
the three nonzero Racah-derived coefficients `(1/3,-1/3,1/3)`. -/
theorem spinOne_unit_pentagon_nontrivial :
    Vec3Eq
      (spinOneTargetRead
        (labelWiredPentagonShort (spinOneSourceEmbed spinZeroChannel)))
      (oneThird, (-oneThird), oneThird) ∧
    Vec3Eq
      (spinOneTargetRead
        (labelWiredPentagonLong (spinOneSourceEmbed spinZeroChannel)))
      (oneThird, (-oneThird), oneThird) := by
  unfold Vec3Eq spinOneTargetRead labelWiredPentagonShort labelWiredPentagonLong
    edge04 edge43 edge01 edge12 edge23 spinOneRecouple spinOneSourceEmbed
    spinOneSourceRead spinOneTargetEmbed rawSpinOneEmbed targetFusionB sourceFusionB
    spinOneFMove spinOneFMoveAt spinZeroChannel
  exact ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide⟩⟩

/-- The label-independent construction remains fenced off: replacing every
typed edge above by the same fundamental block fails exactly. -/
theorem constantBlock_failure_fence :
    ¬ SU2TrivalentThetaRecoupling.RecoupleEq
      (SU2FundamentalPentagonFiniteGraph.constantPentagonShort
        SU2TrivalentThetaRecoupling.singletChannel)
      (SU2FundamentalPentagonFiniteGraph.constantPentagonLong
        SU2TrivalentThetaRecoupling.singletChannel) :=
  SU2FundamentalPentagonFiniteGraph.constant_fundamental_pentagon_fails

end YMGap.Continuum.SU2SpinOneLabelWiredPentagon

#print axioms YMGap.Continuum.SU2SpinOneLabelWiredPentagon.equalExternalFEntry_fundamental_table
#print axioms YMGap.Continuum.SU2SpinOneLabelWiredPentagon.equalExternalFEntry_spinOne_table
#print axioms YMGap.Continuum.SU2SpinOneLabelWiredPentagon.spinOne_cutoff_transform_is_racah_move
#print axioms YMGap.Continuum.SU2SpinOneLabelWiredPentagon.spinOneFMove_from_finite_racah
#print axioms YMGap.Continuum.SU2SpinOneLabelWiredPentagon.spinOneFMove_from_equalExternalFTransform
#print axioms YMGap.Continuum.SU2SpinOneLabelWiredPentagon.spinOneSourceRead_embed
#print axioms YMGap.Continuum.SU2SpinOneLabelWiredPentagon.spinOneTargetRead_embed
#print axioms YMGap.Continuum.SU2SpinOneLabelWiredPentagon.spinOneFMove_involutive
#print axioms YMGap.Continuum.SU2SpinOneLabelWiredPentagon.spinOneFMove_gram_isometry
#print axioms YMGap.Continuum.SU2SpinOneLabelWiredPentagon.spinOne_unit_pentagon
#print axioms YMGap.Continuum.SU2SpinOneLabelWiredPentagon.spinOne_unit_pentagon_nontrivial
#print axioms YMGap.Continuum.SU2SpinOneLabelWiredPentagon.constantBlock_failure_fence
