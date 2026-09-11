/-
# Exact Boolean delta resolution of the edge-touching double cube

The face-major double-cube network contains forty-eight Boolean matrix-index
binders.  This leaf keeps that sum opaque and eliminates the twenty-two Schur
deltas structurally: one three-index equality component is compressed at a
time, leaving sixteen component binders and never enumerating either Boolean
assignment space.

# Axiom gate

No `Classical`, choice, `sorry`/`admit`, `native_decide`, or custom axiom.
No depth-forty-eight Boolean sum is unfolded, simplified, or evaluated.
-/

import YMGap.Continuum.SU2QuaternionEdgeTouchingDoubleCubeDeltaComponents
import YMGap.Continuum.SU2QuaternionEdgeTouchingDoubleCubeFaceWordBridge

namespace YMGap.Continuum.SU2QuaternionEdgeTouchingDoubleCubeBooleanDeltaResolution

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenActiveLinkCarrier
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchur
open YMGap.Continuum.SU2QuaternionFundamentalMatrixSemantics
open YMGap.Continuum.SU2QuaternionComplexRatPolyAlgebra
open YMGap.Continuum.SU2QuaternionComplexBoolSumAlgebra
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionOneLinkFourValentHaarProjector
open YMGap.Continuum.SU2QuaternionFundamentalPlaquetteTraceExpansion
open YMGap.Continuum.SU2QuaternionFiniteProductHaarComplexFourBoolFubini
open YMGap.Continuum.SU2QuaternionElementaryCubeBooleanDeltaResolution
open YMGap.Continuum.SU2QuaternionEdgeTouchingDoubleCubeBivalentContraction
open YMGap.Continuum.SU2QuaternionEdgeTouchingDoubleCubeDeltaComponents
open YMGap.Continuum.SU2QuaternionEdgeTouchingDoubleCubeFaceWordBridge

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
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.zero_add, Int.add_zero] <;>
             ac_rfl))

/-! ## 1. Structural compression of equality triangles -/

/-- Replace every component bit by its three equal tag values. -/
def repeatEachBoolThree : List Bool → List Bool
  | [] => []
  | bit :: bits => bit :: bit :: bit :: repeatEachBoolThree bits

private theorem rationalComplexOne_mul_eqv
    (value : RationalComplex) :
    RationalComplexEqv
      (rationalComplexMul rationalComplexOne value) value := by
  unfold rationalComplexMul rationalComplexOne RationalComplexEqv
  constructor <;> ring_qeqv

private theorem rationalComplexZero_mul_eqv
    (value : RationalComplex) :
    RationalComplexEqv
      (rationalComplexMul rationalComplexZero value) rationalComplexZero := by
  unfold rationalComplexMul rationalComplexZero RationalComplexEqv
  constructor <;> ring_qeqv

private theorem rationalComplexAdd_zero_eqv
    (value : RationalComplex) :
    RationalComplexEqv
      (rationalComplexAdd value rationalComplexZero) value := by
  unfold rationalComplexAdd rationalComplexZero RationalComplexEqv
  constructor <;> ring_qeqv

private theorem rationalComplexZero_add_eqv
    (value : RationalComplex) :
    RationalComplexEqv
      (rationalComplexAdd rationalComplexZero value) value := by
  unfold rationalComplexAdd rationalComplexZero RationalComplexEqv
  constructor <;> ring_qeqv

/-- A three-index equality indicator eliminates two redundant binders even
with an arbitrary rational-complex payload.  Only the eight local Boolean
branches are exposed. -/
theorem rationalComplexThreeBoolBind_equalityTriangleLocal_mul
    (payload : Bool → Bool → Bool → RationalComplex) :
    RationalComplexEqv
      (rationalComplexThreeBoolBind (fun first second third =>
        rationalComplexMul
          (equalityTriangleLocal first second third)
          (payload first second third)))
      (rationalComplexBoolBind (fun bit => payload bit bit bit)) := by
  refine rationalComplexEqv_trans
    (rationalComplexThreeBoolBind_congr
      (right := fun first second third =>
        if equalityTriangleMatchBool first second third then
          payload first second third
        else rationalComplexZero)
      (fun first second third => by
        cases first <;> cases second <;> cases third <;>
          unfold equalityTriangleLocal equalityTriangleMatchBool
            qBoolIndicator pureReal <;>
          simp only [if_false, if_true] <;>
          first
          | exact rationalComplexOne_mul_eqv _
          | exact rationalComplexZero_mul_eqv _)) ?_
  unfold rationalComplexThreeBoolBind rationalComplexBoolBind
    equalityTriangleMatchBool
  simp only [if_false, if_true]
  exact rationalComplexAdd_congr
    (rationalComplexEqv_trans
      (rationalComplexAdd_congr
        (rationalComplexAdd_zero_eqv _)
        (rationalComplexZero_add_eqv rationalComplexZero))
      (rationalComplexAdd_zero_eqv _))
    (rationalComplexEqv_trans
      (rationalComplexAdd_congr
        (rationalComplexZero_add_eqv rationalComplexZero)
        (rationalComplexZero_add_eqv _))
      (rationalComplexZero_add_eqv _))

/-- **Parametric component compression.**  A product of `count` consecutive
equality-triangle indicators reduces a symbolic `3*count`-binder sum to a
`count`-binder sum whose assignments are tripled componentwise.  The proof is
inductive in `count`; no concrete high-depth sum is unfolded. -/
theorem rationalComplexBoolSum_triangleCompression
    (payload : List Bool → RationalComplex) :
    ∀ count : Nat,
      RationalComplexEqv
        (rationalComplexBoolSum (3 * count) (fun assignment =>
          rationalComplexMul
            (threeChunkProduct equalityTriangleLocal count assignment)
            (payload assignment)))
        (rationalComplexBoolSum count (fun components =>
          payload (repeatEachBoolThree components))) := by
  intro count
  induction count generalizing payload with
  | zero =>
      unfold rationalComplexBoolSum threeChunkProduct repeatEachBoolThree
        rationalComplexOne rationalComplexMul RationalComplexEqv
      constructor <;> ring_qeqv
  | succ count ih =>
      rw [show 3 * (count + 1) = 3 * count + 3 by omega]
      rw [rationalComplexBoolSum_add_three]
      simp only [threeChunkProduct, List.getD_cons_zero,
        List.getD_cons_succ, List.drop_succ_cons, List.drop_zero]
      refine rationalComplexEqv_trans
        (rationalComplexThreeBoolBind_congr
          (right := fun first second third =>
            rationalComplexMul
              (equalityTriangleLocal first second third)
              (rationalComplexBoolSum count (fun components =>
                payload (first :: second :: third ::
                  repeatEachBoolThree components))))
          (fun first second third => ?_)) ?_
      · refine rationalComplexEqv_trans
          (rationalComplexBoolSum_congr (3 * count) (fun rest =>
            rationalComplexMul_assoc
              (equalityTriangleLocal first second third)
              (threeChunkProduct equalityTriangleLocal count rest)
              (payload (first :: second :: third :: rest)))) ?_
        refine rationalComplexEqv_trans
          (rationalComplexEqv_symm
            (rationalComplexMul_boolSum
              (equalityTriangleLocal first second third) (3 * count)
              (fun rest => rationalComplexMul
                (threeChunkProduct equalityTriangleLocal count rest)
                (payload (first :: second :: third :: rest))))) ?_
        exact rationalComplexMul_congr_right _
          (ih (payload := fun rest =>
            payload (first :: second :: third :: rest)))
      · refine rationalComplexEqv_trans
          (rationalComplexThreeBoolBind_equalityTriangleLocal_mul
            (fun first second third =>
              rationalComplexBoolSum count (fun components =>
                payload (first :: second :: third ::
                  repeatEachBoolThree components)))) ?_
        change RationalComplexEqv
          (rationalComplexBoolBind (fun bit =>
            rationalComplexBoolSum count (fun components =>
              payload (bit :: bit :: bit :: repeatEachBoolThree components))))
          (rationalComplexBoolSum (count + 1) (fun components =>
            payload (repeatEachBoolThree components)))
        exact rationalComplexEqv_refl _

/-! ## 2. The sixteen-component projector sum -/

/-- The two-sheet projector read from four consecutive component bits.  At
offset six these are, in component order, `B1,A1,A2,B2`. -/
def twoSheetComponentProjectorAt
    (offset : Nat) (components : List Bool) : RationalComplex :=
  orientedFourFundamentalHaarProjector
    (components.getD (offset + 1) false)
    (components.getD offset false)
    (components.getD (offset + 2) false)
    (components.getD (offset + 3) false)
    (components.getD offset false)
    (components.getD (offset + 1) false)
    (components.getD (offset + 3) false)
    (components.getD (offset + 2) false)

def twoSheetComponentProjector (components : List Bool) : RationalComplex :=
  twoSheetComponentProjectorAt 6 components

theorem twoSheetComponentProjectorAt_cons_three
    (offset : Nat) (first second third : Bool) (rest : List Bool) :
    twoSheetComponentProjectorAt (offset + 3)
        (first :: second :: third :: rest) =
      twoSheetComponentProjectorAt offset rest := by
  unfold twoSheetComponentProjectorAt
  simp only [List.getD_cons_succ]

theorem repeatEachBoolThree_getD_zero
    (components : List Bool) : ∀ component : Nat,
    (repeatEachBoolThree components).getD (3 * component) false =
      components.getD component false
  | 0 => by
      cases components <;>
        simp only [repeatEachBoolThree, List.getD_nil,
          List.getD_cons_zero, Nat.mul_zero]
  | component + 1 => by
      cases components with
      | nil =>
          simp only [repeatEachBoolThree, List.getD_nil]
      | cons bit bits =>
          simp only [repeatEachBoolThree, Nat.mul_add, Nat.mul_one,
            List.getD_cons_succ]
          exact repeatEachBoolThree_getD_zero bits component

theorem repeatEachBoolThree_getD_one
    (components : List Bool) (component : Nat) :
    (repeatEachBoolThree components).getD (3 * component + 1) false =
      components.getD component false := by
  cases components with
  | nil => simp only [repeatEachBoolThree, List.getD_nil]
  | cons bit bits =>
      cases component with
      | zero =>
          simp only [repeatEachBoolThree, Nat.mul_zero, Nat.zero_add,
            List.getD_cons_succ, List.getD_cons_zero]
      | succ component =>
          simp only [repeatEachBoolThree, Nat.mul_add, Nat.mul_one,
            List.getD_cons_succ]
          exact repeatEachBoolThree_getD_one bits component

theorem repeatEachBoolThree_getD_two
    (components : List Bool) (component : Nat) :
    (repeatEachBoolThree components).getD (3 * component + 2) false =
      components.getD component false := by
  cases components with
  | nil => simp only [repeatEachBoolThree, List.getD_nil]
  | cons bit bits =>
      cases component with
      | zero =>
          simp only [repeatEachBoolThree, Nat.mul_zero, Nat.zero_add,
            List.getD_cons_succ, List.getD_cons_zero]
      | succ component =>
          simp only [repeatEachBoolThree, Nat.mul_add, Nat.mul_one,
            List.getD_cons_succ]
          exact repeatEachBoolThree_getD_two bits component

/-- Tripling the sixteen component bits feeds the shared projector exactly in
the cross-wired order certified by the bivalent graph. -/
theorem radiusZeroEdgeTouchingDoubleCubeSharedProjector_repeatEachBoolThree
    (components : List Bool) :
    radiusZeroEdgeTouchingDoubleCubeSharedProjector
        (repeatEachBoolThree components) =
      twoSheetComponentProjector components := by
  unfold radiusZeroEdgeTouchingDoubleCubeSharedProjector
    twoSheetComponentProjector twoSheetComponentProjectorAt
    doubleCubeTagValue
  rw [show 23 = 3 * 7 + 2 by omega,
    repeatEachBoolThree_getD_two components 7]
  rw [show 19 = 3 * 6 + 1 by omega,
    repeatEachBoolThree_getD_one components 6]
  rw [show 25 = 3 * 8 + 1 by omega,
    repeatEachBoolThree_getD_one components 8]
  rw [show 28 = 3 * 9 + 1 by omega,
    repeatEachBoolThree_getD_one components 9]
  rw [show 18 = 3 * 6 by omega,
    repeatEachBoolThree_getD_zero components 6]
  rw [show 22 = 3 * 7 + 1 by omega,
    repeatEachBoolThree_getD_one components 7]
  rw [show 27 = 3 * 9 by omega,
    repeatEachBoolThree_getD_zero components 9]
  rw [show 24 = 3 * 8 by omega,
    repeatEachBoolThree_getD_zero components 8]

/-- A constant family over exactly three Boolean binders contributes eight.
This bounded proof is kept literal so no open-ended power recursion enters
the trust boundary. -/
private theorem rationalComplexOne_add_one_eqv_two :
    RationalComplexEqv
      (rationalComplexAdd rationalComplexOne rationalComplexOne)
      (pureReal (Q'.ofNat 2)) := by
  unfold rationalComplexAdd rationalComplexOne pureReal RationalComplexEqv
  constructor <;> decide

private theorem rationalComplexBoolBind_const_two
    (value : RationalComplex) :
    RationalComplexEqv
      (rationalComplexBoolBind (fun _ => value))
      (rationalComplexMul (pureReal (Q'.ofNat 2)) value) := by
  unfold rationalComplexBoolBind
  refine rationalComplexEqv_trans
    (rationalComplexAdd_congr
      (rationalComplexEqv_symm (rationalComplexOne_mul_eqv value))
      (rationalComplexEqv_symm (rationalComplexOne_mul_eqv value))) ?_
  refine rationalComplexEqv_trans
    (rationalComplexEqv_symm
      (rationalComplexAdd_mul
        rationalComplexOne rationalComplexOne value)) ?_
  exact rationalComplexMul_congr
    rationalComplexOne_add_one_eqv_two
    (rationalComplexEqv_refl value)

theorem rationalComplexThreeBoolBind_const (value : RationalComplex) :
    RationalComplexEqv
      (rationalComplexThreeBoolBind (fun _ _ _ => value))
      (rationalComplexMul (pureReal (Q'.ofNat 8)) value) := by
  let two := pureReal (Q'.ofNat 2)
  let four := pureReal (Q'.ofNat 4)
  have htwoTwo : RationalComplexEqv
      (rationalComplexMul two two) four := by
    dsimp [two, four]
    exact rationalComplexEqv_trans
      (rationalComplexMul_pureReal (Q'.ofNat 2) (Q'.ofNat 2))
      (pureReal_congr (by decide))
  have hfourTwo : RationalComplexEqv
      (rationalComplexMul four two) (pureReal (Q'.ofNat 8)) := by
    dsimp [two, four]
    exact rationalComplexEqv_trans
      (rationalComplexMul_pureReal (Q'.ofNat 4) (Q'.ofNat 2))
      (pureReal_congr (by decide))
  unfold rationalComplexThreeBoolBind
  refine rationalComplexEqv_trans
    (rationalComplexBoolBind_congr (fun _ =>
      rationalComplexBoolBind_congr (fun _ =>
        rationalComplexBoolBind_const_two value))) ?_
  refine rationalComplexEqv_trans
    (rationalComplexBoolBind_congr (fun _ =>
      rationalComplexBoolBind_const_two
        (rationalComplexMul two value))) ?_
  refine rationalComplexEqv_trans
    (rationalComplexBoolBind_const_two
      (rationalComplexMul two (rationalComplexMul two value))) ?_
  refine rationalComplexEqv_trans
    (rationalComplexEqv_symm
      (rationalComplexMul_assoc two two
        (rationalComplexMul two value))) ?_
  refine rationalComplexEqv_trans
    (rationalComplexMul_congr
      htwoTwo
      (rationalComplexEqv_refl _)) ?_
  refine rationalComplexEqv_trans
    (rationalComplexEqv_symm
      (rationalComplexMul_assoc four two value)) ?_
  exact rationalComplexMul_congr
    hfourTwo
    (rationalComplexEqv_refl value)

theorem rationalComplexBoolSum_const_six (value : RationalComplex) :
    RationalComplexEqv
      (rationalComplexBoolSum 6 (fun _ => value))
      (rationalComplexMul (pureReal (Q'.ofNat 64)) value) := by
  rw [show 6 = 3 + 3 by omega, rationalComplexBoolSum_add_three]
  refine rationalComplexEqv_trans
    (rationalComplexThreeBoolBind_congr (fun _ _ _ =>
      rationalComplexThreeBoolBind_const value)) ?_
  refine rationalComplexEqv_trans
    (rationalComplexThreeBoolBind_const
      (rationalComplexMul (pureReal (Q'.ofNat 8)) value)) ?_
  refine rationalComplexEqv_trans
    (rationalComplexEqv_symm
      (rationalComplexMul_assoc
        (pureReal (Q'.ofNat 8))
        (pureReal (Q'.ofNat 8)) value)) ?_
  exact rationalComplexMul_congr
    (rationalComplexEqv_trans
      (rationalComplexMul_pureReal (Q'.ofNat 8) (Q'.ofNat 8))
      (pureReal_congr (by decide)))
    (rationalComplexEqv_refl value)

theorem rationalComplexMul_fourBoolSum
    (factor : RationalComplex)
    (family : Bool → Bool → Bool → Bool → RationalComplex) :
    RationalComplexEqv
      (rationalComplexMul factor (rationalComplexFourBoolSum family))
      (rationalComplexFourBoolSum (fun first second third fourth =>
        rationalComplexMul factor (family first second third fourth))) := by
  unfold rationalComplexFourBoolSum
  refine rationalComplexEqv_trans
    (rationalComplexMul_boolBind factor _) ?_
  apply rationalComplexBoolBind_congr
  intro first
  refine rationalComplexEqv_trans
    (rationalComplexMul_boolBind factor _) ?_
  apply rationalComplexBoolBind_congr
  intro second
  refine rationalComplexEqv_trans
    (rationalComplexMul_boolBind factor _) ?_
  apply rationalComplexBoolBind_congr
  intro third
  exact rationalComplexMul_boolBind factor (family first second third)

/-- The natural component order `B1,A1,A2,B2` is constructively exchanged
into the banked external-wiring order `A1,A2,B1,B2`. -/
theorem twoSheetComponentProjector_fourBoolSum :
    RationalComplexEqv
      (rationalComplexFourBoolSum (fun firstB firstA secondA secondB =>
        orientedFourFundamentalHaarProjector
          firstA firstB secondA secondB
          firstB firstA secondB secondA))
      ((4 : Q'), 0) := by
  unfold rationalComplexFourBoolSum
  refine rationalComplexEqv_trans
    (rationalComplexBoolBind_swap (fun firstB firstA =>
      rationalComplexBoolBind (fun secondA =>
        rationalComplexBoolBind (fun secondB =>
          orientedFourFundamentalHaarProjector
            firstA firstB secondA secondB
            firstB firstA secondB secondA)))) ?_
  refine rationalComplexEqv_trans
    (rationalComplexBoolBind_congr (fun firstA =>
      rationalComplexBoolBind_swap (fun firstB secondA =>
        rationalComplexBoolBind (fun secondB =>
          orientedFourFundamentalHaarProjector
            firstA firstB secondA secondB
            firstB firstA secondB secondA)))) ?_
  exact orientedFourFundamentalHaarProjector_twoSheetExternalWiringSum

theorem rationalComplexBoolSum_ten_twoSheetComponentProjectorAt_zero :
    RationalComplexEqv
      (rationalComplexBoolSum 10 (twoSheetComponentProjectorAt 0))
      (pureReal (Q'.ofNat 256)) := by
  rw [show 10 = 6 + 4 by omega, rationalComplexBoolSum_add_four]
  refine rationalComplexEqv_trans
    (rationalComplexFourBoolSum_congr (fun firstB firstA secondA secondB =>
      rationalComplexBoolSum_congr 6 (fun suffix => by
        change RationalComplexEqv
          (twoSheetComponentProjectorAt 0
            (firstB :: firstA :: secondA :: secondB :: suffix))
          (orientedFourFundamentalHaarProjector
            firstA firstB secondA secondB
            firstB firstA secondB secondA)
        unfold twoSheetComponentProjectorAt
        simp only [List.getD_cons_zero, List.getD_cons_succ]
        exact rationalComplexEqv_refl _))) ?_
  refine rationalComplexEqv_trans
    (rationalComplexFourBoolSum_congr (fun firstB firstA secondA secondB =>
      rationalComplexBoolSum_const_six
        (orientedFourFundamentalHaarProjector
          firstA firstB secondA secondB
          firstB firstA secondB secondA))) ?_
  refine rationalComplexEqv_trans
    (rationalComplexEqv_symm
      (rationalComplexMul_fourBoolSum (pureReal (Q'.ofNat 64)) _)) ?_
  refine rationalComplexEqv_trans
    (rationalComplexMul_congr_right _
      twoSheetComponentProjector_fourBoolSum) ?_
  refine rationalComplexEqv_trans
    (rationalComplexMul_pureReal (Q'.ofNat 64) (Q'.ofNat 4)) ?_
  exact pureReal_congr (by decide)

/-- Twelve ordinary component bits multiply the cross-wired four-index sum
by `2^12`; the complete sixteen-component projector sum is `16384`. -/
theorem rationalComplexBoolSum_twoSheetComponentProjector :
    RationalComplexEqv
      (rationalComplexBoolSum 16 twoSheetComponentProjector)
      (pureReal (Q'.ofNat 16384)) := by
  have hthirteen : RationalComplexEqv
      (rationalComplexBoolSum 13 (twoSheetComponentProjectorAt 3))
      (pureReal (Q'.ofNat 2048)) := by
    rw [show 13 = 10 + 3 by omega, rationalComplexBoolSum_add_three]
    refine rationalComplexEqv_trans
      (rationalComplexThreeBoolBind_congr (fun first second third =>
        rationalComplexBoolSum_congr 10 (fun rest => by
          simpa only [twoSheetComponentProjectorAt_cons_three] using
            (rationalComplexEqv_refl
              (twoSheetComponentProjectorAt 0 rest))))) ?_
    refine rationalComplexEqv_trans
      (rationalComplexThreeBoolBind_const
        (rationalComplexBoolSum 10 (twoSheetComponentProjectorAt 0))) ?_
    refine rationalComplexEqv_trans
      (rationalComplexMul_congr_right _
        rationalComplexBoolSum_ten_twoSheetComponentProjectorAt_zero) ?_
    refine rationalComplexEqv_trans
      (rationalComplexMul_pureReal (Q'.ofNat 8) (Q'.ofNat 256)) ?_
    exact pureReal_congr (by decide)
  change RationalComplexEqv
    (rationalComplexBoolSum 16 (twoSheetComponentProjectorAt 6)) _
  rw [show 16 = 13 + 3 by omega, rationalComplexBoolSum_add_three]
  refine rationalComplexEqv_trans
    (rationalComplexThreeBoolBind_congr (fun first second third =>
      rationalComplexBoolSum_congr 13 (fun rest => by
        simpa only [twoSheetComponentProjectorAt_cons_three] using
          (rationalComplexEqv_refl
            (twoSheetComponentProjectorAt 3 rest))))) ?_
  refine rationalComplexEqv_trans
    (rationalComplexThreeBoolBind_const
      (rationalComplexBoolSum 13 (twoSheetComponentProjectorAt 3))) ?_
  refine rationalComplexEqv_trans
    (rationalComplexMul_congr_right _ hthirteen) ?_
  refine rationalComplexEqv_trans
    (rationalComplexMul_pureReal (Q'.ofNat 8) (Q'.ofNat 2048)) ?_
  exact pureReal_congr (by decide)

/-! ## 3. Exact depth-forty-eight closure -/

/-- Scalar part of the shared-link projector in its certified canonical
`F1 F2 R1 R2` slot convention. -/
def radiusZeroEdgeTouchingDoubleCubeSharedProjectorScalar
    (assignment : List Bool) : Q' :=
  orientedFourFundamentalHaarProjectorScalar
    (doubleCubeTagValue assignment 23)
    (doubleCubeTagValue assignment 19)
    (doubleCubeTagValue assignment 25)
    (doubleCubeTagValue assignment 28)
    (doubleCubeTagValue assignment 18)
    (doubleCubeTagValue assignment 22)
    (doubleCubeTagValue assignment 27)
    (doubleCubeTagValue assignment 24)

theorem radiusZeroEdgeTouchingDoubleCubeSharedProjector_eq_pureReal
    (assignment : List Bool) :
    radiusZeroEdgeTouchingDoubleCubeSharedProjector assignment =
      pureReal
        (radiusZeroEdgeTouchingDoubleCubeSharedProjectorScalar assignment) := by
  rfl

/-- The pointwise resolved integrand.  It is deliberately ordered as
`sixteen equality triangles * (2^-22 * shared projector)` so that the
generic component-compression theorem applies without exposing the
depth-forty-eight recursion. -/
def radiusZeroEdgeTouchingDoubleCubeResolvedDeltaValue
    (assignment : List Bool) : RationalComplex :=
  rationalComplexMul
    (threeChunkProduct equalityTriangleLocal 16 assignment)
    (rationalComplexMul
      (pureReal (qpow (Q'.invSucc 1) 22))
      (radiusZeroEdgeTouchingDoubleCubeSharedProjector assignment))

/-- Pointwise resolution of all twenty-two Schur half-factors and their
forty-four crossed deltas into the sixteen certified components. -/
theorem radiusZeroEdgeTouchingDoubleCubeContractedValue_eqv_resolved
    (assignment : List Bool) :
    RationalComplexEqv
      (radiusZeroEdgeTouchingDoubleCubeContractedValue assignment)
      (radiusZeroEdgeTouchingDoubleCubeResolvedDeltaValue assignment) := by
  let scalar :=
    radiusZeroEdgeTouchingDoubleCubeSharedProjectorScalar assignment
  let schedule :=
    radiusZeroEdgeTouchingDoubleCubeBivalentSchedule assignment
  let halfPower := qpow (Q'.invSucc 1) 22
  let matchProduct := contractionMatchProduct schedule
  let triangleProduct := triangleMatchProduct 16 assignment
  have hmatch : matchProduct ≈ triangleProduct := by
    exact radiusZeroEdgeTouchingDoubleCubeContractionMatchProduct_eqv_components
      assignment
  have hreorder :
      (scalar * halfPower) * matchProduct ≈
        triangleProduct * (halfPower * scalar) := by
    refine Q'.eqv_trans _
      ((scalar * halfPower) * triangleProduct) _
      (Q'.mul_eqv_congr_left (scalar * halfPower)
        matchProduct triangleProduct hmatch) ?_
    ring_qeqv
  have hresolved : RationalComplexEqv
      (radiusZeroEdgeTouchingDoubleCubeResolvedDeltaValue assignment)
      (pureReal (triangleProduct * (halfPower * scalar))) := by
    unfold radiusZeroEdgeTouchingDoubleCubeResolvedDeltaValue
    rw [radiusZeroEdgeTouchingDoubleCubeSharedProjector_eq_pureReal]
    refine rationalComplexEqv_trans
      (rationalComplexMul_congr
        (threeChunkProduct_equalityTriangleLocal_eqv 16 assignment)
        (rationalComplexMul_pureReal halfPower scalar)) ?_
    exact rationalComplexMul_pureReal triangleProduct (halfPower * scalar)
  unfold radiusZeroEdgeTouchingDoubleCubeContractedValue
  rw [radiusZeroEdgeTouchingDoubleCubeSharedProjector_eq_pureReal]
  refine rationalComplexEqv_trans
    (schurDeltaProductFrom_eqv_pureReal scalar schedule) ?_
  rw [radiusZeroEdgeTouchingDoubleCubeBivalentSchedule_length assignment]
  refine rationalComplexEqv_trans (pureReal_congr hreorder) ?_
  exact rationalComplexEqv_symm hresolved

/-- **Exact structural sum.**  The opaque forty-eight-binder sum compresses
to sixteen component bits.  Twelve ordinary bits give `2^12`, while the
four shared components close the signed projector with value four; after
the twenty-two Schur half-factors the exact result is `1/256`.

No depth-sixteen or depth-forty-eight Boolean recursion is unfolded. -/
theorem rationalComplexBoolSum_radiusZeroEdgeTouchingDoubleCubeResolvedDeltaValue_exact :
    RationalComplexEqv
      (rationalComplexBoolSum 48
        radiusZeroEdgeTouchingDoubleCubeResolvedDeltaValue)
      (Q'.mkPos 1 256 (by decide), 0) := by
  unfold radiusZeroEdgeTouchingDoubleCubeResolvedDeltaValue
  rw [show 48 = 3 * 16 by omega]
  refine rationalComplexEqv_trans
    (rationalComplexBoolSum_triangleCompression
      (payload := fun assignment =>
        rationalComplexMul
          (pureReal (qpow (Q'.invSucc 1) 22))
          (radiusZeroEdgeTouchingDoubleCubeSharedProjector assignment))
      16) ?_
  refine rationalComplexEqv_trans
    (rationalComplexBoolSum_congr 16 (fun components => by
      simpa only
          [radiusZeroEdgeTouchingDoubleCubeSharedProjector_repeatEachBoolThree]
        using
          (rationalComplexEqv_refl
            (rationalComplexMul
              (pureReal (qpow (Q'.invSucc 1) 22))
              (twoSheetComponentProjector components))))) ?_
  refine rationalComplexEqv_trans
    (rationalComplexEqv_symm
      (rationalComplexMul_boolSum
        (pureReal (qpow (Q'.invSucc 1) 22)) 16
        twoSheetComponentProjector)) ?_
  refine rationalComplexEqv_trans
    (rationalComplexMul_congr_right _
      rationalComplexBoolSum_twoSheetComponentProjector) ?_
  refine rationalComplexEqv_trans
    (rationalComplexMul_pureReal
      (qpow (Q'.invSucc 1) 22) (Q'.ofNat 16384)) ?_
  exact pureReal_congr (by decide)

theorem rationalComplexBoolSum_radiusZeroEdgeTouchingDoubleCubeContractedValue_exact :
    RationalComplexEqv
      (rationalComplexBoolSum 48
        radiusZeroEdgeTouchingDoubleCubeContractedValue)
      (Q'.mkPos 1 256 (by decide), 0) :=
  rationalComplexEqv_trans
    (rationalComplexBoolSum_congr 48 (fun assignment =>
      radiusZeroEdgeTouchingDoubleCubeContractedValue_eqv_resolved
        assignment))
    rationalComplexBoolSum_radiusZeroEdgeTouchingDoubleCubeResolvedDeltaValue_exact

/-! ## 4. Honest face-major coefficient network -/

/-- The descriptor-certified production boundary word, summed over its
forty-eight matrix indices.  This is an honest polynomial network.  A later
leaf will identify it with the literal product of twelve four-binder
plaquette-trace polynomials. -/
def radiusZeroEdgeTouchingDoubleCubeFaceMajorCoefficientNetwork :
    ComplexRatPoly :=
  complexRatPolyBoolSum 48 (fun assignment =>
    complexRatPolyProduct
      (radiusZeroEdgeTouchingDoubleCubeFaceMajorCoefficientWord assignment))

theorem finiteProductHaarComplex_radiusZeroEdgeTouchingDoubleCubeFaceMajorCoefficientNetwork_eq_contractedSum :
    RationalComplexEqv
      (finiteProductHaarComplex
        (adjacentEvenActiveLinks 0).length
        radiusZeroEdgeTouchingDoubleCubeFaceMajorCoefficientNetwork)
      (rationalComplexBoolSum 48
        radiusZeroEdgeTouchingDoubleCubeContractedValue) :=
  rationalComplexEqv_trans
    (finiteProductHaarComplex_boolSum
      (adjacentEvenActiveLinks 0).length 48
      (fun assignment =>
        complexRatPolyProduct
          (radiusZeroEdgeTouchingDoubleCubeFaceMajorCoefficientWord
            assignment)))
    (rationalComplexBoolSum_congr 48 (fun assignment =>
      finiteProductHaarComplex_radiusZeroEdgeTouchingDoubleCubeFaceMajorCoefficientProduct_eq_contractedValue
        assignment))

/-- Exact Haar value of the fully wired face-major coefficient network. -/
theorem finiteProductHaarComplex_radiusZeroEdgeTouchingDoubleCubeFaceMajorCoefficientNetwork_exact :
    RationalComplexEqv
      (finiteProductHaarComplex
        (adjacentEvenActiveLinks 0).length
        radiusZeroEdgeTouchingDoubleCubeFaceMajorCoefficientNetwork)
      (Q'.mkPos 1 256 (by decide), 0) :=
  rationalComplexEqv_trans
    finiteProductHaarComplex_radiusZeroEdgeTouchingDoubleCubeFaceMajorCoefficientNetwork_eq_contractedSum
    rationalComplexBoolSum_radiusZeroEdgeTouchingDoubleCubeContractedValue_exact

#print axioms rationalComplexThreeBoolBind_equalityTriangleLocal_mul
#print axioms rationalComplexBoolSum_triangleCompression
#print axioms radiusZeroEdgeTouchingDoubleCubeSharedProjector_repeatEachBoolThree
#print axioms rationalComplexThreeBoolBind_const
#print axioms rationalComplexBoolSum_const_six
#print axioms twoSheetComponentProjector_fourBoolSum
#print axioms rationalComplexBoolSum_twoSheetComponentProjector
#print axioms radiusZeroEdgeTouchingDoubleCubeContractedValue_eqv_resolved
#print axioms rationalComplexBoolSum_radiusZeroEdgeTouchingDoubleCubeResolvedDeltaValue_exact
#print axioms rationalComplexBoolSum_radiusZeroEdgeTouchingDoubleCubeContractedValue_exact
#print axioms finiteProductHaarComplex_radiusZeroEdgeTouchingDoubleCubeFaceMajorCoefficientNetwork_eq_contractedSum
#print axioms finiteProductHaarComplex_radiusZeroEdgeTouchingDoubleCubeFaceMajorCoefficientNetwork_exact

end YMGap.Continuum.SU2QuaternionEdgeTouchingDoubleCubeBooleanDeltaResolution
