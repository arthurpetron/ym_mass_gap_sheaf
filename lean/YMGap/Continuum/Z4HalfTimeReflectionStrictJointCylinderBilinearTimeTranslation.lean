/-
# Polarized strict-cylinder reflection form and geometric time translation

The positive strict-cylinder quadratic is polarized here into an exact
symmetric bilinear form.  The algebra is first proved for an arbitrary finite
joint kernel, then applied after pullback to the complete half-support space.
The resulting constructive-real form descends in both arguments through the
semantic cylinder-vector relation.

The final section equips presentations with the already machine-checked
nonnegative Euclidean-time translation of canonical roots.  We prove exact
covariance with vector addition and rational scaling.  No invariance of the
reflection form, contraction, transfer-semigroup, or GNS claim is made here.
-/

import YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderSeminorm
import YMGap.Continuum.Z4FiniteCylinderTimeTranslation
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBilinearTimeTranslation

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

open YMGap.Constructive
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability
open YMGap.Continuum.Z4FiniteCylinderTimeTranslation
open YMGap.Continuum.Z4HalfTimeReflectionLocalSupportPushforward
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPartition
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCenteredLimit
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderPresentation
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointGramLimitPositivity
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointMarkedCylinder
open YMGap.Continuum.Z4HalfTimeReflectionStrictQueryGeometry
open YMGap.Continuum.Z4HalfTimeReflectionSupportPushforwardGram
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Q'.mkPos_num, Q'.mkPos_den,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.zero_add, Int.add_zero]; ac_rfl))

/-! ## 1. Exact finite-kernel polarization algebra -/

/-- The exact rational `1/4` used in real polarization. -/
def strictJointPolarizationQuarter : Q' :=
  Q'.mkPos 1 4 (by decide)

private def polarizationIntegrandL : PolyExpr :=
  let scale := PolyExpr.var 0
  let a := PolyExpr.var 1
  let b := PolyExpr.var 2
  let c := PolyExpr.var 3
  let d := PolyExpr.var 4
  let kernel := PolyExpr.var 5
  .mul scale
    (.add
      (.mul (.mul (.add a b) (.add c d)) kernel)
      (.neg (.mul (.mul (.add a (.neg b))
        (.add c (.neg d))) kernel)))

private def polarizationIntegrandR : PolyExpr :=
  let scale := PolyExpr.var 0
  let a := PolyExpr.var 1
  let b := PolyExpr.var 2
  let c := PolyExpr.var 3
  let d := PolyExpr.var 4
  let kernel := PolyExpr.var 5
  .mul
    (.mul (.add scale scale)
      (.add (.mul a d) (.mul b c))) kernel

private theorem polarizationIntegrand_normal :
    normalize polarizationIntegrandL =
      normalize polarizationIntegrandR := by
  decide

private theorem polarization_integrand_algebra
    (scale a b c d kernel : Q') :
    scale *
        ((((a + b) * (c + d)) * kernel) +
          (-(((a + (-b)) * (c + (-d))) * kernel))) ≈
      (((scale + scale) * ((a * d) + (b * c))) * kernel) := by
  let ρ : Nat → Q' := fun n =>
    if n = 0 then scale else if n = 1 then a else if n = 2 then b
    else if n = 3 then c else if n = 4 then d else kernel
  have h := poly_identity_of_normal_eq
    polarizationIntegrandL polarizationIntegrandR
    polarizationIntegrand_normal ρ
  simpa [polarizationIntegrandL, polarizationIntegrandR,
    RingNormaliser.eval, ρ] using h

/-- Move a common scale through the difference of two finite sums. -/
theorem listQSum_scaled_sub_eqv {A : Type}
    (scale : Q') (left right : A → Q') :
    ∀ xs : List A,
      scale * (listQSum left xs + (-listQSum right xs)) ≈
        listQSum
          (fun item => scale * (left item + (-right item))) xs
  | [] => by
      change scale * ((0 : Q') + (-0)) ≈ 0
      rw [show (-(0 : Q')) = 0 from rfl, Q'.zero_add' 0]
      exact Q'.mul_zero_eqv scale
  | item :: rest => by
      change
        scale *
            ((left item + listQSum left rest) +
              (-(right item + listQSum right rest))) ≈
          scale * (left item + (-right item)) +
            listQSum
              (fun target =>
                scale * (left target + (-right target))) rest
      have hsplit :
          scale *
              ((left item + listQSum left rest) +
                (-(right item + listQSum right rest))) ≈
            scale * (left item + (-right item)) +
              scale *
                (listQSum left rest + (-listQSum right rest)) := by
        ring_qeqv
      exact Q'.eqv_trans _ _ _ hsplit
        (Q'.add_eqv_congr_left _ _ _
          (listQSum_scaled_sub_eqv scale left right rest))

/-- The symmetric cross form represented by an arbitrary finite joint
kernel.  The factor is written as `1/4 + 1/4`, so the polarization theorem
needs no division or field normalization tactic. -/
def finiteJointPolarizedBilinear {State : Type}
    (states : List State)
    (leftCoefficient rightCoefficient : State → Q')
    (joint : State → State → Q') : Q' :=
  listQSum (fun left =>
    listQSum (fun right =>
      ((strictJointPolarizationQuarter +
          strictJointPolarizationQuarter) *
        ((leftCoefficient left * rightCoefficient right) +
          (rightCoefficient left * leftCoefficient right))) *
        joint left right) states) states

/-- Exact real-polarization identity for every finite joint kernel, without
assuming that the kernel is symmetric. -/
theorem finiteJointQuadratic_polarization
    {State : Type} (states : List State)
    (leftCoefficient rightCoefficient : State → Q')
    (joint : State → State → Q') :
    strictJointPolarizationQuarter *
        (finiteJointQuadratic states
            (fun state => leftCoefficient state + rightCoefficient state)
            joint +
          (-finiteJointQuadratic states
            (fun state => leftCoefficient state +
              (-rightCoefficient state)) joint)) ≈
      finiteJointPolarizedBilinear states
        leftCoefficient rightCoefficient joint := by
  unfold finiteJointQuadratic finiteJointPolarizedBilinear
  refine Q'.eqv_trans _ _ _
    (listQSum_scaled_sub_eqv strictJointPolarizationQuarter
      (fun left => listQSum
        (fun right =>
          (((leftCoefficient left + rightCoefficient left) *
              (leftCoefficient right + rightCoefficient right)) *
            joint left right)) states)
      (fun left => listQSum
        (fun right =>
          (((leftCoefficient left + (-rightCoefficient left)) *
              (leftCoefficient right + (-rightCoefficient right))) *
            joint left right)) states)
      states) ?_
  apply listQSum_congr_on
  intro left hleft
  refine Q'.eqv_trans _ _ _
    (listQSum_scaled_sub_eqv strictJointPolarizationQuarter
      (fun right =>
        (((leftCoefficient left + rightCoefficient left) *
            (leftCoefficient right + rightCoefficient right)) *
          joint left right))
      (fun right =>
        (((leftCoefficient left + (-rightCoefficient left)) *
            (leftCoefficient right + (-rightCoefficient right))) *
          joint left right)) states) ?_
  apply listQSum_congr_on
  intro right hright
  exact polarization_integrand_algebra
    strictJointPolarizationQuarter
    (leftCoefficient left) (rightCoefficient left)
    (leftCoefficient right) (rightCoefficient right)
    (joint left right)

theorem finiteJointPolarizedBilinear_symm
    {State : Type} (states : List State)
    (leftCoefficient rightCoefficient : State → Q')
    (joint : State → State → Q') :
    finiteJointPolarizedBilinear states
        leftCoefficient rightCoefficient joint ≈
      finiteJointPolarizedBilinear states
        rightCoefficient leftCoefficient joint := by
  unfold finiteJointPolarizedBilinear
  apply listQSum_congr_on
  intro left hleft
  apply listQSum_congr_on
  intro right hright
  unfold strictJointPolarizationQuarter
  ring_qeqv

theorem finiteJointPolarizedBilinear_self
    {State : Type} (states : List State)
    (coefficient : State → Q')
    (joint : State → State → Q') :
    finiteJointPolarizedBilinear states
        coefficient coefficient joint ≈
      finiteJointQuadratic states coefficient joint := by
  unfold finiteJointPolarizedBilinear finiteJointQuadratic
  apply listQSum_congr_on
  intro left hleft
  apply listQSum_congr_on
  intro right hright
  let product := coefficient left * coefficient right
  have hquarter :
      strictJointPolarizationQuarter + strictJointPolarizationQuarter ≈
        HalfPow.half := by
    decide
  have hscale :
      (strictJointPolarizationQuarter + strictJointPolarizationQuarter) *
          (product + product) ≈
        HalfPow.half * (product + product) :=
    Q'.mul_eqv_congr_right _ _ _ hquarter
  have hdouble :
      HalfPow.half * (product + product) ≈ product :=
    Q'.eqv_trans _ _ _
      (Q'.mul_add_eqv HalfPow.half product product)
      (ExpNeg.two_halves product)
  exact Q'.mul_eqv_congr_right _ _ _
    (Q'.eqv_trans _ _ _ hscale hdouble)

theorem finiteJointPolarizedBilinear_coefficient_eqv
    {State : Type} (states : List State)
    (leftCoefficient leftCoefficient'
      rightCoefficient rightCoefficient' : State → Q')
    (joint : State → State → Q')
    (hleft : ∀ state, state ∈ states →
      leftCoefficient state ≈ leftCoefficient' state)
    (hright : ∀ state, state ∈ states →
      rightCoefficient state ≈ rightCoefficient' state) :
    finiteJointPolarizedBilinear states
        leftCoefficient rightCoefficient joint ≈
      finiteJointPolarizedBilinear states
        leftCoefficient' rightCoefficient' joint := by
  unfold finiteJointPolarizedBilinear
  apply listQSum_congr_on
  intro left hleftMem
  apply listQSum_congr_on
  intro right hrightMem
  have hfirst :
      leftCoefficient left * rightCoefficient right ≈
        leftCoefficient' left * rightCoefficient' right :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (hleft left hleftMem))
      (Q'.mul_eqv_congr_left _ _ _ (hright right hrightMem))
  have hsecond :
      rightCoefficient left * leftCoefficient right ≈
        rightCoefficient' left * leftCoefficient' right :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (hright left hleftMem))
      (Q'.mul_eqv_congr_left _ _ _ (hleft right hrightMem))
  have hcross := Q'.add_eqv_congr' hfirst hsecond
  have hscaled :
      (strictJointPolarizationQuarter + strictJointPolarizationQuarter) *
          ((leftCoefficient left * rightCoefficient right) +
            (rightCoefficient left * leftCoefficient right)) ≈
        (strictJointPolarizationQuarter + strictJointPolarizationQuarter) *
          ((leftCoefficient' left * rightCoefficient' right) +
            (rightCoefficient' left * leftCoefficient' right)) :=
    Q'.mul_eqv_congr_left _ _ _ hcross
  exact Q'.mul_eqv_congr_right _ _ _ hscaled

theorem finiteJointPolarizedBilinear_add_left
    {State : Type} (states : List State)
    (first second rightCoefficient : State → Q')
    (joint : State → State → Q') :
    finiteJointPolarizedBilinear states
        (fun state => first state + second state)
        rightCoefficient joint ≈
      finiteJointPolarizedBilinear states first rightCoefficient joint +
        finiteJointPolarizedBilinear states second rightCoefficient joint := by
  unfold finiteJointPolarizedBilinear
  refine Q'.eqv_trans _ _ _ ?_ (listQSum_add _ _ states)
  apply listQSum_congr_on
  intro left hleft
  refine Q'.eqv_trans _ _ _ ?_ (listQSum_add _ _ states)
  apply listQSum_congr_on
  intro right hright
  ring_qeqv

theorem finiteJointPolarizedBilinear_smul_left
    {State : Type} (states : List State) (scalar : Q')
    (leftCoefficient rightCoefficient : State → Q')
    (joint : State → State → Q') :
    finiteJointPolarizedBilinear states
        (fun state => scalar * leftCoefficient state)
        rightCoefficient joint ≈
      scalar * finiteJointPolarizedBilinear states
        leftCoefficient rightCoefficient joint := by
  unfold finiteJointPolarizedBilinear
  refine Q'.eqv_trans _ _ _ ?_
    (listQSum_mul_left scalar _ states)
  apply listQSum_congr_on
  intro left hleft
  refine Q'.eqv_trans _ _ _ ?_
    (listQSum_mul_left scalar _ states)
  apply listQSum_congr_on
  intro right hright
  ring_qeqv

/-! ## 2. Normalized complete-support bilinear form -/

def centralNormalizedSupportReflectionBilinear
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff half : Nat)
    (leftCoefficient rightCoefficient : List Nat → Q') : Q' :=
  Q'.divPos
    (finiteJointPolarizedBilinear
      (centralHalfSupportSpace half)
      leftCoefficient rightCoefficient
      (centralSupportReflectedKernel coupling cutoff half))
    (slabParametricKPhysicalPartition coupling cutoff
      (centralExtent half))
    (slabParametricKPhysicalPartition_pos hcoupling cutoff
      (centralExtent half))

theorem centralNormalizedSupportReflectionQuadratic_polarization
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff half : Nat)
    (leftCoefficient rightCoefficient : List Nat → Q') :
    strictJointPolarizationQuarter *
        (centralNormalizedSupportReflectionQuadratic
            coupling hcoupling cutoff half
            (fun support =>
              leftCoefficient support + rightCoefficient support) +
          (-centralNormalizedSupportReflectionQuadratic
            coupling hcoupling cutoff half
            (fun support =>
              leftCoefficient support + (-rightCoefficient support)))) ≈
      centralNormalizedSupportReflectionBilinear
        coupling hcoupling cutoff half
          leftCoefficient rightCoefficient := by
  unfold centralNormalizedSupportReflectionQuadratic
    centralSupportReflectionQuadratic
    centralNormalizedSupportReflectionBilinear Q'.divPos
  have hpolarization := finiteJointQuadratic_polarization
    (centralHalfSupportSpace half) leftCoefficient rightCoefficient
    (centralSupportReflectedKernel coupling cutoff half)
  refine Q'.eqv_trans _ _ _ ?_
    (Q'.mul_eqv_congr_right _ _ _ hpolarization)
  ring_qeqv

theorem centralNormalizedSupportReflectionBilinear_symm
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff half : Nat)
    (leftCoefficient rightCoefficient : List Nat → Q') :
    centralNormalizedSupportReflectionBilinear
        coupling hcoupling cutoff half
          leftCoefficient rightCoefficient ≈
      centralNormalizedSupportReflectionBilinear
        coupling hcoupling cutoff half
          rightCoefficient leftCoefficient := by
  unfold centralNormalizedSupportReflectionBilinear Q'.divPos
  apply Q'.mul_eqv_congr_right
  exact finiteJointPolarizedBilinear_symm
    (centralHalfSupportSpace half) leftCoefficient rightCoefficient
    (centralSupportReflectedKernel coupling cutoff half)

theorem centralNormalizedSupportReflectionBilinear_self
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff half : Nat) (coefficient : List Nat → Q') :
    centralNormalizedSupportReflectionBilinear
        coupling hcoupling cutoff half coefficient coefficient ≈
      centralNormalizedSupportReflectionQuadratic
        coupling hcoupling cutoff half coefficient := by
  unfold centralNormalizedSupportReflectionBilinear
    centralNormalizedSupportReflectionQuadratic
    centralSupportReflectionQuadratic Q'.divPos
  apply Q'.mul_eqv_congr_right
  exact finiteJointPolarizedBilinear_self
    (centralHalfSupportSpace half) coefficient
    (centralSupportReflectedKernel coupling cutoff half)

theorem centralNormalizedSupportReflectionBilinear_coefficient_eqv
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff half : Nat)
    (leftCoefficient leftCoefficient'
      rightCoefficient rightCoefficient' : List Nat → Q')
    (hleft : ∀ support,
      leftCoefficient support ≈ leftCoefficient' support)
    (hright : ∀ support,
      rightCoefficient support ≈ rightCoefficient' support) :
    centralNormalizedSupportReflectionBilinear
        coupling hcoupling cutoff half
          leftCoefficient rightCoefficient ≈
      centralNormalizedSupportReflectionBilinear
        coupling hcoupling cutoff half
          leftCoefficient' rightCoefficient' := by
  unfold centralNormalizedSupportReflectionBilinear Q'.divPos
  apply Q'.mul_eqv_congr_right
  exact finiteJointPolarizedBilinear_coefficient_eqv
    (centralHalfSupportSpace half)
    leftCoefficient leftCoefficient'
    rightCoefficient rightCoefficient'
    (centralSupportReflectedKernel coupling cutoff half)
    (fun support _ => hleft support)
    (fun support _ => hright support)

theorem centralNormalizedSupportReflectionBilinear_add_left
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff half : Nat)
    (first second rightCoefficient : List Nat → Q') :
    centralNormalizedSupportReflectionBilinear
        coupling hcoupling cutoff half
        (fun support => first support + second support)
        rightCoefficient ≈
      centralNormalizedSupportReflectionBilinear
          coupling hcoupling cutoff half first rightCoefficient +
        centralNormalizedSupportReflectionBilinear
          coupling hcoupling cutoff half second rightCoefficient := by
  unfold centralNormalizedSupportReflectionBilinear Q'.divPos
  have hadd := finiteJointPolarizedBilinear_add_left
    (centralHalfSupportSpace half) first second rightCoefficient
    (centralSupportReflectedKernel coupling cutoff half)
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ hadd) ?_
  ring_qeqv

theorem centralNormalizedSupportReflectionBilinear_smul_left
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff half : Nat) (scalar : Q')
    (leftCoefficient rightCoefficient : List Nat → Q') :
    centralNormalizedSupportReflectionBilinear
        coupling hcoupling cutoff half
        (fun support => scalar * leftCoefficient support)
        rightCoefficient ≈
      scalar * centralNormalizedSupportReflectionBilinear
        coupling hcoupling cutoff half
          leftCoefficient rightCoefficient := by
  unfold centralNormalizedSupportReflectionBilinear Q'.divPos
  have hsmul := finiteJointPolarizedBilinear_smul_left
    (centralHalfSupportSpace half) scalar
    leftCoefficient rightCoefficient
    (centralSupportReflectedKernel coupling cutoff half)
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ hsmul) ?_
  ring_qeqv

theorem centralNormalizedSupportReflectionBilinear_add_right
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff half : Nat)
    (leftCoefficient first second : List Nat → Q') :
    centralNormalizedSupportReflectionBilinear
        coupling hcoupling cutoff half leftCoefficient
        (fun support => first support + second support) ≈
      centralNormalizedSupportReflectionBilinear
          coupling hcoupling cutoff half leftCoefficient first +
        centralNormalizedSupportReflectionBilinear
          coupling hcoupling cutoff half leftCoefficient second := by
  have hsymm := centralNormalizedSupportReflectionBilinear_symm
    coupling hcoupling cutoff half leftCoefficient
    (fun support => first support + second support)
  have hadd := centralNormalizedSupportReflectionBilinear_add_left
    coupling hcoupling cutoff half first second leftCoefficient
  have hfirst := centralNormalizedSupportReflectionBilinear_symm
    coupling hcoupling cutoff half first leftCoefficient
  have hsecond := centralNormalizedSupportReflectionBilinear_symm
    coupling hcoupling cutoff half second leftCoefficient
  exact Q'.eqv_trans _ _ _ hsymm
    (Q'.eqv_trans _ _ _ hadd
      (Q'.add_eqv_congr' hfirst hsecond))

theorem centralNormalizedSupportReflectionBilinear_smul_right
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff half : Nat) (scalar : Q')
    (leftCoefficient rightCoefficient : List Nat → Q') :
    centralNormalizedSupportReflectionBilinear
        coupling hcoupling cutoff half leftCoefficient
        (fun support => scalar * rightCoefficient support) ≈
      scalar * centralNormalizedSupportReflectionBilinear
        coupling hcoupling cutoff half
          leftCoefficient rightCoefficient := by
  have hsymm := centralNormalizedSupportReflectionBilinear_symm
    coupling hcoupling cutoff half leftCoefficient
    (fun support => scalar * rightCoefficient support)
  have hsmul := centralNormalizedSupportReflectionBilinear_smul_left
    coupling hcoupling cutoff half scalar rightCoefficient leftCoefficient
  have hright := centralNormalizedSupportReflectionBilinear_symm
    coupling hcoupling cutoff half rightCoefficient leftCoefficient
  exact Q'.eqv_trans _ _ _ hsymm
    (Q'.eqv_trans _ _ _ hsmul
      (Q'.mul_eqv_congr_left scalar _ _ hright))

/-! ## 3. The constructive-real cylinder bilinear form -/

private theorem neg_one_mul_eqv_local (value : Q') :
    ((-1 : Q') * value) ≈ -value := by
  refine Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv (1 : Q') value) ?_
  exact Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv value)

/-- Direct complete-support approximation to the polarized form. -/
def strictJointCylinderReflectionBilinearSequence
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    {base : Nat} (left right : StrictJointCylinderVector base)
    (stage : Nat) : Q' :=
  centralNormalizedSupportReflectionBilinear
    coupling hcoupling
    (centralStrictJointCenteredStageCutoff base stage)
    (strictQueryBase base + stage)
    (centralLocalSupportCoefficient
      (centralStrictLocalQueryCode
        (strictQueryBase base + stage) base left.roots)
      left.coefficient)
    (centralLocalSupportCoefficient
      (centralStrictLocalQueryCode
        (strictQueryBase base + stage) base right.roots)
      right.coefficient)

/-- The limiting symmetric bilinear reflection form, defined by exact real
polarization of the already constructed positive quadratic. -/
def strictJointCylinderReflectionBilinear
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} (left right : StrictJointCylinderVector base) : CReal :=
  CReal.mul (CReal.ofQ' strictJointPolarizationQuarter)
    (CReal.add
      ((left.add right).reflectionQuadratic hcoupling hle)
      (CReal.neg
        ((left.add (right.smul (-1))).reflectionQuadratic
          hcoupling hle)))

@[simp] theorem strictJointCylinderReflectionBilinear_approx
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base stage : Nat} (left right : StrictJointCylinderVector base) :
    (strictJointCylinderReflectionBilinear hcoupling hle left right).approx stage =
      strictJointPolarizationQuarter *
        (centralNormalizedStrictJointFixedQuadraticSequence
            coupling hcoupling base
            (left.add right).roots
            (left.add right).coefficient stage +
          (-centralNormalizedStrictJointFixedQuadraticSequence
            coupling hcoupling base
            (left.add (right.smul (-1))).roots
            (left.add (right.smul (-1))).coefficient stage)) := rfl

/-- The CReal polarization approximation is exactly the direct symmetric
complete-support bilinear form at every stage. -/
theorem StrictJointCylinderVector.reflectionBilinear_approx_eqv_sequence
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base stage : Nat} (left right : StrictJointCylinderVector base) :
    (strictJointCylinderReflectionBilinear hcoupling hle left right).approx stage ≈
      strictJointCylinderReflectionBilinearSequence
        coupling hcoupling left right stage := by
  let radius := strictQueryBase base + stage
  let cutoff := centralStrictJointCenteredStageCutoff base stage
  let leftCoefficient := centralLocalSupportCoefficient
    (centralStrictLocalQueryCode radius base left.roots)
    left.coefficient
  let rightCoefficient := centralLocalSupportCoefficient
    (centralStrictLocalQueryCode radius base right.roots)
    right.coefficient
  let plus := left.add right
  let minus := left.add (right.smul (-1))
  have hplusGram :=
    centralNormalizedStrictJointFixedQuadraticSequence_eqv_supportGram
      coupling hcoupling base plus.roots plus.coefficient stage
  have hplusCoefficient :
      ∀ support,
        centralLocalSupportCoefficient
            (centralStrictLocalQueryCode radius base plus.roots)
            plus.coefficient support ≈
          leftCoefficient support + rightCoefficient support := by
    intro support
    exact StrictJointCylinderVector.add_coefficient_code
      left right radius support
  have hplusCongr :=
    centralNormalizedSupportReflectionQuadratic_coefficient_eqv
      coupling hcoupling cutoff radius
      (centralLocalSupportCoefficient
        (centralStrictLocalQueryCode radius base plus.roots)
        plus.coefficient)
      (fun support => leftCoefficient support + rightCoefficient support)
      hplusCoefficient
  have hplus := Q'.eqv_trans _ _ _ hplusGram hplusCongr
  have hminusGram :=
    centralNormalizedStrictJointFixedQuadraticSequence_eqv_supportGram
      coupling hcoupling base minus.roots minus.coefficient stage
  have hminusCoefficient :
      ∀ support,
        centralLocalSupportCoefficient
            (centralStrictLocalQueryCode radius base minus.roots)
            minus.coefficient support ≈
          leftCoefficient support + (-rightCoefficient support) := by
    intro support
    have hadd := StrictJointCylinderVector.add_coefficient_code
      left (right.smul (-1)) radius support
    refine Q'.eqv_trans _ _ _ hadd ?_
    exact Q'.add_eqv_congr_left _ _ _
      (neg_one_mul_eqv_local (rightCoefficient support))
  have hminusCongr :=
    centralNormalizedSupportReflectionQuadratic_coefficient_eqv
      coupling hcoupling cutoff radius
      (centralLocalSupportCoefficient
        (centralStrictLocalQueryCode radius base minus.roots)
        minus.coefficient)
      (fun support => leftCoefficient support + (-rightCoefficient support))
      hminusCoefficient
  have hminus := Q'.eqv_trans _ _ _ hminusGram hminusCongr
  have hdifference := Q'.add_eqv_congr' hplus
    (Q'.neg_eqv_congr _ _ hminus)
  have hscaled := Q'.mul_eqv_congr_left
    strictJointPolarizationQuarter _ _ hdifference
  refine Q'.eqv_trans _ _ _ hscaled ?_
  simpa only [strictJointCylinderReflectionBilinearSequence,
    strictJointCylinderReflectionBilinear_approx,
    radius, cutoff, leftCoefficient, rightCoefficient, plus, minus] using
      (centralNormalizedSupportReflectionQuadratic_polarization
        coupling hcoupling cutoff radius leftCoefficient rightCoefficient)

theorem StrictJointCylinderVector.reflectionBilinear_approx_eqv_of_equivalent
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base stage : Nat}
    {left left' right right' : StrictJointCylinderVector base}
    (hleft : StrictJointCylinderVectorEquivalent left left')
    (hright : StrictJointCylinderVectorEquivalent right right') :
    (strictJointCylinderReflectionBilinear hcoupling hle left right).approx stage ≈
      (strictJointCylinderReflectionBilinear
        hcoupling hle left' right').approx stage := by
  let radius := strictQueryBase base + stage
  have hdirect :=
    centralNormalizedSupportReflectionBilinear_coefficient_eqv
      coupling hcoupling
      (centralStrictJointCenteredStageCutoff base stage) radius
      (centralLocalSupportCoefficient
        (centralStrictLocalQueryCode radius base left.roots)
        left.coefficient)
      (centralLocalSupportCoefficient
        (centralStrictLocalQueryCode radius base left'.roots)
        left'.coefficient)
      (centralLocalSupportCoefficient
        (centralStrictLocalQueryCode radius base right.roots)
        right.coefficient)
      (centralLocalSupportCoefficient
        (centralStrictLocalQueryCode radius base right'.roots)
        right'.coefficient)
      (fun support => hleft radius support)
      (fun support => hright radius support)
  exact Q'.eqv_trans _ _ _
    (StrictJointCylinderVector.reflectionBilinear_approx_eqv_sequence
      hcoupling hle left right)
    (Q'.eqv_trans _ _ _ hdirect
      (Q'.eqv_symm
        (StrictJointCylinderVector.reflectionBilinear_approx_eqv_sequence
          hcoupling hle left' right')))

/-- The bilinear reflection form is presentation-independent in both
arguments. -/
theorem StrictJointCylinderVector.reflectionBilinear_equiv
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat}
    {left left' right right' : StrictJointCylinderVector base}
    (hleft : StrictJointCylinderVectorEquivalent left left')
    (hright : StrictJointCylinderVectorEquivalent right right') :
    CReal.Equiv
      (strictJointCylinderReflectionBilinear hcoupling hle left right)
      (strictJointCylinderReflectionBilinear hcoupling hle left' right') := by
  intro epsilon hepsilon
  refine ⟨0, fun stage _ => ?_⟩
  have heqv :=
    StrictJointCylinderVector.reflectionBilinear_approx_eqv_of_equivalent
      hcoupling hle (stage := stage) hleft hright
  have hepsilonNonnegative : (0 : Q') ≤ epsilon := Q'.le_of_lt hepsilon
  exact ⟨
    Q'.le_trans' _ _ _ (Q'.le_of_eqv heqv)
      (Q'.add_le_self_of_nonneg _ _ hepsilonNonnegative),
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv heqv)
      (Q'.add_le_self_of_nonneg _ _ hepsilonNonnegative)⟩

theorem StrictJointCylinderVector.reflectionBilinear_symm
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} (left right : StrictJointCylinderVector base) :
    CReal.Equiv
      (strictJointCylinderReflectionBilinear hcoupling hle left right)
      (strictJointCylinderReflectionBilinear hcoupling hle right left) := by
  intro epsilon hepsilon
  refine ⟨0, fun stage _ => ?_⟩
  have hleft :=
    StrictJointCylinderVector.reflectionBilinear_approx_eqv_sequence
      hcoupling hle (stage := stage) left right
  have hsymm := centralNormalizedSupportReflectionBilinear_symm
    coupling hcoupling
    (centralStrictJointCenteredStageCutoff base stage)
    (strictQueryBase base + stage)
    (centralLocalSupportCoefficient
      (centralStrictLocalQueryCode
        (strictQueryBase base + stage) base left.roots)
      left.coefficient)
    (centralLocalSupportCoefficient
      (centralStrictLocalQueryCode
        (strictQueryBase base + stage) base right.roots)
      right.coefficient)
  have hright :=
    StrictJointCylinderVector.reflectionBilinear_approx_eqv_sequence
      hcoupling hle (stage := stage) right left
  have heqv := Q'.eqv_trans _ _ _ hleft
    (Q'.eqv_trans _ _ _ hsymm (Q'.eqv_symm hright))
  have hepsilonNonnegative : (0 : Q') ≤ epsilon := Q'.le_of_lt hepsilon
  exact ⟨
    Q'.le_trans' _ _ _ (Q'.le_of_eqv heqv)
      (Q'.add_le_self_of_nonneg _ _ hepsilonNonnegative),
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv heqv)
      (Q'.add_le_self_of_nonneg _ _ hepsilonNonnegative)⟩

theorem strictJointCylinderReflectionBilinear_approx_self_eqv
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base stage : Nat} (vector : StrictJointCylinderVector base) :
    (strictJointCylinderReflectionBilinear
        hcoupling hle vector vector).approx stage ≈
      (vector.reflectionQuadratic hcoupling hle).approx stage := by
  have hbilinear :=
    StrictJointCylinderVector.reflectionBilinear_approx_eqv_sequence
      hcoupling hle (stage := stage) vector vector
  have hself := centralNormalizedSupportReflectionBilinear_self
    coupling hcoupling
    (centralStrictJointCenteredStageCutoff base stage)
    (strictQueryBase base + stage)
    (centralLocalSupportCoefficient
      (centralStrictLocalQueryCode
        (strictQueryBase base + stage) base vector.roots)
      vector.coefficient)
  have hquadratic :=
    centralNormalizedStrictJointFixedQuadraticSequence_eqv_supportGram
      coupling hcoupling base vector.roots vector.coefficient stage
  exact Q'.eqv_trans _ _ _ hbilinear
    (Q'.eqv_trans _ _ _ hself (Q'.eqv_symm hquadratic))

/-- The diagonal of the polarized form recovers the original limiting
reflection quadratic. -/
theorem strictJointCylinderReflectionBilinear_self
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} (vector : StrictJointCylinderVector base) :
    CReal.Equiv
      (strictJointCylinderReflectionBilinear hcoupling hle vector vector)
      (vector.reflectionQuadratic hcoupling hle) := by
  intro epsilon hepsilon
  refine ⟨0, fun stage _ => ?_⟩
  have heqv := strictJointCylinderReflectionBilinear_approx_self_eqv
    hcoupling hle (stage := stage) vector
  have hepsilonNonnegative : (0 : Q') ≤ epsilon := Q'.le_of_lt hepsilon
  exact ⟨
    Q'.le_trans' _ _ _ (Q'.le_of_eqv heqv)
      (Q'.add_le_self_of_nonneg _ _ hepsilonNonnegative),
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv heqv)
      (Q'.add_le_self_of_nonneg _ _ hepsilonNonnegative)⟩

/-! ## 4. Exact additivity and rational homogeneity -/

theorem strictJointCylinderReflectionBilinear_approx_add_left_eqv
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base stage : Nat}
    (first second right : StrictJointCylinderVector base) :
    (strictJointCylinderReflectionBilinear hcoupling hle
        (first.add second) right).approx stage ≈
      (CReal.add
        (strictJointCylinderReflectionBilinear hcoupling hle first right)
        (strictJointCylinderReflectionBilinear
          hcoupling hle second right)).approx stage := by
  let radius := strictQueryBase base + stage
  let cutoff := centralStrictJointCenteredStageCutoff base stage
  let firstCoefficient := centralLocalSupportCoefficient
    (centralStrictLocalQueryCode radius base first.roots)
    first.coefficient
  let secondCoefficient := centralLocalSupportCoefficient
    (centralStrictLocalQueryCode radius base second.roots)
    second.coefficient
  let rightCoefficient := centralLocalSupportCoefficient
    (centralStrictLocalQueryCode radius base right.roots)
    right.coefficient
  let combinedCoefficient := centralLocalSupportCoefficient
    (centralStrictLocalQueryCode radius base (first.add second).roots)
    (first.add second).coefficient
  have hcombined :=
    StrictJointCylinderVector.reflectionBilinear_approx_eqv_sequence
      hcoupling hle (stage := stage) (first.add second) right
  have hcombinedCoefficient : ∀ support,
      combinedCoefficient support ≈
        firstCoefficient support + secondCoefficient support := by
    intro support
    exact StrictJointCylinderVector.add_coefficient_code
      first second radius support
  have hcoefficient :=
    centralNormalizedSupportReflectionBilinear_coefficient_eqv
      coupling hcoupling cutoff radius
      combinedCoefficient
      (fun support => firstCoefficient support + secondCoefficient support)
      rightCoefficient rightCoefficient
      hcombinedCoefficient (fun support => Q'.eqv_refl _)
  have hadd := centralNormalizedSupportReflectionBilinear_add_left
    coupling hcoupling cutoff radius
    firstCoefficient secondCoefficient rightCoefficient
  have hfirst :=
    StrictJointCylinderVector.reflectionBilinear_approx_eqv_sequence
      hcoupling hle (stage := stage) first right
  have hsecond :=
    StrictJointCylinderVector.reflectionBilinear_approx_eqv_sequence
      hcoupling hle (stage := stage) second right
  have hcomponents := Q'.add_eqv_congr'
    (Q'.eqv_symm hfirst) (Q'.eqv_symm hsecond)
  exact Q'.eqv_trans _ _ _ hcombined
    (Q'.eqv_trans _ _ _ hcoefficient
      (Q'.eqv_trans _ _ _ hadd hcomponents))

/-- The descended reflection form is additive in its first argument. -/
theorem strictJointCylinderReflectionBilinear_add_left
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat}
    (first second right : StrictJointCylinderVector base) :
    CReal.Equiv
      (strictJointCylinderReflectionBilinear hcoupling hle
        (first.add second) right)
      (CReal.add
        (strictJointCylinderReflectionBilinear hcoupling hle first right)
        (strictJointCylinderReflectionBilinear
          hcoupling hle second right)) := by
  intro epsilon hepsilon
  refine ⟨0, fun stage _ => ?_⟩
  have heqv := strictJointCylinderReflectionBilinear_approx_add_left_eqv
    hcoupling hle (stage := stage) first second right
  have hepsilonNonnegative : (0 : Q') ≤ epsilon := Q'.le_of_lt hepsilon
  exact ⟨
    Q'.le_trans' _ _ _ (Q'.le_of_eqv heqv)
      (Q'.add_le_self_of_nonneg _ _ hepsilonNonnegative),
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv heqv)
      (Q'.add_le_self_of_nonneg _ _ hepsilonNonnegative)⟩

theorem strictJointCylinderReflectionBilinear_approx_smul_left_eqv
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base stage : Nat} (scalar : Q')
    (left right : StrictJointCylinderVector base) :
    (strictJointCylinderReflectionBilinear hcoupling hle
        (left.smul scalar) right).approx stage ≈
      (CReal.mul (CReal.ofQ' scalar)
        (strictJointCylinderReflectionBilinear
          hcoupling hle left right)).approx stage := by
  let radius := strictQueryBase base + stage
  let cutoff := centralStrictJointCenteredStageCutoff base stage
  let leftCoefficient := centralLocalSupportCoefficient
    (centralStrictLocalQueryCode radius base left.roots)
    left.coefficient
  let rightCoefficient := centralLocalSupportCoefficient
    (centralStrictLocalQueryCode radius base right.roots)
    right.coefficient
  have hscaled :=
    StrictJointCylinderVector.reflectionBilinear_approx_eqv_sequence
      hcoupling hle (stage := stage) (left.smul scalar) right
  have hsupport := centralNormalizedSupportReflectionBilinear_smul_left
    coupling hcoupling cutoff radius scalar leftCoefficient rightCoefficient
  have hleft :=
    StrictJointCylinderVector.reflectionBilinear_approx_eqv_sequence
      hcoupling hle (stage := stage) left right
  have hcomponent := Q'.mul_eqv_congr_left scalar _ _
    (Q'.eqv_symm hleft)
  exact Q'.eqv_trans _ _ _ hscaled
    (Q'.eqv_trans _ _ _ hsupport hcomponent)

/-- The descended reflection form is homogeneous over exact rationals in
its first argument. -/
theorem strictJointCylinderReflectionBilinear_smul_left
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} (scalar : Q')
    (left right : StrictJointCylinderVector base) :
    CReal.Equiv
      (strictJointCylinderReflectionBilinear hcoupling hle
        (left.smul scalar) right)
      (CReal.mul (CReal.ofQ' scalar)
        (strictJointCylinderReflectionBilinear
          hcoupling hle left right)) := by
  intro epsilon hepsilon
  refine ⟨0, fun stage _ => ?_⟩
  have heqv := strictJointCylinderReflectionBilinear_approx_smul_left_eqv
    hcoupling hle (stage := stage) scalar left right
  have hepsilonNonnegative : (0 : Q') ≤ epsilon := Q'.le_of_lt hepsilon
  exact ⟨
    Q'.le_trans' _ _ _ (Q'.le_of_eqv heqv)
      (Q'.add_le_self_of_nonneg _ _ hepsilonNonnegative),
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv heqv)
      (Q'.add_le_self_of_nonneg _ _ hepsilonNonnegative)⟩

theorem strictJointCylinderReflectionBilinear_approx_add_right_eqv
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base stage : Nat}
    (left first second : StrictJointCylinderVector base) :
    (strictJointCylinderReflectionBilinear hcoupling hle
        left (first.add second)).approx stage ≈
      (CReal.add
        (strictJointCylinderReflectionBilinear hcoupling hle left first)
        (strictJointCylinderReflectionBilinear
          hcoupling hle left second)).approx stage := by
  let radius := strictQueryBase base + stage
  let cutoff := centralStrictJointCenteredStageCutoff base stage
  let leftCoefficient := centralLocalSupportCoefficient
    (centralStrictLocalQueryCode radius base left.roots)
    left.coefficient
  let firstCoefficient := centralLocalSupportCoefficient
    (centralStrictLocalQueryCode radius base first.roots)
    first.coefficient
  let secondCoefficient := centralLocalSupportCoefficient
    (centralStrictLocalQueryCode radius base second.roots)
    second.coefficient
  let combinedCoefficient := centralLocalSupportCoefficient
    (centralStrictLocalQueryCode radius base (first.add second).roots)
    (first.add second).coefficient
  have hcombined :=
    StrictJointCylinderVector.reflectionBilinear_approx_eqv_sequence
      hcoupling hle (stage := stage) left (first.add second)
  have hcombinedCoefficient : ∀ support,
      combinedCoefficient support ≈
        firstCoefficient support + secondCoefficient support := by
    intro support
    exact StrictJointCylinderVector.add_coefficient_code
      first second radius support
  have hcoefficient :=
    centralNormalizedSupportReflectionBilinear_coefficient_eqv
      coupling hcoupling cutoff radius
      leftCoefficient leftCoefficient
      combinedCoefficient
      (fun support => firstCoefficient support + secondCoefficient support)
      (fun support => Q'.eqv_refl _) hcombinedCoefficient
  have hadd := centralNormalizedSupportReflectionBilinear_add_right
    coupling hcoupling cutoff radius
    leftCoefficient firstCoefficient secondCoefficient
  have hfirst :=
    StrictJointCylinderVector.reflectionBilinear_approx_eqv_sequence
      hcoupling hle (stage := stage) left first
  have hsecond :=
    StrictJointCylinderVector.reflectionBilinear_approx_eqv_sequence
      hcoupling hle (stage := stage) left second
  have hcomponents := Q'.add_eqv_congr'
    (Q'.eqv_symm hfirst) (Q'.eqv_symm hsecond)
  exact Q'.eqv_trans _ _ _ hcombined
    (Q'.eqv_trans _ _ _ hcoefficient
      (Q'.eqv_trans _ _ _ hadd hcomponents))

/-- The descended reflection form is additive in its second argument. -/
theorem strictJointCylinderReflectionBilinear_add_right
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat}
    (left first second : StrictJointCylinderVector base) :
    CReal.Equiv
      (strictJointCylinderReflectionBilinear hcoupling hle
        left (first.add second))
      (CReal.add
        (strictJointCylinderReflectionBilinear hcoupling hle left first)
        (strictJointCylinderReflectionBilinear
          hcoupling hle left second)) := by
  intro epsilon hepsilon
  refine ⟨0, fun stage _ => ?_⟩
  have heqv := strictJointCylinderReflectionBilinear_approx_add_right_eqv
    hcoupling hle (stage := stage) left first second
  have hepsilonNonnegative : (0 : Q') ≤ epsilon := Q'.le_of_lt hepsilon
  exact ⟨
    Q'.le_trans' _ _ _ (Q'.le_of_eqv heqv)
      (Q'.add_le_self_of_nonneg _ _ hepsilonNonnegative),
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv heqv)
      (Q'.add_le_self_of_nonneg _ _ hepsilonNonnegative)⟩

theorem strictJointCylinderReflectionBilinear_approx_smul_right_eqv
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base stage : Nat} (scalar : Q')
    (left right : StrictJointCylinderVector base) :
    (strictJointCylinderReflectionBilinear hcoupling hle
        left (right.smul scalar)).approx stage ≈
      (CReal.mul (CReal.ofQ' scalar)
        (strictJointCylinderReflectionBilinear
          hcoupling hle left right)).approx stage := by
  let radius := strictQueryBase base + stage
  let cutoff := centralStrictJointCenteredStageCutoff base stage
  let leftCoefficient := centralLocalSupportCoefficient
    (centralStrictLocalQueryCode radius base left.roots)
    left.coefficient
  let rightCoefficient := centralLocalSupportCoefficient
    (centralStrictLocalQueryCode radius base right.roots)
    right.coefficient
  have hscaled :=
    StrictJointCylinderVector.reflectionBilinear_approx_eqv_sequence
      hcoupling hle (stage := stage) left (right.smul scalar)
  have hsupport := centralNormalizedSupportReflectionBilinear_smul_right
    coupling hcoupling cutoff radius scalar leftCoefficient rightCoefficient
  have hright :=
    StrictJointCylinderVector.reflectionBilinear_approx_eqv_sequence
      hcoupling hle (stage := stage) left right
  have hcomponent := Q'.mul_eqv_congr_left scalar _ _
    (Q'.eqv_symm hright)
  exact Q'.eqv_trans _ _ _ hscaled
    (Q'.eqv_trans _ _ _ hsupport hcomponent)

/-- The descended reflection form is homogeneous over exact rationals in
its second argument. -/
theorem strictJointCylinderReflectionBilinear_smul_right
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} (scalar : Q')
    (left right : StrictJointCylinderVector base) :
    CReal.Equiv
      (strictJointCylinderReflectionBilinear hcoupling hle
        left (right.smul scalar))
      (CReal.mul (CReal.ofQ' scalar)
        (strictJointCylinderReflectionBilinear
          hcoupling hle left right)) := by
  intro epsilon hepsilon
  refine ⟨0, fun stage _ => ?_⟩
  have heqv := strictJointCylinderReflectionBilinear_approx_smul_right_eqv
    hcoupling hle (stage := stage) scalar left right
  have hepsilonNonnegative : (0 : Q') ≤ epsilon := Q'.le_of_lt hepsilon
  exact ⟨
    Q'.le_trans' _ _ _ (Q'.le_of_eqv heqv)
      (Q'.add_le_self_of_nonneg _ _ hepsilonNonnegative),
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv heqv)
      (Q'.add_le_self_of_nonneg _ _ hepsilonNonnegative)⟩

/-! ## 5. Geometric time translation on cylinder presentations -/

/-- Translate every canonical root forward in Euclidean time while leaving
the coefficient table unchanged.  The target base is enlarged by exactly the
translation distance. -/
def timeTranslateStrictJointCylinderVector
    {base : Nat} (shift : Nat)
    (vector : StrictJointCylinderVector base) :
    StrictJointCylinderVector (base + shift) where
  roots := vector.roots.map (timeShiftCanonicalRoot shift base)
  rootsCanonical := by
    intro root hroot
    obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hroot
    exact timeShiftCanonicalRoot_canonical
      (vector.rootsCanonical source hsource)
  coefficient := vector.coefficient

@[simp] theorem timeTranslateStrictJointCylinderVector_roots
    {base shift : Nat} (vector : StrictJointCylinderVector base) :
    (timeTranslateStrictJointCylinderVector shift vector).roots =
      vector.roots.map (timeShiftCanonicalRoot shift base) := rfl

@[simp] theorem timeTranslateStrictJointCylinderVector_coefficient
    {base shift : Nat} (vector : StrictJointCylinderVector base) :
    (timeTranslateStrictJointCylinderVector shift vector).coefficient =
      vector.coefficient := rfl

theorem timeTranslateStrictJointCylinderVector_roots_length
    {base shift : Nat} (vector : StrictJointCylinderVector base) :
    (timeTranslateStrictJointCylinderVector shift vector).roots.length =
      vector.roots.length := by
  change
    (vector.roots.map
      (timeShiftCanonicalRoot shift base)).length = vector.roots.length
  exact List.length_map (timeShiftCanonicalRoot shift base)

private theorem strictJointCylinderVector_ext_local
    {base : Nat} {left right : StrictJointCylinderVector base}
    (hroots : left.roots = right.roots)
    (hcoefficient : left.coefficient = right.coefficient) :
    left = right := by
  obtain ⟨leftRoots, leftCanonical, leftCoefficient⟩ := left
  obtain ⟨rightRoots, rightCanonical, rightCoefficient⟩ := right
  simp only at hroots hcoefficient
  subst rightRoots
  subst rightCoefficient
  rfl

private theorem timeTranslateStrictJointCylinderRoots_zero
    {base : Nat} (roots : List (List Nat))
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    roots.map (timeShiftCanonicalRoot 0 base) = roots := by
  induction roots with
  | nil => rfl
  | cons root rest ih =>
      simp only [List.map_cons]
      rw [timeShiftCanonicalRoot_zero
        (hroots root List.mem_cons_self)]
      rw [ih (fun item hitem =>
        hroots item (List.mem_cons_of_mem root hitem))]

/-- Zero time translation is exactly the identity presentation. -/
theorem timeTranslateStrictJointCylinderVector_zero
    {base : Nat} (vector : StrictJointCylinderVector base) :
    timeTranslateStrictJointCylinderVector 0 vector = vector := by
  apply strictJointCylinderVector_ext_local
  · exact timeTranslateStrictJointCylinderRoots_zero
      vector.roots vector.rootsCanonical
  · rfl

/-- Time translation is exactly compatible with the quotient-free
presentation addition. -/
theorem timeTranslateStrictJointCylinderVector_add
    {base : Nat} (shift : Nat)
    (left right : StrictJointCylinderVector base) :
    timeTranslateStrictJointCylinderVector shift (left.add right) =
      (timeTranslateStrictJointCylinderVector shift left).add
        (timeTranslateStrictJointCylinderVector shift right) := by
  apply strictJointCylinderVector_ext_local
  · exact List.map_append
  · funext bits
    simp only [timeTranslateStrictJointCylinderVector_coefficient]
    change
      left.coefficient
          (leftAppendStrictJointFingerprint left.roots.length bits) +
        right.coefficient
          (rightAppendStrictJointFingerprint left.roots.length bits) =
        left.coefficient
            (leftAppendStrictJointFingerprint
              (left.roots.map
                (timeShiftCanonicalRoot shift base)).length bits) +
          right.coefficient
            (rightAppendStrictJointFingerprint
              (left.roots.map
                (timeShiftCanonicalRoot shift base)).length bits)
    rw [List.length_map]

/-- Time translation is exactly compatible with rational scaling of a
presentation. -/
theorem timeTranslateStrictJointCylinderVector_smul
    {base : Nat} (shift : Nat) (scalar : Q')
    (vector : StrictJointCylinderVector base) :
    timeTranslateStrictJointCylinderVector shift (vector.smul scalar) =
      (timeTranslateStrictJointCylinderVector shift vector).smul scalar := by
  apply strictJointCylinderVector_ext_local
  · rfl
  · rfl

#print axioms finiteJointQuadratic_polarization
#print axioms finiteJointPolarizedBilinear_self
#print axioms centralNormalizedSupportReflectionQuadratic_polarization
#print axioms centralNormalizedSupportReflectionBilinear_self
#print axioms StrictJointCylinderVector.reflectionBilinear_approx_eqv_sequence
#print axioms StrictJointCylinderVector.reflectionBilinear_equiv
#print axioms StrictJointCylinderVector.reflectionBilinear_symm
#print axioms strictJointCylinderReflectionBilinear_self
#print axioms strictJointCylinderReflectionBilinear_add_left
#print axioms strictJointCylinderReflectionBilinear_smul_left
#print axioms strictJointCylinderReflectionBilinear_add_right
#print axioms strictJointCylinderReflectionBilinear_smul_right
#print axioms timeTranslateStrictJointCylinderVector_zero
#print axioms timeTranslateStrictJointCylinderVector_add
#print axioms timeTranslateStrictJointCylinderVector_smul

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBilinearTimeTranslation
