/-
# Literal observables for the all-spin cube reflected form

Each cube state is sent to the existing exact lower-state cylinder (agreement
on ALL lower faces), and finite signed lists to finite-linear observables.
Past a computed admission cutoff, their actual conditional Markov form equals
the normalized physical cube form, including cross terms and repetitions.
This is a dense reflected-form identification, not a marginal-norm isometry,
a completion equivalence, a geometric-time pin, or a strict gap.
-/

import YMGap.Continuum.BF4PhysicalCubeNormalizedKernelLimit
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLinearRealization
import YMGap.Continuum.BF4PhysicalJointFormTransfer

namespace YMGap.Continuum.BF4PhysicalCubeObservableRealization

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.RationalKernelSpan
open YMGap.Continuum.BF4PhysicalCubeGNSData
open YMGap.Continuum.BF4PhysicalCubeNormalizedKernelLimit
open YMGap.Continuum.BF4PhysicalCubeKernelSaturation
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalVacuumSectorCubeClassification
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLinearRealization
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm
open YMGap.Continuum.BF4PhysicalJointFormTransfer
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

/-- Literal finite signed sum of exact state cylinders; no cutoff in its type. -/
def cubeObservable : CubeSpan → CentralPhysicalLinearObservable
  | [] => .zero
  | term :: terms => .add
      (.smul term.2 (.atom (centralPhysicalStateCylinderUnitObservable 0 term.1.val)))
      (cubeObservable terms)

private theorem select_sum {A : Type} (p : A → Bool) (f : A → Q') (target : A)
    (items : List A) (hn : items.Nodup) (ht : target ∈ items) (hp : p target = true)
    (hu : ∀ a, a ∈ items → p a = true → a = target) :
    listQSum (fun a => if p a then f a else 0) items ≈ f target := by
  induction items with
  | nil => exact False.elim (List.not_mem_nil ht)
  | cons a rest ih =>
    have hn' := List.nodup_cons.mp hn
    rcases List.mem_cons.mp ht with he | ht'
    · subst target
      simp only [listQSum, hp, if_true]
      refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ ?_)
        (Q'.eqv_of_eq (Q'.add_zero' _))
      refine Q'.eqv_trans _ (listQSum (fun _ => (0 : Q')) rest) _ ?_ (listQSum_zero rest)
      apply listQSum_congr_on
      intro b hb
      cases hpb : p b with
      | false => exact Q'.eqv_refl _
      | true =>
        have he := hu b (List.mem_cons_of_mem a hb) hpb
        subst b
        exact False.elim (hn'.1 hb)
    · have ha : p a = false := by
        cases hpa : p a with
        | false => rfl
        | true =>
          have he := hu a List.mem_cons_self hpa
          subst target
          exact False.elim (hn'.1 ht')
      simp only [listQSum, ha, Bool.false_eq_true, if_false]
      exact Q'.eqv_trans _ _ _ (Q'.eqv_of_eq (Q'.zero_add' _))
        (ih hn'.2 ht' (fun b hb => hu b (List.mem_cons_of_mem a hb)))

/-- The actual positive row carrier contains each all-spin state eventually. -/
theorem state_mem_positive {w : Q'} (hw : (0 : Q') < w) (state : CubeSectorState)
    (K : Nat) (hK : stateCutoff state ≤ K) :
    state.val ∈ centralPositiveHalfStates w (Q'.le_of_lt hw) K 0 :=
  centralPhysicalFiniteVacuumSectorState_mem_positive w (Q'.le_of_lt hw) K 0
    (vacuumSector_cutoff_mono hw (stateCutoff state) K (by unfold stateCutoff; omega)
      hK (state_mem_finite_sector hw state))

private theorem cylinder_select {w : Q'} (hw : (0 : Q') ≤ w) (K half : Nat)
    (state : EdgeLabelling) (hs : state ∈ centralPositiveHalfStates w hw K half)
    (f : EdgeLabelling → Q') :
    listQSum (fun a => (centralPhysicalStateCylinderUnitObservable half state).value a * f a)
      (centralPositiveHalfStates w hw K half) ≈ f state := by
  refine Q'.eqv_trans _
    (listQSum (fun a => if labellingsAgreeOnB (centralLowerFaceIds half) a state then f a else 0)
      (centralPositiveHalfStates w hw K half)) _ (listQSum_congr (fun a => ?_) _) ?_
  · change (if labellingsAgreeOnB (centralLowerFaceIds half) a state then 1 else 0) * f a ≈
      (if labellingsAgreeOnB (centralLowerFaceIds half) a state then f a else 0)
    cases labellingsAgreeOnB (centralLowerFaceIds half) a state
    · exact Q'.zero_mul_eqv _
    · exact Q'.one_mul_eqv _
  · apply select_sum (fun a => labellingsAgreeOnB (centralLowerFaceIds half) a state)
      f state (centralPositiveHalfStates w hw K half)
      (centralPositiveHalfStates_nodup w hw K half) hs
      (labellingsAgreeOnB_self _ state)
    intro a ha hagree
    exact eq_of_labellingsAgreeOnB_of_bounded
      (mem_centralPositiveHalfStates_iff.mp ha).1
      (mem_centralPositiveHalfStates_iff.mp hs).1 hagree

/-- Two literal indicator insertions select exactly the original normalized entry. -/
theorem cylinder_form_eq_kernel {w : Q'} (hw : (0 : Q') < w)
    (K : Nat) (left right : CubeSectorState)
    (hl : stateCutoff left ≤ K) (hr : stateCutoff right ≤ K) :
    (physicalJointSmulGNS w (Q'.le_of_lt hw) K 0).toGNSData.B
        (centralPhysicalStateCylinderUnitObservable 0 left.val).value
        (centralPhysicalStateCylinderUnitObservable 0 right.val).value ≈
      centralNormalizedPhysicalReflectedKernel w (Q'.le_of_lt hw) K 0 left.val right.val := by
  refine Q'.eqv_trans _ _ _ (physicalJoint_B_eq_joint w (Q'.le_of_lt hw) K 0 _ _) ?_
  unfold physicalJointBilinear
  refine Q'.eqv_trans _
    (listQSum (fun source => (centralPhysicalStateCylinderUnitObservable 0 left.val).value source *
      listQSum (fun target => (centralPhysicalStateCylinderUnitObservable 0 right.val).value target *
        centralNormalizedPhysicalReflectedKernel w (Q'.le_of_lt hw) K 0 source target)
        (centralPositiveHalfStates w (Q'.le_of_lt hw) K 0))
      (centralPositiveHalfStates w (Q'.le_of_lt hw) K 0)) _
    (listQSum_congr (fun source => ?_) _) ?_
  · exact Q'.eqv_trans _ _ _ (listQSum_congr
      (fun target => Q'.mul_assoc_eqv _ _ _) _)
      (listQSum_mul_left _ _ _)
  · refine Q'.eqv_trans _ _ _ (cylinder_select (Q'.le_of_lt hw) K 0 left.val
      (state_mem_positive hw left K hl) _) ?_
    exact cylinder_select (Q'.le_of_lt hw) K 0 right.val
      (state_mem_positive hw right K hr) _

private def evalSpan {A : Type} (D : GNSData) (f : A → D.V) : Span A → D.V
  | [] => D.zero
  | t :: ts => D.add (D.smul t.2 (f t.1)) (evalSpan D f ts)

private theorem eval_left {A : Type} (D : GNSData) (f : A → D.V)
    (ts : Span A) (b : D.V) :
    D.B (evalSpan D f ts) b ≈ listQSum (fun t => t.2 * D.B (f t.1) b) ts := by
  induction ts with
  | nil => exact D.B_zero_left b
  | cons t ts ih =>
    exact Q'.eqv_trans _ _ _ (D.B_add_left _ _ b)
      (Q'.add_eqv_congr' (D.B_smul_left _ _ _) ih)

private theorem eval_form {A : Type} (D : GNSData) (f : A → D.V) (k : A → A → Q')
    (left right : Span A)
    (hpin : ∀ l, l ∈ left → ∀ r, r ∈ right → D.B (f l.1) (f r.1) ≈ k l.1 r.1) :
    D.B (evalSpan D f left) (evalSpan D f right) ≈ form k left right := by
  refine Q'.eqv_trans _ _ _ (D.B_symm _ _) ?_
  refine Q'.eqv_trans _ _ _ (eval_left D f right _) ?_
  apply listQSum_congr_on
  intro r hr
  apply Q'.mul_eqv_congr_left
  refine Q'.eqv_trans _ _ _ (D.B_symm _ _) ?_
  refine Q'.eqv_trans _ _ _ (eval_left D f left _) ?_
  apply listQSum_congr_on
  intro l hl
  exact Q'.mul_eqv_congr_left _ _ _ (hpin l hl r hr)

private theorem eval_cube (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) (terms : CubeSpan) :
    evalSpan (physicalJointSmulGNS w hw K 0).toGNSData
      (fun s : CubeSectorState => (centralPhysicalStateCylinderUnitObservable 0 s.val).value)
      terms = (cubeObservable terms).value := by
  induction terms with
  | nil => rfl
  | cons t ts ih =>
    simp only [evalSpan, ih]
    rfl

/-- One explicit cutoff pays state admission AND raw-kernel saturation. -/
def realizationCutoff (left right : CubeSpan) : Nat :=
  2 * (termSpinBound left + termSpinBound right) + 1

/-- Exact whole signed form, with the physical conditional action and its
original normalization. No positivity restriction on the coefficients. -/
theorem cubeObservable_finite_form {w : Q'} (hw : (0 : Q') < w)
    (left right : CubeSpan) (K : Nat) (hK : realizationCutoff left right ≤ K) :
    centralPhysicalWeightedInner w (Q'.le_of_lt hw) K 0
        (cubeObservable left).value
        (centralPhysicalMarkovApply w (Q'.le_of_lt hw) K 0 (cubeObservable right).value) ≈
      finiteNormalizedForm w (Q'.le_of_lt hw) K left right := by
  let D := (physicalJointSmulGNS w (Q'.le_of_lt hw) K 0).toGNSData
  change D.B (cubeObservable left).value (cubeObservable right).value ≈ _
  rw [← eval_cube w (Q'.le_of_lt hw) K left, ← eval_cube w (Q'.le_of_lt hw) K right]
  apply eval_form
  intro l hl r hr
  apply cylinder_form_eq_kernel hw K l.1 r.1
  · have hb := termSpinBound_member left hl
    unfold stateCutoff realizationCutoff at *
    omega
  · have hb := termSpinBound_member right hr
    unfold stateCutoff realizationCutoff at *
    omega

/-- Past the computed cutoff, the actual observable form is exactly the
constructed normalized raw form's approximation, not merely bounded by it. -/
theorem cubeObservable_form_eq_normalized_approx {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (left right : CubeSpan) (K : Nat) (hK : realizationCutoff left right ≤ K) :
    centralPhysicalWeightedInner w (Q'.le_of_lt hw0) K 0
        (cubeObservable left).value
        (centralPhysicalMarkovApply w (Q'.le_of_lt hw0) K 0 (cubeObservable right).value) ≈
      (normalizedFormLimit hw0 hw1 left right).approx K :=
  Q'.eqv_trans _ _ _ (cubeObservable_finite_form hw0 left right K hK)
    (normalizedFormLimit_approx_finite hw0 hw1 left right K (by
      unfold realizationCutoff at hK; omega))

end YMGap.Continuum.BF4PhysicalCubeObservableRealization

#print axioms YMGap.Continuum.BF4PhysicalCubeObservableRealization.cubeObservable
#print axioms YMGap.Continuum.BF4PhysicalCubeObservableRealization.state_mem_positive
#print axioms YMGap.Continuum.BF4PhysicalCubeObservableRealization.cylinder_form_eq_kernel
#print axioms YMGap.Continuum.BF4PhysicalCubeObservableRealization.realizationCutoff
#print axioms YMGap.Continuum.BF4PhysicalCubeObservableRealization.cubeObservable_finite_form
#print axioms YMGap.Continuum.BF4PhysicalCubeObservableRealization.cubeObservable_form_eq_normalized_approx
