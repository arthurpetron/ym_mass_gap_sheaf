/-
Square-root-free trace domination for a finite positive Gram-channel
resolution.

This is the generic analytic leaf needed by the global cutoff-one coefficient
network.  If `W` preserves a positive-semidefinite Gram form and a finite
channel resolution has nonnegative rational weights, then

  |sum_c weight(c) * <v_c, W v_c>|
    <= sum_c weight(c) * <v_c, v_c>.

The proof never introduces square roots.  Its one-channel input is the sharp
Young inequality

  2 * |<x,y>| <= <x,x> + <y,y>,

the two diagonal terms agree for `y = W x`, and the positive factor `2`
cancels constructively in `Q'`.  A structural list induction supplies the
finite triangle inequality and monotonicity.

The right-hand side is deliberately called `resolvedTraceMass`, not `rank`.
Downstream projector leaves must prove that their concrete orthogonal channel
resolution has mass equal to the appropriate invariant-space dimension.  No
rank statement, trace bound, or desired conclusion is stored as a structure
field here.

# Axiom gate

The public declarations below use only the repository's constructive `Q'`
arithmetic and the already-proved OS pre-inner-form laws.  No `Classical.*`,
`native_decide`, `sorry`, `admit`, or custom axiom is used.
-/

import YMGap.Continuum.OSReconstructionProgress
import YMGap.Constructive.AbsQ

namespace YMGap.Continuum.OSReconstructionProgress.PreInnerForm

open YMGap.Constructive

variable {V : Type}

/-- Square-root-free two-sided Young bound:
`2 * |<a,b>| <= <a,a> + <b,b>`.

The nonnegative sign is `young_cs`.  In the negative sign, `inner_lower`
moves `2<a,b>` across the order and gives the matching estimate for
`2*(-<a,b>)`. -/
theorem two_mul_abs_inner_le (F : PreInnerForm V) (a b : V) :
    2 * Q'.abs (F.B a b) <= F.B a a + F.B b b := by
  unfold Q'.abs
  by_cases h : (0 : Q') <= F.B a b
  · rw [if_pos h]
    exact F.young_cs a b
  · rw [if_neg h]
    have hLower := F.inner_lower a b
    have hReorder :
        ((F.B a a + 2 * F.B a b) + F.B b b).eqv
          ((F.B a a + F.B b b) + 2 * F.B a b) :=
      Q'.eqv_trans _ _ _
        (Q'.add_assoc_eqv (F.B a a) (2 * F.B a b) (F.B b b))
        (Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_left (F.B a a)
            (2 * F.B a b + F.B b b) (F.B b b + 2 * F.B a b)
            (Q'.add_comm_eqv (2 * F.B a b) (F.B b b)))
          (Q'.eqv_symm
            (Q'.add_assoc_eqv (F.B a a) (F.B b b) (2 * F.B a b))))
    have hSum :
        (0 : Q') <= (F.B a a + F.B b b) + 2 * F.B a b :=
      le_of_le_eqv hLower hReorder
    have hSub :
        (0 : Q') <=
          (F.B a a + F.B b b) + (-(-(2 * F.B a b))) :=
      le_of_le_eqv hSum
        (Q'.add_eqv_congr_left (F.B a a + F.B b b)
          (2 * F.B a b) (-(-(2 * F.B a b)))
          (Q'.eqv_symm (Q'.neg_neg_eqv (2 * F.B a b))))
    have hNeg :
        (-(2 * F.B a b)) <= F.B a a + F.B b b :=
      q_le_of_sub_nonneg hSub
    exact le_of_eqv_le (Q'.mul_neg_eqv 2 (F.B a b)) hNeg

end YMGap.Continuum.OSReconstructionProgress.PreInnerForm

namespace YMGap.Continuum.PositiveChannelTraceBound

open YMGap.Constructive
open YMGap.Continuum.OSReconstructionProgress

/-! ## Minimal rational absolute-value and finite-list infrastructure -/

/-- The lower half of the absolute-value interval: `-|x| <= x`. -/
private theorem neg_abs_le_self (x : Q') : -(Q'.abs x) <= x := by
  have h := Q'.neg_le_neg (Q'.neg_le_abs x)
  exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.neg_neg_eqv x))

/-- Local two-term triangle inequality, proved from the minimal `AbsQ` API. -/
private theorem abs_add_le (u v : Q') :
    Q'.abs (u + v) <= Q'.abs u + Q'.abs v := by
  refine Q'.abs_le ?_ ?_
  · have hNeg :
        (-(Q'.abs u + Q'.abs v)).eqv
          ((-(Q'.abs u)) + (-(Q'.abs v))) :=
      Q'.neg_add_eqv (Q'.abs u) (Q'.abs v)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hNeg)
      (Q'.add_le_add (neg_abs_le_self u) (neg_abs_le_self v))
  · exact Q'.add_le_add (Q'.le_abs_self u) (Q'.le_abs_self v)

/-- Multiplication by a nonnegative rational preserves an absolute majorant.
This avoids importing a downstream absolute-value/product library. -/
private theorem abs_mul_le_mul_of_nonneg_left {w x m : Q'}
    (hw : (0 : Q') <= w) (hx : Q'.abs x <= m) :
    Q'.abs (w * x) <= w * m := by
  refine Q'.abs_le ?_ ?_
  · have hNegMass : -m <= -(Q'.abs x) := Q'.neg_le_neg hx
    have hLower : -m <= x :=
      Q'.le_trans' _ _ _ hNegMass (neg_abs_le_self x)
    have hWeighted : w * (-m) <= w * x :=
      Q'.mul_le_mul_of_nonneg_left (-m) x w hLower hw
    exact le_of_eqv_le (Q'.eqv_symm (Q'.mul_neg_eqv w m)) hWeighted
  · have hUpper : x <= m :=
      Q'.le_trans' _ _ _ (Q'.le_abs_self x) hx
    exact Q'.mul_le_mul_of_nonneg_left x m w hUpper hw

/-- Lightweight structural sum, kept local to avoid importing a downstream
polymer or representation-theory summation module. -/
def listQSum {A : Type} (f : A -> Q') : List A -> Q'
  | [] => 0
  | x :: xs => f x + listQSum f xs

/-- Structural monotonicity of the lightweight list sum. -/
theorem listQSum_mono {A : Type} {f g : A -> Q'}
    (h : forall x, f x <= g x) :
    forall xs, listQSum f xs <= listQSum g xs
  | [] => Q'.le_refl' 0
  | x :: xs => Q'.add_le_add (h x) (listQSum_mono h xs)

/-- Finite triangle inequality for the lightweight list sum. -/
theorem abs_listQSum_le {A : Type} (f : A -> Q') :
    forall xs, Q'.abs (listQSum f xs) <=
      listQSum (fun x => Q'.abs (f x)) xs
  | [] => by
      unfold listQSum Q'.abs
      rw [if_pos (Q'.le_refl' 0)]
      exact Q'.le_refl' 0
  | x :: xs => by
      exact Q'.le_trans' _ _ _
        (abs_add_le (f x) (listQSum f xs))
        (Q'.add_le_add (Q'.le_refl' (Q'.abs (f x)))
          (abs_listQSum_le f xs))

/-- A map preserving the rational Gram form.  Linearity is not required by
the trace estimate and is therefore not postulated here. -/
structure GramIsometry {V : Type} (F : PreInnerForm V) where
  map : V -> V
  gram_eqv : forall a b, (F.B (map a) (map b)).eqv (F.B a b)

namespace GramIsometry

variable {V : Type}

/-- Identity Gram isometry. -/
def id (F : PreInnerForm V) : GramIsometry F where
  map := fun v => v
  gram_eqv := fun a b => Q'.eqv_refl (F.B a b)

end GramIsometry

/-- One positive weighted channel.  The vector need not be normalized: the
exact rational weight records the positive projector coefficient without a
square root. -/
structure PositiveChannel (V : Type) where
  vector : V
  weight : Q'
  weight_nonneg : (0 : Q') <= weight

/-- A finite positive channel resolution for a fixed Gram form.

No trace estimate or rank claim is stored here.  Orthogonality and the
identification of the total mass with an operator rank belong to concrete
projector realizations downstream. -/
structure FinitePositiveChannelResolution {V : Type} (F : PreInnerForm V) where
  channels : List (PositiveChannel V)

variable {V : Type}

/-- The signed contribution of one channel to the resolved trace. -/
def channelTraceTerm (F : PreInnerForm V) (W : GramIsometry F)
    (c : PositiveChannel V) : Q' :=
  c.weight * F.B c.vector (W.map c.vector)

/-- The nonnegative Gram mass assigned to one channel. -/
def channelTraceMass (F : PreInnerForm V) (c : PositiveChannel V) : Q' :=
  c.weight * F.B c.vector c.vector

/-- The finite signed trace in a positive channel resolution. -/
def resolvedTrace (F : PreInnerForm V)
    (R : FinitePositiveChannelResolution F) (W : GramIsometry F) : Q' :=
  listQSum (channelTraceTerm F W) R.channels

/-- The total positive Gram mass of the resolution.  Concrete orthogonal
projector leaves may subsequently identify this quantity with rank. -/
def resolvedTraceMass (F : PreInnerForm V)
    (R : FinitePositiveChannelResolution F) : Q' :=
  listQSum (channelTraceMass F) R.channels

/-- Each channel mass is nonnegative. -/
theorem channelTraceMass_nonneg (F : PreInnerForm V) (c : PositiveChannel V) :
    (0 : Q') <= channelTraceMass F c :=
  Q'.mul_nonneg c.weight (F.B c.vector c.vector)
    c.weight_nonneg (F.self_nonneg c.vector)

/-- One weighted channel is dominated by its positive Gram mass. -/
theorem abs_channelTraceTerm_le_mass (F : PreInnerForm V)
    (W : GramIsometry F) (c : PositiveChannel V) :
    Q'.abs (channelTraceTerm F W c) <= channelTraceMass F c := by
  have hYoung := F.two_mul_abs_inner_le c.vector (W.map c.vector)
  have hDiagonal :
      (F.B c.vector c.vector + F.B (W.map c.vector) (W.map c.vector)).eqv
        (2 * F.B c.vector c.vector) :=
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (F.B c.vector c.vector)
        (F.B (W.map c.vector) (W.map c.vector))
        (F.B c.vector c.vector) (W.gram_eqv c.vector c.vector))
      (q_two_mul (F.B c.vector c.vector))
  have hTwice :
      2 * Q'.abs (F.B c.vector (W.map c.vector)) <=
        2 * F.B c.vector c.vector :=
    le_of_le_eqv hYoung hDiagonal
  have hInner :
      Q'.abs (F.B c.vector (W.map c.vector)) <=
        F.B c.vector c.vector :=
    q_cancel_left (c := (2 : Q')) (by decide) hTwice
  exact abs_mul_le_mul_of_nonneg_left c.weight_nonneg hInner

/-- The total resolved trace mass is nonnegative. -/
theorem resolvedTraceMass_nonneg (F : PreInnerForm V)
    (R : FinitePositiveChannelResolution F) :
    (0 : Q') <= resolvedTraceMass F R := by
  unfold resolvedTraceMass
  induction R.channels with
  | nil => exact Q'.le_refl' 0
  | cons c cs ih =>
      exact Q'.zero_le_add _ _ (channelTraceMass_nonneg F c) ih

/-- **Square-root-free positive-channel trace domination.**

The absolute value of the signed trace is at most the positive Gram mass of
the finite resolution.  The conclusion is derived from Gram positivity,
isometry, finite triangle, and sum monotonicity; it is not an input field. -/
theorem abs_resolvedTrace_le_mass (F : PreInnerForm V)
    (R : FinitePositiveChannelResolution F) (W : GramIsometry F) :
    Q'.abs (resolvedTrace F R W) <= resolvedTraceMass F R := by
  unfold resolvedTrace resolvedTraceMass
  exact Q'.le_trans' _ _ _
    (abs_listQSum_le (channelTraceTerm F W) R.channels)
    (listQSum_mono
      (fun c => abs_channelTraceTerm_le_mass F W c) R.channels)

/-! ## Nonvacuity and sharp one-channel pins -/

/-- The one-channel positive resolution of `v` with nonnegative weight `w`. -/
def oneChannelResolution (F : PreInnerForm V) (v : V) (w : Q')
    (hw : (0 : Q') <= w) : FinitePositiveChannelResolution F where
  channels := [{ vector := v, weight := w, weight_nonneg := hw }]

/-- The one-channel resolution is structurally nonempty. -/
theorem oneChannelResolution_nonempty (F : PreInnerForm V) (v : V) (w : Q')
    (hw : (0 : Q') <= w) :
    (oneChannelResolution F v w hw).channels != [] := by
  intro h
  cases h

/-- The identity isometry makes the one-channel signed trace exactly equal,
up to the native rational setoid, to its Gram mass.  Thus the estimate is
sharp whenever that mass is positive. -/
theorem oneChannel_id_trace_eqv_mass (F : PreInnerForm V) (v : V) (w : Q')
    (hw : (0 : Q') <= w) :
    (resolvedTrace F (oneChannelResolution F v w hw) (GramIsometry.id F)).eqv
      (resolvedTraceMass F (oneChannelResolution F v w hw)) :=
  Q'.eqv_refl _

/-- Concrete nondegenerate unit-weight form for the sharpness regression. -/
def unitWeightForm : PreInnerForm Q' :=
  weightForm 1 (by decide)

/-- A concrete positive one-channel resolution of the unit vector. -/
def sharpOneChannelResolution :
    FinitePositiveChannelResolution unitWeightForm :=
  oneChannelResolution unitWeightForm 1 1 (by decide)

/-- The concrete one-channel Gram mass is strictly positive. -/
theorem sharpOneChannel_mass_pos :
    (0 : Q') < resolvedTraceMass unitWeightForm sharpOneChannelResolution := by
  decide

/-- The absolute trace bound is attained exactly on the concrete one-channel
identity isometry. -/
theorem sharpOneChannel_abs_trace_eqv_mass :
    (Q'.abs
      (resolvedTrace unitWeightForm sharpOneChannelResolution
        (GramIsometry.id unitWeightForm))).eqv
      (resolvedTraceMass unitWeightForm sharpOneChannelResolution) := by
  decide

end YMGap.Continuum.PositiveChannelTraceBound

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.OSReconstructionProgress.PreInnerForm.two_mul_abs_inner_le
#print axioms YMGap.Continuum.PositiveChannelTraceBound.GramIsometry.id
#print axioms YMGap.Continuum.PositiveChannelTraceBound.channelTraceMass_nonneg
#print axioms YMGap.Continuum.PositiveChannelTraceBound.abs_channelTraceTerm_le_mass
#print axioms YMGap.Continuum.PositiveChannelTraceBound.resolvedTraceMass_nonneg
#print axioms YMGap.Continuum.PositiveChannelTraceBound.abs_resolvedTrace_le_mass
#print axioms YMGap.Continuum.PositiveChannelTraceBound.oneChannel_id_trace_eqv_mass
#print axioms YMGap.Continuum.PositiveChannelTraceBound.sharpOneChannel_mass_pos
#print axioms YMGap.Continuum.PositiveChannelTraceBound.sharpOneChannel_abs_trace_eqv_mass
