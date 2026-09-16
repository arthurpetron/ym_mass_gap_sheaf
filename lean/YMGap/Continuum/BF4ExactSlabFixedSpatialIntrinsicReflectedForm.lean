/-
# Intrinsic natural-distance presentations of the reflected form

Here every natural label is a distance from the reflection plane, not a
window offset. The finite list supplies its own computed radius. A valid
chart of radius h sends distance d to offset h-d, retaining every signed
coefficient and ordered spatial face word. No enclosing chart is chosen
by an existence argument.

The pairing is the existing reflected form in the computed common chart
max(radius xs, radius ys). Centered inclusion identifies it with every
larger valid chart, and the existing actual-action symmetry and positivity
pass to these intrinsic presentations. Nome, spatial width, and heat stage
stay fixed throughout.

This is a scalar form on finite signed natural-distance presentations. It
does not yet quotient their linear or physical relations, construct a
completed half-space, identify a physical time-shift operator, or claim
completeness of the gauge-observable algebra.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedForm
import YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedCauchySchwarz

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicReflectedForm

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabTemporalSweep (FaceFactor)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredWindowShift
open YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedCauchySchwarz

/-- The existing finite signed list shape, now labelled by natural
distances from the reflection plane rather than offsets in a chart. -/
abbrev DistanceSpan := Span

/-- Computed maximum distance in one ordered schedule, with empty maximum zero. -/
def scheduleRadius : List (Nat × List FaceFactor) → Nat
  | [] => 0
  | e::es => max e.1 (scheduleRadius es)

/-- Computed maximum distance over every schedule of the signed presentation. -/
def radius : DistanceSpan → Nat
  | [] => 0
  | x::xs => max (scheduleRadius x.2) (radius xs)

/-- Concatenation uses the explicit maximum of the two distance radii. -/
theorem radius_append : (xs ys : DistanceSpan) →
    radius (xs++ys) = max (radius xs) (radius ys)
  | [], ys => by simp only [List.nil_append, radius, Nat.zero_max]
  | x::xs, ys => by
      change max (scheduleRadius x.2) (radius (xs++ys)) =
        max (max (scheduleRadius x.2) (radius xs)) (radius ys)
      rw [radius_append xs ys]
      exact (Nat.max_assoc _ _ _).symm

/-- Signed coefficient scaling does not alter the computed distance radius. -/
theorem radius_scale (c : Q') : (xs : DistanceSpan) →
    radius (scaleSpan c xs) = radius xs
  | [] => rfl
  | x::xs => by
      change max (scheduleRadius x.2) (radius (scaleSpan c xs)) =
        max (scheduleRadius x.2) (radius xs)
      rw [radius_scale c xs]

theorem scheduleRadius_within : (fs : List (Nat × List FaceFactor)) →
    ∀ e, e ∈ fs → e.1 ≤ scheduleRadius fs
  | [], _, he => False.elim (List.not_mem_nil he)
  | f::fs, e, he => by
      cases List.mem_cons.mp he with
      | inl heq =>
          subst e
          exact Nat.le_max_left _ _
      | inr ht =>
          exact Nat.le_trans (scheduleRadius_within fs e ht) (Nat.le_max_right _ _)

/-- Every distance is bounded by the explicit radius; no witness extraction. -/
theorem radius_within : (xs : DistanceSpan) → Within (radius xs) xs
  | [] => fun _ hx => False.elim (List.not_mem_nil hx)
  | y::ys => by
      intro x hx e he
      cases List.mem_cons.mp hx with
      | inl hxy =>
          subst x
          exact Nat.le_trans (scheduleRadius_within y.2 e he) (Nat.le_max_left _ _)
      | inr ht =>
          exact Nat.le_trans (radius_within ys x ht e he) (Nat.le_max_right _ _)

/-- Encode distances as lower-half offsets. All semantic uses below carry
the radius bound that prevents truncated subtraction from identifying times. -/
def encodeSchedule (h : Nat) (fs : List (Nat × List FaceFactor)) :
    List (Nat × List FaceFactor) :=
  fs.map (fun e => (h-e.1, e.2))

/-- The same signed presentation in an explicit chart centred at offset h. -/
def encodeChart (h : Nat) (xs : DistanceSpan) : Span :=
  xs.map (fun x => (x.1, encodeSchedule h x.2))

theorem encodeChart_append (h : Nat) (xs ys : DistanceSpan) :
    encodeChart h (xs++ys) = encodeChart h xs ++ encodeChart h ys :=
  List.map_append

theorem encodeChart_scale (h : Nat) (c : Q') (xs : DistanceSpan) :
    encodeChart h (scaleSpan c xs) = scaleSpan c (encodeChart h xs) := by
  simp only [encodeChart, scaleSpan, List.map_map, Function.comp_def]

/-- A valid computed chart lies in the required closed half-window. -/
theorem encodeChart_within (h : Nat) (xs : DistanceSpan) (_hh : radius xs ≤ h) :
    Within h (encodeChart h xs) := by
  intro x hx e he
  obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
  obtain ⟨f, _, rfl⟩ := List.mem_map.mp he
  exact Nat.sub_le _ _

/-- Chart encoding never changes any physical spatial face. -/
theorem encodeChart_physical {width : Nat} (h : Nat) (xs : DistanceSpan)
    (hf : Physical width xs) : Physical width (encodeChart h xs) := by
  intro x hx e he f hmem
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp he
  exact hf y hy g hg f hmem

private theorem encodeSchedule_succ (h : Nat) :
    (fs : List (Nat × List FaceFactor)) →
    (hf : ∀ e, e ∈ fs → e.1 ≤ h) →
    encodeSchedule (h+1) fs = shiftSchedule (encodeSchedule h fs)
  | [], _ => rfl
  | e::es, hf => by
      have he := hf e List.mem_cons_self
      have htime : (h+1)-e.1 = (h-e.1)+1 := by omega
      change ((h+1)-e.1, e.2)::encodeSchedule (h+1) es =
        ((h-e.1)+1, e.2)::shiftSchedule (encodeSchedule h es)
      rw [htime, encodeSchedule_succ h es
        (fun f hmem => hf f (List.mem_cons_of_mem e hmem))]

/-- Increasing a valid chart radius shifts each offset by one, leaving
each intrinsic distance to the reflection plane unchanged. -/
theorem encodeChart_succ (h : Nat) :
    (xs : DistanceSpan) → (hh : radius xs ≤ h) →
    encodeChart (h+1) xs = shiftSpan (encodeChart h xs)
  | [], _ => rfl
  | x::xs, hh => by
      have hhead : ∀ e, e ∈ x.2 → e.1 ≤ h := fun e he =>
        Nat.le_trans (scheduleRadius_within x.2 e he)
          (Nat.le_trans (Nat.le_max_left _ _) hh)
      have htail : radius xs ≤ h := Nat.le_trans (Nat.le_max_right _ _) hh
      change (x.1, encodeSchedule (h+1) x.2)::encodeChart (h+1) xs =
        (x.1, shiftSchedule (encodeSchedule h x.2))::shiftSpan (encodeChart h xs)
      rw [encodeSchedule_succ h x.2 hhead, encodeChart_succ h xs htail]

/-- The existing centered-inclusion theorem at explicit distance charts. -/
theorem form_chart_succ {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width h : Nat) (xs ys : DistanceSpan) (hx : radius xs ≤ h) (hy : radius ys ≤ h)
    (stage : Nat) :
    Equiv (form hw0 hw1 width (h+1) (encodeChart (h+1) xs) (encodeChart (h+1) ys)
      (encodeChart_within (h+1) xs (Nat.le_trans hx (Nat.le_succ h)))
      (encodeChart_within (h+1) ys (Nat.le_trans hy (Nat.le_succ h))) stage)
      (form hw0 hw1 width h (encodeChart h xs) (encodeChart h ys)
        (encodeChart_within h xs hx) (encodeChart_within h ys hy) stage) := by
  simpa only [encodeChart_succ h xs hx, encodeChart_succ h ys hy] using
    form_centered_inclusion hw0 hw1 width h (encodeChart h xs) (encodeChart h ys)
      (encodeChart_within h xs hx) (encodeChart_within h ys hy) stage

/-- Iterated centered inclusion compares any two valid nested charts.
The induction changes neither the intrinsic presentation nor the heat stage. -/
theorem form_chart_mono {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width h H : Nat) (xs ys : DistanceSpan)
    (hx : radius xs ≤ h) (hy : radius ys ≤ h) (hH : h ≤ H) (stage : Nat) :
    Equiv (form hw0 hw1 width H (encodeChart H xs) (encodeChart H ys)
      (encodeChart_within H xs (Nat.le_trans hx hH))
      (encodeChart_within H ys (Nat.le_trans hy hH)) stage)
      (form hw0 hw1 width h (encodeChart h xs) (encodeChart h ys)
        (encodeChart_within h xs hx) (encodeChart_within h ys hy) stage) := by
  have hsteps : ∀ k : Nat,
      Equiv (form hw0 hw1 width (h+k) (encodeChart (h+k) xs) (encodeChart (h+k) ys)
        (encodeChart_within (h+k) xs (Nat.le_trans hx (Nat.le_add_right h k)))
        (encodeChart_within (h+k) ys (Nat.le_trans hy (Nat.le_add_right h k))) stage)
        (form hw0 hw1 width h (encodeChart h xs) (encodeChart h ys)
          (encodeChart_within h xs hx) (encodeChart_within h ys hy) stage) := by
    intro k
    induction k with
    | zero => exact Equiv.refl _
    | succ k ih =>
        have hs := form_chart_succ hw0 hw1 width (h+k) xs ys
          (Nat.le_trans hx (Nat.le_add_right h k))
          (Nat.le_trans hy (Nat.le_add_right h k)) stage
        exact Equiv.trans (by simpa only [Nat.add_succ] using hs) ih
  have hindex : h+(H-h) = H := by omega
  simpa only [hindex] using hsteps (H-h)

/-- Intrinsic scalar pairing, evaluated in the computed common chart.
It is the same explicit-modulus reflected window limit, not a new state. -/
def pairing {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (xs ys : DistanceSpan) (stage : Nat) : CReal :=
  let H := max (radius xs) (radius ys)
  form hw0 hw1 width H (encodeChart H xs) (encodeChart H ys)
    (encodeChart_within H xs (Nat.le_max_left _ _))
    (encodeChart_within H ys (Nat.le_max_right _ _)) stage

/-- Pin the computed pairing to any explicit chart containing both finite
distance supports. Different charts need not use identical CReal moduli. -/
theorem pairing_chart {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width h : Nat) (xs ys : DistanceSpan) (hx : radius xs ≤ h) (hy : radius ys ≤ h)
    (stage : Nat) :
    Equiv (pairing hw0 hw1 width xs ys stage)
      (form hw0 hw1 width h (encodeChart h xs) (encodeChart h ys)
        (encodeChart_within h xs hx) (encodeChart_within h ys hy) stage) := by
  have hh : max (radius xs) (radius ys) ≤ h := Nat.max_le.mpr ⟨hx, hy⟩
  exact Equiv.symm (form_chart_mono hw0 hw1 width (max (radius xs) (radius ys)) h xs ys
    (Nat.le_max_left _ _) (Nat.le_max_right _ _) hh stage)

/-- Physical reflected symmetry now refers to natural-distance presentations,
with the two orderings compared in the same computed chart. -/
theorem pairing_symm {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (xs ys : DistanceSpan)
    (hxf : Physical width xs) (hyf : Physical width ys) (stage : Nat) :
    Equiv (pairing hw0 hw1 width xs ys stage) (pairing hw0 hw1 width ys xs stage) := by
  let H := max (radius xs) (radius ys)
  have hx : radius xs ≤ H := Nat.le_max_left _ _
  have hy : radius ys ≤ H := Nat.le_max_right _ _
  exact Equiv.trans (pairing_chart hw0 hw1 width H xs ys hx hy stage)
    (Equiv.trans
      (form_symm hw0 hw1 width H (encodeChart H xs) (encodeChart H ys)
        (encodeChart_within H xs hx) (encodeChart_within H ys hy)
        (encodeChart_physical H xs hxf) (encodeChart_physical H ys hyf) stage)
      (Equiv.symm (pairing_chart hw0 hw1 width H ys xs hy hx stage)))

/-- Actual signed-span reflection positivity in the computed intrinsic chart. -/
theorem pairing_self_nonnegative {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (xs : DistanceSpan) (hf : Physical width xs) (stage : Nat) :
    leEv (ofQ' 0) (pairing hw0 hw1 width xs xs stage) := by
  unfold pairing
  exact form_self_nonnegative hw0 hw1 width _ _ _
    (encodeChart_physical _ xs hf) stage

/-- All three terms are pinned to one explicitly computed chart before
using the original form's addition law. -/
theorem pairing_add_left {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (xs ys zs : DistanceSpan) (stage : Nat) :
    Equiv (pairing hw0 hw1 width (xs++ys) zs stage)
      (add (pairing hw0 hw1 width xs zs stage) (pairing hw0 hw1 width ys zs stage)) := by
  let H := max (radius xs) (max (radius ys) (radius zs))
  have hx : radius xs ≤ H := Nat.le_max_left _ _
  have hy : radius ys ≤ H := Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  have hz : radius zs ≤ H := Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  have hxy : radius (xs++ys) ≤ H := by rw [radius_append]; exact Nat.max_le.mpr ⟨hx, hy⟩
  have hpin := pairing_chart hw0 hw1 width H (xs++ys) zs hxy hz stage
  have hadd := form_add_left hw0 hw1 width H (encodeChart H xs) (encodeChart H ys)
    (encodeChart H zs) (encodeChart_within H xs hx) (encodeChart_within H ys hy)
    (encodeChart_within H zs hz) stage
  exact Equiv.trans (by simpa only [encodeChart_append] using hpin)
    (Equiv.trans hadd (Equiv_add
      (Equiv.symm (pairing_chart hw0 hw1 width H xs zs hx hz stage))
      (Equiv.symm (pairing_chart hw0 hw1 width H ys zs hy hz stage))))

theorem pairing_add_right {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (xs ys zs : DistanceSpan) (stage : Nat) :
    Equiv (pairing hw0 hw1 width xs (ys++zs) stage)
      (add (pairing hw0 hw1 width xs ys stage) (pairing hw0 hw1 width xs zs stage)) := by
  let H := max (radius xs) (max (radius ys) (radius zs))
  have hx : radius xs ≤ H := Nat.le_max_left _ _
  have hy : radius ys ≤ H := Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  have hz : radius zs ≤ H := Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  have hyz : radius (ys++zs) ≤ H := by rw [radius_append]; exact Nat.max_le.mpr ⟨hy, hz⟩
  have hpin := pairing_chart hw0 hw1 width H xs (ys++zs) hx hyz stage
  have hadd := form_add_right hw0 hw1 width H (encodeChart H xs) (encodeChart H ys)
    (encodeChart H zs) (encodeChart_within H xs hx) (encodeChart_within H ys hy)
    (encodeChart_within H zs hz) stage
  exact Equiv.trans (by simpa only [encodeChart_append] using hpin)
    (Equiv.trans hadd (Equiv_add
      (Equiv.symm (pairing_chart hw0 hw1 width H xs ys hx hy stage))
      (Equiv.symm (pairing_chart hw0 hw1 width H xs zs hx hz stage))))

theorem pairing_smul_left {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (c : Q') (xs ys : DistanceSpan) (stage : Nat) :
    Equiv (pairing hw0 hw1 width (scaleSpan c xs) ys stage)
      (mul (ofQ' c) (pairing hw0 hw1 width xs ys stage)) := by
  let H := max (radius xs) (radius ys)
  have hx : radius xs ≤ H := Nat.le_max_left _ _
  have hy : radius ys ≤ H := Nat.le_max_right _ _
  have hcx : radius (scaleSpan c xs) ≤ H := by simpa only [radius_scale] using hx
  have hpin := pairing_chart hw0 hw1 width H (scaleSpan c xs) ys hcx hy stage
  have hscale := form_smul_left hw0 hw1 width H c (encodeChart H xs) (encodeChart H ys)
    (encodeChart_within H xs hx) (encodeChart_within H ys hy) stage
  exact Equiv.trans (by simpa only [encodeChart_scale] using hpin)
    (Equiv.trans hscale (TrigSignedAdd.mul_congr_right
      (Equiv.symm (pairing_chart hw0 hw1 width H xs ys hx hy stage))))

theorem pairing_smul_right {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (c : Q') (xs ys : DistanceSpan) (stage : Nat) :
    Equiv (pairing hw0 hw1 width xs (scaleSpan c ys) stage)
      (mul (ofQ' c) (pairing hw0 hw1 width xs ys stage)) := by
  let H := max (radius xs) (radius ys)
  have hx : radius xs ≤ H := Nat.le_max_left _ _
  have hy : radius ys ≤ H := Nat.le_max_right _ _
  have hcy : radius (scaleSpan c ys) ≤ H := by simpa only [radius_scale] using hy
  have hpin := pairing_chart hw0 hw1 width H xs (scaleSpan c ys) hx hcy stage
  have hscale := form_smul_right hw0 hw1 width H c (encodeChart H xs) (encodeChart H ys)
    (encodeChart_within H xs hx) (encodeChart_within H ys hy) stage
  exact Equiv.trans (by simpa only [encodeChart_scale] using hpin)
    (Equiv.trans hscale (TrigSignedAdd.mul_congr_right
      (Equiv.symm (pairing_chart hw0 hw1 width H xs ys hx hy stage))))

private theorem product_congr {a b c d : CReal} (ha : Equiv a b) (hc : Equiv c d) :
    Equiv (mul a c) (mul b d) :=
  Equiv.trans (CReal.mul_congr_left ha) (TrigSignedAdd.mul_congr_right hc)

/-- Sharp CS for the intrinsic pairing, including the potentially different
computed charts of its two diagonals. -/
theorem pairing_cauchySchwarz {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (xs ys : DistanceSpan)
    (hxf : Physical width xs) (hyf : Physical width ys) (stage : Nat) :
    leEv (mul (pairing hw0 hw1 width xs ys stage) (pairing hw0 hw1 width xs ys stage))
      (mul (pairing hw0 hw1 width xs xs stage) (pairing hw0 hw1 width ys ys stage)) := by
  let H := max (radius xs) (radius ys)
  have hx : radius xs ≤ H := Nat.le_max_left _ _
  have hy : radius ys ≤ H := Nat.le_max_right _ _
  have hxy := pairing_chart hw0 hw1 width H xs ys hx hy stage
  have hxx := pairing_chart hw0 hw1 width H xs xs hx hx stage
  have hyy := pairing_chart hw0 hw1 width H ys ys hy hy stage
  exact leEv_trans (leEv_of_equiv (product_congr hxy hxy))
    (leEv_trans (form_cauchySchwarz hw0 hw1 width H (encodeChart H xs) (encodeChart H ys)
      (encodeChart_within H xs hx) (encodeChart_within H ys hy)
      (encodeChart_physical H xs hxf) (encodeChart_physical H ys hyf) stage)
      (leEv_of_equiv (Equiv.symm (product_congr hxx hyy))))

/-- Null pairing vanishes against every physical intrinsic presentation.
This is the actual radical law, not an input required of a future producer. -/
theorem pairing_radical_zero {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (xs ys : DistanceSpan)
    (hxf : Physical width xs) (hyf : Physical width ys) (stage : Nat)
    (hnull : Equiv (pairing hw0 hw1 width xs xs stage) (ofQ' 0)) :
    Equiv (pairing hw0 hw1 width xs ys stage) (ofQ' 0) := by
  let H := max (radius xs) (radius ys)
  have hx : radius xs ≤ H := Nat.le_max_left _ _
  have hy : radius ys ≤ H := Nat.le_max_right _ _
  have hxy := pairing_chart hw0 hw1 width H xs ys hx hy stage
  have hxx := pairing_chart hw0 hw1 width H xs xs hx hx stage
  exact Equiv.trans hxy (form_radical_zero hw0 hw1 width H (encodeChart H xs) (encodeChart H ys)
    (encodeChart_within H xs hx) (encodeChart_within H ys hy)
    (encodeChart_physical H xs hxf) (encodeChart_physical H ys hyf) stage
    (Equiv.trans (Equiv.symm hxx) hnull))

end YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicReflectedForm

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicReflectedForm.scheduleRadius
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicReflectedForm.radius
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicReflectedForm.radius_append
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicReflectedForm.radius_scale
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicReflectedForm.scheduleRadius_within
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicReflectedForm.radius_within
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicReflectedForm.encodeSchedule
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicReflectedForm.encodeChart
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicReflectedForm.encodeChart_append
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicReflectedForm.encodeChart_scale
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicReflectedForm.encodeChart_within
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicReflectedForm.encodeChart_physical
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicReflectedForm.encodeChart_succ
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicReflectedForm.form_chart_succ
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicReflectedForm.form_chart_mono
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicReflectedForm.pairing
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicReflectedForm.pairing_chart
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicReflectedForm.pairing_symm
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicReflectedForm.pairing_self_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicReflectedForm.pairing_add_left
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicReflectedForm.pairing_add_right
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicReflectedForm.pairing_smul_left
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicReflectedForm.pairing_smul_right
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicReflectedForm.pairing_cauchySchwarz
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicReflectedForm.pairing_radical_zero
