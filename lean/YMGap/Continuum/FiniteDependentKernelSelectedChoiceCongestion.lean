/-
# One selected channel per row with bounded target congestion

First-source thinning obtains column capacity by deleting every row except
the first one reaching a target.  That is unnecessarily rigid when a
many-to-one realization has a quantitative fiber bound.  This module keeps
one displayed channel in every source row and scales all selected channels by
`1 / (congestion + 1)`.  If at most `congestion + 1` selected rows reach any
one target, the scaled kernel has column mass at most one.

If the selected local weights have a common positive floor `eta`, every row
retains the common fraction

```text
  invSucc congestion * eta.
```

Thus the next application may prove bounded congestion rather than a global
collision-free matching.  This is exact finite algebra only.  No
`Classical`, choice, `native_decide`, `sorry`, new axiom, noncomputable
declaration, or unbounded heartbeat option is used.
-/

import YMGap.Constructive.CauchyConv
import YMGap.Continuum.FiniteDependentKernelCapacity

namespace YMGap.Continuum.FiniteDependentKernelSelectedChoiceCongestion

set_option autoImplicit false
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.FiniteDependentKernelCapacity
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

private theorem listQSum_le_termwise_local
    {A : Type} (left right : A → Q') :
    ∀ items : List A,
      (∀ item, item ∈ items → left item ≤ right item) →
        listQSum left items ≤ listQSum right items
  | [], _ => Q'.le_refl' 0
  | head :: tail, hterm => by
      exact Q'.add_le_add
        (hterm head List.mem_cons_self)
        (listQSum_le_termwise_local left right tail
          (fun item hitem =>
            hterm item (List.mem_cons_of_mem head hitem)))

private theorem listQSum_mask_eqv_filter_local
    {A : Type} (test : A → Bool) (value : A → Q') :
    ∀ items : List A,
      listQSum (fun item => if test item then value item else 0) items ≈
        listQSum value (items.filter test)
  | [] => Q'.eqv_refl 0
  | head :: tail => by
      cases htest : test head with
      | false =>
          simp only [listQSum, htest, Bool.false_eq_true, if_false,
            List.filter_cons]
          exact Q'.eqv_trans _ _ _
            (Q'.add_eqv_congr' (Q'.eqv_refl 0)
              (listQSum_mask_eqv_filter_local test value tail))
            (Q'.eqv_of_eq (Q'.zero_add' _))
      | true =>
          simp only [listQSum, htest, if_true, List.filter_cons]
          exact Q'.add_eqv_congr' (Q'.eqv_refl _)
            (listQSum_mask_eqv_filter_local test value tail)

private theorem listQSum_le_length_mul_local
    {A : Type} (value : A → Q') {bound : Q'}
    (hboundNonnegative : (0 : Q') ≤ bound) :
    ∀ items : List A,
      (∀ item, item ∈ items → value item ≤ bound) →
        listQSum value items ≤ Q'.ofNat items.length * bound
  | [], _ =>
      Q'.le_of_eqv (Q'.eqv_symm (Q'.zero_mul_eqv bound))
  | head :: tail, hbound => by
      have hhead := hbound head List.mem_cons_self
      have htail :=
        listQSum_le_length_mul_local value hboundNonnegative tail
          (fun item hitem =>
            hbound item (List.mem_cons_of_mem head hitem))
      refine Q'.le_trans' _ _ _ (Q'.add_le_add hhead htail) ?_
      refine Q'.le_of_eqv (Q'.eqv_symm ?_)
      refine Q'.eqv_trans _ ((Q'.ofNat tail.length + 1) * bound) _ ?_ ?_
      · exact Q'.mul_eqv_congr_right _ _ bound
          (Q'.ofNat_add_eqv tail.length 1)
      refine Q'.eqv_trans _
        (Q'.ofNat tail.length * bound + (1 : Q') * bound) _
        (Q'.add_mul_eqv (Q'.ofNat tail.length) 1 bound) ?_
      exact Q'.eqv_trans _
        (Q'.ofNat tail.length * bound + bound) _
        (Q'.add_eqv_congr_left _ _ _ (Q'.one_mul_eqv bound))
        (Q'.add_comm_eqv (Q'.ofNat tail.length * bound) bound)

private theorem invSucc_le_one_local (congestion : Nat) :
    Q'.invSucc congestion ≤ (1 : Q') := by
  show (Q'.invSucc congestion).num * ((1 : Q').den : Int) ≤
    (1 : Q').num * ((Q'.invSucc congestion).den : Int)
  rw [Q'.invSucc_num, Q'.invSucc_den]
  simp only [show ((1 : Q').den : Int) = 1 from rfl,
    show (1 : Q').num = 1 from rfl]
  omega

/-! ## 1. The explicit selected-channel congestion certificate -/

/-- The fiber of selected source rows reaching one target. -/
def selectedTargetFiber
    {Source Target : Type} [DecidableEq Target]
    (sources : List Source) (Choice : Source → Type)
    (selected : (source : Source) → Choice source)
    (realize : (source : Source) → Choice source → Target)
    (target : Target) : List Source :=
  sources.filter fun source =>
    decide (target = realize source (selected source))

/-- One displayed member of every dependent row, a common positive local
weight floor, and a uniform bound on the multiplicity of its realized target.
The upper bound is written as `congestion + 1`, so its reciprocal is always a
constructively positive rational. -/
structure SelectedChoiceCongestionCertificate
    {Source Target : Type} [DecidableEq Target]
    (sources : List Source) (Choice : Source → Type)
    (choices : (source : Source) → List (Choice source))
    (localWeight : (source : Source) → Choice source → Q')
    (realize : (source : Source) → Choice source → Target)
    (eta : Q') (congestion : Nat) : Type where
  eta_pos : (0 : Q') < eta
  eta_le_one : eta ≤ (1 : Q')
  selected : (source : Source) → Choice source
  selected_mem : ∀ source, source ∈ sources →
    selected source ∈ choices source
  selected_weight_nonnegative : ∀ source, source ∈ sources →
    (0 : Q') ≤ localWeight source (selected source)
  selected_weight_floor : ∀ source, source ∈ sources →
    eta ≤ localWeight source (selected source)
  selected_weight_le_one : ∀ source, source ∈ sources →
    localWeight source (selected source) ≤ (1 : Q')
  fiber_count_le : ∀ target,
    (selectedTargetFiber sources Choice selected realize target).length ≤
      congestion + 1

namespace SelectedChoiceCongestionCertificate

/-! ## 2. The scaled singleton dependent kernel -/

/-- The common retained row fraction supplied by the certificate. -/
def fraction
    {Source Target : Type} [DecidableEq Target]
    {sources : List Source} {Choice : Source → Type}
    {choices : (source : Source) → List (Choice source)}
    {localWeight : (source : Source) → Choice source → Q'}
    {realize : (source : Source) → Choice source → Target}
    {eta : Q'} {congestion : Nat}
    (_data : SelectedChoiceCongestionCertificate
      sources Choice choices localWeight realize eta congestion) : Q' :=
  Q'.invSucc congestion * eta

/-- The scaled kernel uses exactly one unit choice in every source row. -/
def scaledChoices
    {Source : Type} (_source : Source) : List Unit :=
  [()]

/-- Weight of the one retained unit choice. -/
def scaledLocalWeight
    {Source Target : Type} [DecidableEq Target]
    {sources : List Source} {Choice : Source → Type}
    {choices : (source : Source) → List (Choice source)}
    {localWeight : (source : Source) → Choice source → Q'}
    {realize : (source : Source) → Choice source → Target}
    {eta : Q'} {congestion : Nat}
    (data : SelectedChoiceCongestionCertificate
      sources Choice choices localWeight realize eta congestion)
    (source : Source) (_choice : Unit) : Q' :=
  Q'.invSucc congestion * localWeight source (data.selected source)

/-- Realization of the one retained unit choice. -/
def scaledRealize
    {Source Target : Type} [DecidableEq Target]
    {sources : List Source} {Choice : Source → Type}
    {choices : (source : Source) → List (Choice source)}
    {localWeight : (source : Source) → Choice source → Q'}
    {realize : (source : Source) → Choice source → Target}
    {eta : Q'} {congestion : Nat}
    (data : SelectedChoiceCongestionCertificate
      sources Choice choices localWeight realize eta congestion)
    (source : Source) (_choice : Unit) : Target :=
  realize source (data.selected source)

theorem fraction_pos
    {Source Target : Type} [DecidableEq Target]
    {sources : List Source} {Choice : Source → Type}
    {choices : (source : Source) → List (Choice source)}
    {localWeight : (source : Source) → Choice source → Q'}
    {realize : (source : Source) → Choice source → Target}
    {eta : Q'} {congestion : Nat}
    (data : SelectedChoiceCongestionCertificate
      sources Choice choices localWeight realize eta congestion) :
    (0 : Q') < data.fraction :=
  Q'.mul_pos (Q'.invSucc_pos congestion) data.eta_pos

theorem fraction_le_one
    {Source Target : Type} [DecidableEq Target]
    {sources : List Source} {Choice : Source → Type}
    {choices : (source : Source) → List (Choice source)}
    {localWeight : (source : Source) → Choice source → Q'}
    {realize : (source : Source) → Choice source → Target}
    {eta : Q'} {congestion : Nat}
    (data : SelectedChoiceCongestionCertificate
      sources Choice choices localWeight realize eta congestion) :
    data.fraction ≤ (1 : Q') := by
  have hscaled := Q'.mul_le_mul_of_nonneg_left
    eta 1 (Q'.invSucc congestion) data.eta_le_one
    (Q'.invSucc_nonneg congestion)
  exact Q'.le_trans' _ _ _ hscaled
    (Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_one_eqv (Q'.invSucc congestion)))
      (invSucc_le_one_local congestion))

theorem scaledLocalWeight_nonnegative
    {Source Target : Type} [DecidableEq Target]
    {sources : List Source} {Choice : Source → Type}
    {choices : (source : Source) → List (Choice source)}
    {localWeight : (source : Source) → Choice source → Q'}
    {realize : (source : Source) → Choice source → Target}
    {eta : Q'} {congestion : Nat}
    (data : SelectedChoiceCongestionCertificate
      sources Choice choices localWeight realize eta congestion)
    (source : Source) (hsource : source ∈ sources) (choice : Unit) :
    (0 : Q') ≤ data.scaledLocalWeight source choice :=
  Q'.mul_nonneg _ _ (Q'.invSucc_nonneg congestion)
    (data.selected_weight_nonnegative source hsource)

/-- Every selected singleton row has at least the common fraction. -/
theorem fraction_le_scaledRowMass
    {Source Target : Type} [DecidableEq Target]
    {sources : List Source} {Choice : Source → Type}
    {choices : (source : Source) → List (Choice source)}
    {localWeight : (source : Source) → Choice source → Q'}
    {realize : (source : Source) → Choice source → Target}
    {eta : Q'} {congestion : Nat}
    (data : SelectedChoiceCongestionCertificate
      sources Choice choices localWeight realize eta congestion)
    (source : Source) (hsource : source ∈ sources) :
    data.fraction ≤
      listQSum (data.scaledLocalWeight source)
        (scaledChoices source) := by
  have hscaled := Q'.mul_le_mul_of_nonneg_left
    eta (localWeight source (data.selected source))
    (Q'.invSucc congestion)
    (data.selected_weight_floor source hsource)
    (Q'.invSucc_nonneg congestion)
  exact Q'.le_trans' _ _ _ hscaled
    (Q'.le_of_eqv
      (Q'.eqv_symm
        (Q'.eqv_of_eq
          (Q'.add_zero' (data.scaledLocalWeight source ())))))

private theorem pushedWeight_le_mask
    {Source Target : Type} [DecidableEq Target]
    {sources : List Source} {Choice : Source → Type}
    {choices : (source : Source) → List (Choice source)}
    {localWeight : (source : Source) → Choice source → Q'}
    {realize : (source : Source) → Choice source → Target}
    {eta : Q'} {congestion : Nat}
    (data : SelectedChoiceCongestionCertificate
      sources Choice choices localWeight realize eta congestion)
    (source : Source) (hsource : source ∈ sources) (target : Target) :
    dependentKernelPushforwardWeight
        (fun _ : Source => Unit) scaledChoices data.scaledLocalWeight
        data.scaledRealize source target ≤
      if decide (target = data.scaledRealize source ())
      then Q'.invSucc congestion else 0 := by
  unfold dependentKernelPushforwardWeight kernelPushforwardWeight
    scaledChoices
  simp only [listQSum]
  by_cases htarget : target = data.scaledRealize source ()
  · rw [if_pos (decide_eq_true htarget)]
    subst target
    rw [deterministicKernel_on_image]
    have hweight := Q'.mul_le_mul_of_nonneg_left
      (localWeight source (data.selected source)) 1
      (Q'.invSucc congestion)
      (data.selected_weight_le_one source hsource)
      (Q'.invSucc_nonneg congestion)
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr'
            (Q'.mul_one_eqv (data.scaledLocalWeight source ()))
            (Q'.eqv_refl 0))
          (Q'.eqv_of_eq (Q'.add_zero' _))))
      (Q'.le_trans' _ _ _ hweight
        (Q'.le_of_eqv (Q'.mul_one_eqv (Q'.invSucc congestion))))
  · have hdecision : decide
        (target = data.scaledRealize source ()) = false :=
      decide_eq_false htarget
    simp only [hdecision, Bool.false_eq_true, if_false]
    rw [deterministicKernel_off_image htarget]
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr'
            (Q'.mul_zero_eqv (data.scaledLocalWeight source ()))
            (Q'.eqv_refl 0))
          (Q'.eqv_of_eq (Q'.zero_add' 0))))
      (Q'.le_refl' 0)

/-! ## 3. Bounded selected fibers give column capacity -/

/-- Scaling one chosen channel in every row by the reciprocal congestion
bound yields a genuine unit column-capacity kernel. -/
theorem scaledColumn_le_one
    {Source Target : Type} [DecidableEq Target]
    {sources : List Source} {Choice : Source → Type}
    {choices : (source : Source) → List (Choice source)}
    {localWeight : (source : Source) → Choice source → Q'}
    {realize : (source : Source) → Choice source → Target}
    {eta : Q'} {congestion : Nat}
    (data : SelectedChoiceCongestionCertificate
      sources Choice choices localWeight realize eta congestion)
    (target : Target) :
    listQSum
        (fun source => dependentKernelPushforwardWeight
          (fun _ : Source => Unit) scaledChoices data.scaledLocalWeight
          data.scaledRealize source target)
        sources ≤ (1 : Q') := by
  let test := fun source : Source =>
    decide (target = data.scaledRealize source ())
  let scale := Q'.invSucc congestion
  have hterm :
      listQSum
          (fun source => dependentKernelPushforwardWeight
            (fun _ : Source => Unit) scaledChoices data.scaledLocalWeight
            data.scaledRealize source target)
          sources ≤
        listQSum (fun source => if test source then scale else 0)
          sources := by
    apply listQSum_le_termwise_local
    intro source hsource
    exact data.pushedWeight_le_mask source hsource target
  have hfilter :
      listQSum (fun source => if test source then scale else 0) sources ≈
        listQSum (fun _ : Source => scale)
          (selectedTargetFiber sources Choice data.selected realize target) := by
    exact listQSum_mask_eqv_filter_local test (fun _ : Source => scale) sources
  have hlength :
      listQSum (fun _ : Source => scale)
          (selectedTargetFiber sources Choice data.selected realize target) ≤
        Q'.ofNat
            (selectedTargetFiber sources Choice data.selected realize target).length *
          scale := by
    apply listQSum_le_length_mul_local
    · exact Q'.invSucc_nonneg congestion
    · intro _ _
      exact Q'.le_refl' scale
  have hcount :
      Q'.ofNat
            (selectedTargetFiber sources Choice data.selected realize target).length *
          scale ≤
        Q'.ofNat (congestion + 1) * scale :=
    Q'.mul_le_mul_of_nonneg_right _ _ scale
      (Q'.ofNat_le_ofNat (data.fiber_count_le target))
      (Q'.invSucc_nonneg congestion)
  exact Q'.le_trans' _ _ _ hterm
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hfilter)
      (Q'.le_trans' _ _ _ hlength
        (Q'.le_trans' _ _ _ hcount
          (Q'.le_of_eqv (Q'.ofNat_succ_mul_invSucc congestion)))))

#print axioms SelectedChoiceCongestionCertificate.fraction_pos
#print axioms SelectedChoiceCongestionCertificate.fraction_le_one
#print axioms SelectedChoiceCongestionCertificate.fraction_le_scaledRowMass
#print axioms SelectedChoiceCongestionCertificate.scaledColumn_le_one

end SelectedChoiceCongestionCertificate

end YMGap.Continuum.FiniteDependentKernelSelectedChoiceCongestion
