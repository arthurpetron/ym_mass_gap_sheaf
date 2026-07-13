/-
# Activity transport and normalization for first-conflict splicing

The state step inserts the selected excursion and clears the selected
residual occurrence.  At the activity level those two operations cancel the
unsafe-occurrence factor exactly.  The sole remaining multiplier is the
activity of the conflict vertex duplicated by the return detour.  This file
records that exact law, the corresponding local compensation inequality,
and a terminating normalizer driven by the strict residual potential.
-/

import YMGap.Continuum.XiExceptionalFirstConflictPotential
import YMGap.Continuum.SelfFusionLogConcave
import YMGap.Continuum.PinnedCluster

namespace YMGap.Continuum.XiExceptionalFirstConflictActivity

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiPairSwitching
open YMGap.Continuum.XiExceptionalPathExtraction
open YMGap.Continuum.XiExceptionalMaskCarrier
open YMGap.Continuum.XiExceptionalRecoveredBackground
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalUnsafeSideExclusion
open YMGap.Continuum.XiExceptionalFirstConflictDetour
open YMGap.Continuum.XiExceptionalFirstConflictSplice
open YMGap.Continuum.XiExceptionalEntryFirstConflictSplice
open YMGap.Continuum.XiExceptionalFirstConflictPotential
open YMGap.Continuum.PinnedCluster
open YMGap.Continuum.SelfFusionLogConcave

variable {L : Lattice} [DecidableEq L.Plaquette]

local infix:50 " ≈ " => Q'.eqv

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Int.add_mul, Int.mul_add, Int.one_mul,
               Int.mul_one]; ac_rfl))

/-! ## Exact residual activity refund -/

def residualActivity (w : Q') (label : L.Plaquette → Rep) :
    (Gamma : List (Polymer L)) → OccBitVec Gamma.length → Q'
  | [], .nil => 1
  | X :: Gamma, .cons head tail =>
      (if head then activity w X label else 1) *
        residualActivity w label Gamma tail

theorem residualActivity_nonnegative {w : Q'} (hw : (0 : Q') ≤ w)
    (label : L.Plaquette → Rep) :
  ∀ (Gamma : List (Polymer L)) (bits : OccBitVec Gamma.length),
      (0 : Q') ≤ residualActivity w label Gamma bits
  | [], .nil => by
      show (0 : Q') ≤ 1
      decide
  | X :: Gamma, .cons head tail => by
      cases head <;> simp only [residualActivity, ↓reduceIte]
      · exact Q'.mul_nonneg _ _ (by
          show (0 : Q') ≤ 1
          decide)
          (residualActivity_nonnegative hw label Gamma tail)
      · exact Q'.mul_nonneg _ _ (activity_nonneg hw X label)
          (residualActivity_nonnegative hw label Gamma tail)

private theorem polyAt_cons_zero (X : Polymer L)
    (Gamma : List (Polymer L)) : polyAt (X :: Gamma) 0 = X := by
  rfl

private theorem polyAt_cons_succ (X : Polymer L)
    (Gamma : List (Polymer L)) (i : Nat) :
    polyAt (X :: Gamma) (i + 1) = polyAt Gamma i := by
  rfl

theorem residualActivity_clearResidualAt_eqv
    (w : Q') (label : L.Plaquette → Rep) :
    ∀ (Gamma : List (Polymer L)) (bits : OccBitVec Gamma.length) (i : Nat),
      bits.at i = true →
      residualActivity w label Gamma bits ≈
        activity w (polyAt Gamma i) label *
          residualActivity w label Gamma (clearResidualAt bits i)
  | [], .nil, _, h => by cases h
  | X :: Gamma, .cons head tail, 0, h => by
      change head = true at h
      subst head
      change activity w X label * residualActivity w label Gamma tail ≈
        activity w X label * (1 * residualActivity w label Gamma tail)
      exact Q'.mul_eqv_congr_left _ _ _
        (Q'.eqv_symm (Q'.one_mul_eqv _))
  | X :: Gamma, .cons head tail, i + 1, h => by
      have ih := residualActivity_clearResidualAt_eqv
        w label Gamma tail i h
      rw [polyAt_cons_succ]
      cases head
      · change 1 * residualActivity w label Gamma tail ≈
          activity w (polyAt Gamma i) label *
            (1 * residualActivity w label Gamma (clearResidualAt tail i))
        refine Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left _ _ _ ih) ?_
        ring_qeqv
      · change activity w X label * residualActivity w label Gamma tail ≈
          activity w (polyAt Gamma i) label *
            (activity w X label *
              residualActivity w label Gamma (clearResidualAt tail i))
        refine Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left _ _ _ ih) ?_
        ring_qeqv

/-! ## Mapped walk activity and the exact one-step law -/

private theorem incAtDistinct_incompat
    (Gamma : List (Polymer L)) {i j : Nat}
    (h : incAtDistinct Gamma i j = true) :
    (!(compatibleB (polyAt Gamma i) (polyAt Gamma j))) = true := by
  exact ((Bool.and_eq_true _ _).mp h).2

private theorem mapCWalk_append
    {a b : Type} {edgeA : a → a → Bool}
    {edgeB : b → b → Bool} (f : a → b)
    (hedge : ∀ x y, edgeA x y = true → edgeB (f x) (f y) = true) :
    ∀ {x y z : a} (pre : CWalk edgeA x y) (suf : CWalk edgeA y z),
      mapCWalk f hedge (pre.append suf) =
        (mapCWalk f hedge pre).append (mapCWalk f hedge suf)
  | _, _, _, .single _, suf => rfl
  | _, _, _, .cons _ rest, suf => by
      simp only [CWalk.append, mapCWalk]
      rw [mapCWalk_append f hedge rest suf]

private theorem map_firstConflictEndpointDetour
    (Gamma : List (Polymer L)) {start finish : Nat}
    (walk : CWalk (incAtDistinct Gamma) start finish) (u : Nat)
    (hunsafe : pathSafe Gamma walk.vertices u = false) :
    let j := firstConflictIndex Gamma walk.vertices u
    let split := CWalk.firstConflictFactorization Gamma walk u hunsafe
    let hedge : ∀ i k, incAtDistinct Gamma i k = true →
        (!(compatibleB (polyAt Gamma i) (polyAt Gamma k))) = true :=
      fun _ _ h => incAtDistinct_incompat Gamma h
    let hconflict :=
      (firstConflictIndex_mem_and_conflict Gamma walk.vertices u hunsafe).2
    let hout : (!(compatibleB (polyAt Gamma j) (polyAt Gamma u))) = true :=
      incAtDistinct_incompat Gamma
        (incAtDistinct_of_symConflict_true Gamma j u hconflict)
    let hin : (!(compatibleB (polyAt Gamma u) (polyAt Gamma j))) = true :=
      incAtDistinct_incompat Gamma (by
        rw [← incAtDistinct_symm Gamma]
        exact incAtDistinct_of_symConflict_true Gamma j u hconflict)
    mapCWalk (edgeB := fun A B : Polymer L => !(compatibleB A B))
        (polyAt Gamma) hedge
        (CWalk.firstConflictEndpointDetour Gamma walk u hunsafe) =
      CWalk.endpointDetour
        (mapCWalk (edgeB := fun A B : Polymer L => !(compatibleB A B))
          (polyAt Gamma) hedge split.pre)
        (mapCWalk (edgeB := fun A B : Polymer L => !(compatibleB A B))
          (polyAt Gamma) hedge split.suf)
        (polyAt Gamma u) hout hin := by
  dsimp only
  let split := CWalk.firstConflictFactorization Gamma walk u hunsafe
  let hedge : ∀ i k, incAtDistinct Gamma i k = true →
      (!(compatibleB (polyAt Gamma i) (polyAt Gamma k))) = true :=
    fun _ _ h => incAtDistinct_incompat Gamma h
  change mapCWalk (edgeB := fun A B : Polymer L => !(compatibleB A B))
      (polyAt Gamma) hedge
      (CWalk.endpointDetour split.pre split.suf u _ _) = _
  unfold CWalk.endpointDetour
  rw [mapCWalk_append]
  rfl

def SpliceState.walkActivity (w : Q') (label : L.Plaquette → Rep)
    {Gamma : List (Polymer L)} {start finish : Nat}
    (state : SpliceState Gamma start finish) : Q' :=
  (mapCWalk (polyAt Gamma)
    (fun _ _ h => incAtDistinct_incompat Gamma h) state.walk).activityWeight
      w label

def SpliceState.totalActivity (w : Q') (label : L.Plaquette → Rep)
    {Gamma : List (Polymer L)} {start finish : Nat}
    (state : SpliceState Gamma start finish) : Q' :=
  SpliceState.walkActivity w label state *
    residualActivity w label Gamma state.residual

theorem SpliceState.walkActivity_nonnegative {w : Q'}
    (hw : (0 : Q') ≤ w) (label : L.Plaquette → Rep)
    {Gamma : List (Polymer L)} {start finish : Nat}
    (state : SpliceState Gamma start finish) :
    (0 : Q') ≤ SpliceState.walkActivity w label state :=
  CWalk.activityWeight_nonnegative hw label _

theorem SpliceState.totalActivity_nonnegative {w : Q'}
    (hw : (0 : Q') ≤ w) (label : L.Plaquette → Rep)
    {Gamma : List (Polymer L)} {start finish : Nat}
    (state : SpliceState Gamma start finish) :
    (0 : Q') ≤ SpliceState.totalActivity w label state :=
  Q'.mul_nonneg _ _ (SpliceState.walkActivity_nonnegative hw label state)
    (residualActivity_nonnegative hw label Gamma state.residual)

theorem SpliceState.step_walkActivity_eqv
    (w : Q') (label : L.Plaquette → Rep)
    {Gamma : List (Polymer L)} {start finish : Nat}
    (state : SpliceState Gamma start finish)
    (hunsafe : state.unsafeCheckB = false) :
    let u := state.selectedUnsafe
    let j := firstConflictIndex Gamma state.walk.vertices u
    SpliceState.walkActivity w label (state.step hunsafe) ≈
      (SpliceState.walkActivity w label state *
        activity w (polyAt Gamma j) label) *
        activity w (polyAt Gamma u) label := by
  dsimp only
  let hu := state.selectedUnsafe_spec hunsafe
  have hmapped := map_firstConflictEndpointDetour
    Gamma state.walk state.selectedUnsafe hu.2.2
  change CWalk.activityWeight w label
      (mapCWalk (polyAt Gamma) _ (state.step hunsafe).walk) ≈ _
  change CWalk.activityWeight w label
      (mapCWalk (polyAt Gamma) _
        (CWalk.firstConflictEndpointDetour
          Gamma state.walk state.selectedUnsafe hu.2.2)) ≈ _
  rw [hmapped]
  exact
    CWalk.firstConflictEndpointDetour_mapped_activity_eqv
      w label Gamma state.walk state.selectedUnsafe hu.2.2

theorem SpliceState.step_totalActivity_eqv
    (w : Q') (label : L.Plaquette → Rep)
    {Gamma : List (Polymer L)} {start finish : Nat}
    (state : SpliceState Gamma start finish)
    (hunsafe : state.unsafeCheckB = false) :
    let u := state.selectedUnsafe
    let j := firstConflictIndex Gamma state.walk.vertices u
    SpliceState.totalActivity w label (state.step hunsafe) ≈
      SpliceState.totalActivity w label state *
        activity w (polyAt Gamma j) label := by
  dsimp only
  let hu := state.selectedUnsafe_spec hunsafe
  have hwalk := SpliceState.step_walkActivity_eqv w label state hunsafe
  have hresidual := residualActivity_clearResidualAt_eqv
    w label Gamma state.residual state.selectedUnsafe hu.2.1
  change SpliceState.walkActivity w label (state.step hunsafe) *
      residualActivity w label Gamma (clearResidualAt state.residual
        state.selectedUnsafe) ≈
    (SpliceState.walkActivity w label state *
      residualActivity w label Gamma state.residual) *
        activity w (polyAt Gamma (firstConflictIndex Gamma
          state.walk.vertices state.selectedUnsafe)) label
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ hwalk) ?_
  refine Q'.eqv_trans _
    ((SpliceState.walkActivity w label state *
      (activity w (polyAt Gamma state.selectedUnsafe) label *
        residualActivity w label Gamma
          (clearResidualAt state.residual state.selectedUnsafe))) *
      activity w (polyAt Gamma (firstConflictIndex Gamma
        state.walk.vertices state.selectedUnsafe)) label) _ ?_ ?_
  · ring_qeqv
  · exact Q'.mul_eqv_congr_right
      (SpliceState.walkActivity w label state *
        (activity w (polyAt Gamma state.selectedUnsafe) label *
          residualActivity w label Gamma
            (clearResidualAt state.residual state.selectedUnsafe)))
      (SpliceState.walkActivity w label state *
        residualActivity w label Gamma state.residual)
      (activity w (polyAt Gamma (firstConflictIndex Gamma
        state.walk.vertices state.selectedUnsafe)) label)
      (Q'.mul_eqv_congr_left
        (SpliceState.walkActivity w label state)
        (activity w (polyAt Gamma state.selectedUnsafe) label *
          residualActivity w label Gamma
            (clearResidualAt state.residual state.selectedUnsafe))
        (residualActivity w label Gamma state.residual)
        (Q'.eqv_symm hresidual))

/-! ## The minimal local compensation and its sharp fence -/

theorem SpliceState.step_totalActivity_le_of_conflict_activity_le_one
    {w : Q'} (hw : (0 : Q') ≤ w) (label : L.Plaquette → Rep)
    {Gamma : List (Polymer L)} {start finish : Nat}
    (state : SpliceState Gamma start finish)
    (hunsafe : state.unsafeCheckB = false)
    (hlocal : activity w (polyAt Gamma
      (firstConflictIndex Gamma state.walk.vertices state.selectedUnsafe))
        label ≤ 1) :
    SpliceState.totalActivity w label (state.step hunsafe) ≤
      SpliceState.totalActivity w label state := by
  let J := activity w (polyAt Gamma
    (firstConflictIndex Gamma state.walk.vertices state.selectedUnsafe)) label
  have hexact := SpliceState.step_totalActivity_eqv w label state hunsafe
  have hscaled := Q'.mul_le_mul_of_nonneg_left J 1
    (SpliceState.totalActivity w label state) hlocal
    (SpliceState.totalActivity_nonnegative hw label state)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hexact)
    (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv (Q'.mul_one_eqv _)))

/-! The local factor bound is derived throughout the exact strong-coupling
window; it is not an additional target-fuel hypothesis. -/

theorem coeffW_le_one_of_strong {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw : w ≤ Q'.mkPos 1 2 (by decide)) (r : Rep) :
    coeffW w r ≤ (1 : Q') := by
  cases r with
  | zero =>
      rw [coeffW_zero]
      exact Q'.le_refl' _
  | succ k =>
      have hlead := PinnedCluster.coeffW_le_one_le hw0 hw (k + 1) (by omega)
      exact Q'.le_trans' _ _ _ hlead
        (SelfFusionLogConcave.coeffW1_le_one_of_strong hw0 hw)

theorem activity_le_one_of_strong {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw : w ≤ Q'.mkPos 1 2 (by decide))
    (label : L.Plaquette → Rep) :
    ∀ X : Polymer L, activity w X label ≤ (1 : Q')
  | [] => Q'.le_refl' _
  | p :: X => by
      rw [activity_cons]
      unfold plaqWeight
      have hhead := coeffW_le_one_of_strong hw0 hw (label p)
      have htail := activity_le_one_of_strong hw0 hw label X
      have htail0 := activity_nonneg hw0 X label
      have hmul := Q'.mul_le_mul_of_nonneg_right
        (coeffW w (label p)) 1 (activity w X label) hhead htail0
      exact Q'.le_trans' _ _ _ hmul
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.one_mul_eqv _)) htail)

theorem unconditional_local_compensation_false :
    ¬ (∀ A J U R : Q',
      (0 : Q') ≤ A → (0 : Q') ≤ J → (0 : Q') ≤ U → (0 : Q') ≤ R →
      ((A * J) * U) * R ≤ A * (U * R)) := by
  intro h
  have hbad := h 1 2 1 1 (by decide) (by decide) (by decide) (by decide)
  have hnot : ¬ ((((1 : Q') * 2) * 1) * 1 ≤ 1 * (1 * 1)) := by decide
  exact hnot hbad

/-! ## Terminating repeated normalization -/

def SpliceState.exhaust {Gamma : List (Polymer L)} {start finish : Nat}
    (state : SpliceState Gamma start finish) :
    SpliceState Gamma start finish :=
  if hunsafe : state.unsafeCheckB = false then
    SpliceState.exhaust (state.step hunsafe)
  else state
termination_by state.potential
decreasing_by apply SpliceState.step_potential_lt

theorem SpliceState.exhaust_totalActivity_le_of_local_compensation
    {w : Q'} (hw : (0 : Q') ≤ w) (label : L.Plaquette → Rep)
    {Gamma : List (Polymer L)} {start finish : Nat}
    (state : SpliceState Gamma start finish)
    (hlocal : ∀ (current : SpliceState Gamma start finish),
      (hunsafe : current.unsafeCheckB = false) →
      activity w (polyAt Gamma (firstConflictIndex Gamma
        current.walk.vertices current.selectedUnsafe)) label ≤ 1) :
    SpliceState.totalActivity w label (SpliceState.exhaust state) ≤
      SpliceState.totalActivity w label state := by
  rw [SpliceState.exhaust]
  split
  next hunsafe =>
    have ih := SpliceState.exhaust_totalActivity_le_of_local_compensation
      hw label (state.step hunsafe) hlocal
    have hone :=
      SpliceState.step_totalActivity_le_of_conflict_activity_le_one
        hw label state hunsafe (hlocal state hunsafe)
    exact Q'.le_trans' _ _ _ ih hone
  next _ => exact Q'.le_refl' _
termination_by state.potential
decreasing_by apply SpliceState.step_potential_lt

theorem SpliceState.exhaust_totalActivity_le_of_strong
    {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw : w ≤ Q'.mkPos 1 2 (by decide))
    (label : L.Plaquette → Rep)
    {Gamma : List (Polymer L)} {start finish : Nat}
    (state : SpliceState Gamma start finish) :
    SpliceState.totalActivity w label (SpliceState.exhaust state) ≤
      SpliceState.totalActivity w label state := by
  apply SpliceState.exhaust_totalActivity_le_of_local_compensation
    hw0 label state
  intro current _
  exact activity_le_one_of_strong hw0 hw label _

theorem SpliceState.exhaust_unsafeCheckB_true
    {Gamma : List (Polymer L)} {start finish : Nat}
    (state : SpliceState Gamma start finish) :
    (SpliceState.exhaust state).unsafeCheckB = true := by
  rw [SpliceState.exhaust]
  split
  next hunsafe =>
    exact SpliceState.exhaust_unsafeCheckB_true (state.step hunsafe)
  next hsafe =>
    cases hcheck : state.unsafeCheckB with
    | false => exact False.elim (hsafe hcheck)
    | true => rfl
termination_by state.potential
decreasing_by apply SpliceState.step_potential_lt

#print axioms residualActivity_clearResidualAt_eqv
#print axioms SpliceState.step_walkActivity_eqv
#print axioms SpliceState.step_totalActivity_eqv
#print axioms SpliceState.step_totalActivity_le_of_conflict_activity_le_one
#print axioms coeffW_le_one_of_strong
#print axioms activity_le_one_of_strong
#print axioms unconditional_local_compensation_false
#print axioms SpliceState.exhaust
#print axioms SpliceState.exhaust_totalActivity_le_of_local_compensation
#print axioms SpliceState.exhaust_totalActivity_le_of_strong
#print axioms SpliceState.exhaust_unsafeCheckB_true

end YMGap.Continuum.XiExceptionalFirstConflictActivity
