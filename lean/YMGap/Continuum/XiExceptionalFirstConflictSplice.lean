/-
# First-conflict path factorization and splice activity

The selected first conflict is now split out of the canonical conflict walk
as an actual prefix/suffix factorization.  Splicing the excursion through the
unsafe occurrence preserves the indexed endpoints and costs exactly two walk
vertices.  After mapping to polymers, its activity is the original path
activity multiplied by precisely the unsafe-occurrence activity and one extra
copy of the conflict-vertex activity.
-/

import YMGap.Continuum.XiExceptionalFirstConflictDetour
import YMGap.Continuum.XiExceptionalCrossSpineCarrier

namespace YMGap.Continuum.XiExceptionalFirstConflictSplice

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiPairSwitching
open YMGap.Continuum.XiReverseComponentRecovery
open YMGap.Continuum.XiExceptionalPathExtraction
open YMGap.Continuum.XiExceptionalMaskCarrier
open YMGap.Continuum.XiExceptionalRecoveredBackground
open YMGap.Continuum.XiExceptionalUnsafeSideExclusion
open YMGap.Continuum.XiExceptionalFirstConflictDetour
open YMGap.Continuum.XiExceptionalFirstConflictDetour.CWalk
open YMGap.Continuum.XiExceptionalCrossSpineCarrier
open YMGap.Continuum.XiExceptionalCrossSpineCarrier.CWalk

local infix:50 " ≈ " => Q'.eqv

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Int.add_mul, Int.mul_add, Int.one_mul,
               Int.mul_one]; ac_rfl))

/-! ## Constructive factorization at a walk member -/

namespace CWalk

variable {a : Type} {edge : a → a → Bool}

structure Factorization {x y : a} (walk : CWalk edge x y)
    (pivot : a) : Type where
  pre : CWalk edge x pivot
  suf : CWalk edge pivot y
  rejoin : pre.append suf = walk

def factorAt [DecidableEq a] : ∀ {x y : a} (walk : CWalk edge x y)
    (pivot : a), pivot ∈ walk.vertices → Factorization walk pivot
  | _, _, .single x, pivot, hpivot => by
      have hpx : pivot = x := List.mem_singleton.mp hpivot
      subst pivot
      exact { pre := .single x, suf := .single x, rejoin := rfl }
  | x, y, @CWalk.cons _ _ _ next _ hxn rest, pivot, hpivot => by
      by_cases hpx : pivot = x
      · subst pivot
        exact { pre := .single x, suf := .cons hxn rest, rejoin := rfl }
      · have htail : pivot ∈ rest.vertices :=
          (List.mem_cons.mp hpivot).resolve_left hpx
        let tail := factorAt rest pivot htail
        exact
          { pre := .cons hxn tail.pre
            suf := tail.suf
            rejoin := by
              simp only [CWalk.append]
              rw [tail.rejoin] }

theorem factorAt_rejoin [DecidableEq a] {x y : a}
    (walk : CWalk edge x y) (pivot : a) (hpivot : pivot ∈ walk.vertices) :
    (factorAt walk pivot hpivot).pre.append
        (factorAt walk pivot hpivot).suf = walk :=
  (factorAt walk pivot hpivot).rejoin

/-! ## Factor and splice at the Boolean first conflict -/

variable {L : Lattice} [DecidableEq L.Plaquette]

def firstConflictFactorization (Gamma : List (Polymer L))
    {x y : Nat} (walk : CWalk (incAtDistinct Gamma) x y) (u : Nat)
    (hunsafe : pathSafe Gamma walk.vertices u = false) :
    Factorization walk (firstConflictIndex Gamma walk.vertices u) :=
  factorAt walk (firstConflictIndex Gamma walk.vertices u)
    (firstConflictIndex_mem_and_conflict Gamma walk.vertices u hunsafe).1

def firstConflictEndpointDetour (Gamma : List (Polymer L))
    {x y : Nat} (walk : CWalk (incAtDistinct Gamma) x y) (u : Nat)
    (hunsafe : pathSafe Gamma walk.vertices u = false) :
    CWalk (incAtDistinct Gamma) x y :=
  let split := firstConflictFactorization Gamma walk u hunsafe
  let j := firstConflictIndex Gamma walk.vertices u
  let hconflict :=
    (firstConflictIndex_mem_and_conflict Gamma walk.vertices u hunsafe).2
  YMGap.Continuum.XiExceptionalFirstConflictDetour.CWalk.endpointDetour
    split.pre split.suf u
    (incAtDistinct_of_symConflict_true Gamma j u hconflict)
    (by
      rw [← incAtDistinct_symm Gamma]
      exact incAtDistinct_of_symConflict_true Gamma j u hconflict)

theorem firstConflictEndpointDetour_length (Gamma : List (Polymer L))
    {x y : Nat} (walk : CWalk (incAtDistinct Gamma) x y) (u : Nat)
    (hunsafe : pathSafe Gamma walk.vertices u = false) :
    (firstConflictEndpointDetour Gamma walk u hunsafe).vertices.length =
      walk.vertices.length + 2 := by
  let split := firstConflictFactorization Gamma walk u hunsafe
  let j := firstConflictIndex Gamma walk.vertices u
  have hconflict :=
    (firstConflictIndex_mem_and_conflict Gamma walk.vertices u hunsafe).2
  let hout : incAtDistinct Gamma j u = true :=
    incAtDistinct_of_symConflict_true Gamma j u hconflict
  let hin : incAtDistinct Gamma u j = true := by
    rw [← incAtDistinct_symm Gamma]
    exact hout
  have hlen :=
    YMGap.Continuum.XiExceptionalFirstConflictDetour.CWalk.endpointDetour_vertices_length
      split.pre split.suf u hout hin
  change (firstConflictEndpointDetour Gamma walk u hunsafe).vertices.length =
    walk.vertices.length + 2
  rw [show firstConflictEndpointDetour Gamma walk u hunsafe =
      YMGap.Continuum.XiExceptionalFirstConflictDetour.CWalk.endpointDetour
        split.pre split.suf u hout hin by rfl]
  rw [hlen, split.rejoin]

end CWalk

/-! ## Exact repeated-vertex activity -/

variable {L : Lattice} [DecidableEq L.Plaquette]

theorem CWalk.endpointDetour_activityWeight_eqv
    (w : Q') (label : L.Plaquette → Rep)
    {X P Y : Polymer L}
    (pre : CWalk (fun A B : Polymer L => !(compatibleB A B)) X P)
    (suf : CWalk (fun A B : Polymer L => !(compatibleB A B)) P Y)
    (U : Polymer L)
    (hout : (!(compatibleB P U)) = true)
    (hin : (!(compatibleB U P)) = true) :
    (YMGap.Continuum.XiExceptionalFirstConflictDetour.CWalk.endpointDetour
      pre suf U hout hin).activityWeight w label ≈
      ((pre.append suf).activityWeight w label * activity w P label) *
        activity w U label := by
  have hdetour := CWalk.append_activityWeight_eqv w label pre
    (.cons hout (.cons hin suf))
  have hplain := CWalk.append_activityWeight_eqv w label pre suf
  unfold CWalk.endpointDetour
  refine Q'.eqv_trans _
    (prefixActivityWeight w label pre *
      (activity w P label *
        (activity w U label * suf.activityWeight w label))) _ hdetour ?_
  refine Q'.eqv_trans _
    (((prefixActivityWeight w label pre * suf.activityWeight w label) *
      activity w P label) * activity w U label) _ ?_ ?_
  · ring_qeqv
  · exact Q'.eqv_symm
      (Q'.mul_eqv_congr_right _ _ (activity w U label)
        (Q'.mul_eqv_congr_right _ _ (activity w P label) hplain))

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

theorem CWalk.firstConflictEndpointDetour_mapped_activity_eqv
    (w : Q') (label : L.Plaquette → Rep)
    (Gamma : List (Polymer L)) {x y : Nat}
    (walk : CWalk (incAtDistinct Gamma) x y) (u : Nat)
    (hunsafe : pathSafe Gamma walk.vertices u = false) :
    let j := firstConflictIndex Gamma walk.vertices u
    let split := firstConflictFactorization Gamma walk u hunsafe
    let pre := mapCWalk (polyAt Gamma)
      (fun _ _ h => incAtDistinct_incompat Gamma h) split.pre
    let suf := mapCWalk (polyAt Gamma)
      (fun _ _ h => incAtDistinct_incompat Gamma h) split.suf
    let original := mapCWalk (polyAt Gamma)
      (fun _ _ h => incAtDistinct_incompat Gamma h) walk
    let hconflict :=
      (firstConflictIndex_mem_and_conflict Gamma walk.vertices u hunsafe).2
    let hout : (!(compatibleB (polyAt Gamma j) (polyAt Gamma u))) = true :=
      incAtDistinct_incompat Gamma
        (incAtDistinct_of_symConflict_true Gamma j u hconflict)
    let hin : (!(compatibleB (polyAt Gamma u) (polyAt Gamma j))) = true :=
      incAtDistinct_incompat Gamma (by
        rw [← incAtDistinct_symm Gamma]
        exact incAtDistinct_of_symConflict_true Gamma j u hconflict)
    (YMGap.Continuum.XiExceptionalFirstConflictDetour.CWalk.endpointDetour
      pre suf (polyAt Gamma u) hout hin).activityWeight w label ≈
      (original.activityWeight w label *
        activity w (polyAt Gamma j) label) *
          activity w (polyAt Gamma u) label := by
  dsimp only
  let j := firstConflictIndex Gamma walk.vertices u
  let split := firstConflictFactorization Gamma walk u hunsafe
  let hedge : ∀ i k, incAtDistinct Gamma i k = true →
      (!(compatibleB (polyAt Gamma i) (polyAt Gamma k))) = true :=
    fun _ _ h => incAtDistinct_incompat Gamma h
  let pre := mapCWalk
    (edgeB := fun A B : Polymer L => !(compatibleB A B))
    (polyAt Gamma) hedge split.pre
  let suf := mapCWalk
    (edgeB := fun A B : Polymer L => !(compatibleB A B))
    (polyAt Gamma) hedge split.suf
  let original := mapCWalk
    (edgeB := fun A B : Polymer L => !(compatibleB A B))
    (polyAt Gamma) hedge walk
  have hconflict :=
    (firstConflictIndex_mem_and_conflict Gamma walk.vertices u hunsafe).2
  let hout : (!(compatibleB (polyAt Gamma j) (polyAt Gamma u))) = true :=
    incAtDistinct_incompat Gamma
      (incAtDistinct_of_symConflict_true Gamma j u hconflict)
  let hin : (!(compatibleB (polyAt Gamma u) (polyAt Gamma j))) = true :=
    incAtDistinct_incompat Gamma (by
      rw [← incAtDistinct_symm Gamma]
      exact incAtDistinct_of_symConflict_true Gamma j u hconflict)
  have hactivity := CWalk.endpointDetour_activityWeight_eqv
    w label pre suf (polyAt Gamma u) hout hin
  have hrejoinMap := congrArg
    (mapCWalk (edgeB := fun A B : Polymer L => !(compatibleB A B))
      (polyAt Gamma) hedge) split.rejoin
  rw [mapCWalk_append] at hrejoinMap
  change pre.append suf = original at hrejoinMap
  rw [hrejoinMap] at hactivity
  exact hactivity

#print axioms CWalk.factorAt_rejoin
#print axioms CWalk.firstConflictEndpointDetour_length
#print axioms CWalk.endpointDetour_activityWeight_eqv
#print axioms CWalk.firstConflictEndpointDetour_mapped_activity_eqv

end YMGap.Continuum.XiExceptionalFirstConflictSplice
