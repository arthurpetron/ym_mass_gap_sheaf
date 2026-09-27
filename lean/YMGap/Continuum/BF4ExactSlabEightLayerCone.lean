/-
# Exact eight-layer causal cone in the original completed action

Each physical link occurs once in the direction/parity schedule. Within
one color the actual conditional projections commute. Updates outside the
input's conditional support can therefore be removed EXACTLY. One layer
enlarges that support by at most one original Ward star; one complete sweep
uses eight such enlargements, independent of the ambient volume.

Conditional support means fixation by updates outside the stated link set.
Literal polynomial support supplies it, but the converse is not asserted.
The pruned sweep equals the full completed vector, not a surrogate vector.
No coefficient-support representative is extracted from a quotient.

These are finite-speed identities for conditional L2 updates, not spatial
correlation decay. A useful interacting coercivity estimate, the normalized
covariance join, physical-time/spacing control and continuum YM remain open.
-/

import YMGap.Continuum.GNSCommutingSweep
import YMGap.Continuum.BF4ExactSlabConditionalSweep
import YMGap.Continuum.Z4LinkEightColor

namespace YMGap.Continuum.BF4ExactSlabEightLayerCone

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSProjectionSweep
open YMGap.Continuum.BF4ExactSlabConditionalSweep
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabLinkStarGeometry
open YMGap.Continuum.BF4ExactSlabWardStarGeometry
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.BF4ExactSlabStarIndependentProbe
open YMGap.Continuum.BF4ExactSlabStarNonneighborCommutation
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4LinkEightColor

/-- A computed subset of the original physical links, retaining their
membership proofs. No replacement links or omitted boundary links. -/
def layer (extent : Nat) (c : Color) : List (PhysicalLink extent) :=
  (boundaryCompleteSlabLinks extent).attach.filter (fun i => decide (color i.val = c))

theorem mem_layer (extent : Nat) (c : Color) (i : PhysicalLink extent) :
    i ∈ layer extent c ↔ color i.val = c := by
  constructor
  · exact fun h => of_decide_eq_true (List.mem_filter.mp h).2
  · intro h
    exact List.mem_filter.mpr ⟨List.mem_attach _ i, decide_eq_true h⟩

theorem layer_nodup (extent : Nat) (c : Color) : (layer extent c).Nodup := by
  apply List.filter_sublist.nodup
  apply List.Pairwise.of_map (S := fun a b : Z4Link => a ≠ b)
    Subtype.val (fun _ _ h he => h (congrArg Subtype.val he))
  rw [List.attach_map_subtype_val]
  exact boundaryCompleteSlabLinks_nodup extent

def schedule (extent : Nat) : List (PhysicalLink extent) := colors.flatMap (layer extent)

theorem schedule_covers (extent : Nat) (i : PhysicalLink extent) :
    i ∈ schedule extent :=
  List.mem_flatMap.mpr ⟨color i.val, color_mem_colors i.val,
    (mem_layer extent (color i.val) i).mpr rfl⟩

private theorem layers_nodup (extent : Nat) (cs : List Color) (hc : cs.Nodup) :
    (cs.flatMap (layer extent)).Nodup := by
  induction cs with
  | nil => exact List.nodup_nil
  | cons c rest ih =>
    have hparts := List.nodup_cons.mp hc
    apply List.nodup_append.mpr
    refine ⟨layer_nodup extent c, ih hparts.2, ?_⟩
    intro i hi j hj he
    subst j
    obtain ⟨d, hd, hid⟩ := List.mem_flatMap.mp hj
    have hcd : c = d := ((mem_layer extent c i).mp hi).symm.trans
      ((mem_layer extent d i).mp hid)
    exact hparts.1 (hcd.symm ▸ hd)

theorem schedule_nodup (extent : Nat) : (schedule extent).Nodup :=
  layers_nodup extent colors colors_nodup

/-- One star expansion, deduplicated at each step to avoid retaining an
exponentially duplicated path list. -/
def expand (extent : Nat) (support : List Z4Link) : List Z4Link :=
  (support.flatMap (starLinks extent)).eraseDups

theorem mem_expand (extent : Nat) (support : List Z4Link) (j : Z4Link) :
    j ∈ expand extent support ↔ ∃ i, i ∈ support ∧ Near extent i j := by
  simp only [expand, List.mem_eraseDups, List.mem_flatMap, Near]

theorem support_mem_expand (extent : Nat) (support : List Z4Link) (i : Z4Link)
    (hi : i ∈ support) : i ∈ expand extent support :=
  (mem_expand extent support i).mpr ⟨i, hi, near_refl extent i⟩

def grow (extent : Nat) : Nat → List Z4Link → List Z4Link
  | 0, support => support
  | n+1, support => grow extent n (expand extent support)

/-- A computed list of n complete eight-color rounds. -/
def cycles : Nat → List Color
  | 0 => []
  | n+1 => colors ++ cycles n

theorem cycles_length (n : Nat) : (cycles n).length = 8*n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [cycles, List.length_append, colors_length, ih]
    omega

theorem mem_grow (extent n : Nat) (support : List Z4Link) (i : Z4Link)
    (hi : i ∈ support) : i ∈ grow extent n support := by
  induction n generalizing support with
  | zero => exact hi
  | succ n ih => exact ih (expand extent support) (support_mem_expand extent support i hi)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K)

local notation "F" => fullData hw0 hw1 K extent hK
local notation "P" => projections hw0 hw1 K extent hK

/-- An operational, completed notion of support. This predicate asserts
actual equalities of original-action operators, not polynomial syntax. -/
def Localized (support : List Z4Link) (x : GNSCompletionSpace F) : Prop :=
  ∀ i : PhysicalLink extent, i.val ∉ support → (P).op i x = x

theorem localized_embed (support : List Z4Link) (p : (F).V)
    (hp : LinkLocal extent support p.val) :
    Localized hw0 hw1 K extent hK support (embedV F p) := by
  intro i hi
  exact conditionalProjection_fix_local hw0 hw1 K extent hK
    i.val i.property support p hp hi

theorem same_color_commute (i j : PhysicalLink extent)
    (hc : color i.val = color j.val) (x : GNSCompletionSpace F) :
    (P).op i ((P).op j x) = (P).op j ((P).op i x) := by
  by_cases he : i.val = j.val
  · have hij : i = j := Subtype.ext he
    subst j
    rfl
  · apply conditionalProjection_commute
    intro hj
    obtain ⟨id, hid, hj⟩ := List.mem_flatMap.mp hj
    have hi := (mem_incidentIds_iff extent i.val id).mp hid
    exact he (same_color_on_face_eq (slabPlaquetteAt extent id)
      i.val j.val hi.2 hj hc)

theorem layer_commute (c : Color) (i j : PhysicalLink extent)
    (hi : i ∈ layer extent c) (hj : j ∈ layer extent c) (x : GNSCompletionSpace F) :
    (P).op i ((P).op j x) = (P).op j ((P).op i x) :=
  same_color_commute hw0 hw1 K extent hK i j
    (((mem_layer extent c i).mp hi).trans ((mem_layer extent c j).mp hj).symm) x

def activeLayer (extent : Nat) (c : Color) (support : List Z4Link) :
    List (PhysicalLink extent) :=
  (layer extent c).filter (fun i => decide (i.val ∈ support))

/-- Exact deletion of every initially inactive update in one full physical
color layer. The actual original-action completed output is unchanged. -/
theorem layer_prune (c : Color) (support : List Z4Link) (x : GNSCompletionSpace F)
    (hx : Localized hw0 hw1 K extent hK support x) :
    (P).sweep (layer extent c) x = (P).sweep (activeLayer extent c support) x := by
  apply (P).sweep_filter
  · intro i hi j hj y
    exact layer_commute hw0 hw1 K extent hK c i j hi hj y
  · intro i _ hi
    apply hx i
    exact of_decide_eq_false hi

/-- A completed layer has at most ONE star of conditional support growth,
however many distant updates it contains. -/
theorem layer_localized (c : Color) (support : List Z4Link) (x : GNSCompletionSpace F)
    (hx : Localized hw0 hw1 K extent hK support x) :
    Localized hw0 hw1 K extent hK (expand extent support)
      ((P).sweep (layer extent c) x) := by
  rw [layer_prune hw0 hw1 K extent hK c support x hx]
  intro j hj
  have hfix : (P).op j x = x := hx j
    (fun h => hj (support_mem_expand extent support j.val h))
  have hcomm : ∀ i, i ∈ activeLayer extent c support → ∀ y,
      (P).op j ((P).op i y) = (P).op i ((P).op j y) := by
    intro i hi y
    have hiS : i.val ∈ support := of_decide_eq_true (List.mem_filter.mp hi).2
    have hfar : j.val ∉ faceLinks extent (incidentIds extent i.val) := by
      intro hnear
      exact hj ((mem_expand extent support j.val).mpr
        ⟨i.val, hiS, List.mem_cons_of_mem i.val hnear⟩)
    exact (conditionalProjection_commute hw0 hw1 K extent hK
      i.val j.val i.property j.property hfar y).symm
  rw [(P).op_sweep j (activeLayer extent c support) hcomm, hfix]

def runLayers (cs : List Color) (x : GNSCompletionSpace F) : GNSCompletionSpace F :=
  (P).sweep (cs.flatMap (layer extent)) x

theorem runLayers_cons (c : Color) (cs : List Color) (x : GNSCompletionSpace F) :
    runLayers hw0 hw1 K extent hK (c :: cs) x =
      runLayers hw0 hw1 K extent hK cs ((P).sweep (layer extent c) x) :=
  (P).sweep_append _ _ x

/-- Explicit truncated cone computation. The region is enlarged once after
each layer, and only updates meeting its current region are retained. -/
def coneLayers (cs : List Color) (support : List Z4Link) (x : GNSCompletionSpace F) :
    GNSCompletionSpace F :=
  match cs with
  | [] => x
  | c :: rest => coneLayers rest (expand extent support)
      ((P).sweep (activeLayer extent c support) x)

theorem runLayers_localized (cs : List Color) (support : List Z4Link)
    (x : GNSCompletionSpace F) (hx : Localized hw0 hw1 K extent hK support x) :
    Localized hw0 hw1 K extent hK (grow extent cs.length support)
      (runLayers hw0 hw1 K extent hK cs x) := by
  induction cs generalizing support x with
  | nil => exact hx
  | cons c rest ih =>
    rw [runLayers_cons]
    exact ih (expand extent support) ((P).sweep (layer extent c) x)
      (layer_localized hw0 hw1 K extent hK c support x hx)

theorem runLayers_eq_cone (cs : List Color) (support : List Z4Link)
    (x : GNSCompletionSpace F) (hx : Localized hw0 hw1 K extent hK support x) :
    runLayers hw0 hw1 K extent hK cs x = coneLayers hw0 hw1 K extent hK cs support x := by
  induction cs generalizing support x with
  | nil => rfl
  | cons c rest ih =>
    rw [runLayers_cons]
    have hnext := layer_localized hw0 hw1 K extent hK c support x hx
    rw [ih (expand extent support) ((P).sweep (layer extent c) x) hnext,
      layer_prune hw0 hw1 K extent hK c support x hx]
    rfl

/-- One COMPLETE physical sweep, each link once, has only eight star
expansions of conditional support, independent of volume, K and w. -/
theorem eight_layer_localized (support : List Z4Link) (x : GNSCompletionSpace F)
    (hx : Localized hw0 hw1 K extent hK support x) :
    Localized hw0 hw1 K extent hK (grow extent 8 support)
      ((P).sweep (schedule extent) x) :=
  runLayers_localized hw0 hw1 K extent hK colors support x hx

/-- Literal source support supplies the input to the exact full/cone pin. -/
theorem eight_layer_cone_embed (support : List Z4Link) (p : (F).V)
    (hp : LinkLocal extent support p.val) :
    (P).sweep (schedule extent) (embedV F p) =
      coneLayers hw0 hw1 K extent hK colors support (embedV F p) :=
  runLayers_eq_cone hw0 hw1 K extent hK colors support (embedV F p)
    (localized_embed hw0 hw1 K extent hK support p hp)

/-- A test outside the active layer region is fixed by every retained
operator. Self-adjointness gives an exact SAME-form pairing identity. -/
theorem layer_pairing (c : Color) (support testSupport : List Z4Link)
    (x y : GNSCompletionSpace F)
    (hx : Localized hw0 hw1 K extent hK support x)
    (hy : Localized hw0 hw1 K extent hK testSupport y)
    (hsep : LinksDisjoint support testSupport) :
    (F).cinnerCompl ((P).sweep (layer extent c) x) y = (F).cinnerCompl x y := by
  rw [layer_prune hw0 hw1 K extent hK c support x hx]
  apply (P).sweep_pair_fixed
  intro i hi
  apply hy i
  exact hsep i.val (of_decide_eq_true (List.mem_filter.mp hi).2)

/-- Until the growing cone meets the test, ANY finite list of color layers
preserves the original interacting pairing exactly. -/
theorem runLayers_pairing (cs : List Color) (support testSupport : List Z4Link)
    (x y : GNSCompletionSpace F)
    (hx : Localized hw0 hw1 K extent hK support x)
    (hy : Localized hw0 hw1 K extent hK testSupport y)
    (hsep : LinksDisjoint (grow extent cs.length support) testSupport) :
    (F).cinnerCompl (runLayers hw0 hw1 K extent hK cs x) y = (F).cinnerCompl x y := by
  induction cs generalizing support x with
  | nil => rfl
  | cons c rest ih =>
    rw [runLayers_cons]
    have hn := layer_localized hw0 hw1 K extent hK c support x hx
    rw [ih (expand extent support) ((P).sweep (layer extent c) x) hn hsep]
    apply layer_pairing hw0 hw1 K extent hK c support testSupport x y hx hy
    intro i hi
    exact hsep i (mem_grow extent (c :: rest).length support i hi)

/-- Source syntax pins both inputs to the exact separated-test identity.
This is an unnormalized covariance precursor, not a decay estimate. -/
theorem eight_layer_pairing_embed (support testSupport : List Z4Link)
    (p q : (F).V) (hp : LinkLocal extent support p.val)
    (hq : LinkLocal extent testSupport q.val)
    (hsep : LinksDisjoint (grow extent 8 support) testSupport) :
    (F).cinnerCompl ((P).sweep (schedule extent) (embedV F p)) (embedV F q) =
      (F).cinnerCompl (embedV F p) (embedV F q) :=
  runLayers_pairing hw0 hw1 K extent hK colors support testSupport
    (embedV F p) (embedV F q)
    (localized_embed hw0 hw1 K extent hK support p hp)
    (localized_embed hw0 hw1 K extent hK testSupport q hq) hsep

/-- The cycle enumeration really is iteration of the full physical sweep,
not an unrelated family of local approximants. -/
theorem cycles_succ (n : Nat) (x : GNSCompletionSpace F) :
    runLayers hw0 hw1 K extent hK (cycles (n+1)) x =
      runLayers hw0 hw1 K extent hK (cycles n) ((P).sweep (schedule extent) x) := by
  unfold runLayers
  rw [cycles, List.flatMap_append, (P).sweep_append]
  rfl

/-- n complete sweeps have at most 8*n star expansions of conditional
support, with no volume or heat-cutoff factor. -/
theorem cycles_localized (n : Nat) (support : List Z4Link) (x : GNSCompletionSpace F)
    (hx : Localized hw0 hw1 K extent hK support x) :
    Localized hw0 hw1 K extent hK (grow extent (8*n) support)
      (runLayers hw0 hw1 K extent hK (cycles n) x) := by
  have h := runLayers_localized hw0 hw1 K extent hK (cycles n) support x hx
  rwa [cycles_length] at h

/-- Exact iterated SAME-pairing identity up to the first cone/test contact.
No strict contraction or zero-covariance premise is assumed here. -/
theorem cycles_pairing (n : Nat) (support testSupport : List Z4Link)
    (x y : GNSCompletionSpace F)
    (hx : Localized hw0 hw1 K extent hK support x)
    (hy : Localized hw0 hw1 K extent hK testSupport y)
    (hsep : LinksDisjoint (grow extent (8*n) support) testSupport) :
    (F).cinnerCompl (runLayers hw0 hw1 K extent hK (cycles n) x) y =
      (F).cinnerCompl x y := by
  apply runLayers_pairing hw0 hw1 K extent hK (cycles n) support testSupport x y hx hy
  rwa [cycles_length]

#print axioms schedule_covers
#print axioms schedule_nodup
#print axioms mem_expand
#print axioms localized_embed
#print axioms same_color_commute
#print axioms layer_prune
#print axioms layer_localized
#print axioms runLayers_localized
#print axioms runLayers_eq_cone
#print axioms eight_layer_localized
#print axioms eight_layer_cone_embed
#print axioms layer_pairing
#print axioms runLayers_pairing
#print axioms eight_layer_pairing_embed
#print axioms cycles_length
#print axioms cycles_succ
#print axioms cycles_localized
#print axioms cycles_pairing

end YMGap.Continuum.BF4ExactSlabEightLayerCone
