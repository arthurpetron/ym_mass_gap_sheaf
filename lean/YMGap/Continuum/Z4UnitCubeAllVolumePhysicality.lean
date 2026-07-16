/-
# All-volume physicality of the elementary cube mode

The six-face cube label was originally checked only in the size-two box.
Here the geometric incidence parity, the numerical enumeration bridge, and
the exact degree-six link bound are propagated through every trivalent fusion
chain.  The resulting label is gauge-admissible and genuinely nonvacuum in
every finite box containing the cube.
-/

import YMGap.Continuum.Z4UnitCubeFullPrefixParity
import YMGap.Continuum.Z4FiniteBoxIncidentDegreeBound

namespace YMGap.Continuum.Z4UnitCubeAllVolumePhysicality

open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4FiniteBoxPacketState
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4UnitCubeEnumerationParity
open YMGap.Continuum.Z4UnitCubeFullPrefixParity
open YMGap.Continuum.Z4FiniteBoxIncidentDegreeBound
open YMGap.Continuum.Z4UnitCubeSurfaceGeometry
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

def paritySpin (c : Nat) : Nat := if c % 2 = 1 then 2 else 0

private theorem paritySpin_eq_zero_of_mod_zero {c : Nat} (hc : c % 2 = 0) :
    paritySpin c = 0 := by
  unfold paritySpin
  rw [if_neg]
  omega

private theorem paritySpin_eq_two_of_mod_one {c : Nat} (hc : c % 2 = 1) :
    paritySpin c = 2 := by
  unfold paritySpin
  rw [if_pos hc]

private theorem add_mod_two_zero_zero {a b : Nat}
    (ha : a % 2 = 0) (hb : b % 2 = 0) : (a + b) % 2 = 0 := by
  rw [Nat.add_mod, ha, hb]

private theorem add_mod_two_zero_one {a b : Nat}
    (ha : a % 2 = 0) (hb : b % 2 = 1) : (a + b) % 2 = 1 := by
  rw [Nat.add_mod, ha, hb]

private theorem add_mod_two_one_zero {a b : Nat}
    (ha : a % 2 = 1) (hb : b % 2 = 0) : (a + b) % 2 = 1 := by
  rw [Nat.add_mod, ha, hb]

private theorem add_mod_two_one_one {a b : Nat}
    (ha : a % 2 = 1) (hb : b % 2 = 1) : (a + b) % 2 = 0 := by
  rw [Nat.add_mod, ha, hb]

theorem fusionOK_paritySpin_add (a b : Nat) :
    fusionOK (paritySpin a) (paritySpin b) (paritySpin (a + b)) = true := by
  rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
    rcases Nat.mod_two_eq_zero_or_one b with hb | hb
  · rw [paritySpin_eq_zero_of_mod_zero ha,
      paritySpin_eq_zero_of_mod_zero hb,
      paritySpin_eq_zero_of_mod_zero (add_mod_two_zero_zero ha hb)]
    decide
  · rw [paritySpin_eq_zero_of_mod_zero ha,
      paritySpin_eq_two_of_mod_one hb,
      paritySpin_eq_two_of_mod_one (add_mod_two_zero_one ha hb)]
    decide
  · rw [paritySpin_eq_two_of_mod_one ha,
      paritySpin_eq_zero_of_mod_zero hb,
      paritySpin_eq_two_of_mod_one (add_mod_two_one_zero ha hb)]
    decide
  · rw [paritySpin_eq_two_of_mod_one ha,
      paritySpin_eq_two_of_mod_one hb,
      paritySpin_eq_zero_of_mod_zero (add_mod_two_one_one ha hb)]
    decide

theorem enumerateFrom_get?_of_mem {a : Type} {start i : Nat} {x : a} :
    ∀ {xs : List a}, (i, x) ∈ enumerateFrom start xs →
      (enumerateFrom start xs)[i - start]? = some (i, x)
  | [], h => by cases h
  | y :: ys, h => by
      simp only [enumerateFrom, List.mem_cons] at h
      rcases h with h | h
      · have hi : i = start := congrArg Prod.fst h
        have hx : x = y := congrArg Prod.snd h
        rw [hi, hx]
        simp [enumerateFrom]
      · have hge := enumerateFrom_index_ge h
        have ih := enumerateFrom_get?_of_mem h
        have hidx : i - start = (i - (start + 1)) + 1 := by omega
        rw [hidx]
        exact ih

theorem enumerate_get?_of_mem {a : Type} {xs : List a} {i : Nat} {x : a}
    (h : (i, x) ∈ enumerate xs) : (enumerate xs)[i]? = some (i, x) := by
  have hg := enumerateFrom_get?_of_mem h
  simpa only [Nat.sub_zero] using hg

theorem enumerateFrom_index_lt {a : Type} {start i : Nat} {x : a} :
    ∀ {xs : List a}, (i, x) ∈ enumerateFrom start xs →
      i < start + xs.length
  | [], h => by cases h
  | y :: ys, h => by
      simp only [enumerateFrom, List.mem_cons] at h
      rcases h with h | h
      · have hi : i = start := congrArg Prod.fst h
        rw [hi]
        simp
      · have ht := enumerateFrom_index_lt h
        simp only [List.length_cons]
        omega

theorem enumerate_index_lt {a : Type} {xs : List a} {i : Nat} {x : a}
    (h : (i, x) ∈ enumerate xs) : i < xs.length := by
  have ht := enumerateFrom_index_lt h
  simpa only [Nat.zero_add] using ht

theorem vertexEdge_mem_usedResolutionEdges {n : Nat} {v : TrivalentVertex}
    (hv : v ∈ resolutionVertices n) {edge : Nat}
    (he : edge ∈ vertexEdgeIds v) : edge ∈ usedResolutionEdges n := by
  by_cases hphysical : edge < plaquetteEdgeCount n
  · apply List.mem_append_left
    exact List.mem_range.mpr hphysical
  · apply List.mem_append_right
    unfold usedAuxiliaryEdges
    simp only [List.mem_eraseDups, List.mem_filter, decide_eq_true_eq]
    refine ⟨List.mem_flatMap.mpr ⟨v, hv, he⟩, ?_⟩
    omega

theorem incidentPlaqId_lt_count {n : Nat} {ell : Z4Link} {edge : Nat}
    (he : edge ∈ incidentPlaqIds n ell) : edge < plaquetteEdgeCount n := by
  obtain ⟨p, hp, _⟩ := mem_incidentPlaqIds.mp he
  unfold plaquetteEdgeCount
  exact enumerate_index_lt hp

theorem incidentPlaqId_mem_used {n : Nat} {ell : Z4Link} {edge : Nat}
    (he : edge ∈ incidentPlaqIds n ell) : edge ∈ usedResolutionEdges n := by
  apply List.mem_append_left
  exact List.mem_range.mpr (incidentPlaqId_lt_count he)

theorem incidentPlaqIdsByLinkId_eq {n linkId : Nat} {ell : Z4Link}
    (hindexed : (linkId, ell) ∈ enumerate (distinctBoxLinks n)) :
    incidentPlaqIdsByLinkId n linkId = incidentPlaqIds n ell := by
  have hget := enumerate_get?_of_mem hindexed
  unfold incidentPlaqIdsByLinkId
  rw [hget]

def selectedCount (sel : Nat → Bool) (xs : List Nat) : Nat :=
  (xs.filter sel).length

def selectedOne (sel : Nat → Bool) (x : Nat) : Nat :=
  if sel x then 1 else 0

theorem selectedCount_cons (sel : Nat → Bool) (x : Nat) (xs : List Nat) :
    selectedCount sel (x :: xs) = selectedOne sel x + selectedCount sel xs := by
  unfold selectedCount selectedOne
  by_cases hx : sel x = true <;> simp [hx, Nat.add_comm]

theorem paritySpin_zero : paritySpin 0 = 0 := rfl

theorem paritySpin_eq_zero_of_even {c : Nat} (hc : c % 2 = 0) :
    paritySpin c = 0 := by simp [paritySpin, hc]

theorem paritySpin_eq_of_sum_even {a b : Nat} (h : (a + b) % 2 = 0) :
    paritySpin a = paritySpin b := by
  rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
    rcases Nat.mod_two_eq_zero_or_one b with hb | hb
  · rw [paritySpin_eq_zero_of_mod_zero ha,
      paritySpin_eq_zero_of_mod_zero hb]
  · have hab := add_mod_two_zero_one ha hb
    rw [hab] at h
    contradiction
  · have hab := add_mod_two_one_zero ha hb
    rw [hab] at h
    contradiction
  · rw [paritySpin_eq_two_of_mod_one ha,
      paritySpin_eq_two_of_mod_one hb]

theorem fuseChain_verticesAdmissibleB_parity
    (label : EdgeLabelling) (sel : Nat → Bool) (vacuum : Nat) :
    ∀ (tail : List Nat) (aux left right c : Nat),
      label vacuum = 0 →
      label left = paritySpin c →
      (∀ e, e ∈ right :: tail →
        label e = paritySpin (selectedOne sel e)) →
      (∀ j, j + 3 ≤ (right :: tail).length →
        label (aux + j) = paritySpin
          (c + selectedCount sel ((right :: tail).take (j + 1)))) →
      (c + selectedCount sel (right :: tail)) % 2 = 0 →
      verticesAdmissibleB (fuseChain vacuum aux left right tail) label = true
  | [], aux, left, right, c, hvac, hleft, hinputs, _, hfull => by
      simp only [fuseChain, verticesAdmissibleB]
      have hright := hinputs right List.mem_cons_self
      rw [hleft, hright, hvac]
      have hcount : selectedCount sel [right] = selectedOne sel right := by
        rw [selectedCount_cons]
        rfl
      rw [hcount] at hfull
      have hout : paritySpin (c + selectedOne sel right) = 0 :=
        paritySpin_eq_zero_of_even hfull
      rw [← hout]
      rw [if_pos (fusionOK_paritySpin_add c (selectedOne sel right))]
  | [last], aux, left, right, c, _, hleft, hinputs, _, hfull => by
      simp only [fuseChain, verticesAdmissibleB]
      have hright := hinputs right List.mem_cons_self
      have hlast := hinputs last (by simp)
      rw [hleft, hright, hlast]
      have hcount : selectedCount sel [right, last] =
          selectedOne sel right + selectedOne sel last := by
        rw [selectedCount_cons, selectedCount_cons]
        rfl
      rw [hcount] at hfull
      have hfull' :
          ((c + selectedOne sel right) + selectedOne sel last) % 2 = 0 := by
        simpa only [Nat.add_assoc] using hfull
      have hout : paritySpin (c + selectedOne sel right) =
          paritySpin (selectedOne sel last) :=
        paritySpin_eq_of_sum_even hfull'
      rw [← hout]
      rw [if_pos (fusionOK_paritySpin_add c (selectedOne sel right))]
  | next :: after :: rest, aux, left, right, c,
      hvac, hleft, hinputs, haux, hfull => by
      simp only [fuseChain, verticesAdmissibleB]
      have hright := hinputs right List.mem_cons_self
      have haux0 := haux 0 (by simp)
      have htake : (right :: next :: after :: rest).take 1 = [right] := rfl
      have hcount : selectedCount sel [right] = selectedOne sel right := by
        rw [selectedCount_cons]
        rfl
      rw [Nat.add_zero, htake, hcount] at haux0
      rw [hleft, hright, haux0]
      rw [if_pos (fusionOK_paritySpin_add c (selectedOne sel right))]
      apply fuseChain_verticesAdmissibleB_parity label sel vacuum
        (after :: rest) (aux + 1) aux next
        (c + selectedOne sel right) hvac haux0
      · intro e he
        exact hinputs e (List.mem_cons_of_mem right he)
      · intro j hj
        have hold := haux (j + 1) (by simp only [List.length_cons] at hj ⊢; omega)
        have htakeSucc :
            (right :: next :: after :: rest).take (j + 1 + 1) =
              right :: (next :: after :: rest).take (j + 1) := by
          rfl
        have hedge : aux + (j + 1) = aux + 1 + j := by omega
        rw [hedge, htakeSucc, selectedCount_cons] at hold
        simpa only [Nat.add_assoc] using hold
      · rw [selectedCount_cons] at hfull
        simpa only [Nat.add_assoc] using hfull

theorem fuseLabels_verticesAdmissibleB_parity
    (label : EdgeLabelling) (sel : Nat → Bool) (vacuum aux : Nat)
    (labels : List Nat)
    (hvac : label vacuum = 0)
    (hinputs : ∀ e, e ∈ labels →
      label e = paritySpin (selectedOne sel e))
    (haux : ∀ j, j + 4 ≤ labels.length →
      label (aux + j) =
        paritySpin (selectedCount sel (labels.take (j + 2))))
    (hfull : selectedCount sel labels % 2 = 0) :
    verticesAdmissibleB (fuseLabels vacuum aux labels) label = true := by
  cases labels with
  | nil => rfl
  | cons only rest =>
      cases rest with
      | nil =>
          simp only [fuseLabels, verticesAdmissibleB]
          rw [hinputs only List.mem_cons_self, hvac]
          have hc : selectedCount sel [only] = selectedOne sel only := by
            rw [selectedCount_cons]
            rfl
          rw [hc] at hfull
          have hzero := paritySpin_eq_zero_of_even hfull
          rw [hzero]
          decide
      | cons right tail =>
          apply fuseChain_verticesAdmissibleB_parity label sel vacuum tail aux
            only right (selectedOne sel only) hvac
            (hinputs only List.mem_cons_self)
          · intro e he
            exact hinputs e (List.mem_cons_of_mem only he)
          · intro j hj
            have ha := haux j (by simp only [List.length_cons] at hj ⊢; omega)
            simpa only [List.take, selectedCount_cons] using ha
          · rw [selectedCount_cons] at hfull
            exact hfull

theorem fuseChain_aux_has_vertex (vacuum : Nat) :
    ∀ (tail : List Nat) (aux left right j : Nat),
      j + 3 ≤ (right :: tail).length →
      ∃ v, v ∈ fuseChain vacuum aux left right tail ∧
        aux + j ∈ vertexEdgeIds v
  | [], _, _, _, _, h => by simp at h
  | [last], _, _, _, _, h => by simp at h
  | next :: after :: rest, aux, left, right, j, h => by
      cases j with
      | zero =>
          refine ⟨(left, right, aux), by simp [fuseChain], ?_⟩
          simp [vertexEdgeIds]
      | succ j =>
          have hrec : j + 3 ≤ (next :: after :: rest).length := by
            simp only [List.length_cons] at h ⊢
            omega
          obtain ⟨v, hv, hedge⟩ := fuseChain_aux_has_vertex vacuum
            (after :: rest) (aux + 1) aux next j hrec
          refine ⟨v, by simp [fuseChain, hv], ?_⟩
          have heq : aux + (j + 1) = aux + 1 + j := by omega
          simpa only [heq] using hedge

theorem fuseLabels_aux_has_vertex (vacuum aux : Nat) (labels : List Nat)
    (j : Nat) (h : j + 4 ≤ labels.length) :
    ∃ v, v ∈ fuseLabels vacuum aux labels ∧
      aux + j ∈ vertexEdgeIds v := by
  cases labels with
  | nil => simp at h
  | cons left rest =>
      cases rest with
      | nil => simp at h
      | cons right tail =>
          have hchain : j + 3 ≤ (right :: tail).length := by
            simp only [List.length_cons] at h ⊢
            omega
          simpa only [fuseLabels] using
            (fuseChain_aux_has_vertex vacuum tail aux left right j hchain)

def cubeSelected (n : Nat) (edge : Nat) : Bool :=
  decide (edge ∈ unitCubeSurfaceIds n)

theorem selectedPrefixCount_eq_selectedCount {n linkId : Nat} {ell : Z4Link}
    (hindexed : (linkId, ell) ∈ enumerate (distinctBoxLinks n))
    (prefixLength : Nat) :
    selectedPrefixCount n linkId prefixLength =
      selectedCount (cubeSelected n)
        ((incidentPlaqIds n ell).take prefixLength) := by
  unfold selectedPrefixCount selectedCount cubeSelected
  rw [incidentPlaqIdsByLinkId_eq hindexed]

theorem unitCubeSurfaceLabel_on_incident {n : Nat} {ell : Z4Link}
    {edge : Nat} (he : edge ∈ incidentPlaqIds n ell) :
    unitCubeSurfaceLabel n edge =
      paritySpin (selectedOne (cubeSelected n) edge) := by
  have hused := incidentPlaqId_mem_used he
  have hlt := incidentPlaqId_lt_count he
  by_cases hselected : edge ∈ unitCubeSurfaceIds n
  · simp [unitCubeSurfaceLabel, hused, hlt, paritySpin,
      selectedOne, cubeSelected, hselected]
  · simp [unitCubeSurfaceLabel, hused, hlt, paritySpin,
      selectedOne, cubeSelected, hselected]

theorem linkAux_mem_used {n linkId : Nat} {ell : Z4Link}
    (hindexed : (linkId, ell) ∈ enumerate (distinctBoxLinks n))
    (j : Nat) (hj : j + 4 ≤ (incidentPlaqIds n ell).length) :
    linkBlockBase n linkId + 1 + j ∈ usedResolutionEdges n := by
  obtain ⟨v, hv, hedge⟩ := fuseLabels_aux_has_vertex
    (linkBlockBase n linkId) (linkBlockBase n linkId + 1)
    (incidentPlaqIds n ell) j hj
  have hvglobal : v ∈ resolutionVertices n := by
    unfold resolutionVertices linkResolutionVertices
    exact List.mem_flatMap.mpr ⟨(linkId, ell), hindexed, hv⟩
  exact vertexEdge_mem_usedResolutionEdges hvglobal hedge

theorem unitCubeSurfaceLabel_on_linkAux {n linkId : Nat} {ell : Z4Link}
    (hindexed : (linkId, ell) ∈ enumerate (distinctBoxLinks n))
    (j : Nat) (hj : j + 4 ≤ (incidentPlaqIds n ell).length) :
    unitCubeSurfaceLabel n (linkBlockBase n linkId + 1 + j) =
      paritySpin (selectedCount (cubeSelected n)
        ((incidentPlaqIds n ell).take (j + 2))) := by
  let edge := linkBlockBase n linkId + 1 + j
  have hused : edge ∈ usedResolutionEdges n :=
    linkAux_mem_used hindexed j hj
  have hdegree := incidentPlaqIds_length_le_six n ell
  have hjlt : 1 + j < 8 := by omega
  have hge : plaquetteEdgeCount n ≤ edge := by
    dsimp only [edge]
    unfold linkBlockBase
    omega
  have hdelta : edge - plaquetteEdgeCount n = 8 * linkId + (1 + j) := by
    dsimp only [edge]
    unfold linkBlockBase
    omega
  have hoffset : (edge - plaquetteEdgeCount n) % 8 = 1 + j := by
    rw [hdelta]
    omega
  have hblock : (edge - plaquetteEdgeCount n) / 8 = linkId := by
    rw [hdelta]
    omega
  have hprefix := selectedPrefixCount_eq_selectedCount hindexed (j + 2)
  dsimp only [edge] at hused hge hoffset hblock ⊢
  unfold unitCubeSurfaceLabel
  rw [if_pos hused, if_neg (Nat.not_lt.mpr hge)]
  simp only [hoffset, hblock]
  rw [if_neg (by omega : 1 + j ≠ 0)]
  rw [show 1 + j + 1 = j + 2 by omega]
  rw [hprefix]
  rfl

theorem unitCubeSurfaceLabel_on_vacuumBase (n linkId : Nat) :
    unitCubeSurfaceLabel n (linkBlockBase n linkId) = 0 := by
  by_cases hused : linkBlockBase n linkId ∈ usedResolutionEdges n
  · have hge : plaquetteEdgeCount n ≤ linkBlockBase n linkId := by
      unfold linkBlockBase
      omega
    have hdelta : linkBlockBase n linkId - plaquetteEdgeCount n =
        8 * linkId := by
      unfold linkBlockBase
      omega
    unfold unitCubeSurfaceLabel
    rw [if_pos hused, if_neg (Nat.not_lt.mpr hge)]
    rw [hdelta]
    simp
  · simp [unitCubeSurfaceLabel, hused]

theorem selectedCount_cube_incident_even {n linkId : Nat} {ell : Z4Link}
    (hn : 2 ≤ n)
    (hindexed : (linkId, ell) ∈ enumerate (distinctBoxLinks n)) :
    selectedCount (cubeSelected n) (incidentPlaqIds n ell) % 2 = 0 := by
  have hfull := selectedPrefixCount_full_even hn linkId
  rw [incidentPlaqIdsByLinkId_eq hindexed] at hfull
  unfold selectedPrefixCount at hfull
  rw [incidentPlaqIdsByLinkId_eq hindexed] at hfull
  unfold selectedCount cubeSelected
  rw [List.take_length] at hfull
  exact hfull

theorem linkResolutionVertices_cube_admissible {n linkId : Nat}
    {ell : Z4Link} (hn : 2 ≤ n)
    (hindexed : (linkId, ell) ∈ enumerate (distinctBoxLinks n)) :
    verticesAdmissibleB (linkResolutionVertices n linkId ell)
      (unitCubeSurfaceLabel n) = true := by
  unfold linkResolutionVertices
  apply fuseLabels_verticesAdmissibleB_parity
    (unitCubeSurfaceLabel n) (cubeSelected n)
    (linkBlockBase n linkId) (linkBlockBase n linkId + 1)
    (incidentPlaqIds n ell)
  · exact unitCubeSurfaceLabel_on_vacuumBase n linkId
  · intro edge he
    exact unitCubeSurfaceLabel_on_incident he
  · intro j hj
    exact unitCubeSurfaceLabel_on_linkAux hindexed j hj
  · exact selectedCount_cube_incident_even hn hindexed

theorem verticesAdmissibleB_append_true (label : EdgeLabelling) :
    ∀ xs ys : List TrivalentVertex,
      verticesAdmissibleB xs label = true →
      verticesAdmissibleB ys label = true →
      verticesAdmissibleB (xs ++ ys) label = true
  | [], ys, _, hy => hy
  | x :: xs, ys, hx, hy => by
      simp only [verticesAdmissibleB] at hx
      change (if fusionOK (label x.1) (label x.2.1) (label x.2.2) = true
        then verticesAdmissibleB (xs ++ ys) label else false) = true
      by_cases hguard :
          fusionOK (label x.1) (label x.2.1) (label x.2.2) = true
      · rw [if_pos hguard] at hx ⊢
        exact verticesAdmissibleB_append_true label xs ys hx hy
      · rw [if_neg hguard] at hx
        contradiction

theorem verticesAdmissibleB_flatMap_true {a : Type}
    (label : EdgeLabelling) (f : a → List TrivalentVertex) :
    ∀ xs : List a,
      (∀ x, x ∈ xs → verticesAdmissibleB (f x) label = true) →
      verticesAdmissibleB (xs.flatMap f) label = true
  | [], _ => rfl
  | x :: xs, h => by
      simp only [List.flatMap_cons]
      apply verticesAdmissibleB_append_true label
      · exact h x List.mem_cons_self
      · apply verticesAdmissibleB_flatMap_true label f xs
        intro y hy
        exact h y (List.mem_cons_of_mem x hy)

theorem resolutionVertices_cube_admissible {n : Nat} (hn : 2 ≤ n) :
    verticesAdmissibleB (resolutionVertices n) (unitCubeSurfaceLabel n) = true := by
  unfold resolutionVertices
  apply verticesAdmissibleB_flatMap_true
  intro indexed hindexed
  exact linkResolutionVertices_cube_admissible hn hindexed

theorem unitCubeSurfaceLabel_hasExcited {n : Nat} (hn : 2 ≤ n) :
    hasExcitedB (unitCubeSurfaceLabel n) (usedResolutionEdges n) = true := by
  let p : Z4Plaq := ((0, 0, 0, 0), .p01)
  have hpSurface : p ∈ unitCubeSurface := by
    simp [p, unitCubeSurface]
  have hpBox : p ∈ boxPlaquettes n :=
    unitCubeSurface_mem_box hn hpSurface
  obtain ⟨edge, hedge⟩ := exists_mem_enumerate hpBox
  have hselected : edge ∈ unitCubeSurfaceIds n := by
    exact (mem_unitCubeSurfaceIds_iff_of_enumerate hedge).mpr hpSurface
  have hlt : edge < plaquetteEdgeCount n := by
    unfold plaquetteEdgeCount
    exact enumerate_index_lt hedge
  have hused : edge ∈ usedResolutionEdges n := by
    apply List.mem_append_left
    exact List.mem_range.mpr hlt
  have hlabel : unitCubeSurfaceLabel n edge = 2 := by
    simp [unitCubeSurfaceLabel, hused, hlt, hselected]
  apply hasExcitedB_true_of_mem (unitCubeSurfaceLabel n) hused
  rw [hlabel]
  omega

theorem unitCubeSurfaceLabel_physical_all_volumes {n : Nat} (hn : 2 ≤ n) :
    GraphPhysical (usedResolutionEdges n) (resolutionVertices n)
      (unitCubeSurfaceLabel n) := by
  unfold GraphPhysical graphPhysicalB
  rw [unitCubeSurfaceLabel_hasExcited hn,
    resolutionVertices_cube_admissible hn]
  rfl

#print axioms fusionOK_paritySpin_add
#print axioms enumerate_get?_of_mem
#print axioms vertexEdge_mem_usedResolutionEdges
#print axioms fuseChain_verticesAdmissibleB_parity
#print axioms fuseLabels_verticesAdmissibleB_parity
#print axioms unitCubeSurfaceLabel_on_linkAux
#print axioms linkResolutionVertices_cube_admissible
#print axioms resolutionVertices_cube_admissible
#print axioms unitCubeSurfaceLabel_hasExcited
#print axioms unitCubeSurfaceLabel_physical_all_volumes

end YMGap.Continuum.Z4UnitCubeAllVolumePhysicality
