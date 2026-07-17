import YMGap.Continuum.Z4UnitCubeEnumerationParity

namespace YMGap.Continuum.Z4FiniteBoxIncidentDegreeBound

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4UnitCubeEnumerationParity

theorem incidentPlaqIds_length_eq_incidentBoxFaces
    (n : Nat) (ell : Z4Link) :
    (incidentPlaqIds n ell).length =
      ((boxPlaquettes n).filter fun p => decide (ell ∈ edgesOf p)).length := by
  unfold incidentPlaqIds
  rw [List.length_map]
  let entries := enumerate (boxPlaquettes n)
  let pred : Z4Plaq → Bool := fun p => decide (ell ∈ edgesOf p)
  have hmapped : (entries.filter (pred ∘ Prod.snd)).map Prod.snd =
      (boxPlaquettes n).filter pred := by
    rw [← List.filter_map, enumerate_map_snd]
  change (entries.filter (pred ∘ Prod.snd)).length = _
  rw [← List.length_map Prod.snd, hmapped]

theorem incidentPlaqIds_length_le_six (n : Nat) (ell : Z4Link) :
    (incidentPlaqIds n ell).length ≤ 6 := by
  obtain ⟨u, d⟩ := ell
  rw [incidentPlaqIds_length_eq_incidentBoxFaces]
  have hnodup : ((boxPlaquettes n).filter fun p =>
      decide ((u, d) ∈ edgesOf p)).Nodup :=
    List.filter_sublist.nodup (boxPlaquettes_nodup n)
  have hsub : ∀ p, p ∈ ((boxPlaquettes n).filter fun p =>
      decide ((u, d) ∈ edgesOf p)) → p ∈ edgePlaqs u d := by
    intro p hp
    have hinc : (u, d) ∈ edgesOf p := by
      simpa only [decide_eq_true_eq] using (List.mem_filter.mp hp).2
    exact edge_complete p u d hinc
  have hle :=
    YMGap.Continuum.Z4UnitCubeEnumerationParity.nodup_subset_length_le
      _ _ hnodup hsub
  rw [edgePlaqs_length] at hle
  exact hle

end YMGap.Continuum.Z4FiniteBoxIncidentDegreeBound
