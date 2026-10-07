/-
# Explicit finite enumeration of parity shells

The lists below enumerate the actual integer even shell and shifted-odd shell.
They are finite index data, not an assumed shell-count estimate or a completed
theta identity.
-/

import YMGap.Continuum.ThetaParityShellGeometry
import YMGap.Continuum.TorusWilsonAction

namespace YMGap.Continuum.ThetaParityShellEnumeration

set_option autoImplicit false

open YMGap.Continuum.ThetaParityConvolution
open YMGap.Continuum.ThetaParityShellGeometry

/-- Four nonoverlapping sides of the even Manhattan shell. -/
def evenSide0 (T : Nat) : List SignedPair :=
  (List.range T).map (fun i => (Int.ofNat (T-i), Int.ofNat i))

def evenSide1 (T : Nat) : List SignedPair :=
  (List.range T).map (fun i => (-Int.ofNat i, Int.ofNat (T-i)))

def evenSide2 (T : Nat) : List SignedPair :=
  (List.range T).map (fun i => (Int.ofNat i-(T : Int), -Int.ofNat i))

def evenSide3 (T : Nat) : List SignedPair :=
  (List.range T).map (fun i => (Int.ofNat i, Int.ofNat i-(T : Int)))

/-- Actual explicit enumeration of the even shell, in four disjoint sectors. -/
def evenShellIndices (T : Nat) : List SignedPair :=
  evenSide0 T ++ evenSide1 T ++ evenSide2 T ++ evenSide3 T

/-- Four sign sectors of the shifted-odd shell. -/
def oddSide0 (T : Nat) : List SignedPair :=
  (List.range T).map (fun i => (Int.ofNat i, Int.ofNat (T-i-1)))

def oddSide1 (T : Nat) : List SignedPair :=
  (List.range T).map (fun i => (Int.ofNat i, -Int.ofNat (T-i)))

def oddSide2 (T : Nat) : List SignedPair :=
  (List.range T).map (fun i => (-Int.ofNat (i+1), -Int.ofNat (T-i)))

def oddSide3 (T : Nat) : List SignedPair :=
  (List.range T).map (fun i => (-Int.ofNat (i+1), Int.ofNat (T-i-1)))

/-- Actual explicit enumeration of the shifted-odd shell. -/
def oddShellIndices (T : Nat) : List SignedPair :=
  oddSide0 T ++ oddSide1 T ++ oddSide2 T ++ oddSide3 T

/-- The even enumeration has exactly four points per positive shell radius. -/
theorem evenShellIndices_length (T : Nat) :
    (evenShellIndices T).length = 4*T := by
  simp [evenShellIndices, evenSide0, evenSide1, evenSide2, evenSide3]
  omega

/-- The shifted-odd enumeration has exactly four points per shell radius. -/
theorem oddShellIndices_length (T : Nat) :
    (oddShellIndices T).length = 4*T := by
  simp [oddShellIndices, oddSide0, oddSide1, oddSide2, oddSide3]
  omega

/-- Every positive-radius even shell point occurs in the explicit list. -/
theorem evenShellIndices_mem_of_radius (T : Nat) (hT : 1 ≤ T)
    (z : SignedPair) (hr : evenRadius z.1 z.2 = T) :
    z ∈ evenShellIndices T := by
  rcases z with ⟨j,k⟩
  have hsum : j.natAbs + k.natAbs = T := by
    exact_mod_cast hr
  have hsumI : (j.natAbs : Int) + (k.natAbs : Int) = (T : Int) := by
    exact_mod_cast hsum
  by_cases hj : 0 < j
  · by_cases hk : 0 ≤ k
    · let i := k.natAbs
      have hjabs : (j.natAbs : Int) = j := Int.natAbs_of_nonneg (by omega)
      have hkabs : (k.natAbs : Int) = k := Int.natAbs_of_nonneg hk
      rw [hjabs, hkabs] at hsumI
      have hi : i < T := by dsimp [i]; omega
      have hfirst : (Int.ofNat (T-i)) = j := by
        change ((T-i : Nat) : Int) = j
        dsimp [i]
        omega
      have hside : (j,k) ∈ evenSide0 T := by
        unfold evenSide0
        apply List.mem_map.mpr
        refine ⟨i, List.mem_range.mpr hi, ?_⟩
        exact Prod.ext hfirst (by dsimp [i]; omega)
      simp only [evenShellIndices, List.mem_append]
      exact Or.inl (Or.inl (Or.inl hside))
    · have hklt : k < 0 := by omega
      let i := j.natAbs
      have hjabs : (j.natAbs : Int) = j := Int.natAbs_of_nonneg (by omega)
      have hkabs : (k.natAbs : Int) = -k := Int.ofNat_natAbs_of_nonpos (by omega)
      rw [hjabs, hkabs] at hsumI
      have hi : i < T := by dsimp [i]; omega
      have hfirst : Int.ofNat i = j := by dsimp [i]; omega
      have hsecond : Int.ofNat i - (T : Int) = k := by
        dsimp [i]
        omega
      have hside : (j,k) ∈ evenSide3 T := by
        unfold evenSide3
        apply List.mem_map.mpr
        refine ⟨i, List.mem_range.mpr hi, ?_⟩
        exact Prod.ext hfirst hsecond
      simp only [evenShellIndices, List.mem_append]
      exact Or.inr hside
  · have hjle : j ≤ 0 := by omega
    by_cases hk : 0 < k
    · let i := j.natAbs
      have hjabs : (j.natAbs : Int) = -j := Int.ofNat_natAbs_of_nonpos (by omega)
      have hkabs : (k.natAbs : Int) = k := Int.natAbs_of_nonneg (by omega)
      rw [hjabs, hkabs] at hsumI
      have hi : i < T := by dsimp [i]; omega
      have hfirst : -Int.ofNat i = j := by dsimp [i]; omega
      have hsecond : Int.ofNat (T-i) = k := by
        change ((T-i : Nat) : Int) = k
        dsimp [i]
        omega
      have hside : (j,k) ∈ evenSide1 T := by
        unfold evenSide1
        apply List.mem_map.mpr
        refine ⟨i, List.mem_range.mpr hi, ?_⟩
        exact Prod.ext hfirst hsecond
      simp only [evenShellIndices, List.mem_append]
      exact Or.inl (Or.inl (Or.inr hside))
    · have hkle : k ≤ 0 := by omega
      let i := k.natAbs
      have hjabs : (j.natAbs : Int) = -j := Int.ofNat_natAbs_of_nonpos hjle
      have hkabs : (k.natAbs : Int) = -k := Int.ofNat_natAbs_of_nonpos hkle
      rw [hjabs, hkabs] at hsumI
      by_cases hj0 : j = 0
      · have hkabs : (k.natAbs : Int) = -k := Int.ofNat_natAbs_of_nonpos hkle
        have hzero : Int.ofNat 0 = j := by simp [hj0]
        have hneg : Int.ofNat 0 - (T : Int) = k := by
          change (0 : Int) - (T : Int) = k
          omega
        have hside : (j,k) ∈ evenSide3 T := by
          unfold evenSide3
          apply List.mem_map.mpr
          refine ⟨0, List.mem_range.mpr hT, ?_⟩
          exact Prod.ext hzero hneg
        simp only [evenShellIndices, List.mem_append]
        exact Or.inr hside
      have hjlt : j < 0 := by omega
      have hi : i < T := by dsimp [i]; omega
      have hfirst : Int.ofNat i - (T : Int) = j := by
        dsimp [i]
        omega
      have hsecond : -Int.ofNat i = k := by dsimp [i]; omega
      have hside : (j,k) ∈ evenSide2 T := by
        unfold evenSide2
        apply List.mem_map.mpr
        refine ⟨i, List.mem_range.mpr hi, ?_⟩
        exact Prod.ext hfirst hsecond
      simp only [evenShellIndices, List.mem_append]
      exact Or.inl (Or.inr hside)

/-- Every shifted-odd shell point occurs in the explicit list. -/
theorem oddShellIndices_mem_of_radius (T : Nat) (z : SignedPair)
    (hr : oddRadius z.1 z.2 = T) : z ∈ oddShellIndices T := by
  rcases z with ⟨j,k⟩
  have hsum : 2*T = (2*j+1).natAbs + (2*k+1).natAbs := by
    rw [← hr, oddRadius_frequency_formula]
  have hsumI : (2*j+1).natAbs + (2*k+1).natAbs = 2*(T : Int) := by
    exact_mod_cast hsum.symm
  by_cases hj : 0 ≤ j
  · by_cases hk : 0 ≤ k
    · let i := j.natAbs
      have hu : ((2*j+1).natAbs : Int) = 2*j+1 := Int.natAbs_of_nonneg (by omega)
      have hv : ((2*k+1).natAbs : Int) = 2*k+1 := Int.natAbs_of_nonneg (by omega)
      rw [hu, hv] at hsumI
      have hi : i < T := by dsimp [i]; omega
      have hfirst : Int.ofNat i = j := by dsimp [i]; exact Int.natAbs_of_nonneg hj
      have hsecond : Int.ofNat (T-i-1) = k := by
        change ((T-i-1 : Nat) : Int) = k
        dsimp [i]
        omega
      have hside : (j,k) ∈ oddSide0 T := by
        unfold oddSide0
        apply List.mem_map.mpr
        refine ⟨i, List.mem_range.mpr hi, ?_⟩
        exact Prod.ext hfirst hsecond
      simp only [oddShellIndices, List.mem_append]
      exact Or.inl (Or.inl (Or.inl hside))
    · have hklt : k < 0 := by omega
      let i := j.natAbs
      have hu : ((2*j+1).natAbs : Int) = 2*j+1 := Int.natAbs_of_nonneg (by omega)
      have hv : ((2*k+1).natAbs : Int) = -(2*k+1) := Int.ofNat_natAbs_of_nonpos (by omega)
      rw [hu, hv] at hsumI
      have hi : i < T := by dsimp [i]; omega
      have hfirst : Int.ofNat i = j := by dsimp [i]; exact Int.natAbs_of_nonneg hj
      have hsecond : -Int.ofNat (T-i) = k := by
        change -((T-i : Nat) : Int) = k
        dsimp [i]
        omega
      have hside : (j,k) ∈ oddSide1 T := by
        unfold oddSide1
        apply List.mem_map.mpr
        refine ⟨i, List.mem_range.mpr hi, ?_⟩
        exact Prod.ext hfirst hsecond
      simp only [oddShellIndices, List.mem_append]
      exact Or.inl (Or.inl (Or.inr hside))
  · have hjlt : j < 0 := by omega
    by_cases hk : 0 ≤ k
    · let i := (-j-1).natAbs
      have hu : ((2*j+1).natAbs : Int) = -(2*j+1) := Int.ofNat_natAbs_of_nonpos (by omega)
      have hv : ((2*k+1).natAbs : Int) = 2*k+1 := Int.natAbs_of_nonneg (by omega)
      rw [hu, hv] at hsumI
      have hiabs : ((-j-1).natAbs : Int) = -j-1 := Int.natAbs_of_nonneg (by omega)
      have hi : i < T := by
        have h : (i : Int) < T := by dsimp [i]; rw [hiabs]; omega
        exact_mod_cast h
      have hfirst : -Int.ofNat (i+1) = j := by dsimp [i]; rw [hiabs]; omega
      have hsecond : Int.ofNat (T-i-1) = k := by
        change ((T-i-1 : Nat) : Int) = k
        dsimp [i]
        omega
      have hside : (j,k) ∈ oddSide3 T := by
        unfold oddSide3
        apply List.mem_map.mpr
        refine ⟨i, List.mem_range.mpr hi, ?_⟩
        exact Prod.ext hfirst hsecond
      simp only [oddShellIndices, List.mem_append]
      exact Or.inr hside
    · have hklt : k < 0 := by omega
      let i := (-j-1).natAbs
      have hu : ((2*j+1).natAbs : Int) = -(2*j+1) := Int.ofNat_natAbs_of_nonpos (by omega)
      have hv : ((2*k+1).natAbs : Int) = -(2*k+1) := Int.ofNat_natAbs_of_nonpos (by omega)
      rw [hu, hv] at hsumI
      have hiabs : ((-j-1).natAbs : Int) = -j-1 := Int.natAbs_of_nonneg (by omega)
      have hi : i < T := by
        have h : (i : Int) < T := by dsimp [i]; rw [hiabs]; omega
        exact_mod_cast h
      have hfirst : -Int.ofNat (i+1) = j := by dsimp [i]; rw [hiabs]; omega
      have hsecond : -Int.ofNat (T-i) = k := by
        change -((T-i : Nat) : Int) = k
        dsimp [i]
        omega
      have hside : (j,k) ∈ oddSide2 T := by
        unfold oddSide2
        apply List.mem_map.mpr
        refine ⟨i, List.mem_range.mpr hi, ?_⟩
        exact Prod.ext hfirst hsecond
      simp only [oddShellIndices, List.mem_append]
      exact Or.inl (Or.inr hside)

end YMGap.Continuum.ThetaParityShellEnumeration

#print axioms YMGap.Continuum.ThetaParityShellEnumeration.evenShellIndices_length
#print axioms YMGap.Continuum.ThetaParityShellEnumeration.oddShellIndices_length
#print axioms YMGap.Continuum.ThetaParityShellEnumeration.evenShellIndices_mem_of_radius
#print axioms YMGap.Continuum.ThetaParityShellEnumeration.oddShellIndices_mem_of_radius
