import YMGap.Continuum.Z4ThreeCubeComponentSubsupportObservable

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4ThreeCubeAxisOverlapPhysicalSummand
open YMGap.Continuum.Z4UnitCubeIncidenceParity

def plainXZ : List Z4Plaq :=
  (axisCubeSurface zeroAxisOffset ++ axisCubeSurface xAxisOffset).eraseDups

def xorXZ : List Z4Plaq :=
  (axisCubeSurface zeroAxisOffset ++ axisCubeSurface xAxisOffset).filter
    (fun p => decide
      ((p ∈ axisCubeSurface zeroAxisOffset) !=
        (p ∈ axisCubeSurface xAxisOffset)))

def links : List Z4Link :=
  (plainXZ.flatMap edgesOf).eraseDups

def encDir : Dir4 → Nat
  | .x0 => 0 | .x1 => 1 | .x2 => 2 | .x3 => 3

def encLink (l : Z4Link) : Nat × Nat × Nat × Nat × Nat :=
  (l.1.1, l.1.2.1, l.1.2.2.1, l.1.2.2.2, encDir l.2)

#eval plainXZ.length
#eval xorXZ.length
#eval links.map (fun l => (encLink l, faceIncidenceCount l plainXZ))
#eval links.map (fun l => (encLink l, faceIncidenceCount l xorXZ))

theorem plain_bad : faceIncidenceCount ((1,0,0,0), .x1) plainXZ = 3 := by
  decide

theorem xor_eq_literal : xorXZ =
    [((0,0,0,0), .p01), ((0,0,1,0), .p01),
     ((0,0,0,0), .p02), ((0,1,0,0), .p02),
     ((0,0,0,0), .p12),
     ((1,0,0,0), .p01), ((1,0,1,0), .p01),
     ((1,0,0,0), .p02), ((1,1,0,0), .p02),
     ((2,0,0,0), .p12)] := by
  decide

theorem xor_closed :
    YMGap.Continuum.Z4DyadicDeterministicSupportKernel.EvenFaceIncidence
      xorXZ := by
  intro link
  rw [xor_eq_literal]
  obtain ⟨⟨a, b, c, d⟩, direction⟩ := link
  cases direction <;>
    simp [faceIncidenceCount, edgesOf, dirsOf, addE, Prod.mk.injEq]
  all_goals
    by_cases ha : a ≤ 2
    · by_cases hb : b ≤ 1
      · by_cases hc : c ≤ 1
        · by_cases hd : d = 0
          · subst d
            have haCases : a = 0 ∨ a = 1 ∨ a = 2 := by omega
            have hbCases : b = 0 ∨ b = 1 := by omega
            have hcCases : c = 0 ∨ c = 1 := by omega
            rcases haCases with rfl | rfl | rfl <;>
              rcases hbCases with rfl | rfl <;>
              rcases hcCases with rfl | rfl <;> decide
          · have hd0 : d ≠ 0 := hd
            simp [hd0]
        · have hc0 : c ≠ 0 := by omega
          have hc1 : c ≠ 1 := by omega
          simp [hc0, hc1]
      · have hb0 : b ≠ 0 := by omega
        have hb1 : b ≠ 1 := by omega
        simp [hb0, hb1]
    · have ha0 : a ≠ 0 := by omega
      have ha1 : a ≠ 1 := by omega
      have ha2 : a ≠ 2 := by omega
      simp [ha0, ha1, ha2]
