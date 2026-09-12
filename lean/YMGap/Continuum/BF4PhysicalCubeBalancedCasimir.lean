/-
# Uniform quadratic Casimir payment for balanced cube descent

All six labels are retained. A sum-of-squares reserve at a maximal label
pays the common offset and the rounding errors. For M=max label >=1400:

  72 * C4(balancedState source) + M^2 <= 72 * C4(source).

This is an all-state energy estimate, not yet a diagonal-kernel or row
probability bound. Constants are tested by bf4_cube_balanced_descent.py.
-/

import YMGap.Continuum.BF4PhysicalCubeBalancedDescent

namespace YMGap.Continuum.BF4PhysicalCubeBalancedCasimir

set_option autoImplicit false

open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4PhysicalCubeBalancedDescent
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

def labelSum : List Nat → Nat
  | [] => 0
  | s :: ss => s + labelSum ss

def squareSum : List Nat → Nat
  | [] => 0
  | s :: ss => s * s + squareSum ss

def casimirSum : List Nat → Nat
  | [] => 0
  | s :: ss => c4 s + casimirSum ss

theorem casimirSum_eq (ss : List Nat) : casimirSum ss = squareSum ss + 2 * labelSum ss := by
  induction ss with
  | nil => rfl
  | cons s ss ih => simp only [casimirSum, squareSum, labelSum, ih, c4, Nat.mul_add]; omega

private theorem two_mul_le_squares (a b : Nat) : 2 * (a * b) ≤ a * a + b * b := by
  by_cases h : a ≤ b
  · have he : b = a + (b - a) := by omega
    rw [he]
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_comm (b - a) a]
    omega
  · have he : a = b + (a - b) := by omega
    rw [he]
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_comm (a - b) b]
    omega

private theorem young (M s : Nat) : 8 * (M * s) ≤ 16 * (s * s) + M * M := by
  have h := two_mul_le_squares M (4 * s)
  have hleft : 2 * (M * (4 * s)) = 8 * (M * s) := by
    calc
      _ = (2 * 4) * (M * s) := by ac_rfl
      _ = _ := rfl
  have hright : (4 * s) * (4 * s) = 16 * (s * s) := by
    calc
      _ = (4 * 4) * (s * s) := by ac_rfl
      _ = _ := rfl
  rw [hleft, hright] at h
  omega

private theorem sum_young (M : Nat) : ∀ ss : List Nat,
    8 * (M * labelSum ss) ≤ 16 * squareSum ss + ss.length * (M * M)
  | [] => by simp [labelSum, squareSum]
  | s :: ss => by
      have h := young M s
      have ih := sum_young M ss
      simp only [labelSum, squareSum, List.length_cons, Nat.mul_add, Nat.add_mul]
      omega

/-- The maximal coordinate contributes an extra reserve `9*M^2` to the
usual termwise Young inequality. Only membership is needed for this identity. -/
theorem maximal_square_reserve (M : Nat) : ∀ ss : List Nat, M ∈ ss →
    8 * (M * labelSum ss) + 9 * (M * M) ≤ 16 * squareSum ss + ss.length * (M * M)
  | [], h => by cases h
  | s :: ss, h => by
      rcases List.mem_cons.mp h with he | ht
      · subst s
        have h := sum_young M ss
        simp only [labelSum, squareSum, List.length_cons, Nat.mul_add, Nat.add_mul]
        omega
      · have h := young M s
        have ih := maximal_square_reserve M ss ht
        simp only [labelSum, squareSum, List.length_cons, Nat.mul_add, Nat.add_mul]
        omega

theorem member_square_le (M : Nat) : ∀ ss : List Nat, M ∈ ss → M * M ≤ squareSum ss
  | [], h => by cases h
  | s :: ss, h => by
      rcases List.mem_cons.mp h with rfl | ht
      · exact Nat.le_add_right _ _
      · have h := member_square_le M ss ht; change _ ≤ s * s + _; omega

theorem labelSum_le (M : Nat) : ∀ ss : List Nat,
    (∀ s, s ∈ ss → s ≤ M) → labelSum ss ≤ ss.length * M
  | [], _ => by simp [labelSum]
  | s :: ss, h => by
      have hh := h s List.mem_cons_self
      have ht := labelSum_le M ss (fun t ht => h t (List.mem_cons_of_mem s ht))
      simp only [labelSum, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

private theorem balanced_casimir_pointwise (M s : Nat) :
    36 * c4 (balancedLabel M s) ≤
      16 * (s * s) + 8 * (M * s) + M * M + 144 * s + 36 * M + 288 := by
  have ha : 6 * balancedLabel M s ≤ 4 * s + M + 12 := by
    have h := balancedLabel_affine_bound M s; omega
  have hs := Nat.mul_le_mul ha ha
  have hl := Nat.mul_le_mul_left 12 ha
  have hleft : (6 * balancedLabel M s) * (6 * balancedLabel M s) =
      36 * (balancedLabel M s * balancedLabel M s) := by
    calc
      _ = (6 * 6) * (balancedLabel M s * balancedLabel M s) := by ac_rfl
      _ = _ := rfl
  have hright : (4 * s) * (4 * s) = 16 * (s * s) := by
    calc
      _ = (4 * 4) * (s * s) := by ac_rfl
      _ = _ := rfl
  rw [hleft] at hs
  simp only [Nat.add_mul, Nat.mul_add] at hs
  rw [hright, show (4 * s) * M = 4 * (M * s) by ac_rfl,
    show M * (4 * s) = 4 * (M * s) by ac_rfl] at hs
  simp only [c4, Nat.mul_add]
  omega

private theorem balanced_casimir_sum (M : Nat) : ∀ ss : List Nat,
    36 * casimirSum (ss.map (balancedLabel M)) ≤
      16 * squareSum ss + 8 * (M * labelSum ss) + ss.length * (M * M) +
        144 * labelSum ss + 36 * ss.length * M + 288 * ss.length
  | [] => by simp [casimirSum, squareSum, labelSum]
  | s :: ss => by
      have h := balanced_casimir_pointwise M s
      have ih := balanced_casimir_sum M ss
      simp only [List.map_cons, casimirSum, squareSum, labelSum, List.length_cons,
        Nat.mul_add, Nat.add_mul, Nat.one_mul]
      omega

theorem six_label_payment (ss : List Nat) (hlen : ss.length = 6) (M : Nat)
    (hm : M ∈ ss) (hb : ∀ s, s ∈ ss → s ≤ M) :
    36 * casimirSum (ss.map (balancedLabel M)) + M * M ≤
      36 * casimirSum ss + 648 * M + 1728 := by
  have h := balanced_casimir_sum M ss
  have hr := maximal_square_reserve M ss hm
  have he := member_square_le M ss hm
  have hl := labelSum_le M ss hb
  rw [hlen] at h hr hl
  rw [casimirSum_eq ss]
  omega

def cubeCasimir (state : EdgeLabelling) : Nat := casimirSum (cubeLabels state)

theorem balanced_cubeLabels (state : EdgeLabelling) :
    cubeLabels (balancedState state) = (cubeLabels state).map (balancedLabel (radius state)) := by
  unfold cubeLabels
  rw [List.map_map]
  apply List.map_congr_left
  intro face hf
  exact balancedState_on state face hf

theorem cube_casimir_payment (state : EdgeLabelling) :
    36 * cubeCasimir (balancedState state) + radius state * radius state ≤
      36 * cubeCasimir state + 648 * radius state + 1728 := by
  unfold cubeCasimir
  rw [balanced_cubeLabels]
  apply six_label_payment
  · simp [cubeLabels, centralLowerCubeFaceIds]
  · exact maxLabel_mem _ (by simp [cubeLabels, centralLowerCubeFaceIds])
  · intro s hs; exact member_le_maxLabel _ hs

theorem large_radius_payment (M : Nat) (hM : 1400 ≤ M) : 1296 * M + 3456 ≤ M * M := by
  have h := Nat.mul_le_mul_right M hM
  omega

/-- Uniform all-state quadratic energy descent beyond a fixed finite head.
No assumption on common parity is needed for the energy inequality itself. -/
theorem cube_casimir_quadratic_drop (state : EdgeLabelling) (hM : 1400 ≤ radius state) :
    72 * cubeCasimir (balancedState state) + radius state * radius state ≤ 72 * cubeCasimir state := by
  have h := cube_casimir_payment state
  have hr := large_radius_payment _ hM
  omega

private theorem casimirSum_le (M : Nat) : ∀ ss : List Nat,
    (∀ s, s ∈ ss → s ≤ M) → casimirSum ss ≤ ss.length * c4 M
  | [], _ => by simp [casimirSum]
  | s :: ss, h => by
      have hs := h s List.mem_cons_self
      have hh : c4 s ≤ c4 M := Nat.mul_le_mul hs (by omega)
      have ht := casimirSum_le M ss (fun t ht => h t (List.mem_cons_of_mem s ht))
      simp only [casimirSum, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

theorem cube_casimir_radius_ceiling (state : EdgeLabelling) :
    cubeCasimir state ≤ 6 * c4 (radius state) := by
  have h := casimirSum_le (radius state) (cubeLabels state)
    (fun _ hs => member_le_maxLabel _ hs)
  have hlen : (cubeLabels state).length = 6 := by simp [cubeLabels, centralLowerCubeFaceIds]
  simpa only [hlen] using h

/-- A common relative rate for the LABEL ENERGY outside the finite head.
This is not a Rayleigh quotient or spectral-gap theorem. -/
theorem cube_casimir_relative_contraction (state : EdgeLabelling) (hM : 1400 ≤ radius state) :
    864 * cubeCasimir (balancedState state) ≤ 863 * cubeCasimir state := by
  have hd := cube_casimir_quadratic_drop state hM
  have hc := cube_casimir_radius_ceiling state
  have htwo := Nat.mul_le_mul_right (radius state) (show 2 ≤ radius state by omega)
  simp only [c4, Nat.mul_add] at hc
  omega

end YMGap.Continuum.BF4PhysicalCubeBalancedCasimir

#print axioms YMGap.Continuum.BF4PhysicalCubeBalancedCasimir.labelSum
#print axioms YMGap.Continuum.BF4PhysicalCubeBalancedCasimir.squareSum
#print axioms YMGap.Continuum.BF4PhysicalCubeBalancedCasimir.casimirSum
#print axioms YMGap.Continuum.BF4PhysicalCubeBalancedCasimir.casimirSum_eq
#print axioms YMGap.Continuum.BF4PhysicalCubeBalancedCasimir.maximal_square_reserve
#print axioms YMGap.Continuum.BF4PhysicalCubeBalancedCasimir.member_square_le
#print axioms YMGap.Continuum.BF4PhysicalCubeBalancedCasimir.labelSum_le
#print axioms YMGap.Continuum.BF4PhysicalCubeBalancedCasimir.six_label_payment
#print axioms YMGap.Continuum.BF4PhysicalCubeBalancedCasimir.cubeCasimir
#print axioms YMGap.Continuum.BF4PhysicalCubeBalancedCasimir.balanced_cubeLabels
#print axioms YMGap.Continuum.BF4PhysicalCubeBalancedCasimir.cube_casimir_payment
#print axioms YMGap.Continuum.BF4PhysicalCubeBalancedCasimir.large_radius_payment
#print axioms YMGap.Continuum.BF4PhysicalCubeBalancedCasimir.cube_casimir_quadratic_drop
#print axioms YMGap.Continuum.BF4PhysicalCubeBalancedCasimir.cube_casimir_radius_ceiling
#print axioms YMGap.Continuum.BF4PhysicalCubeBalancedCasimir.cube_casimir_relative_contraction
