/-
# Geometry of the even and shifted-odd theta parity shells

This leaf records shell radii and the exact transformed box domains. It does
not identify a finite diamond with a rectangle, nor assert a completed theta
addition formula or an angular-tail estimate.
-/

import YMGap.Continuum.ThetaParityConvolution

namespace YMGap.Continuum.ThetaParityShellGeometry

set_option autoImplicit false

open YMGap.Continuum.ThetaParityConvolution

/-- Manhattan radius on the even integer lattice. -/
def evenRadius (j k : Int) : Nat := j.natAbs + k.natAbs

/-- Manhattan radius on the shifted odd lattice, in integer shell units. -/
def oddRadius (j k : Int) : Nat :=
  ((2*j+1).natAbs + (2*k+1).natAbs) / 2

/-- The exact exponent in the transformed even theta cell. -/
def evenExponent (j k : Int) : Nat :=
  2 * (j.natAbs*j.natAbs + k.natAbs*k.natAbs)

/-- The exact exponent in the transformed odd theta cell. -/
def oddExponent (j k : Int) : Nat :=
  2 * ((j*(j+1)).toNat + (k*(k+1)).toNat) + 1

/-- The even encoded box is exactly the Manhattan diamond. -/
theorem evenDiamond_iff_radius (N : Nat) (j k : Int) :
    EvenDiamondBound N (j,k) ↔ evenRadius j k ≤ N := by
  rcases Int.le_total 0 j with hj | hj <;>
    rcases Int.le_total 0 k with hk | hk
  · have hjabs : (j.natAbs : Int) = j := Int.natAbs_of_nonneg hj
    have hkabs : (k.natAbs : Int) = k := Int.natAbs_of_nonneg hk
    have hr : (evenRadius j k : Int) = j+k := by
      simp only [evenRadius, Int.natCast_add, hjabs, hkabs]
    constructor
    · intro h
      have h' : (evenRadius j k : Int) ≤ N := by
        rw [hr]
        simpa [EvenDiamondBound, BoxBound, encodeEven] using h.2.1
      exact_mod_cast h'
    · intro h
      have h' : (evenRadius j k : Int) ≤ N := by exact_mod_cast h
      rw [hr] at h'
      dsimp [EvenDiamondBound, BoxBound, encodeEven]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> omega
  · have hjabs : (j.natAbs : Int) = j := Int.natAbs_of_nonneg hj
    have hkabs : (k.natAbs : Int) = -k := Int.ofNat_natAbs_of_nonpos hk
    have hr : (evenRadius j k : Int) = j-k := by
      simp only [evenRadius, Int.natCast_add, hjabs, hkabs]
      omega
    constructor
    · intro h
      have h' : (evenRadius j k : Int) ≤ N := by
        rw [hr]
        simpa [EvenDiamondBound, BoxBound, encodeEven] using h.2.2.2
      exact_mod_cast h'
    · intro h
      have h' : (evenRadius j k : Int) ≤ N := by exact_mod_cast h
      rw [hr] at h'
      dsimp [EvenDiamondBound, BoxBound, encodeEven]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> omega
  · have hjabs : (j.natAbs : Int) = -j := Int.ofNat_natAbs_of_nonpos hj
    have hkabs : (k.natAbs : Int) = k := Int.natAbs_of_nonneg hk
    have hr : (evenRadius j k : Int) = k-j := by
      simp only [evenRadius, Int.natCast_add, hjabs, hkabs]
      omega
    constructor
    · intro h
      have h' : (evenRadius j k : Int) ≤ N := by
        rw [hr]
        have hn := h.2.2.1
        change -(N : Int) ≤ j-k at hn
        omega
      exact_mod_cast h'
    · intro h
      have h' : (evenRadius j k : Int) ≤ N := by exact_mod_cast h
      rw [hr] at h'
      dsimp [EvenDiamondBound, BoxBound, encodeEven]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> omega
  · have hjabs : (j.natAbs : Int) = -j := Int.ofNat_natAbs_of_nonpos hj
    have hkabs : (k.natAbs : Int) = -k := Int.ofNat_natAbs_of_nonpos hk
    have hr : (evenRadius j k : Int) = -j-k := by
      simp only [evenRadius, Int.natCast_add, hjabs, hkabs]
      omega
    constructor
    · intro h
      have h' : (evenRadius j k : Int) ≤ N := by
        rw [hr]
        have hn := h.1
        change -(N : Int) ≤ j+k at hn
        omega
      exact_mod_cast h'
    · intro h
      have h' : (evenRadius j k : Int) ≤ N := by exact_mod_cast h
      rw [hr] at h'
      dsimp [EvenDiamondBound, BoxBound, encodeEven]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

/-- The shifted odd radius is the exact half-sum of the two odd frequencies. -/
theorem oddRadius_frequency_formula (j k : Int) :
    2 * oddRadius j k = (2*j+1).natAbs + (2*k+1).natAbs := by
  unfold oddRadius
  have hodd1 : (2*j+1).natAbs % 2 = 1 := by
    by_cases h : 0 ≤ 2*j+1
    · have habs : ((2*j+1).natAbs : Int) = 2*j+1 := Int.natAbs_of_nonneg h
      omega
    · have habs : ((2*j+1).natAbs : Int) = -(2*j+1) :=
        Int.ofNat_natAbs_of_nonpos (by omega)
      omega
  have hodd2 : (2*k+1).natAbs % 2 = 1 := by
    by_cases h : 0 ≤ 2*k+1
    · have habs : ((2*k+1).natAbs : Int) = 2*k+1 := Int.natAbs_of_nonneg h
      omega
    · have habs : ((2*k+1).natAbs : Int) = -(2*k+1) :=
        Int.ofNat_natAbs_of_nonpos (by omega)
      omega
  omega

private theorem manhattan_sq_le_two_sq (a b : Nat) :
    (a+b)*(a+b) ≤ 2*(a*a+b*b) := by
  by_cases hab : a ≤ b
  · let d := b-a
    have hb : b = a+d := by dsimp [d]; omega
    have hiden : 2*(a*a+(a+d)*(a+d)) =
        (a+(a+d))*(a+(a+d))+d*d := by
      simp only [Nat.mul_add, Nat.add_mul]
      omega
    rw [hb]
    rw [hiden]
    omega
  · have hba : b ≤ a := Nat.le_of_not_ge hab
    let d := a-b
    have ha : a = b+d := by dsimp [d]; omega
    have hiden : 2*(b*b+(b+d)*(b+d)) =
        (b+(b+d))*(b+(b+d))+d*d := by
      simp only [Nat.mul_add, Nat.add_mul]
      omega
    have hcomm : 2*((b+d)*(b+d)+b*b) = 2*(b*b+(b+d)*(b+d)) := by ac_rfl
    have hsum : b+d+b = b+(b+d) := by omega
    rw [ha, hsum, hcomm, hiden]
    omega

/-- The even Jacobi exponent dominates the square of the Manhattan shell. -/
theorem even_exponent_ge_radius_sq (j k : Int) :
    evenRadius j k * evenRadius j k ≤ evenExponent j k := by
  unfold evenRadius evenExponent
  exact manhattan_sq_le_two_sq j.natAbs k.natAbs

/-- Each even branch frequency lies within twice its Manhattan radius. -/
theorem even_frequencies_le_radius (j k : Int) :
    (2*j).natAbs ≤ 2*evenRadius j k ∧
      (2*k).natAbs ≤ 2*evenRadius j k := by
  have hj := Int.natAbs_add_le j j
  have hk := Int.natAbs_add_le k k
  have hj' : (2*j).natAbs ≤ j.natAbs+j.natAbs := by
    simpa only [show j+j = 2*j by omega] using hj
  have hk' : (2*k).natAbs ≤ k.natAbs+k.natAbs := by
    simpa only [show k+k = 2*k by omega] using hk
  dsimp [evenRadius]
  constructor <;> omega

/-- Each odd branch frequency lies within twice its shifted-shell radius. -/
theorem odd_frequencies_le_radius (j k : Int) :
    (2*j+1).natAbs ≤ 2*oddRadius j k ∧
      (2*k+1).natAbs ≤ 2*oddRadius j k := by
  rw [oddRadius_frequency_formula]
  constructor <;> omega

/-- The original transformed odd-box predicate retains both endpoints. -/
theorem oddDiamond_iff_radius (N : Nat) (j k : Int) :
    OddDiamondBound N (j,k) ↔ oddRadius j k ≤ N := by
  rcases Int.le_total 0 (2*j+1) with hu | hu <;>
    rcases Int.le_total 0 (2*k+1) with hv | hv
  · have huAbs : ((2*j+1).natAbs : Int) = 2*j+1 := Int.natAbs_of_nonneg hu
    have hvAbs : ((2*k+1).natAbs : Int) = 2*k+1 := Int.natAbs_of_nonneg hv
    have hrad : (oddRadius j k : Int) = j+k+1 := by
      have h := congrArg (fun n : Nat => (n : Int)) (oddRadius_frequency_formula j k)
      simp only [Int.natCast_mul, Int.natCast_add] at h
      rw [huAbs, hvAbs] at h
      omega
    constructor
    · intro h
      have h' : (oddRadius j k : Int) ≤ N := by
        rw [hrad]
        simpa [OddDiamondBound, BoxBound, encodeOdd] using h.2.1
      exact_mod_cast h'
    · intro h
      have h' : (oddRadius j k : Int) ≤ N := by exact_mod_cast h
      rw [hrad] at h'
      dsimp [OddDiamondBound, BoxBound, encodeOdd]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

  · have huAbs : ((2*j+1).natAbs : Int) = 2*j+1 := Int.natAbs_of_nonneg hu
    have hvAbs : ((2*k+1).natAbs : Int) = -(2*k+1) :=
      Int.ofNat_natAbs_of_nonpos (by omega)
    have hrad : (oddRadius j k : Int) = j-k := by
      have h := congrArg (fun n : Nat => (n : Int)) (oddRadius_frequency_formula j k)
      simp only [Int.natCast_mul, Int.natCast_add] at h
      rw [huAbs, hvAbs] at h
      omega
    constructor
    · intro h
      have h' : (oddRadius j k : Int) ≤ N := by
        rw [hrad]
        simpa [OddDiamondBound, BoxBound, encodeOdd] using h.2.2.2
      exact_mod_cast h'
    · intro h
      have h' : (oddRadius j k : Int) ≤ N := by exact_mod_cast h
      rw [hrad] at h'
      dsimp [OddDiamondBound, BoxBound, encodeOdd]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> omega
  · have huAbs : ((2*j+1).natAbs : Int) = -(2*j+1) :=
      Int.ofNat_natAbs_of_nonpos (by omega)
    have hvAbs : ((2*k+1).natAbs : Int) = 2*k+1 := Int.natAbs_of_nonneg hv
    have hrad : (oddRadius j k : Int) = k-j := by
      have h := congrArg (fun n : Nat => (n : Int)) (oddRadius_frequency_formula j k)
      simp only [Int.natCast_mul, Int.natCast_add] at h
      rw [huAbs, hvAbs] at h
      omega
    constructor
    · intro h
      have h' : (oddRadius j k : Int) ≤ N := by
        rw [hrad]
        have hn := h.2.2.1
        change -(N : Int) ≤ j-k at hn
        omega
      exact_mod_cast h'
    · intro h
      have h' : (oddRadius j k : Int) ≤ N := by exact_mod_cast h
      rw [hrad] at h'
      dsimp [OddDiamondBound, BoxBound, encodeOdd]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> omega
  · have huAbs : ((2*j+1).natAbs : Int) = -(2*j+1) :=
      Int.ofNat_natAbs_of_nonpos (by omega)
    have hvAbs : ((2*k+1).natAbs : Int) = -(2*k+1) :=
      Int.ofNat_natAbs_of_nonpos (by omega)
    have hrad : (oddRadius j k : Int) = -j-k-1 := by
      have h := congrArg (fun n : Nat => (n : Int)) (oddRadius_frequency_formula j k)
      simp only [Int.natCast_mul, Int.natCast_add] at h
      rw [huAbs, hvAbs] at h
      omega
    constructor
    · intro h
      have h' : (oddRadius j k : Int) ≤ N := by
        rw [hrad]
        have hn := h.1
        change -(N : Int) ≤ j+k+1 at hn
        omega
      exact_mod_cast h'
    · intro h
      have h' : (oddRadius j k : Int) ≤ N := by exact_mod_cast h
      rw [hrad] at h'
      dsimp [OddDiamondBound, BoxBound, encodeOdd]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

private theorem int_interval_iff_natAbs (N : Nat) (z : Int) :
    (-(N : Int) ≤ z ∧ z ≤ N) ↔ z.natAbs ≤ N := by
  rcases Int.le_total 0 z with hz | hz
  · constructor
    · intro h
      have h' : (z.natAbs : Int) ≤ N := by
        rw [Int.natAbs_of_nonneg hz]
        exact h.2
      exact_mod_cast h'
    · intro h
      have h' : (z.natAbs : Int) ≤ N := by exact_mod_cast h
      rw [Int.natAbs_of_nonneg hz] at h'
      exact ⟨by omega, h'⟩
  · constructor
    · intro h
      have h' : (z.natAbs : Int) ≤ N := by
        rw [Int.ofNat_natAbs_of_nonpos hz]
        have hn := h.1
        omega
      exact_mod_cast h'
    · intro h
      have h' : (z.natAbs : Int) ≤ N := by exact_mod_cast h
      rw [Int.ofNat_natAbs_of_nonpos hz] at h'
      exact ⟨by omega, by omega⟩

private theorem boxBound_iff_cornerRadius (N : Nat) (m n : Int) :
    BoxBound N (m,n) ↔ max m.natAbs n.natAbs ≤ N := by
  constructor
  · intro h
    have hm := (int_interval_iff_natAbs N m).mp ⟨h.1, h.2.1⟩
    have hn := (int_interval_iff_natAbs N n).mp ⟨h.2.2.1, h.2.2.2⟩
    exact Nat.max_le.mpr ⟨hm,hn⟩
  · intro h
    have hab := Nat.max_le.mp h
    have hm := (int_interval_iff_natAbs N m).mpr hab.1
    have hn := (int_interval_iff_natAbs N n).mpr hab.2
    exact ⟨hm.1,hm.2,hn.1,hn.2⟩

/-- The exact shifted radius is the maximum absolute encoded corner. -/
theorem oddRadius_eq_encoded_corner_max (j k : Int) :
    oddRadius j k = max (j+k+1).natAbs (j-k).natAbs := by
  have hcorner (N : Nat) :
      OddDiamondBound N (j,k) ↔ max (j+k+1).natAbs (j-k).natAbs ≤ N :=
    boxBound_iff_cornerRadius N (j+k+1) (j-k)
  have h1 : max (j+k+1).natAbs (j-k).natAbs ≤ oddRadius j k :=
    (hcorner (oddRadius j k)).mp
      ((oddDiamond_iff_radius (oddRadius j k) j k).mpr (Nat.le_refl _))
  have h2 : oddRadius j k ≤ max (j+k+1).natAbs (j-k).natAbs :=
    (oddDiamond_iff_radius (max (j+k+1).natAbs (j-k).natAbs) j k).mp
      ((hcorner (max (j+k+1).natAbs (j-k).natAbs)).mpr (Nat.le_refl _))
  exact Nat.le_antisymm h2 h1

private theorem adjacent_product_nonneg (j : Int) : 0 ≤ j*(j+1) := by
  by_cases hj : 0 ≤ j
  · exact Int.mul_nonneg hj (by omega)
  · exact Int.mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)

private theorem oddExponent_eq_encoded_corner_squares (j k : Int) :
    oddExponent j k =
      (j+k+1).natAbs*(j+k+1).natAbs + (j-k).natAbs*(j-k).natAbs := by
  have hj := adjacent_product_nonneg j
  have hk := adjacent_product_nonneg k
  have hJ : ((j*(j+1)).toNat : Int) = j*(j+1) := Int.toNat_of_nonneg hj
  have hK : ((k*(k+1)).toNat : Int) = k*(k+1) := Int.toNat_of_nonneg hk
  have hE : (oddExponent j k : Int) = 2*(j*(j+1)+k*(k+1))+1 := by
    simp only [oddExponent, Int.natCast_mul, Int.natCast_add, hJ, hK]
    rfl
  have hpin := odd_exponent_pin j k
  have hsum : (oddExponent j k : Int) =
      (j+k+1)*(j+k+1) + (j-k)*(j-k) := hE.trans hpin.symm
  have hcast :
      (((j+k+1).natAbs*(j+k+1).natAbs + (j-k).natAbs*(j-k).natAbs : Nat) : Int) =
        (j+k+1)*(j+k+1) + (j-k)*(j-k) := by
    simp only [Int.natCast_add, Int.natCast_mul, Int.natAbs_mul_self']
  exact Int.ofNat.inj (hsum.trans hcast.symm)

/-- The shifted-odd exponent dominates the square of its actual shell. -/
theorem odd_exponent_ge_radius_sq (j k : Int) :
    oddRadius j k * oddRadius j k ≤ oddExponent j k := by
  rw [oddRadius_eq_encoded_corner_max, oddExponent_eq_encoded_corner_squares]
  rcases Nat.le_total (j+k+1).natAbs (j-k).natAbs with hab | hba
  · rw [Nat.max_eq_right hab]
    omega
  · rw [Nat.max_eq_left hba]
    omega

end YMGap.Continuum.ThetaParityShellGeometry

#print axioms YMGap.Continuum.ThetaParityShellGeometry.evenDiamond_iff_radius
#print axioms YMGap.Continuum.ThetaParityShellGeometry.oddRadius_frequency_formula
#print axioms YMGap.Continuum.ThetaParityShellGeometry.even_exponent_ge_radius_sq
#print axioms YMGap.Continuum.ThetaParityShellGeometry.even_frequencies_le_radius
#print axioms YMGap.Continuum.ThetaParityShellGeometry.odd_frequencies_le_radius
#print axioms YMGap.Continuum.ThetaParityShellGeometry.oddDiamond_iff_radius
#print axioms YMGap.Continuum.ThetaParityShellGeometry.oddRadius_eq_encoded_corner_max
#print axioms YMGap.Continuum.ThetaParityShellGeometry.odd_exponent_ge_radius_sq
