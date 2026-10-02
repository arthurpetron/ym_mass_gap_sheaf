/-
# Computed original Jacobi active-factor block

For 16/17 <= q < 1, write h=1-q=p/d. The executable block has
start=floor((d+2p)/(4p)), stop=floor((3d+4p)/(8p)), N=stop-start.
Its ORIGINAL odd exponents m=2(start+j)+1 satisfy 1/2 <= m*h <= 3/4.
Consequently 1/4 <= q^m <= 3/4, N*h >= 1/16, and N >= 2.

The count and start are actual Nat data, not supplied counting hypotheses.
This feeds retained finite Jacobi factor multiplication. Full heat-profile
limits, original Haar shape certificates and relative survival remain OPEN.
-/

import YMGap.Continuum.HeatKernelConvGen
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.SU2HeatJacobiActiveFactorCount

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv

private def blockStart (p d : Nat) : Nat := (d+2*p)/(4*p)
private def blockStop (p d : Nat) : Nat := (3*d+4*p)/(8*p)

/-- First actual original Jacobi factor in the computed block. -/
def activeFactorStart (q : Q') : Nat :=
  blockStart (1-q).num.toNat (1-q).den

/-- Number of consecutive actual original Jacobi factors retained. -/
def activeFactorCount (q : Q') : Nat :=
  blockStop (1-q).num.toNat (1-q).den - activeFactorStart q

private theorem integer_block (p d : Nat) (hp : 0 < p) (hd : 17*p ≤ d) :
    2 ≤ blockStop p d-blockStart p d ∧
      d ≤ 16*((blockStop p d-blockStart p d)*p) ∧
      ∀ j, j < blockStop p d-blockStart p d →
        d ≤ 2*((2*(blockStart p d+j)+1)*p) ∧
          4*((2*(blockStart p d+j)+1)*p) ≤ 3*d := by
  let s := blockStart p d
  let t := blockStop p d
  have hp4 : 0 < 4*p := Nat.mul_pos (by decide) hp
  have hp8 : 0 < 8*p := Nat.mul_pos (by decide) hp
  have hs0 : 4*(s*p) ≤ d+2*p := by
    simpa only [s, blockStart, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      using Nat.div_mul_le_self (d+2*p) (4*p)
  have hs1 : d < 4*(s*p)+2*p := by
    have hdiv := Nat.div_add_mod (d+2*p) (4*p)
    have hrem := Nat.mod_lt (d+2*p) hp4
    have hdiv' : 4*(s*p)+(d+2*p)%(4*p)=d+2*p := by
      simpa only [s, blockStart, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
        using hdiv
    omega
  have ht0 : 8*(t*p) ≤ 3*d+4*p := by
    simpa only [t, blockStop, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      using Nat.div_mul_le_self (3*d+4*p) (8*p)
  have ht1 : 3*d < 8*(t*p)+4*p := by
    have hdiv := Nat.div_add_mod (3*d+4*p) (8*p)
    have hrem := Nat.mod_lt (3*d+4*p) hp8
    have hdiv' : 8*(t*p)+(3*d+4*p)%(8*p)=3*d+4*p := by
      simpa only [t, blockStop, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
        using hdiv
    omega
  have hst : s ≤ t := by
    by_cases h : s ≤ t
    · exact h
    · have hts : t+1 ≤ s := by omega
      have hm := Nat.mul_le_mul_right p hts
      simp only [Nat.add_mul, Nat.one_mul] at hm
      omega
  have hjoin : t*p=s*p+(t-s)*p := by
    rw [← Nat.add_mul, Nat.add_sub_of_le hst]
  have hlength : d < 8*((t-s)*p)+8*p := by
    rw [hjoin] at ht1
    omega
  have htwo : 2 ≤ t-s := by
    by_cases h : 2 ≤ t-s
    · exact h
    · have hsmall : t-s ≤ 1 := by omega
      have hm := Nat.mul_le_mul_right p hsmall
      simp only [Nat.one_mul] at hm
      omega
  have hmass : d ≤ 16*((t-s)*p) := by omega
  refine ⟨htwo, hmass, ?_⟩
  intro j hj
  have hjt : s+j+1 ≤ t := by omega
  have hm := Nat.mul_le_mul_right p hjt
  simp only [Nat.add_mul, Nat.one_mul] at hm
  change d ≤ 2*((2*(s+j)+1)*p) ∧ 4*((2*(s+j)+1)*p) ≤ 3*d
  constructor
  · simp only [Nat.add_mul, Nat.mul_assoc, Nat.one_mul]
    omega
  · simp only [Nat.add_mul, Nat.mul_assoc, Nat.one_mul]
    omega

private theorem gap_data {q : Q'}
    (hq : Q'.mkPos 16 17 (by decide) ≤ q) (hq1 : q < (1 : Q')) :
    0 < (1-q).num.toNat ∧ 17*(1-q).num.toNat ≤ (1-q).den := by
  have hnum := CReal.num_pos_of_pos (HKPos.one_sub_pos hq1)
  have hcast : ((1-q).num.toNat : Int)=(1-q).num :=
    Int.toNat_of_nonneg (Int.le_of_lt hnum)
  have hg : 1-q ≤ Q'.mkPos 1 17 (by decide) :=
    Q'.le_trans' _ _ _ (Q'.add_le_add_left 1 _ _ (Q'.neg_le_neg hq))
      (Q'.le_of_eqv (by decide : (1 : Q')-Q'.mkPos 16 17 (by decide) ≈
        Q'.mkPos 1 17 (by decide)))
  have hg' : 17*(1-q).num ≤ ((1-q).den : Int) := by
    change (1-q).num*17 ≤ 1*((1-q).den : Int) at hg
    simpa only [Int.one_mul, Int.mul_comm] using hg
  have hnat : 0 < (1-q).num.toNat := by
    have hpos : (0 : Int) < ((1-q).num.toNat : Int) := by
      rw [hcast]
      exact hnum
    exact_mod_cast hpos
  have hsize : 17*(1-q).num.toNat ≤ (1-q).den := by
    have hsize' : (17 : Int)*((1-q).num.toNat : Int) ≤ ((1-q).den : Int) := by
      rw [hcast]
      exact hg'
    exact_mod_cast hsize'
  exact ⟨hnat,hsize⟩

/-- The actual retained count has at least two factors, uniformly near one. -/
theorem activeFactorCount_two {q : Q'}
    (hq : Q'.mkPos 16 17 (by decide) ≤ q) (hq1 : q < (1 : Q')) :
    2 ≤ activeFactorCount q :=
  (integer_block _ _ (gap_data hq hq1).1 (gap_data hq hq1).2).1

/-- The actual retained count supplies at least one sixteenth of nome gap. -/
theorem activeFactorCount_mass {q : Q'}
    (hq : Q'.mkPos 16 17 (by decide) ≤ q) (hq1 : q < (1 : Q')) :
    Q'.mkPos 1 16 (by decide) ≤ Q'.ofNat (activeFactorCount q)*(1-q) := by
  have h := (integer_block _ _ (gap_data hq hq1).1 (gap_data hq hq1).2).2.1
  have hcast : ((1-q).num.toNat : Int)=(1-q).num :=
    Int.toNat_of_nonneg (Int.le_of_lt (CReal.num_pos_of_pos (HKPos.one_sub_pos hq1)))
  have hi : ((1-q).den : Int) ≤
      16*((activeFactorCount q : Int)*((1-q).num.toNat : Int)) := by
    exact_mod_cast h
  rw [hcast] at hi
  show (1 : Int)*((Q'.ofNat (activeFactorCount q)*(1-q)).den : Int) ≤
    (Q'.ofNat (activeFactorCount q)*(1-q)).num*16
  rw [Q'.mul_den_cast]
  change 1*(1*((1-q).den : Int)) ≤ ((activeFactorCount q : Int)*(1-q).num)*16
  simpa only [Int.one_mul, Int.mul_comm] using hi

private theorem exponent_gap_bounds {q : Q'}
    (hq : Q'.mkPos 16 17 (by decide) ≤ q) (hq1 : q < (1 : Q'))
    (j : Nat) (hj : j < activeFactorCount q) :
    Q'.mkPos 1 2 (by decide) ≤ Q'.ofNat (2*(activeFactorStart q+j)+1)*(1-q) ∧
      Q'.ofNat (2*(activeFactorStart q+j)+1)*(1-q) ≤ Q'.mkPos 3 4 (by decide) := by
  have h := (integer_block _ _ (gap_data hq hq1).1 (gap_data hq hq1).2).2.2 j hj
  have hcast : ((1-q).num.toNat : Int)=(1-q).num :=
    Int.toNat_of_nonneg (Int.le_of_lt (CReal.num_pos_of_pos (HKPos.one_sub_pos hq1)))
  have hlo : ((1-q).den : Int) ≤
      2*(((2*(activeFactorStart q+j)+1 : Nat) : Int)*((1-q).num.toNat : Int)) := by
    exact_mod_cast h.1
  have hhi : 4*(((2*(activeFactorStart q+j)+1 : Nat) : Int)*((1-q).num.toNat : Int)) ≤
      3*((1-q).den : Int) := by
    exact_mod_cast h.2
  rw [hcast] at hlo hhi
  constructor
  · show (1 : Int)*((Q'.ofNat (2*(activeFactorStart q+j)+1)*(1-q)).den : Int) ≤
      (Q'.ofNat (2*(activeFactorStart q+j)+1)*(1-q)).num*2
    rw [Q'.mul_den_cast]
    change 1*(1*((1-q).den : Int)) ≤ (((2*(activeFactorStart q+j)+1 : Nat) : Int)*(1-q).num)*2
    simpa only [Int.one_mul, Int.mul_comm] using hlo
  · show (Q'.ofNat (2*(activeFactorStart q+j)+1)*(1-q)).num*4 ≤
      (3 : Int)*((Q'.ofNat (2*(activeFactorStart q+j)+1)*(1-q)).den : Int)
    rw [Q'.mul_den_cast]
    change (((2*(activeFactorStart q+j)+1 : Nat) : Int)*(1-q).num)*4 ≤ 3*(1*((1-q).den : Int))
    simpa only [Int.one_mul, Int.mul_comm] using hhi

private theorem bScale_pin (h : Q') : ∀ n, HKConvGen.bScale h n ≈ 1+Q'.ofNat n*h
  | 0 => Q'.eqv_symm (Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left 1 _ _ (Q'.zero_mul_eqv h))
      (Q'.eqv_of_eq (Q'.add_zero' 1)))
  | n+1 => Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ h (bScale_pin h n))
      (Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
        (.add (.add (.const 1) (.mul (.var 0) (.var 1))) (.var 1))
        (.add (.const 1) (.mul (.add (.var 0) (.const 1)) (.var 1)))
        (by decide) (fun | 0 => Q'.ofNat n | _ => h))
        (Q'.add_eqv_congr_left 1 _ _ (Q'.mul_eqv_congr_right _ _ h
          (Q'.eqv_symm (HKConvGen.ofNat_succ_eqv n)))))

private theorem lower_bernoulli {q : Q'} (hq0 : (0 : Q') ≤ q)
    (hq1 : q ≤ (1 : Q')) : ∀ n, (1 : Q') ≤ q^n+Q'.ofNat n*(1-q)
  | 0 => by
      exact Q'.ge_of_eqv (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left 1 _ _ (Q'.zero_mul_eqv (1-q)))
        (Q'.eqv_of_eq (Q'.add_zero' 1)))
  | n+1 => by
      have hn := HKConvGen.ofNat_succ_eqv n
      have hg := Q'.sub_nonneg_of_le hq1
      have hn0 : (0 : Q') ≤ Q'.ofNat n := by
        rw [Q'.zero_le_iff_num_nonneg]
        exact Int.natCast_nonneg n
      have hs : (0 : Q') ≤ Q'.ofNat n*((1-q)*(1-q)) :=
        Q'.mul_nonneg _ _ hn0 (Q'.mul_nonneg _ _ hg hg)
      have hm := Q'.mul_le_mul_of_nonneg_left _ _ q (lower_bernoulli hq0 hq1 n) hq0
      have ha := Q'.add_le_add_right _ _ (1-q) hm
      have hz : 1 ≈ q*1+(1-q) := poly_identity_of_normal_eq
        (.const 1) (.add (.mul (.var 0) (.const 1)) (.add (.const 1) (.neg (.var 0))))
        (by decide) (fun _ => q)
      have he : q*(q^n+Q'.ofNat n*(1-q))+(1-q)+Q'.ofNat n*((1-q)*(1-q)) ≈
          q*q^n+(Q'.ofNat n+1)*(1-q) :=
        poly_identity_of_normal_eq
          (.add (.add (.mul (.var 0) (.add (.var 1) (.mul (.var 2)
            (.add (.const 1) (.neg (.var 0)))))) (.add (.const 1) (.neg (.var 0))))
            (.mul (.var 2) (.mul (.add (.const 1) (.neg (.var 0)))
              (.add (.const 1) (.neg (.var 0))))))
          (.add (.mul (.var 0) (.var 1))
            (.mul (.add (.var 2) (.const 1)) (.add (.const 1) (.neg (.var 0)))))
          (by decide) (fun | 0 => q | 1 => q^n | _ => Q'.ofNat n)
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hz)
        (Q'.le_trans' _ _ _ ha (Q'.le_trans' _ _ _
          (Q'.add_le_self_of_nonneg _ _ hs)
          (Q'.le_trans' _ _ _ (Q'.le_of_eqv he) (Q'.ge_of_eqv
            (Q'.add_eqv_congr_left (q*q^n) _ _ (Q'.mul_eqv_congr_right _ _ (1-q) hn))))))

/-- Every retained factor is the ORIGINAL odd amplitude, in [1/4,3/4]. -/
theorem activeFactor_amplitude_bounds {q : Q'}
    (hq : Q'.mkPos 16 17 (by decide) ≤ q) (hq1 : q < (1 : Q'))
    (j : Nat) (hj : j < activeFactorCount q) :
    Q'.mkPos 1 4 (by decide) ≤ HKPos.geoAmp q (activeFactorStart q+j) ∧
      HKPos.geoAmp q (activeFactorStart q+j) ≤ Q'.mkPos 3 4 (by decide) := by
  let m := 2*(activeFactorStart q+j)+1
  have hq0 : (0 : Q') ≤ q := Q'.le_trans' _ _ _ (by decide) hq
  have hq1' := Q'.le_of_lt hq1
  have hg := exponent_gap_bounds hq hq1 j hj
  have hlow := lower_bernoulli hq0 hq1' m
  have hupper : (1+Q'.ofNat m*(1-q))*q^m ≤ (1 : Q') :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_eqv_congr_right _ _ (q^m)
      (bScale_pin (1-q) m))) (HKConvGen.bernoulli_pow hq0 hq1' m)
  have hp0 := Q'.pow_nonneg q hq0 m
  constructor
  · have h := Q'.add_le_add_left (q^m) _ _ hg.2
    have ha : (1 : Q') ≤ q^m+Q'.mkPos 3 4 (by decide) := Q'.le_trans' _ _ _ hlow h
    have hs := Q'.add_le_add_right _ _ (-(Q'.mkPos 3 4 (by decide))) ha
    exact Q'.le_trans' _ _ _
      (Q'.ge_of_eqv (by decide : (1 : Q')+ -(Q'.mkPos 3 4 (by decide)) ≈
        Q'.mkPos 1 4 (by decide)))
      (Q'.le_trans' _ _ _ hs (Q'.le_of_eqv (poly_identity_of_normal_eq
        (.add (.add (.var 0) (.var 1)) (.neg (.var 1))) (.var 0)
        (by decide) (fun | 0 => q^m | _ => Q'.mkPos 3 4 (by decide)))))
  · have hmul := Q'.mul_le_mul_of_nonneg_right _ _ (q^m)
      (Q'.add_le_add_left 1 _ _ hg.1) hp0
    apply HKConvGen.mul_le_mul_left_cancel
      (by decide : (0 : Q') < 1+Q'.mkPos 1 2 (by decide))
    exact Q'.le_trans' _ _ _ hmul (Q'.le_trans' _ _ _ hupper
      (by decide : (1 : Q') ≤ (1+Q'.mkPos 1 2 (by decide))*Q'.mkPos 3 4 (by decide)))

#print axioms activeFactorStart
#print axioms activeFactorCount
#print axioms activeFactorCount_two
#print axioms activeFactorCount_mass
#print axioms activeFactor_amplitude_bounds

end YMGap.Continuum.SU2HeatJacobiActiveFactorCount
