/-
# A nonzero extremal column for every admissible transvectant

The all-order coefficient formula becomes useful for basis construction only
after one exhibits a pivot that cannot vanish.  Here the input monomial
`x^a \otimes x^(b-k)y^k` follows the positive Cayley branch exclusively.
Its order-`k` output at the highest slot is a recursively positive rational.
-/

import YMGap.Continuum.SU2TransvectantAllOrder

namespace YMGap.Continuum.SU2TransvectantAdmissibleExtremal

open YMGap.Constructive
open YMGap.Continuum.BinaryForms
open YMGap.Continuum.TransvectantCG
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2TransvectantFactorialSeed
open YMGap.Continuum.SU2TransvectantMonomialRecurrence
open YMGap.Continuum.SU2TransvectantAllOrder
open YMGap.Continuum.SU2TransvectantLinearity
open YMGap.Continuum.BondMovingStep

/-- The product `a·k (a-1)·(k-1) ...` produced by following only the positive
Cayley branch. -/
def extremalCoeff : Nat → Nat → Q'
  | _, 0 => 1
  | a, k + 1 => Q'.ofNat (a * (k + 1)) * extremalCoeff (a - 1) k

/-- Every in-range extremal coefficient has strictly positive numerator. -/
theorem extremalCoeff_num_pos : ∀ a k : Nat, k ≤ a → 0 < (extremalCoeff a k).num := by
  intro a k
  induction k generalizing a with
  | zero =>
      intro _
      change 0 < (1 : Q').num
      decide
  | succ k ih =>
      intro hk
      have ha : 0 < a := by omega
      have hk' : k ≤ a - 1 := by omega
      have hih := ih (a - 1) hk'
      unfold extremalCoeff
      simp only [Q'.mul_num_cast, Q'.ofNat_num_cast]
      exact Int.mul_pos (by exact_mod_cast Nat.mul_pos ha (Nat.succ_pos k)) hih

/-- In particular the extremal coefficient is not semantically zero. -/
theorem extremalCoeff_not_eqv_zero (a k : Nat) (hk : k ≤ a) :
    ¬ (extremalCoeff a k).eqv 0 := by
  intro h
  unfold Q'.eqv at h
  have hn : (extremalCoeff a k).num = 0 := by
    have h' : (extremalCoeff a k).num * (1 : Int) =
        (0 : Int) * ((extremalCoeff a k).den : Int) := h
    rwa [Int.mul_one, Int.zero_mul] at h'
  have hp := extremalCoeff_num_pos a k hk
  omega

/-- The extremal input follows the positive branch exclusively, so its actual
order-`k` transvectant is the recursive positive coefficient. -/
theorem transvect_extremal : ∀ k a b : Nat, k ≤ a → k ≤ b →
    (transvect a b k
      (tprod (mono a) (mono (b - k))) (a + b - 2 * k)).eqv
      (extremalCoeff a k) := by
  intro k
  induction k with
  | zero =>
      intro a b _ _
      have h := transvect_monomial_matches_factorial_on_shell 0 a b a b
        (Nat.zero_le (a + b))
      refine Q'.eqv_trans _
        (transvectFactorialCoeff a b 0 a b) _ (by simpa using h) ?_
      simpa [extremalCoeff] using transvectFactorialCoeff_zero a b a b
  | succ k ih =>
      intro a b hka hkb
      have ha : 0 < a := by omega
      have hb : 0 < b := by omega
      have hka' : k ≤ a - 1 := by omega
      have hkb' : k ≤ b - 1 := by omega
      have hj : b - (k + 1) = (b - 1) - k := by omega
      have hs : a + b - 2 * (k + 1) = (a - 1) + (b - 1) - 2 * k := by omega
      have hgap : b - (b - (k + 1)) = k + 1 := by omega
      have hbranch0 := ih (a - 1) (b - 1) hka' hkb'
      have hbranch :
          (transvect (a - 1) (b - 1) k
            (tprod (mono (a - 1)) (mono (b - (k + 1))))
            (a + b - 2 * (k + 1))).eqv
            (extremalCoeff (a - 1) k) := by
        rw [hj, hs]
        exact hbranch0
      have hrec := transvect_succ_monomial a b k a (b - (k + 1))
        (a + b - 2 * (k + 1))
      have hpositive := Q'.mul_eqv_congr_left (Q'.ofNat (a * (k + 1)))
        _ _ hbranch
      have hnegative :
          ((-(Q'.ofNat ((a - a) * (b - (k + 1))))) *
            transvect (a - 1) (b - 1) k
              (tprod (mono a) (mono (b - (k + 1) - 1)))
              (a + b - 2 * (k + 1))).eqv 0 := by
        simp only [Nat.sub_self, Nat.zero_mul]
        change ((0 : Q') *
          transvect (a - 1) (b - 1) k
            (tprod (mono a) (mono (b - (k + 1) - 1)))
            (a + b - 2 * (k + 1))).eqv 0
        exact Q'.zero_mul_eqv _
      have hbranches :
          (Q'.ofNat (a * (k + 1)) *
              transvect (a - 1) (b - 1) k
                (tprod (mono (a - 1)) (mono (b - (k + 1))))
                (a + b - 2 * (k + 1)) +
            (-(Q'.ofNat ((a - a) * (b - (k + 1))))) *
              transvect (a - 1) (b - 1) k
                (tprod (mono a) (mono (b - (k + 1) - 1)))
                (a + b - 2 * (k + 1))).eqv
            (Q'.ofNat (a * (k + 1)) * extremalCoeff (a - 1) k) := by
        refine Q'.eqv_trans _
          (Q'.ofNat (a * (k + 1)) * extremalCoeff (a - 1) k + 0) _
          (Q'.add_eqv_congr' hpositive hnegative) ?_
        exact Q'.eqv_of_eq (Q'.add_zero' _)
      refine Q'.eqv_trans _ _ _ (by simpa only [hgap] using hrec) ?_
      simpa only [extremalCoeff] using hbranches

/-- The extremal output is not merely one nonzero coordinate: support
localization identifies the whole output form with that scalar times the
highest monomial. -/
theorem transvect_extremal_form (a b k : Nat) (hka : k ≤ a) (hkb : k ≤ b) :
    BFormEqv
      (transvect a b k (tprod (mono a) (mono (b - k))))
      (fun s => extremalCoeff a k * mono (a + b - 2 * k) s) := by
  intro s
  by_cases hs : s = a + b - 2 * k
  · subst s
    refine Q'.eqv_trans _ _ _ (transvect_extremal k a b hka hkb) ?_
    simp only [mono]
    exact Q'.eqv_symm (Q'.mul_one_eqv _)
  · have hoff :=
      YMGap.Continuum.SU2TransvectantGeneralCoefficient.transvect_monomial_zero_offshell
        a b k a (b - k) s (by omega)
    refine Q'.eqv_trans _ 0 _ hoff ?_
    simp only [mono, if_neg hs]
    exact Q'.eqv_symm (Q'.mul_zero_eqv _)

/-- Arithmetic content of the SU(2) fusion guard.  The selected contraction
order is integral, lies inside both input degrees, and leaves exactly the
declared output degree. -/
theorem fusionOK_couplingOrder_spec (a b c : Nat) (h : fusionOK a b c = true) :
    let k := couplingOrder a b c
    2 * k = a + b - c ∧ k ≤ a ∧ k ≤ b ∧ c + 2 * k = a + b := by
  unfold fusionOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  unfold couplingOrder
  have hlower := h.1.1
  have hupper := h.1.2
  have hparity := h.2
  have heven : (a + b - c) % 2 = 0 := by omega
  have htwice : 2 * ((a + b - c) / 2) = a + b - c := by omega
  have hleft : (a + b - c) / 2 ≤ a := by
    have hdiff : a + b - c ≤ 2 * a := by
      by_cases hab : a ≤ b
      · have : b - a ≤ c := by
          simpa [Nat.max_eq_right hab, Nat.min_eq_left hab] using hlower
        omega
      · have hba : b ≤ a := by omega
        omega
    omega
  have hright : (a + b - c) / 2 ≤ b := by
    have hdiff : a + b - c ≤ 2 * b := by
      by_cases hba : b ≤ a
      · have : a - b ≤ c := by
          simpa [Nat.max_eq_left hba, Nat.min_eq_right hba] using hlower
        omega
      · have hab : a ≤ b := by omega
        omega
    omega
  exact ⟨htwice, hleft, hright, by omega⟩

/-- Every admissible Clebsch--Gordan channel therefore has an explicit
nonzero highest-monomial pivot. -/
theorem admissible_transvect_extremal (a b c : Nat)
    (h : fusionOK a b c = true) :
    (transvect a b (couplingOrder a b c)
      (tprod (mono a) (mono (b - couplingOrder a b c))) c).eqv
      (extremalCoeff a (couplingOrder a b c)) := by
  let k := couplingOrder a b c
  change (transvect a b k (tprod (mono a) (mono (b - k))) c).eqv
    (extremalCoeff a k)
  have hs := fusionOK_couplingOrder_spec a b c h
  have hkA : k ≤ a := by simpa only [k] using hs.2.1
  have hkB : k ≤ b := by simpa only [k] using hs.2.2.1
  have hc : c = a + b - 2 * k := by
    dsimp only [k]
    omega
  rw [hc]
  exact transvect_extremal k a b hkA hkB

theorem admissible_transvect_extremal_not_zero (a b c : Nat)
    (h : fusionOK a b c = true) :
    ¬ (transvect a b (couplingOrder a b c)
      (tprod (mono a) (mono (b - couplingOrder a b c))) c).eqv 0 := by
  intro hz
  have hs := fusionOK_couplingOrder_spec a b c h
  apply extremalCoeff_not_eqv_zero a (couplingOrder a b c) hs.2.1
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm (admissible_transvect_extremal a b c h)) hz

/-- Form-level admissible pivot: the selected transvectant is exactly a
nonzero scalar multiple of the declared channel's highest monomial, at every
output coordinate. -/
theorem admissible_transvect_extremal_form (a b c : Nat)
    (h : fusionOK a b c = true) :
    BFormEqv
      (transvect a b (couplingOrder a b c)
        (tprod (mono a) (mono (b - couplingOrder a b c))))
      (fun s => extremalCoeff a (couplingOrder a b c) * mono c s) := by
  let k := couplingOrder a b c
  change BFormEqv
    (transvect a b k (tprod (mono a) (mono (b - k))))
    (fun s => extremalCoeff a k * mono c s)
  have hs := fusionOK_couplingOrder_spec a b c h
  have hkA : k ≤ a := by simpa only [k] using hs.2.1
  have hkB : k ≤ b := by simpa only [k] using hs.2.2.1
  have hc : c = a + b - 2 * k := by
    dsimp only [k]
    omega
  intro s
  rw [hc]
  exact transvect_extremal_form a b k hkA hkB s

/-- The closed factorial coefficient has the same nonzero extremal pivot. -/
theorem transvectFactorialCoeff_extremal (a b k : Nat)
    (hka : k ≤ a) (hkb : k ≤ b) :
    (transvectFactorialCoeff a b k a (b - k)).eqv (extremalCoeff a k) := by
  have hs := transvect_monomial_matches_factorial_on_shell k a b a (b - k)
    (by omega : k ≤ a + (b - k))
  have hindex : a + (b - k) - k = a + b - 2 * k := by omega
  have hext := transvect_extremal k a b hka hkb
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm hs) ?_
  rw [hindex]
  exact hext

/-- Hence every in-range order has a literal nonvanishing factorial pivot. -/
theorem transvectFactorialCoeff_extremal_not_zero (a b k : Nat)
    (hka : k ≤ a) (hkb : k ≤ b) :
    ¬ (transvectFactorialCoeff a b k a (b - k)).eqv 0 := by
  intro hzero
  apply extremalCoeff_not_eqv_zero a k hka
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm (transvectFactorialCoeff_extremal a b k hka hkb)) hzero

end YMGap.Continuum.SU2TransvectantAdmissibleExtremal

#print axioms YMGap.Continuum.SU2TransvectantAdmissibleExtremal.extremalCoeff_num_pos
#print axioms YMGap.Continuum.SU2TransvectantAdmissibleExtremal.extremalCoeff_not_eqv_zero
#print axioms YMGap.Continuum.SU2TransvectantAdmissibleExtremal.transvect_extremal
#print axioms YMGap.Continuum.SU2TransvectantAdmissibleExtremal.transvect_extremal_form
#print axioms YMGap.Continuum.SU2TransvectantAdmissibleExtremal.fusionOK_couplingOrder_spec
#print axioms YMGap.Continuum.SU2TransvectantAdmissibleExtremal.admissible_transvect_extremal
#print axioms YMGap.Continuum.SU2TransvectantAdmissibleExtremal.admissible_transvect_extremal_not_zero
#print axioms YMGap.Continuum.SU2TransvectantAdmissibleExtremal.admissible_transvect_extremal_form
#print axioms YMGap.Continuum.SU2TransvectantAdmissibleExtremal.transvectFactorialCoeff_extremal
#print axioms YMGap.Continuum.SU2TransvectantAdmissibleExtremal.transvectFactorialCoeff_extremal_not_zero
