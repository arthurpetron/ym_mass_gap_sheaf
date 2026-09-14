/-
# All-spin center charge and exact Haar vanishing

Parity, unlike exact homogeneous degree, survives the ordinary character
recurrence. Every monomial of chi_n(x) has block charge n*d modulo two
when x has block charge d. Products add charges, including shared blocks.
An odd charge at ANY integrated block gives zero original Haar moment.
No small-nome, independence, cutoff, positivity or connectedness premise.
-/

import YMGap.Continuum.SU2QuaternionSolidZonalCharacter
import YMGap.Continuum.SU2QuaternionRatPolyDifferential

namespace YMGap.Continuum.SU2QuaternionBlockCenterCharge

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionRatPolyDifferential

local infix:50 " ≈ " => Q'.eqv

/-- Integer charge is retained as data; the condition only depends on parity. -/
def HasCharge (block charge : Nat) (p : RatPoly) : Prop :=
  ∀ t, t ∈ p → quaternionBlockDegree t.1 block % 2 = charge % 2

theorem HasCharge.of_degree {block degree : Nat} {p : RatPoly}
    (h : HasQuaternionBlockDegree block degree p) : HasCharge block degree p :=
  fun t ht => congrArg (fun n => n % 2) (h t ht)

theorem HasCharge.relabel {block a b : Nat} {p : RatPoly}
    (h : HasCharge block a p) (he : a % 2 = b % 2) : HasCharge block b p :=
  fun t ht => (h t ht).trans he

theorem HasCharge.one (block : Nat) : HasCharge block 0 polyOne :=
  HasCharge.of_degree (hasQuaternionBlockDegree_one block)

theorem HasCharge.smul {block a : Nat} {p : RatPoly} (h : HasCharge block a p) (c : Q') :
    HasCharge block a (polySmul c p) := by
  intro t ht
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp ht
  exact h s hs

theorem HasCharge.add {block a : Nat} {p q : RatPoly}
    (hp : HasCharge block a p) (hq : HasCharge block a q) : HasCharge block a (polyAdd p q) :=
  fun t ht => (List.mem_append.mp ht).elim (hp t) (hq t)

theorem HasCharge.mul {block a b : Nat} {p q : RatPoly}
    (hp : HasCharge block a p) (hq : HasCharge block b q) : HasCharge block (a+b) (polyMul p q) := by
  intro t ht
  obtain ⟨u,hu,ht⟩ := List.mem_flatMap.mp ht
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp ht
  have hd : quaternionBlockDegree (monoMul u.1 v.1) block =
      quaternionBlockDegree u.1 block + quaternionBlockDegree v.1 block := by
    unfold quaternionBlockDegree
    simp only [SU2QuaternionRatPolyDifferential.exponentAt_monoMul]
    omega
  rw [hd, Nat.add_mod, hp u hu, hq v hv, ← Nat.add_mod]

/-- All spins, not just the homogeneous fundamental character. -/
theorem HasCharge.character {block d : Nat} {p : RatPoly} (h : HasCharge block d p) :
    ∀ n, HasCharge block (n*d) (characterPolynomial p n)
  | 0 => by simpa only [Nat.zero_mul] using HasCharge.one block
  | 1 => by simpa only [Nat.one_mul] using h.smul 2
  | n+2 => by
    apply HasCharge.add
    · exact ((h.smul 2).mul (h.character (n+1))).relabel (by
        simp only [Nat.add_mul, Nat.one_mul, Nat.two_mul]; omega)
    · exact ((h.character n).smul (-1)).relabel (by
        simp only [Nat.add_mul, Nat.two_mul]; omega)

private theorem prefix_zero (blocks block : Nat) (m : List Nat) (hb : block < blocks)
    (ho : quaternionBlockDegree m block % 2 = 1) : quaternionHaarPrefix blocks m ≈ 0 := by
  induction blocks generalizing block m with
  | zero => omega
  | succ blocks ih =>
    cases block with
    | zero =>
      have hz : sphereMoment4 (exponentAt m 0) (exponentAt m 1)
          (exponentAt m 2) (exponentAt m 3) = 0 := by
        unfold sphereMoment4
        split
        · change (exponentAt m 0 + exponentAt m 1 + exponentAt m 2 + exponentAt m 3) % 2 = 1 at ho
          omega
        · rfl
      change _ * quaternionHaarPrefix blocks (m.drop 4) ≈ 0
      rw [hz]
      exact Q'.zero_mul_eqv _
    | succ block =>
      have hd : quaternionBlockDegree (m.drop 4) block = quaternionBlockDegree m (block+1) := by
        unfold quaternionBlockDegree
        simp only [exponentAt_drop]
        have he (i : Nat) : 4 + (4*block+i) = 4*(block+1)+i := by omega
        rw [show 4+4*block = 4*(block+1) by omega, he 1, he 2, he 3]
      have hz := ih block (m.drop 4) (by omega) (by rw [hd]; exact ho)
      exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hz) (Q'.mul_zero_eqv _)

theorem monomial_zero (blocks block : Nat) (m : List Nat) (hb : block < blocks)
    (ho : quaternionBlockDegree m block % 2 = 1) : quaternionHaarMono blocks m ≈ 0 := by
  unfold quaternionHaarMono
  split
  · exact prefix_zero blocks block m hb ho
  · exact Q'.eqv_refl _

theorem haar_zero {blocks block charge : Nat} {p : RatPoly} (hb : block < blocks)
    (h : HasCharge block charge p) (ho : charge % 2 = 1) : quaternionHaar blocks p ≈ 0 := by
  induction p with
  | nil => exact Q'.eqv_refl _
  | cons t p ih =>
    have hm := monomial_zero blocks block t.1 hb ((h t List.mem_cons_self).trans ho)
    have ht := ih (fun s hs => h s (List.mem_cons_of_mem t hs))
    exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hm) (Q'.mul_zero_eqv _)) ht)
      (Q'.eqv_of_eq (Q'.zero_add' 0))

/-- The insertion need not be independent: its charge joins the SAME link. -/
theorem haar_insert_zero {blocks block a b : Nat} {p q : RatPoly} (hb : block < blocks)
    (hp : HasCharge block a p) (hq : HasCharge block b q) (ho : (a+b) % 2 = 1) :
    quaternionHaar blocks (polyMul p q) ≈ 0 := haar_zero hb (hp.mul hq) ho

end YMGap.Continuum.SU2QuaternionBlockCenterCharge

#print axioms YMGap.Continuum.SU2QuaternionBlockCenterCharge.HasCharge.of_degree
#print axioms YMGap.Continuum.SU2QuaternionBlockCenterCharge.HasCharge.relabel
#print axioms YMGap.Continuum.SU2QuaternionBlockCenterCharge.HasCharge.one
#print axioms YMGap.Continuum.SU2QuaternionBlockCenterCharge.HasCharge.smul
#print axioms YMGap.Continuum.SU2QuaternionBlockCenterCharge.HasCharge.add
#print axioms YMGap.Continuum.SU2QuaternionBlockCenterCharge.HasCharge.mul
#print axioms YMGap.Continuum.SU2QuaternionBlockCenterCharge.HasCharge.character
#print axioms YMGap.Continuum.SU2QuaternionBlockCenterCharge.monomial_zero
#print axioms YMGap.Continuum.SU2QuaternionBlockCenterCharge.haar_zero
#print axioms YMGap.Continuum.SU2QuaternionBlockCenterCharge.haar_insert_zero
