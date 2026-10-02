/-
# Finite scalar sampling of the ORIGINAL anchored dyadic response

At scale k>=p, the assigned geometric dyadic sample v/2^p has actual integer lag
2*side(k)+v*2^(k-p). Inside its cell, the SAME unit response decreases by
at most half^(p+1). Monotonicity means a two-family sample comparison pays
only ONE such cell error in each direction, even for different nomes and
widths. Division and remainder cover every integer query in a sampled cell.

The finite maximum below retains supplied per-sample moduli as data. No
cross-scale sample estimate is manufactured: those literal scalar comparisons
remain an input to the finite theorem, not a whole-convergence bundle.
No carrier map, changing-family limit, surviving norm, physical calibration
or continuum Yang--Mills conclusion is asserted.
-/

import YMGap.Continuum.BF4WilsonAllNomeDyadicResponseRounding
import YMGap.Continuum.BF4WilsonAllNomePositiveLagIncrement

namespace YMGap.Continuum.BF4WilsonAllNomeDyadicResponseSampling

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.HalfPow (half)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4DyadicWilsonSquare
open YMGap.Continuum.BF4WilsonAllNomeDyadicUnitExcitation (dyadicUnitResponse)
open YMGap.Continuum.BF4WilsonAllNomeDyadicResponseRounding
  (dyadicUnitResponse_shift_bounds)
open YMGap.Continuum.BF4WilsonAllNomePositiveLagIncrement (invSucc_le_spacing)

/-- Actual integer lag of the assigned geometric dyadic sample v/2^p. -/
def sampleLag (scale p v : Nat) : Nat := 2*side scale+v*2^(scale-p)

/-- The SAME original normalized connected correlator, not a surrogate table. -/
def sampleResponse {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (scale width : Nat) (hwidth : side scale < width) (p v : Nat) : CReal :=
  dyadicUnitResponse hw0 hw1 scale width hwidth (sampleLag scale p v)

private theorem mesh_spacing_pin (scale p : Nat) (hp : p ≤ scale) :
    Q'.eqv (Q'.ofNat (2^(scale-p))*spacing scale) (half^p) := by
  have hsplit : scale=(scale-p)+p := by omega
  have hnorm : Q'.eqv (Q'.ofNat (2^(scale-p))*half^(scale-p)) 1 :=
    Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (unit_side (scale-p))
  change Q'.eqv (Q'.ofNat (2^(scale-p))*half^scale) (half^p)
  have hpow := SU3CharFactor.pow_add_eqv half (scale-p) p
  rw [← hsplit] at hpow
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left _ _ _ hpow)
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hnorm)
        (Q'.one_mul_eqv _)))

/-- The table index has exactly the assigned geometric time, independent of
the finer scale. This is not a physical Yang--Mills time calibration. -/
theorem sample_spacing_pin (scale p v : Nat) (hp : p ≤ scale) :
    Q'.eqv (Q'.ofNat (v*2^(scale-p))*spacing scale) (Q'.ofNat v*half^p) :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ (SU3CharFactor.ofNat_mul_eqv v (2^(scale-p))))
    (Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _)
      (Q'.mul_eqv_congr_left _ _ _ (mesh_spacing_pin scale p hp)))

private theorem cell_spacing_pin (scale p : Nat) (hp : p ≤ scale) :
    Q'.eqv (Q'.ofNat (2^(scale-p))*spacing (scale+1)) (half^(p+1)) := by
  have h := mesh_spacing_pin (scale+1) (p+1) (Nat.succ_le_succ hp)
  have he : scale+1-(p+1)=scale-p := by omega
  simpa only [he] using h

private theorem cell_coefficient_bound (scale p v i : Nat) (hp : p ≤ scale)
    (hi : i < 2^(scale-p)) :
    Q'.ofNat i*Q'.invSucc (sampleLag scale p v) ≤ half^(p+1) := by
  have hn : side (scale+1) ≤ sampleLag scale p v := by
    change 2^(scale+1) ≤ 2*2^scale+v*2^(scale-p)
    rw [Nat.pow_succ, Nat.mul_comm (2^scale) 2]
    omega
  have hfirst := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat i)
    (invSucc_le_spacing (scale+1) (sampleLag scale p v) hn) (Q'.ofNat_nonneg i)
  have hsecond := Q'.mul_le_mul_of_nonneg_right _ _ (spacing (scale+1))
    (CReal.ofNat_le_ofNat (Nat.le_of_lt hi))
    (Q'.le_of_lt (spacing_positive (scale+1)))
  exact Q'.le_trans' _ _ _ hfirst
    (Q'.le_trans' _ _ _ hsecond (Q'.le_of_eqv (cell_spacing_pin scale p hp)))

/-- An actual query inside a sampled cell lies between the sample and that
sample minus half a mesh. Includes v=0 and zero remainder. -/
theorem dyadicUnitResponse_cell_bounds {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (scale width : Nat) (hwidth : side scale < width) (p v i : Nat)
    (hp : p ≤ scale) (hi : i < 2^(scale-p)) :
    leEv (dyadicUnitResponse hw0 hw1 scale width hwidth (sampleLag scale p v+i))
      (sampleResponse hw0 hw1 scale width hwidth p v) ∧
    leEv (sampleResponse hw0 hw1 scale width hwidth p v)
      (add (dyadicUnitResponse hw0 hw1 scale width hwidth (sampleLag scale p v+i))
        (ofQ' (half^(p+1)))) := by
  have h := dyadicUnitResponse_shift_bounds hw0 hw1 scale hwidth (sampleLag scale p v) i
  exact ⟨h.1, leEv_trans h.2 (leEv_add (leEv_refl _)
    (leEv_of_le (ofQ'_le_ofQ' (cell_coefficient_bound scale p v i hp hi))))⟩

private theorem add_budget (x : CReal) (a b : Q') :
    Equiv (add (add x (ofQ' a)) (ofQ' b)) (add x (ofQ' (b+a))) :=
  SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.add (.var 0) (.var 1)) (.var 2))
      (.add (.var 0) (.add (.var 2) (.var 1))) (by decide)
      (fun | 0 => x.approx n | 1 => a | _ => b))

variable {w₁ w₂ : Q'}
  (hw₁0 : (0 : Q') < w₁) (hw₁1 : w₁ < (1 : Q'))
  (hw₂0 : (0 : Q') < w₂) (hw₂1 : w₂ < (1 : Q'))
  (scale₁ width₁ : Nat) (hwidth₁ : side scale₁ < width₁)
  (scale₂ width₂ : Nat) (hwidth₂ : side scale₂ < width₂)

local notation "R₁" n:arg => dyadicUnitResponse hw₁0 hw₁1 scale₁ width₁ hwidth₁ n
local notation "R₂" n:arg => dyadicUnitResponse hw₂0 hw₂1 scale₂ width₂ hwidth₂ n
local notation "F₁" p:arg v:arg => sampleResponse hw₁0 hw₁1 scale₁ width₁ hwidth₁ p v
local notation "F₂" p:arg v:arg => sampleResponse hw₂0 hw₂1 scale₂ width₂ hwidth₂ p v

/-- ONE actual scalar sample controls the whole matched cell. Sample drift is
not proved or replaced by a convergence assumption. Monotonicity pays only one
half-mesh error in each direction. -/
theorem sample_cell_compare (p v i j : Nat) (hp₁ : p ≤ scale₁) (hp₂ : p ≤ scale₂)
    (hi : i < 2^(scale₁-p)) (hj : j < 2^(scale₂-p)) (epsilon : Q')
    (hsample : leEv (F₁ p v) (add (F₂ p v) (ofQ' epsilon)) ∧
      leEv (F₂ p v) (add (F₁ p v) (ofQ' epsilon))) :
    leEv (R₁ (sampleLag scale₁ p v+i))
      (add (R₂ (sampleLag scale₂ p v+j)) (ofQ' (epsilon+half^(p+1)))) ∧
    leEv (R₂ (sampleLag scale₂ p v+j))
      (add (R₁ (sampleLag scale₁ p v+i)) (ofQ' (epsilon+half^(p+1)))) := by
  have h₁ := dyadicUnitResponse_cell_bounds hw₁0 hw₁1 scale₁ width₁ hwidth₁ p v i hp₁ hi
  have h₂ := dyadicUnitResponse_cell_bounds hw₂0 hw₂1 scale₂ width₂ hwidth₂ p v j hp₂ hj
  constructor
  · exact leEv_trans h₁.1 (leEv_trans hsample.1
      (leEv_trans (leEv_add h₂.2 (leEv_refl _))
        (leEv_of_equiv (add_budget _ (half^(p+1)) epsilon))))
  · exact leEv_trans h₂.1 (leEv_trans hsample.2
      (leEv_trans (leEv_add h₁.2 (leEv_refl _))
        (leEv_of_equiv (add_budget _ (half^(p+1)) epsilon))))

private theorem quotient_remainder (n h : Nat) : n=(n/h)*h+n%h := by
  have he := Nat.mod_add_div n h
  simpa only [Nat.mul_comm, Nat.add_comm] using he.symm

/-- A FINITE actual table covers every pair of integer queries in matching
assigned geometric cells. The quotient equality is exact geometry, not a carrier map. -/
theorem sample_table_compare (p count n₁ n₂ : Nat)
    (hp₁ : p ≤ scale₁) (hp₂ : p ≤ scale₂)
    (hcell : n₁/2^(scale₁-p)=n₂/2^(scale₂-p))
    (hcount : n₁/2^(scale₁-p) < count) (epsilon : Q')
    (htable : ∀ v, v<count →
      leEv (F₁ p v) (add (F₂ p v) (ofQ' epsilon)) ∧
        leEv (F₂ p v) (add (F₁ p v) (ofQ' epsilon))) :
    leEv (R₁ (2*side scale₁+n₁))
      (add (R₂ (2*side scale₂+n₂)) (ofQ' (epsilon+half^(p+1)))) ∧
    leEv (R₂ (2*side scale₂+n₂))
      (add (R₁ (2*side scale₁+n₁)) (ofQ' (epsilon+half^(p+1)))) := by
  have h := sample_cell_compare hw₁0 hw₁1 hw₂0 hw₂1
    scale₁ width₁ hwidth₁ scale₂ width₂ hwidth₂
    p (n₁/2^(scale₁-p)) (n₁%2^(scale₁-p)) (n₂%2^(scale₂-p))
    hp₁ hp₂ (Nat.mod_lt _ (Nat.pow_pos (by decide)))
    (Nat.mod_lt _ (Nat.pow_pos (by decide))) epsilon
    (htable _ hcount)
  have e₁ : sampleLag scale₁ p (n₁/2^(scale₁-p))+n₁%2^(scale₁-p)=
      2*side scale₁+n₁ := by
    unfold sampleLag
    rw [Nat.add_assoc, ← quotient_remainder]
  have e₂ : sampleLag scale₂ p (n₁/2^(scale₁-p))+n₂%2^(scale₂-p)=
      2*side scale₂+n₂ := by
    rw [hcell]
    unfold sampleLag
    rw [Nat.add_assoc, ← quotient_remainder]
  simpa only [e₁, e₂] using h

/-- Type-level finite maximum of supplied sample moduli. No sample estimate
or whole changing-family convergence is asserted by this computation. -/
def finiteSampleModulus (count : Nat) (modulus : Nat → Q' → Nat) (epsilon : Q') : Nat :=
  (List.range count).foldr (fun v bound => max (modulus v epsilon) bound) 0

private theorem member_le_fold (f : Nat → Nat) :
    ∀ (xs : List Nat) (v : Nat), v∈xs → f v ≤ xs.foldr (fun i bound => max (f i) bound) 0
  | [], _, h => False.elim (List.not_mem_nil h)
  | a::xs, v, h => by
      rcases List.mem_cons.mp h with rfl | hv
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (member_le_fold f xs v hv) (Nat.le_max_right _ _)

theorem finiteSampleModulus_spec (count : Nat) (modulus : Nat → Q' → Nat)
    (epsilon : Q') (v : Nat) (hv : v<count) :
    modulus v epsilon ≤ finiteSampleModulus count modulus epsilon :=
  member_le_fold (fun i => modulus i epsilon) (List.range count) v (List.mem_range.mpr hv)

/-- The computed finite maximum really consumes the supplied per-sample tail
comparisons of an ORIGINAL parameter family. Only this finite scalar table is
assumed; the SAME-cell rounding conclusion is then proved for all its queries. -/
theorem sample_table_tail_compare (nome : Nat → Q')
    (hnome0 : ∀ k, (0 : Q') < nome k) (hnome1 : ∀ k, nome k < (1 : Q'))
    (width : Nat → Nat) (hwidth : ∀ k, side k < width k)
    (p count : Nat) (modulus : Nat → Q' → Nat) (epsilon : Q')
    (hsample : ∀ v, v<count → ∀ k l,
      modulus v epsilon ≤ k → modulus v epsilon ≤ l →
      p ≤ k → p ≤ l →
      leEv (sampleResponse (hnome0 k) (hnome1 k) k (width k) (hwidth k) p v)
        (add (sampleResponse (hnome0 l) (hnome1 l) l (width l) (hwidth l) p v)
          (ofQ' epsilon)) ∧
      leEv (sampleResponse (hnome0 l) (hnome1 l) l (width l) (hwidth l) p v)
        (add (sampleResponse (hnome0 k) (hnome1 k) k (width k) (hwidth k) p v)
          (ofQ' epsilon)))
    (k l n₁ n₂ : Nat)
    (hk : max p (finiteSampleModulus count modulus epsilon) ≤ k)
    (hl : max p (finiteSampleModulus count modulus epsilon) ≤ l)
    (hcell : n₁/2^(k-p)=n₂/2^(l-p)) (hcount : n₁/2^(k-p) < count) :
    leEv (dyadicUnitResponse (hnome0 k) (hnome1 k) k (width k) (hwidth k)
        (2*side k+n₁))
      (add (dyadicUnitResponse (hnome0 l) (hnome1 l) l (width l) (hwidth l)
        (2*side l+n₂)) (ofQ' (epsilon+half^(p+1)))) ∧
    leEv (dyadicUnitResponse (hnome0 l) (hnome1 l) l (width l) (hwidth l)
        (2*side l+n₂))
      (add (dyadicUnitResponse (hnome0 k) (hnome1 k) k (width k) (hwidth k)
        (2*side k+n₁)) (ofQ' (epsilon+half^(p+1)))) := by
  exact sample_table_compare (hnome0 k) (hnome1 k) (hnome0 l) (hnome1 l)
    k (width k) (hwidth k) l (width l) (hwidth l) p count n₁ n₂
    (Nat.le_trans (Nat.le_max_left _ _) hk)
    (Nat.le_trans (Nat.le_max_left _ _) hl) hcell hcount epsilon
    (fun v hv => hsample v hv k l
      (Nat.le_trans (finiteSampleModulus_spec count modulus epsilon v hv)
        (Nat.le_trans (Nat.le_max_right _ _) hk))
      (Nat.le_trans (finiteSampleModulus_spec count modulus epsilon v hv)
        (Nat.le_trans (Nat.le_max_right _ _) hl))
      (Nat.le_trans (Nat.le_max_left _ _) hk)
      (Nat.le_trans (Nat.le_max_left _ _) hl))

#print axioms sampleLag
#print axioms sampleResponse
#print axioms sample_spacing_pin
#print axioms dyadicUnitResponse_cell_bounds
#print axioms sample_cell_compare
#print axioms sample_table_compare
#print axioms finiteSampleModulus
#print axioms finiteSampleModulus_spec
#print axioms sample_table_tail_compare

end YMGap.Continuum.BF4WilsonAllNomeDyadicResponseSampling
