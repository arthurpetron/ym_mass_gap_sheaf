/-
# Constructive reflection of extensional `QPoly` equality

`SU2ClassPolynomialAlgebra.PolyEqv` says that two coefficient lists have
semantically equal values at every rational point.  Descending the vacuum
coefficient from a Chebyshev packet to a bare polynomial requires the converse
direction to the existing `QPoly.poly_eqv`: extensional equality must force the
coefficient difference to be semantically zero.

This file proves that converse without choice or normalization of `Q'`.  The
engine is a division-free root-count induction.  A tail of a polynomial that
vanishes everywhere vanishes at sufficiently many positive integer points;
those points are nonzero, so cancellation is constructive.  Root counting then
promotes the finite tail information to all rational points, allowing induction
through every coefficient.

The resulting equivalence

  `PolyEqv p q <-> QPoly.allZero (QPoly.psub p q)`

is the exact reflection/uniqueness hinge needed by a canonical Chebyshev-U
coefficient extractor.  It does not itself define that extractor or the Haar
functional.

# Axiom gate

All declarations are MLTT/HoTT-clean up to `propext` / `Quot.sound`.  There is
no `Classical.*`, `Real`, `native_decide`, `sorry`, `admit`, or custom axiom.
-/

import YMGap.Continuum.SU2ClassPolynomialAlgebra

namespace YMGap.Continuum.SU2ClassPolynomialExtensionalReflection

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum.SU2ClassPolynomialAlgebra

/-! ## A division-free factor theorem and root count -/

theorem eqv_zero_iff_num {a : Q'} : a.eqv 0 <-> a.num = 0 := by
  constructor
  · intro h
    have h' : a.num * (1 : Int) = (0 : Int) * (a.den : Int) := h
    simpa using h'
  · intro h
    show a.num * (1 : Int) = (0 : Int) * (a.den : Int)
    simp [h]

theorem eqv_zero_of_mul_left {a b : Q'} (ha : ¬ a.eqv 0)
    (h : (a * b).eqv 0) : b.eqv 0 := by
  have hnum : a.num * b.num = 0 := by
    have h' : (a * b).num * ((0 : Q').den : Int) =
        (0 : Q').num * ((a * b).den : Int) := h
    have : a.num * b.num * (1 : Int) =
        0 * ((a * b).den : Int) := h'
    simpa using this
  have hanum : a.num ≠ 0 := fun hc => ha (eqv_zero_iff_num.2 hc)
  rcases Int.mul_eq_zero.1 hnum with h0 | h0
  · exact absurd h0 hanum
  · exact eqv_zero_iff_num.2 h0

/-- Division-free synthetic deflation at `r`. -/
def deflate (r : Q') : Poly -> Poly
  | [] => []
  | [_] => []
  | (_ :: c1 :: cs) => eval (c1 :: cs) r :: deflate r (c1 :: cs)

theorem length_deflate_le (r : Q') : forall p : Poly,
    (deflate r p).length <= p.length - 1
  | [] => Nat.le_refl 0
  | [_] => Nat.le_refl 0
  | (_ :: c1 :: cs) => by
      have ih := length_deflate_le r (c1 :: cs)
      show (eval (c1 :: cs) r :: deflate r (c1 :: cs)).length <=
        (c1 :: cs).length
      simp only [List.length_cons] at *
      omega

private theorem deflate_algebra (c x r E Er R : Q')
    (ih : E.eqv (Er + (x + -r) * R)) :
    (c + x * E).eqv
      ((c + r * Er) + (x + -r) * (Er + x * R)) := by
  have hL : (c + x * E).eqv
      ((c + x * Er) + (x + -r) * (x * R)) := by
    have hxE : (x * E).eqv (x * Er + (x + -r) * (x * R)) := by
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left x _ _ ih) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_add_eqv x Er ((x + -r) * R)) ?_
      refine Q'.add_eqv_congr_left _ _ _ ?_
      refine Q'.eqv_trans _ ((x * (x + -r)) * R) _
        (Q'.eqv_symm (Q'.mul_assoc_eqv x (x + -r) R)) ?_
      refine Q'.eqv_trans _ (((x + -r) * x) * R) _
        (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv x (x + -r))) ?_
      exact Q'.mul_assoc_eqv (x + -r) x R
    refine Q'.eqv_trans _ (c + (x * Er + (x + -r) * (x * R))) _
      (Q'.add_eqv_congr_left _ _ _ hxE) ?_
    exact Q'.eqv_symm (Q'.add_assoc_eqv c (x * Er) ((x + -r) * (x * R)))
  have hR : ((c + r * Er) + (x + -r) * (Er + x * R)).eqv
      ((c + x * Er) + (x + -r) * (x * R)) := by
    have hexpand : ((x + -r) * (Er + x * R)).eqv
        ((x * Er + (-r) * Er) + (x + -r) * (x * R)) := by
      refine Q'.eqv_trans _ _ _
        (Q'.mul_add_eqv (x + -r) Er (x * R)) ?_
      exact Q'.add_eqv_congr_right _ _ _ (q_add_mul x (-r) Er)
    refine Q'.eqv_trans _
      ((c + r * Er) + ((x * Er + (-r) * Er) + (x + -r) * (x * R))) _
      (Q'.add_eqv_congr_left _ _ _ hexpand) ?_
    refine Q'.eqv_trans _
      (c + (r * Er + ((x * Er + (-r) * Er) + (x + -r) * (x * R)))) _
      (Q'.add_assoc_eqv c (r * Er)
        ((x * Er + (-r) * Er) + (x + -r) * (x * R))) ?_
    have hin : (r * Er + ((x * Er + (-r) * Er) +
        (x + -r) * (x * R))).eqv
        (x * Er + (x + -r) * (x * R)) := by
      refine Q'.eqv_trans _
        (r * Er + (x * Er + ((-r) * Er + (x + -r) * (x * R)))) _
        (Q'.add_eqv_congr_left _ _ _
          (Q'.add_assoc_eqv (x * Er) ((-r) * Er) ((x + -r) * (x * R)))) ?_
      refine Q'.eqv_trans _
        ((r * Er + x * Er) + ((-r) * Er + (x + -r) * (x * R))) _
        (Q'.eqv_symm (Q'.add_assoc_eqv (r * Er) (x * Er)
          ((-r) * Er + (x + -r) * (x * R)))) ?_
      refine Q'.eqv_trans _
        ((x * Er + r * Er) + ((-r) * Er + (x + -r) * (x * R))) _
        (Q'.add_eqv_congr_right _ _ _ (Q'.add_comm_eqv (r * Er) (x * Er))) ?_
      refine Q'.eqv_trans _
        (x * Er + (r * Er + ((-r) * Er + (x + -r) * (x * R)))) _
        (Q'.add_assoc_eqv (x * Er) (r * Er)
          ((-r) * Er + (x + -r) * (x * R))) ?_
      refine Q'.add_eqv_congr_left _ _ _ ?_
      refine Q'.eqv_trans _
        ((r * Er + (-r) * Er) + (x + -r) * (x * R)) _
        (Q'.eqv_symm (Q'.add_assoc_eqv (r * Er) ((-r) * Er)
          ((x + -r) * (x * R)))) ?_
      refine Q'.eqv_trans _ ((0 : Q') + (x + -r) * (x * R)) _ ?_
        (q_zero_add_eqv _)
      refine Q'.add_eqv_congr_right _ _ _ ?_
      refine Q'.eqv_trans _ (r * Er + -(r * Er)) _
        (Q'.add_eqv_congr_left _ _ _ (Q'.neg_mul_eqv r Er)) ?_
      exact Q'.eqv_trans _ (-(r * Er) + r * Er) _
        (Q'.add_comm_eqv (r * Er) (-(r * Er)))
        (Q'.neg_add_self_eqv (r * Er))
    refine Q'.eqv_trans _ (c + (x * Er + (x + -r) * (x * R))) _
      (Q'.add_eqv_congr_left _ _ _ hin) ?_
    exact Q'.eqv_symm
      (Q'.add_assoc_eqv c (x * Er) ((x + -r) * (x * R)))
  exact Q'.eqv_trans _ _ _ hL (Q'.eqv_symm hR)

/-- `p(x) = p(r) + (x-r) deflate_r(p)(x)`, semantically over `Q'`. -/
theorem eval_deflate (r : Q') : forall (p : Poly) (x : Q'),
    (eval p x).eqv (eval p r + (x + -r) * eval (deflate r p) x)
  | [], x => by
      show (0 : Q').eqv (0 + (x + -r) * eval ([] : Poly) x)
      refine Q'.eqv_symm ?_
      exact Q'.eqv_trans _ _ _ (q_zero_add_eqv _)
        (q_mul_zero (x + -r))
  | [c], x => by
      show (c + x * eval ([] : Poly) x).eqv
        ((c + r * eval ([] : Poly) r) +
          (x + -r) * eval (deflate r [c]) x)
      refine Q'.eqv_trans _ c _ ?_ ?_
      · exact Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_left _ _ _ (q_mul_zero x)) (q_add_zero_eqv c)
      · refine Q'.eqv_symm ?_
        refine Q'.eqv_trans _ ((c + r * eval ([] : Poly) r) + (0 : Q')) _
          (Q'.add_eqv_congr_left _ _ _ (q_mul_zero (x + -r))) ?_
        refine Q'.eqv_trans _ (c + r * eval ([] : Poly) r) _
          (q_add_zero_eqv _) ?_
        exact Q'.eqv_trans _ (c + (0 : Q')) _
          (Q'.add_eqv_congr_left _ _ _ (q_mul_zero r)) (q_add_zero_eqv c)
  | (c :: c1 :: cs), x => by
      have ih := eval_deflate r (c1 :: cs) x
      show (c + x * eval (c1 :: cs) x).eqv
        ((c + r * eval (c1 :: cs) r) +
          (x + -r) * (eval (c1 :: cs) r +
            x * eval (deflate r (c1 :: cs)) x))
      exact deflate_algebra c x r (eval (c1 :: cs) x)
        (eval (c1 :: cs) r) (eval (deflate r (c1 :: cs)) x) ih

theorem sub_eqv_zero_iff {x y : Q'} : (y + -x).eqv 0 <-> x.eqv y := by
  have hnum : (y + -x).num =
      y.num * (x.den : Int) - x.num * (y.den : Int) := by
    show y.num * ((-x).den : Int) + (-x).num * (y.den : Int) =
      y.num * (x.den : Int) - x.num * (y.den : Int)
    have h1 : ((-x).den : Int) = (x.den : Int) := by rw [Q'.neg_den]
    have h2 : (-x).num = -x.num := rfl
    rw [h1, h2, Int.neg_mul, Int.sub_eq_add_neg]
  rw [eqv_zero_iff_num, hnum]
  constructor
  · intro h
    show x.num * (y.den : Int) = y.num * (x.den : Int)
    omega
  · intro h
    have hxy : x.num * (y.den : Int) = y.num * (x.den : Int) := h
    omega

inductive QDistinct : List Q' -> Prop
  | nil : QDistinct []
  | cons : forall {x : Q'} {xs : List Q'},
      (forall y, y ∈ xs -> ¬ x.eqv y) -> QDistinct xs -> QDistinct (x :: xs)

theorem roots_zero : forall xs : List Q', QDistinct xs -> forall p : Poly,
    p.length <= xs.length ->
    (forall y, y ∈ xs -> (eval p y).eqv 0) ->
    forall z, (eval p z).eqv 0
  | [], _, p, hlen, _, z => by
      cases p with
      | nil => exact Q'.eqv_refl 0
      | cons _ _ => simp at hlen
  | (x0 :: rest), hdist, p, hlen, hroots, z => by
      cases hdist with
      | cons hne hdrest =>
        have hpx0 : (eval p x0).eqv 0 :=
          hroots x0 (List.mem_cons_self ..)
        have hlenq : (deflate x0 p).length <= rest.length := by
          have h1 := length_deflate_le x0 p
          have h2 : p.length <= rest.length + 1 := by
            simpa [List.length_cons] using hlen
          omega
        have hrootsq : forall y, y ∈ rest ->
            (eval (deflate x0 p) y).eqv 0 := by
          intro y hy
          have hpy : (eval p y).eqv 0 :=
            hroots y (List.mem_cons_of_mem _ hy)
          have hdef := eval_deflate x0 p y
          have hprod : ((y + -x0) * eval (deflate x0 p) y).eqv 0 := by
            have hAB : (eval p x0 +
                (y + -x0) * eval (deflate x0 p) y).eqv
                ((y + -x0) * eval (deflate x0 p) y) :=
              Q'.eqv_trans _ ((0 : Q') +
                  (y + -x0) * eval (deflate x0 p) y) _
                (Q'.add_eqv_congr_right _ _ _ hpx0) (q_zero_add_eqv _)
            exact Q'.eqv_trans _ (eval p y) _
              (Q'.eqv_symm (Q'.eqv_trans _ _ _ hdef hAB)) hpy
          apply eqv_zero_of_mul_left (b := eval (deflate x0 p) y) _ hprod
          intro hz
          exact hne y hy (sub_eqv_zero_iff.1 hz)
        have hqz := roots_zero rest hdrest (deflate x0 p) hlenq hrootsq z
        refine Q'.eqv_trans _
          (eval p x0 + (z + -x0) * eval (deflate x0 p) z) _
          (eval_deflate x0 p z) ?_
        refine Q'.eqv_trans _ ((0 : Q') + (0 : Q')) _ ?_
          (q_zero_add_eqv 0)
        exact q_add_congr hpx0
          (Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_left _ _ _ hqz) (q_mul_zero _))

/-! ## Positive rational grids -/

def positiveGrid : Nat -> List Q'
  | 0 => []
  | n + 1 => Q'.ofNat (n + 1) :: positiveGrid n

@[simp] theorem positiveGrid_length : forall n,
    (positiveGrid n).length = n
  | 0 => rfl
  | n + 1 => by simp [positiveGrid, positiveGrid_length n]

theorem positiveGrid_member : forall {n : Nat} {y : Q'},
    y ∈ positiveGrid n ->
    exists k : Nat, 0 < k /\ k <= n /\ y = Q'.ofNat k
  | 0, _, h => by simp [positiveGrid] at h
  | n + 1, y, h => by
      rw [positiveGrid, List.mem_cons] at h
      rcases h with h | h
      · exact ⟨n + 1, Nat.succ_pos n, Nat.le_refl _, h⟩
      · obtain ⟨k, hk0, hkn, hy⟩ := positiveGrid_member h
        exact ⟨k, hk0, Nat.le_trans hkn (Nat.le_succ n), hy⟩

theorem ofNat_eqv_iff (m n : Nat) :
    (Q'.ofNat m).eqv (Q'.ofNat n) <-> m = n := by
  show Int.ofNat m * (1 : Int) = Int.ofNat n * (1 : Int) <-> m = n
  simpa using (Int.ofNat_inj : (Int.ofNat m = Int.ofNat n <-> m = n))

theorem positiveGrid_distinct : forall n, QDistinct (positiveGrid n)
  | 0 => QDistinct.nil
  | n + 1 => by
      rw [positiveGrid]
      apply QDistinct.cons
      · intro y hy heq
        obtain ⟨k, hk0, hkn, rfl⟩ := positiveGrid_member hy
        have hnk : n + 1 = k := (ofNat_eqv_iff (n + 1) k).1 heq
        omega
      · exact positiveGrid_distinct n

theorem positiveGrid_nonzero {n : Nat} {y : Q'}
    (hy : y ∈ positiveGrid n) : ¬ y.eqv 0 := by
  obtain ⟨k, hk0, _, rfl⟩ := positiveGrid_member hy
  intro h
  have hk : k = 0 := (ofNat_eqv_iff k 0).1 h
  omega

/-! ## Coefficient reflection -/

def CoeffZero (p : Poly) : Prop := forall c, c ∈ p -> c.eqv 0

private theorem eval_cons_zero (c : Q') (cs : Poly) :
    (eval (c :: cs) 0).eqv c := by
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left _ _ _ (q_zero_mul (eval cs 0)))
    (q_add_zero_eqv c)

/-- A polynomial vanishing at every rational point has every raw coefficient
semantically zero.  Trailing and unnormalized zero representatives are allowed. -/
theorem coeffZero_of_evalZero : forall p : Poly,
    (forall x, (eval p x).eqv 0) -> CoeffZero p
  | [], _ => by intro c hc; simp at hc
  | (c :: cs), h => by
      have hc : c.eqv 0 :=
        Q'.eqv_trans _ _ _ (Q'.eqv_symm (eval_cons_zero c cs)) (h 0)
      have htailRoots : forall y, y ∈ positiveGrid cs.length ->
          (eval cs y).eqv 0 := by
        intro y hy
        have hp : (eval (c :: cs) y).eqv 0 := h y
        have hprod : (y * eval cs y).eqv 0 := by
          refine Q'.eqv_trans _ (c + y * eval cs y) _ ?_ hp
          refine Q'.eqv_symm ?_
          exact Q'.eqv_trans _ ((0 : Q') + y * eval cs y) _
            (Q'.add_eqv_congr_right _ _ _ hc) (q_zero_add_eqv _)
        exact eqv_zero_of_mul_left (positiveGrid_nonzero hy) hprod
      have htail : forall x, (eval cs x).eqv 0 :=
        roots_zero (positiveGrid cs.length) (positiveGrid_distinct cs.length)
          cs (by simp) htailRoots
      have ih := coeffZero_of_evalZero cs htail
      intro a ha
      rw [List.mem_cons] at ha
      rcases ha with rfl | ha
      · exact hc
      · exact ih a ha

theorem allZero_of_coeffZero : forall p : Poly, CoeffZero p -> allZero p
  | [], _ => rfl
  | c :: cs, h => by
      unfold allZero allZeroB
      rw [Bool.and_eq_true]
      constructor
      · exact decide_eq_true (h c (List.mem_cons_self ..))
      · exact allZero_of_coeffZero cs
          (fun a ha => h a (List.mem_cons_of_mem c ha))

/-- The missing converse to `QPoly.poly_eqv`: extensional equality forces the
coefficient difference to pass the exact kernel `allZero` test. -/
theorem allZero_psub_of_polyEqv {p q : Poly} (h : PolyEqv p q) :
    allZero (psub p q) := by
  apply allZero_of_coeffZero
  apply coeffZero_of_evalZero
  intro x
  refine Q'.eqv_trans _ (eval p x + -(eval q x)) _
    (eval_psub p q x) ?_
  refine Q'.eqv_trans _ (eval q x + -(eval q x)) _
    (Q'.add_eqv_congr_right _ _ _ (h x)) ?_
  exact Q'.eqv_trans _ _ _
    (Q'.add_comm_eqv (eval q x) (-(eval q x)))
    (Q'.neg_add_self_eqv (eval q x))

/-- Extensional equality and the reflective coefficient test coincide. -/
theorem polyEqv_iff_allZero_psub (p q : Poly) :
    PolyEqv p q <-> allZero (psub p q) := by
  constructor
  · exact allZero_psub_of_polyEqv
  · intro h x
    exact poly_eqv p q x h

end YMGap.Continuum.SU2ClassPolynomialExtensionalReflection

#print axioms YMGap.Continuum.SU2ClassPolynomialExtensionalReflection.eval_deflate
#print axioms YMGap.Continuum.SU2ClassPolynomialExtensionalReflection.roots_zero
#print axioms YMGap.Continuum.SU2ClassPolynomialExtensionalReflection.positiveGrid_distinct
#print axioms YMGap.Continuum.SU2ClassPolynomialExtensionalReflection.coeffZero_of_evalZero
#print axioms YMGap.Continuum.SU2ClassPolynomialExtensionalReflection.allZero_psub_of_polyEqv
#print axioms YMGap.Continuum.SU2ClassPolynomialExtensionalReflection.polyEqv_iff_allZero_psub
