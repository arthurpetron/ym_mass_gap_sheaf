/-
# Bounded slab insertion on the periodic torus (C11; PP Lemma 3.3 finite core)

Source: F215 paper 5 ("An Isolated Particle Pole for the Two-Dimensional O(3)
Spin Field"), Lemma 3.3, as extracted in `reviews/openai-math/F215-METHODS.md`
§1.6 P6.  The lemma: for a bounded observable `F` supported in a time slab of
thickness `r`, the slab operator `A_F` has `‖A_F‖ ≤ ‖F‖_∞`, and for `t > r`
`|E_{tor;t,w} F − E_{cyl,w} F| ≤ ‖F‖_∞ (s(t−r) + s(t))`, where
`s(u) = Σ_{j≥1} e^{−uE_j}` is the excited heat trace.  Proof:
`E_tor F = Tr(A_F T^{(t−r)/a}) / (1 + s(t))`.

ADDITIVE.  Two layers:

1. **Slab geometry on `Z4TorusGeometry`** (proved finite lemmas, general `N`):
   time slabs `slabVertices N s r` (x0 ∈ {s, …, s+r−1} mod N), counts
   `r·N³` (vertices) and `6·r·N³` (plaquettes), membership, inclusion in the
   torus, the slab/complement count `r·N³ + (N−r)·N³ = N⁴`, and transport of
   slabs by time translation.
2. **Spectral-list algebra of Lemma 3.3** (proved, `Q'`): with `λ₀ = 1`,
   `λ_i ≥ 0`, `−M ≤ d_i ≤ M`,
   `|Num − d₀·Den| ≤ M(s_m + s_n)` and, for any `E` with `E·Den ≈ Num`,
   `|E − d₀| ≤ M(s_m + s_n)` (`slab_insertion_bound`).

The analytic input is the named structure `SlabInsertionSpectrum`: the
torus expectation is the trace ratio `E·(1+s_n) = d₀ + Σ_{i≥1} d_i λ_i^m`
with `d_i = ⟨e_i, A_F e_i⟩` and `|d_i| ≤ ‖F‖_∞` (spectral theorem for the
transfer matrix, `‖A_F‖ ≤ ‖F‖_∞`), and `E_cyl F = d₀`.  These are fields,
not proofs: REDUCTION.

**U(1) test.** The statement is group-blind (any positive transfer matrix);
it is geometric/spectral PLUMBING.  It converts small excited traces into
torus≈cylinder comparison, but it cannot produce the smallness of `s`; that
is the gap itself.  Choice-free; axioms `propext`, `Quot.sound` only.
-/

import YMGap.Continuum.Z4TorusGeometry
import YMGap.Continuum.RingNormaliser
import YMGap.Constructive.AbsQ
import YMGap.Constructive.Geometric

namespace YMGap.Continuum.TorusSlabInsertion

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4TorusGeometry

/-! ## 1. Time slabs on the torus -/

/-- Time coordinates `s, s+1, …, s+r−1` (mod `N`). -/
def slabTimes (N s r : Nat) : List Nat := (List.range r).map fun j => (s + j) % N

/-- Spatial cross-section `{0..N−1}³`. -/
def crossSection (N : Nat) : List (Nat × Nat × Nat) :=
  (List.range N).flatMap fun b => (List.range N).flatMap fun c =>
    (List.range N).map fun d => (b, c, d)

theorem crossSection_length (N : Nat) : (crossSection N).length = N * (N * N) := by
  unfold crossSection
  rw [length_flatMap_const _ (N * N) (fun _ => by
    rw [length_flatMap_const _ N (fun _ => by rw [List.length_map, List.length_range]), List.length_range]),
    List.length_range]

theorem mem_crossSection (N : Nat) (x : Nat × Nat × Nat) :
    x ∈ crossSection N ↔ x.1 < N ∧ x.2.1 < N ∧ x.2.2 < N := by
  obtain ⟨b, c, d⟩ := x
  unfold crossSection
  constructor
  · intro h
    obtain ⟨b', hb, h⟩ := List.mem_flatMap.mp h
    obtain ⟨c', hc, h⟩ := List.mem_flatMap.mp h
    obtain ⟨d', hd, he⟩ := List.mem_map.mp h
    have e1 : b' = b := congrArg (fun z : Nat × Nat × Nat => z.1) he
    have e2 : c' = c := congrArg (fun z : Nat × Nat × Nat => z.2.1) he
    have e3 : d' = d := congrArg (fun z : Nat × Nat × Nat => z.2.2) he
    exact ⟨e1 ▸ List.mem_range.mp hb, e2 ▸ List.mem_range.mp hc, e3 ▸ List.mem_range.mp hd⟩
  · rintro ⟨hb, hc, hd⟩
    exact List.mem_flatMap.mpr ⟨b, List.mem_range.mpr hb, List.mem_flatMap.mpr
      ⟨c, List.mem_range.mpr hc, List.mem_map.mpr ⟨d, List.mem_range.mpr hd, rfl⟩⟩⟩

/-- Vertices of the time slab of thickness `r` starting at time `s`. -/
def slabVertices (N s r : Nat) : List Z4Vertex :=
  (slabTimes N s r).flatMap fun a => (crossSection N).map fun x => (a, x)

/-- Plaquettes based in the slab (all six planes). -/
def slabPlaquettes (N s r : Nat) : List Z4Plaq :=
  (slabVertices N s r).flatMap fun v => z4Planes.map fun P => (v, P)

theorem slabVertices_length (N s r : Nat) :
    (slabVertices N s r).length = r * (N * (N * N)) := by
  unfold slabVertices
  rw [length_flatMap_const _ (N * (N * N)) (fun _ => by
    rw [List.length_map, crossSection_length]), slabTimes, List.length_map,
    List.length_range]

theorem slabPlaquettes_length (N s r : Nat) :
    (slabPlaquettes N s r).length = 6 * (r * (N * (N * N))) := by
  unfold slabPlaquettes
  rw [length_flatMap_const _ 6 (fun _ => rfl), slabVertices_length, Nat.mul_comm]

/-- Cutting the time circle at a slab of thickness `r ≤ N`: slab and
complementary slab together carry exactly the `N⁴` torus vertices (count). -/
theorem slab_complement_count {N r : Nat} (hr : r ≤ N) (s : Nat) :
    (slabVertices N s r).length + (slabVertices N (s + r) (N - r)).length =
      (boxVertices N).length := by
  rw [slabVertices_length, slabVertices_length, ← Nat.add_mul, Nat.add_sub_cancel' hr,
    boxVertices_length, Nat.mul_assoc, Nat.mul_assoc]

theorem mem_slabVertices (N s r : Nat) (v : Z4Vertex) :
    v ∈ slabVertices N s r ↔
      (∃ j, j < r ∧ v.1 = (s + j) % N) ∧ v.2.1 < N ∧ v.2.2.1 < N ∧ v.2.2.2 < N := by
  obtain ⟨a, x⟩ := v
  unfold slabVertices slabTimes
  constructor
  · intro h
    obtain ⟨a', ha, h⟩ := List.mem_flatMap.mp h
    obtain ⟨x', hx, he⟩ := List.mem_map.mp h
    obtain ⟨j, hj, hja⟩ := List.mem_map.mp ha
    have e1 : a' = a := congrArg Prod.fst he
    have e2 : x' = x := congrArg Prod.snd he
    rw [e2] at hx
    exact ⟨⟨j, List.mem_range.mp hj, e1 ▸ hja.symm⟩, (mem_crossSection N x).mp hx⟩
  · rintro ⟨⟨j, hj, hja⟩, hx⟩
    exact List.mem_flatMap.mpr ⟨a, List.mem_map.mpr ⟨j, List.mem_range.mpr hj, hja.symm⟩,
      List.mem_map.mpr ⟨x, (mem_crossSection N x).mpr hx, rfl⟩⟩

theorem slab_inBox {N s r : Nat} (hN : 0 < N) {v : Z4Vertex}
    (hv : v ∈ slabVertices N s r) : InBox N v := by
  obtain ⟨⟨j, _, hj⟩, h2, h3, h4⟩ := (mem_slabVertices N s r v).mp hv
  exact ⟨hj ▸ Nat.mod_lt _ hN, h2, h3, h4⟩

/-- Slab plaquettes are torus plaquettes. -/
theorem slabPlaquettes_sub {N s r : Nat} (hN : 0 < N) {p : Z4Plaq}
    (hp : p ∈ slabPlaquettes N s r) : p ∈ torusPlaquettes N := by
  obtain ⟨v, hv, hpv⟩ := List.mem_flatMap.mp hp
  obtain ⟨P, _, rfl⟩ := List.mem_map.mp hpv
  exact (mem_torusPlaquettes N v P).mpr (slab_inBox hN hv)

/-- Time translation by `t` carries the slab at `s` onto the slab at `s+t`. -/
theorem slab_timeShift {N s r : Nat} (t : Nat) {v : Z4Vertex}
    (hv : v ∈ slabVertices N s r) : tShift N (t, 0, 0, 0) v ∈ slabVertices N (s + t) r := by
  obtain ⟨⟨j, hj, hja⟩, h2, h3, h4⟩ := (mem_slabVertices N s r v).mp hv
  refine (mem_slabVertices N (s + t) r _).mpr ⟨⟨j, hj, ?_⟩, ?_, ?_, ?_⟩
  · show (v.1 + t) % N = (s + t + j) % N
    rw [hja, Nat.mod_add_mod, Nat.add_right_comm]
  · show (v.2.1 + 0) % N < N
    rw [Nat.add_zero, Nat.mod_eq_of_lt h2]; exact h2
  · show (v.2.2.1 + 0) % N < N
    rw [Nat.add_zero, Nat.mod_eq_of_lt h3]; exact h3
  · show (v.2.2.2 + 0) % N < N
    rw [Nat.add_zero, Nat.mod_eq_of_lt h4]; exact h4

/-! ## 2. Spectral-list algebra (Lemma 3.3 core) -/

/-- `Σ_{i=1}^{K} f i`. -/
def tailSum (f : Nat → Q') : Nat → Q'
  | 0 => 0
  | K + 1 => tailSum f K + f (K + 1)

/-- Excited heat trace `s(u) = Σ_{i=1}^{K} λ_i^u`. -/
def excited (lam : Nat → Q') (K u : Nat) : Q' := tailSum (fun i => lam i ^ u) K

theorem tailSum_nonneg (f : Nat → Q') (hf : ∀ i, (0 : Q') ≤ f i) :
    ∀ K, (0 : Q') ≤ tailSum f K
  | 0 => by show (0 : Q') ≤ (0 : Q'); decide
  | K + 1 => by
      have h := Q'.add_le_add_left (tailSum f K) 0 (f (K + 1)) (hf (K + 1))
      exact Q'.le_trans' _ _ _ (tailSum_nonneg f hf K)
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv (by
          exact poly_identity_of_normal_eq (.var 0) (.add (.var 0) (.const 0)) (by decide)
            (fun _ => tailSum f K))) h)

theorem add_le_add2 {a b c d : Q'} (h1 : a ≤ b) (h2 : c ≤ d) : a + c ≤ b + d :=
  Q'.le_trans' _ _ _ (Q'.add_le_add_right a b c h1) (Q'.add_le_add_left b c d h2)

/-- Termwise two-sided bound: `−M·S ≤ Σ d_i p_i ≤ M·S` for `p_i ≥ 0`, `|d_i| ≤ M`. -/
theorem tail_weighted_bounds (d p : Nat → Q') (M : Q') (hp : ∀ i, (0 : Q') ≤ p i)
    (hd : ∀ i, -M ≤ d i ∧ d i ≤ M) :
    ∀ K, -(M * tailSum p K) ≤ tailSum (fun i => d i * p i) K ∧
      tailSum (fun i => d i * p i) K ≤ M * tailSum p K
  | 0 => by
      constructor
      · show -(M * (0 : Q')) ≤ (0 : Q')
        exact Q'.le_of_eqv (poly_identity_of_normal_eq (.neg (.mul (.var 0) (.const 0)))
          (.const 0) (by decide) (fun _ => M))
      · show (0 : Q') ≤ M * (0 : Q')
        exact Q'.le_of_eqv (poly_identity_of_normal_eq (.const 0)
          (.mul (.var 0) (.const 0)) (by decide) (fun _ => M))
  | K + 1 => by
      obtain ⟨ih1, ih2⟩ := tail_weighted_bounds d p M hp hd K
      have hu := Q'.mul_le_mul_of_nonneg_right _ _ (p (K + 1)) (hd (K + 1)).2 (hp (K + 1))
      have hl := Q'.mul_le_mul_of_nonneg_right _ _ (p (K + 1)) (hd (K + 1)).1 (hp (K + 1))
      constructor
      · show -(M * (tailSum p K + p (K + 1))) ≤
          tailSum (fun i => d i * p i) K + d (K + 1) * p (K + 1)
        have e : (-(M * (tailSum p K + p (K + 1)))).eqv
            (-(M * tailSum p K) + (-M) * p (K + 1)) :=
          poly_identity_of_normal_eq
            (.neg (.mul (.var 0) (.add (.var 1) (.var 2))))
            (.add (.neg (.mul (.var 0) (.var 1))) (.mul (.neg (.var 0)) (.var 2)))
            (by decide) (fun | 0 => M | 1 => tailSum p K | _ => p (K + 1))
        exact Q'.le_trans' _ _ _ (Q'.le_of_eqv e) (add_le_add2 ih1 hl)
      · show tailSum (fun i => d i * p i) K + d (K + 1) * p (K + 1) ≤
          M * (tailSum p K + p (K + 1))
        have e : (M * tailSum p K + M * p (K + 1)).eqv (M * (tailSum p K + p (K + 1))) :=
          poly_identity_of_normal_eq
            (.add (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 2)))
            (.mul (.var 0) (.add (.var 1) (.var 2)))
            (by decide) (fun | 0 => M | 1 => tailSum p K | _ => p (K + 1))
        exact Q'.le_trans' _ _ _ (add_le_add2 ih2 hu) (Q'.le_of_eqv e)

/-- **Analytic input of Lemma 3.3, as explicit named data (REDUCTION).**
`K` excited levels; transfer eigenvalues `λ₀ = 1` (normalised) and `λ_i ≥ 0`;
`d_i = ⟨e_i, A_F e_i⟩` the slab-operator diagonal in the transfer eigenbasis,
bounded by `M = ‖F‖_∞` (from `‖A_F‖ ≤ ‖F‖_∞`); `m = (t−r)/a` free transfer
steps, `n = t/a` total steps, `m + r = n` with `r` the slab thickness; and the
trace-ratio identity `E_tor·Tr Tⁿ = Tr(A_F T^m)`.  The cylinder expectation is
`d₀ = ⟨Ω, A_F Ω⟩`. -/
structure SlabInsertionSpectrum where
  K : Nat
  lam : Nat → Q'
  d : Nat → Q'
  M : Q'
  m : Nat
  r : Nat
  n : Nat
  steps : m + r = n
  lam_nonneg : ∀ i, (0 : Q') ≤ lam i
  M_nonneg : (0 : Q') ≤ M
  d_bound : ∀ i, -M ≤ d i ∧ d i ≤ M
  torusExp : Q'
  trace_ratio : (torusExp * ((1 : Q') + excited lam K n)).eqv
    (d 0 + tailSum (fun i => d i * lam i ^ m) K)

namespace SlabInsertionSpectrum

variable (S : SlabInsertionSpectrum)

def numer : Q' := S.d 0 + tailSum (fun i => S.d i * S.lam i ^ S.m) S.K
def denom : Q' := (1 : Q') + excited S.lam S.K S.n
def bound : Q' := S.M * (excited S.lam S.K S.m + excited S.lam S.K S.n)

theorem excited_nonneg (u : Nat) : (0 : Q') ≤ excited S.lam S.K u :=
  tailSum_nonneg _ (fun i => Q'.pow_nonneg _ (S.lam_nonneg i) u) S.K

theorem bound_nonneg : (0 : Q') ≤ S.bound :=
  Q'.mul_nonneg _ _ S.M_nonneg (Q'.le_trans' _ _ _ (S.excited_nonneg S.m)
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (poly_identity_of_normal_eq (.var 0)
      (.add (.var 0) (.const 0)) (by decide) (fun _ => excited S.lam S.K S.m)))
      (Q'.add_le_add_left _ _ _ (S.excited_nonneg S.n))))

/-- **Numerator error** `−B ≤ Num − d₀·Den ≤ B`, `B = M(s_m + s_n)`. -/
theorem numer_error :
    -S.bound ≤ S.numer + -(S.d 0 * S.denom) ∧ S.numer + -(S.d 0 * S.denom) ≤ S.bound := by
  obtain ⟨t1, t2⟩ := tail_weighted_bounds S.d (fun i => S.lam i ^ S.m) S.M
    (fun i => Q'.pow_nonneg _ (S.lam_nonneg i) S.m) S.d_bound S.K
  have hsn := S.excited_nonneg S.n
  have u1 := Q'.mul_le_mul_of_nonneg_right _ _ (excited S.lam S.K S.n) (S.d_bound 0).2 hsn
  have u2 := Q'.mul_le_mul_of_nonneg_right _ _ (excited S.lam S.K S.n) (S.d_bound 0).1 hsn
  have u1' := Q'.neg_le_neg u1
  have u2' := Q'.neg_le_neg u2
  -- X ≈ T + -(d0·s_n)
  have eX : (S.numer + -(S.d 0 * S.denom)).eqv
      (tailSum (fun i => S.d i * S.lam i ^ S.m) S.K + -(S.d 0 * excited S.lam S.K S.n)) :=
    poly_identity_of_normal_eq
      (.add (.add (.var 0) (.var 1)) (.neg (.mul (.var 0) (.add (.const 1) (.var 2)))))
      (.add (.var 1) (.neg (.mul (.var 0) (.var 2)))) (by decide)
      (fun | 0 => S.d 0 | 1 => tailSum (fun i => S.d i * S.lam i ^ S.m) S.K
           | _ => excited S.lam S.K S.n)
  constructor
  · have e : (-S.bound).eqv (-(S.M * excited S.lam S.K S.m) + -(S.M * excited S.lam S.K S.n)) :=
      poly_identity_of_normal_eq
        (.neg (.mul (.var 0) (.add (.var 1) (.var 2))))
        (.add (.neg (.mul (.var 0) (.var 1))) (.neg (.mul (.var 0) (.var 2)))) (by decide)
        (fun | 0 => S.M | 1 => excited S.lam S.K S.m | _ => excited S.lam S.K S.n)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv e)
      (Q'.le_trans' _ _ _ (add_le_add2 t1 u1') (Q'.le_of_eqv (Q'.eqv_symm eX)))
  · have e : (S.M * excited S.lam S.K S.m + -(-S.M * excited S.lam S.K S.n)).eqv S.bound :=
      poly_identity_of_normal_eq
        (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.neg (.var 0)) (.var 2))))
        (.mul (.var 0) (.add (.var 1) (.var 2))) (by decide)
        (fun | 0 => S.M | 1 => excited S.lam S.K S.m | _ => excited S.lam S.K S.n)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv eX)
      (Q'.le_trans' _ _ _ (add_le_add2 t2 u2') (Q'.le_of_eqv e))

/-- **Bounded slab insertion (PP (3.7), finite form).**
`|E_tor F − E_cyl F| ≤ ‖F‖_∞ (s(t−r) + s(t))`. -/
theorem slab_insertion_bound :
    Q'.abs (S.torusExp + -(S.d 0)) ≤ S.bound := by
  obtain ⟨hX1, hX2⟩ := S.numer_error
  have hB := S.bound_nonneg
  have hDen : (1 : Q') ≤ S.denom :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (poly_identity_of_normal_eq (.const 1)
      (.add (.const 1) (.const 0)) (by decide) (fun _ => (0 : Q'))))
      (Q'.add_le_add_left _ _ _ (S.excited_nonneg S.n))
  -- y·Den ≈ X
  have eY : ((S.torusExp + -(S.d 0)) * S.denom).eqv (S.numer + -(S.d 0 * S.denom)) :=
    Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq
        (.mul (.add (.var 0) (.neg (.var 1))) (.var 2))
        (.add (.mul (.var 0) (.var 2)) (.neg (.mul (.var 1) (.var 2)))) (by decide)
        (fun | 0 => S.torusExp | 1 => S.d 0 | _ => S.denom))
      (Q'.add_eqv_congr_right _ _ _ S.trace_ratio)
  have hz : (-S.bound) ≤ 0 := Q'.le_trans' _ _ _ (Q'.neg_le_neg hB)
    (Q'.le_of_eqv (poly_identity_of_normal_eq (.neg (.const 0)) (.const 0) (by decide)
      (fun _ => (0 : Q'))))
  apply Q'.abs_le
  · rcases Decidable.em ((0 : Q') ≤ S.torusExp + -(S.d 0)) with hy | hy
    · exact Q'.le_trans' _ _ _ hz hy
    · have hw := Q'.neg_nonneg_of_not_nonneg hy
      have h1 := Q'.mul_le_mul_of_nonneg_left _ _ _ hDen hw
      have e1 : (-(S.torusExp + -(S.d 0))).eqv (-(S.torusExp + -(S.d 0)) * 1) :=
        poly_identity_of_normal_eq (.var 0) (.mul (.var 0) (.const 1)) (by decide)
          (fun _ => -(S.torusExp + -(S.d 0)))
      have e2 : (-(S.torusExp + -(S.d 0)) * S.denom).eqv
          (-((S.torusExp + -(S.d 0)) * S.denom)) :=
        poly_identity_of_normal_eq (.mul (.neg (.var 0)) (.var 1)) (.neg (.mul (.var 0) (.var 1)))
          (by decide) (fun | 0 => S.torusExp + -(S.d 0) | _ => S.denom)
      have hnX : -(S.numer + -(S.d 0 * S.denom)) ≤ S.bound :=
        Q'.le_trans' _ _ _ (Q'.neg_le_neg hX1) (Q'.le_of_eqv (Q'.neg_neg_eqv _))
      have hwB : -(S.torusExp + -(S.d 0)) ≤ S.bound :=
        Q'.le_trans' _ _ _ (Q'.le_of_eqv e1) (Q'.le_trans' _ _ _ h1
          (Q'.le_trans' _ _ _ (Q'.le_of_eqv e2)
            (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.neg_eqv_congr _ _ eY)) hnX)))
      exact Q'.le_trans' _ _ _ (Q'.neg_le_neg hwB) (Q'.le_of_eqv (Q'.neg_neg_eqv _))
  · rcases Decidable.em ((0 : Q') ≤ S.torusExp + -(S.d 0)) with hy | hy
    · have h1 := Q'.mul_le_mul_of_nonneg_left _ _ _ hDen hy
      have e1 : (S.torusExp + -(S.d 0)).eqv ((S.torusExp + -(S.d 0)) * 1) :=
        poly_identity_of_normal_eq (.var 0) (.mul (.var 0) (.const 1)) (by decide)
          (fun _ => S.torusExp + -(S.d 0))
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv e1) (Q'.le_trans' _ _ _ h1
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv eY) hX2))
    · exact Q'.le_trans' _ _ _ (Q'.nonpos_of_not_nonneg hy) hB

end SlabInsertionSpectrum

end YMGap.Continuum.TorusSlabInsertion
