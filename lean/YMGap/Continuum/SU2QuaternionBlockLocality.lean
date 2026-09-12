/-
# Quaternion-block locality of raw polynomial channels

Locality means that every monomial has zero exponents in blocks outside
an explicitly named predicate. Coefficients may be signed, duplicated or
zero. This is finer than merely bounding the total coordinate count.
The laws are syntactic, including arbitrary ordered polynomial products.
No Haar factorization or positivity is assumed.
-/

import YMGap.Continuum.BF4ExactSlabReflectedSquareHaarForm

namespace YMGap.Continuum.SU2QuaternionBlockLocality

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter

def BlockZero (monomial : List Nat) (block : Nat) : Prop :=
  ∀ component, component < 4 → exponentAt monomial (4 * block + component) = 0

def BlockLocal (blocks : Nat) (allowed : Nat → Prop) (p : RatPoly) : Prop :=
  ∀ term, term ∈ p → ∀ block, block < blocks → ¬ allowed block → BlockZero term.1 block

namespace BlockLocal

theorem zero (blocks : Nat) (allowed : Nat → Prop) : BlockLocal blocks allowed polyZero :=
  fun _ h => False.elim (List.not_mem_nil h)

theorem one (blocks : Nat) (allowed : Nat → Prop) : BlockLocal blocks allowed polyOne := by
  intro t ht _ _ _ _ _
  have he := List.mem_singleton.mp ht
  subst t
  exact List.getD_nil

theorem coordinate {blocks : Nat} {allowed : Nat → Prop} (coordinate : Nat)
    (ha : allowed (coordinate / 4)) : BlockLocal blocks allowed (polyVar coordinate) := by
  intro t ht block _ hn component hc
  have he := List.mem_singleton.mp ht
  subst t
  rw [exponentAt_varMono]
  apply if_neg
  intro heq
  have hblock : coordinate / 4 = block := by omega
  exact hn (hblock ▸ ha)

theorem add {blocks : Nat} {allowed : Nat → Prop} {p q : RatPoly}
    (hp : BlockLocal blocks allowed p) (hq : BlockLocal blocks allowed q) :
    BlockLocal blocks allowed (polyAdd p q) := by
  intro t ht
  exact (List.mem_append.mp ht).elim (hp t) (hq t)

theorem neg {blocks : Nat} {allowed : Nat → Prop} {p : RatPoly}
    (hp : BlockLocal blocks allowed p) : BlockLocal blocks allowed (polyNeg p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

theorem smul {blocks : Nat} {allowed : Nat → Prop} {p : RatPoly}
    (hp : BlockLocal blocks allowed p) (a : Q') : BlockLocal blocks allowed (polySmul a p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

theorem mul {blocks : Nat} {allowed : Nat → Prop} {p q : RatPoly}
    (hp : BlockLocal blocks allowed p) (hq : BlockLocal blocks allowed q) :
    BlockLocal blocks allowed (polyMul p q) := by
  intro t ht block hb hn component hc
  obtain ⟨s, hs, h⟩ := List.mem_flatMap.mp ht
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp h
  rw [exponentAt_monoMul, hp s hs block hb hn component hc, hq r hr block hb hn component hc]

theorem character {blocks : Nat} {allowed : Nat → Prop} {p : RatPoly}
    (hp : BlockLocal blocks allowed p) : ∀ spin, BlockLocal blocks allowed (characterPolynomial p spin)
  | 0 => one blocks allowed
  | 1 => hp.smul 2
  | n + 2 => ((hp.smul 2).mul (hp.character (n + 1))).add ((hp.character n).smul (-1))

theorem finiteSum {A : Type} {blocks : Nat} {allowed : Nat → Prop} (f : A → RatPoly) :
    ∀ xs : List A, (∀ a, a ∈ xs → BlockLocal blocks allowed (f a)) →
      BlockLocal blocks allowed (finitePolySum f xs)
  | [], _ => zero blocks allowed
  | a :: xs, h => (h a List.mem_cons_self).add
      (finiteSum f xs (fun b hb => h b (List.mem_cons_of_mem a hb)))

theorem fold {A : Type} {blocks : Nat} {allowed : Nat → Prop} (f : A → RatPoly) :
    ∀ xs : List A, (∀ a, a ∈ xs → BlockLocal blocks allowed (f a)) →
      BlockLocal blocks allowed (xs.foldr (fun a p => polyMul (f a) p) polyOne)
  | [], _ => one blocks allowed
  | a :: xs, h => (h a List.mem_cons_self).mul
      (fold f xs (fun b hb => h b (List.mem_cons_of_mem a hb)))

theorem signSelected {blocks : Nat} {allowed : Nat → Prop} {p : RatPoly}
    (hp : BlockLocal blocks allowed p) (coordinates : Nat) (selected : Nat → Bool) :
    BlockLocal blocks allowed (signSelectedPolynomial coordinates selected p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

/-- Block pullback transports the allowed-block predicate along the SAME
permutation. Bounds are explicit; coefficient signs do not affect locality. -/
theorem reindex {blocks : Nat} {allowed target : Nat → Prop} {p : RatPoly}
    (hp : BlockLocal blocks allowed p) (permutation : QuaternionBlockInvolution blocks)
    (hmap : ∀ b, b < blocks → allowed (permutation.map b) → target b) :
    BlockLocal blocks target (reindexQuaternionPolynomial permutation p) := by
  intro t ht block hb hn component hc
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  rw [exponentAt_reindexQuaternionExponents permutation s.1 (by omega),
    show (4 * block + component) / 4 = block by omega,
    show (4 * block + component) % 4 = component by omega]
  exact hp s hs (permutation.map block) (permutation.map_lt block hb)
    (fun h => hn (hmap block hb h)) component hc

end BlockLocal

end YMGap.Continuum.SU2QuaternionBlockLocality

#print axioms YMGap.Continuum.SU2QuaternionBlockLocality.BlockZero
#print axioms YMGap.Continuum.SU2QuaternionBlockLocality.BlockLocal
#print axioms YMGap.Continuum.SU2QuaternionBlockLocality.BlockLocal.zero
#print axioms YMGap.Continuum.SU2QuaternionBlockLocality.BlockLocal.one
#print axioms YMGap.Continuum.SU2QuaternionBlockLocality.BlockLocal.coordinate
#print axioms YMGap.Continuum.SU2QuaternionBlockLocality.BlockLocal.add
#print axioms YMGap.Continuum.SU2QuaternionBlockLocality.BlockLocal.neg
#print axioms YMGap.Continuum.SU2QuaternionBlockLocality.BlockLocal.smul
#print axioms YMGap.Continuum.SU2QuaternionBlockLocality.BlockLocal.mul
#print axioms YMGap.Continuum.SU2QuaternionBlockLocality.BlockLocal.character
#print axioms YMGap.Continuum.SU2QuaternionBlockLocality.BlockLocal.finiteSum
#print axioms YMGap.Continuum.SU2QuaternionBlockLocality.BlockLocal.fold
#print axioms YMGap.Continuum.SU2QuaternionBlockLocality.BlockLocal.signSelected
#print axioms YMGap.Continuum.SU2QuaternionBlockLocality.BlockLocal.reindex
