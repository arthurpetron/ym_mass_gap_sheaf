/-
# R1 commit 7: geometry of the link-compatibility gas on the torus box

ADDITIVE.  **GROUP-BLIND PLUMBING.**  Plaquettes are `Z4Plaq` inside the `N`-box (`torusPlaquettes N`).
* `plaqLinks_mem`: `plaqLinks N p` and `torusEdgesOf N p` are the same 4 links.
* `adj_symm`, `incL_symm`.
* `nb N p := (plaqLinks N p).flatMap (incidentPlaqs N)`, length 24.  `mem_nb`: a box plaquette
  sharing a link with `p` is in `nb N p`.  No box hypothesis on `p` is needed.
* `adjT`: in the box, `adj` gives `(torusLattice N).Adjacent`.
* `Grow`: grown by adding plaquettes that touch the current cluster.  `grow_conn`: a grown
  cluster in the box is `connectedIn` in `torusChain N`.
-/

import YMGap.Continuum.SU2PolymerIdentity
import YMGap.Continuum.Z4PlaqMetric

namespace YMGap.Continuum.SU2LinkGasGeometry

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4TorusGeometry
open YMGap.Continuum.Z4TorusPolymerKP
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.SU2PlaqSupport (plaqLinks)
open YMGap.Continuum.SU2ClusterExplore (adj touch)
open YMGap.Continuum.SU2PolymerIdentity (incL touch_of_mem)

variable (N : Nat)

theorem plaqLinks_mem (p : Z4Plaq) (ℓ : Z4Link) : ℓ ∈ plaqLinks N p ↔ ℓ ∈ torusEdgesOf N p := by
  simp only [plaqLinks, torusEdgesOf, List.mem_cons, List.mem_nil_iff, or_false]
  constructor
  · rintro (h | h | h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr h))
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inl h)
  · rintro (h | h | h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr h))
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inl h)

theorem adj_iff (p q : Z4Plaq) :
    adj N p q = true ↔ ∃ ℓ, ℓ ∈ plaqLinks N p ∧ ℓ ∈ plaqLinks N q := by
  constructor
  · intro h
    obtain ⟨ℓ, hℓ, h2⟩ := List.any_eq_true.mp h
    obtain ⟨ℓ', hℓ', e⟩ := List.any_eq_true.mp h2
    exact ⟨ℓ, hℓ, (of_decide_eq_true e) ▸ hℓ'⟩
  · rintro ⟨ℓ, hp, hq⟩
    exact List.any_eq_true.mpr ⟨ℓ, hp, List.any_eq_true.mpr ⟨ℓ, hq, decide_eq_true rfl⟩⟩

theorem adj_symm (p q : Z4Plaq) : adj N p q = adj N q p := by
  cases h : adj N q p with
  | true =>
    obtain ⟨ℓ, h1, h2⟩ := (adj_iff N q p).mp h
    exact (adj_iff N p q).mpr ⟨ℓ, h2, h1⟩
  | false =>
    cases h' : adj N p q with
    | false => rfl
    | true =>
      obtain ⟨ℓ, h1, h2⟩ := (adj_iff N p q).mp h'
      rw [(adj_iff N q p).mpr ⟨ℓ, h2, h1⟩] at h; exact absurd h (by decide)

theorem incL_iff (A B : List Z4Plaq) :
    incL N A B = true ↔ ∃ a, a ∈ A ∧ ∃ b, b ∈ B ∧ adj N a b = true := by
  constructor
  · intro h
    obtain ⟨b, hb, h2⟩ := List.any_eq_true.mp h
    obtain ⟨a, ha, h3⟩ := List.any_eq_true.mp h2
    exact ⟨a, ha, b, hb, h3⟩
  · rintro ⟨a, ha, b, hb, h⟩
    exact List.any_eq_true.mpr ⟨b, hb, List.any_eq_true.mpr ⟨a, ha, h⟩⟩

theorem incL_symm (A B : List Z4Plaq) : incL N A B = incL N B A := by
  cases h : incL N B A with
  | true =>
    obtain ⟨b, hb, a, ha, e⟩ := (incL_iff N B A).mp h
    exact (incL_iff N A B).mpr ⟨a, ha, b, hb, by rw [adj_symm]; exact e⟩
  | false =>
    cases h' : incL N A B with
    | false => rfl
    | true =>
      obtain ⟨a, ha, b, hb, e⟩ := (incL_iff N A B).mp h'
      rw [(incL_iff N B A).mpr ⟨b, hb, a, ha, by rw [adj_symm]; exact e⟩] at h
      exact absurd h (by decide)

/-- The 24 (with repetition) plaquettes sharing a link with `p`. -/
def nb (p : Z4Plaq) : List Z4Plaq := (plaqLinks N p).flatMap (incidentPlaqs N)

theorem nb_length (p : Z4Plaq) : (nb N p).length = 24 := by
  unfold nb plaqLinks
  simp only [List.flatMap_cons, List.flatMap_nil, List.length_append, incidentPlaqs_length,
    List.append_nil]

theorem mem_nb {p q : Z4Plaq} (hq : q ∈ torusPlaquettes N) (h : adj N p q = true) :
    q ∈ nb N p := by
  obtain ⟨ℓ, hp, hq'⟩ := (adj_iff N p q).mp h
  obtain ⟨v, μ⟩ := ℓ
  exact List.mem_flatMap.mpr ⟨(v, μ), hp, filter_sub_incident q
    (List.mem_filter.mpr ⟨hq, decide_eq_true ((plaqLinks_mem N q _).mp hq')⟩)⟩

theorem inBoxB_of_mem {p : Z4Plaq} (hp : p ∈ torusPlaquettes N) : inBoxB N p.1 = true := by
  obtain ⟨v, P⟩ := p
  obtain ⟨h1, h2, h3, h4⟩ := (mem_torusPlaquettes N v P).mp hp
  unfold inBoxB
  rw [decide_eq_true h1, decide_eq_true h2, decide_eq_true h3, decide_eq_true h4]; rfl

theorem adjT {p q : Z4Plaq} (hp : p ∈ torusPlaquettes N) (hq : q ∈ torusPlaquettes N)
    (h : adj N p q = true) : Nonempty ((torusLattice N).Adjacent p q) := by
  obtain ⟨ℓ, h1, h2⟩ := (adj_iff N p q).mp h
  have b : ∀ r, r ∈ torusPlaquettes N → ℓ ∈ plaqLinks N r → torusBoundary N r ℓ = true :=
    fun r hr hl => by
      unfold torusBoundary
      rw [inBoxB_of_mem N hr, decide_eq_true ((plaqLinks_mem N r ℓ).mp hl)]; rfl
  exact ⟨⟨ℓ, b p hp h1, b q hq h2⟩⟩

/-! ## Chains -/

abbrev TL := torusLattice N

def cmono {X Y : List Z4Plaq} (h : ∀ x, x ∈ X → x ∈ Y) :
    {a b : Z4Plaq} → ChainIn (TL N) X a b → ChainIn (TL N) Y a b
  | _, _, .refl a => .refl a
  | _, _, .step e hr rest => .step e (h _ hr) (cmono h rest)

def ctrans {X : List Z4Plaq} : {a b c : Z4Plaq} → ChainIn (TL N) X a b → ChainIn (TL N) X b c →
    ChainIn (TL N) X a c
  | _, _, _, .refl _, k => k
  | _, _, _, .step e hr rest, k => .step e hr (ctrans rest k)

def asymm {a b : Z4Plaq} (e : (TL N).Adjacent a b) : (TL N).Adjacent b a := ⟨e.link, e.on_q, e.on_p⟩

def crev {X : List Z4Plaq} : {a b : Z4Plaq} → ChainIn (TL N) X a b → a ∈ X → ChainIn (TL N) X b a
  | _, _, .refl a, _ => .refl a
  | _, _, .step e hr rest, ha => ctrans N (crev rest hr) (.step (asymm N e) ha (.refl _))

/-- Clusters grown by successively adding a touching plaquette. -/
inductive Grow : List Z4Plaq → Prop
  | one (r : Z4Plaq) : Grow [r]
  | add (q : Z4Plaq) (B : List Z4Plaq) : Grow B → touch N B q = true → Grow (q :: B)

theorem grow_conn : ∀ X : List Z4Plaq, Grow N X → (∀ p, p ∈ X → p ∈ torusPlaquettes N) →
    Nonempty (connectedIn (L := TL N) X)
  | _, .one r, _ => ⟨connectedIn_singleton (L := TL N) r⟩
  | _, .add q B hB ht, hX => by
    obtain ⟨cB⟩ := grow_conn B hB (fun p hp => hX p (List.mem_cons_of_mem _ hp))
    obtain ⟨b, hb, hab⟩ := List.any_eq_true.mp ht
    obtain ⟨e⟩ := adjT N (hX b (List.mem_cons_of_mem _ hb)) (hX q List.mem_cons_self) hab
    have sub : ∀ x, x ∈ B → x ∈ q :: B := fun x hx => List.mem_cons_of_mem _ hx
    -- chain from any member to `b`
    let toB : (p : Z4Plaq) → p ∈ q :: B → ChainIn (TL N) (q :: B) p b := fun p hp =>
      if h : p = q then by subst h; exact .step (asymm N e) (sub b hb) (ChainIn.refl (L := TL N) (X := p :: B) b)
      else cmono N sub (cB p b ((List.mem_cons.mp hp).resolve_left h) hb)
    exact ⟨fun p p' hp hp' => ctrans N (toB p hp) (crev N (toB p' hp') hp')⟩

end YMGap.Continuum.SU2LinkGasGeometry
