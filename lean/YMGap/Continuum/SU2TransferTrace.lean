/-
# Transfer step (2g): Z as a periodic chain of time-shifted kernels (trace form), fixed K, Wilson torus

ADDITIVE.  **Labels:** STRONG COUPLING / Wilson `T_K` track, fixed `K`; also true for U(1), not gap
evidence.

One kernel, as a function of where its variables sit:
`Tker ι = ∫dV_0 [Π_{p∈slicePS 0} T_K^ι(p) · Π_{p∈slicePT 0} T_K^ι(p)]`.  Here `ι` places the link
variables, and the private blocks `V_0` are integrated in place.  Its translate to slice `t` is
`Tker (iota t)`, with `iota t ℓ = idxOf (τ_t ℓ)`.

* `trT N = H(Π_{t<N} Tker (iota t))`: the Haar integral over the remaining (spatial, `U`) blocks of
  the product of the translated copies of the single kernel: a periodic chained-kernel integral
  (trace form).  No operator `T` on a Hilbert or polynomial space is defined here, and no operator
  statement `Tr T^{N_t}` is claimed.
* **`z_eq_trace`** (PROVED): `H(Π_{p∈torus} T_K(p)) ≈ trT N`, i.e. Z as a periodic chain of time-shifted kernels (trace form), given
  `torusLinks N ⊆ links`.

Not claimed: self-adjointness or positivity of `T` (T ≥ 0 is the Realizer's hW, now `torus_rp`), or
any spectral statement.
-/

import YMGap.Continuum.SU2TimeShift

namespace YMGap.Continuum.SU2TransferTrace

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4TorusGeometry
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionBlockLocality
open YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini (integrateQuaternionBlocks)
open YMGap.Continuum.SU2HaarL1Activity (prodPoly)
open YMGap.Continuum.SU2TorusSlice
open YMGap.Continuum.SU2SliceIntegrate
open YMGap.Continuum.SU2SliceOrder (prod_perm torus_prod_slice)
open YMGap.Continuum.SU2WilsonSliceGood
open YMGap.Continuum.SU2TimeShift

local infix:50 " ≈ " => Q'.eqv
local infix:50 " ≅ " => RatPolyCoeffEqv

variable (links : List Z4Link) (N : Nat) (β : Q') (K : Nat)

local notation "F" => YMGap.Continuum.SU2WilsonPolymerIdentity.TK links N β K

/-! ## The single kernel and its trace -/

/-- The transfer kernel with variables placed by `ι`. -/
def Tker (ι : Z4Link → Nat) : RatPoly :=
  integrateQuaternionBlocks ((sliceV N 0).map ι)
    (polyMul (prodPoly (TKi N β K ι) (slicePS N 0)) (prodPoly (TKi N β K ι) (slicePT N 0)))

/-- Variable placement of slice `t`. -/
def iota (t : Nat) : Z4Link → Nat := fun ℓ => links.idxOf (shv N t ℓ)

def polyProd : List RatPoly → RatPoly
  | [] => polyOne
  | p :: ps => polyMul p (polyProd ps)

/-- Trace form: Haar over the `U` blocks of the product of the translated kernels. -/
def trT : Q' := quaternionHaar links.length (polyProd ((List.range N).map fun t => Tker N β K (iota links N t)))

/-! ## Generalised `Good` for slice families -/

def wslG (A B : Nat → List Z4Plaq) (V : Nat → List Z4Link) (ts : List Nat) : List (RatPoly × List Nat) :=
  ts.map fun t => (polyMul (prodPoly F (A t)) (prodPoly F (B t)), (V t).map links.idxOf)

theorem Wg_local (blocks t t' : Nat) (ht : t ≠ t') (A B : List Z4Plaq) (hA : ∀ p ∈ A, p ∈ slicePS N t)
    (hB : ∀ p ∈ B, p ∈ slicePT N t) (ℓ : Z4Link) (hℓ : ℓ ∈ links) (hs : linkSlice ℓ = (t', true)) :
    BlockLocal blocks (· ≠ links.idxOf ℓ) (polyMul (prodPoly F A) (prodPoly F B)) :=
  BlockLocal.mul
    (prod_local _ _ fun p hp => tk_local_of links N β K p ℓ hℓ (not_link N t t' ht ℓ hs p (Or.inl (hA p hp))) blocks)
    (prod_local _ _ fun p hp => tk_local_of links N β K p ℓ hℓ (not_link N t t' ht ℓ hs p (Or.inr (hB p hp))) blocks)

theorem good_gen (hL : ∀ ℓ ∈ torusLinks N, ℓ ∈ links) (A B : Nat → List Z4Plaq) (V : Nat → List Z4Link) :
    ∀ ts : List Nat, ts.Nodup → (∀ t ∈ ts, ∀ p ∈ A t, p ∈ slicePS N t) → (∀ t ∈ ts, ∀ p ∈ B t, p ∈ slicePT N t) →
    (∀ t ∈ ts, ∀ ℓ ∈ V t, ℓ ∈ sliceV N t) → Good links.length (wslG links N β K A B V ts)
  | [], _, _, _, _ => trivial
  | t :: ts, hn, hA, hB, hV => by
    obtain ⟨hnt, hn'⟩ := List.nodup_cons.mp hn
    have hA' := fun s hs => hA s (List.mem_cons_of_mem _ hs)
    have hB' := fun s hs => hB s (List.mem_cons_of_mem _ hs)
    have hV' := fun s hs => hV s (List.mem_cons_of_mem _ hs)
    refine ⟨fun b hb => ?_, local_of_all fun b hb => ?_, fun v hv => ?_, good_gen hL A B V ts hn' hA' hB' hV'⟩
    · obtain ⟨ℓ, hℓ, rfl⟩ := List.mem_map.mp hb
      exact List.idxOf_lt_length_of_mem (hL ℓ (List.mem_filter.mp (hV t List.mem_cons_self ℓ hℓ)).1)
    · have hm : b ∈ allS (wslG links N β K A B V ts) := Decidable.byContradiction hb
      obtain ⟨w, hw, hbw⟩ := List.mem_flatMap.mp hm
      obtain ⟨t', ht', rfl⟩ := List.mem_map.mp hw
      obtain ⟨ℓ, hℓ, rfl⟩ := List.mem_map.mp hbw
      have hv := hV' t' ht' ℓ hℓ
      exact Wg_local links N β K _ t t' (fun e => hnt (e ▸ ht')) _ _ (hA t List.mem_cons_self)
        (hB t List.mem_cons_self) ℓ (hL ℓ (List.mem_filter.mp hv).1) ((mem_sliceV N t' ℓ).mp hv).2
    · obtain ⟨t', ht', rfl⟩ := List.mem_map.mp hv
      refine local_of_all fun b hb => ?_
      have hm : b ∈ (V t).map links.idxOf := Decidable.byContradiction hb
      obtain ⟨ℓ, hℓ, rfl⟩ := List.mem_map.mp hm
      have hv := hV t List.mem_cons_self ℓ hℓ
      exact Wg_local links N β K _ t' t (fun e => hnt (e ▸ ht')) _ _ (hA' t' ht') (hB' t' ht')
        ℓ (hL ℓ (List.mem_filter.mp hv).1) ((mem_sliceV N t ℓ).mp hv).2

/-! ## Assembly -/

def A0 (t : Nat) : List Z4Plaq := (slicePS N 0).map (shv N t)
def B0 (t : Nat) : List Z4Plaq := (slicePT N 0).map (shv N t)
def V0 (t : Nat) : List Z4Link := (sliceV N 0).map (shv N t)

theorem prod_map (G : Z4Plaq → RatPoly) (g : Z4Plaq → Z4Plaq) (H' : Z4Plaq → RatPoly) (h : ∀ p, G (g p) = H' p) :
    ∀ l : List Z4Plaq, prodPoly G (l.map g) = prodPoly H' l
  | [] => rfl
  | p :: l => by
    show polyMul (G (g p)) (prodPoly G (l.map g)) = polyMul (H' p) (prodPoly H' l)
    rw [h p, prod_map G g H' h l]

theorem kint_shift : ∀ ts : List Nat,
    kprod (kint (wslG links N β K (A0 N) (B0 N) (V0 N) ts)) = polyProd (ts.map fun t => Tker N β K (iota links N t))
  | [] => rfl
  | t :: ts => by
    show polyMul (integrateQuaternionBlocks (((sliceV N 0).map (shv N t)).map links.idxOf)
        (polyMul (prodPoly F ((slicePS N 0).map (shv N t))) (prodPoly F ((slicePT N 0).map (shv N t)))))
        (kprod (kint (wslG links N β K (A0 N) (B0 N) (V0 N) ts))) = _
    rw [kint_shift ts, List.map_map, prod_map _ _ _ (tk_shift N β K links t), prod_map _ _ _ (tk_shift N β K links t)]
    rfl

theorem perm_step : ∀ ts : List Nat, (∀ t ∈ ts, t < N) →
    kprod (wsl links N β K ts) ≅ kprod (wslG links N β K (A0 N) (B0 N) (V0 N) ts)
  | [], _ => RatPolyCoeffEqv.refl _
  | t :: ts, h => RatPolyCoeffEqv.mul
      (RatPolyCoeffEqv.mul (prod_perm F (ps_perm N t (h t List.mem_cons_self)))
        (prod_perm F (pt_perm N t (h t List.mem_cons_self))))
      (perm_step ts fun s hs => h s (List.mem_cons_of_mem _ hs))

/-- **Z as a periodic chain of time-shifted kernels (trace form) (PROVED).**  STRONG COUPLING / Wilson `T_K`, fixed `K`; also true for U(1),
not gap evidence. -/
theorem z_eq_trace (hL : ∀ ℓ ∈ torusLinks N, ℓ ∈ links) :
    quaternionHaar links.length (prodPoly F (torusPlaquettes N)) ≈ trT links N β K := by
  have hr : ∀ t ∈ List.range N, t < N := fun t ht => List.mem_range.mp ht
  refine Q'.eqv_trans _ _ _ (SU2CharacterHaarBound.haar_coeff (torus_prod_slice F N) _) ?_
  rw [← kprod_wsl links N β K]
  refine Q'.eqv_trans _ _ _ (SU2CharacterHaarBound.haar_coeff (perm_step links N β K _ hr) _) ?_
  refine Q'.eqv_trans _ _ _ (slice_integrate _ _ (good_gen links N β K hL _ _ _ _ (range_nd N)
    (fun t ht p hp => (ps_perm N t (hr t ht)).mem_iff.mpr hp)
    (fun t ht p hp => (pt_perm N t (hr t ht)).mem_iff.mpr hp)
    (fun t ht ℓ hℓ => (v_perm N t (hr t ht)).mem_iff.mpr hℓ))) ?_
  rw [kint_shift]
  exact Q'.eqv_refl _

end YMGap.Continuum.SU2TransferTrace
