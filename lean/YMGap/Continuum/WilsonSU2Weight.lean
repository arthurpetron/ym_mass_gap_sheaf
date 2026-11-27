/-
# P1: the literal SU(2) Wilson plaquette energy on the rational unit-quaternion carrier

**Label: Wilson lattice scaffolding; also true for U(1); not gap evidence. No chart-closure claim.**
Additive. Constructive and intuitionistic: no `Classical`, no excluded middle beyond decidable
equality of `Dir4`; axioms within `propext`, `Quot.sound`.

Carrier: `RationalQuaternion.UnitNorm.group` (rational points of S³ ⊂ ℍ, i.e. of SU(2)). Gauge configurations
and holonomies come from `TorusWilsonAction` (`U_p = U(w,a)·U(w+â,b)·U(w+b̂,a)⁻¹·U(w,b)⁻¹`).

* `plaqWeight g = 1 − Re g`. For `g ∈ SU(2)`, `Re g = ½ Re tr g`, so this is `1 − ½ Re tr U_p`, OpenAI's
  `wilsonEnergy` summand for `n + 1 = 2`.
* `wilsonPlaqEnergy`, `wilsonEnergy N U = Σ_{p ∈ torusPlaquettes N} (1 − Re U_p)`.
* `wilsonPlaqEnergy_gauge` / `wilsonEnergy_gauge`: invariance under every vertex gauge transformation
  `U(v,μ) ↦ g(v)·U(v,μ)·g(v+μ̂)⁻¹`. Proof: explicit word cancellation with `ḡg ≈ 1`, plus cyclicity of `Re`.
* `wilsonEnergy_shift`: invariance under every periodic translation (from `wilsonAction_shift_invariant`).
* `wilsonEnergy_axisFlip`: invariance under the link-midpoint reflection `x_d ↦ 1 − x_d (mod 2M)` of any axis `d`
  on the `2M` torus. Links along `d` are reversed (`U ↦ U⁻¹`).
* `wilsonEnergy_timeMirror`: the case `d = x0`, which is the repo's RP reflection Θ (`flipV_x0 = rv`).
  Deviation from OpenAI: their `timeMirrorLinks` is the site-centred mirror `t ↦ −t`; ours is link-centred
  `t ↦ 1 − t`. The two differ by a unit time translation, and `wilsonEnergy_shift` covers translations.
-/

import YMGap.Continuum.TorusWilsonAction
import YMGap.RepTheory.RationalQuaternionUnitNormGroup
import YMGap.Continuum.SU2TorusRPThetaTime

namespace YMGap.Continuum.WilsonSU2Weight

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4TorusGeometry
open YMGap.Continuum.TorusWilsonAction
open YMGap.Continuum.SU2TorusRPGeom (rt rv rt_lt rt_invol)
open YMGap.Continuum.SU2TorusRPThetaTime (rt_shift)
open YMGap.RepTheory
open YMGap.RepTheory.RationalQuaternion
  (mul conj one mul_assoc mul_congr conj_conj conj_mul one_mul mul_one UnitNorm)

local infix:50 " ≈ " => Q'.eqv

/-- Raw rational quaternions. -/
abbrev RQ := RationalQuaternion

local infix:50 " ≃ " => RationalQuaternion.Equivalent

/-- The SU(2) carrier as a constructive group. -/
abbrev SU2Q : ConstructiveGroup := RationalQuaternion.UnitNorm.group

/-! ## 1. Quaternion word lemmas -/

theorem E_refl (x : RQ) : x ≃ x := RationalQuaternion.semanticSetoid.iseqv.refl x
theorem E_symm {x y : RQ} (h : x ≃ y) : y ≃ x := RationalQuaternion.semanticSetoid.iseqv.symm h
theorem E_trans {x y z : RQ} (h1 : x ≃ y) (h2 : y ≃ z) : x ≃ z :=
  RationalQuaternion.semanticSetoid.iseqv.trans h1 h2

/-- `Re(xy) = Re(yx)` (reflected ring normaliser). -/
theorem re_cyc (x y : RQ) : (mul x y).r ≈ (mul y x).r :=
  poly_identity_of_normal_eq
    (.add (.add (.mul (.var 0) (.var 4)) (.neg (.mul (.var 1) (.var 5))))
      (.add (.neg (.mul (.var 2) (.var 6))) (.neg (.mul (.var 3) (.var 7)))))
    (.add (.add (.mul (.var 4) (.var 0)) (.neg (.mul (.var 5) (.var 1))))
      (.add (.neg (.mul (.var 6) (.var 2))) (.neg (.mul (.var 7) (.var 3)))))
    (by decide)
    (fun | 0 => x.r | 1 => x.i | 2 => x.j | 3 => x.k | 4 => y.r | 5 => y.i | 6 => y.j | _ => y.k)

/-- Reversed plaquette word, reflected axis is the plaquette's first direction. -/
theorem re_caseA (u1 u2 u3 u4 : RQ) :
    (mul (mul (conj u1) u2) (mul (conj (conj u3)) (conj u4))).r ≈
      (mul (mul u1 u4) (mul (conj u3) (conj u2))).r := by
  have h1 : mul (mul (conj u1) u2) (mul (conj (conj u3)) (conj u4)) ≃
      mul (conj u1) (mul u2 (mul u3 (conj u4))) :=
    E_trans (mul_congr (E_refl _) (mul_congr (conj_conj u3) (E_refl _))) (mul_assoc _ _ _)
  have h2 : mul (mul u2 (mul u3 (conj u4))) (conj u1) ≃ mul (mul u2 u3) (mul (conj u4) (conj u1)) :=
    E_trans (mul_assoc _ _ _) (E_trans (mul_congr (E_refl _) (mul_assoc _ _ _)) (E_symm (mul_assoc _ _ _)))
  have hR : conj (mul (mul u1 u4) (mul (conj u3) (conj u2))) ≃
      mul (mul u2 u3) (mul (conj u4) (conj u1)) :=
    E_trans (conj_mul _ _)
      (mul_congr (E_trans (conj_mul _ _) (mul_congr (conj_conj _) (conj_conj _))) (conj_mul _ _))
  exact Q'.eqv_trans _ _ _ h1.1
    (Q'.eqv_trans _ _ _ (re_cyc _ _) (Q'.eqv_trans _ _ _ h2.1 (Q'.eqv_symm hR.1)))

/-- Reversed plaquette word, reflected axis is the plaquette's second direction. -/
theorem re_caseB (X Y Z W : RQ) :
    (mul (mul X (conj Y)) (mul (conj Z) (conj (conj W)))).r ≈
      (mul (mul Z Y) (mul (conj X) (conj W))).r := by
  have h1 : mul (mul X (conj Y)) (mul (conj Z) (conj (conj W))) ≃
      mul (mul (mul X (conj Y)) (conj Z)) W :=
    E_trans (mul_congr (E_refl _) (mul_congr (E_refl _) (conj_conj W))) (E_symm (mul_assoc _ _ _))
  have h2 : mul W (mul (mul X (conj Y)) (conj Z)) ≃ mul (mul W X) (mul (conj Y) (conj Z)) :=
    E_trans (mul_congr (E_refl _) (mul_assoc _ _ _)) (E_symm (mul_assoc _ _ _))
  have hR : conj (mul (mul Z Y) (mul (conj X) (conj W))) ≃ mul (mul W X) (mul (conj Y) (conj Z)) :=
    E_trans (conj_mul _ _)
      (mul_congr (E_trans (conj_mul _ _) (mul_congr (conj_conj _) (conj_conj _))) (conj_mul _ _))
  exact Q'.eqv_trans _ _ _ h1.1
    (Q'.eqv_trans _ _ _ (re_cyc _ _) (Q'.eqv_trans _ _ _ h2.1 (Q'.eqv_symm hR.1)))

/-- Right-nested product of a word. -/
def pr : List RQ → RQ
  | [] => one
  | x :: l => mul x (pr l)

theorem pr_app : ∀ (l1 l2 : List RQ), pr (l1 ++ l2) ≃ mul (pr l1) (pr l2)
  | [], l2 => E_symm (one_mul (pr l2))
  | x :: l1, l2 => E_trans (mul_congr (E_refl x) (pr_app l1 l2)) (E_symm (mul_assoc _ _ _))

/-- Cancel an adjacent `ḡ·g` (unit `g`). -/
theorem pr_cancel (l1 l2 : List RQ) (u : UnitNorm) :
    pr (l1 ++ conj u.val :: u.val :: l2) ≃ pr (l1 ++ l2) := by
  have h : pr (conj u.val :: u.val :: l2) ≃ pr l2 :=
    E_trans (E_symm (mul_assoc _ _ _))
      (E_trans (mul_congr (RationalQuaternion.UnitNorm.inv_mul u) (E_refl _)) (one_mul _))
  exact E_trans (pr_app _ _) (E_trans (mul_congr (E_refl _) h) (E_symm (pr_app _ _)))

theorem pr1 (x : RQ) : pr [x] ≃ x := mul_one x

theorem pr3 (x y z : RQ) : pr [x, y, z] ≃ mul (mul x y) z :=
  E_trans (mul_congr (E_refl x) (mul_congr (E_refl y) (mul_one z))) (E_symm (mul_assoc _ _ _))

theorem pr3' (x y z : RQ) : pr [x, y, z] ≃ mul x (mul y z) :=
  mul_congr (E_refl x) (mul_congr (E_refl y) (mul_one z))

theorem pr4 (a b c d : RQ) : pr [a, b, c, d] ≃ mul (mul a b) (mul c d) :=
  E_trans (pr_app [a, b] [c, d])
    (mul_congr (mul_congr (E_refl a) (mul_one b)) (mul_congr (E_refl c) (mul_one d)))

/-- The gauge-transformed plaquette word has the same real part. -/
theorem gauge_word (g0 g1 g2 g3 : UnitNorm) (a b c d : RQ) :
    (mul (mul (mul (mul g0.val a) (conj g1.val)) (mul (mul g1.val b) (conj g2.val)))
      (mul (conj (mul (mul g3.val c) (conj g2.val))) (conj (mul (mul g0.val d) (conj g3.val))))).r ≈
    (mul (mul a b) (mul (conj c) (conj d))).r := by
  have hA := E_symm (pr3 g0.val a (conj g1.val))
  have hB := E_symm (pr3 g1.val b (conj g2.val))
  have hC : conj (mul (mul g3.val c) (conj g2.val)) ≃ pr [g2.val, conj c, conj g3.val] :=
    E_trans (conj_mul _ _) (E_trans (mul_congr (conj_conj _) (conj_mul _ _)) (E_symm (pr3' _ _ _)))
  have hD : conj (mul (mul g0.val d) (conj g3.val)) ≃ pr [g3.val, conj d, conj g0.val] :=
    E_trans (conj_mul _ _) (E_trans (mul_congr (conj_conj _) (conj_mul _ _)) (E_symm (pr3' _ _ _)))
  have hAB := E_trans (mul_congr hA hB) (E_symm (pr_app [g0.val, a, conj g1.val] [g1.val, b, conj g2.val]))
  have hCD := E_trans (mul_congr hC hD)
    (E_symm (pr_app [g2.val, conj c, conj g3.val] [g3.val, conj d, conj g0.val]))
  have hall := E_trans (mul_congr hAB hCD)
    (E_symm (pr_app [g0.val, a, conj g1.val, g1.val, b, conj g2.val]
      [g2.val, conj c, conj g3.val, g3.val, conj d, conj g0.val]))
  have c1 := pr_cancel [g0.val, a] [b, conj g2.val, g2.val, conj c, conj g3.val, g3.val, conj d, conj g0.val] g1
  have c2 := pr_cancel [g0.val, a, b] [conj c, conj g3.val, g3.val, conj d, conj g0.val] g2
  have c3 := pr_cancel [g0.val, a, b, conj c] [conj d, conj g0.val] g3
  have hw : mul (mul (mul (mul g0.val a) (conj g1.val)) (mul (mul g1.val b) (conj g2.val)))
      (mul (conj (mul (mul g3.val c) (conj g2.val))) (conj (mul (mul g0.val d) (conj g3.val)))) ≃
      mul g0.val (pr [a, b, conj c, conj d, conj g0.val]) :=
    E_trans hall (E_trans c1 (E_trans c2 c3))
  have hz : mul (pr [a, b, conj c, conj d, conj g0.val]) g0.val ≃ mul (mul a b) (mul (conj c) (conj d)) :=
    E_trans (mul_congr (E_refl _) (E_symm (pr1 g0.val)))
      (E_trans (E_symm (pr_app [a, b, conj c, conj d, conj g0.val] [g0.val]))
        (E_trans (pr_cancel [a, b, conj c, conj d] [] g0) (pr4 _ _ _ _)))
  exact Q'.eqv_trans _ _ _ hw.1 (Q'.eqv_trans _ _ _ (re_cyc _ _) hz.1)

/-! ## 2. The Wilson weight and energy -/

/-- `1 − Re g = 1 − ½ Re tr g` on SU(2). -/
def plaqWeight (g : UnitNorm) : Q' := 1 - g.val.r

theorem plaqWeight_congr {g h : UnitNorm} (e : g.val.r ≈ h.val.r) : plaqWeight g ≈ plaqWeight h :=
  Q'.add_eqv_congr_left 1 (-g.val.r) (-h.val.r) (Q'.neg_eqv_congr _ _ e)

/-- Wilson plaquette energy `1 − ½ Re tr U_p`. -/
def wilsonPlaqEnergy (N : Nat) (U : GaugeConfig SU2Q) (p : Z4Plaq) : Q' :=
  plaqWeight (holonomy SU2Q N U p)

/-- Wilson energy `Σ_p (1 − ½ Re tr U_p)` over the torus plaquettes. -/
def wilsonEnergy (N : Nat) (U : GaugeConfig SU2Q) : Q' := wilsonAction SU2Q N plaqWeight U

theorem wilsonEnergy_eq (N : Nat) (U : GaugeConfig SU2Q) :
    wilsonEnergy N U = qsum ((torusPlaquettes N).map (wilsonPlaqEnergy N U)) := rfl

theorem qsum_map_congr {α : Type} (f g : α → Q') :
    ∀ (l : List α), (∀ x, x ∈ l → f x ≈ g x) → qsum (l.map f) ≈ qsum (l.map g)
  | [], _ => Q'.eqv_refl _
  | x :: l, h =>
      Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ (h x List.mem_cons_self))
        (Q'.add_eqv_congr_left _ _ _
          (qsum_map_congr f g l fun y hy => h y (List.mem_cons_of_mem _ hy)))

/-! ## 3. Gauge invariance -/

/-- Vertex gauge transformation `U(v,μ) ↦ g(v)·U(v,μ)·g(v+μ̂)⁻¹`. -/
def gaugeAct (N : Nat) (g : Z4Vertex → UnitNorm) (U : GaugeConfig SU2Q) : GaugeConfig SU2Q :=
  fun ℓ => UnitNorm.mul (UnitNorm.mul (g ℓ.1) (U ℓ)) (UnitNorm.inv (g (tAdd N ℓ.1 ℓ.2)))

theorem tAdd_comm_ne (N : Nat) (v : Z4Vertex) {μ ν : Dir4} (h : μ ≠ ν) :
    tAdd N (tAdd N v μ) ν = tAdd N (tAdd N v ν) μ := by
  obtain ⟨a, b, c, e⟩ := v
  cases μ <;> cases ν <;> first | rfl | exact absurd rfl h

theorem dirsOf_ne (P : Z4Plane) : (dirsOf P).1 ≠ (dirsOf P).2 := by cases P <;> decide

theorem gauge_word' (g0 g1 g2 g2' g3 : UnitNorm) (e : g2' = g2) (a b c d : RQ) :
    (mul (mul (mul (mul g0.val a) (conj g1.val)) (mul (mul g1.val b) (conj g2.val)))
      (mul (conj (mul (mul g3.val c) (conj g2'.val))) (conj (mul (mul g0.val d) (conj g3.val))))).r ≈
    (mul (mul a b) (mul (conj c) (conj d))).r := by
  subst e; exact gauge_word g0 g1 g2' g3 a b c d

/-- **Gauge invariance of the plaquette energy** (every plaquette, every `N`). -/
theorem wilsonPlaqEnergy_gauge (N : Nat) (g : Z4Vertex → UnitNorm) (U : GaugeConfig SU2Q) (p : Z4Plaq) :
    wilsonPlaqEnergy N (gaugeAct N g U) p ≈ wilsonPlaqEnergy N U p := by
  obtain ⟨w, P⟩ := p
  exact plaqWeight_congr (gauge_word' (g w) (g (tAdd N w (dirsOf P).1))
    (g (tAdd N (tAdd N w (dirsOf P).1) (dirsOf P).2)) (g (tAdd N (tAdd N w (dirsOf P).2) (dirsOf P).1))
    (g (tAdd N w (dirsOf P).2))
    (congrArg g (tAdd_comm_ne N w (dirsOf_ne P)).symm)
    (U (w, (dirsOf P).1)).val (U (tAdd N w (dirsOf P).1, (dirsOf P).2)).val
    (U (tAdd N w (dirsOf P).2, (dirsOf P).1)).val (U (w, (dirsOf P).2)).val)

/-- **Gauge invariance of the Wilson energy.** -/
theorem wilsonEnergy_gauge (N : Nat) (g : Z4Vertex → UnitNorm) (U : GaugeConfig SU2Q) :
    wilsonEnergy N (gaugeAct N g U) ≈ wilsonEnergy N U :=
  qsum_map_congr _ _ (torusPlaquettes N) fun p _ => wilsonPlaqEnergy_gauge N g U p

/-! ## 4. Translation invariance -/

/-- **Translation invariance** (`N ≥ 1`, every periodic translation `t`). -/
theorem wilsonEnergy_shift {N : Nat} (hN : 0 < N) (t : Z4Vertex) (U : GaugeConfig SU2Q) :
    wilsonEnergy N (shiftConfig SU2Q N t U) ≈ wilsonEnergy N U :=
  wilsonAction_shift_invariant SU2Q hN plaqWeight t U

/-! ## 5. Link-midpoint axis reflections on the `2M` torus -/

/-- Reflect coordinate `d`: `x_d ↦ 1 − x_d (mod 2M)`. -/
def flipV (M : Nat) : Dir4 → Z4Vertex → Z4Vertex
  | .x0, (a, b, c, e) => (rt M a, b, c, e)
  | .x1, (a, b, c, e) => (a, rt M b, c, e)
  | .x2, (a, b, c, e) => (a, b, rt M c, e)
  | .x3, (a, b, c, e) => (a, b, c, rt M e)

/-- The time case is the repo's RP reflection `rv`. -/
theorem flipV_x0 (M : Nat) (v : Z4Vertex) : flipV M .x0 v = rv M v := by
  obtain ⟨a, b, c, e⟩ := v; rfl

/-- Reflected configuration: links along `d` are reversed. -/
def flipConfig (M : Nat) (d : Dir4) (U : GaugeConfig SU2Q) : GaugeConfig SU2Q :=
  fun ℓ => if ℓ.2 = d then UnitNorm.inv (U (flipV M d (tAdd (2 * M) ℓ.1 d), d)) else U (flipV M d ℓ.1, ℓ.2)

/-- Reflected plaquette. -/
def flipPlaq (M : Nat) (d : Dir4) (p : Z4Plaq) : Z4Plaq :=
  if (dirsOf p.2).1 = d ∨ (dirsOf p.2).2 = d then (flipV M d (tAdd (2 * M) p.1 d), p.2)
  else (flipV M d p.1, p.2)

theorem flipConfig_same (M : Nat) (d : Dir4) (U : GaugeConfig SU2Q) (v : Z4Vertex) :
    flipConfig M d U (v, d) = UnitNorm.inv (U (flipV M d (tAdd (2 * M) v d), d)) := if_pos rfl

theorem flipConfig_other (M : Nat) (d : Dir4) (U : GaugeConfig SU2Q) (v : Z4Vertex) {μ : Dir4}
    (h : μ ≠ d) : flipConfig M d U (v, μ) = U (flipV M d v, μ) := if_neg h

theorem flipPlaq_in (M : Nat) (d : Dir4) (w : Z4Vertex) (P : Z4Plane)
    (h : (dirsOf P).1 = d ∨ (dirsOf P).2 = d) :
    flipPlaq M d (w, P) = (flipV M d (tAdd (2 * M) w d), P) := if_pos h

theorem flipPlaq_out (M : Nat) (d : Dir4) (w : Z4Vertex) (P : Z4Plane)
    (h : ¬ ((dirsOf P).1 = d ∨ (dirsOf P).2 = d)) :
    flipPlaq M d (w, P) = (flipV M d w, P) := if_neg h

section Geometry

variable {M : Nat} (hM : 1 ≤ M)
include hM

theorem flipV_box (d : Dir4) {v : Z4Vertex} (hv : InBox (2 * M) v) : InBox (2 * M) (flipV M d v) := by
  obtain ⟨a, b, c, e⟩ := v
  obtain ⟨h1, h2, h3, h4⟩ := hv
  cases d
  · exact ⟨rt_lt hM h1, h2, h3, h4⟩
  · exact ⟨h1, rt_lt hM h2, h3, h4⟩
  · exact ⟨h1, h2, rt_lt hM h3, h4⟩
  · exact ⟨h1, h2, h3, rt_lt hM h4⟩

theorem flipV_invol (d : Dir4) {v : Z4Vertex} (hv : InBox (2 * M) v) : flipV M d (flipV M d v) = v := by
  obtain ⟨a, b, c, e⟩ := v
  obtain ⟨h1, h2, h3, h4⟩ := hv
  cases d
  · show (rt M (rt M a), b, c, e) = (a, b, c, e); rw [rt_invol hM h1]
  · show (a, rt M (rt M b), c, e) = (a, b, c, e); rw [rt_invol hM h2]
  · show (a, b, rt M (rt M c), e) = (a, b, c, e); rw [rt_invol hM h3]
  · show (a, b, c, rt M (rt M e)) = (a, b, c, e); rw [rt_invol hM h4]

/-- `Θ_d v = Θ_d(v + d̂) + d̂`. -/
theorem flipV_shift (d : Dir4) {v : Z4Vertex} (hv : InBox (2 * M) v) :
    flipV M d v = tAdd (2 * M) (flipV M d (tAdd (2 * M) v d)) d := by
  obtain ⟨a, b, c, e⟩ := v
  obtain ⟨h1, h2, h3, h4⟩ := hv
  cases d
  · show (rt M a, b, c, e) = (wrapSucc (2 * M) (rt M (wrapSucc (2 * M) a)), b, c, e)
    rw [← rt_shift hM h1]
  · show (a, rt M b, c, e) = (a, wrapSucc (2 * M) (rt M (wrapSucc (2 * M) b)), c, e)
    rw [← rt_shift hM h2]
  · show (a, b, rt M c, e) = (a, b, wrapSucc (2 * M) (rt M (wrapSucc (2 * M) c)), e)
    rw [← rt_shift hM h3]
  · show (a, b, c, rt M e) = (a, b, c, wrapSucc (2 * M) (rt M (wrapSucc (2 * M) e)))
    rw [← rt_shift hM h4]

omit hM in
theorem flipV_tAdd_ne (d : Dir4) (v : Z4Vertex) {μ : Dir4} (h : μ ≠ d) :
    flipV M d (tAdd (2 * M) v μ) = tAdd (2 * M) (flipV M d v) μ := by
  obtain ⟨a, b, c, e⟩ := v
  cases d <;> cases μ <;> first | rfl | exact absurd rfl h

theorem flipPlaq_invol (d : Dir4) (p : Z4Plaq) (hp : InBox (2 * M) p.1) : flipPlaq M d (flipPlaq M d p) = p := by
  obtain ⟨w, P⟩ := p
  by_cases h : (dirsOf P).1 = d ∨ (dirsOf P).2 = d
  · rw [flipPlaq_in M d w P h, flipPlaq_in M d _ P h]
    show (flipV M d (tAdd (2 * M) (flipV M d (tAdd (2 * M) w d)) d), P) = (w, P)
    rw [← flipV_shift hM d hp, flipV_invol hM d hp]
  · rw [flipPlaq_out M d w P h, flipPlaq_out M d _ P h, flipV_invol hM d hp]

theorem flipPlaq_box (d : Dir4) (p : Z4Plaq) (hp : InBox (2 * M) p.1) : InBox (2 * M) (flipPlaq M d p).1 := by
  obtain ⟨w, P⟩ := p
  by_cases h : (dirsOf P).1 = d ∨ (dirsOf P).2 = d
  · rw [flipPlaq_in M d w P h]
    exact flipV_box hM d (tAdd_inBox (Nat.lt_of_lt_of_le (by decide) (Nat.mul_le_mul_left 2 hM)) hp d)
  · rw [flipPlaq_out M d w P h]; exact flipV_box hM d hp

/-- The reflection permutes the torus plaquettes. -/
theorem flipPlaq_perm (d : Dir4) :
    ((torusPlaquettes (2 * M)).map (flipPlaq M d)).Perm (torusPlaquettes (2 * M)) := by
  have hn2 := torusPlaquettes_nodup (2 * M)
  have mem : ∀ p : Z4Plaq, p ∈ torusPlaquettes (2 * M) ↔ InBox (2 * M) p.1 := fun p =>
    mem_torusPlaquettes (2 * M) p.1 p.2
  have hn1 : ((torusPlaquettes (2 * M)).map (flipPlaq M d)).Nodup := by
    refine nodup_map_on _ ?_ hn2
    intro x hx y hy he
    rw [← flipPlaq_invol hM d x ((mem x).mp hx), he, flipPlaq_invol hM d y ((mem y).mp hy)]
  refine perm_of_nodup_mem hn1 hn2 fun p => ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨q, hq, e⟩ := List.mem_map.mp h
    rw [← e]; exact (mem _).mpr (flipPlaq_box hM d q ((mem q).mp hq))
  · exact List.mem_map.mpr ⟨flipPlaq M d p, (mem _).mpr (flipPlaq_box hM d p ((mem p).mp h)),
      flipPlaq_invol hM d p ((mem p).mp h)⟩

/-- **Reflected holonomy:** `Re U^Θ_p = Re U_{Θp}` for every box plaquette. -/
theorem holonomy_flip_re (d : Dir4) (U : GaugeConfig SU2Q) (w : Z4Vertex) (hw : InBox (2 * M) w)
    (P : Z4Plane) :
    (holonomy SU2Q (2 * M) (flipConfig M d U) (w, P)).val.r ≈
      (holonomy SU2Q (2 * M) U (flipPlaq M d (w, P))).val.r := by
  have hab := dirsOf_ne P
  by_cases ha : (dirsOf P).1 = d
  · rw [flipPlaq_in M d w P (Or.inl ha)]
    unfold holonomy
    dsimp only
    rw [ha] at hab ⊢
    have hb : (dirsOf P).2 ≠ d := fun h => hab h.symm
    rw [flipConfig_same, flipConfig_other M d U _ hb, flipConfig_same, flipConfig_other M d U _ hb,
      tAdd_comm_ne (2 * M) w hb, flipV_tAdd_ne d _ hb, ← flipV_shift hM d hw]
    exact re_caseA _ _ _ _
  · by_cases hb : (dirsOf P).2 = d
    · rw [flipPlaq_in M d w P (Or.inr hb)]
      unfold holonomy
      dsimp only
      rw [hb] at hab ⊢
      rw [flipConfig_other M d U _ ha, flipConfig_same, flipConfig_other M d U _ ha, flipConfig_same,
        tAdd_comm_ne (2 * M) w hab, flipV_tAdd_ne d _ hab, ← flipV_shift hM d hw]
      exact re_caseB _ _ _ _
    · rw [flipPlaq_out M d w P (fun h => h.elim ha hb)]
      unfold holonomy
      dsimp only
      rw [flipConfig_other M d U _ ha, flipConfig_other M d U _ hb, flipConfig_other M d U _ ha,
        flipConfig_other M d U _ hb, flipV_tAdd_ne d _ ha, flipV_tAdd_ne d _ hb]
      exact Q'.eqv_refl _

/-- **Axis-reflection invariance of the Wilson energy** (any axis `d`, link-midpoint reflection on the `2M` torus). -/
theorem wilsonEnergy_axisFlip (d : Dir4) (U : GaugeConfig SU2Q) :
    wilsonEnergy (2 * M) (flipConfig M d U) ≈ wilsonEnergy (2 * M) U := by
  rw [wilsonEnergy_eq, wilsonEnergy_eq]
  refine Q'.eqv_trans _ _ _ (qsum_map_congr _ (fun p => wilsonPlaqEnergy (2 * M) U (flipPlaq M d p))
    (torusPlaquettes (2 * M)) fun p hp => ?_) ?_
  · obtain ⟨w, P⟩ := p
    exact plaqWeight_congr (holonomy_flip_re hM d U w ((mem_torusPlaquettes (2 * M) w P).mp hp) P)
  · have e : (fun p => wilsonPlaqEnergy (2 * M) U (flipPlaq M d p)) =
        wilsonPlaqEnergy (2 * M) U ∘ flipPlaq M d := rfl
    rw [e, ← List.map_map]
    exact qsum_perm ((flipPlaq_perm hM d).map _)

/-- **Time-mirror invariance** (the RP reflection Θ, `x0 ↦ 1 − x0`). -/
theorem wilsonEnergy_timeMirror (U : GaugeConfig SU2Q) :
    wilsonEnergy (2 * M) (flipConfig M .x0 U) ≈ wilsonEnergy (2 * M) U :=
  wilsonEnergy_axisFlip hM .x0 U

end Geometry

end YMGap.Continuum.WilsonSU2Weight
#print axioms YMGap.Continuum.WilsonSU2Weight.E_refl
#print axioms YMGap.Continuum.WilsonSU2Weight.E_symm
#print axioms YMGap.Continuum.WilsonSU2Weight.E_trans
#print axioms YMGap.Continuum.WilsonSU2Weight.re_cyc
#print axioms YMGap.Continuum.WilsonSU2Weight.re_caseA
#print axioms YMGap.Continuum.WilsonSU2Weight.re_caseB
#print axioms YMGap.Continuum.WilsonSU2Weight.pr
#print axioms YMGap.Continuum.WilsonSU2Weight.pr_app
#print axioms YMGap.Continuum.WilsonSU2Weight.pr_cancel
#print axioms YMGap.Continuum.WilsonSU2Weight.pr1
#print axioms YMGap.Continuum.WilsonSU2Weight.pr3
#print axioms YMGap.Continuum.WilsonSU2Weight.pr3'
#print axioms YMGap.Continuum.WilsonSU2Weight.pr4
#print axioms YMGap.Continuum.WilsonSU2Weight.gauge_word
#print axioms YMGap.Continuum.WilsonSU2Weight.plaqWeight
#print axioms YMGap.Continuum.WilsonSU2Weight.plaqWeight_congr
#print axioms YMGap.Continuum.WilsonSU2Weight.wilsonPlaqEnergy
#print axioms YMGap.Continuum.WilsonSU2Weight.wilsonEnergy
#print axioms YMGap.Continuum.WilsonSU2Weight.wilsonEnergy_eq
#print axioms YMGap.Continuum.WilsonSU2Weight.qsum_map_congr
#print axioms YMGap.Continuum.WilsonSU2Weight.gaugeAct
#print axioms YMGap.Continuum.WilsonSU2Weight.tAdd_comm_ne
#print axioms YMGap.Continuum.WilsonSU2Weight.dirsOf_ne
#print axioms YMGap.Continuum.WilsonSU2Weight.gauge_word'
#print axioms YMGap.Continuum.WilsonSU2Weight.wilsonPlaqEnergy_gauge
#print axioms YMGap.Continuum.WilsonSU2Weight.wilsonEnergy_gauge
#print axioms YMGap.Continuum.WilsonSU2Weight.wilsonEnergy_shift
#print axioms YMGap.Continuum.WilsonSU2Weight.flipV
#print axioms YMGap.Continuum.WilsonSU2Weight.flipV_x0
#print axioms YMGap.Continuum.WilsonSU2Weight.flipConfig
#print axioms YMGap.Continuum.WilsonSU2Weight.flipPlaq
#print axioms YMGap.Continuum.WilsonSU2Weight.flipConfig_same
#print axioms YMGap.Continuum.WilsonSU2Weight.flipConfig_other
#print axioms YMGap.Continuum.WilsonSU2Weight.flipPlaq_in
#print axioms YMGap.Continuum.WilsonSU2Weight.flipPlaq_out
#print axioms YMGap.Continuum.WilsonSU2Weight.flipV_box
#print axioms YMGap.Continuum.WilsonSU2Weight.flipV_invol
#print axioms YMGap.Continuum.WilsonSU2Weight.flipV_shift
#print axioms YMGap.Continuum.WilsonSU2Weight.flipV_tAdd_ne
#print axioms YMGap.Continuum.WilsonSU2Weight.flipPlaq_invol
#print axioms YMGap.Continuum.WilsonSU2Weight.flipPlaq_box
#print axioms YMGap.Continuum.WilsonSU2Weight.flipPlaq_perm
#print axioms YMGap.Continuum.WilsonSU2Weight.holonomy_flip_re
#print axioms YMGap.Continuum.WilsonSU2Weight.wilsonEnergy_axisFlip
#print axioms YMGap.Continuum.WilsonSU2Weight.wilsonEnergy_timeMirror
