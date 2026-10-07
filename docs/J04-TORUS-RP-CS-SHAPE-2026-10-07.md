# J04: RP Cauchy–Schwarz shape for `SU2LogConvexGap` (2026-10-07 PT)

**Consumer.** `SU2LogConvexGap.LogConvex G L := ∀ j, j+2 ≤ L → G(j+1)*G(j+1) ≤ G j * G(j+2)`, where `G : Nat → Q'`.
It is rational and cross-multiplied, with no roots. `Pos G L` is a separate hypothesis.

**Agreed producer shape** (`SU2TorusRPCSShape`, definitions only):

* `rpB hM β K F G := ∫_{|torusLinks (2M)|} thetaT(F) · G · Π_{torusPlaquettes} T_K`. This is the unnormalised
  `T_K` weight. Normalisation by `Z > 0` cancels in CS.
* `PtSup F`: every variable that occurs lies in a `Pt M` block of `torusLinks`. Constants qualify, so the class is
  closed under `F ↦ F − c`, which gives the truncated `F − ⟨F⟩`.
* `TorusRPPoly : ∀ F, PtSup F → 0 ≤ rpB F F` (target 1).
* `TorusCS : ∀ F G, PtSup F → PtSup G → rpB F G * rpB F G ≤ rpB F F * rpB G G` (target 2). This is the same `≤`
  and cross-multiplied form as `LogConvex`.

**From CS to `LogConvex`.** This step is not done here. It needs `G(n) := rpB F (τ_n F)` with time translation
`τ`, and the identity `rpB (τ_x F) (τ_y F) ≈ G(x+y)` (transfer structure), so that `TorusCS` at `(τ_x F, τ_y F)` gives
`G(x+y)² ≤ G(2x)·G(2y)`. Odd `j` additionally needs the CS for the pair `(F, τ_1 F)`. This is a separate open item.

**Proof plan.**
1. A monomial decomposition `PtSup F → F ≡PE eval (obsOf F)`, with `OnLinks Pt`, reduces `TorusRPPoly` to
   `torus_rp`.
2. Bilinearity of `rpB`: `thetaT` is a `RingSub`, and Haar is linear.
3. Symmetry `rpB F G ≈ rpB G F`: by Θ-invariance of Haar (`theta_haar`), `Θ Π T_K ≡ Π T_K` (`theta_prod` over all
   torus plaquettes), and `Θ∘Θ ≡ id` on supported polynomials. All quantities are real, because Θ includes the
   quaternion conjugation on time links, so there is no complex conjugate.
4. Rational polarization: `0 ≤ rpB(sF+tG, sF+tG) ≈ s²a + 2st·b + t²c`.
   * Take `(s,t) = (c, −b)` to get `c(ac−b²)`.
   * Take `(−b, a)` to get `a(ac−b²)`.
   * Take `(1, −b)` with `a ≈ c ≈ 0` to get `−2b²`.
   * Case on the decidable `0 < c` and `0 < a`.

   Q' identities reduce to Int, closed by `simp only [Int.mul_add, …, Int.mul_comm, Int.mul_left_comm]; omega`
   (checked [propext, Quot.sound]; `grind` brings in Classical and is avoided).

Integer discriminant core `SU2TorusRPCSCore.cs_int` and rational form `SU2TorusRPCSRat.cs_q` (`(∀ s t : Int, 0 ≤ quad a b c s t) → b*b ≤ a*c`): PROVED ([propext, Quot.sound]). Symmetry `SU2TorusRPSym.rpB_symm`: `rpB (eval e) (eval e') ≈ rpB (eval e') (eval e)` for observables on torus links,
via `theta_haar`, `theta_prod`, `tp_mir_perm` and `theta2_obs` (`Θ∘Θ ≡ id`): PROVED ([propext, Quot.sound]).
Remaining for `TorusCS`: the bilinear expansion `rpB(sF+tG, sF+tG) ≈ quad (rpB F F) (rpB F G) (rpB G G) s t`. This
needs PE distributivity and smul-extraction lemmas, then `torus_rp` at `s·e + t·e'` and `cs_q`. Also remaining:
`TorusRPPoly`, i.e. `PtSup F → F ≡ eval (obsOf F)`.

**Interface needed from the Prover (time translation, item 3).** `τ : Nat → RatPoly → RatPoly` such that:
(i) `PtSup F → PtSup (τ n F)` (or the `Obs` analogue `OnLinks (· ∈ Pt M)`);
(ii) `rpB (τ x F) (τ y F) ≈ G(x+y)` with `G n := rpB F (τ n F)`, i.e. `Θ∘τ_x = τ_{-x}∘Θ` under the T_K measure,
plus invariance of `Π T_K` under time shifts.
Then `TorusCS` gives `G(x+y)² ≤ G(2x)·G(2y)`. The `LogConvex` step `j ↦ j+1` needs the pair `(τ_a F, τ_{a+1} F)`,
with `G(2a+1)² ≤ G(2a)·G(2a+2)`; odd `j` uses `F' := τ_? ` conventions decided by the Prover.

**STATUS: `TorusRPPoly` AND `TorusCS` ARE OPEN (stated, not proved).**
