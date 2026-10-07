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

**From CS to `LogConvex`.** This step is not done here. It takes `G(j) := rpB F (τ_j F)`, where `τ` is the
time-translation of observables and `τ_j F` is again `PtSup`, and uses `rpB (τ_a F) (τ_b F) = G(a+b)`. Applying
`TorusCS` to `τ_j F` and `τ_{j+2} F`... that identification of `G` (transfer structure) is a separate open item.

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

**STATUS: `TorusRPPoly` AND `TorusCS` ARE OPEN (stated, not proved).**
