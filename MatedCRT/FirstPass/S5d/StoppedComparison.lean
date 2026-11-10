import MatedCRT.Proofs.WalkPotential.GreenFirstStep
import MatedCRT.Proofs.WalkPotential.MaximumPrinciple
import MatedCRT.Proofs.Sec5.StoppedSurplusComparison
import MatedCRT.Proofs.Sec4.SubsequentialProperties.DiscreteComparison
import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.EquicontinuityLemmas
import MatedCRT.Proofs.Infra.RandomWalk

/-!
# Deterministic comparison for the stopped clause of Proposition 5.1 (z5, fp-S5d-5-1-stopped-repair)

Referee notes/fp-gaps/CHATGPT-5-1-gaps-referee.md §5.2 (maximum-principle comparison (5.3)), §5.2 (5.5).
For a finite killing set `I ⊆ ℤ` (the intersection `S_ε ∩ V^ε(Λ_t)` of the referee) and the Green combination
`J_I(a) = κ g_I(a,0) - ∑_{b∈I} g_I(a,b)`, `g_I = G_I / deg` (Armitage-Gardiner Green kernel), the discrete
Laplacian of `J_I` on `I` is `1/deg(a) - κ 1_{a=0}/deg(0)`. A surplus `v` with the same Laplacian on `I` and
`v ≤ M` off `I` satisfies `v - M ≤ J_I` on `I` (minimum principle, `nonpos_of_lapSum_nonneg`).

Probabilistic inputs (exterior error, fixed-radius Green lower bounds, surplus lower bound on the target) are NOT
here; this file is purely deterministic.
-/

namespace MatedCRT

open Set

/-- Adding a constant does not change `lapSum`. -/
theorem lapSum_sub_const_fn {m : ℤ → ℤ → ℕ} (hlf : IsLocallyFiniteMult m) (u : ℤ → ℝ) (c : ℝ) (a : ℤ) :
    lapSum hlf (fun x => u x - c) a = lapSum hlf u a := by
  simp only [lapSum]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

/-- **Comparison (5.3)** (referee §5.2): if `Δ J = Δ v` on the finite set `I`, `J = 0` and `v ≤ M` off `I`, then
`v - M ≤ J` on `I`. Maximum principle `nonpos_of_lapSum_nonneg` applied to `w = v - J - M`. -/
theorem surplus_sub_le_of_mLaplacian_eq {m : ℤ → ℤ → ℕ} (hlf : IsLocallyFiniteMult m)
    (hsucc : ∀ k : ℤ, m k (k + 1) ≠ 0) {I : Set ℤ} (hI : I.Finite) {J v : ℤ → ℝ} {M : ℝ}
    (hlap : ∀ a ∈ I, mLaplacian m J a = mLaplacian m v a)
    (hJ : ∀ b ∉ I, J b = 0) (hvM : ∀ b ∉ I, v b ≤ M) :
    ∀ a ∈ I, v a - M ≤ J a := by
  have hsub : ∀ a ∈ I, 0 ≤ lapSum hlf (fun x => v x - J x - M) a := by
    intro a ha
    have h1 : lapSum hlf (fun x => v x - J x - M) a = lapSum hlf (fun x => v x - J x) a :=
      lapSum_sub_const_fn hlf (fun x => v x - J x) M a
    have h2 : lapSum hlf (fun x => v x - J x) a = lapSum hlf v a - lapSum hlf J a :=
      lapSum_sub hlf v J a
    have hJv : lapSum hlf J a = lapSum hlf v a := by
      rw [← mLaplacian_mul_mdeg hlf J a, ← mLaplacian_mul_mdeg hlf v a, hlap a ha]
    linarith
  have hbd : ∀ a ∈ I, ∀ b, m a b ≠ 0 → b ∉ I → v b - J b - M ≤ 0 := by
    intro a _ b _ hb
    rw [hJ b hb]
    linarith [hvM b hb]
  have key := nonpos_of_lapSum_nonneg hlf hI (escape_of_adjacent_succ hsucc hI) hsub hbd
  intro a ha
  have h := key a ha
  linarith

/-- The Green combination `J_I(a) = κ g_I(a,0) - ∑_{b∈I} g_I(a,b)` vanishes off `I`. -/
theorem greenComb_eq_zero_of_not_mem {m : ℤ → ℤ → ℕ} {I : Set ℤ} (hI : I.Finite) (κ : ℝ) {x : ℤ}
    (hx : x ∉ I) :
    κ * greenKernel m I x 0 - ∑ b ∈ hI.toFinset, greenKernel m I x b = 0 := by
  simp [greenKernel_eq_zero_of_not_mem m hx]

/-- **Discrete Laplacian of the Green combination** (referee §5.2, the identity behind (5.3)): for `a ∈ I`,
`Δ J_I(a) = -κ 1_{a=0}/deg(0) + 1/deg(a)`, from `Δ_x G_I(x,b) = -δ_{xb}` (`WalkPotential.mLaplacian_greenFn`) and
`Δ ∑_{b∈I} g_I(·,b) = -1/deg` on `I` (`mLaplacian_greenPotential_finset`). -/
theorem mLaplacian_greenComb {m : ℤ → ℤ → ℕ} (hlf : IsLocallyFiniteMult m) (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0)
    {I : Set ℤ} (hI : I.Finite) (κ : ℝ) {a : ℤ} (ha : a ∈ I) :
    mLaplacian m (fun y => κ * greenKernel m I y 0 - ∑ b ∈ hI.toFinset, greenKernel m I y b) a
      = -(κ * (if a = 0 then (mdeg m 0 : ℝ)⁻¹ else 0)) + (mdeg m a : ℝ)⁻¹ := by
  have hG : mLaplacian m (fun y => greenFn m I y 0) a = -(if a = 0 then 1 else 0) :=
    WalkPotential.mLaplacian_greenFn hlf hcons hI 0 a ha
  have hfun : (fun y => κ * greenKernel m I y 0) = fun y => (κ * (mdeg m 0 : ℝ)⁻¹) * greenFn m I y 0 := by
    funext y
    unfold greenKernel
    ring
  have hK : mLaplacian m (fun y => κ * greenKernel m I y 0) a
      = κ * (mdeg m 0 : ℝ)⁻¹ * -(if a = 0 then 1 else 0) := by
    have h : mLaplacian m (fun y => (κ * (mdeg m 0 : ℝ)⁻¹) * greenFn m I y 0) a
        = (κ * (mdeg m 0 : ℝ)⁻¹) * mLaplacian m (fun y => greenFn m I y 0) a :=
      MatedCRT.Tightness.mLaplacian_const_mul hlf (κ * (mdeg m 0 : ℝ)⁻¹) (fun y => greenFn m I y 0) a
    rw [hfun, h, hG]
  have hmem : a ∈ hI.toFinset := hI.mem_toFinset.2 ha
  have hS : mLaplacian m (fun y => ∑ b ∈ hI.toFinset, greenKernel m I y b) a
      = -(if a ∈ hI.toFinset then (mdeg m a : ℝ)⁻¹ else 0) :=
    mLaplacian_greenPotential_finset hlf (fun b x hx => WalkPotential.mLaplacian_greenFn hlf hcons hI b x hx)
      hI.toFinset ha
  have hsplit : mLaplacian m (fun y => κ * greenKernel m I y 0 - ∑ b ∈ hI.toFinset, greenKernel m I y b) a
      = mLaplacian m (fun y => κ * greenKernel m I y 0) a
        - mLaplacian m (fun y => ∑ b ∈ hI.toFinset, greenKernel m I y b) a :=
    mLaplacian_sub_of_locallyFinite hlf _ _ a
  rw [hsplit, hK, hS]
  simp only [hmem, ↓reduceIte]
  split_ifs <;> ring

/-- **The surplus comparison for the Green combination** (referee §5.2, (5.3)): if the surplus `v` satisfies the
discrete Laplacian identity `Δ v = 1/deg - κ 1_{a=0}/deg(0)` on `I` (paper line 1970, with `κ = t/ε`) and
`v ≤ M` off `I`, then `v(a) - M ≤ κ g_I(a,0) - ∑_{b∈I} g_I(a,b)` for `a ∈ I`. -/
theorem surplus_sub_le_greenComb {m : ℤ → ℤ → ℕ} (hlf : IsLocallyFiniteMult m)
    (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) {I : Set ℤ} (hI : I.Finite) (κ : ℝ) {v : ℤ → ℝ} {M : ℝ}
    (hv : ∀ a ∈ I, mLaplacian m v a = (mdeg m a : ℝ)⁻¹ - κ * (if a = 0 then (mdeg m 0 : ℝ)⁻¹ else 0))
    (hvM : ∀ b ∉ I, v b ≤ M) :
    ∀ a ∈ I, v a - M ≤ κ * greenKernel m I a 0 - ∑ b ∈ hI.toFinset, greenKernel m I a b := by
  refine surplus_sub_le_of_mLaplacian_eq hlf hcons hI ?_ (fun b hb => greenComb_eq_zero_of_not_mem hI κ hb) hvM
  intro a ha
  rw [mLaplacian_greenComb hlf hcons hI κ ha, hv a ha]
  ring

/-- **Arithmetic of (5.4)-(5.5)** (referee §5.2): if `g - q ≥ c/(2ε)` (the comparison at a target, with
`g = (t/ε) g_I(a,0)` and `q = q_I(a)`) and `q ≤ C/ε` (exit-time bound) with `c ≥ 0`, `C > 0`, `ε > 0`, then
`(1 + c/(2C)) q ≤ g`, the first Green inequality of Lemma 5.2. -/
theorem firstGreen_of_surplus_bound {g q ε c C : ℝ} (hε : 0 < ε) (hC : 0 < C) (hc : 0 ≤ c)
    (hq : q ≤ C / ε) (hJ : c / (2 * ε) ≤ g - q) :
    (1 + c / (2 * C)) * q ≤ g := by
  have hqε : q * ε ≤ C := by
    have h := hq
    rw [le_div_iff₀ hε] at h
    exact h
  have h1 : c / (2 * C) * q ≤ c / (2 * ε) := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hqε hc]
  nlinarith

end MatedCRT
