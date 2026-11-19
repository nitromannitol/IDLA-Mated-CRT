import MatedCRT.FirstPass.Derived.AnnealedWalkLawInterpClosenessAtPoint

/-!
# Annealed integrals of the quenched walk law started at the random vertices `k_n`

On the product space `annealedWalksAt hS ε hk` of the annealed laws of the embedded walks started at the random
vertices `k_n(ω)`, the quenched path law `Q^{ε_n}(k_n(ω))` is a measurable function of the environment, the annealed
expectation of `g (D_n, X_n)` for the interpolated walk path `X_n` equals the annealed expectation of the
integral of `g (D_n, ·)` against `Q^{ε_n}(k_n)`, and convergence in law of the environment datum `D_n` under
`S.P` is convergence in law of `D_n(ω)` under the product measure.  These are the three ingredients of the passage
from the closeness of the quenched law to a continuous function of the datum to the convergence in law of the
pair `(D_n, X_n)`.

* `measurable_walkPathLaw_start`: `ω ↦ Q^ε(k ω)(ω)` is measurable.
* `integral_annealedWalksAt_integral_walkPathLaw_eq`: the annealed expectation of `∫ g (D_n, x) dQ^{ε_n}(k_n)`.
* `tendsto_integral_annealedWalksAt_comp_fst`: convergence in law of the datum, transported to the product space.
-/

namespace MatedCRT.FirstPass.Derived

open MeasureTheory ProbabilityTheory Filter Topology Set Metric LatticeProb Preorder
open MarkovProcess (ContinuousPath)
open scoped NNReal ENNReal BoundedContinuousFunction

attribute [local instance] LatticeProb.dUnifMetricSpace

variable {Ω : Type} [MeasurableSpace Ω]

/-- The quenched path law started at a measurable random vertex is a measurable function of the
environment. -/
theorem measurable_walkPathLaw_start {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {S : MatedCRTEnv Ω}
    (hS : S.IsValid 𝒮 γ) {v : Ω → ℤ → ℂ} (hv : Measurable v) {m : ℝ} (hm : 0 ≤ m) (ε : ℝ)
    {k : Ω → ℤ} (hk : Measurable k) :
    Measurable fun ω => walkPathLaw S v hm ε (k ω) ω := by
  have h1 : Measurable fun r : Ω × ℤ => walkPathLaw S v hm ε r.2 r.1 :=
    measurable_from_prod_countable_left fun k => measurable_walkPathLaw hS hv hm ε k
  exact h1.comp (measurable_id.prodMk hk)

/-- **The annealed expectation of the integral against the quenched walk law from the random vertex.**  For a
bounded continuous `g` on the product of the datum space and the path space, the annealed expectation over
`annealedWalksAt` of `∫ g (D_n, x) dQ^{ε_n}(k_n)(x)` equals the annealed expectation of `g (D_n, X_n)`, where
`X_n` is the interpolated walk path. -/
theorem integral_annealedWalksAt_integral_walkPathLaw_eq
    {S₀ : Type*} [PseudoMetricSpace S₀] [SecondCountableTopology S₀] [MeasurableSpace S₀]
    [BorelSpace S₀] {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {S : MatedCRTEnv Ω}
    (hS : S.IsValid 𝒮 γ) [IsProbabilityMeasure S.P] (ε : ℕ → ℝ) {k : ℕ → Ω → ℤ}
    (hk : ∀ n, Measurable (k n)) {v : ℕ → Ω → ℤ → ℂ} (hv : ∀ n, Measurable (v n)) {m : ℕ → ℝ}
    (hm : ∀ n, 0 < m n) {d : ℕ → Ω → S₀} (hd : ∀ n, Measurable (d n))
    (g : (S₀ × C(ℝ≥0, ℂ)) →ᵇ ℝ) (n : ℕ) :
    ∫ p, ∫ x, g (d n (p n).1, x)
        ∂(walkPathLaw S (v n) (hm n).le (ε n) (k n (p n).1) (p n).1 : Measure C(ℝ≥0, ℂ))
        ∂annealedWalksAt hS ε hk =
      ∫ p, g (d n (p n).1, interpPathCM (v n (p n).1) (hm n).le (p n).2) ∂annealedWalksAt hS ε hk := by
  have hfst : Measurable fun p : ℕ → Ω × (ℕ → ℤ) => (p n).1 :=
    measurable_fst.comp (measurable_pi_apply n)
  have hG : Measurable fun q : Ω × (ℕ → ℤ) =>
      g (d n q.1, interpPathCM (v n q.1) (hm n).le q.2) :=
    g.continuous.measurable.comp (((hd n).comp measurable_fst).prodMk
      ((measurable_interpPathCM_uncurry (hm n).le).comp
        (((hv n).comp measurable_fst).prodMk measurable_snd)))
  have hF₀ : StronglyMeasurable fun ω => ∫ y, g (d n ω, interpPathCM (v n ω) (hm n).le y)
      ∂(walkKernelAt hS (ε n) (hk n) ω) := hG.stronglyMeasurable.integral_kernel_prod_right'
  have hFeq : (fun ω => ∫ y, g (d n ω, interpPathCM (v n ω) (hm n).le y)
        ∂(walkKernelAt hS (ε n) (hk n) ω)) = fun ω => ∫ x, g (d n ω, x)
        ∂(walkPathLaw S (v n) (hm n).le (ε n) (k n ω) ω : Measure C(ℝ≥0, ℂ)) := by
    funext ω
    have hfm : Measurable fun y : C(ℝ≥0, ℂ) => g (d n ω, y) :=
      g.continuous.measurable.comp (measurable_const.prodMk measurable_id)
    exact integral_walkStartKernel hS (v n) (hm n).le (ε n) ω (k n ω) hfm
  rw [hFeq] at hF₀
  rw [integral_annealedWalksAt_eq_integral_walkPathLaw hS ε hk hv hm hd g n]
  have h := integral_map (μ := annealedWalksAt hS ε hk) hfst.aemeasurable hF₀.aestronglyMeasurable
  rw [annealedWalksAt_map_fst hS ε hk n] at h
  exact h.symm

/-- **Convergence in law of the environment datum, on the annealed product space.**  If the data `D_n(ω)` converge
in law under `S.P` to `νD`, then `D_n((p n).1)` converges in law to `νD` under `annealedWalksAt`: the
environment coordinate of the `n`-th factor has law `S.P`. -/
theorem tendsto_integral_annealedWalksAt_comp_fst
    {S₀ : Type*} [TopologicalSpace S₀] [MeasurableSpace S₀] [OpensMeasurableSpace S₀]
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {S : MatedCRTEnv Ω}
    (hS : S.IsValid 𝒮 γ) [IsProbabilityMeasure S.P] (ε : ℕ → ℝ) {k : ℕ → Ω → ℤ}
    (hk : ∀ n, Measurable (k n)) {d : ℕ → Ω → S₀} (hd : ∀ n, Measurable (d n))
    {νD : Measure S₀}
    (h : ∀ f : S₀ →ᵇ ℝ,
      Tendsto (fun n => ∫ ω, f (d n ω) ∂S.P) atTop (𝓝 (∫ s, f s ∂νD))) (f : S₀ →ᵇ ℝ) :
    Tendsto (fun n => ∫ p, f (d n (p n).1) ∂annealedWalksAt hS ε hk) atTop (𝓝 (∫ s, f s ∂νD)) := by
  refine (h f).congr fun n => ?_
  have hfst : Measurable fun p : ℕ → Ω × (ℕ → ℤ) => (p n).1 :=
    measurable_fst.comp (measurable_pi_apply n)
  have hF : AEStronglyMeasurable (fun ω => f (d n ω)) S.P :=
    (f.continuous.measurable.comp (hd n)).aestronglyMeasurable
  have h2 := integral_map hfst.aemeasurable
    (μ := annealedWalksAt hS ε hk) (f := fun ω => f (d n ω))
    (by rw [annealedWalksAt_map_fst hS ε hk n]; exact hF)
  rw [annealedWalksAt_map_fst hS ε hk n] at h2
  exact h2

end MatedCRT.FirstPass.Derived
