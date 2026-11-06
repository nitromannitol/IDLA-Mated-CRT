import MatedCRT.Draft.Section4Prepared
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.Subsequence

/-! Dense evaluations determine the uniform limit of a relatively compact sequence. -/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric HarmonicBalls

/-- A relatively compact sequence of functions converges uniformly if its
point evaluations converge on a dense subset of the compact set. -/
theorem tendstoUniformlyOn_of_dense_subsequential_compactness
    {F : ℕ → ℂ → ℝ} {K : Set ℂ} (x : ℕ → ℂ)
    (hx : ∀ i, x i ∈ K) (hdense : K ⊆ closure (range x))
    (hc : ∀ ψ : ℕ → ℕ, StrictMono ψ → ∃ θ : ℕ → ℕ, StrictMono θ ∧ ∃ w : ℂ → ℝ,
      ContinuousOn w K ∧ TendstoUniformlyOn (fun n => F (ψ (θ n))) w atTop K)
    (hp : ∀ i, ∃ l : ℝ, Tendsto (fun n => F n (x i)) atTop (𝓝 l)) :
    ∃ w : ℂ → ℝ, ContinuousOn w K ∧ TendstoUniformlyOn F w atTop K := by
  obtain ⟨θ, hθ, w, hw, hconv⟩ := hc id strictMono_id
  refine ⟨w, hw, ?_⟩
  apply tendstoUniformlyOn_of_subsequence
  intro ψ hψ
  obtain ⟨ζ, hζ, v, hv, hvconv⟩ := hc ψ hψ
  have heq : EqOn v w K := by
    apply Set.EqOn.of_subset_closure ?_ hv hw (range_subset_iff.mpr hx) hdense
    rintro _ ⟨i, rfl⟩
    obtain ⟨l, hl⟩ := hp i
    have hvp := hvconv.tendsto_at (hx i)
    have hwp := hconv.tendsto_at (hx i)
    have hv_eq : v (x i) = l := tendsto_nhds_unique hvp
      (hl.comp (hψ.comp hζ).tendsto_atTop)
    have hw_eq : w (x i) = l := tendsto_nhds_unique hwp
      (hl.comp hθ.tendsto_atTop)
    exact hv_eq.trans hw_eq.symm
  exact ⟨ζ, hζ, hvconv.congr_right heq⟩

/-- Under prepared compactness, convergence on a dense set determines a
Hölder continuous uniform limit along the same subsequence. -/
theorem OdometerPreparedCompactness.uniform_limit_of_dense
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {ρ t : ℝ} {e : ℕ → ℝ} {ω : Ω}
    (hcompact : OdometerPreparedCompactness S ρ t e ω)
    (Φ : ℕ → ℕ) (hΦ : StrictMono Φ) (x : ℕ → ℂ)
    (hx : ∀ i, x i ∈ closedBall (0 : ℂ) ρ)
    (hdense : closedBall (0 : ℂ) ρ ⊆ closure (range x))
    (hp : ∀ i, ∃ l : ℝ, Tendsto
      (fun n => rescaledMatedLeastSupersolution S ρ t (e (Φ n)) ω (x i)) atTop (𝓝 l)) :
    ∃ w : ℂ → ℝ, ContinuousOn w (closedBall 0 ρ) ∧
      IsHolderContinuousOn w (closedBall 0 ρ) ∧
      TendstoUniformlyOn (fun n => rescaledMatedLeastSupersolution S ρ t (e (Φ n)) ω)
        w atTop (closedBall 0 ρ) := by
  obtain ⟨w, hw, hconv⟩ := tendstoUniformlyOn_of_dense_subsequential_compactness x hx hdense
    (fun ψ hψ => hcompact.1 (Φ ∘ ψ) (hΦ.comp hψ)) hp
  exact ⟨w, hw, hcompact.2 Φ hΦ w hconv, hconv⟩

end MatedCRT
