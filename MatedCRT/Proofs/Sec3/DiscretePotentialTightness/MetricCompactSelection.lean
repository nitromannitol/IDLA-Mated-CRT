import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.Selection
import MatedCRT.Proofs.Sec4.SubsequentialConvergence.PreparedPointBounds

/-! # Selection by distances in a metric space -/

namespace MatedCRT

open Filter Topology MeasureTheory

/-- In a metric space, relative sequential compactness plus convergence of
    distances to every member of the original sequence determines a limit. -/
theorem tendsto_of_subsequential_compactness_and_distances
    {X : Type*} [MetricSpace X] (F : ℕ → X)
    (hc : ∀ ψ : ℕ → ℕ, StrictMono ψ → ∃ θ : ℕ → ℕ, StrictMono θ ∧
      ∃ w : X, Tendsto (fun n => F (ψ (θ n))) atTop (𝓝 w))
    (hd : ∀ m, ∃ l : ℝ, Tendsto (fun n => dist (F n) (F m)) atTop (𝓝 l)) :
    ∃ w : X, Tendsto F atTop (𝓝 w) := by
  obtain ⟨θ, hθ, w, hw⟩ := hc id strictMono_id
  refine ⟨w, ?_⟩
  apply Filter.tendsto_of_subseq_tendsto
  intro ψ hψ
  obtain ⟨δ, hδ, hψδ⟩ := strictMono_subseq_of_tendsto_atTop hψ
  obtain ⟨ζ, hζ, v, hv⟩ := hc (ψ ∘ δ) hψδ
  have heq : ∀ m, dist w (F m) = dist v (F m) := by
    intro m
    obtain ⟨l, hl⟩ := hd m
    have hw' : Tendsto (fun n => dist (F (θ n)) (F m)) atTop (𝓝 (dist w (F m))) :=
      hw.dist tendsto_const_nhds
    have hv' : Tendsto (fun n => dist (F (ψ (δ (ζ n)))) (F m)) atTop (𝓝 (dist v (F m))) :=
      hv.dist tendsto_const_nhds
    exact (tendsto_nhds_unique hw' (hl.comp hθ.tendsto_atTop)).trans
      (tendsto_nhds_unique hv' (hl.comp (hψδ.comp hζ).tendsto_atTop)).symm
  have hvw : v = w := by
    have h₁ : Tendsto (fun n => dist w (F (θ n))) atTop (𝓝 0) := by
      have hh : Tendsto (fun n => dist w (F (θ n))) atTop (𝓝 (dist w w)) :=
        tendsto_const_nhds.dist hw
      simpa using hh
    have h₂ : Tendsto (fun n => dist v (F (θ n))) atTop (𝓝 (dist v w)) :=
      tendsto_const_nhds.dist hw
    have hz : dist v w = 0 := tendsto_nhds_unique h₂ (by simpa only [heq] using h₁)
    exact dist_eq_zero.mp hz
  subst v
  exact ⟨δ ∘ ζ, hv⟩

/-- Measurable pairwise distances select one subsequence converging for every
    member of a countable relatively compact family. -/
theorem exists_measurable_subsequence_of_metric_compactness
    {Ω X : Type*} [MeasurableSpace Ω] [MetricSpace X]
    (F : Ω → ℕ → ℕ → X)
    (hdm : ∀ j n m, Measurable fun ω => dist (F ω j n) (F ω j m))
    (P : Ω → Prop)
    (hc : ∀ ω, P ω → ∀ j ψ, StrictMono ψ →
      ∃ θ : ℕ → ℕ, StrictMono θ ∧ ∃ w : X,
        Tendsto (fun n => F ω j (ψ (θ n))) atTop (𝓝 w)) :
    ∃ Φ : Ω → ℕ → ℕ, (∀ k, Measurable fun ω => Φ ω k) ∧
      ∀ ω, StrictMono (Φ ω) ∧ (P ω → ∀ j, ∃ w : X,
        Tendsto (fun n => F ω j (Φ ω n)) atTop (𝓝 w)) := by
  let y : Ω → ℕ → ℕ → ℝ := fun ω n c => dist (F ω c.unpair.1 n) (F ω c.unpair.1 c.unpair.2)
  obtain ⟨Φ, hΦm, hΦ⟩ := Tightness.exists_measurable_diagonal_subseq y
    (fun n c => hdm c.unpair.1 n c.unpair.2)
  refine ⟨Φ, hΦm, fun ω => ⟨(hΦ ω).1, ?_⟩⟩
  intro hP j
  apply tendsto_of_subsequential_compactness_and_distances
  · intro ψ hψ
    exact hc ω hP j (Φ ω ∘ ψ) ((hΦ ω).1.comp hψ)
  · intro m
    let c := Nat.pair j (Φ ω m)
    have hb : ∃ M : ℝ, ∀ᶠ n in atTop, |y ω n c| ≤ M := by
      apply eventually_bounded_of_subsequential_compactness
      intro ψ hψ
      obtain ⟨θ, hθ, w, hw⟩ := hc ω hP j ψ hψ
      refine ⟨θ, hθ, dist w (F ω j (Φ ω m)), ?_⟩
      simpa [y, c] using hw.dist (tendsto_const_nhds : Tendsto (fun _ : ℕ => F ω j (Φ ω m)) atTop _)
    obtain ⟨l, hl⟩ := (hΦ ω).2 c hb
    exact ⟨l, by simpa [y, c] using hl⟩

/-- Each member may have a separate pathwise compactness condition. -/
theorem exists_measurable_subsequence_of_conditional_metric_compactness
    {Ω X : Type*} [MeasurableSpace Ω] [MetricSpace X]
    (F : Ω → ℕ → ℕ → X)
    (hdm : ∀ j n m, Measurable fun ω => dist (F ω j n) (F ω j m))
    (P : Ω → ℕ → Prop)
    (hc : ∀ ω j, P ω j → ∀ ψ, StrictMono ψ →
      ∃ θ : ℕ → ℕ, StrictMono θ ∧ ∃ w : X,
        Tendsto (fun n => F ω j (ψ (θ n))) atTop (𝓝 w)) :
    ∃ Φ : Ω → ℕ → ℕ, (∀ k, Measurable fun ω => Φ ω k) ∧
      ∀ ω, StrictMono (Φ ω) ∧ (∀ j, P ω j → ∃ w : X,
        Tendsto (fun n => F ω j (Φ ω n)) atTop (𝓝 w)) := by
  let y : Ω → ℕ → ℕ → ℝ := fun ω n c => dist (F ω c.unpair.1 n) (F ω c.unpair.1 c.unpair.2)
  obtain ⟨Φ, hΦm, hΦ⟩ := Tightness.exists_measurable_diagonal_subseq y
    (fun n c => hdm c.unpair.1 n c.unpair.2)
  refine ⟨Φ, hΦm, fun ω => ⟨(hΦ ω).1, ?_⟩⟩
  intro j hP
  apply tendsto_of_subsequential_compactness_and_distances
  · intro ψ hψ
    exact hc ω j hP (Φ ω ∘ ψ) ((hΦ ω).1.comp hψ)
  · intro m
    let c := Nat.pair j (Φ ω m)
    have hb : ∃ M : ℝ, ∀ᶠ n in atTop, |y ω n c| ≤ M := by
      apply eventually_bounded_of_subsequential_compactness
      intro ψ hψ
      obtain ⟨θ, hθ, w, hw⟩ := hc ω j hP ψ hψ
      refine ⟨θ, hθ, dist w (F ω j (Φ ω m)), ?_⟩
      simpa [y, c] using hw.dist (tendsto_const_nhds : Tendsto (fun _ : ℕ => F ω j (Φ ω m)) atTop _)
    obtain ⟨l, hl⟩ := (hΦ ω).2 c hb
    exact ⟨l, by simpa [y, c] using hl⟩

end MatedCRT
