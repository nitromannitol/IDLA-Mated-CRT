import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.MetricCompactSelection

/-! # Selection using measurable versions of distances -/

namespace MatedCRT

open Filter Topology MeasureTheory

/-- Measurable versions need agree with the pairwise distances only where
    the corresponding compactness condition is used. -/
theorem exists_measurable_subsequence_of_conditional_distance_versions
    {Ω X : Type*} [MeasurableSpace Ω] [MetricSpace X]
    (F : Ω → ℕ → ℕ → X) (d : ℕ → ℕ → ℕ → Ω → ℝ)
    (hdm : ∀ j n m, Measurable (d j n m)) (P : Ω → ℕ → Prop)
    (hd : ∀ ω j, P ω j → ∀ n m, d j n m ω = dist (F ω j n) (F ω j m))
    (hc : ∀ ω j, P ω j → ∀ ψ, StrictMono ψ →
      ∃ θ : ℕ → ℕ, StrictMono θ ∧ ∃ w : X,
        Tendsto (fun n => F ω j (ψ (θ n))) atTop (𝓝 w)) :
    ∃ Φ : Ω → ℕ → ℕ, (∀ k, Measurable fun ω => Φ ω k) ∧
      ∀ ω, StrictMono (Φ ω) ∧ (∀ j, P ω j → ∃ w : X,
        Tendsto (fun n => F ω j (Φ ω n)) atTop (𝓝 w)) := by
  let y : Ω → ℕ → ℕ → ℝ := fun ω n c => d c.unpair.1 n c.unpair.2 ω
  obtain ⟨Φ, hΦm, hΦ⟩ := Tightness.exists_measurable_diagonal_subseq y
    (fun n c => hdm c.unpair.1 n c.unpair.2)
  refine ⟨Φ, hΦm, fun ω => ⟨(hΦ ω).1, ?_⟩⟩
  intro j hP
  apply tendsto_of_subsequential_compactness_and_distances
  · intro ψ hψ
    exact hc ω j hP (Φ ω ∘ ψ) ((hΦ ω).1.comp hψ)
  · intro m
    let c := Nat.pair j (Φ ω m)
    have hy : ∀ n, y ω n c = dist (F ω j n) (F ω j (Φ ω m)) := by
      intro n
      simpa [y, c] using hd ω j hP n (Φ ω m)
    have hb : ∃ M : ℝ, ∀ᶠ n in atTop, |y ω n c| ≤ M := by
      apply eventually_bounded_of_subsequential_compactness
      intro ψ hψ
      obtain ⟨θ, hθ, w, hw⟩ := hc ω j hP ψ hψ
      refine ⟨θ, hθ, dist w (F ω j (Φ ω m)), ?_⟩
      simpa only [hy] using hw.dist
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => F ω j (Φ ω m)) atTop _)
    obtain ⟨l, hl⟩ := (hΦ ω).2 c hb
    exact ⟨l, by simpa only [hy] using hl⟩

end MatedCRT
