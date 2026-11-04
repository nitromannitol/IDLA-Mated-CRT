import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.InteriorDiscreteModulus

/-! A deterministic consequence of local uniform subsequential convergence. -/

namespace MatedCRT

open Set Metric Filter Topology

/-- Uniform convergence to a continuous function on a compact set rules out a
fixed oscillation at scales tending to zero. The approximating functions need
not themselves be continuous. -/
theorem eventually_small_oscillation_of_uniform_subsequence
    {α : Type*} [PseudoMetricSpace α] (K : Set α) (hK : IsCompact K)
    (f : ℕ → α → ℝ) (u : α → ℝ) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hu : ContinuousOn u K) (hconv : TendstoUniformlyOn (fun n => f (φ n)) u atTop K)
    {t : ℝ} (ht : 0 < t) :
    ∀ᶠ n in atTop, ∀ x ∈ K, ∀ y ∈ K,
      dist x y < 1 / ((φ n : ℝ) + 1) → |f (φ n) x - f (φ n) y| < t := by
  have ht3 : 0 < t / 3 := by linarith
  obtain ⟨δ, hδ, hδu⟩ := Metric.uniformContinuousOn_iff.mp
    (hK.uniformContinuousOn_of_continuous hu) (t / 3) ht3
  have hscale : Tendsto (fun n : ℕ => 1 / ((φ n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
  have hnear := (Metric.tendstoUniformlyOn_iff.1 hconv) (t / 3) ht3
  filter_upwards [hscale.eventually (Iio_mem_nhds hδ), hnear] with n hn hclose
  intro x hx y hy hxy
  have hux := hclose x hx
  have huy := hclose y hy
  have hxyu := hδu x hx y hy (hxy.trans hn)
  rw [Real.dist_eq] at hux huy hxyu
  rw [abs_sub_comm] at hux huy
  have htri : |f (φ n) x - f (φ n) y| ≤
      |f (φ n) x - u x| + |u x - u y| + |f (φ n) y - u y| := by
    calc
      |f (φ n) x - f (φ n) y| =
          |(f (φ n) x - u x) + (u x - u y) - (f (φ n) y - u y)| := by congr 1; ring
      _ ≤ |(f (φ n) x - u x) + (u x - u y)| + |f (φ n) y - u y| := abs_sub _ _
      _ ≤ |f (φ n) x - u x| + |u x - u y| + |f (φ n) y - u y| := by
        gcongr
        exact abs_add_le _ _
  linarith

end MatedCRT
