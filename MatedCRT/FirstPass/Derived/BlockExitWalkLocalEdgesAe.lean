import MatedCRT.FirstPass.Derived.LocalEdgesTendstoZero

/-!
# Almost surely, edges starting in a fixed ball are eventually shorter than any `θ`

The closed-ball form of `MatedCRTEnv.IsValid.ae_eventually_local_edges_lt`, with the non-strict
bound in the form used by the walk-side block-exit estimates.

## Main results

* `MatedCRTEnv.IsValid.ae_eventually_edges_le_of_norm_le`: almost surely, for every `θ > 0`, along a
  null sequence of meshes, eventually every edge of the mated-CRT map whose starting vertex has
  embedded norm at most `B` has embedded length at most `θ`.
-/

open MeasureTheory Set Metric Filter
open scoped Topology

namespace MatedCRT

/-- **Almost surely, edges starting in the closed ball of radius `B` are eventually of length at most
`θ`, for every `θ > 0`, along every null sequence of meshes.** -/
theorem MatedCRTEnv.IsValid.ae_eventually_edges_le_of_norm_le {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    (hS : S.IsValid 𝒮 γ) {e : ℕ → ℝ} (he : ∀ n, 0 < e n) (he0 : Tendsto e atTop (𝓝 0)) (B : ℝ) :
    ∀ᵐ ω ∂S.P, ∀ θ : ℝ, 0 < θ → ∀ᶠ n in atTop, ∀ j k : ℤ,
      S.mult (e n) ω j k ≠ 0 → ‖vertexPoint (e n) (S.η ω) j‖ ≤ B →
      dist (vertexPoint (e n) (S.η ω) j) (vertexPoint (e n) (S.η ω) k) ≤ θ := by
  filter_upwards [hS.ae_eventually_local_edges_lt hγ hγ2 he he0 (B + 1)] with ω hω θ hθ
  filter_upwards [hω θ hθ] with n hn j k hm hj
  exact (hn j k hm (by rw [mem_ball_zero_iff]; linarith)).le

end MatedCRT
