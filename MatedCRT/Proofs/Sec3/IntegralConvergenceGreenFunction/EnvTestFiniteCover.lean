import MatedCRT.Defs.Notation

/-!
# Finite-cover reduction for environment-dependent test functions (E-c2-9)

Probabilistic core of the argument of `docs/campaign/GAPS-SEC3.md`, section E-c2-9. A functional whose
test function depends on the environment is approximated, for every accuracy, by finitely many
deterministic tests on events whose union has probability close to one. Convergence in probability
then transfers from the deterministic tests (Theorem 2.11) to the random test.
-/

namespace MatedCRT

open MeasureTheory Set Filter Topology
open scoped ENNReal

/-- **Finite-cover criterion for convergence in probability.** Suppose `Xj j → Yj j` in probability for
each `j : ℕ`. Suppose also that for every accuracy `b > 0` and every `κ > 0` there are `J` and events
`A j` such that, on each `A j` with `j < J`, the random pair `(X ε, Y)` is `b`-close to the `j`-th
deterministic pair `(Xj j ε, Yj j)` uniformly in `ε`, and the union of the `A j` has probability at least
`1 - κ`. Then `X ε → Y` in probability. -/
theorem tendstoInProbability_of_finite_cover {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℝ → Ω → ℝ) (Y : Ω → ℝ) (Xj : ℕ → ℝ → Ω → ℝ) (Yj : ℕ → Ω → ℝ)
    (hconv : ∀ j : ℕ, TendstoInProbability P (Xj j) (Yj j))
    (hcover : ∀ b : ℝ, 0 < b → ∀ κ : ℝ≥0∞, 0 < κ → ∃ (J : ℕ) (A : ℕ → Set Ω),
      (∀ j ∈ Finset.range J, ∀ ε : ℝ, ∀ ω ∈ A j,
        |X ε ω - Xj j ε ω| ≤ b ∧ |Y ω - Yj j ω| ≤ b) ∧
      P ((⋃ j ∈ Finset.range J, A j)ᶜ) < κ) :
    TendstoInProbability P X Y := by
  intro η hη
  refine ENNReal.tendsto_nhds_zero.2 fun e he => ?_
  obtain ⟨J, A, hA, hcov⟩ := hcover (η / 4) (by linarith) (e / 2) (ENNReal.half_pos he.ne')
  have hsum : Tendsto (fun ε => ∑ j ∈ Finset.range J, P {ω | η / 2 < |Xj j ε ω - Yj j ω|})
      (𝓝[>] 0) (𝓝 0) := by
    simpa using tendsto_finsetSum (Finset.range J) (fun j _ => hconv j (η / 2) (by linarith))
  filter_upwards [ENNReal.tendsto_nhds_zero.1 hsum (e / 2) (ENNReal.half_pos he.ne')] with ε hε
  have hsub : {ω | η < |X ε ω - Y ω|} ⊆
      (⋃ j ∈ Finset.range J, A j)ᶜ ∪ ⋃ j ∈ Finset.range J, {ω | η / 2 < |Xj j ε ω - Yj j ω|} := by
    intro ω hω
    by_cases hU : ω ∈ ⋃ j ∈ Finset.range J, A j
    · right
      obtain ⟨j, hj, hωA⟩ := mem_iUnion₂.1 hU
      refine mem_iUnion₂.2 ⟨j, hj, ?_⟩
      obtain ⟨h1, h2⟩ := hA j hj ε ω hωA
      have key := abs_add_three (X ε ω - Xj j ε ω) (Xj j ε ω - Yj j ω) (Yj j ω - Y ω)
      have e2 : X ε ω - Xj j ε ω + (Xj j ε ω - Yj j ω) + (Yj j ω - Y ω) = X ε ω - Y ω := by ring
      rw [e2, abs_sub_comm (Yj j ω) (Y ω)] at key
      have hω' : η < |X ε ω - Y ω| := hω
      show η / 2 < |Xj j ε ω - Yj j ω|
      linarith
    · left
      exact hU
  calc P {ω | η < |X ε ω - Y ω|}
      ≤ P ((⋃ j ∈ Finset.range J, A j)ᶜ ∪ ⋃ j ∈ Finset.range J, {ω | η / 2 < |Xj j ε ω - Yj j ω|}) :=
        measure_mono hsub
    _ ≤ P ((⋃ j ∈ Finset.range J, A j)ᶜ) +
          P (⋃ j ∈ Finset.range J, {ω | η / 2 < |Xj j ε ω - Yj j ω|}) := measure_union_le _ _
    _ ≤ P ((⋃ j ∈ Finset.range J, A j)ᶜ) + ∑ j ∈ Finset.range J, P {ω | η / 2 < |Xj j ε ω - Yj j ω|} :=
        add_le_add le_rfl (measure_biUnion_finset_le _ _)
    _ ≤ e / 2 + e / 2 := add_le_add hcov.le hε
    _ = e := ENNReal.add_halves e

/-- **Pathwise comparison of integrals over `(0, a]`.** If two integrands are integrable on `Ioc 0 a` and
differ by at most `δ` there, their integrals differ by at most `δ a`. This is the bound applied to the
truncated occupation functionals of an environment-dependent test `f ω` and a deterministic test `g`,
whose integrands agree up to `δ` while the path stays in the ball. -/
theorem abs_setIntegral_sub_le_of_abs_le {F G : ℝ → ℝ} {a δ : ℝ} (ha : 0 ≤ a)
    (hF : IntegrableOn F (Ioc 0 a)) (hG : IntegrableOn G (Ioc 0 a))
    (h : ∀ t ∈ Ioc 0 a, |F t - G t| ≤ δ) :
    |(∫ t in Ioc 0 a, F t) - ∫ t in Ioc 0 a, G t| ≤ δ * a := by
  rw [← integral_sub hF hG, ← Real.norm_eq_abs]
  have hvol : volume (Ioc (0 : ℝ) a) < ⊤ := by
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top
  have h1 := norm_setIntegral_le_of_norm_le_const (C := δ) (f := fun t => F t - G t) hvol
    (fun t ht => by rw [Real.norm_eq_abs]; exact h t ht)
  rw [Real.volume_real_Ioc_of_le ha, sub_zero] at h1
  exact h1

end MatedCRT
