import MatedCRT.Steps.Sec1.Convergence
import MatedCRT.Proofs.Sec2.ConeScaleInvarianceUpToFixedTime.Obstacle

/-!
# Scaling covariance of the cone harmonic ball families (Theorem 2.3 conditions; lines 3286-3293)

`harmonicBallFamilyScalingStep` proves `HarmonicBallFamilyScalingStep`: if `{Λ_t}_{t > 0}` satisfies the conditions
(a)-(c) of Theorem 2.3 for `μ`, then `{R⁻¹ Λ_{bt}}_{t > 0}` satisfies them for `rescaledMeasure μ R b = b⁻¹ μ(R ·)`.

The conditions on a time interval `(0, T)` scale by the lemmas of Lemma 2.5 (`IsHarmonicBall.rescale`,
`SatisfiesHarmonicBallConditionsOn.rescale`, `SatisfiesObstacleCharacterizationOn.rescale`); this file passes between
the conditions on `(0, ∞)` and the conditions on every `(0, T)`.
-/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric HarmonicBalls

namespace Sec1

variable {μ : Measure ℂ} {Λ : ℝ → Set ℂ} {z : ℂ}

/-- The harmonic ball conditions on `(0, ∞)` give those on `(0, T)`. -/
theorem satisfiesHarmonicBallConditionsOn_of_global (h : SatisfiesHarmonicBallConditions μ Λ z) {T : ℝ}
    (hT : 0 < T) : SatisfiesHarmonicBallConditionsOn μ Λ z T where
  measure_eq t ht := h.measure_eq t ht.1
  measure_frontier t ht := h.measure_frontier t ht.1
  isRegularOpen t ht := h.isRegularOpen t ht.1
  isBounded t ht := h.isBounded t ht.1
  isConnected t ht := h.isConnected t ht.1
  mem t ht := h.mem t ht.1
  monotoneOn := h.monotoneOn.mono Ioo_subset_Ioi_self
  hausdorffContinuousOn t ht ε hε :=
    (h.hausdorffContinuousOn t ht.1 ε hε).filter_mono (nhdsWithin_mono t Ioo_subset_Ioi_self)
  iInter_eq := by
    refine Subset.antisymm (fun x hx => ?_) (fun x hx => ?_)
    · rw [← h.iInter_eq]
      simp only [mem_iInter] at hx ⊢
      intro t ht
      rcases lt_or_ge t T with htT | hTt
      · exact hx t ⟨ht, htT⟩
      · have hT2 : T / 2 ∈ Ioi (0 : ℝ) := half_pos hT
        exact h.monotoneOn hT2 ht (by linarith) (hx (T / 2) ⟨half_pos hT, half_lt_self hT⟩)
    · rw [mem_singleton_iff] at hx
      subst hx
      simp only [mem_iInter]
      exact fun t ht => h.mem t ht.1

/-- The harmonic ball conditions on every `(0, T)` give those on `(0, ∞)`. -/
theorem satisfiesHarmonicBallConditions_of_forall_on
    (h : ∀ T : ℝ, 0 < T → SatisfiesHarmonicBallConditionsOn μ Λ z T) : SatisfiesHarmonicBallConditions μ Λ z where
  measure_eq t ht := (h (t + 1) (by linarith)).measure_eq t ⟨ht, lt_add_one t⟩
  measure_frontier t ht := (h (t + 1) (by linarith)).measure_frontier t ⟨ht, lt_add_one t⟩
  isRegularOpen t ht := (h (t + 1) (by linarith)).isRegularOpen t ⟨ht, lt_add_one t⟩
  isBounded t ht := (h (t + 1) (by linarith)).isBounded t ⟨ht, lt_add_one t⟩
  isConnected t ht := (h (t + 1) (by linarith)).isConnected t ⟨ht, lt_add_one t⟩
  mem t ht := (h (t + 1) (by linarith)).mem t ⟨ht, lt_add_one t⟩
  monotoneOn s hs t ht hst := by
    have hs' : (0 : ℝ) < s := hs
    have ht' : (0 : ℝ) < t := ht
    exact (h (t + 1) (by linarith)).monotoneOn ⟨hs', by linarith⟩ ⟨ht', lt_add_one t⟩ hst
  hausdorffContinuousOn t ht ε hε := by
    have ht' : (0 : ℝ) < t := ht
    have h1 := (h (t + 1) (by linarith)).hausdorffContinuousOn t ⟨ht', lt_add_one t⟩ ε hε
    rw [nhdsWithin_eq_nhds.2 (Ioo_mem_nhds ht' (lt_add_one t))] at h1
    rwa [nhdsWithin_eq_nhds.2 (Ioi_mem_nhds ht')]
  iInter_eq := by
    have h1 := (h 1 one_pos).iInter_eq
    refine Subset.antisymm (fun x hx => ?_) (fun x hx => ?_)
    · rw [← h1]
      simp only [mem_iInter] at hx ⊢
      exact fun t ht => hx t ht.1
    · rw [mem_singleton_iff] at hx
      subst hx
      simp only [mem_iInter]
      intro t ht
      have ht' : (0 : ℝ) < t := ht
      exact (h (t + 1) (by linarith)).mem t ⟨ht', lt_add_one t⟩

/-- The obstacle characterization on `(0, ∞)` gives that on `(0, T)`. -/
theorem satisfiesObstacleCharacterizationOn_of_global (h : SatisfiesObstacleCharacterization μ Λ) (T : ℝ) :
    SatisfiesObstacleCharacterizationOn μ Λ T :=
  fun t r ht => h t r ht.1

/-- The obstacle characterization on every `(0, T)` gives that on `(0, ∞)`. -/
theorem satisfiesObstacleCharacterization_of_forall_on
    (h : ∀ T : ℝ, 0 < T → SatisfiesObstacleCharacterizationOn μ Λ T) : SatisfiesObstacleCharacterization μ Λ :=
  fun t r ht => h (t + 1) (by linarith) t r ⟨ht, lt_add_one t⟩

/-- A family of harmonic balls of Theorem 2.3 on `(0, ∞)` is one on every `(0, T)`. -/
theorem isConeHarmonicBallFamilyOn_of_global (h : IsConeHarmonicBallFamily μ Λ) {T : ℝ} (hT : 0 < T) :
    IsConeHarmonicBallFamilyOn μ Λ T :=
  ⟨fun t ht => h.1 t ht.1, satisfiesHarmonicBallConditionsOn_of_global h.2.1 hT,
    satisfiesObstacleCharacterizationOn_of_global h.2.2 T⟩

end Sec1

/-- **Scaling covariance of the harmonic balls of Theorem 2.3** (`HarmonicBallFamilyScalingStep`): if `{Λ_t}`
satisfies the conditions of Theorem 2.3 for `μ`, then `{R⁻¹ Λ_{bt}}` satisfies them for `b⁻¹ μ(R ·)`. -/
theorem harmonicBallFamilyScalingStep : HarmonicBallFamilyScalingStep := by
  intro μ Λ R b hR hb hΛ
  refine ⟨fun t ht => ?_, Sec1.satisfiesHarmonicBallConditions_of_forall_on fun T hT => ?_,
    Sec1.satisfiesObstacleCharacterization_of_forall_on fun T _ => ?_⟩
  · exact IsHarmonicBall.rescale (hΛ.1 (b * t) (mul_pos hb ht)) hR hb
  · exact SatisfiesHarmonicBallConditionsOn.rescale
      (Sec1.satisfiesHarmonicBallConditionsOn_of_global hΛ.2.1 (mul_pos hb hT)) hR hb
  · exact SatisfiesObstacleCharacterizationOn.rescale
      (Sec1.satisfiesObstacleCharacterizationOn_of_global hΛ.2.2 (b * T)) hR hb

end MatedCRT
