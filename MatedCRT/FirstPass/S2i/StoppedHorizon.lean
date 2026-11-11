import MatedCRT.Defs.Setting
import MatedCRT.Proofs.Sec2.ConeFamily

/-! # Uniqueness of stopped horizons

Two families for the same measure, both stopped at `∂B_{1/2}`
(`IsStoppedAtHalfBall`), have the same horizon, provided each has closure contained in `B_{1/2}` at every time before its
horizon (`ConeHalfBallClosureInsideStep`, a.s.). Proof: if `T₁ < T₂`, at a time `t' ∈ (T₁, T₂)` the compact set
`cl Λ₂_{t'}` lies in `B_{1/2}`, hence in a ball `B_r` with `r < 1/2`; by monotonicity and fixed-time uniqueness
`Λ₁_t ⊆ B_r` for every `t < T₁`, contradicting the stopping property of `Λ₁` at `T₁`. -/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric HarmonicBalls

/-- A stopped family cannot have a strictly shorter horizon than a family whose closures stay in `B_{1/2}`. -/
theorem isStopped_not_lt {μ : Measure ℂ} {T₁ T₂ : ℝ} {Λ₁ Λ₂ : ℝ → Set ℂ}
    (h₁ : IsConeHarmonicBallFamilyOn μ Λ₁ T₁) (s₁ : IsStoppedAtHalfBall Λ₁ T₁)
    (h₂ : IsConeHarmonicBallFamilyOn μ Λ₂ T₂)
    (hcl₂ : ∀ t ∈ Ioo 0 T₂, closure (Λ₂ t) ⊆ ball (0 : ℂ) (1 / 2)) (hlt : T₁ < T₂) : False := by
  set t' : ℝ := (T₁ + T₂) / 2 with ht'def
  have ht' : t' ∈ Ioo 0 T₂ := by
    obtain ⟨t₀, ht₀, -⟩ := s₁.2 0 (by norm_num)
    constructor
    · rw [ht'def]; linarith [ht₀.1, ht₀.2]
    · rw [ht'def]; linarith
  have hKc : IsCompact (closure (Λ₂ t')) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure (h₂.2.1.isBounded t' ht').closure
  have hKne : (closure (Λ₂ t')).Nonempty :=
    ⟨0, subset_closure (h₂.2.1.mem t' ht')⟩
  obtain ⟨z₀, hz₀K, hmax⟩ := hKc.exists_isMaxOn hKne continuous_norm.continuousOn
  have hz₀ : ‖z₀‖ < 1 / 2 := by
    have hball := hcl₂ t' ht' hz₀K
    rwa [mem_ball, dist_zero_right] at hball
  set r : ℝ := (‖z₀‖ + 1 / 2) / 2 with hrdef
  have hr : r < 1 / 2 := by rw [hrdef]; linarith
  have hsub : ∀ t ∈ Ioo 0 T₁, Λ₁ t ⊆ ball (0 : ℂ) r := by
    intro t ht z hz
    have htT₂ : t ∈ Ioo 0 T₂ := ⟨ht.1, ht.2.trans hlt⟩
    have hmin : t ∈ Ioo 0 (min T₁ T₂) := ⟨ht.1, by rw [min_eq_left hlt.le]; exact ht.2⟩
    have hEq : Λ₂ t = Λ₁ t := h₁.eqOn h₂ hmin
    have hz₂ : z ∈ Λ₂ t := by rw [hEq]; exact hz
    have hle : t ≤ t' := by rw [ht'def]; linarith [ht.2]
    have hmono : Λ₂ t ⊆ Λ₂ t' := h₂.2.1.monotoneOn htT₂ ht' hle
    have hzK : z ∈ closure (Λ₂ t') := subset_closure (hmono hz₂)
    have hnorm : ‖z‖ ≤ ‖z₀‖ := isMaxOn_iff.mp hmax z hzK
    rw [mem_ball, dist_zero_right]
    linarith
  obtain ⟨t, ht, hnot⟩ := s₁.2 r hr
  exact hnot (hsub t ht)

/-- Two stopped families with closures in `B_{1/2}` before their horizons have the same horizon. -/
theorem stopped_horizon_unique {μ : Measure ℂ} {T₁ T₂ : ℝ} {Λ₁ Λ₂ : ℝ → Set ℂ}
    (h₁ : IsConeHarmonicBallFamilyOn μ Λ₁ T₁) (s₁ : IsStoppedAtHalfBall Λ₁ T₁)
    (h₂ : IsConeHarmonicBallFamilyOn μ Λ₂ T₂) (s₂ : IsStoppedAtHalfBall Λ₂ T₂)
    (hcl₁ : ∀ t ∈ Ioo 0 T₁, closure (Λ₁ t) ⊆ ball (0 : ℂ) (1 / 2))
    (hcl₂ : ∀ t ∈ Ioo 0 T₂, closure (Λ₂ t) ⊆ ball (0 : ℂ) (1 / 2)) : T₁ = T₂ := by
  rcases lt_trichotomy T₁ T₂ with h | h | h
  · exact (isStopped_not_lt h₁ s₁ h₂ hcl₂ h).elim
  · exact h
  · exact (isStopped_not_lt h₂ s₂ h₁ hcl₁ h).elim

/-- Fixed-horizon families of the same measure have the same space-time process on `(0, T)`. -/
theorem familyProcess_eq_of_family {μ : Measure ℂ} {T : ℝ} {Λ₁ Λ₂ : ℝ → Set ℂ}
    (h₁ : IsConeHarmonicBallFamilyOn μ Λ₁ T) (h₂ : IsConeHarmonicBallFamilyOn μ Λ₂ T) :
    familyProcess Λ₁ T = familyProcess Λ₂ T := by
  have hE : EqOn Λ₂ Λ₁ (Ioo 0 T) := by
    have := h₁.eqOn h₂
    rwa [min_self] at this
  funext p
  obtain ⟨t, x⟩ := p
  apply propext
  simp only [familyProcess]
  constructor
  · rintro ⟨ht, hx⟩
    refine ⟨ht, ?_⟩
    rw [hE ht]
    exact hx
  · rintro ⟨ht, hx⟩
    refine ⟨ht, ?_⟩
    rw [hE ht] at hx
    exact hx

end MatedCRT
