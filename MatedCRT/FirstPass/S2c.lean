import MatedCRT.Proofs.Sec2.ConeFamilyMeasurable.StoppedClosure

/-! # FIRST PASS S2c: closure before the stopping time

`ConeHalfBallClosureInsideStep` (`Proofs/Sec2/ConeFamilyMeasurable/StoppedClosure.lean:18`) is reduced to the almost-sure
absence of two rational touching times, `ConeNoTwoTouchStep` (NEW; proved as `firstPass_noTwoTouch` in `FirstPass/S2d.lean`). The deterministic core,
`closure_inside_of_noTwoTouch`, follows the written argument.
No strict growth of harmonic balls is assumed. -/

namespace MatedCRT

open MeasureTheory Filter Set Metric HarmonicBalls

/-- A set `A` touches the half circle `∂B_{1/2}` when its closure meets it. For a stopped family `Λ_t ⊆ B_{1/2}`
(`IsStoppedAtHalfBall`), `sup_{x ∈ Λ_t} |x| = 1/2` if and only if `Λ_t` touches `∂B_{1/2}`, since the supremum is
attained on the compact closure. -/
def TouchesHalfCircle (A : Set ℂ) : Prop := ∃ x ∈ closure A, ‖x‖ = 1 / 2

/-- **NEW, FIRST PASS S2c; proved as `firstPass_noTwoTouch` (`FirstPass/S2d.lean`).** Almost surely, for every stopped cone family `{Λ_t}_{0<t<T}` (with the properties of
Lemma 2.4) and all rationals `0 < q₁ < q₂ < T`, the sets `Λ_{q₁}` and `Λ_{q₂}` do not both touch `∂B_{1/2}`.
Written argument (no prescribed plateau radius, Tonelli and scaling),
`:275-289` (excluded event on `B_{3/4}`, [HB] Lemma 5.8 and the obstacle characterization). Lean route:
`ConePrematureContactNullStep` (`Proofs/Sec4/Prop42Closure/HalfBallClosure.lean`) through
`coneNoTwoTouchStep_of_prematureContactNull` (`FirstPass/S2d.lean`). -/
def ConeNoTwoTouchStep : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), IsConeField γ P hC hcirc μ →
    ∀ᵐ ω ∂P, ∀ (T : ℝ) (Λ : ℝ → Set ℂ), IsConeHarmonicBallFamilyOn (μ ω) Λ T → IsStoppedAtHalfBall Λ T →
      ∀ q₁ q₂ : ℚ, 0 < (q₁ : ℝ) → (q₁ : ℝ) < q₂ → (q₂ : ℝ) < T →
        ¬ (TouchesHalfCircle (Λ (q₁ : ℝ)) ∧ TouchesHalfCircle (Λ (q₂ : ℝ)))

/-- **Deterministic core of the closure step** (written argument `prop42-proof.tex:291-304`). If `Λ` is stopped at `T`,
is monotone on `(0, T)`, `t ∈ (0, T)`, and no two rational times in `(t, T)` touch `∂B_{1/2}`, then
`closure (Λ t) ⊆ B_{1/2}`. Proof: if `closure (Λ t)` met `∂B_{1/2}` at `x`, monotonicity puts `x` in `closure (Λ s)`
for every `s ∈ (t, T)`, so every such `Λ s` touches `∂B_{1/2}`; two rationals in `(t, T)` then contradict the hypothesis. -/
theorem closure_inside_of_noTwoTouch {Λ : ℝ → Set ℂ} {T t : ℝ} (hs : IsStoppedAtHalfBall Λ T)
    (hmono : MonotoneOn Λ (Ioo 0 T)) (ht : t ∈ Ioo 0 T)
    (hno : ∀ q₁ q₂ : ℚ, 0 < (q₁ : ℝ) → (q₁ : ℝ) < q₂ → (q₂ : ℝ) < T →
      ¬ (TouchesHalfCircle (Λ (q₁ : ℝ)) ∧ TouchesHalfCircle (Λ (q₂ : ℝ)))) :
    closure (Λ t) ⊆ ball (0 : ℂ) (1 / 2) := by
  by_contra hnot
  have hcl_sub : closure (Λ t) ⊆ closedBall (0 : ℂ) (1 / 2) :=
    closure_minimal (fun x hx => ball_subset_closedBall (hs.1 t ht hx)) isClosed_closedBall
  obtain ⟨x, hx, hxn⟩ := Set.not_subset.mp hnot
  have hxr : ‖x‖ = 1 / 2 := by
    have h1 : ‖x‖ ≤ 1 / 2 := by
      have := hcl_sub hx
      rwa [mem_closedBall, dist_zero_right] at this
    have h2 : 1 / 2 ≤ ‖x‖ := by
      by_contra h
      exact hxn (by rw [mem_ball, dist_zero_right]; exact not_le.mp h)
    exact le_antisymm h1 h2
  have htT : t < T := ht.2
  have htouch : ∀ s ∈ Ioo t T, TouchesHalfCircle (Λ s) := by
    intro s hs'
    have hsT : s ∈ Ioo 0 T := ⟨ht.1.trans hs'.1, hs'.2⟩
    have hsub : Λ t ⊆ Λ s := hmono ht hsT hs'.1.le
    exact ⟨x, closure_mono hsub hx, hxr⟩
  obtain ⟨q₁, hq₁a, hq₁b⟩ := exists_rat_btwn (show t < (t + T) / 2 by linarith)
  obtain ⟨q₂, hq₂a, hq₂b⟩ := exists_rat_btwn (show (t + T) / 2 < T by linarith)
  have h0 : (0 : ℝ) < q₁ := ht.1.trans hq₁a
  have h12 : (q₁ : ℝ) < q₂ := hq₁b.trans hq₂a
  have h2 : (q₂ : ℝ) < T := hq₂b
  exact hno q₁ q₂ h0 h12 h2
    ⟨htouch (q₁ : ℝ) ⟨hq₁a, by linarith⟩, htouch (q₂ : ℝ) ⟨by linarith, h2⟩⟩

/-- **Closure step from the no-two-touch input.** `ConeHalfBallClosureInsideStep` follows from the NEW open step
`ConeNoTwoTouchStep`. Monotonicity of the family is the field `monotoneOn` of `SatisfiesHarmonicBallConditionsOn`
(`Harmonic-Balls-LQG/HarmonicBalls/Draft/Section5.lean:76`, condition (b) of Theorem 2.3). -/
theorem coneHalfBallClosureInsideStep_of_noTwoTouch (hno : ConeNoTwoTouchStep) :
    ConeHalfBallClosureInsideStep := by
  intro γ hγ hγ2 Ω _ P hC hcirc μ hcone
  filter_upwards [hno γ hγ hγ2 Ω P hC hcirc μ hcone] with ω hω
  intro T Λ hΛ hs t ht
  exact closure_inside_of_noTwoTouch hs hΛ.2.1.monotoneOn ht (hω T Λ hΛ hs)

end MatedCRT
