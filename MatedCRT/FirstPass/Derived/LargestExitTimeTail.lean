import MatedCRT.Proofs.Sec1.EnvironmentScaling.Field
import MatedCRT.Draft.Section2

/-!
# A tail of the largest exit-time variable `𝓜(B_ρ)` uniform over quantum-cone fields

`𝓜(D) = sup_{z ∈ D} ∫_D (log (1/|z - w|) + 1) dμ_h(w)` (`largestExitTimeRV`, eq:largest-exit-time-rv,
line 884) is monotone in `D`. When `𝓜(B_ρ)` is almost surely a fixed measurable functional `Ψ` of the
whole-plane observable process (all admissible pairings and positive-radius circle averages of the
field), its law is the same for every `γ`-quantum cone field, because the law of the observable process
is (`IsQuantumCone.observable_law_eq`). Together with the almost sure finiteness of `𝓜(B_ρ)`
(Lemma 2.17), this gives a tail bound `P(𝓜(B_ρ) > K) ≤ δ` with `K` independent of the cone field.

## Main results

* `MatedCRT.largestExitTimeRV_mono`: `𝓜` is monotone in the domain.
* `MatedCRT.IsQuantumCone.measurable_wholePlaneObservableProc`: the observable process of a quantum
  cone is measurable for the product σ-algebra.
* `MatedCRT.largestExitTimeRV_tail_uniform_of_factor`: the uniform tail bound, from a measurable
  factorization through the observable process and almost sure finiteness.
* `MatedCRT.largestExitTimeRV_ball_tail_uniform`: the same with the finiteness taken from Lemma 2.17.
-/

open MeasureTheory Set Metric Filter HarmonicBalls
open scoped ENNReal Topology

namespace MatedCRT

/-- **Monotonicity of `𝓜`.** If `D ⊆ D'` then `𝓜(D) ≤ 𝓜(D')`: the supremum runs over more points
and each integral over a larger domain. -/
theorem largestExitTimeRV_mono {μ : Measure ℂ} {D D' : Set ℂ} (h : D ⊆ D') :
    largestExitTimeRV μ D ≤ largestExitTimeRV μ D' :=
  iSup₂_le fun z hz => le_iSup₂_of_le (f := fun z (_ : z ∈ D') =>
    ∫⁻ w in D', ENNReal.ofReal (Real.log (1 / ‖z - w‖) + 1) ∂μ) z (h hz) (lintegral_mono_set h)

/-- The whole-plane observable process of a quantum cone (admissible pairings and positive-radius
circle averages) is measurable for the product σ-algebra. -/
theorem IsQuantumCone.measurable_wholePlaneObservableProc {Ω : Type*} [MeasurableSpace Ω] {γ : ℝ}
    {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsQuantumCone γ P hC hcirc) : Measurable (wholePlaneObservableProc hC hcirc) := by
  apply measurable_pi_iff.mpr
  rintro ⟨o, ho⟩
  cases o with
  | pairing φ => exact h.measurable_pairing φ ho
  | circle r z => exact h.measurable_circle r z ho

/-- **A tail of `𝓜(B_ρ)` uniform over quantum-cone fields.** Suppose that, for every `γ`-quantum cone
field, `𝓜(B_ρ)` is almost surely equal to `Ψ` of the observable process for one fixed measurable `Ψ`,
and is almost surely finite. Then for every `δ > 0` there is `K ≥ 0`, independent of the cone field,
with `P(𝓜(B_ρ) > K) ≤ δ`. -/
theorem largestExitTimeRV_tail_uniform_of_factor {γ ρ : ℝ}
    {Ψ : (GFFObservable.Admissible → ℝ) → ℝ≥0∞} (hΨ : Measurable Ψ)
    (hfac : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), IsConeField γ P hC hcirc μ →
      ∀ᵐ ω ∂P, largestExitTimeRV (μ ω) (ball 0 ρ) = Ψ (wholePlaneObservableProc hC hcirc ω))
    (hfin : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), IsConeField γ P hC hcirc μ →
      ∀ᵐ ω ∂P, largestExitTimeRV (μ ω) (ball 0 ρ) < ⊤)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), IsConeField γ P hC hcirc μ →
      P {ω | ENNReal.ofReal K < largestExitTimeRV (μ ω) (ball 0 ρ)} ≤ ENNReal.ofReal δ := by
  by_cases hex : ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), IsConeField γ P hC hcirc μ
  swap
  · exact ⟨0, le_rfl, fun Ω _ P hC hcirc μ hc => absurd ⟨Ω, _, P, hC, hcirc, μ, hc⟩ hex⟩
  obtain ⟨Ω₀, m₀, P₀, hC₀, hcirc₀, μ₀, hc₀⟩ := hex
  have := hc₀.1
  have hg₀ : Measurable (Ψ ∘ wholePlaneObservableProc hC₀ hcirc₀) :=
    hΨ.comp (IsQuantumCone.measurable_wholePlaneObservableProc hc₀.2.1)
  set ν : Measure ℝ≥0∞ := P₀.map (Ψ ∘ wholePlaneObservableProc hC₀ hcirc₀) with hν
  -- `ν` charges no mass at `⊤`
  have htop : ν {⊤} = 0 := by
    rw [hν, Measure.map_apply hg₀ (measurableSet_singleton ⊤), measure_eq_zero_iff_ae_notMem]
    filter_upwards [hfac Ω₀ P₀ hC₀ hcirc₀ μ₀ hc₀, hfin Ω₀ P₀ hC₀ hcirc₀ μ₀ hc₀] with ω h1 h2 h3
    rw [mem_preimage, Function.comp_apply, mem_singleton_iff, ← h1] at h3
    exact h2.ne h3
  have hinter : (⋂ n : ℕ, Ioi (n : ℝ≥0∞)) = {⊤} := by
    ext x
    simp only [mem_iInter, mem_Ioi, mem_singleton_iff]
    refine ⟨fun hx => ?_, fun hx n => hx ▸ ENNReal.natCast_lt_top n⟩
    by_contra hne
    obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hne
    exact lt_asymm (hx n) hn
  have htend : Tendsto (fun n : ℕ => ν (Ioi (n : ℝ≥0∞))) atTop (𝓝 0) := by
    have := tendsto_measure_iInter_atTop (μ := ν) (s := fun n : ℕ => Ioi (n : ℝ≥0∞))
      (fun n => measurableSet_Ioi.nullMeasurableSet)
      (fun m n hmn => Ioi_subset_Ioi (by exact_mod_cast hmn)) ⟨0, by rw [hν]; exact measure_ne_top _ _⟩
    rwa [hinter, htop] at this
  obtain ⟨n, hn⟩ := ((tendsto_order.1 htend).2 _ (ENNReal.ofReal_pos.2 hδ)).exists
  refine ⟨n, n.cast_nonneg, fun Ω _ P hC hcirc μ hc => ?_⟩
  have := hc.1
  have hg : Measurable (Ψ ∘ wholePlaneObservableProc hC hcirc) :=
    hΨ.comp (IsQuantumCone.measurable_wholePlaneObservableProc hc.2.1)
  have hlaw : P.map (Ψ ∘ wholePlaneObservableProc hC hcirc) = ν := by
    rw [hν, ← Measure.map_map hΨ (IsQuantumCone.measurable_wholePlaneObservableProc hc.2.1),
      ← Measure.map_map hΨ (IsQuantumCone.measurable_wholePlaneObservableProc hc₀.2.1),
      Sec1.IsQuantumCone.observable_law_eq hc.2.1 hc₀.2.1]
  have hset : {ω | ENNReal.ofReal n < largestExitTimeRV (μ ω) (ball 0 ρ)} =ᵐ[P]
      (Ψ ∘ wholePlaneObservableProc hC hcirc) ⁻¹' Ioi (n : ℝ≥0∞) := by
    refine eventuallyEqSet_iff.2 ?_
    filter_upwards [hfac Ω P hC hcirc μ hc] with ω hω
    simp only [mem_preimage, Function.comp_apply, mem_Ioi, hω, ENNReal.ofReal_natCast]
  rw [measure_congr hset, ← Measure.map_apply hg measurableSet_Ioi, hlaw]
  exact hn.le

/-- **A tail of `𝓜(B_ρ)` uniform over quantum-cone fields, from Lemma 2.17.** For `0 < ρ < 1`, given a
measurable factorization of `𝓜(B_ρ)` through the observable process, the almost sure finiteness of
Lemma 2.17 gives, for every `δ > 0`, a `K ≥ 0` independent of the cone field with
`P(𝓜(B_ρ) > K) ≤ δ`. -/
theorem largestExitTimeRV_ball_tail_uniform (h217 : BoundedExitTimeRVStmt) {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ψ : (GFFObservable.Admissible → ℝ) → ℝ≥0∞} (hΨ : Measurable Ψ)
    (hfac : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), IsConeField γ P hC hcirc μ →
      ∀ᵐ ω ∂P, largestExitTimeRV (μ ω) (ball 0 ρ) = Ψ (wholePlaneObservableProc hC hcirc ω))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), IsConeField γ P hC hcirc μ →
      P {ω | ENNReal.ofReal K < largestExitTimeRV (μ ω) (ball 0 ρ)} ≤ ENNReal.ofReal δ := by
  obtain ⟨q, -, h⟩ := h217 γ hγ hγ2
  refine largestExitTimeRV_tail_uniform_of_factor hΨ hfac (fun Ω _ P hC hcirc μ hc => ?_) hδ
  filter_upwards [(h ρ hρ hρ1 Ω P hC hcirc μ hc).1] with ω hω
  exact lt_of_le_of_lt (le_iSup₂ (f := fun (D : Set ℂ) (_ : D ⊆ ball (0 : ℂ) ρ) =>
    largestExitTimeRV (μ ω) D) (ball 0 ρ) le_rfl) hω

end MatedCRT
