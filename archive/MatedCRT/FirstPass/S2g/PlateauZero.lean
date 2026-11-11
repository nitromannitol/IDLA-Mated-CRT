import MatedCRT.FirstPass.S2g.Family

/-!
# Plateau radii and the zero law at a fixed radius

Measure-theoretic part of the zero cone law: the plateau radii of one
measure are countable, the Tonelli identity over the radius, and the scaling argument that makes the
probability of "r is a plateau radius" constant in `r` and therefore zero at every radius.

Not proved here, and passed as explicit hypotheses of `plateau_fixed_radius_null`: the measurability of the plateau
event in `Ω × ℝ` (a Borel-code statement, Sections 1-3 and 5.1 of the note) and the scale covariance of the plateau
event under the law of the cone field (equations (41)-(44) of the note).
-/

namespace MatedCRT

open MeasureTheory Set Metric HarmonicBalls
open scoped ENNReal

/-- The raw radius `r_{ν,N}(p)` of the cluster of `ν` in `B_N` at time `p` with pole `0`:
the supremum of `|x|` over the closure of the HB cluster `cluster ν N 0 p`. -/
noncomputable def rawRadius (ν : Measure ℂ) (N : ℕ) (p : ℝ) : ℝ :=
  sSup ((fun x : ℂ => ‖x‖) '' closure (cluster ν (N : ℝ) 0 p))

/-- The plateau radii of `ν`: radii `r < N` at which the raw radii of the disc `B_N`
take the value `r` at two rational times `0 < p < q`. -/
def plateauRadii (ν : Measure ℂ) : Set ℝ :=
  {r | ∃ N : ℕ, 0 < N ∧ ∃ p q : ℚ, 0 < (p : ℝ) ∧ (p : ℝ) < (q : ℝ) ∧ r < (N : ℝ) ∧
    rawRadius ν N p = r ∧ rawRadius ν N q = r}

/-- The plateau radii of one measure are countable: they lie in the range of the countable family
`(N, p) ↦ rawRadius ν N p`, `N ∈ ℕ`, `p ∈ ℚ`. -/
theorem plateauRadii_countable (ν : Measure ℂ) : (plateauRadii ν).Countable := by
  refine Set.Countable.mono ?_ (Set.countable_range (fun q : ℕ × ℚ => rawRadius ν q.1 (q.2 : ℝ)))
  rintro r ⟨N, _, p, _, _, _, _, hr, _⟩
  exact ⟨(N, p), hr⟩

/-- Tonelli over the radius with countable sections: if every section
`{r | (ω, r) ∈ E}` is countable, then `∫_{(1,2)} P{ω | (ω, r) ∈ E} dr = 0`. -/
theorem lintegral_plateau_sections_eq_zero {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    {E : Set (Ω × ℝ)} (hE : MeasurableSet E) (hcount : ∀ ω : Ω, {r : ℝ | (ω, r) ∈ E}.Countable) :
    ∫⁻ r in Ioo (1 : ℝ) 2, P {ω | (ω, r) ∈ E} = 0 := by
  have hsec : ∀ r : ℝ, P {ω | (ω, r) ∈ E} = ∫⁻ ω, E.indicator (1 : Ω × ℝ → ℝ≥0∞) (ω, r) ∂P := by
    intro r
    have hs : MeasurableSet {ω : Ω | (ω, r) ∈ E} := hE.preimage (measurable_id.prodMk measurable_const)
    rw [← lintegral_indicator_one hs]
    congr 1
  have hmeas : Measurable (fun q : ℝ × Ω => E.indicator (1 : Ω × ℝ → ℝ≥0∞) (q.2, q.1)) :=
    (measurable_one.indicator hE).comp (measurable_snd.prodMk measurable_fst)
  calc ∫⁻ r in Ioo (1 : ℝ) 2, P {ω | (ω, r) ∈ E}
      = ∫⁻ r in Ioo (1 : ℝ) 2, ∫⁻ ω, E.indicator (1 : Ω × ℝ → ℝ≥0∞) (ω, r) ∂P :=
        lintegral_congr fun r => hsec r
    _ = ∫⁻ ω, (∫⁻ r in Ioo (1 : ℝ) 2, E.indicator (1 : Ω × ℝ → ℝ≥0∞) (ω, r)) ∂P := by
        refine lintegral_lintegral_swap ?_
        exact hmeas.aemeasurable
    _ = ∫⁻ _ : Ω, (0 : ℝ≥0∞) ∂P := by
        refine lintegral_congr fun ω => ?_
        have hind : (fun r : ℝ => E.indicator (1 : Ω × ℝ → ℝ≥0∞) (ω, r)) =
            {r : ℝ | (ω, r) ∈ E}.indicator (1 : ℝ → ℝ≥0∞) := by
          ext r
          rfl
        rw [hind, lintegral_indicator_one (hcount ω).measurableSet, Measure.restrict_apply
          (hcount ω).measurableSet]
        exact measure_mono_null Set.inter_subset_left ((hcount ω).measure_zero volume)
    _ = 0 := by simp

/-- A probability which is constant in the radius and integrates to zero over `(1, 2)` vanishes at every positive radius. -/
theorem eq_zero_of_scale_invariant {f : ℝ → ℝ≥0∞} (hscale : ∀ s r : ℝ, 0 < s → 0 < r → f (s * r) = f r)
    (hint : ∫⁻ r in Ioo (1 : ℝ) 2, f r = 0) : ∀ r : ℝ, 0 < r → f r = 0 := by
  have hconst : ∀ r : ℝ, 0 < r → f r = f 1 := fun r hr => by
    simpa using hscale r 1 hr one_pos
  have hset : ∫⁻ r in Ioo (1 : ℝ) 2, f r = ∫⁻ _ in Ioo (1 : ℝ) 2, f 1 :=
    setLIntegral_congr_fun measurableSet_Ioo fun r hr => hconst r (lt_trans zero_lt_one hr.1)
  have hf1 : f 1 = 0 := by
    rw [hset, setLIntegral_const, Real.volume_Ioo] at hint
    norm_num at hint
    exact hint
  intro r hr
  rw [hconst r hr, hf1]

/-- The zero law at a fixed radius for a family of probabilities: if the plateau event is jointly measurable and
countable in the radius for each `ω`, and its probability is invariant under the scalings `r ↦ s r`, then it has
probability zero at every positive radius. -/
theorem plateau_prob_eq_zero {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    {E : Set (Ω × ℝ)} (hE : MeasurableSet E) (hcount : ∀ ω : Ω, {r : ℝ | (ω, r) ∈ E}.Countable)
    (hscale : ∀ s r : ℝ, 0 < s → 0 < r → P {ω | (ω, s * r) ∈ E} = P {ω | (ω, r) ∈ E}) :
    ∀ r : ℝ, 0 < r → P {ω | (ω, r) ∈ E} = 0 :=
  eq_zero_of_scale_invariant hscale (lintegral_plateau_sections_eq_zero P hE hcount)

/-- The zero law for the cone plateau event. The two hypotheses are the open inputs of the note: `hmeas` is the
measurability of the plateau event in `Ω × ℝ` (Borel code); `hscale` is the scale
covariance of the law of the field under `r ↦ s r`. With these, every fixed positive radius is a
plateau radius with probability zero. -/
theorem plateau_fixed_radius_null {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (μ : Ω → Measure ℂ)
    (hmeas : MeasurableSet {q : Ω × ℝ | q.2 ∈ plateauRadii (μ q.1)})
    (hscale : ∀ s r : ℝ, 0 < s → 0 < r →
      P {ω | s * r ∈ plateauRadii (μ ω)} = P {ω | r ∈ plateauRadii (μ ω)}) :
    ∀ r : ℝ, 0 < r → P {ω | r ∈ plateauRadii (μ ω)} = 0 :=
  plateau_prob_eq_zero P hmeas (fun ω => plateauRadii_countable (μ ω)) hscale

end MatedCRT
