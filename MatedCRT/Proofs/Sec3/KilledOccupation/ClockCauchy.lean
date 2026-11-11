import MatedCRT.Proofs.Sec3.KilledOccupation.ClockIdentificationConcrete

/-!
# Two-parameter Cauchy bound for the regularized clock

Step B2 of the MQ-li-8 (b) argument (transfer of thm:occ-main to the cone). The regularized clocks `φ_ε` and `φ_ε'`
(`regClock`) are compared through the Brownian-weighted clock: with `ennDist` the extended distance
`|a - b| = (a - b) + (b - a)` on `ℝ≥0∞`, the sup-distance `clockDistPair ε ε' = sup_s |φ_ε(s) - φ_ε'(s)|` satisfies
`clockDistPair ε ε' ≤ clockDistD ε + clockDistD ε'` (`clockDistPair_le`, triangle inequality). Hence convergence in
measure of `clockDistD` as `ε → 0` gives convergence in measure of `clockDistPair` as `(ε, ε') → (0, 0)` along
`𝓝[>] 0 ×ˢ 𝓝[>] 0` (`tendsto_clockDistPair_of_clockDistD`). This is the Cauchy property used to choose a
deterministic subsequence in the Borel-Cantelli step B2.
-/

open MeasureTheory Set Filter Topology MarkovProcess
open scoped ENNReal NNReal

namespace MatedCRT.KilledOccupation

/-- Symmetry of the extended distance `ennDist a b = (a - b) + (b - a)`. -/
lemma ennDist_swap (a b : ℝ≥0∞) : ennDist a b = ennDist b a := by
  unfold ennDist
  exact add_comm _ _

/-- Triangle inequality for the extended distance `ennDist a b = (a - b) + (b - a)` on `ℝ≥0∞`. -/
lemma ennDist_triangle (a b c : ℝ≥0∞) : ennDist a c ≤ ennDist a b + ennDist b c := by
  unfold ennDist
  have h1 : a - c ≤ (a - b) + (b - c) := by
    rw [tsub_le_iff_right]
    calc a ≤ (a - b) + b := le_tsub_add
      _ ≤ (a - b) + ((b - c) + c) := add_le_add le_rfl le_tsub_add
      _ = (a - b) + (b - c) + c := (add_assoc _ _ _).symm
  have h2 : c - a ≤ (c - b) + (b - a) := by
    rw [tsub_le_iff_right]
    calc c ≤ (c - b) + b := le_tsub_add
      _ ≤ (c - b) + ((b - a) + a) := add_le_add le_rfl le_tsub_add
      _ = (c - b) + (b - a) + a := (add_assoc _ _ _).symm
  calc (a - c) + (c - a) ≤ ((a - b) + (b - c)) + ((c - b) + (b - a)) := add_le_add h1 h2
    _ = ((a - b) + (b - a)) + ((b - c) + (c - b)) := by ring

/-- The sup-distance `sup_s |φ_ε(s) - φ_ε'(s)|` between two regularized clocks on the same path (extended distance
`ennDist`): the Cauchy quantity in the two regularization parameters `ε, ε'`. -/
noncomputable def clockDistPair {Ω : Type*} (γ : ℝ) (hc : Ω → ℝ → ℂ → ℝ) (σ : ContinuousPath ℂ → ℝ≥0) (ε ε' : ℝ)
    (x : Ω × ContinuousPath ℂ) : ℝ≥0∞ :=
  ⨆ s : ℝ≥0, ennDist (regClock γ ε (hc x.1) (σ x.2) ⇑x.2 s) (regClock γ ε' (hc x.1) (σ x.2) ⇑x.2 s)

/-- Triangle inequality through the Brownian-weighted clock: `clockDistPair ε ε' ≤ clockDistD ε + clockDistD ε'`. -/
theorem clockDistPair_le {Ω : Type*} (γ : ℝ) (hc : Ω → ℝ → ℂ → ℝ)
    (dA : Ω → ContinuousPath ℂ → Measure ℝ≥0) (σ : ContinuousPath ℂ → ℝ≥0) (ε ε' : ℝ)
    (x : Ω × ContinuousPath ℂ) :
    clockDistPair γ hc σ ε ε' x ≤ clockDistD γ hc dA σ ε x + clockDistD γ hc dA σ ε' x := by
  refine iSup_le fun s => ?_
  refine (ennDist_triangle _
    (weightedClock (dA x.1 x.2) (fun u => gammaWeight γ (x.2 u)) (σ x.2) s) _).trans (add_le_add ?_ ?_)
  · exact le_iSup (fun s : ℝ≥0 => ennDist (regClock γ ε (hc x.1) (σ x.2) ⇑x.2 s)
      (weightedClock (dA x.1 x.2) (fun u => gammaWeight γ (x.2 u)) (σ x.2) s)) s
  · rw [ennDist_swap]
    exact le_iSup (fun s : ℝ≥0 => ennDist (regClock γ ε' (hc x.1) (σ x.2) ⇑x.2 s)
      (weightedClock (dA x.1 x.2) (fun u => gammaWeight γ (x.2 u)) (σ x.2) s)) s

/-- If `ofReal η < a + b` in `ℝ≥0∞`, then `ofReal (η/2) < a` or `ofReal (η/2) < b`. -/
lemma ofReal_half_lt_of_ofReal_lt_add {η : ℝ} (hη : 0 < η) {a b : ℝ≥0∞}
    (h : ENNReal.ofReal η < a + b) :
    ENNReal.ofReal (η / 2) < a ∨ ENNReal.ofReal (η / 2) < b := by
  by_contra hcon
  have ha : a ≤ ENNReal.ofReal (η / 2) := not_lt.1 fun h' => hcon (Or.inl h')
  have hb : b ≤ ENNReal.ofReal (η / 2) := not_lt.1 fun h' => hcon (Or.inr h')
  have hsum : a + b ≤ ENNReal.ofReal η := by
    calc a + b ≤ ENNReal.ofReal (η / 2) + ENNReal.ofReal (η / 2) := add_le_add ha hb
      _ = ENNReal.ofReal (η / 2 + η / 2) := (ENNReal.ofReal_add (by linarith) (by linarith)).symm
      _ = ENNReal.ofReal η := by congr 1; ring
  exact absurd h (not_lt.2 hsum)

/-- Convergence in measure of the two-parameter sup-distance: if `clockDistD ε` tends to `0` in measure as
`ε → 0+` for every positive threshold, then `clockDistPair ε ε'` tends to `0` in measure as `(ε, ε') → (0+, 0+)`. -/
theorem tendsto_clockDistPair_of_clockDistD {Ω : Type*} [MeasurableSpace Ω] (γ : ℝ) (hc : Ω → ℝ → ℂ → ℝ)
    (dA : Ω → ContinuousPath ℂ → Measure ℝ≥0) (σ : ContinuousPath ℂ → ℝ≥0)
    {μ : Measure (Ω × ContinuousPath ℂ)}
    (h : ∀ η : ℝ, 0 < η →
      Tendsto (fun ε => μ {x | ENNReal.ofReal η < clockDistD γ hc dA σ ε x}) (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    ∀ η : ℝ, 0 < η →
      Tendsto (fun p : ℝ × ℝ => μ {x | ENNReal.ofReal η < clockDistPair γ hc σ p.1 p.2 x})
        (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 0) := by
  intro η hη
  have hA := h (η / 2) (half_pos hη)
  have hsum : Tendsto (fun p : ℝ × ℝ =>
      μ {x | ENNReal.ofReal (η / 2) < clockDistD γ hc dA σ p.1 x} +
        μ {x | ENNReal.ofReal (η / 2) < clockDistD γ hc dA σ p.2 x})
      (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hT := (hA.comp Filter.tendsto_fst).add (hA.comp Filter.tendsto_snd)
    rw [add_zero] at hT
    exact hT
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum ?_ ?_
  · exact fun p => zero_le
  · intro p
    refine (measure_mono ?_).trans (measure_union_le _ _)
    intro x hx
    have hx' : ENNReal.ofReal η < clockDistPair γ hc σ p.1 p.2 x := hx
    have hlt := lt_of_lt_of_le hx' (clockDistPair_le γ hc dA σ p.1 p.2 x)
    rcases ofReal_half_lt_of_ofReal_lt_add hη hlt with h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1

end MatedCRT.KilledOccupation
