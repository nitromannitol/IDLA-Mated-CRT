import MatedCRT.FirstPass.Derived.MepsUpperCellSize
import MatedCRT.FirstPass.Derived.MepsUpperDeterministic
import MatedCRT.FirstPass.Derived.CellSizeOfConeCouplingProd
import MatedCRT.FirstPass.Derived.LargestExitTimeTail
import MatedCRT.FirstPass.Derived.MepsScalingOfCdfBounds
import MatedCRT.FirstPass.S5c.BadEvents

/-!
# The upper half of the scaling of `m_ε`, from the expected exit time bound

The annealed exit-time distribution function `F_ε(s) = E[P^{h,η}(τ ≤ s)]` of the embedded walk from
`B_{1/2}` satisfies `F_ε(c₂ ε⁻¹) ≥ 1/2` for small `ε`, with `c₂` depending only on `γ`
(Berestycki-Gwynne arXiv:2003.10320 (1.8), upper half). The inputs are the expected exit time bound
`Q^ε_D(a) ≤ C ε⁻¹ 𝓜(B_{ε^α}(D))` (Lemma 2.18, second conjunct), the a.s. finiteness of `𝓜(B_ρ)`
(Lemma 2.17), the cell size estimate (Lemma 2.8) and a measurable factorization of `𝓜(B_{3/4})`
through the whole-plane observable process of the cone field, which makes the tail bound of
`𝓜(B_{3/4})` uniform over the environment.

Proof. Take `D = B_{5/8}`, `ρ = 3/4`, `K` with `P(𝓜(B_{3/4}) > K) ≤ 1/8` for every cone field and
`c₂ = 8 C (K + 1)`. For small `ε` the event `G_ε` on which the bound of Lemma 2.18 holds, every cell
meeting `B_{5/8}` has diameter `< 1/8`, `𝓜(B_{3/4}) ≤ K` and `η` is area-parametrized, has probability
at least `3/4`. On `G_ε` the embedded walk leaves `B_{1/2}` no later than it leaves the interior
vertices of `B_{5/8}`, the starting vertex `a^ε_0` is a vertex of `B_{5/8}`, and
`B_{ε^α}(B_{5/8}) ⊆ B_{3/4}`, so by Markov's inequality `P^{h,η}(τ ≤ c₂ ε⁻¹) ≥ 1 - C ε⁻¹ K / (c₂ ε⁻¹)
≥ 7/8`. Hence `F_ε(c₂ ε⁻¹) ≥ (7/8)(3/4) > 1/2`.

## Main results

* `exitTimeMoment_one`, `one_sub_div_le_srwLaw_vExitTime_le`: Markov's inequality for the exit time,
  in the form `1 - E_a[τ_B] / s ≤ P_a(τ_A ≤ s)` for `A ⊆ B`.
* `mεCdf_upper_of_factor`: `∃ c₂ > 0, ∀ valid S, ∃ ε₀ > 0, ∀ ε ∈ (0, ε₀), 1/2 ≤ F_ε(c₂ ε⁻¹)`.
-/

open MeasureTheory Set Metric Filter HarmonicBalls
open scoped ENNReal Topology

namespace MatedCRT

/-- The first exit-time moment is the expected exit time. -/
theorem exitTimeMoment_one (m : ℤ → ℤ → ℕ) (A : Set ℤ) (a : ℤ) :
    exitTimeMoment m A a 1 = expectedExitTime m A a := by
  simp [exitTimeMoment, expectedExitTime]

/-- **Markov's inequality for exit times, complement form.** For `A ⊆ B` and `0 < s < ∞`, the walk
started at `a` exits `A` by time `s` with probability at least `1 - E_a[τ_B] / s`. -/
theorem one_sub_div_le_srwLaw_vExitTime_le (m : ℤ → ℤ → ℕ) {A B : Set ℤ} (hAB : A ⊆ B) (a : ℤ)
    {s : ℝ≥0∞} (hs0 : s ≠ 0) (hs : s ≠ ∞) :
    1 - expectedExitTime m B a / s ≤ srwLaw m a {x | (vExitTime A x : ℝ≥0∞) ≤ s} := by
  have hmeas : MeasurableSet {x : ℕ → ℤ | s < (vExitTime A x : ℝ≥0∞)} :=
    measurableSet_lt measurable_const (Tightness.measurable_vExitTime_coe A)
  have hcompl : {x : ℕ → ℤ | (vExitTime A x : ℝ≥0∞) ≤ s} =
      {x | s < (vExitTime A x : ℝ≥0∞)}ᶜ := by
    ext x
    simp [not_lt]
  rw [hcompl, prob_compl_eq_one_sub hmeas, ← exitTimeMoment_one]
  exact tsub_le_tsub_left (srwLaw_lt_vExitTime_le m hAB a hs0 hs) 1

/-- **Upper half of eq:meps-scaling** (BG20 (1.8)): from Lemma 2.18, Lemma 2.17 and a measurable
factorization of `𝓜(B_{3/4})` through the whole-plane observable process, there is `c₂ = c₂(γ) > 0`
with `F_ε(c₂ ε⁻¹) ≥ 1/2` for all small `ε`, for every valid environment. -/
theorem mεCdf_upper_of_factor {𝒮 : SpaceFillingSLEModel} (h218 : ExitTimeUpperBoundStmt 𝒮)
    (h217 : BoundedExitTimeRVStmt) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ψ : (GFFObservable.Admissible → ℝ) → ℝ≥0∞} (hΨ : Measurable Ψ)
    (hfac : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), IsConeField γ P hC hcirc μ →
      ∀ᵐ ω ∂P, largestExitTimeRV (μ ω) (ball 0 (3 / 4)) = Ψ (wholePlaneObservableProc hC hcirc ω)) :
    ∃ c₂ : ℝ, 0 < c₂ ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → 1 / 2 ≤ S.mεCdf ε (c₂ * ε⁻¹) := by
  obtain ⟨α, hα, h218'⟩ := h218 γ hγ hγ2
  obtain ⟨C, hC, h218''⟩ := h218' (3 / 4) (by norm_num) (by norm_num)
  obtain ⟨K, hK0, hK⟩ := largestExitTimeRV_ball_tail_uniform h217 hγ hγ2 (ρ := 3 / 4)
    (by norm_num) (by norm_num) hΨ hfac (δ := 1 / 8) (by norm_num)
  refine ⟨8 * C * (K + 1), by positivity, fun Ω _ S hS => ?_⟩
  have : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  have hcone : IsConeField γ S.P S.hC S.hcirc S.μ :=
    ⟨hS.isProbabilityMeasure, hS.isQuantumCone, hS.isLQGMeasure⟩
  have hKS := hK Ω S.P S.hC S.hcirc S.μ hcone
  obtain ⟨E, hEpoly, hEsub⟩ : ∃ E : ℝ → Set Ω, PolyHighProb S.P E ∧ ∀ ε : ℝ, E ε ⊆
      {ω | ∀ D : Set ℂ, D ⊆ ball 0 (3 / 4) → ∀ a ∈ cellVertices ε (S.η ω) D,
        expectedExitTime (S.mult ε ω) (interiorCellVertices ε (S.η ω) D) a ≤
          ENNReal.ofReal (C * ε⁻¹) * largestExitTimeRV (S.μ ω) (thickening (ε ^ α) D)} :=
    ⟨_, h218'' Ω S hS, fun ε ω hω D hD a ha => (hω.2 D hD a ha).2⟩
  have hT1 := S5c.tendsto_compl_of_polyHighProb hEpoly
  have hT2 := cellDiam_bad_tendsto_zero_of_cellSizeEstimate
    (FirstPass.Derived.cellSizeEstimateStmt_holds 𝒮) hγ hγ2 S hS
  have hpow : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε ^ α < 1 / 8 := by
    have hc : Tendsto (fun ε : ℝ => ε ^ α) (𝓝 0) (𝓝 0) := by
      have := (Real.continuousAt_rpow_const 0 α (Or.inr hα.le)).tendsto
      simpa [Real.zero_rpow hα.ne'] using this
    exact (hc.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 8))).filter_mono
      nhdsWithin_le_nhds
  have h16 : (0 : ℝ≥0∞) < ENNReal.ofReal (1 / 16) := by simp
  have hev := (hT1.eventually (gt_mem_nhds h16)).and ((hT2.eventually (gt_mem_nhds h16)).and hpow)
  obtain ⟨ε₀, hε₀, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
  refine ⟨ε₀, hε₀, fun ε hε hεε₀ => ?_⟩
  obtain ⟨hE1, hE2, hεα⟩ := hsub ⟨hε, hεε₀⟩
  set s : ℝ≥0∞ := ENNReal.ofReal (8 * C * (K + 1) * ε⁻¹) with hs
  have hs0 : s ≠ 0 := by
    rw [hs]
    exact (ENNReal.ofReal_pos.2 (by positivity)).ne'
  -- the good event
  set G : Set Ω := {ω | (∀ D : Set ℂ, D ⊆ ball 0 (3 / 4) → ∀ a ∈ cellVertices ε (S.η ω) D,
      expectedExitTime (S.mult ε ω) (interiorCellVertices ε (S.η ω) D) a ≤
        ENNReal.ofReal (C * ε⁻¹) * largestExitTimeRV (S.μ ω) (thickening (ε ^ α) D)) ∧
    (∀ k : ℤ, (cell ε (S.η ω) k ∩ ball 0 (5 / 8)).Nonempty → diam (cell ε (S.η ω) k) < 1 / 8) ∧
    largestExitTimeRV (S.μ ω) (ball 0 (3 / 4)) ≤ ENNReal.ofReal K ∧
    IsAreaParametrized (S.μ ω) (S.η ω)} with hG
  -- the integrand is at least `7/8` on `G`
  have hpt : ∀ ω ∈ G, ENNReal.ofReal (7 / 8) ≤ srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) 0)
      {x | (embeddedExitTime ε (S.η ω) (ball 0 (1 / 2)) x : ℝ≥0∞) ≤ s} := by
    intro ω ⟨hQ, hd, hM, hpar⟩
    have hcont : Continuous (S.η ω) := hpar.1
    have h0 : S.η ω 0 = 0 := hpar.2.1
    have hd' : ∀ k : ℤ, (cell ε (S.η ω) k ∩ ball 0 (5 / 8)).Nonempty →
        diam (cell ε (S.η ω) k) < 5 / 8 - 1 / 2 := fun k hk => by
      have := hd k hk
      linarith
    set A := interiorCellVertices ε (S.η ω) (ball 0 (5 / 8)) with hA
    have hsubA : {x : ℕ → ℤ | (vExitTime A x : ℝ≥0∞) ≤ s} ⊆
        {x | (embeddedExitTime ε (S.η ω) (ball 0 (1 / 2)) x : ℝ≥0∞) ≤ s} :=
      fun x (hx : (vExitTime A x : ℝ≥0∞) ≤ s) =>
      show (embeddedExitTime ε (S.η ω) (ball 0 (1 / 2)) x : ℝ≥0∞) ≤ s from le_trans (ENat.toENNReal_le.mpr
        (embeddedExitTime_le_vExitTime hε.le hcont (by norm_num) hd' x)) hx
    have ha0 : vertexOf ε (S.η ω) 0 ∈ cellVertices ε (S.η ω) (ball 0 (5 / 8)) :=
      ⟨0, zero_mem_cell_vertexOf hε.le h0, by simp⟩
    have hthick : thickening (ε ^ α) (ball (0 : ℂ) (5 / 8)) ⊆ ball 0 (3 / 4) :=
      (Metric.thickening_ball 0 _ _).trans (ball_subset_ball (by linarith))
    have hQ' : expectedExitTime (S.mult ε ω) A (vertexOf ε (S.η ω) 0) ≤
        ENNReal.ofReal (C * ε⁻¹ * K) := by
      refine (hQ (ball 0 (5 / 8)) (ball_subset_ball (by norm_num)) _ ha0).trans ?_
      rw [show ENNReal.ofReal (C * ε⁻¹ * K) = ENNReal.ofReal (C * ε⁻¹) * ENNReal.ofReal K from
        ENNReal.ofReal_mul (by positivity)]
      exact mul_le_mul' le_rfl ((largestExitTimeRV_mono hthick).trans hM)
    have hdiv : expectedExitTime (S.mult ε ω) A (vertexOf ε (S.η ω) 0) / s ≤
        ENNReal.ofReal (1 / 8) := by
      refine ENNReal.div_le_of_le_mul (hQ'.trans ?_)
      rw [hs, ← ENNReal.ofReal_mul (by norm_num)]
      refine ENNReal.ofReal_le_ofReal ?_
      have hCε : 0 ≤ C * ε⁻¹ := by positivity
      have : 1 / 8 * (8 * C * (K + 1) * ε⁻¹) = C * ε⁻¹ * K + C * ε⁻¹ := by ring
      linarith
    have h78 : ENNReal.ofReal (7 / 8) = 1 - ENNReal.ofReal (1 / 8) := by
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by norm_num)]
      norm_num
    rw [h78]
    exact (tsub_le_tsub_left hdiv 1).trans
      ((one_sub_div_le_srwLaw_vExitTime_le _ subset_rfl _ hs0 ENNReal.ofReal_ne_top).trans
        (measure_mono hsubA))
  -- the bad event is small
  have hGc : S.P Gᶜ ≤ ENNReal.ofReal (1 / 4) := by
    have hpar0 : S.P {ω | ¬ IsAreaParametrized (S.μ ω) (S.η ω)} = 0 :=
      ae_iff.1 hS.isAreaParametrized
    have hcov : Gᶜ ⊆ (((E ε)ᶜ ∪ {ω | ∃ k : ℤ, (cell ε (S.η ω) k ∩ ball 0 (5 / 8)).Nonempty ∧
        1 / 8 ≤ diam (cell ε (S.η ω) k)}) ∪
        {ω | ENNReal.ofReal K < largestExitTimeRV (S.μ ω) (ball 0 (3 / 4))}) ∪
        {ω | ¬ IsAreaParametrized (S.μ ω) (S.η ω)} := by
      intro ω hω
      by_contra hn
      apply hω
      have h1 : ω ∈ E ε := not_not.1 fun h => hn (Or.inl (Or.inl (Or.inl h)))
      exact ⟨hEsub ε h1, fun k hk => lt_of_not_ge fun h => hn (Or.inl (Or.inl (Or.inr ⟨k, hk, h⟩))),
        not_lt.1 fun h => hn (Or.inl (Or.inr h)), not_not.1 fun h => hn (Or.inr h)⟩
    calc S.P Gᶜ ≤ _ := measure_mono hcov
      _ ≤ _ := (measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans
          (add_le_add (measure_union_le _ _) le_rfl)) le_rfl)
      _ ≤ ENNReal.ofReal (1 / 16) + ENNReal.ofReal (1 / 16) + ENNReal.ofReal (1 / 8) + 0 :=
          add_le_add (add_le_add (add_le_add hE1.le hE2.le) hKS) hpar0.le
      _ = ENNReal.ofReal (1 / 4) := by
          rw [add_zero, ← ENNReal.ofReal_add (by norm_num) (by norm_num),
            ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
          norm_num
  have hG' : MeasurableSet (toMeasurable S.P Gᶜ)ᶜ := (measurableSet_toMeasurable _ _).compl
  have hG'sub : (toMeasurable S.P Gᶜ)ᶜ ⊆ G := fun ω hω =>
    not_not.1 fun h => hω (subset_toMeasurable S.P Gᶜ h)
  have hPG' : ENNReal.ofReal (3 / 4) ≤ S.P (toMeasurable S.P Gᶜ)ᶜ := by
    rw [prob_compl_eq_one_sub (measurableSet_toMeasurable _ _), measure_toMeasurable]
    calc ENNReal.ofReal (3 / 4) = 1 - ENNReal.ofReal (1 / 4) := by
          rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by norm_num)]
          norm_num
      _ ≤ 1 - S.P Gᶜ := tsub_le_tsub_left hGc 1
  have hhalf : (1 / 2 : ℝ≥0∞) = ENNReal.ofReal (1 / 2) := by
    rw [ENNReal.ofReal_div_of_pos two_pos]
    simp
  unfold MatedCRTEnv.mεCdf
  calc (1 / 2 : ℝ≥0∞) ≤ ENNReal.ofReal (7 / 8) * ENNReal.ofReal (3 / 4) := by
        rw [← ENNReal.ofReal_mul (by norm_num), hhalf]
        exact ENNReal.ofReal_le_ofReal (by norm_num)
    _ ≤ ENNReal.ofReal (7 / 8) * S.P (toMeasurable S.P Gᶜ)ᶜ := mul_le_mul' le_rfl hPG'
    _ = ∫⁻ ω, (toMeasurable S.P Gᶜ)ᶜ.indicator (fun _ => ENNReal.ofReal (7 / 8)) ω ∂S.P :=
        (lintegral_indicator_const hG' _).symm
    _ ≤ _ := lintegral_mono fun ω =>
        Set.indicator_le' (fun ω hω => hpt ω (hG'sub hω)) (fun _ _ => zero_le) ω

end MatedCRT
