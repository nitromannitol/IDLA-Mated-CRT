import MatedCRT.FirstPass.Derived.LargestExitTimeFactor

/-!
# The exit time of the embedded walk from `B_{1/2}` is `O(ε⁻¹)`, uniformly in the starting vertex

Berestycki–Gwynne (2020), Proposition 5.1 with `N = 1` combined with Lemma 2.17 (the expected exit time bound
`Q^ε_D(a) ≤ C ε⁻¹ 𝓜(B_{ε^α}(D))` and the a.s. finiteness of `𝓜(B_ρ)`), in the form needed for the finite exit
of subsequential limits of the interpolated walk laws.  The statement is that of `mεCdf_upper_of_factor`
(`MepsUpperAssembly`) with the single starting vertex `vertexOf ε η 0` replaced by every vertex `k` with
`η(εk) ∈ B_{1/2}` simultaneously: with probability at least `1 - θ`, from every such start the embedded walk
exits `B_{1/2}` before step `K ε⁻¹` except with quenched probability at most `θ`.  The constant `K` depends on
`θ` and `γ` only, not on the environment.

* `exitTail_half_uniformStart`.
-/

open MeasureTheory Set Metric Filter HarmonicBalls
open scoped ENNReal Topology

namespace MatedCRT

/-- **Exit tail from `B_{1/2}`, uniform in the start.** -/
theorem exitTail_half_uniformStart {𝒮 : SpaceFillingSLEModel} (h214 : ExitTimeUpperBoundStmt 𝒮)
    (h217 : BoundedExitTimeRVStmt) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {θ : ℝ} (hθ : 0 < θ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        S.P {ω | ∃ k : ℤ, vertexPoint ε (S.η ω) k ∈ ball (0 : ℂ) (1 / 2) ∧
          ENNReal.ofReal θ < srwLaw (S.mult ε ω) k
            {x | ENNReal.ofReal (K * ε⁻¹) <
              (embeddedExitTime ε (S.η ω) (ball 0 (1 / 2)) x : ℝ≥0∞)}}
          ≤ ENNReal.ofReal θ := by
  obtain ⟨Ψ, hΨ, hfac⟩ := exists_measurable_largestExitTimeRV_ball_factor γ (3 / 4)
  obtain ⟨α, hα, h218'⟩ := h214 γ hγ hγ2
  obtain ⟨C, hC, h218''⟩ := h218' (3 / 4) (by norm_num) (by norm_num)
  obtain ⟨K₀, hK0, hK⟩ := largestExitTimeRV_ball_tail_uniform h217 hγ hγ2 (ρ := 3 / 4)
    (by norm_num) (by norm_num) hΨ hfac (δ := θ / 2) (by positivity)
  refine ⟨C * (K₀ + 1) / θ, by positivity, fun Ω _ S hS => ?_⟩
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
  have h4 : (0 : ℝ≥0∞) < ENNReal.ofReal (θ / 4) := ENNReal.ofReal_pos.2 (by positivity)
  have hev := (hT1.eventually (gt_mem_nhds h4)).and ((hT2.eventually (gt_mem_nhds h4)).and hpow)
  obtain ⟨ε₀, hε₀, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
  refine ⟨ε₀, hε₀, fun ε hε hεε₀ => ?_⟩
  obtain ⟨hE1, hE2, hεα⟩ := hsub ⟨hε, hεε₀⟩
  set s : ℝ≥0∞ := ENNReal.ofReal (C * (K₀ + 1) / θ * ε⁻¹) with hs
  have hs0 : s ≠ 0 := by
    rw [hs]
    exact (ENNReal.ofReal_pos.2 (by positivity)).ne'
  -- the good event
  set G : Set Ω := {ω | (∀ D : Set ℂ, D ⊆ ball 0 (3 / 4) → ∀ a ∈ cellVertices ε (S.η ω) D,
      expectedExitTime (S.mult ε ω) (interiorCellVertices ε (S.η ω) D) a ≤
        ENNReal.ofReal (C * ε⁻¹) * largestExitTimeRV (S.μ ω) (thickening (ε ^ α) D)) ∧
    (∀ k : ℤ, (cell ε (S.η ω) k ∩ ball 0 (5 / 8)).Nonempty → diam (cell ε (S.η ω) k) < 1 / 8) ∧
    largestExitTimeRV (S.μ ω) (ball 0 (3 / 4)) ≤ ENNReal.ofReal K₀ ∧
    IsAreaParametrized (S.μ ω) (S.η ω)} with hG
  -- on `G` no start in `B_{1/2}` has a long exit time
  have hpt : ∀ ω ∈ G, ∀ k : ℤ, vertexPoint ε (S.η ω) k ∈ ball (0 : ℂ) (1 / 2) →
      srwLaw (S.mult ε ω) k
        {x | s < (embeddedExitTime ε (S.η ω) (ball 0 (1 / 2)) x : ℝ≥0∞)} ≤ ENNReal.ofReal θ := by
    intro ω ⟨hQ, hd, hM, hpar⟩ k hk
    have hcont : Continuous (S.η ω) := hpar.1
    have hd' : ∀ k : ℤ, (cell ε (S.η ω) k ∩ ball 0 (5 / 8)).Nonempty →
        diam (cell ε (S.η ω) k) < 5 / 8 - 1 / 2 := fun k hk => by
      have := hd k hk
      linarith
    set A := interiorCellVertices ε (S.η ω) (ball 0 (5 / 8)) with hA
    have hsubA : {x : ℕ → ℤ | s < (embeddedExitTime ε (S.η ω) (ball 0 (1 / 2)) x : ℝ≥0∞)} ⊆
        {x | s < (vExitTime A x : ℝ≥0∞)} :=
      fun x (hx : s < (embeddedExitTime ε (S.η ω) (ball 0 (1 / 2)) x : ℝ≥0∞)) =>
      show s < (vExitTime A x : ℝ≥0∞) from lt_of_lt_of_le hx (ENat.toENNReal_le.mpr
        (embeddedExitTime_le_vExitTime hε.le hcont (by norm_num) hd' x))
    have ha0 : k ∈ cellVertices ε (S.η ω) (ball 0 (5 / 8)) :=
      ⟨vertexPoint ε (S.η ω) k, ⟨ε * k, ⟨mul_le_mul_of_nonneg_left (by linarith) hε.le, le_rfl⟩, rfl⟩,
        ball_subset_ball (by norm_num) hk⟩
    have hthick : thickening (ε ^ α) (ball (0 : ℂ) (5 / 8)) ⊆ ball 0 (3 / 4) :=
      (Metric.thickening_ball 0 _ _).trans (ball_subset_ball (by linarith))
    have hQ' : expectedExitTime (S.mult ε ω) A k ≤ ENNReal.ofReal (C * ε⁻¹ * K₀) := by
      refine (hQ (ball 0 (5 / 8)) (ball_subset_ball (by norm_num)) _ ha0).trans ?_
      rw [show ENNReal.ofReal (C * ε⁻¹ * K₀) = ENNReal.ofReal (C * ε⁻¹) * ENNReal.ofReal K₀ from
        ENNReal.ofReal_mul (by positivity)]
      exact mul_le_mul' le_rfl ((largestExitTimeRV_mono hthick).trans hM)
    have hdiv : expectedExitTime (S.mult ε ω) A k / s ≤ ENNReal.ofReal θ := by
      refine ENNReal.div_le_of_le_mul (hQ'.trans ?_)
      rw [hs, ← ENNReal.ofReal_mul hθ.le]
      refine ENNReal.ofReal_le_ofReal ?_
      have hCε : 0 ≤ C * ε⁻¹ := by positivity
      have : θ * (C * (K₀ + 1) / θ * ε⁻¹) = C * ε⁻¹ * K₀ + C * ε⁻¹ := by
        field_simp
      linarith
    exact (measure_mono hsubA).trans ((srwLaw_lt_vExitTime_le _ subset_rfl k hs0
      ENNReal.ofReal_ne_top).trans (by simpa [exitTimeMoment_one] using hdiv))
  -- the bad event is small
  have hGc : S.P Gᶜ ≤ ENNReal.ofReal θ := by
    have hpar0 : S.P {ω | ¬ IsAreaParametrized (S.μ ω) (S.η ω)} = 0 :=
      ae_iff.1 hS.isAreaParametrized
    have hcov : Gᶜ ⊆ (((E ε)ᶜ ∪ {ω | ∃ k : ℤ, (cell ε (S.η ω) k ∩ ball 0 (5 / 8)).Nonempty ∧
        1 / 8 ≤ diam (cell ε (S.η ω) k)}) ∪
        {ω | ENNReal.ofReal K₀ < largestExitTimeRV (S.μ ω) (ball 0 (3 / 4))}) ∪
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
      _ ≤ ENNReal.ofReal (θ / 4) + ENNReal.ofReal (θ / 4) + ENNReal.ofReal (θ / 2) + 0 :=
          add_le_add (add_le_add (add_le_add hE1.le hE2.le) hKS) hpar0.le
      _ = ENNReal.ofReal θ := by
          rw [add_zero, ← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          ring
  refine le_trans (measure_mono fun ω hω => ?_) hGc
  obtain ⟨k, hk, hlt⟩ := hω
  intro hωG
  exact absurd hlt (not_lt.2 (hpt ω hωG k hk))

end MatedCRT
