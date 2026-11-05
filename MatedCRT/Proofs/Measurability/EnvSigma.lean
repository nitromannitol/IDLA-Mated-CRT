import MatedCRT.Proofs.Sec5.IDLALowerBound.Statement
import MatedCRT.Proofs.Measurability.EnvSigmaCore

/-!
# The environment is a random variable up to null sets (ESCALATIONS E-c2-1)

`EnvSigmaMeasurableStep 𝒮` (`σ(h, η) ≤ 𝓕`, MatedCRT/Steps/Sec5/GeneralIDLALowerBound.lean) does not follow from
`MatedCRTEnv.IsValid`: the curve `η` is only almost surely equal to the measurable curve `η'` of the mating-of-trees
coupling (`IsMatingOfTreesCoupling.measurable_curves`, and `∀ᵐ ω, η' ω = S.η ω` in `IsValid.matingOfTrees`), so the
point evaluations `ω ↦ η(ω, s)` are only `P`-null-measurable, and changing `η` on a non-measurable subset of a
`P`-null set preserves validity. What does follow is that every `σ(h, η)`-measurable set is `P`-null-measurable
(`MatedCRTEnv.IsValid.envSigma_le_nullMeasurableSpace`), and this is all that the proof of Lemma 5.2 uses: the events
`{𝔰 < δ}` are null-measurable, so that `P[𝔰 < δ] → 0` as `δ → 0` (`tendsto_outerLIntegral_of_eventually_le₀`).

Lemma 5.2 in its relaxed form (`generalIDLALowerBoundRelaxed_of_steps₀`), Lemma 5.2 itself
(`generalIDLALowerBound_of_volumeGrowth_cellSize`: from Lemmas 2.7 and 2.8 only) and Proposition 5.1
(`iDLALowerBound_of_volumeGrowth_cellSize`) follow without `EnvSigmaMeasurableStep`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Metric HarmonicBalls
open scoped ENNReal NNReal

namespace MatedCRT

/-- `tendsto_outerLIntegral_of_eventually_le` for an almost everywhere measurable `𝔰 > 0`: if `f ε ≤ 1` and, for
each `δ₀ > 0`, eventually `f ε ≤ β ε → 0` on `E ε ∩ {𝔰 ≥ δ₀}`, where `P[(E ε)ᶜ] → 0`, then `∫* f ε dP → 0`. -/
theorem tendsto_outerLIntegral_of_eventually_le₀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (f : ℝ → Ω → ℝ≥0∞) (hf : ∀ ε ω, f ε ω ≤ 1) (s : Ω → ℝ)
    (hs : AEMeasurable s P) (hspos : ∀ ω, 0 < s ω) (E : ℝ → Set Ω)
    (hE : Tendsto (fun ε => P (E ε)ᶜ) (𝓝[>] 0) (𝓝 0))
    (hb : ∀ δ₀ : ℝ, 0 < δ₀ → ∃ β : ℝ → ℝ≥0∞, Tendsto β (𝓝[>] 0) (𝓝 0) ∧
      ∀ᶠ ε in 𝓝[>] 0, ∀ ω ∈ E ε, δ₀ ≤ s ω → f ε ω ≤ β ε) :
    Tendsto (fun ε => outerLIntegral P (f ε)) (𝓝[>] 0) (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro e he
  have he2 : 0 < e / 2 := ENNReal.half_pos he.ne'
  set A : ℕ → Set Ω := fun n => {ω | s ω < 1 / ((n : ℝ) + 1)} with hA
  have hlim : Tendsto (fun n => P (A n)) atTop (𝓝 0) := by
    have hanti : Antitone A := by
      intro i j hij ω hω
      simp only [hA, mem_ofPred_eq] at hω ⊢
      refine hω.trans_le (one_div_le_one_div_of_le (by positivity) ?_)
      have : (i : ℝ) ≤ j := by exact_mod_cast hij
      linarith
    have h := tendsto_measure_iInter_atTop (μ := P)
      (fun n => nullMeasurableSet_lt hs aemeasurable_const) hanti ⟨0, measure_ne_top P _⟩
    have hempty : (⋂ n, A n) = ∅ := by
      ext ω
      simp only [hA, mem_iInter, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_forall, not_lt]
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (hspos ω)
      exact ⟨n, hn.le⟩
    rw [hempty, measure_empty] at h
    exact h
  obtain ⟨N, hN⟩ := (ENNReal.tendsto_nhds_zero.1 hlim (e / 2) he2).exists
  have hδ₀ : (0 : ℝ) < 1 / ((N : ℝ) + 1) := by positivity
  obtain ⟨β, hβ, hev⟩ := hb _ hδ₀
  have hsum : Tendsto (fun ε => P (E ε)ᶜ + β ε) (𝓝[>] 0) (𝓝 0) := by
    simpa using hE.add hβ
  filter_upwards [hev, ENNReal.tendsto_nhds_zero.1 hsum (e / 2) he2] with ε hε hε2
  set T := toMeasurable P ((E ε)ᶜ ∪ A N) with hT
  have hpt : ∀ ω, f ε ω ≤ T.indicator 1 ω + β ε := by
    intro ω
    by_cases hω : ω ∈ T
    · rw [indicator_of_mem hω]
      exact (hf ε ω).trans le_self_add
    · have hω' : ω ∉ (E ε)ᶜ ∪ A N := fun h => hω (subset_toMeasurable _ _ h)
      simp only [hA, mem_union, mem_compl_iff, not_or, not_not, mem_ofPred_eq, not_lt] at hω'
      exact (hε ω hω'.1 hω'.2).trans le_add_self
  have hgm : Measurable fun ω => T.indicator 1 ω + β ε :=
    (measurable_one.indicator (measurableSet_toMeasurable _ _)).add measurable_const
  calc outerLIntegral P (f ε) ≤ ∫⁻ ω, (T.indicator 1 ω + β ε) ∂P :=
        iInf_le_of_le (fun ω => T.indicator 1 ω + β ε) (iInf_le_of_le hgm (iInf_le_of_le hpt le_rfl))
    _ = P T + β ε := by
        rw [lintegral_add_right _ measurable_const,
          lintegral_indicator_one (measurableSet_toMeasurable _ _), lintegral_const, measure_univ, mul_one]
    _ ≤ (P (E ε)ᶜ + P (A N)) + β ε := by
        rw [hT, measure_toMeasurable]
        exact add_le_add (measure_union_le _ _) le_rfl
    _ = P (A N) + (P (E ε)ᶜ + β ε) := by rw [add_comm (P (E ε)ᶜ), add_assoc]
    _ ≤ e / 2 + e / 2 := add_le_add hN hε2
    _ = e := ENNReal.add_halves e

/-- **Lemma 5.2 (relaxed)** from its quenched steps and `CellCountStep`, without `EnvSigmaMeasurableStep`: the proof
of `generalIDLALowerBoundRelaxed_of_steps`, where the `σ(h, η)`-measurable `𝔰` is only used through the
null-measurability of `{𝔰 < δ}` (`MatedCRTEnv.IsValid.aemeasurable_of_envSigma`). -/
theorem generalIDLALowerBoundRelaxed_of_steps₀ (𝒮 : SpaceFillingSLEModel) (hG : GreenHittingStep)
    (hQ : QuenchedSiteBoundStep) (hC : CellCountStep 𝒮) : GeneralIDLALowerBoundRelaxedStep 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS O₁ O₂ K q s hO hq hs hspos hgood
  have := hS.isProbabilityMeasure
  have hsm : AEMeasurable s S.P := hS.aemeasurable_of_envSigma hs
  set A : ℝ → Set Ω := fun ε =>
    {ω | O₁ ε ω ⊆ O₂ ε ω ∧ O₂ ε ω ⊆ cellVertices ε (S.η ω) (ball 0 ρ)} with hA
  set B : ℝ → Set Ω := fun ε => {ω | ∀ a ∈ O₁ ε ω,
      (1 + s ω) * ∑' b : O₂ ε ω, greenFn (S.mult ε ω) (O₂ ε ω) b a ≤
        K ε * greenFn (S.mult ε ω) (O₂ ε ω) 0 a ∧
      ε ^ (-q) ≤ (∑' b : O₂ ε ω, greenFn (S.mult ε ω) (O₂ ε ω) b a) /
        greenFn (S.mult ε ω) (O₂ ε ω) a a} with hB
  set C : ℝ → Set Ω := fun ε => {ω | (cellVertices ε (S.η ω) (ball 0 ρ)).Finite ∧
      ((cellVertices ε (S.η ω) (ball 0 ρ)).ncard : ℝ) ≤ ε ^ (-2 : ℝ)} with hCdef
  have hBt : Tendsto (fun ε => S.P (B ε)ᶜ) (𝓝[>] 0) (𝓝 0) := hgood
  have hCt : Tendsto (fun ε => S.P (C ε)ᶜ) (𝓝[>] 0) (𝓝 0) := hC γ hγ hγ2 ρ hρ hρ1 Ω S hS
  have hE : Tendsto (fun ε => S.P (A ε ∩ B ε ∩ C ε)ᶜ) (𝓝[>] 0) (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (by simpa using hBt.add hCt) (Eventually.of_forall fun _ => zero_le) ?_
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    have hnull : S.P (A ε)ᶜ = 0 := by
      refine measure_mono_null ?_ (ae_iff.1 (hO ε hε))
      intro ω hω
      simp only [hA, mem_compl_iff, mem_ofPred_eq] at hω
      simp only [mem_ofPred_eq]
      exact fun h => hω ⟨h.1, h.2⟩
    calc S.P (A ε ∩ B ε ∩ C ε)ᶜ = S.P ((A ε)ᶜ ∪ (B ε)ᶜ ∪ (C ε)ᶜ) := by
          rw [compl_inter, compl_inter]
      _ ≤ S.P (A ε)ᶜ + S.P (B ε)ᶜ + S.P (C ε)ᶜ :=
          (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
      _ = S.P (B ε)ᶜ + S.P (C ε)ᶜ := by rw [hnull, zero_add]
  have main : ∀ clus : ℝ → Ω → (ℕ → ℕ → ℤ) → Set ℤ,
      (∀ δ₀ : ℝ, 0 < δ₀ → ∃ c : ℝ, 0 < c ∧ ∀ ε : ℝ, 0 < ε → 2 / δ₀ ≤ ε ^ (-q) → ∀ ω ∈ B ε,
        δ₀ ≤ s ω → ∀ a ∈ O₁ ε ω, walkerSequenceLaw (S.mult ε ω) 0 {xs | a ∉ clus ε ω xs} ≤
          ENNReal.ofReal (2 * Real.exp (-(c * ε ^ (-q))))) →
      Tendsto (fun ε => S.idlaSectionProb ε {p | ¬ O₁ ε p.1 ⊆ clus ε p.1 p.2}) (𝓝[>] 0) (𝓝 0) := by
    intro clus hsite
    refine tendsto_outerLIntegral_of_eventually_le₀ S.P
      (fun ε ω => walkerSequenceLaw (S.mult ε ω) 0 {xs | ¬ O₁ ε ω ⊆ clus ε ω xs})
      (fun ε ω => prob_le_one) s hsm hspos (fun ε => A ε ∩ B ε ∩ C ε) hE ?_
    intro δ₀ hδ₀
    obtain ⟨c, hc, hcs⟩ := hsite δ₀ hδ₀
    refine ⟨fun ε => ENNReal.ofReal (ε ^ (-2 : ℝ) * (2 * Real.exp (-(c * ε ^ (-q))))), ?_, ?_⟩
    · simpa using ENNReal.tendsto_ofReal (tendsto_card_mul_exp_bound hq hc)
    filter_upwards [self_mem_nhdsWithin,
      (tendsto_rpow_neg_nhdsGT_zero_atTop hq).eventually_ge_atTop (2 / δ₀)] with ε (hε : 0 < ε) hεq
    rintro ω ⟨⟨⟨hsub1, hsub2⟩, hωB⟩, hCfin, hCcard⟩ hsω
    have hfin : (O₁ ε ω).Finite := hCfin.subset (hsub1.trans hsub2)
    have hsite' := hcs ε hε hεq ω hωB hsω
    calc walkerSequenceLaw (S.mult ε ω) 0 {xs | ¬ O₁ ε ω ⊆ clus ε ω xs}
        ≤ walkerSequenceLaw (S.mult ε ω) 0 (⋃ a ∈ hfin.toFinset, {xs | a ∉ clus ε ω xs}) := by
          apply measure_mono
          intro xs hxs
          simp only [mem_ofPred_eq, not_subset] at hxs
          obtain ⟨a, ha, hna⟩ := hxs
          simp only [mem_iUnion]
          exact ⟨a, hfin.mem_toFinset.2 ha, hna⟩
      _ ≤ ∑ a ∈ hfin.toFinset, walkerSequenceLaw (S.mult ε ω) 0 {xs | a ∉ clus ε ω xs} :=
          measure_biUnion_finset_le _ _
      _ ≤ hfin.toFinset.card • ENNReal.ofReal (2 * Real.exp (-(c * ε ^ (-q)))) :=
          Finset.sum_le_card_nsmul _ _ _ fun a ha => hsite' a (hfin.mem_toFinset.1 ha)
      _ ≤ ENNReal.ofReal (ε ^ (-2 : ℝ) * (2 * Real.exp (-(c * ε ^ (-q))))) := by
          rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
          apply ENNReal.ofReal_le_ofReal
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          rw [← Set.ncard_eq_toFinset_card _ hfin]
          exact (Nat.cast_le.2 (Set.ncard_le_ncard (hsub1.trans hsub2) hCfin)).trans hCcard
  have hsite : ∀ δ₀ : ℝ, 0 < δ₀ → ∃ c : ℝ, 0 < c ∧ ∀ ε : ℝ, 0 < ε → 2 / δ₀ ≤ ε ^ (-q) → ∀ ω ∈ B ε,
      δ₀ ≤ s ω → ∀ a ∈ O₁ ε ω,
        walkerSequenceLaw (S.mult ε ω) 0 {xs | a ∉ idlaCluster xs ⌊K ε⌋₊} ≤
            ENNReal.ofReal (2 * Real.exp (-(c * ε ^ (-q)))) ∧
          walkerSequenceLaw (S.mult ε ω) 0 {xs | a ∉ stoppedIDLACluster (O₂ ε ω) xs ⌊K ε⌋₊} ≤
            ENNReal.ofReal (2 * Real.exp (-(c * ε ^ (-q)))) := by
    intro δ₀ hδ₀
    obtain ⟨c, hc, hcQ⟩ := hQ (δ₀ / 2) (by positivity)
    refine ⟨c, hc, fun ε hε hεq ω hωB hsω a ha => ?_⟩
    obtain ⟨h1, h2⟩ := hωB a ha
    exact siteBound_of_conditions hG hδ₀ hc hcQ (S.mult ε ω) (O₂ ε ω) a (K ε) (s ω) (ε ^ (-q))
      (Real.rpow_pos_of_pos hε _) hεq hsω h1 h2
  refine ⟨main (fun ε _ xs => idlaCluster xs ⌊K ε⌋₊) ?_,
    main (fun ε ω xs => stoppedIDLACluster (O₂ ε ω) xs ⌊K ε⌋₊) ?_⟩
  · intro δ₀ hδ₀
    obtain ⟨c, hc, h⟩ := hsite δ₀ hδ₀
    exact ⟨c, hc, fun ε hε hεq ω hωB hsω a ha => (h ε hε hεq ω hωB hsω a ha).1⟩
  · intro δ₀ hδ₀
    obtain ⟨c, hc, h⟩ := hsite δ₀ hδ₀
    exact ⟨c, hc, fun ε hε hεq ω hωB hsω a ha => (h ε hε hεq ω hωB hsω a ha).2⟩

/-- **Lemma 5.2 (relaxed)** from Lemma 2.7 (`VolumeGrowthStmt`, BG20 Lemma A.1) and Lemma 2.8
(`CellSizeEstimateStmt`, BG20 Lemma 2.4). -/
theorem generalIDLALowerBoundRelaxed_of_volumeGrowth_cellSize (𝒮 : SpaceFillingSLEModel) (h27 : VolumeGrowthStmt)
    (h28 : CellSizeEstimateStmt 𝒮) : GeneralIDLALowerBoundRelaxedStep 𝒮 :=
  generalIDLALowerBoundRelaxed_of_steps₀ 𝒮 greenHittingStep
    (quenchedSiteBound_of_steps missedSiteVisitStep visitCountLowerTailStep lateVisitUpperTailStep)
    (cellCountStep 𝒮 h27 h28)

/-- **Lemma 5.2** from Lemma 2.7 (`VolumeGrowthStmt`) and Lemma 2.8 (`CellSizeEstimateStmt`). -/
theorem generalIDLALowerBound_of_volumeGrowth_cellSize (𝒮 : SpaceFillingSLEModel) (h27 : VolumeGrowthStmt)
    (h28 : CellSizeEstimateStmt 𝒮) : GeneralIDLALowerBoundStmt 𝒮 :=
  generalIDLALowerBound_of_relaxed 𝒮 (generalIDLALowerBoundRelaxed_of_volumeGrowth_cellSize 𝒮 h27 h28)

/-- **Proposition 5.1** from Lemmas 2.7, 2.8, 5.3, 5.4, the discrete-cluster form of Proposition 4.2 and the stopped
step (`iDLALowerBound_of_inputs` without `EnvSigmaMeasurableStep`). -/
theorem iDLALowerBound_of_volumeGrowth_cellSize (𝒮 : SpaceFillingSLEModel) (h27 : VolumeGrowthStmt)
    (h28 : CellSizeEstimateStmt 𝒮) (h53 : MeanValueInequalityStmt 𝒮) (h54 : LLowerBoundStmt 𝒮)
    (hI : DiscreteClusterInnerBoundStep 𝒮) (hstop : IDLALowerBoundStoppedStep 𝒮) : IDLALowerBoundStmt 𝒮 :=
  iDLALowerBound_of_steps 𝒮 (generalIDLALowerBoundRelaxed_of_volumeGrowth_cellSize 𝒮 h27 h28) h53 h54 h28 hI hstop

end MatedCRT
