import MatedCRT.FirstPass.Derived.PlanarOptionalTimeStrongMarkov

/-!
# The strong Markov property at an optional time, as an identity of laws and for bounded real tests

For an optional time `T` of the canonical filtration of the planar path and a variable `V` of `F_{T+}`
(`{V ∈ B} ∩ {T < t} ∈ F⁰_t`), the law under planar Brownian motion from `z`, restricted to `{T < ∞}`, of the pair
`(V, θ_T ω)` is the composition of the law of `ω` with the kernel `ω ↦ δ_{V ω} ⊗ P_{ω_T}`
(`map_pair_shift_optionalTime`).  Hence, for a bounded measurable `h`,
`E_z[h(V, θ_T ω)] = E_z[∫ h(V ω, ω') dP_{ω_T}(ω')]` when `T < ∞` almost surely
(`integral_pair_shift_optionalTime`).  This is the real-valued form of the parameter form
`lintegral_planarLaw_shift_optionalTime_param`.
-/

open MeasureTheory ProbabilityTheory Set Filter MarkovProcess
open scoped ENNReal NNReal

namespace MatedCRT.OptionalTime

open _root_.HarmonicBalls

/-- **Strong Markov property at an optional time, as an identity of laws.** -/
theorem map_pair_shift_optionalTime {β : Type*} [MeasurableSpace β] (z : ℂ)
    (T : ContinuousPath ℂ → WithTop ℝ≥0)
    (hT : ∀ t : ℝ≥0, MeasurableSet[ContinuousPath.canonicalFiltration (alpha := ℂ) t]
      {ω | T ω < t})
    (V : ContinuousPath ℂ → β) (hVm : Measurable V)
    (hV : ∀ B : Set β, MeasurableSet B → ∀ t : ℝ≥0,
      MeasurableSet[ContinuousPath.canonicalFiltration (alpha := ℂ) t]
        (V ⁻¹' B ∩ {ω | T ω < t})) :
    ((planarLaw z).restrict {ω | T ω < ⊤}).map
        (fun ω => (V ω, ContinuousPath.shift ((T ω).untopD 0) ω)) =
      (Kernel.deterministic V hVm ×ₖ Kernel.comap planarBrownianMotion
        (fun ω : ContinuousPath ℂ ↦ ω ((T ω).untopD 0)) (measurable_eval_untopD hT)) ∘ₘ
        ((planarLaw z).restrict {ω | T ω < ⊤}) := by
  set μ := (planarLaw z).restrict {ω | T ω < ⊤} with hμ
  set s : ContinuousPath ℂ → ContinuousPath ℂ :=
    fun ω ↦ ContinuousPath.shift ((T ω).untopD 0) ω with hs
  have hsm : Measurable s := ContinuousPath.measurable_shift_of_measurable _ (measurable_untopD hT)
  have hpm : Measurable fun ω => (V ω, s ω) := hVm.prodMk hsm
  set κ₀ := Kernel.comap planarBrownianMotion (fun ω : ContinuousPath ℂ ↦ ω ((T ω).untopD 0))
    (measurable_eval_untopD hT) with hκ₀
  set κ := Kernel.deterministic V hVm ×ₖ κ₀ with hκ
  have hκapp : ∀ ω, κ ω = (planarLaw (ω ((T ω).untopD 0))).map (Prod.mk (V ω)) := by
    intro ω
    rw [hκ, Kernel.prod_apply, Kernel.deterministic_apply, Measure.dirac_prod, hκ₀,
      Kernel.comap_apply]
    rfl
  have hsub : ∀ B : Set β, MeasurableSet B → ∀ t : ℝ≥0,
      MeasurableSet[ContinuousPath.canonicalFiltration (alpha := ℂ) t]
        (V ⁻¹' B ∩ {ω | T ω < t}) := hV
  have heq : μ.map (fun ω => (V ω, s ω)) = κ ∘ₘ μ := by
    refine ext_of_generate_finite _ generateFrom_prod.symm isPiSystem_prod ?_ ?_
    · rintro _ ⟨B, hB, G, hG, rfl⟩
      replace hB : MeasurableSet B := hB
      replace hG : MeasurableSet G := hG
      have h1 : ∀ ω, κ ω (B ×ˢ G) =
          (V ⁻¹' B).indicator (fun ω => planarLaw (ω ((T ω).untopD 0)) G) ω := by
        intro ω
        rw [hκ, Kernel.prod_apply, Measure.prod_prod, Kernel.deterministic_apply, hκ₀,
          Kernel.comap_apply, Measure.dirac_apply' _ hB]
        by_cases h : V ω ∈ B <;> simp [h, planarLaw]
      rw [Measure.map_apply hpm (hB.prod hG), Measure.bind_apply (hB.prod hG)
        (Kernel.aemeasurable _)]
      simp_rw [h1]
      rw [lintegral_indicator (hVm hB), hμ, Measure.restrict_restrict (hVm hB),
        Measure.restrict_apply (hpm (hB.prod hG)),
        ← planarLaw_inter_shift_preimage_optionalTime z T hT _ (hsub B hB) hG]
      congr 1
      ext ω
      simp only [mem_inter_iff, mem_preimage, mem_prod, mem_ofPred_eq, hs]
      tauto
    · rw [Measure.map_apply hpm MeasurableSet.univ,
        Measure.bind_apply MeasurableSet.univ (Kernel.aemeasurable _)]
      simp [measure_univ]
  exact heq

/-- **Strong Markov property at an optional time, bounded real form.** If `T < ∞` almost surely, `V` is a variable
of `F_{T+}` and `h` is bounded and measurable, then `E_z[h(V, θ_T ω)] = E_z[∫ h(V ω, ω') dP_{ω_T}(ω')]`. -/
theorem integral_pair_shift_optionalTime {β : Type*} [MeasurableSpace β] (z : ℂ)
    (T : ContinuousPath ℂ → WithTop ℝ≥0)
    (hT : ∀ t : ℝ≥0, MeasurableSet[ContinuousPath.canonicalFiltration (alpha := ℂ) t]
      {ω | T ω < t})
    (V : ContinuousPath ℂ → β) (hVm : Measurable V)
    (hV : ∀ B : Set β, MeasurableSet B → ∀ t : ℝ≥0,
      MeasurableSet[ContinuousPath.canonicalFiltration (alpha := ℂ) t]
        (V ⁻¹' B ∩ {ω | T ω < t}))
    (hfin : ∀ᵐ ω ∂planarLaw z, T ω < ⊤)
    {h : β × ContinuousPath ℂ → ℝ} (hm : Measurable h) {C : ℝ} (hC : ∀ p, ‖h p‖ ≤ C) :
    ∫ ω, h (V ω, ContinuousPath.shift ((T ω).untopD 0) ω) ∂planarLaw z =
      ∫ ω, ∫ ω', h (V ω, ω') ∂planarLaw (ω ((T ω).untopD 0)) ∂planarLaw z := by
  have hμ : (planarLaw z).restrict {ω | T ω < ⊤} = planarLaw z :=
    Measure.restrict_eq_self_of_ae_mem hfin
  have hmap := map_pair_shift_optionalTime z T hT V hVm hV
  rw [hμ] at hmap
  set s : ContinuousPath ℂ → ContinuousPath ℂ :=
    fun ω ↦ ContinuousPath.shift ((T ω).untopD 0) ω with hs
  have hsm : Measurable s := ContinuousPath.measurable_shift_of_measurable _ (measurable_untopD hT)
  have hpm : Measurable fun ω => (V ω, s ω) := hVm.prodMk hsm
  set κ := Kernel.deterministic V hVm ×ₖ Kernel.comap planarBrownianMotion
    (fun ω : ContinuousPath ℂ ↦ ω ((T ω).untopD 0)) (measurable_eval_untopD hT) with hκ
  have hκapp : ∀ ω, κ ω = (planarLaw (ω ((T ω).untopD 0))).map (Prod.mk (V ω)) := by
    intro ω
    rw [hκ, Kernel.prod_apply, Kernel.deterministic_apply, Measure.dirac_prod, Kernel.comap_apply]
    rfl
  have hint : Integrable h (κ ∘ₘ planarLaw z) := by
    rw [← hmap]
    exact Integrable.of_bound hm.aestronglyMeasurable C (Filter.Eventually.of_forall hC)
  rw [← integral_map hpm.aemeasurable hm.aestronglyMeasurable, hmap, Measure.comp_eq_comp_const_apply,
    Kernel.integral_comp (by rwa [← Measure.comp_eq_comp_const_apply])]
  simp only [Kernel.const_apply]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  dsimp only
  rw [hκapp, integral_map measurable_prodMk_left.aemeasurable hm.aestronglyMeasurable]

end MatedCRT.OptionalTime
