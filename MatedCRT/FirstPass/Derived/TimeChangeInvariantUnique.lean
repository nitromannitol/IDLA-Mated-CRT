import MatedCRT.FirstPass.Derived.TimeChangeInvariantLevelSet

/-!
# Invariant measures of the time change are multiples of the Revuz measure

Let `A` be a PCAF of planar Brownian motion with a good clock, `P_u = timeChangeKernel A u` the kernel of the time
change and `μ_A` the Revuz measure.  For a `σ`-finite measure `ν` invariant for the time change put `λ = ν + μ_A` and
`f = dν/dλ`.

* **Zero-one law.**  If `λ` restricted to a Borel set `G` is invariant and `μ_A(Gᶜ) ≠ 0`, then `λ(G) = 0`: the
  invariance gives `∫_G P_u(x, Gᶜ) dλ(x) = 0` for every `u`, while the time-changed occupation
  `∫_{(0,∞)} P_r(x, Gᶜ) dr` is infinite for every `x` (`setLIntegral_Ioi_timeChangeKernel_eq_top`).  Applied to the
  level sets `{f > a}` and their complements, which are invariant (`bind_timeChangeKernel_restrict_levelSet_eq`), it
  shows that every level set `{f > a}` is `λ`-null or `λ`-conull.
* Hence `f` is `λ`-a.e. equal to a constant `a₀` (the sets `(q, ∞]`, `q` rational, separate the points of `[0, ∞]`),
  so that `ν = a₀ λ` and `μ_A = (1 - a₀) λ`; since `μ_A ≠ 0`, `a₀ < 1` and `ν = a₀ (1 - a₀)⁻¹ μ_A`.

This proves `TimeChangeInvariantUniqueInput` (`timeChangeInvariantUniqueInput_derived`).
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

namespace MatedCRT

open MarkovProcess _root_.HarmonicBalls

/-- **Zero-one law for invariant restrictions**: if the restriction of an s-finite measure `L` to a Borel set `G` is
invariant for the time change and `μ_A(Gᶜ) ≠ 0`, then `L(G) = 0`. -/
theorem measure_eq_zero_of_restrict_invariant {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsPCAF planarLaw A) (hG : GoodClock planarLaw A) {L : Measure ℂ} [SFinite L] {G : Set ℂ}
    (hGm : MeasurableSet G) (hinv : ∀ u, timeChangeKernel A u ∘ₘ L.restrict G = L.restrict G)
    (hμ : revuz planarLaw A Gᶜ ≠ 0) : L G = 0 := by
  have hzero : ∀ u, ∫⁻ x in G, timeChangeKernel A u x Gᶜ ∂L = 0 := fun u => by
    rw [← Measure.bind_apply hGm.compl (Kernel.aemeasurable _), hinv u, Measure.restrict_apply hGm.compl,
      compl_inter_self, measure_empty]
  have hmeas := measurable_timeChangeKernel_apply_uncurry hA.meas hGm.compl
  have hm2 : Measurable (Function.uncurry fun (x : ℂ) (r : ℝ) => timeChangeKernel A r.toNNReal x Gᶜ) := by
    simpa only [Function.uncurry_def, Function.comp_def, Prod.fst_swap, Prod.snd_swap] using
      hmeas.comp measurable_swap
  have hswap : ∫⁻ x in G, (∫⁻ r in Ioi (0 : ℝ), timeChangeKernel A r.toNNReal x Gᶜ) ∂L =
      ∫⁻ r in Ioi (0 : ℝ), (∫⁻ x in G, timeChangeKernel A r.toNNReal x Gᶜ ∂L) :=
    lintegral_lintegral_swap hm2.aemeasurable
  have hR : ∫⁻ r in Ioi (0 : ℝ), (∫⁻ x in G, timeChangeKernel A r.toNNReal x Gᶜ ∂L) = 0 := by
    simp only [hzero, lintegral_zero]
  have hLft : ∫⁻ x in G, (∫⁻ r in Ioi (0 : ℝ), timeChangeKernel A r.toNNReal x Gᶜ) ∂L = ∫⁻ _ in G, ∞ ∂L :=
    lintegral_congr fun x => setLIntegral_Ioi_timeChangeKernel_eq_top hA hG hGm.compl hμ x
  have htop : ∫⁻ _ in G, (∞ : ℝ≥0∞) ∂L = 0 := hLft.symm.trans (hswap.trans hR)
  rw [lintegral_const, Measure.restrict_apply_univ] at htop
  exact (mul_eq_zero.1 htop).resolve_left ENNReal.top_ne_zero

/-- **Every level set of the density of an invariant measure is null or conull**: for `ν` `σ`-finite and invariant
for the time change, `λ = ν + μ_A`, `f = dν/dλ` and `a ∈ [0, ∞)`, either `λ{f > a} = 0` or `λ{f ≤ a} = 0`. -/
theorem levelSet_eq_zero_or_compl_eq_zero {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsPCAF planarLaw A) (hG : GoodClock planarLaw A) {ν : Measure ℂ} [SigmaFinite ν]
    (hν : ∀ u, timeChangeKernel A u ∘ₘ ν = ν) (a : ℝ≥0) :
    (ν + revuz planarLaw A) {x | (a : ℝ≥0∞) < ν.rnDeriv (ν + revuz planarLaw A) x} = 0 ∨
      (ν + revuz planarLaw A) {x | (a : ℝ≥0∞) < ν.rnDeriv (ν + revuz planarLaw A) x}ᶜ = 0 := by
  have : SigmaFinite (revuz planarLaw A) := sigmaFinite_revuz hA hG
  have hFm : MeasurableSet {x | (a : ℝ≥0∞) < ν.rnDeriv (ν + revuz planarLaw A) x} :=
    measurableSet_lt measurable_const (Measure.measurable_rnDeriv _ _)
  by_cases hc : revuz planarLaw A {x | (a : ℝ≥0∞) < ν.rnDeriv (ν + revuz planarLaw A) x}ᶜ = 0
  · right
    have hF0 : revuz planarLaw A {x | (a : ℝ≥0∞) < ν.rnDeriv (ν + revuz planarLaw A) x} ≠ 0 := by
      intro h
      apply revuz_planarLaw_ne_zero hA hG
      rw [← Measure.measure_univ_eq_zero, ← union_compl_self {x | (a : ℝ≥0∞) < ν.rnDeriv (ν + revuz planarLaw A) x}]
      exact measure_union_null h hc
    refine measure_eq_zero_of_restrict_invariant hA hG hFm.compl
      (bind_timeChangeKernel_restrict_levelSet_compl_eq hA hG hν a) ?_
    rwa [compl_compl]
  · left
    exact measure_eq_zero_of_restrict_invariant hA hG hFm (bind_timeChangeKernel_restrict_levelSet_eq hA hG hν a) hc

/-- The intervals `(q, ∞]`, `q ∈ [0, ∞)`, include a countable family separating the points of `[0, ∞]`. -/
theorem hasCountableSeparatingOn_Ioi_coe :
    HasCountableSeparatingOn ℝ≥0∞ (fun U => ∃ a : ℝ≥0, U = Ioi (a : ℝ≥0∞)) univ := by
  refine ⟨⟨range fun q : ℚ => Ioi ((Real.toNNReal q : ℝ≥0) : ℝ≥0∞), countable_range _, ?_, ?_⟩⟩
  · rintro _ ⟨q, rfl⟩
    exact ⟨_, rfl⟩
  · have key : ∀ x y : ℝ≥0∞, x < y →
        ∃ U ∈ range (fun q : ℚ => Ioi ((Real.toNNReal q : ℝ≥0) : ℝ≥0∞)), x ∉ U ∧ y ∈ U := by
      intro x y hxy
      obtain ⟨q, -, hxq, hqy⟩ := ENNReal.lt_iff_exists_rat_btwn.1 hxy
      exact ⟨_, ⟨q, rfl⟩, fun h => lt_irrefl _ (lt_trans hxq (show _ < x from h)), hqy⟩
    intro x _ y _ h
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · obtain ⟨U, hU, hxU, hyU⟩ := key x y hlt
      exact hxU ((h U hU).2 hyU)
    · obtain ⟨U, hU, hyU, hxU⟩ := key y x hlt
      exact hyU ((h U hU).1 hxU)

/-- **The density of an invariant measure is a.e. constant**: for `ν` `σ`-finite and invariant for the time change
and `λ = ν + μ_A`, the density `dν/dλ` is `λ`-a.e. equal to a constant. -/
theorem exists_rnDeriv_ae_eq_const {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsPCAF planarLaw A) (hG : GoodClock planarLaw A) {ν : Measure ℂ} [SigmaFinite ν]
    (hν : ∀ u, timeChangeKernel A u ∘ₘ ν = ν) :
    ∃ a₀ : ℝ≥0∞, ν.rnDeriv (ν + revuz planarLaw A) =ᵐ[ν + revuz planarLaw A] fun _ => a₀ := by
  have := hasCountableSeparatingOn_Ioi_coe
  obtain ⟨a₀, h⟩ := exists_eventuallyEq_const_of_forall_separating (l := ae (ν + revuz planarLaw A))
    (f := ν.rnDeriv (ν + revuz planarLaw A)) (fun U => ∃ a : ℝ≥0, U = Ioi (a : ℝ≥0∞)) (by
      rintro _ ⟨a, rfl⟩
      rcases levelSet_eq_zero_or_compl_eq_zero hA hG hν a with h | h
      · exact Or.inr (measure_eq_zero_iff_ae_notMem.1 h)
      · exact Or.inl (ae_iff.2 h))
  exact ⟨a₀, h⟩

/-- **Invariant measures of the time change are multiples of the Revuz measure**: every `σ`-finite measure
invariant for the time change of planar Brownian motion by a PCAF with a good clock is a finite constant multiple of
the Revuz measure.  This proves `TimeChangeInvariantUniqueInput`. -/
theorem timeChangeInvariantUniqueInput_derived : TimeChangeInvariantUniqueInput := by
  intro A hA hG ν hνsf hinv
  have hν : ∀ u, timeChangeKernel A u ∘ₘ ν = ν := (isInvTC_iff hA ν).1 hinv
  have : SigmaFinite (revuz planarLaw A) := sigmaFinite_revuz hA hG
  obtain ⟨a₀, ha₀⟩ := exists_rnDeriv_ae_eq_const hA hG hν
  have hne := revuz_planarLaw_ne_zero hA hG
  set μ := revuz planarLaw A with hμdef
  set L := ν + μ with hL
  have hLsf : SigmaFinite L := by rw [hL]; infer_instance
  have hνL : ν ≪ L := Measure.AbsolutelyContinuous.rfl.add_right μ
  have hμL : μ ≪ L := Measure.AbsolutelyContinuous.rfl.add_right' ν
  have h1 : ν = a₀ • L :=
    calc ν = L.withDensity (ν.rnDeriv L) := (Measure.withDensity_rnDeriv_eq ν L hνL).symm
      _ = L.withDensity (fun _ => a₀) := withDensity_congr_ae ha₀
      _ = a₀ • L := withDensity_const a₀
  have h2 : μ.rnDeriv L =ᵐ[L] fun _ => 1 - a₀ := by
    filter_upwards [Measure.rnDeriv_add' ν μ L, L.rnDeriv_self, ha₀] with x hx1 hx2 hx3
    rw [Pi.add_apply, hx3, ← hL, hx2] at hx1
    have ha₀top : a₀ ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top (hx1 ▸ le_self_add)
    exact ENNReal.eq_sub_of_add_eq ha₀top (by rw [add_comm]; exact hx1.symm)
  have h3 : μ = (1 - a₀) • L :=
    calc μ = L.withDensity (μ.rnDeriv L) := (Measure.withDensity_rnDeriv_eq μ L hμL).symm
      _ = L.withDensity (fun _ => 1 - a₀) := withDensity_congr_ae h2
      _ = (1 - a₀) • L := withDensity_const _
  have hb0 : 1 - a₀ ≠ 0 := by
    intro h
    rw [h, zero_smul] at h3
    exact hne h3
  have hbtop : 1 - a₀ ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
  have ha₀top : a₀ ≠ ∞ := (lt_of_not_ge fun h => hb0 (tsub_eq_zero_of_le h)).trans ENNReal.one_lt_top |>.ne
  have hLμ : L = (1 - a₀)⁻¹ • μ := by
    rw [h3, smul_smul, ENNReal.inv_mul_cancel hb0 hbtop, one_smul]
  have hc : a₀ * (1 - a₀)⁻¹ ≠ ∞ := ENNReal.mul_ne_top ha₀top (ENNReal.inv_ne_top.2 hb0)
  refine ⟨(a₀ * (1 - a₀)⁻¹).toNNReal, ?_⟩
  rw [ENNReal.coe_toNNReal hc, h1, hLμ, smul_smul]

end MatedCRT
