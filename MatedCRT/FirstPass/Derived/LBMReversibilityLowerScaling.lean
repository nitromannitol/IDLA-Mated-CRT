import MatedCRT.FirstPass.Derived.LBMReversibilityOfLimit

/-!
# Reversibility of the LQG measure for a subsequential limit, from `m_{ε_n} → ∞`

`ae_compProd_evalLawKernel_swap_of_tendsto_law` (BG20 Lemma 7.6) uses the scaling input
`m_ε ≍ ε⁻¹` (`MepsScalingInput`, eq:meps-scaling) only through the convergence of the lattice times
`⌊m_{ε_n} s⌋ / m_{ε_n} → s`, and for that only the lower half `m_ε ≥ C⁻¹ ε⁻¹` matters. The lattice
times converge as soon as `m_{ε_n} → ∞`, so the same conclusion holds with `MepsScalingInput`
replaced by the hypothesis `m_{ε_n} → ∞` on the given environment and the given sequence `ε_n`.

* `tendsto_latticeTime_of_tendsto_atTop`: if `m_n → ∞`, the lattice times `⌊m_n s⌋ / m_n` converge
  to `s`.
* `ae_compProd_evalLawKernel_swap_of_tendsto_law_of_tendsto_mε`: BG20 Lemma 7.6 for a subsequential
  limit, with `m_{ε_n} → ∞` in place of `MepsScalingInput`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Metric LatticeProb
open MarkovProcess (ContinuousPath)
open scoped NNReal ENNReal BoundedContinuousFunction

namespace MatedCRT.FirstPass.Derived

/-- **The lattice times converge** when `m_n → ∞`: the lattice times `⌊m_n s⌋ / m_n` converge
to `s`. -/
theorem tendsto_latticeTime_of_tendsto_atTop {m : ℕ → ℝ} (hm : Tendsto m atTop atTop) (s : ℝ≥0) :
    Tendsto (fun n => latticeTime (m n) s) atTop (𝓝 s) :=
  tendsto_latticeTime (c := fun n => (m n)⁻¹)
    ((hm.eventually_gt_atTop 0).mono fun _ hn => ⟨hn, le_rfl⟩) (tendsto_inv_atTop_zero.comp hm) s

/-- **The LQG measure is reversible for a subsequential limit of the walk laws** (BG20 Lemma 7.6),
with the scaling input `m_ε ≍ ε⁻¹` replaced by `m_{ε_n} → ∞` along the given sequence.
Let `S` be a valid environment with a measurable version `η'` of the space-filling SLE curve, let
`ε n → 0⁺` with `m_{ε_n} → ∞`, and assume the input of Lemma 2.7 (`DegreeMeasureConvergenceStmt`)
and the equicontinuity in law `hEqLaw` of the walk laws. Let `D n` be random data in a second
countable metrizable space `X` whose coordinate `μX (D n)` is almost surely the LQG measure `μ_h`,
with `d ↦ 6 ψ μX d` Lévy–Prokhorov continuous for every cutoff `ψ`, and let `(D n, P̃^{ε_n})`
converge in law to `ν`. Then for `ν`-almost every `(d, P)` and every `s ≥ 0`, the measure
`m_s(dz, dw) = μX d (dz) P_z(X_s ∈ dw)` is invariant under `(z, w) ↦ (w, z)`. -/
theorem ae_compProd_evalLawKernel_swap_of_tendsto_law_of_tendsto_mε
    {𝒮 : SpaceFillingSLEModel} (hD27 : DegreeMeasureConvergenceStmt 𝒮)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    (hS : S.IsValid 𝒮 γ) {η' : Ω → C(ℝ, ℂ)} (hη' : Measurable η')
    (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω)
    {ε : ℕ → ℝ} (hε0 : ∀ n, 0 < ε n) (hε : Tendsto ε atTop (𝓝 0))
    (hm : Tendsto (fun n => S.mε (ε n)) atTop atTop)
    (hEqLaw : ∀ R a : ℝ, 0 < a → ∃ δ > 0, ∀ᶠ n in atTop,
      S.P {ω | ENNReal.ofReal a < walkLawModulus S η' (ε n) R δ ω} ≤ ENNReal.ofReal a)
    {X : Type*} [TopologicalSpace X] [TopologicalSpace.PseudoMetrizableSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    {D : ℕ → Ω → X} (hD : ∀ n, AEMeasurable (D n) S.P)
    (μX : X → Measure ℂ) [∀ d, IsLocallyFiniteMeasure (μX d)]
    (hμXD : ∀ n, ∀ᵐ ω ∂S.P, μX (D n ω) = S.μ ω)
    (hπ : ∀ (ψ : ℂ → ℝ) (hψ : Continuous ψ) (hψc : HasCompactSupport ψ), (∀ z, 0 ≤ ψ z) →
      Continuous fun d => LevyProkhorov.ofMeasure (cutoffWeightedMeasure (μX d) hψ hψc 6))
    {ν : Measure (X × C(ℂ, ProbabilityMeasure (ContinuousPath ℂ)))}
    (hlaw : ∀ F : (X × C(ℂ, ProbabilityMeasure (ContinuousPath ℂ))) →ᵇ ℝ,
      Tendsto (fun n => ∫ ω, F (D n ω, interpWalkLaw S η' (ε n) ω) ∂S.P) atTop (𝓝 (∫ p, F p ∂ν))) :
    ∀ᵐ p ∂ν, ∀ s : ℝ≥0,
      (μX p.1 ⊗ₘ evalLawKernel p.2 s).map Prod.swap = μX p.1 ⊗ₘ evalLawKernel p.2 s := by
  have := hS.isProbabilityMeasure
  let : MeasurableSpace (LevyProkhorov (FiniteMeasure ℂ)) := borel _
  have : BorelSpace (LevyProkhorov (FiniteMeasure ℂ)) := ⟨rfl⟩
  let : MeasurableSpace (FiniteMeasure ℂ) := borel _
  have : BorelSpace (FiniteMeasure ℂ) := ⟨rfl⟩
  refine ae_compProd_evalLawKernel_swap_of_pairing_symm_rat (P₀ := ν) (fun p => μX p.1)
    (fun _ => inferInstance) (fun p => p.2) fun f hf g hg q => ?_
  obtain ⟨⟨Kf, hfl⟩, hfc⟩ := lipschitz_hasCompactSupport_of_mem_pairingTestFamily hf
  obtain ⟨⟨Kg, hgl⟩, hgc⟩ := lipschitz_hasCompactSupport_of_mem_pairingTestFamily hg
  obtain ⟨ψ, hψ1, -, hψc, hψI⟩ := exists_continuous_one_zero_of_isCompact
    (hfc.isCompact.union hgc.isCompact) isClosed_empty (disjoint_empty _)
  have hψ0 : ∀ z, 0 ≤ ψ z := fun z => (hψI z).1
  have ht : Tendsto (fun n => latticeTime (S.mε (ε n)) (q : ℝ≥0)) atTop (𝓝 (q : ℝ≥0)) :=
    tendsto_latticeTime_of_tendsto_atTop hm _
  have hπψ := hπ ψ ψ.continuous hψc hψ0
  have hπw : Continuous fun d => cutoffWeightedMeasure (μX d) ψ.continuous hψc 6 :=
    continuous_levyProkhorov_toFiniteMeasure.comp hπψ
  have hπD : ∀ n, ∀ᵐ ω ∂S.P, (cutoffWeightedMeasure (μX (D n ω)) ψ.continuous hψc 6 : Measure ℂ) =
      (S.μ ω).withDensity fun z => ENNReal.ofReal (6 * ψ z) := fun n =>
    (hμXD n).mono fun ω h => by rw [coe_cutoffWeightedMeasure, h]
  have hΘ : AEMeasurable (fun p : X × C(ℂ, ProbabilityMeasure (ContinuousPath ℂ)) =>
      (cutoffWeightedMeasure (μX p.1) ψ.continuous hψc 6, p.2, (q : ℝ≥0))) ν :=
    ((hπw.measurable.comp measurable_fst).prodMk
      (measurable_snd.prodMk measurable_const)).aemeasurable
  have hfb := exists_abs_le_of_lipschitzWith_of_hasCompactSupport hfl hfc
  have hgb := exists_abs_le_of_lipschitzWith_of_hasCompactSupport hgl hgc
  have htT : ∀ n, latticeTime (S.mε (ε n)) (q : ℝ≥0) ≤ (q : ℝ≥0) := fun n =>
    latticeTime_le (S.mε_nonneg (ε n)) _
  have htN : ∀ n, ∃ N : ℕ, S.mε (ε n) * (latticeTime (S.mε (ε n)) (q : ℝ≥0) : ℝ) = N := fun n =>
    ⟨_, mul_latticeTime (S.mε_nonneg (ε n)) _⟩
  have hpair : TendstoInMeasure S.P (fun n ω => reversibilityPairing f g ψ
      (degreeCutoffMeasure (S.mult (ε n) ω) (ε n) (vertexPoint (ε n) ⇑(η' ω)) ψ)
      (interpWalkLaw S η' (ε n) ω) (latticeTime (S.mε (ε n)) (q : ℝ≥0))) atTop (fun _ => 0) :=
    tendstoInMeasure_reversibilityPairing_degreeCutoffMeasure_of_D27_of_walkLaw hD27 hγ hγ2 hS hae
      hfb hfl hgb hgl ψ.continuous hψc hψ0 hψ1 hε0 hε htT htN hEqLaw
  have hlawW := tendsto_integral_degreeCutoffMeasure_interpWalkLaw_of_tendsto_law hD27 hγ hγ2 hS
    hη' hae hε0 hε hD hlaw ψ.continuous hψc hψ0
    (π := fun d => cutoffWeightedMeasure (μX d) ψ.continuous hψc 6) hπD hπψ ht hΘ
  have hμm : ∀ n, AEMeasurable (fun ω =>
      degreeCutoffMeasure (S.mult (ε n) ω) (ε n) (vertexPoint (ε n) ⇑(η' ω)) ψ) S.P := fun n =>
    continuous_levyProkhorov_toFiniteMeasure.measurable.comp_aemeasurable
      (hμ_degreeCutoffMeasure_of_isValid hS hae ψ.continuous.measurable hψc hε0 n)
  have hWm : ∀ n, AEMeasurable (fun ω =>
      (degreeCutoffMeasure (S.mult (ε n) ω) (ε n) (vertexPoint (ε n) ⇑(η' ω)) ψ,
        interpWalkLaw S η' (ε n) ω, latticeTime (S.mε (ε n)) (q : ℝ≥0))) S.P := fun n =>
    (hμm n).prodMk ((aemeasurable_interpWalkLaw hS hη' hae (hε0 n)).prodMk aemeasurable_const)
  exact ae_integral_pairing_symm_of_tendsto_law (ν := ν) (fun p => μX p.1) (fun p => p.2)
    hfl hfc hgl hgc ψ.continuous hψc hψ0 hψ1 (q : ℝ≥0) hΘ hWm hlawW hpair

end MatedCRT.FirstPass.Derived
