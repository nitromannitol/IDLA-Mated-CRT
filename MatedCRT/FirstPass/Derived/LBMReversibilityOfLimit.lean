import MatedCRT.FirstPass.Derived.DegreeCutoffMeasurable
import MatedCRT.FirstPass.Derived.ReversibilityPairingDiscrete
import MatedCRT.FirstPass.Derived.LevyProkhorovWeakFiniteMeasure
import MatedCRT.FirstPass.Derived.DegreeCutoffLevyProkhorov
import MatedCRT.FirstPass.Derived.InterpolatedLawAssembly
import LatticeProb.Prob.ConvergingTogetherProjection
import MatedCRT.External.SLE
import LatticeProb.Prob.PairingLawLimitZero
import LatticeProb.Prob.PairingSymmetricAllTimes

/-!
# Reversibility of the LQG measure for a subsequential limit of the walk laws (BG20 Lemma 7.6)

Let `S` be a valid environment, `ε_n → 0⁺`, and let `(D n, P̃^{ε_n})` converge in law to `ν`, where
`P̃^ε = interpWalkLaw S η' ε` is the interpolated quenched law of the embedded walk and `D n` is a random
datum whose coordinate `μX (D n)` is almost surely the LQG measure `μ_h`. Then for `ν`-almost every
`(d, P)` and every `s ≥ 0` the space-time measure `m_s(dz, dw) = μ_h(dz) P_z(X_s ∈ dw)`, with
`μ_h = μX d`, is invariant under `(z, w) ↦ (w, z)`: the LQG measure is reversible for the limiting
process (BG20 Lemma 7.6, without Lemma 7.7).

The proof follows BG20 Section 7.2:

* (C2) the discrete reversibility identity `deg(x) p_n(x, y) = deg(y) p_n(y, x)` makes the
  reversibility pairing `Φ_{f,g,t}(ν^ε, P̃^ε)` at the cutoff degree measure tend to `0` in probability
  at the lattice times `t_n = ⌊m_{ε_n} s⌋ / m_{ε_n}`;
* (C3) `(ν^{ε_n}, P̃^{ε_n}, t_n)` converges in law to the image of `ν` under
  `(d, P) ↦ (6 ψ μX d, P, s)`;
* (C4) by continuous mapping the pairing of the limit vanishes almost surely
  (`LatticeProb.ae_reversibilityPairing_eq_zero_of_tendsto_law`); at the cutoff-weighted measure
  `6 ψ μ_h` it is `6 (∫ f E_{P_z}[g(X_s)] dμ_h - ∫ g E_{P_z}[f(X_s)] dμ_h)`; a countable family of test
  functions and the rational times give the swap invariance at every time
  (`LatticeProb.ae_compProd_evalLawKernel_swap_of_pairing_symm_rat`).

The lattice times converge to `s` because `m_ε ≥ C⁻¹ ε⁻¹` for small `ε` (`MepsScalingInput`).

* `tendsto_latticeTime`, `tendsto_latticeTime_mε`: the lattice times converge.
* `ae_integral_pairing_symm_of_tendsto_law`: the symmetric pairing for a limit in law.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Metric LatticeProb
open MarkovProcess (ContinuousPath)
open scoped NNReal ENNReal BoundedContinuousFunction

namespace MatedCRT.FirstPass.Derived

/-! ### Lattice times -/

/-- If `m_n > 0` and `m_n⁻¹ ≤ c_n → 0` eventually, the lattice times `⌊m_n s⌋ / m_n` converge to `s`. -/
theorem tendsto_latticeTime {m c : ℕ → ℝ} (hm : ∀ᶠ n in atTop, 0 < m n ∧ (m n)⁻¹ ≤ c n)
    (hc : Tendsto c atTop (𝓝 0)) (s : ℝ≥0) :
    Tendsto (fun n => latticeTime (m n) s) atTop (𝓝 s) := by
  rw [← NNReal.tendsto_coe]
  have hlow : Tendsto (fun n => (s : ℝ) - c n) atTop (𝓝 (s : ℝ)) := by
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (s : ℝ)) atTop _).sub hc
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [hm] with n hn
    have hne : m n ≠ 0 := hn.1.ne'
    have h1 := mul_latticeTime hn.1.le s
    have h2 := Nat.lt_floor_add_one (m n * (s : ℝ))
    rw [← h1] at h2
    have h3 : (m n)⁻¹ * (m n * (s : ℝ)) < (m n)⁻¹ * (m n * (latticeTime (m n) s : ℝ) + 1) :=
      mul_lt_mul_of_pos_left h2 (inv_pos.2 hn.1)
    have e1 : (m n)⁻¹ * (m n * (s : ℝ)) = s := by
      rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]
    have e2 : (m n)⁻¹ * (m n * (latticeTime (m n) s : ℝ) + 1) =
        (latticeTime (m n) s : ℝ) + (m n)⁻¹ := by
      rw [mul_add, ← mul_assoc, inv_mul_cancel₀ hne, one_mul, mul_one]
    rw [e1, e2] at h3
    linarith [hn.2]
  · filter_upwards [hm] with n hn
    exact NNReal.coe_le_coe.2 (latticeTime_le hn.1.le s)

/-- **The lattice times converge**: for a valid environment and `ε_n → 0⁺`, the lattice times
`⌊m_{ε_n} s⌋ / m_{ε_n}` converge to `s`, since `m_ε ≥ C⁻¹ ε⁻¹` for small `ε` (eq:meps-scaling). -/
theorem tendsto_latticeTime_mε {𝒮 : SpaceFillingSLEModel} (hM : MepsScalingInput 𝒮) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    (hS : S.IsValid 𝒮 γ) {ε : ℕ → ℝ} (hε0 : ∀ n, 0 < ε n) (hε : Tendsto ε atTop (𝓝 0))
    (s : ℝ≥0) : Tendsto (fun n => latticeTime (S.mε (ε n)) s) atTop (𝓝 s) := by
  obtain ⟨C, hC1, hCS⟩ := hM γ hγ hγ2
  obtain ⟨ε₀, hε₀, hbound⟩ := hCS Ω S hS
  have hC0 : 0 < C := by linarith
  refine tendsto_latticeTime (c := fun n => C * ε n) ?_ (by simpa using hε.const_mul C) s
  filter_upwards [hε.eventually (gt_mem_nhds hε₀)] with n hn
  have hlow : 0 < C⁻¹ * (ε n)⁻¹ := mul_pos (inv_pos.2 hC0) (inv_pos.2 (hε0 n))
  have h1 := (hbound (ε n) (hε0 n) hn).1
  refine ⟨hlow.trans_le h1, ?_⟩
  have h2 := inv_anti₀ hlow h1
  rwa [mul_inv, inv_inv, inv_inv] at h2

/-! ### The pairing of a limit in law -/

theorem exists_abs_le_of_lipschitzWith_of_hasCompactSupport {f : ℂ → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (hfc : HasCompactSupport f) : ∃ C, ∀ z, |f z| ≤ C := by
  obtain ⟨C, hC⟩ := hf.continuous.bounded_above_of_compact_support hfc
  exact ⟨C, fun z => by simpa [Real.norm_eq_abs] using hC z⟩

/-- **The pairing of a limit in law is symmetric.** Let `W n` be random elements of
`FiniteMeasure ℂ × C(ℂ, Prob(ContinuousPath ℂ)) × ℝ≥0` converging in law to the image of a measure `ν`
under `p ↦ (6 ψ μ p, Q p, s)`, for locally finite measures `μ p` and law fields `Q p`. If the
reversibility pairings `Φ_{f,g}(W n)` tend to `0` in probability, then for `ν`-almost every `p`,
`∫ f(z) E_{Q_p(z)}[g(X_s)] dμ_p(z) = ∫ g(z) E_{Q_p(z)}[f(X_s)] dμ_p(z)`. -/
theorem ae_integral_pairing_symm_of_tendsto_law {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    [MeasurableSpace (FiniteMeasure ℂ × C(ℂ, ProbabilityMeasure (ContinuousPath ℂ)) × ℝ≥0)]
    [OpensMeasurableSpace (FiniteMeasure ℂ × C(ℂ, ProbabilityMeasure (ContinuousPath ℂ)) × ℝ≥0)]
    {T : Type*} [MeasurableSpace T] {ν : Measure T} (μ : T → Measure ℂ)
    [∀ p, IsLocallyFiniteMeasure (μ p)] (Q : T → C(ℂ, ProbabilityMeasure (ContinuousPath ℂ)))
    {f g ψ : ℂ → ℝ} {Kf Kg : ℝ≥0} (hfl : LipschitzWith Kf f) (hfc : HasCompactSupport f)
    (hgl : LipschitzWith Kg g) (hgc : HasCompactSupport g) (hψ : Continuous ψ)
    (hψc : HasCompactSupport ψ) (hψ0 : ∀ z, 0 ≤ ψ z) (hψ1 : EqOn ψ 1 (tsupport f ∪ tsupport g))
    (s : ℝ≥0) (hΘ : AEMeasurable (fun p => (cutoffWeightedMeasure (μ p) hψ hψc 6, Q p, s)) ν)
    {W : ℕ → Ω → FiniteMeasure ℂ × C(ℂ, ProbabilityMeasure (ContinuousPath ℂ)) × ℝ≥0}
    (hW : ∀ n, AEMeasurable (W n) P)
    (hlaw : ∀ F : (FiniteMeasure ℂ × C(ℂ, ProbabilityMeasure (ContinuousPath ℂ)) × ℝ≥0) →ᵇ ℝ,
      Tendsto (fun n => ∫ ω, F (W n ω) ∂P) atTop
        (𝓝 (∫ w, F w ∂(ν.map fun p => (cutoffWeightedMeasure (μ p) hψ hψc 6, Q p, s)))))
    (hpair : TendstoInMeasure P
      (fun n ω => reversibilityPairing f g ψ (W n ω).1 (W n ω).2.1 (W n ω).2.2) atTop (fun _ => 0)) :
    ∀ᵐ p ∂ν, ∫ z, f z * (∫ X, g (X s) ∂(Q p z : Measure (ContinuousPath ℂ))) ∂(μ p) =
      ∫ z, g z * (∫ X, f (X s) ∂(Q p z : Measure (ContinuousPath ℂ))) ∂(μ p) := by
  have h0 := ae_reversibilityPairing_eq_zero_of_tendsto_law hW hlaw
    (exists_abs_le_of_lipschitzWith_of_hasCompactSupport hfl hfc) hfl
    (exists_abs_le_of_lipschitzWith_of_hasCompactSupport hgl hgc) hgl hψ hψc hpair
  filter_upwards [ae_of_ae_map hΘ h0] with p hp
  have hp' := (reversibilityPairing_cutoffWeightedMeasure (μ p) (Q p) s hψ hψc hψ0 hψ1
    (c := 6) (by norm_num)).symm.trans hp
  exact sub_eq_zero.1 ((mul_eq_zero.1 hp').resolve_left (by norm_num))

/-! ### The walk-side tuple converges in law -/

/-- **The cell diameters tend to `0` in probability** along `ε → 0⁺`, for a valid environment. -/
theorem tendsto_measure_ofReal_lt_maxCellDiam_nhdsGT {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    {η' : Ω → C(ℝ, ℂ)} (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) (R a : ℝ) (ha : 0 < a) :
    Tendsto (fun e => S.P {ω | ENNReal.ofReal a < maxCellDiam e (⇑(η' ω)) R}) (𝓝[>] 0) (𝓝 0) :=
  tendsto_iff_seq_tendsto.2 fun _ hu =>
    hdiam_of_isValid hS hae (tendsto_nhdsWithin_iff.1 hu).1 R a ha

/-- **The cutoff degree measure, the walk law and the times converge in law** (BG20 Section 7.2).
Let `(D n, P̃^{ε_n})` converge in law to `ν`, where `P̃^ε = interpWalkLaw S η' ε`, let `π d` be a
finite measure depending Lévy–Prokhorov continuously on the datum `d`, with `π (D n) = 6 ψ μ_h`
almost surely, and let `t n → s₀`. Then `(ν^{ε_n}, P̃^{ε_n}, t n)`, with `ν^ε` the degree measure
cut off by `ψ`, converges in law to the image of `ν` under `(d, P) ↦ (π d, P, s₀)`. This is the
converging-together lemma with a projected coordinate
(`LatticeProb.tendsto_integral_levyProkhorov_projection_of_tendstoInMeasure_levyProkhorovDist`),
the Lévy–Prokhorov convergence of the cutoff degree measure
(`tendstoInMeasure_levyProkhorovDist_degreeCutoffMeasure_projection`), and the continuity of the
identity from the Lévy–Prokhorov to the weak topology (`continuous_levyProkhorov_toFiniteMeasure`). -/
theorem tendsto_integral_degreeCutoffMeasure_interpWalkLaw_of_tendsto_law
    [MeasurableSpace (LevyProkhorov (FiniteMeasure ℂ))]
    [BorelSpace (LevyProkhorov (FiniteMeasure ℂ))]
    [MeasurableSpace (FiniteMeasure ℂ × C(ℂ, ProbabilityMeasure (ContinuousPath ℂ)) × ℝ≥0)]
    [OpensMeasurableSpace (FiniteMeasure ℂ × C(ℂ, ProbabilityMeasure (ContinuousPath ℂ)) × ℝ≥0)]
    {𝒮 : SpaceFillingSLEModel} (hD27 : DegreeMeasureConvergenceStmt 𝒮)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    (hS : S.IsValid 𝒮 γ) {η' : Ω → C(ℝ, ℂ)} (hη' : Measurable η')
    (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω)
    {ε : ℕ → ℝ} (hε0 : ∀ n, 0 < ε n) (hε : Tendsto ε atTop (𝓝 0))
    {X : Type*} [TopologicalSpace X] [TopologicalSpace.PseudoMetrizableSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    {D : ℕ → Ω → X} (hD : ∀ n, AEMeasurable (D n) S.P)
    {ν : Measure (X × C(ℂ, ProbabilityMeasure (ContinuousPath ℂ)))}
    (hlaw : ∀ F : (X × C(ℂ, ProbabilityMeasure (ContinuousPath ℂ))) →ᵇ ℝ,
      Tendsto (fun n => ∫ ω, F (D n ω, interpWalkLaw S η' (ε n) ω) ∂S.P) atTop (𝓝 (∫ p, F p ∂ν)))
    {ψ : ℂ → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) (hψ0 : ∀ z, 0 ≤ ψ z)
    {π : X → FiniteMeasure ℂ}
    (hπD : ∀ n, ∀ᵐ ω ∂S.P,
      (π (D n ω) : Measure ℂ) = (S.μ ω).withDensity fun z => ENNReal.ofReal (6 * ψ z))
    (hπ : Continuous fun d => LevyProkhorov.ofMeasure (π d))
    {t : ℕ → ℝ≥0} {s₀ : ℝ≥0} (ht : Tendsto t atTop (𝓝 s₀))
    (hmap : AEMeasurable (fun p : X × C(ℂ, ProbabilityMeasure (ContinuousPath ℂ)) =>
      (π p.1, p.2, s₀)) ν) :
    ∀ F : (FiniteMeasure ℂ × C(ℂ, ProbabilityMeasure (ContinuousPath ℂ)) × ℝ≥0) →ᵇ ℝ,
      Tendsto (fun n => ∫ ω, F (degreeCutoffMeasure (S.mult (ε n) ω) (ε n)
          (vertexPoint (ε n) ⇑(η' ω)) ψ, interpWalkLaw S η' (ε n) ω, t n) ∂S.P) atTop
        (𝓝 (∫ w, F w ∂(ν.map fun p => (π p.1, p.2, s₀)))) := by
  intro F
  have := hS.isProbabilityMeasure
  have hεw : Tendsto ε atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hε, Eventually.of_forall hε0⟩
  have hμπ := tendstoInMeasure_levyProkhorovDist_degreeCutoffMeasure_projection hγ hγ2 hS
    (hD27 γ hγ hγ2 Ω S hS) hae hψ hψc hψ0
    (tendsto_measure_ofReal_lt_maxCellDiam_nhdsGT hS hae) hεw hπD
  have hμ := hμ_degreeCutoffMeasure_of_isValid hS hae hψ.measurable hψc hε0
  have hQ : ∀ n, AEMeasurable (interpWalkLaw S η' (ε n)) S.P := fun n =>
    aemeasurable_interpWalkLaw hS hη' hae (hε0 n)
  have hG := tendsto_integral_levyProkhorov_projection_of_tendstoInMeasure_levyProkhorovDist
    hD hμ hQ hπ hlaw hμπ ht
  let Φ : C(X × LevyProkhorov (FiniteMeasure ℂ) × C(ℂ, ProbabilityMeasure (ContinuousPath ℂ)) × ℝ≥0,
      FiniteMeasure ℂ × C(ℂ, ProbabilityMeasure (ContinuousPath ℂ)) × ℝ≥0) :=
    ⟨fun x => (LevyProkhorov.toMeasure x.2.1, x.2.2.1, x.2.2.2),
      (continuous_levyProkhorov_toFiniteMeasure.comp continuous_snd.fst).prodMk
        (continuous_snd.snd.fst.prodMk continuous_snd.snd.snd)⟩
  have e : (∫ p, F.compContinuous Φ (p.1, LevyProkhorov.ofMeasure (π p.1), p.2, s₀) ∂ν) =
      ∫ w, F w ∂(ν.map fun p => (π p.1, p.2, s₀)) := by
    rw [integral_map hmap F.continuous.aestronglyMeasurable]
    rfl
  rw [← e]
  exact hG (F.compContinuous Φ)

/-! ### Reversibility for a subsequential limit -/

/-- **The LQG measure is reversible for a subsequential limit of the walk laws** (BG20 Lemma 7.6).
Let `S` be a valid environment with a measurable version `η'` of the space-filling SLE curve, let
`ε n → 0⁺`, and assume the input of Lemma 2.7 (`DegreeMeasureConvergenceStmt`), the scaling
`m_ε ≍ ε⁻¹` (`MepsScalingInput`) and the equicontinuity in law `hEqLaw` of the walk laws. Let
`D n` be random data in a second countable metrizable space `X` whose coordinate `μX (D n)` is
almost surely the LQG measure `μ_h`, with `d ↦ 6 ψ μX d` Lévy–Prokhorov continuous for every
cutoff `ψ`, and let `(D n, P̃^{ε_n})` converge in law to `ν`. Then for `ν`-almost every `(d, P)` and
every `s ≥ 0`, the measure `m_s(dz, dw) = μX d (dz) P_z(X_s ∈ dw)` is invariant under
`(z, w) ↦ (w, z)`. -/
theorem ae_compProd_evalLawKernel_swap_of_tendsto_law
    {𝒮 : SpaceFillingSLEModel} (hD27 : DegreeMeasureConvergenceStmt 𝒮) (hM : MepsScalingInput 𝒮)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    (hS : S.IsValid 𝒮 γ) {η' : Ω → C(ℝ, ℂ)} (hη' : Measurable η')
    (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω)
    {ε : ℕ → ℝ} (hε0 : ∀ n, 0 < ε n) (hε : Tendsto ε atTop (𝓝 0))
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
    tendsto_latticeTime_mε hM hγ hγ2 hS hε0 hε _
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
