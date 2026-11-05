import MatedCRT.Proofs.Measurability.VagueWholePlane

/-! # Vague convergence from a countable dense family of tests

If the integrals of a sequence of measures, finite on compacts, against every member of a countable
uniformly dense family of tests (`VagueWholePlane.IsDenseTestFamilyC`) converge to the integrals
against a measure `ν`, finite on compacts, then so do the integrals against every continuous
compactly supported function. This is used for the degree measures `μ^ε_h → 6 μ_h` (Lemma 2.10)
along a subsequence, almost surely, in the proof of Lemma 3.3 (paper, lines 1200-1208). -/

namespace MatedCRT.GreenEnvironment

open MeasureTheory Filter Topology Set
open MatedCRT.VagueWholePlane

/-- Convergence of integrals against a dense test family identifies the limit of the integrals
against every continuous compactly supported test. -/
theorem tendsto_integral_of_denseTestFamilyC {μs : ℕ → Measure ℂ} {ν : Measure ℂ}
    (hfin : ∀ K, IsCompact K → ∀ᶠ k in atTop, μs k K < ⊤)
    (hν : ∀ K, IsCompact K → ν K < ⊤)
    {F : Set (ℂ → ℝ)} (hF : IsDenseTestFamilyC F)
    (hconv : ∀ g ∈ F, Tendsto (fun k => ∫ z, g z ∂(μs k)) atTop (𝓝 (∫ z, g z ∂ν)))
    (f : ℂ → ℝ) (hf : IsTestC f) :
    Tendsto (fun k => ∫ z, f z ∂(μs k)) atTop (𝓝 (∫ z, f z ∂ν)) := by
  obtain ⟨K, hK, hfK, ⟨φ, hφF, hφ0, hφ1⟩, happrox⟩ := hF.2 f hf
  have hφ := hF.1 φ hφF
  have hlφ := hconv φ hφF
  rw [Metric.tendsto_atTop]
  intro ε hε
  set B : ℝ := |∫ z, φ z ∂ν| + 1 with hBdef
  have hB0 : 0 < B := by positivity
  set η : ℝ := ε / (4 * B) with hηdef
  have hη0 : 0 < η := by positivity
  obtain ⟨g, hgF, hgK, hfg⟩ := happrox η hη0
  have hg := hF.1 g hgF
  have hkey : ∀ m : Measure ℂ, m K < ⊤ → m (tsupport φ) < ⊤ →
      |∫ z, f z ∂m - ∫ z, g z ∂m| ≤ η * ∫ z, φ z ∂m := by
    intro m hmK hmφ
    have hfi : Integrable f m := hf.integrable (lt_of_le_of_lt (measure_mono hfK) hmK)
    have hgi : Integrable g m := hg.integrable (lt_of_le_of_lt (measure_mono hgK) hmK)
    have hφi : Integrable φ m := hφ.integrable hmφ
    rw [← integral_sub hfi hgi, ← integral_const_mul]
    refine (abs_integral_le_integral_abs).trans
      (integral_mono (hfi.sub hgi).abs (hφi.const_mul η) fun z => ?_)
    show |f z - g z| ≤ η * φ z
    by_cases hz : z ∈ K
    · have h1 := hφ1 z hz
      have h2 := hfg z
      nlinarith
    · have hfz : f z = 0 := image_eq_zero_of_notMem_tsupport fun h => hz (hfK h)
      have hgz : g z = 0 := image_eq_zero_of_notMem_tsupport fun h => hz (hgK h)
      rw [hfz, hgz, sub_zero, abs_zero]
      exact mul_nonneg hη0.le (hφ0 z)
  have hlg := hconv g hgF
  have hev : ∀ᶠ k in atTop, μs k K < ⊤ ∧ μs k (tsupport φ) < ⊤ ∧
      dist (∫ z, φ z ∂(μs k)) (∫ z, φ z ∂ν) < 1 ∧
      dist (∫ z, g z ∂(μs k)) (∫ z, g z ∂ν) < ε / 4 :=
    (hfin K hK).and ((hfin _ hφ.2).and ((Metric.tendsto_nhds.1 hlφ 1 one_pos).and
      (Metric.tendsto_nhds.1 hlg _ (by positivity))))
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  refine ⟨N, fun k hk => ?_⟩
  obtain ⟨hK1, hK2, h1, h2⟩ := hN k hk
  have e1 := hkey (μs k) hK1 hK2
  have e2 := hkey ν (hν K hK) (hν _ hφ.2)
  rw [Real.dist_eq] at h1 h2 ⊢
  have hle := le_abs_self (∫ z, φ z ∂ν)
  have hφk : ∫ z, φ z ∂(μs k) ≤ B := by
    have := (abs_lt.1 h1).2
    linarith
  have hφν : ∫ z, φ z ∂ν ≤ B := by linarith
  have hηB : η * B = ε / 4 := by
    rw [hηdef]
    field_simp
  have b1 : η * ∫ z, φ z ∂(μs k) ≤ η * B := mul_le_mul_of_nonneg_left hφk hη0.le
  have b2 : η * ∫ z, φ z ∂ν ≤ η * B := mul_le_mul_of_nonneg_left hφν hη0.le
  have a1 := abs_le.1 (e1.trans b1)
  have a2 := abs_lt.1 h2
  have a3 := abs_le.1 (e2.trans b2)
  rw [abs_lt]
  constructor <;> linarith

end MatedCRT.GreenEnvironment
