import MatedCRT.FirstPass.S3c.CommonEquicontinuity

/-!
# Lemma 3.1 (corrected, [C11]): the measurable selection on one almost-sure event

`tightness_selection_common` is `tightnessSelectionStep_of_meps` (MatedCRT/Proofs/Sec3/DiscretePotentialTightness/
SelectionStep.lean) with the almost-sure event fixed before the domain and the data. The measurable subsequence `Φ` is
still chosen after the data (`Tightness.exists_measurable_diagonal_subseq` applies to each data separately), and its
pointwise properties hold at every `ω` of the common event `Ω₀`, which is `Ω₁` (from `tightness_equicontinuity_common`)
intersected with the environment events `isAreaParametrized` and `ae_tendsto_cocompact`.
-/

open MatedCRT.Tightness
open MeasureTheory ProbabilityTheory Filter Topology Set Metric HarmonicBalls
open scoped ENNReal NNReal

namespace MatedCRT.S3c

/-- **Lemma 3.1, selection with a common event** (C11). For a deterministic polynomially summable scale sequence `e`
there is one probability-one event `Ω₀`, chosen before the domain and the data. For every connected open `D ⊆ B_ρ`, every
`σ(h,η)`-measurable `E` with values in `range e` tending to zero, and every `u`, `C` satisfying the hypotheses of Lemma 3.1,
there is a `σ(h,η)`-measurable subsequence `Φ` such that, at every `ω ∈ Ω₀`, `E ∘ Φ` converges as needed: `ū^ε → ū`
uniformly on compacts of `D`, and on `cl(D)` under the "moreover" hypotheses. -/
theorem tightness_selection_common {𝒮 : SpaceFillingSLEModel} (hm : MepsScalingInput 𝒮)
    (h217 : BoundedExitTimeRVStmt) (h218 : ExitTimeUpperBoundStmt 𝒮) (hH : DiscreteHolderContinuityCorrectedStep 𝒮)
    (hadj : AdjacentCellsMeetAeStep 𝒮) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
    ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
    ∀ e : ℕ → ℝ, IsPolySummableScales e → ∃ Ω₀ : Set Ω, (∀ᵐ ω ∂S.P, ω ∈ Ω₀) ∧
    ∀ D : Set ℂ, D ⊆ ball 0 ρ → IsOpen D → IsConnected D →
    ∀ (E : Ω → ℕ → ℝ) (u : Ω → ℕ → ℤ → ℝ) (C : Ω → ℝ), IsTightnessData S D e E u C →
    ∃ Φ : Ω → ℕ → ℕ, (∀ k, Measurable[S.envSigma] fun ω => Φ ω k) ∧
      ∀ ω ∈ Ω₀, StrictMono (Φ ω) ∧ ∃ ubar : ℂ → ℝ, ContinuousOn ubar D ∧
        (∀ O : Set ℂ, IsCompact O → closure O ⊆ D →
          TendstoUniformlyOn (fun k => rescale (S.mε (E ω (Φ ω k))) (E ω (Φ ω k)) (S.η ω) (u ω (Φ ω k)))
            ubar atTop O) ∧
        ((SimplyConnectedSpace D ∧
            (∀ n, ∀ a ∈ interiorCellVertices (E ω n) (S.η ω) D, matedLaplacian (S.mult (E ω n) ω) (u ω n) a = 0) ∧
            ∃ χ C' : ℝ, 0 < χ ∧ χ ≤ 1 ∧ 0 < C' ∧ ∀ n, E ω n < 1 →
              ∀ a ∈ cellVertices (E ω n) (S.η ω) (frontier D), ∀ b ∈ cellVertices (E ω n) (S.η ω) (frontier D),
                |u ω n a - u ω n b| ≤
                  C' / E ω n * max (E ω n) ‖vertexPoint (E ω n) (S.η ω) a - vertexPoint (E ω n) (S.η ω) b‖ ^ χ) →
          TendstoUniformlyOn (fun k => rescale (S.mε (E ω (Φ ω k))) (E ω (Φ ω k)) (S.η ω) (u ω (Φ ω k)))
            ubar atTop (closure D)) := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS e he
  obtain ⟨Ω₁, hΩ₁, hEq⟩ := tightness_equicontinuity_common h217 h218 hH hadj γ hγ hγ2 ρ hρ hρ1 Ω S hS e he
  obtain ⟨Cm, hCm1, hmS⟩ := hm γ hγ hγ2
  obtain ⟨ε₀, hε₀, hmε⟩ := hmS Ω S hS
  have hCm : 0 < Cm := one_pos.trans hCm1
  obtain ⟨Ω₀, hΩ₀, hQ⟩ :=
    exists_common_of_ae (hΩ₁.and (hS.isAreaParametrized.and hS.ae_tendsto_cocompact))
  refine ⟨Ω₀, hΩ₀, fun D hDρ hDo hDc E u C hdata => ?_⟩
  have hEqD := hEq D hDρ hDo hDc E u C hdata
  obtain ⟨hEm, hEe, hEt, hum, -, hCp, -, hbd⟩ := hdata
  have hEpos : ∀ ω n, 0 < E ω n := fun ω n => by
    obtain ⟨j, hj⟩ := hEe ω n
    rw [← hj]
    exact he.1 j
  have hmev : ∀ ω, ∀ᶠ n in atTop, 0 ≤ (S.mε (E ω n))⁻¹ ∧ (S.mε (E ω n))⁻¹ ≤ Cm * E ω n := by
    intro ω
    filter_upwards [(hEt ω).eventually (gt_mem_nhds hε₀)] with n hn
    have h := (hmε (E ω n) (hEpos ω n) hn).1
    have hpos : 0 < Cm⁻¹ * (E ω n)⁻¹ := mul_pos (inv_pos.2 hCm) (inv_pos.2 (hEpos ω n))
    refine ⟨inv_nonneg.2 (hpos.le.trans h), ?_⟩
    have h2 := inv_anti₀ hpos h
    rwa [mul_inv, inv_inv, inv_inv] at h2
  set y : Ω → ℕ → ℕ → ℝ := fun ω n c =>
    Tightness.proxyCoord (E ω) (S.η ω) D (fun n => S.mε (E ω n)) (u ω) n c with hy_def
  have hy : ∀ n c, Measurable[S.envSigma] fun ω => y ω n c := by
    intro n c
    exact @Tightness.measurable_comp_range Ω S.envSigma e (fun ω => E ω n) (hEm n) (fun ω => hEe ω n)
      (fun ε ω => Tightness.proxyValue ε (S.η ω) D (TopologicalSpace.denseSeq ℂ c.unpair.1)
        (1 / ((c.unpair.2 : ℝ) + 1)) fun a => (S.mε ε)⁻¹ * u ω n a)
      fun j => @Tightness.measurable_proxyValue Ω S.envSigma S.η (fun ω a => (S.mε (e j))⁻¹ * u ω n a)
        (Tightness.measurable_eta_of_envSigma S) (fun a => (hum n a).const_mul _) D hDo.measurableSet
        (e j) _ _
  obtain ⟨Φ, hΦm, hΦ⟩ := @Tightness.exists_measurable_diagonal_subseq Ω S.envSigma y hy
  refine ⟨Φ, hΦm, ?_⟩
  intro ω hωΩ
  obtain ⟨hω1, hη, hp⟩ := hQ ω hωΩ
  have hω := hEqD ω hω1
  obtain ⟨hmono, hconvY⟩ := hΦ ω
  have hbddY : ∀ c, ∃ M, ∀ᶠ n in atTop, |y ω n c| ≤ M := by
    intro c
    refine ⟨Cm * C ω, ?_⟩
    filter_upwards [hmev ω] with n hn
    have hC := hCp ω
    refine Tightness.abs_proxyValue_le (mul_pos hCm hC).le fun k hk => ?_
    have hkD : k ∈ cellVertices (E ω n) (S.η ω) D := Tightness.mem_cellVertices_of_vertexPoint_mem (hEpos ω n) hk
    show |(S.mε (E ω n))⁻¹ * u ω n k| ≤ Cm * C ω
    have hE := hEpos ω n
    rw [abs_mul, abs_of_nonneg hn.1]
    calc (S.mε (E ω n))⁻¹ * |u ω n k| ≤ (Cm * E ω n) * (C ω / E ω n) :=
          mul_le_mul hn.2 (hbd ω n k hkD) (abs_nonneg _) (mul_pos hCm hE).le
      _ = Cm * C ω * (E ω n * (E ω n)⁻¹) := by ring
      _ = Cm * C ω := by rw [mul_inv_cancel₀ hE.ne', mul_one]
  have hY : ∀ c, ∃ l, Tendsto (fun k => Tightness.proxyCoord (E ω) (S.η ω) D (fun n => S.mε (E ω n)) (u ω)
      (Φ ω k) c) atTop (𝓝 l) := fun c => hconvY c (hbddY c)
  obtain ⟨ubar, h1, h2, h3⟩ := Tightness.tightness_of_proxies hDo (isBounded_ball.subset hDρ) hη.1 hp hη.2.2.1
    (hEpos ω) (hEt ω) hCm (hmev ω) hω.1 hmono hY
  exact ⟨hmono, ubar, h1, h2, fun hH => h3 (hω.2 hH)⟩

end MatedCRT.S3c
