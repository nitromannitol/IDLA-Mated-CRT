import MatedCRT.FirstPass.S3c.PointwiseEquicontinuity

/-!
# Lemma 3.1 (corrected, [C11]), samplewise admissibility: the measurable selection

`tightness_selection_pointwise` is `tightness_selection_common` (FirstPass/S3c/CommonSelection.lean) with the
admissibility of the data moved inside the implication on the common event `Ω₀` (§1.3 of
notes/fp-gaps/CHATGPT-idla-3-1-audit.md). Only the measurability of the data is imposed on the whole carrier.

The diagonal extraction `Tightness.exists_measurable_diagonal_subseq` needs its input measurable and is pointwise: its
convergence conclusion at `ω` uses only the boundedness of `y ω · c` at `ω`. The measurability of `y` needs the range
condition `E ω n ∈ range e` at every `ω`, which holds only on the samples; it is restored by replacing `E` by
`E' ω n := if E ω n ∈ range e then E ω n else e 0`, which is measurable and equals `E` at every admissible sample.
-/

open MatedCRT.Tightness
open MeasureTheory ProbabilityTheory Filter Topology Set Metric HarmonicBalls
open scoped ENNReal NNReal

namespace MatedCRT.S3c

/-- **Lemma 3.1, selection with samplewise admissibility** (C11): one probability-one event `Ω₀`, chosen before the
domain and the data; for every connected open `D ⊆ B_ρ` and every measurable data `E, u, C`, there is a measurable
subsequence `Φ` such that at every `ω ∈ Ω₀` at which the data are admissible (`PointwiseTightnessData`), `Φ ω` is strictly
increasing and the conclusion holds. -/
theorem tightness_selection_pointwise {𝒮 : SpaceFillingSLEModel} (hm : MepsScalingInput 𝒮)
    (h217 : BoundedExitTimeRVStmt) (h218 : ExitTimeUpperBoundStmt 𝒮) (hH : DiscreteHolderContinuityCorrectedStep 𝒮)
    (hadj : AdjacentCellsMeetAeStep 𝒮) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
    ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
    ∀ e : ℕ → ℝ, IsPolySummableScales e → ∃ Ω₀ : Set Ω, (∀ᵐ ω ∂S.P, ω ∈ Ω₀) ∧
    ∀ D : Set ℂ, D ⊆ ball 0 ρ → IsOpen D → IsConnected D →
    ∀ (E : Ω → ℕ → ℝ) (u : Ω → ℕ → ℤ → ℝ) (C : Ω → ℝ),
    (∀ n, Measurable[S.envSigma] fun ω => E ω n) → (∀ n a, Measurable[S.envSigma] fun ω => u ω n a) →
    Measurable[S.envSigma] C →
    ∃ Φ : Ω → ℕ → ℕ, (∀ k, Measurable[S.envSigma] fun ω => Φ ω k) ∧
      ∀ ω ∈ Ω₀, PointwiseTightnessData S D e E u C ω → StrictMono (Φ ω) ∧ ∃ ubar : ℂ → ℝ, ContinuousOn ubar D ∧
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
  classical
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS e he
  obtain ⟨Ω₁, hΩ₁, hEq⟩ := tightness_equicontinuity_pointwise h217 h218 hH hadj γ hγ hγ2 ρ hρ hρ1 Ω S hS e he
  obtain ⟨Cm, hCm1, hmS⟩ := hm γ hγ hγ2
  obtain ⟨ε₀, hε₀, hmε⟩ := hmS Ω S hS
  have hCm : 0 < Cm := one_pos.trans hCm1
  obtain ⟨Ω₀, hΩ₀, hQ⟩ :=
    exists_common_of_ae (hΩ₁.and (hS.isAreaParametrized.and hS.ae_tendsto_cocompact))
  refine ⟨Ω₀, hΩ₀, fun D hDρ hDo hDc E u C hEm hum hCmeas => ?_⟩
  -- the scales restored into `range e` everywhere (equal to `E` on every admissible sample)
  obtain ⟨E', hE'def⟩ : ∃ E' : Ω → ℕ → ℝ, E' = fun ω n => if E ω n ∈ range e then E ω n else e 0 :=
    ⟨_, rfl⟩
  have hE'mem : ∀ ω n, E' ω n ∈ range e := by
    intro ω n
    rw [hE'def]
    by_cases h : E ω n ∈ range e
    · simp [h]
    · simp [h]
  have hE'meas : ∀ n, Measurable[S.envSigma] fun ω => E' ω n := by
    intro n
    rw [hE'def]
    exact Measurable.ite ((hEm n) (Set.Countable.measurableSet (Set.countable_range e)))
      (hEm n) measurable_const
  have hE'ω : ∀ ω, (∀ n, E ω n ∈ range e) → E' ω = E ω := by
    intro ω h
    rw [hE'def]
    funext n
    simp [h n]
  obtain ⟨y, hy_def⟩ : ∃ y : Ω → ℕ → ℕ → ℝ,
      y = fun ω n c => Tightness.proxyCoord (E' ω) (S.η ω) D (fun n => S.mε (E' ω n)) (u ω) n c :=
    ⟨_, rfl⟩
  have hy : ∀ n c, Measurable[S.envSigma] fun ω => y ω n c := by
    intro n c
    rw [hy_def]
    exact @Tightness.measurable_comp_range Ω S.envSigma e (fun ω => E' ω n) (hE'meas n) (fun ω => hE'mem ω n)
      (fun ε ω => Tightness.proxyValue ε (S.η ω) D (TopologicalSpace.denseSeq ℂ c.unpair.1)
        (1 / ((c.unpair.2 : ℝ) + 1)) fun a => (S.mε ε)⁻¹ * u ω n a)
      fun j => @Tightness.measurable_proxyValue Ω S.envSigma S.η (fun ω a => (S.mε (e j))⁻¹ * u ω n a)
        (Tightness.measurable_eta_of_envSigma S) (fun a => (hum n a).const_mul _) D hDo.measurableSet
        (e j) _ _
  obtain ⟨Φ, hΦm, hΦ⟩ := @Tightness.exists_measurable_diagonal_subseq Ω S.envSigma y hy
  refine ⟨Φ, hΦm, ?_⟩
  intro ω hωΩ hpw
  obtain ⟨hEe, hEt, hCp, hlap, hbd⟩ := hpw
  obtain ⟨hω1, hη, hp⟩ := hQ ω hωΩ
  have hω := hEq D hDρ hDo hDc E u C ω hω1 ⟨hEe, hEt, hCp, hlap, hbd⟩
  have hEpos : ∀ n, 0 < E ω n := fun n => by
    obtain ⟨j, hj⟩ := hEe n
    rw [← hj]
    exact he.1 j
  have hE'ωeq : E' ω = E ω := hE'ω ω hEe
  have hyω : ∀ n c, y ω n c = Tightness.proxyCoord (E ω) (S.η ω) D (fun n => S.mε (E ω n)) (u ω) n c := by
    intro n c
    rw [hy_def]
    simp only [hE'ωeq]
  have hmev : ∀ᶠ n in atTop, 0 ≤ (S.mε (E ω n))⁻¹ ∧ (S.mε (E ω n))⁻¹ ≤ Cm * E ω n := by
    filter_upwards [hEt.eventually (gt_mem_nhds hε₀)] with n hn
    have h := (hmε (E ω n) (hEpos n) hn).1
    have hpos : 0 < Cm⁻¹ * (E ω n)⁻¹ := mul_pos (inv_pos.2 hCm) (inv_pos.2 (hEpos n))
    refine ⟨inv_nonneg.2 (hpos.le.trans h), ?_⟩
    have h2 := inv_anti₀ hpos h
    rwa [mul_inv, inv_inv, inv_inv] at h2
  have hbddY : ∀ c, ∃ M, ∀ᶠ n in atTop, |y ω n c| ≤ M := by
    intro c
    refine ⟨Cm * C ω, ?_⟩
    filter_upwards [hmev] with n hn
    rw [hyω]
    refine Tightness.abs_proxyValue_le (mul_pos hCm hCp).le fun k hk => ?_
    have hkD : k ∈ cellVertices (E ω n) (S.η ω) D :=
      Tightness.mem_cellVertices_of_vertexPoint_mem (hEpos n) hk
    show |(S.mε (E ω n))⁻¹ * u ω n k| ≤ Cm * C ω
    have hE := hEpos n
    rw [abs_mul, abs_of_nonneg hn.1]
    calc (S.mε (E ω n))⁻¹ * |u ω n k| ≤ (Cm * E ω n) * (C ω / E ω n) :=
          mul_le_mul hn.2 (hbd n k hkD) (abs_nonneg _) (mul_pos hCm hE).le
      _ = Cm * C ω * (E ω n * (E ω n)⁻¹) := by ring
      _ = Cm * C ω := by rw [mul_inv_cancel₀ hE.ne', mul_one]
  obtain ⟨hmono, hconvY⟩ := hΦ ω
  have hY : ∀ c, ∃ l, Tendsto (fun k => Tightness.proxyCoord (E ω) (S.η ω) D (fun n => S.mε (E ω n)) (u ω)
      (Φ ω k) c) atTop (𝓝 l) := by
    intro c
    have h := hconvY c (hbddY c)
    simpa only [hyω] using h
  obtain ⟨ubar, h1, h2, h3⟩ := Tightness.tightness_of_proxies hDo (isBounded_ball.subset hDρ) hη.1 hp hη.2.2.1
    hEpos hEt hCm hmev hω.1 hmono hY
  exact ⟨hmono, ubar, h1, h2, fun hH => h3 (hω.2 hH)⟩

end MatedCRT.S3c
