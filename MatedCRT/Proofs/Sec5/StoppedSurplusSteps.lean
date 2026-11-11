import MatedCRT.Proofs.Sec5.StoppedMeanValueInequality
import MatedCRT.Proofs.Sec5.StoppedSurplusComparison
import MatedCRT.Proofs.Measurability.EnvSigma

/-!
# Lemma 5.3 on `V^ε(Λ_t)`: the stopped surplus lower bound from three estimates on the obstacle surplus

Let `A = V^ε(Λ_t)`, `D = Λ^ε_t`, `B = V^ε(B_ρ) \ V^ε(∂B_ρ)` and let `v^ε_t = w̃^ε_t + (t ε⁻¹) g^ε_B(0, ·)` be the obstacle
surplus (the stopped odometer, eq:stopped-odometer-de) of Section 4. By Lemma 4.4 (corrected), `Δ w̃^ε_t = (deg)⁻¹` on
`D` and `Δ w̃^ε_t ≥ 0` on `B`, so the comparison `stoppedSurplus_ge_obstacleSurplus` gives on `A`
`(t ε⁻¹) g_A(·, 0) - q_A ≥ v^ε_t - sup_{x ∉ A} v^ε_t(x) - ∑_{b ∈ A \ D} g_A(·, b) / deg(b)`.
Hence `StoppedMeanValueSurplusLowerStep` (with constant `c/2`) follows from:

* `StoppedSurplusInteriorStep`: `v^ε_t ≥ c ε⁻¹` on the `δ`-interior of `A`, for a `σ(h, η)`-measurable `c > 0`;
* `StoppedSurplusExteriorStep`: `v^ε_t ≤ κ ε⁻¹` off `A`, for every `κ > 0`;
* `StoppedLayerPotentialStep`: `∑_{b ∈ A \ D} g_A(a, b) / deg(b) ≤ κ ε⁻¹` for `a ∈ A`, for every `κ > 0`.

Heuristically, `ε v^ε_t` converges uniformly to the continuum odometer `t G_{B_ρ}(0, ·) + w̄_t` (Theorem 4.1 and
Lemma 3.3), which vanishes off `Λ_t` and is positive on `Λ_t` (eq:strictly-above-in-interior); and `A \ D` is contained
in a thin neighbourhood of `∂Λ_t`, whose Green potential is small (Lemma 3.4). These three estimates are not in the
paper.

* `stoppedMeanValueSurplusLower_of_steps : StoppedMeanValueSurplusLowerStep 𝒮` from the three steps.
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

/-- **Step (Lemma 5.3 on `V^ε(Λ_t)`, interior).** There is a `σ(h, η)`-measurable `c > 0` such that, on `{t < T}`,
with probability tending to one, `v^ε_t(a) = w̃^ε_t(a) + (t ε⁻¹) g^ε_{B_ρ}(0, a) ≥ c ε⁻¹` for all `a ∈ V^ε(Λ_t)` with
`dist(η(a), ∂ V̄^ε(Λ_t)) > δ`. Not in the paper. -/
def StoppedSurplusInteriorStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  DiscreteLaplacianBoundCorrectedStmt 𝒮 → MaximumPrincipleStmt 𝒮 →
  ConvergenceDivisibleStmt 𝒮 → UniformConvergenceGreenKernelStmt 𝒮 → ExitTimeUpperBoundStmt 𝒮 →
  IntegralConvergenceGreenFunctionStmt 𝒮 →
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) →
  ∀ δ t : ℝ, 0 < δ → δ < ρ → 0 < t →
  ∃ c : Ω → ℝ, Measurable[S.envSigma] c ∧ (∀ ω, 0 < c ω) ∧
    TendsToOneOn S.P {ω | t < clusterExitTime (Λ ω) ρ} fun ε => {ω |
      ∀ a ∈ cellVertices ε (S.η ω) (Λ ω t),
        δ < infDist (vertexPoint ε (S.η ω) a)
          (frontier (fillCells ε (S.η ω) (cellVertices ε (S.η ω) (Λ ω t)))) →
        c ω / ε ≤ matedLeastSupersolution (S.mult ε ω) ε (S.η ω) ρ t a +
          t / ε * greenKernel (S.mult ε ω) (ballInterior ε (S.η ω) ρ) 0 a}

/-- **Step (Lemma 5.3 on `V^ε(Λ_t)`, exterior).** For every `κ > 0`, on `{t < T}`, with probability tending to one,
`v^ε_t(x) = w̃^ε_t(x) + (t ε⁻¹) g^ε_{B_ρ}(0, x) ≤ κ ε⁻¹` for all `x ∉ V^ε(Λ_t)`. Not in the paper. -/
def StoppedSurplusExteriorStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  DiscreteLaplacianBoundCorrectedStmt 𝒮 → MaximumPrincipleStmt 𝒮 →
  ConvergenceDivisibleStmt 𝒮 → UniformConvergenceGreenKernelStmt 𝒮 → ExitTimeUpperBoundStmt 𝒮 →
  IntegralConvergenceGreenFunctionStmt 𝒮 →
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) →
  ∀ t : ℝ, 0 < t → ∀ κ : ℝ, 0 < κ →
    TendsToOneOn S.P {ω | t < clusterExitTime (Λ ω) ρ} fun ε => {ω |
      ∀ x ∉ cellVertices ε (S.η ω) (Λ ω t),
        matedLeastSupersolution (S.mult ε ω) ε (S.η ω) ρ t x +
          t / ε * greenKernel (S.mult ε ω) (ballInterior ε (S.η ω) ρ) 0 x ≤ κ / ε}

/-- **Step (Lemma 5.3 on `V^ε(Λ_t)`, boundary layer).** For every `κ > 0`, on `{t < T}`, with probability tending to
one, the Green potential in `A = V^ε(Λ_t)` of the vertices of `A` outside the discrete cluster `Λ^ε_t` is at most
`κ ε⁻¹`: `∑_{b ∈ A \ Λ^ε_t} g^ε_A(a, b) / deg(b) ≤ κ ε⁻¹` for all `a ∈ A`. Not in the paper. -/
def StoppedLayerPotentialStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  DiscreteLaplacianBoundCorrectedStmt 𝒮 → MaximumPrincipleStmt 𝒮 →
  ConvergenceDivisibleStmt 𝒮 → UniformConvergenceGreenKernelStmt 𝒮 → ExitTimeUpperBoundStmt 𝒮 →
  IntegralConvergenceGreenFunctionStmt 𝒮 →
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) →
  ∀ t : ℝ, 0 < t → ∀ κ : ℝ, 0 < κ →
    TendsToOneOn S.P {ω | t < clusterExitTime (Λ ω) ρ} fun ε => {ω |
      ∀ a ∈ cellVertices ε (S.η ω) (Λ ω t),
        ∑ᶠ b ∈ cellVertices ε (S.η ω) (Λ ω t) \ matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t,
          greenKernel (S.mult ε ω) (cellVertices ε (S.η ω) (Λ ω t)) a b ≤ κ / ε}

namespace StoppedMeanValue

/-- An almost everywhere measurable `c > 0` is small only with small probability: for `η > 0` there is `κ > 0` with
`P[c ≤ κ] ≤ η`. -/
theorem exists_measure_le_le_of_pos {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {c : Ω → ℝ} (hc : AEMeasurable c P) (hcpos : ∀ ω, 0 < c ω) {η : ℝ≥0∞} (hη : 0 < η) :
    ∃ κ : ℝ, 0 < κ ∧ P {ω | c ω ≤ κ} ≤ η := by
  let A : ℕ → Set Ω := fun n => {ω | c ω ≤ 1 / ((n : ℝ) + 1)}
  have hA : ∀ n, NullMeasurableSet (A n) P := fun n => hc.nullMeasurable measurableSet_Iic
  have hanti : Antitone A := by
    intro n k hnk ω hω
    have hnk' : (n : ℝ) ≤ k := by exact_mod_cast hnk
    have hω' : c ω ≤ 1 / ((k : ℝ) + 1) := hω
    show c ω ≤ 1 / ((n : ℝ) + 1)
    exact hω'.trans (one_div_le_one_div_of_le (by positivity) (by linarith))
  have hinter : P (⋂ n, A n) = 0 := by
    refine measure_mono_null (fun ω hω => ?_) measure_empty
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (hcpos ω)
    exact absurd (mem_iInter.1 hω n) (not_le.2 hn)
  have ht := tendsto_measure_iInter_atTop hA hanti ⟨0, measure_ne_top P _⟩
  rw [hinter] at ht
  obtain ⟨n, hn⟩ := (ht.eventually (Iic_mem_nhds hη)).exists
  exact ⟨1 / ((n : ℝ) + 1), by positivity, hn⟩

/-- On `F`, an event `E₁` of probability tending to one, events `E₂ κ`, `E₃ κ` of probability tending to one for each
`κ > 0`, an event `H` of probability tending to one and the event `{κ < c}` (whose complement has small probability
for small `κ`) give every event `E` containing their intersection. -/
theorem tendsToOneOn_of_small_constant {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {F : Set Ω} {E₁ H E : ℝ → Set Ω} {E₂ E₃ : ℝ → ℝ → Set Ω} {c : Ω → ℝ}
    (hc : AEMeasurable c P) (hcpos : ∀ ω, 0 < c ω) (h₁ : TendsToOneOn P F E₁)
    (h₂ : ∀ κ : ℝ, 0 < κ → TendsToOneOn P F (E₂ κ)) (h₃ : ∀ κ : ℝ, 0 < κ → TendsToOneOn P F (E₃ κ))
    (hH : ProbTendsToOne P H)
    (hE : ∀ κ : ℝ, 0 < κ → ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ ω ∈ F, ω ∈ E₁ ε → ω ∈ E₂ κ ε → ω ∈ E₃ κ ε →
      ω ∈ H ε → κ < c ω → ω ∈ E ε) : TendsToOneOn P F E := by
  unfold TendsToOneOn at h₁ h₂ h₃ ⊢
  unfold ProbTendsToOne at hH
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  obtain ⟨κ, hκ, hPκ⟩ := exists_measure_le_le_of_pos hc hcpos (ENNReal.half_pos hη.ne')
  have hsum := ((h₁.add (h₂ κ hκ)).add (h₃ κ hκ)).add hH
  simp only [add_zero] at hsum
  have hev := (ENNReal.tendsto_nhds_zero.1 hsum) (η / 2) (ENNReal.half_pos hη.ne')
  filter_upwards [hev, hE κ hκ] with ε hε hEε
  calc P (F ∩ (E ε)ᶜ) ≤ P ((F ∩ (E₁ ε)ᶜ) ∪ (F ∩ (E₂ κ ε)ᶜ) ∪ (F ∩ (E₃ κ ε)ᶜ) ∪ (H ε)ᶜ ∪
        {ω | c ω ≤ κ}) := by
        apply measure_mono
        rintro ω ⟨hF, hω⟩
        by_contra hno
        simp only [mem_union, mem_inter_iff, mem_compl_iff, mem_ofPred_eq, not_or, not_and, not_not,
          not_le] at hno
        obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hno
        exact hω (hEε ω hF (h1 hF) (h2 hF) (h3 hF) h4 h5)
    _ ≤ P (F ∩ (E₁ ε)ᶜ) + P (F ∩ (E₂ κ ε)ᶜ) + P (F ∩ (E₃ κ ε)ᶜ) + P (H ε)ᶜ + P {ω | c ω ≤ κ} := by
        refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
        refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
        refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
        exact measure_union_le _ _
    _ ≤ η / 2 + η / 2 := add_le_add hε hPκ
    _ = η := ENNReal.add_halves η

end StoppedMeanValue

open StoppedMeanValue in
/-- **The stopped surplus lower bound** (`StoppedMeanValueSurplusLowerStep`, with constant `c/2`) from the interior,
exterior and boundary-layer estimates on the obstacle surplus, by the comparison
`stoppedSurplus_ge_obstacleSurplus` and Lemma 4.4 (corrected). -/
theorem stoppedMeanValueSurplusLower_of_steps (𝒮 : SpaceFillingSLEModel)
    (h1 : StoppedSurplusInteriorStep 𝒮) (h2 : StoppedSurplusExteriorStep 𝒮)
    (h3 : StoppedLayerPotentialStep 𝒮) : StoppedMeanValueSurplusLowerStep 𝒮 := by
  intro h44 h213 h41 h33 h218 h34 γ hγ hγ2 ρ hρ hρ1 Ω _ S hS Λ hΛ δ t hδ hδρ ht
  have := hS.isProbabilityMeasure
  obtain ⟨c, hc, hcpos, hE1⟩ :=
    h1 h44 h213 h41 h33 h218 h34 γ hγ hγ2 ρ hρ hρ1 Ω S hS Λ hΛ δ t hδ hδρ ht
  refine ⟨fun ω => c ω / 2, hc.div_const 2, fun ω => half_pos (hcpos ω), ?_⟩
  have hgood := (ae_isRegularMatedMap (adjacentCellsMeetAeStep 𝒮) hγ hγ2 hS).and
    (hS.isAreaParametrized.and (hΛ.and (h44 γ hγ hγ2 ρ hρ hρ1 Ω S hS)))
  refine tendsToOneOn_of_small_constant (hS.aemeasurable_of_envSigma hc) hcpos hE1
    (fun κ hκ => h2 h44 h213 h41 h33 h218 h34 γ hγ hγ2 ρ hρ hρ1 Ω S hS Λ hΛ t ht (κ / 4) (by positivity))
    (fun κ hκ => h3 h44 h213 h41 h33 h218 h34 γ hγ hγ2 ρ hρ hρ1 Ω S hS Λ hΛ t ht (κ / 4) (by positivity))
    (IterativeBound.probTendsToOne_inter (IterativeBound.probTendsToOne_of_ae hgood)
      (hS.probTendsToOne_small_cells ρ (ρ / 2) (half_pos hρ))) ?_
  intro κ hκ
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε : 0 < ε := hε
  rintro ω hT hv hM hQ ⟨⟨hregω, harea, hfam, h44ω⟩, hsmall⟩ hκc
  intro a ha hdist
  obtain ⟨hlap, hlapB, -, -⟩ := h44ω t ε ht hε
  have hd := hregω ε hε
  have hB : (ballInterior ε (S.η ω) ρ).Finite := hd.finite_ballInterior
  have hΛt : Λ ω t ⊆ ball 0 (ρ / 3) :=
    IDLALowerBound.subset_ball_div_three_of_lt_clusterExitTime hfam.2.1.monotoneOn ht hT
  have hAB : cellVertices ε (S.η ω) (Λ ω t) ⊆ ballInterior ε (S.η ω) ρ := by
    intro b hb
    refine StoppedLLowerBound.mem_ballInterior_of_cell_subset ?_
      (StoppedLLowerBound.cell_subset_ball_of_mem_cellVertices harea.1 hΛt (half_pos hρ).le
        (by linarith) hsmall hb)
    obtain ⟨y, hy⟩ := hb
    exact ⟨y, hy.1⟩
  have hA := hB.subset hAB
  have hlf := hd.locallyFinite
  have h0 : (0 : ℤ) ∈ cellVertices ε (S.η ω) (Λ ω t) := by
    refine ⟨0, ?_, (hfam.1 t ht).2.1⟩
    unfold cell
    refine ⟨0, ⟨?_, ?_⟩, harea.2.1⟩
    · simp [hε.le]
    · simp
  have hfinE : (cellVertices ε (S.η ω) (Λ ω t) \
      matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t).Finite := hA.subset sdiff_subset
  have hcmp := stoppedSurplus_ge_obstacleSurplus hd.symm hlf hd.succ hA hB hAB h0
    (fun b => greenFn_laplacian_fst hlf hd.succ hA b) (fun b => greenFn_laplacian_fst hlf hd.succ hB b)
    (matedLeastSupersolution (S.mult ε ω) ε (S.η ω) ρ t) (t / ε) (κ / 4 / ε) hfinE.toFinset
    (fun x _ hxD => hlap x hxD) (fun x hx _ => (hlapB x (hAB hx)).1)
    (fun x hx hxD => hfinE.mem_toFinset.2 ⟨hx, hxD⟩) hM a
  have hva := hv a ha hdist
  have hQa := hQ a ha
  rw [finsum_mem_eq_finite_toFinset_sum _ hfinE] at hQa
  have hcκ : κ / ε < c ω / ε := div_lt_div_of_pos_right hκc hε
  have e1 : c ω / 2 / ε = c ω / ε / 2 := by ring
  have e2 : κ / 4 / ε = κ / ε / 4 := by ring
  rw [e1]
  rw [e2] at hcmp hQa
  linarith

end MatedCRT
