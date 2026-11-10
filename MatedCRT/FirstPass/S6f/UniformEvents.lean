import MatedCRT.FirstPass.S6f

/-!
# Events of Lemma 6.8, uniform in scale and vertex (fp-S6f, round 2, q1)

The walk-level inputs of `Uniform68Local.greenLow_of_event`, `Uniform68Local.exitMoment_of_event`, `hdiam` of
`Uniform68Point.hloc_band_point` and `hlow` of `EnvInputs68.ballMass_lower_env` are, in the Draft, the following
events of polynomially high probability (`PolyHighProb`, Armstrong-Kuusi-Mourrat style, as in `Draft/Section2`):

* `greenLowEvent68`: the Green lower bound on the vertices of `B_{ρ-ε^{ω₀}}` at all scales `r ∈ [ε^{ω₀}, dist(a, ∂B_ρ)]`
  (Draft Lemma 2.16, `GreenKernelLowerBoundStmt`); the second conjunct only, in the form of `greenLow_of_event`.
  The exponent `ω₀` is any `0 < ω₀ ≤ ω_G` (monotonicity in the exponent, `greenLowEvent68_polyHighProb`).
* `cellSizeEvent68`: the cell-size estimate on the cells meeting `B_ρ` (Draft Lemma 2.8, `CellSizeEstimateStmt`).
* `exitTimeEvent68`: the exit-time bound on all `D ⊆ B_ρ` with `ε^α ≤ μ(D)` (Draft Lemma 2.18,
  `ExitTimeUpperBoundStmt`), in the form of the `hD` input of `exitMoment_of_event`.
* `ballMassLowerEvent68`: the lower ball-mass bound `δ^b ≤ μ(B_δ(z))` for `z ∈ B_{1-δ}` (Draft Lemma 2.7,
  `VolumeGrowthStmt`), the `hlow` input of `ballMass_lower_env`, for every `b > (2+γ)²/2`.

The parameters are chosen by `draft68_uniform_events`: `ζ = 1/(2+γ)²`, `ω₀ < α` and `ω₀ < 2/(2+γ)² - ζ`
(the cell exponent), so that `ε^α = o(ε^{ω₀})` and `diam ≤ ε^{2/(2+γ)²-ζ} = o(ε^{ω₀})`.
The almost-sure finiteness input `hfin` is `draft68_hfin_ae` (`MatedCRT.FirstPass.S6f`).
-/

open HarmonicBalls
namespace MatedCRT

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

/-- The Green lower-bound event of Draft Lemma 2.16 (second conjunct, `C⁻¹ log(...) - 1 ≤ G`), at exponent `ω₀`,
radius `ρ`, constant `CG`, scale `ε`. Form of `Uniform68Local.greenLow_of_event`. -/
def greenLowEvent68 {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ω₀ ρ CG : ℝ) (ε : ℝ) : Set Ω :=
  {ω | ∀ a ∈ cellVertices ε (S.η ω) (ball 0 (ρ - ε ^ ω₀)), ∀ r : ℝ, ε ^ ω₀ ≤ r →
    r ≤ infDist (vertexPoint ε (S.η ω) a) (sphere 0 ρ) →
    ∀ b ∈ cellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) a) (r / 3)),
      CG⁻¹ * Real.log (if vertexPoint ε (S.η ω) a = vertexPoint ε (S.η ω) b then ε⁻¹
          else min (r / ‖vertexPoint ε (S.η ω) a - vertexPoint ε (S.η ω) b‖) ε⁻¹) - 1 ≤
        greenKernel (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) a) r)) a b}

/-- The cell-size event of Draft Lemma 2.8 (`CellSizeEstimateStmt`) at `γ`, `ζ`, radius `ρ`, scale `ε`. -/
def cellSizeEvent68 {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (γ ζ ρ : ℝ) (ε : ℝ) : Set Ω :=
  {ω | ∀ k : ℤ, (cell ε (S.η ω) k ∩ ball 0 ρ).Nonempty →
    ε ^ (2 / (2 - γ) ^ 2 + ζ) ≤ diam (cell ε (S.η ω) k) ∧
      diam (cell ε (S.η ω) k) ≤ ε ^ (2 / (2 + γ) ^ 2 - ζ)}

/-- The exit-time event of Draft Lemma 2.18 (`ExitTimeUpperBoundStmt`) at `α`, radius `ρ`, constant `CE`, scale `ε`.
The first conjunct is the `hD` input of `Uniform68Local.exitMoment_of_event`. -/
def exitTimeEvent68 {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (α ρ CE : ℝ) (ε : ℝ) : Set Ω :=
  {ω | (∀ D : Set ℂ, MeasurableSet D → D ⊆ ball 0 ρ → ENNReal.ofReal (ε ^ α) ≤ S.μ ω D →
      ∀ a ∈ cellVertices ε (S.η ω) D, ∀ N : ℕ,
        exitTimeMoment (S.mult ε ω) (interiorCellVertices ε (S.η ω) D) a N ≤
          ENNReal.ofReal (N.factorial * CE ^ N * ε ^ (-(N : ℝ))) *
            (⨆ z ∈ D, ∫⁻ w in thickening (ε ^ α) D,
              ENNReal.ofReal (Real.log (1 / ‖z - w‖) + 1) ∂S.μ ω) ^ N) ∧
    (∀ D : Set ℂ, D ⊆ ball 0 ρ → ∀ a ∈ cellVertices ε (S.η ω) D,
      ENNReal.ofReal (normExitTime (S.mult ε ω) (interiorCellVertices ε (S.η ω) D) a) ≤
        expectedExitTime (S.mult ε ω) (interiorCellVertices ε (S.η ω) D) a ∧
      expectedExitTime (S.mult ε ω) (interiorCellVertices ε (S.η ω) D) a ≤
        ENNReal.ofReal (CE * ε⁻¹) * largestExitTimeRV (S.μ ω) (thickening (ε ^ α) D))}

/-- The lower ball-mass event of Draft Lemma 2.7 (`VolumeGrowthStmt`) at exponent `b`, radius `δ`: the `hlow` input of
`EnvInputs68.ballMass_lower_env`. -/
def ballMassLowerEvent68 {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (b : ℝ) (δ : ℝ) : Set Ω :=
  {ω | ∀ z ∈ Metric.ball (0 : ℂ) (1 - δ), ENNReal.ofReal (δ ^ b) ≤ S.μ ω (Metric.ball z δ)}

/-- Monotonicity of `V^ε(·)` in the set (local copy of `Uniform68Local.cellVertices_mono_local`). -/
theorem cellVertices_mono_ball68 {ε : ℝ} {η : ℝ → ℂ} {D D' : Set ℂ} (h : D ⊆ D') {k : ℤ}
    (hk : k ∈ cellVertices ε η D) : k ∈ cellVertices ε η D' :=
  (show (cell ε η k ∩ D).Nonempty from hk).mono (Set.inter_subset_inter_right _ h)

/-- **Lemma 2.16 at every exponent `0 < ω₀ ≤ ω_G`.** The Draft exponent `ω_G` and, for each `ρ`, a constant `CG` with
`greenLowEvent68` of polynomially high probability for all valid environments and all `ω₀ ∈ (0, ω_G]`. The event at
`ω_G` implies the event at a smaller exponent `ω₀` (the vertex ball and the scale range both shrink for `ε < 1`). -/
theorem greenLowEvent68_polyHighProb {𝒮 : SpaceFillingSLEModel} (hG : GreenKernelLowerBoundStmt 𝒮)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∃ ωG : ℝ, 0 < ωG ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∃ CG : ℝ, 0 < CG ∧
    ∀ ω₀ : ℝ, 0 < ω₀ → ω₀ ≤ ωG → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
    PolyHighProb S.P (greenLowEvent68 S ω₀ ρ CG) := by
  obtain ⟨ωG, hωG, hGr⟩ := hG γ hγ hγ2
  refine ⟨ωG, hωG, fun ρ hρ0 hρ1 => ?_⟩
  obtain ⟨CG, hCG, hGS⟩ := hGr ρ hρ0 hρ1
  refine ⟨CG, hCG, fun ω₀ hω₀ hle Ω _ S hS => ?_⟩
  refine (hGS Ω S hS).mono_of_eventually ?_
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds (zero_lt_one : (0 : ℝ) < 1))]
    with ε hε0 hε1
  have hε0' : 0 < ε := hε0
  have hε1' : ε < 1 := hε1
  intro ω hω
  simp only [greenLowEvent68, Set.mem_ofPred_eq] at hω ⊢
  have hpow : ε ^ ωG ≤ ε ^ ω₀ := Real.rpow_le_rpow_of_exponent_ge hε0' hε1'.le hle
  have hsub : ball (0 : ℂ) (ρ - ε ^ ω₀) ⊆ ball (0 : ℂ) (ρ - ε ^ ωG) :=
    Metric.ball_subset_ball (by linarith)
  intro a ha r hr1 hr2 b hb
  exact (hω a (cellVertices_mono_ball68 hsub ha) r (hpow.trans hr1) hr2 b hb).2

/-- **Lemma 2.7 (lower half) at every exponent `b > (2+γ)²/2`.** For a valid environment, `ballMassLowerEvent68` is of
polynomially high probability. This is `hlow` of `EnvInputs68.ballMass_lower_env`. -/
theorem ballMassLowerEvent68_polyHighProb {𝒮 : SpaceFillingSLEModel} (hV : VolumeGrowthStmt)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {b : ℝ} (hb : (2 + γ) ^ 2 / 2 < b)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ) :
    PolyHighProb S.P (ballMassLowerEvent68 S b) := by
  have hpos : 0 < (2 - γ) ^ 2 := pow_pos (by linarith) 2
  have hcone : IsConeField γ S.P S.hC S.hcirc S.μ := by
    unfold IsConeField
    exact ⟨hS.isProbabilityMeasure, hS.isQuantumCone, hS.isLQGMeasure⟩
  have h := hV γ hγ hγ2 ((2 - γ) ^ 2 / 4) b (by linarith) (by linarith) hb Ω S.P S.hC S.hcirc S.μ hcone
  exact h.mono fun δ ω hω z hz => (hω z hz).1

/-- **Parameters and events of Lemma 6.8, uniform in scale and vertex.** There are `ζ = 1/(2+γ)²`, and exponents
`0 < ω₀ < α` with `ω₀ < 2/(2+γ)² - ζ`, such that for each `ρ ∈ (0,1)` there are constants `CG`, `CE` with: for every
valid environment, the Green event at `ω₀`, the cell-size event at `ζ`, and the exit-time event at `α` all have
polynomially high probability. (Each event is stated for its own radius `ρ`; the assembly may use different radii for
different events, since the statement holds for every `ρ ∈ (0,1)`.) -/
theorem draft68_uniform_events {𝒮 : SpaceFillingSLEModel}
    (hG : GreenKernelLowerBoundStmt 𝒮) (hC : CellSizeEstimateStmt 𝒮) (hE : ExitTimeUpperBoundStmt 𝒮)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∃ ζ : ℝ, 0 < ζ ∧ ζ < 1 ∧ ∃ ω₀ α : ℝ, 0 < ω₀ ∧ ω₀ < α ∧ 0 < α ∧ ω₀ < 2 / (2 + γ) ^ 2 - ζ ∧
    ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∃ CG : ℝ, 0 < CG ∧ ∃ CE : ℝ, 0 < CE ∧
    ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      PolyHighProb S.P (greenLowEvent68 S ω₀ ρ CG) ∧
      PolyHighProb S.P (cellSizeEvent68 S γ ζ ρ) ∧
      PolyHighProb S.P (exitTimeEvent68 S α ρ CE) := by
  obtain ⟨ωG, hωG, hGr⟩ := greenLowEvent68_polyHighProb hG hγ hγ2
  obtain ⟨α, hα, hEr⟩ := hE γ hγ hγ2
  obtain ⟨q, hq_def⟩ : ∃ q : ℝ, q = 1 / (2 + γ) ^ 2 := ⟨_, rfl⟩
  have h2γ : 0 < (2 + γ) ^ 2 := by positivity
  have hq0 : 0 < q := by rw [hq_def]; positivity
  have hq1 : q < 1 := by
    rw [hq_def, div_lt_one h2γ]
    nlinarith
  have hqq : 2 / (2 + γ) ^ 2 - q = q := by rw [hq_def]; ring
  obtain ⟨ω₀, hω₀def⟩ : ∃ ω₀ : ℝ, ω₀ = min ωG (min (α / 2) (q / 2)) := ⟨_, rfl⟩
  have hω₀1 : ω₀ ≤ ωG := by rw [hω₀def]; exact min_le_left _ _
  have hω₀2 : ω₀ ≤ α / 2 := by rw [hω₀def]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hω₀3 : ω₀ ≤ q / 2 := by rw [hω₀def]; exact (min_le_right _ _).trans (min_le_right _ _)
  have hω₀pos : 0 < ω₀ := by
    rw [hω₀def]; exact lt_min hωG (lt_min (half_pos hα) (half_pos hq0))
  refine ⟨q, hq0, hq1, ω₀, α, hω₀pos, by linarith, hα, by rw [hqq]; linarith, ?_⟩
  intro ρ hρ0 hρ1
  obtain ⟨CG, hCG, hGS⟩ := hGr ρ hρ0 hρ1
  obtain ⟨CE, hCE, hES⟩ := hEr ρ hρ0 hρ1
  refine ⟨CG, hCG, CE, hCE, fun Ω _ S hS => ⟨?_, ?_, ?_⟩⟩
  · exact hGS ω₀ hω₀pos hω₀1 Ω S hS
  · exact hC γ hγ hγ2 q ρ hq0 hq1 hρ0 hρ1 Ω S hS
  · exact hES Ω S hS

end MatedCRT

#print axioms MatedCRT.draft68_uniform_events
#print axioms MatedCRT.ballMassLowerEvent68_polyHighProb
