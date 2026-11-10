import MatedCRT.FirstPass.S5d.ClusterInner
import MatedCRT.FirstPass.S5d.CellInner
import MatedCRT.FirstPass.S5d.CoverEvent
import MatedCRT.FirstPass.S5d.Decode

/-!
# The compact containment (3.1) from strict positivity of the stopped odometer (task fp-S5d-5-1-stopped-repair)

Referee notes/fp-gaps/CHATGPT-5-1-gaps-referee.md section 3 (compact-containment statement (3.1)) and section 5.2.
The NEW probabilistic step `StrictClusterCompactContainmentStep` (ClusterInner.lean) is reduced to one NEW step,
`StrictStoppedOdometerPositivityStep`: on `{t < T}`, with probability tending to one, the stopped odometer
`u^ε_t = w̃^ε_t + (t/ε) g^ε_{B_ρ}(0, ·)` (`stoppedOdometer`, Defs/Sandpile.lean:93) is strictly positive at the vertices
of the cells of every point of the inner neighbourhood `B⁻_σ(Λ_t)`. The reduction uses the cell-size estimate
(Lemma 2.8, `CellSizeEstimateStmt`, via `cellSizeEvent`), the deterministic containment `cell_subset_innerNbhd_half`
(CellInner.lean) and the exclusive decoding `mem_matedDiscreteCluster_of_odometer_pos_on_cell` (below).
-/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

/-- **NEW, OPEN (probabilistic input; referee sections 3.2-3.3 and 5.2).** For deterministic `σ > 0` and `t > 0`, on
`{t < T}` (`T` the cluster exit time), with probability tending to `1` as `ε → 0⁺`, the stopped odometer
`stoppedOdometer` is strictly positive at the vertex `vertexOf ε η x` of every point `x` of `B⁻_σ(Λ_t)`. Its written argument
is the uniform convergence of the rescaled least supersolution (Thm 4.1, `ConvergenceDivisibleStmt`) and of the annular Green
functions (Lemma 3.3, `UniformConvergenceGreenKernelStmt`) with the fixed-time positivity (3.2) of `u_t` on `Λ_t ∖ {0}`,
together with the pole argument near `0`. -/
def StrictStoppedOdometerPositivityStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) →
  ∀ σ t : ℝ, 0 < σ → 0 < t →
    TendsToOneOn S.P {ω | t < clusterExitTime (Λ ω) ρ} fun ε => {ω |
      ∀ x ∈ innerNbhd σ (Λ ω t), 0 < stoppedOdometer (S.mult ε ω) ε (S.η ω) ρ t (vertexOf ε (S.η ω) x)}

/-- **Exclusive decoding of the stopped odometer.** If the cell `H^ε_a` lies in `B_ρ` and the stopped odometer is positive
at `vertexOf x` for every `x` of the cell, then `a` lies in the strict discrete cluster. Unlike
`mem_matedDiscreteCluster_of_pos_on_cell` (Decode.lean) no rescaling constant `m_ε` appears, so no positivity of `m_ε` is
needed. -/
theorem mem_matedDiscreteCluster_of_odometer_pos_on_cell {μ : Measure ℂ} {η : ℝ → ℂ} (hap : IsAreaParametrized μ η)
    {m : ℤ → ℤ → ℕ} {ε ρ t : ℝ} (hε : 0 < ε) {a : ℤ} (hcell : cell ε η a ⊆ ball (0 : ℂ) ρ)
    (hpos : ∀ x ∈ cell ε η a, 0 < stoppedOdometer m ε η ρ t (vertexOf ε η x)) :
    a ∈ matedDiscreteCluster m ε η ρ t := by
  obtain ⟨x, hxa, hex⟩ := MatedCRT.S5c.exists_exclusive_mem_cell hap hε a
  have hv : vertexOf ε η x = a := MatedCRT.S5c.vertexOf_eq_of_exclusive hxa hex
  have hodo : 0 < stoppedOdometer m ε η ρ t a := by
    have h := hpos x hxa
    rwa [hv] at h
  have hW : a ∈ cellVertices ε η (ball (0 : ℂ) ρ) := ⟨x, hxa, hcell hxa⟩
  have hWc : a ∈ cellVertices ε η (closedBall (0 : ℂ) ρ) :=
    ⟨x, hxa, ball_subset_closedBall (hcell hxa)⟩
  unfold stoppedOdometer at hodo
  simp only [hWc, ↓reduceIte] at hodo
  unfold matedDiscreteCluster discreteCluster
  exact ⟨hW, by linarith⟩

/-- Generic probability bookkeeping: if `E'` is `TendsToOneOn` on `F` and the cover event `Z` fails with probability tending
to zero and the null set `N` is negligible, then `E` is `TendsToOneOn` on `F` as soon as `E'`, `Z` and `¬N` force `E`
eventually. -/
theorem tendsToOneOn_of_good_cover {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {F N : Set Ω}
    {E E' Z : ℝ → Set Ω} (hE' : TendsToOneOn P F E')
    (hZ : Tendsto (fun ε => P (Z ε)ᶜ) (𝓝[>] 0) (𝓝 0)) (hN : P N = 0)
    (h : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ ω ∈ F, ω ∉ N → ω ∈ Z ε → ω ∈ E' ε → ω ∈ E ε) :
    TendsToOneOn P F E := by
  unfold TendsToOneOn at hE' ⊢
  have hsum := hE'.add hZ
  rw [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [h] with ε hε
  have hsub : F ∩ (E ε)ᶜ ⊆ (F ∩ (E' ε)ᶜ ∪ (Z ε)ᶜ) ∪ N := by
    intro ω hω
    obtain ⟨hωF, hωE⟩ := hω
    by_cases hωN : ω ∈ N
    · exact Or.inr hωN
    by_cases hωZ : ω ∈ Z ε
    · by_cases hωE' : ω ∈ E' ε
      · exact absurd (hε ω hωF hωN hωZ hωE') hωE
      · exact Or.inl (Or.inl ⟨hωF, hωE'⟩)
    · exact Or.inl (Or.inr hωZ)
  calc P (F ∩ (E ε)ᶜ) ≤ P ((F ∩ (E' ε)ᶜ ∪ (Z ε)ᶜ) ∪ N) := measure_mono hsub
    _ ≤ P (F ∩ (E' ε)ᶜ ∪ (Z ε)ᶜ) + P N := measure_union_le _ _
    _ ≤ (P (F ∩ (E' ε)ᶜ) + P (Z ε)ᶜ) + P N := by gcongr; exact measure_union_le _ _
    _ = P (F ∩ (E' ε)ᶜ) + P (Z ε)ᶜ := by rw [hN, add_zero]

/-- **The compact containment (3.1) from strict positivity of the stopped odometer.** The NEW step
`StrictClusterCompactContainmentStep` follows from the NEW step `StrictStoppedOdometerPositivityStep` (with `σ = s/2`) and the
cell-size estimate `CellSizeEstimateStmt` (Lemma 2.8). -/
theorem strictClusterCompactContainmentStep_of_odometerPositivity (𝒮 : SpaceFillingSLEModel)
    (h28 : CellSizeEstimateStmt 𝒮) (hP : StrictStoppedOdometerPositivityStep 𝒮) :
    StrictClusterCompactContainmentStep 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS Λ hΛ s t hs ht
  have hγ2' : 0 < (2 + γ) ^ 2 := by positivity
  set ζ : ℝ := 1 / (2 + γ) ^ 2 with hζ_def
  have hζ0 : 0 < ζ := by positivity
  have hζ1 : ζ < 1 := by
    rw [hζ_def, div_lt_one hγ2']
    nlinarith
  have hb : 0 < 2 / (2 + γ) ^ 2 - ζ := by
    have h : 2 / (2 + γ) ^ 2 - ζ = ζ := by rw [hζ_def]; ring
    rw [h]; exact hζ0
  obtain ⟨p, hp, C, r₀, hr₀, hPoly⟩ := h28 γ hγ hγ2 ζ ρ hζ0 hζ1 hρ hρ1 Ω S hS
  -- the tail of the size event tends to zero (Lemma 2.8)
  have hPolyT : Tendsto (fun r : ℝ => ENNReal.ofReal (C * r ^ p)) (𝓝[>] 0) (𝓝 0) := by
    have hc : Tendsto (fun r : ℝ => C * r ^ p) (𝓝 0) (𝓝 (C * (0 : ℝ) ^ p)) :=
      (continuous_const.mul (Real.continuous_rpow_const hp.le)).tendsto 0
    rw [Real.zero_rpow hp.ne', mul_zero] at hc
    have hc' : Tendsto (fun r : ℝ => C * r ^ p) (𝓝[>] 0) (𝓝 0) := hc.mono_left nhdsWithin_le_nhds
    have h := ENNReal.tendsto_ofReal hc'
    rwa [ENNReal.ofReal_zero] at h
  have hZT : Tendsto (fun ε => S.P (cellSizeEvent S γ ζ ρ ε)ᶜ) (𝓝[>] 0) (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hPolyT
      (Eventually.of_forall fun _ => zero_le) ?_
    filter_upwards [eventually_mem_nhdsWithin, nhdsWithin_le_nhds (gt_mem_nhds hr₀)] with ε hε hεr
    exact hPoly ε hε hεr
  -- the Lemma 2.8 bound is eventually below `s/2`
  have hsmall : Tendsto (fun ε : ℝ => ε ^ (2 / (2 + γ) ^ 2 - ζ)) (𝓝[>] 0) (𝓝 0) := by
    have hc : Tendsto (fun ε : ℝ => ε ^ (2 / (2 + γ) ^ 2 - ζ)) (𝓝 0)
        (𝓝 ((0 : ℝ) ^ (2 / (2 + γ) ^ 2 - ζ))) :=
      (Real.continuous_rpow_const hb.le).tendsto 0
    rw [Real.zero_rpow hb.ne'] at hc
    exact hc.mono_left nhdsWithin_le_nhds
  have hev_small : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ^ (2 / (2 + γ) ^ 2 - ζ) < s / 2 :=
    hsmall.eventually (gt_mem_nhds (by linarith))
  -- almost surely: the cells are the area parametrization and `Λ` is monotone
  have hgood : ∀ᵐ ω ∂S.P, IsAreaParametrized (S.μ ω) (S.η ω) ∧ MonotoneOn (Λ ω) (Ioi 0) :=
    hS.isAreaParametrized.and (hΛ.mono fun ω h => h.2.1.monotoneOn)
  have hN : S.P {ω | ¬ (IsAreaParametrized (S.μ ω) (S.η ω) ∧ MonotoneOn (Λ ω) (Ioi 0))} = 0 :=
    ae_iff.1 hgood
  -- the odometer positivity of Step `StrictStoppedOdometerPositivityStep` at level `s/2`
  have hP' := hP γ hγ hγ2 ρ hρ hρ1 Ω S hS Λ hΛ (s / 2) t (half_pos hs) ht
  refine tendsToOneOn_of_good_cover hP' hZT hN ?_
  filter_upwards [hev_small, eventually_mem_nhdsWithin] with ε hεs hε0
  have hε : (0 : ℝ) < ε := hε0
  intro ω hωF hωN hωZ hωE'
  have hap := not_not.mp hωN
  have hΛball : Λ ω t ⊆ ball 0 ρ := subset_ball_of_lt_clusterExitTime hρ hap.2 ht hωF
  intro a ha
  obtain ⟨y, hyc, hyK⟩ := ha
  have hcellmeet : (cell ε (S.η ω) a ∩ ball 0 ρ).Nonempty := ⟨y, hyc, hΛball hyK.1⟩
  obtain ⟨hlo, hup⟩ := hωZ a hcellmeet
  have hdiam : diam (cell ε (S.η ω) a) ≤ s / 2 := hup.trans hεs.le
  have hbd : Bornology.IsBounded (cell ε (S.η ω) a) := by
    by_contra hunb
    rw [Metric.diam_eq_zero_of_unbounded hunb] at hlo
    have : 0 < ε ^ (2 / (2 - γ) ^ 2 + ζ) := Real.rpow_pos_of_pos hε _
    linarith
  have hsub := cell_subset_innerNbhd_half hs hbd hdiam ⟨y, hyc, hyK⟩
  exact mem_matedDiscreteCluster_of_odometer_pos_on_cell hap.1 hε
    (fun x hx => hΛball (hsub hx).1) (fun x hx => hωE' x (hsub hx))

end MatedCRT
