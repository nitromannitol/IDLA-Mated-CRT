import MatedCRT.Draft.Section2
import MatedCRT.Proofs.Sec5.IDLALowerBound.Geometry

/-!
# FIRST PASS, Proposition 5.1: the vertex-threshold cover with probability tending to one

Probability bookkeeping around the deterministic covering lemma. Inputs, all as hypotheses:
`CellSizeEstimateStmt 𝒮` (Lemma 2.8, paper line 669) with `ζ = 1/(2+γ)²`, and the cover event `TendsToOneOn`
for the cluster `L` (Proposition 4.2 at `δ/2`, paper line 1611, when `L` is the divisible sandpile cluster).
The cluster `L` is a parameter: the sets `O₁` of Lemma 5.2 are taken inside `L` by the caller, which is
where the gaps G1a/G1b/G1c of `notes/z5.md` enter, not here.

Deterministic covering: `innerNbhd_subset_fillCells_vertexThresholdSet` reduces to
`MatedCRT.IDLALowerBound.innerNbhd_subset_fillCells_deep` (`MatedCRT/Proofs/Sec5/IDLALowerBound/Geometry.lean`,
axioms propext, Classical.choice, Quot.sound), which is reused here by import.
-/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

/-- The vertex threshold set of Proposition 5.1 (CORRECTION [C4]): the vertices of `L` whose cells meet `B_ρ`
and whose vertex point lies at distance `> δ/4` from the frontier of the cell union of `L ∩ V^ε(B_ρ)`. -/
def vertexThresholdSet (ε : ℝ) (η : ℝ → ℂ) (L : Set ℤ) (ρ δ : ℝ) : Set ℤ :=
  {a | a ∈ L ∩ cellVertices ε η (ball 0 ρ) ∧
    δ / 4 < infDist (vertexPoint ε η a) (frontier (fillCells ε η (L ∩ cellVertices ε η (ball 0 ρ))))}

/-- The size event of Lemma 2.8 (`CellSizeEstimateStmt`): every cell meeting `B_ρ` has diameter between
`ε^{2/(2-γ)²+ζ}` and `ε^{2/(2+γ)²-ζ}`. -/
def cellSizeEvent {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (γ ζ ρ ε : ℝ) : Set Ω :=
  {ω | ∀ k : ℤ, (cell ε (S.η ω) k ∩ ball 0 ρ).Nonempty →
    ε ^ (2 / (2 - γ) ^ 2 + ζ) ≤ diam (cell ε (S.η ω) k) ∧ diam (cell ε (S.η ω) k) ≤ ε ^ (2 / (2 + γ) ^ 2 - ζ)}

/-- Deterministic covering: `B⁻_δ(Λ) ⊆ Ā(vertexThresholdSet)` when `B⁻_{δ/2}(Λ) ⊆ Ā(L)`, the cells are bounded
and have diameter `< δ/4` when they meet `B_ρ`, and `Λ ⊆ B_ρ`. -/
theorem innerNbhd_subset_fillCells_vertexThresholdSet {ε : ℝ} {η : ℝ → ℂ} (hε : 0 ≤ ε) (hcont : Continuous η)
    {L : Set ℤ} {ρ δ : ℝ} (hδ : 0 < δ) {X : Set ℂ} (hX : X ⊆ ball 0 ρ)
    (hL : innerNbhd (δ / 2) X ⊆ fillCells ε η L)
    (hd : ∀ k : ℤ, (cell ε η k ∩ ball 0 ρ).Nonempty → diam (cell ε η k) < δ / 4) :
    innerNbhd δ X ⊆ fillCells ε η (vertexThresholdSet ε η L ρ δ) := by
  have hb : ∀ a ∈ L ∩ cellVertices ε η (ball 0 ρ), Bornology.IsBounded (cell ε η a) :=
    fun a _ => (isCompact_Icc.image hcont).isBounded
  have hball : ∀ a ∈ L ∩ cellVertices ε η (ball 0 ρ), (cell ε η a ∩ ball 0 ρ).Nonempty :=
    fun a ha => ha.2
  have hd' : ∀ a ∈ L ∩ cellVertices ε η (ball 0 ρ), diam (cell ε η a) < δ / 4 :=
    fun a ha => hd a ha.2
  have hX' : innerNbhd (δ / 2) X ⊆ fillCells ε η (L ∩ cellVertices ε η (ball 0 ρ)) := by
    intro x hx
    have hxL : x ∈ fillCells ε η L := hL hx
    obtain ⟨a, haL, hxa⟩ : ∃ a ∈ L, x ∈ cell ε η a := by
      simpa only [fillCells, mem_iUnion, exists_prop] using hxL
    have hacv : a ∈ cellVertices ε η (ball 0 ρ) := by
      show (cell ε η a ∩ ball 0 ρ).Nonempty
      exact ⟨x, hxa, hX hx.1⟩
    simp only [fillCells, mem_iUnion, exists_prop]
    exact ⟨a, ⟨haL, hacv⟩, hxa⟩
  unfold vertexThresholdSet
  exact IDLALowerBound.innerNbhd_subset_fillCells_deep hε hδ hb hd' hball hX'

/-- Time restriction: for `0 < t < T`, `Λ_t ⊆ B_ρ`, where `T = clusterExitTime Λ ρ` (paper line 1589) and
`Λ` is nondecreasing on `(0, ∞)` (`SatisfiesHarmonicBallConditions.monotoneOn`). -/
theorem subset_ball_of_lt_clusterExitTime_cover {Λ : ℝ → Set ℂ} {ρ t : ℝ} (hρ : 0 < ρ)
    (hmono : MonotoneOn Λ (Ioi 0)) (ht : 0 < t) (hT : t < clusterExitTime Λ ρ) : Λ t ⊆ ball 0 ρ := by
  have hT' : t < sSup {s : ℝ | 0 < s ∧ Λ s ⊆ ball 0 (ρ / 3)} := hT
  have hne : {s : ℝ | 0 < s ∧ Λ s ⊆ ball 0 (ρ / 3)}.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    rw [h, Real.sSup_empty] at hT'
    linarith
  obtain ⟨s, hs, hts⟩ := exists_lt_of_lt_csSup hne hT'
  have hsub : Λ t ⊆ Λ s := hmono ht hs.1 hts.le
  exact hsub.trans (hs.2.trans (ball_subset_ball (by linarith)))

/-- **Cover with probability tending to one** (Proposition 5.1, geometric part). Assume the cover event of
Proposition 4.2 at `δ/2` for the cluster `L` (`hcov`), and Lemma 2.8 (`h28`). Then the cover of `B⁻_δ(Λ_t)` by
`Ā_ε(vertexThresholdSet)` holds on `{t < T}` except on an event of probability tending to `0`. -/
theorem tendsToOneOn_cover_vertexThresholdSet {Ω : Type} [MeasurableSpace Ω] {𝒮 : SpaceFillingSLEModel}
    {γ ρ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (h28 : CellSizeEstimateStmt 𝒮)
    (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    (Λ : Ω → ℝ → Set ℂ) (hΛ : ∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω))
    (δ t : ℝ) (hδ : 0 < δ) (ht : 0 < t) (L : ℝ → Ω → Set ℤ)
    (hcov : TendsToOneOn S.P {ω | t < clusterExitTime (Λ ω) ρ}
      fun ε => {ω | innerNbhd (δ / 2) (Λ ω t) ⊆ fillCells ε (S.η ω) (L ε ω)}) :
    TendsToOneOn S.P {ω | t < clusterExitTime (Λ ω) ρ}
      fun ε => {ω | innerNbhd δ (Λ ω t) ⊆ fillCells ε (S.η ω) (vertexThresholdSet ε (S.η ω) (L ε ω) ρ δ)} := by
  -- the exponent of Lemma 2.8 with `ζ = 1/(2+γ)²`
  have hγ2' : 0 < (2 + γ) ^ 2 := by positivity
  set ζ : ℝ := 1 / (2 + γ) ^ 2 with hζ_def
  have hζ0 : 0 < ζ := by positivity
  have hζ1 : ζ < 1 := by
    rw [hζ_def, div_lt_one hγ2']
    nlinarith
  have hb : 0 < 2 / (2 + γ) ^ 2 - ζ := by
    have h : 2 / (2 + γ) ^ 2 - ζ = ζ := by rw [hζ_def]; ring
    rw [h]; exact hζ0
  obtain ⟨p, hp, C, r₀, hr₀, hPoly⟩ := h28 γ hγ0 hγ2 ζ ρ hζ0 hζ1 hρ hρ1 Ω S hS
  -- almost surely: continuity of `η` and monotonicity of `Λ` on `(0, ∞)`
  have hcont : ∀ᵐ ω ∂S.P, Continuous (S.η ω) ∧ MonotoneOn (Λ ω) (Ioi 0) :=
    (hS.isAreaParametrized.and (hΛ.mono fun ω h => h.2.1.monotoneOn)).mono fun ω h => ⟨h.1.1, h.2⟩
  have hNnull : S.P {ω | ¬ (Continuous (S.η ω) ∧ MonotoneOn (Λ ω) (Ioi 0))} = 0 := ae_iff.1 hcont
  have hz0 : ∀ x : ℝ≥0∞, (0 : ℝ≥0∞) ≤ x := fun x => zero_le
  -- the bound of Lemma 2.8 tends to zero
  have hsmall : Tendsto (fun ε : ℝ => ε ^ (2 / (2 + γ) ^ 2 - ζ)) (𝓝[>] 0) (𝓝 0) := by
    have hc : Tendsto (fun ε : ℝ => ε ^ (2 / (2 + γ) ^ 2 - ζ)) (𝓝 0)
        (𝓝 ((0 : ℝ) ^ (2 / (2 + γ) ^ 2 - ζ))) :=
      (Real.continuous_rpow_const hb.le).tendsto 0
    rw [Real.zero_rpow hb.ne'] at hc
    exact hc.mono_left nhdsWithin_le_nhds
  have hPolyT : Tendsto (fun r : ℝ => ENNReal.ofReal (C * r ^ p)) (𝓝[>] 0) (𝓝 0) := by
    have hc : Tendsto (fun r : ℝ => C * r ^ p) (𝓝 0) (𝓝 (C * (0 : ℝ) ^ p)) :=
      (continuous_const.mul (Real.continuous_rpow_const hp.le)).tendsto 0
    rw [Real.zero_rpow hp.ne', mul_zero] at hc
    have hc' : Tendsto (fun r : ℝ => C * r ^ p) (𝓝[>] 0) (𝓝 0) := hc.mono_left nhdsWithin_le_nhds
    have h := ENNReal.tendsto_ofReal hc'
    rwa [ENNReal.ofReal_zero] at h
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ ε ^ (2 / (2 + γ) ^ 2 - ζ) < δ / 4 ∧ ε < r₀ := by
    have h1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ^ (2 / (2 + γ) ^ 2 - ζ) < δ / 4 :=
      hsmall.eventually (gt_mem_nhds (by linarith))
    have h2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := eventually_mem_nhdsWithin
    have h3 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < r₀ := nhdsWithin_le_nhds (gt_mem_nhds hr₀)
    filter_upwards [h1, h2, h3] with ε h1 h2 h3
    exact ⟨h2, h1, h3⟩
  -- the size event fails with probability tending to zero (Lemma 2.8 gives a polynomial bound)
  have hZT : Tendsto (fun ε => S.P (cellSizeEvent S γ ζ ρ ε)ᶜ) (𝓝[>] 0) (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hPolyT (Eventually.of_forall fun _ => hz0 _) ?_
    filter_upwards [hev] with ε hε
    exact hPoly ε hε.1 hε.2.2
  unfold TendsToOneOn at hcov ⊢
  have hsum := hcov.add hZT
  rw [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum (Eventually.of_forall fun _ => hz0 _) ?_
  filter_upwards [hev] with ε hε
  obtain ⟨hε0, hεs, hεr⟩ := hε
  -- off the three exceptional events, the cover holds
  have hsub : {ω | t < clusterExitTime (Λ ω) ρ} ∩
      {ω | innerNbhd δ (Λ ω t) ⊆ fillCells ε (S.η ω) (vertexThresholdSet ε (S.η ω) (L ε ω) ρ δ)}ᶜ ⊆
      ((({ω | t < clusterExitTime (Λ ω) ρ} ∩
          {ω | innerNbhd (δ / 2) (Λ ω t) ⊆ fillCells ε (S.η ω) (L ε ω)}ᶜ) ∪
        (cellSizeEvent S γ ζ ρ ε)ᶜ) ∪
        {ω | ¬ (Continuous (S.η ω) ∧ MonotoneOn (Λ ω) (Ioi 0))}) := by
    rintro ω ⟨hF, hnc⟩
    by_contra hcon
    have hA : innerNbhd (δ / 2) (Λ ω t) ⊆ fillCells ε (S.η ω) (L ε ω) := by
      by_contra hA
      exact hcon (Or.inl (Or.inl ⟨hF, hA⟩))
    have hZ : ω ∈ cellSizeEvent S γ ζ ρ ε := by
      by_contra hZ
      exact hcon (Or.inl (Or.inr hZ))
    have hN : Continuous (S.η ω) ∧ MonotoneOn (Λ ω) (Ioi 0) := by
      by_contra hN
      exact hcon (Or.inr hN)
    exact hnc (innerNbhd_subset_fillCells_vertexThresholdSet hε0.le hN.1 hδ
      (subset_ball_of_lt_clusterExitTime_cover hρ hN.2 ht hF)
      hA (fun k hk => lt_of_le_of_lt ((hZ k hk).2) hεs))
  calc S.P ({ω | t < clusterExitTime (Λ ω) ρ} ∩
        {ω | innerNbhd δ (Λ ω t) ⊆ fillCells ε (S.η ω) (vertexThresholdSet ε (S.η ω) (L ε ω) ρ δ)}ᶜ)
      ≤ S.P (((({ω | t < clusterExitTime (Λ ω) ρ} ∩
          {ω | innerNbhd (δ / 2) (Λ ω t) ⊆ fillCells ε (S.η ω) (L ε ω)}ᶜ) ∪
        (cellSizeEvent S γ ζ ρ ε)ᶜ) ∪
        {ω | ¬ (Continuous (S.η ω) ∧ MonotoneOn (Λ ω) (Ioi 0))})) := measure_mono hsub
    _ ≤ S.P ((({ω | t < clusterExitTime (Λ ω) ρ} ∩
          {ω | innerNbhd (δ / 2) (Λ ω t) ⊆ fillCells ε (S.η ω) (L ε ω)}ᶜ) ∪
        (cellSizeEvent S γ ζ ρ ε)ᶜ)) +
        S.P {ω | ¬ (Continuous (S.η ω) ∧ MonotoneOn (Λ ω) (Ioi 0))} := measure_union_le _ _
    _ ≤ (S.P ({ω | t < clusterExitTime (Λ ω) ρ} ∩
          {ω | innerNbhd (δ / 2) (Λ ω t) ⊆ fillCells ε (S.η ω) (L ε ω)}ᶜ) +
        S.P (cellSizeEvent S γ ζ ρ ε)ᶜ) +
        S.P {ω | ¬ (Continuous (S.η ω) ∧ MonotoneOn (Λ ω) (Ioi 0))} := by
          gcongr
          exact measure_union_le _ _
    _ = S.P ({ω | t < clusterExitTime (Λ ω) ρ} ∩
          {ω | innerNbhd (δ / 2) (Λ ω t) ⊆ fillCells ε (S.η ω) (L ε ω)}ᶜ) +
        S.P (cellSizeEvent S γ ζ ρ ε)ᶜ := by
          rw [hNnull, add_zero]

end MatedCRT
