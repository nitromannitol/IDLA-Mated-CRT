import MatedCRT.Steps.Sec5.IDLALowerBound

/-!
# Proposition 5.1, stopped part: reduction to Lemmas 5.3 and 5.4 on `V^ε(Λ_t)`

Proposition 5.1 (corrected.tex:1972-1982) claims the inner bound also for walkers stopped upon exiting `V^ε(Λ_t)`, and
Theorem 6.1 uses exactly this form (lines 2860-2870). The printed proof (lines 2030-2048) gives the bound for walkers
stopped upon exiting the discrete cluster `Λ^ε_t` only; since `Λ^ε_t ⊄ V^ε(Λ_t)` in general, this does not imply the
stated claim (E-c1-5).

The argument of the printed proof does give the stated claim once the two conditions of Lemma 5.2 are known for the
domain `O₂^ε = V^ε(Λ_t)` instead of `Λ^ε_t`: these are Lemmas 5.3 and 5.4 with `Λ^ε_t` replaced by `V^ε(Λ_t)`
(`StoppedMeanValueInequalityStep`, `StoppedLLowerBoundStep`; not in the paper). Then Lemma 5.2 (relaxed) applies with
`O₁^ε = {a ∈ V^ε(Λ_t) : dist(η(a), ∂ V̄^ε(Λ_t)) > δ/4}`, `O₂^ε = V^ε(Λ_t)`, `K_ε = t ε⁻¹`, and the cell-size estimate
(Lemma 2.8) passes from `O₁^ε` to `B⁻_δ(Λ_t)`; the covering `Λ_t ⊆ V̄^ε(Λ_t)` replaces Proposition 4.2.

* `iDLALowerBoundStopped_of_steps : IDLALowerBoundStoppedStep 𝒮` from Lemma 5.2 (relaxed), Lemma 2.8 and the two
  steps above.
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

/-! ## Steps: Lemmas 5.3 and 5.4 on `V^ε(Λ_t)` -/

/-- **Lemma 5.3 on `V^ε(Λ_t)`** (the mean value inequality of Lemma 5.3 with the discrete cluster `Λ^ε_t` replaced by
the vertex set `V^ε(Λ_t)` of the cells meeting the harmonic ball): for `δ ∈ (0, ρ)` and `t > 0` there is a
`σ(h, η)`-measurable `𝔰 > 0` such that, on `{t < T}`, except on an event of probability tending to `0`,
`(1 + 𝔰) ∑_{b ∈ V^ε(Λ_t)} G(b, a) ≤ t ε⁻¹ G(0, a)` for all `a ∈ V^ε(Λ_t)` with `dist(η(a), ∂ V̄^ε(Λ_t)) > δ`,
`G = G^ε_{V^ε(Λ_t)}`. Not in the paper (E-c1-5). -/
def StoppedMeanValueInequalityStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) →
  ∀ δ t : ℝ, 0 < δ → δ < ρ → 0 < t →
  ∃ s : Ω → ℝ, Measurable[S.envSigma] s ∧ (∀ ω, 0 < s ω) ∧
    TendsToOneOn S.P {ω | t < clusterExitTime (Λ ω) ρ} fun ε => {ω |
      ∀ a ∈ cellVertices ε (S.η ω) (Λ ω t),
        δ < infDist (vertexPoint ε (S.η ω) a)
          (frontier (fillCells ε (S.η ω) (cellVertices ε (S.η ω) (Λ ω t)))) →
        (1 + s ω) * ∑' b : cellVertices ε (S.η ω) (Λ ω t),
            greenFn (S.mult ε ω) (cellVertices ε (S.η ω) (Λ ω t)) b a ≤
          t / ε * greenFn (S.mult ε ω) (cellVertices ε (S.η ω) (Λ ω t)) 0 a}

/-- **Lemma 5.4 on `V^ε(Λ_t)`**: there is a deterministic `q > 0` such that for `δ ∈ (0, ρ)` and `t > 0`, on
`{t < T}`, except on an event of probability tending to `0`,
`∑_{b ∈ V^ε(Λ_t)} G(b, a) / G(a, a) ≥ ε^{-q}` for all `a ∈ V^ε(Λ_t)` with `dist(η(a), ∂ V̄^ε(Λ_t)) > δ`,
`G = G^ε_{V^ε(Λ_t)}`. Not in the paper (E-c1-5). -/
def StoppedLLowerBoundStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∃ q : ℝ, 0 < q ∧
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) →
  ∀ δ t : ℝ, 0 < δ → δ < ρ → 0 < t →
    TendsToOneOn S.P {ω | t < clusterExitTime (Λ ω) ρ} fun ε => {ω |
      ∀ a ∈ cellVertices ε (S.η ω) (Λ ω t),
        δ < infDist (vertexPoint ε (S.η ω) a)
          (frontier (fillCells ε (S.η ω) (cellVertices ε (S.η ω) (Λ ω t)))) →
        ε ^ (-q) ≤ (∑' b : cellVertices ε (S.η ω) (Λ ω t),
            greenFn (S.mult ε ω) (cellVertices ε (S.η ω) (Λ ω t)) b a) /
          greenFn (S.mult ε ω) (cellVertices ε (S.η ω) (Λ ω t)) a a}

namespace IDLALowerBound

/-- For a surjective curve, every set is covered by the cells of the vertices whose cells meet it:
`A ⊆ V̄^ε(A)`. -/
theorem subset_fillCells_cellVertices {ε : ℝ} {η : ℝ → ℂ} (hε : 0 < ε) (hsurj : Function.Surjective η)
    (A : Set ℂ) : A ⊆ fillCells ε η (cellVertices ε η A) := by
  intro x hx
  obtain ⟨s, rfl⟩ := hsurj x
  set k : ℤ := ⌈s / ε⌉ with hk
  have h1 : s / ε ≤ k := Int.le_ceil _
  have h2 : (k : ℝ) < s / ε + 1 := Int.ceil_lt_add_one _
  have e : ε * (s / ε) = s := by field_simp
  have h3 : ε * (k : ℝ) < s + ε := by
    have := mul_lt_mul_of_pos_left h2 hε
    rwa [mul_add, mul_one, e] at this
  have h4 : s ≤ ε * (k : ℝ) := by
    have := mul_le_mul_of_nonneg_left h1 hε.le
    rwa [e] at this
  have hmem : η s ∈ cell ε η k := by
    refine ⟨s, ⟨?_, h4⟩, rfl⟩
    rw [mul_sub, mul_one]
    linarith
  exact mem_iUnion₂.mpr ⟨k, ⟨η s, hmem, hx⟩, hmem⟩

/-- On `{t < T}`, `Λ_t ⊆ B_{ρ/3}` (the family is increasing). -/
theorem subset_ball_div_three_of_lt_clusterExitTime {Λ : ℝ → Set ℂ} {ρ t : ℝ} (hmono : MonotoneOn Λ (Ioi 0))
    (ht : 0 < t) (hT : t < clusterExitTime Λ ρ) : Λ t ⊆ ball 0 (ρ / 3) := by
  unfold clusterExitTime at hT
  have hne : {t' : ℝ | 0 < t' ∧ Λ t' ⊆ ball 0 (ρ / 3)}.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    rw [h, Real.sSup_empty] at hT
    linarith
  obtain ⟨t', ⟨ht'0, ht'⟩, htt'⟩ := exists_lt_of_lt_csSup hne hT
  exact fun x hx => ht' (hmono ht ht'0 htt'.le hx)

end IDLALowerBound

open IDLALowerBound in
/-- **The stopped part of Proposition 5.1** from Lemma 5.2 (relaxed), Lemma 2.8 and Lemmas 5.3, 5.4 on `V^ε(Λ_t)`
(with `δ/4`): the argument of lines 2030-2048 with `O₂^ε = V^ε(Λ_t)`. -/
theorem iDLALowerBoundStopped_of_steps (𝒮 : SpaceFillingSLEModel) (h52 : GeneralIDLALowerBoundRelaxedStep 𝒮)
    (h53 : StoppedMeanValueInequalityStep 𝒮) (h54 : StoppedLLowerBoundStep 𝒮) (h28 : CellSizeEstimateStmt 𝒮) :
    IDLALowerBoundStoppedStep 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS Λ hΛ δ t hδ hδρ ht
  have := hS.isProbabilityMeasure
  have hδ4 : 0 < δ / 4 := by positivity
  have hδ4ρ : δ / 4 < ρ := by linarith
  obtain ⟨q, hq, h54'⟩ := h54 γ hγ hγ2 ρ hρ hρ1
  have h4 := h54' Ω S hS Λ hΛ (δ / 4) t hδ4 hδ4ρ ht
  obtain ⟨s, hsm, hspos, h3⟩ := h53 γ hγ hγ2 ρ hρ hρ1 Ω S hS Λ hΛ (δ / 4) t hδ4 hδ4ρ ht
  unfold TendsToOneOn at h3 h4
  -- the cell-size estimate with `ζ = 1/(2+γ)²`
  set e : ℝ := 1 / (2 + γ) ^ 2 with he_def
  have he : 0 < e := by positivity
  have he1 : e < 1 := by
    rw [he_def, div_lt_one (by positivity)]
    nlinarith
  have hexp : 2 / (2 + γ) ^ 2 - e = e := by
    rw [he_def]
    ring
  have hcell := probTendsToOne_of_polyHighProb' (h28 γ hγ hγ2 e ρ he he1 hρ hρ1 Ω S hS)
  unfold ProbTendsToOne at hcell
  -- Lemma 5.2 with `O₁ = {a ∈ V^ε(Λ_t) : dist(η(a), ∂V̄^ε(Λ_t)) > δ/4}`, `O₂ = V^ε(Λ_t)` (both empty off
  -- `{t < T, Λ_t ⊆ B_ρ}`) and `K = t/ε`
  set F : Set Ω := {ω | t < clusterExitTime (Λ ω) ρ} with hF
  set V : ℝ → Ω → Set ℤ := fun ε ω => cellVertices ε (S.η ω) (Λ ω t) with hV
  set G : Set Ω := {ω | ω ∈ F ∧ Λ ω t ⊆ ball 0 ρ} with hG
  set O₂ : ℝ → Ω → Set ℤ := fun ε ω => {a ∈ V ε ω | ω ∈ G} with hO₂
  set O₁ : ℝ → Ω → Set ℤ := fun ε ω => {a ∈ V ε ω | ω ∈ G ∧
    δ / 4 < infDist (vertexPoint ε (S.η ω) a) (frontier (fillCells ε (S.η ω) (V ε ω)))} with hO₁
  have hO₂eq : ∀ ε ω, ω ∈ G → O₂ ε ω = V ε ω := fun ε ω hω => by
    ext a
    exact ⟨fun h => h.1, fun h => ⟨h, hω⟩⟩
  have hO : ∀ ε, 0 < ε → ∀ᵐ ω ∂S.P, O₁ ε ω ⊆ O₂ ε ω ∧ O₂ ε ω ⊆ cellVertices ε (S.η ω) (ball 0 ρ) := by
    intro ε _
    refine ae_of_all _ fun ω => ⟨fun a ha => ⟨ha.1, ha.2.1⟩, fun a ha => ?_⟩
    obtain ⟨x, hx1, hx2⟩ := ha.1
    exact ⟨x, hx1, ha.2.2 hx2⟩
  have h34 := h3.add h4
  rw [zero_add] at h34
  have hgood : ProbTendsToOne S.P (fun ε => {ω | ∀ a ∈ O₁ ε ω,
      (1 + s ω) * ∑' b : O₂ ε ω, greenFn (S.mult ε ω) (O₂ ε ω) b a ≤
        t / ε * greenFn (S.mult ε ω) (O₂ ε ω) 0 a ∧
      ε ^ (-q) ≤ (∑' b : O₂ ε ω, greenFn (S.mult ε ω) (O₂ ε ω) b a) / greenFn (S.mult ε ω) (O₂ ε ω) a a}) := by
    unfold ProbTendsToOne
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h34
      (Eventually.of_forall fun _ => zero_le) (Eventually.of_forall fun ε => ?_)
    refine le_trans (measure_mono ?_) (measure_union_le _ _)
    intro ω hω
    rw [mem_compl_iff] at hω
    have hωG : ω ∈ G := by
      by_contra hωG
      exact hω fun a ha => absurd ha.2.1 hωG
    have hωF : ω ∈ F := hωG.1
    by_contra hcon
    simp only [mem_union, mem_inter_iff, mem_compl_iff, not_or, not_and, not_not] at hcon
    apply hω
    rw [mem_ofPred_eq, hO₂eq ε ω hωG]
    exact fun a ha => ⟨hcon.1 hωF a ha.1 ha.2.2, hcon.2 hωF a ha.1 ha.2.2⟩
  obtain ⟨-, hB⟩ := h52 γ hγ hγ2 ρ hρ hρ1 Ω S hS O₁ O₂ (fun ε => t / ε) q s hO hq hsm hspos hgood
  -- the bad environments: large or degenerate cells, and the null set where `η` is not surjective or `Λ` not
  -- increasing
  set N : Set Ω := {ω | ¬ (Function.Surjective (S.η ω) ∧ MonotoneOn (Λ ω) (Ioi 0))} with hN_def
  have hN : S.P N = 0 := by
    have hae : ∀ᵐ ω ∂S.P, Function.Surjective (S.η ω) ∧ MonotoneOn (Λ ω) (Ioi 0) := by
      filter_upwards [hS.isAreaParametrized, hΛ] with ω h1 h2
      exact ⟨h1.2.2.1, h2.2.1.monotoneOn⟩
    exact ae_iff.1 hae
  have hbad : Tendsto (fun ε => S.P ({ω | ∀ k : ℤ, (cell ε (S.η ω) k ∩ ball 0 ρ).Nonempty →
        ε ^ (2 / (2 - γ) ^ 2 + e) ≤ diam (cell ε (S.η ω) k) ∧
          diam (cell ε (S.η ω) k) ≤ ε ^ (2 / (2 + γ) ^ 2 - e)}ᶜ ∪ N)) (𝓝[>] 0) (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hcell
      (Eventually.of_forall fun _ => zero_le)
      (Eventually.of_forall fun _ => (measure_union_le _ _).trans (by rw [hN, add_zero]))
  have h := hB.add hbad
  rw [zero_add] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [self_mem_nhdsWithin, (tendsto_rpow_nhdsGT_zero' he).eventually (gt_mem_nhds hδ4)]
    with ε (hε : 0 < ε) hεe
  refine annealedOuterProb_le_add S.P _ _ _ _ fun ω hω xs hxs => ?_
  simp only [mem_union, mem_compl_iff, mem_ofPred_eq, not_or, not_not] at hω
  obtain ⟨hcs, hωN⟩ := hω
  obtain ⟨hsurj, hmono⟩ :=
    not_not.1 (hωN : ¬¬ (Function.Surjective (S.η ω) ∧ MonotoneOn (Λ ω) (Ioi 0)))
  obtain ⟨hωF, hnot⟩ := hxs
  have hΛb : Λ ω t ⊆ ball 0 ρ :=
    (subset_ball_div_three_of_lt_clusterExitTime hmono ht hωF).trans (ball_subset_ball (by linarith))
  have hωG : ω ∈ G := ⟨hωF, hΛb⟩
  intro hsub
  apply hnot
  change O₁ ε ω ⊆ stoppedIDLACluster (O₂ ε ω) xs ⌊t / ε⌋₊ at hsub
  rw [hO₂eq ε ω hωG] at hsub
  have hcellL : ∀ a ∈ V ε ω, (cell ε (S.η ω) a ∩ ball 0 ρ).Nonempty := by
    intro a ha
    obtain ⟨x, hx1, hx2⟩ := ha
    exact ⟨x, hx1, hΛb hx2⟩
  have hdiam : ∀ a ∈ V ε ω, ε ^ (2 / (2 - γ) ^ 2 + e) ≤ diam (cell ε (S.η ω) a) ∧
      diam (cell ε (S.η ω) a) ≤ ε ^ e := by
    intro a ha
    have := hcs a (hcellL a ha)
    rwa [hexp] at this
  have hb : ∀ a ∈ V ε ω, Bornology.IsBounded (cell ε (S.η ω) a) := by
    intro a ha
    by_contra hnb
    have h1 := (hdiam a ha).1
    rw [diam_eq_zero_of_unbounded hnb] at h1
    exact absurd h1 (not_le.2 (Real.rpow_pos_of_pos hε _))
  have hd : ∀ a ∈ V ε ω, diam (cell ε (S.η ω) a) < δ / 4 := fun a ha => (hdiam a ha).2.trans_lt hεe
  have hin : innerNbhd (δ / 2) (Λ ω t) ⊆ fillCells ε (S.η ω) (V ε ω) :=
    fun x hx => subset_fillCells_cellVertices hε hsurj _ hx.1
  calc innerNbhd δ (Λ ω t)
      ⊆ fillCells ε (S.η ω) {a ∈ V ε ω |
          δ / 4 < infDist (vertexPoint ε (S.η ω) a) (frontier (fillCells ε (S.η ω) (V ε ω)))} :=
        innerNbhd_subset_fillCells_deep hε.le hδ hb hd hcellL hin
    _ ⊆ fillCells ε (S.η ω) (O₁ ε ω) := fillCells_mono' fun a ha => ⟨ha.1, hωG, ha.2⟩
    _ ⊆ fillCells ε (S.η ω) (stoppedIDLACluster (V ε ω) xs ⌊t / ε⌋₊) := fillCells_mono' hsub

end MatedCRT
