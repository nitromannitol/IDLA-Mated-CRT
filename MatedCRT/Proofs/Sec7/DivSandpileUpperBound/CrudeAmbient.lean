import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.CrudeConfinement

/-! Removing the ambient graph-closure hypothesis from the crude confinement bound. -/

namespace MatedCRT.Sec7

open MeasureTheory Set Metric HarmonicBalls Filter Topology

/-- Small cells meeting a ball force the graph closure of its vertices to meet any
larger concentric ball, provided adjacent cells meet. -/
theorem closure_cellVertices_subset_larger_ball
    {m : ℤ → ℤ → ℕ} {ε ρ R D : ℝ} {η : ℝ → ℂ} {A : Set ℤ}
    (hη : Continuous η) (hρR : ρ < R) (hD : D < R - ρ)
    (hA : A ⊆ cellVertices ε η (ball 0 ρ))
    (hadj : ∀ a b, m a b ≠ 0 → (cell ε η a ∩ cell ε η b).Nonempty)
    (hdiam : ∀ a ∈ cellVertices ε η (ball 0 R), diam (cell ε η a) ≤ D) :
    vClosure m A ⊆ cellVertices ε η (ball 0 R) := by
  intro b hb
  rcases hb with hb | ⟨_, a, ha, hab⟩
  · obtain ⟨z, hzc, hzb⟩ := hA hb
    exact ⟨z, hzc, ball_subset_ball hρR.le hzb⟩
  · obtain ⟨y, hya, hyball⟩ := hA ha
    have haR : a ∈ cellVertices ε η (ball 0 R) :=
      ⟨y, hya, ball_subset_ball hρR.le hyball⟩
    obtain ⟨z, hza, hzb⟩ := hadj a b hab
    have hbounded : Bornology.IsBounded (cell ε η a) := (isCompact_Icc.image hη).isBounded
    have hdist := (dist_le_diam_of_mem hbounded hza hya).trans (hdiam a haR)
    refine ⟨z, hzb, ?_⟩
    rw [mem_ball] at hyball ⊢
    linarith [dist_triangle z y (0 : ℂ)]

/-- The final crude bound follows from a boundary odometer bound, with cell size
estimated in a slightly larger ball around the stopped domain. -/
theorem crude_confinement_without_closure_hypothesis (𝒮 : SpaceFillingSLEModel)
    (hcell : CellSizeEstimateStmt 𝒮) (hcrude : CrudeUpperBoundStmt 𝒮)
    (hadj : AdjacentCellsMeetAeStep 𝒮)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (ζ ρ ω₀ δ : ℝ)
    (hζ : 0 < ζ) (hζ1 : ζ < 1) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hω : 0 < ω₀) (hωα : ω₀ < 2 / (2 + γ) ^ 2 - ζ) (hδ : 0 < δ)
    (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    (t : ℝ) (ht : 0 < t) :
    PolyHighProb S.P fun ε => {ω |
      let m := S.mult ε ω
      let η := S.η ω
      let A := matedDiscreteCluster m ε η ρ t
      ∀ Θ : Set ℤ, (0 : ℤ) ∈ Θ →
        (∀ c ∈ vBoundary m Θ, stoppedOdometer m ε η ρ t c ≤ ε ^ (-ω₀)) →
        fillCells ε η (insert 0 (vClosure m A)) ⊆ cthickening δ (fillCells ε η (vClosure m Θ))} := by
  let R := (ρ + 1) / 2
  have hρR : ρ < R := by dsimp [R]; linarith
  have hR0 : 0 < R := lt_trans hρ hρR
  have hR1 : R < 1 := by dsimp [R]; linarith
  have hα : 0 < 2 / (2 + γ) ^ 2 - ζ := lt_trans hω hωα
  have hp : Tendsto (fun ε : ℝ => ε ^ (2 / (2 + γ) ^ 2 - ζ)) (𝓝[>] 0) (𝓝 0) := by
    have hi : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
    simpa [Real.zero_rpow hα.ne'] using hi.rpow_const (Or.inr hα.le)
  have hsmall := (tendsto_order.1 hp).2 (R - ρ) (sub_pos.mpr hρR)
  obtain ⟨ε₀, hε₀, hεsmall⟩ := (nhdsGT_basis (0 : ℝ)).eventually_iff.mp hsmall
  have hrad := (tendsto_order.1 (tendsto_crude_confinement_radius hα hωα)).2 δ hδ
  obtain ⟨ε₁, hε₁, hεrad⟩ := (nhdsGT_basis (0 : ℝ)).eventually_iff.mp hrad
  have hgood : ∀ᵐ ω ∂S.P, Continuous (S.η ω) ∧
      ∀ ε : ℝ, 0 < ε → ∀ j k : ℤ, S.mult ε ω j k ≠ 0 →
        (cell ε (S.η ω) j ∩ cell ε (S.η ω) k).Nonempty :=
    (hS.isAreaParametrized.and (hadj γ hγ hγ2 Ω S hS)).mono fun _ h => ⟨h.1.1, h.2⟩
  apply polyHighProb_of_inter_ae
    (hcrude γ hγ hγ2 ρ hρ hρ1 Ω S hS t ht)
    (hcell γ hγ hγ2 ζ R hζ hζ1 hR0 hR1 Ω S hS) hgood (lt_min (lt_min hε₀ hε₁) one_pos)
  intro ε hε hε' ω hpath hsize hgeom
  have hε₀' : ε < ε₀ := (hε'.trans_le (min_le_left _ _)).trans_le (min_le_left _ _)
  have hε₁' : ε < ε₁ := (hε'.trans_le (min_le_left _ _)).trans_le (min_le_right _ _)
  have hε1 : ε < 1 := hε'.trans_le (min_le_right _ _)
  dsimp only
  intro Θ hzero hbound
  have hclosure : vClosure (S.mult ε ω) (matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t) ⊆
      cellVertices ε (S.η ω) (ball 0 R) := by
    apply closure_cellVertices_subset_larger_ball hgeom.1 hρR (hεsmall ⟨hε, hε₀'⟩)
      (fun _ ha => ha.1) (hgeom.2 ε hε)
    intro c hc
    exact (hsize c hc).2
  have hlog : 0 < Real.log ε⁻¹ := Real.log_pos ((one_lt_inv₀ hε).2 hε1)
  have hd : 0 < (Real.log ε⁻¹)⁻¹ ^ 2 := by positivity
  have hcontain := crudeUpperBound_event_confinement (S.mult ε ω) Θ ε ρ t
    (ε ^ (2 / (2 + γ) ^ 2 - ζ)) (ε ^ (-ω₀)) (S.η ω)
    (S.mult_symm ε ω) hε.le (Real.rpow_nonneg hε.le _) (Real.rpow_nonneg hε.le _)
    hd hgeom.1 hzero hpath (hgeom.2 ε hε) (fun c hc => (hsize c (hclosure hc)).2) hbound
  have hcontain' := hcontain.trans (cthickening_mono (hεrad ⟨hε, hε₁'⟩).le _)
  intro z hz
  obtain ⟨a, ha, hza⟩ := mem_iUnion₂.mp hz
  rcases ha with rfl | ha
  · exact Metric.self_subset_cthickening _ (mem_iUnion₂.mpr ⟨0, Or.inl hzero, hza⟩)
  · exact hcontain' (mem_iUnion₂.mpr ⟨a, ha, hza⟩)

end MatedCRT.Sec7
