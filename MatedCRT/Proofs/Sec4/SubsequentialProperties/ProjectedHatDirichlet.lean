import MatedCRT.Proofs.Sec4.SubsequentialProperties.Dirichlet
import MatedCRT.Draft.Section3DirichletCorrected

/-! Discrete harmonic extensions of projected hat data. -/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric _root_.HarmonicBalls Real
open scoped ENNReal

/-- **Lemma 3.5 with hat data**, and the value of the limit at the centre. -/
theorem dirichlet_projected_hat_limit (𝒮 : SpaceFillingSLEModel) (h35 : DiscreteDirichletProblemCorrectedStmt 𝒮) {γ : ℝ}
    (hγ : 0 < γ) (hγ' : γ < 2) {ρ : ℝ} (hρ : 0 < ρ) (hρ' : ρ < 1) {Ω : Type} [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ) {z : ℂ} {r : ℝ} (hr : 0 < r) (hzr : ‖z‖ + r < ρ)
    (n : ℕ) (j l : ℤ) :
    ∃ fbar : Ω → ℂ → ℝ, (∀ᵐ ω ∂S.P, fbar ω z = circleAverage (hat n j l) z r) ∧
      TendstoUniformlyOnInProbability S.P (fun ε ω => rescale (S.mε ε) ε (S.η ω)
        (dirichletData (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball z r))
          (fun b => S.mε ε * hat n j l (ballRetraction z r (vertexPoint ε (S.η ω) b))))) fbar (closedBall z r) := by
  have hψb : ∃ M : ℝ, ∀ x ∈ ball z r, |(fun _ : ℂ => (0 : ℝ)) x| ≤ M := ⟨0, fun x _ => by simp⟩
  have hψh : IsHolderContinuousOn (fun _ : ℂ => (0 : ℝ)) (ball z r) :=
    ⟨0, 1, one_pos, le_rfl, (LipschitzWith.const (0 : ℝ)).holderWith.holderOnWith _⟩
  obtain ⟨fbar, hfae, hconv⟩ := h35 γ hγ hγ' ρ hρ hρ' Ω S hS r z hr (ball_subset_ball_of_norm_add_lt hzr)
    (fun _ => 0) (hat n j l) hψb hψh (isHolderContinuousOn_hat n j l _)
    (fun ε ω => dirichletData (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball z r))
      (fun b => S.mε ε * hat n j l (ballRetraction z r (vertexPoint ε (S.η ω) b)))) (by
      intro ε hε
      filter_upwards [hS.ae_isLocallyFiniteMult hγ hγ' (adjacentCellsMeetAeStep 𝒮), hS.ae_tendsto_cocompact,
        hS.isAreaParametrized] with ω hlf hp harea
      have hA : (interiorCellVertices ε (S.η ω) (ball z r)).Finite :=
        (Tightness.cellVertices_finite harea.1 hp hε isBounded_ball).subset fun b hb => hb.1
      refine ⟨fun a ha => ?_, fun b hb => ?_⟩
      · exact mLaplacian_dirichletData (hlf ε hε) (S.mult_succ_ne_zero hε.le ω) hA _ ha
      · have hbA : b ∉ interiorCellVertices ε (S.η ω) (ball z r) :=
          fun h => h.2 (by rwa [frontier_ball z hr.ne'])
        exact dirichletData_of_not_mem hA _ hbA)
  refine ⟨fbar, ?_, hconv⟩
  filter_upwards [hfae] with ω hω
  obtain ⟨hc, hlap, hbd, -⟩ := hω
  refine eq_circleAverage_of_hasLaplacian_zero hr hc
    (hasLaplacian_of_eq hlap (withDensity_eq_zero_of_forall fun x => by simp)
      (withDensity_eq_zero_of_forall fun x => by simp)) hbd


/-- Projection stability for the hat Dirichlet solutions used in the proof of
Lemma 4.8, corrected paper lines 1803–1857. This is an open discrete
boundary-comparison obligation, not a consequence asserted by the statement
of Lemma 3.5 alone. -/
def HatDirichletProjectionStabilityStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  CellSizeEstimateStmt 𝒮 →
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ (r : ℝ) (z : ℂ), 0 < r → ‖z‖ + r < ρ →
  ∀ (n : ℕ) (j l : ℤ), TendstoUniformlyOnInProbability S.P
    (fun ε ω x =>
      rescale (S.mε ε) ε (S.η ω)
        (dirichletData (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball z r))
          (fun b => S.mε ε * hat n j l (vertexPoint ε (S.η ω) b))) x -
      rescale (S.mε ε) ε (S.η ω)
        (dirichletData (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball z r))
          (fun b => S.mε ε * hat n j l (ballRetraction z r (vertexPoint ε (S.η ω) b)))) x)
    (fun _ _ => 0) (closedBall z r)

/-- Uniform convergence in probability is stable under a uniformly negligible
perturbation. -/
theorem uniformInProbability_of_uniform_difference {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (u v : ℝ → Ω → ℂ → ℝ) (w : Ω → ℂ → ℝ) (K : Set ℂ)
    (huv : TendstoUniformlyOnInProbability P (fun ε ω x => u ε ω x - v ε ω x)
      (fun _ _ => 0) K) (hv : TendstoUniformlyOnInProbability P v w K) :
    TendstoUniformlyOnInProbability P u w K := by
  intro δ hδ
  rw [ENNReal.tendsto_nhds_zero]
  intro e he
  have he2 : 0 < e / 2 := ENNReal.half_pos he.ne'
  have h1 := ENNReal.tendsto_nhds_zero.1 (huv (δ / 2) (by positivity)) (e / 2) he2
  have h2 := ENNReal.tendsto_nhds_zero.1 (hv (δ / 2) (by positivity)) (e / 2) he2
  filter_upwards [h1, h2] with ε h1 h2
  calc
    P {ω | ∃ x ∈ K, δ < |u ε ω x - w ω x|} ≤
      P ({ω | ∃ x ∈ K, δ / 2 < |(u ε ω x - v ε ω x) - 0|} ∪
        {ω | ∃ x ∈ K, δ / 2 < |v ε ω x - w ω x|}) := by
      apply measure_mono
      rintro ω ⟨x, hx, hbig⟩
      by_cases h : δ / 2 < |u ε ω x - v ε ω x|
      · exact Or.inl ⟨x, hx, by simpa using h⟩
      · right
        refine ⟨x, hx, ?_⟩
        have hb := abs_add_le (u ε ω x - v ε ω x) (v ε ω x - w ω x)
        have heq : u ε ω x - v ε ω x + (v ε ω x - w ω x) = u ε ω x - w ω x := by ring
        rw [heq] at hb
        linarith [le_of_not_gt h]
    _ ≤ _ := measure_union_le _ _
    _ ≤ e / 2 + e / 2 := add_le_add h1 h2
    _ = e := ENNReal.add_halves e

/-- The existing unprojected hat limit follows from projected Dirichlet
convergence and projection stability. -/
theorem dirichlet_hat_limit_of_projection_stability
    (𝒮 : SpaceFillingSLEModel) (h35 : DiscreteDirichletProblemCorrectedStmt 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮) (hstability : HatDirichletProjectionStabilityStep 𝒮)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ' : γ < 2) (hρ : 0 < ρ) (hρ' : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {z : ℂ} {r : ℝ} (hr : 0 < r) (hzr : ‖z‖ + r < ρ) (n : ℕ) (j l : ℤ) :
    ∃ fbar : Ω → ℂ → ℝ, (∀ᵐ ω ∂S.P, fbar ω z = circleAverage (hat n j l) z r) ∧
      TendstoUniformlyOnInProbability S.P (fun ε ω => rescale (S.mε ε) ε (S.η ω)
        (dirichletData (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball z r))
          (fun b => S.mε ε * hat n j l (vertexPoint ε (S.η ω) b)))) fbar (closedBall z r) := by
  obtain ⟨fbar, hc, hp⟩ := dirichlet_projected_hat_limit 𝒮 h35 hγ hγ' hρ hρ' S hS hr hzr n j l
  refine ⟨fbar, hc, ?_⟩
  exact uniformInProbability_of_uniform_difference S.P _ _ _ _
    (hstability h28 γ hγ hγ' ρ hρ hρ' Ω S hS r z hr hzr n j l) hp

/-- The common subsequence for all rational disks and hats, conditional on projection stability. -/
theorem ae_tendsto_hatDirichletAtCentre_of_projection_stability (𝒮 : SpaceFillingSLEModel) (h35 : DiscreteDirichletProblemCorrectedStmt 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮) (hstability : HatDirichletProjectionStabilityStep 𝒮)
    {γ : ℝ} (hγ : 0 < γ) (hγ' : γ < 2) {ρ : ℝ} (hρ : 0 < ρ) (hρ' : ρ < 1) {Ω : Type} [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ) {εs : ℕ → ℝ} (hε : ∀ n, 0 < εs n)
    (hε0 : Tendsto εs atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ ω ∂S.P, ∀ (q₁ q₂ s : ℚ) (n : ℕ) (j l : ℤ), (0 : ℝ) < s →
      ‖ratPoint q₁ q₂‖ + s < ρ →
      Tendsto (fun k => hatDirichletAtCentre S (ratPoint q₁ q₂) s n j l (εs (φ k)) ω) atTop
        (𝓝 (circleAverage (hat n j l) (ratPoint q₁ q₂) s)) := by
  classical
  have key : ∀ i : DiscHatIndex, ∃ fbar : Ω → ℂ → ℝ,
      ((0 : ℝ) < i.2.2.1 ∧ ‖ratPoint i.1 i.2.1‖ + i.2.2.1 < ρ) →
      (∀ᵐ ω ∂S.P, fbar ω (ratPoint i.1 i.2.1) =
          circleAverage (hat i.2.2.2.1 i.2.2.2.2.1 i.2.2.2.2.2) (ratPoint i.1 i.2.1) i.2.2.1) ∧
        TendstoUniformlyOnInProbability S.P (fun ε ω => rescale (S.mε ε) ε (S.η ω)
          (dirichletData (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball (ratPoint i.1 i.2.1) i.2.2.1))
            (fun b => S.mε ε * hat i.2.2.2.1 i.2.2.2.2.1 i.2.2.2.2.2 (vertexPoint ε (S.η ω) b))))
          fbar (closedBall (ratPoint i.1 i.2.1) i.2.2.1) := by
    intro i
    by_cases hc : (0 : ℝ) < i.2.2.1 ∧ ‖ratPoint i.1 i.2.1‖ + i.2.2.1 < ρ
    · obtain ⟨fbar, h1, h2⟩ := dirichlet_hat_limit_of_projection_stability 𝒮 h35 h28 hstability hγ hγ' hρ hρ' S hS hc.1 hc.2
        i.2.2.2.1 i.2.2.2.2.1 i.2.2.2.2.2
      exact ⟨fbar, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨0, fun h => absurd h hc⟩
  choose fbar hfbar using key
  let E : DiscHatIndex × ℕ → ℝ → Set Ω := fun ia ε =>
    {ω | ((0 : ℝ) < ia.1.2.2.1 ∧ ‖ratPoint ia.1.1 ia.1.2.1‖ + ia.1.2.2.1 < ρ) →
      ∀ x ∈ closedBall (ratPoint ia.1.1 ia.1.2.1) ia.1.2.2.1,
        |rescale (S.mε ε) ε (S.η ω)
            (dirichletData (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball (ratPoint ia.1.1 ia.1.2.1) ia.1.2.2.1))
              (fun b => S.mε ε * hat ia.1.2.2.2.1 ia.1.2.2.2.2.1 ia.1.2.2.2.2.2 (vertexPoint ε (S.η ω) b))) x -
          fbar ia.1 ω x| ≤ 1 / ((ia.2 : ℝ) + 1)}
  have hE : ∀ ia, ProbTendsToOne S.P (E ia) := by
    intro ia
    by_cases hc : (0 : ℝ) < ia.1.2.2.1 ∧ ‖ratPoint ia.1.1 ia.1.2.1‖ + ia.1.2.2.1 < ρ
    · have hTU := (hfbar ia.1 hc).2 (1 / ((ia.2 : ℝ) + 1)) (by positivity)
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hTU (fun _ => zero_le)
        (fun ε => measure_mono ?_)
      intro ω hω
      by_contra hne
      apply hω
      intro _ x hx
      by_contra hlt
      exact hne ⟨x, hx, lt_of_not_ge hlt⟩
    · have h0 : ∀ ε, S.P (E ia ε)ᶜ = 0 := fun ε =>
        measure_mono_null (fun ω hω => (hω fun h => absurd h hc).elim) measure_empty
      show Tendsto (fun ε => S.P (E ia ε)ᶜ) (𝓝[>] 0) (𝓝 0)
      simp only [h0]
      exact tendsto_const_nhds
  obtain ⟨φ, hφ, hφae⟩ := exists_strictMono_ae_eventually_mem_countable hE hε hε0
  refine ⟨φ, hφ, ?_⟩
  have hcentre : ∀ᵐ ω ∂S.P, ∀ i : DiscHatIndex,
      ((0 : ℝ) < i.2.2.1 ∧ ‖ratPoint i.1 i.2.1‖ + i.2.2.1 < ρ) →
      fbar i ω (ratPoint i.1 i.2.1) =
        circleAverage (hat i.2.2.2.1 i.2.2.2.2.1 i.2.2.2.2.2) (ratPoint i.1 i.2.1) i.2.2.1 := by
    rw [ae_all_iff]
    intro i
    by_cases hc : (0 : ℝ) < i.2.2.1 ∧ ‖ratPoint i.1 i.2.1‖ + i.2.2.1 < ρ
    · filter_upwards [(hfbar i hc).1] with ω h _
      exact h
    · exact Eventually.of_forall fun ω h => absurd h hc
  filter_upwards [hφae, hcentre] with ω hω hc
  intro q₁ q₂ s n j l hs hzr
  have hcond : (0 : ℝ) < ((q₁, q₂, s, n, j, l) : DiscHatIndex).2.2.1 ∧
      ‖ratPoint ((q₁, q₂, s, n, j, l) : DiscHatIndex).1 ((q₁, q₂, s, n, j, l) : DiscHatIndex).2.1‖ +
        ((q₁, q₂, s, n, j, l) : DiscHatIndex).2.2.1 < ρ := ⟨hs, hzr⟩
  have hfz := hc (q₁, q₂, s, n, j, l) hcond
  simp only at hfz
  rw [← hfz, Metric.tendsto_atTop]
  intro δ hδ
  obtain ⟨a, ha⟩ := exists_nat_one_div_lt hδ
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hω ((q₁, q₂, s, n, j, l), a))
  refine ⟨N, fun k hk => ?_⟩
  have h := hN k hk hcond (ratPoint q₁ q₂) (mem_closedBall_self hs.le)
  rw [Real.dist_eq]
  exact lt_of_le_of_lt h ha

end MatedCRT

#print axioms MatedCRT.dirichlet_projected_hat_limit
#print axioms MatedCRT.dirichlet_hat_limit_of_projection_stability
#print axioms MatedCRT.ae_tendsto_hatDirichletAtCentre_of_projection_stability
