import MatedCRT.Proofs.Sec4.SubsequentialProperties.SubMeanValue
import MatedCRT.Proofs.Sec4.SubsequentialProperties.ObstacleApproximation
import MatedCRT.Proofs.MatingOfTrees.AdjacentCells
import MatedCRT.Proofs.Infra.LocallyFinite

/-!
# Discrete Dirichlet problems with hat data on rational discs (Lemma 3.5 along a subsequence)

For Steps 2 and 3 of the proof of Lemma 4.8 (paper/idla_mated_crt-corrected.tex, l.1803-1857): "take another
subsequence for which the convergence of Lemma 3.5 occurs a.s. for all `z ∈ ℚ²` and rational `r > 0`, `ψ ≡ 0`, and all
`φ ∈ 𝓕(B_r(z))`". Here `𝓕` is the countable family of tensor hats (`MatedCRT/Proofs/Sec4/SubsequentialProperties/
Hats.lean`).

* `dirichlet_hat_limit`: Lemma 3.5 with `ψ = 0` and data `hat n j l`, applied to the solutions `dirichletData`, and
  the identification of the value of the limit at the centre (`eq_circleAverage_of_hasLaplacian_zero`);
* `exists_strictMono_ae_eventually_mem_countable`: Borel-Cantelli along a diagonal subsequence for a countable family;
* `ae_tendsto_hatDirichletAtCentre`: along a deterministic subsequence, almost surely, for every rational disc
  `B_s(q₁ + i q₂) ⋐ B_ρ` and every hat, the rescaled discrete solution at the centre converges to the circle average
  of the hat.
-/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric _root_.HarmonicBalls Real
open scoped ENNReal

/-- **Borel-Cantelli along a diagonal subsequence**, for a countable family of events holding with probability
tending to one. -/
theorem exists_strictMono_ae_eventually_mem_countable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {ι : Type*} [Countable ι] {E : ι → ℝ → Set Ω} (hE : ∀ i, ProbTendsToOne P (E i)) {εs : ℕ → ℝ}
    (hεs : ∀ n, 0 < εs n) (hεs0 : Tendsto εs atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ ω ∂P, ∀ i, ∀ᶠ n in atTop, ω ∈ E i (εs (φ n)) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨id, strictMono_id, Eventually.of_forall fun ω i => isEmptyElim i⟩
  · obtain ⟨e, he⟩ := exists_surjective_nat ι
    obtain ⟨φ, hφ, hae⟩ := exists_strictMono_ae_eventually_mem_all (E := fun j => E (e j))
      (fun j => hE (e j)) hεs hεs0
    refine ⟨φ, hφ, ?_⟩
    filter_upwards [hae] with ω hω i
    obtain ⟨j, rfl⟩ := he i
    exact hω j

/-- Transport of the measures in `HasLaplacian`. -/
theorem hasLaplacian_of_eq {f : ℂ → ℝ} {μ₁ μ₂ ν₁ ν₂ : Measure ℂ} {U : Set ℂ} (h : HasLaplacian f μ₁ μ₂ U)
    (h1 : μ₁ = ν₁) (h2 : μ₂ = ν₂) : HasLaplacian f ν₁ ν₂ U := h1 ▸ h2 ▸ h

/-- A density which vanishes identically gives the zero measure. -/
theorem withDensity_eq_zero_of_forall {μ : Measure ℂ} {g : ℂ → ℝ≥0∞} (hg : ∀ x, g x = 0) :
    μ.withDensity g = 0 := by
  rw [show g = 0 from funext hg, withDensity_zero]

/-- The rescaled value at the centre `z` of the solution of the discrete Dirichlet problem on
`V^ε(B_r(z)) \ V^ε(∂B_r(z))` with data `m_ε hat n j l (η(·))`. -/
noncomputable def hatDirichletAtCentre {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (z : ℂ) (r : ℝ)
    (n : ℕ) (j l : ℤ) (ε : ℝ) (ω : Ω) : ℝ :=
  (S.mε ε)⁻¹ * dirichletData (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball z r))
    (fun b => S.mε ε * hat n j l (vertexPoint ε (S.η ω) b)) (vertexOf ε (S.η ω) z)

/-- A disc with `|z| + r < ρ` lies in `B_ρ`. -/
theorem ball_subset_ball_of_norm_add_lt {z : ℂ} {r ρ : ℝ} (hzr : ‖z‖ + r < ρ) : ball z r ⊆ ball 0 ρ := by
  intro y hy
  rw [mem_ball] at hy ⊢
  have h := dist_triangle y z 0
  rw [dist_zero_right z] at h
  linarith

/-- **Lemma 3.5 with hat data**, and the value of the limit at the centre. -/
theorem dirichlet_hat_limit (𝒮 : SpaceFillingSLEModel) (h35 : DiscreteDirichletProblemStmt 𝒮) {γ : ℝ}
    (hγ : 0 < γ) (hγ' : γ < 2) {ρ : ℝ} (hρ : 0 < ρ) (hρ' : ρ < 1) {Ω : Type} [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ) {z : ℂ} {r : ℝ} (hr : 0 < r) (hzr : ‖z‖ + r < ρ)
    (n : ℕ) (j l : ℤ) :
    ∃ fbar : Ω → ℂ → ℝ, (∀ᵐ ω ∂S.P, fbar ω z = circleAverage (hat n j l) z r) ∧
      TendstoUniformlyOnInProbability S.P (fun ε ω => rescale (S.mε ε) ε (S.η ω)
        (dirichletData (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball z r))
          (fun b => S.mε ε * hat n j l (vertexPoint ε (S.η ω) b)))) fbar (closedBall z r) := by
  have hψb : ∃ M : ℝ, ∀ x ∈ ball z r, |(fun _ : ℂ => (0 : ℝ)) x| ≤ M := ⟨0, fun x _ => by simp⟩
  have hψh : IsHolderContinuousOn (fun _ : ℂ => (0 : ℝ)) (ball z r) :=
    ⟨0, 1, one_pos, le_rfl, (LipschitzWith.const (0 : ℝ)).holderWith.holderOnWith _⟩
  obtain ⟨fbar, hfae, hconv⟩ := h35 γ hγ hγ' ρ hρ hρ' Ω S hS r z hr (ball_subset_ball_of_norm_add_lt hzr)
    (fun _ => 0) (hat n j l) hψb hψh ⟨1, one_pos, isHolderContinuousOn_hat n j l _⟩
    (fun ε ω => dirichletData (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball z r))
      (fun b => S.mε ε * hat n j l (vertexPoint ε (S.η ω) b))) (by
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

/-- Indices of the rational discs and of the hats: `(q₁, q₂, s, n, j, l)` stands for the disc `B_s(q₁ + i q₂)` and
`hat n j l`. -/
abbrev DiscHatIndex := ℚ × ℚ × ℚ × ℕ × ℤ × ℤ

/-- **Lemma 3.5 along a deterministic subsequence**: almost surely, for every rational disc `B_s(z) ⋐ B_ρ` and every
hat, the rescaled solution at the centre converges to `⨍_{∂B_s(z)} hat`. -/
theorem ae_tendsto_hatDirichletAtCentre (𝒮 : SpaceFillingSLEModel) (h35 : DiscreteDirichletProblemStmt 𝒮)
    {γ : ℝ} (hγ : 0 < γ) (hγ' : γ < 2) {ρ : ℝ} (hρ : 0 < ρ) (hρ' : ρ < 1) {Ω : Type} [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ) {εs : ℕ → ℝ} (hε : ∀ n, 0 < εs n)
    (hε0 : Tendsto εs atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ ω ∂S.P, ∀ (q₁ q₂ s : ℚ) (n : ℕ) (j l : ℤ), (0 : ℝ) < s →
      ‖rationalGridPoint q₁ q₂‖ + s < ρ →
      Tendsto (fun k => hatDirichletAtCentre S (rationalGridPoint q₁ q₂) s n j l (εs (φ k)) ω) atTop
        (𝓝 (circleAverage (hat n j l) (rationalGridPoint q₁ q₂) s)) := by
  classical
  have key : ∀ i : DiscHatIndex, ∃ fbar : Ω → ℂ → ℝ,
      ((0 : ℝ) < i.2.2.1 ∧ ‖rationalGridPoint i.1 i.2.1‖ + i.2.2.1 < ρ) →
      (∀ᵐ ω ∂S.P, fbar ω (rationalGridPoint i.1 i.2.1) =
          circleAverage (hat i.2.2.2.1 i.2.2.2.2.1 i.2.2.2.2.2) (rationalGridPoint i.1 i.2.1) i.2.2.1) ∧
        TendstoUniformlyOnInProbability S.P (fun ε ω => rescale (S.mε ε) ε (S.η ω)
          (dirichletData (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball (rationalGridPoint i.1 i.2.1) i.2.2.1))
            (fun b => S.mε ε * hat i.2.2.2.1 i.2.2.2.2.1 i.2.2.2.2.2 (vertexPoint ε (S.η ω) b))))
          fbar (closedBall (rationalGridPoint i.1 i.2.1) i.2.2.1) := by
    intro i
    by_cases hc : (0 : ℝ) < i.2.2.1 ∧ ‖rationalGridPoint i.1 i.2.1‖ + i.2.2.1 < ρ
    · obtain ⟨fbar, h1, h2⟩ := dirichlet_hat_limit 𝒮 h35 hγ hγ' hρ hρ' S hS hc.1 hc.2
        i.2.2.2.1 i.2.2.2.2.1 i.2.2.2.2.2
      exact ⟨fbar, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨0, fun h => absurd h hc⟩
  choose fbar hfbar using key
  let E : DiscHatIndex × ℕ → ℝ → Set Ω := fun ia ε =>
    {ω | ((0 : ℝ) < ia.1.2.2.1 ∧ ‖rationalGridPoint ia.1.1 ia.1.2.1‖ + ia.1.2.2.1 < ρ) →
      ∀ x ∈ closedBall (rationalGridPoint ia.1.1 ia.1.2.1) ia.1.2.2.1,
        |rescale (S.mε ε) ε (S.η ω)
            (dirichletData (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball (rationalGridPoint ia.1.1 ia.1.2.1) ia.1.2.2.1))
              (fun b => S.mε ε * hat ia.1.2.2.2.1 ia.1.2.2.2.2.1 ia.1.2.2.2.2.2 (vertexPoint ε (S.η ω) b))) x -
          fbar ia.1 ω x| ≤ 1 / ((ia.2 : ℝ) + 1)}
  have hE : ∀ ia, ProbTendsToOne S.P (E ia) := by
    intro ia
    by_cases hc : (0 : ℝ) < ia.1.2.2.1 ∧ ‖rationalGridPoint ia.1.1 ia.1.2.1‖ + ia.1.2.2.1 < ρ
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
      ((0 : ℝ) < i.2.2.1 ∧ ‖rationalGridPoint i.1 i.2.1‖ + i.2.2.1 < ρ) →
      fbar i ω (rationalGridPoint i.1 i.2.1) =
        circleAverage (hat i.2.2.2.1 i.2.2.2.2.1 i.2.2.2.2.2) (rationalGridPoint i.1 i.2.1) i.2.2.1 := by
    rw [ae_all_iff]
    intro i
    by_cases hc : (0 : ℝ) < i.2.2.1 ∧ ‖rationalGridPoint i.1 i.2.1‖ + i.2.2.1 < ρ
    · filter_upwards [(hfbar i hc).1] with ω h _
      exact h
    · exact Eventually.of_forall fun ω h => absurd h hc
  filter_upwards [hφae, hcentre] with ω hω hc
  intro q₁ q₂ s n j l hs hzr
  have hcond : (0 : ℝ) < ((q₁, q₂, s, n, j, l) : DiscHatIndex).2.2.1 ∧
      ‖rationalGridPoint ((q₁, q₂, s, n, j, l) : DiscHatIndex).1 ((q₁, q₂, s, n, j, l) : DiscHatIndex).2.1‖ +
        ((q₁, q₂, s, n, j, l) : DiscHatIndex).2.2.1 < ρ := ⟨hs, hzr⟩
  have hfz := hc (q₁, q₂, s, n, j, l) hcond
  simp only at hfz
  rw [← hfz, Metric.tendsto_atTop]
  intro δ hδ
  obtain ⟨a, ha⟩ := exists_nat_one_div_lt hδ
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hω ((q₁, q₂, s, n, j, l), a))
  refine ⟨N, fun k hk => ?_⟩
  have h := hN k hk hcond (rationalGridPoint q₁ q₂) (mem_closedBall_self hs.le)
  rw [Real.dist_eq]
  exact lt_of_le_of_lt h ha

end MatedCRT
