import MatedCRT.FirstPass.S3g.Estimates
import MatedCRT.Draft.Section2
import MatedCRT.Draft.Section3
import MatedCRT.Draft.Section3DirichletCorrected
import MatedCRT.Proofs.MatingOfTrees.AdjacentCells
import MatedCRT.Steps.Sec2.MaximumPrinciple

/-! # fp-S3g: corrected Lemma 3.5 implies the printed Lemma 3.5 (boundary-stability bridge)

Printed Lemma 3.5 (`DiscreteDirichletProblemStmt`, Draft/Section3.lean:132) prescribes the boundary data
`mε φ(η(b))` at the cells `b` meeting `∂B_r(z)`; corrected Lemma 3.5 (`DiscreteDirichletProblemCorrectedStmt`,
Draft/Section3DirichletCorrected.lean:13) prescribes `mε φ(π η(b))`, with `π` the radial retraction onto
`cl B_r(z)`. The bridge (CHATGPT-idla-printed-3-5.md, "Relation to the corrected statement"):

* `G` solves the corrected problem with the same interior datum `ψ` (`exists_discrete_dirichlet_extension`,
  from the discrete maximum principle `MaximumPrincipleStmt`);
* `H = F - G` is discrete harmonic on the interior cells, so the discrete maximum principle bounds it by its values on
  the boundary cells, where `|H(b)| = mε |φ(η b) - φ(π η b)| ≤ mε C diam(H_b)^χ` (`boundary_bound`);
* the cell-size estimate `CellSizeEstimateStmt` makes `diam(H_b) → 0` in probability, so `rescale F - rescale G → 0`
  uniformly on `cl B_r(z)` in probability; with the corrected limit for `G` this gives the printed limit for `F`.

Inputs: `h28 : CellSizeEstimateStmt 𝒮`, `hmax : MaximumPrincipleStmt 𝒮`, `h35c : DiscreteDirichletProblemCorrectedStmt 𝒮`.
The mating-of-trees adjacency `AdjacentCellsMeetAeStep` (used for the local finiteness and for the boundary location
of the discrete problem) is the proved theorem `adjacentCellsMeetAeStep`, so it is not a further hypothesis. -/

namespace MatedCRT.FirstPass35Bridge

open MeasureTheory Filter Topology Set Metric

/-- The almost-sure graph and curve facts at one sample point, for all `ε > 0`: local finiteness, adjacent cells
meet, the maximum principle on every finite set, and the properness, continuity and surjectivity of `η`. -/
def BridgeGood {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ω : Ω) : Prop :=
  (∀ ε : ℝ, 0 < ε → IsLocallyFiniteMult (S.mult ε ω)) ∧
  (∀ ε : ℝ, 0 < ε → ∀ j k : ℤ, S.mult ε ω j k ≠ 0 → (cell ε (S.η ω) j ∩ cell ε (S.η ω) k).Nonempty) ∧
  (∀ ε : ℝ, 0 < ε → ∀ A : Set ℤ, A.Finite → ∀ u : ℤ → ℝ, IsSubharmonicOn (S.mult ε ω) u A →
    ∀ a ∈ A, ∃ b ∈ vBoundary (S.mult ε ω) A, u a ≤ u b) ∧
  Tendsto (S.η ω) (cocompact ℝ) (cocompact ℂ) ∧ Continuous (S.η ω) ∧ Function.Surjective (S.η ω)

/-- The interior cells of a ball form a finite set (properness of `η`). -/
theorem interior_finite {ε : ℝ} {η : ℝ → ℂ} {z : ℂ} {r : ℝ} (hη : Continuous η)
    (hp : Tendsto η (cocompact ℝ) (cocompact ℂ)) (hε : 0 < ε) :
    (interiorCellVertices ε η (ball z r)).Finite :=
  (cellVertices_finite_of_isCompact hη hp hε (isCompact_closedBall z r)).subset fun _ ha =>
    Set.Nonempty.mono (inter_subset_inter_right _ ball_subset_closedBall) ha.1

/-- **Bridge (fp-S3g).** Corrected Lemma 3.5 together with the cell-size estimate and the discrete maximum principle
gives the printed Lemma 3.5 (`DiscreteDirichletProblemStmt`). The conclusion `fbar` is the one of the corrected
statement for the projected problem `G`. -/
theorem discreteDirichletProblem_of_corrected {𝒮 : SpaceFillingSLEModel}
    (h28 : CellSizeEstimateStmt 𝒮) (hmax : MaximumPrincipleStmt 𝒮)
    (h35c : DiscreteDirichletProblemCorrectedStmt 𝒮) : DiscreteDirichletProblemStmt 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS r z hr hball ψ φ hψb hψh hφ F hF
  obtain ⟨s, hs, hφs⟩ := hφ
  obtain ⟨C, χ, hχ0, hχ1, hHol⟩ := hφs
  have hr0 : r ≠ 0 := hr.ne'
  have hφr : IsHolderContinuousOn φ (closedBall z r) :=
    ⟨C, χ, hχ0, hχ1, hHol.mono (closedBall_subset_closedBall (by linarith))⟩
  -- almost sure graph and curve facts
  have hgoodAe : ∀ᵐ ω ∂S.P, BridgeGood S ω := by
    filter_upwards [hS.ae_isLocallyFiniteMult hγ hγ2 (adjacentCellsMeetAeStep 𝒮),
      adjacentCellsMeetAeStep 𝒮 γ hγ hγ2 Ω S hS, hmax γ hγ hγ2 Ω S hS,
      hS.ae_tendsto_cocompact, hS.isAreaParametrized] with ω h1 h2 h3 h4 h5
    exact ⟨h1, h2, fun ε hε A hAf u hu a ha => h3 ε hε A ⟨a, ha⟩ hAf u hu a ha, h4, h5.1, h5.2.2.1⟩
  -- the projected discrete solution `G` (corrected boundary datum), pointwise in `(ε, ω)`
  have hex : ∀ (ε : ℝ) (ω : Ω), ∃ g : ℤ → ℝ, 0 < ε → BridgeGood S ω →
      (∀ a ∈ interiorCellVertices ε (S.η ω) (ball z r),
        matedLaplacian (S.mult ε ω) g a = ψ (vertexPoint ε (S.η ω) a)) ∧
      ∀ b ∈ cellVertices ε (S.η ω) (sphere z r),
        g b = S.mε ε * φ (ballRetraction z r (vertexPoint ε (S.η ω) b)) := by
    intro ε ω
    by_cases h : 0 < ε ∧ BridgeGood S ω
    · obtain ⟨hε, hlfG, -, hmaxG, hcocG, hcontG, -⟩ := And.intro h.1 h.2
      have hfin : (interiorCellVertices ε (S.η ω) (ball z r)).Finite := interior_finite hcontG hcocG hε
      obtain ⟨G, hGb, hGa⟩ := exists_discrete_dirichlet_extension (hlfG ε hε) hfin
        (fun u hu a ha => hmaxG ε hε _ hfin u hu a ha)
        (fun a => ψ (vertexPoint ε (S.η ω) a))
        (Set.indicator (cellVertices ε (S.η ω) (sphere z r))
          (fun b => S.mε ε * φ (ballRetraction z r (vertexPoint ε (S.η ω) b))))
      refine ⟨G, fun _ _ => ⟨fun a ha => hGa a ha, fun b hb => ?_⟩⟩
      have hbnot : b ∉ interiorCellVertices ε (S.η ω) (ball z r) := fun hA =>
        hA.2 (by rw [frontier_ball z hr0]; exact hb)
      rw [hGb b hbnot, Set.indicator_of_mem hb]
    · exact ⟨fun _ => 0, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose Gf hGf using hex
  -- the good events for the probability argument
  have hGfAe : ∀ ε, 0 < ε → ∀ᵐ ω ∂S.P,
      (∀ a ∈ interiorCellVertices ε (S.η ω) (ball z r),
        matedLaplacian (S.mult ε ω) (Gf ε ω) a = ψ (vertexPoint ε (S.η ω) a)) ∧
      ∀ b ∈ cellVertices ε (S.η ω) (sphere z r),
        Gf ε ω b = S.mε ε * φ (ballRetraction z r (vertexPoint ε (S.η ω) b)) := by
    intro ε hε
    filter_upwards [hgoodAe] with ω h1
    exact hGf ε ω hε h1
  obtain ⟨fbar, hfbar, hconv⟩ :=
    h35c γ hγ hγ2 ρ hρ hρ1 Ω S hS r z hr hball ψ φ hψb hψh hφr Gf hGfAe
  refine ⟨fbar, ?_, ?_⟩
  · filter_upwards [hfbar] with ω hω
    exact ⟨hω.1, hω.2.1, hω.2.2.1, hω.2.2.2⟩
  · -- the convergence of the printed problem, from `hconv` and the cell-size estimate
    have hq : 0 < 2 / (2 + γ) ^ 2 - 1 / 16 := by
      have hpos : (0 : ℝ) < (2 + γ) ^ 2 := by positivity
      rw [sub_pos, lt_div_iff₀ hpos]
      nlinarith
    have hρ₁ : 0 < (1 + ρ) / 2 := by linarith
    have hρ₁1 : (1 + ρ) / 2 < 1 := by linarith
    have hEpoly := h28 γ hγ hγ2 (1 / 16) ((1 + ρ) / 2) (by norm_num) (by norm_num) hρ₁ hρ₁1 Ω S hS
    have hsph : sphere z r ⊆ ball 0 ((1 + ρ) / 2) :=
      sphere_subset_ball_of_ball_subset hr0 hρ hball (by linarith)
    have hχpos : 0 < (χ : ℝ) := NNReal.coe_pos.2 hχ0
    have hg : Tendsto (fun ε : ℝ => (C : ℝ) * (ε ^ (2 / (2 + γ) ^ 2 - 1 / 16)) ^ (χ : ℝ)) (𝓝[>] 0) (𝓝 0) := by
      have h1 := (tendsto_const_nhds (x := (C : ℝ))).mul
        ((tendsto_rpow_zero_nhds hχpos).comp (tendsto_rpow_nhdsGT_zero hq))
      rw [mul_zero] at h1
      exact h1
    have hsmall : ∀ᶠ ε in 𝓝[>] 0, ε ^ (2 / (2 + γ) ^ 2 - 1 / 16) ≤ s :=
      (tendsto_rpow_nhdsGT_zero hq).eventually (eventually_le_nhds hs)
    have hGsetAe : ∀ ε, 0 < ε → ∀ᵐ ω ∂S.P, ω ∈ {ω : Ω | BridgeGood S ω ∧
        (∀ a ∈ interiorCellVertices ε (S.η ω) (ball z r),
          matedLaplacian (S.mult ε ω) (F ε ω) a = ψ (vertexPoint ε (S.η ω) a)) ∧
        ∀ b ∈ cellVertices ε (S.η ω) (sphere z r), F ε ω b = S.mε ε * φ (vertexPoint ε (S.η ω) b)} := by
      intro ε hε
      filter_upwards [hgoodAe, hF ε hε] with ω h1 h2
      show BridgeGood S ω ∧ _
      exact ⟨h1, h2.1, h2.2⟩
    refine tendsto_uniformly_inProb_of_sup_bound S.P hconv hEpoly hGsetAe hg ?_
    filter_upwards [hsmall, self_mem_nhdsWithin] with ε hεs hε0
    have hε : 0 < ε := hε0
    intro ω hωG hωE x hx
    obtain ⟨hωGood, hFint, hFbd⟩ : BridgeGood S ω ∧
        (∀ a ∈ interiorCellVertices ε (S.η ω) (ball z r),
          matedLaplacian (S.mult ε ω) (F ε ω) a = ψ (vertexPoint ε (S.η ω) a)) ∧
        ∀ b ∈ cellVertices ε (S.η ω) (sphere z r), F ε ω b = S.mε ε * φ (vertexPoint ε (S.η ω) b) := hωG
    have hωE' : ∀ k : ℤ, (cell ε (S.η ω) k ∩ ball 0 ((1 + ρ) / 2)).Nonempty →
        ε ^ (2 / (2 - γ) ^ 2 + 1 / 16) ≤ diam (cell ε (S.η ω) k) ∧
          diam (cell ε (S.η ω) k) ≤ ε ^ (2 / (2 + γ) ^ 2 - 1 / 16) := hωE
    have hGood' := hGf ε ω hε hωGood
    obtain ⟨hlfG, hadjG, hmaxG, hcocG, hcontG, hsurjG⟩ := hωGood
    have hlfε := hlfG ε hε
    have hfin : (interiorCellVertices ε (S.η ω) (ball z r)).Finite :=
      interior_finite hcontG hcocG hε
    have hHarm : ∀ a ∈ interiorCellVertices ε (S.η ω) (ball z r),
        mLaplacian (S.mult ε ω) (fun y => F ε ω y - Gf ε ω y) a = 0 := by
      intro a ha
      rw [mLaplacian_sub_of_locallyFinite hlfε (F ε ω) (Gf ε ω) a]
      have h1 : mLaplacian (S.mult ε ω) (F ε ω) a = ψ (vertexPoint ε (S.η ω) a) := hFint a ha
      have h2 : mLaplacian (S.mult ε ω) (Gf ε ω) a = ψ (vertexPoint ε (S.η ω) a) := hGood'.1 a ha
      rw [h1, h2, sub_self]
    have hD : ∀ b ∈ cellVertices ε (S.η ω) (sphere z r),
        |F ε ω b - Gf ε ω b| ≤ |S.mε ε| * ((C : ℝ) * (ε ^ (2 / (2 + γ) ^ 2 - 1 / 16)) ^ (χ : ℝ)) := by
      intro b hb
      have hdiam : diam (cell ε (S.η ω) b) ≤ ε ^ (2 / (2 + γ) ^ 2 - 1 / 16) := by
        obtain ⟨w, hw1, hw2⟩ := hb
        exact (hωE' b ⟨w, hw1, hsph hw2⟩).2
      have hbb := boundary_bound hε hcontG hr hs hεs hHol hb hdiam
      rw [hFbd b hb, hGood'.2 b hb, ← mul_sub, abs_mul]
      exact mul_le_mul_of_nonneg_left hbb (abs_nonneg _)
    have hK₀ : 0 ≤ (C : ℝ) * (ε ^ (2 / (2 + γ) ^ 2 - 1 / 16)) ^ (χ : ℝ) :=
      mul_nonneg (NNReal.coe_nonneg C) (Real.rpow_nonneg (Real.rpow_nonneg hε.le _) _)
    exact rescale_sub_bound hε hcontG hsurjG hcocG hr hlfε (hadjG ε hε)
      (fun u hu a ha => hmaxG ε hε _ hfin u hu a ha) (F ε ω) (Gf ε ω) hK₀ hHarm hD x hx

/-- **Corollary (fp-S3g).** The printed Lemma 3.5 from the corrected one and the cell-size estimate; the discrete
maximum principle is the proved `maximumPrinciple_of_steps (adjacentCellsMeetAeStep 𝒮)`. -/
theorem discreteDirichletProblem_of_corrected_of_steps {𝒮 : SpaceFillingSLEModel}
    (h28 : CellSizeEstimateStmt 𝒮) (h35c : DiscreteDirichletProblemCorrectedStmt 𝒮) :
    DiscreteDirichletProblemStmt 𝒮 :=
  discreteDirichletProblem_of_corrected h28 (maximumPrinciple_of_steps (adjacentCellsMeetAeStep 𝒮)) h35c

end MatedCRT.FirstPass35Bridge

#print axioms MatedCRT.FirstPass35Bridge.discreteDirichletProblem_of_corrected
#print axioms MatedCRT.FirstPass35Bridge.discreteDirichletProblem_of_corrected_of_steps
