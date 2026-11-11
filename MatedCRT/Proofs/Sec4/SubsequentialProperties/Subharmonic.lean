import MatedCRT.Proofs.Sec4.SubsequentialProperties.Dirichlet

/-!
# Lemma 4.8, item 2: subsequential limits of the odometer are subharmonic

Step 2 of the proof of Lemma 4.8 (paper/idla_mated_crt-corrected.tex, l.1803-1857).

* `isSuperharmonicOn_neg_of_discrete`: pathwise, if rescaled discrete functions `U_k` converge uniformly on
  `cl(B_ρ)` to `v` and are discrete subharmonic (eventually) on `V^ε(B_s(z)) \ V^ε(∂B_s(z))` for every rational disc
  `cl(B_s(z)) ⊆ O`, along a sequence on which the discrete Dirichlet problems with hat data converge at the centres
  (`ae_tendsto_hatDirichletAtCentre`), then `-v` is superharmonic on the open set `O`;
* `integral_mul_laplacian_nonneg_of_isSuperharmonicOn_neg`: then `Δv ≥ 0` weakly on `O`
  (`laplacianLEOfSuperharmonicStep_holds`, HarmonicBalls);
* `odometer_integral_mul_laplacian_nonneg`: item 2 pathwise, for `U_k = w̃^{ε_k}_t` (discrete subharmonic on
  `V^ε(B_ρ) \ V^ε(∂B_ρ)` by the corrected Lemma 4.4);
* `ae_odometer_integral_mul_laplacian_nonneg`: item 2 almost surely along a deterministic subsequence, for all `t > 0`
  and all uniform subsequential limits.
-/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric _root_.HarmonicBalls Real Laplacian

/-- If `B_s(z) ⊆ B_ρ`, then `V^ε(B_s(z)) \ V^ε(∂B_s(z)) ⊆ V^ε(B_ρ) \ V^ε(∂B_ρ)`. -/
theorem interiorCellVertices_subset_of_ball_subset {ε s ρ : ℝ} {η : ℝ → ℂ} (hη : Continuous η) {z : ℂ}
    (hs : 0 < s) (hρ : 0 < ρ) (h : ball z s ⊆ ball 0 ρ) :
    interiorCellVertices ε η (ball z s) ⊆ interiorCellVertices ε η (ball 0 ρ) := by
  intro a ha
  have hcell := cell_subset_ball_of_mem_interiorCellVertices hη hs ha
  obtain ⟨y, hy, -⟩ := ha.1
  refine ⟨show (cell ε η a ∩ ball 0 ρ).Nonempty from ⟨y, hy, h (hcell hy)⟩, ?_⟩
  rintro ⟨y', hy', hy's⟩
  rw [frontier_ball 0 hρ.ne'] at hy's
  have h1 := h (hcell hy')
  rw [mem_ball] at h1
  rw [mem_sphere] at hy's
  linarith

/-- **Superharmonicity of `-v` from discrete subharmonic approximations** (pathwise). -/
theorem isSuperharmonicOn_neg_of_discrete {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ω : Ω) {ρ : ℝ}
    (harea : IsAreaParametrized (S.μ ω) (S.η ω)) (hp : Tendsto (S.η ω) (cocompact ℝ) (cocompact ℂ))
    (hlf : ∀ ε, 0 < ε → IsLocallyFiniteMult (S.mult ε ω))
    (hcells : ∀ ε, 0 < ε → ∀ j k : ℤ, S.mult ε ω j k ≠ 0 → (cell ε (S.η ω) j ∩ cell ε (S.η ω) k).Nonempty)
    (hmax : ∀ ε, 0 < ε → ∀ A : Set ℤ, A.Nonempty → A.Finite → ∀ u : ℤ → ℝ, IsSubharmonicOn (S.mult ε ω) u A →
      ∀ a ∈ A, ∃ b ∈ vBoundary (S.mult ε ω) A, u a ≤ u b)
    {εk : ℕ → ℝ} (hεk : ∀ k, 0 < εk k) (hεk0 : Tendsto εk atTop (𝓝 0))
    (hdir : ∀ (q₁ q₂ s : ℚ) (n : ℕ) (j l : ℤ), (0 : ℝ) < s → ‖rationalGridPoint q₁ q₂‖ + s < ρ →
      Tendsto (fun k => hatDirichletAtCentre S (rationalGridPoint q₁ q₂) s n j l (εk k) ω) atTop
        (𝓝 (circleAverage (hat n j l) (rationalGridPoint q₁ q₂) s)))
    {U : ℕ → ℤ → ℝ} {v : ℂ → ℝ} (hv : ContinuousOn v (closedBall 0 ρ))
    (hconv : TendstoUniformlyOn (fun k x => (S.mε (εk k))⁻¹ * U k (vertexOf (εk k) (S.η ω) x)) v atTop
      (closedBall 0 ρ))
    {O : Set ℂ} (hO : IsOpen O) (hOρ : O ⊆ ball 0 ρ)
    (hsub : ∀ q₁ q₂ s : ℚ, (0 : ℝ) < s → closedBall (rationalGridPoint q₁ q₂) s ⊆ O →
      ∀ᶠ k in atTop, ∀ a ∈ interiorCellVertices (εk k) (S.η ω) (ball (rationalGridPoint q₁ q₂) s),
        0 ≤ mLaplacian (S.mult (εk k) ω) (U k) a) :
    _root_.HarmonicBalls.IsSuperharmonicOn O (-v) := by
  refine isSuperharmonicOn_of_ratCircles hO ((hv.mono (hOρ.trans ball_subset_closedBall)).neg) ?_
  intro q₁ q₂ s hs hdisc
  have hzr := norm_add_lt_of_closedBall_subset_ball hs.le (hdisc.trans hOρ)
  have h := le_circleAverage_of_discrete_subharmonic harea hp hv hεk hεk0 (M := fun k => S.mult (εk k) ω)
    (fun k => hlf _ (hεk k)) (fun k i => S.mult_succ_ne_zero (hεk k).le ω i) (fun k => hcells _ (hεk k))
    (fun k => hmax _ (hεk k)) (m := fun k => S.mε (εk k)) (fun k => S.mε_nonneg _) hconv hs hzr
    (hsub q₁ q₂ s hs hdisc) (fun n j l => hdir q₁ q₂ s n j l hs hzr)
  rw [circleAverage_neg_fun, Pi.neg_apply]
  linarith

/-- A function whose negative is superharmonic on an open set has a nonnegative weak Laplacian there. -/
theorem integral_mul_laplacian_nonneg_of_isSuperharmonicOn_neg {O : Set ℂ} (hO : IsOpen O) {v : ℂ → ℝ}
    (hvO : ContinuousOn v O) (hsup : _root_.HarmonicBalls.IsSuperharmonicOn O (-v)) :
    ∀ f : ℂ → ℝ, IsTestFunction O f → 0 ≤ f → 0 ≤ ∫ x, v x * Δ f x := by
  have hle := laplacianLEOfSuperharmonicStep_holds O (-v) hO hvO.neg hsup
  intro f hf hf0
  have h := hle.2 f hf hf0 integrable_zero_measure
  simp only [integral_zero_measure, Pi.neg_apply, neg_mul, integral_neg] at h
  linarith

/-- **Lemma 4.8, item 2, pathwise**: along a sequence on which the discrete Dirichlet problems with hat data converge
at the centres of the rational discs, every uniform limit on `cl(B_ρ)` of the rescaled odometers `w̄^{ε_k}_t` satisfies
`Δw ≥ 0` weakly on `B_ρ`. -/
theorem odometer_integral_mul_laplacian_nonneg {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ω : Ω)
    {ρ : ℝ} (hρ : 0 < ρ)
    (harea : IsAreaParametrized (S.μ ω) (S.η ω)) (hp : Tendsto (S.η ω) (cocompact ℝ) (cocompact ℂ))
    (hlf : ∀ ε, 0 < ε → IsLocallyFiniteMult (S.mult ε ω))
    (hcells : ∀ ε, 0 < ε → ∀ j k : ℤ, S.mult ε ω j k ≠ 0 → (cell ε (S.η ω) j ∩ cell ε (S.η ω) k).Nonempty)
    (hmax : ∀ ε, 0 < ε → ∀ A : Set ℤ, A.Nonempty → A.Finite → ∀ u : ℤ → ℝ, IsSubharmonicOn (S.mult ε ω) u A →
      ∀ a ∈ A, ∃ b ∈ vBoundary (S.mult ε ω) A, u a ≤ u b)
    {εk : ℕ → ℝ} (hεk : ∀ k, 0 < εk k) (hεk0 : Tendsto εk atTop (𝓝 0))
    (hdir : ∀ (q₁ q₂ s : ℚ) (n : ℕ) (j l : ℤ), (0 : ℝ) < s → ‖rationalGridPoint q₁ q₂‖ + s < ρ →
      Tendsto (fun k => hatDirichletAtCentre S (rationalGridPoint q₁ q₂) s n j l (εk k) ω) atTop
        (𝓝 (circleAverage (hat n j l) (rationalGridPoint q₁ q₂) s)))
    {t : ℝ} (hsub : ∀ ε, 0 < ε → ∀ a ∈ ballInterior ε (S.η ω) ρ,
      0 ≤ matedLaplacian (S.mult ε ω) (matedLeastSupersolution (S.mult ε ω) ε (S.η ω) ρ t) a)
    {w : ℂ → ℝ} (hwc : ContinuousOn w (closedBall 0 ρ))
    (hconv : TendstoUniformlyOn (fun k => rescaledMatedLeastSupersolution S ρ t (εk k) ω) w atTop
      (closedBall 0 ρ)) :
    ∀ f : ℂ → ℝ, IsTestFunction (ball 0 ρ) f → 0 ≤ f → 0 ≤ ∫ x, w x * Δ f x := by
  refine integral_mul_laplacian_nonneg_of_isSuperharmonicOn_neg isOpen_ball
    (hwc.mono ball_subset_closedBall) ?_
  refine isSuperharmonicOn_neg_of_discrete S ω harea hp hlf hcells hmax hεk hεk0 hdir
    (U := fun k => matedLeastSupersolution (S.mult (εk k) ω) (εk k) (S.η ω) ρ t) hwc hconv isOpen_ball
    subset_rfl ?_
  intro q₁ q₂ s hs hdisc
  refine Eventually.of_forall fun k a ha => ?_
  have ha' : a ∈ ballInterior (εk k) (S.η ω) ρ :=
    interiorCellVertices_subset_of_ball_subset harea.1 hs hρ (ball_subset_closedBall.trans hdisc) ha
  exact hsub (εk k) (hεk k) a ha'

/-- **Lemma 4.8, item 2** (Step 2 of its proof), almost surely along a deterministic subsequence: for all `t > 0`,
every uniform subsequential limit `w` of `w̄^ε_t` on `cl(B_ρ)` satisfies `Δw ≥ 0` weakly on `B_ρ`. Uses Lemma 3.5,
Lemma 2.13 and the corrected Lemma 4.4. -/
theorem ae_odometer_integral_mul_laplacian_nonneg (𝒮 : SpaceFillingSLEModel)
    (h35 : DiscreteDirichletProblemStmt 𝒮) (h213 : MaximumPrincipleStmt 𝒮) (h44 : DiscreteLaplacianBoundCorrectedStmt 𝒮)
    {γ : ℝ} (hγ : 0 < γ) (hγ' : γ < 2) {ρ : ℝ} (hρ : 0 < ρ) (hρ' : ρ < 1) {Ω : Type} [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ) {εs : ℕ → ℝ} (hε : ∀ n, 0 < εs n)
    (hε0 : Tendsto εs atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ ω ∂S.P, ∀ t : ℝ, 0 < t → ∀ w : ℂ → ℝ,
      (ContinuousOn w (closedBall 0 ρ) ∧ ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
        TendstoUniformlyOn (fun k => rescaledMatedLeastSupersolution S ρ t (εs (φ (ψ k))) ω)
          w atTop (closedBall 0 ρ)) →
      ∀ f : ℂ → ℝ, IsTestFunction (ball 0 ρ) f → 0 ≤ f → 0 ≤ ∫ x, w x * Δ f x := by
  obtain ⟨φ, hφ, hφae⟩ := ae_tendsto_hatDirichletAtCentre 𝒮 h35 hγ hγ' hρ hρ' S hS hε hε0
  refine ⟨φ, hφ, ?_⟩
  filter_upwards [hφae, hS.ae_isLocallyFiniteMult hγ hγ' (adjacentCellsMeetAeStep 𝒮),
    adjacentCellsMeetAeStep 𝒮 γ hγ hγ' Ω S hS, h213 γ hγ hγ' Ω S hS, h44 γ hγ hγ' ρ hρ hρ' Ω S hS,
    hS.ae_tendsto_cocompact, hS.isAreaParametrized] with ω hdir hlf hcells hmax h44ω hp harea
  intro t ht w ⟨hwc, ψ, hψ, hconv⟩
  have hφψ : StrictMono (φ ∘ ψ) := hφ.comp hψ
  exact odometer_integral_mul_laplacian_nonneg S ω hρ harea hp hlf hcells hmax (εk := fun k => εs (φ (ψ k)))
    (fun k => hε _) (hε0.comp hφψ.tendsto_atTop)
    (fun q₁ q₂ s n j l hs hzr => (hdir q₁ q₂ s n j l hs hzr).comp hψ.tendsto_atTop)
    (fun ε hε' a ha => ((h44ω t ε ht hε').2.1 a ha).1) hwc hconv

end MatedCRT
