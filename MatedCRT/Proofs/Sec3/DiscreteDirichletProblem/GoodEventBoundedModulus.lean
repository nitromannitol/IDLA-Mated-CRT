import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.GoodEventRescaleModulus

/-! # Prepared moduli from good-event local bounds -/

namespace MatedCRT

open Set Metric MeasureTheory Filter Topology
open scoped ENNReal

/-- A measurable representative that agrees locally with a field on good
events transfers prepared random bounds into a mesh modulus in probability.
The thinning in the bounds is deterministic and precedes random indices. -/
theorem MatedCRTEnv.IsValid.rescale_modulus_of_good_event_bounds
    {𝒮 : SpaceFillingSLEModel} (h31 : DiscretePotentialTightnessPreparedStmt 𝒮)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    {z : ℂ} {r : ℝ} (hr : 0 < r) (hD : ball z r ⊆ ball 0 ρ)
    (K : Set ℂ) (hK : IsCompact K) (hKD : closure K ⊆ ball z r)
    (F G : ℝ → Ω → ℤ → ℝ) (E : ℝ → Set Ω)
    (hEq : ∀ ε, 0 < ε → ∀ᵐ ω ∂S.P, ω ∈ E ε →
      ∀ a ∈ cellVertices ε (S.η ω) (ball z r), F ε ω a = G ε ω a)
    (hG : ∀ ε, 0 < ε → ∀ a, Measurable[S.envSigma] fun ω => G ε ω a)
    (hbad : Tendsto (fun ε => S.P (E ε)ᶜ) (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hgood : ∀ ε : ℕ → ℝ, (∀ n, 0 < ε n ∧ ε n < (1 / 2) ^ n) →
      ∃ τ : ℕ → ℕ, StrictMono τ ∧ ∃ C : Ω → ℝ,
      Measurable[S.envSigma] C ∧ (∀ ω, 0 < C ω) ∧
      ∀ᵐ ω ∂S.P, ∀ᶠ n in atTop,
        (∀ a ∈ cellVertices (ε (τ n)) (S.η ω) (ball z r),
          G (ε (τ n)) ω a = F (ε (τ n)) ω a) ∧
        (∀ a ∈ interiorCellVertices (ε (τ n)) (S.η ω) (ball z r),
          |matedLaplacian (S.mult (ε (τ n)) ω) (F (ε (τ n)) ω) a| ≤ C ω) ∧
        (∀ a ∈ cellVertices (ε (τ n)) (S.η ω) (ball z r),
          |F (ε (τ n)) ω a| ≤ C ω / ε (τ n)))
    (t : ℝ) (ht : 0 < t) {e : ℝ≥0∞} (he : 0 < e) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), S.P {ω | ∃ x ∈ K, ∃ y ∈ K,
      dist x y < δ ∧ t < |rescale (S.mε ε) ε (S.η ω) (F ε ω) x -
        rescale (S.mε ε) ε (S.η ω) (F ε ω) y|} ≤ e := by
  apply hS.rescale_modulus_of_good_event_compactness (ball z r) K
    (subset_closure.trans hKD) hK F G E hEq hG ?_ hbad t ht he
  intro ε hε
  have hε0 : Tendsto ε atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (show Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) from
        tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
    · intro n; exact (hε n).1.le
    · intro n; exact (hε n).2.le
  obtain ⟨τ, hτ, C, hCm, hC, hbound⟩ := hgood ε hε
  have heq : ∀ᵐ ω ∂S.P, ∀ᶠ n in atTop,
      ∀ a ∈ cellVertices (ε (τ n)) (S.η ω) (ball z r),
        G (ε (τ n)) ω a = F (ε (τ n)) ω a := hbound.mono fun _ h => h.mono fun _ hn => hn.1
  have hb : ∀ᵐ ω ∂S.P, ∀ᶠ n in atTop,
      (∀ a ∈ interiorCellVertices (ε (τ n)) (S.η ω) (ball z r),
        |matedLaplacian (S.mult (ε (τ n)) ω) (F (ε (τ n)) ω) a| ≤ C ω) ∧
      (∀ a ∈ cellVertices (ε (τ n)) (S.η ω) (ball z r),
        |F (ε (τ n)) ω a| ≤ C ω / ε (τ n)) := hbound.mono fun _ h => h.mono fun _ hn => hn.2
  obtain ⟨φ, hφ, hcompact⟩ := hS.prepared_compactness_of_good_event_bounds
    h31 hγ hγ2 hρ hρ1 hr hD (ε ∘ τ) (fun n => (hε (τ n)).1)
    (hε0.comp hτ.tendsto_atTop) (fun ω n => F (ε (τ n)) ω)
    (fun ω n => G (ε (τ n)) ω) (fun n => hG _ (hε (τ n)).1) C hCm hC heq hb
  refine ⟨τ ∘ φ, hτ.comp hφ, ?_⟩
  intro ψ hψ I hIm hI
  let J : Ω → ℕ → ℕ := fun ω n => ψ (I ω n)
  have hJm : ∀ n, Measurable[S.envSigma] fun ω => J ω n := by
    intro n
    let : MeasurableSpace Ω := S.envSigma
    exact (measurable_from_nat (f := ψ)).comp (hIm n)
  have hJ : ∀ ω n, n ≤ J ω n := fun ω n => (hI ω n).trans (hψ.id_le _)
  obtain ⟨θ, hθm, hθ⟩ := hcompact J hJm hJ
  filter_upwards [hθ] with ω hω
  obtain ⟨hm, u, hu, hlocal⟩ := hω
  exact ⟨θ ω, hm, u, hu.mono (subset_closure.trans hKD), by
    simpa only [J, Function.comp_apply] using hlocal K hK hKD⟩

/-- Polynomially high probability implies convergence of the failure
probability to zero along positive mesh sizes. -/
theorem polyHighProb_compl_tendsto_zero
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {E : ℝ → Set Ω}
    (hE : _root_.HarmonicBalls.PolyHighProb P E) :
    Tendsto (fun ε => P (E ε)ᶜ) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  obtain ⟨p, hp, C, r₀, hr₀, h⟩ := hE
  have hlim : Tendsto (fun ε : ℝ => ENNReal.ofReal (C * ε ^ p)) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous (fun ε : ℝ => C * ε ^ p) :=
      continuous_const.mul (continuous_id.rpow_const fun _ => Or.inr hp.le)
    have hzero : Tendsto (fun ε : ℝ => C * ε ^ p) (𝓝[>] 0) (𝓝 (C * (0 : ℝ) ^ p)) :=
      (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    rw [Real.zero_rpow hp.ne', mul_zero] at hzero
    simpa only [ENNReal.ofReal_zero, Function.comp_def] using
      (ENNReal.continuous_ofReal.tendsto _).comp hzero
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [Ioo_mem_nhdsGT hr₀] with ε hε
  exact h ε hε.1 hε.2

/-- Dirichlet data yield a prepared modulus when a measurable representative
agrees on polynomially likely events. The existence of the representative is
a separate finite-domain Green representation obligation. -/
theorem MatedCRTEnv.IsValid.dirichlet_modulus_of_good_event_versions
    {𝒮 : SpaceFillingSLEModel} (h31 : DiscretePotentialTightnessPreparedStmt 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮) (hm : MepsScalingInput 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (h217 : BoundedExitTimeRVStmt)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    {z : ℂ} {r : ℝ} (hr : 0 < r) (hD : ball z r ⊆ ball 0 ρ)
    (ψ φ : ℂ → ℝ) (hψ : ∃ C : ℝ, ∀ x ∈ ball z r, |ψ x| ≤ C)
    (hφ : ∃ s : ℝ, 0 < s ∧ IsHolderContinuousOn φ (closedBall z (r + s)))
    (F G : ℝ → Ω → ℤ → ℝ) (E : ℝ → Set Ω)
    (hF : ∀ ε, 0 < ε → ∀ᵐ ω ∂S.P,
      (∀ a ∈ interiorCellVertices ε (S.η ω) (ball z r),
        matedLaplacian (S.mult ε ω) (F ε ω) a = ψ (vertexPoint ε (S.η ω) a)) ∧
      ∀ b ∈ cellVertices ε (S.η ω) (sphere z r),
        F ε ω b = S.mε ε * φ (vertexPoint ε (S.η ω) b))
    (hEq : ∀ ε, 0 < ε → ∀ᵐ ω ∂S.P, ω ∈ E ε →
      ∀ a ∈ cellVertices ε (S.η ω) (ball z r), F ε ω a = G ε ω a)
    (hG : ∀ ε, 0 < ε → ∀ a, Measurable[S.envSigma] fun ω => G ε ω a)
    (hE : _root_.HarmonicBalls.PolyHighProb S.P E)
    (K : Set ℂ) (hK : IsCompact K) (hKD : closure K ⊆ ball z r)
    (t : ℝ) (ht : 0 < t) {e : ℝ≥0∞} (he : 0 < e) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), S.P {ω | ∃ x ∈ K, ∃ y ∈ K,
      dist x y < δ ∧ t < |rescale (S.mε ε) ε (S.η ω) (F ε ω) x -
        rescale (S.mε ε) ε (S.η ω) (F ε ω) y|} ≤ e := by
  obtain ⟨C, hC⟩ := hψ
  let C' := max C 0
  have hC' : 0 ≤ C' := le_max_right _ _
  have hψ' : ∀ x ∈ ball z r, |ψ x| ≤ C' := fun x hx => (hC x hx).trans (le_max_left _ _)
  obtain ⟨s, hs, L, χ, hχ, _, hh⟩ := hφ
  have hc : ContinuousOn (fun x => |φ x|) (closedBall z (r + s)) := (hh.continuousOn hχ).abs
  obtain ⟨M, hM⟩ := (isCompact_closedBall z (r + s)).bddAbove_image hc
  have hφb : ∀ x ∈ closedBall z (r + s), |φ x| ≤ M := fun x hx => hM ⟨x, hx, rfl⟩
  apply hS.rescale_modulus_of_good_event_bounds h31 hγ hγ2 hρ hρ1 hr hD K hK hKD F G E
    hEq hG (polyHighProb_compl_tendsto_zero hE) ?_ t ht he
  intro ε hε
  have hpoly := isPolySummableScales_of_lt_half_pow hε
  have hε0 := hpoly.tendsto_zero
  have hevent := Tightness.ae_eventually_mem_of_polyHighProb hE hpoly
  have hall : ∀ᵐ ω ∂S.P, ∀ n, ω ∈ E (ε n) →
      ∀ a ∈ cellVertices (ε n) (S.η ω) (ball z r), F (ε n) ω a = G (ε n) ω a :=
    ae_all_iff.mpr fun n => hEq (ε n) (hε n).1
  have heq : ∀ᵐ ω ∂S.P, ∀ᶠ n in atTop,
      ∀ a ∈ cellVertices (ε n) (S.η ω) (ball z r), G (ε n) ω a = F (ε n) ω a := by
    filter_upwards [hevent, hall] with ω hω hallω
    exact hω.mono fun n hn a ha => (hallω n hn a ha).symm
  have hb := ae_eventual_dirichlet_size_of_data h28 hm h218 h217 hγ hγ2 hρ hρ1 S hS
    hr hs hD ψ φ hC' hψ' hφb ε hpoly hε0 F hF
  have hb' : ∀ᵐ ω ∂S.P, ∃ B : ℝ, ∀ᶠ n in atTop,
      ∀ a ∈ cellVertices (ε n) (S.η ω) (ball z r), ε n * |F (ε n) ω a| ≤ B := by
    filter_upwards [hb] with ω ⟨B, hB⟩
    exact ⟨B, hB.mono fun _ hn => hn.2⟩
  obtain ⟨B, hBm, hBpos, hbound⟩ := hS.exists_measurable_local_bound_of_eventual_agreement
    (ball z r) (Or.inl isOpen_ball) isBounded_ball ε (fun n => (hε n).1)
    (fun ω n => F (ε n) ω) (fun ω n => G (ε n) ω) (fun n => hG _ (hε n).1) heq hb'
  refine ⟨id, strictMono_id, fun ω => max C' (B ω), measurable_const.max hBm, ?_, ?_⟩
  · intro ω
    exact lt_of_lt_of_le (by linarith [hBpos ω]) (le_max_right _ _)
  · filter_upwards [heq, hb, hbound] with ω heqω ⟨_, hbω⟩ hboundω
    filter_upwards [heqω, hbω, hboundω] with n hn hbn hboundn
    simp only [id_eq]
    refine ⟨hn, fun a ha => (hbn.1 a ha).trans (le_max_left _ _), fun a ha => ?_⟩
    exact (hboundn a ha).trans (div_le_div_of_nonneg_right (le_max_right _ _) (hε n).1.le)

end MatedCRT
