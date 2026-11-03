import MatedCRT.Steps.Sec4.ObstacleSpecialization

/-!
# Section 4: proof of `MatedObstacleSettingStep` and Lemmas 4.3-4.5 from the inputs

* `cellVertices_finite_of_isBounded`: for a continuous proper curve, finitely many cells meet a bounded set; hence
  `V^ε(B_ρ) \ V^ε(∂B_ρ)` is finite and `𝒢^ε` is locally finite.
* `matedObstacleSettingStep_of`: `MatedObstacleSettingStep` from `EtaProperStep`, `ConsecutiveCellsAdjacentStep`,
  `GreenKernelLaplacianStep` and the connectivity of `V^ε(B_ρ) \ V^ε(∂B_ρ)` required by the field
  `IsObstacleSetting.connected` (ESCALATIONS E-c1-2: this connectivity can fail; the hypothesis disappears once the
  field is weakened).
-/

namespace MatedCRT

open MeasureTheory Set Metric Filter Topology

section Deterministic

variable {ε : ℝ} {η : ℝ → ℂ} {ρ : ℝ}

/-- For a continuous curve with `η(s) → ∞` as `|s| → ∞`, finitely many cells meet a bounded set. -/
theorem cellVertices_finite_of_isBounded (hη : Continuous η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    (hε : 0 < ε) {K : Set ℂ} (hK : Bornology.IsBounded K) : (cellVertices ε η K).Finite := by
  obtain ⟨R, hR⟩ := hK.subset_closedBall 0
  have hc : IsCompact (η ⁻¹' closedBall 0 R) :=
    (isProperMap_iff_tendsto_cocompact.2 ⟨hη, hp⟩).isCompact_preimage (isCompact_closedBall 0 R)
  obtain ⟨T, hT⟩ := hc.isBounded.subset_closedBall 0
  refine (Set.finite_Icc (-⌈T / ε + 1⌉) ⌈T / ε + 1⌉).subset ?_
  intro k hk
  obtain ⟨z, ⟨s, hs, rfl⟩, hzK⟩ : ∃ z, z ∈ η '' Icc (ε * (k - 1)) (ε * k) ∧ z ∈ K := hk
  have hsT : |s| ≤ T := by simpa [Real.dist_eq] using hT (hR hzK)
  have h1 : ε * (k - 1) ≤ T := hs.1.trans ((le_abs_self s).trans hsT)
  have h2 : -T ≤ ε * k := ((neg_le_neg hsT).trans (neg_abs_le s)).trans hs.2
  have hk1 : (k : ℝ) ≤ T / ε + 1 := by
    have : (k : ℝ) - 1 ≤ T / ε := (le_div_iff₀ hε).2 (by rw [mul_comm]; exact h1)
    linarith
  have hk2 : -(T / ε + 1) ≤ (k : ℝ) := by
    have h3 : -T / ε ≤ (k : ℝ) := (div_le_iff₀ hε).2 (by rw [mul_comm]; exact h2)
    rw [neg_div] at h3
    linarith
  have hc1 := Int.le_ceil (T / ε + 1)
  constructor
  · have : ((-⌈T / ε + 1⌉ : ℤ) : ℝ) ≤ k := by push_cast; linarith
    exact_mod_cast this
  · exact_mod_cast hk1.trans hc1

/-- `𝒢^ε` is locally finite (continuous proper curve). -/
theorem cellMult_locallyFinite (hη : Continuous η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ)) (hε : 0 < ε)
    (a : ℤ) : {b | cellMult ε η a b ≠ 0}.Finite := by
  have hK : Bornology.IsBounded (cell ε η a) := (isCompact_Icc.image hη).isBounded
  refine (cellVertices_finite_of_isBounded hη hp hε hK).subset fun b hb => ?_
  obtain ⟨z, hza, hzb⟩ := cell_inter_nonempty_of_cellMult_ne_zero hb
  exact ⟨z, hzb, hza⟩

/-- `V^ε(B_ρ) \ V^ε(∂B_ρ)` is finite (continuous proper curve). -/
theorem ballInterior_finite (hη : Continuous η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ)) (hε : 0 < ε) :
    (ballInterior ε η ρ).Finite :=
  (cellVertices_finite_of_isBounded hη hp hε isBounded_ball).subset ballInterior_subset_cellVertices_ball

end Deterministic

/-- `MatedObstacleSettingStep` from the inputs, given the connectivity required by `IsObstacleSetting.connected`
(ESCALATIONS E-c1-2). -/
theorem matedObstacleSettingStep_of {𝒮 : SpaceFillingSLEModel} (hp : EtaProperStep 𝒮)
    (hcons : ConsecutiveCellsAdjacentStep 𝒮) (hG : GreenKernelLaplacianStep)
    (hconn : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ᵐ ω ∂S.P, ∀ ε : ℝ, 0 < ε → (0 : ℤ) ∈ ballInterior ε (S.η ω) ρ →
        IsVConnected (S.mult ε ω) (ballInterior ε (S.η ω) ρ)) :
    MatedObstacleSettingStep 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS
  filter_upwards [hp γ hγ hγ2 Ω S hS, hcons γ hγ hγ2 Ω S hS, hS.isAreaParametrized,
    hconn γ hγ hγ2 ρ hρ hρ1 Ω S hS] with ω hpω hc hη hcω
  intro t ε ht hε h0
  have hlf := cellMult_locallyFinite hη.1 hpω hε
  have hfin : (ballInterior ε (S.η ω) ρ).Finite := ballInterior_finite hη.1 hpω hε
  exact matedObstacle_isObstacleSetting ht hε hlf hfin (hc ε hε) (hcω ε hε h0) h0
    (hG _ _ (cellMult_symm ε (S.η ω)) hlf (hc ε hε) hfin 0 h0)

/-- **Lemma 4.3** (lemma:discrete-basic-properties, line 1679) from the inputs (and the connectivity of E-c1-2). -/
theorem discreteBasicProperties_of_inputs {𝒮 : SpaceFillingSLEModel} (hp : EtaProperStep 𝒮)
    (hcons : ConsecutiveCellsAdjacentStep 𝒮) (hG : GreenKernelLaplacianStep) (hq : NormExitTimeLaplacianStep)
    (hconn : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ᵐ ω ∂S.P, ∀ ε : ℝ, 0 < ε → (0 : ℤ) ∈ ballInterior ε (S.η ω) ρ →
        IsVConnected (S.mult ε ω) (ballInterior ε (S.η ω) ρ)) :
    DiscreteBasicPropertiesStmt 𝒮 :=
  discreteBasicProperties_of_steps (matedObstacleSettingStep_of hp hcons hG hconn) hcons hq

end MatedCRT
