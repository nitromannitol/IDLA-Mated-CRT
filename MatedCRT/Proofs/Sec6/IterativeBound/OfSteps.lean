import MatedCRT.Steps.Sec6.IterativeBound
import MatedCRT.Proofs.Sec6.ChanceOfBeingAbsorbed.Chernoff

/-!
# Lemma 6.10 from its steps: the annealed assembly (lines 2706-2709, 2836-2838)

`iterativeBound_of_steps`: Lemma 6.9 is applied at `(1 + ρ)/2` with `β⁻ = (2 + γ)²/2 + 1`, Lemma 2.8 with
`ζ = (2 + γ)⁻²` (so `diam H^ε_a ≤ ε^{(2+γ)⁻²}`), the quenched iteration gives `β` and `D₀`, and
`𝛅₀ = min(D₀, s₅ (𝛅 ∧ 1)^{2β⁻}/2)` with `𝛅` the radius of Lemma 6.9. The conclusion holds with `C = 1`. On the
intersection of the events of Lemmas 6.9, 2.8, the adjacency of cells and the almost sure Abelian property and
continuity of `η`, and on `{𝛅 ≥ τ}`, the supremum of the quenched failure probabilities is at most `θ(ε) → 0`; the
outer integral then tends to `0` (`tendsto_outerLIntegral_of_eventually_le`).
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace IterativeBound

theorem probTendsToOne_inter {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {E F : ℝ → Set Ω}
    (hE : ProbTendsToOne P E) (hF : ProbTendsToOne P F) : ProbTendsToOne P fun ε => E ε ∩ F ε := by
  unfold ProbTendsToOne at *
  have h := hE.add hF
  rw [add_zero] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => zero_le) fun ε => ?_
  rw [compl_inter]
  exact measure_union_le _ _

/-- An event of polynomially high probability as `ε → 0` holds with probability tending to `1`. -/
theorem probTendsToOne_of_polyHighProb {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {E : ℝ → Set Ω}
    (h : HarmonicBalls.PolyHighProb P E) : ProbTendsToOne P E := by
  obtain ⟨p, hp, C, r₀, hr₀, hbound⟩ := h
  have hup : Tendsto (fun ε : ℝ => ENNReal.ofReal (C * ε ^ p)) (𝓝[>] 0) (𝓝 0) := by
    have h3 : Tendsto (fun ε : ℝ => ε ^ p) (𝓝[>] 0) (𝓝 ((0 : ℝ) ^ p)) :=
      ((Real.continuousAt_rpow_const 0 p (Or.inr hp.le)).tendsto).mono_left nhdsWithin_le_nhds
    rw [Real.zero_rpow hp.ne'] at h3
    have h4 := h3.const_mul C
    rw [mul_zero] at h4
    have h5 := ENNReal.tendsto_ofReal h4
    rwa [ENNReal.ofReal_zero] at h5
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hr₀)] with ε hε hεr
  exact hbound _ hε hεr

theorem probTendsToOne_of_ae {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {G : Set Ω}
    (hG : ∀ᵐ ω ∂P, ω ∈ G) : ProbTendsToOne P fun _ => G := by
  unfold ProbTendsToOne
  have h : P Gᶜ = 0 := ae_iff.1 hG
  simp only [h]
  exact tendsto_const_nhds

/-- If `f ε ≤ 1` and, for each `τ > 0`, eventually `f ε ≤ θ ε → 0` on `E ε ∩ {s ≥ τ}`, where `P[(E ε)ᶜ] → 0` and
`s > 0` is measurable, then the outer integral `∫* f ε dP → 0`. (Worker c2's
`tendsto_outerLIntegral_of_eventually_le` of MatedCRT/Steps/Sec5/GeneralIDLALowerBound.lean, repeated here because
that module imports MatedCRT/Draft/Section5.lean, which does not build in the current working tree.) -/
theorem tendsto_outerLIntegral_of_eventually_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (f : ℝ → Ω → ℝ≥0∞) (hf : ∀ ε ω, f ε ω ≤ 1) (s : Ω → ℝ)
    (hs : Measurable s) (hspos : ∀ ω, 0 < s ω) (E : ℝ → Set Ω)
    (hE : Tendsto (fun ε => P (E ε)ᶜ) (𝓝[>] 0) (𝓝 0))
    (hb : ∀ τ : ℝ, 0 < τ → ∃ θ : ℝ → ℝ≥0∞, Tendsto θ (𝓝[>] 0) (𝓝 0) ∧
      ∀ᶠ ε in 𝓝[>] 0, ∀ ω ∈ E ε, τ ≤ s ω → f ε ω ≤ θ ε) :
    Tendsto (fun ε => outerLIntegral P (f ε)) (𝓝[>] 0) (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro e he
  have he2 : 0 < e / 2 := ENNReal.half_pos he.ne'
  set A : ℕ → Set Ω := fun n => {ω | s ω < 1 / ((n : ℝ) + 1)} with hA
  have hlim : Tendsto (fun n => P (A n)) atTop (𝓝 0) := by
    have hanti : Antitone A := by
      intro i j hij ω hω
      simp only [hA, mem_ofPred_eq] at hω ⊢
      refine hω.trans_le (one_div_le_one_div_of_le (by positivity) ?_)
      have : (i : ℝ) ≤ j := by exact_mod_cast hij
      linarith
    have h := tendsto_measure_iInter_atTop (μ := P)
      (fun n => (measurableSet_lt hs measurable_const).nullMeasurableSet) hanti ⟨0, measure_ne_top P _⟩
    have hempty : (⋂ n, A n) = ∅ := by
      ext ω
      simp only [hA, mem_iInter, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_forall, not_lt]
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (hspos ω)
      exact ⟨n, hn.le⟩
    rw [hempty, measure_empty] at h
    exact h
  obtain ⟨N, hN⟩ := (ENNReal.tendsto_nhds_zero.1 hlim (e / 2) he2).exists
  have hτ : (0 : ℝ) < 1 / ((N : ℝ) + 1) := by positivity
  obtain ⟨θ, hθ, hev⟩ := hb _ hτ
  have hsum : Tendsto (fun ε => P (E ε)ᶜ + θ ε) (𝓝[>] 0) (𝓝 0) := by
    simpa using hE.add hθ
  filter_upwards [hev, ENNReal.tendsto_nhds_zero.1 hsum (e / 2) he2] with ε hε hε2
  set T := toMeasurable P ((E ε)ᶜ ∪ A N) with hT
  have hpt : ∀ ω, f ε ω ≤ T.indicator 1 ω + θ ε := by
    intro ω
    by_cases hω : ω ∈ T
    · rw [indicator_of_mem hω]
      exact (hf ε ω).trans le_self_add
    · have hω' : ω ∉ (E ε)ᶜ ∪ A N := fun h => hω (subset_toMeasurable _ _ h)
      simp only [hA, mem_union, mem_compl_iff, not_or, not_not, mem_ofPred_eq, not_lt] at hω'
      exact (hε ω hω'.1 hω'.2).trans le_add_self
  have hgm : Measurable fun ω => T.indicator 1 ω + θ ε :=
    (measurable_one.indicator (measurableSet_toMeasurable _ _)).add measurable_const
  calc outerLIntegral P (f ε) ≤ ∫⁻ ω, (T.indicator 1 ω + θ ε) ∂P :=
        iInf_le_of_le (fun ω => T.indicator 1 ω + θ ε) (iInf_le_of_le hgm (iInf_le_of_le hpt le_rfl))
    _ = P T + θ ε := by
        rw [lintegral_add_right _ measurable_const,
          lintegral_indicator_one (measurableSet_toMeasurable _ _), lintegral_const, measure_univ, mul_one]
    _ ≤ (P (E ε)ᶜ + P (A N)) + θ ε := by
        rw [hT, measure_toMeasurable]
        exact add_le_add (measure_union_le _ _) le_rfl
    _ = P (A N) + (P (E ε)ᶜ + θ ε) := by rw [add_comm (P (E ε)ᶜ), add_assoc]
    _ ≤ e / 2 + e / 2 := add_le_add hN hε2
    _ = e := ENNReal.add_halves e

end IterativeBound

open IterativeBound in
/-- **Lemma 6.10** from Lemma 6.9 (E-A10 (b) form), Lemma 6.3 for arbitrary starting sites (E-c5-2), Lemma 2.8, the
adjacency of cells (IR-A2), the walk path property, the measurability of the environment and the quenched
iteration. -/
theorem iterativeBound_of_steps (𝒮 : SpaceFillingSLEModel) (h69 : ChanceOfBeingAbsorbedLogLossStmt 𝒮)
    (h63 : AbelianIDLAAnyStartStep 𝒮) (h28 : CellSizeEstimateStmt 𝒮) (hadj : AdjacentCellsMeetStep 𝒮)
    (hsrw : SrwPathStep) (henv : FieldSigmaMeasurableStep 𝒮) (hq : QuenchedIterationStep) :
    IterativeBoundStmt 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1
  have hρ'0 : 0 < (1 + ρ) / 2 := by linarith
  have hρ'1 : (1 + ρ) / 2 < 1 := by linarith
  have hβm : (2 + γ) ^ 2 / 2 < (2 + γ) ^ 2 / 2 + 1 := by linarith
  have hβm0 : 1 ≤ (2 + γ) ^ 2 / 2 + 1 := le_add_of_nonneg_left (by positivity)
  have hγ' : 0 < (2 + γ) ^ 2 := by positivity
  have hζ0 : 0 < 1 / (2 + γ) ^ 2 := by positivity
  have hζ1 : 1 / (2 + γ) ^ 2 < 1 := by
    rw [div_lt_one hγ']
    nlinarith
  have hκ : 0 < 2 / (2 + γ) ^ 2 - 1 / (2 + γ) ^ 2 := by
    have : 2 / (2 + γ) ^ 2 - 1 / (2 + γ) ^ 2 = 1 / (2 + γ) ^ 2 := by ring
    rw [this]
    exact hζ0
  obtain ⟨ω₀, hω₀, h69⟩ := h69 γ hγ hγ2 _ hρ'0 hρ'1 _ hβm
  obtain ⟨β, hβ, hq⟩ := hq ρ _ ω₀ _ hρ hρ1 hβm0 hω₀ hκ
  refine ⟨β, 1, hβ, one_pos, fun s₀ hs₀ hs₀1 Ω _ S hS => ?_⟩
  have := hS.isProbabilityMeasure
  obtain ⟨s₃, s₄, s₅, hs₃, hs₄, hs₄1, hs₅, hs₅1, h69⟩ := h69 s₀ hs₀ hs₀1
  obtain ⟨D₀, hD₀, hq⟩ := hq s₀ s₃ s₄ s₅ hs₀ hs₃ hs₄ hs₄1 hs₅ hs₅1
  obtain ⟨dd, hddm, hddpos, hE9⟩ := h69 Ω S hS
  refine ⟨fun ω => min D₀ (s₅ * min (dd ω) 1 ^ (2 * ((2 + γ) ^ 2 / 2 + 1)) / 2), ?_, ?_, ?_⟩
  · exact measurable_const.min ((((hddm.min measurable_const).pow_const _).const_mul _).div_const _)
  · intro ω
    have h1 : 0 < min (dd ω) 1 := lt_min (hddpos ω) one_pos
    exact lt_min hD₀ (div_pos (mul_pos hs₅ (Real.rpow_pos_of_pos h1 _)) two_pos)
  · have hddm' : Measurable dd := hddm.mono (henv γ hγ hγ2 Ω S hS) le_rfl
    have h28' := probTendsToOne_of_polyHighProb
      (h28 γ hγ hγ2 (1 / (2 + γ) ^ 2) ((1 + ρ) / 2) hζ0 hζ1 hρ'0 hρ'1 Ω S hS)
    have hadj' := hadj γ hγ hγ2 ((1 + ρ) / 2) hρ'0 hρ'1 Ω S hS
    have hab' := probTendsToOne_of_ae (P := S.P)
      (G := {ω | ∀ ε : ℝ, 0 < ε → IsAbelianIDLA (S.mult ε ω)}) (h63 γ hγ hγ2 Ω S hS)
    have hc' := probTendsToOne_of_ae (P := S.P) (G := {ω | Continuous (S.η ω)})
      (by filter_upwards [hS.isAreaParametrized] with ω hω using hω.1)
    have hE := probTendsToOne_inter (probTendsToOne_inter (probTendsToOne_inter
      (probTendsToOne_inter hE9 h28') hadj') hab') hc'
    refine tendsto_outerLIntegral_of_eventually_le S.P _ (fun ε ω => ?_) dd hddm' hddpos _ hE
      (fun τ hτ => ?_)
    · exact iSup_le fun Θ => iSup_le fun _ => iSup_le fun _ => iSup_le fun δ₀ => iSup_le fun _ =>
        iSup_le fun _ => iSup_le fun j => iSup_le fun _ => iSup_le fun a => iSup_le fun _ => prob_le_one
    · obtain ⟨θ, hθ, hev⟩ := hq τ hτ
      refine ⟨θ, hθ, ?_⟩
      filter_upwards [hev, self_mem_nhdsWithin] with ε hε hεpos ω hω hτω
      obtain ⟨⟨⟨⟨h9, h28ω⟩, hadjω⟩, habω⟩, hcω⟩ := hω
      refine iSup_le fun Θ => iSup_le fun hΘ1 => iSup_le fun hΘ2 => iSup_le fun δ₀ => iSup_le fun hδ₀ =>
        iSup_le fun hδ₀' => iSup_le fun j => iSup_le fun hj => iSup_le fun a => iSup_le fun ha => ?_
      simp only [one_mul]
      exact hε (S.mult ε ω) (S.η ω) (dd ω) hτω hcω (habω ε hεpos) (hsrw _) h9 hadjω
        (fun b hb => (h28ω b hb).2) Θ hΘ1 hΘ2 δ₀ hδ₀ (hδ₀'.trans_le (min_le_left _ _))
        (hδ₀'.trans_le (min_le_right _ _)) j hj a ha

/-- **Lemma 6.10** from the drafted Lemma 6.9 (which implies its E-A10 (b) form) and the other steps. -/
theorem iterativeBound_of_steps' (𝒮 : SpaceFillingSLEModel) (h69 : ChanceOfBeingAbsorbedStmt 𝒮)
    (h63 : AbelianIDLAAnyStartStep 𝒮) (h28 : CellSizeEstimateStmt 𝒮) (hadj : AdjacentCellsMeetStep 𝒮)
    (hsrw : SrwPathStep) (henv : FieldSigmaMeasurableStep 𝒮) (hq : QuenchedIterationStep) :
    IterativeBoundStmt 𝒮 :=
  iterativeBound_of_steps 𝒮 h69.logLoss h63 h28 hadj hsrw henv hq

end MatedCRT
