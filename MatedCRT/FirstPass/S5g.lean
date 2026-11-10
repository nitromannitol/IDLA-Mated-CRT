import MatedCRT.FirstPass.S5d.StoppedSteps
import MatedCRT.FirstPass.S5d.CoverEvent
import MatedCRT.FirstPass.S4S6c.EnvInputs68
import MatedCRT.Proofs.Sec5.LLowerBound.Mass
import MatedCRT.Proofs.Measurability.EnvSigmaCore

/-!
# Uniform positive mass of the stopped targets (Proposition 5.1, correction [C21]; fp-S5g, z8)

Written source: `paper/idla_mated_crt-corrected.tex`, proof of Proposition 5.1, lines 2368-2372 (`% CORRECTION [C21]`):
"The full support of `μ_h` and a finite cover of the possible centers give a uniform positive random lower bound for the
masses of these smaller balls." Referee check: `notes/fp-gaps/CHATGPT-idla-C20-C21-referee.md`.

`stoppedTargetMass_tendsToOne` is the uniform mass bound of the stopped clause: there is a positive `envSigma`-measurable
random level `mr` such that, with probability tending to one on `{t < T_ρ}` (the cluster exit time), `ε^{1/4} ≤ mr` and every
target centre `η(εa)`, `a ∈ V^ε(B⁻_δ(Λ_t))`, has `μ_h`-mass at least `mr` in the ball of radius `s`.

Route:
* On `{t < T_ρ}` the cluster lies in `B_{ρ/3}` (`subset_ball_of_lt_clusterExitTime`), so every target cell meets `B_ρ`.
* The cell-size estimate (Lemma 2.8, `CellSizeEstimateStmt`, hypothesis `h28`) bounds the diameter of such cells by `1`
  (for `ε < 1`), and a target centre `η(εa)` is an endpoint of its cell, so it lies in the closed ball of radius `ρ + 1`.
* A finite net `Z` of mesh `s/2` covers that closed ball; every centre `z` of the net gives `B_{s/2}(z) ⊆ B_s(η(εa))`.
* `mr := min_{z ∈ Z} massFloor(μ_h(B_{s/2}(z)))`, with `massFloor x = min(x, 1)` and value `1` at `x = 0`, so `mr > 0`
  everywhere. The masses `μ_h(B_{s/2}(z))` are positive almost surely because `η` is area-parametrized, which gives full
  support (`open_pos_of_area_parametrized`); the identification with a field-measurable version of `μ_h` is
  `EnvInputs68.exists_fieldMeasurable_mu`.
* `P(mr < ε^{1/4}) → 0` since `mr > 0`, by continuity from above of the measure along `ε ↓ 0`.

Inputs: the Draft statement `CellSizeEstimateStmt 𝒮` (Lemma 2.8) is a hypothesis; no other external fact is used.
-/

namespace MatedCRT

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal NNReal

namespace StoppedTargetMass

/-- The floored ball mass `massFloor x = min (x, 1)` as a real number, with the value `1` at the null mass `x = 0`. It is
positive for every `x` (`massFloor_pos`) and at most `x` when `x ≠ 0` (`ofReal_massFloor_le`). -/
noncomputable def massFloor (x : ℝ≥0∞) : ℝ :=
  if x = 0 then 1 else (min x 1).toReal

lemma massFloor_pos (x : ℝ≥0∞) : 0 < massFloor x := by
  unfold massFloor
  split_ifs with hx
  · exact one_pos
  · exact ENNReal.toReal_pos (lt_min (pos_iff_ne_zero.2 hx) zero_lt_one).ne'
      (ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _))

lemma ofReal_massFloor_le {x : ℝ≥0∞} (hx : x ≠ 0) : ENNReal.ofReal (massFloor x) ≤ x := by
  have h : massFloor x = (min x 1).toReal := by
    unfold massFloor
    simp [hx]
  rw [h, ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _))]
  exact min_le_left _ _

lemma measurable_massFloor : Measurable massFloor := by
  unfold massFloor
  exact Measurable.ite (measurableSet_singleton (0 : ℝ≥0∞)) measurable_const
    (measurable_id.min measurable_const).ennreal_toReal

/-- The random level of the stopped clause: the minimum over a finite net `Z` of the floored masses `massFloor (g ω (B_r(z)))`
of the balls of radius `r` about the net points. -/
noncomputable def netMassFloor {Ω : Type} (g : Ω → Measure ℂ) {Z : Finset ℂ} (hZ : Z.Nonempty) (r : ℝ) (ω : Ω) : ℝ :=
  Z.inf' hZ fun z => massFloor (g ω (ball z r))

lemma netMassFloor_pos {Ω : Type} (g : Ω → Measure ℂ) {Z : Finset ℂ} (hZ : Z.Nonempty) (r : ℝ) (ω : Ω) :
    0 < netMassFloor g hZ r ω :=
  (Finset.lt_inf'_iff hZ).2 fun _ _ => massFloor_pos _

lemma netMassFloor_le {Ω : Type} (g : Ω → Measure ℂ) {Z : Finset ℂ} (hZ : Z.Nonempty) (r : ℝ) (ω : Ω) {z : ℂ}
    (hz : z ∈ Z) : netMassFloor g hZ r ω ≤ massFloor (g ω (ball z r)) :=
  Finset.inf'_le _ hz

/-- A finite infimum of real functions which are measurable for `m` is measurable for `m`. -/
theorem measurable_finset_inf'_real {Ω ι : Type} [DecidableEq ι] {m : MeasurableSpace Ω} (f : ι → Ω → ℝ)
    (hf : ∀ i, Measurable[m] (f i)) (s : Finset ι) (hs : s.Nonempty) :
    Measurable[m] fun ω => s.inf' hs fun i => f i ω := by
  induction s using Finset.induction_on with
  | empty => exact absurd hs Finset.not_nonempty_empty
  | @insert a s ha ih =>
    rcases s.eq_empty_or_nonempty with rfl | hs'
    · simpa using hf a
    · have h := ih hs'
      have e : (fun ω => (insert a s).inf' hs fun i => f i ω) =
          fun ω : Ω => (f a ω : ℝ) ⊓ (s.inf' hs' fun i => f i ω : ℝ) := by
        funext ω
        rw [Finset.inf'_insert]
      rw [e]
      exact (hf a).inf h

end StoppedTargetMass

open StoppedTargetMass

theorem stoppedTargetMass_tendsToOne (𝒮 : SpaceFillingSLEModel) {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) {ρ : ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ) (Λ : Ω → ℝ → Set ℂ)
    (hΛ : ∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) {δ t s : ℝ} (hδ : 0 < δ) (hδρ : δ < ρ)
    (ht : 0 < t) (hs : 0 < s) (h28 : CellSizeEstimateStmt 𝒮) :
    ∃ mr : Ω → ℝ, Measurable[S.envSigma] mr ∧ (∀ ω, 0 < mr ω) ∧
      TendsToOneOn S.P {ω | t < clusterExitTime (Λ ω) ρ} fun ε => {ω | ε ^ (1 / 4 : ℝ) ≤ mr ω ∧
        ∀ a ∈ stoppedTargetSet S Λ δ t ε ω, ENNReal.ofReal (mr ω) ≤ S.μ ω (Metric.ball (vertexPoint ε (S.η ω) a) s)} := by
  classical
  have : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  -- a field-measurable version `g` of the LQG measure, equal to `S.μ` almost surely
  obtain ⟨g, hg, hgμ⟩ := EnvInputs68.exists_fieldMeasurable_mu hγ0 hγ2 S hS
  -- a finite net `Z` of mesh `s/2` covering the closed ball of radius `ρ + 1`
  obtain ⟨T, -, hTfin, hTcov⟩ :=
    finite_cover_balls_of_compact (isCompact_closedBall (0 : ℂ) (ρ + 1)) (half_pos hs)
  obtain ⟨Z, rfl⟩ : ∃ Z : Finset ℂ, (Z : Set ℂ) = T := ⟨hTfin.toFinset, hTfin.coe_toFinset⟩
  have hcov : ∀ y : ℂ, dist y 0 ≤ ρ + 1 → ∃ z ∈ Z, dist y z < s / 2 := by
    intro y hy
    obtain ⟨z, hzZ, hyz⟩ := mem_iUnion₂.1 (hTcov (mem_closedBall.2 hy))
    exact ⟨z, hzZ, mem_ball.1 hyz⟩
  have hZne : Z.Nonempty := by
    obtain ⟨z, hz, -⟩ := hcov 0 (by rw [dist_self]; linarith)
    exact ⟨z, hz⟩
  -- the random level is field-measurable, hence envSigma-measurable
  have hball : ∀ z : ℂ, Measurable[S.fieldSigma] fun ω => g ω (ball z (s / 2)) :=
    fun z => (Measure.measurable_coe measurableSet_ball).comp hg
  have hmr_fs : Measurable[S.fieldSigma] (netMassFloor g hZne (s / 2)) :=
    measurable_finset_inf'_real (fun z ω => massFloor (g ω (ball z (s / 2))))
      (fun z => measurable_massFloor.comp (hball z)) Z hZne
  have hmr_env : Measurable[S.envSigma] (netMassFloor g hZne (s / 2)) :=
    hmr_fs.mono (show S.fieldSigma ≤ S.envSigma from le_sup_left) le_rfl
  refine ⟨netMassFloor g hZne (s / 2), hmr_env, netMassFloor_pos g hZne (s / 2), ?_⟩
  -- almost surely: area parametrization, identification `S.μ = g`, and the cone harmonic balls
  have hgood : ∀ᵐ ω ∂S.P, IsAreaParametrized (S.μ ω) (S.η ω) ∧ S.μ ω = g ω ∧
      IsConeHarmonicBallFamily (S.μ ω) (Λ ω) := by
    filter_upwards [hS.isAreaParametrized, hgμ, hΛ] with ω h1 h2 h3
    exact ⟨h1, h2, h3⟩
  -- the cell-size estimate (Lemma 2.8) at the exponent `ζ = 1/(2+γ)²`, for which the upper exponent is `ζ > 0`
  have hζ0 : (0 : ℝ) < 1 / (2 + γ) ^ 2 := by positivity
  have hζ1 : 1 / (2 + γ) ^ 2 < 1 := by
    rw [div_lt_one (by positivity)]
    nlinarith
  have hexp : (0 : ℝ) < 2 / (2 + γ) ^ 2 - 1 / (2 + γ) ^ 2 := by
    rw [show (2 : ℝ) / (2 + γ) ^ 2 - 1 / (2 + γ) ^ 2 = 1 / (2 + γ) ^ 2 by ring]
    exact hζ0
  obtain ⟨p, hp, C, r₀, hr₀, hcell⟩ := h28 γ hγ0 hγ2 (1 / (2 + γ) ^ 2) ρ hζ0 hζ1 hρ0 hρ1 Ω S hS
  -- the size event fails with probability tending to zero
  have hB : Tendsto (fun ε : ℝ => S.P (cellSizeEvent S γ (1 / (2 + γ) ^ 2) ρ ε)ᶜ) (𝓝[>] 0) (𝓝 0) := by
    have hc : Tendsto (fun ε : ℝ => ε ^ p) (𝓝 0) (𝓝 ((0 : ℝ) ^ p)) :=
      (Real.continuousAt_rpow_const 0 p (Or.inr hp.le)).tendsto
    rw [Real.zero_rpow hp.ne'] at hc
    have hrp : Tendsto (fun ε : ℝ => ε ^ p) (𝓝[>] 0) (𝓝 0) := hc.mono_left nhdsWithin_le_nhds
    have hcC : Tendsto (fun ε : ℝ => C * ε ^ p) (𝓝[>] 0) (𝓝 0) := by
      simpa using (tendsto_const_nhds (x := C)).mul hrp
    have hupperB : Tendsto (fun ε : ℝ => ENNReal.ofReal (C * ε ^ p)) (𝓝[>] 0) (𝓝 0) := by
      simpa using ENNReal.tendsto_ofReal hcC
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupperB
      (Eventually.of_forall fun _ => zero_le) ?_
    filter_upwards [Ioo_mem_nhdsGT hr₀] with ε hε
    exact hcell ε hε.1 hε.2
  -- the random level is below `ε^{1/4}` with probability tending to zero (it is positive everywhere)
  have hA : Tendsto (fun ε : ℝ => S.P {ω | netMassFloor g hZne (s / 2) ω < ε ^ (1 / 4 : ℝ)}) (𝓝[>] 0) (𝓝 0) := by
    have hempty : (⋂ r > (0 : ℝ), {ω | netMassFloor g hZne (s / 2) ω < r}) = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.2 fun ω hω => ?_
      have h := mem_iInter₂.1 hω (netMassFloor g hZne (s / 2) ω / 2)
        (by linarith [netMassFloor_pos g hZne (s / 2) ω])
      have h' : netMassFloor g hZne (s / 2) ω < netMassFloor g hZne (s / 2) ω / 2 := h
      linarith [netMassFloor_pos g hZne (s / 2) ω]
    have hlim : Tendsto (S.P ∘ fun r : ℝ => {ω | netMassFloor g hZne (s / 2) ω < r}) (𝓝[>] 0)
        (𝓝 (S.P (⋂ r > (0 : ℝ), {ω | netMassFloor g hZne (s / 2) ω < r}))) :=
      tendsto_measure_biInter_gt
        (fun r _ => hS.nullMeasurableSet_of_envSigma (measurableSet_lt hmr_env measurable_const))
        (fun i j _ hij ω hω => lt_of_lt_of_le hω hij)
        ⟨1, one_pos, measure_ne_top _ _⟩
    rw [hempty, measure_empty] at hlim
    have hpow : Tendsto (fun ε : ℝ => ε ^ (1 / 4 : ℝ)) (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have hc : Tendsto (fun ε : ℝ => ε ^ (1 / 4 : ℝ)) (𝓝 0) (𝓝 ((0 : ℝ) ^ (1 / 4 : ℝ))) :=
          (Real.continuousAt_rpow_const 0 _ (Or.inr (by norm_num))).tendsto
        rw [Real.zero_rpow (by norm_num)] at hc
        exact hc.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with ε hε
        exact Real.rpow_pos_of_pos hε _
    exact hlim.comp hpow
  -- pointwise step: on the good event, every target centre has mass at least the net floor in its ball of radius `s`
  have key : ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ ω : Ω, t < clusterExitTime (Λ ω) ρ →
      IsAreaParametrized (S.μ ω) (S.η ω) → S.μ ω = g ω → IsConeHarmonicBallFamily (S.μ ω) (Λ ω) →
      ω ∈ cellSizeEvent S γ (1 / (2 + γ) ^ 2) ρ ε → ∀ a ∈ stoppedTargetSet S Λ δ t ε ω,
        ENNReal.ofReal (netMassFloor g hZne (s / 2) ω) ≤ S.μ ω (Metric.ball (vertexPoint ε (S.η ω) a) s) := by
    intro ε hε0 hε1 ω hF hAP hμg hΛω hC a ha
    have := open_pos_of_area_parametrized hAP
    have hmono : MonotoneOn (Λ ω) (Ioi 0) := fun a ha b hb hab => hΛω.2.1.monotoneOn ha hb hab
    have hsub : Λ ω t ⊆ ball 0 ρ := subset_ball_of_lt_clusterExitTime hρ0 hmono ht hF
    obtain ⟨x, hxcell, hxin⟩ : (cell ε (S.η ω) a ∩ innerNbhd δ (Λ ω t)).Nonempty := ha
    have hxB : x ∈ ball (0 : ℂ) ρ := hsub hxin.1
    unfold cellSizeEvent at hC
    have hC' := hC a
    obtain ⟨hlow, hup⟩ := hC' ⟨x, hxcell, hxB⟩
    have hpos : 0 < diam (cell ε (S.η ω) a) := lt_of_lt_of_le (Real.rpow_pos_of_pos hε0 _) hlow
    have hbdd : Bornology.IsBounded (cell ε (S.η ω) a) := by
      by_contra hb
      have := Metric.diam_eq_zero_of_unbounded hb
      linarith
    have hdiam : diam (cell ε (S.η ω) a) ≤ 1 :=
      hup.trans (Real.rpow_le_one hε0.le hε1.le hexp.le)
    have hvert : S.η ω (ε * (a : ℝ)) ∈ cell ε (S.η ω) a := by
      unfold cell
      exact ⟨ε * (a : ℝ), ⟨mul_le_mul_of_nonneg_left (by linarith) hε0.le, le_rfl⟩, rfl⟩
    have hdist : dist (S.η ω (ε * (a : ℝ))) x ≤ 1 :=
      (dist_le_diam_of_mem hbdd hvert hxcell).trans hdiam
    obtain ⟨z, hzZ, hzd⟩ := hcov (S.η ω (ε * (a : ℝ)))
      (by linarith [dist_triangle (S.η ω (ε * (a : ℝ))) x 0, mem_ball.1 hxB])
    have hsmall : ball z (s / 2) ⊆ ball (S.η ω (ε * (a : ℝ))) s := by
      intro y hy
      rw [mem_ball] at hy ⊢
      linarith [dist_triangle y z (S.η ω (ε * (a : ℝ))), dist_comm z (S.η ω (ε * (a : ℝ)))]
    have hgpos : g ω (ball z (s / 2)) ≠ 0 := by
      rw [← hμg]
      exact (measure_ball_pos (S.μ ω) z (half_pos hs)).ne'
    calc ENNReal.ofReal (netMassFloor g hZne (s / 2) ω)
        ≤ ENNReal.ofReal (massFloor (g ω (ball z (s / 2)))) :=
          ENNReal.ofReal_le_ofReal (netMassFloor_le g hZne (s / 2) ω hzZ)
      _ ≤ g ω (ball z (s / 2)) := ofReal_massFloor_le hgpos
      _ = S.μ ω (ball z (s / 2)) := by rw [hμg]
      _ ≤ S.μ ω (ball (S.η ω (ε * (a : ℝ))) s) := measure_mono hsmall
  -- the exceptional events, with the good event, cover the failure event
  have hincl : ∀ ε : ℝ, 0 < ε → ε < 1 →
      ({ω | t < clusterExitTime (Λ ω) ρ} ∩
        {ω | ε ^ (1 / 4 : ℝ) ≤ netMassFloor g hZne (s / 2) ω ∧
          ∀ a ∈ stoppedTargetSet S Λ δ t ε ω,
            ENNReal.ofReal (netMassFloor g hZne (s / 2) ω) ≤ S.μ ω (Metric.ball (vertexPoint ε (S.η ω) a) s)}ᶜ) ⊆
      (({ω | ¬ (IsAreaParametrized (S.μ ω) (S.η ω) ∧ S.μ ω = g ω ∧ IsConeHarmonicBallFamily (S.μ ω) (Λ ω))} ∪
        {ω | netMassFloor g hZne (s / 2) ω < ε ^ (1 / 4 : ℝ)}) ∪ (cellSizeEvent S γ (1 / (2 + γ) ^ 2) ρ ε)ᶜ) := by
    rintro ε hε0 hε1 ω ⟨hF, hE⟩
    by_cases hG : IsAreaParametrized (S.μ ω) (S.η ω) ∧ S.μ ω = g ω ∧ IsConeHarmonicBallFamily (S.μ ω) (Λ ω)
    · by_cases hA' : netMassFloor g hZne (s / 2) ω < ε ^ (1 / 4 : ℝ)
      · exact Or.inl (Or.inr hA')
      · by_cases hC : ω ∈ cellSizeEvent S γ (1 / (2 + γ) ^ 2) ρ ε
        · have hP : ε ^ (1 / 4 : ℝ) ≤ netMassFloor g hZne (s / 2) ω ∧
              ∀ a ∈ stoppedTargetSet S Λ δ t ε ω,
                ENNReal.ofReal (netMassFloor g hZne (s / 2) ω) ≤ S.μ ω (Metric.ball (vertexPoint ε (S.η ω) a) s) :=
            ⟨not_lt.1 hA', fun a ha => key ε hε0 hε1 ω hF hG.1 hG.2.1 hG.2.2 hC a ha⟩
          exact (hE hP).elim
        · exact Or.inr hC
    · exact Or.inl (Or.inl hG)
  have hbad : S.P {ω | ¬ (IsAreaParametrized (S.μ ω) (S.η ω) ∧ S.μ ω = g ω ∧
      IsConeHarmonicBallFamily (S.μ ω) (Λ ω))} = 0 :=
    ae_iff.1 hgood
  unfold TendsToOneOn
  have h0 : Tendsto (fun _ : ℝ => S.P {ω | ¬ (IsAreaParametrized (S.μ ω) (S.η ω) ∧ S.μ ω = g ω ∧
      IsConeHarmonicBallFamily (S.μ ω) (Λ ω))}) (𝓝[>] 0) (𝓝 0) := by
    rw [hbad]
    exact tendsto_const_nhds
  have hup := (h0.add hA).add hB
  rw [add_zero, add_zero] at hup
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [Ioo_mem_nhdsGT one_pos] with ε hε
  refine (measure_mono (hincl ε hε.1 hε.2)).trans ?_
  refine (measure_union_le _ _).trans ?_
  gcongr
  exact measure_union_le _ _

end MatedCRT
