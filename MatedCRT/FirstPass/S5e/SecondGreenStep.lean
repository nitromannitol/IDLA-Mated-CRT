import MatedCRT.FirstPass.S5e.SecondGreenDet
import MatedCRT.FirstPass.S5d.StoppedPathwise
import MatedCRT.FirstPass.S5c.BadEvents
import MatedCRT.Draft.Section2

/-!
# The stopped second Green inequality from its probabilistic inputs (FIRST PASS, S5e)

Reduces `StoppedSecondGreenStep` (FirstPass/S5d/StoppedSteps.lean:73, the second Green inequality (5.7) of the stopped
clause, correction [C21]) to two NEW probabilistic inputs, `StoppedFloorHalfStep` and `StoppedMassLowerStep`, and to the
Draft statements 2.8 (`CellSizeEstimateStmt`), 2.15 (`GreenFunctionCrudeBoundStmt`) and 2.16
(`GreenKernelLowerBoundStmt`), together with the pathwise inputs `stoppedPathwiseInputs_ae`. The deterministic argument
is `MatedCRT.S5e.secondGreen_pointwise` (SecondGreenDet.lean).

Probabilistic bookkeeping: `TendsToOneOn` is closed under finite intersections, polynomially high events are
`TendsToOneOn`, almost sure events are `TendsToOneOn`, and the mass event `{ε^{1/4} ≤ mr}` is `TendsToOneOn` by
continuity of measure along `ε ↓ 0` (`tendsto_measure_biInter_gt`) since `mr > 0` almost surely.
-/

open MeasureTheory Set Metric Filter Topology

namespace MatedCRT.S5e

/-- **NEW, OPEN (probabilistic input; correction [C21], tex 2355-2362: "a positive random `c` such that
`u^ε(a) ≥ c ε^{-1}` for every cell meeting `B⁻_{δ/2}(Λ_t)`").** For `δ ∈ (0, ρ)` and `t > 0`, on `{t < T}`, with
probability tending to `1` as `ε → 0⁺`, every cell meeting `B⁻_{δ/2}(Λ_t)` has positive stopped odometer. This is the
floor of the first Green step (`StoppedFirstGreenInputsStep`, StoppedFirstGreenInputs.lean) at level `δ/2` on the cells
(not only on the targets), weakened to positivity. -/
def StoppedFloorHalfStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) →
  ∀ δ t : ℝ, 0 < δ → δ < ρ → 0 < t →
    TendsToOneOn S.P {ω | t < clusterExitTime (Λ ω) ρ} fun ε => {ω | ∀ k : ℤ,
      (cell ε (S.η ω) k ∩ innerNbhd (δ / 2) (Λ ω t)).Nonempty →
        0 < stoppedOdometer (S.mult ε ω) ε (S.η ω) ρ t k}

/-- **NEW, OPEN (probabilistic input; correction [C21], tex 2368-2372: "the full support of `μ_h` and a finite cover of
the possible centers give a uniform positive random lower bound for the masses of these smaller balls").** For `ρ, s > 0`
there is a measurable random `mr > 0` with `μ_h(B_s(z)) ≥ mr` for every `z ∈ B̄_ρ`, almost surely. For each outcome the
bound is deterministic (`MatedCRT.S5c.mass_net_lower_bound` from `IsAreaParametrized`); the measurable choice of `mr` is
the open part. -/
def StoppedMassLowerStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ s : ℝ, 0 < s → ∃ mr : Ω → ℝ, Measurable mr ∧ (∀ᵐ ω ∂S.P, 0 < mr ω) ∧
    ∀ᵐ ω ∂S.P, ∀ z ∈ closedBall (0 : ℂ) ρ, ENNReal.ofReal (mr ω) ≤ S.μ ω (ball z s)

section Probability

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}

/-- Finite intersections of `TendsToOneOn` events are `TendsToOneOn`. -/
lemma tendsToOneOn_inter {F : Set Ω} {E₁ E₂ : ℝ → Set Ω} (h₁ : TendsToOneOn P F E₁)
    (h₂ : TendsToOneOn P F E₂) : TendsToOneOn P F (fun ε => E₁ ε ∩ E₂ ε) := by
  unfold TendsToOneOn at *
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (by simpa only [add_zero] using h₁.add h₂) (Eventually.of_forall fun ε => zero_le)
    (Eventually.of_forall fun ε => ?_)
  calc P (F ∩ (E₁ ε ∩ E₂ ε)ᶜ) ≤ P ((F ∩ (E₁ ε)ᶜ) ∪ (F ∩ (E₂ ε)ᶜ)) := by
        apply measure_mono
        intro ω hω
        by_cases h : ω ∈ E₁ ε
        · exact Or.inr ⟨hω.1, fun h2 => hω.2 ⟨h, h2⟩⟩
        · exact Or.inl ⟨hω.1, h⟩
    _ ≤ P (F ∩ (E₁ ε)ᶜ) + P (F ∩ (E₂ ε)ᶜ) := measure_union_le _ _

/-- A polynomially high probability event is a `TendsToOneOn` event. -/
lemma tendsToOneOn_of_polyHighProb [IsFiniteMeasure P] (F : Set Ω) {E : ℝ → Set Ω}
    (h : HarmonicBalls.PolyHighProb P E) : TendsToOneOn P F E := by
  unfold TendsToOneOn
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (MatedCRT.S5c.tendsto_compl_of_polyHighProb h)
    (Eventually.of_forall fun ε => zero_le) (Eventually.of_forall fun ε => measure_mono Set.inter_subset_right)

/-- An almost sure event (for all `ε`) is a `TendsToOneOn` event. -/
lemma tendsToOneOn_of_ae (F : Set Ω) {E : ℝ → Set Ω} (h : ∀ᵐ ω ∂P, ∀ ε : ℝ, ω ∈ E ε) :
    TendsToOneOn P F E := by
  unfold TendsToOneOn
  have h0 : ∀ ε : ℝ, P (F ∩ (E ε)ᶜ) = 0 := fun ε => by
    have hsub : F ∩ (E ε)ᶜ ⊆ {ω | ¬ ∀ ε' : ℝ, ω ∈ E ε'} := fun ω hω hall => hω.2 (hall ε)
    exact measure_mono_null hsub (ae_iff.1 h)
  have hfun : (fun ε : ℝ => P (F ∩ (E ε)ᶜ)) = fun _ => 0 := funext h0
  rw [hfun]
  exact tendsto_const_nhds

/-- Passing to a larger event on a neighbourhood of `0⁺`. -/
lemma tendsToOneOn_of_eventually {F : Set Ω} {E G : ℝ → Set Ω} (hG : TendsToOneOn P F G)
    (h : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ ω ∈ F, ω ∈ G ε → ω ∈ E ε) : TendsToOneOn P F E := by
  unfold TendsToOneOn at *
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hG
    (Eventually.of_forall fun ε => zero_le) ?_
  filter_upwards [h] with ε hε
  have hsub : F ∩ (E ε)ᶜ ⊆ F ∩ (G ε)ᶜ := by
    intro ω hω
    have h2 : ω ∉ E ε := hω.2
    exact ⟨hω.1, fun hωG => h2 (hε ω hω.1 hωG)⟩
  exact measure_mono hsub

/-- A power of `ε` tends to `0` at `0⁺`: eventually below any positive constant. -/
lemma eventually_rpow_lt {p c : ℝ} (hp : 0 < p) (hc : 0 < c) : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ^ p < c := by
  have h : Tendsto (fun ε : ℝ => ε ^ p) (𝓝[>] (0 : ℝ)) (𝓝 ((0 : ℝ) ^ p)) :=
    ((Real.continuous_rpow_const hp.le).tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  rw [Real.zero_rpow hp.ne'] at h
  exact h.eventually (gt_mem_nhds hc)

/-- Eventually below any positive constant, on `(0, ∞)`. -/
lemma eventually_lt_nhdsWithin_zero {c : ℝ} (hc : 0 < c) : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < c :=
  eventually_nhdsWithin_of_eventually_nhds (gt_mem_nhds hc)

/-- The mass event `{ε^{1/4} ≤ mr}` is a `TendsToOneOn` event when `mr` is measurable and positive almost surely:
`P(mr < ε^{1/4}) → P(mr ≤ 0) = 0` by continuity of measure. -/
lemma tendsToOneOn_of_mass [IsProbabilityMeasure P] (F : Set Ω) {mr : Ω → ℝ} (hmr : Measurable mr)
    (hpos : ∀ᵐ ω ∂P, 0 < mr ω) :
    TendsToOneOn P F (fun ε : ℝ => {ω | ε ^ (1 / 4 : ℝ) ≤ mr ω}) := by
  unfold TendsToOneOn
  have hlim : Tendsto (fun ε : ℝ => P {ω | mr ω < ε ^ (1 / 4 : ℝ)}) (𝓝[Ioi 0] 0)
      (𝓝 (P (⋂ r > (0 : ℝ), {ω | mr ω < r ^ (1 / 4 : ℝ)}))) := by
    refine tendsto_measure_biInter_gt (fun r _ => ?_) (fun i j hi hij ω hω => ?_)
      ⟨1, one_pos, measure_ne_top _ _⟩
    · exact (measurableSet_lt hmr measurable_const).nullMeasurableSet
    · exact lt_of_lt_of_le hω (Real.rpow_le_rpow (le_of_lt hi) hij (by norm_num))
  have hnull : P (⋂ r > (0 : ℝ), {ω | mr ω < r ^ (1 / 4 : ℝ)}) = 0 := by
    apply measure_mono_null _ (ae_iff.1 hpos)
    intro ω hω hpos'
    have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), r ^ (1 / 4 : ℝ) < mr ω := eventually_rpow_lt (by norm_num) hpos'
    obtain ⟨r, hr', hrpos⟩ := (hev.and self_mem_nhdsWithin).exists
    have hωr : mr ω < r ^ (1 / 4 : ℝ) := mem_iInter₂.1 hω r hrpos
    linarith
  rw [hnull] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun ε => zero_le) (Eventually.of_forall fun ε => measure_mono ?_)
  intro ω hω
  have h2 : ¬ (ε ^ (1 / 4 : ℝ) ≤ mr ω) := hω.2
  exact not_le.1 h2

end Probability

/-- **The stopped second Green inequality from its probabilistic inputs** (correction [C21]; referee §5.3). The Draft
events 2.8, 2.15, 2.16 give the diameter, crude-diagonal and kernel-lower-bound events; `StoppedFloorHalfStep` gives the
floor on `B⁻_{δ/2}(Λ_t)`; `StoppedMassLowerStep` gives the measurable mass bound `mr`; the pathwise inputs of the
stopped clause hold almost surely (`stoppedPathwiseInputs_ae`). -/
theorem stoppedSecondGreenStep_of_inputs (𝒮 : SpaceFillingSLEModel)
    (hcell : AdjacentCellsMeetAeStep 𝒮) (hlap : DiscreteLaplacianBoundCorrectedStmt 𝒮)
    (hG15 : GreenFunctionCrudeBoundStmt 𝒮) (hG16 : GreenKernelLowerBoundStmt 𝒮)
    (hD8 : CellSizeEstimateStmt 𝒮) (hfloor : StoppedFloorHalfStep 𝒮) (hmass : StoppedMassLowerStep 𝒮) :
    StoppedSecondGreenStep 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS Λ hΛ δ t hδ hδρ ht
  have : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  obtain ⟨ω₀, hω₀, hG16₁⟩ := hG16 γ hγ hγ2
  obtain ⟨C, hC, hG16₂⟩ := hG16₁ ρ hρ hρ1
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℝ, ζ = 1 / (2 + γ) ^ 2 := ⟨_, rfl⟩
  have h2γ : (1 : ℝ) < (2 + γ) ^ 2 := by nlinarith
  have hζ0 : 0 < ζ := by rw [hζ]; positivity
  have hζ1 : ζ < 1 := by rw [hζ, div_lt_one (by positivity)]; exact h2γ
  have he : 0 < 2 / (2 + γ) ^ 2 - ζ := by
    rw [hζ, show (2 : ℝ) / (2 + γ) ^ 2 - 1 / (2 + γ) ^ 2 = 1 / (2 + γ) ^ 2 by ring]
    positivity
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = δ / 4 := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = r * Real.exp (-(2 * C)) / 6 := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [hr]; linarith
  have hexp0 : 0 < Real.exp (-(2 * C)) := Real.exp_pos _
  have hs0 : 0 < s := by rw [hs]; exact div_pos (mul_pos hr0 hexp0) (by norm_num)
  have hD8S := hD8 γ hγ hγ2 ζ ρ hζ0 hζ1 hρ hρ1 Ω S hS
  have hG15S := hG15 γ hγ hγ2 ρ (1 / 2) hρ hρ1 (by norm_num) (by norm_num) Ω S hS
  have hG16S := hG16₂ Ω S hS
  obtain ⟨mr, hmrM, hmrpos, hmrball⟩ := hmass γ hγ hγ2 ρ hρ hρ1 Ω S hS s hs0
  have hpath := stoppedPathwiseInputs_ae 𝒮 hcell hlap γ hγ hγ2 ρ hρ hρ1 Ω S hS Λ hΛ t ht
  have hap0 : ∀ᵐ ω ∂S.P, IsAreaParametrized (S.μ ω) (S.η ω) ∧ MonotoneOn (Λ ω) (Ioi 0) :=
    hS.isAreaParametrized.and (hΛ.mono fun ω h => h.2.1.monotoneOn)
  have hfl := hfloor γ hγ hγ2 ρ hρ hρ1 Ω S hS Λ hΛ δ t hδ hδρ ht
  set F : Set Ω := {ω | t < clusterExitTime (Λ ω) ρ} with hF
  have hT15 := tendsToOneOn_of_polyHighProb (P := S.P) F hG15S
  have hT16 := tendsToOneOn_of_polyHighProb (P := S.P) F hG16S
  have hT8 := tendsToOneOn_of_polyHighProb (P := S.P) F hD8S
  have hTpath : TendsToOneOn S.P F (fun _ : ℝ => {ω | ∀ ε : ℝ, 0 < ε →
      StoppedPathwiseInputs S Λ ρ t ε ω}) :=
    tendsToOneOn_of_ae F (hpath.mono fun ω h _ => h)
  have hTmb : TendsToOneOn S.P F (fun _ : ℝ => {ω | ∀ z ∈ closedBall (0 : ℂ) ρ,
      ENNReal.ofReal (mr ω) ≤ S.μ ω (ball z s)}) :=
    tendsToOneOn_of_ae F (hmrball.mono fun ω h _ => h)
  have hTmr := tendsToOneOn_of_mass (P := S.P) F hmrM hmrpos
  have hT0 : TendsToOneOn S.P F (fun _ : ℝ => {ω | IsAreaParametrized (S.μ ω) (S.η ω) ∧
      MonotoneOn (Λ ω) (Ioi 0)}) :=
    tendsToOneOn_of_ae F (hap0.mono fun ω h _ => h)
  have hgood := tendsToOneOn_inter (tendsToOneOn_inter (tendsToOneOn_inter (tendsToOneOn_inter
    (tendsToOneOn_inter (tendsToOneOn_inter (tendsToOneOn_inter hfl hT15) hT16) hT8) hTpath) hTmb) hTmr) hT0
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < Real.exp (-(2 * C)) ∧ ε ^ ω₀ < r ∧
      ε ^ (2 / (2 + γ) ^ 2 - ζ) < s :=
    (eventually_lt_nhdsWithin_zero hexp0).and
      ((eventually_rpow_lt hω₀ hr0).and (eventually_rpow_lt he hs0))
  refine tendsToOneOn_of_eventually hgood ?_
  filter_upwards [hev, self_mem_nhdsWithin] with ε hε hεpos
  intro ω hωF hωG
  obtain ⟨⟨⟨⟨⟨⟨⟨hωfl, hω15⟩, hω16⟩, hω8⟩, hωpath⟩, hωmb⟩, hωmr⟩, hωap⟩ := hωG
  have hεpos' : 0 < ε := hεpos
  have hbd : ∀ k : ℤ, Bornology.IsBounded (cell ε (S.η ω) k) := fun k =>
    (isCompact_Icc.image hωap.1.1).isBounded
  have hdiamω : ∀ k : ℤ, (cell ε (S.η ω) k ∩ ball 0 ρ).Nonempty →
      ∀ x ∈ cell ε (S.η ω) k, ∀ y ∈ cell ε (S.η ω) k, dist x y ≤ s := fun k hk x hx y hy =>
    (dist_le_diam_of_mem (hbd k) hx hy).trans ((hω8 k hk).2.trans hε.2.2.le)
  exact secondGreen_pointwise S Λ ω hωap.1 (hωpath ε hεpos') hωap.2 hδ hδρ hρ ht hωF hεpos' hC
    hε.1.le hr hs hε.2.1.le hωfl hdiamω hω15
    (fun a ha r' h1 h2 b hb => (hω16 a ha r' h1 h2 b hb).2) hωmb hωmr

end MatedCRT.S5e
