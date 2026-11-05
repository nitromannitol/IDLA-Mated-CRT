import MatedCRT.Steps.Sec5.GeneralIDLALowerBound
import MatedCRT.Steps.Sec4.DivSandpileLowerBound
import MatedCRT.Proofs.Sec5.IDLALowerBound.Geometry

/-!
# Proposition 5.1: carving into steps (proof at lines 2030-2048)

The printed proof applies Lemma 5.2 with `O₁^ε = {a ∈ Λ^ε_t : dist(η(a), ∂Λ̄^ε_t) > δ/4}`, `O₂^ε = Λ^ε_t` and
`K_ε = t ε⁻¹`, the two conditions coming from Lemmas 5.3 and 5.4 (with `δ/4`), then passes from `O₁^ε` to `B⁻_δ(Λ_t)`
with the cell-size estimates (Lemma 2.8) and the inclusion `B⁻_{δ/2}(Λ_t) ⊆ Λ̄^ε_t`.

Three points of the printed proof need a different input than the one cited (reported to the lead):
1. Lemma 5.2 as stated asks that `O₁^ε, O₂^ε` be `σ(h, η)`-measurable *domains* (connected) containing the origin, for
   every `ε`, almost surely. The set `O₁^ε` of the proof need not be connected, need not contain the origin (the origin
   may lie within `δ/4` of `∂Λ̄^ε_t` when `δ` is large), and the two conditions hold only on `{t < T}`. The proof of
   Lemma 5.2 (`generalIDLALowerBound_of_steps`, MatedCRT/Steps/Sec5/GeneralIDLALowerBound.lean) uses none of these
   hypotheses: only `O₁ ⊆ O₂ ⊆ V^ε(B_ρ)`. `GeneralIDLALowerBoundRelaxedStep` is Lemma 5.2 with exactly these
   hypotheses; it is proved here from the same steps as Lemma 5.2 (`generalIDLALowerBoundRelaxed_of_steps`) and
   implies it (`generalIDLALowerBound_of_relaxed`).
2. Line 2043 derives `B⁻_{δ/2}(Λ_t) ⊆ Λ̄^ε_t` from Proposition 4.2 (`B⁻_δ(Λ_t) ⊆ D̄_ε(t ε⁻¹)`) and
   eq:cluster-and-lambdat (`D_ε(t ε⁻¹) = cl(Λ^ε_t)`). Since `Λ^ε_t ⊆ D_ε(t ε⁻¹)`, this inclusion goes the wrong way:
   the cells of the sites of `D_ε \ Λ^ε_t` are not covered. The proof of Proposition 4.2 (lines 1662-1680) shows the
   needed `Λ^ε_t` form directly; it is `DiscreteClusterInnerBoundStep`, the conclusion of
   `ObstacleClusterInnerApproximationStep` (MatedCRT/Steps/Sec4/DivSandpileLowerBound.lean).
3. The proof gives the bound for walkers stopped upon exiting `Λ^ε_t` (line 2042), while the statement (line 1981,
   used at line 2862) stops them upon exiting `V^ε(Λ_t)`. Stopping is monotone in the stopping set, but
   `Λ^ε_t ⊄ V^ε(Λ_t)` in general (the discrete cluster may overshoot `Λ_t`). The stopped claim is the named step
   `IDLALowerBoundStoppedStep`; `iDLALowerBound_discrete_of_steps` proves the version the printed proof gives.
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Topology Set Metric HarmonicBalls
open scoped ENNReal NNReal

/-! ## Steps -/

/-- **Lemma 5.2 with the hypotheses its proof uses** (lines 2148-2229): only `O₁^ε ⊆ O₂^ε ⊆ V^ε(B_ρ)` almost surely,
without the measurability of `O₁^ε, O₂^ε`, their connectedness, `0 ∈ O₁^ε` or `K_ε > 0`. -/
def GeneralIDLALowerBoundRelaxedStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ (O₁ O₂ : ℝ → Ω → Set ℤ) (K : ℝ → ℝ) (q : ℝ) (s : Ω → ℝ),
    (∀ ε, 0 < ε → ∀ᵐ ω ∂S.P, O₁ ε ω ⊆ O₂ ε ω ∧ O₂ ε ω ⊆ cellVertices ε (S.η ω) (ball 0 ρ)) →
    0 < q → Measurable[S.envSigma] s → (∀ ω, 0 < s ω) →
    ProbTendsToOne S.P (fun ε => {ω | ∀ a ∈ O₁ ε ω,
      (1 + s ω) * ∑' b : O₂ ε ω, greenFn (S.mult ε ω) (O₂ ε ω) b a ≤
        K ε * greenFn (S.mult ε ω) (O₂ ε ω) 0 a ∧
      ε ^ (-q) ≤ (∑' b : O₂ ε ω, greenFn (S.mult ε ω) (O₂ ε ω) b a) / greenFn (S.mult ε ω) (O₂ ε ω) a a}) →
    Tendsto (fun ε => S.idlaSectionProb ε {p | ¬ O₁ ε p.1 ⊆ idlaCluster p.2 ⌊K ε⌋₊}) (𝓝[>] 0) (𝓝 0) ∧
    Tendsto (fun ε => S.idlaSectionProb ε {p | ¬ O₁ ε p.1 ⊆ stoppedIDLACluster (O₂ ε p.1) p.2 ⌊K ε⌋₊})
      (𝓝[>] 0) (𝓝 0)

/-- **The discrete-cluster form of Proposition 4.2** (what its proof shows, lines 1662-1680): for `δ ∈ (0, ρ)` and
`t > 0`, on `{t < T}`, except on an event of probability tending to `0`, `B⁻_δ(Λ_t) ⊆ Λ̄^ε_t`. This is the conclusion
of `ObstacleClusterInnerApproximationStep` (`discreteClusterInnerBound_of_steps`). -/
def DiscreteClusterInnerBoundStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) →
  ∀ δ t : ℝ, 0 < δ → δ < ρ → 0 < t →
    TendsToOneOn S.P {ω | t < clusterExitTime (Λ ω) ρ} fun ε =>
      {ω | innerNbhd δ (Λ ω t) ⊆ fillCells ε (S.η ω) (matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t)}

/-- **The stopped part of Proposition 5.1** (line 1980): the lower bound holds for walkers stopped upon exiting
`V^ε(Λ_t)`. Not implied by the printed proof, which stops the walkers upon exiting `Λ^ε_t` (line 2042;
`iDLALowerBound_discrete_of_steps`). -/
def IDLALowerBoundStoppedStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) →
  ∀ δ t : ℝ, 0 < δ → δ < ρ → 0 < t →
    Tendsto (fun ε => S.idlaProb ε {p | t < clusterExitTime (Λ p.1) ρ ∧
        ¬ innerNbhd δ (Λ p.1 t) ⊆
          fillCells ε (S.η p.1) (stoppedIDLACluster (cellVertices ε (S.η p.1) (Λ p.1 t)) p.2 ⌊t / ε⌋₊)})
      (𝓝[>] 0) (𝓝 0)

/-- `DiscreteClusterInnerBoundStep` from the step `ObstacleClusterInnerApproximationStep` of Proposition 4.2 and its
inputs (Theorem 4.1, Theorem 2.3, Lemma 2.13, Lemma 3.3, Lemma 2.8). -/
theorem discreteClusterInnerBound_of_steps (𝒮 : SpaceFillingSLEModel)
    (hI : ObstacleClusterInnerApproximationStep 𝒮) (h41 : ConvergenceDivisibleStmt 𝒮)
    (h23 : ConeHarmonicBallsStmt) (h213 : MaximumPrincipleStmt 𝒮) (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮) : DiscreteClusterInnerBoundStep 𝒮 :=
  hI h41 h23 h213 h33 h28

/-! ## Lemma 5.2, relaxed -/

/-- **Lemma 5.2 (relaxed)** from the steps of Lemma 5.2: the proof of `generalIDLALowerBound_of_steps`, which uses
only `O₁ ⊆ O₂ ⊆ V^ε(B_ρ)`. -/
theorem generalIDLALowerBoundRelaxed_of_steps (𝒮 : SpaceFillingSLEModel) (hG : GreenHittingStep)
    (hQ : QuenchedSiteBoundStep) (hC : CellCountStep 𝒮) (hM : EnvSigmaMeasurableStep 𝒮) :
    GeneralIDLALowerBoundRelaxedStep 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS O₁ O₂ K q s hO hq hs hspos hgood
  have := hS.isProbabilityMeasure
  have hsm : Measurable s := hs.mono (hM γ hγ hγ2 Ω S hS) le_rfl
  set A : ℝ → Set Ω := fun ε =>
    {ω | O₁ ε ω ⊆ O₂ ε ω ∧ O₂ ε ω ⊆ cellVertices ε (S.η ω) (ball 0 ρ)} with hA
  set B : ℝ → Set Ω := fun ε => {ω | ∀ a ∈ O₁ ε ω,
      (1 + s ω) * ∑' b : O₂ ε ω, greenFn (S.mult ε ω) (O₂ ε ω) b a ≤
        K ε * greenFn (S.mult ε ω) (O₂ ε ω) 0 a ∧
      ε ^ (-q) ≤ (∑' b : O₂ ε ω, greenFn (S.mult ε ω) (O₂ ε ω) b a) /
        greenFn (S.mult ε ω) (O₂ ε ω) a a} with hB
  set C : ℝ → Set Ω := fun ε => {ω | (cellVertices ε (S.η ω) (ball 0 ρ)).Finite ∧
      ((cellVertices ε (S.η ω) (ball 0 ρ)).ncard : ℝ) ≤ ε ^ (-2 : ℝ)} with hCdef
  have hBt : Tendsto (fun ε => S.P (B ε)ᶜ) (𝓝[>] 0) (𝓝 0) := hgood
  have hCt : Tendsto (fun ε => S.P (C ε)ᶜ) (𝓝[>] 0) (𝓝 0) := hC γ hγ hγ2 ρ hρ hρ1 Ω S hS
  have hE : Tendsto (fun ε => S.P (A ε ∩ B ε ∩ C ε)ᶜ) (𝓝[>] 0) (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (by simpa using hBt.add hCt) (Eventually.of_forall fun _ => zero_le) ?_
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    have hnull : S.P (A ε)ᶜ = 0 := by
      refine measure_mono_null ?_ (ae_iff.1 (hO ε hε))
      intro ω hω
      simp only [hA, mem_compl_iff, mem_ofPred_eq] at hω
      simp only [mem_ofPred_eq]
      exact fun h => hω ⟨h.1, h.2⟩
    calc S.P (A ε ∩ B ε ∩ C ε)ᶜ = S.P ((A ε)ᶜ ∪ (B ε)ᶜ ∪ (C ε)ᶜ) := by
          rw [compl_inter, compl_inter]
      _ ≤ S.P (A ε)ᶜ + S.P (B ε)ᶜ + S.P (C ε)ᶜ :=
          (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
      _ = S.P (B ε)ᶜ + S.P (C ε)ᶜ := by rw [hnull, zero_add]
  have main : ∀ clus : ℝ → Ω → (ℕ → ℕ → ℤ) → Set ℤ,
      (∀ δ₀ : ℝ, 0 < δ₀ → ∃ c : ℝ, 0 < c ∧ ∀ ε : ℝ, 0 < ε → 2 / δ₀ ≤ ε ^ (-q) → ∀ ω ∈ B ε,
        δ₀ ≤ s ω → ∀ a ∈ O₁ ε ω, walkerSequenceLaw (S.mult ε ω) 0 {xs | a ∉ clus ε ω xs} ≤
          ENNReal.ofReal (2 * Real.exp (-(c * ε ^ (-q))))) →
      Tendsto (fun ε => S.idlaSectionProb ε {p | ¬ O₁ ε p.1 ⊆ clus ε p.1 p.2}) (𝓝[>] 0) (𝓝 0) := by
    intro clus hsite
    refine tendsto_outerLIntegral_of_eventually_le S.P
      (fun ε ω => walkerSequenceLaw (S.mult ε ω) 0 {xs | ¬ O₁ ε ω ⊆ clus ε ω xs})
      (fun ε ω => prob_le_one) s hsm hspos (fun ε => A ε ∩ B ε ∩ C ε) hE ?_
    intro δ₀ hδ₀
    obtain ⟨c, hc, hcs⟩ := hsite δ₀ hδ₀
    refine ⟨fun ε => ENNReal.ofReal (ε ^ (-2 : ℝ) * (2 * Real.exp (-(c * ε ^ (-q))))), ?_, ?_⟩
    · simpa using ENNReal.tendsto_ofReal (tendsto_card_mul_exp_bound hq hc)
    filter_upwards [self_mem_nhdsWithin,
      (tendsto_rpow_neg_nhdsGT_zero_atTop hq).eventually_ge_atTop (2 / δ₀)] with ε (hε : 0 < ε) hεq
    rintro ω ⟨⟨⟨hsub1, hsub2⟩, hωB⟩, hCfin, hCcard⟩ hsω
    have hfin : (O₁ ε ω).Finite := hCfin.subset (hsub1.trans hsub2)
    have hsite' := hcs ε hε hεq ω hωB hsω
    calc walkerSequenceLaw (S.mult ε ω) 0 {xs | ¬ O₁ ε ω ⊆ clus ε ω xs}
        ≤ walkerSequenceLaw (S.mult ε ω) 0 (⋃ a ∈ hfin.toFinset, {xs | a ∉ clus ε ω xs}) := by
          apply measure_mono
          intro xs hxs
          simp only [mem_ofPred_eq, not_subset] at hxs
          obtain ⟨a, ha, hna⟩ := hxs
          simp only [mem_iUnion]
          exact ⟨a, hfin.mem_toFinset.2 ha, hna⟩
      _ ≤ ∑ a ∈ hfin.toFinset, walkerSequenceLaw (S.mult ε ω) 0 {xs | a ∉ clus ε ω xs} :=
          measure_biUnion_finset_le _ _
      _ ≤ hfin.toFinset.card • ENNReal.ofReal (2 * Real.exp (-(c * ε ^ (-q)))) :=
          Finset.sum_le_card_nsmul _ _ _ fun a ha => hsite' a (hfin.mem_toFinset.1 ha)
      _ ≤ ENNReal.ofReal (ε ^ (-2 : ℝ) * (2 * Real.exp (-(c * ε ^ (-q))))) := by
          rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
          apply ENNReal.ofReal_le_ofReal
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          rw [← Set.ncard_eq_toFinset_card _ hfin]
          exact (Nat.cast_le.2 (Set.ncard_le_ncard (hsub1.trans hsub2) hCfin)).trans hCcard
  have hsite : ∀ δ₀ : ℝ, 0 < δ₀ → ∃ c : ℝ, 0 < c ∧ ∀ ε : ℝ, 0 < ε → 2 / δ₀ ≤ ε ^ (-q) → ∀ ω ∈ B ε,
      δ₀ ≤ s ω → ∀ a ∈ O₁ ε ω,
        walkerSequenceLaw (S.mult ε ω) 0 {xs | a ∉ idlaCluster xs ⌊K ε⌋₊} ≤
            ENNReal.ofReal (2 * Real.exp (-(c * ε ^ (-q)))) ∧
          walkerSequenceLaw (S.mult ε ω) 0 {xs | a ∉ stoppedIDLACluster (O₂ ε ω) xs ⌊K ε⌋₊} ≤
            ENNReal.ofReal (2 * Real.exp (-(c * ε ^ (-q)))) := by
    intro δ₀ hδ₀
    obtain ⟨c, hc, hcQ⟩ := hQ (δ₀ / 2) (by positivity)
    refine ⟨c, hc, fun ε hε hεq ω hωB hsω a ha => ?_⟩
    obtain ⟨h1, h2⟩ := hωB a ha
    exact siteBound_of_conditions hG hδ₀ hc hcQ (S.mult ε ω) (O₂ ε ω) a (K ε) (s ω) (ε ^ (-q))
      (Real.rpow_pos_of_pos hε _) hεq hsω h1 h2
  refine ⟨main (fun ε _ xs => idlaCluster xs ⌊K ε⌋₊) ?_,
    main (fun ε ω xs => stoppedIDLACluster (O₂ ε ω) xs ⌊K ε⌋₊) ?_⟩
  · intro δ₀ hδ₀
    obtain ⟨c, hc, h⟩ := hsite δ₀ hδ₀
    exact ⟨c, hc, fun ε hε hεq ω hωB hsω a ha => (h ε hε hεq ω hωB hsω a ha).1⟩
  · intro δ₀ hδ₀
    obtain ⟨c, hc, h⟩ := hsite δ₀ hδ₀
    exact ⟨c, hc, fun ε hε hεq ω hωB hsω a ha => (h ε hε hεq ω hωB hsω a ha).2⟩

/-- The relaxed form of Lemma 5.2 implies the stated one. -/
theorem generalIDLALowerBound_of_relaxed (𝒮 : SpaceFillingSLEModel) (h : GeneralIDLALowerBoundRelaxedStep 𝒮) :
    GeneralIDLALowerBoundStmt 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS O₁ O₂ K q s hm₁ hm₂ hO _ hq hs hspos hgood
  obtain ⟨hl, hs'⟩ := h γ hγ hγ2 ρ hρ hρ1 Ω S hS O₁ O₂ K q s
    (fun ε hε => (hO ε hε).mono fun _ h => ⟨h.1, h.2.1⟩) hq hs hspos hgood
  obtain ⟨hjl, hjs⟩ := hS.joint_generalIDLABounds_of_sectionwise O₁ O₂ K hm₁ hm₂ hl hs'
  exact ⟨hjl, hjs⟩

/-! ## Assembly -/

namespace IDLALowerBound

/-- `ε^b → 0` as `ε → 0⁺`, for `b > 0`. -/
theorem tendsto_rpow_nhdsGT_zero' {b : ℝ} (hb : 0 < b) :
    Tendsto (fun ε : ℝ => ε ^ b) (𝓝[>] 0) (𝓝 0) := by
  have h : Tendsto (fun ε : ℝ => ε ^ b) (𝓝[>] 0) (𝓝 ((0 : ℝ) ^ b)) :=
    ((Real.continuousAt_rpow_const 0 b (Or.inr hb.le)).tendsto).mono_left nhdsWithin_le_nhds
  rwa [Real.zero_rpow hb.ne'] at h

/-- An event of polynomially high probability holds with probability tending to `1`. -/
theorem probTendsToOne_of_polyHighProb' {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {E : ℝ → Set Ω}
    (h : PolyHighProb P E) : ProbTendsToOne P E := by
  obtain ⟨p, hp, C, r₀, hr₀, hbound⟩ := h
  have hup : Tendsto (fun ε : ℝ => ENNReal.ofReal (C * ε ^ p)) (𝓝[>] 0) (𝓝 0) := by
    have h4 := (tendsto_rpow_nhdsGT_zero' hp).const_mul C
    rw [mul_zero] at h4
    have h5 := ENNReal.tendsto_ofReal h4
    rwa [ENNReal.ofReal_zero] at h5
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT hr₀] with ε hε hεr
  exact hbound ε hε hεr.2

end IDLALowerBound

open IDLALowerBound in
/-- **Proposition 5.1 for the discrete cluster** (the printed proof, lines 2030-2048): for `δ ∈ (0, ρ)` and `t > 0`,
on `{t < T}`, except on an event of probability tending to `0`, `B⁻_δ(Λ_t) ⊆ Ā_ε(⌊t ε⁻¹⌋)`, also for walkers stopped
upon exiting `Λ^ε_t`. From Lemma 5.2 (relaxed), Lemmas 5.3 and 5.4 (with `δ/4`), Lemma 2.8 and the discrete-cluster
form of Proposition 4.2 (with `δ/2`). -/
theorem iDLALowerBound_discrete_of_steps (𝒮 : SpaceFillingSLEModel) (h52 : GeneralIDLALowerBoundRelaxedStep 𝒮)
    (h53 : MeanValueInequalityStmt 𝒮) (h54 : LLowerBoundStmt 𝒮) (h28 : CellSizeEstimateStmt 𝒮)
    (hI : DiscreteClusterInnerBoundStep 𝒮) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
    ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
    ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) →
    ∀ δ t : ℝ, 0 < δ → δ < ρ → 0 < t →
      Tendsto (fun ε => S.idlaSectionProb ε {p | t < clusterExitTime (Λ p.1) ρ ∧
          ¬ innerNbhd δ (Λ p.1 t) ⊆ fillCells ε (S.η p.1) (idlaCluster p.2 ⌊t / ε⌋₊)})
        (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (fun ε => S.idlaSectionProb ε {p | t < clusterExitTime (Λ p.1) ρ ∧
          ¬ innerNbhd δ (Λ p.1 t) ⊆ fillCells ε (S.η p.1)
            (stoppedIDLACluster (matedDiscreteCluster (S.mult ε p.1) ε (S.η p.1) ρ t) p.2 ⌊t / ε⌋₊)})
        (𝓝[>] 0) (𝓝 0) := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS Λ hΛ δ t hδ hδρ ht
  have := hS.isProbabilityMeasure
  have hδ4 : 0 < δ / 4 := by positivity
  have hδ4ρ : δ / 4 < ρ := by linarith
  obtain ⟨q, hq, h54'⟩ := h54 γ hγ hγ2 ρ hρ hρ1
  have h4 := h54' Ω S hS Λ hΛ (δ / 4) t hδ4 hδ4ρ ht
  obtain ⟨s, hsm, hspos, h3⟩ := h53 γ hγ hγ2 ρ hρ hρ1 Ω S hS Λ hΛ (δ / 4) t hδ4 hδ4ρ ht
  have hI' := hI γ hγ hγ2 ρ hρ hρ1 Ω S hS Λ hΛ (δ / 2) t (by positivity) (by linarith) ht
  unfold TendsToOneOn at h3 h4 hI'
  -- the cell-size estimate with `ζ = 1/(2+γ)²`
  set e : ℝ := 1 / (2 + γ) ^ 2 with he_def
  have he : 0 < e := by positivity
  have he1 : e < 1 := by
    rw [he_def, div_lt_one (by positivity)]
    nlinarith
  have hexp : 2 / (2 + γ) ^ 2 - e = e := by
    rw [he_def]
    ring
  have hcell := probTendsToOne_of_polyHighProb' (h28 γ hγ hγ2 e ρ he he1 hρ hρ1 Ω S hS)
  unfold ProbTendsToOne at hcell
  -- Lemma 5.2 with `O₁ = {a ∈ Λ^ε_t : dist(η(a), ∂Λ̄^ε_t) > δ/4}` (empty off `{t < T}`), `O₂ = Λ^ε_t`, `K = t/ε`
  set F : Set Ω := {ω | t < clusterExitTime (Λ ω) ρ} with hF
  set L : ℝ → Ω → Set ℤ := fun ε ω => matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t with hL
  set O₁ : ℝ → Ω → Set ℤ := fun ε ω => {a ∈ L ε ω | ω ∈ F ∧
    δ / 4 < infDist (vertexPoint ε (S.η ω) a) (frontier (fillCells ε (S.η ω) (L ε ω)))} with hO₁
  have hO : ∀ ε, 0 < ε → ∀ᵐ ω ∂S.P, O₁ ε ω ⊆ L ε ω ∧ L ε ω ⊆ cellVertices ε (S.η ω) (ball 0 ρ) :=
    fun ε _ => ae_of_all _ fun ω => ⟨fun a ha => ha.1, fun a ha => ha.1⟩
  have h34 := h3.add h4
  rw [zero_add] at h34
  have hgood : ProbTendsToOne S.P (fun ε => {ω | ∀ a ∈ O₁ ε ω,
      (1 + s ω) * ∑' b : L ε ω, greenFn (S.mult ε ω) (L ε ω) b a ≤
        t / ε * greenFn (S.mult ε ω) (L ε ω) 0 a ∧
      ε ^ (-q) ≤ (∑' b : L ε ω, greenFn (S.mult ε ω) (L ε ω) b a) / greenFn (S.mult ε ω) (L ε ω) a a}) := by
    unfold ProbTendsToOne
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h34
      (Eventually.of_forall fun _ => zero_le) (Eventually.of_forall fun ε => ?_)
    refine le_trans (measure_mono ?_) (measure_union_le _ _)
    intro ω hω
    rw [mem_compl_iff] at hω
    have hωF : ω ∈ F := by
      by_contra hωF
      exact hω fun a ha => absurd ha.2.1 hωF
    by_contra hcon
    simp only [mem_union, mem_inter_iff, mem_compl_iff, not_or, not_and, not_not] at hcon
    exact hω fun a ha => ⟨hcon.1 hωF a ha.1 ha.2.2, hcon.2 hωF a ha.1 ha.2.2⟩
  obtain ⟨hA, hB⟩ := h52 γ hγ hγ2 ρ hρ hρ1 Ω S hS O₁ L (fun ε => t / ε) q s hO hq hsm hspos hgood
  -- from `O₁ ⊆ A` to `B⁻_δ(Λ_t) ⊆ Ā`, off the bad events of the cell size and of Proposition 4.2
  have hbad : Tendsto (fun ε => S.P ((F ∩ {ω | innerNbhd (δ / 2) (Λ ω t) ⊆
      fillCells ε (S.η ω) (L ε ω)}ᶜ) ∪ {ω | ∀ k : ℤ, (cell ε (S.η ω) k ∩ ball 0 ρ).Nonempty →
        ε ^ (2 / (2 - γ) ^ 2 + e) ≤ diam (cell ε (S.η ω) k) ∧
          diam (cell ε (S.η ω) k) ≤ ε ^ (2 / (2 + γ) ^ 2 - e)}ᶜ)) (𝓝[>] 0) (𝓝 0) := by
    have h := hI'.add hcell
    rw [zero_add] at h
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h
      (Eventually.of_forall fun _ => zero_le) (Eventually.of_forall fun _ => measure_union_le _ _)
  have fin : ∀ clus : ℝ → Ω → (ℕ → ℕ → ℤ) → Set ℤ,
      Tendsto (fun ε => S.idlaSectionProb ε {p | ¬ O₁ ε p.1 ⊆ clus ε p.1 p.2}) (𝓝[>] 0) (𝓝 0) →
      Tendsto (fun ε => S.idlaSectionProb ε {p | t < clusterExitTime (Λ p.1) ρ ∧
        ¬ innerNbhd δ (Λ p.1 t) ⊆ fillCells ε (S.η p.1) (clus ε p.1 p.2)}) (𝓝[>] 0) (𝓝 0) := by
    intro clus hcl
    have h := hcl.add hbad
    rw [zero_add] at h
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h
      (Eventually.of_forall fun _ => zero_le) ?_
    filter_upwards [self_mem_nhdsWithin, (tendsto_rpow_nhdsGT_zero' he).eventually (gt_mem_nhds hδ4)]
      with ε (hε : 0 < ε) hεe
    refine annealedOuterProb_le_add S.P _ _ _ _ fun ω hω xs hxs => ?_
    simp only [mem_union, mem_inter_iff, mem_compl_iff, not_or, not_and, not_not] at hω
    obtain ⟨hωF, hnot⟩ := hxs
    have hin := hω.1 hωF
    have hcs := hω.2
    intro hsub
    apply hnot
    have hcellL : ∀ a ∈ L ε ω, (cell ε (S.η ω) a ∩ ball 0 ρ).Nonempty := fun a ha => ha.1
    have hdiam : ∀ a ∈ L ε ω, ε ^ (2 / (2 - γ) ^ 2 + e) ≤ diam (cell ε (S.η ω) a) ∧
        diam (cell ε (S.η ω) a) ≤ ε ^ e := by
      intro a ha
      have := hcs a (hcellL a ha)
      rwa [hexp] at this
    have hb : ∀ a ∈ L ε ω, Bornology.IsBounded (cell ε (S.η ω) a) := by
      intro a ha
      by_contra hnb
      have h1 := (hdiam a ha).1
      rw [diam_eq_zero_of_unbounded hnb] at h1
      exact absurd h1 (not_le.2 (Real.rpow_pos_of_pos hε _))
    have hd : ∀ a ∈ L ε ω, diam (cell ε (S.η ω) a) < δ / 4 := fun a ha => (hdiam a ha).2.trans_lt hεe
    calc innerNbhd δ (Λ ω t)
        ⊆ fillCells ε (S.η ω) {a ∈ L ε ω |
            δ / 4 < infDist (vertexPoint ε (S.η ω) a) (frontier (fillCells ε (S.η ω) (L ε ω)))} :=
          innerNbhd_subset_fillCells_deep hε.le hδ hb hd hcellL hin
      _ ⊆ fillCells ε (S.η ω) (O₁ ε ω) := fillCells_mono' fun a ha => ⟨ha.1, hωF, ha.2⟩
      _ ⊆ fillCells ε (S.η ω) (clus ε ω xs) := fillCells_mono' hsub
  exact ⟨fin (fun ε _ xs => idlaCluster xs ⌊t / ε⌋₊) hA,
    fin (fun ε ω xs => stoppedIDLACluster (L ε ω) xs ⌊t / ε⌋₊) hB⟩

end MatedCRT
