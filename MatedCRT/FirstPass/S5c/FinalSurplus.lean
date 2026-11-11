import MatedCRT.FirstPass.S5c.HsubChain
import MatedCRT.FirstPass.S5c.HsubMargin
import MatedCRT.FirstPass.S5c.MeshCriterion
import MatedCRT.FirstPass.S5c.SubseqArbitrary
import MatedCRT.FirstPass.S5c.ValidCellFacts
import MatedCRT.FirstPass.S5c.MassWire
import MatedCRT.FirstPass.S5c.MeshScale
import MatedCRT.FirstPass.S5c.ClusterCells
import MatedCRT.FirstPass.S5c.HDist
import MatedCRT.FirstPass.S5c.MassPositive
import MatedCRT.FirstPass.S4d.ExitTimeBall
import MatedCRT.Proofs.Infra.LocallyFinite
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.HarmonicPathExit
import MatedCRT.Proofs.MatingOfTrees.AdjacentCells
import MatedCRT.Proofs.Sec5.LLowerBound.SmallCellsProb
import MatedCRT.Proofs.Sec5.MeanValueInequality.SurplusSteps
import MatedCRT.Proofs.Sec1.ConeScaleRadius

/-!
# FIRST PASS, Lemma 5.3: `MeanValueSurplusLowerStep`

Assembly:
* Output constant `c ω = (c₀/6) * b0 ω / (2 * C)`; `b0` is the measurable positive margin at the fixed depth `δ`
  (`marginExact_proved`), and `C` is the mesh constant of `mesh_scale_eventually`.
* Cover margins: `marginExact_countable` at the deterministic depths `coverDepth j`.
* Subsequence: `exists_subseq_ae_eventually_good_of_seq` on the bad families `badFamily53`
  (ConvergenceDivisibleStmt at `t` and `t/2` with tolerance `(1/2)^k`; small cells at `δ/8`).
* Deterministic outcome chain: `hsub_outcome`. Outcome-level inputs: `FPFirstHitVisits` (through `ae_cell_facts`),
  `AdjacentCellsMeetAeStep` (through local finiteness of the multiplicities), `MepsScalingInput` (mesh scaling).
-/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal
open _root_.HarmonicBalls
open S5c

/-- The floor algebra: `t (-w/(t/2)) = -2 w`, so the margin `b ≤ a - 2 w` gives the floor of `hsub_outcome`. -/
lemma floor_form_53 {a w t b : ℝ} (ht : 0 < t) (h : b ≤ a - 2 * w) :
    b ≤ a + t * (-w / (t / 2)) := by
  have ht' : t ≠ 0 := ht.ne'
  have hm : t * (-w / (t / 2)) = -2 * w := by
    field_simp
  linarith

/-- The bad family of the subsequence criterion at mesh `ε` and index `k`: failure of the convergence of the
rescaled least supersolution at time `t` or `t/2` to `(c₀/6) w̄` at tolerance `(1/2)^k` on `{t < T}`
(`ConvergenceDivisibleStmt`, Theorem 4.1), or failure of the small-cell event at diameter `δ/8`. -/
def badFamily53 {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (Λ : Ω → ℝ → Set ℂ) (ρ t δ : ℝ)
    (ε : ℝ) (k : ℕ) : Set Ω :=
  {ω | t < clusterExitTime (Λ ω) ρ ∧ ∃ y ∈ ball (0 : ℂ) ρ,
      (1 / 2 : ℝ) ^ k < |rescaledMatedLeastSupersolution S ρ t ε ω y -
        S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t y|} ∪
  {ω | t / 2 < clusterExitTime (Λ ω) ρ ∧ ∃ y ∈ ball (0 : ℂ) ρ,
      (1 / 2 : ℝ) ^ k < |rescaledMatedLeastSupersolution S ρ (t / 2) ε ω y -
        S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 (t / 2) y|} ∪
  {ω | ¬ ∀ a ∈ cellVertices ε (S.η ω) (ball (0 : ℂ) ρ), diam (cell ε (S.η ω) a) ≤ δ / 8}

/-- **Lemma 5.3, surplus lower bound (first pass).** `MeanValueSurplusLowerStep` with the external Props
`FrozenLQGMeasureFieldMeasurable`, `FrozenUniversalMeasurabilityOfAnalytic`, `FrozenDiskGreenNonnegCont`,
`FrozenGreenDiscPole`, `FPStrongMinimumPrinciple`, `ConeScaleInvarianceCodedStmt`, `ConeScaleRadiusPosStep`
(inputs of `marginExact_proved`), `FPFirstHitVisits` and `MepsScalingInput` passed as hypotheses. -/
theorem firstPass_5_3_step {𝒮 : SpaceFillingSLEModel}
    (hF : FrozenLQGMeasureFieldMeasurable 𝒮) (hF1 : FrozenUniversalMeasurabilityOfAnalytic)
    (hF3 : FrozenDiskGreenNonnegCont) (hG : FrozenGreenDiscPole) (hmin : FPStrongMinimumPrinciple)
    (hLs : ConeScaleInvarianceCodedStmt) (hpos : ConeScaleRadiusPosStep)
    (hfirst : FPFirstHitVisits 𝒮) (hM : MepsScalingInput 𝒮) :
    MeanValueSurplusLowerStep 𝒮 := by
  intro _hDL _hMP hCD _hUC _hET γ hγ0 hγ2 ρ hρ0 hρ1 Ω _ S hS Λ hΛ δ t hδ hδρ ht
  have : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  have hδ1 : δ < 1 := by linarith
  -- Margins: the target floor at the fixed depth δ, and the countable cover margins.
  obtain ⟨b0, hb0m, hb0pos, hb0ae⟩ :=
    marginExact_proved hγ0 hγ2 hF hF1 hF3 hG hmin hLs hpos S hS Λ hΛ hρ0 hδ ht
  obtain ⟨bj, hbjm, hbjpos, hbjae⟩ :=
    marginExact_countable hγ0 hγ2 hF hF1 hF3 hG hmin hLs hpos S hS Λ hΛ hρ0 ht coverDepth coverDepth_pos
  -- Constants: c₀ = 2/m₀ > 0 and the mesh constant C > 1.
  have hm0 : 0 < S.m₀ := hS.m₀_pos hγ0 hγ2
  have hc0 : 0 < S.c₀ := div_pos two_pos hm0
  have hκ : 0 < S.c₀ / 6 := div_pos hc0 (by norm_num)
  obtain ⟨C, hC1, hMS⟩ := mesh_scale_eventually hM hγ0 hγ2 Ω S hS
  have hCpos : 0 < C := by linarith
  -- The output constant: measurable for the environment sigma-algebra, positive everywhere.
  have hc : Measurable[S.envSigma] (fun ω => S.c₀ / 6 * b0 ω / (2 * C)) :=
    (hb0m.const_mul (S.c₀ / 6)).div_const (2 * C)
  refine ⟨fun ω => S.c₀ / 6 * b0 ω / (2 * C), hc, fun ω => ?_, ?_⟩
  · exact div_pos (mul_pos hκ (hb0pos ω)) (by linarith)
  -- Almost-sure facts of the environment.
  have hcell := ae_cell_facts hS (hfirst γ hγ0 hγ2 Ω S hS)
  have hmass := ae_fillCells_mass_le hγ0 hγ2 hρ0 hρ1 Ω S hS
  have hlfAll := hS.ae_isLocallyFiniteMult hγ0 hγ2 (adjacentCellsMeetAeStep 𝒮)
  have hcont := ae_continuous_eta_of hS
  have hprop : ∀ᵐ ω ∂S.P, Tendsto (S.η ω) (cocompact ℝ) (cocompact ℂ) := hS.ae_tendsto_cocompact
  have hap : ∀ᵐ ω ∂S.P, IsAreaParametrized (S.μ ω) (S.η ω) := hS.isAreaParametrized
  -- Small cells at diameter δ/8 (`ProbTendsToOne`, unfolded).
  have hsmall : Tendsto (fun ε => S.P ({ω | ∀ a ∈ cellVertices ε (S.η ω) (ball (0 : ℂ) ρ),
      diam (cell ε (S.η ω) a) ≤ δ / 8}ᶜ)) (𝓝[>] 0) (𝓝 0) :=
    hS.probTendsToOne_small_cells ρ (δ / 8) (by linarith)
  -- Bad families: summable failure probabilities along 𝓝[>] 0.
  have hbad : ∀ k : ℕ, Tendsto (fun ε => S.P (badFamily53 S Λ ρ t δ ε k)) (𝓝[>] 0) (𝓝 0) := by
    intro k
    have h1 := hCD γ hγ0 hγ2 ρ hρ0 hρ1 Ω S hS Λ hΛ t ht ((1 / 2 : ℝ) ^ k) (by positivity)
    have h2 := hCD γ hγ0 hγ2 ρ hρ0 hρ1 Ω S hS Λ hΛ (t / 2) (by linarith) ((1 / 2 : ℝ) ^ k)
      (by positivity)
    have hsum := (h1.add h2).add hsmall
    rw [add_zero, add_zero] at hsum
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ => zero_le)
      (fun ε => ?_)
    unfold badFamily53
    exact (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
  -- The target: null measurability of the success events, and the subsequence criterion.
  refine tendsToOneOn_of_subsequence_ae_eventually ?_ ?_
  · filter_upwards [eventually_mem_nhdsWithin] with ε hε
    exact nullMeasurableSet_success_proved hS hγ0 hγ2 hε ρ t δ ht _ hc
      (hlfAll.mono fun ω hω b => hω ε hε b)
  · intro e he
    obtain ⟨N, hN⟩ := eventually_atTop.1 (he.eventually eventually_mem_nhdsWithin)
    have hxpos : ∀ n : ℕ, 0 < e (n + N) := fun n => hN (n + N) (by omega)
    have hxlim : Tendsto (fun n : ℕ => e (n + N)) atTop (𝓝 0) :=
      (he.mono_right nhdsWithin_le_nhds).comp (tendsto_add_atTop_nat N)
    obtain ⟨φ, hφ, hae⟩ := exists_subseq_ae_eventually_good_of_seq
      (fun ε k => badFamily53 S Λ ρ t δ ε k) hbad (fun n => e (n + N)) hxpos hxlim
    refine ⟨fun k => φ k + N, fun a b hab => Nat.add_lt_add_right (hφ hab) N, ?_⟩
    filter_upwards [hae, hcell, hmass, hcont, hprop, hap, hΛ, hb0ae, hbjae] with
      ω hωbad hcellω hmassω hcontω hpropω hapω hΛω hb0ω hmj hTω
    have hTω' : t < clusterExitTime (Λ ω) ρ := hTω
    have hT2 : t / 2 < clusterExitTime (Λ ω) ρ := by linarith
    -- Outcome facts for the harmonic-ball family `Λ_t(ω)`.
    have hLball : Λ ω t ⊆ ball (0 : ℂ) ρ :=
      (MatedCRT.subset_ball_of_lt_clusterExitTime hΛω ht hTω').trans (ball_subset_ball (by linarith))
    have hLc : (Λ ω t)ᶜ.Nonempty := ⟨((ρ + 1 : ℝ) : ℂ), fun h => by
      have h' := mem_ball_zero_iff.1 (hLball h)
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)] at h'
      linarith⟩
    have hμL : S.μ ω (Λ ω t) = ENNReal.ofReal t := hΛω.2.1.measure_eq t ht
    have hLreg : interior (closure (Λ ω t)) = Λ ω t := hΛω.2.1.isRegularOpen t ht
    have hfull : ∀ (x : ℂ) (r : ℝ), 0 < r → 0 < S.μ ω (ball x r) :=
      fun x r hr => mass_ball_pos hapω x hr
    have hfloor0 : ∀ x ∈ compactCore (Λ ω t) ρ δ,
        b0 ω ≤ leastSupersolution (S.μ ω) ρ 0 t x +
          t * (-(leastSupersolution (S.μ ω) ρ 0 (t / 2) x) / (t / 2)) :=
      fun x hx => floor_form_53 ht (hb0ω hTω' x hx.1 hx.2)
    have hfloorj : ∀ j : ℕ, ∀ x ∈ compactCore (Λ ω t) ρ (coverDepth j),
        bj j ω ≤ leastSupersolution (S.μ ω) ρ 0 t x +
          t * (-(leastSupersolution (S.μ ω) ρ 0 (t / 2) x) / (t / 2)) :=
      fun j x hx => floor_form_53 ht (hmj hTω' j x hx.1 hx.2)
    -- Outcome facts for the subsequence, from the bad families.
    have hεpos : ∀ k : ℕ, 0 < e (φ k + N) := fun k => hxpos (φ k)
    have hεlim : Tendsto (fun k : ℕ => e (φ k + N)) atTop (𝓝 0) := hxlim.comp hφ.tendsto_atTop
    have hscale := hMS (fun k : ℕ => e (φ k + N)) hεpos hεlim
    have hkev : ∀ᶠ k in atTop, ω ∉ badFamily53 S Λ ρ t δ (e (φ k + N)) k := hωbad
    have hbdd : ∀ (k : ℕ) (a : ℤ), Bornology.IsBounded (cell (e (φ k + N)) (S.η ω) a) :=
      fun k a => (isCompact_Icc.image hcontω).isBounded
    have hx : ∀ (k : ℕ) (a : ℤ), ∃ y ∈ cell (e (φ k + N)) (S.η ω) a,
        vertexOf (e (φ k + N)) (S.η ω) y = a :=
      fun k a => hcellω.2 _ (hεpos k) a
    have hfin : ∀ k : ℕ, (matedDiscreteCluster (S.mult (e (φ k + N)) ω) (e (φ k + N)) (S.η ω) ρ t).Finite :=
      fun k => (cellVertices_finite_of_isCompact hcontω hpropω (hεpos k)
        (isCompact_closedBall (0 : ℂ) ρ)).subset (fun a ha => by
          obtain ⟨y, hy⟩ := cell_meets_ball_of_mem_matedCluster ha
          exact ⟨y, hy.1, ball_subset_closedBall hy.2⟩)
    have hU : ∀ k : ℕ, IsCompact (fillCells (e (φ k + N)) (S.η ω)
        (matedDiscreteCluster (S.mult (e (φ k + N)) ω) (e (φ k + N)) (S.η ω) ρ t)) :=
      fun k => isCompact_fillCells_of_finite hcontω (hfin k)
    have hEt : ∀ᶠ k in atTop, ∀ y ∈ ball (0 : ℂ) ρ,
        |rescale (S.mε (e (φ k + N))) (e (φ k + N)) (S.η ω)
          (matedLeastSupersolution (S.mult (e (φ k + N)) ω) (e (φ k + N)) (S.η ω) ρ t) y -
          S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t y| ≤ (1 / 2 : ℝ) ^ k := by
      filter_upwards [hkev] with k hk
      intro y hy
      exact not_lt.1 (fun h => hk (Or.inl (Or.inl ⟨hTω', y, hy, h⟩)))
    have hEs : ∀ᶠ k in atTop, ∀ y ∈ ball (0 : ℂ) ρ,
        |rescale (S.mε (e (φ k + N))) (e (φ k + N)) (S.η ω)
          (matedLeastSupersolution (S.mult (e (φ k + N)) ω) (e (φ k + N)) (S.η ω) ρ (t / 2)) y -
          S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 (t / 2) y| ≤ (1 / 2 : ℝ) ^ k := by
      filter_upwards [hkev] with k hk
      intro y hy
      exact not_lt.1 (fun h => hk (Or.inl (Or.inr ⟨hT2, y, hy, h⟩)))
    have hsmallk : ∀ᶠ k in atTop, ∀ a ∈ cellVertices (e (φ k + N)) (S.η ω) (ball (0 : ℂ) ρ),
        diam (cell (e (φ k + N)) (S.η ω) a) ≤ δ / 8 := by
      filter_upwards [hkev] with k hk
      exact not_not.1 (fun h => hk (Or.inr h))
    have hdiam : ∀ᶠ k in atTop, ∀ a ∈ matedDiscreteCluster (S.mult (e (φ k + N)) ω) (e (φ k + N))
        (S.η ω) ρ t, diam (cell (e (φ k + N)) (S.η ω) a) < δ / 4 := by
      filter_upwards [hsmallk] with k hk
      intro a ha
      have := hk a (cell_meets_ball_of_mem_matedCluster ha)
      linarith
    have hUQ : ∀ᶠ k in atTop, fillCells (e (φ k + N)) (S.η ω)
        (matedDiscreteCluster (S.mult (e (φ k + N)) ω) (e (φ k + N)) (S.η ω) ρ t) ⊆
        closedBall (0 : ℂ) (ρ + 1) := by
      filter_upwards [hsmallk] with k hk
      exact (fillCells_subset_closedBall_of_diam (hbdd k)
        (fun a ha => cell_meets_ball_of_mem_matedCluster ha)
        (fun a ha => hk a (cell_meets_ball_of_mem_matedCluster ha))).trans
        (closedBall_subset_closedBall (by linarith))
    have hUmass : ∀ᶠ k in atTop, S.μ ω (fillCells (e (φ k + N)) (S.η ω)
        (matedDiscreteCluster (S.mult (e (φ k + N)) ω) (e (φ k + N)) (S.η ω) ρ t)) ≤
        ENNReal.ofReal t :=
      Eventually.of_forall fun k => hmassω t _ ht (hεpos k)
    have hmemcell : ∀ᶠ k in atTop, ∀ y ∈ Λ ω t,
        y ∈ cell (e (φ k + N)) (S.η ω) (vertexOf (e (φ k + N)) (S.η ω) y) :=
      Eventually.of_forall fun k y _ => hcellω.1 _ (hεpos k) y
    have hmε : ∀ᶠ k in atTop, 0 < S.mε (e (φ k + N)) := hscale.mono fun k hk => hk.1
    have hCmε : ∀ᶠ k in atTop, 1 ≤ S.mε (e (φ k + N)) * e (φ k + N) * C :=
      hscale.mono fun k hk => hk.2
    have hεev : ∀ᶠ k in atTop, 0 < e (φ k + N) := Eventually.of_forall hεpos
    have he' : Tendsto (fun k : ℕ => (1 / 2 : ℝ) ^ k) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    -- The deterministic outcome chain.
    exact hsub_outcome (μ := S.μ ω) (L := Λ ω t) (ρ := ρ) (t := t) (δ := δ)
      (κ := S.c₀ / 6) (Cm := C) (b0 := b0 ω) (bj := fun j => bj j ω)
      (m := fun k => S.mult (e (φ k + N)) ω) (ε := fun k => e (φ k + N))
      (mε := fun k => S.mε (e (φ k + N))) (η := S.η ω) (e := fun k => (1 / 2 : ℝ) ^ k)
      ht hκ hCpos hδ (hb0pos ω) (fun j => hbjpos j ω) hLreg hLc hLball hμL hfull
      hfloor0 hfloorj hEt hEs he' hbdd hx hmε hεev hCmε (Eventually.of_forall hU) hUQ hUmass
      hmemcell hdiam

/-- **Lemma 5.3, mean-value inequality (first pass, final form).** `MeanValueInequalityStmt 𝒮` (Draft `Section5`,
lemma:mean-value-ineq). It is the reduction `meanValueInequality_of_lower` (SurplusSteps.lean) applied to the surplus
lower bound `firstPass_5_3_step`, with
* the step `ConeScaleRadiusPosStep` discharged from the quantum cone scaling input `QuantumConeScalingInput`
  (DMS14 Proposition 4.13(i); `coneScaleRadiusPosStep_of_input`, Proofs/Sec1/ConeScaleRadius.lean:315);
* the step `LQGMeasureFieldMeasurableStep` obtained from `FrozenLQGMeasureFieldMeasurable` by symmetry of the a.s. equality.
The Draft inputs `DiscreteLaplacianBoundCorrectedStmt` (Lemma 4.4 corrected), `MaximumPrincipleStmt`,
`ConvergenceDivisibleStmt`, `UniformConvergenceGreenKernelStmt`, `ExitTimeUpperBoundStmt` and `BoundedExitTimeRVStmt`
(Lemma 2.17) are cited inputs of Lemma 5.3, passed as hypotheses. -/
theorem firstPass_5_3_final {𝒮 : SpaceFillingSLEModel}
    (hF : FrozenLQGMeasureFieldMeasurable 𝒮) (hF1 : FrozenUniversalMeasurabilityOfAnalytic)
    (hF3 : FrozenDiskGreenNonnegCont) (hG : FrozenGreenDiscPole) (hmin : FPStrongMinimumPrinciple)
    (hLs : ConeScaleInvarianceCodedStmt) (hscale : QuantumConeScalingInput)
    (hfirst : FPFirstHitVisits 𝒮) (hM : MepsScalingInput 𝒮)
    (h44 : DiscreteLaplacianBoundCorrectedStmt 𝒮) (h213 : MaximumPrincipleStmt 𝒮)
    (h41 : ConvergenceDivisibleStmt 𝒮) (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (h217 : BoundedExitTimeRVStmt) :
    MeanValueInequalityStmt 𝒮 := by
  have hμ : LQGMeasureFieldMeasurableStep 𝒮 := by
    intro γ hγ hγ2 Ω _ S hS
    obtain ⟨g, hg, hae⟩ := hF γ hγ hγ2 Ω S hS
    exact ⟨g, hg, hae.mono fun ω hω => hω.symm⟩
  exact meanValueInequality_of_lower 𝒮 h44 h213 h41 h33 h218 h217 hμ
    (firstPass_5_3_step hF hF1 hF3 hG hmin hLs (coneScaleRadiusPosStep_of_input hscale) hfirst hM)

end MatedCRT
