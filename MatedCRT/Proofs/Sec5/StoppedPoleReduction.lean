import MatedCRT.Proofs.Sec5.StoppedInterior
import MatedCRT.Proofs.Sec5.StoppedPoleBound
import MatedCRT.Proofs.Sec5.MeanValueInequality.SurplusSteps
import MatedCRT.FirstPass.LPBridge.InRepoProofs
import MatedCRT.FirstPass.S1S2S8SA
import MatedCRT.FirstPass.Derived.CoreExitTimeFromBG20

/-!
# The stopped surplus on annuli around the pole, and the pole step from the geometry and margin steps

`stoppedSurplusAnnulus_of_gap` is the annulus half of `StoppedInterior.stoppedSurplusInterior_of_gap`, for every
deterministic radius `s > 0`: on `{t < T}`, with probability tending to one, `c/ε ≤ v^ε_t(a)` for every `δ`-interior
vertex `a` of `V^ε(Λ_t)` with `s ≤ |η(a)|`, for a `σ(h, η)`-measurable `c > 0`. The proof is that of
`stoppedSurplusInterior_of_gap` (Theorem 4.1 on `B_ρ`, Lemma 3.3 on the annulus, the strict obstacle gap, the geometry
step at radius `s/2` and the margin step), with the pole region left out; it does not use the pole step.

`stoppedSurplusPole_of_steps` derives the pole step `StoppedSurplusPoleStep` from the same inputs and Lemmas 2.16 and
2.18: near the pole the logarithmic bound `stoppedPoleLowerBound` holds on
`{𝓜 ≤ n}` for `|η(a)| < r_n`, the annulus bound holds for `r_n ≤ |η(a)|`, and the constant is `min 1 c_N` at the
random index `N = ⌈𝓜⌉`, computed from a `σ(h)`-measurable version of `μ_h` (`frozenLQGMeasureFieldMeasurable_holds`);
`𝓜` is finite almost surely by Lemma 2.17.
-/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace StoppedInterior

/-- **The stopped surplus on the annulus `{s ≤ |η(a)|}`** for a deterministic radius `s > 0`, from the strict obstacle
gap, the geometry step, the margin step, the scaling of the expected exit time, Theorem 4.1 and Lemma 3.3: the annulus
half of `stoppedSurplusInterior_of_gap`, which does not use the pole step. -/
theorem stoppedSurplusAnnulus_of_gap (𝒮 : SpaceFillingSLEModel) (hgap : HarmonicBallStrictObstacleGapStep 𝒮)
    (hgeo : StoppedInteriorGeometryStep 𝒮) (hmeas : StoppedInteriorMeasurableStep 𝒮)
    (hmeps : MepsScalingInput 𝒮) (h41 : ConvergenceDivisibleStmt 𝒮) (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    (Λ : Ω → ℝ → Set ℂ) (hΛ : ∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω))
    (δ t : ℝ) (hδ : 0 < δ) (ht : 0 < t) (s : ℝ) (hs : 0 < s) :
    ∃ c : Ω → ℝ, Measurable[S.envSigma] c ∧ (∀ ω, 0 < c ω) ∧
      TendsToOneOn S.P {ω | t < clusterExitTime (Λ ω) ρ} fun ε => {ω |
        ∀ a ∈ cellVertices ε (S.η ω) (Λ ω t),
          δ < infDist (vertexPoint ε (S.η ω) a)
            (frontier (fillCells ε (S.η ω) (cellVertices ε (S.η ω) (Λ ω t)))) →
          s ≤ ‖vertexPoint ε (S.η ω) a‖ →
          c ω / ε ≤ matedLeastSupersolution (S.mult ε ω) ε (S.η ω) ρ t a +
            t / ε * greenKernel (S.mult ε ω) (ballInterior ε (S.η ω) ρ) 0 a} := by
  have := hS.isProbabilityMeasure
  have hm0 : 0 < S.m₀ := MatedCRTEnv.IsValid.m₀_pos hγ hγ2 hS
  have hc0 : 0 < S.c₀ / 6 := by
    unfold MatedCRTEnv.c₀
    exact div_pos (div_pos (by norm_num) hm0) (by norm_num)
  obtain ⟨C, hC1, hCS⟩ := hmeps γ hγ hγ2
  obtain ⟨ε₀, hε₀, hmεb⟩ := hCS Ω S hS
  set cp : Ω → ℝ := fun _ => 1 with hcpdef
  have hcp : Measurable[S.envSigma] cp := measurable_const
  have hcppos : ∀ ω, 0 < cp ω := fun _ => one_pos
  have hGeoE := hgeo γ hγ hγ2 ρ hρ hρ1 Ω S hS Λ hΛ δ t (s / 2) hδ ht (half_pos hs)
  have hsA0 : 0 < min (s / 2) (ρ / 2) := lt_min (half_pos hs) (half_pos hρ)
  have hsAle : min (s / 2) (ρ / 2) ≤ s / 2 := min_le_left _ _
  obtain ⟨Mhat, hMhatMeas, hMhatAe⟩ := hmeas γ hγ hγ2 ρ hρ hρ1 Ω S hS Λ hΛ (δ / 2) (min (s / 2) (ρ / 2)) t
    (half_pos hδ) hsA0 ht
  have hgapE := hgap γ hγ hγ2 ρ hρ hρ1 Ω S hS Λ hΛ t ht
  set sA : ℝ := min (s / 2) (ρ / 2) with hsA
  -- the raw margin `cinf` is used only through its a.s. agreement with the measurable version `Mhat` on `{t < T}`
  set cinf : Ω → ℝ := fun ω => ⨅ x : {x : ℂ | x ∈ Λ ω t ∧ sA ≤ ‖x‖ ∧ δ / 2 ≤ infDist x (Λ ω t)ᶜ},
    (HarmonicBalls.leastSupersolution (S.μ ω) ρ 0 t (x : ℂ) +
      t * HarmonicBalls.greenFunction (ball 0 ρ) 0 (x : ℂ)) with hcinf
  set cpos : Ω → ℝ := fun ω => if 0 < Mhat ω then Mhat ω else 1 with hcposdef
  have hcpos_meas : Measurable[S.envSigma] cpos :=
    Measurable.ite (measurableSet_lt measurable_const hMhatMeas) hMhatMeas measurable_const
  have hcpos_pos : ∀ ω, 0 < cpos ω := fun ω => by
    simp only [hcposdef]
    split_ifs with h
    · exact h
    · exact one_pos
  have hcpos_ae : AEMeasurable cpos S.P := hS.aemeasurable_of_envSigma hcpos_meas
  set c : ℝ := S.c₀ / 6 with hcdef
  set cfin : Ω → ℝ := fun ω => min (cp ω) (c * cpos ω / (2 * C)) with hcfin
  have hcfin_meas : Measurable[S.envSigma] cfin :=
    Measurable.min hcp ((measurable_const.mul hcpos_meas).div_const _)
  have hcfin_pos : ∀ ω, 0 < cfin ω := fun ω =>
    lt_min (hcppos ω) (div_pos (mul_pos hc0 (hcpos_pos ω)) (by linarith))
  have hgood : ∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω) ∧ IsAreaParametrized (S.μ ω) (S.η ω) ∧
      (∀ ε : ℝ, 0 < ε → vertexOf ε (S.η ω) 0 = 0) ∧ Tendsto (S.η ω) (cocompact ℝ) (cocompact ℂ) ∧
      (t < clusterExitTime (Λ ω) ρ → Λ ω t ⊆ HarmonicBalls.cluster (S.μ ω) ρ 0 t) ∧
      (t < clusterExitTime (Λ ω) ρ → Mhat ω = cinf ω) :=
    hΛ.and (hS.isAreaParametrized.and ((MatedCRTEnv.IsValid.ae_vertexOf_zero_eq_zero hS).and
      ((MatedCRTEnv.IsValid.ae_tendsto_cocompact hS).and (hgapE.and hMhatAe))))
  set Good : Set Ω := {ω | IsConeHarmonicBallFamily (S.μ ω) (Λ ω) ∧ IsAreaParametrized (S.μ ω) (S.η ω) ∧
    (∀ ε : ℝ, 0 < ε → vertexOf ε (S.η ω) 0 = 0) ∧ Tendsto (S.η ω) (cocompact ℝ) (cocompact ℂ) ∧
    (t < clusterExitTime (Λ ω) ρ → Λ ω t ⊆ HarmonicBalls.cluster (S.μ ω) ρ 0 t) ∧
    (t < clusterExitTime (Λ ω) ρ → Mhat ω = cinf ω)} with hGooddef
  have hGoodnull : S.P Goodᶜ = 0 := ae_iff.1 hgood
  set Pole : ℝ → Set Ω := fun _ => Set.univ with hPoledef
  have hPoleE : TendsToOneOn S.P {ω | t < clusterExitTime (Λ ω) ρ} Pole := by
    unfold TendsToOneOn
    simp only [hPoledef, Set.compl_univ, Set.inter_empty, measure_empty]
    exact tendsto_const_nhds
  set Geo : ℝ → Set Ω := fun ε => {ω | ∀ a ∈ cellVertices ε (S.η ω) (Λ ω t),
      δ < infDist (vertexPoint ε (S.η ω) a)
        (frontier (fillCells ε (S.η ω) (cellVertices ε (S.η ω) (Λ ω t)))) →
      ∀ x ∈ cell ε (S.η ω) a, δ / 2 ≤ infDist x (Λ ω t)ᶜ ∧ dist x (vertexPoint ε (S.η ω) a) < s / 2} with hGeodef
  set E : ℝ → Set Ω := fun ε => {ω | ∀ a ∈ cellVertices ε (S.η ω) (Λ ω t),
      δ < infDist (vertexPoint ε (S.η ω) a)
        (frontier (fillCells ε (S.η ω) (cellVertices ε (S.η ω) (Λ ω t)))) →
      s ≤ ‖vertexPoint ε (S.η ω) a‖ →
      cfin ω / ε ≤ matedLeastSupersolution (S.mult ε ω) ε (S.η ω) ρ t a +
        t / ε * greenKernel (S.mult ε ω) (ballInterior ε (S.η ω) ρ) 0 a} with hEdef
  -- the annulus of Lemma 3.3 and the sets of the convergence events
  have hO_pos : 0 < min sA (ρ / 2) := lt_min hsA0 (half_pos hρ)
  have hOsub : {y : ℂ | y ∈ ball (0 : ℂ) ρ ∧ min sA (ρ / 2) ≤ ‖y‖} ⊆ closedBall (0 : ℂ) ρ \ {0} := by
    intro y hy
    refine ⟨ball_subset_closedBall hy.1, fun h => ?_⟩
    rw [mem_singleton_iff] at h
    have hy2 := hy.2
    rw [h, norm_zero] at hy2
    exact absurd hy2 (not_le.2 hO_pos)
  have hOinf : 0 < infDist (0 : ℂ) {y : ℂ | y ∈ ball (0 : ℂ) ρ ∧ min sA (ρ / 2) ≤ ‖y‖} := by
    have hy0 : (((min sA (ρ / 2)) : ℝ) : ℂ) ∈ {y : ℂ | y ∈ ball (0 : ℂ) ρ ∧ min sA (ρ / 2) ≤ ‖y‖} :=
      ⟨mem_ball_zero_iff.2 (by
          rw [Complex.norm_real, Real.norm_of_nonneg hO_pos.le]
          linarith [min_le_right sA (ρ / 2)]),
        le_of_eq (by rw [Complex.norm_real, Real.norm_of_nonneg hO_pos.le])⟩
    have hle : min sA (ρ / 2) ≤ infDist (0 : ℂ) {y : ℂ | y ∈ ball (0 : ℂ) ρ ∧ min sA (ρ / 2) ≤ ‖y‖} :=
      (Metric.le_infDist ⟨_, hy0⟩).2 fun y hy => by
        rw [dist_zero_left]
        exact hy.2
    linarith
  -- the probability of the convergence events at the errors `δ0`, `δ1` (chosen from the level `κ`)
  have hlev : ∀ κ : ℝ, 0 < κ → ∃ B₁ B₂ : ℝ → Set Ω,
      Tendsto (fun ε => S.P ({ω | t < clusterExitTime (Λ ω) ρ} ∩ B₁ ε)) (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
      Tendsto (fun ε => S.P ({ω | t < clusterExitTime (Λ ω) ρ} ∩ B₂ ε)) (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ ω ∈ {ω | t < clusterExitTime (Λ ω) ρ} ∩ Pole ε ∩ Geo ε ∩ Good,
        ω ∉ B₁ ε → ω ∉ B₂ ε → κ < cpos ω → ω ∈ E ε := by
    intro κ hκ
    set δ0 : ℝ := c * κ / 4 with hδ0def
    set δ1 : ℝ := c * κ / 4 / (1 + t) with hδ1def
    have hδ0pos : 0 < δ0 := div_pos (mul_pos hc0 hκ) (by norm_num)
    have hδ1pos : 0 < δ1 := div_pos (div_pos (mul_pos hc0 hκ) (by norm_num)) (by linarith)
    have htδ1 : t * δ1 ≤ c * κ / 4 := by
      have e : t * δ1 = c * κ / 4 * (t / (1 + t)) := by
        rw [hδ1def]
        ring
      rw [e]
      exact mul_le_of_le_one_right (div_nonneg (mul_nonneg hc0.le hκ.le) (by norm_num))
        ((div_le_one (by linarith)).2 (by linarith))
    refine ⟨fun ε => {ω | t < clusterExitTime (Λ ω) ρ ∧ ∃ x ∈ ball (0 : ℂ) ρ,
        δ0 < |rescaledMatedLeastSupersolution S ρ t ε ω x -
          S.c₀ / 6 * HarmonicBalls.leastSupersolution (S.μ ω) ρ 0 t x|},
      fun ε => {ω | ¬ ∀ x ∈ {y : ℂ | y ∈ ball (0 : ℂ) ρ ∧ min sA (ρ / 2) ≤ ‖y‖},
        |rescale (S.mε ε) ε (S.η ω) (fun a => ε⁻¹ *
          greenKernel (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball 0 ρ)) (vertexOf ε (S.η ω) 0) a) x -
          c * HarmonicBalls.greenFunction (ball 0 ρ) 0 x| ≤ δ1}, ?_, ?_, ?_⟩
    · have hB1 := h41 γ hγ hγ2 ρ hρ hρ1 Ω S hS Λ hΛ t ht δ0 hδ0pos
      exact Tendsto.congr (fun ε => congrArg S.P (Set.inter_eq_right.2 (fun ω hω => hω.1)).symm) hB1
    · have hP33 := h33 γ hγ hγ2 ρ hρ hρ1 Ω S hS ρ 0 0 hρ subset_rfl (mem_ball_self hρ) δ1 hδ1pos _ hOsub hOinf
      refine ENNReal.tendsto_nhds_zero.2 fun η hη => ?_
      filter_upwards [ENNReal.tendsto_nhds_zero.1 hP33 η hη] with ε hε
      exact le_trans (measure_mono Set.inter_subset_right) hε
    · filter_upwards [Ioo_mem_nhdsGT hε₀] with ε hε
      intro ω hω h1 h2 hκω
      obtain ⟨⟨⟨hF, -⟩, hGe⟩, hGω⟩ := hω
      obtain ⟨hΛω, hηω, hv0ω, hcocω, hclω, hMω⟩ := hGω
      have hT : t < clusterExitTime (Λ ω) ρ := hF
      have hε0 : 0 < ε := hε.1
      have hmεb' := hmεb ε hε.1 hε.2
      have hmpos : 0 < S.mε ε := lt_of_lt_of_le (mul_pos (inv_pos.2 (by linarith)) (inv_pos.2 hε0)) hmεb'.1
      have hΛt : Λ ω t ⊆ ball 0 (ρ / 3) :=
        IDLALowerBound.subset_ball_div_three_of_lt_clusterExitTime hΛω.2.1.monotoneOn ht hT
      obtain ⟨-, hcont, -⟩ := hΛω.2.2 t (ρ / 3) ht (by linarith) hΛt ρ (by linarith)
      have hGe' : ∀ a ∈ cellVertices ε (S.η ω) (Λ ω t),
          δ < infDist (vertexPoint ε (S.η ω) a)
            (frontier (fillCells ε (S.η ω) (cellVertices ε (S.η ω) (Λ ω t)))) →
          ∀ x ∈ cell ε (S.η ω) a, δ / 2 ≤ infDist x (Λ ω t)ᶜ ∧ dist x (vertexPoint ε (S.η ω) a) < s / 2 := by
        have hg := hGe
        simp only [hGeodef, Set.mem_ofPred_eq] at hg
        exact hg
      simp only [hEdef, Set.mem_ofPred_eq]
      intro a ha hδa hsa'
      obtain ⟨x, hxcell, hxa⟩ := exists_vertexOf_eq_of_area_parametrized hηω hcocω hε0 a
      obtain ⟨hdx, hdist⟩ := hGe' a ha hδa x hxcell
      have hxΛ : x ∈ Λ ω t := by
        by_contra hn
        have h0 : infDist x (Λ ω t)ᶜ = 0 := Metric.infDist_zero_of_mem (mem_compl hn)
        linarith
      have hxcl : x ∈ HarmonicBalls.cluster (S.μ ω) ρ 0 t := hclω hT hxΛ
      have hxball : x ∈ ball (0 : ℂ) ρ := hxcl.1
      have hxsA : sA ≤ ‖x‖ := by
        have h1' : ‖vertexPoint ε (S.η ω) a‖ - ‖x‖ ≤ dist x (vertexPoint ε (S.η ω) a) := by
          rw [dist_comm, dist_eq_norm]
          exact norm_sub_norm_le _ _
        linarith
      obtain ⟨c1, hc1pos, hc1⟩ := exists_pos_lower_surplus hρ hsA0 (half_pos hδ) (hclω hT) hcont
      have hKne : ({x : ℂ | x ∈ Λ ω t ∧ sA ≤ ‖x‖ ∧ δ / 2 ≤ infDist x (Λ ω t)ᶜ}).Nonempty :=
        ⟨x, hxΛ, hxsA, hdx⟩
      have : Nonempty {x : ℂ | x ∈ Λ ω t ∧ sA ≤ ‖x‖ ∧ δ / 2 ≤ infDist x (Λ ω t)ᶜ} := hKne.to_subtype
      have hbdd : ∀ y : {x : ℂ | x ∈ Λ ω t ∧ sA ≤ ‖x‖ ∧ δ / 2 ≤ infDist x (Λ ω t)ᶜ},
          c1 ≤ HarmonicBalls.leastSupersolution (S.μ ω) ρ 0 t (y : ℂ) +
            t * HarmonicBalls.greenFunction (ball 0 ρ) 0 (y : ℂ) := by
        intro y
        obtain ⟨hyΛ, hysA, hyd⟩ := y.2
        exact hc1 _ hyΛ hysA hyd
      have hcinf_ge : c1 ≤ cinf ω := le_ciInf hbdd
      have hcinf_le : cinf ω ≤ HarmonicBalls.leastSupersolution (S.μ ω) ρ 0 t x +
          t * HarmonicBalls.greenFunction (ball 0 ρ) 0 x :=
        ciInf_le ⟨c1, by rintro _ ⟨y, rfl⟩; exact hbdd y⟩ (⟨x, hxΛ, hxsA, hdx⟩ :
          {x : ℂ | x ∈ Λ ω t ∧ sA ≤ ‖x‖ ∧ δ / 2 ≤ infDist x (Λ ω t)ᶜ})
      have hMhatEq : Mhat ω = cinf ω := hMω hT
      have hpos' : 0 < cinf ω := lt_of_lt_of_le hc1pos hcinf_ge
      have hcpos_eq : cpos ω = cinf ω := by simp [hcposdef, hMhatEq, hpos']
      have hκc : κ < cinf ω := by
        rw [← hcpos_eq]
        exact hκω
      have hW : ∀ y ∈ ball (0 : ℂ) ρ, |rescale (S.mε ε) ε (S.η ω)
          (matedLeastSupersolution (S.mult ε ω) ε (S.η ω) ρ t) y -
          c * HarmonicBalls.leastSupersolution (S.μ ω) ρ 0 t y| ≤ δ0 := by
        intro y hy
        by_contra hlt
        exact h1 ⟨hF, y, hy, not_le.1 hlt⟩
      have hG : ∀ y ∈ ball (0 : ℂ) ρ, sA ≤ ‖y‖ → |rescale (S.mε ε) ε (S.η ω) (fun b => ε⁻¹ *
          greenKernel (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball 0 ρ)) (vertexOf ε (S.η ω) 0) b) y -
          c * HarmonicBalls.greenFunction (ball 0 ρ) 0 y| ≤ δ1 := by
        intro y hy hyO
        exact not_not.1 h2 y ⟨hy, (min_le_left _ _).trans hyO⟩
      have hbound := interior_vertex_bound (μ := S.μ ω) (η := S.η ω) (m := S.mult ε ω) (ε := ε)
        (ρ := ρ) (t := t) (s := sA) (c := c) (c1 := cinf ω) (δ := δ0) (δ' := δ1) (mε := S.mε ε)
        ht hc0.le hmpos (hv0ω ε hε0) hW hG hxball hxsA hcinf_le
      rw [hxa] at hbound
      have hkey : c * cinf ω / 2 ≤ c * cinf ω - δ0 - t * δ1 := by
        have hcκ : c * κ ≤ c * cinf ω := mul_le_mul_of_nonneg_left hκc.le hc0.le
        linarith
      have hc2 : 0 ≤ c * cinf ω / 2 :=
        div_nonneg (mul_nonneg hc0.le (le_trans hc1pos.le hcinf_ge)) (by norm_num)
      have h3 : C⁻¹ * ε⁻¹ * (c * cinf ω / 2) ≤ S.mε ε * (c * cinf ω - δ0 - t * δ1) :=
        mul_le_mul hmεb'.1 hkey hc2 hmpos.le
      have hcf : cfin ω ≤ c * cinf ω / (2 * C) := (min_le_right _ _).trans (by rw [hcpos_eq])
      have h4 : cfin ω / ε ≤ C⁻¹ * ε⁻¹ * (c * cinf ω / 2) := by
        calc cfin ω / ε ≤ (c * cinf ω / (2 * C)) / ε := div_le_div_of_nonneg_right hcf hε0.le
          _ = C⁻¹ * ε⁻¹ * (c * cinf ω / 2) := by ring
      exact le_trans h4 (le_trans h3 hbound)
  refine ⟨cfin, hcfin_meas, hcfin_pos, ?_⟩
  exact tendsToOneOn_of_levels S.P {ω | t < clusterExitTime (Λ ω) ρ} Good hGoodnull cpos hcpos_ae hcpos_pos
    E Pole Geo hPoleE hGeoE hlev


/-- A function `x ↦ f (N x) x` with measurable `f n` for every `n` and measurable `N : α → ℕ` is measurable. -/
theorem measurable_comp_nat {α : Type*} {m : MeasurableSpace α} {f : ℕ → α → ℝ} (hf : ∀ n, Measurable[m] (f n))
    {N : α → ℕ} (hN : Measurable[m] N) : Measurable[m] fun x => f (N x) x := by
  intro s hs
  have h : (fun x => f (N x) x) ⁻¹' s = ⋃ n, N ⁻¹' {n} ∩ f n ⁻¹' s := by
    ext x
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_singleton_iff]
    refine ⟨fun h => ⟨N x, rfl, h⟩, fun ⟨n, hn, h⟩ => ?_⟩
    rw [hn]
    exact h
  rw [h]
  exact MeasurableSet.iUnion fun n => (hN (measurableSet_singleton n)).inter (hf n hs)

/-- For `K, t > 0` and `n`, the radius `r = min(ρ/6, (ρ/2) e^{-K(1 + (K n + 1)/t)})` satisfies the condition
`t (K⁻¹ log(ρ/(2r)) - 1) - K n ≥ 1` of `stoppedPoleLowerBound`. -/
theorem one_le_of_poleRadius {K t ρ : ℝ} (hK : 0 < K) (ht : 0 < t) (hρ : 0 < ρ) (n : ℕ) :
    1 ≤ t * (K⁻¹ * Real.log (ρ / (2 * min (ρ / 6) (ρ / 2 * Real.exp (-(K * (1 + (K * n + 1) / t)))))) - 1) -
      K * n := by
  obtain ⟨A, hA⟩ : ∃ A, A = K * (1 + (K * n + 1) / t) := ⟨_, rfl⟩
  rw [← hA]
  obtain ⟨r, hr⟩ : ∃ r, r = min (ρ / 6) (ρ / 2 * Real.exp (-A)) := ⟨_, rfl⟩
  rw [← hr]
  have hrpos : 0 < r := by rw [hr]; exact lt_min (by linarith) (by positivity)
  have hle : r ≤ ρ / 2 * Real.exp (-A) := by rw [hr]; exact min_le_right _ _
  have hlog : A ≤ Real.log (ρ / (2 * r)) := by
    rw [Real.le_log_iff_exp_le (by positivity), le_div_iff₀ (by positivity)]
    calc Real.exp A * (2 * r) ≤ Real.exp A * (2 * (ρ / 2 * Real.exp (-A))) := by gcongr
      _ = ρ * (Real.exp A * Real.exp (-A)) := by ring
      _ = ρ := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
  have h1 : 1 + (K * n + 1) / t ≤ K⁻¹ * Real.log (ρ / (2 * r)) := by
    rw [le_inv_mul_iff₀ hK, ← hA]
    exact hlog
  have h2 : t * ((K * n + 1) / t) = K * n + 1 := by field_simp
  have h3 := mul_le_mul_of_nonneg_left
    (show (K * n + 1) / t ≤ K⁻¹ * Real.log (ρ / (2 * r)) - 1 by linarith) ht.le
  linarith

/-- **The pole step `StoppedSurplusPoleStep`** from the strict obstacle gap, the geometry and margin
steps, the scaling of the expected exit time, Theorem 4.1 and Lemmas 3.3, 2.16 and 2.18. The cutoff is `s = ρ/6`
and the constant `c = min 1 c_N` with `N = ⌈𝓜⌉`. -/
theorem stoppedSurplusPole_of_steps (𝒮 : SpaceFillingSLEModel) (hgap : HarmonicBallStrictObstacleGapStep 𝒮)
    (hgeo : StoppedInteriorGeometryStep 𝒮) (hmeas : StoppedInteriorMeasurableStep 𝒮)
    (hmeps : MepsScalingInput 𝒮) (h41 : ConvergenceDivisibleStmt 𝒮) (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    (h216 : GreenKernelLowerBoundStmt 𝒮) (h218 : ExitTimeUpperBoundStmt 𝒮) :
    StoppedSurplusPoleStep 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS Λ hΛ δ t hδ _ ht
  have := hS.isProbabilityMeasure
  obtain ⟨K, hK, hpole⟩ := stoppedPoleLowerBound_tendsToOneOn h216 h218 hγ hγ2 hρ hρ1
  obtain ⟨r, hrdef⟩ : ∃ r : ℕ → ℝ,
      r = fun n : ℕ => min (ρ / 6) (ρ / 2 * Real.exp (-(K * (1 + (K * (n : ℝ) + 1) / t)))) := ⟨_, rfl⟩
  have hr : ∀ n, 0 < r n := fun n => by rw [hrdef]; exact lt_min (by linarith) (by positivity)
  have hr6 : ∀ n, r n ≤ ρ / 6 := fun n => by rw [hrdef]; exact min_le_left _ _
  have hrK : ∀ n : ℕ, 1 ≤ t * (K⁻¹ * Real.log (ρ / (2 * r n)) - 1) - K * n := fun n => by
    rw [hrdef]; exact one_le_of_poleRadius hK ht hρ n
  choose c hcm hcpos hann using fun n : ℕ => stoppedSurplusAnnulus_of_gap 𝒮 hgap hgeo hmeas hmeps h41 h33
    γ hγ hγ2 ρ hρ hρ1 Ω S hS Λ hΛ δ t hδ ht (r n) (hr n)
  -- the random index from a measurable version of `μ_h`
  obtain ⟨g, hgm, hgae⟩ := frozenLQGMeasureFieldMeasurable_holds 𝒮 γ hγ hγ2 Ω S hS
  have hge : Measurable[S.envSigma] g := hgm.mono (show S.fieldSigma ≤ S.envSigma from le_sup_left) le_rfl
  obtain ⟨Mv, hMvdef⟩ : ∃ Mv : Ω → ℝ,
      Mv = fun ω => (largestExitTimeRV (g ω) (ball 0 ((1 + ρ) / 2))).toReal := ⟨_, rfl⟩
  have hMm : Measurable[S.envSigma] Mv := by
    rw [hMvdef]
    exact ((measurable_largestExitTimeRV_ball_measure _).comp hge).ennreal_toReal
  have hNm : Measurable[S.envSigma] fun ω => ⌈Mv ω⌉₊ := Nat.measurable_ceil.comp hMm
  have hcfm : Measurable[S.envSigma] fun ω => min 1 (c ⌈Mv ω⌉₊ ω) :=
    Measurable.min measurable_const (measurable_comp_nat hcm hNm)
  refine ⟨ρ / 6, by linarith, fun ω => min 1 (c ⌈Mv ω⌉₊ ω), hcfm, fun ω => lt_min one_pos (hcpos _ ω), ?_⟩
  -- the null set and the tail of the index
  obtain ⟨q, -, h217⟩ := firstPass_2_17 FirstPass.Derived.volumeGrowthStmt_holds γ hγ hγ2
  have hfin := (h217 ((3 + ρ) / 4) (by linarith) (by linarith) Ω S.P S.hC S.hcirc S.μ hS.isConeField).1
  have hgood : ∀ᵐ ω ∂S.P, S.μ ω = g ω ∧ largestExitTimeRV (S.μ ω) (ball 0 ((1 + ρ) / 2)) < ⊤ := by
    filter_upwards [hgae, hfin] with ω h1 h2
    refine ⟨h1, lt_of_le_of_lt ?_ h2⟩
    exact le_iSup₂_of_le (f := fun (D : Set ℂ) (_ : D ⊆ ball 0 ((3 + ρ) / 4)) => largestExitTimeRV (S.μ ω) D)
      (ball 0 ((1 + ρ) / 2)) (ball_subset_ball (by linarith)) le_rfl
  have hnull : S.P {ω | ¬ (S.μ ω = g ω ∧ largestExitTimeRV (S.μ ω) (ball 0 ((1 + ρ) / 2)) < ⊤)} = 0 :=
    ae_iff.1 hgood
  have htail : Tendsto (fun n : ℕ => S.P {ω | (n : ℝ) < Mv ω}) atTop (𝓝 0) := by
    have hMae : AEMeasurable Mv S.P := hS.aemeasurable_of_envSigma hMm
    have h := tendsto_measure_iInter_atTop (μ := S.P) (s := fun n : ℕ => {ω | (n : ℝ) < Mv ω})
      (fun n => hMae.nullMeasurable measurableSet_Ioi)
      (fun m n hmn ω hω => show (m : ℝ) < Mv ω from
        lt_of_le_of_lt (Nat.cast_le.2 hmn) (show (n : ℝ) < Mv ω from hω)) ⟨0, measure_ne_top _ _⟩
    have hempty : (⋂ n : ℕ, {ω | (n : ℝ) < Mv ω}) = ∅ := by
      ext ω
      simp only [Set.mem_iInter, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      obtain ⟨n, hn⟩ := exists_nat_ge (Mv ω)
      exact absurd (h n) (not_lt.2 hn)
    rw [hempty, measure_empty] at h
    exact h
  -- the two estimates for each index
  have hP : ∀ n : ℕ, Tendsto (fun ε => S.P
      ({ω | largestExitTimeRV (S.μ ω) (ball 0 ((1 + ρ) / 2)) ≤ ENNReal.ofReal n} ∩
        {ω | ∀ a : ℤ, ‖vertexPoint ε (S.η ω) a‖ < r n →
          1 / ε ≤ matedLeastSupersolution (S.mult ε ω) ε (S.η ω) ρ t a +
            t / ε * greenKernel (S.mult ε ω) (ballInterior ε (S.η ω) ρ) 0 a}ᶜ)) (𝓝[>] 0) (𝓝 0) :=
    fun n => hpole Ω S hS t n (r n) ht (Nat.cast_nonneg n) (hr n) (hr6 n) (hrK n)
  have hA : ∀ n : ℕ, Tendsto (fun ε => S.P ({ω | t < clusterExitTime (Λ ω) ρ} ∩
      {ω | ∀ a ∈ cellVertices ε (S.η ω) (Λ ω t),
        δ < infDist (vertexPoint ε (S.η ω) a)
          (frontier (fillCells ε (S.η ω) (cellVertices ε (S.η ω) (Λ ω t)))) →
        r n ≤ ‖vertexPoint ε (S.η ω) a‖ →
        c n ω / ε ≤ matedLeastSupersolution (S.mult ε ω) ε (S.η ω) ρ t a +
          t / ε * greenKernel (S.mult ε ω) (ballInterior ε (S.η ω) ρ) 0 a}ᶜ)) (𝓝[>] 0) (𝓝 0) :=
    fun n => hann n
  unfold TendsToOneOn
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  have hη2 : (0 : ℝ≥0∞) < η / 2 := ENNReal.div_pos_iff.2 ⟨hη.ne', by norm_num⟩
  obtain ⟨N₀, hN₀⟩ := (ENNReal.tendsto_nhds_zero.1 htail (η / 2) hη2).exists
  have hsum := tendsto_finsetSum (Finset.range (N₀ + 1)) (fun n _ => (hP n).add (hA n))
  simp only [add_zero, Finset.sum_const_zero] at hsum
  filter_upwards [self_mem_nhdsWithin, ENNReal.tendsto_nhds_zero.1 hsum (η / 2) hη2] with ε hεpos hε
  have hεpos' : 0 < ε := hεpos
  have hsub : {ω | t < clusterExitTime (Λ ω) ρ} ∩ {ω | ∀ a ∈ cellVertices ε (S.η ω) (Λ ω t),
        δ < infDist (vertexPoint ε (S.η ω) a)
          (frontier (fillCells ε (S.η ω) (cellVertices ε (S.η ω) (Λ ω t)))) →
        ‖vertexPoint ε (S.η ω) a‖ < ρ / 6 →
        min 1 (c ⌈Mv ω⌉₊ ω) / ε ≤ matedLeastSupersolution (S.mult ε ω) ε (S.η ω) ρ t a +
          t / ε * greenKernel (S.mult ε ω) (ballInterior ε (S.η ω) ρ) 0 a}ᶜ ⊆
      ({ω | (N₀ : ℝ) < Mv ω} ∪
        (⋃ n ∈ Finset.range (N₀ + 1),
          (({ω | largestExitTimeRV (S.μ ω) (ball 0 ((1 + ρ) / 2)) ≤ ENNReal.ofReal n} ∩
            {ω | ∀ a : ℤ, ‖vertexPoint ε (S.η ω) a‖ < r n →
              1 / ε ≤ matedLeastSupersolution (S.mult ε ω) ε (S.η ω) ρ t a +
                t / ε * greenKernel (S.mult ε ω) (ballInterior ε (S.η ω) ρ) 0 a}ᶜ) ∪
          ({ω | t < clusterExitTime (Λ ω) ρ} ∩
            {ω | ∀ a ∈ cellVertices ε (S.η ω) (Λ ω t),
              δ < infDist (vertexPoint ε (S.η ω) a)
                (frontier (fillCells ε (S.η ω) (cellVertices ε (S.η ω) (Λ ω t)))) →
              r n ≤ ‖vertexPoint ε (S.η ω) a‖ →
              c n ω / ε ≤ matedLeastSupersolution (S.mult ε ω) ε (S.η ω) ρ t a +
                t / ε * greenKernel (S.mult ε ω) (ballInterior ε (S.η ω) ρ) 0 a}ᶜ)))) ∪
        {ω | ¬ (S.μ ω = g ω ∧ largestExitTimeRV (S.μ ω) (ball 0 ((1 + ρ) / 2)) < ⊤)} := by
    rintro ω ⟨hF, hE⟩
    by_cases hg : S.μ ω = g ω ∧ largestExitTimeRV (S.μ ω) (ball 0 ((1 + ρ) / 2)) < ⊤
    swap
    · exact Or.inr hg
    by_cases hN : (N₀ : ℝ) < Mv ω
    · exact Or.inl (Or.inl hN)
    refine Or.inl (Or.inr ?_)
    have hn : ⌈Mv ω⌉₊ ≤ N₀ := Nat.ceil_le.2 (not_lt.1 hN)
    rw [Set.mem_iUnion₂]
    refine ⟨⌈Mv ω⌉₊, Finset.mem_range.2 (Nat.lt_succ_of_le hn), ?_⟩
    by_contra hcon
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff, not_or, not_and, not_not] at hcon
    obtain ⟨h1, h2⟩ := hcon
    have hB : largestExitTimeRV (S.μ ω) (ball 0 ((1 + ρ) / 2)) ≤ ENNReal.ofReal (⌈Mv ω⌉₊ : ℝ) := by
      rw [ENNReal.le_ofReal_iff_toReal_le hg.2.ne (Nat.cast_nonneg _), hg.1]
      have hMv : Mv ω = (largestExitTimeRV (g ω) (ball 0 ((1 + ρ) / 2))).toReal := by rw [hMvdef]
      rw [← hMv]
      exact Nat.le_ceil _
    have hPo := h1 hB
    have hAn := h2 hF
    apply hE
    intro a ha hδa _
    by_cases har : ‖vertexPoint ε (S.η ω) a‖ < r ⌈Mv ω⌉₊
    · exact le_trans (div_le_div_of_nonneg_right (min_le_left _ _) hεpos'.le) (hPo a har)
    · exact le_trans (div_le_div_of_nonneg_right (min_le_right _ _) hεpos'.le)
        (hAn a ha hδa (not_lt.1 har))
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  rw [hnull, add_zero]
  refine (measure_union_le _ _).trans ?_
  refine (add_le_add hN₀ ((measure_biUnion_finset_le _ _).trans
    (Finset.sum_le_sum fun n _ => measure_union_le _ _))).trans ?_
  exact (add_le_add le_rfl hε).trans (ENNReal.add_halves η).le

end StoppedInterior

end MatedCRT

/-! ## Audit -/
#print axioms MatedCRT.StoppedInterior.stoppedSurplusAnnulus_of_gap
#print axioms MatedCRT.StoppedInterior.stoppedSurplusPole_of_steps
