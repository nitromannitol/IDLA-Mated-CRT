import MatedCRT.FirstPass.Derived.GMS21UniformStartOfAnnulus

/-!
# The uniform-start invariance principle from the comparison on annuli at the vertices

In the proof of Gwynne–Miller–Sheffield (arXiv:1705.11161), Theorem 3.4, case 1, the comparison of the embedded walk
with Brownian motion on annuli `B_R(0) \ closedBall 0 α` is transferred from the `0`-quantum cone to the `γ`-quantum
cone by Lemma 3.3, which compares the laws of the local cell configurations. A good set that is a function of the local
cell configuration is the comparison at the vertices: for every vertex `x` whose point `η(ε x)` lies in
`closedBall 0 ρ \ B_b(0)`, the walk from `x` and Brownian motion from `η(ε x)`, both stopped at their exits from the
annulus, have laws at Lévy–Prokhorov distance less than `c` (`vertexAnnulusLPData`). It contains the good set for all
starts in the cells (`annulusSelectedLPData_subset_vertexAnnulusLPData`).

This file proves that the comparison at the vertices on annuli already gives the uniform-start comparison on balls
required by the reference-environment route (`tendsto_uniformStartSelectedLPData_of_vertexAnnulus`): the passage from
the annulus to the ball (`GMS21BallOfAnnulus`) applied with the one-point cells `{η(ε x)}` gives the comparison on
`B_R(0)` from every vertex of `closedBall 0 ρ'`, and a start `z` in the cell of `x` is within the cell diameter of
`η(ε x)`, where the law of Brownian motion stopped at its exit from `B_R(0)` is uniformly continuous in the start on
`closedBall 0 ρ'` (`exists_uniform_levyProkhorovEDist_planarBrownianMotion_stoppedExitCurve_lt`).

## Main results

* `vertexAnnulusLPData`: the good set on the annulus at the vertices.
* `annulusSelectedLPData_subset_vertexAnnulusLPData`
* `exists_uniform_levyProkhorovEDist_planarBrownianMotion_stoppedExitCurve_lt`
* `dist_vertexPoint_le_of_mem_cell`: the small-cell condition at rational times bounds the distance from the points of
  a cell to the point of its vertex.
* `tendsto_uniformStartSelectedLPData_of_vertexAnnulus`
-/

set_option autoImplicit false

open MeasureTheory Filter Topology Set Metric HarmonicBalls MarkovProcess
open scoped ENNReal NNReal

namespace MatedCRT

open StopAtExitLevyProkhorov

/-- The good set on the annulus at the vertices at mesh `ε`: for every vertex `x` whose point `η(ε x)` lies in
`closedBall 0 ρ \ B_b(0)`, the laws of the curve classes of the walk of `d.2` from `x`, embedded by `d.1(ε ·)` and
interpolated, and of planar Brownian motion from `η(ε x)`, both stopped at their exits from the annulus
`B_R(0) \ closedBall 0 α`, are at Lévy–Prokhorov distance less than `c`. -/
def vertexAnnulusLPData (ε α b ρ R c : ℝ) : Set (C(ℝ, ℂ) × (ℤ → ℤ → ℕ)) :=
  {d | ∀ x : ℤ, vertexPoint ε d.1 x ∉ ball (0 : ℂ) b → vertexPoint ε d.1 x ∈ closedBall (0 : ℂ) ρ →
    levyProkhorovEDist ((srwLaw d.2 x).map fun w =>
        stoppedExitCurve (ball (0 : ℂ) R \ closedBall (0 : ℂ) α) (interpPathCM (vertexPoint ε d.1) zero_le_one w))
      ((planarBrownianMotion (vertexPoint ε d.1 x)).map
        (stoppedExitCurve (ball (0 : ℂ) R \ closedBall (0 : ℂ) α))) < ENNReal.ofReal c}

/-- The comparison for all starts in the cells contains the comparison at the vertices, since the point of a vertex
lies in its cell. -/
theorem annulusSelectedLPData_subset_vertexAnnulusLPData {ε : ℝ} (hε : 0 < ε) (α b ρ R c : ℝ) :
    annulusSelectedLPData ε α b ρ R c ⊆ vertexAnnulusLPData ε α b ρ R c := by
  intro d hd x hxb hxρ
  exact hd _ hxb hxρ x (mem_cell_vertexPoint hε _ x)

/-- **Uniform continuity of the stopped Brownian class law in the start.** For `ρ < R` and `κ > 0` there is `δ > 0`
such that for all `u, v ∈ closedBall 0 ρ` with `|u - v| < δ`, the laws of the curve classes of planar Brownian motion
from `u` and from `v`, stopped at their exits from `B_R(0)`, are at Lévy–Prokhorov distance less than `κ`. -/
theorem exists_uniform_levyProkhorovEDist_planarBrownianMotion_stoppedExitCurve_lt {ρ R : ℝ} (hρR : ρ < R)
    {κ : ℝ} (hκ : 0 < κ) :
    ∃ δ > 0, ∀ u ∈ closedBall (0 : ℂ) ρ, ∀ v ∈ closedBall (0 : ℂ) ρ, dist u v < δ →
      levyProkhorovEDist ((planarBrownianMotion u).map (stoppedExitCurve (ball (0 : ℂ) R)))
        ((planarBrownianMotion v).map (stoppedExitCurve (ball (0 : ℂ) R))) < ENNReal.ofReal κ := by
  have hprob : ∀ z : ℂ,
      IsProbabilityMeasure ((planarBrownianMotion z).map (stoppedExitCurve (ball (0 : ℂ) R))) := fun z =>
    (Measure.isProbabilityMeasure_map_iff (measurable_stoppedExitCurve _ isOpen_ball).aemeasurable).2
      inferInstance
  let F : ℂ → LevyProkhorov (ProbabilityMeasure (BouRabeeGwynne.CurveSpace 2)) := fun z =>
    LevyProkhorov.ofMeasure ⟨(planarBrownianMotion z).map (stoppedExitCurve (ball (0 : ℂ) R)), hprob z⟩
  have hcont : ContinuousOn F (closedBall (0 : ℂ) ρ) := by
    intro z hz
    have hzR : z ∈ ball (0 : ℂ) R := closedBall_subset_ball hρR hz
    have h : Tendsto F (𝓝 z) (𝓝 (F z)) := tendsto_iff_dist_tendsto_zero.2
      (BrownianClassLawContinuity.tendsto_levyProkhorovDist_planarBrownianMotion_stoppedExitCurve hzR)
    exact ContinuousAt.continuousWithinAt h
  obtain ⟨δ, hδ, H⟩ := Metric.uniformContinuousOn_iff.1
    ((isCompact_closedBall (0 : ℂ) ρ).uniformContinuousOn_of_continuous hcont) κ hκ
  refine ⟨δ, hδ, fun u hu v hv huv => ?_⟩
  have h : levyProkhorovDist ((planarBrownianMotion u).map (stoppedExitCurve (ball (0 : ℂ) R)))
      ((planarBrownianMotion v).map (stoppedExitCurve (ball (0 : ℂ) R))) < κ := H u hu v hv huv
  exact (ENNReal.lt_ofReal_iff_toReal_lt (levyProkhorovEDist_ne_top _ _)).2 h

/-- **Points of a small cell.** If the points of the cells at rational times inside `B_b(0)` lie within distance `L`
of the points of their vertices, then so does every point of a cell inside `B_b(0)`. -/
theorem dist_vertexPoint_le_of_mem_cell {ε b L : ℝ} (hε : 0 < ε) {η : C(ℝ, ℂ)}
    (hdiam : ∀ x : ℤ, ∀ q : ℚ, (q : ℝ) ∈ Icc (ε * (x - 1)) (ε * x) →
      b ≤ ‖η (q : ℝ)‖ ∨ dist (η (ε * x)) (η (q : ℝ)) ≤ L)
    (x : ℤ) {w : ℂ} (hwx : w ∈ cell ε η x) (hwb : w ∈ ball (0 : ℂ) b) :
    dist (vertexPoint ε η x) w ≤ L := by
  obtain ⟨t, ht, rfl⟩ := hwx
  have hcont : Continuous ⇑η := η.continuous
  have hlt : ε * ((x : ℝ) - 1) < ε * x := mul_lt_mul_of_pos_left (by linarith) hε
  have hCc : IsClosed ({s : ℝ | b ≤ ‖η s‖} ∪ {s : ℝ | dist (η (ε * x)) (η s) ≤ L}) :=
    (isClosed_le continuous_const (continuous_norm.comp hcont)).union
      (isClosed_le (continuous_const.dist hcont) continuous_const)
  have hIoo : Ioo (ε * ((x : ℝ) - 1)) (ε * x) ⊆
      {s : ℝ | b ≤ ‖η s‖} ∪ {s : ℝ | dist (η (ε * x)) (η s) ≤ L} :=
    subset_of_rat_mem isOpen_Ioo hCc fun q hq => hdiam x q (Ioo_subset_Icc_self hq)
  have hIcc : Icc (ε * ((x : ℝ) - 1)) (ε * x) ⊆
      {s : ℝ | b ≤ ‖η s‖} ∪ {s : ℝ | dist (η (ε * x)) (η s) ≤ L} := by
    rw [← closure_Ioo hlt.ne]
    exact closure_minimal hIoo hCc
  rcases hIcc ht with h | h
  · exact absurd (mem_ball_zero_iff.1 hwb) (not_lt.2 h)
  · exact h

/-- **The uniform-start invariance principle on balls from the comparison on annuli at the vertices**
(Gwynne–Miller–Sheffield, arXiv:1705.11161, proof of Theorem 3.4, case 1). Let `S` be a valid environment for
`0 < γ < 2` with a measurable continuous version `η₀` of its curve. Suppose that for all `0 < α < b < ρ < R` and
`c > 0`, the law of `(η₀, S.mult (1/n))` gives mass at most `θ` to the complement of the good set at the vertices
`vertexAnnulusLPData (1/n) α b ρ R c` for all large `n`, for every `θ > 0`. Then for all `0 < ρ < R` and `κ, θ > 0`
it gives mass at most `θ` to the complement of `uniformStartSelectedLPData (1/n) ρ R κ` for all large `n`: this is
the premise `hTutteLP` at `S` and `η₀`. -/
theorem tendsto_uniformStartSelectedLPData_of_vertexAnnulus {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    {η₀ : Ω → C(ℝ, ℂ)} (hη₀m : Measurable η₀) (hη₀ : ∀ᵐ ω ∂S.P, ⇑(η₀ ω) = S.η ω)
    (hann : ∀ α b ρ R c : ℝ, 0 < α → α < b → b < ρ → ρ < R → 0 < c → ∀ θ : ℝ, 0 < θ →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        S.P.map (fun ω => (η₀ ω, S.mult (1 / (n : ℝ)) ω))
          (vertexAnnulusLPData (1 / (n : ℝ)) α b ρ R c)ᶜ ≤ ENNReal.ofReal θ) :
    ∀ R ρ : ℝ, 0 < ρ → ρ < R → ∀ κ : ℝ, 0 < κ → ∀ θ : ℝ, 0 < θ →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        S.P.map (fun ω => (η₀ ω, S.mult (1 / (n : ℝ)) ω))
          (uniformStartSelectedLPData (1 / (n : ℝ)) ρ R κ)ᶜ ≤ ENNReal.ofReal θ := by
  intro R ρ hρ hρR κ hκ θ hθ
  have hP := hS.isProbabilityMeasure
  set ρ₁ : ℝ := (ρ + R) / 2 with hρ₁
  have hρρ₁ : ρ < ρ₁ := by linarith
  have hρ₁R : ρ₁ < R := by linarith
  obtain ⟨δ, hδ, hU⟩ :=
    exists_uniform_levyProkhorovEDist_planarBrownianMotion_stoppedExitCurve_lt hρ₁R (half_pos hκ)
  obtain ⟨α, b, L, c, hα, hαb, hL, hbLR, hc, H⟩ :=
    exists_forall_levyProkhorovEDist_walk_ball_lt (hρ.trans hρR) (half_pos hκ)
  set ρ' : ℝ := max ρ₁ (b + 2 * L)
  have hbρ' : b + 2 * L ≤ ρ' := le_max_right _ _
  have hbρ'' : b < ρ' := lt_of_lt_of_le (by linarith) hbρ'
  have hρ'R : ρ' < R := max_lt hρ₁R hbLR
  set L₂ : ℝ := min (δ / 2) ((R - ρ₁) / 4)
  have hL₂0 : 0 < L₂ := lt_min (half_pos hδ) (by linarith)
  have hL₂δ : L₂ < δ := (min_le_left _ _).trans_lt (half_lt_self hδ)
  have hL₂R : L₂ ≤ (R - ρ₁) / 4 := min_le_right _ _
  have hρ₁L₂R : ρ₁ + 2 * L₂ < R := by linarith
  obtain ⟨N₁, hN₁⟩ := hann α b ρ' R c hα hαb hbρ'' hρ'R hc (θ / 2) (half_pos hθ)
  have hfm : ∀ n : ℕ, Measurable fun ω => (η₀ ω, S.mult (1 / (n : ℝ)) ω) :=
    fun n => hη₀m.prodMk (hS.measurable_mult_array _)
  have hGm : ∀ n : ℕ,
      MeasurableSet (restartMeshData (1 / (n : ℝ)) b L ∩ restartMeshData (1 / (n : ℝ)) ρ₁ L₂) := fun n =>
    (measurableSet_restartMeshData _ b L).inter (measurableSet_restartMeshData _ ρ₁ L₂)
  have hae : ∀ᵐ ω ∂S.P, ∀ᶠ n : ℕ in atTop,
      ω ∉ (fun ω => (η₀ ω, S.mult (1 / (n : ℝ)) ω)) ⁻¹'
        (restartMeshData (1 / (n : ℝ)) b L ∩ restartMeshData (1 / (n : ℝ)) ρ₁ L₂)ᶜ := by
    filter_upwards [hη₀, ae_mem_properOntoCurves hS hη₀, Uniform68Env.ae_envInputs hγ hγ2 hS]
      with ω h1 h2 h3
    obtain ⟨hc', hp', hadj⟩ := h3
    have hadj' : ∀ ε : ℝ, 0 < ε → ∀ j k : ℤ, S.mult ε ω j k ≠ 0 →
        (cell ε ⇑(η₀ ω) j ∩ cell ε ⇑(η₀ ω) k).Nonempty := by
      rw [h1]
      exact hadj
    filter_upwards [eventually_mem_restartMeshData h2 (fun ε => S.mult ε ω)
      (fun ε hε => (Uniform68Env.envAt S hε ω hc' hp' hadj).1)
      (fun ε hε => (Uniform68Env.envAt S hε ω hc' hp' hadj).2.1) hadj' hL hbLR,
      eventually_mem_restartMeshData h2 (fun ε => S.mult ε ω)
      (fun ε hε => (Uniform68Env.envAt S hε ω hc' hp' hadj).1)
      (fun ε hε => (Uniform68Env.envAt S hε ω hc' hp' hadj).2.1) hadj' hL₂0 hρ₁L₂R] with n hn hn'
    exact fun h => h ⟨hn, hn'⟩
  have hmeas : Tendsto (fun n : ℕ => S.P ((fun ω => (η₀ ω, S.mult (1 / (n : ℝ)) ω)) ⁻¹'
      (restartMeshData (1 / (n : ℝ)) b L ∩ restartMeshData (1 / (n : ℝ)) ρ₁ L₂)ᶜ)) atTop (𝓝 0) := by
    have hlim := tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure atTop MeasurableSet.empty
      (fun n => (hfm n) (hGm n).compl)
      (hae.mono fun ω hω => hω.mono fun n hn => iff_of_false hn (notMem_empty ω))
    rwa [measure_empty] at hlim
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.1
    ((ENNReal.tendsto_nhds_zero.1 hmeas) (ENNReal.ofReal (θ / 2)) (ENNReal.ofReal_pos.2 (half_pos hθ)))
  refine ⟨max (max N₁ N₂) 1, fun n hn => ?_⟩
  have hn1 : N₁ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn2 : N₂ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn0 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hε : (0 : ℝ) < 1 / (n : ℝ) := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn0
    positivity
  have hsub : (uniformStartSelectedLPData (1 / (n : ℝ)) ρ R κ)ᶜ ⊆
      (vertexAnnulusLPData (1 / (n : ℝ)) α b ρ' R c)ᶜ ∪
        (restartMeshData (1 / (n : ℝ)) b L ∩ restartMeshData (1 / (n : ℝ)) ρ₁ L₂)ᶜ := by
    intro d hd
    rw [mem_compl_iff] at hd
    by_contra hcon
    simp only [mem_union, mem_compl_iff, not_or, not_not] at hcon
    obtain ⟨hA, ⟨hpo, hlf, hsucc, hstep, -⟩, ⟨-, -, -, -, hdiam₂⟩⟩ := hcon
    apply hd
    intro z hz
    have hcont : Continuous ⇑d.1 := d.1.continuous
    have hfinb : {k : ℤ | vertexPoint (1 / (n : ℝ)) d.1 k ∈ ball (0 : ℂ) b}.Finite := by
      refine (cellVertices_finite_of_isCompact hcont hpo.1 hε (isCompact_closedBall (0 : ℂ) b)).subset ?_
      intro k hk
      exact ⟨vertexPoint (1 / (n : ℝ)) d.1 k, mem_cell_vertexPoint hε _ k, ball_subset_closedBall hk⟩
    have hstep' : ∀ x y : ℤ, vertexPoint (1 / (n : ℝ)) d.1 x ∈ closedBall (0 : ℂ) (b + L) → d.2 x y ≠ 0 →
        dist (vertexPoint (1 / (n : ℝ)) d.1 x) (vertexPoint (1 / (n : ℝ)) d.1 y) ≤ L := by
      intro x y hx hxy
      rcases hstep x y with h | h | h
      · exact absurd (mem_closedBall_zero_iff.1 hx) (not_le.2 h)
      · exact absurd h hxy
      · exact h
    refine ⟨UniformStartGood.ae_pathExitTime_interpolatedWalk_ne_top hε hcont hpo.1 hlf hsucc R _, ?_⟩
    set x : ℤ := vertexOf (1 / (n : ℝ)) d.1 z
    have hzx : z ∈ cell (1 / (n : ℝ)) d.1 x := Tightness.mem_cell_vertexOf hcont hpo.1 hpo.2 hε z
    have hzρ₁ : z ∈ ball (0 : ℂ) ρ₁ := closedBall_subset_ball hρρ₁ hz
    have hxz : dist (vertexPoint (1 / (n : ℝ)) d.1 x) z ≤ L₂ :=
      dist_vertexPoint_le_of_mem_cell hε hdiam₂ x hzx hzρ₁
    have hpx : vertexPoint (1 / (n : ℝ)) d.1 x ∈ closedBall (0 : ℂ) ρ₁ := by
      rw [mem_closedBall]
      have h1 := dist_triangle (vertexPoint (1 / (n : ℝ)) d.1 x) z 0
      have h2 : dist z 0 ≤ ρ := mem_closedBall.1 hz
      linarith
    have hball := H d.2 (vertexPoint (1 / (n : ℝ)) d.1) (fun y => ({vertexPoint (1 / (n : ℝ)) d.1 y} : Set ℂ))
      ρ' (fun y => mem_singleton _) hstep'
      (fun y w hw _ => by rw [mem_singleton_iff.1 hw, dist_self]; exact hL.le)
      (fun a _ => ae_ballExitIndex_ne_top hlf hsucc hfinb a) hbρ'
      (fun w hw hw' y hwy => by
        rw [mem_singleton_iff.1 hwy] at hw hw' ⊢
        exact hA y hw hw')
      (vertexPoint (1 / (n : ℝ)) d.1 x) (closedBall_subset_closedBall (le_max_left _ _) hpx) x
      (mem_singleton _)
    have hbm := hU _ hpx z (ball_subset_closedBall hzρ₁) (hxz.trans_lt hL₂δ)
    refine (levyProkhorovEDist_triangle _
      ((planarBrownianMotion (vertexPoint (1 / (n : ℝ)) d.1 x)).map (stoppedExitCurve (ball (0 : ℂ) R)))
      _).trans_lt ?_
    calc _ < ENNReal.ofReal (κ / 2) + ENNReal.ofReal (κ / 2) := ENNReal.add_lt_add hball hbm
      _ = ENNReal.ofReal κ := by
        rw [← ENNReal.ofReal_add (half_pos hκ).le (half_pos hκ).le, add_halves]
  calc S.P.map (fun ω => (η₀ ω, S.mult (1 / (n : ℝ)) ω)) (uniformStartSelectedLPData (1 / (n : ℝ)) ρ R κ)ᶜ
      ≤ S.P.map (fun ω => (η₀ ω, S.mult (1 / (n : ℝ)) ω))
          ((vertexAnnulusLPData (1 / (n : ℝ)) α b ρ' R c)ᶜ ∪
            (restartMeshData (1 / (n : ℝ)) b L ∩ restartMeshData (1 / (n : ℝ)) ρ₁ L₂)ᶜ) :=
        measure_mono hsub
    _ ≤ S.P.map (fun ω => (η₀ ω, S.mult (1 / (n : ℝ)) ω)) (vertexAnnulusLPData (1 / (n : ℝ)) α b ρ' R c)ᶜ +
          S.P.map (fun ω => (η₀ ω, S.mult (1 / (n : ℝ)) ω))
            (restartMeshData (1 / (n : ℝ)) b L ∩ restartMeshData (1 / (n : ℝ)) ρ₁ L₂)ᶜ :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal (θ / 2) + ENNReal.ofReal (θ / 2) := by
        refine add_le_add (hN₁ n hn1) ?_
        rw [Measure.map_apply (hfm n) (hGm n).compl]
        exact hN₂ n hn2
    _ = ENNReal.ofReal θ := by
        have hθ2 : 0 ≤ θ / 2 := by linarith
        rw [← ENNReal.ofReal_add hθ2 hθ2, add_halves]

end MatedCRT
