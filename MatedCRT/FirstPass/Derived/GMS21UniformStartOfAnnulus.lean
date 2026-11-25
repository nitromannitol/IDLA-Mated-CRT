import MatedCRT.FirstPass.Derived.GMS21BallOfAnnulus
import MatedCRT.FirstPass.Derived.GMS21UniformStartOfSelectedProkhorov
import MatedCRT.FirstPass.Derived.UniformStartGoodFinExit
import MatedCRT.FirstPass.Derived.GoodCurveSet
import MatedCRT.FirstPass.Derived.InterpolatedLawWiring
import MatedCRT.FirstPass.Derived.CellInballDisjoint
import MatedCRT.Proofs.Sec5.LLowerBound.SmallCells
import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.Cells
import MatedCRT.Proofs.Infra.LocallyFinite

/-!
# The uniform-start invariance principle on the `γ`-quantum cone from its form on annuli

In the proof of Gwynne–Miller–Sheffield (arXiv:1705.11161), Theorem 3.4, case 1, the comparison of the embedded walk
with Brownian motion is obtained on the `γ`-quantum cone from the `0`-quantum cone on annuli `B_R(0) \ closedBall 0 α`
avoiding the origin, where the two fields are mutually absolutely continuous. This file proves that the form on
annuli gives the form on balls required by the reference-environment route (`uniformStartSelectedLPData`): if, for
every annulus `B_R(0) \ closedBall 0 α` and starts `z ∈ closedBall 0 ρ \ B_b(0)` (`0 < α < b < ρ < R`), the law of
(curve, edge multiplicities) at the mesh `1/n` gives vanishing mass to the failure of the comparison stopped at the
exit from the annulus, then the same holds for the comparison stopped at the exit from the ball `B_R(0)`, for all
starts `z ∈ closedBall 0 ρ`.

The step is deterministic (`GMS21BallOfAnnulus`) on the measurable set `restartMeshData ε b L` of data with a proper
onto curve, a locally finite multigraph with the successor edges, edges of embedded length at most `L` from
`closedBall 0 (b + L)`, and cells meeting `B_b(0)` within distance `L` of their points (checked at rational times).
For a valid environment almost every curve is proper and onto with adjacent cells intersecting, so the data lie in
`restartMeshData (1/n) b L` for all large `n` almost surely.

## Main results

* `annulusSelectedLPData`: the good set on the annulus.
* `restartMeshData`, `measurableSet_restartMeshData`: the mesh conditions at the origin.
* `eventually_mem_restartMeshData`: they hold for all large `n` for a proper onto curve with intersecting adjacent
  cells.
* `tendsto_uniformStartSelectedLPData_of_annulus`: the uniform-start invariance principle on balls from its form on
  annuli.
-/

set_option autoImplicit false

open MeasureTheory Filter Topology Set Metric HarmonicBalls MarkovProcess
open scoped ENNReal NNReal

namespace MatedCRT

open StopAtExitLevyProkhorov

/-- The good set on the annulus at mesh `ε`: for every start `z ∈ closedBall 0 ρ \ B_b(0)` and every vertex `x` whose
cell contains `z`, the laws of the curve classes of the walk of `d.2` from `x`, embedded by `d.1(ε ·)` and
interpolated, and of planar Brownian motion from `z`, both stopped at their exits from the annulus
`B_R(0) \ closedBall 0 α`, are at Lévy–Prokhorov distance less than `c`. -/
def annulusSelectedLPData (ε α b ρ R c : ℝ) : Set (C(ℝ, ℂ) × (ℤ → ℤ → ℕ)) :=
  {d | ∀ z, z ∉ ball (0 : ℂ) b → z ∈ closedBall (0 : ℂ) ρ → ∀ x, z ∈ cell ε d.1 x →
    levyProkhorovEDist ((srwLaw d.2 x).map fun w =>
        stoppedExitCurve (ball (0 : ℂ) R \ closedBall (0 : ℂ) α) (interpPathCM (vertexPoint ε d.1) zero_le_one w))
      ((planarBrownianMotion z).map (stoppedExitCurve (ball (0 : ℂ) R \ closedBall (0 : ℂ) α))) <
      ENNReal.ofReal c}

/-- The mesh conditions at the origin at mesh `ε`: the curve is proper and onto, the multigraph is locally finite with
the successor edges, the edges from vertices embedded in `closedBall 0 (b + L)` have embedded length at most `L`, and
the points of a cell at rational times inside `B_b(0)` lie within distance `L` of the point of the cell. -/
def restartMeshData (ε b L : ℝ) : Set (C(ℝ, ℂ) × (ℤ → ℤ → ℕ)) :=
  {d | d.1 ∈ properOntoCurves ∧ IsLocallyFiniteMult d.2 ∧ (∀ k : ℤ, d.2 k (k + 1) ≠ 0) ∧
    (∀ x y : ℤ, b + L < ‖d.1 (ε * x)‖ ∨ d.2 x y = 0 ∨ dist (d.1 (ε * x)) (d.1 (ε * y)) ≤ L) ∧
    ∀ x : ℤ, ∀ q : ℚ, (q : ℝ) ∈ Icc (ε * (x - 1)) (ε * x) →
      b ≤ ‖d.1 (q : ℝ)‖ ∨ dist (d.1 (ε * x)) (d.1 (q : ℝ)) ≤ L}

/-- The set of points at which a family of measurable memberships indexed by `ℤ` is finite is measurable. -/
private theorem measurableSet_finite_setOf_int {X : Type} [MeasurableSpace X] (P : X → ℤ → Prop)
    (hP : ∀ c, MeasurableSet {x | P x c}) : MeasurableSet {x | {c | P x c}.Finite} := by
  have heq : {x | {c | P x c}.Finite} =
      ⋃ N : ℕ, ⋂ c : ℤ, ({x | P x c}ᶜ ∪ {_x | -(N : ℤ) ≤ c ∧ c ≤ (N : ℤ)}) := by
    ext x
    simp only [mem_ofPred_eq, mem_iUnion, mem_iInter, mem_union, mem_compl_iff]
    constructor
    · intro hfin
      obtain ⟨N, hN⟩ := (hfin.image (fun c : ℤ => c.natAbs)).bddAbove
      refine ⟨N, fun c => ?_⟩
      by_cases hc : P x c
      · right
        have h1 : c.natAbs ≤ N := hN ⟨c, hc, rfl⟩
        rcases Int.natAbs_eq c with h | h <;> constructor <;> omega
      · exact Or.inl hc
    · rintro ⟨N, hN⟩
      apply (Set.finite_Icc (-(N : ℤ)) (N : ℤ)).subset
      intro c hc
      rcases hN c with h | h
      · exact absurd hc h
      · exact h
  rw [heq]
  exact MeasurableSet.iUnion fun N => MeasurableSet.iInter fun c => (hP c).compl.union (MeasurableSet.const _)

/-- The mesh conditions at the origin form a measurable set of data. -/
theorem measurableSet_restartMeshData (ε b L : ℝ) : MeasurableSet (restartMeshData ε b L) := by
  have hev : ∀ t : ℝ, Measurable fun d : C(ℝ, ℂ) × (ℤ → ℤ → ℕ) => d.1 t :=
    fun t => (continuous_eval_const t).measurable.comp measurable_fst
  have hm : ∀ x y : ℤ, Measurable fun d : C(ℝ, ℂ) × (ℤ → ℤ → ℕ) => d.2 x y :=
    fun x y => (measurable_pi_apply y).comp ((measurable_pi_apply x).comp measurable_snd)
  have h0 : ∀ x y : ℤ, MeasurableSet {d : C(ℝ, ℂ) × (ℤ → ℤ → ℕ) | d.2 x y = 0} :=
    fun x y => measurableSet_eq_fun (hm x y) measurable_const
  have hlf : MeasurableSet {d : C(ℝ, ℂ) × (ℤ → ℤ → ℕ) | IsLocallyFiniteMult d.2} := by
    have heq : {d : C(ℝ, ℂ) × (ℤ → ℤ → ℕ) | IsLocallyFiniteMult d.2} =
        ⋂ a : ℤ, {d : C(ℝ, ℂ) × (ℤ → ℤ → ℕ) | {c : ℤ | d.2 a c ≠ 0}.Finite} := by
      ext d
      simp only [mem_iInter, mem_ofPred_eq]
      exact Iff.rfl
    rw [heq]
    exact MeasurableSet.iInter fun a => measurableSet_finite_setOf_int _ fun c => (h0 a c).compl
  unfold restartMeshData
  simp only [ofPred_and, ofPred_forall, ofPred_or]
  refine (measurable_fst measurableSet_properOntoCurves).inter (hlf.inter
    ((MeasurableSet.iInter fun k => (h0 k (k + 1)).compl).inter
      ((MeasurableSet.iInter fun x => MeasurableSet.iInter fun y =>
        (measurableSet_lt measurable_const (hev _).norm).union ((h0 x y).union
          (measurableSet_le ((hev _).dist (hev _)) measurable_const))).inter
      (MeasurableSet.iInter fun x => MeasurableSet.iInter fun q => MeasurableSet.iInter fun _ =>
        (measurableSet_le measurable_const (hev _).norm).union
          (measurableSet_le ((hev _).dist (hev _)) measurable_const)))))

/-- The point `η(ε k)` of the vertex `k` lies in its cell. -/
theorem mem_cell_vertexPoint {ε : ℝ} (hε : 0 < ε) (η : ℝ → ℂ) (k : ℤ) : vertexPoint ε η k ∈ cell ε η k :=
  ⟨ε * k, ⟨mul_le_mul_of_nonneg_left (by linarith) hε.le, le_rfl⟩, rfl⟩

/-- **The mesh conditions at the origin hold eventually.** For a proper onto curve and edge multiplicities `m ε`
that are locally finite with the successor edges and join intersecting cells, the data `(η, m (1/n))` lie in
`restartMeshData (1/n) b L` for all large `n`, when `L > 0` and `b + 2 L < R`. -/
theorem eventually_mem_restartMeshData {η : C(ℝ, ℂ)} (hη : η ∈ properOntoCurves) (m : ℝ → ℤ → ℤ → ℕ)
    (hlf : ∀ ε : ℝ, 0 < ε → IsLocallyFiniteMult (m ε)) (hsucc : ∀ ε : ℝ, 0 < ε → ∀ k : ℤ, m ε k (k + 1) ≠ 0)
    (hadj : ∀ ε : ℝ, 0 < ε → ∀ j k : ℤ, m ε j k ≠ 0 → (cell ε η j ∩ cell ε η k).Nonempty)
    {b L R : ℝ} (hL : 0 < L) (hbLR : b + 2 * L < R) :
    ∀ᶠ n : ℕ in atTop, (η, m (1 / (n : ℝ))) ∈ restartMeshData (1 / (n : ℝ)) b L := by
  obtain ⟨ε₀, hε₀, hsmall⟩ := cell_diam_small_of_proper η.continuous hη.1 R (L / 2) (half_pos hL)
  have hlim : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) := tendsto_one_div_atTop_nhds_zero_nat
  filter_upwards [hlim.eventually (gt_mem_nhds hε₀), eventually_ge_atTop 1] with n hn hn1
  have hε : (0 : ℝ) < 1 / (n : ℝ) := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    positivity
  set ε : ℝ := 1 / (n : ℝ) with hεdef
  have hbR : b < R := by linarith
  have hdiam : ∀ k : ℤ, ∀ w ∈ cell ε η k, ‖w‖ < R → Metric.diam (cell ε η k) ≤ L / 2 :=
    fun k w hw hwR => hsmall ε hε hn k ⟨w, hw, mem_ball_zero_iff.2 hwR⟩
  refine ⟨hη, hlf ε hε, hsucc ε hε, fun x y => ?_, fun x q hq => ?_⟩
  · by_cases hx : b + L < ‖η (ε * x)‖
    · exact Or.inl hx
    by_cases hm : m ε x y = 0
    · exact Or.inr (Or.inl hm)
    right
    right
    obtain ⟨w, hwx, hwy⟩ := hadj ε hε x y hm
    have hpx : η (ε * x) ∈ cell ε η x := mem_cell_vertexPoint hε η x
    have hpy : η (ε * y) ∈ cell ε η y := mem_cell_vertexPoint hε η y
    have hdx := hdiam x _ hpx (by linarith [not_lt.1 hx])
    have hd1 : dist (η (ε * x)) w ≤ L / 2 :=
      (dist_le_diam_of_mem (isBounded_cell η.continuous x) hpx hwx).trans hdx
    have hw : ‖w‖ < R := by
      have h3 : ‖w‖ ≤ ‖η (ε * x)‖ + dist (η (ε * x)) w := by
        rw [dist_comm, dist_eq_norm]
        linarith [norm_sub_norm_le w (η (ε * x))]
      linarith [not_lt.1 hx]
    have hdy := hdiam y w hwy hw
    have hd2 : dist w (η (ε * y)) ≤ L / 2 :=
      (dist_le_diam_of_mem (isBounded_cell η.continuous y) hwy hpy).trans hdy
    calc dist (η (ε * x)) (η (ε * y)) ≤ dist (η (ε * x)) w + dist w (η (ε * y)) := dist_triangle _ _ _
      _ ≤ L := by linarith
  · by_cases hq' : b ≤ ‖η (q : ℝ)‖
    · exact Or.inl hq'
    right
    have hqx : η (q : ℝ) ∈ cell ε η x := ⟨q, hq, rfl⟩
    have hpx : η (ε * x) ∈ cell ε η x := mem_cell_vertexPoint hε η x
    have hdx := hdiam x _ hqx (by linarith [not_le.1 hq'])
    exact (dist_le_diam_of_mem (isBounded_cell η.continuous x) hpx hqx).trans (hdx.trans (by linarith))

/-- **The uniform-start invariance principle on balls from its form on annuli** (Gwynne–Miller–Sheffield,
arXiv:1705.11161, proof of Theorem 3.4, case 1). Let `S` be a valid environment for `0 < γ < 2` with a measurable
continuous version `η₀` of its curve. Suppose that for all `0 < α < b < ρ < R` and `c > 0`, the law of
`(η₀, S.mult (1/n))` gives mass at most `θ` to the complement of the good set on the annulus
`annulusSelectedLPData (1/n) α b ρ R c` for all large `n`, for every `θ > 0`. Then for all `0 < ρ < R` and
`κ, θ > 0` it gives mass at most `θ` to the complement of `uniformStartSelectedLPData (1/n) ρ R κ` for all large
`n`: this is the premise `hTutteLP` at `S` and `η₀`. -/
theorem tendsto_uniformStartSelectedLPData_of_annulus {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    {η₀ : Ω → C(ℝ, ℂ)} (hη₀m : Measurable η₀) (hη₀ : ∀ᵐ ω ∂S.P, ⇑(η₀ ω) = S.η ω)
    (hann : ∀ α b ρ R c : ℝ, 0 < α → α < b → b < ρ → ρ < R → 0 < c → ∀ θ : ℝ, 0 < θ →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        S.P.map (fun ω => (η₀ ω, S.mult (1 / (n : ℝ)) ω))
          (annulusSelectedLPData (1 / (n : ℝ)) α b ρ R c)ᶜ ≤ ENNReal.ofReal θ) :
    ∀ R ρ : ℝ, 0 < ρ → ρ < R → ∀ κ : ℝ, 0 < κ → ∀ θ : ℝ, 0 < θ →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        S.P.map (fun ω => (η₀ ω, S.mult (1 / (n : ℝ)) ω))
          (uniformStartSelectedLPData (1 / (n : ℝ)) ρ R κ)ᶜ ≤ ENNReal.ofReal θ := by
  intro R ρ hρ hρR κ hκ θ hθ
  have hP := hS.isProbabilityMeasure
  obtain ⟨α, b, L, c, hα, hαb, hL, hbLR, hc, H⟩ :=
    exists_forall_levyProkhorovEDist_walk_ball_lt (hρ.trans hρR) hκ
  set ρ' : ℝ := max ρ (b + 2 * L) with hρ'
  have hbρ' : b + 2 * L ≤ ρ' := le_max_right _ _
  have hbρ'' : b < ρ' := lt_of_lt_of_le (by linarith) hbρ'
  have hρ'R : ρ' < R := max_lt hρR hbLR
  obtain ⟨N₁, hN₁⟩ := hann α b ρ' R c hα hαb hbρ'' hρ'R hc (θ / 2) (half_pos hθ)
  have hfm : ∀ n : ℕ, Measurable fun ω => (η₀ ω, S.mult (1 / (n : ℝ)) ω) :=
    fun n => hη₀m.prodMk (hS.measurable_mult_array _)
  have hae : ∀ᵐ ω ∂S.P, ∀ᶠ n : ℕ in atTop,
      ω ∉ (fun ω => (η₀ ω, S.mult (1 / (n : ℝ)) ω)) ⁻¹' (restartMeshData (1 / (n : ℝ)) b L)ᶜ := by
    filter_upwards [hη₀, ae_mem_properOntoCurves hS hη₀, Uniform68Env.ae_envInputs hγ hγ2 hS]
      with ω h1 h2 h3
    obtain ⟨hc', hp', hadj⟩ := h3
    have hadj' : ∀ ε : ℝ, 0 < ε → ∀ j k : ℤ, S.mult ε ω j k ≠ 0 →
        (cell ε ⇑(η₀ ω) j ∩ cell ε ⇑(η₀ ω) k).Nonempty := by
      rw [h1]
      exact hadj
    filter_upwards [eventually_mem_restartMeshData h2 (fun ε => S.mult ε ω)
      (fun ε hε => (Uniform68Env.envAt S hε ω hc' hp' hadj).1)
      (fun ε hε => (Uniform68Env.envAt S hε ω hc' hp' hadj).2.1) hadj' hL hbLR] with n hn
    exact fun h => h hn
  have hmeas : Tendsto (fun n : ℕ => S.P ((fun ω => (η₀ ω, S.mult (1 / (n : ℝ)) ω)) ⁻¹'
      (restartMeshData (1 / (n : ℝ)) b L)ᶜ)) atTop (𝓝 0) := by
    have hlim := tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure atTop MeasurableSet.empty
      (fun n => (hfm n) (measurableSet_restartMeshData (1 / (n : ℝ)) b L).compl)
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
      (annulusSelectedLPData (1 / (n : ℝ)) α b ρ' R c)ᶜ ∪ (restartMeshData (1 / (n : ℝ)) b L)ᶜ := by
    intro d hd
    rw [mem_compl_iff] at hd
    by_contra hcon
    simp only [mem_union, mem_compl_iff, not_or, not_not] at hcon
    obtain ⟨hA, hpo, hlf, hsucc, hstep, hdiam⟩ := hcon
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
    have hdiam' : ∀ (x : ℤ) (w : ℂ), w ∈ cell (1 / (n : ℝ)) d.1 x → w ∈ ball (0 : ℂ) b →
        dist (vertexPoint (1 / (n : ℝ)) d.1 x) w ≤ L := by
      intro x w hwx hwb
      obtain ⟨t, ht, rfl⟩ := hwx
      have hlt : 1 / (n : ℝ) * ((x : ℝ) - 1) < 1 / (n : ℝ) * x :=
        mul_lt_mul_of_pos_left (by linarith) hε
      have hCc : IsClosed ({s : ℝ | b ≤ ‖d.1 s‖} ∪ {s : ℝ | dist (d.1 (1 / (n : ℝ) * x)) (d.1 s) ≤ L}) :=
        (isClosed_le continuous_const (continuous_norm.comp hcont)).union
          (isClosed_le (continuous_const.dist hcont) continuous_const)
      have hIoo : Ioo (1 / (n : ℝ) * ((x : ℝ) - 1)) (1 / (n : ℝ) * x) ⊆
          {s : ℝ | b ≤ ‖d.1 s‖} ∪ {s : ℝ | dist (d.1 (1 / (n : ℝ) * x)) (d.1 s) ≤ L} :=
        subset_of_rat_mem isOpen_Ioo hCc fun q hq => hdiam x q (Ioo_subset_Icc_self hq)
      have hIcc : Icc (1 / (n : ℝ) * ((x : ℝ) - 1)) (1 / (n : ℝ) * x) ⊆
          {s : ℝ | b ≤ ‖d.1 s‖} ∪ {s : ℝ | dist (d.1 (1 / (n : ℝ) * x)) (d.1 s) ≤ L} := by
        rw [← closure_Ioo hlt.ne]
        exact closure_minimal hIoo hCc
      rcases hIcc ht with h | h
      · exact absurd (mem_ball_zero_iff.1 hwb) (not_lt.2 h)
      · exact h
    refine ⟨UniformStartGood.ae_pathExitTime_interpolatedWalk_ne_top hε hcont hpo.1 hlf hsucc R _, ?_⟩
    exact H d.2 (vertexPoint (1 / (n : ℝ)) d.1) (cell (1 / (n : ℝ)) d.1) ρ'
      (fun x => mem_cell_vertexPoint hε _ x) hstep' hdiam'
      (fun a _ => ae_ballExitIndex_ne_top hlf hsucc hfinb a) hbρ' hA z
      (closedBall_subset_closedBall (le_max_left _ _) hz) _
      (Tightness.mem_cell_vertexOf hcont hpo.1 hpo.2 hε z)
  calc S.P.map (fun ω => (η₀ ω, S.mult (1 / (n : ℝ)) ω)) (uniformStartSelectedLPData (1 / (n : ℝ)) ρ R κ)ᶜ
      ≤ S.P.map (fun ω => (η₀ ω, S.mult (1 / (n : ℝ)) ω))
          ((annulusSelectedLPData (1 / (n : ℝ)) α b ρ' R c)ᶜ ∪ (restartMeshData (1 / (n : ℝ)) b L)ᶜ) :=
        measure_mono hsub
    _ ≤ S.P.map (fun ω => (η₀ ω, S.mult (1 / (n : ℝ)) ω)) (annulusSelectedLPData (1 / (n : ℝ)) α b ρ' R c)ᶜ +
          S.P.map (fun ω => (η₀ ω, S.mult (1 / (n : ℝ)) ω)) (restartMeshData (1 / (n : ℝ)) b L)ᶜ :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal (θ / 2) + ENNReal.ofReal (θ / 2) := by
        refine add_le_add (hN₁ n hn1) ?_
        rw [Measure.map_apply (hfm n) (measurableSet_restartMeshData _ b L).compl]
        exact hN₂ n hn2
    _ = ENNReal.ofReal θ := by
        have hθ2 : 0 ≤ θ / 2 := by linarith
        rw [← ENNReal.ofReal_add hθ2 hθ2, add_halves]

end MatedCRT
