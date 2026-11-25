import MatedCRT.Proofs.Sec5.StoppedClusterCode
import MatedCRT.Proofs.Sec5.StoppedLayerBound
import MatedCRT.FirstPass.Derived.CellSizeOfConeCouplingProd
import MatedCRT.FirstPass.S5e.SecondGreenStep

/-!
# The discrete-to-continuum geometry of the `δ`-interior of `V^ε(Λ_t)`

`StoppedInterior.StoppedInteriorGeometryStep` asks that, on `{t < T}` and with probability tending to one, every vertex
`a` of `V^ε(Λ_t)` whose point `η(a)` is at distance more than `δ` from the frontier of the union `F` of the cells of
`V^ε(Λ_t)` has all points of its cell within `r` of `η(a)` and at distance at least `δ/2` from `Λ_tᶜ`.

The deterministic core (`geometry_of_witness`): let `Λ ⊆ B_R` be open with `int (cl Λ) = Λ`, and let the cells meeting
`Λ` have diameters at most `d`. Every point of `F` is within `d` of `Λ`, and the ball `B(η(a), δ)` lies in `F` (it is
connected and misses the frontier of `F`). Suppose that every point `q ∉ Λ` of a dense set `D` with `|q| < R + 1` has a
witness `z ∈ D` with `|z - q| < δ/8` at distance more than `2d` from the points of `D ∩ Λ`. Then
`B(η(a), 3δ/4) ⊆ Λ`: a point `y ∉ Λ` of this ball is a limit of points of `D ∖ cl Λ` (regularity), whose witness
would lie in `F`, hence within `2d` of `D ∩ Λ`. The conclusion follows when `d ≤ δ/8` and `d < r`.

The witnesses exist uniformly (`exists_exterior_witness`): by compactness of `Λᶜ ∩ B̄_R` and regularity, some `c > 0`
works for all `q`. The largest admissible `2d` is the countable expression `geometryThreshold`; for
`Λ_t = codeBall ρ t (W ω)` (`StoppedCode.ae_codeBall_eq`) it is a `σ(h)`-measurable function of the code which is positive
almost surely on `{t < T}`. With the cell-size estimate of Lemma 2.8 (diameters at most `ε^{1/(2+γ)²}` on `B_ρ` with
polynomially high probability) this gives `stoppedInteriorGeometryStep_holds` for every model.
-/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric TopologicalSpace
open scoped ENNReal

namespace StoppedGeometry

/-- The point `η(εk)` lies in the cell `η([ε(k-1), εk])`. -/
theorem vertexPoint_mem_cell {ε : ℝ} (hε : 0 ≤ ε) (η : ℝ → ℂ) (k : ℤ) : vertexPoint ε η k ∈ cell ε η k :=
  ⟨ε * k, ⟨mul_le_mul_of_nonneg_left (by linarith) hε, le_rfl⟩, rfl⟩

/-- Cells of a continuous curve are bounded. -/
theorem isBounded_cell {η : ℝ → ℂ} (hη : Continuous η) (ε : ℝ) (k : ℤ) : Bornology.IsBounded (cell ε η k) :=
  (isCompact_Icc.image hη).isBounded

/-- **Deterministic core of the geometry step.** See the module docstring. -/
theorem geometry_of_witness {Λ : Set ℂ} (hΛo : IsOpen Λ) (hreg : interior (closure Λ) = Λ) {R : ℝ}
    (hΛR : Λ ⊆ ball 0 R) {D : Set ℂ} (hD : Dense D) {η : ℝ → ℂ} (hη : Continuous η) {ε d δ r : ℝ} (hε : 0 < ε)
    (hd : 0 < d) (hd1 : d ≤ 1) (hdδ : d ≤ δ / 8) (hdr : d < r)
    (hdiam : ∀ k ∈ cellVertices ε η Λ, diam (cell ε η k) ≤ d)
    (hwit : ∀ q ∈ D, q ∉ Λ → ‖q‖ < R + 1 → ∃ z ∈ D, dist z q < δ / 8 ∧ ∀ p ∈ D, p ∈ Λ → 2 * d < dist z p) :
    ∀ a ∈ cellVertices ε η Λ, δ < infDist (vertexPoint ε η a) (frontier (fillCells ε η (cellVertices ε η Λ))) →
      ∀ x ∈ cell ε η a, δ / 2 ≤ infDist x Λᶜ ∧ dist x (vertexPoint ε η a) < r := by
  intro a ha hδa x hx
  set F := fillCells ε η (cellVertices ε η Λ) with hFdef
  set v := vertexPoint ε η a with hvdef
  have hδ : 0 < δ := by linarith
  have hvcell : v ∈ cell ε η a := vertexPoint_mem_cell hε.le η a
  have hdist : ∀ y ∈ cell ε η a, dist y v ≤ d := fun y hy =>
    (dist_le_diam_of_mem (isBounded_cell hη ε a) hy hvcell).trans (hdiam a ha)
  have hFnear : ∀ z ∈ F, ∃ p ∈ Λ, dist z p ≤ d := by
    intro z hz
    rw [hFdef, fillCells, mem_iUnion₂] at hz
    obtain ⟨k, hk, hzk⟩ := hz
    obtain ⟨p, hpk, hpΛ⟩ := id hk
    exact ⟨p, hpΛ, (dist_le_diam_of_mem (isBounded_cell hη ε k) hzk hpk).trans (hdiam k hk)⟩
  have hvF : v ∈ F := mem_iUnion₂.2 ⟨a, ha, hvcell⟩
  have hball : ball v δ ⊆ F := by
    have hnf : ∀ y ∈ ball v δ, y ∉ frontier F := fun y hy hyf => by
      have h1 := infDist_le_dist_of_mem hyf (x := v)
      rw [mem_ball, dist_comm] at hy
      linarith
    have hcover : ball v δ ⊆ interior F ∪ (closure F)ᶜ := fun y hy => by
      by_cases hyc : y ∈ closure F
      · left
        by_contra hyi
        exact hnf y hy ⟨hyc, hyi⟩
      · exact Or.inr hyc
    have hvi : v ∈ interior F := by
      by_contra hvi
      exact hnf v (mem_ball_self hδ) ⟨subset_closure hvF, hvi⟩
    have hdisj : Disjoint (interior F) (closure F)ᶜ :=
      disjoint_compl_right.mono_left (interior_subset.trans subset_closure)
    exact ((isPreconnected_ball : IsPreconnected (ball v δ)).subset_left_of_subset_union isOpen_interior
      isClosed_closure.isOpen_compl hdisj hcover ⟨v, mem_ball_self hδ, hvi⟩).trans interior_subset
  have hin : ball v (3 * δ / 4) ⊆ Λ := by
    intro y hy
    by_contra hyΛ
    have hy' : y ∈ closure (closure Λ)ᶜ := by
      rw [closure_compl, hreg]
      exact hyΛ
    have hne : ((closure Λ)ᶜ ∩ ball y (δ / 16)).Nonempty := by
      obtain ⟨z, hz, hzy⟩ := Metric.mem_closure_iff.1 hy' (δ / 16) (by positivity)
      exact ⟨z, hz, by rw [mem_ball, dist_comm]; exact hzy⟩
    obtain ⟨q, ⟨hqc, hqy⟩, hqD⟩ :=
      hD.inter_open_nonempty _ (isClosed_closure.isOpen_compl.inter isOpen_ball) hne
    have hqΛ : q ∉ Λ := fun h => hqc (subset_closure h)
    rw [mem_ball] at hqy hy
    have hqv : dist q v < 13 * δ / 16 := by linarith [dist_triangle q y v]
    have hqF : q ∈ F := hball (by rw [mem_ball]; linarith)
    obtain ⟨p0, hp0Λ, hqp0⟩ := hFnear q hqF
    have hqR : ‖q‖ < R + 1 := by
      have h0 := hΛR hp0Λ
      rw [mem_ball_zero_iff] at h0
      have h1 : ‖q‖ ≤ ‖p0‖ + dist q p0 := by
        rw [dist_eq_norm]
        calc ‖q‖ = ‖p0 + (q - p0)‖ := by rw [add_sub_cancel]
          _ ≤ ‖p0‖ + ‖q - p0‖ := norm_add_le _ _
      linarith
    obtain ⟨z, hzD, hzq, hzfar⟩ := hwit q hqD hqΛ hqR
    have hzF : z ∈ F := hball (by rw [mem_ball]; linarith [dist_triangle z q v])
    obtain ⟨p1, hp1Λ, hzp1⟩ := hFnear z hzF
    obtain ⟨p, ⟨hpΛ, hpp1⟩, hpD⟩ :=
      hD.inter_open_nonempty _ (hΛo.inter isOpen_ball) ⟨p1, hp1Λ, mem_ball_self hd⟩
    have hfar := hzfar p hpD hpΛ
    rw [mem_ball] at hpp1
    linarith [dist_triangle z p1 p, dist_comm p p1]
  have hΛc : Λᶜ.Nonempty := by
    refine ⟨((max R 0 : ℝ) : ℂ), fun h => ?_⟩
    have h0 := hΛR h
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_max_right R 0)] at h0
    linarith [le_max_left R 0]
  refine ⟨?_, (hdist x hx).trans_lt hdr⟩
  rw [le_infDist hΛc]
  intro y hy
  by_contra hlt
  push Not at hlt
  have hxv := hdist x hx
  exact hy (hin (by rw [mem_ball]; linarith [dist_triangle y x v, dist_comm x y]))

/-- **Uniform exterior witnesses.** For a regular open `Λ`, a dense `D` and `R, ζ > 0` there is `c > 0` such that every
`q ∉ Λ` with `|q| ≤ R` has a point `z ∈ D` with `|z - q| < ζ` at distance at least `c` from `Λ`. -/
theorem exists_exterior_witness {Λ : Set ℂ} (hreg : interior (closure Λ) = Λ) {D : Set ℂ} (hD : Dense D)
    (R : ℝ) {ζ : ℝ} (hζ : 0 < ζ) :
    ∃ c : ℝ, 0 < c ∧ ∀ q, q ∉ Λ → ‖q‖ ≤ R → ∃ z ∈ D, dist z q < ζ ∧ ∀ p ∈ Λ, c ≤ dist z p := by
  have hΛo : IsOpen Λ := hreg ▸ isOpen_interior
  by_cases hΛe : Λ = ∅
  · refine ⟨1, one_pos, fun q _ _ => ?_⟩
    obtain ⟨z, hzD, hzq⟩ := hD.exists_dist_lt q hζ
    exact ⟨z, hzD, by rw [dist_comm]; exact hzq, fun p hp => by rw [hΛe] at hp; exact absurd hp (notMem_empty p)⟩
  have hne : Λ.Nonempty := nonempty_iff_ne_empty.2 hΛe
  set K : Set ℂ := Λᶜ ∩ closedBall 0 R with hKdef
  have hK : IsCompact K := (isCompact_closedBall 0 R).inter_left hΛo.isClosed_compl
  have hloc : ∀ q ∈ K, ∃ z ∈ D, dist z q < ζ / 2 ∧ 0 < infDist z Λ := by
    intro q hq
    have hq' : q ∈ closure (closure Λ)ᶜ := by
      rw [closure_compl, hreg]
      exact hq.1
    have hne' : ((closure Λ)ᶜ ∩ ball q (ζ / 2)).Nonempty := by
      obtain ⟨z, hz, hzq⟩ := Metric.mem_closure_iff.1 hq' (ζ / 2) (half_pos hζ)
      exact ⟨z, hz, by rw [mem_ball, dist_comm]; exact hzq⟩
    obtain ⟨z, ⟨hzc, hzq⟩, hzD⟩ :=
      hD.inter_open_nonempty _ (isClosed_closure.isOpen_compl.inter isOpen_ball) hne'
    exact ⟨z, hzD, hzq, (infDist_pos_iff_notMem_closure hne).1 hzc⟩
  choose! z hzD hzq hzpos using hloc
  obtain ⟨T, hTK, hcov⟩ := hK.elim_nhds_subcover (fun q => ball q (ζ / 2))
    (fun q _ => ball_mem_nhds q (half_pos hζ))
  by_cases hT : T.Nonempty
  · refine ⟨T.inf' hT fun q => infDist (z q) Λ, (Finset.lt_inf'_iff hT).2 fun q hq => hzpos q (hTK q hq), ?_⟩
    intro q' hq'Λ hq'R
    have hq'K : q' ∈ K := ⟨hq'Λ, mem_closedBall_zero_iff.2 hq'R⟩
    obtain ⟨q, hqT, hq'q⟩ := mem_iUnion₂.1 (hcov hq'K)
    refine ⟨z q, hzD q (hTK q hqT), ?_, fun p hp => ?_⟩
    · rw [mem_ball] at hq'q
      linarith [dist_triangle (z q) q q', hzq q (hTK q hqT), dist_comm q' q]
    · exact (Finset.inf'_le _ hqT).trans (infDist_le_dist_of_mem hp)
  · refine ⟨1, one_pos, fun q' hq'Λ hq'R => ?_⟩
    have hq'K : q' ∈ K := ⟨hq'Λ, mem_closedBall_zero_iff.2 hq'R⟩
    obtain ⟨q, hqT, -⟩ := mem_iUnion₂.1 (hcov hq'K)
    exact absurd ⟨q, hqT⟩ hT

open Classical in
/-- The threshold of the geometry step: the infimum over `q ∈ denseC ∖ U` with `|q| < R` of the supremum over
`z ∈ denseC` with `|z - q| < ζ` of the distance from `z` to `denseC ∩ U`, in `[0, ∞]`. -/
noncomputable def geometryThreshold (U : Set ℂ) (R ζ : ℝ) : ℝ≥0∞ :=
  ⨅ q : denseC, if (q : ℂ) ∉ U ∧ ‖(q : ℂ)‖ < R then
    ⨆ z : denseC, if dist (z : ℂ) q < ζ then
      ⨅ p : denseC, if (p : ℂ) ∈ U then edist (z : ℂ) p else ⊤
    else 0
  else ⊤

/-- Above `2d`, the threshold gives the witnesses of `geometry_of_witness`. -/
theorem witness_of_lt_geometryThreshold {U : Set ℂ} {R ζ d : ℝ}
    (h : ENNReal.ofReal (2 * d) < geometryThreshold U R ζ) :
    ∀ q ∈ denseC, q ∉ U → ‖q‖ < R → ∃ z ∈ denseC, dist z q < ζ ∧ ∀ p ∈ denseC, p ∈ U → 2 * d < dist z p := by
  classical
  intro q hqD hqU hqR
  have h1 := h.trans_le (iInf_le _ ⟨q, hqD⟩)
  simp only [hqU, not_false_eq_true, hqR, and_self, ite_true] at h1
  obtain ⟨⟨z, hzD⟩, hz⟩ := lt_iSup_iff.1 h1
  by_cases hzq : dist z q < ζ
  · simp only [hzq, ite_true] at hz
    refine ⟨z, hzD, hzq, fun p hpD hpU => ?_⟩
    have h2 := hz.trans_le (iInf_le _ ⟨p, hpD⟩)
    simp only [hpU, ite_true, edist_dist] at h2
    exact ((ENNReal.ofReal_lt_ofReal_iff' (p := 2 * d) (q := dist z p)).1 h2).1
  · simp only [hzq, ite_false] at hz
    exact absurd hz (not_lt_zero)

/-- The threshold of a regular open set is positive. -/
theorem geometryThreshold_pos {U : Set ℂ} (hreg : interior (closure U) = U) (R : ℝ) {ζ : ℝ} (hζ : 0 < ζ) :
    0 < geometryThreshold U R ζ := by
  classical
  obtain ⟨c, hc, hwit⟩ := exists_exterior_witness hreg denseC_spec.2 R hζ
  refine lt_of_lt_of_le (ENNReal.ofReal_pos.2 hc) (le_iInf fun q => ?_)
  split_ifs with hq
  · obtain ⟨z, hzD, hzq, hzc⟩ := hwit q hq.1 hq.2.le
    refine le_iSup_of_le ⟨z, hzD⟩ ?_
    simp only [hzq, ite_true]
    refine le_iInf fun p => ?_
    split_ifs with hp
    · rw [edist_dist]
      exact ENNReal.ofReal_le_ofReal (hzc p hp)
    · exact le_top
  · exact le_top

/-- The threshold of the regularized cluster of a code is a Borel function of the code. -/
theorem measurable_geometryThreshold_codeBall {ρ t : ℝ} (hρ : 0 < ρ) (ht : 0 < t) (R ζ : ℝ) :
    Measurable fun w : DiskFun ρ => geometryThreshold (StoppedCode.codeBall ρ t w) R ζ := by
  classical
  have : Countable denseC := denseC_spec.1.to_subtype
  have hmem : ∀ x : ℂ, MeasurableSet {w : DiskFun ρ | x ∈ StoppedCode.codeBall ρ t w} :=
    StoppedCode.measurableSet_mem_codeBall hρ ht
  refine Measurable.iInf fun q => Measurable.ite ?_ (Measurable.iSup fun z => Measurable.ite
    (MeasurableSet.const _) (Measurable.iInf fun p => Measurable.ite (hmem p) measurable_const measurable_const)
    measurable_const) measurable_const
  exact (hmem q).compl.inter (MeasurableSet.const _)

/-- **The geometry step** `StoppedInterior.StoppedInteriorGeometryStep` for every model. -/
theorem stoppedInteriorGeometryStep_holds (𝒮 : SpaceFillingSLEModel) :
    StoppedInterior.StoppedInteriorGeometryStep 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS Λ hΛ δ t r hδ ht hr
  have := hS.isProbabilityMeasure
  obtain ⟨W, hWm, hWae⟩ := StoppedCode.ae_codeBall_eq 𝒮 hγ hγ2 hρ hρ1 hS hΛ ht
  set R : ℝ := ρ / 3 with hRdef
  set θ : Ω → ℝ≥0∞ := fun ω => geometryThreshold (StoppedCode.codeBall ρ t (W ω)) (R + 1) (δ / 8) with hθdef
  have hθm : Measurable[S.envSigma] θ :=
    ((measurable_geometryThreshold_codeBall hρ ht (R + 1) (δ / 8)).comp hWm).mono le_sup_left le_rfl
  set c : Ω → ℝ := fun ω => (min (θ ω) 1).toReal with hcdef
  have hcm : Measurable[S.envSigma] c := (hθm.min measurable_const).ennreal_toReal
  set cpos : Ω → ℝ := fun ω => if 0 < c ω then c ω else 1 with hcposdef
  have hcposm : Measurable[S.envSigma] cpos :=
    Measurable.ite (measurableSet_lt measurable_const hcm) hcm measurable_const
  have hcpos : ∀ ω, 0 < cpos ω := fun ω => by
    simp only [hcposdef]
    split_ifs with h
    · exact h
    · exact one_pos
  have hcae : AEMeasurable cpos S.P := hS.aemeasurable_of_envSigma hcposm
  -- the cell-size estimate of Lemma 2.8
  have hζ0 : (0 : ℝ) < 1 / (2 + γ) ^ 2 := by positivity
  have hζ1 : 1 / (2 + γ) ^ 2 < 1 := by
    rw [div_lt_one (by positivity)]
    nlinarith
  have hb : 0 < 2 / (2 + γ) ^ 2 - 1 / (2 + γ) ^ 2 := by
    rw [div_sub_div_same]
    norm_num
    positivity
  have hcell := S5e.tendsToOneOn_of_polyHighProb {ω | t < clusterExitTime (Λ ω) ρ}
    (FirstPass.Derived.cellSizeEstimateStmt_holds 𝒮 γ hγ hγ2 (1 / (2 + γ) ^ 2) ρ hζ0 hζ1 hρ hρ1 Ω S hS)
  -- the good event
  set G : Set Ω := {ω | (t < clusterExitTime (Λ ω) ρ → Λ ω t = StoppedCode.codeBall ρ t (W ω)) ∧
    IsConeHarmonicBallFamily (S.μ ω) (Λ ω) ∧ Continuous (S.η ω)} with hGdef
  have hG : S.P Gᶜ = 0 := by
    have h : ∀ᵐ ω ∂S.P, ω ∈ G := by
      filter_upwards [hWae, hΛ, hS.isAreaParametrized] with ω hωW hωΛ hωη
      exact ⟨fun hT => (hωW hT).1, hωΛ, hωη.1⟩
    exact ae_iff.1 h
  unfold TendsToOneOn
  rw [ENNReal.tendsto_nhds_zero]
  intro e he
  have he2 : (0 : ℝ≥0∞) < e / 2 := ENNReal.div_pos_iff.2 ⟨he.ne', by norm_num⟩
  obtain ⟨κ, hκ, hPκ⟩ := StoppedMeanValue.exists_measure_le_le_of_pos hcae hcpos he2
  set d : ℝ := min (min (κ / 4) (δ / 8)) (min (r / 2) 1) with hddef
  have hd : 0 < d := lt_min (lt_min (by positivity) (by positivity)) (lt_min (by positivity) one_pos)
  have hd1 : d ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
  have hdδ : d ≤ δ / 8 := (min_le_left _ _).trans (min_le_right _ _)
  have hdr : d < r := lt_of_le_of_lt ((min_le_right _ _).trans (min_le_left _ _)) (by linarith)
  have hdκ : 2 * d < κ := by
    have : d ≤ κ / 4 := (min_le_left _ _).trans (min_le_left _ _)
    linarith
  have hpow : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ^ (2 / (2 + γ) ^ 2 - 1 / (2 + γ) ^ 2) < d :=
    (tendsto_rpow_nhdsGT_zero_zero hb).eventually (gt_mem_nhds hd)
  filter_upwards [self_mem_nhdsWithin, hpow, ENNReal.tendsto_nhds_zero.1 hcell (e / 2) he2] with ε hε hεd hεP
  have hεpos : 0 < ε := hε
  have hsub : {ω | t < clusterExitTime (Λ ω) ρ} ∩ {ω | ∀ a ∈ cellVertices ε (S.η ω) (Λ ω t),
      δ < infDist (vertexPoint ε (S.η ω) a) (frontier (fillCells ε (S.η ω) (cellVertices ε (S.η ω) (Λ ω t)))) →
      ∀ x ∈ cell ε (S.η ω) a, δ / 2 ≤ infDist x (Λ ω t)ᶜ ∧ dist x (vertexPoint ε (S.η ω) a) < r}ᶜ ⊆
      ({ω | t < clusterExitTime (Λ ω) ρ} ∩ {ω | ∀ k : ℤ, (cell ε (S.η ω) k ∩ ball 0 ρ).Nonempty →
        ε ^ (2 / (2 - γ) ^ 2 + 1 / (2 + γ) ^ 2) ≤ diam (cell ε (S.η ω) k) ∧
          diam (cell ε (S.η ω) k) ≤ ε ^ (2 / (2 + γ) ^ 2 - 1 / (2 + γ) ^ 2)}ᶜ) ∪
        {ω | cpos ω ≤ κ} ∪ Gᶜ := by
    rintro ω ⟨hT, hbad⟩
    by_contra hcon
    simp only [mem_union, mem_inter_iff, mem_compl_iff, mem_ofPred_eq, not_or, not_and, not_not, not_le] at hcon
    obtain ⟨⟨hcellω, hκω⟩, hGω⟩ := hcon
    obtain ⟨hcode, hfam, hηc⟩ := hGω
    have hcellω := hcellω hT
    apply hbad
    have hΛeq := hcode hT
    have hreg : interior (closure (Λ ω t)) = Λ ω t :=
      StoppedInteriorMargin.interior_closure_eq_self_of_eq hΛeq
    have hΛo : IsOpen (Λ ω t) := hΛeq ▸ isOpen_interior
    have hΛR : Λ ω t ⊆ ball 0 R :=
      IDLALowerBound.subset_ball_div_three_of_lt_clusterExitTime hfam.2.1.monotoneOn ht hT
    have hθpos : 0 < θ ω := by
      simp only [hθdef]
      rw [← hΛeq]
      exact geometryThreshold_pos hreg (R + 1) (by positivity)
    have hcω : 0 < c ω := by
      simp only [hcdef]
      exact ENNReal.toReal_pos (lt_min hθpos one_pos).ne' (min_le_right _ _ |>.trans_lt ENNReal.one_lt_top).ne
    have hκc : κ < c ω := by
      have h := hκω
      simp only [hcposdef, hcω, ite_true] at h
      exact h
    have hθd : ENNReal.ofReal (2 * d) < θ ω := by
      have h1 : ENNReal.ofReal κ < min (θ ω) 1 :=
        (ENNReal.ofReal_lt_iff_lt_toReal hκ.le ((min_le_right _ _).trans_lt ENNReal.one_lt_top).ne).2 hκc
      exact (ENNReal.ofReal_lt_ofReal_iff hκ |>.2 hdκ).trans (h1.trans_le (min_le_left _ _))
    have hwit := witness_of_lt_geometryThreshold hθd
    rw [← hΛeq] at hwit
    refine geometry_of_witness hΛo hreg hΛR denseC_spec.2 hηc hεpos hd hd1 hdδ hdr ?_
      (fun q hqD hqΛ hqR => hwit q hqD hqΛ hqR)
    intro k hk
    obtain ⟨y, hyk, hyΛ⟩ := id hk
    exact (hcellω k ⟨y, hyk, ball_subset_ball (by linarith) (hΛR hyΛ)⟩).2.trans hεd.le
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  rw [hG, add_zero]
  refine (measure_union_le _ _).trans ?_
  exact (add_le_add hεP hPκ).trans (ENNReal.add_halves e).le

end StoppedGeometry

end MatedCRT
