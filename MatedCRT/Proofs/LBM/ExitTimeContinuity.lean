import MatedCRT.Proofs.LBM.ExitTimeChange

/-! Stability of ball exit times under locally uniform path perturbations. -/

namespace MatedCRT

open MeasureTheory Set Filter Topology HarmonicBalls MarkovProcess Metric
open scoped ENNReal NNReal

/-- A path stays a positive distance inside a ball on each compact time interval
strictly before its exit time. -/
theorem exists_ball_margin_before_exit (p : ContinuousPath ℂ) (z : ℂ) (r : ℝ)
    {u : ℝ≥0} (hu : (u : ℝ≥0∞) < ContinuousPath.exitTime (ball z r) p) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t ≤ u, dist (p t) z ≤ r - δ := by
  have hcont : Continuous (fun t : ℝ≥0 => dist (p t) z) := p.continuous.dist continuous_const
  obtain ⟨s, hs, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc (0 : ℝ≥0) u).Nonempty from ⟨0, bot_le, bot_le⟩) hcont.continuousOn
  have hslt : (s : ℝ≥0∞) < ContinuousPath.exitTime (ball z r) p :=
    (ENNReal.coe_le_coe.mpr hs.2).trans_lt hu
  have hsball : p s ∈ ball z r := ContinuousPath.mem_of_lt_exitTime _ _ _ hslt
  have hgap : 0 < r - dist (p s) z := by
    have := mem_ball.mp hsball
    linarith
  refine ⟨r - dist (p s) z, hgap, ?_⟩
  intro t ht
  have hle := hmax (show t ∈ Icc (0 : ℝ≥0) u from ⟨bot_le, ht⟩)
  change dist (p t) z ≤ dist (p s) z at hle
  linarith

/-- Uniformly close paths have exit time between a strict pre-exit time and a
time at which the reference path is outside the closed ball. -/
theorem exists_uniform_ball_exit_bounds (p : ContinuousPath ℂ) (z : ℂ) (r : ℝ)
    {u v : ℝ≥0} (huv : u ≤ v)
    (hu : (u : ℝ≥0∞) < ContinuousPath.exitTime (ball z r) p)
    (hv : p v ∉ closedBall z r) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ g : ℝ≥0 → ℂ,
      (∀ t ≤ v, dist (g t) (p t) < δ) →
      (u : ℝ≥0∞) ≤ pathExitTime (ball z r) g ∧
        pathExitTime (ball z r) g ≤ (v : ℝ≥0∞) := by
  obtain ⟨a, ha, hinside⟩ := exists_ball_margin_before_exit p z r hu
  have hout : r < dist (p v) z := by
    simpa only [mem_closedBall, not_le] using hv
  let δ := min a (dist (p v) z - r) / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδa : δ < a := by dsimp [δ]; have := min_le_left a (dist (p v) z - r); linarith
  have hδb : δ < dist (p v) z - r := by
    dsimp [δ]; have := min_le_right a (dist (p v) z - r); linarith
  refine ⟨δ, hδ, ?_⟩
  intro g hg
  constructor
  · unfold pathExitTime
    apply le_sInf
    rintro _ ⟨t, rfl, ht⟩
    rw [ENNReal.coe_le_coe]
    by_contra hn
    have htu : t ≤ u := (lt_of_not_ge hn).le
    have hdist := hg t (htu.trans huv)
    have htriangle := dist_triangle (g t) (p t) z
    apply ht
    apply mem_ball.mpr
    have := hinside t htu
    linarith
  · unfold pathExitTime
    apply sInf_le
    refine ⟨v, rfl, ?_⟩
    intro hmem
    have hdist := hg v le_rfl
    have htriangle := dist_triangle (p v) (g v) z
    have hsym : dist (p v) (g v) = dist (g v) (p v) := dist_comm _ _
    have hmem' := mem_ball.mp hmem
    linarith

/-- A strict crossing gives a stable upper bound for exit times. -/
theorem exists_uniform_ball_exit_upper_bound (p : ContinuousPath ℂ) (z : ℂ) (r : ℝ)
    {v : ℝ≥0} (hv : p v ∉ closedBall z r) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ g : ℝ≥0 → ℂ,
      dist (g v) (p v) < δ → pathExitTime (ball z r) g ≤ (v : ℝ≥0∞) := by
  have hout : r < dist (p v) z := by simpa only [mem_closedBall, not_le] using hv
  refine ⟨(dist (p v) z - r) / 2, by linarith, ?_⟩
  intro g hg
  unfold pathExitTime
  apply sInf_le
  refine ⟨v, rfl, ?_⟩
  intro hmem
  have htriangle := dist_triangle (p v) (g v) z
  have hsym : dist (p v) (g v) = dist (g v) (p v) := dist_comm _ _
  have hmem' := mem_ball.mp hmem
  linarith

/-- At a finite regular exit, locally uniform convergence of paths implies
convergence of their ball exit times. The approximating paths need not be continuous. -/
theorem tendsto_ball_exitTime_of_locally_uniform {ι : Type*} {l : Filter ι}
    (p : ContinuousPath ℂ) (z : ℂ) (r : ℝ)
    (hfin : ContinuousPath.exitTime (ball z r) p < ⊤)
    (hregular : ∃ᶠ t in 𝓝[>] (ContinuousPath.exitTime (ball z r) p).toNNReal,
      p t ∉ closedBall z r)
    (g : ι → ℝ≥0 → ℂ)
    (hconv : ∀ v : ℝ≥0, ∀ δ : ℝ, 0 < δ →
      ∀ᶠ i in l, ∀ t ≤ v, dist (g i t) (p t) < δ) :
    Tendsto (fun i => pathExitTime (ball z r) (g i)) l
      (𝓝 (ContinuousPath.exitTime (ball z r) p)) := by
  let τ := ContinuousPath.exitTime (ball z r) p
  have htau : ((τ.toNNReal : ℝ≥0) : ℝ≥0∞) = τ := ENNReal.coe_toNNReal (ne_of_lt hfin)
  have hexists : ∃ v : ℝ≥0, τ.toNNReal < v ∧ p v ∉ closedBall z r := by
    obtain ⟨v, hvout, hvgt⟩ := (hregular.and_eventually self_mem_nhdsWithin).exists
    exact ⟨v, hvgt, hvout⟩
  apply tendsto_order.mpr
  constructor
  · intro a ha
    obtain ⟨b, hab, hbτ⟩ := exists_between ha
    have hbtop : b ≠ ⊤ := ne_of_lt (hbτ.trans hfin)
    let u := b.toNNReal
    have hbu : (u : ℝ≥0∞) = b := ENNReal.coe_toNNReal hbtop
    have hu : (u : ℝ≥0∞) < τ := hbu ▸ hbτ
    obtain ⟨v, hvτ, hvout⟩ := hexists
    have huv : u ≤ v := by
      have hult : u < τ.toNNReal := by
        apply ENNReal.coe_lt_coe.mp
        simpa only [htau] using hu
      exact le_of_lt (hult.trans hvτ)
    obtain ⟨δ, hδ, hbound⟩ := exists_uniform_ball_exit_bounds p z r huv hu hvout
    filter_upwards [hconv v δ hδ] with i hi
    exact hab.trans_le (hbu ▸ (hbound (g i) hi).1)
  · intro a ha
    by_cases hatop : a = ⊤
    · obtain ⟨v, _, hvout⟩ := hexists
      obtain ⟨δ, hδ, hbound⟩ := exists_uniform_ball_exit_upper_bound p z r hvout
      filter_upwards [hconv v δ hδ] with i hi
      rw [hatop]
      exact (hbound (g i) (hi v le_rfl)).trans_lt ENNReal.coe_lt_top
    · have hta : τ.toNNReal < a.toNNReal := by
        apply ENNReal.coe_lt_coe.mp
        simpa only [htau, ENNReal.coe_toNNReal hatop] using ha
      obtain ⟨v, hvout, hv⟩ := (hregular.and_eventually (Ioo_mem_nhdsGT hta)).exists
      obtain ⟨δ, hδ, hbound⟩ := exists_uniform_ball_exit_upper_bound p z r hvout
      filter_upwards [hconv v δ hδ] with i hi
      have hva : (v : ℝ≥0∞) < a := by
        rw [← ENNReal.coe_toNNReal hatop, ENNReal.coe_lt_coe]
        exact hv.2
      exact (hbound (g i) (hi v le_rfl)).trans_lt hva

/-- The exit position also converges at a finite regular exit under local
uniform convergence of the approximating paths. -/
theorem tendsto_ball_exitPosition_of_locally_uniform {ι : Type*} {l : Filter ι}
    (p : ContinuousPath ℂ) (z : ℂ) (r : ℝ)
    (hfin : ContinuousPath.exitTime (ball z r) p < ⊤)
    (hregular : ∃ᶠ t in 𝓝[>] (ContinuousPath.exitTime (ball z r) p).toNNReal,
      p t ∉ closedBall z r)
    (g : ι → ℝ≥0 → ℂ)
    (hconv : ∀ v : ℝ≥0, ∀ δ : ℝ, 0 < δ →
      ∀ᶠ i in l, ∀ t ≤ v, dist (g i t) (p t) < δ) :
    Tendsto (fun i => pathExitPosition (ball z r) (g i)) l
      (𝓝 (p (ContinuousPath.exitTime (ball z r) p).toNNReal)) := by
  let τ := ContinuousPath.exitTime (ball z r) p
  let τg : ι → ℝ≥0 := fun i => (pathExitTime (ball z r) (g i)).toNNReal
  have htimes : Tendsto τg l (𝓝 τ.toNNReal) :=
    (ENNReal.tendsto_toNNReal (ne_of_lt hfin)).comp
      (tendsto_ball_exitTime_of_locally_uniform p z r hfin hregular g hconv)
  have hpositions : Tendsto (fun i => p (τg i)) l (𝓝 (p τ.toNNReal)) :=
    (p.continuous.tendsto τ.toNNReal).comp htimes
  let v : ℝ≥0 := τ.toNNReal + 1
  have hv : τ.toNNReal < v := by simp [v]
  have hevent : ∀ᶠ i in l, τg i < v := htimes.eventually (Iio_mem_nhds hv)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  have hp := (Metric.tendsto_nhds.mp hpositions) (ε / 2) hε2
  filter_upwards [hevent, hconv v (ε / 2) hε2, hp] with i hi hclose hpclose
  change dist (g i (τg i)) (p τ.toNNReal) < ε
  have hgclose := hclose (τg i) hi.le
  have htriangle := dist_triangle (g i (τg i)) (p (τg i)) (p τ.toNNReal)
  linarith

end MatedCRT
