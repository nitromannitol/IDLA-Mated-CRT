import MatedCRT.FirstPass.Derived.LocalMeshSubsequence
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.T12P2D

/-! # A common local mesh subsequence for bounded disks -/

set_option autoImplicit false
noncomputable section

open Set Metric MeasureTheory Filter Topology
open scoped ENNReal

namespace MatedCRT

/-- One deterministic mesh subsequence gives almost sure uniform edge decay
simultaneously on every bounded disk. -/
theorem exists_subseq_all_local_edges_tendsto_zero
    {Ω : Type} [MeasurableSpace Ω] {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    {η' : Ω → C(ℝ, ℂ)} (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω)
    {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n) (hε0 : Tendsto ε atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ ω ∂S.P, ∀ R a : ℝ, 0 < a →
      ∀ᶠ n in atTop, ∀ j k : ℤ,
        S.mult (ε (φ n)) ω j k ≠ 0 →
        vertexPoint (ε (φ n)) (⇑(η' ω)) j ∈ ball (0 : ℂ) R →
        dist (vertexPoint (ε (φ n)) (⇑(η' ω)) j)
          (vertexPoint (ε (φ n)) (⇑(η' ω)) k) < a := by
  let D : ℕ → ℕ → Ω → ℝ≥0∞ := fun k n ω =>
    FirstPass.Derived.maxCellDiam (ε n) (⇑(η' ω)) k
  let Q : ℕ → ℕ → Ω → ℝ := fun k n ω => (min (D k n ω) 1).toReal
  have hq0 (k n : ℕ) (ω : Ω) : 0 ≤ Q k n ω := ENNReal.toReal_nonneg
  have hq (k n : ℕ) (ω : Ω) : ENNReal.ofReal (Q k n ω) = min (D k n ω) 1 :=
    ENNReal.ofReal_toReal (ne_top_of_le_ne_top (by simp) (min_le_right _ _))
  have hQ (k : ℕ) : TendstoInMeasure S.P (Q k) atTop (fun _ => 0) := by
    have hD : TendstoInMeasure S.P (D k) atTop (fun _ => 0) :=
      maxCellDiam_tendstoInMeasure_zero hS hae hε0 k
    apply tendstoInMeasure_of_ne_top
    intro t ht httop
    let d : ℝ := min (t.toReal / 2) (1 / 2)
    have htpos : 0 < t.toReal := ENNReal.toReal_pos ht.ne' httop
    have hd : 0 < d := by dsimp [d]; positivity
    have hdt : ENNReal.ofReal d < t := by
      calc
        ENNReal.ofReal d ≤ ENNReal.ofReal (t.toReal / 2) :=
          ENNReal.ofReal_le_ofReal (min_le_left _ _)
        _ < ENNReal.ofReal t.toReal :=
          (ENNReal.ofReal_lt_ofReal_iff htpos).2 (by linarith)
        _ = t := ENNReal.ofReal_toReal httop
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (hD _ (ENNReal.ofReal_pos.mpr hd)) (fun _ => zero_le) ?_
    intro n
    apply measure_mono
    intro ω hω
    change t ≤ edist (Q k n ω) 0 at hω
    rw [edist_dist, Real.dist_eq, sub_zero, abs_of_nonneg (hq0 k n ω)] at hω
    change ENNReal.ofReal d ≤ edist (D k n ω) 0
    rw [ENNReal.edist_zero_right]
    have h := le_trans hdt.le hω
    rw [hq] at h
    exact le_trans h (min_le_left _ _)
  let : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  obtain ⟨φ, hφ, hφae⟩ :=
    LQGMetric.DFGPS.T12.exists_subseq_ae_tendsto_all hQ
  refine ⟨φ, hφ, ?_⟩
  filter_upwards [hφae, hae, adjacentCellsMeetAeStep 𝒮 γ hγ hγ2 Ω S hS] with ω hlim hη hmeet
  intro R a ha
  obtain ⟨k, hk⟩ := exists_nat_gt R
  let d : ℝ := min (a / 4) (1 / 2)
  have hd : 0 < d := by dsimp [d]; positivity
  have hd1 : d < 1 := by dsimp [d]; linarith [min_le_right (a / 4) (1 / 2 : ℝ)]
  have hda : 2 * d < a := by dsimp [d]; linarith [min_le_left (a / 4) (1 / 2 : ℝ)]
  have hsmall := (tendsto_order.1 (hlim k)).2 _ hd
  filter_upwards [hsmall] with n hn
  intro j l hjl hj
  have hqsmall : ENNReal.ofReal (Q k (φ n) ω) ≤ ENNReal.ofReal d :=
    ENNReal.ofReal_le_ofReal hn.le
  rw [hq] at hqsmall
  have hdlt : ENNReal.ofReal d < 1 := by
    rw [← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2 hd1
  have hmesh : D k (φ n) ω ≤ ENNReal.ofReal d := by
    exact (min_le_iff.mp hqsmall).resolve_right (not_le_of_gt hdlt)
  have hc := hmeet (ε (φ n)) (hε (φ n)) j l hjl
  rw [← hη] at hc
  have hj' : vertexPoint (ε (φ n)) (⇑(η' ω)) j ∈ ball (0 : ℂ) k :=
    ball_subset_ball hk.le hj
  have hb := vertexPoint_dist_le_of_maxCellDiam_le (η' ω).continuous (hε (φ n)).le
    hd.le hd1 hmesh hj' hc
  linarith

end MatedCRT
end
