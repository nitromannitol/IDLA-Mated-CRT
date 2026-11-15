import MatedCRT.FirstPass.Derived.LocalMeshInMeasure

/-! # Almost sure local mesh bounds along a subsequence -/

set_option autoImplicit false
noncomputable section

open Set Metric MeasureTheory Filter Topology
open scoped ENNReal

namespace MatedCRT

/-- A deterministic subsequence has vanishing local cell diameters almost surely. -/
theorem exists_subseq_maxCellDiam_tendsto_zero
    {Ω : Type} [MeasurableSpace Ω] {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    {η' : Ω → C(ℝ, ℂ)} (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω)
    {ε : ℕ → ℝ} (hε0 : Tendsto ε atTop (𝓝 0)) (R : ℝ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ ω ∂S.P,
      Tendsto (fun n => FirstPass.Derived.maxCellDiam (ε (φ n)) (⇑(η' ω)) R)
        atTop (𝓝 0) := by
  let D : ℕ → Ω → ℝ≥0∞ := fun n ω =>
    FirstPass.Derived.maxCellDiam (ε n) (⇑(η' ω)) R
  let Q : ℕ → Ω → ℝ := fun n ω => (min (D n ω) 1).toReal
  have hq0 (n : ℕ) (ω : Ω) : 0 ≤ Q n ω := ENNReal.toReal_nonneg
  have hq (n : ℕ) (ω : Ω) : ENNReal.ofReal (Q n ω) = min (D n ω) 1 := by
    exact ENNReal.ofReal_toReal (ne_top_of_le_ne_top (by simp) (min_le_right _ _))
  have hD : TendstoInMeasure S.P D atTop (fun _ => 0) :=
    maxCellDiam_tendstoInMeasure_zero hS hae hε0 R
  have hQ : TendstoInMeasure S.P Q atTop (fun _ => 0) := by
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
          (ENNReal.ofReal_lt_ofReal_iff (ENNReal.toReal_pos ht.ne' httop)).2 (by
            linarith [ENNReal.toReal_pos ht.ne' httop])
        _ = t := ENNReal.ofReal_toReal httop
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hD _ (ENNReal.ofReal_pos.mpr hd)) (fun _ => zero_le) ?_
    intro n
    apply measure_mono
    intro ω hω
    change t ≤ edist (Q n ω) 0 at hω
    rw [edist_dist, Real.dist_eq, sub_zero, abs_of_nonneg (hq0 n ω)] at hω
    change ENNReal.ofReal d ≤ edist (D n ω) 0
    rw [ENNReal.edist_zero_right]
    have : ENNReal.ofReal d ≤ ENNReal.ofReal (Q n ω) := le_trans hdt.le hω
    rw [hq] at this
    exact le_trans this (min_le_left _ _)
  obtain ⟨φ, hφ, hφae⟩ := hQ.exists_seq_tendsto_ae
  refine ⟨φ, hφ, ?_⟩
  filter_upwards [hφae] with ω hω
  apply tendsto_order.2
  constructor
  · intro a ha
    exact (not_lt_of_ge bot_le ha).elim
  · intro b hb
    have hb' : 0 < min b 1 := lt_min hb (by simp)
    have hbtop : min b 1 ≠ ⊤ := ne_top_of_le_ne_top (by simp) (min_le_right _ _)
    have hbr : 0 < (min b 1).toReal := ENNReal.toReal_pos hb'.ne' hbtop
    have he := (tendsto_order.1 hω).2 _ hbr
    filter_upwards [he] with n hn
    have hn' : ENNReal.ofReal (Q (φ n) ω) < min b 1 := by
      rw [← ENNReal.ofReal_toReal hbtop]
      exact (ENNReal.ofReal_lt_ofReal_iff hbr).2 hn
    rw [hq] at hn'
    have : D (φ n) ω < min b 1 := by
      exact (min_lt_iff.mp hn').resolve_right (not_lt_of_ge (min_le_right _ _))
    exact lt_of_lt_of_le this (min_le_left _ _)

/-- Along one deterministic subsequence, all edges starting in a fixed disk
have vanishing embedded length almost surely. -/
theorem exists_subseq_local_edges_tendsto_zero
    {Ω : Type} [MeasurableSpace Ω] {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    {η' : Ω → C(ℝ, ℂ)} (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω)
    {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n) (hε0 : Tendsto ε atTop (𝓝 0))
    (R : ℝ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ ω ∂S.P, ∀ a : ℝ, 0 < a →
      ∀ᶠ n in atTop, ∀ j k : ℤ,
        S.mult (ε (φ n)) ω j k ≠ 0 →
        vertexPoint (ε (φ n)) (⇑(η' ω)) j ∈ ball (0 : ℂ) R →
        dist (vertexPoint (ε (φ n)) (⇑(η' ω)) j)
          (vertexPoint (ε (φ n)) (⇑(η' ω)) k) < a := by
  obtain ⟨φ, hφ, hφae⟩ := exists_subseq_maxCellDiam_tendsto_zero hS hae hε0 R
  refine ⟨φ, hφ, ?_⟩
  filter_upwards [hφae, hae, adjacentCellsMeetAeStep 𝒮 γ hγ hγ2 Ω S hS] with ω hlim hη hmeet
  intro a ha
  let d : ℝ := min (a / 4) (1 / 2)
  have hd : 0 < d := by dsimp [d]; positivity
  have hd1 : d < 1 := by dsimp [d]; linarith [min_le_right (a / 4) (1 / 2 : ℝ)]
  have hda : 2 * d < a := by dsimp [d]; linarith [min_le_left (a / 4) (1 / 2 : ℝ)]
  have hsmall := (tendsto_order.1 hlim).2 _ (ENNReal.ofReal_pos.mpr hd)
  filter_upwards [hsmall] with n hn
  intro j k hjk hj
  have hc := hmeet (ε (φ n)) (hε (φ n)) j k hjk
  rw [← hη] at hc
  have hb := vertexPoint_dist_le_of_maxCellDiam_le (η' ω).continuous (hε (φ n)).le
    hd.le hd1 hn.le hj hc
  linarith

end MatedCRT
end
