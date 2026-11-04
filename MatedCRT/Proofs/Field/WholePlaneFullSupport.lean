import MatedCRT.Proofs.Field.WholePlaneCircleBridge
import MatedCRT.Proofs.Sec6.AnnulusHit.Geometry

/-!
# Positivity of whole-plane LQG mass on a fixed ball

The GMC lower-tail estimate proved by Leonardo Bonanno implies that a fixed
nonempty ball has positive mass almost surely. This is one ingredient of the
denominator bound in Lemma 6.5.
-/

namespace MatedCRT.Field

open MeasureTheory ProbabilityTheory Filter Set Metric HarmonicBalls
open scoped ENNReal

theorem wholePlane_lqg_ball_pos_ae {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {γ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (h : HarmonicBalls.IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasure P γ hcirc μ)
    (z : ℂ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ∀ᵐ ω ∂P, 0 < μ ω (ball z ε) := by
  let _ : IsProbabilityMeasure P := h.isProbabilityMeasure
  obtain ⟨δ₀, hδ₀, hbound⟩ := wholePlane_gmc_lower_tail hγ hγ2 h hμ 1 1 zero_lt_one
  have hzero : (P {ω | μ ω (ball z ε) = 0}).toReal = 0 := by
    apply le_antisymm _ ENNReal.toReal_nonneg
    refine le_of_forall_pos_le_add fun t ht => ?_
    let δ := min δ₀ t / 2
    have hδ : 0 < δ := by dsimp [δ]; positivity
    have hδ₀' : δ < δ₀ := by dsimp [δ]; linarith [min_le_left δ₀ t]
    have hδt : δ ≤ t := by dsimp [δ]; linarith [min_le_right δ₀ t]
    let E : Set Ω := {ω | μ ω (ball z ε) <
      ENNReal.ofReal (δ * ε ^ (2 + γ ^ 2 / 2) * Real.exp (γ * hcirc ω ε z))}
    have hsub : {ω | μ ω (ball z ε) = 0} ⊆ E := by
      intro ω hω
      change μ ω (ball z ε) = 0 at hω
      change μ ω (ball z ε) < _
      rw [hω, ENNReal.ofReal_pos]
      positivity
    calc (P {ω | μ ω (ball z ε) = 0}).toReal ≤ (P E).toReal :=
          ENNReal.toReal_mono (measure_ne_top P E) (measure_mono hsub)
      _ ≤ δ := by simpa [E] using hbound δ ⟨hδ, hδ₀'⟩ z ε ⟨hε, hε1⟩
      _ ≤ 0 + t := by simpa using hδt
  have hmeasure : P {ω | μ ω (ball z ε) = 0} = 0 := by
    simpa [ENNReal.toReal_eq_zero_iff, measure_ne_top P _] using hzero
  have hae : ∀ᵐ ω ∂P, μ ω (ball z ε) ≠ 0 := by
    rw [ae_iff]
    simpa using hmeasure
  filter_upwards [hae] with ω hω
  exact bot_lt_iff_ne_bot.mpr hω

/-- The whole-plane LQG measure has full support almost surely. -/
theorem wholePlane_lqg_full_support_ae {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {γ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (h : HarmonicBalls.IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasure P γ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ z : ℂ, ∀ r : ℝ, 0 < r → 0 < μ ω (ball z r) := by
  obtain ⟨d, hd⟩ := TopologicalSpace.exists_dense_seq ℂ
  have hall : ∀ᵐ ω ∂P, ∀ n k : ℕ, 0 < μ ω (ball (d n) (1 / ((k : ℝ) + 2))) := by
    rw [ae_all_iff]
    intro n
    rw [ae_all_iff]
    intro k
    apply wholePlane_lqg_ball_pos_ae hγ hγ2 h hμ
    · positivity
    · have : (1 : ℝ) < (k : ℝ) + 2 := by
        have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
        linarith
      exact (div_lt_one (by positivity)).2 this
  filter_upwards [hall] with ω hω z r hr
  obtain ⟨n, hn⟩ := hd.exists_dist_lt z (show 0 < r / 2 by positivity)
  obtain ⟨k, hk⟩ := exists_nat_gt (2 / r)
  have hk' : 1 / ((k : ℝ) + 2) < r / 2 := by
    have hk0 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
    rw [div_lt_div_iff₀ hk0 (by norm_num : (0 : ℝ) < 2)]
    have hkr : 2 < (k : ℝ) * r := by rwa [div_lt_iff₀ hr] at hk
    nlinarith
  have hsub : ball (d n) (1 / ((k : ℝ) + 2)) ⊆ ball z r := by
    intro x hx
    rw [mem_ball] at hx ⊢
    have htriangle := dist_triangle x (d n) z
    rw [dist_comm z (d n)] at hn
    linarith [htriangle]
  exact (hω n k).trans_le (measure_mono hsub)

/-- Full support gives a uniform positive lower mass on balls centred in a compact set. -/
theorem compact_uniform_ball_mass_pos {μ : Measure ℂ}
    (hμ : ∀ z : ℂ, ∀ r : ℝ, 0 < r → 0 < μ (ball z r))
    {K : Set ℂ} (hK : IsCompact K) {r : ℝ} (hr : 0 < r) :
    0 < ⨅ z ∈ K, μ (ball z r) := by
  classical
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun z : ℂ => ball z (r / 2))
    (fun _ => isOpen_ball) (by
      intro z hz
      exact mem_iUnion.2 ⟨z, mem_ball_self (by positivity)⟩)
  let a : ℝ≥0∞ := t.inf fun z => μ (ball z (r / 2))
  have ha : 0 < a := by
    apply (Finset.lt_inf_iff (by simp : (0 : ℝ≥0∞) < ⊤)).2
    intro z _
    exact hμ z (r / 2) (by positivity)
  refine ha.trans_le (le_iInf fun z => le_iInf fun hz => ?_)
  obtain ⟨w, hw, hzw⟩ := mem_iUnion₂.1 (ht hz)
  have hsub : ball w (r / 2) ⊆ ball z r := by
    intro x hx
    rw [mem_ball] at hx hzw ⊢
    have htriangle := dist_triangle x w z
    rw [dist_comm w z] at htriangle
    linarith
  exact (Finset.inf_le hw).trans (measure_mono hsub)

/-- Almost surely, ball masses are uniformly positive over every compact set of centres. -/
theorem wholePlane_lqg_compact_ball_mass_pos_ae {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {γ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (h : HarmonicBalls.IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasure P γ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ K : Set ℂ, IsCompact K → ∀ r : ℝ, 0 < r →
      0 < ⨅ z ∈ K, μ ω (ball z r) := by
  filter_upwards [wholePlane_lqg_full_support_ae hγ hγ2 h hμ] with ω hω K hK r hr
  exact compact_uniform_ball_mass_pos hω hK hr

/-- The denominator in the unit good-annulus event is almost surely positive. -/
theorem wholePlane_goodAnnulus_denominator_pos_ae {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {γ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (h : HarmonicBalls.IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasure P γ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ c₀ : ℝ, 0 < c₀ →
      0 < ⨅ w ∈ annulus 0 1 (2 * 1), μ ω (ball w (c₀ * 1)) := by
  filter_upwards [wholePlane_lqg_compact_ball_mass_pos_ae hγ hγ2 h hμ] with ω hω c₀ hc₀
  have hpos := hω (closedBall (0 : ℂ) 2) (isCompact_closedBall _ _) c₀ hc₀
  refine hpos.trans_le (le_iInf fun w => le_iInf fun hw => ?_)
  have hw' : w ∈ closedBall (0 : ℂ) 2 := by
    have hdist := (MatedCRT.mem_annulus_iff_norm.mp hw).2
    simp only [sub_zero, mul_one] at hdist
    simpa [mem_closedBall, dist_eq_norm] using hdist.le
  simpa only [mul_one] using (iInf₂_le w hw' :
    (⨅ v ∈ closedBall (0 : ℂ) 2, μ ω (ball v c₀)) ≤ μ ω (ball w c₀))

end MatedCRT.Field
