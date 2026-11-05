import MatedCRT.Proofs.LBM.LocalUniformDistance
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Continuous mapping for almost-everywhere continuous path functionals

Theorem 2.11 gives convergence in probability of the conditional expectations of
bounded Lipschitz path functionals. This file extends it to a bounded path
functional `G` that is continuous, for the local uniform distance, at almost
every limiting path. The extension uses the Pasch--Hausdorff (inf-convolution)
envelopes `U_k G (w) = sup_v (G v - k d(v, w))`, which are bounded `k`-Lipschitz
functionals decreasing to `G` at its continuity points.
-/

namespace MatedCRT

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

/-! ## The local uniform distance is a pseudometric -/

theorem localUniformDist_nonneg (f g : ℝ≥0 → ℂ) : 0 ≤ localUniformDist f g :=
  tsum_nonneg fun _ => mul_nonneg (by positivity) ENNReal.toReal_nonneg

theorem localUniformDist_self (f : ℝ≥0 → ℂ) : localUniformDist f f = 0 := by
  simp [localUniformDist]

theorem localUniformDist_comm (f g : ℝ≥0 → ℂ) :
    localUniformDist f g = localUniformDist g f := by
  unfold localUniformDist
  simp_rw [norm_sub_rev (f _) (g _)]

theorem toReal_min_one_le_add {x a b : ℝ≥0∞} (h : x ≤ a + b) :
    (min 1 x).toReal ≤ (min 1 a).toReal + (min 1 b).toReal := by
  have hfin : ∀ c : ℝ≥0∞, min 1 c ≠ ⊤ := fun c =>
    ((min_le_left 1 c).trans_lt ENNReal.one_lt_top).ne
  rw [← ENNReal.toReal_add (hfin a) (hfin b)]
  refine ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfin a, hfin b⟩) ?_
  by_cases ha : 1 ≤ a
  · rw [min_eq_left ha]
    exact (min_le_left _ _).trans le_self_add
  by_cases hb : 1 ≤ b
  · rw [min_eq_left hb]
    exact (min_le_left _ _).trans le_add_self
  rw [min_eq_right (not_le.mp ha).le, min_eq_right (not_le.mp hb).le]
  exact (min_le_right _ _).trans h

theorem localUniformDist_triangle (f g h : ℝ≥0 → ℂ) :
    localUniformDist f h ≤ localUniformDist f g + localUniformDist g h := by
  unfold localUniformDist
  rw [← Summable.tsum_add (summable_localUniformDist_terms f g)
    (summable_localUniformDist_terms g h)]
  refine Summable.tsum_le_tsum (fun k => ?_) (summable_localUniformDist_terms f h)
    ((summable_localUniformDist_terms f g).add (summable_localUniformDist_terms g h))
  rw [← mul_add]
  refine mul_le_mul_of_nonneg_left (toReal_min_one_le_add ?_) (by positivity)
  refine iSup_le fun t => ?_
  calc ENNReal.ofReal ‖f t - h t‖ ≤ ENNReal.ofReal (‖f t - g t‖ + ‖g t - h t‖) :=
        ENNReal.ofReal_le_ofReal (norm_sub_le_norm_sub_add_norm_sub _ _ _)
    _ = ENNReal.ofReal ‖f t - g t‖ + ENNReal.ofReal ‖g t - h t‖ :=
        ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)
    _ ≤ _ := add_le_add
        (le_iSup (fun s : Icc (0 : ℝ≥0) (k + 1 : ℕ) => ENNReal.ofReal ‖f s - g s‖) t)
        (le_iSup (fun s : Icc (0 : ℝ≥0) (k + 1 : ℕ) => ENNReal.ofReal ‖g s - h s‖) t)

/-! ## Pasch--Hausdorff envelopes -/

/-- A path functional `G` is *continuous at* `w` for the local uniform distance. -/
def PathFunctionalContinuousAt (G : (ℝ≥0 → ℂ) → ℝ) (w : ℝ≥0 → ℂ) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ ρ : ℝ, 0 < ρ ∧ ∀ v, localUniformDist v w < ρ → |G v - G w| ≤ η

/-- The Pasch--Hausdorff upper envelope `sup_v (G v - k d(v, w))` of a path functional. -/
noncomputable def pathUpperEnvelope (G : (ℝ≥0 → ℂ) → ℝ) (k : ℝ) (w : ℝ≥0 → ℂ) : ℝ :=
  ⨆ v, (G v - k * localUniformDist v w)

section Envelope

variable {G : (ℝ≥0 → ℂ) → ℝ} (hG : ∀ w, |G w| ≤ 1) {k : ℝ} (hk : 0 ≤ k)
include hG hk

theorem bddAbove_pathUpperEnvelope (w : ℝ≥0 → ℂ) :
    BddAbove (range fun v => G v - k * localUniformDist v w) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨v, rfl⟩
  have := (abs_le.mp (hG v)).2
  have := mul_nonneg hk (localUniformDist_nonneg v w)
  linarith

theorem le_pathUpperEnvelope (w : ℝ≥0 → ℂ) : G w ≤ pathUpperEnvelope G k w := by
  refine le_ciSup_of_le (bddAbove_pathUpperEnvelope hG hk w) w ?_
  rw [localUniformDist_self, mul_zero, sub_zero]

theorem pathUpperEnvelope_le_one (w : ℝ≥0 → ℂ) : pathUpperEnvelope G k w ≤ 1 := by
  refine ciSup_le fun v => ?_
  have := (abs_le.mp (hG v)).2
  have := mul_nonneg hk (localUniformDist_nonneg v w)
  linarith

theorem abs_pathUpperEnvelope_le_one (w : ℝ≥0 → ℂ) : |pathUpperEnvelope G k w| ≤ 1 := by
  have h1 := le_pathUpperEnvelope hG hk w
  have h2 := pathUpperEnvelope_le_one hG hk w
  have h3 := (abs_le.mp (hG w)).1
  exact abs_le.mpr ⟨by linarith, h2⟩

theorem pathUpperEnvelope_le_add (w w' : ℝ≥0 → ℂ) :
    pathUpperEnvelope G k w ≤ pathUpperEnvelope G k w' + k * localUniformDist w w' := by
  refine ciSup_le fun v => ?_
  have htri := localUniformDist_triangle v w w'
  have hle : G v - k * localUniformDist v w' ≤ pathUpperEnvelope G k w' :=
    le_ciSup (bddAbove_pathUpperEnvelope hG hk w') v
  have := mul_le_mul_of_nonneg_left htri hk
  nlinarith

theorem isBoundedLipschitzPathFunctional_pathUpperEnvelope :
    IsBoundedLipschitzPathFunctional (pathUpperEnvelope G k) := by
  refine ⟨abs_pathUpperEnvelope_le_one hG hk, k, fun w w' => abs_sub_le_iff.mpr ⟨?_, ?_⟩⟩
  · have := pathUpperEnvelope_le_add hG hk w w'
    linarith
  · have := pathUpperEnvelope_le_add hG hk w' w
    rw [localUniformDist_comm] at this
    linarith

end Envelope

/-- At a continuity point, the envelopes `U_n G` converge to `G` as `n → ∞`. -/
theorem tendsto_pathUpperEnvelope {G : (ℝ≥0 → ℂ) → ℝ} (hG : ∀ w, |G w| ≤ 1)
    {w : ℝ≥0 → ℂ} (hw : PathFunctionalContinuousAt G w) :
    Tendsto (fun n : ℕ => pathUpperEnvelope G n w) atTop (𝓝 (G w)) := by
  refine tendsto_order.2 ⟨fun a ha => Eventually.of_forall fun n =>
    ha.trans_le (le_pathUpperEnvelope hG (Nat.cast_nonneg n) w), fun a ha => ?_⟩
  obtain ⟨ρ, hρ, hcont⟩ := hw ((a - G w) / 2) (by linarith)
  obtain ⟨N, hN⟩ := exists_nat_gt (2 / ρ)
  filter_upwards [eventually_ge_atTop N] with n hn
  have hnρ : 2 ≤ (n : ℝ) * ρ := by
    have h1 : (N : ℝ) ≤ n := by exact_mod_cast hn
    have h2 : 2 / ρ * ρ = 2 := div_mul_cancel₀ 2 hρ.ne'
    nlinarith
  refine lt_of_le_of_lt (ciSup_le fun v => ?_) (show G w + (a - G w) / 2 < a by linarith)
  have hd := localUniformDist_nonneg v w
  have hGw := (abs_le.mp (hG w)).1
  have hGv := (abs_le.mp (hG v)).2
  rcases lt_or_ge (localUniformDist v w) ρ with hlt | hge
  · have := (abs_le.mp (hcont v hlt)).2
    nlinarith [mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) hd]
  · have : (n : ℝ) * ρ ≤ n * localUniformDist v w :=
      mul_le_mul_of_nonneg_left hge (Nat.cast_nonneg n)
    linarith

theorem pathFunctionalContinuousAt_neg {G : (ℝ≥0 → ℂ) → ℝ} {w : ℝ≥0 → ℂ}
    (hw : PathFunctionalContinuousAt G w) : PathFunctionalContinuousAt (fun v => -G v) w := by
  intro η hη
  obtain ⟨ρ, hρ, h⟩ := hw η hη
  refine ⟨ρ, hρ, fun v hv => ?_⟩
  rw [show -G v - -G w = -(G v - G w) by ring, abs_neg]
  exact h v hv

/-! ## Convergence in probability by sandwiching -/

theorem tendstoInProbability_neg {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {V : ℝ → Ω → ℝ} {V' : Ω → ℝ} (h : TendstoInProbability P V V') :
    TendstoInProbability P (fun ε ω => -V ε ω) (fun ω => -V' ω) := by
  intro δ hδ
  have heq : ∀ ε ω, |(-V ε ω) - (-V' ω)| = |V ε ω - V' ω| := fun ε ω => by
    rw [neg_sub_neg, abs_sub_comm]
  simp only [heq]
  exact h δ hδ

/-- If `X` is squeezed between `L k` and `U k`, these converge in probability to
`Llim k` and `Ulim k`, and `Ulim k`, `Llim k` converge to `Y` in probability as
`k → ∞`, then `X` converges to `Y` in probability. -/
theorem tendstoInProbability_of_sandwich {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℝ → Ω → ℝ) (Y : Ω → ℝ) (U L : ℕ → ℝ → Ω → ℝ) (Ulim Llim : ℕ → Ω → ℝ)
    (hU : ∀ k, TendstoInProbability P (U k) (Ulim k))
    (hL : ∀ k, TendstoInProbability P (L k) (Llim k))
    (hXU : ∀ k ε ω, X ε ω ≤ U k ε ω) (hLX : ∀ k ε ω, L k ε ω ≤ X ε ω)
    (hUY : ∀ δ : ℝ, 0 < δ → Tendsto (fun k => P {ω | δ < |Ulim k ω - Y ω|}) atTop (𝓝 0))
    (hLY : ∀ δ : ℝ, 0 < δ → Tendsto (fun k => P {ω | δ < |Llim k ω - Y ω|}) atTop (𝓝 0)) :
    TendstoInProbability P X Y := by
  intro δ hδ
  have hδ2 : 0 < δ / 2 := by linarith
  rw [ENNReal.tendsto_nhds_zero]
  intro e he
  set q : ℝ≥0∞ := e / 2 / 2 with hqdef
  have hq : 0 < q := ENNReal.div_pos (ENNReal.div_pos he.ne' ENNReal.ofNat_ne_top).ne'
    ENNReal.ofNat_ne_top
  have hsum : q + q + q + q = e := by
    rw [hqdef, add_assoc (e / 2 / 2 + e / 2 / 2), ENNReal.add_halves, ENNReal.add_halves]
  obtain ⟨k, hkU, hkL⟩ := ((ENNReal.tendsto_nhds_zero.1 (hUY _ hδ2) q hq).and
    (ENNReal.tendsto_nhds_zero.1 (hLY _ hδ2) q hq)).exists
  filter_upwards [ENNReal.tendsto_nhds_zero.1 (hU k _ hδ2) q hq,
    ENNReal.tendsto_nhds_zero.1 (hL k _ hδ2) q hq] with ε hεU hεL
  calc P {ω | δ < |X ε ω - Y ω|}
      ≤ P ((({ω | δ / 2 < |U k ε ω - Ulim k ω|} ∪ {ω | δ / 2 < |Ulim k ω - Y ω|}) ∪
          {ω | δ / 2 < |L k ε ω - Llim k ω|}) ∪ {ω | δ / 2 < |Llim k ω - Y ω|}) := by
        apply measure_mono
        intro ω hω
        change δ < |X ε ω - Y ω| at hω
        by_contra hcon
        simp only [mem_union, not_or] at hcon
        obtain ⟨⟨⟨hA, hB⟩, hC⟩, hD⟩ := hcon
        change ¬ (δ / 2 < |U k ε ω - Ulim k ω|) at hA
        change ¬ (δ / 2 < |Ulim k ω - Y ω|) at hB
        change ¬ (δ / 2 < |L k ε ω - Llim k ω|) at hC
        change ¬ (δ / 2 < |Llim k ω - Y ω|) at hD
        have hA' := abs_le.mp (not_lt.mp hA)
        have hB' := abs_le.mp (not_lt.mp hB)
        have hC' := abs_le.mp (not_lt.mp hC)
        have hD' := abs_le.mp (not_lt.mp hD)
        have h1 := hXU k ε ω
        have h2 := hLX k ε ω
        rcases lt_abs.mp hω with h | h <;> linarith [hA'.1, hA'.2, hB'.1, hB'.2, hC'.1, hC'.2,
          hD'.1, hD'.2]
    _ ≤ P {ω | δ / 2 < |U k ε ω - Ulim k ω|} + P {ω | δ / 2 < |Ulim k ω - Y ω|} +
          P {ω | δ / 2 < |L k ε ω - Llim k ω|} + P {ω | δ / 2 < |Llim k ω - Y ω|} :=
        by
          refine (measure_union_le _ _).trans ?_
          gcongr
          refine (measure_union_le _ _).trans ?_
          gcongr
          exact measure_union_le _ _
    _ ≤ q + q + q + q := by gcongr
    _ = e := hsum

/-- Almost-sure convergence of almost-everywhere measurable variables gives
convergence of the strict-error probabilities to zero. -/
theorem tendsto_measure_abs_sub_gt_of_ae_tendsto_nat {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (V : ℕ → Ω → ℝ) (Y : Ω → ℝ)
    (hV : ∀ n, AEMeasurable (V n) P)
    (hconv : ∀ᵐ ω ∂P, Tendsto (fun n => V n ω) atTop (𝓝 (Y ω)))
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n => P {ω | δ < |V n ω - Y ω|}) atTop (𝓝 0) := by
  have hmeas := tendstoInMeasure_of_tendsto_ae (fun n => (hV n).aestronglyMeasurable) hconv
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (hmeas (ENNReal.ofReal δ) (ENNReal.ofReal_pos.2 hδ))
    (fun _ => zero_le) fun n => measure_mono fun ω hω => ?_
  change δ < |V n ω - Y ω| at hω
  change ENNReal.ofReal δ ≤ edist (V n ω) (Y ω)
  rw [edist_dist, Real.dist_eq]
  exact ENNReal.ofReal_le_ofReal hω.le

/-! ## Continuous mapping for almost-everywhere continuous functionals -/

/-- Dominated convergence of the envelopes along almost every continuity point. -/
theorem tendsto_integral_pathUpperEnvelope {β : Type*} [MeasurableSpace β]
    (μ : Measure β) [IsFiniteMeasure μ] {G : (ℝ≥0 → ℂ) → ℝ} (hG : ∀ w, |G w| ≤ 1)
    (X : β → ℝ≥0 → ℂ)
    (hmeas : ∀ n : ℕ, AEStronglyMeasurable (fun b => pathUpperEnvelope G n (X b)) μ)
    (hcont : ∀ᵐ b ∂μ, PathFunctionalContinuousAt G (X b)) :
    Tendsto (fun n : ℕ => ∫ b, pathUpperEnvelope G n (X b) ∂μ) atTop
      (𝓝 (∫ b, G (X b) ∂μ)) := by
  refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ)) hmeas
    (integrable_const 1) (fun n => Eventually.of_forall fun b => ?_) ?_
  · rw [Real.norm_eq_abs]
    exact abs_pathUpperEnvelope_le_one hG (Nat.cast_nonneg n) (X b)
  · filter_upwards [hcont] with b hb
    exact tendsto_pathUpperEnvelope hG hb

/-- **Continuous mapping in probability.** If the conditional expectations of
every bounded Lipschitz path functional converge in probability, then so do those
of a bounded functional `G` which is continuous at almost every limiting path.
The measurability hypotheses concern the envelopes `U_n (± G)` only. -/
theorem tendstoInProbability_of_ae_continuous_pathFunctional
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (Q : ℝ → Ω → Measure α) (hQ : ∀ ε ω, IsFiniteMeasure (Q ε ω))
    (W : ℝ → Ω → α → ℝ≥0 → ℂ)
    (R : Ω → Measure β) (hR : ∀ ω, IsFiniteMeasure (R ω)) (X : Ω → β → ℝ≥0 → ℂ)
    (hBL : ∀ F, IsBoundedLipschitzPathFunctional F →
      TendstoInProbability P (fun ε ω => ∫ x, F (W ε ω x) ∂(Q ε ω))
        (fun ω => ∫ b, F (X ω b) ∂(R ω)))
    (G : (ℝ≥0 → ℂ) → ℝ) (hG : ∀ w, |G w| ≤ 1)
    (hGW : ∀ ε ω, AEStronglyMeasurable (fun x => G (W ε ω x)) (Q ε ω))
    (hFW : ∀ F, IsBoundedLipschitzPathFunctional F → ∀ ε ω,
      AEStronglyMeasurable (fun x => F (W ε ω x)) (Q ε ω))
    (hFX : ∀ F, IsBoundedLipschitzPathFunctional F → ∀ᵐ ω ∂P,
      AEStronglyMeasurable (fun b => F (X ω b)) (R ω))
    (hFXω : ∀ F, IsBoundedLipschitzPathFunctional F →
      AEMeasurable (fun ω => ∫ b, F (X ω b) ∂(R ω)) P)
    (hcont : ∀ᵐ ω ∂P, ∀ᵐ b ∂(R ω), PathFunctionalContinuousAt G (X ω b)) :
    TendstoInProbability P (fun ε ω => ∫ x, G (W ε ω x) ∂(Q ε ω))
      (fun ω => ∫ b, G (X ω b) ∂(R ω)) := by
  have hG' : ∀ w, |(fun v => -G v) w| ≤ 1 := fun w => by simpa only [abs_neg] using hG w
  have hBLU := fun n : ℕ =>
    isBoundedLipschitzPathFunctional_pathUpperEnvelope hG (Nat.cast_nonneg (α := ℝ) n)
  have hBLL := fun n : ℕ =>
    isBoundedLipschitzPathFunctional_pathUpperEnvelope hG' (Nat.cast_nonneg (α := ℝ) n)
  have hint : ∀ ε ω (F : (ℝ≥0 → ℂ) → ℝ), (∀ w, |F w| ≤ 1) →
      AEStronglyMeasurable (fun x => F (W ε ω x)) (Q ε ω) →
      Integrable (fun x => F (W ε ω x)) (Q ε ω) := fun ε ω F hF hm => by
    have := hQ ε ω
    exact Integrable.of_bound hm 1 (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact hF _)
  apply tendstoInProbability_of_sandwich P _ _
    (fun n ε ω => ∫ x, pathUpperEnvelope G n (W ε ω x) ∂(Q ε ω))
    (fun n ε ω => -∫ x, pathUpperEnvelope (fun v => -G v) n (W ε ω x) ∂(Q ε ω))
    (fun n ω => ∫ b, pathUpperEnvelope G n (X ω b) ∂(R ω))
    (fun n ω => -∫ b, pathUpperEnvelope (fun v => -G v) n (X ω b) ∂(R ω))
    (fun n => hBL _ (hBLU n)) (fun n => tendstoInProbability_neg (hBL _ (hBLL n)))
  · intro n ε ω
    exact integral_mono (hint ε ω G hG (hGW ε ω))
      (hint ε ω _ (hBLU n).1 (hFW _ (hBLU n) ε ω))
      fun x => le_pathUpperEnvelope hG (Nat.cast_nonneg n) _
  · intro n ε ω
    rw [← integral_neg]
    refine integral_mono (hint ε ω (fun w => -pathUpperEnvelope (fun v => -G v) n w)
      (fun w => by simpa only [abs_neg] using (hBLL n).1 w)
      (hFW _ (hBLL n) ε ω).neg) (hint ε ω G hG (hGW ε ω)) fun x => ?_
    have := le_pathUpperEnvelope hG' (Nat.cast_nonneg (α := ℝ) n) (W ε ω x)
    change -pathUpperEnvelope (fun v => -G v) n (W ε ω x) ≤ G (W ε ω x)
    linarith
  · intro δ hδ
    refine tendsto_measure_abs_sub_gt_of_ae_tendsto_nat P _ _ (fun n => hFXω _ (hBLU n)) ?_ hδ
    have hall := ae_all_iff.2 fun n : ℕ => hFX _ (hBLU n)
    filter_upwards [hall, hcont] with ω hm hc
    have := hR ω
    exact tendsto_integral_pathUpperEnvelope (R ω) hG (X ω) hm hc
  · intro δ hδ
    refine tendsto_measure_abs_sub_gt_of_ae_tendsto_nat P _ _
      (fun n => (hFXω _ (hBLL n)).neg) ?_ hδ
    have hall := ae_all_iff.2 fun n : ℕ => hFX _ (hBLL n)
    filter_upwards [hall, hcont] with ω hm hc
    have := hR ω
    have hc' : ∀ᵐ b ∂(R ω), PathFunctionalContinuousAt (fun v => -G v) (X ω b) :=
      hc.mono fun b hb => pathFunctionalContinuousAt_neg hb
    have := (tendsto_integral_pathUpperEnvelope (R ω) hG' (X ω) hm hc').neg
    rw [integral_neg, neg_neg] at this
    exact this

end MatedCRT
