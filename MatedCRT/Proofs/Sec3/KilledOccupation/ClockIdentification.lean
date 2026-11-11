import Mathlib
import MarkovProcess.Path.Basic
import MatedCRT.Proofs.Sec3.KilledOccupation.WeightedClock

/-!
# Identification of the clock `φ = Φ` (Appendix B, step S6)

Source: `paper/appendix-occupation-C16.tex`, proof of Theorem thm:occ-main, "Identification of the
clock of the main text" (lines 370-425). The argument splits the regularized clock and the weighted
clock along the cutoff `χ_a` (`0` on `B_a`, `1` off `B_{2a}`):
* `φ_ε = (χ_a-part) + R_{ε,a}` and `Φ = (χ_a-part) + Q_a`, with `R_{ε,a}` and `Q_a` the removed parts;
* the `χ_a`-parts converge uniformly in `s` in probability (tex:377-385, from lem:occ-base);
* `R_{ε,a}` is small uniformly in small `ε` as `a → 0` (tex:386-400, from lem:occ-tails and the
  occupation identity of the removed part);
* `Q_a → 0` as `a → 0` (tex:402-405; proved below, `removedWeightedClock_tendsto_zero`).

The combination `sup_s |φ_ε - Φ| → 0` in probability is `clock_identification_of_split`. Its inputs
`hE`, `hR`, `hsplit` are explicit hypotheses (see the docstring of that theorem).
-/

namespace MatedCRT.KilledOccupation

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

/-- The removed part of the weighted clock off the disk `B_{2a}`: the integral over
`[0, s ∧ σ]` of `1{|B_u| < 2a} w(B_u)` against `dA` (tex:402-405, the removed part `Q_a`). -/
noncomputable def removedWeightedClock (γ : ℝ) (dA : Measure ℝ≥0) (σ : ℝ≥0) (a : ℝ) (B : ℝ≥0 → ℂ)
    (s : ℝ≥0) : ℝ≥0∞ :=
  ∫⁻ u in Icc 0 (min s σ), (if ‖B u‖ < 2 * a then gammaWeight γ (B u) else 0) ∂dA

/-- Pathwise limit of the removed weight: for a continuous path with finite weighted clock at the exit
time and `γ ≠ 0`, `Q_a(σ) → 0` as `a ↓ 0` (dominated convergence; at a zero of the path the weight is
the junk value `0`, and for `B_u ≠ 0` the indicator vanishes once `2a < |B_u|`). -/
theorem removedWeightedClock_tendsto_zero {γ : ℝ} (hγ : γ ≠ 0) (dA : Measure ℝ≥0) (σ : ℝ≥0)
    (B : ℝ≥0 → ℂ) (hB : Continuous B)
    (hfin : weightedClock dA (fun u => gammaWeight γ (B u)) σ σ ≠ ⊤) :
    Tendsto (fun a : ℝ => removedWeightedClock γ dA σ a B σ) (𝓝[>] 0) (𝓝 0) := by
  have hmeas : ∀ a : ℝ, Measurable fun u => (if ‖B u‖ < 2 * a then gammaWeight γ (B u) else 0) :=
    fun a => Measurable.ite (measurableSet_lt (hB.measurable.norm) measurable_const)
      ((measurable_gammaWeight γ).comp hB.measurable) measurable_const
  have hbd : ∫⁻ u in Icc 0 (min σ σ), gammaWeight γ (B u) ∂dA ≠ ⊤ := by
    simpa only [weightedClock, min_self] using hfin
  -- for each time `u`, the integrand vanishes for all small `a > 0`
  have hzero : ∀ u, ∀ᶠ a in 𝓝[>] (0 : ℝ),
      (if ‖B u‖ < 2 * a then gammaWeight γ (B u) else 0) = 0 := by
    intro u
    by_cases hu : B u = 0
    · refine Eventually.of_forall fun a => ?_
      split_ifs with h
      · rw [hu, gammaWeight, norm_zero, Real.zero_rpow (neg_ne_zero.2 (pow_ne_zero 2 hγ)),
          ENNReal.ofReal_zero]
      · rfl
    · have hpos : 0 < ‖B u‖ := norm_pos_iff.2 hu
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < ‖B u‖ / 2 by positivity)] with a ha
      simp [show ¬ (‖B u‖ < 2 * a) from not_lt.2 (by linarith [ha.2])]
  unfold removedWeightedClock
  have hbound : ∀ᶠ a in 𝓝[>] (0 : ℝ), ∀ᵐ u ∂(dA.restrict (Icc 0 (min σ σ))),
      (if ‖B u‖ < 2 * a then gammaWeight γ (B u) else 0) ≤ gammaWeight γ (B u) :=
    Eventually.of_forall fun a => ae_of_all _ fun u => by split_ifs <;> simp
  have hlimit : ∀ᵐ u ∂(dA.restrict (Icc 0 (min σ σ))),
      Tendsto (fun a : ℝ => if ‖B u‖ < 2 * a then gammaWeight γ (B u) else 0) (𝓝[>] 0) (𝓝 0) :=
    ae_of_all _ fun u => tendsto_const_nhds.congr' ((hzero u).mono fun a h => h.symm)
  have hlim := tendsto_lintegral_filter_of_dominated_convergence (l := 𝓝[>] (0 : ℝ))
    (fun u => gammaWeight γ (B u)) (Eventually.of_forall fun a => hmeas a) hbound hbd hlimit
  simpa using hlim

/-- **Identification of the clock, combination step** (paper tex:370-425, final display). Let `D ε x`
be the distance `sup_s |φ_ε(s) - Φ(s)|` on the product probability space `μ` of field and Brownian
motion, and let `E ε a`, `R ε a`, `Q a` be the sup-distances of the `χ_a`-parts and of the removed
parts. Hypotheses:
* `hE` (tex:377-385): for fixed `a > 0`, the `χ_a`-parts converge in probability as `ε → 0`;
* `hR` (tex:386-400): the removed `φ`-parts are small in probability, uniformly in small `ε`, as
  `a → 0`;
* `hQ` (tex:402-405): `Q_a → 0` in probability as `a → 0` (a.s. pathwise limit,
  `removedWeightedClock_tendsto_zero`, on a probability space);
* `hsplit`: the triangle inequality for the three parts, a.s., for `ε < a`.
Conclusion: `sup_s |φ_ε - Φ| → 0` in probability as `ε → 0` (`l` is the filter of `ε ↓ 0`). -/
theorem clock_identification_of_split {ι X : Type*} {l : Filter ι} [l.NeBot] [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (D : ι → X → ℝ≥0∞) (E R : ι → ℝ → X → ℝ≥0∞) (Q : ℝ → X → ℝ≥0∞)
    (hE : ∀ a : ℝ, 0 < a → ∀ η : ℝ, 0 < η →
      Tendsto (fun ε => μ {x | ENNReal.ofReal η < E ε a x}) l (𝓝 0))
    (hR : ∀ η : ℝ, 0 < η → ∀ δ : ℝ≥0∞, 0 < δ → ∀ᶠ a in 𝓝[>] (0 : ℝ), ∀ᶠ ε in l,
      μ {x | ENNReal.ofReal η < R ε a x} ≤ δ)
    (hQ : ∀ η : ℝ, 0 < η → Tendsto (fun a => μ {x | ENNReal.ofReal η < Q a x}) (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hsplit : ∀ᶠ a in 𝓝[>] (0 : ℝ), ∀ᶠ ε in l, ∀ᵐ x ∂μ, D ε x ≤ E ε a x + R ε a x + Q a x) :
    ∀ η : ℝ, 0 < η → Tendsto (fun ε => μ {x | ENNReal.ofReal η < D ε x}) l (𝓝 0) := by
  intro η hη
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  have h3 : (0 : ℝ) ≤ η / 3 := (div_pos hη (by norm_num)).le
  have hc : ENNReal.ofReal (η / 3) + ENNReal.ofReal (η / 3) + ENNReal.ofReal (η / 3) =
      ENNReal.ofReal η := by
    rw [← ENNReal.ofReal_add h3 h3, ← ENNReal.ofReal_add (add_nonneg h3 h3) h3]
    congr 1
    ring
  have hthird : 0 < δ / 3 := ENNReal.div_pos_iff.2 ⟨hδ.ne', ENNReal.ofNat_ne_top⟩
  have hQ' := (hQ (η / 3) (div_pos hη (by norm_num))).eventually (gt_mem_nhds hthird)
  have hR' := hR (η / 3) (div_pos hη (by norm_num)) (δ / 3) hthird
  obtain ⟨a, hQa, hRa, hapos, hsa⟩ :=
    (hQ'.and (hR'.and ((eventually_mem_nhdsWithin : ∀ᶠ a in 𝓝[>] (0 : ℝ), a ∈ Ioi (0 : ℝ)).and
      hsplit))).exists
  have hEe := ((hE a hapos (η / 3) (div_pos hη (by norm_num))).eventually (gt_mem_nhds hthird))
  filter_upwards [hEe, hRa, hsa] with ε hEε hRε hsε
  have hsub : ∀ᵐ x ∂μ, ENNReal.ofReal η < D ε x →
      x ∈ {x | ENNReal.ofReal (η / 3) < E ε a x} ∪ {x | ENNReal.ofReal (η / 3) < R ε a x} ∪
        {x | ENNReal.ofReal (η / 3) < Q a x} := by
    filter_upwards [hsε] with x hx hxD
    by_contra hcon
    simp only [mem_union, Set.mem_ofPred_eq, not_or, not_lt] at hcon
    obtain ⟨⟨h1, h2⟩, h4⟩ := hcon
    have : D ε x ≤ ENNReal.ofReal η := by
      rw [← hc]
      exact hx.trans (add_le_add (add_le_add h1 h2) h4)
    exact absurd hxD (not_lt.2 this)
  calc μ {x | ENNReal.ofReal η < D ε x}
      ≤ μ ({x | ENNReal.ofReal (η / 3) < E ε a x} ∪ {x | ENNReal.ofReal (η / 3) < R ε a x} ∪
        {x | ENNReal.ofReal (η / 3) < Q a x}) := measure_mono_ae hsub
    _ ≤ μ {x | ENNReal.ofReal (η / 3) < E ε a x} + μ {x | ENNReal.ofReal (η / 3) < R ε a x} +
        μ {x | ENNReal.ofReal (η / 3) < Q a x} :=
          (measure_union_le _ _).trans (by gcongr; exact measure_union_le _ _)
    _ ≤ δ / 3 + δ / 3 + δ / 3 := add_le_add (add_le_add hEε.le hRε) hQa.le
    _ = δ := ENNReal.add_thirds δ

end MatedCRT.KilledOccupation
