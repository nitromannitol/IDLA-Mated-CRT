import MatedCRT.FirstPass.Derived.ConeEventTransfer
import MatedCRT.FirstPass.Derived.ConeLogIntegralBound
import MatedCRT.FirstPass.Derived.LargestExitTimeFactor

/-!
# The logarithmic-kernel integral bound for the quantum cone, uniform over cone fields

Berestycki and Gwynne (arXiv:2003.10320v2), estimate (6.17): for `ℓ > 0`, `ζ > 0` and `R < 1` there are `p > 0`,
`C` and `r₀ > 0`, depending only on `γ`, `ℓ`, `ζ` and `R`, such that for every γ-quantum cone field and every
`δ ∈ (0, r₀)`, with probability at least `1 - C δ^p`, every `z ∈ B_R(0)` satisfies, with `s = δ^ℓ`,
`sup_{z' ∈ B_s(z)} ∫_{B_{2s}(z)} (log (1/|z' - w|) + 1) dμ_h(w) ≤ δ^{-ζ} μ_h(B_{3s}(z))`.

The right-hand ball has radius `3s` rather than `2s`: this slack is what lets the event contain a Borel event of the
measure `μ_h` alone. With a countable dense set `D ⊆ ℂ`, the Borel event "every `z₀ ∈ D ∩ B_ρ(0)` satisfies
`sup_{z' ∈ B_{5s/4}(z₀) ∩ D} ∫_{B_{9s/4}(z₀)} (log (1/|z' - w|) + 1) dμ_h(w) ≤ δ^{-ζ} μ_h(B_{11s/4}(z₀))`" lies between
the event of (6.17) at the scale `(5/4)^{1/ℓ} δ` and the event above. The supremum over an open ball equals the
supremum over a dense subset by the lower semicontinuity of the kernel and Fatou's lemma. The uniformity then comes
from `exists_uniform_polyBound_of_sandwich`.
-/

open MeasureTheory Set Metric Filter HarmonicBalls LatticeProb
open LatticeProb.LQG.LQGMeasureNonatomicMass
open scoped ENNReal Topology

namespace MatedCRT.FirstPass.Derived

/-- **The supremum over an open set is a supremum over a dense subset.** If `T ⊆ U ⊆ closure T`, then for every
measure `ν` and every set `S`, `sup_{z ∈ U} ∫_S (log (1/|z - w|) + 1) dν(w) = sup_{z ∈ T} ∫_S (log (1/|z - w|) + 1)
dν(w)`: by Fatou's lemma and the lower semicontinuity of the kernel, the integral at `z ∈ U` is at most the limit
inferior of the integrals along a sequence of `T` converging to `z`. -/
theorem iSup_setLIntegral_logKernel_eq_of_dense (ν : Measure ℂ) {U T S : Set ℂ} (hTU : T ⊆ U)
    (hUT : U ⊆ closure T) :
    (⨆ z ∈ U, ∫⁻ w in S, ENNReal.ofReal (Real.log (1 / ‖z - w‖) + 1) ∂ν) =
      ⨆ z ∈ T, ∫⁻ w in S, ENNReal.ofReal (Real.log (1 / ‖z - w‖) + 1) ∂ν := by
  set g : ℂ → ℂ → ℝ≥0∞ := fun z w => ENNReal.ofReal (Real.log (1 / ‖z - w‖) + 1) with hg
  refine le_antisymm (iSup₂_le fun z hz => ?_) (iSup₂_le fun z hz => le_iSup₂_of_le z (hTU hz) le_rfl)
  obtain ⟨u, huT, hu⟩ := mem_closure_iff_seq_limit.1 (hUT hz)
  have hpt : ∀ w, g z w ≤ liminf (fun n => g (u n) w) atTop := by
    intro w
    refine le_of_forall_lt fun y hy => ?_
    obtain ⟨y', hyy', hy'⟩ := exists_between hy
    have hev : ∀ᶠ n in atTop, y' < g (u n) w := hu.eventually (lowerSemicontinuous_logKernel w z y' hy')
    exact hyy'.trans_le (le_liminf_of_le (by isBoundedDefault) (hev.mono fun n hn => hn.le))
  calc ∫⁻ w in S, g z w ∂ν ≤ ∫⁻ w in S, liminf (fun n => g (u n) w) atTop ∂ν := lintegral_mono hpt
    _ ≤ liminf (fun n => ∫⁻ w in S, g (u n) w ∂ν) atTop :=
        lintegral_liminf_le fun n => measurable_exitTimeKernel (u n)
    _ ≤ ⨆ n, ∫⁻ w in S, g (u n) w ∂ν := by
        rw [liminf_eq_iSup_iInf_of_nat]
        exact iSup_mono fun n => iInf₂_le n le_rfl
    _ ≤ ⨆ z ∈ T, ∫⁻ w in S, g z w ∂ν :=
        iSup_le fun n => le_iSup₂_of_le (f := fun z (_ : z ∈ T) => ∫⁻ w in S, g z w ∂ν) (u n) (huT n) le_rfl

/-- The integral of the logarithmic kernel over a ball is a Borel function of the measure. -/
theorem measurable_setLIntegral_logKernel_ball (z' z₀ : ℂ) (r : ℝ) :
    Measurable fun ν : Measure ℂ =>
      ∫⁻ w in ball z₀ r, ENNReal.ofReal (Real.log (1 / ‖z' - w‖) + 1) ∂ν := by
  simp_rw [← lintegral_indicator measurableSet_ball]
  exact Measure.measurable_lintegral ((measurable_exitTimeKernel z').indicator measurableSet_ball)

/-- **BG20 (6.17) with constants uniform over cone fields**, with right-hand ball radius `3δ^ℓ`. For `ℓ > 0`,
`ζ > 0` and `R < 1` there are `p > 0`, `C` and `r₀ > 0` such that for every γ-quantum cone field and `δ ∈ (0, r₀)`,
the event "`sup_{z' ∈ B_{δ^ℓ}(z)} ∫_{B_{2δ^ℓ}(z)} (log (1/|z' - w|) + 1) dμ_h(w) ≤ δ^{-ζ} μ_h(B_{3δ^ℓ}(z))` for
every `z ∈ B_R(0)`" fails with probability at most `C δ^p`. -/
theorem exists_uniform_logIntegral {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {ℓ ζ R : ℝ} (hℓ : 0 < ℓ)
    (hζ : 0 < ζ) (hR : R < 1) :
    ∃ p : ℝ, 0 < p ∧ ∃ C : ℝ, ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
      IsConeField γ P hC hcirc μ → ∀ δ : ℝ, 0 < δ → δ < r₀ →
        P {ω | ∀ z ∈ ball (0 : ℂ) R,
          (⨆ z' ∈ ball z (δ ^ ℓ), ∫⁻ w in ball z (2 * δ ^ ℓ),
              ENNReal.ofReal (Real.log (1 / ‖z' - w‖) + 1) ∂μ ω) ≤
            ENNReal.ofReal (δ ^ (-ζ)) * μ ω (ball z (3 * δ ^ ℓ))}ᶜ ≤ ENNReal.ofReal (C * δ ^ p) := by
  obtain ⟨D, hDc, hD⟩ := TopologicalSpace.exists_countable_dense ℂ
  obtain ⟨c, hc_def⟩ : ∃ c : ℝ, c = (5 / 4 : ℝ) ^ (1 / ℓ) := ⟨_, rfl⟩
  have hc0 : 0 < c := by rw [hc_def]; positivity
  have hc1 : 1 ≤ c := by rw [hc_def]; exact Real.one_le_rpow (by norm_num) (by positivity)
  have hcℓ : ∀ δ : ℝ, 0 < δ → (c * δ) ^ ℓ = 5 / 4 * δ ^ ℓ := by
    intro δ hδ
    rw [Real.mul_rpow hc0.le hδ.le, hc_def, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 5 / 4),
      one_div_mul_cancel hℓ.ne', Real.rpow_one]
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = (1 + R) / 2 := ⟨_, rfl⟩
  have hρ1 : ρ < 1 := by rw [hρ]; linarith
  have hRρ : R < ρ := by rw [hρ]; linarith
  refine exists_uniform_polyBound_of_sandwich (γ := γ)
    (Es := fun δ => {ν : Measure ℂ | ∀ z ∈ ball (0 : ℂ) ρ,
      (⨆ z' ∈ ball z ((c * δ) ^ ℓ), ∫⁻ w in ball z (2 * (c * δ) ^ ℓ),
          ENNReal.ofReal (Real.log (1 / ‖z' - w‖) + 1) ∂ν) ≤
        ENNReal.ofReal ((c * δ) ^ (-ζ)) * ν (ball z (2 * (c * δ) ^ ℓ))})
    (Bm := fun δ => ⋂ z₀ ∈ D ∩ ball (0 : ℂ) ρ, {ν : Measure ℂ |
      (⨆ z' ∈ ball z₀ (5 / 4 * δ ^ ℓ) ∩ D, ∫⁻ w in ball z₀ (9 / 4 * δ ^ ℓ),
          ENNReal.ofReal (Real.log (1 / ‖z' - w‖) + 1) ∂ν) ≤
        ENNReal.ofReal (δ ^ (-ζ)) * ν (ball z₀ (11 / 4 * δ ^ ℓ))})
    (Ew := fun δ => {ν : Measure ℂ | ∀ z ∈ ball (0 : ℂ) R,
      (⨆ z' ∈ ball z (δ ^ ℓ), ∫⁻ w in ball z (2 * δ ^ ℓ),
          ENNReal.ofReal (Real.log (1 / ‖z' - w‖) + 1) ∂ν) ≤
        ENNReal.ofReal (δ ^ (-ζ)) * ν (ball z (3 * δ ^ ℓ))})
    (fun δ => MeasurableSet.biInter (hDc.mono inter_subset_left) fun z₀ _ =>
      measurableSet_le
        (Measurable.biSup _ (hDc.mono inter_subset_right) fun z' _ =>
          measurable_setLIntegral_logKernel_ball z' z₀ _)
        ((Measure.measurable_coe measurableSet_ball).const_mul _))
    (r₁ := 1) one_pos (fun δ hδ _ => ?_) ?_
  · have hs : 0 < δ ^ ℓ := Real.rpow_pos_of_pos hδ ℓ
    refine ⟨fun ν hν => mem_iInter₂.2 fun z₀ hz₀ => ?_, fun ν hν => ?_⟩
    · have h := hν z₀ hz₀.2
      rw [hcℓ δ hδ] at h
      have hpow : (c * δ) ^ (-ζ) ≤ δ ^ (-ζ) :=
        Real.rpow_le_rpow_of_nonpos hδ (le_mul_of_one_le_left hδ.le hc1) (by linarith)
      calc (⨆ z' ∈ ball z₀ (5 / 4 * δ ^ ℓ) ∩ D, ∫⁻ w in ball z₀ (9 / 4 * δ ^ ℓ),
              ENNReal.ofReal (Real.log (1 / ‖z' - w‖) + 1) ∂ν)
          ≤ ⨆ z' ∈ ball z₀ (5 / 4 * δ ^ ℓ), ∫⁻ w in ball z₀ (2 * (5 / 4 * δ ^ ℓ)),
              ENNReal.ofReal (Real.log (1 / ‖z' - w‖) + 1) ∂ν :=
            iSup₂_le fun z' hz' => le_iSup₂_of_le (f := fun z' (_ : z' ∈ ball z₀ (5 / 4 * δ ^ ℓ)) =>
              ∫⁻ w in ball z₀ (2 * (5 / 4 * δ ^ ℓ)), ENNReal.ofReal (Real.log (1 / ‖z' - w‖) + 1) ∂ν) z' hz'.1
              (lintegral_mono_set (ball_subset_ball (by linarith)))
        _ ≤ ENNReal.ofReal ((c * δ) ^ (-ζ)) * ν (ball z₀ (2 * (5 / 4 * δ ^ ℓ))) := h
        _ ≤ ENNReal.ofReal (δ ^ (-ζ)) * ν (ball z₀ (11 / 4 * δ ^ ℓ)) :=
            mul_le_mul' (ENNReal.ofReal_le_ofReal hpow) (measure_mono (ball_subset_ball (by linarith)))
    · intro z hz
      obtain ⟨z₀, hz₀D, hzz₀⟩ :=
        hD.exists_dist_lt z (lt_min (by positivity : 0 < δ ^ ℓ / 4) (by linarith : 0 < ρ - R))
      have hd1 : dist z z₀ < δ ^ ℓ / 4 := hzz₀.trans_le (min_le_left _ _)
      have hd2 : dist z z₀ < ρ - R := hzz₀.trans_le (min_le_right _ _)
      have hz₀ : z₀ ∈ D ∩ ball (0 : ℂ) ρ := by
        refine ⟨hz₀D, ?_⟩
        have htri := dist_triangle z₀ z 0
        rw [mem_ball] at hz ⊢
        rw [dist_comm z₀ z] at htri
        linarith
      have h := mem_iInter₂.1 hν z₀ hz₀
      have hdense := iSup_setLIntegral_logKernel_eq_of_dense ν (U := ball z₀ (5 / 4 * δ ^ ℓ))
        (T := ball z₀ (5 / 4 * δ ^ ℓ) ∩ D) (S := ball z₀ (9 / 4 * δ ^ ℓ)) inter_subset_left
        (hD.open_subset_closure_inter isOpen_ball)
      calc (⨆ z' ∈ ball z (δ ^ ℓ), ∫⁻ w in ball z (2 * δ ^ ℓ),
              ENNReal.ofReal (Real.log (1 / ‖z' - w‖) + 1) ∂ν)
          ≤ ⨆ z' ∈ ball z₀ (5 / 4 * δ ^ ℓ), ∫⁻ w in ball z₀ (9 / 4 * δ ^ ℓ),
              ENNReal.ofReal (Real.log (1 / ‖z' - w‖) + 1) ∂ν :=
            iSup₂_le fun z' hz' => le_iSup₂_of_le (f := fun z' (_ : z' ∈ ball z₀ (5 / 4 * δ ^ ℓ)) =>
              ∫⁻ w in ball z₀ (9 / 4 * δ ^ ℓ), ENNReal.ofReal (Real.log (1 / ‖z' - w‖) + 1) ∂ν) z'
              (ball_subset_ball' (by linarith) hz')
              (lintegral_mono_set (ball_subset_ball' (by linarith)))
        _ = ⨆ z' ∈ ball z₀ (5 / 4 * δ ^ ℓ) ∩ D, ∫⁻ w in ball z₀ (9 / 4 * δ ^ ℓ),
              ENNReal.ofReal (Real.log (1 / ‖z' - w‖) + 1) ∂ν := hdense
        _ ≤ ENNReal.ofReal (δ ^ (-ζ)) * ν (ball z₀ (11 / 4 * δ ^ ℓ)) := h
        _ ≤ ENNReal.ofReal (δ ^ (-ζ)) * ν (ball z (3 * δ ^ ℓ)) :=
            mul_le_mul' le_rfl (measure_mono (ball_subset_ball' (by rw [dist_comm]; linarith)))
  · intro Ω _ P hC hcirc μ hcone
    exact polyHighProb_comp_mul
      (polyHighProb_iSup_setLIntegral_log_le_cone hγ hγ2 hℓ hζ hρ1 hcone) hc0

end MatedCRT.FirstPass.Derived
