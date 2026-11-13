import MatedCRT.FirstPass.Derived.MepsUpperAssembly
import MatedCRT.FirstPass.Derived.ConeAreaMeasureCode

/-!
# The largest exit-time variable as a Borel function of the field

`𝓜(D) = sup_{z ∈ D} ∫_D (log (1/|z - w|) + 1) dμ_h(w)` (eq:largest-exit-time-rv, line 884) is a Borel function of
the measure `μ_h`: the kernel `z ↦ log (1/|z - w|) + 1` is lower semicontinuous, so by Fatou's lemma
`z ↦ ∫_D (log (1/|z - w|) + 1) dμ(w)` is lower semicontinuous and, for an open ball `D`, the supremum over `D` is a
supremum over a countable dense subset of `D`. Composed with the Borel decoder of the `γ`-LQG measure from the test
pairings of the field (`exists_measurable_fieldCode_lqgMeasure_of_isQuantumCone`), this writes `𝓜(B_ρ)` almost
surely as one Borel function of the whole-plane observable process, for every `γ`-quantum cone. With the uniform tail
bound of `largestExitTimeRV_ball_tail_uniform` this gives the upper half of eq:meps-scaling (BG20 (1.8)) from
Lemmas 2.17 and 2.18 alone.

## Main results

* `lowerSemicontinuous_logKernel`, `largestExitTimeRV_eq_iSup_of_dense`: the reduction to a countable supremum.
* `measurable_largestExitTimeRV_ball`: `ν ↦ 𝓜_ν(B_ρ)` is measurable on `Measure ℂ`.
* `exists_measurable_largestExitTimeRV_ball_factor`: `𝓜(B_ρ) = Ψ(observable process)` a.s. for every cone field,
  with `Ψ` Borel and depending only on `γ` and `ρ`.
* `mεCdf_upper`: `∃ c₂ > 0, ∀ valid S, ∃ ε₀ > 0, ∀ ε ∈ (0, ε₀), 1/2 ≤ F_ε(c₂ ε⁻¹)`, from Lemmas 2.17 and 2.18.
-/

open MeasureTheory Set Metric Filter HarmonicBalls
open scoped ENNReal Topology

namespace MatedCRT

/-- **The logarithmic kernel is lower semicontinuous** in the pole: `z ↦ log (1/|z - w|) + 1` (in `[0, ∞]`) is lower
semicontinuous; at `z = w` it takes the value `1` (`log (1/0) = 0` in Lean), below its values near `w`. -/
theorem lowerSemicontinuous_logKernel (w : ℂ) :
    LowerSemicontinuous fun z : ℂ => ENNReal.ofReal (Real.log (1 / ‖z - w‖) + 1) := by
  intro z
  by_cases hzw : z = w
  · subst hzw
    intro y hy
    have hy1 : y < 1 := by simpa using hy
    filter_upwards [ball_mem_nhds z one_pos] with z' hz'
    refine hy1.trans_le ?_
    have hlog : 0 ≤ Real.log (1 / ‖z' - z‖) := by
      rcases eq_or_lt_of_le (norm_nonneg (z' - z)) with h0 | hpos
      · rw [← h0]
        simp
      · refine Real.log_nonneg ?_
        rw [le_div_iff₀ hpos, one_mul]
        exact (mem_ball_iff_norm.1 hz').le
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  · have hne : ‖z - w‖ ≠ 0 := norm_ne_zero_iff.2 (sub_ne_zero.2 hzw)
    have hc : ContinuousAt (fun z' : ℂ => Real.log (1 / ‖z' - w‖) + 1) z := by
      refine ContinuousAt.add ?_ continuousAt_const
      refine ContinuousAt.log ?_ (one_div_ne_zero hne)
      exact continuousAt_const.div (continuous_norm.continuousAt.comp
        (continuousAt_id.sub continuousAt_const)) hne
    exact (ENNReal.continuous_ofReal.continuousAt.comp hc).lowerSemicontinuousAt

/-- The logarithmic kernel is measurable in the integration variable. -/
theorem measurable_exitTimeKernel (z : ℂ) :
    Measurable fun w : ℂ => ENNReal.ofReal (Real.log (1 / ‖z - w‖) + 1) :=
  (((measurable_const.sub measurable_id).norm.const_div 1).log.add_const 1).ennreal_ofReal

/-- **The supremum over `D` is a supremum over a dense subset.** If `T ⊆ D ⊆ closure T`, then
`𝓜_ν(D) = sup_{z ∈ T} ∫_D (log (1/|z - w|) + 1) dν(w)`, for every measure `ν`: by Fatou's lemma and the lower
semicontinuity of the kernel, the integral at `z ∈ D` is at most the limit inferior of the integrals along a sequence
of `T` converging to `z`. -/
theorem largestExitTimeRV_eq_iSup_of_dense (ν : Measure ℂ) {D T : Set ℂ} (hTD : T ⊆ D)
    (hDT : D ⊆ closure T) :
    largestExitTimeRV ν D =
      ⨆ z ∈ T, ∫⁻ w in D, ENNReal.ofReal (Real.log (1 / ‖z - w‖) + 1) ∂ν := by
  set g : ℂ → ℂ → ℝ≥0∞ := fun z w => ENNReal.ofReal (Real.log (1 / ‖z - w‖) + 1) with hg
  refine le_antisymm (iSup₂_le fun z hz => ?_) (iSup₂_le fun z hz => le_iSup₂_of_le z (hTD hz) le_rfl)
  obtain ⟨u, huT, hu⟩ := mem_closure_iff_seq_limit.1 (hDT hz)
  have hpt : ∀ w, g z w ≤ liminf (fun n => g (u n) w) atTop := by
    intro w
    refine le_of_forall_lt fun y hy => ?_
    obtain ⟨y', hyy', hy'⟩ := exists_between hy
    have hev : ∀ᶠ n in atTop, y' < g (u n) w := hu.eventually (lowerSemicontinuous_logKernel w z y' hy')
    exact hyy'.trans_le (le_liminf_of_le (by isBoundedDefault) (hev.mono fun n hn => hn.le))
  calc ∫⁻ w in D, g z w ∂ν ≤ ∫⁻ w in D, liminf (fun n => g (u n) w) atTop ∂ν := lintegral_mono hpt
    _ ≤ liminf (fun n => ∫⁻ w in D, g (u n) w ∂ν) atTop :=
        lintegral_liminf_le fun n => measurable_exitTimeKernel (u n)
    _ ≤ ⨆ n, ∫⁻ w in D, g (u n) w ∂ν := by
        rw [liminf_eq_iSup_iInf_of_nat]
        exact iSup_mono fun n => iInf₂_le n le_rfl
    _ ≤ ⨆ z ∈ T, ∫⁻ w in D, g z w ∂ν :=
        iSup_le fun n => le_iSup₂_of_le (f := fun z (_ : z ∈ T) => ∫⁻ w in D, g z w ∂ν) (u n) (huT n) le_rfl

/-- **`𝓜(B_ρ)` is a Borel function of the measure**: `ν ↦ 𝓜_ν(B_ρ)` is measurable for the Giry σ-algebra on
`Measure ℂ`. -/
theorem measurable_largestExitTimeRV_ball (ρ : ℝ) :
    Measurable fun ν : Measure ℂ => largestExitTimeRV ν (ball 0 ρ) := by
  obtain ⟨s, hs, hsd⟩ := TopologicalSpace.exists_countable_dense ℂ
  have hT : ball (0 : ℂ) ρ ∩ s ⊆ ball 0 ρ := inter_subset_left
  have hcl : ball (0 : ℂ) ρ ⊆ closure (ball 0 ρ ∩ s) := hsd.open_subset_closure_inter isOpen_ball
  simp_rw [largestExitTimeRV_eq_iSup_of_dense _ hT hcl]
  refine Measurable.biSup _ (hs.mono inter_subset_right) fun z _ => ?_
  simp_rw [← lintegral_indicator measurableSet_ball]
  exact Measure.measurable_lintegral ((measurable_exitTimeKernel z).indicator measurableSet_ball)

/-- **The largest exit-time variable of a ball factors through the observable process** (U2 of the upper bound on
`m_ε`): there is a Borel `Ψ`, depending only on `γ` and `ρ`, such that for every cone field
`𝓜(B_ρ) = Ψ((h, φ)_φ, (h_r(z))_{r,z})` almost surely. `Ψ` reads the test pairings, decodes the `γ`-LQG measure
(`exists_measurable_fieldCode_lqgMeasure_of_isQuantumCone`) and applies `measurable_largestExitTimeRV_ball`. -/
theorem exists_measurable_largestExitTimeRV_ball_factor (γ ρ : ℝ) :
    ∃ Ψ : (GFFObservable.Admissible → ℝ) → ℝ≥0∞, Measurable Ψ ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
        (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), IsConeField γ P hC hcirc μ →
        ∀ᵐ ω ∂P, largestExitTimeRV (μ ω) (ball 0 ρ) = Ψ (wholePlaneObservableProc hC hcirc ω) := by
  obtain ⟨M, hM, hrec⟩ := exists_measurable_fieldCode_lqgMeasure_of_isQuantumCone γ
  let R : (GFFObservable.Admissible → ℝ) → FieldPairingCode := fun x φ =>
    x ⟨GFFObservable.pairing φ.1, φ.2⟩
  have hR : Measurable R := measurable_pi_iff.2 fun φ => measurable_pi_apply _
  refine ⟨fun x => largestExitTimeRV (M (R x)) (ball 0 ρ),
    (measurable_largestExitTimeRV_ball ρ).comp (hM.comp hR), fun Ω _ P hC hcirc μ hc => ?_⟩
  let S : MatedCRTEnv Ω := ⟨P, hC, hcirc, μ, fun _ _ => 0, fun _ _ _ => 0, fun _ => 0⟩
  filter_upwards [hrec (S := S) (μ := μ) hc.2.1 hc.2.2] with ω hω
  have hRω : R (wholePlaneObservableProc hC hcirc ω) = fieldPairingCode S ω := rfl
  simp only [hRω, hω]

/-- **Upper half of eq:meps-scaling** (BG20 (1.8)): from Lemma 2.18 and Lemma 2.17 there is `c₂ = c₂(γ) > 0` with
`F_ε(c₂ ε⁻¹) ≥ 1/2` for all small `ε`, for every valid environment. -/
theorem mεCdf_upper {𝒮 : SpaceFillingSLEModel} (h218 : ExitTimeUpperBoundStmt 𝒮)
    (h217 : BoundedExitTimeRVStmt) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∃ c₂ : ℝ, 0 < c₂ ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → 1 / 2 ≤ S.mεCdf ε (c₂ * ε⁻¹) := by
  obtain ⟨Ψ, hΨ, hfac⟩ := exists_measurable_largestExitTimeRV_ball_factor γ (3 / 4)
  exact mεCdf_upper_of_factor h218 h217 hγ hγ2 hΨ hfac

end MatedCRT
