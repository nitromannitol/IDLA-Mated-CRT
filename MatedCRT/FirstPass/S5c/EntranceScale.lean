import MatedCRT.FirstPass.S5c.CodeEntrance
import MatedCRT.FirstPass.S5c.ScaleEntry
import MatedCRT.FirstPass.S5c.EnvInputs
import MatedCRT.FirstPass.S2g.LawCoded
import MatedCRT.Steps.Sec2.ConeScaleInvarianceUpToFixedTime

/-!
# FIRST PASS, Lemma 5.3 (three-inputs A4, `hscale`): the new-entrance probability is scale invariant

Lemma 2.6 (coded law, `ConeScaleInvarianceCodedStmt`) transports the global family code under the rescaling
`Λ^b_s = R_b⁻¹ Λ_{bs}`, with the cone scale radius `R_b = coneScaleRadius γ h b` (positive almost surely by
`ConeScaleRadiusPosStep`, from `QuantumConeScalingInput`, DMS14 Prop. 4.13(i)). The new-entrance event is
`EntranceAt`, which is a countable formula in the global code (`entrance_iff_B`, CodeEntrance.lean), and it is
pointwise invariant: `EntranceAt (Λ^b) t ↔ EntranceAt Λ (b t)`. Hence `P(E(b t)) = P(E t)`.
-/

namespace MatedCRT.S5c

open MeasureTheory Filter Set Metric Topology HarmonicBalls

/-- Rescaling by `R > 0` and `b > 0` keeps a good family good: `t ↦ R⁻¹ Λ_{bt}` (`rescaledFamily`). -/
theorem goodFamily_rescale {F : ℝ → Set ℂ} (hF : GoodFamily F) {R b : ℝ} (hR : 0 < R) (hb : 0 < b) :
    GoodFamily (rescaledFamily F R b) := by
  have hRC : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  set φ : ℂ ≃ₜ ℂ := Homeomorph.mulLeft₀ (R : ℂ) hRC with hφ
  have hφx : ∀ x : ℂ, φ x = (R : ℂ) * x := fun x => rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t ht
    exact (hF.isOpen (b * t) (mul_pos hb ht)).preimage (continuous_const.mul continuous_id)
  · intro s hs t ht hst x hx
    exact hF.monotoneOn (show b * s ∈ Ioi (0 : ℝ) from mul_pos hb hs)
      (show b * t ∈ Ioi (0 : ℝ) from mul_pos hb ht) (mul_le_mul_of_nonneg_left hst hb.le) hx
  · intro t ht
    have hbt : 0 < b * t := mul_pos hb ht
    show interior (closure (φ ⁻¹' F (b * t))) = φ ⁻¹' F (b * t)
    rw [← φ.preimage_closure, ← φ.preimage_interior, hF.isRegularOpen (b * t) hbt]
  · intro t ht x hx ε hε
    have hbt : 0 < b * t := mul_pos hb ht
    have hRx : (R : ℂ) * x ∈ F (b * t) := hx
    have hlt := hF.leftApprox (b * t) hbt ((R : ℂ) * x) hRx (R * ε) (mul_pos hR hε)
    have hT : Tendsto (fun s : ℝ => b * s) (𝓝[<] t) (𝓝[<] (b * t)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · exact ((continuous_const.mul continuous_id).tendsto t).mono_left nhdsWithin_le_nhds
      · exact (eventually_mem_nhdsWithin).mono fun s hs => mul_lt_mul_of_pos_left hs hb
    refine (hT.eventually hlt).mono fun s hs => ?_
    obtain ⟨y, hy, hdy⟩ := hs
    refine ⟨(R : ℂ)⁻¹ * y, ?_, ?_⟩
    · show (R : ℂ) * ((R : ℂ)⁻¹ * y) ∈ F (b * s)
      rw [mul_inv_cancel_left₀ hRC]
      exact hy
    · have hkey : (R : ℂ) * x - y = (R : ℂ) * (x - (R : ℂ)⁻¹ * y) := by
        field_simp
      have hnorm : ‖(R : ℂ) * x - y‖ = R * ‖x - (R : ℂ)⁻¹ * y‖ := by
        rw [hkey, norm_mul, Complex.norm_real, Real.norm_of_nonneg hR.le]
      rw [dist_eq_norm] at hdy
      rw [dist_eq_norm]
      refine lt_of_mul_lt_mul_left ?_ hR.le
      rw [← hnorm]
      exact hdy

/-- Pointwise invariance of the entrance event under the rescaling `R⁻¹ Λ_{b·}` (`R ≠ 0`, `b > 0`):
`E(R⁻¹Λ_{b·}, t) = E(Λ, b t)`, with `y = R x` and `s' = b s`. -/
theorem entranceAt_rescale_iff (F : ℝ → Set ℂ) {R b : ℝ} (hR : 0 < R) (hb : 0 < b) (t : ℝ) :
    EntranceAt (rescaledFamily F R b) t ↔ EntranceAt F (b * t) := by
  have hRC : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  classical
  constructor
  · rintro ⟨x, hx, hnew⟩
    refine ⟨(R : ℂ) * x, hx, fun s' hs' hmem => ?_⟩
    have hs : s' / b ∈ Ioo (0 : ℝ) t :=
      ⟨div_pos hs'.1 hb, by rw [div_lt_iff₀ hb]; linarith [hs'.2]⟩
    have e : b * (s' / b) = s' := by field_simp
    apply hnew (s' / b) hs
    show (R : ℂ) * x ∈ F (b * (s' / b))
    rw [e]
    exact hmem
  · rintro ⟨y, hy, hnew⟩
    refine ⟨(R : ℂ)⁻¹ * y, ?_, fun s hs hmem => ?_⟩
    · show (R : ℂ) * ((R : ℂ)⁻¹ * y) ∈ F (b * t)
      rw [mul_inv_cancel_left₀ hRC]
      exact hy
    · have hmem' : (R : ℂ) * ((R : ℂ)⁻¹ * y) ∈ F (b * s) := hmem
      rw [mul_inv_cancel_left₀ hRC] at hmem'
      exact hnew (b * s) ⟨mul_pos hb hs.1, mul_lt_mul_of_pos_left hs.2 hb⟩ hmem'

/-- A global-code bit is the indicator of `0 < t` and `x ∈ G t` at the rational pair `(ratTime i, ratPoint j)`. -/
theorem globalCode_bit (G : ℝ → Set ℂ) (i j : ℕ) :
    globalCode G (i, j) = true ↔ (0 < ratTime i ∧ ratPoint j ∈ G (ratTime i)) := by
  classical
  constructor
  · intro h; exact @of_decide_eq_true (globalFamilyProcess G (ratTime i, ratPoint j)) (Classical.propDecidable _) h
  · intro h; exact @decide_eq_true (globalFamilyProcess G (ratTime i, ratPoint j)) (Classical.propDecidable _) h

/-- The entrance event of a good family is the countable code formula of its global code. -/
theorem entrance_iff_code {G : ℝ → Set ℂ} (hG : GoodFamily G) {t : ℝ} (ht : 0 < t) :
    EntranceAt G t ↔ EntranceB (fun i j => globalCode G (i, j) = true) t := by
  have hbits : (fun i j => globalCode G (i, j) = true) =
      (fun i j => 0 < ratTime i ∧ ratPoint j ∈ G (ratTime i)) :=
    funext fun i => funext fun j => propext (globalCode_bit G i j)
  rw [hbits]
  exact entrance_iff_B hG ht

/-- **Lemma 5.3 input `hscale` (three-inputs A4): the new-entrance probability is scale invariant.** From the coded
law of Lemma 2.6 (`ConeScaleInvarianceCodedStmt`, a hypothesis) and the positivity of the cone scale radius
(`ConeScaleRadiusPosStep`, a hypothesis from DMS14 Prop. 4.13(i)). -/
theorem newEntrance_scale {Ω : Type} [MeasurableSpace Ω] {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (P : Measure Ω) [IsProbabilityMeasure P] (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (hcone : IsConeField γ P hC hcirc μ)
    (hL : ConeScaleInvarianceCodedStmt) (hpos : ConeScaleRadiusPosStep)
    (Λ : Ω → ℝ → Set ℂ) (hΛ : ∀ᵐ ω ∂P, IsConeHarmonicBallFamily (μ ω) (Λ ω))
    {b t : ℝ} (hb : 0 < b) (ht : 0 < t) :
    P (newEntranceEvent Λ (b * t)) = P (newEntranceEvent Λ t) := by
  have hG : ∀ᵐ ω ∂P, GoodFamily (Λ ω) :=
    hΛ.mono fun ω hω => ⟨fun s hs => (hω.1 s hs).1, hω.2.1.monotoneOn,
      fun s hs => hω.2.1.isRegularOpen s hs, leftApprox_of_hausdorff hω.2.1.hausdorffContinuousOn⟩
  have hR : ∀ᵐ ω ∂P, 0 < coneScaleRadius γ (hcirc ω) b :=
    hpos γ hγ0 hγ2 Ω P hC hcirc hcone.1 hcone.2.1 b hb
  have hGR : ∀ᵐ ω ∂P, GoodFamily (rescaledFamily (Λ ω) (coneScaleRadius γ (hcirc ω) b) b) :=
    (hR.and hG).mono fun ω h => goodFamily_rescale h.2 h.1 hb
  have h1 : P (newEntranceEvent Λ (b * t)) =
      P {ω | EntranceAt (rescaledFamily (Λ ω) (coneScaleRadius γ (hcirc ω) b) b) t} := by
    apply measure_congr
    filter_upwards [hR] with ω hω
    exact propext (entranceAt_rescale_iff (Λ ω) hω hb t).symm
  have h2 : P {ω | EntranceAt (rescaledFamily (Λ ω) (coneScaleRadius γ (hcirc ω) b) b) t} =
      P {ω | EntranceB (fun i j => globalCode (rescaledFamily (Λ ω) (coneScaleRadius γ (hcirc ω) b) b) (i, j) = true) t} := by
    apply measure_congr
    filter_upwards [hGR] with ω hω
    exact propext (entrance_iff_code hω ht)
  have hid := hL γ hγ0 hγ2 Ω P hC hcirc μ hcone Λ hΛ b hb
  have hid2 := hid.comp measurable_snd
  have h3 := hid2.measure_mem_eq (measurableSet_entranceB t)
  have h4 : P {ω | EntranceB (fun i j => globalCode (Λ ω) (i, j) = true) t} = P (newEntranceEvent Λ t) := by
    apply measure_congr
    filter_upwards [hG] with ω hω
    exact propext (entrance_iff_code hω ht).symm
  calc P (newEntranceEvent Λ (b * t))
      = P {ω | EntranceAt (rescaledFamily (Λ ω) (coneScaleRadius γ (hcirc ω) b) b) t} := h1
    _ = P {ω | EntranceB (fun i j => globalCode (rescaledFamily (Λ ω) (coneScaleRadius γ (hcirc ω) b) b) (i, j) = true) t} := h2
    _ = P {ω | EntranceB (fun i j => globalCode (Λ ω) (i, j) = true) t} := h3.symm
    _ = P (newEntranceEvent Λ t) := h4

/-- **Statement (a) of three-inputs section 1 for a valid environment, with `hscale` proved**: almost surely, on
`{t < T}`, every compact `K ⊆ Λ_t` carries a uniform positive lower bound on `w_t - 2 w_{t/2}`. The inputs are the
frozen `FPStrongMinimumPrinciple` and the frozen measurability/Green inputs, and the cited coded law of Lemma 2.6
(`ConeScaleInvarianceCodedStmt`) and the scale-radius positivity (`ConeScaleRadiusPosStep`). -/
theorem fixedIndexMargin_proved {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hF : FrozenLQGMeasureFieldMeasurable 𝒮) (hF1 : FrozenUniversalMeasurabilityOfAnalytic)
    (hF3 : FrozenDiskGreenNonnegCont) (hG : FrozenGreenDiscPole) (hmin : FPStrongMinimumPrinciple)
    (hL : ConeScaleInvarianceCodedStmt) (hpos : ConeScaleRadiusPosStep)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ) (Λ : Ω → ℝ → Set ℂ)
    (hΛ : ∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω))
    {ρ t : ℝ} (hρ : 0 < ρ) (ht : 0 < t) :
    ∀ᵐ ω ∂S.P, t < clusterExitTime (Λ ω) ρ → ∀ K : Set ℂ, IsCompact K → K ⊆ Λ ω t →
      ∃ β : ℝ, 0 < β ∧
        ∀ x ∈ K, β ≤ leastSupersolution (S.μ ω) ρ 0 t x - 2 * leastSupersolution (S.μ ω) ρ 0 (t / 2) x := by
  have := hS.isProbabilityMeasure
  have hcone : IsConeField γ S.P S.hC S.hcirc S.μ :=
    ⟨hS.isProbabilityMeasure, hS.isQuantumCone, hS.isLQGMeasure⟩
  have hscale : ∀ b t : ℝ, 0 < b → 0 < t → S.P (newEntranceEvent Λ (b * t)) = S.P (newEntranceEvent Λ t) :=
    fun b t hb ht => newEntrance_scale hγ0 hγ2 S.P S.hC S.hcirc S.μ hcone hL hpos Λ hΛ hb ht
  exact fixedIndexMargin_compact_env hγ0 hγ2 hF hF1 hF3 hG hmin S hS Λ hΛ hscale hρ ht

end MatedCRT.S5c
