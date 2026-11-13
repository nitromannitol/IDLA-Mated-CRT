import MatedCRT.FirstPass.Derived.CoreExitTimeFromBG20
import LatticeProb.Analysis.LogKernelSplit
import LatticeProb.LQG.LQGMeasureNonatomicMassPoly

/-!
# The log-kernel integral of the γ-quantum cone at a mesoscopic scale

Berestycki-Gwynne, *Random walks on mated-CRT planar maps and Liouville Brownian motion*, proof of
Lemma 6.7, estimate (6.17). Fix `ℓ > 0`, `ζ > 0` and `ρ < 1`. With polynomially high probability as
`δ → 0`, for every `z ∈ B_ρ`,
`sup_{z' ∈ B_{δ^ℓ}(z)} ∫_{B_{2δ^ℓ}(z)} (log(1/|z' - w|) + 1) dμ_h(w) ≤ δ^{-ζ} μ_h(B_{2δ^ℓ}(z))`.

Berestycki and Gwynne derive (6.17) from the exponential tail of their Lemma A.3 and Lemma A.1. Here
only Lemma A.1 is used (the volume growth estimate of the paper, `VolumeGrowthStmt`, a theorem:
`volumeGrowthStmt_holds`):

* the upper bound `μ_h(B_r(w)) ≤ r^{βp}` at the dyadic radii `δ^M 2^{-k}`, for all centres at once by a
  union bound, controls the singularity of the kernel below the scale `s = δ^M`
  (`LatticeProb.LogKernel.iSup_setLIntegral_log_le_mul_of_dyadic`);
* the lower bound `μ_h(B_{2δ^ℓ}(z)) ≥ (2δ^ℓ)^{βm}` absorbs the remaining tail, because `M βp = ℓ βm + 1`.

The failure probability obtained is polynomial in `δ`, not superpolynomial; Lemma 6.7 only needs it to
tend to `0`.
-/

namespace MatedCRT.FirstPass.Derived

open MeasureTheory Filter Topology Set Metric LatticeProb.Gauss
open scoped ENNReal

/-- **Berestycki-Gwynne (6.17)** for the γ-quantum cone, with polynomially high probability: for
`ℓ > 0`, `ζ > 0` and `ρ < 1`, as `δ → 0`, every `z ∈ B_ρ` satisfies
`sup_{z' ∈ B_{δ^ℓ}(z)} ∫_{B_{2δ^ℓ}(z)} (log(1/|z' - w|) + 1) dμ_h(w) ≤ δ^{-ζ} μ_h(B_{2δ^ℓ}(z))`. -/
theorem polyHighProb_iSup_setLIntegral_log_le_cone {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {ℓ ζ ρ : ℝ} (hℓ : 0 < ℓ) (hζ : 0 < ζ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ} (hcone : IsConeField γ P hC hcirc μ) :
    PolyHighProb P fun δ => {ω | ∀ z ∈ ball (0 : ℂ) ρ,
      (⨆ z' ∈ ball z (δ ^ ℓ), ∫⁻ w in ball z (2 * δ ^ ℓ),
          ENNReal.ofReal (Real.log (1 / ‖z' - w‖) + 1) ∂μ ω) ≤
        ENNReal.ofReal (δ ^ (-ζ)) * μ ω (ball z (2 * δ ^ ℓ))} := by
  -- the exponents
  have hγ' : 0 < 2 - γ := by linarith
  obtain ⟨βp, hβp0, hβp1⟩ : ∃ β : ℝ, 0 < β ∧ β < (2 - γ) ^ 2 / 2 :=
    ⟨(2 - γ) ^ 2 / 4, by positivity, by nlinarith [pow_pos hγ' 2]⟩
  obtain ⟨βm, hβm, hβm0⟩ : ∃ β : ℝ, (2 + γ) ^ 2 / 2 < β ∧ 0 ≤ β :=
    ⟨(2 + γ) ^ 2 / 2 + 1, by linarith, by positivity⟩
  have hℓβ : 0 < ℓ * βm + 1 := by nlinarith [mul_nonneg hℓ.le hβm0]
  obtain ⟨M, hM0, hMβ⟩ : ∃ M : ℝ, 0 < M ∧ M * βp = ℓ * βm + 1 :=
    ⟨(ℓ * βm + 1) / βp, div_pos hℓβ hβp0, div_mul_cancel₀ _ hβp0.ne'⟩
  -- Lemma A.1 (volume growth) and the dyadic union bound
  have hVG := volumeGrowthStmt_holds γ hγ0 hγ2 βp βm hβp0 hβp1 hβm Ω P hC hcirc μ hcone
  have hVG' := hVG
  obtain ⟨p, hp, K, r₀, hr₀, hV⟩ := hVG'
  have hdy : PolyHighProb P fun s => {ω | ∀ z ∈ ball (0 : ℂ) (1 - s), ∀ k : ℕ,
      μ ω (ball z (s * (1 / 2) ^ k)) ≤ ENNReal.ofReal ((s * (1 / 2) ^ k) ^ βp)} := by
    refine ⟨p, hp, max K 0 * (1 - (1 / 2) ^ p)⁻¹, r₀, hr₀, fun s hs hsr => ?_⟩
    refine LatticeProb.LogKernel.measure_compl_iInter_le hp hV hs hsr ?_
    intro ω hω z hz k
    rw [mem_iInter] at hω
    have hrad : 1 - s ≤ 1 - s * (1 / 2) ^ k := by
      have := mul_le_of_le_one_right hs.le
        (pow_le_one₀ (by norm_num) (by norm_num) : ((1 : ℝ) / 2) ^ k ≤ 1)
      linarith
    exact (hω k z (ball_subset_ball hrad hz)).2
  have hE1 := LatticeProb.LQG.LQGMeasureNonatomicMass.polyHighProb_comp_rpow
    (LatticeProb.LQG.LQGMeasureNonatomicMass.polyHighProb_comp_mul hVG two_pos) hℓ
  have hE2 := LatticeProb.LQG.LQGMeasureNonatomicMass.polyHighProb_comp_rpow hdy hM0
  -- the deterministic conditions on `δ`
  have hT : ∀ a : ℝ, 0 < a → Tendsto (fun δ : ℝ => δ ^ a) (𝓝[>] 0) (𝓝 0) := fun a ha => by
    have h := (Real.continuous_rpow_const ha.le).tendsto 0
    rw [Real.zero_rpow ha.ne'] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hpos : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ := self_mem_nhdsWithin
  have hlt1 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ < 1 :=
    Filter.mem_of_superset (Ioo_mem_nhdsGT one_pos) fun δ h => h.2
  have hsmall : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 2 * δ ^ ℓ + δ ^ M < 1 - ρ := by
    have h := ((hT ℓ hℓ).const_mul 2).add (hT M hM0)
    rw [mul_zero, add_zero] at h
    exact (tendsto_order.1 h).2 _ (by linarith)
  have hA : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      (-M * (Real.log δ * δ ^ (1 : ℝ)) + (1 + Real.log 2) * δ ^ (1 : ℝ)) *
        (1 - (1 / 2) ^ βp)⁻¹ < 1 := by
    have h := (((tendsto_log_mul_rpow_nhdsGT_zero one_pos).const_mul (-M)).add
      ((hT 1 one_pos).const_mul (1 + Real.log 2))).mul_const ((1 - (1 / 2) ^ βp)⁻¹)
    rw [mul_zero, mul_zero, add_zero, zero_mul] at h
    exact (tendsto_order.1 h).2 1 one_pos
  have hB : ∀ᶠ δ in 𝓝[>] (0 : ℝ), -M * (Real.log δ * δ ^ ζ) + 2 * δ ^ ζ < 1 := by
    have h := ((tendsto_log_mul_rpow_nhdsGT_zero hζ).const_mul (-M)).add
      ((hT ζ hζ).const_mul 2)
    rw [mul_zero, mul_zero, add_zero] at h
    exact (tendsto_order.1 h).2 1 one_pos
  have hdet : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ ∧ δ ^ M ≤ 1 ∧ ρ ≤ 1 - 2 * δ ^ ℓ ∧
      δ ^ ℓ + ρ ≤ 1 - δ ^ M ∧
      (Real.log (1 / δ ^ M) + 1 + Real.log 2) * (δ ^ M) ^ βp * (1 - (1 / 2) ^ βp)⁻¹ ≤
        (2 * δ ^ ℓ) ^ βm ∧
      Real.log (1 / δ ^ M) + 2 ≤ δ ^ (-ζ) := by
    filter_upwards [hpos, hlt1, hsmall, hA, hB] with δ hδ0 hδ1 hsm hA' hB'
    have hℓ0 : 0 ≤ δ ^ ℓ := Real.rpow_nonneg hδ0.le ℓ
    have hM0' : 0 ≤ δ ^ M := Real.rpow_nonneg hδ0.le M
    have hlogM : Real.log (1 / δ ^ M) = -(M * Real.log δ) := by
      rw [one_div, Real.log_inv, Real.log_rpow hδ0]
    refine ⟨hδ0, Real.rpow_le_one hδ0.le hδ1.le hM0.le, by linarith, by linarith, ?_, ?_⟩
    · have e1 : (δ ^ M) ^ βp = δ ^ (ℓ * βm) * δ ^ (1 : ℝ) := by
        rw [← Real.rpow_mul hδ0.le, hMβ, Real.rpow_add hδ0]
      have e2 : (2 * δ ^ ℓ) ^ βm = 2 ^ βm * δ ^ (ℓ * βm) := by
        rw [Real.mul_rpow (by norm_num) hℓ0, ← Real.rpow_mul hδ0.le]
      have hq : 0 ≤ δ ^ (ℓ * βm) := Real.rpow_nonneg hδ0.le _
      have h2 : (1 : ℝ) ≤ 2 ^ βm := Real.one_le_rpow (by norm_num) hβm0
      rw [hlogM, e1, e2]
      calc (-(M * Real.log δ) + 1 + Real.log 2) * (δ ^ (ℓ * βm) * δ ^ (1 : ℝ)) *
            (1 - (1 / 2) ^ βp)⁻¹
          = ((-M * (Real.log δ * δ ^ (1 : ℝ)) + (1 + Real.log 2) * δ ^ (1 : ℝ)) *
              (1 - (1 / 2) ^ βp)⁻¹) * δ ^ (ℓ * βm) := by ring
        _ ≤ 1 * δ ^ (ℓ * βm) := mul_le_mul_of_nonneg_right hA'.le hq
        _ ≤ 2 ^ βm * δ ^ (ℓ * βm) := mul_le_mul_of_nonneg_right h2 hq
    · rw [hlogM, Real.rpow_neg hδ0.le, ← one_div, le_div_iff₀ (Real.rpow_pos_of_pos hδ0 ζ)]
      linarith
  -- on the intersection of the two events, the bound holds
  refine LatticeProb.LQG.LQGMeasureNonatomicMass.polyHighProb_mono_of_eventually
    (LatticeProb.LQG.LQGMeasureNonatomicMass.polyHighProb_inter hE1 hE2) ?_
  filter_upwards [hdet] with δ hδ
  obtain ⟨hδ0, hs1, hρ2, hρs, htail, hlog⟩ := hδ
  rintro ω ⟨h1, h2⟩
  have h1' : ∀ z ∈ ball (0 : ℂ) (1 - 2 * δ ^ ℓ),
      ENNReal.ofReal ((2 * δ ^ ℓ) ^ βm) ≤ μ ω (ball z (2 * δ ^ ℓ)) ∧
        μ ω (ball z (2 * δ ^ ℓ)) ≤ ENNReal.ofReal ((2 * δ ^ ℓ) ^ βp) := h1
  have h2' : ∀ z ∈ ball (0 : ℂ) (1 - δ ^ M), ∀ k : ℕ,
      μ ω (ball z (δ ^ M * (1 / 2) ^ k)) ≤ ENNReal.ofReal ((δ ^ M * (1 / 2) ^ k) ^ βp) := h2
  intro z hz
  refine (LatticeProb.LogKernel.iSup_setLIntegral_log_le_mul_of_dyadic measurableSet_ball
    (Real.rpow_pos_of_pos hδ0 M) hs1 hβp0 ?_ ?_).trans ?_
  · intro z' hz' k
    refine h2' z' ?_ k
    rw [mem_ball] at hz hz' ⊢
    calc dist z' 0 ≤ dist z' z + dist z 0 := dist_triangle _ _ _
      _ < δ ^ ℓ + ρ := add_lt_add hz' hz
      _ ≤ 1 - δ ^ M := hρs
  · exact (ENNReal.ofReal_le_ofReal htail).trans (h1' z (ball_subset_ball hρ2 hz)).1
  · exact mul_le_mul' (ENNReal.ofReal_le_ofReal hlog) le_rfl

end MatedCRT.FirstPass.Derived
