import MatedCRT.FirstPass.Derived.EqLawPerOmega
import MatedCRT.FirstPass.Derived.ExitTimeLowerStopped
import MatedCRT.FirstPass.Derived.MepsUpperBound
import MatedCRT.FirstPass.Derived.ConeRadiusTails
import MatedCRT.FirstPass.Derived.ExitCouplingBoundaryUnion
import MatedCRT.Steps.Sec1.Convergence

/-!
# Equicontinuity in law of the quenched walks from the cone scaling (Berestycki–Gwynne (2020), §6.4)

`hEqLaw_of_scaling`: for a valid environment `S`, with embedded curves `η'` and mesh sizes `ε_n → 0`, for all `R, a > 0`
there is `δ > 0` with `P[ω^{ε_n}_R(δ) > a] ≤ a` for all large `n` (the input `hEqLaw` of
`tendstoInMeasure_reversibilityPairing_degreeCutoffMeasure`).

Proof (BG20 §6.4, "stopped → unstopped for arbitrary `R`").  Fix the scaling parameter `b = n₀ + 1` first, large
enough that `P[R_b ≤ 4 (R + 2)] ≤ θ` (the cone scale radii tend to infinity in probability) and that
`m_ε / b` is at most `1` and the exit time of the rescaled walk at mesh `ε / b` is long (`m_ε ≤ c₂ ε⁻¹`); then `M`
with `P[M < R_b] ≤ θ`, the rescaled environment `S'` with the same law, the exit-time lower bound of Lemma 6.11 for
`S'` and the vertex form of Proposition 6.12 for `S'`.  On the complement of the four bad events, the deterministic
bound `walkLawModulus_le_of_rescaled` gives `ω^ε_R(δ) ≤ 2 κ + M r ≤ a`.
-/

namespace MatedCRT.FirstPass.Derived

open MeasureTheory Set Metric Filter LatticeProb
open scoped ENNReal NNReal Topology
open MatedCRT.SuccessiveExitGaps

attribute [local instance] LatticeProb.dUnifMetricSpace

/-- **Equicontinuity in law of the quenched walks** (BG20 §6.4; the input `hEqLaw` of the reversibility pairing),
from the cone scaling step, the exit-time bounds of Section 2, Lemma 6.9 (`h632`), Lemma 6.10 (`h636`) and
Lemma 6.13 (`hbd`). -/
theorem hEqLaw_of_scaling {𝒮 : SpaceFillingSLEModel}
    (h32 : FrozenDiscreteHolderContinuityCorrected 𝒮)
    (h213 : GreenKernelLowerBoundStmt 𝒮) (h214 : ExitTimeUpperBoundStmt 𝒮)
    (h217 : BoundedExitTimeRVStmt) (h219 : ExpectedExitTimeExplicitBoundStmt 𝒮)
    (hEnvS : ConeEnvironmentScalingStep 𝒮)
    (h632 : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ ℓ : ℝ, 1 < ℓ →
      ∀ ζ : ℝ, 0 < ζ → ζ < 1 → ∃ ψ₀ : ℝ → ℝ,
      ((∀ δ : ℝ, 0 ≤ δ → 0 ≤ ψ₀ δ) ∧ ψ₀ 0 = 0 ∧
        ∀ p : ℝ, 0 < p → Tendsto (fun δ => δ ^ (-p) * ψ₀ δ) (𝓝[>] 0) (𝓝 0)) ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ θ : ℝ, 0 < θ → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        S.P {ω | ∀ x ∈ cellVertices ε (S.η ω) (ball 0 (ρ - δ)),
          srwLaw (S.mult ε ω) x {y |
            vExitTime (cellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) x) δ)) y <
              SuccessiveExitGaps.succExit
                (fun z => cellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) z) (δ ^ ℓ)))
                ⌊δ ^ (-((2 - ζ) * (ℓ - 1)))⌋₊ y} ≤ ENNReal.ofReal (ψ₀ δ)}ᶜ ≤ ENNReal.ofReal θ)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (h636 : ∃ ψ₀ : ℝ → ℝ, ((∀ δ : ℝ, 0 ≤ δ → 0 ≤ ψ₀ δ) ∧
        ∀ p : ℝ, 0 < p → Tendsto (fun δ => δ ^ (-p) * ψ₀ δ) (𝓝[>] 0) (𝓝 0)) ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
        LimLimSmall S.P (fun s ε => {ω | ¬ ∀ x ∈ cellVertices ε (S.η ω) (ball (0 : ℂ) (1 / 2)),
          srwLaw (S.mult ε ω) x
            {X | ¬ vExitTime (interiorCellVertices ε (S.η ω) (ball (0 : ℂ) (1 / 2))) X ≤
              succExit (fun w => interiorCellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) w) (2 * s)))
                ⌊(2 * s) ^ (-3 : ℝ)⌋₊ X} ≤ ENNReal.ofReal (ψ₀ (2 * s))}))
    (hbd : ∃ ξ A : ℝ, 0 < ξ ∧ 0 < A ∧ ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ (Ω : Type) [MeasurableSpace Ω]
      (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      _root_.HarmonicBalls.PolyHighProb S.P fun ε => {ω | ∀ x ∈ cellVertices ε (S.η ω)
          (ball (0 : ℂ) (1 / 2) \ ball (0 : ℂ) (1 / 2 - δ)),
        ENNReal.ofReal (1 - A * δ ^ ξ) ≤
          srwLaw (S.mult ε ω) x {X | vExitTime (cellVertices ε (S.η ω) (ball (0 : ℂ) (1 / 2))) X <
            vHitTime (cellVertices ε (S.η ω)
              (frontier (ball (vertexPoint ε (S.η ω) x) (Real.sqrt δ)))) X ∧
            ∀ n : ℕ, (n : ℕ∞) ≤ vExitTime (cellVertices ε (S.η ω) (ball (0 : ℂ) (1 / 2))) X →
              cell ε (S.η ω) (X n) ⊆ ball (vertexPoint ε (S.η ω) x) (Real.sqrt δ)}})
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    {η' : Ω → C(ℝ, ℂ)} (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω)
    {eps : ℕ → ℝ} (hε0 : ∀ n, 0 < eps n) (hε : Tendsto eps atTop (𝓝 0)) :
    ∀ R a : ℝ, 0 < a → ∃ δ > 0, ∀ᶠ n in atTop,
      S.P {ω | ENNReal.ofReal a < walkLawModulus S η' (eps n) R δ ω} ≤ ENNReal.ofReal a := by
  intro R a ha
  have : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  obtain ⟨a', ha'⟩ : ∃ a' : ℝ, a' = min a (1 / 2) := ⟨_, rfl⟩
  have ha'0 : 0 < a' := by rw [ha']; exact lt_min ha (by norm_num)
  have ha'a : a' ≤ a := by rw [ha']; exact min_le_left _ _
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = a' / 3 := ⟨_, rfl⟩
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = a' / 5 := ⟨_, rfl⟩
  have hκ0 : 0 < κ := by rw [hκ]; positivity
  have hθ0 : 0 < θ := by rw [hθ]; positivity
  obtain ⟨T0, hT0def⟩ : ∃ T0 : ℝ, T0 = |Real.log κ| + 1 := ⟨_, rfl⟩
  have hT0 : 0 ≤ T0 := by rw [hT0def]; positivity
  have hκT : Real.exp (-T0) < κ := by
    have h1 : -T0 ≤ Real.log κ - 1 := by
      rw [hT0def]; have := neg_abs_le (Real.log κ); linarith
    have h2 : Real.exp (Real.log κ - 1) = κ / Real.exp 1 := by
      rw [Real.exp_sub, Real.exp_log hκ0]
    have h3 : 1 < Real.exp 1 := by
      have := Real.add_one_lt_exp (one_ne_zero : (1 : ℝ) ≠ 0); linarith
    calc Real.exp (-T0) ≤ Real.exp (Real.log κ - 1) := Real.exp_le_exp.2 h1
      _ = κ / Real.exp 1 := h2
      _ < κ := div_lt_self hκ0 h3
  obtain ⟨s, hs, hsL9⟩ := exitTimeLowerStopped_half h213 h214 h632 γ hγ hγ2 κ hκ0 θ hθ0
  obtain ⟨c2, hc2, hmε⟩ := mε_le_of_exitTimeUpper h214 h217 hγ hγ2
  obtain ⟨N, hN⟩ := exists_measure_coneScaleRadius_le_le hγ hγ2 hS.isQuantumCone (4 * (R + 2))
    (θ := ENNReal.ofReal θ) (ENNReal.ofReal_pos.2 hθ0)
  obtain ⟨m, hm⟩ := exists_nat_ge (max c2 (c2 * T0 / s))
  obtain ⟨b, hbdef⟩ : ∃ b : ℝ, b = ((max N m : ℕ) : ℝ) + 1 := ⟨_, rfl⟩
  have hb : 0 < b := by rw [hbdef]; positivity
  have hbm : max c2 (c2 * T0 / s) ≤ b := by
    rw [hbdef]
    have : (m : ℝ) ≤ ((max N m : ℕ) : ℝ) := by exact_mod_cast le_max_right N m
    linarith
  have hbc2 : c2 ≤ b := (le_max_left _ _).trans hbm
  have hbT : c2 * T0 ≤ b * s := by
    have := (le_max_right _ _).trans hbm
    rwa [div_le_iff₀ hs] at this
  have hE1 : S.P {ω | coneScaleRadius γ (S.hcirc ω) b ≤ 4 * (R + 2)} ≤ ENNReal.ofReal θ := by
    rw [hbdef]; exact hN _ (le_max_left _ _)
  obtain ⟨M, hM⟩ := exists_measure_gt_le_coneScaleRadius hγ hγ2 hS.isQuantumCone b
    (θ := ENNReal.ofReal θ) (ENNReal.ofReal_pos.2 hθ0)
  obtain ⟨M', hM'⟩ : ∃ M' : ℝ, M' = max M 1 := ⟨_, rfl⟩
  have hM'1 : 1 ≤ M' := by rw [hM']; exact le_max_right _ _
  have hM'0 : 0 < M' := lt_of_lt_of_le one_pos hM'1
  have hMM' : M ≤ M' := by rw [hM']; exact le_max_left _ _
  have hE2 : S.P {ω | M' < coneScaleRadius γ (S.hcirc ω) b} ≤ ENNReal.ofReal θ :=
    (measure_mono (fun ω (hω : M' < coneScaleRadius γ (S.hcirc ω) b) => lt_of_le_of_lt hMM' hω)).trans hM
  obtain ⟨S', hS', hP, hηs, hbmS, -⟩ := hEnvS γ hγ hγ2 Ω S hS b hb
  obtain ⟨q0, hq0, hq0E⟩ := hsL9 Ω S' hS'
  obtain ⟨r, hrdef⟩ : ∃ r : ℝ, r = a' / (3 * M') := ⟨_, rfl⟩
  have hr : 0 < r := by rw [hrdef]; positivity
  have h612 := MatedCRT.ExitCouplingBoundaryUnion.limLimSmall_levyProkhorovEDist_stoppedWalk_vertices
    (cellSizeEstimateStmt_holds 𝒮) h32 h213 h214 h219 hγ hγ2 (ρ0 := 1 / 2) (ρ1 := 3 / 4)
    (by norm_num) (by norm_num) (by norm_num) (h632 γ hγ hγ2 (3 / 4) (by norm_num) (by norm_num))
    h636 hbd hr Ω S' hS'
  obtain ⟨δ0, hδ0, h612a⟩ := h612 θ hθ0
  obtain ⟨e0, he0, h612b⟩ := h612a (δ0 / 2) (half_pos hδ0) (half_lt_self hδ0)
  obtain ⟨e1, he1, hmε'⟩ := hmε Ω S hS
  refine ⟨δ0 / 2, half_pos hδ0, ?_⟩
  have hev : ∀ᶠ n in atTop, eps n < min e1 (min (e0 * b) (q0 * b)) :=
    hε.eventually (gt_mem_nhds (lt_min he1 (lt_min (mul_pos he0 hb) (mul_pos hq0 hb))))
  filter_upwards [hev] with n hn
  have hn1 : eps n < e1 := hn.trans_le (min_le_left _ _)
  have hn2 : eps n < e0 * b := hn.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hn3 : eps n < q0 * b := hn.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hq : 0 < eps n / b := div_pos (hε0 n) hb
  have hmn := hmε' (eps n) (hε0 n) hn1
  have hlam : S.mε (eps n) * (eps n / b) ≤ 1 := by
    have h1 : S.mε (eps n) * (eps n / b) ≤ c2 * (eps n)⁻¹ * (eps n / b) :=
      mul_le_mul_of_nonneg_right hmn hq.le
    have h2 : c2 * (eps n)⁻¹ * (eps n / b) = c2 / b := by
      have := (hε0 n).ne'
      have := hb.ne'
      field_simp
    have h3 : c2 / b ≤ 1 := (div_le_one hb).2 hbc2
    linarith
  have hmT0 : S.mε (eps n) * T0 ≤ (eps n / b)⁻¹ * s := by
    have h1 : S.mε (eps n) * T0 ≤ c2 * (eps n)⁻¹ * T0 := mul_le_mul_of_nonneg_right hmn hT0
    have h2 : c2 * (eps n)⁻¹ * T0 = c2 * T0 / eps n := by
      have := (hε0 n).ne'
      field_simp
    have h3 : (eps n / b)⁻¹ * s = b * s / eps n := by
      have := (hε0 n).ne'
      have := hb.ne'
      field_simp
    have h4 : c2 * T0 / eps n ≤ b * s / eps n := by
      have := hε0 n
      gcongr
    rw [h3]
    linarith
  have hE3 := hq0E (eps n / b) hq ((div_lt_iff₀ hb).2 hn3)
  have hE4 := h612b (eps n / b) hq ((div_lt_iff₀ hb).2 hn2)
  have hmain := eqLaw_event_of_scaling hγ hγ2 hS' hP η' hae hb hηs hbmS (hε0 n) hκ0 hT0 hκT
    hr.le hlam hmT0 hE1 hE2 hE3 hE4
  have hsum : 2 * κ + M' * r = a' := by
    have := hM'0.ne'
    rw [hκ, hrdef]; field_simp; ring
  rw [hsum] at hmain
  calc S.P {ω | ENNReal.ofReal a < walkLawModulus S η' (eps n) R (δ0 / 2) ω}
      ≤ S.P {ω | ENNReal.ofReal a' < walkLawModulus S η' (eps n) R (δ0 / 2) ω} :=
        measure_mono (fun ω hω => lt_of_le_of_lt (ENNReal.ofReal_le_ofReal ha'a) hω)
    _ ≤ 4 * ENNReal.ofReal θ := hmain
    _ ≤ ENNReal.ofReal a := by
        rw [show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by simp, ← ENNReal.ofReal_mul (by norm_num)]
        exact ENNReal.ofReal_le_ofReal (by rw [hθ]; linarith)

end MatedCRT.FirstPass.Derived
