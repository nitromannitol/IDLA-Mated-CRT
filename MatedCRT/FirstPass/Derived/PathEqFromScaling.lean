import MatedCRT.FirstPass.Derived.EqLawFromScaling
import MatedCRT.FirstPass.Derived.PathEventOfScaling
import MatedCRT.FirstPass.Derived.ExitCouplingPathEvent

/-!
# Equicontinuity of the paths of the unstopped quenched walks

Berestycki and Gwynne, *Random walks on mated-CRT planar maps and Liouville Brownian motion*
(arXiv:2003.10320), proof of Proposition 6.1 (the second condition of Lemma 6.3).  Parameter chase for the
fixed cone-scale event bound `pathFailure_event_of_scaling`, the analogue for the path modulus of the unstopped
walks of `hEqLaw_of_scaling`.

For a valid environment `S` with the cone-scale rescaling `hEnvS`, every level `R`, every `L > 0` and every
`a > 0`, there is a scale `δ > 0` such that for all large `n`, with probability at least `1 - a`, the quenched
interpolated walk of speed `m_ε` started from any vertex of `V^{ε_n}(B_{R+1})` has, with probability at most
`a`, a modulus of continuity on `[0, L]` at scale `δ` larger than `1 / L`
(the event `LatticeProb.pathModulusFailure L δ`).
-/

set_option autoImplicit false

namespace MatedCRT.FirstPass.Derived

open MeasureTheory Set Metric Filter LatticeProb
open scoped ENNReal NNReal Topology
open MarkovProcess (ContinuousPath)
open MatedCRT.SuccessiveExitGaps

/-- **Equicontinuity of the unstopped quenched walk laws from the cone-rescaled stopped walks** (Berestycki–Gwynne
(2020), proof of Proposition 6.1).  See the module docstring.  Hypotheses: the Green kernel lower bound
(Lemma 2.13), the exit time moment bound (Lemma 2.14), the bounded exit time random variable (Lemma 2.17),
the cone scaling of valid environments, the estimate (6.32) of Lemma 6.9 and the estimate (6.36). -/
theorem hEqPath_of_scaling {𝒮 : SpaceFillingSLEModel}
    (h213 : GreenKernelLowerBoundStmt 𝒮) (h214 : ExitTimeUpperBoundStmt 𝒮)
    (h217 : BoundedExitTimeRVStmt)
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
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    {η' : Ω → C(ℝ, ℂ)} (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω)
    {eps : ℕ → ℝ} (hε0 : ∀ n, 0 < eps n) (hε : Tendsto eps atTop (𝓝 0)) :
    ∀ R L a : ℝ, 0 < L → 0 < a → ∃ δ : ℝ≥0, 0 < δ ∧ ∀ᶠ n in atTop,
      S.P {ω | ∃ j : ℤ, vertexPoint (eps n) (⇑(η' ω)) j ∈ ball (0 : ℂ) (R + 1) ∧
        ENNReal.ofReal a <
          ((walkPathLaw S (fun ω => vertexPoint (eps n) (⇑(η' ω))) (S.mε_nonneg (eps n)) (eps n) j ω :
            ProbabilityMeasure (ContinuousPath ℂ)) : Measure (ContinuousPath ℂ))
            (pathModulusFailure (E := ℂ) L δ)} ≤ ENNReal.ofReal a := by
  intro R L a hL ha
  have : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = a / 2 := ⟨_, rfl⟩
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = a / 4 := ⟨_, rfl⟩
  have hκ0 : 0 < κ := by rw [hκ]; positivity
  have hθ0 : 0 < θ := by rw [hθ]; positivity
  obtain ⟨s, hs, hsL9⟩ := exitTimeLowerStopped_half h213 h214 h632 γ hγ hγ2 κ hκ0 θ hθ0
  obtain ⟨c2, hc2, hmε⟩ := mε_le_of_exitTimeUpper h214 h217 hγ hγ2
  obtain ⟨N, hN⟩ := exists_measure_coneScaleRadius_le_le hγ hγ2 hS.isQuantumCone (4 * (R + 2))
    (θ := ENNReal.ofReal θ) (ENNReal.ofReal_pos.2 hθ0)
  obtain ⟨m, hm⟩ := exists_nat_ge (max c2 (c2 * L / s))
  obtain ⟨b, hbdef⟩ : ∃ b : ℝ, b = ((max N m : ℕ) : ℝ) + 1 := ⟨_, rfl⟩
  have hb : 0 < b := by rw [hbdef]; positivity
  have hbm : max c2 (c2 * L / s) ≤ b := by
    rw [hbdef]
    have : (m : ℝ) ≤ ((max N m : ℕ) : ℝ) := by exact_mod_cast le_max_right N m
    linarith
  have hbc2 : c2 ≤ b := (le_max_left _ _).trans hbm
  have hbL : c2 * L ≤ b * s := by
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
  obtain ⟨χ, hχ, hP2⟩ := MatedCRT.ExitCouplingPathEvent.limLimSmall_stoppedOscillation h213 h214 hγ hγ2 (ρ0 := 1 / 2) (ρ1 := 3 / 4)
    (by norm_num) (by norm_num) (by norm_num) (h632 γ hγ hγ2 (3 / 4) (by norm_num) (by norm_num)) h636
  have hr : 0 < 1 / (L * M') := by positivity
  obtain ⟨δ0, hδ0, hLL⟩ := hP2 hr hθ0 Ω S' hS' θ hθ0
  obtain ⟨e0, he0, hLL2⟩ := hLL (δ0 / 2) (half_pos hδ0) (half_lt_self hδ0)
  obtain ⟨e1, he1, hmε'⟩ := hmε Ω S hS
  have hδpos : 0 < (((δ0 / 2) ^ χ / 2).toNNReal) := by
    rw [Real.toNNReal_pos]; positivity
  refine ⟨((δ0 / 2) ^ χ / 2).toNNReal, hδpos, ?_⟩
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
  have hmL : S.mε (eps n) * L ≤ (eps n / b)⁻¹ * s := by
    have h1 : S.mε (eps n) * L ≤ c2 * (eps n)⁻¹ * L := mul_le_mul_of_nonneg_right hmn hL.le
    have h2 : c2 * (eps n)⁻¹ * L = c2 * L / eps n := by
      have := (hε0 n).ne'
      field_simp
    have h3 : (eps n / b)⁻¹ * s = b * s / eps n := by
      have := (hε0 n).ne'
      have := hb.ne'
      field_simp
    have h4 : c2 * L / eps n ≤ b * s / eps n := by
      have := hε0 n
      gcongr
    rw [h3]
    linarith
  have hE3 := hq0E (eps n / b) hq ((div_lt_iff₀ hb).2 hn3)
  have hE4 := hLL2 (eps n / b) hq ((div_lt_iff₀ hb).2 hn2)
  have hmain := pathFailure_event_of_scaling hγ hγ2 hS' hP η' hae hb hηs hbmS
    (((δ0 / 2) ^ χ / 2).toNNReal) (hε0 n) hL hlam hmL hE1 hE2 hE3 hE4
  have hsum : ENNReal.ofReal κ + ENNReal.ofReal θ ≤ ENNReal.ofReal a := by
    rw [← ENNReal.ofReal_add hκ0.le hθ0.le]
    exact ENNReal.ofReal_le_ofReal (by rw [hκ, hθ]; linarith)
  calc S.P {ω | ∃ j : ℤ, vertexPoint (eps n) (⇑(η' ω)) j ∈ ball (0 : ℂ) (R + 1) ∧
        ENNReal.ofReal a <
          ((walkPathLaw S (fun ω => vertexPoint (eps n) (⇑(η' ω))) (S.mε_nonneg (eps n)) (eps n) j ω :
            ProbabilityMeasure (ContinuousPath ℂ)) : Measure (ContinuousPath ℂ))
            (pathModulusFailure (E := ℂ) L ((((δ0 / 2) ^ χ / 2).toNNReal)))}
      ≤ S.P {ω | ∃ j : ℤ, vertexPoint (eps n) (⇑(η' ω)) j ∈ ball (0 : ℂ) (R + 1) ∧
        ENNReal.ofReal κ + ENNReal.ofReal θ <
          ((walkPathLaw S (fun ω => vertexPoint (eps n) (⇑(η' ω))) (S.mε_nonneg (eps n)) (eps n) j ω :
            ProbabilityMeasure (ContinuousPath ℂ)) : Measure (ContinuousPath ℂ))
            (pathModulusFailure (E := ℂ) L ((((δ0 / 2) ^ χ / 2).toNNReal)))} :=
        measure_mono (fun ω ⟨j, hj, hlt⟩ => ⟨j, hj, lt_of_le_of_lt hsum hlt⟩)
    _ ≤ 4 * ENNReal.ofReal θ := hmain
    _ ≤ ENNReal.ofReal a := by
        rw [show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by simp, ← ENNReal.ofReal_mul (by norm_num)]
        exact ENNReal.ofReal_le_ofReal (by rw [hθ]; linarith)

end MatedCRT.FirstPass.Derived
