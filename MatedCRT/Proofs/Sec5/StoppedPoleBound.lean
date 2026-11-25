import MatedCRT.Draft.Section2
import MatedCRT.Draft.Section4
import MatedCRT.Proofs.Sec3.UniformConvergenceGreenKernel.KernelMonotonicity
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.AnnulusBarriers
import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.GoodEventBoundedModulus
import MatedCRT.Proofs.Sec4.ObstacleSpecialization.Final
import MatedCRT.FirstPass.S5u
import MatedCRT.FirstPass.S3i.GoodEvent
import MatedCRT.FirstPass.S3c.ExitTimeBridge
import MatedCRT.FirstPass.Derived.DegreeCutoffMeasurable
import MatedCRT.Proofs.Infra.Setting

/-!
# The discrete surplus at the pole

The first part of the lower bound of the stopped surplus near the source in Proposition 5.1 (the step
`StoppedInterior.StoppedSurplusPoleStep`). Let `D = V^ε(B_ρ) \ V^ε(∂B_ρ)`, `w̃^ε_t` the discrete least supersolution of
the obstacle problem in `D` and `v^ε_t = w̃^ε_t + (t/ε) g^ε_D(0, ·)` the surplus. Write
`𝓜 = 𝓜(B_{(1+ρ)/2})` for the random variable of Lemma 2.17 (`largestExitTimeRV`), which is finite almost surely and does
not depend on the mesh.

* `w̃^ε_t ≥ -q_D` with `q_D = ∑_{b ∈ D} g_D(·, b)` (the discrete basic properties), and `ε q_D ≤ K 𝓜` by Lemma 2.18;
* by Lemma 2.16 at the source `0` in the disk `B_{ρ/2}`, and the monotonicity of the killed Green kernel in the killing
  set, `g_D(0, a) ≥ K⁻¹ log((ρ/2)/r) - 1` for every vertex `a` with `|η(a)| < r ≤ ρ/6` once `ε ≤ 2r/ρ`.

Hence `ε v^ε_t(a) ≥ t (K⁻¹ log(ρ/(2r)) - 1) - K M` on `{𝓜 ≤ M}`, outside the failure events of Lemmas 2.16 and 2.18.
For each `M` a deterministic radius `r(M)` makes the right-hand side at least `1`. This is the discrete logarithmic
bound at zero of the consultant's answer to target 8 (the stopped sandpile at its pole); the bound on the annulus
`r(M) ≤ |η(a)| < s` comes from Theorem 4.1 and Lemma 3.3 and is not in this file.

## Main results

* `stoppedPoleLowerBound`: the event `{𝓜 ≤ M} → ∀ a, |η(a)| < r → 1/ε ≤ v^ε_t(a)` has polynomially high probability,
  with a constant `K` chosen before the environment, for every `t > 0`, `M ≥ 0` and `0 < r ≤ ρ/6` with
  `t (K⁻¹ log(ρ/(2r)) - 1) - K M ≥ 1`;
* `stoppedPoleLowerBound_tendsToOneOn`: on `{𝓜 ≤ M}` the same event holds with probability tending to one.
-/

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace MatedCRT

/-- The `δ`-thickening of `B_ρ(0)` lies in `B_{ρ + δ}(0)`. -/
theorem thickening_ball_zero_subset {ρ δ : ℝ} : thickening δ (ball (0 : ℂ) ρ) ⊆ ball 0 (ρ + δ) := by
  intro x hx
  obtain ⟨z, hz, hxz⟩ := mem_thickening_iff.1 hx
  rw [mem_ball_zero_iff] at hz ⊢
  have : ‖x‖ ≤ ‖z‖ + dist x z := by
    rw [dist_eq_norm]
    calc ‖x‖ = ‖z + (x - z)‖ := by rw [add_sub_cancel]
      _ ≤ ‖z‖ + ‖x - z‖ := norm_add_le _ _
  linarith

/-- For `0 < x` and `0 < b`, `ε < x^{1/b}` implies `ε^b < x`. -/
theorem rpow_lt_of_lt_rpow_inv {ε x b : ℝ} (hε : 0 ≤ ε) (hx : 0 < x) (hb : 0 < b) (h : ε < x ^ b⁻¹) :
    ε ^ b < x :=
  calc ε ^ b < (x ^ b⁻¹) ^ b := Real.rpow_lt_rpow hε h hb
    _ = x := Real.rpow_inv_rpow hx.le hb.ne'

/-- **The discrete surplus at the pole** (target 8, the logarithmic bound at zero). For `γ ∈ (0, 2)` and `ρ ∈ (0, 1)`
there is `K > 0`, chosen before the environment, such that for every valid environment, every `t > 0`, `M ≥ 0` and
`0 < r ≤ ρ/6` with `t (K⁻¹ log(ρ/(2r)) - 1) - K M ≥ 1`, with polynomially high probability as `ε → 0`: if
`𝓜(B_{(1+ρ)/2}) ≤ M`, then `1/ε ≤ w̃^ε_t(a) + (t/ε) g^ε_D(0, a)` for every vertex `a` with `|η(a)| < r`. -/
theorem stoppedPoleLowerBound {𝒮 : SpaceFillingSLEModel} (h216 : GreenKernelLowerBoundStmt 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮) {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) {ρ : ℝ} (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
    ∀ t M r : ℝ, 0 < t → 0 ≤ M → 0 < r → r ≤ ρ / 6 →
      1 ≤ t * (K⁻¹ * Real.log (ρ / (2 * r)) - 1) - K * M →
      HarmonicBalls.PolyHighProb S.P fun ε => {ω |
        largestExitTimeRV (S.μ ω) (ball 0 ((1 + ρ) / 2)) ≤ ENNReal.ofReal M →
        ∀ a : ℤ, ‖vertexPoint ε (S.η ω) a‖ < r →
          1 / ε ≤ matedLeastSupersolution (S.mult ε ω) ε (S.η ω) ρ t a +
            t / ε * greenKernel (S.mult ε ω) (ballInterior ε (S.η ω) ρ) 0 a} := by
  have hρ2 : 0 < (1 + ρ) / 2 := by linarith
  have hρ21 : (1 + ρ) / 2 < 1 := by linarith
  have hρρ2 : ρ < (1 + ρ) / 2 := by linarith
  obtain ⟨ω₀, hω₀, hG⟩ := h216 γ hγ0 hγ2
  obtain ⟨C₂, hC₂, hG'⟩ := hG ρ hρ0 hρ1
  obtain ⟨α, hα, hE⟩ := h218 γ hγ0 hγ2
  obtain ⟨C₁, hC₁, hE'⟩ := hE ((1 + ρ) / 2) hρ2 hρ21
  refine ⟨max C₁ C₂, lt_max_of_lt_left hC₁, fun Ω _ S hS t M r ht hM hr hr6 hK => ?_⟩
  have hK0 : 0 < max C₁ C₂ := lt_max_of_lt_left hC₁
  have hbasic := discreteBasicProperties 𝒮 γ hγ0 hγ2 ρ hρ0 hρ1 Ω S hS
  have hq : ∀ᵐ ω ∂S.P, ((Continuous (S.η ω) ∧ S.η ω 0 = 0) ∧ Tendsto (S.η ω) (cocompact ℝ) (cocompact ℂ)) ∧
      (∀ ε : ℝ, 0 < ε → IsLocallyFiniteMult (S.mult ε ω)) ∧
      ∀ t ε : ℝ, 0 < t → 0 < ε →
        (∀ a ∈ cellVertices ε (S.η ω) (closedBall 0 ρ),
          max (-normExitTime (S.mult ε ω) (ballInterior ε (S.η ω) ρ) a)
              (matedObstacle (S.mult ε ω) ε (S.η ω) ρ t a) ≤
            matedLeastSupersolution (S.mult ε ω) ε (S.η ω) ρ t a ∧
          matedLeastSupersolution (S.mult ε ω) ε (S.η ω) ρ t a ≤ 0) ∧
        ∀ a ∈ ballInterior ε (S.η ω) ρ,
          matedLaplacian (S.mult ε ω) (matedLeastSupersolution (S.mult ε ω) ε (S.η ω) ρ t) a ≤
            ((matedDeg (S.mult ε ω) a : ℕ) : ℝ)⁻¹ := by
    filter_upwards [hS.isAreaParametrized, hS.ae_tendsto_cocompact,
      FirstPass.Derived.ae_isLocallyFiniteMult_of_isValid hS, hbasic] with ω hap hp hlf hb
    exact ⟨⟨⟨hap.1, hap.2.1⟩, hp⟩, hlf, hb⟩
  have hr₁ : 0 < min (min ((ρ / 2) ^ ω₀⁻¹) (((1 - ρ) / 2) ^ α⁻¹)) (2 * r / ρ) := by
    have h1 : 0 < (ρ / 2) ^ ω₀⁻¹ := Real.rpow_pos_of_pos (by linarith) _
    have h2 : 0 < ((1 - ρ) / 2) ^ α⁻¹ := Real.rpow_pos_of_pos (by linarith) _
    have h3 : 0 < 2 * r / ρ := by positivity
    exact lt_min (lt_min h1 h2) h3
  refine S3cBridge.polyHighProb_mono_ae_small hr₁ (FirstPass36.polyHighProb_inter (hG' Ω S hS) (hE' Ω S hS)) hq ?_
  intro ε hε hεr ω hω hqω
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq] at hω ⊢
  obtain ⟨hωG, hωE⟩ := hω
  obtain ⟨⟨⟨hηc, hη0⟩, hηp⟩, hlfω, hbω⟩ := hqω
  have hεω₀ : ε ^ ω₀ < ρ / 2 := rpow_lt_of_lt_rpow_inv hε.le (by linarith) hω₀
    (hεr.trans_le ((min_le_left _ _).trans (min_le_left _ _)))
  have hεα : ε ^ α < (1 - ρ) / 2 := rpow_lt_of_lt_rpow_inv hε.le (by linarith) hα
    (hεr.trans_le ((min_le_left _ _).trans (min_le_right _ _)))
  have hεr' : ε < 2 * r / ρ := hεr.trans_le (min_le_right _ _)
  intro hMω a ha
  set m := S.mult ε ω with hm
  set η := S.η ω with hη
  have hlf := hlfω ε hε
  have hcons : ∀ k : ℤ, m k (k + 1) ≠ 0 := fun k => S.mult_succ_ne_zero hε.le ω k
  have hv0 : vertexPoint ε η 0 = 0 := by
    simp [vertexPoint, hη0]
  have hvk : ∀ k : ℤ, vertexPoint ε η k ∈ cell ε η k := fun k =>
    ⟨ε * k, ⟨mul_le_mul_of_nonneg_left (by linarith) hε.le, le_rfl⟩, rfl⟩
  have hva := hvk a
  -- the exit-time potential
  have haρ : a ∈ cellVertices ε η (ball 0 ρ) :=
    ⟨vertexPoint ε η a, hva, mem_ball_zero_iff.2 (by linarith)⟩
  have hqbound : normExitTime m (ballInterior ε η ρ) a ≤ C₁ * ε⁻¹ * M := by
    obtain ⟨h1, h2⟩ := hωE.2 (ball 0 ρ) (ball_subset_ball hρρ2.le) a haρ
    have hthick : thickening (ε ^ α) (ball (0 : ℂ) ρ) ⊆ ball 0 ((1 + ρ) / 2) :=
      thickening_ball_zero_subset.trans (ball_subset_ball (by linarith))
    have h3 : largestExitTimeRV (S.μ ω) (thickening (ε ^ α) (ball 0 ρ)) ≤ ENNReal.ofReal M :=
      (largestExitTimeRV_mono _ hthick).trans hMω
    have h4 : ENNReal.ofReal (normExitTime m (ballInterior ε η ρ) a) ≤ ENNReal.ofReal (C₁ * ε⁻¹ * M) := by
      calc ENNReal.ofReal (normExitTime m (ballInterior ε η ρ) a)
          ≤ ENNReal.ofReal (C₁ * ε⁻¹) * largestExitTimeRV (S.μ ω) (thickening (ε ^ α) (ball 0 ρ)) :=
            h1.trans h2
        _ ≤ ENNReal.ofReal (C₁ * ε⁻¹) * ENNReal.ofReal M := by gcongr
        _ = ENNReal.ofReal (C₁ * ε⁻¹ * M) :=
            (ENNReal.ofReal_mul (by positivity)).symm
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h4
  have hwlow : -normExitTime m (ballInterior ε η ρ) a ≤ matedLeastSupersolution m ε η ρ t a :=
    (le_max_left _ _).trans ((hbω t ε ht hε).1 a ⟨vertexPoint ε η a, hva, mem_closedBall_zero_iff.2 (by linarith)⟩).1
  -- the Green kernel at the pole
  have h0mem : (0 : ℤ) ∈ cellVertices ε η (ball 0 (ρ - ε ^ ω₀)) := by
    refine ⟨vertexPoint ε η 0, hvk 0, ?_⟩
    rw [hv0, mem_ball_zero_iff, norm_zero]
    linarith
  have hinf : ρ / 2 ≤ infDist (vertexPoint ε η 0) (sphere 0 ρ) := by
    rw [hv0, le_infDist (NormedSpace.sphere_nonempty.2 hρ0.le)]
    intro y hy
    rw [dist_comm, dist_zero_right, mem_sphere_zero_iff_norm.1 hy]
    linarith
  have hab : a ∈ cellVertices ε η (ball (vertexPoint ε η 0) (ρ / 2 / 3)) :=
    ⟨vertexPoint ε η a, hva, by rw [hv0, mem_ball_zero_iff]; linarith⟩
  have hlog := (hωG 0 h0mem (ρ / 2) hεω₀.le hinf a hab).2
  rw [hv0] at hlog
  have hL0 : 0 ≤ Real.log (ρ / (2 * r)) := Real.log_nonneg (by
    rw [le_div_iff₀ (by positivity)]
    linarith)
  have hlogL : Real.log (ρ / (2 * r)) ≤
      Real.log (if (0 : ℂ) = vertexPoint ε η a then ε⁻¹
        else min (ρ / 2 / ‖0 - vertexPoint ε η a‖) ε⁻¹) := by
    have hεinv : ρ / (2 * r) < ε⁻¹ := by
      rw [lt_inv_comm₀ (by positivity) hε, inv_div]
      exact hεr'
    have hpos : 0 < ρ / (2 * r) := by positivity
    split_ifs with h0a
    · exact Real.log_le_log hpos hεinv.le
    · have hn : 0 < ‖0 - vertexPoint ε η a‖ := norm_pos_iff.2 (sub_ne_zero.2 h0a)
      have hn' : ‖0 - vertexPoint ε η a‖ < r := by rw [zero_sub, norm_neg]; exact ha
      refine Real.log_le_log hpos (le_min ?_ hεinv.le)
      rw [div_div, div_le_div_iff₀ (by positivity) (by linarith)]
      exact mul_le_mul_of_nonneg_left (by linarith) hρ0.le
  have hsubI : interiorCellVertices ε η (ball (0 : ℂ) (ρ / 2)) ⊆ ballInterior ε η ρ :=
    interiorCellVertices_concentric_ball_mono hηc 0 (by linarith)
  have hfinA : (interiorCellVertices ε η (ball (0 : ℂ) (ρ / 2))).Finite :=
    (cellVertices_ball_finite_of_proper hηc hηp hε 0 (ρ / 2)).subset Set.sdiff_subset
  have hfinB : (ballInterior ε η ρ).Finite :=
    (cellVertices_ball_finite_of_proper hηc hηp hε 0 ρ).subset Set.sdiff_subset
  have hmono := greenKernel_mono_of_finite hlf hcons hfinA hfinB hsubI 0 a
  have hgreen : (max C₁ C₂)⁻¹ * Real.log (ρ / (2 * r)) - 1 ≤ greenKernel m (ballInterior ε η ρ) 0 a := by
    have hinvC : (max C₁ C₂)⁻¹ ≤ C₂⁻¹ := inv_anti₀ hC₂ (le_max_right _ _)
    calc (max C₁ C₂)⁻¹ * Real.log (ρ / (2 * r)) - 1 ≤ C₂⁻¹ * Real.log (ρ / (2 * r)) - 1 :=
          sub_le_sub_right (mul_le_mul_of_nonneg_right hinvC hL0) 1
      _ ≤ C₂⁻¹ * Real.log (if (0 : ℂ) = vertexPoint ε η a then ε⁻¹
            else min (ρ / 2 / ‖0 - vertexPoint ε η a‖) ε⁻¹) - 1 :=
          sub_le_sub_right (mul_le_mul_of_nonneg_left hlogL (inv_nonneg.2 hC₂.le)) 1
      _ ≤ greenKernel m (interiorCellVertices ε η (ball (0 : ℂ) (ρ / 2))) 0 a := hlog
      _ ≤ greenKernel m (ballInterior ε η ρ) 0 a := hmono
  -- combine
  have hC1 : C₁ * M ≤ max C₁ C₂ * M := mul_le_mul_of_nonneg_right (le_max_left _ _) hM
  have hεinv : 0 < ε⁻¹ := inv_pos.2 hε
  have key : 1 ≤ t * greenKernel m (ballInterior ε η ρ) 0 a - C₁ * M := by
    have := mul_le_mul_of_nonneg_left hgreen ht.le
    linarith
  calc 1 / ε = ε⁻¹ * 1 := by ring
    _ ≤ ε⁻¹ * (t * greenKernel m (ballInterior ε η ρ) 0 a - C₁ * M) :=
        mul_le_mul_of_nonneg_left key hεinv.le
    _ = -(C₁ * ε⁻¹ * M) + t / ε * greenKernel m (ballInterior ε η ρ) 0 a := by ring
    _ ≤ -normExitTime m (ballInterior ε η ρ) a + t / ε * greenKernel m (ballInterior ε η ρ) 0 a := by
        linarith
    _ ≤ matedLeastSupersolution m ε η ρ t a + t / ε * greenKernel m (ballInterior ε η ρ) 0 a := by
        linarith

/-- **The discrete surplus at the pole, on `{𝓜 ≤ M}`**: under the conditions of `stoppedPoleLowerBound`, the event
`∀ a, |η(a)| < r → 1/ε ≤ v^ε_t(a)` holds on `{𝓜(B_{(1+ρ)/2}) ≤ M}` with probability tending to one. -/
theorem stoppedPoleLowerBound_tendsToOneOn {𝒮 : SpaceFillingSLEModel} (h216 : GreenKernelLowerBoundStmt 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮) {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) {ρ : ℝ} (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
    ∀ t M r : ℝ, 0 < t → 0 ≤ M → 0 < r → r ≤ ρ / 6 →
      1 ≤ t * (K⁻¹ * Real.log (ρ / (2 * r)) - 1) - K * M →
      TendsToOneOn S.P {ω | largestExitTimeRV (S.μ ω) (ball 0 ((1 + ρ) / 2)) ≤ ENNReal.ofReal M}
        fun ε => {ω | ∀ a : ℤ, ‖vertexPoint ε (S.η ω) a‖ < r →
          1 / ε ≤ matedLeastSupersolution (S.mult ε ω) ε (S.η ω) ρ t a +
            t / ε * greenKernel (S.mult ε ω) (ballInterior ε (S.η ω) ρ) 0 a} := by
  obtain ⟨K, hK, h⟩ := stoppedPoleLowerBound h216 h218 hγ0 hγ2 hρ0 hρ1
  refine ⟨K, hK, fun Ω _ S hS t M r ht hM hr hr6 hKr => ?_⟩
  have hlim := polyHighProb_compl_tendsto_zero (h Ω S hS t M r ht hM hr hr6 hKr)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => zero_le) (Eventually.of_forall fun ε => measure_mono ?_)
  rintro ω ⟨hM', hnot⟩ himp
  exact hnot (himp hM')

end MatedCRT

/-! ## Audit -/
#print axioms MatedCRT.stoppedPoleLowerBound
#print axioms MatedCRT.stoppedPoleLowerBound_tendsToOneOn
