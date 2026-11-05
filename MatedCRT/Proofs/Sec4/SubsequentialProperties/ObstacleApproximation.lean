import MatedCRT.Proofs.Sec4.SubsequentialProperties.Corrected
import MatedCRT.Proofs.Sec4.DivSandpileLowerBound.SourceVertex
import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.Cells
import MatedCRT.Proofs.Infra.MatingOfTrees

/-!
# Lemma 4.8: the obstacle approximation step

`odometerObstacleApproximationStep` proves `OdometerObstacleApproximationStep` (MatedCRT/Steps/Sec4/
SubsequentialProperties.lean), Step 1 of the proof of Lemma 4.8 (paper/idla_mated_crt-corrected.tex, l.1786-1801):

* the rescaled bounds `-(t ε⁻¹) ḡ^ε ≤ w̄^ε_t ≤ 0` on `cl(B_ρ)` follow from Lemma 4.3 at the vertex `a^ε_x`, whose cell
  contains `x` (`Tightness.mem_cell_vertexOf`), and from `m_ε ≥ 0` (`MatedCRTEnv.mε_nonneg`);
* the convergence of the rescaled obstacle at each `x ∈ cl(B_ρ) \ {0}` follows from Lemma 3.3 with `y = 0`,
  `B_r(z) = B_ρ`, on the annuli `cl(B_ρ) \ B_{ρ/(j+2)}` with accuracy `1/(j+1)`. The source vertex `a^ε_0` of Lemma 3.3
  is `0` almost surely (`MatedCRTEnv.IsValid.ae_vertexOf_zero_eq_zero`, E-x3-3). Lemma 3.3 holds in probability; a
  diagonal deterministic subsequence along which the failure probabilities of the first `n` annuli are at most `2^{-n}`
  makes it hold almost surely, eventually, for every annulus (Borel-Cantelli,
  `exists_strictMono_ae_eventually_mem_all`).
-/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric HarmonicBalls
open scoped ENNReal

/-- `m_ε ≥ 0`: the median `m_ε` (eq:meps) is an infimum of nonnegative reals. -/
theorem MatedCRTEnv.mε_nonneg {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ε : ℝ) : 0 ≤ S.mε ε := by
  unfold MatedCRTEnv.mε medianOf
  exact Real.sInf_nonneg fun _ hm => hm.1

/-- **Borel-Cantelli along a diagonal subsequence.** If each of countably many events `E j ε` holds with probability
tending to one as `ε → 0`, and `ε_n → 0` (`ε_n > 0`), there is a deterministic strictly increasing `φ` such that
almost surely, for every `j`, `ω ∈ E j (ε_{φ(n)})` for all large `n`. -/
theorem exists_strictMono_ae_eventually_mem_all {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {E : ℕ → ℝ → Set Ω} (hE : ∀ j, ProbTendsToOne P (E j)) {εs : ℕ → ℝ} (hεs : ∀ n, 0 < εs n)
    (hεs0 : Tendsto εs atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ ω ∂P, ∀ j, ∀ᶠ n in atTop, ω ∈ E j (εs (φ n)) := by
  have hεs' : Tendsto εs atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hεs0 (Eventually.of_forall hεs)
  have hlim : ∀ j, Tendsto (fun k => P (E j (εs k))ᶜ) atTop (𝓝 0) := fun j => (hE j).comp hεs'
  have hpos : ∀ n : ℕ, (0 : ℝ≥0∞) < ENNReal.ofReal (1 / 2) ^ n := fun n =>
    ENNReal.pow_pos (ENNReal.ofReal_pos.2 (by norm_num)) n
  have hev : ∀ n : ℕ, ∀ᶠ k in atTop, ∀ j ∈ Set.Iic n,
      P (E j (εs k))ᶜ < ENNReal.ofReal (1 / 2) ^ n := by
    intro n
    refine (Filter.eventually_all_finite (Set.finite_Iic n)).2 fun j _ => ?_
    exact (hlim j).eventually (Iio_mem_nhds (hpos n))
  obtain ⟨φ, hφ, hφP⟩ := Filter.extraction_forall_of_eventually hev
  refine ⟨φ, hφ, ?_⟩
  rw [ae_all_iff]
  intro j
  have hbound : ∀ n, P {ω | j ≤ n ∧ ω ∈ (E j (εs (φ n)))ᶜ} ≤ ENNReal.ofReal (1 / 2) ^ n := by
    intro n
    by_cases hjn : j ≤ n
    · exact (measure_mono fun ω hω => hω.2).trans (hφP n j hjn).le
    · have hsub : {ω | j ≤ n ∧ ω ∈ (E j (εs (φ n)))ᶜ} ⊆ ∅ := fun ω hω => absurd hω.1 hjn
      exact (measure_mono hsub).trans (by simp)
  have hr1 : ENNReal.ofReal (1 / 2) < 1 := ENNReal.ofReal_lt_one.2 (by norm_num)
  have hsum : ∑' n, P {ω | j ≤ n ∧ ω ∈ (E j (εs (φ n)))ᶜ} ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hbound)
    rw [ENNReal.tsum_geometric]
    exact ENNReal.inv_ne_top.2 (tsub_pos_of_lt hr1).ne'
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  filter_upwards [hω, eventually_ge_atTop j] with n hn hjn
  by_contra hc
  exact hn ⟨hjn, hc⟩

/-- **Step 1 of the proof of Lemma 4.8** (l.1786-1801): along a deterministic subsequence, almost surely, for all
`t > 0`, the rescaled bounds `ō^ε_t ≤ w̄^ε_t ≤ 0` hold on `cl(B_ρ)` (Lemma 4.3) and the rescaled obstacle
`ō^ε_t = -(t ε⁻¹) ḡ^ε` converges to `-t (c₀/6) G_{B_ρ}(0, ·)` off the pole (Lemma 3.3). -/
theorem odometerObstacleApproximationStep (𝒮 : SpaceFillingSLEModel) :
    OdometerObstacleApproximationStep 𝒮 := by
  intro h33 h43 γ hγ hγ' ρ hρ hρ' Ω _ S hS εs hε hε0
  have hj2 : ∀ j : ℕ, (0 : ℝ) < (j : ℝ) + 2 := fun j => by positivity
  have hr_pos : ∀ j : ℕ, 0 < ρ / ((j : ℝ) + 2) := fun j => div_pos hρ (hj2 j)
  have hr_lt : ∀ j : ℕ, ρ / ((j : ℝ) + 2) < ρ := fun j =>
    div_lt_self hρ (by have := (Nat.cast_nonneg j : (0 : ℝ) ≤ j); linarith)
  have hδ : ∀ j : ℕ, (0 : ℝ) < 1 / ((j : ℝ) + 1) := fun j => by positivity
  have hρn : ‖(ρ : ℂ)‖ = ρ := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ]
  have hsub : ∀ j : ℕ, closedBall (0 : ℂ) ρ \ ball 0 (ρ / ((j : ℝ) + 2)) ⊆ closedBall 0 ρ \ {0} :=
    fun j y hy => ⟨hy.1, fun h0 => hy.2 (by rw [Set.mem_singleton_iff.1 h0]; exact mem_ball_self (hr_pos j))⟩
  have hdist : ∀ j : ℕ, 0 < infDist (0 : ℂ) (closedBall (0 : ℂ) ρ \ ball 0 (ρ / ((j : ℝ) + 2))) := by
    intro j
    have hne : (closedBall (0 : ℂ) ρ \ ball 0 (ρ / ((j : ℝ) + 2))).Nonempty :=
      ⟨(ρ : ℂ), mem_closedBall.2 (le_of_eq (by rw [dist_zero_right, hρn])),
        fun h => lt_asymm (hr_lt j) (by rwa [mem_ball, dist_zero_right, hρn] at h)⟩
    refine lt_of_lt_of_le (hr_pos j) ((le_infDist hne).2 fun y hy => ?_)
    have hy2 := hy.2
    rw [mem_ball] at hy2
    rw [dist_comm]
    exact not_lt.1 hy2
  obtain ⟨φ, hφ, hφae⟩ := exists_strictMono_ae_eventually_mem_all (fun j => h33 γ hγ hγ' ρ hρ hρ' Ω S hS ρ 0 0 hρ
    subset_rfl (mem_ball_self hρ) _ (hδ j) _ (hsub j) (hdist j)) hε hε0
  refine ⟨φ, hφ, ?_⟩
  filter_upwards [hφae, h43 γ hγ hγ' ρ hρ hρ' Ω S hS, hS.ae_vertexOf_zero_eq_zero,
    hS.isAreaParametrized, hS.ae_tendsto_cocompact] with ω hconv hbasic hv0 harea hp
  intro t ht
  refine ⟨fun n x hx => ?_, fun x hx hx0 => ?_⟩
  · have hεn := hε (φ n)
    have ha : vertexOf (εs (φ n)) (S.η ω) x ∈ cellVertices (εs (φ n)) (S.η ω) (closedBall 0 ρ) :=
      show (cell (εs (φ n)) (S.η ω) (vertexOf (εs (φ n)) (S.η ω) x) ∩ closedBall 0 ρ).Nonempty from
        ⟨x, Tightness.mem_cell_vertexOf harea.1 hp harea.2.2.1 hεn x, hx⟩
    obtain ⟨h1, h2⟩ := (hbasic t (εs (φ n)) ht hεn).1 _ ha
    have hm : 0 ≤ (S.mε (εs (φ n)))⁻¹ := inv_nonneg.2 (S.mε_nonneg _)
    simp only [rescaledMatedObstacle, rescaledMatedLeastSupersolution, rescale]
    exact ⟨mul_le_mul_of_nonneg_left (max_le_iff.1 h1).2 hm, mul_nonpos_of_nonneg_of_nonpos hm h2⟩
  · have hx' : 0 < ‖x‖ := norm_pos_iff.2 hx0
    have heq : ∀ n, rescaledMatedObstacle S ρ t (εs (φ n)) ω x =
        -t * rescale (S.mε (εs (φ n))) (εs (φ n)) (S.η ω)
          (fun a => (εs (φ n))⁻¹ * greenKernel (S.mult (εs (φ n)) ω)
            (interiorCellVertices (εs (φ n)) (S.η ω) (ball 0 ρ)) (vertexOf (εs (φ n)) (S.η ω) 0) a) x := by
      intro n
      simp only [rescaledMatedObstacle, rescale, matedObstacle, ballInterior, hv0 _ (hε (φ n))]
      ring
    have hlim : Tendsto (fun n => rescale (S.mε (εs (φ n))) (εs (φ n)) (S.η ω)
          (fun a => (εs (φ n))⁻¹ * greenKernel (S.mult (εs (φ n)) ω)
            (interiorCellVertices (εs (φ n)) (S.η ω) (ball 0 ρ)) (vertexOf (εs (φ n)) (S.η ω) 0) a) x)
        atTop (𝓝 (S.c₀ / 6 * greenFunction (ball 0 ρ) 0 x)) := by
      rw [Metric.tendsto_atTop]
      intro δ hδpos
      obtain ⟨j₁, hj₁⟩ := exists_nat_one_div_lt hδpos
      obtain ⟨j₂, hj₂⟩ := exists_nat_gt (ρ / ‖x‖)
      have hj₁' : (j₁ : ℝ) ≤ (max j₁ j₂ : ℕ) := by exact_mod_cast le_max_left j₁ j₂
      have hj₂' : (j₂ : ℝ) ≤ (max j₁ j₂ : ℕ) := by exact_mod_cast le_max_right j₁ j₂
      have hxj : x ∈ closedBall (0 : ℂ) ρ \ ball 0 (ρ / (((max j₁ j₂ : ℕ) : ℝ) + 2)) := by
        refine ⟨hx, fun h => ?_⟩
        rw [mem_ball, dist_zero_right] at h
        have h1 : ρ < (j₂ : ℝ) * ‖x‖ := (div_lt_iff₀ hx').1 hj₂
        have h2 : (j₂ : ℝ) * ‖x‖ ≤ ((max j₁ j₂ : ℕ) : ℝ) * ‖x‖ :=
          mul_le_mul_of_nonneg_right hj₂' (norm_nonneg x)
        have h3 : ρ < ‖x‖ * (((max j₁ j₂ : ℕ) : ℝ) + 2) := by linarith
        exact lt_asymm h ((div_lt_iff₀ (hj2 _)).2 h3)
      have hacc : 1 / (((max j₁ j₂ : ℕ) : ℝ) + 1) ≤ 1 / ((j₁ : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hconv (max j₁ j₂))
      refine ⟨N, fun n hn => ?_⟩
      have hb := hN n hn x hxj
      rw [Real.dist_eq]
      linarith
    refine (tendsto_congr heq).2 ?_
    rw [mul_assoc]
    exact hlim.const_mul (-t)

/-- **Lemma 4.8** (lemma:subsequential-properties, l.1774 of paper/idla_mated_crt-corrected.tex) from Lemmas 3.3, 3.5,
3.7 and 2.13 (Draft) and `OdometerDistributionalLimitCorrectedStep` (Steps 2 and 3 of its proof). Lemma 4.3, the
corrected Lemma 4.4 and the obstacle approximation step (Step 1) are discharged. -/
theorem subsequentialProperties_of_distributionalLimit (𝒮 : SpaceFillingSLEModel)
    (h33 : UniformConvergenceGreenKernelStmt 𝒮) (h35 : DiscreteDirichletProblemStmt 𝒮)
    (h37 : ConvergenceNormalizedExitTimeStmt 𝒮) (h213 : MaximumPrincipleStmt 𝒮)
    (hlap : OdometerDistributionalLimitCorrectedStep 𝒮) : SubsequentialPropertiesStmt 𝒮 :=
  subsequentialProperties_of_corrected 𝒮 h33 h35 h37 h213 (odometerObstacleApproximationStep 𝒮) hlap

end MatedCRT

/-! ## Audit -/

#print axioms MatedCRT.odometerObstacleApproximationStep
#print axioms MatedCRT.subsequentialProperties_of_distributionalLimit
