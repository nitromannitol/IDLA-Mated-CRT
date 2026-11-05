import MatedCRT.Steps.Sec3.ConvergenceNormalizedExitTime
import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.CompactnessFromBounds
import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.DiscreteBoundaryLayer
import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.EquicontinuityLemmas

/-!
# Lemma 3.7, Step 1: random subsequential compactness along summable scales

Step 1 of the proof of Lemma 3.7 (corrected.tex 1417-1430): along a deterministic sequence of scales,
Lemma 2.18 (with polynomially high probability, `q^ε_D ≤ C ε⁻¹ 𝓜(B_{ε^α}(D))`) and Lemma 2.17 (`𝓜(B_ρ') < ∞`
a.s.) bound `ε q^ε_{B_r(z)}` by a random constant; along polynomially summable scales this holds eventually
almost surely (Borel-Cantelli). Lemma 3.1 (corrected, with almost-sure hypotheses:
`DiscretePotentialTightnessAeStep`) then gives a random subsequence along which the rescaled exit times
converge locally uniformly.
-/

namespace MatedCRT

open Set Metric MeasureTheory Filter Topology _root_.HarmonicBalls
open scoped ENNReal

/-- Scales dominated by `2^{-n}` are polynomially summable. -/
theorem isPolySummableScales_of_lt_half_pow {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n ∧ ε n < (1 / 2) ^ n) :
    IsPolySummableScales ε := by
  refine ⟨fun n => (hε n).1, fun p hp => ?_⟩
  have hg : Summable fun n : ℕ => ((1 / 2 : ℝ) ^ p) ^ n := by
    apply summable_geometric_of_lt_one (Real.rpow_nonneg (by norm_num) p)
    exact Real.rpow_lt_one (by norm_num) (by norm_num) hp
  refine Summable.of_nonneg_of_le (fun n => Real.rpow_nonneg (hε n).1.le p) (fun n => ?_) hg
  calc ε n ^ p ≤ ((1 / 2 : ℝ) ^ n) ^ p := Real.rpow_le_rpow (hε n).1.le (hε n).2.le hp.le
    _ = ((1 / 2 : ℝ) ^ p) ^ n := by
      rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (x := 1 / 2) (by norm_num),
        ← Real.rpow_mul (x := 1 / 2) (by norm_num), mul_comm]

/-- **The size bound of Step 1** (corrected.tex 1425-1427, from Lemmas 2.18 and 2.17): along random scales
with values in polynomially summable scales, almost surely `ε |q^ε_D| ≤ C` on `V^ε(D)` for all but finitely
many scales, for a random `C`. -/
theorem ae_eventual_exit_size_of_statements
    {𝒮 : SpaceFillingSLEModel} (h218 : ExitTimeUpperBoundStmt 𝒮) (h217 : BoundedExitTimeRVStmt)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {D : Set ℂ} (hD : D ⊆ ball 0 ρ) (e : ℕ → ℝ) (he : IsPolySummableScales e)
    (E : Ω → ℕ → ℝ) (hErange : ∀ ω n, E ω n ∈ range e)
    (hElim : ∀ ω, Tendsto (E ω) atTop (𝓝 0)) :
    ∀ᵐ ω ∂S.P, ∃ C : ℝ, ∀ᶠ n in atTop,
      ∀ a ∈ cellVertices (E ω n) (S.η ω) D,
        E ω n * |normExitTime (S.mult (E ω n) ω) (interiorCellVertices (E ω n) (S.η ω) D) a| ≤ C := by
  obtain ⟨α, hα, h218α⟩ := h218 γ hγ hγ2
  obtain ⟨C₀, hC₀, h218C⟩ := h218α ρ hρ hρ1
  set ρ' : ℝ := (1 + ρ) / 2 with hρ'
  have hρρ' : ρ < ρ' := by rw [hρ']; linarith
  have hρ'1 : ρ' < 1 := by rw [hρ']; linarith
  have hρ'0 : 0 < ρ' := by linarith
  obtain ⟨q, -, h217q⟩ := h217 γ hγ hγ2
  have hfin := (h217q ρ' hρ'0 hρ'1 Ω S.P S.hC S.hcirc S.μ hS.isConeField).1
  have key : ∀ G : ℝ → Set Ω, PolyHighProb S.P G → ∀ᵐ ω ∂S.P, ∀ᶠ n in atTop, ω ∈ G (E ω n) := by
    intro G hG
    filter_upwards [Tightness.ae_eventually_mem_of_polyHighProb hG he] with ω hω
    exact Tightness.eventually_of_range (Q := fun ε => ω ∈ G ε) he.1 (hErange ω) (hElim ω) hω
  have hεα : Tendsto (fun ε : ℝ => ε ^ α) (𝓝 0) (𝓝 0) := by
    have h3 := (Real.continuousAt_rpow_const 0 α (Or.inr hα.le)).tendsto
    rwa [Real.zero_rpow hα.ne'] at h3
  filter_upwards [key _ (h218C Ω S hS), hfin] with ω hω hfinω
  refine ⟨C₀ * (largestExitTimeRV (S.μ ω) (ball 0 ρ')).toReal, ?_⟩
  have hsmall : ∀ᶠ n in atTop, E ω n ^ α < ρ' - ρ :=
    (hεα.comp (hElim ω)).eventually (gt_mem_nhds (by linarith))
  have hMle : largestExitTimeRV (S.μ ω) (ball 0 ρ') ≤
      ⨆ (D : Set ℂ) (_ : D ⊆ ball 0 ρ'), largestExitTimeRV (S.μ ω) D :=
    le_iSup₂_of_le (ball 0 ρ') Subset.rfl le_rfl
  have hM : largestExitTimeRV (S.μ ω) (ball 0 ρ') < ⊤ := hMle.trans_lt hfinω
  filter_upwards [hω, hsmall] with n hn hsm
  intro a ha
  obtain ⟨-, hn2⟩ := hn
  obtain ⟨j, hj⟩ := hErange ω n
  have hε : 0 < E ω n := hj ▸ he.1 j
  have hsm' : E ω n ^ α < ρ' - ρ := hsm
  have hqa := hn2 D hD a ha
  have hsub : thickening (E ω n ^ α) D ⊆ ball 0 ρ' := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := mem_thickening_iff.1 hx
    have hy' := hD hy
    rw [mem_ball] at hy' ⊢
    linarith [dist_triangle x y 0]
  have hCε : 0 ≤ C₀ * (E ω n)⁻¹ := mul_nonneg hC₀.le (inv_nonneg.2 hε.le)
  have hreal : 0 ≤ C₀ * (E ω n)⁻¹ * (largestExitTimeRV (S.μ ω) (ball 0 ρ')).toReal :=
    mul_nonneg hCε ENNReal.toReal_nonneg
  have hq' : ENNReal.ofReal (normExitTime (S.mult (E ω n) ω)
      (interiorCellVertices (E ω n) (S.η ω) D) a) ≤
      ENNReal.ofReal (C₀ * (E ω n)⁻¹ * (largestExitTimeRV (S.μ ω) (ball 0 ρ')).toReal) := by
    calc
      _ ≤ ENNReal.ofReal (C₀ * (E ω n)⁻¹) *
          largestExitTimeRV (S.μ ω) (thickening (E ω n ^ α) D) := hqa.1.trans hqa.2
      _ ≤ ENNReal.ofReal (C₀ * (E ω n)⁻¹) * largestExitTimeRV (S.μ ω) (ball 0 ρ') :=
        mul_le_mul_right (Tightness.largestExitTimeRV_mono hsub) _
      _ = _ := by rw [ENNReal.ofReal_mul hCε, ENNReal.ofReal_toReal hM.ne]
  have hle := (ENNReal.ofReal_le_ofReal_iff hreal).1 hq'
  rw [abs_of_nonneg (normExitTime_nonneg _ _ _)]
  calc E ω n * normExitTime (S.mult (E ω n) ω) (interiorCellVertices (E ω n) (S.η ω) D) a ≤
        E ω n * (C₀ * (E ω n)⁻¹ * (largestExitTimeRV (S.μ ω) (ball 0 ρ')).toReal) :=
        mul_le_mul_of_nonneg_left hle hε.le
    _ = C₀ * (largestExitTimeRV (S.μ ω) (ball 0 ρ')).toReal * (E ω n * (E ω n)⁻¹) := by ring
    _ = C₀ * (largestExitTimeRV (S.μ ω) (ball 0 ρ')).toReal := by
        rw [mul_inv_cancel₀ hε.ne', mul_one]

/-- Lemma 3.1 (corrected, almost-sure hypotheses) applied to the normalized exit times along selected
scales: an eventual pathwise size bound yields random subsequential local uniform convergence. -/
theorem exit_compactness_of_ae_tightness
    (𝒮 : SpaceFillingSLEModel) (hAe : DiscretePotentialTightnessAeStep 𝒮)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    (D : Set ℂ) (hD : D ⊆ ball 0 ρ) (hDo : IsOpen D) (hconn : IsConnected D)
    (K : Set ℂ) (hK : IsCompact K) (hKD : closure K ⊆ D)
    (ε : ℕ → ℝ) (he : IsPolySummableScales ε) (I : Ω → ℕ → ℕ)
    (hI : ∀ n, Measurable[S.envSigma] fun ω => I ω n)
    (hElim : ∀ ω, Tendsto (fun n => ε (I ω n)) atTop (𝓝 0))
    (hsize : ∀ᵐ ω ∂S.P, ∃ C : ℝ, ∀ᶠ n in atTop,
      ∀ a ∈ cellVertices (ε (I ω n)) (S.η ω) D,
        ε (I ω n) * |normExitTime (S.mult (ε (I ω n)) ω)
          (interiorCellVertices (ε (I ω n)) (S.η ω) D) a| ≤ C) :
    ∀ᵐ ω ∂S.P, ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ u : ℂ → ℝ,
      ContinuousOn u K ∧ TendstoUniformlyOn
        (fun k => rescale (S.mε (ε (I ω (φ k)))) (ε (I ω (φ k))) (S.η ω)
          (normExitTime (S.mult (ε (I ω (φ k))) ω)
            (interiorCellVertices (ε (I ω (φ k))) (S.η ω) D))) u atTop K := by
  have hEpos : ∀ ω n, 0 < ε (I ω n) := fun ω n => he.1 _
  have hDb : Bornology.IsBounded D := isBounded_ball.subset hD
  obtain ⟨C, hCm, hC, hCa⟩ := hS.exists_measurable_exit_time_bound_of_eventual
    ε I hI hEpos D (Or.inl hDo) hDb hsize
  have hbounds := hS.ae_exit_bounds_of_eventual_size hγ hγ2 D hDb
    (fun ω n => ε (I ω n)) hEpos C hC
    (by filter_upwards [hCa] with ω hω; exact Eventually.of_forall (fun n a _ => hω n a))
  obtain ⟨u, hum, hue⟩ := hS.exists_envSigma_measurable_selected_normExitTime ε D (Or.inl hDo) I hI
  have hEm : ∀ n, Measurable[S.envSigma] fun ω => ε (I ω n) := fun n =>
    (measurable_of_countable ε).comp (hI n)
  obtain ⟨Φ, hΦm, hΦ⟩ := hAe γ hγ hγ2 ρ hρ hρ1 Ω S hS D hD hDo hconn ε he
    (fun ω n => ε (I ω n)) u C hEm (fun ω n => ⟨I ω n, rfl⟩) hElim hum hCm
    (fun ω => zero_lt_one.trans_le (hC ω)) (by
      filter_upwards [hbounds, hue] with ω hb hu
      filter_upwards [hb] with n hn
      have hfun : u ω n = normExitTime (S.mult (ε (I ω n)) ω)
          (interiorCellVertices (ε (I ω n)) (S.η ω) D) := funext (hu n)
      rw [hfun]
      exact hn)
  filter_upwards [hΦ, hue] with ω hω hu
  obtain ⟨hmono, ubar, hcont, hconv⟩ := hω
  refine ⟨Φ ω, hmono, ubar, hcont.mono (subset_closure.trans hKD), ?_⟩
  have hfun : ∀ n, u ω n = normExitTime (S.mult (ε (I ω n)) ω)
      (interiorCellVertices (ε (I ω n)) (S.η ω) D) := fun n => funext (hu n)
  apply (hconv K hK hKD).congr
  exact Eventually.of_forall fun k x _ => by simp only [hfun]

/-- **Step 1 of Lemma 3.7** along `2^{-n}`-dominated scales: for every strictly increasing deterministic
reindexing `ψ` and every `σ(h, η)`-measurable random reindexing `I`, almost surely some subsequence of the
rescaled exit times converges uniformly on `cl(B_{r'}(z))`, `r' < r`. -/
theorem exit_compactness_dyadic_of_statements
    (𝒮 : SpaceFillingSLEModel) (h218 : ExitTimeUpperBoundStmt 𝒮) (h217 : BoundedExitTimeRVStmt)
    (hAe : DiscretePotentialTightnessAeStep 𝒮)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {r r' : ℝ} {z : ℂ} (hr : 0 < r) (hr' : r' < r) (hball : ball z r ⊆ ball 0 ρ) :
    ∀ ε : ℕ → ℝ, (∀ n, 0 < ε n ∧ ε n < (1 / 2) ^ n) →
      ∀ ψ : ℕ → ℕ, StrictMono ψ → ∀ I : Ω → ℕ → ℕ,
      (∀ n, Measurable[S.envSigma] fun ω => I ω n) → (∀ ω n, n ≤ I ω n) →
      ∀ᵐ ω ∂S.P, ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ u : ℂ → ℝ,
        ContinuousOn u (closedBall z r') ∧ TendstoUniformlyOn
          (fun k => rescale (S.mε (ε (ψ (I ω (φ k))))) (ε (ψ (I ω (φ k)))) (S.η ω)
            (normExitTime (S.mult (ε (ψ (I ω (φ k)))) ω)
              (interiorCellVertices (ε (ψ (I ω (φ k)))) (S.η ω) (ball z r))))
          u atTop (closedBall z r') := by
  intro ε hε ψ hψ I hI hIge
  have he : IsPolySummableScales ε := isPolySummableScales_of_lt_half_pow hε
  have hI' : ∀ n, Measurable[S.envSigma] fun ω => ψ (I ω n) := fun n =>
    measurable_from_nat.comp (hI n)
  have hlim : ∀ ω, Tendsto (fun n => ε (ψ (I ω n))) atTop (𝓝 0) := fun ω =>
    he.tendsto_zero.comp (hψ.tendsto_atTop.comp (tendsto_atTop_mono (hIge ω) tendsto_id))
  have hKD : closure (closedBall z r') ⊆ ball z r := by
    rw [isClosed_closedBall.closure_eq]
    exact closedBall_subset_ball hr'
  exact exit_compactness_of_ae_tightness 𝒮 hAe hγ hγ2 hρ hρ1 S hS (ball z r) hball isOpen_ball
    ((convex_ball z r).isConnected (nonempty_ball.2 hr)) (closedBall z r')
    (isCompact_closedBall _ _) hKD ε he (fun ω n => ψ (I ω n)) hI' hlim
    (ae_eventual_exit_size_of_statements h218 h217 hγ hγ2 hρ hρ1 S hS hball ε he
      (fun ω n => ε (ψ (I ω n))) (fun ω n => ⟨ψ (I ω n), rfl⟩) hlim)

end MatedCRT
