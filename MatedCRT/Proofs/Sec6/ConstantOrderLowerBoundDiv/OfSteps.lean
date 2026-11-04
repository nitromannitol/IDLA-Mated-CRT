import MatedCRT.Proofs.Sec6.ConstantOrderLowerBoundDiv.Vertex
import MatedCRT.Proofs.Sec6.ConstantOrderLowerBoundDiv.Reduction
import MatedCRT.Proofs.Sec6.ConstantOrderLowerBoundDiv.Threshold
import MatedCRT.Proofs.Sec6.ConstantOrderLowerBound.Model
import MatedCRT.Proofs.Sec6.ConstantOrderLowerBound.Walk
import MatedCRT.Steps.Infra.MatingOfTrees
import MatedCRT.Proofs.Infra.Setting
import MatedCRT.Proofs.Measurability.GoodScale

/-!
# Lemma 6.8, route (b) of E-A10: `constantOrderLowerBoundDiv_of_steps` (proof of lines 2493-2621)

* `div_core`: deterministic given the map `(m, η, μ)` and the conclusions at `ε` of the inputs. For
  `r ∈ [10 ε^{ω₀}, ρ/16 ∧ s₀/8 ∧ 2^{-N}]`: Step 1 with the scale fix of E-A10 — the dyadic `δ ∈ (r²/128, r²/64]`, the
  point `p` of the cell of `a` on `∂(Θ̄ + B_{r/2})`, the grid point `z ∈ (δ/100) ℤ²` within `δ/100` of `p`, the good
  radius `R = 𝐫_z ∈ [δ, √δ]` of Lemma 6.4 — and the strong Markov property at the first visit to
  `V^ε(∂B_{(4/3)R}(z))` (`prob_stay_le_of_crossing`), then Steps 2-4 at that vertex (`stay_le_at_frontier_vertex`).
* `constantOrderLowerBoundDiv_of_aeSteps`: the Borel-Cantelli step of line 2505 (`exists_measurable_threshold`, with
  the almost-sure `GoodScaleEventMeasurableAEStep` for the `σ(h)`-measurability of `𝛅`: the `σ(h)`-measurable
  approximations are contained in the good-scale events outside one null set), the events of Lemmas 2.8, 2.9, 2.16,
  2.18 at `ε`,
  the finiteness of `V^ε(B_ρ)` and the exit of the walk (worker c5's `cellVerticesBallFiniteStep`, `walkExitsStep`),
  and the deterministic smallness of `ε` (line 2506: "`ε < 𝛑`").
Constants: `𝐜₀ = e^{-3C₂/2}/12` (eq:choice-of-constant-annulus, `C₂` of Lemma 2.16), `s₁ = (𝐜₀/256)^{β⁻}/4`,
`s₂ = 1/2 ∧ (2592 C₁² C²)⁻¹` (`C₁` of Lemma 2.18, `C` of Lemma 6.4), `ω₀ = (κ ∧ ω ∧ α₁ ∧ α₉)/(4β⁻)` with
`κ = 1/(2+γ)²` (Lemma 2.8).
-/

namespace MatedCRT

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace ConstantOrderDiv

set_option maxHeartbeats 400000 in
/-- **Lemma 6.8 given the map** (lines 2509-2620). -/
theorem div_core (hW : SrwHitDecompositionStep) {m : ℤ → ℤ → ℕ} {ε : ℝ} {η : ℝ → ℂ} {μ : Measure ℂ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hη : Continuous η)
    {ρ βm βp c₀ CE C₁ C₂ α₁ α₉ β₉ ω₂ κ ω₀ s₀ s₁ s₂ lam : ℝ} {N : ℕ}
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hs₀ : 0 < s₀) (hC₂ : 0 < C₂) (hc₀ : c₀ = Real.exp (-(3 / 2) * C₂) / 12)
    (hCE : 0 < CE) (hC₁ : 0 < C₁) (hβm : 1 ≤ βm) (hβ₉ : 0 < β₉) (hs₁ : s₁ = 1 / 4 * (c₀ / 256) ^ βm)
    (hs₂ : s₂ ≤ 1 / (2592 * C₁ ^ 2 * CE ^ 2))
    (hlam : 0 < lam) (hlamr : ∀ r : ℝ, 10 * ε ^ ω₀ ≤ r → lam ≤ r ^ 2 / 128)
    (hS1 : ε ^ κ ≤ c₀ * lam / 100) (hS2 : ε ^ ω₂ ≤ lam / 4) (hS3 : ε ^ α₁ ≤ lam / 100)
    (hS4 : ε ^ α₁ ≤ (c₀ * lam / 2) ^ βm) (hS5 : 4 * ε ^ α₉ ≤ (c₀ * lam / 2) ^ βm)
    (hS6 : Real.exp (3 / 2 * C₂) ≤ ε⁻¹)
    (hadj : ∀ a : ℤ, ∀ᵐ x ∂srwLaw m a,
      ∀ n, x (n + 1) = x n ∨ (cell ε η (x n) ∩ cell ε η (x (n + 1))).Nonempty)
    (hexit : ∀ O : Set ℂ, IsOpen O → ball 0 s₀ ⊆ O → O ⊆ ball 0 ρ → ∀ a : ℤ,
      srwLaw m a {x | vExitTime (interiorCellVertices ε η O) x = ⊤} = 0)
    (hdiam : ∀ k, (cell ε η k ∩ ball 0 ρ).Nonempty → diam (cell ε η k) ≤ ε ^ κ)
    (hfin : (cellVertices ε η (ball 0 ρ)).Finite)
    (h216 : GreenLowerAt m ε η ρ ω₂ C₂) (hLL : LogLossAt m ε η μ ρ α₁ C₁) (h29 : CountingAt ε η μ ρ α₉ β₉)
    (hgoodN : ∀ n, N ≤ n →
      GoodAnnulusCover μ ρ c₀ CE ((1 / 2 : ℝ) ^ n) ∧ VolumeGrowthAt μ βp βm ((1 / 2 : ℝ) ^ n)) :
    ∀ r : ℝ, 10 * ε ^ ω₀ ≤ r → r ≤ min (ρ / 16) (min (s₀ / 8) ((1 / 2 : ℝ) ^ N)) → ∀ Θ : Set ℤ,
      closure (fillCells ε η Θ) ⊆ ball 0 (ρ / 2) → ball 0 s₀ ⊆ fillCells ε η Θ →
      ∀ A ⊆ cellVertices ε η (thickening r (fillCells ε η Θ)) \ Θ,
        (∀ z : ℂ, ((A ∩ cellVertices ε η (ball z r)).ncard : ℝ) < s₁ * r ^ (2 * βm) / ε) →
        ∀ a ∈ cellVertices ε η (frontier (thickening (r / 2) (fillCells ε η Θ))),
          srwLaw m a {x | ∀ n : ℕ,
            (n : ℕ∞) < vExitTime (cellVertices ε η (thickening r (fillCells ε η Θ)) \ Θ) x →
            x n ∈ A} ≤ ENNReal.ofReal (1 - s₂ / (1 + |Real.log r|) ^ 2) := by
  intro r hr1 hr2 Θ hΘ1 hΘ2 A _hA hAcard a ha
  have hεω : 0 < 10 * ε ^ ω₀ := by positivity
  have hrpos : 0 < r := lt_of_lt_of_le hεω hr1
  have hrρ : r ≤ ρ / 16 := hr2.trans (min_le_left _ _)
  have hrs₀ : r ≤ s₀ / 8 := hr2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrN : r ≤ (1 / 2 : ℝ) ^ N := hr2.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hr1' : r ≤ 1 := by linarith
  have hlr : lam ≤ r ^ 2 / 128 := hlamr r hr1
  have hrsq : r ^ 2 ≤ r := pow_le_of_le_one hrpos.le hr1' (by norm_num)
  have hc₀pos : 0 < c₀ := by rw [hc₀]; positivity
  have hc₀1 : c₀ ≤ 1 / 12 := by
    have : Real.exp (-(3 / 2) * C₂) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    rw [hc₀]
    linarith
  -- the dyadic scale `δ ∈ (r²/128, r²/64]`
  obtain ⟨n, hn1, hn2⟩ := exists_half_pow_mem (by positivity : 0 < r ^ 2 / 64) (by linarith)
  have hNn : N ≤ n := ge_of_half_pow_lt (by linarith)
  have hδpos : (0 : ℝ) < (1 / 2) ^ n := by positivity
  have hsqrtδ : Real.sqrt ((1 / 2 : ℝ) ^ n) ≤ r / 8 := by
    calc Real.sqrt ((1 / 2 : ℝ) ^ n) ≤ Real.sqrt ((r / 8) ^ 2) := Real.sqrt_le_sqrt (by linarith)
      _ = r / 8 := Real.sqrt_sq (by positivity)
  have hsqrt0 : 0 ≤ Real.sqrt ((1 / 2 : ℝ) ^ n) := Real.sqrt_nonneg _
  -- the point `p` of the cell of `a` on `∂(Θ̄ + B_{r/2})`
  obtain ⟨p, hpa, hpF⟩ := ha
  have hp : infDist p (fillCells ε η Θ) = r / 2 := infDist_eq_of_mem_frontier_thickening (by positivity) hpF
  have hΘne : (fillCells ε η Θ).Nonempty := ⟨0, hΘ2 (mem_ball_self hs₀)⟩
  have hps₀ : s₀ ≤ ‖p‖ := by
    by_contra h
    push Not at h
    exact notMem_closure_of_near hp (by rw [sub_self, norm_zero]; positivity)
      (subset_closure (hΘ2 (mem_ball_zero_iff.2 h)))
  have hpρ : ‖p‖ < ρ / 2 + r := by
    obtain ⟨q, hq, hpq⟩ := (infDist_lt_iff hΘne).1 (by rw [hp]; linarith : infDist p (fillCells ε η Θ) < r)
    have hq' := mem_ball_zero_iff.1 (hΘ1 (subset_closure hq))
    rw [dist_eq_norm] at hpq
    have := norm_le_add_norm_sub p q
    linarith
  -- the grid point `z`
  obtain ⟨m', n', hpz⟩ := exists_grid_near hδpos p
  have hzp : ‖((((1 / 2 : ℝ) ^ n / 100 : ℝ) : ℂ) * (m' + n' * Complex.I)) - p‖ ≤ (1 / 2 : ℝ) ^ n / 100 := by
    rw [norm_sub_rev]
    exact hpz
  set z : ℂ := (((1 / 2 : ℝ) ^ n / 100 : ℝ) : ℂ) * (m' + n' * Complex.I) with hzdef
  have hδr : (1 / 2 : ℝ) ^ n / 100 ≤ r / 6400 := by linarith
  have hz1 := norm_le_add_norm_sub z p
  have hz2 := norm_le_add_norm_sub p z
  rw [norm_sub_rev p z] at hz2
  have hzmem : z ∈ ball 0 (ρ - 3 * Real.sqrt ((1 / 2 : ℝ) ^ n)) \ ball 0 (10 * Real.sqrt ((1 / 2 : ℝ) ^ n)) := by
    refine ⟨mem_ball_zero_iff.2 (by linarith), fun h => ?_⟩
    have := mem_ball_zero_iff.1 h
    linarith
  -- the good radius `R = 𝐫_z` of Lemma 6.4
  obtain ⟨R, hδR, hRδ, -, hgoodR⟩ := (hgoodN n hNn).1 z hzmem ⟨m', n', rfl⟩
  have hRpos : 0 < R := lt_of_lt_of_le hδpos hδR
  have hRr : 8 * R ≤ r := by linarith
  have hr2R : r ^ 2 / 128 ≤ R := by linarith
  have hlamR : lam ≤ R := by linarith
  -- the safe region around `z`
  have hnearp : ∀ w : ℂ, ‖w - z‖ < 2 * R → ‖w - p‖ < 3 * r / 8 := by
    intro w hw
    have := norm_sub_le_norm_sub_add_norm_sub w z p
    linarith
  have hnear : ∀ w : ℂ, ‖w - z‖ < 2 * R →
      w ∈ thickening r (fillCells ε η Θ) ∧ w ∉ closure (fillCells ε η Θ) := fun w hw =>
    ⟨mem_thickening_of_near hΘne hp (hnearp w hw), notMem_closure_of_near hp (hnearp w hw)⟩
  have hzρ : ‖z‖ + 2 * r ≤ 7 * ρ / 8 := by linarith
  have hthickρ : ∀ t, t ≤ 2 * r → thickening t (fillCells ε η Θ) ⊆ ball 0 ρ := by
    intro t ht w hw
    obtain ⟨q, hq, hwq⟩ := mem_thickening_iff.1 hw
    have hq' := mem_ball_zero_iff.1 (hΘ1 (subset_closure hq))
    rw [dist_eq_norm] at hwq
    have := norm_le_add_norm_sub w q
    rw [mem_ball_zero_iff]
    linarith
  have hclO : ∀ w ∈ closure (ball z (4 * R / 3)), ‖w - z‖ < 2 * R := by
    intro w hw
    rw [closure_ball z (by positivity : 4 * R / 3 ≠ 0), mem_closedBall, dist_eq_norm] at hw
    linarith
  have hdr : ε ^ κ < r / 8 := by
    have := mul_le_mul_of_nonneg_right hc₀1 hlam.le
    linarith
  -- Step 1: the strong Markov property at the first visit to `V^ε(∂B_{(4/3)R}(z))`
  refine prob_stay_le_of_crossing hW hη (I := interiorCellVertices ε η (thickening r (fillCells ε η Θ)))
    (O := ball z (4 * R / 3)) isOpen_ball (hadj a)
    (hexit _ isOpen_thickening (hΘ2.trans (self_subset_thickening hrpos _)) (hthickρ r (by linarith)) a)
    ?_ ?_ ⟨p, hpa, ?_⟩ ?_
  · intro k hk
    rw [eq_empty_iff_forall_notMem]
    rintro w ⟨hwk, hwcl⟩
    have hwz := hclO w hwcl
    have hwT := (hnear w hwz).1
    have hkF : k ∈ cellVertices ε η (frontier (thickening r (fillCells ε η Θ))) := by
      by_contra h
      exact hk ⟨⟨w, hwk, hwT⟩, h⟩
    obtain ⟨w₁, hw₁k, hw₁F⟩ := hkF
    have hw₁ρ : w₁ ∈ ball (0 : ℂ) ρ := by
      have hinf := infDist_eq_of_mem_frontier_thickening hrpos.le hw₁F
      obtain ⟨q, hq, hq'⟩ :=
        (infDist_lt_iff hΘne).1 (by rw [hinf]; linarith : infDist w₁ (fillCells ε η Θ) < 2 * r)
      exact hthickρ (2 * r) le_rfl (mem_thickening_iff.2 ⟨q, hq, hq'⟩)
    have h1 := dist_le_of_mem_cell hη (hdiam k ⟨w₁, hw₁k, hw₁ρ⟩) hw₁k hwk
    have h2 := lt_dist_of_mem_frontier hrpos.le hp (hnearp w hwz) hw₁F
    linarith
  · intro k hk
    rw [eq_empty_iff_forall_notMem]
    rintro w ⟨hwk, hwcl⟩
    obtain ⟨hwT, hwc⟩ := hnear w (hclO w hwcl)
    exact hk ⟨⟨w, hwk, hwT⟩, fun hkΘ => hwc (subset_closure (mem_biUnion hkΘ hwk))⟩
  · rw [mem_ball, dist_eq_norm, norm_sub_rev]
    linarith
  · rintro b ⟨hb, -⟩
    exact stay_le_at_frontier_vertex hε hε1 hη hρ hρ1 hC₂ hc₀ hCE hC₁ hβm hβ₉ hs₁ hs₂ hrpos hr1' hrN
      hRpos hRr hr2R hlamR hlam hS1 hS2 hS3 hS4 hS5 hS6 hzρ hnear hdiam hfin h216 hLL h29
      (fun n hn => (hgoodN n hn).2) hgoodR hAcard hb

/-- `ε^a ≤ K ε^b` for small `ε > 0`, if `b < a`. -/
theorem eventually_rpow_le {a b K : ℝ} (hK : 0 < K) (hab : b < a) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ^ a ≤ K * ε ^ b := by
  have h := (tendsto_rpow_nhdsGT_zero (sub_pos.2 hab)).eventually (gt_mem_nhds hK)
  filter_upwards [h, self_mem_nhdsWithin] with ε hε hε0
  have hε0' : (0 : ℝ) < ε := hε0
  rw [show a = (a - b) + b by ring, Real.rpow_add hε0']
  exact mul_le_mul_of_nonneg_right hε.le (Real.rpow_nonneg hε0'.le _)

/-- `(c (K ε^a)/2)^β = (c K/2)^β ε^{aβ}`. -/
theorem rpow_lam {c K a β ε : ℝ} (hc : 0 ≤ c) (hK : 0 ≤ K) (hε : 0 < ε) :
    (c * (K * ε ^ a) / 2) ^ β = (c * K / 2) ^ β * ε ^ (a * β) := by
  rw [show c * (K * ε ^ a) / 2 = c * K / 2 * ε ^ a by ring, Real.mul_rpow (by positivity) (by positivity),
    ← Real.rpow_mul hε.le]

end ConstantOrderDiv

/-- A `σ(h)`-measurable inner approximation of `E` is an almost-sure one. -/
theorem MatedCRTEnv.isFieldInnerMeasurableAE_of_isFieldInnerMeasurable {Ω : Type} [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω) {E : Set Ω} (h : IsFieldInnerMeasurable S E) : IsFieldInnerMeasurableAE S E := by
  obtain ⟨F, hF, hFE, hP⟩ := h
  exact ⟨F, hF, measure_mono_null (fun ω hω => absurd (hFE hω.1) hω.2) measure_empty, hP⟩

/-- `GoodScaleEventMeasurableStep` implies its almost-sure form `GoodScaleEventMeasurableAEStep`. -/
theorem goodScaleEventMeasurableAEStep_of_step {𝒮 : SpaceFillingSLEModel} (h : GoodScaleEventMeasurableStep 𝒮) :
    GoodScaleEventMeasurableAEStep 𝒮 := fun γ hγ hγ2 Ω _ S hS ρ c₀ C βp βm δ =>
  ⟨S.isFieldInnerMeasurableAE_of_isFieldInnerMeasurable (h γ hγ hγ2 Ω S hS ρ c₀ C βp βm δ).1,
    S.isFieldInnerMeasurableAE_of_isFieldInnerMeasurable (h γ hγ hγ2 Ω S hS ρ c₀ C βp βm δ).2⟩

open ConstantOrderDiv in
set_option maxHeartbeats 400000 in
/-- **Lemma 6.8, route (b) of E-A10** (lemma:constant-order-lower-bound-div, line 2455), from Lemmas 2.7, 2.8, 2.9,
2.16, 2.18, 2.19, 6.4, the almost-sure `σ(h)`-measurability of the good-scale events (line 2505) and the intersection
of adjacent cells. -/
theorem constantOrderLowerBoundDiv_of_aeSteps (𝒮 : SpaceFillingSLEModel)
    (h216 : GreenKernelLowerBoundStmt 𝒮) (h27 : VolumeGrowthStmt) (h28 : CellSizeEstimateStmt 𝒮)
    (h29 : CountingMeasureConvergenceStmt 𝒮) (h64 : GoodAnnulusPrevalenceStmt)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (h219 : ExpectedExitTimeExplicitBoundStmt 𝒮)
    (hmeas : GoodScaleEventMeasurableAEStep 𝒮) (hcell : AdjacentCellsMeetAeStep 𝒮) :
    ConstantOrderLowerBoundDivLogStmt 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 βm hβm
  obtain ⟨ω₂, hω₂, h216a⟩ := h216 γ hγ hγ2
  obtain ⟨C₂, hC₂, h216b⟩ := h216a ρ hρ hρ1
  obtain ⟨α₁, hα₁, hLLa⟩ := exitTimeLogLossStep_of_exitTimeUpperBound h218 γ hγ hγ2
  obtain ⟨C₁, hC₁, hLLb⟩ := hLLa ρ hρ hρ1
  obtain ⟨α₉, β₉, hα₉, hβ₉, h29a⟩ := h29 γ hγ hγ2
  have hγ4 : 4 < (2 + γ) ^ 2 := by nlinarith
  have hβm1 : 1 ≤ βm := by linarith
  set κ : ℝ := 1 / (2 + γ) ^ 2 with hκdef
  have hκ : 0 < κ := by positivity
  have hκ1 : κ < 1 := by rw [hκdef, div_lt_one (by positivity)]; linarith
  have hκe : 2 / (2 + γ) ^ 2 - κ = κ := by rw [hκdef]; ring
  set c₀ : ℝ := Real.exp (-(3 / 2) * C₂) / 12 with hc₀def
  have hc₀pos : 0 < c₀ := by positivity
  have hc₀1 : c₀ ≤ 1 / 12 := by
    have : Real.exp (-(3 / 2) * C₂) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    linarith
  obtain ⟨CE, hCE, h64a⟩ := h64 γ hγ hγ2 ρ hρ hρ1 c₀ hc₀pos (by linarith)
  have h2γ : 0 < 2 - γ := by linarith
  have hβp : 0 < (2 - γ) ^ 2 / 4 := by positivity
  have hβp2 : (2 - γ) ^ 2 / 4 < (2 - γ) ^ 2 / 2 := by
    have : 0 < (2 - γ) ^ 2 := by positivity
    linarith
  set μ₀ : ℝ := min (min κ ω₂) (min α₁ α₉) with hμ₀def
  have hμ₀ : 0 < μ₀ := lt_min (lt_min hκ hω₂) (lt_min hα₁ hα₉)
  have hμκ : μ₀ ≤ κ := (min_le_left _ _).trans (min_le_left _ _)
  have hμω : μ₀ ≤ ω₂ := (min_le_left _ _).trans (min_le_right _ _)
  have hμα₁ : μ₀ ≤ α₁ := (min_le_right _ _).trans (min_le_left _ _)
  have hμα₉ : μ₀ ≤ α₉ := (min_le_right _ _).trans (min_le_right _ _)
  set ω₀ : ℝ := μ₀ / (4 * βm) with hω₀def
  have hω₀ : 0 < ω₀ := by positivity
  have h2ωβ : 2 * ω₀ * βm = μ₀ / 2 := by
    rw [hω₀def]
    field_simp
    ring
  have h2ω : 2 * ω₀ ≤ μ₀ / 2 := by
    have := mul_le_mul_of_nonneg_left hβm1 (by positivity : (0 : ℝ) ≤ 2 * ω₀)
    linarith
  refine ⟨ω₀, hω₀, fun s₀ hs₀ hs₀1 => ?_⟩
  set s₁ : ℝ := 1 / 4 * (c₀ / 256) ^ βm with hs₁def
  have hs₁pos : 0 < s₁ := by positivity
  have hs₁1 : s₁ < 1 := by
    have : (c₀ / 256) ^ βm ≤ 1 := Real.rpow_le_one (by positivity) (by linarith) (by linarith)
    linarith
  set s₂ : ℝ := min (1 / 2) (1 / (2592 * C₁ ^ 2 * CE ^ 2)) with hs₂def
  have hs₂pos : 0 < s₂ := lt_min (by norm_num) (by positivity)
  have hs₂1 : s₂ < 1 := (min_le_left _ _).trans_lt (by norm_num)
  refine ⟨s₁, s₂, hs₁pos, hs₁1, hs₂pos, hs₂1, fun Ω _ S hS => ?_⟩
  have hP : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  have hcone := hS.isConeField
  -- the Borel-Cantelli step of line 2505
  have hcov := h64a Ω S.P S.hC S.hcirc S.μ hcone
  have hvolp := h27 γ hγ hγ2 _ βm hβp hβp2 hβm Ω S.P S.hC S.hcirc S.μ hcone
  have hFc' : ∀ n : ℕ, ∃ F : Set Ω, MeasurableSet[S.fieldSigma] F ∧
      S.P (F \ {ω | GoodAnnulusCover (S.μ ω) ρ c₀ CE ((1 / 2 : ℝ) ^ n)}) = 0 ∧
      S.P Fᶜ ≤ S.P {ω | GoodAnnulusCover (S.μ ω) ρ c₀ CE ((1 / 2 : ℝ) ^ n)}ᶜ := fun n =>
    (hmeas γ hγ hγ2 Ω S hS ρ c₀ CE ((2 - γ) ^ 2 / 4) βm ((1 / 2 : ℝ) ^ n)).1
  have hFv' : ∀ n : ℕ, ∃ F : Set Ω, MeasurableSet[S.fieldSigma] F ∧
      S.P (F \ {ω | VolumeGrowthAt (S.μ ω) ((2 - γ) ^ 2 / 4) βm ((1 / 2 : ℝ) ^ n)}) = 0 ∧
      S.P Fᶜ ≤ S.P {ω | VolumeGrowthAt (S.μ ω) ((2 - γ) ^ 2 / 4) βm ((1 / 2 : ℝ) ^ n)}ᶜ := fun n =>
    (hmeas γ hγ hγ2 Ω S hS ρ c₀ CE ((2 - γ) ^ 2 / 4) βm ((1 / 2 : ℝ) ^ n)).2
  choose Fc hFc using hFc'
  choose Fv hFv using hFv'
  -- almost surely, every `Fc n` (resp. `Fv n`) is contained in the event it approximates
  have hFE : ∀ᵐ ω ∂S.P, ∀ n : ℕ, (ω ∈ Fc n → GoodAnnulusCover (S.μ ω) ρ c₀ CE ((1 / 2 : ℝ) ^ n)) ∧
      (ω ∈ Fv n → VolumeGrowthAt (S.μ ω) ((2 - γ) ^ 2 / 4) βm ((1 / 2 : ℝ) ^ n)) := by
    refine ae_all_iff.2 fun n => ?_
    have hc : ∀ᵐ ω ∂S.P, ω ∈ Fc n → GoodAnnulusCover (S.μ ω) ρ c₀ CE ((1 / 2 : ℝ) ^ n) :=
      ae_iff.2 (measure_mono_null (fun ω hω => not_imp.1 hω) (hFc n).2.1)
    have hv : ∀ᵐ ω ∂S.P, ω ∈ Fv n → VolumeGrowthAt (S.μ ω) ((2 - γ) ^ 2 / 4) βm ((1 / 2 : ℝ) ^ n) :=
      ae_iff.2 (measure_mono_null (fun ω hω => not_imp.1 hω) (hFv n).2.1)
    exact hc.and hv
  have hsum : ∑' n, S.P (Fc n ∩ Fv n)ᶜ ≠ ⊤ := by
    refine ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨tsum_dyadic_ne_top hcov, tsum_dyadic_ne_top hvolp⟩) ?_
    rw [← ENNReal.tsum_add]
    refine ENNReal.tsum_le_tsum fun n => ?_
    rw [compl_inter]
    exact (measure_union_le _ _).trans (add_le_add (hFc n).2.2 (hFv n).2.2)
  obtain ⟨Nf, hNm, hNae⟩ := exists_measurable_threshold S.P (F := fun n => Fc n ∩ Fv n)
    (fun n => (hFc n).1.inter (hFv n).1) hsum
  refine ⟨fun ω => min (ρ / 16) (min (s₀ / 8) ((1 / 2 : ℝ) ^ Nf ω)), ?_, fun ω => ?_, ?_⟩
  · exact measurable_const.min (measurable_const.min
      ((measurable_from_nat (f := fun n : ℕ => (1 / 2 : ℝ) ^ n)).comp hNm))
  · exact lt_min (by positivity) (lt_min (by positivity) (by positivity))
  -- the events at `ε`
  have hGη : ∀ᵐ ω ∂S.P, ω ∈ {ω | Continuous (S.η ω) ∧ ∀ ε : ℝ, 0 < ε → ∀ j k : ℤ, S.mult ε ω j k ≠ 0 →
      (cell ε (S.η ω) j ∩ cell ε (S.η ω) k).Nonempty} :=
    (hS.isAreaParametrized.and (hcell γ hγ hγ2 Ω S hS)).mono fun ω hω => ⟨hω.1.1, hω.2⟩
  have hNE : ∀ᵐ ω ∂S.P, ω ∈ {ω | ∀ n, Nf ω ≤ n → GoodAnnulusCover (S.μ ω) ρ c₀ CE ((1 / 2 : ℝ) ^ n) ∧
      VolumeGrowthAt (S.μ ω) ((2 - γ) ^ 2 / 4) βm ((1 / 2 : ℝ) ^ n)} := by
    filter_upwards [hNae, hFE] with ω h1 h2 n hn
    exact ⟨(h2 n).1 (h1 n hn).1, (h2 n).2 (h1 n hn).2⟩
  have hall := (((((((probTendsToOne_of_ae hNE).inter
    (probTendsToOne_of_ae hGη)).inter (HarmonicBalls.PolyHighProb.probTendsToOne (h216b Ω S hS))).inter
    (HarmonicBalls.PolyHighProb.probTendsToOne (hLLb Ω S hS))).inter
    (HarmonicBalls.PolyHighProb.probTendsToOne (h29a ρ hρ hρ1 Ω S hS))).inter
    (HarmonicBalls.PolyHighProb.probTendsToOne (h28 γ hγ hγ2 κ ρ hκ hκ1 hρ hρ1 Ω S hS))).inter
    (cellVerticesBallFiniteStep 𝒮 h27 h28 γ hγ hγ2 ρ hρ hρ1 Ω S hS)).inter
    (walkExitsStep 𝒮 h27 h219 γ hγ hγ2 ρ s₀ hρ hρ1 hs₀ Ω S hS)
  refine hall.mono_ev ?_
  -- the deterministic smallness of `ε` (line 2506)
  have hK4 : 0 < (c₀ * (100 / 128) / 2) ^ βm := by positivity
  have e1 := eventually_rpow_le (by positivity : (0 : ℝ) < c₀ / 128) (by linarith : 2 * ω₀ < κ)
  have e2 := eventually_rpow_le (by norm_num : (0 : ℝ) < 100 / 512) (by linarith : 2 * ω₀ < ω₂)
  have e3 := eventually_rpow_le (by norm_num : (0 : ℝ) < 1 / 128) (by linarith : 2 * ω₀ < α₁)
  have e4 := eventually_rpow_le hK4 (by linarith : 2 * ω₀ * βm < α₁)
  have e5 := eventually_rpow_le (by positivity : 0 < (c₀ * (100 / 128) / 2) ^ βm / 4)
    (by linarith : 2 * ω₀ * βm < α₉)
  filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (zero_lt_one' ℝ),
    Ioo_mem_nhdsGT (Real.exp_pos (-(3 / 2) * C₂)), e1, e2, e3, e4, e5] with ε hε0 hεone hεC hS1 hS2 hS3 hS4 hS5
  have hε : (0 : ℝ) < ε := hε0
  set lam : ℝ := 100 / 128 * ε ^ (2 * ω₀) with hlamdef
  have hlam : 0 < lam := by positivity
  have hlamr : ∀ r : ℝ, 10 * ε ^ ω₀ ≤ r → lam ≤ r ^ 2 / 128 := by
    intro r hr
    have hsq : (10 * ε ^ ω₀) ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (by positivity) hr 2
    have he : (ε ^ ω₀) ^ 2 = ε ^ (2 * ω₀) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hε.le, mul_comm]
      norm_num
    rw [hlamdef, ← he]
    linarith
  have hS6 : Real.exp (3 / 2 * C₂) ≤ ε⁻¹ := by
    have h := inv_anti₀ hε hεC.2.le
    rwa [← Real.exp_neg, show -(-(3 / 2) * C₂) = 3 / 2 * C₂ by ring] at h
  intro ω hω
  obtain ⟨⟨⟨⟨⟨⟨⟨hN, hηω⟩, h216ω⟩, hLLω⟩, h29ω⟩, h28ω⟩, hfinω⟩, hexitω⟩ := hω
  have hadj : ∀ a : ℤ, ∀ᵐ x ∂srwLaw (S.mult ε ω) a, ∀ n, x (n + 1) = x n ∨
      (cell ε (S.η ω) (x n) ∩ cell ε (S.η ω) (x (n + 1))).Nonempty := fun a => by
    filter_upwards [srwAeAdjacentStep (S.mult ε ω) a] with x hx n
    rcases hx n with h | h
    · exact Or.inl h
    · exact Or.inr (hηω.2 ε hε _ _ h)
  have hdiam : ∀ k, (cell ε (S.η ω) k ∩ ball 0 ρ).Nonempty → diam (cell ε (S.η ω) k) ≤ ε ^ κ := by
    intro k hk
    have := (h28ω k hk).2
    rwa [hκe] at this
  exact div_core srwHitDecompositionStep hε hεone.2.le hηω.1 hρ hρ1 hs₀ hC₂ hc₀def hCE hC₁ hβm1 hβ₉ hs₁def
    (min_le_right _ _) hlam hlamr
    (hS1.trans (le_of_eq (by rw [hlamdef]; ring))) (hS2.trans (le_of_eq (by rw [hlamdef]; ring)))
    (hS3.trans (le_of_eq (by rw [hlamdef]; ring)))
    (hS4.trans (le_of_eq (by rw [hlamdef, rpow_lam hc₀pos.le (by norm_num) hε, h2ωβ])))
    (by
      have := hS5
      rw [hlamdef, rpow_lam hc₀pos.le (by norm_num) hε]
      linarith)
    hS6 hadj hexitω hdiam hfinω h216ω hLLω h29ω hN

/-- **Lemma 6.8, route (b) of E-A10**, with the (non-almost-sure) `GoodScaleEventMeasurableStep`; a corollary of
`constantOrderLowerBoundDiv_of_aeSteps` through `goodScaleEventMeasurableAEStep_of_step`. -/
theorem constantOrderLowerBoundDiv_of_steps (𝒮 : SpaceFillingSLEModel)
    (h216 : GreenKernelLowerBoundStmt 𝒮) (h27 : VolumeGrowthStmt) (h28 : CellSizeEstimateStmt 𝒮)
    (h29 : CountingMeasureConvergenceStmt 𝒮) (h64 : GoodAnnulusPrevalenceStmt)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (h219 : ExpectedExitTimeExplicitBoundStmt 𝒮)
    (hmeas : GoodScaleEventMeasurableStep 𝒮) (hcell : AdjacentCellsMeetAeStep 𝒮) :
    ConstantOrderLowerBoundDivLogStmt 𝒮 :=
  constantOrderLowerBoundDiv_of_aeSteps 𝒮 h216 h27 h28 h29 h64 h218 h219
    (goodScaleEventMeasurableAEStep_of_step hmeas) hcell

end MatedCRT
