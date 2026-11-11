import MatedCRT.Draft.Section2

/-!
# Lemma 6.8, Step 4: the exit-time moment bound at the scale of a good annulus 

Step 4 of the proof of Lemma 6.8 (lemma:constant-order-lower-bound-div, lines 2595-2604) bounds the second moment of
the exit time `ξ` of the walk from the ball `B' = B_{𝐫_z/4}(η(b))`, which lies in the good annulus `𝔸_{𝐫_z, 2𝐫_z}(z)`,
through Lemma 2.18 (BG20 Proposition 5.1, line 921), and compares the result with the left side of the good-annulus
event (eq:good-annulus-event, line 2315). After correction [C5] (`MatedCRT.IsGoodAnnulusEvent`) the integrand of the
event is the scale-invariant `log (r/|u - v|) + 1`, while the integrand of Lemma 2.18 is `log (1/|u - v|) + 1`.

* `ExitTimeScaleInvariantStep`: the scale-invariant form of Lemma 2.18 for balls `B_s(y) ⊆ B_ρ` with `s ≥ ε^κ`. With it,
  Step 4 gives an `r`-independent `s₂`, as printed. It is route (a). It is NOT a consequence of the Draft
  statements and the admitted inputs (QuantumConeScalingInput, ConeRestrictionInput, SLEModelInvarianceInput, Fact 2.2):
  the only exact symmetry of the quantum-cone mated-CRT environment is the scaling about the origin (random radius
  `R_b`), and an origin-fixing similarity sending `B_s(y)` into `B_ρ` leaves the additive loss
  `log ((|y| + s)/(ρ s))` (`MatedCRT.log_div_add_log_le_log_one_div_scaled`); Step 4 needs `|y| ≥ s₀`, `s ≤ √δ → 0`.
  It is a new literature input (not stated in BG20) and would have to be admitted as a literature input.
* `ExitTimeLogLossStep`: what Lemma 2.18 does give for balls, the scale-invariant integrand plus the additive loss
  `log (1/s) μ_h(B_{s + ε^α}(y))`. Proved below from `ExitTimeUpperBoundStmt`
  (`exitTimeLogLossStep_of_exitTimeUpperBound`). This is route (b): Step 4 then gives
  `P[V ≥ 1 | h, η] ≥ c (1 + log (1/𝐫_z))⁻²`, so `s₂` of Lemmas 6.7-6.8 carries the factor `(1 + |log r|)⁻²`.
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Topology Set Metric HarmonicBalls
open scoped ENNReal NNReal

/-- **Route (a)** (Lemma 6.8, Step 4, line 2600): the scale-invariant version of Lemma 2.18 (BG20
Proposition 5.1, line 921) for balls. There are `α = α(γ) > 0`, `κ = κ(γ) > 0` and `C = C(ρ, γ) > 0` such that with
polynomially high probability as `ε → 0`: for every ball `B_s(y) ⊆ B_ρ` with `s ≥ ε^κ` and `μ_h(B_s(y)) ≥ ε^α`, every
`a ∈ V^ε(B_s(y))` and every `N ∈ ℕ`,
`E[(τ^ε_{B_s(y)}(a))^N | h, η] ≤ N! C^N ε^{-N} (sup_{v ∈ B_s(y)} ∫_{B_{ε^α}(B_s(y))} (log (s/|u - v|) + 1) dμ_h(u))^N`.
Step 4 uses `N = 2`, `y = η(b)`, `s = 𝐫_z/4`. The integrand is taken through its positive part, as in
`MatedCRT.IsGoodAnnulusEvent`. Not derivable from the Draft statements and the admitted inputs (see the module
docstring). -/
def ExitTimeScaleInvariantStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ α κ : ℝ, 0 < α ∧ 0 < κ ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∃ C : ℝ, 0 < C ∧
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  PolyHighProb S.P fun ε => {ω | ∀ (y : ℂ) (s : ℝ), ε ^ κ ≤ s → ball y s ⊆ ball 0 ρ →
    ENNReal.ofReal (ε ^ α) ≤ S.μ ω (ball y s) →
    ∀ a ∈ cellVertices ε (S.η ω) (ball y s), ∀ N : ℕ,
      exitTimeMoment (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball y s)) a N ≤
        ENNReal.ofReal (N.factorial * C ^ N * ε ^ (-(N : ℝ))) *
          (⨆ v ∈ ball y s, ∫⁻ u in thickening (ε ^ α) (ball y s),
            ENNReal.ofReal (Real.log (s / ‖u - v‖) + 1) ∂S.μ ω) ^ N}

/-- **Route (b)** (Lemma 6.8, Step 4, line 2600): Lemma 2.18 for balls, written with the scale-invariant
integrand plus the loss term. There are `α = α(γ) > 0` and `C = C(ρ, γ) > 0` such that with polynomially high
probability as `ε → 0`: for every ball `B_s(y) ⊆ B_ρ` with `μ_h(B_s(y)) ≥ ε^α`, every `a ∈ V^ε(B_s(y))` and `N ∈ ℕ`,
`E[(τ^ε_{B_s(y)}(a))^N | h, η] ≤ N! C^N ε^{-N} (sup_{v ∈ B_s(y)} ∫_{B_{ε^α}(B_s(y))} (log (s/|u - v|) + 1) dμ_h(u)`
`+ log (1/s) μ_h(B_{ε^α}(B_s(y))))^N`.
The loss `log (1/s) μ_h(B_{ε^α}(B_s(y)))` cannot be removed using Lemma 2.18 alone: on `B_{ε^α}(B_s(y))` the integrand
of Lemma 2.18 is at least `log (1/(2(s + ε^α))) + 1` (`MatedCRT.log_one_div_le_of_mem_thickening_ball`). Consequence of
Lemma 2.18: `exitTimeLogLossStep_of_exitTimeUpperBound`. -/
def ExitTimeLogLossStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ α : ℝ, 0 < α ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∃ C : ℝ, 0 < C ∧
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  PolyHighProb S.P fun ε => {ω | ∀ (y : ℂ) (s : ℝ), 0 < s → ball y s ⊆ ball 0 ρ →
    ENNReal.ofReal (ε ^ α) ≤ S.μ ω (ball y s) →
    ∀ a ∈ cellVertices ε (S.η ω) (ball y s), ∀ N : ℕ,
      exitTimeMoment (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball y s)) a N ≤
        ENNReal.ofReal (N.factorial * C ^ N * ε ^ (-(N : ℝ))) *
          ((⨆ v ∈ ball y s, ∫⁻ u in thickening (ε ^ α) (ball y s),
              ENNReal.ofReal (Real.log (s / ‖u - v‖) + 1) ∂S.μ ω) +
            ENNReal.ofReal (Real.log (1 / s)) * S.μ ω (thickening (ε ^ α) (ball y s))) ^ N}

/-- Splitting the logarithmic kernel at scale `s`: `(log (1/x) + 1)⁺ ≤ (log (s/x) + 1)⁺ + (log (1/s))⁺` for `x ≥ 0`
(with Lean's `log 0 = 0` at `x = 0`). -/
theorem ofReal_log_one_div_add_one_le {s : ℝ} (hs : 0 < s) {x : ℝ} (hx : 0 ≤ x) :
    ENNReal.ofReal (Real.log (1 / x) + 1) ≤
      ENNReal.ofReal (Real.log (s / x) + 1) + ENNReal.ofReal (Real.log (1 / s)) := by
  rcases hx.eq_or_lt with rfl | hx
  · rw [div_zero, div_zero, Real.log_zero]
    exact le_self_add
  · calc ENNReal.ofReal (Real.log (1 / x) + 1)
          = ENNReal.ofReal ((Real.log (s / x) + 1) + Real.log (1 / s)) := by
            congr 1
            rw [Real.log_div hs.ne' hx.ne']
            simp only [one_div, Real.log_inv]
            ring
      _ ≤ _ := ENNReal.ofReal_add_le

/-- `ofReal_log_one_div_add_one_le` for the kernel `|v - u|` of Lemma 2.18, written with `|u - v|` as in
`MatedCRT.IsGoodAnnulusEvent`. -/
theorem ofReal_log_one_div_norm_sub_le {s : ℝ} (hs : 0 < s) (u v : ℂ) :
    ENNReal.ofReal (Real.log (1 / ‖v - u‖) + 1) ≤
      ENNReal.ofReal (Real.log (s / ‖u - v‖) + 1) + ENNReal.ofReal (Real.log (1 / s)) := by
  rw [norm_sub_rev v u]
  exact ofReal_log_one_div_add_one_le hs (norm_nonneg _)

/-- The logarithmic potential of `μ` on `T` at scale `1` is at most the one at scale `s` plus `log (1/s) μ(T)`. -/
theorem setLIntegral_log_one_div_le (μ : Measure ℂ) (T : Set ℂ) (v : ℂ) {s : ℝ} (hs : 0 < s) :
    ∫⁻ u in T, ENNReal.ofReal (Real.log (1 / ‖v - u‖) + 1) ∂μ ≤
      ∫⁻ u in T, ENNReal.ofReal (Real.log (s / ‖u - v‖) + 1) ∂μ +
        ENNReal.ofReal (Real.log (1 / s)) * μ T :=
  calc ∫⁻ u in T, ENNReal.ofReal (Real.log (1 / ‖v - u‖) + 1) ∂μ
        ≤ ∫⁻ u in T, (ENNReal.ofReal (Real.log (s / ‖u - v‖) + 1) +
            ENNReal.ofReal (Real.log (1 / s))) ∂μ :=
          lintegral_mono fun u => ofReal_log_one_div_norm_sub_le hs u v
    _ = ∫⁻ u in T, ENNReal.ofReal (Real.log (s / ‖u - v‖) + 1) ∂μ +
          ∫⁻ _ in T, ENNReal.ofReal (Real.log (1 / s)) ∂μ :=
          lintegral_add_right _ measurable_const
    _ = _ := by rw [setLIntegral_const]

/-- The quantity of Lemma 2.18 (sup over `D` of the logarithmic potential on `T`) is at most the scale-`s` quantity
plus the loss `log (1/s) μ(T)`. -/
theorem iSup_setLIntegral_log_one_div_le (μ : Measure ℂ) (D T : Set ℂ) {s : ℝ} (hs : 0 < s) :
    (⨆ v ∈ D, ∫⁻ u in T, ENNReal.ofReal (Real.log (1 / ‖v - u‖) + 1) ∂μ) ≤
      (⨆ v ∈ D, ∫⁻ u in T, ENNReal.ofReal (Real.log (s / ‖u - v‖) + 1) ∂μ) +
        ENNReal.ofReal (Real.log (1 / s)) * μ T :=
  iSup₂_le fun v hv => (setLIntegral_log_one_div_le μ T v hs).trans <| by
    gcongr
    exact le_iSup₂ (f := fun v (_ : v ∈ D) =>
      ∫⁻ u in T, ENNReal.ofReal (Real.log (s / ‖u - v‖) + 1) ∂μ) v hv

/-- **Route (b)**: Lemma 2.18 implies its log-loss form for balls. -/
theorem exitTimeLogLossStep_of_exitTimeUpperBound {𝒮 : SpaceFillingSLEModel}
    (h218 : ExitTimeUpperBoundStmt 𝒮) : ExitTimeLogLossStep 𝒮 := by
  intro γ hγ hγ2
  obtain ⟨α, hα, h⟩ := h218 γ hγ hγ2
  refine ⟨α, hα, fun ρ hρ hρ1 => ?_⟩
  obtain ⟨C, hC, h⟩ := h ρ hρ hρ1
  refine ⟨C, hC, fun Ω _ S hS => ?_⟩
  obtain ⟨p, hp, K, r₀, hr₀, hK⟩ := h Ω S hS
  refine ⟨p, hp, K, r₀, hr₀, fun ε hε hεr => (measure_mono ?_).trans (hK ε hε hεr)⟩
  refine Set.compl_subset_compl.mpr fun ω hω => ?_
  simp only [Set.mem_ofPred_eq] at hω ⊢
  intro y s hs hys hμ a ha N
  refine (hω.1 (ball y s) measurableSet_ball hys hμ a ha N).trans ?_
  gcongr
  exact iSup_setLIntegral_log_one_div_le _ _ _ hs

end MatedCRT
