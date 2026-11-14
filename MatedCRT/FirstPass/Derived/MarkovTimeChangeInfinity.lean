import MatedCRT.FirstPass.Derived.MarkovTimeChange
import MatedCRT.FirstPass.LPBridge.PlanarBrownianSpace
import LatticeProb.Prob.MarkovPathNoLimit

/-!
# The time change of a Markovian time-changed Brownian motion is unbounded

For a Markovian time-changed planar Brownian motion `P` (Definitions 7.1-7.2 of Berestycki-Gwynne, typed in
`MatedCRT.IsMarkovTCBM`) the process `τ` of Definition 7.2 tends to infinity almost surely, although this is
not part of the definition: if `τ` were bounded then `X_u = B_{τ_u}` would converge as `u → ∞`, which a
continuous Markov family of nonconstant paths excludes almost surely.

## Main statements
* `ae_planarLaw_ne_start`: almost surely planar Brownian motion differs from its starting point at all times
  `1 / (n + 1)`.
* `DefinesTimeChangedBM.nonconstant`: the laws `P_w` of a time-changed Brownian motion charge the paths that are
  not constant on `[0, 1]`.
* `IsMarkovTCBM.exists_coupling_tendsto`: the coupling of Definition 7.2 can be taken with `τ_u → ∞`.
-/

open MeasureTheory MarkovProcess Filter Topology
open scoped NNReal ENNReal

namespace MatedCRT

/-- **Planar Brownian motion leaves its starting point at all small times.** Almost surely, for every `n`,
the path at time `1 / (n + 1)` differs from its starting point. -/
theorem ae_planarLaw_ne_start (z : ℂ) :
    ∀ᵐ b ∂planarLaw z, ∀ n : ℕ, b (((n : ℝ≥0) + 1)⁻¹) ≠ b 0 := by
  have hB := PlanarBrownianSpace.isBrownianSpace_halfSpeedPath z
  have h0 : ∀ᵐ b ∂planarLaw z, b 0 = z := by
    filter_upwards [hB.start] with b hb
    have h1 : ‖b (2⁻¹ * 0) - z‖ = 0 := by
      rw [← PlanarBrownianSpace.norm_halfSpeedPath]
      simp [hb]
    simpa [sub_eq_zero] using h1
  rw [ae_all_iff]
  intro n
  set s : ℝ≥0 := ((n : ℝ≥0) + 1)⁻¹ with hs
  have hs0 : (2 * s : ℝ≥0) ≠ 0 := by
    rw [hs]
    positivity
  have hlaw := (hB.coord 0).hasLaw_eval (2 * s)
  have hnull : planarLaw z {b | b s = b 0} = 0 := by
    refine measure_mono_null (t := {b | b 0 ≠ z} ∪
        (fun b => Real.sqrt (2 : ℕ) * (PlanarBrownianSpace.halfSpeedPath z (2 * s) b 0 - 0)) ⁻¹' {0}) ?_
      (measure_union_null (ae_iff.1 h0) ?_)
    · intro b hb
      by_cases hb0 : b 0 = z
      · right
        have hb' : b s = b 0 := hb
        simp [PlanarBrownianSpace.halfSpeedPath_zero, hb', hb0]
      · left
        exact hb0
    · have hpre := Measure.map_apply_of_aemeasurable hlaw.aemeasurable (measurableSet_singleton (0 : ℝ))
      rw [hlaw.map_eq] at hpre
      have := ProbabilityTheory.nullSingletonClass_gaussianReal (μ := 0) hs0
      rw [measure_singleton] at hpre
      exact hpre.symm
  filter_upwards [h0, measure_eq_zero_iff_ae_notMem.1 hnull] with b hb0 hb
  exact hb

/-- **A time-changed Brownian motion is not constant on `[0, 1]`.** For every start `w` the law `P_w` of a
time-changed Brownian motion charges the paths that leave their starting point at some time `r ≤ 1`: almost
surely `X_r = B_{τ_r}` with `τ_1 > 0`, and `B` is not constant on `[0, τ_1]`. -/
theorem DefinesTimeChangedBM.nonconstant {P : PathLawFamily} (hT : DefinesTimeChangedBM P) (w : ℂ) :
    0 < (P w : Measure (ContinuousPath ℂ)) {x | ∃ r : ℝ≥0, r ≤ 1 ∧ x r ≠ x 0} := by
  obtain ⟨Ω, _, Q, _, B, X, τ, hB, hXm, hlaw, hτ, hP⟩ := hT w
  have hne : ∀ᵐ ω ∂Q, ∀ n : ℕ, B ω (((n : ℝ≥0) + 1)⁻¹) ≠ B ω 0 := by
    refine ae_of_ae_map (p := fun b : ContinuousPath ℂ => ∀ n : ℕ, b (((n : ℝ≥0) + 1)⁻¹) ≠ b 0) hB ?_
    rw [hlaw]
    exact ae_planarLaw_ne_start w
  have hmain : ∀ᵐ ω ∂Q, ∃ r : ℝ≥0, r ≤ 1 ∧ X ω r ≠ X ω 0 := by
    filter_upwards [hne, hτ] with ω hω hh
    obtain ⟨hcont, hmono, h0, hXB⟩ := hh
    have hpos : 0 < τ ω 1 := h0 ▸ hmono zero_lt_one
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show (0 : ℝ) < τ ω 1 from hpos)
    have hsle : (((n : ℝ≥0) + 1)⁻¹ : ℝ≥0) ≤ τ ω 1 := by
      rw [← NNReal.coe_le_coe]
      push_cast
      rw [← one_div]
      exact hn.le
    have hmem : (((n : ℝ≥0) + 1)⁻¹ : ℝ≥0) ∈ Set.Icc (τ ω 0) (τ ω 1) := ⟨by rw [h0]; positivity, hsle⟩
    obtain ⟨r, ⟨_, hr1⟩, hr⟩ := intermediate_value_Icc zero_le_one hcont.continuousOn hmem
    refine ⟨r, hr1, ?_⟩
    rw [hXB r, hXB 0, h0, hr]
    exact hω n
  have hle := Measure.le_map_apply hXm {x : ContinuousPath ℂ | ∃ r : ℝ≥0, r ≤ 1 ∧ x r ≠ x 0}
  rw [← hP] at hle
  have hQ : Q Set.univ ≤ Q (X ⁻¹' {x : ContinuousPath ℂ | ∃ r : ℝ≥0, r ≤ 1 ∧ x r ≠ x 0}) :=
    measure_mono_ae (by filter_upwards [hmain] with ω hω _ using hω)
  rw [measure_univ] at hQ
  exact lt_of_lt_of_le zero_lt_one (hQ.trans hle)

/-- **The time change of a Markovian time-changed Brownian motion is unbounded.** In Definition 7.2 for a
Markovian family, the coupling `(B, τ, X)` can be taken with `τ_u → ∞` almost surely: if `τ` were bounded,
`X_u = B_{τ_u}` would converge as `u → ∞`, which a continuous Markov family with nonconstant paths excludes
(`LatticeProb.ae_not_exists_limit_of_markovAt_nat_of_nonconstant`). -/
theorem IsMarkovTCBM.exists_coupling_tendsto {P : PathLawFamily} (h : IsMarkovTCBM P) (z : ℂ) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (Q : Measure Ω) (_ : IsProbabilityMeasure Q)
      (B X : Ω → ContinuousPath ℂ) (τ : Ω → ℝ≥0 → ℝ≥0),
    AEMeasurable B Q ∧ AEMeasurable X Q ∧ Q.map B = planarLaw z ∧
    (∀ᵐ ω ∂Q, Continuous (τ ω) ∧ StrictMono (τ ω) ∧ τ ω 0 = 0 ∧ Tendsto (τ ω) atTop atTop ∧
      ∀ u, X ω u = B ω (τ ω u)) ∧
    (P z : Measure (ContinuousPath ℂ)) = Q.map X := by
  obtain ⟨hT, hM⟩ := h
  have hnolim := LatticeProb.ae_not_exists_limit_of_markovAt_nat_of_nonconstant (K := ⇑P) P.continuous
    (fun n => hM z n) hT.nonconstant
  obtain ⟨Ω, m, Q, hQ, B, X, τ, hB, hXm, hlaw, hτ, hP⟩ := hT z
  refine ⟨Ω, m, Q, hQ, B, X, τ, hB, hXm, hlaw, ?_, hP⟩
  have hnolimQ : ∀ᵐ ω ∂Q, ¬ ∃ L : ℂ, Tendsto (fun u : ℝ≥0 => X ω u) atTop (𝓝 L) := by
    refine ae_of_ae_map (p := fun x : ContinuousPath ℂ => ¬ ∃ L : ℂ, Tendsto (fun u : ℝ≥0 => x u) atTop (𝓝 L))
      hXm ?_
    rw [← hP]
    exact hnolim
  filter_upwards [hτ, hnolimQ] with ω hh hno
  obtain ⟨hc, hm, h0, hXB⟩ := hh
  refine ⟨hc, hm, h0, ?_, hXB⟩
  by_contra hnt
  apply hno
  have hmono : Monotone (τ ω) := hm.monotone
  have hbdd : BddAbove (Set.range (τ ω)) := by
    by_contra hb
    apply hnt
    refine tendsto_atTop_atTop_of_monotone hmono fun b => ?_
    by_contra hcon
    exact hb ⟨b, by rintro _ ⟨u, rfl⟩; exact (not_le.1 fun h => hcon ⟨u, h⟩).le⟩
  refine ⟨B ω (⨆ u, τ ω u), ?_⟩
  have := ((B ω).continuous.tendsto _).comp (tendsto_atTop_ciSup hmono hbdd)
  exact this.congr fun u => (hXB u).symm

end MatedCRT
