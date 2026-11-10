import MatedCRT.FirstPass.S5f
import MatedCRT.FirstPass.S5c.HExclusive
import MatedCRT.Proofs.Sec5.StoppedExterior

/-!
# First pass: the ceiling of Proposition 5.1, `stoppedMaxOutside_proved` (task fp-S5h-5-1-max-outside, z1)

**Theorem `stoppedMaxOutside_proved`.** `StoppedMaxOutsideStep 𝒮` (`ε M^ε → 0` in probability on `{t < T}`, Proposition 5.1,
corrected tex 2355-2360, [C21]) from `stoppedMaxOutside_of_steps` (FirstPass/S5f.lean, z10), with two of its three NEW steps
discharged here:

* `stoppedCellRepresentative_proved`: `StoppedCellRepresentativeStep 𝒮` (FirstPass/S5f/Steps.lean) is PROVED, with no
  hypothesis. Source: tex 2360 ("each cell contains a point belonging to no other cell"). Overlap nullity:
  `MatedCRT.S5c.cell_inter_null_of_lt` (FirstPass/S5c/HExclusive.lean). The representative is taken in the open ball: `η⁻¹(B_ρ)`
  is open, so a nonempty `cell ∩ B_ρ` contains `η '' [a, b]` with `a < b`, of `μ`-mass `b - a > 0` (`IsAreaParametrized`,
  Defs/Setting.lean:125). Hence `μ(cell ∩ B_ρ) > 0` and a `μ`-almost-every point of it is exclusive.
* `stoppedOriginRadius_of_nullMeasurable`: `StoppedOriginRadiusStep 𝒮` (FirstPass/S5f/Steps.lean) from the NEW
  null-measurability step `ConeOriginNullMeasurableStep 𝒮` (Proofs/Sec5/StoppedExterior.lean), by continuity from above along
  `s = 1/(n+1)` (as in `StoppedExterior.origin_of_nullMeasurable`).

Still hypotheses of `stoppedMaxOutside_proved` (BLOCKED, see reports/z1.md):
* `StoppedPoleCellStep 𝒮` (FirstPass/S5f/Steps.lean): `a^ε_0 = 0` for small `ε`, a.s.; no written argument.
* `ConeOriginNullMeasurableStep 𝒮` (Proofs/Sec5/StoppedExterior.lean): NEW; it reduces to `CodeSectionStmt 𝒮`
  (Proofs/Sec5/ConeOriginNullMeasurableProof.lean:575) and `PrestonAnalyticUniversallyMeasurableStmt`
  (Proposed/PrestonAnalytic2008.lean:43) through `coneOriginNullMeasurableStep_of_inputs` (ConeOriginNullMeasurableProof.lean:587).
-/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

/-- An open subset `U` of `ℝ` containing a point `s ∈ [A, B]` (with `A < B`) contains a nondegenerate interval inside `[A, B]`. -/
lemma exists_Icc_subset_open_inter {U : Set ℝ} (hU : IsOpen U) {A B s : ℝ} (hAB : A < B)
    (hs : s ∈ Icc A B) (hsU : s ∈ U) : ∃ a b : ℝ, a < b ∧ Icc a b ⊆ U ∩ Icc A B := by
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hU s hsU
  have hδ2 : (0 : ℝ) < δ / 2 := by positivity
  refine ⟨max A (s - δ / 2), min B (s + δ / 2), ?_, ?_⟩
  · exact lt_min_iff.2 ⟨max_lt_iff.2 ⟨hAB, by linarith [hs.2]⟩, max_lt_iff.2 ⟨by linarith [hs.1], by linarith⟩⟩
  · intro x hx
    have hxA : A ≤ x := (le_max_left _ _).trans hx.1
    have hxB : x ≤ B := hx.2.trans (min_le_left _ _)
    have h1 : s - δ / 2 ≤ x := (le_max_right _ _).trans hx.1
    have h2 : x ≤ s + δ / 2 := hx.2.trans (min_le_right _ _)
    refine ⟨hball ?_, ⟨hxA, hxB⟩⟩
    rw [mem_ball, Real.dist_eq, abs_sub_lt_iff]
    constructor <;> linarith

/-- A nonempty intersection of a cell with the open ball `B_ρ` has positive `μ`-mass, since the preimage of `B_ρ` under the
continuous area parametrization is open and the image of a nondegenerate interval has mass equal to its length. -/
lemma cell_inter_ball_measure_pos {μ : Measure ℂ} {η : ℝ → ℂ} (hap : IsAreaParametrized μ η) {ε : ℝ} (hε : 0 < ε)
    {ρ : ℝ} {k : ℤ} (hne : (cell ε η k ∩ ball (0 : ℂ) ρ).Nonempty) :
    0 < μ (cell ε η k ∩ ball (0 : ℂ) ρ) := by
  obtain ⟨hc, -, -, hμ⟩ := hap
  obtain ⟨y, hy, hyB⟩ := hne
  obtain ⟨s, hs, rfl⟩ := hy
  have hlt : ε * ((k : ℝ) - 1) < ε * (k : ℝ) := mul_lt_mul_of_pos_left (by linarith) hε
  obtain ⟨a, b, hab, hsub⟩ :=
    exists_Icc_subset_open_inter ((Metric.isOpen_ball : IsOpen (ball (0 : ℂ) ρ)).preimage hc) hlt hs hyB
  have hsub' : η '' Icc a b ⊆ cell ε η k ∩ ball (0 : ℂ) ρ := by
    rintro _ ⟨x, hx, rfl⟩
    exact Set.mem_inter (Set.mem_image_of_mem η (hsub hx).2) (hsub hx).1
  have hpos : 0 < μ (η '' Icc a b) := by
    rw [hμ a b hab]
    exact ENNReal.ofReal_pos.2 (sub_pos.2 hab)
  exact lt_of_lt_of_le hpos (measure_mono hsub')

/-- Every cell meeting `B_ρ` has a point of `B_ρ` lying in no other cell, so that its vertex label `vertexOf` is the index `k`. -/
lemma exists_exclusive_mem_cell_inter_ball {μ : Measure ℂ} {η : ℝ → ℂ} (hap : IsAreaParametrized μ η) {ε : ℝ}
    (hε : 0 < ε) {ρ : ℝ} (k : ℤ) (hne : (cell ε η k ∩ ball (0 : ℂ) ρ).Nonempty) :
    ∃ x ∈ cell ε η k ∩ ball (0 : ℂ) ρ, vertexOf ε η x = k := by
  have hBad : μ (⋃ b : ℤ, ⋃ (_ : b ≠ k), cell ε η k ∩ cell ε η b) = 0 := by
    refine measure_iUnion_null fun b => measure_iUnion_null fun hb => ?_
    rcases lt_or_gt_of_ne hb with h | h
    · rw [inter_comm]
      exact S5c.cell_inter_null_of_lt hap hε h
    · exact S5c.cell_inter_null_of_lt hap hε h
  have hnot : ¬ (cell ε η k ∩ ball (0 : ℂ) ρ ⊆ ⋃ b : ℤ, ⋃ (_ : b ≠ k), cell ε η k ∩ cell ε η b) :=
    fun hsub => (cell_inter_ball_measure_pos hap hε hne).ne' (measure_mono_null hsub hBad)
  obtain ⟨x, hx, hxB⟩ := not_subset.mp hnot
  refine ⟨x, hx, S5c.vertexOf_eq_of_exclusive hx.1 fun b hb => ?_⟩
  by_contra hne'
  exact hxB (mem_iUnion.mpr ⟨b, mem_iUnion.mpr ⟨hne', Set.mem_inter hx.1 hb⟩⟩)

/-- **NEW step N-cell, proved.** `StoppedCellRepresentativeStep 𝒮` holds with no further input: almost surely `S.η ω` is an
area parametrization of `S.μ ω` (field `MatedCRTEnv.IsValid.isAreaParametrized`). -/
theorem stoppedCellRepresentative_proved (𝒮 : SpaceFillingSLEModel) : StoppedCellRepresentativeStep 𝒮 := by
  intro γ _ _ ρ _ _ Ω _ S hS ε hε
  filter_upwards [hS.isAreaParametrized] with ω hap k hne
  exact exists_exclusive_mem_cell_inter_ball hap hε k hne

/-- **Origin radius from null-measurability.** `StoppedOriginRadiusStep 𝒮` follows from the null-measurability of the origin
inclusion events `{¬ B_s(0) ⊆ Λ_t}` (`ConeOriginNullMeasurableStep 𝒮`). The events `E_n = {¬ B_{1/(n+1)}(0) ⊆ Λ_t}` decrease to a
null set, since almost surely `Λ_t` is open and contains `0`, so `P(E_n) → 0`; and `{t < T} ∩ {¬ B_s(0) ⊆ Λ_t} ⊆ E_n` for
`s < 1/(n+1)`. Cf. `StoppedExterior.origin_of_nullMeasurable` (Proofs/Sec5/StoppedExterior.lean). -/
theorem stoppedOriginRadius_of_nullMeasurable (𝒮 : SpaceFillingSLEModel) (hmeas : ConeOriginNullMeasurableStep 𝒮) :
    StoppedOriginRadiusStep 𝒮 := by
  intro γ hγ hγ2 ρ _ _ Ω _ S hS Λ hΛ t ht
  have := hS.isProbabilityMeasure
  let E : ℕ → Set Ω := fun n => {ω | ¬ ball (0 : ℂ) (1 / ((n : ℝ) + 1)) ⊆ Λ ω t}
  have hE : ∀ n : ℕ, NullMeasurableSet (E n) S.P := fun n =>
    hmeas γ hγ hγ2 Ω S hS Λ hΛ t ht (1 / ((n : ℝ) + 1)) (by positivity)
  have hanti : Antitone E := by
    intro n m hnm ω hω
    show ¬ ball (0 : ℂ) (1 / ((n : ℝ) + 1)) ⊆ Λ ω t
    intro h
    apply (show ¬ ball (0 : ℂ) (1 / ((m : ℝ) + 1)) ⊆ Λ ω t from hω)
    have hnm' : (n : ℝ) ≤ m := by exact_mod_cast hnm
    exact (Metric.ball_subset_ball (one_div_le_one_div_of_le (by positivity) (by linarith))).trans h
  have hae : ∀ᵐ ω ∂S.P, ∃ s : ℝ, 0 < s ∧ ball (0 : ℂ) s ⊆ Λ ω t := by
    filter_upwards [hΛ] with ω hω
    obtain ⟨hHB, -, -⟩ := hω
    obtain ⟨hopen, h0, -⟩ := hHB t ht
    obtain ⟨s, hs, hsub⟩ := Metric.isOpen_iff.1 hopen 0 h0
    exact ⟨s, hs, hsub⟩
  have hnull : S.P (⋂ n, E n) = 0 := by
    refine measure_mono_null (fun ω hω => ?_) (ae_iff.1 hae)
    show ¬ ∃ s : ℝ, 0 < s ∧ ball (0 : ℂ) s ⊆ Λ ω t
    rintro ⟨s, hs, hsub⟩
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hs
    have hωn : ¬ ball (0 : ℂ) (1 / ((n : ℝ) + 1)) ⊆ Λ ω t := mem_iInter.1 hω n
    exact hωn ((Metric.ball_subset_ball hn.le).trans hsub)
  have hlim0 : Tendsto (fun n : ℕ => S.P (E n)) atTop (𝓝 0) := by
    have h := tendsto_measure_iInter_atTop (fun n => hE n) hanti ⟨0, measure_ne_top _ _⟩
    rwa [hnull] at h
  refine ENNReal.tendsto_nhds_zero.2 fun e he => ?_
  obtain ⟨N, hN⟩ := (ENNReal.tendsto_nhds_zero.1 hlim0 e he).exists
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / ((N : ℝ) + 1) by positivity)] with s hs
  refine (measure_mono ?_).trans hN
  rintro ω ⟨-, hω⟩
  show ¬ ball (0 : ℂ) (1 / ((N : ℝ) + 1)) ⊆ Λ ω t
  intro hsub
  exact hω ((Metric.ball_subset_ball hs.2.le).trans hsub)

/-- **Proposition 5.1, ceiling (`ε M^ε → 0` in probability on `{t < T}`).** `StoppedMaxOutsideStep 𝒮` from the Draft convergence
inputs (Theorem 4.1 `ConvergenceDivisibleStmt`, Lemma 3.3 `UniformConvergenceGreenKernelStmt`), the External mesh scaling
`MepsScalingInput`, the frozen disc Green pole `FrozenGreenDiscPole`, and the two open inputs `StoppedPoleCellStep` (BLOCKED,
no written argument) and `ConeOriginNullMeasurableStep` (NEW). The cell representative step is proved here. -/
theorem stoppedMaxOutside_proved (𝒮 : SpaceFillingSLEModel)
    (hconv : ConvergenceDivisibleStmt 𝒮) (hgreen : UniformConvergenceGreenKernelStmt 𝒮)
    (hM : MepsScalingInput 𝒮) (hG : MatedCRT.FrozenGreenDiscPole)
    (hpole : StoppedPoleCellStep 𝒮) (hmeas : ConeOriginNullMeasurableStep 𝒮) :
    StoppedMaxOutsideStep 𝒮 :=
  stoppedMaxOutside_of_steps 𝒮 hconv hgreen hM hG (stoppedCellRepresentative_proved 𝒮) hpole
    (stoppedOriginRadius_of_nullMeasurable 𝒮 hmeas)

end MatedCRT
