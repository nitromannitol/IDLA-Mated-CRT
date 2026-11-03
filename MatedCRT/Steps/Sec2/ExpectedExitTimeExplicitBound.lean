import MatedCRT.Draft.Section2
import MatedCRT.Proofs.Infra.RandomWalk
import MatedCRT.Proofs.Infra.Setting

/-!
# Lemma 2.19 from Lemmas 2.17 and 2.18

Lemma 2.19 (lemma:expected-exit-time-explicit-bound, line 933) follows from Lemma 2.17 (lemma:bounded-exit-time:
`sup_{D ⊆ B_{ρ'}} 𝓜(D) < ∞` a.s., and `sup_{y ∈ B_ρ} 𝓜(B_δ(y)) ≤ δ^{q₁}` with polynomially high probability) and
Lemma 2.18 (lemma:exit-time-upper-bound, BG20 Proposition 5.1: `q^ε_D ≤ Q^ε_D ≤ C ε⁻¹ 𝓜(B_{ε^α}(D))` on `V^ε(D)`),
as in the proof of line 946, with `ρ' ∈ (ρ, 1)`:
* `B_{ε^α}(D) ⊆ B_{ρ'}` once `ε^α < ρ' - ρ`, so `Q^ε_D ≤ C ε⁻¹ sup_{D' ⊆ B_{ρ'}} 𝓜(D') < ∞`;
* `B_{ε^α}(B_δ(y)) ⊆ B_{2δ}(y)` once `ε^α < δ`, so `Q^ε_{B_δ(y)} ≤ C ε⁻¹ (2δ)^{q₁} ≤ ε⁻¹ δ^{q₁/2}` once
  `C 2^{q₁} δ^{q₁/2} < 1`; the exponent of Lemma 2.19 is `q = q₁/2`.
Outside the interior cell vertices `V^ε(D) ∖ V^ε(∂D)` the walk starts outside the set, and both exit times vanish.
-/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric HarmonicBalls
open scoped ENNReal

/-- The absorption of the constants of Lemma 2.18 into `δ^q` (line 946): if `δ^{q/2} < (C 2^q)⁻¹`, then
`C ε⁻¹ (2δ)^q ≤ ε⁻¹ δ^{q/2}`. -/
theorem expectedExitTimeExplicitBound_rpow_le {C ε δ q : ℝ} (hC : 0 < C) (hε : 0 < ε) (hδ : 0 < δ)
    (hδs : δ ^ (q / 2) < (C * 2 ^ q)⁻¹) : C * ε⁻¹ * (2 * δ) ^ q ≤ ε⁻¹ * δ ^ (q / 2) := by
  have hA : 0 < C * 2 ^ q := mul_pos hC (Real.rpow_pos_of_pos two_pos q)
  have hd : 0 ≤ δ ^ (q / 2) := Real.rpow_nonneg hδ.le _
  have h1 : C * 2 ^ q * δ ^ (q / 2) ≤ 1 := by
    have h := mul_lt_mul_of_pos_left hδs hA
    rw [mul_inv_cancel₀ hA.ne'] at h
    exact h.le
  have h2 : (2 * δ) ^ q = 2 ^ q * (δ ^ (q / 2) * δ ^ (q / 2)) := by
    rw [Real.mul_rpow zero_le_two hδ.le, ← Real.rpow_add hδ, add_halves]
  rw [h2]
  calc C * ε⁻¹ * (2 ^ q * (δ ^ (q / 2) * δ ^ (q / 2)))
      = ε⁻¹ * δ ^ (q / 2) * (C * 2 ^ q * δ ^ (q / 2)) := by ring
    _ ≤ ε⁻¹ * δ ^ (q / 2) * 1 :=
        mul_le_mul_of_nonneg_left h1 (mul_nonneg (inv_nonneg.mpr hε.le) hd)
    _ = ε⁻¹ * δ ^ (q / 2) := mul_one _

/-- **Lemma 2.19** from **Lemma 2.17** (`BoundedExitTimeRVStmt`) and **Lemma 2.18** (`ExitTimeUpperBoundStmt`,
BG20 Proposition 5.1). -/
theorem expectedExitTimeExplicitBound_of_steps {𝒮 : SpaceFillingSLEModel} (h17 : BoundedExitTimeRVStmt)
    (h18 : ExitTimeUpperBoundStmt 𝒮) : ExpectedExitTimeExplicitBoundStmt 𝒮 := by
  intro γ hγ0 hγ2
  obtain ⟨q₁, hq₁, H17⟩ := h17 γ hγ0 hγ2
  obtain ⟨α, hα, H18⟩ := h18 γ hγ0 hγ2
  refine ⟨α, q₁ / 2, hα, half_pos hq₁, fun ρ hρ0 hρ1 Ω _ S hS => ?_⟩
  obtain ⟨C, hC, H18ρ⟩ := H18 ρ hρ0 hρ1
  have hcone := hS.isConeField
  have E18 := H18ρ Ω S hS
  obtain ⟨ρ', hρρ', hρ'1⟩ : ∃ ρ', ρ < ρ' ∧ ρ' < 1 := ⟨(1 + ρ) / 2, by linarith, by linarith⟩
  have hG : S.P {ω | (⨆ (D : Set ℂ) (_ : D ⊆ ball 0 ρ'), largestExitTimeRV (S.μ ω) D) < ⊤}ᶜ = 0 := by
    rw [Set.compl_ofPred]
    exact ae_iff.mp (H17 ρ' (hρ0.trans hρρ') hρ'1 Ω S.P S.hC S.hcirc S.μ hcone).1
  obtain ⟨r₁, hr₁, hr₁s⟩ := exists_pos_rpow_lt hα (sub_pos.mpr hρρ')
  refine ⟨polyHighProb_of_inter_subset E18 hG hr₁ fun ε hε hεr ω hω => ?_, ?_⟩
  · -- `q^ε_D ≤ Q^ε_D < ∞`
    obtain ⟨⟨-, hB⟩, hGω⟩ := hω
    have hGω' : (⨆ (D : Set ℂ) (_ : D ⊆ ball 0 ρ'), largestExitTimeRV (S.μ ω) D) < ⊤ := hGω
    have hεα := hr₁s ε hε hεr
    intro D _ hD _ a
    by_cases ha : a ∈ interiorCellVertices ε (S.η ω) D
    · obtain ⟨h1, h2⟩ := hB D hD a (interiorCellVertices_subset _ _ _ ha)
      have hsub : thickening (ε ^ α) D ⊆ ball 0 ρ' :=
        ((thickening_subset_of_subset _ hD).trans (thickening_ball 0 _ ρ)).trans
          (ball_subset_ball (by linarith))
      exact ⟨h1, h2.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        ((le_iSup₂_of_le (thickening (ε ^ α) D) hsub le_rfl).trans_lt hGω'))⟩
    · rw [normExitTime_eq_zero_of_not_mem _ ha, expectedExitTime_eq_zero_of_not_mem _ ha,
        ENNReal.ofReal_zero]
      exact ⟨le_rfl, ENNReal.zero_lt_top⟩
  · -- `q^ε_{B_δ(y)} ≤ Q^ε_{B_δ(y)} ≤ ε⁻¹ δ^q` as `ε → 0` and then `δ → 0`
    obtain ⟨p₁, hp₁, K₁, r₂, hr₂, h17b⟩ := (H17 ρ hρ0 hρ1 Ω S.P S.hC S.hcirc S.μ hcone).2
    obtain ⟨p, hp, K, r₀, hr₀, h18b⟩ := E18
    obtain ⟨δ₁, hδ₁, hδ₁s⟩ := exists_pos_rpow_lt (half_pos hq₁)
      (inv_pos.mpr (mul_pos hC (Real.rpow_pos_of_pos two_pos q₁)))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (tendsto_ofReal_mul_rpow K₁ 2 p₁ hp₁) (Eventually.of_forall fun _ => zero_le) ?_
    filter_upwards [Ioo_mem_nhdsGT (lt_min hδ₁ (half_pos hr₂))] with δ hδ
    obtain ⟨hδ0, hδlt⟩ := hδ
    have hδs := hδ₁s δ hδ0 (hδlt.trans_le (min_le_left _ _))
    have hδ₂ : 2 * δ < r₂ := by linarith [hδlt.trans_le (min_le_right _ _)]
    obtain ⟨r₃, hr₃, hr₃s⟩ := exists_pos_rpow_lt hα hδ0
    have h1' : Tendsto (fun ε : ℝ => ENNReal.ofReal (K * ε ^ p)) (𝓝[>] 0) (𝓝 0) := by
      simpa using tendsto_ofReal_mul_rpow K 1 p hp
    have hlim : Tendsto (fun ε : ℝ => ENNReal.ofReal (K * ε ^ p) + ENNReal.ofReal (K₁ * (2 * δ) ^ p₁))
        (𝓝[>] 0) (𝓝 (0 + ENNReal.ofReal (K₁ * (2 * δ) ^ p₁))) := h1'.add tendsto_const_nhds
    rw [zero_add] at hlim
    refine (limsup_le_limsup ?_).trans hlim.limsup_eq.le
    filter_upwards [Ioo_mem_nhdsGT (lt_min hr₀ hr₃)] with ε hε
    obtain ⟨hε0, hεlt⟩ := hε
    have hεα := hr₃s ε hε0 (hεlt.trans_le (min_le_right _ _))
    refine measure_setOf_not_le_add (h18b ε hε0 (hεlt.trans_le (min_le_left _ _)))
      (h17b (2 * δ) (mul_pos two_pos hδ0) hδ₂) ?_
    intro ω hA hB y hy a
    obtain ⟨-, hA2⟩ := hA
    have hB' : ∀ y ∈ ball (0 : ℂ) ρ, largestExitTimeRV (S.μ ω) (ball y (2 * δ)) ≤
        ENNReal.ofReal ((2 * δ) ^ q₁) := hB
    by_cases ha : a ∈ interiorCellVertices ε (S.η ω) (ball y δ)
    · obtain ⟨h1, h2⟩ := hA2 (ball y δ) hy a (interiorCellVertices_subset _ _ _ ha)
      refine ⟨h1, h2.trans ?_⟩
      have hsub : thickening (ε ^ α) (ball y δ) ⊆ ball y (2 * δ) :=
        (thickening_ball y _ δ).trans (ball_subset_ball (by linarith))
      have hy0 : y ∈ ball (0 : ℂ) ρ := hy (mem_ball_self hδ0)
      calc ENNReal.ofReal (C * ε⁻¹) * largestExitTimeRV (S.μ ω) (thickening (ε ^ α) (ball y δ))
          ≤ ENNReal.ofReal (C * ε⁻¹) * ENNReal.ofReal ((2 * δ) ^ q₁) := by
            gcongr
            exact (largestExitTimeRV_mono _ hsub).trans (hB' y hy0)
        _ = ENNReal.ofReal (C * ε⁻¹ * (2 * δ) ^ q₁) :=
            (ENNReal.ofReal_mul (mul_pos hC (inv_pos.mpr hε0)).le).symm
        _ ≤ ENNReal.ofReal (ε⁻¹ * δ ^ (q₁ / 2)) :=
            ENNReal.ofReal_le_ofReal (expectedExitTimeExplicitBound_rpow_le hC hε0 hδ0 hδs)
    · rw [normExitTime_eq_zero_of_not_mem _ ha, expectedExitTime_eq_zero_of_not_mem _ ha,
        ENNReal.ofReal_zero]
      exact ⟨le_rfl, zero_le⟩

end MatedCRT
