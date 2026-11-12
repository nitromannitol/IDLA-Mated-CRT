import MatedCRT.FirstPass.Derived.GreenCrudePolyHighProb

/-!
# Inradius of the cells from the segment-ball estimate

BG20 (Berestycki-Gwynne, arXiv:2003.10320), proof of Lemma 5.5 (`lem-cell-comparable`), estimate
`eqn-comp-inrad`: by the cell size estimate `ε^p ≤ diam H ≤ ε^q` together with
Gwynne-Holden-Miller (KPZ formulas for the Liouville quantum gravity metric), Proposition 3.4 and
Remark 3.9, with polynomially high probability every cell `H^ε_x` meeting `B_ρ` contains a
Euclidean disc of radius `ε^{ζ/4} diam H^ε_x`.

The cited estimate is the segment-ball event `E_{ε'}(R, r)`: for every `t ∈ (0, ε']` and every
segment `η([a, b]) ⊆ B_R` of diameter at least `t^{1-r}`, the segment contains a disc of radius
`t`. Applied with `t = (diam H)^{1/(1-r)}` and `ε' = ε^{q/(1-r)}`, it gives a disc of radius
`(diam H)^{r/(1-r)} diam H ≥ ε^{pr/(1-r)} diam H`, and `pr/(1-r) ≤ ζ/4` for small `r`.

## Main statements

* `MatedCRT.exists_ball_subset_image_Icc_of_segmentBalls`: the deterministic step.
* `MatedCRT.polyHighProb_comp_rpow`: polynomially high probability is preserved by `ε ↦ ε^a`.
* `MatedCRT.MatedCRTEnv.IsValid.polyHighProb_cellInballEvent_of_segmentBalls`: the inradius
  event `S.cellInballEvent δ ρ` with polynomially high probability.
-/

open Set Metric MeasureTheory Filter Topology HarmonicBalls

namespace MatedCRT

/-- **Deterministic step of BG20 `eqn-comp-inrad`.** If every segment of `η` inside `B_R` of
diameter at least `t^{1-r}` contains a disc of radius `t` (for `t ∈ (0, ε']`), then a segment
`η([a, b]) ⊆ B_R` with `ε^p ≤ diam ≤ ε^q`, `ε^{q/(1-r)} ≤ ε'` and `pr/(1-r) ≤ ζ/4` contains a disc
of radius `ε^{ζ/4}` times its diameter. -/
theorem exists_ball_subset_image_Icc_of_segmentBalls {η : ℝ → ℂ} {R r ε ε' p q ζ a b : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hseg : ∀ t ∈ Ioc (0 : ℝ) ε', ∀ a b : ℝ, a < b → η '' Icc a b ⊆ ball 0 R →
      t ^ (1 - r) ≤ diam (η '' Icc a b) → ∃ w : ℂ, ball w t ⊆ η '' Icc a b)
    (hε' : ε ^ (q / (1 - r)) ≤ ε') (hpr : p * r / (1 - r) ≤ ζ / 4)
    (hab : a < b) (hR : η '' Icc a b ⊆ ball 0 R)
    (hlo : ε ^ p ≤ diam (η '' Icc a b)) (hhi : diam (η '' Icc a b) ≤ ε ^ q) :
    ∃ w : ℂ, ball w (ε ^ (ζ / 4) * diam (η '' Icc a b)) ⊆ η '' Icc a b := by
  set d := diam (η '' Icc a b) with hd_def
  have h1r : 0 < 1 - r := sub_pos.2 hr1
  have hd : 0 < d := (Real.rpow_pos_of_pos hε p).trans_le hlo
  have hδ0 : 0 < d ^ (1 / (1 - r)) := Real.rpow_pos_of_pos hd _
  have hδε : d ^ (1 / (1 - r)) ≤ ε' := by
    calc d ^ (1 / (1 - r)) ≤ (ε ^ q) ^ (1 / (1 - r)) :=
          Real.rpow_le_rpow hd.le hhi (by positivity)
      _ = ε ^ (q / (1 - r)) := by rw [← Real.rpow_mul hε.le, mul_one_div]
      _ ≤ ε' := hε'
  have hδr : (d ^ (1 / (1 - r))) ^ (1 - r) = d := by
    rw [← Real.rpow_mul hd.le, one_div_mul_cancel h1r.ne', Real.rpow_one]
  obtain ⟨w, hw⟩ := hseg _ ⟨hδ0, hδε⟩ a b hab hR hδr.le
  refine ⟨w, (ball_subset_ball ?_).trans hw⟩
  have hsplit : d ^ (1 / (1 - r)) = d ^ (r / (1 - r)) * d := by
    rw [← Real.rpow_add_one hd.ne']
    congr 1
    field_simp
    ring
  rw [hsplit]
  refine mul_le_mul_of_nonneg_right ?_ hd.le
  calc ε ^ (ζ / 4) ≤ ε ^ (p * r / (1 - r)) := Real.rpow_le_rpow_of_exponent_ge hε hε1 hpr
    _ = (ε ^ p) ^ (r / (1 - r)) := by rw [← Real.rpow_mul hε.le, mul_div_assoc]
    _ ≤ d ^ (r / (1 - r)) :=
        Real.rpow_le_rpow (Real.rpow_pos_of_pos hε p).le hlo (div_nonneg hr0 h1r.le)

/-- Polynomially high probability is preserved under the change of scale `ε ↦ ε^a`, `a > 0`. -/
theorem polyHighProb_comp_rpow {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {E : ℝ → Set Ω} (h : PolyHighProb P E) {a : ℝ} (ha : 0 < a) :
    PolyHighProb P fun r => E (r ^ a) := by
  obtain ⟨p, hp, C, r₀, hr₀, hE⟩ := h
  refine ⟨a * p, mul_pos ha hp, C, r₀ ^ (1 / a), Real.rpow_pos_of_pos hr₀ _,
    fun r hr hrr => ?_⟩
  have h1 : r ^ a < r₀ := by
    calc r ^ a < (r₀ ^ (1 / a)) ^ a := Real.rpow_lt_rpow hr.le hrr ha
      _ = r₀ := by rw [← Real.rpow_mul hr₀.le, one_div_mul_cancel ha.ne', Real.rpow_one]
  have h2 := hE (r ^ a) (Real.rpow_pos_of_pos hr a) h1
  rwa [← Real.rpow_mul hr.le] at h2

/-- **Inradius of the cells (BG20 `eqn-comp-inrad`).** For a valid environment, `0 < δ` and
`0 < ρ < 1`: the cell size estimate and the segment-ball event of Gwynne-Holden-Miller
(Proposition 3.4 and Remark 3.9) inside `B_2`, with polynomially high probability for each
`r ∈ (0, 1)`, give the inradius event `S.cellInballEvent δ ρ` with polynomially high
probability. -/
theorem MatedCRTEnv.IsValid.polyHighProb_cellInballEvent_of_segmentBalls
    {𝒮 : SpaceFillingSLEModel} (hcell : CellSizeEstimateStmt 𝒮) {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    {δ ρ : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hseg : ∀ r ∈ Ioo (0 : ℝ) 1, PolyHighProb S.P fun ε' => {ω | ∀ t ∈ Ioc (0 : ℝ) ε',
      ∀ a b : ℝ, a < b → S.η ω '' Icc a b ⊆ ball 0 2 →
        t ^ (1 - r) ≤ diam (S.η ω '' Icc a b) → ∃ w : ℂ, ball w t ⊆ S.η ω '' Icc a b}) :
    PolyHighProb S.P (S.cellInballEvent δ ρ) := by
  have h2γ : 0 < (2 + γ) ^ 2 := by positivity
  have hζ'0 : 0 < 1 / (2 + γ) ^ 2 := by positivity
  have hζ'1 : 1 / (2 + γ) ^ 2 < 1 := by rw [div_lt_one h2γ]; nlinarith
  have hq : 0 < 2 / (2 + γ) ^ 2 - 1 / (2 + γ) ^ 2 := by
    have e : 2 / (2 + γ) ^ 2 - 1 / (2 + γ) ^ 2 = 1 / (2 + γ) ^ 2 := by ring
    rw [e]
    exact hζ'0
  have hp : 0 < 2 / (2 - γ) ^ 2 + 1 / (2 + γ) ^ 2 := by
    have : 0 < (2 - γ) ^ 2 := by nlinarith
    positivity
  obtain ⟨p, hpdef⟩ : ∃ p : ℝ, p = 2 / (2 - γ) ^ 2 + 1 / (2 + γ) ^ 2 := ⟨_, rfl⟩
  rw [← hpdef] at hp
  obtain ⟨r, hrdef⟩ : ∃ r : ℝ, r = δ / (4 * p + δ) := ⟨_, rfl⟩
  have h4p : 0 < 4 * p + δ := by linarith
  have hr0 : 0 < r := by rw [hrdef]; positivity
  have hr1 : r < 1 := by rw [hrdef, div_lt_one h4p]; linarith
  have h1r : 0 < 1 - r := sub_pos.2 hr1
  have hpr : p * r / (1 - r) ≤ δ / 4 := by
    rw [div_le_iff₀ h1r, hrdef]
    field_simp
    ring_nf
    nlinarith
  have hE1 := hcell γ hγ hγ2 _ ρ hζ'0 hζ'1 hρ hρ1 Ω S hS
  have hE2 := polyHighProb_comp_rpow (hseg r ⟨hr0, hr1⟩) (div_pos hq h1r)
  refine (hE1.inter hE2).mono_of_small one_pos ?_
  rintro ε hε hε1 ω ⟨h1, h2⟩ k hk
  obtain ⟨hlo, hhi⟩ := h1 k hk
  rw [← hpdef] at hlo
  have hlo' : 0 < diam (cell ε (S.η ω) k) := (Real.rpow_pos_of_pos hε p).trans_le hlo
  have hbdd : Bornology.IsBounded (cell ε (S.η ω) k) := by
    by_contra hb
    exact hlo'.ne' (diam_eq_zero_of_unbounded hb)
  have hq1 : ε ^ (2 / (2 + γ) ^ 2 - 1 / (2 + γ) ^ 2) ≤ 1 :=
    Real.rpow_le_one hε.le hε1.le hq.le
  obtain ⟨z, hzH, hzB⟩ := hk
  have hR : cell ε (S.η ω) k ⊆ ball 0 2 := by
    intro x hx
    have hxz : dist x z ≤ diam (cell ε (S.η ω) k) := dist_le_diam_of_mem hbdd hx hzH
    have hz0 : dist z 0 < ρ := hzB
    rw [mem_ball]
    calc dist x 0 ≤ dist x z + dist z 0 := dist_triangle _ _ _
      _ < 2 := by linarith
  have hab : ε * ((k : ℝ) - 1) < ε * k := by nlinarith
  exact exists_ball_subset_image_Icc_of_segmentBalls hr0.le hr1 hε hε1.le h2 le_rfl
    hpr hab hR hlo hhi

end MatedCRT
