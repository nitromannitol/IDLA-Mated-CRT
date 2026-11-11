import MatedCRT.Defs.Setting

/-!
# FIRST PASS, positivity of the quantum mass of balls (eq. (14)) and finite nets (eq. (13))

Eq. (14): `0 < m_r` where `m_r = min_j μ_h(B_{cr/2}(z_j))` over a finite net. Its
positivity is read off from the area parametrization, as the text says (continuity, surjectivity and the mass of
intervals): every ball `B_R(z)` with `R > 0` has positive mass, because `z = η(t)` for some `t` (surjectivity), by
continuity `η([t - δ/2, t + δ/2]) ⊆ B_R(z)` for small `δ`, and `μ_h(η([t - δ/2, t + δ/2])) = δ > 0`
(`IsAreaParametrized`, Defs/Setting.lean:125). No extra LQG input is used.
-/

namespace MatedCRT.S5c

open MeasureTheory Set Metric
open scoped ENNReal

/-- **Balls have positive quantum mass** (§1.4 Step 4, the positivity used in eq. (14)): if `η` is area parametrized by `μ`
and `R > 0`, then `0 < μ (B_R(z))` for every `z ∈ ℂ`. -/
theorem mass_ball_pos {μ : Measure ℂ} {η : ℝ → ℂ} (hap : IsAreaParametrized μ η) (z : ℂ) {R : ℝ} (hR : 0 < R) :
    0 < μ (ball z R) := by
  obtain ⟨hcont, _, hsurj, hmass⟩ := hap
  obtain ⟨t, rfl⟩ := hsurj z
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.1 hcont.continuousAt R hR
  have hsub : η '' Icc (t - δ / 2) (t + δ / 2) ⊆ ball (η t) R := by
    rintro _ ⟨s, hs, rfl⟩
    rw [mem_ball]
    apply hball
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [hs.1, hs.2]
  have hpos : (0 : ℝ≥0∞) < μ (η '' Icc (t - δ / 2) (t + δ / 2)) := by
    rw [hmass (t - δ / 2) (t + δ / 2) (by linarith)]
    exact ENNReal.ofReal_pos.2 (by linarith)
  exact hpos.trans_le (measure_mono hsub)

/-- **Positive lower bound on a finite net** (§1.4 Step 4, eq. (14)): if every net ball `B_δ(x)`, `x ∈ t`, has positive
mass and `t` is finite, then there is a real `m > 0` with `m ≤ μ_h(B_δ(x))` for all net points `x`. The bound is attained
at a minimizing net point, so `m_r` of eq. (13) is well defined. -/
theorem exists_pos_ofReal_le_of_finite {μ : Measure ℂ} {δ : ℝ} {t : Set ℂ} (ht : t.Finite)
    (hpos : ∀ x ∈ t, 0 < μ (ball x δ)) :
    ∃ mr : ℝ, 0 < mr ∧ ∀ x ∈ t, ENNReal.ofReal mr ≤ μ (ball x δ) := by
  rcases t.eq_empty_or_nonempty with h | h
  · exact ⟨1, one_pos, fun x hx => by simp [h] at hx⟩
  · obtain ⟨x0, hx0, hmin⟩ :=
      (ht.toFinset).exists_min_image (fun x => μ (ball x δ)) (ht.toFinset_nonempty.2 h)
    have he0 : 0 < μ (ball x0 δ) := hpos x0 (ht.mem_toFinset.1 hx0)
    have hmin' : ∀ x ∈ t, μ (ball x0 δ) ≤ μ (ball x δ) := fun x hx => hmin x (ht.mem_toFinset.2 hx)
    by_cases htop : μ (ball x0 δ) = ⊤
    · refine ⟨1, one_pos, fun x hx => ?_⟩
      have htx : μ (ball x δ) = ⊤ := top_le_iff.1 (htop ▸ hmin' x hx)
      rw [htx]
      exact le_top
    · refine ⟨(μ (ball x0 δ)).toReal, ENNReal.toReal_pos he0.ne' htop, fun x hx => ?_⟩
      rw [ENNReal.ofReal_toReal htop]
      exact hmin' x hx

/-- **Finite nets of a compact set** (§1.4 Step 4, eq. (13)): a compact set `s` is covered by finitely many balls of any
radius `δ > 0`, centred in the set's net `t`. -/
theorem exists_net_of_compact {s : Set ℂ} (hs : IsCompact s) {δ : ℝ} (hδ : 0 < δ) :
    ∃ t : Set ℂ, t.Finite ∧ ∀ z ∈ s, z ∈ ⋃ x ∈ t, ball x δ := by
  obtain ⟨t, -, htf, hcov⟩ := finite_cover_balls_of_compact hs hδ
  exact ⟨t, htf, fun z hz => hcov hz⟩

end MatedCRT.S5c
