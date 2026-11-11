import MatedCRT.FirstPass.S5c.GreenCount

/-!
# The event `ε^{1/4} ≤ m_r` has probability tending to one

Target (4) of GAP 2 (`green_ratio_target`, `GreenTarget.lean`) needs a real `m_r > 0` with `m_r ≤ μ_h(B_{cr}(z))` on the
relevant centres and the event `ε^{1/4} ≤ m_r`. Here `m_r` is the truncated least mass of a FIXED finite net (the net is
chosen once, independent of `ω`, from the compact set and the radius), a measurable function of `ω` through a measurable
version `g` of the LQG measure (the Frozen input `FrozenLQGMeasureFieldMeasurable`; taken as a hypothesis here).

`TendsToOneOn P F E` uses the outer measure `P`, so only the upper bound of the bad event `{m_r < ε^{1/4}}` is needed:
it is a decreasing (as `ε ↓ 0`) family of measurable sets with null limit, by continuity from above.
-/

namespace MatedCRT.S5c

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

/-- **Continuity from above for the bad event** `{f < ε^{1/4}}`: if `f` is measurable and positive almost surely, the
probability of `{f < ε^{1/4}}` tends to zero as `ε ↓ 0`. -/
theorem tendsto_bad_of_pos_ae {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    {f : Ω → ℝ} (hf : Measurable f) (hpos : ∀ᵐ ω ∂P, 0 < f ω) :
    Tendsto (fun ε : ℝ => P {ω | f ω < ε ^ (1 / 4 : ℝ)}) (𝓝[>] 0) (𝓝 0) := by
  have hmono : ∀ i j : ℝ, 0 < i → i ≤ j →
      {ω | f ω < i ^ (1 / 4 : ℝ)} ⊆ {ω | f ω < j ^ (1 / 4 : ℝ)} := by
    intro i j hi hij ω hω
    exact lt_of_lt_of_le hω (Real.rpow_le_rpow hi.le hij (by norm_num))
  have hnull : P {ω | f ω ≤ 0} = 0 := by
    have h := ae_iff.mp hpos
    simpa [not_lt] using h
  have hinter : P (⋂ r > (0 : ℝ), {ω | f ω < r ^ (1 / 4 : ℝ)}) = 0 := by
    apply measure_mono_null _ hnull
    intro ω hω
    simp only [mem_iInter] at hω
    show f ω ≤ 0
    by_contra h
    have hfp : 0 < f ω := not_le.mp h
    have hr : (0 : ℝ) < (f ω / 2) ^ (4 : ℕ) := by positivity
    have h4 : f ω < ((f ω / 2) ^ (4 : ℕ)) ^ (1 / 4 : ℝ) := hω _ hr
    have hval : ((f ω / 2) ^ (4 : ℕ)) ^ (1 / 4 : ℝ) = f ω / 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      norm_num
    rw [hval] at h4
    linarith
  have hT := tendsto_measure_biInter_gt (μ := P) (a := (0 : ℝ))
    (s := fun r : ℝ => {ω | f ω < r ^ (1 / 4 : ℝ)})
    (fun r _ => (measurableSet_lt hf (measurable_const.pow_const _)).nullMeasurableSet)
    (fun i j hi hij => hmono i j hi hij) ⟨1, one_pos, measure_ne_top P _⟩
  rw [hinter] at hT
  exact hT

/-- The truncated least mass of a finite net of balls of radius `δ`, as a real number: `min (min_{x ∈ t} g_ω(B_δ(x))) 1`
(in `[0, ∞]`), then real. The truncation at `1` keeps it finite; it is a lower bound for the net masses. -/
noncomputable def netMass {Ω : Type*} (g : Ω → Measure ℂ) (t : Set ℂ) (δ : ℝ) (ω : Ω) : ℝ :=
  (min (⨅ x : t, g ω (ball (x : ℂ) δ)) 1).toReal

/-- The truncated net mass is measurable when `g` is (for a finite net). -/
theorem netMass_measurable {Ω : Type*} [MeasurableSpace Ω] {g : Ω → Measure ℂ} {t : Set ℂ} (ht : t.Finite) {δ : ℝ}
    (hg : Measurable g) : Measurable (netMass g t δ) := by
  have : Countable t := ht.countable
  have h1 : Measurable fun ω => ⨅ x : t, g ω (ball (x : ℂ) δ) :=
    Measurable.iInf fun x => (Measure.measurable_measure.1 hg) _ measurableSet_ball
  exact ((h1.min measurable_const).ennreal_toReal)

/-- The truncated net mass is positive as soon as every net ball has positive `g_ω`-mass. -/
theorem netMass_pos {Ω : Type*} {g : Ω → Measure ℂ} {t : Set ℂ} {δ : ℝ} {ω : Ω} (ht : t.Finite)
    (hpos : ∀ x ∈ t, 0 < g ω (ball x δ)) : 0 < netMass g t δ ω := by
  have : Finite t := ht.to_subtype
  have hm : 0 < ⨅ x : t, g ω (ball (x : ℂ) δ) := by
    by_cases hne : Nonempty t
    · obtain ⟨x0, hx0⟩ := Finite.exists_min fun x : t => g ω (ball (x : ℂ) δ)
      have heq : (⨅ x : t, g ω (ball (x : ℂ) δ)) = g ω (ball (x0 : ℂ) δ) :=
        le_antisymm (iInf_le _ _) (le_iInf hx0)
      rw [heq]
      exact hpos _ x0.2
    · rw [not_nonempty_iff] at hne
      rw [iInf_of_empty]
      exact ENNReal.zero_lt_top
  have hmin : 0 < min (⨅ x : t, g ω (ball (x : ℂ) δ)) 1 := lt_min hm one_pos
  have hne_top : min (⨅ x : t, g ω (ball (x : ℂ) δ)) 1 ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)
  exact ENNReal.toReal_pos hmin.ne' hne_top

/-- The ENNReal value of the truncated net mass is at most each net ball mass. -/
theorem ofReal_netMass_le {Ω : Type*} {g : Ω → Measure ℂ} {t : Set ℂ} {δ : ℝ} {ω : Ω} {x : ℂ} (hx : x ∈ t) :
    ENNReal.ofReal (netMass g t δ ω) ≤ g ω (ball x δ) := by
  have hne : min (⨅ y : t, g ω (ball (y : ℂ) δ)) 1 ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)
  unfold netMass
  rw [ENNReal.ofReal_toReal hne]
  exact (min_le_left _ _).trans (iInf_le (fun y : t => g ω (ball (y : ℂ) δ)) ⟨x, hx⟩)

/-- **The net bound with the explicit mass** (eqs. (13)-(15) with the probabilistic `m_r`):
if `μ = g_ω` and `t` is a finite net for the compact set `s` of radius `R/2`, then `ofReal (netMass) ≤ μ(B_R(z))` for
every `z ∈ s`. -/
theorem ofReal_netMass_le_mass_ball {Ω : Type*} {g : Ω → Measure ℂ} {t s : Set ℂ} {R : ℝ} {ω : Ω} {μ : Measure ℂ}
    (hμ : μ = g ω) (hcov : ∀ z ∈ s, z ∈ ⋃ x ∈ t, ball x (R / 2)) {z : ℂ} (hz : z ∈ s) :
    ENNReal.ofReal (netMass g t (R / 2) ω) ≤ μ (ball z R) := by
  have hnet : ∀ x ∈ t, ENNReal.ofReal (netMass g t (R / 2) ω) ≤ μ (ball x (R / 2)) := fun x hx => by
    rw [hμ]
    exact ofReal_netMass_le hx
  exact mass_ball_ge_of_net (hcov z hz) hnet

/-- **The event `ε^{1/4} ≤ m_r` has probability tending to one.** With `g` a measurable version of the
LQG measure and `g_ω(B_δ(x)) > 0` on the net almost surely, `P(m_r < ε^{1/4}) → 0` as `ε ↓ 0`. -/
theorem tendsto_netMass_bad {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    {g : Ω → Measure ℂ} (hg : Measurable g) {t : Set ℂ} (ht : t.Finite) {δ : ℝ}
    (hpos : ∀ᵐ ω ∂P, ∀ x ∈ t, 0 < g ω (ball x δ)) :
    Tendsto (fun ε : ℝ => P {ω | netMass g t δ ω < ε ^ (1 / 4 : ℝ)}) (𝓝[>] 0) (𝓝 0) :=
  tendsto_bad_of_pos_ae P (netMass_measurable ht hg) (hpos.mono fun _ hω => netMass_pos ht hω)

end MatedCRT.S5c
