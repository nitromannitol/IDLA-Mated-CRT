import MatedCRT.FirstPass.Derived.ConeRadialRescale
import LatticeProb.Prob.UpcrossGlue
import LatticeProb.Prob.BrownianRestartPath

/-!
# Rescaling a radial pair at a level below its starting value: the deterministic computation

A radial pair `p = (t ↦ y t + Q t, s ↦ z s - Q s)` with `y 0 = z 0 = 0`, `z ≥ 0` and `y` hitting the level
`-a < 0` has the cone scale radius `R_b = e^{-τ}` at the level `γ⁻¹ log b = -a`, `τ` the first hit of `-a`
by `y`. The rescaling `radialRescale γ b` of `p` is the pair of the same form built from the increments of `y`
after `τ` and from the path `a + y(τ - ·) + z(· - τ)` (the reversal of `y` up to `τ`, glued to `z`).

* `coneE γ y z`: the pair `(y t + Q t, z s - Q s)`.
* `radScale_radialProcess_of_spec`: the scale radius of a radial process from its defining level property.
* `radialRescale_coneE_of_neg`: the computation.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set HarmonicBalls
open scoped NNReal ENNReal Classical

namespace MatedCRT.FirstPass.Derived

/-- The radial pair `(t ↦ y t + Q t, s ↦ z s - Q s)` with `Q = lqgQ γ`. -/
noncomputable def coneE (γ : ℝ) (y z : ℝ≥0 → ℝ) : RadialPair :=
  (fun t => y t + lqgQ γ * (t : ℝ), fun s => z s - lqgQ γ * (s : ℝ))

/-- The reading of a radial pair at the radius `e^x`. -/
lemma radLevel_exp (p : RadialPair) (x : ℝ) :
    radLevel p (Real.exp x) = if 0 ≤ x then p.2 (Real.toNNReal x) else p.1 (Real.toNNReal (-x)) := by
  unfold radLevel
  rw [Real.log_exp]
  by_cases hx : 0 ≤ x
  · have : 1 ≤ Real.exp x := Real.one_le_exp hx
    simp [hx, this]
  · have : ¬ 1 ≤ Real.exp x := by
      rw [not_le]
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.2 (not_le.1 hx)
    simp [hx, this]

/-- The scale radius of a radial process, from its defining level property (deterministic form of
`radScale_radialProcess_ae`). -/
lemma radScale_radialProcess_of_spec {γ b R : ℝ} {hc : ℝ → ℂ → ℝ}
    (hcont : ContinuousOn (fun q : ℝ × ℂ => hc q.1 q.2) (Ioi 0 ×ˢ univ)) (hR : 0 < R)
    (h1 : hc R 0 + lqgQ γ * Real.log R = γ⁻¹ * Real.log b)
    (h2 : ∀ r : ℝ, R < r → γ⁻¹ * Real.log b < hc r 0 + lqgQ γ * Real.log r) :
    radScale γ b (radialProcess hc) = R := by
  have key : ∀ q : ℚ, 0 ≤ (q : ℝ) →
      (radialProcess hc ∈ radWitness γ b q ↔ (q : ℝ) < R) := by
    intro q hq
    rw [radialProcess_mem_radWitness_iff γ b _ hq]
    exact (lt_scaleRadius_iff hcont h1 h2 hq).symm
  have hbdd : BddAbove (range fun q : ℚ =>
      if 0 ≤ (q : ℝ) ∧ radialProcess hc ∈ radWitness γ b q then (q : ℝ) else 0) := by
    refine ⟨R, ?_⟩
    rintro _ ⟨q, rfl⟩
    by_cases hq : 0 ≤ (q : ℝ) ∧ radialProcess hc ∈ radWitness γ b q
    · simp only [hq, and_self, ↓reduceIte]
      exact ((key q hq.1).1 hq.2).le
    · simp only [hq, ↓reduceIte]
      exact hR.le
  unfold radScale
  apply le_antisymm
  · refine ciSup_le fun q => ?_
    by_cases hq : 0 ≤ (q : ℝ) ∧ radialProcess hc ∈ radWitness γ b q
    · simp only [hq, and_self, ↓reduceIte]
      exact ((key q hq.1).1 hq.2).le
    · simp only [hq, ↓reduceIte]
      exact hR.le
  · by_contra hlt
    rw [not_le] at hlt
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (max_lt hlt hR)
    have hq0 : 0 ≤ (q : ℝ) := (le_max_right _ _).trans hq1.le
    have hqW : radialProcess hc ∈ radWitness γ b q := (key q hq0).2 hq2
    have hle := le_ciSup hbdd q
    have hterm : (if 0 ≤ (q : ℝ) ∧ radialProcess hc ∈ radWitness γ b q then (q : ℝ) else 0) = q := by
      simp only [hq0, hqW, and_self, ↓reduceIte]
    simp only [hterm] at hle
    exact absurd (hle.trans_lt ((le_max_left _ _).trans_lt hq1)) (lt_irrefl _)

/-- When the two paths of a radial pair start at the same value, its reading at a positive radius is a
sum of continuous functions of `log r`. -/
lemma radLevel_eq_add (p : RadialPair) (h0 : p.1 0 = p.2 0) {r : ℝ} (hr : 0 < r) :
    radLevel p r = p.2 (Real.toNNReal (Real.log r)) + p.1 (Real.toNNReal (-Real.log r)) - p.1 0 := by
  unfold radLevel
  by_cases h1 : 1 ≤ r
  · have hl : 0 ≤ Real.log r := Real.log_nonneg h1
    have : Real.toNNReal (-Real.log r) = 0 := Real.toNNReal_of_nonpos (by linarith)
    simp [h1, this]
  · have hl : Real.log r < 0 := Real.log_neg hr (not_le.1 h1)
    have : Real.toNNReal (Real.log r) = 0 := Real.toNNReal_of_nonpos hl.le
    simp [h1, this, h0]

lemma continuousOn_radLevel (p : RadialPair) (h0 : p.1 0 = p.2 0) (h1 : Continuous p.1)
    (h2 : Continuous p.2) : ContinuousOn (radLevel p) (Ioi 0) := by
  have hl : ContinuousOn Real.log (Ioi 0) :=
    Real.continuousOn_log.mono fun r hr => ne_of_gt hr
  have e : EqOn (radLevel p)
      (fun r => p.2 (Real.toNNReal (Real.log r)) + p.1 (Real.toNNReal (-Real.log r)) - p.1 0) (Ioi 0) :=
    fun r hr => radLevel_eq_add p h0 hr
  refine ContinuousOn.congr ?_ e
  exact ((h2.comp_continuousOn (continuous_real_toNNReal.comp_continuousOn hl)).add
    (h1.comp_continuousOn (continuous_real_toNNReal.comp_continuousOn hl.neg))).sub continuousOn_const

lemma radialProcess_radLevel (p : RadialPair) (h0 : p.1 0 = p.2 0) :
    radialProcess (fun r (_ : ℂ) => radLevel p r) = p := by
  refine Prod.ext (funext fun t => ?_) (funext fun s => ?_)
  · show radLevel p (Real.exp (-(t : ℝ))) = p.1 t
    rw [radLevel_exp p (-(t : ℝ))]
    by_cases ht : 0 ≤ -(t : ℝ)
    · have h : (t : ℝ) = 0 := le_antisymm (by linarith) t.2
      have : t = 0 := by exact_mod_cast h
      subst this
      simp [h0]
    · simp [ht]
  · show radLevel p (Real.exp (s : ℝ)) = p.2 s
    rw [radLevel_exp p (s : ℝ)]
    simp

/-- The scale radius of a radial pair whose two paths start at the same value and are continuous, from its
defining level property. -/
lemma radScale_of_spec (γ b : ℝ) (p : RadialPair) (h0 : p.1 0 = p.2 0) (h1 : Continuous p.1)
    (h2 : Continuous p.2) {R : ℝ} (hR : 0 < R)
    (hh1 : radLevel p R + lqgQ γ * Real.log R = γ⁻¹ * Real.log b)
    (hh2 : ∀ r : ℝ, R < r → γ⁻¹ * Real.log b < radLevel p r + lqgQ γ * Real.log r) :
    radScale γ b p = R := by
  have hcont : ContinuousOn (fun q : ℝ × ℂ => (fun r (_ : ℂ) => radLevel p r) q.1 q.2)
      (Ioi 0 ×ˢ univ) :=
    (continuousOn_radLevel p h0 h1 h2).comp continuousOn_fst fun q hq => hq.1
  have := radScale_radialProcess_of_spec (γ := γ) (b := b) (hc := fun r (_ : ℂ) => radLevel p r)
    hcont hR hh1 hh2
  rwa [radialProcess_radLevel p h0] at this

/-- **Rescaling the radial pair of a cone at a level `-a < 0`.**  If `y, z` are continuous paths started at `0`
with `z ≥ 0` and `y` hits `-a` (`a > 0`, `γ⁻¹ log b = -a`) at the time `τ`, then the rescaled radial pair of
`(y t + Q t, z s - Q s)` is the pair of the same form with `y` replaced by its increments after `τ` and `z`
replaced by the reversal of `y` up to `τ` glued to `z`. -/
theorem radialRescale_coneE_of_neg {γ b a : ℝ} (ha : 0 < a) (hab : γ⁻¹ * Real.log b = -a)
    {y z : C(ℝ≥0, ℝ)} (hy0 : y 0 = 0) (hz0 : z 0 = 0) (hz : ∀ s, 0 ≤ z s)
    (hT : LatticeProb.hitFrom (-a) 0 (y : ℝ≥0 → ℝ) ≠ ⊤) :
    radialRescale γ b (coneE γ y z) =
      coneE γ (LatticeProb.shiftPath (LatticeProb.glueTime a (y : ℝ≥0 → ℝ)) y)
        (LatticeProb.glueC a y z) := by
  set τ := LatticeProb.glueTime a (y : ℝ≥0 → ℝ) with hτdef
  obtain ⟨s0, hs0, -, hys0, hmin⟩ := LatticeProb.exists_hitFrom_eq y.continuous hT
  have hτ : τ = s0 := by simp [hτdef, LatticeProb.glueTime, hs0]
  have hyτ : y τ = -a := by rw [hτ]; exact hys0
  have hτpos : 0 < τ := by
    rcases (zero_le : (0 : ℝ≥0) ≤ τ).eq_or_lt with h | h
    · exfalso
      rw [← h, hy0] at hyτ
      linarith
    · exact h
  have hlt : ∀ t : ℝ≥0, t < τ → -a < y t := by
    intro t ht
    by_contra hle
    rw [not_lt] at hle
    obtain ⟨s, hs, hys⟩ := intermediate_value_Icc' (zero_le : (0 : ℝ≥0) ≤ t) y.continuous.continuousOn
      (show -a ∈ Icc (y t) (y 0) from ⟨hle, by rw [hy0]; linarith⟩)
    have h1 : s0 ≤ s := hmin s zero_le hys
    have h2 : τ ≤ s := by rw [hτ]; exact h1
    exact absurd (lt_of_lt_of_le ht (h2.trans hs.2)) (lt_irrefl _)
  set p : RadialPair := coneE γ y z with hp
  have hp0 : p.1 0 = p.2 0 := by simp [hp, coneE, hy0, hz0]
  have hp1 : Continuous p.1 := by
    simp only [hp, coneE]
    exact y.continuous.add (continuous_const.mul NNReal.continuous_coe)
  have hp2 : Continuous p.2 := by
    simp only [hp, coneE]
    exact z.continuous.sub (continuous_const.mul NNReal.continuous_coe)
  set R : ℝ := Real.exp (-(τ : ℝ)) with hRdef
  have hR : 0 < R := Real.exp_pos _
  have hlogR : Real.log R = -(τ : ℝ) := Real.log_exp _
  have hscale : radScale γ b p = R := by
    refine radScale_of_spec γ b p hp0 hp1 hp2 hR ?_ ?_
    · have hneg : ¬ 0 ≤ -(τ : ℝ) := by
        have : (0 : ℝ) < τ := by exact_mod_cast hτpos
        linarith
      rw [hRdef, radLevel_exp, hab, hlogR]
      simp only [hneg, ↓reduceIte, hp, coneE, neg_neg, Real.toNNReal_coe, hyτ]
      ring
    · intro r hr
      have hr0 : 0 < r := hR.trans hr
      have hx : -(τ : ℝ) < Real.log r := by
        rw [Real.lt_log_iff_exp_lt hr0]
        exact hr
      have hrx : r = Real.exp (Real.log r) := (Real.exp_log hr0).symm
      rw [hab]
      conv_lhs => skip
      rw [hrx, radLevel_exp, Real.log_exp]
      by_cases hx0 : 0 ≤ Real.log r
      · simp only [hx0, ↓reduceIte]
        simp only [hp, coneE, Real.coe_toNNReal _ hx0]
        have := hz (Real.toNNReal (Real.log r))
        linarith
      · simp only [hx0, ↓reduceIte]
        have hx1 : 0 ≤ -Real.log r := by linarith [not_le.1 hx0]
        simp only [hp, coneE, Real.coe_toNNReal _ hx1]
        have hu : Real.toNNReal (-Real.log r) < τ := by
          rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hx1]
          linarith
        have := hlt _ hu
        linarith
  have hcontAt : ∀ x : ℝ, 0 < x → ContinuousAt (radLevel p) x := fun x hx =>
    (continuousOn_radLevel p hp0 hp1 hp2).continuousAt (Ioi_mem_nhds hx)
  have hread : ∀ x : ℝ, 0 < x → radRead (fun p' => radScale γ b p' * x) p = radLevel p (R * x) := by
    intro x hx
    have e : radRead (fun p' => radScale γ b p' * x) p = radRead (fun _ => R * x) p := by
      simp only [radRead, hscale]
    rw [e]
    exact radRead_const_of_continuousAt (mul_pos hR hx) (hcontAt _ (mul_pos hR hx))
  have hτr : (0 : ℝ) < τ := by exact_mod_cast hτpos
  refine Prod.ext (funext fun t => ?_) (funext fun s => ?_)
  · have lhs : (radialRescale γ b p).1 t =
        radLevel p (R * Real.exp (-(t : ℝ))) + lqgQ γ * Real.log R - γ⁻¹ * Real.log b := by
      show radRead (fun p' => radScale γ b p' * Real.exp (-(t : ℝ))) p +
        lqgQ γ * Real.log (radScale γ b p) - γ⁻¹ * Real.log b = _
      rw [hread _ (Real.exp_pos _), hscale]
    have hexp : R * Real.exp (-(t : ℝ)) = Real.exp (-((τ + t : ℝ≥0) : ℝ)) := by
      rw [hRdef, ← Real.exp_add]
      congr 1
      push_cast
      ring
    have hneg : ¬ 0 ≤ -((τ + t : ℝ≥0) : ℝ) := by
      push_cast
      have := t.2
      intro h
      linarith
    rw [lhs, hexp, radLevel_exp, hlogR]
    simp only [hneg, ↓reduceIte, hp, coneE, neg_neg, Real.toNNReal_coe,
      LatticeProb.shiftPath_apply, hab, hyτ]
    push_cast
    ring
  · have lhs : (radialRescale γ b p).2 s =
        radLevel p (R * Real.exp (s : ℝ)) + lqgQ γ * Real.log R - γ⁻¹ * Real.log b := by
      show radRead (fun p' => radScale γ b p' * Real.exp (s : ℝ)) p +
        lqgQ γ * Real.log (radScale γ b p) - γ⁻¹ * Real.log b = _
      rw [hread _ (Real.exp_pos _), hscale]
    have hexp : R * Real.exp (s : ℝ) = Real.exp ((s : ℝ) - τ) := by
      rw [hRdef, ← Real.exp_add]
      congr 1
      ring
    rw [lhs, hexp, radLevel_exp, hlogR]
    by_cases hs : τ ≤ s
    · have h1 : 0 ≤ (s : ℝ) - τ := sub_nonneg.2 (by exact_mod_cast hs)
      have h2 : Real.toNNReal ((s : ℝ) - τ) = s - τ := by
        rw [← NNReal.coe_sub hs, Real.toNNReal_coe]
      have hg := LatticeProb.glueC_apply_of_ge (a := a) (y := y) (z := z) hy0 hs
      simp only [h1, ↓reduceIte, hp, coneE, h2, hab]
      rw [hg]
      rw [NNReal.coe_sub hs]
      ring
    · have hs' : s < τ := not_le.1 hs
      have h1 : ¬ 0 ≤ (s : ℝ) - τ := by
        have : (s : ℝ) < τ := by exact_mod_cast hs'
        intro h
        linarith
      have h2 : Real.toNNReal (-((s : ℝ) - τ)) = τ - s := by
        rw [neg_sub, ← NNReal.coe_sub hs'.le, Real.toNNReal_coe]
      have hg := LatticeProb.glueC_apply_of_le (a := a) (y := y) (z := z) hs'.le
      rw [hz0] at hg
      simp only [h1, ↓reduceIte, hp, coneE, h2, hab]
      rw [hg]
      rw [NNReal.coe_sub hs'.le]
      ring

end MatedCRT.FirstPass.Derived
