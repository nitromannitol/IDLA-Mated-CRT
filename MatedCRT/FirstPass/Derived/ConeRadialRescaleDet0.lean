import MatedCRT.FirstPass.Derived.ConeRadialRescaleDet

/-!
# Rescaling a radial pair at the level of its starting value: the deterministic computation

If `y, z` are continuous paths started at `0` with `z > 0` on `(0, ∞)` and `γ⁻¹ log b = 0`, the cone scale radius
at the level `0` is `1`, and the rescaling `radialRescale γ b` fixes the radial pair `(y t + Q t, z s - Q s)`
(`radialRescale_coneE_of_zero`).
-/

open MeasureTheory ProbabilityTheory Filter Topology Set HarmonicBalls
open scoped NNReal ENNReal Classical

namespace MatedCRT.FirstPass.Derived

/-- **Rescaling the radial pair of a cone at the level `0`.**  If `y, z` are continuous paths started at `0`
with `z > 0` on `(0, ∞)` and `γ⁻¹ log b = 0`, then `radialRescale γ b` fixes `(y t + Q t, z s - Q s)`. -/
theorem radialRescale_coneE_of_zero {γ b : ℝ} (hb : γ⁻¹ * Real.log b = 0)
    {y z : C(ℝ≥0, ℝ)} (hy0 : y 0 = 0) (hz0 : z 0 = 0) (hzpos : ∀ s : ℝ≥0, 0 < s → 0 < z s) :
    radialRescale γ b (coneE γ y z) = coneE γ y z := by
  set p : RadialPair := coneE γ y z with hp
  have hp0 : p.1 0 = p.2 0 := by simp [hp, coneE, hy0, hz0]
  have hp1 : Continuous p.1 := by
    simp only [hp, coneE]
    exact y.continuous.add (continuous_const.mul NNReal.continuous_coe)
  have hp2 : Continuous p.2 := by
    simp only [hp, coneE]
    exact z.continuous.sub (continuous_const.mul NNReal.continuous_coe)
  have hscale : radScale γ b p = 1 := by
    refine radScale_of_spec γ b p hp0 hp1 hp2 one_pos ?_ ?_
    · have h1 : radLevel p 1 = p.2 0 := by simpa using radLevel_exp p 0
      rw [h1, hb, Real.log_one]
      simp [hp, coneE, hz0]
    · intro r hr
      have hr0 : 0 < r := one_pos.trans hr
      have hx : 0 < Real.log r := Real.log_pos hr
      have hrx : r = Real.exp (Real.log r) := (Real.exp_log hr0).symm
      rw [hb]
      rw [hrx, radLevel_exp, Real.log_exp]
      simp only [hx.le, ↓reduceIte, hp, coneE, Real.coe_toNNReal _ hx.le]
      have := hzpos (Real.toNNReal (Real.log r)) (Real.toNNReal_pos.2 hx)
      linarith
  have hcontAt : ∀ x : ℝ, 0 < x → ContinuousAt (radLevel p) x := fun x hx =>
    (continuousOn_radLevel p hp0 hp1 hp2).continuousAt (Ioi_mem_nhds hx)
  have hread : ∀ x : ℝ, 0 < x → radRead (fun p' => radScale γ b p' * x) p = radLevel p x := by
    intro x hx
    have e : radRead (fun p' => radScale γ b p' * x) p = radRead (fun _ => x) p := by
      simp only [radRead, hscale, one_mul]
    rw [e]
    exact radRead_const_of_continuousAt hx (hcontAt _ hx)
  refine Prod.ext (funext fun t => ?_) (funext fun s => ?_)
  · have lhs : (radialRescale γ b p).1 t = radLevel p (Real.exp (-(t : ℝ))) := by
      show radRead (fun p' => radScale γ b p' * Real.exp (-(t : ℝ))) p +
        lqgQ γ * Real.log (radScale γ b p) - γ⁻¹ * Real.log b = _
      rw [hread _ (Real.exp_pos _), hscale, hb, Real.log_one]
      ring
    rw [lhs, radLevel_exp p (-(t : ℝ))]
    by_cases ht : 0 ≤ -(t : ℝ)
    · have h : (t : ℝ) = 0 := le_antisymm (by linarith) t.2
      have : t = 0 := by exact_mod_cast h
      subst this
      simp [hp0]
    · simp [ht]
  · have lhs : (radialRescale γ b p).2 s = radLevel p (Real.exp (s : ℝ)) := by
      show radRead (fun p' => radScale γ b p' * Real.exp (s : ℝ)) p +
        lqgQ γ * Real.log (radScale γ b p) - γ⁻¹ * Real.log b = _
      rw [hread _ (Real.exp_pos _), hscale, hb, Real.log_one]
      ring
    rw [lhs, radLevel_exp p (s : ℝ)]
    simp

end MatedCRT.FirstPass.Derived
