import MatedCRT.FirstPass.Derived.ConeRadialRescaleDet

/-!
# Rescaling a radial pair at a level above its starting value: the inverse of the rescaling below

If `y` hits `-a` at the time `τ`, the radial pair `(y' t + Q t, z' s - Q s)` of the increments `y'` of `y` after `τ`
and of the glued path `z' = a + y(τ - ·) + z(· - τ)` has the cone scale radius `e^{τ}` at the level
`γ⁻¹ log b = a > 0`, and its rescaling is the pair `(y t + Q t, z s - Q s)` of `y` and `z`
(`radialRescale_coneE_inverse`): it inverts `radialRescale_coneE_of_neg`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set HarmonicBalls
open scoped NNReal ENNReal Classical

namespace MatedCRT.FirstPass.Derived

/-- **Rescaling the radial pair of a glued cone at the level `a > 0`.**  If `y, z` are continuous paths started at
`0`, `z > 0` on `(0, ∞)`, `y` hits `-a` at the time `τ` and `γ⁻¹ log b = a`, then `radialRescale γ b` maps the pair
built from the increments of `y` after `τ` and the glued path of `y` and `z` back to `(y t + Q t, z s - Q s)`. -/
theorem radialRescale_coneE_inverse {γ b a : ℝ} (_ha : 0 < a) (hab : γ⁻¹ * Real.log b = a)
    {y z : C(ℝ≥0, ℝ)} (hy0 : y 0 = 0) (hz0 : z 0 = 0) (hzpos : ∀ s : ℝ≥0, 0 < s → 0 < z s)
    (hT : LatticeProb.hitFrom (-a) 0 (y : ℝ≥0 → ℝ) ≠ ⊤) :
    radialRescale γ b (coneE γ (LatticeProb.restartAt (LatticeProb.glueTime a (y : ℝ≥0 → ℝ)) y)
        (LatticeProb.glueC a y z)) = coneE γ y z := by
  set τ := LatticeProb.glueTime a (y : ℝ≥0 → ℝ) with hτdef
  obtain ⟨s0, hs0, -, hys0, -⟩ := LatticeProb.exists_hitFrom_eq y.continuous hT
  have hτ : τ = s0 := by simp [hτdef, LatticeProb.glueTime, hs0]
  have hyτ : y τ = -a := by rw [hτ]; exact hys0
  set y' := LatticeProb.restartAt τ y with hy'
  set z' := LatticeProb.glueC a y z with hz'
  set p : RadialPair := coneE γ y' z' with hp
  have hy'0 : y' 0 = 0 := by simp [hy']
  have hz'0 : z' 0 = 0 := LatticeProb.glueC_zero hT hz0
  have hp0 : p.1 0 = p.2 0 := by simp [hp, coneE, hy'0, hz'0]
  have hp1 : Continuous p.1 := by
    simp only [hp, coneE]
    exact y'.continuous.add (continuous_const.mul NNReal.continuous_coe)
  have hp2 : Continuous p.2 := by
    simp only [hp, coneE]
    exact z'.continuous.sub (continuous_const.mul NNReal.continuous_coe)
  have hz'τ : z' τ = a := by
    have := LatticeProb.glueC_apply_of_le (a := a) (y := y) (z := z) (s := τ) le_rfl
    rw [← hτdef, tsub_self, hy0, hz0] at this
    rw [hz', this]
    ring
  have hz'ge : ∀ s : ℝ≥0, τ ≤ s → z' s = a + z (s - τ) := fun s hs =>
    LatticeProb.glueC_apply_of_ge (a := a) (y := y) (z := z) hy0 hs
  have hz'le : ∀ s : ℝ≥0, s ≤ τ → z' s = a + y (τ - s) := fun s hs => by
    have := LatticeProb.glueC_apply_of_le (a := a) (y := y) (z := z) (s := s) hs
    rw [← hτdef, hz0] at this
    rw [hz', this]
    ring
  set R : ℝ := Real.exp (τ : ℝ) with hRdef
  have hR : 0 < R := Real.exp_pos _
  have hlogR : Real.log R = (τ : ℝ) := Real.log_exp _
  have hscale : radScale γ b p = R := by
    refine radScale_of_spec γ b p hp0 hp1 hp2 hR ?_ ?_
    · have hnn : 0 ≤ (τ : ℝ) := τ.2
      rw [hRdef, radLevel_exp, hab, hlogR]
      simp only [hnn, ↓reduceIte, hp, coneE, Real.toNNReal_coe, hz'τ]
      ring
    · intro r hr
      have hr0 : 0 < r := hR.trans hr
      have hx : (τ : ℝ) < Real.log r := by
        rw [Real.lt_log_iff_exp_lt hr0]
        exact hr
      have hx0 : 0 ≤ Real.log r := (τ.2).trans hx.le
      have hrx : r = Real.exp (Real.log r) := (Real.exp_log hr0).symm
      rw [hab]
      rw [hrx, radLevel_exp, Real.log_exp]
      simp only [hx0, ↓reduceIte]
      simp only [hp, coneE, Real.coe_toNNReal _ hx0]
      have hτs : τ ≤ Real.toNNReal (Real.log r) := by
        rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hx0]
        exact hx.le
      have hpos : 0 < Real.toNNReal (Real.log r) - τ := by
        rw [tsub_pos_iff_lt, ← NNReal.coe_lt_coe, Real.coe_toNNReal _ hx0]
        exact hx
      rw [hz'ge _ hτs]
      have := hzpos _ hpos
      linarith
  have hcontAt : ∀ x : ℝ, 0 < x → ContinuousAt (radLevel p) x := fun x hx =>
    (continuousOn_radLevel p hp0 hp1 hp2).continuousAt (Ioi_mem_nhds hx)
  have hread : ∀ x : ℝ, 0 < x → radRead (fun p' => radScale γ b p' * x) p = radLevel p (R * x) := by
    intro x hx
    have e : radRead (fun p' => radScale γ b p' * x) p = radRead (fun _ => R * x) p := by
      simp only [radRead, hscale]
    rw [e]
    exact radRead_const_of_continuousAt (mul_pos hR hx) (hcontAt _ (mul_pos hR hx))
  refine Prod.ext (funext fun t => ?_) (funext fun s => ?_)
  · have lhs : (radialRescale γ b p).1 t =
        radLevel p (R * Real.exp (-(t : ℝ))) + lqgQ γ * Real.log R - γ⁻¹ * Real.log b := by
      show radRead (fun p' => radScale γ b p' * Real.exp (-(t : ℝ))) p +
        lqgQ γ * Real.log (radScale γ b p) - γ⁻¹ * Real.log b = _
      rw [hread _ (Real.exp_pos _), hscale]
    have hexp : R * Real.exp (-(t : ℝ)) = Real.exp ((τ : ℝ) - t) := by
      rw [hRdef, ← Real.exp_add]
      congr 1
    rw [lhs, hexp, radLevel_exp, hlogR, hab]
    by_cases ht : t ≤ τ
    · have h1 : 0 ≤ (τ : ℝ) - t := sub_nonneg.2 (by exact_mod_cast ht)
      have h2 : Real.toNNReal ((τ : ℝ) - t) = τ - t := by
        rw [← NNReal.coe_sub ht, Real.toNNReal_coe]
      simp only [h1, ↓reduceIte, hp, coneE, h2]
      rw [hz'le _ tsub_le_self, tsub_tsub_cancel_of_le ht, NNReal.coe_sub ht]
      ring
    · have ht' : τ < t := not_le.1 ht
      have h1 : ¬ 0 ≤ (τ : ℝ) - t := by
        have : (τ : ℝ) < t := by exact_mod_cast ht'
        intro h
        linarith
      have h2 : Real.toNNReal (-((τ : ℝ) - t)) = t - τ := by
        rw [neg_sub, ← NNReal.coe_sub ht'.le, Real.toNNReal_coe]
      simp only [h1, ↓reduceIte, hp, coneE, h2, hy', LatticeProb.restartAt_apply]
      rw [add_tsub_cancel_of_le ht'.le, hyτ, NNReal.coe_sub ht'.le]
      ring
  · have lhs : (radialRescale γ b p).2 s =
        radLevel p (R * Real.exp (s : ℝ)) + lqgQ γ * Real.log R - γ⁻¹ * Real.log b := by
      show radRead (fun p' => radScale γ b p' * Real.exp (s : ℝ)) p +
        lqgQ γ * Real.log (radScale γ b p) - γ⁻¹ * Real.log b = _
      rw [hread _ (Real.exp_pos _), hscale]
    have hexp : R * Real.exp (s : ℝ) = Real.exp ((τ + s : ℝ≥0) : ℝ) := by
      rw [hRdef, ← Real.exp_add]
      push_cast
      rfl
    have h1 : 0 ≤ ((τ + s : ℝ≥0) : ℝ) := NNReal.coe_nonneg _
    rw [lhs, hexp, radLevel_exp, hlogR, hab]
    simp only [h1, ↓reduceIte, hp, coneE, Real.toNNReal_coe]
    rw [hz'ge _ le_self_add, add_tsub_cancel_left]
    push_cast
    ring

end MatedCRT.FirstPass.Derived
