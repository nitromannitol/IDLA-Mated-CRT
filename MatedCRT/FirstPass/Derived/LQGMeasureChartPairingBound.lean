import MatedCRT.FirstPass.Derived.LQGMeasureChartVariableScale

/-!
# The pairing bound for the smooth approximations from the local regularity of the field

A distribution `g` on the disc `B(c, r)` with the local negative regularity in test-function form (the conclusion of
`ZeroBoundaryGFFLocalRegularity` for one field: on every compact `K ⊆ B(c, r)` and for every `α < 0`, the pairings
with `t⁻² η((· − x)/t)`, `x ∈ K`, `η` smooth with support in the unit disc and `|η|, ‖Dη‖ ≤ 1`, are at most `C t^α` for
small `t`; De Nitti–Schweiger, arXiv:2301.13781v4, Proposition 2.1, p. 9) satisfies, for a bump function `f` of
Sheffield–Wang (arXiv:1605.06171v2, p. 2 and (3.3)), the bound `|⟨g, f_ε(z − ·)⟩| ≤ C ε^α` on compact subsets of the
disc at small scales: by radiality `f_ε(z − ·) = ε⁻² f((· − z)/ε)`, and `f / M` is an admissible profile when `M`
bounds `|f|`, `‖Df‖` and `1`.

* `pairFun_smul`: `⟨g, a u⟩ = a ⟨g, u⟩` for every function `u` (both sides vanish when `u` is not an admissible test).
* `exists_abs_pairFun_mollScale_le`: the pairing bound.
* `isVagueLimitOn_varScaleApprox_of_regularity`: the convergence of the smooth approximations at the variable source
  radius `2^{-k} b(z)` (`isVagueLimitOn_varScaleApprox_one_third`, the envelope argument at the end of the proof of
  Sheffield–Wang, Theorem 1.2, p. 11, for the bumps `f` and `f_{1/3}`), for the field `g` on `B(c, r)`, with the
  finiteness of the envelopes obtained from the local regularity.
-/

set_option autoImplicit false

noncomputable section

open scoped Classical

open MeasureTheory Filter Topology Set Metric

namespace MatedCRT

namespace LQGMeasureChart

/-- **Homogeneity of the pairing**: `⟨g, a u⟩ = a ⟨g, u⟩`. When `u` is a smooth function with compact support in `V`
this is the linearity of `g`; otherwise both sides vanish (for `a = 0` the left side is the pairing with the zero test
function). -/
theorem pairFun_smul {V : TopologicalSpace.Opens ℂ} (g : LQGMetric.DistOn V) (a : ℝ) (u : ℂ → ℝ) :
    pairFun g (fun w => a * u w) = a * pairFun g u := by
  by_cases hu : ContDiff ℝ (⊤ : ℕ∞) u ∧ HasCompactSupport u ∧ tsupport u ⊆ V
  · have h' : ContDiff ℝ (⊤ : ℕ∞) (fun w => a * u w) ∧ HasCompactSupport (fun w => a * u w) ∧
        tsupport (fun w => a * u w) ⊆ V :=
      ⟨contDiff_const.mul hu.1, hu.2.1.mul_left, tsupport_mul_subset_right.trans hu.2.2⟩
    unfold pairFun
    rw [dite_eq_left h', dite_eq_left hu, ← smul_eq_mul, ← map_smul]
    rfl
  · by_cases ha : a = 0
    · subst ha
      simp only [zero_mul]
      have h0 : ContDiff ℝ (⊤ : ℕ∞) (fun _ : ℂ => (0 : ℝ)) ∧ HasCompactSupport (fun _ : ℂ => (0 : ℝ)) ∧
          tsupport (fun _ : ℂ => (0 : ℝ)) ⊆ V :=
        ⟨contDiff_const, HasCompactSupport.intro isCompact_empty fun _ _ => rfl,
          (closure_minimal (fun _ hx => (hx rfl).elim) isClosed_empty).trans (empty_subset _)⟩
      unfold pairFun
      rw [dite_eq_left h0]
      have h00 : (⟨fun _ => 0, h0.1, h0.2.1, h0.2.2⟩ : LQGMetric.TestOn V) = 0 :=
        TestFunction.ext fun _ => rfl
      rw [h00, map_zero]
    · have hu' : ¬(ContDiff ℝ (⊤ : ℕ∞) (fun w => a * u w) ∧ HasCompactSupport (fun w => a * u w) ∧
          tsupport (fun w => a * u w) ⊆ V) := by
        rintro ⟨h1, h2, h3⟩
        have e : u = fun w => a⁻¹ * (a * u w) := funext fun w => by rw [← mul_assoc, inv_mul_cancel₀ ha, one_mul]
        apply hu
        rw [e]
        exact ⟨contDiff_const.mul h1, h2.mul_left, tsupport_mul_subset_right.trans h3⟩
      unfold pairFun
      rw [dite_eq_right hu', dite_eq_right hu, mul_zero]

/-- **The pairing bound from the local regularity**: if `g` has the local negative regularity of
`ZeroBoundaryGFFLocalRegularity` (for one field), then for a bump function `f`, every `α < 0` and every compact
`K ⊆ B(c, r)`, the pairings `⟨g, f_ε(z − ·)⟩`, `z ∈ K`, are at most `C ε^α` for `0 < ε ≤ ε₀`. -/
theorem exists_abs_pairFun_mollScale_le {c : ℂ} {r : ℝ} {g : LQGMetric.DistOn (disc c r)}
    (hreg : ∀ α : ℝ, α < 0 → ∀ K : Set ℂ, IsCompact K → K ⊆ ball c r →
      ∃ C t₀ : ℝ, 0 < t₀ ∧ ∀ x ∈ K, ∀ t ∈ Ioc 0 t₀, ∀ η : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) η →
        tsupport η ⊆ ball 0 1 → (∀ z, |η z| ≤ 1) → (∀ z, ‖fderiv ℝ η z‖ ≤ 1) →
        |pairFun g (fun y => (t ^ 2)⁻¹ * η ((y - x) / (t : ℂ)))| ≤ C * t ^ α)
    {f : ℂ → ℝ} (hf : IsMollifier f) {α : ℝ} (hα : α < 0) {K : Set ℂ} (hK : IsCompact K)
    (hKD : K ⊆ ball c r) :
    ∃ C ε₀ : ℝ, 0 < ε₀ ∧ ∀ z ∈ K, ∀ ε ∈ Ioc 0 ε₀,
      |pairFun g (fun w => mollScale f ε (z - w))| ≤ C * ε ^ α := by
  obtain ⟨M₀, hM₀⟩ := hf.contDiff.continuous.bounded_above_of_compact_support hf.hasCompactSupport
  obtain ⟨M₁, hM₁⟩ := (hf.contDiff.continuous_fderiv (by simp)).bounded_above_of_compact_support
    (hf.hasCompactSupport.fderiv (𝕜 := ℝ))
  set M : ℝ := max 1 (max M₀ M₁)
  have hMpos : 0 < M := one_pos.trans_le (le_max_left _ _)
  set η : ℂ → ℝ := fun v => M⁻¹ * f v with hη
  have hηc : ContDiff ℝ (⊤ : ℕ∞) η := contDiff_const.mul hf.contDiff
  have hηs : tsupport η ⊆ ball 0 1 := tsupport_mul_subset_right.trans hf.tsupport_subset
  have hηb : ∀ v, |η v| ≤ 1 := fun v => by
    simp only [hη, abs_mul, abs_inv, abs_of_pos hMpos]
    rw [inv_mul_le_iff₀ hMpos, mul_one]
    have h := hM₀ v
    rw [Real.norm_eq_abs] at h
    exact h.trans ((le_max_left _ _).trans (le_max_right _ _))
  have hηd : ∀ v, ‖fderiv ℝ η v‖ ≤ 1 := fun v => by
    have h : fderiv ℝ η v = M⁻¹ • fderiv ℝ f v :=
      fderiv_const_mul (hf.contDiff.differentiable (by simp) v) M⁻¹
    rw [h, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hMpos, inv_mul_le_iff₀ hMpos, mul_one]
    exact (hM₁ v).trans ((le_max_right _ _).trans (le_max_right _ _))
  obtain ⟨C, t₀, ht₀, hC⟩ := hreg α hα K hK hKD
  refine ⟨M * C, t₀, ht₀, fun z hz ε hε => ?_⟩
  have heq : (fun w => mollScale f ε (z - w)) = fun w => M * ((ε ^ 2)⁻¹ * η ((w - z) / (ε : ℂ))) := by
    funext w
    simp only [mollScale, hη]
    rw [hf.radial ((z - w) / (ε : ℂ)) ((w - z) / (ε : ℂ)) (by rw [norm_div, norm_div, norm_sub_rev])]
    have hMM : M * M⁻¹ = 1 := mul_inv_cancel₀ hMpos.ne'
    calc (ε ^ 2)⁻¹ * f ((w - z) / (ε : ℂ)) = (ε ^ 2)⁻¹ * f ((w - z) / (ε : ℂ)) * (M * M⁻¹) := by
          rw [hMM, mul_one]
      _ = M * ((ε ^ 2)⁻¹ * (M⁻¹ * f ((w - z) / (ε : ℂ)))) := by ring
  rw [heq, pairFun_smul, abs_mul, abs_of_pos hMpos, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hC z hz ε hε η hηc hηs hηb hηd) hMpos.le

/-- **Variable source radii for a field with the local regularity**: `isVagueLimitOn_varScaleApprox_one_third` for
`G = pairFun g` on `D = B(c, r)`, with the finiteness of the upper envelopes derived from the local negative
regularity of `g` (the conclusion of `ZeroBoundaryGFFLocalRegularity` for one field) through
`exists_abs_pairFun_mollScale_le` with `α = -1/2`. -/
theorem isVagueLimitOn_varScaleApprox_of_regularity {γ : ℝ} {f : ℂ → ℝ} {c : ℂ} {r : ℝ}
    {g : LQGMetric.DistOn (disc c r)} {μ : Measure ℂ} {u l u' l' : ℕ → ℝ} (hf : IsMollifier f)
    (hu : ∀ N, 0 < u N) (hl : ∀ N, 0 < l N) (hu' : ∀ N, 0 < u' N) (hl' : ∀ N, 0 < l' N)
    (hu1 : Tendsto u atTop (𝓝 1)) (hl1 : Tendsto l atTop (𝓝 1))
    (hu1' : Tendsto u' atTop (𝓝 1)) (hl1' : Tendsto l' atTop (𝓝 1))
    (hsup : ∀ N : ℕ, 1 ≤ N → QuantumZipper.IsVagueLimitOn (ball c r)
      (fun j => envSup γ f (ball c r) (pairFun g) N j) (ENNReal.ofReal (u N) • μ))
    (hinf : ∀ N : ℕ, 1 ≤ N → QuantumZipper.IsVagueLimitOn (ball c r)
      (fun j => envInf γ f (ball c r) (pairFun g) N j) (ENNReal.ofReal (l N) • μ))
    (hsup' : ∀ N : ℕ, 1 ≤ N → QuantumZipper.IsVagueLimitOn (ball c r)
      (fun j => envSup γ (mollDilate (1 / 3) f) (ball c r) (pairFun g) N j) (ENNReal.ofReal (u' N) • μ))
    (hinf' : ∀ N : ℕ, 1 ≤ N → QuantumZipper.IsVagueLimitOn (ball c r)
      (fun j => envInf γ (mollDilate (1 / 3) f) (ball c r) (pairFun g) N j) (ENNReal.ofReal (l' N) • μ))
    (hreg : ∀ α : ℝ, α < 0 → ∀ K : Set ℂ, IsCompact K → K ⊆ ball c r →
      ∃ C t₀ : ℝ, 0 < t₀ ∧ ∀ x ∈ K, ∀ t ∈ Ioc 0 t₀, ∀ η : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) η →
        tsupport η ⊆ ball 0 1 → (∀ z, |η z| ≤ 1) → (∀ z, ‖fderiv ℝ η z‖ ≤ 1) →
        |pairFun g (fun y => (t ^ 2)⁻¹ * η ((y - x) / (t : ℂ)))| ≤ C * t ^ α)
    {b : ℂ → ℝ} (hb : ContinuousOn b (ball c r)) (hbpos : ∀ z ∈ ball c r, 0 < b z) :
    QuantumZipper.IsVagueLimitOn (ball c r) (varScaleApprox γ f (ball c r) (pairFun g) b) μ :=
  isVagueLimitOn_varScaleApprox_one_third isOpen_ball hf hu hl hu' hl' hu1 hl1 hu1' hl1' hsup hinf hsup' hinf'
    (fun K hK hKD => by
      obtain ⟨C, ε₀, hε₀, h⟩ :=
        exists_abs_pairFun_mollScale_le hreg hf (by norm_num : (-1 / 2 : ℝ) < 0) hK hKD
      exact ⟨C, ε₀, -1 / 2, hε₀, h⟩) hb hbpos

end LQGMeasureChart

end MatedCRT
