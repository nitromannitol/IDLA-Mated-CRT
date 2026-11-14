import MatedCRT.FirstPass.Derived.StopAtExitCmpContinuity

/-!
# Quantitative continuity of the stopping map modulo time parametrization

`MatedCRT.StopAtExitCmp.cmpEDist_stopAtExit_lt_of_frequently` shows that `g ↦ stopAtExit U g` is continuous at a
continuous path `f` which exits `U` regularly, for the distance `cmpEDist` of curves modulo time parametrization.
Here the modulus is explicit. Let `f` leave `U` at the time `τ` and suppose that, for some `η > 0`, `d > 0`, `ε`
and `T`,

* `f` has oscillation at most `ε` at scale `η` on `[0, T]`;
* some time `s ∈ (τ, τ + η)` with `s ≤ T` has the open ball of radius `d` about `f s` outside `U`;
* the open balls of radius `d` about `f t` lie in `U` for every `t` with `t + η / 2 ≤ τ`.

Then every path `g` (no regularity needed) with `cmpEDist g f < min ε d` satisfies
`cmpEDist (stopAtExit U g) (stopAtExit U f) ≤ 2 ε`.

The three conditions involve only the values of `f` and its exit time, so for random paths they define events
whose probability can be estimated; the quantitative form is the step from the almost sure continuity of the
stopping map at Brownian paths to bounds uniform in the starting point, as needed for the uniform-start invariance
principle `MatedCRT.GMS21UniformStartInput`.

## Main statements

* `MatedCRT.StopAtExitCmp.cmpEDist_stopAtExit_le_of_modulus`: the quantitative continuity.
* `MatedCRT.StopAtExitCmp.cmpEDist_stopAtExit_lt_of_modulus`: the same with a strict bound `< 3 ε` for `ε > 0`.
-/

open Set Filter Topology Metric HarmonicBalls
open scoped ENNReal NNReal

namespace MatedCRT.StopAtExitCmp

/-- **Quantitative continuity of the stopped path modulo time parametrization.** Let `f` leave `U` at the time `τ`.
Suppose that `f` has oscillation at most `ε` at scale `η > 0` on `[0, T]`, that some time `s ∈ (τ, τ + η)` with
`s ≤ T` has the open `d`-ball about `f s` outside `U`, and that the open `d`-balls about `f t` lie in `U` whenever
`t + η / 2 ≤ τ`. Then every path `g` within curve distance `min ε d` of `f` has, once stopped at its own exit time
from `U`, curve distance at most `2 ε` from `f` stopped at `τ`. -/
theorem cmpEDist_stopAtExit_le_of_modulus {U : Set ℂ} {f g : ℝ≥0 → ℂ} {τ s η T : ℝ≥0} {ε d : ℝ}
    (hτ : pathExitTime U f = τ) (hη : 0 < η)
    (hmod : ∀ t ≤ T, ∀ t' ≤ T, dist t t' < η → dist (f t) (f t') ≤ ε)
    (hs : s ∈ Ioo τ (τ + η)) (hsT : s ≤ T)
    (hout : ∀ w, dist w (f s) < d → w ∉ U)
    (hin : ∀ t, t + η / 2 ≤ τ → ∀ w, dist w (f t) < d → w ∈ U)
    (hg : cmpEDist g f < ENNReal.ofReal (min ε d)) :
    cmpEDist (stopAtExit U g) (stopAtExit U f) ≤ ENNReal.ofReal (2 * ε) := by
  have hfin : pathExitTime U f ≠ ⊤ := by
    rw [hτ]
    exact ENNReal.coe_ne_top
  have hτdef : (pathExitTime U f).toNNReal = τ := by
    rw [hτ, ENNReal.toNNReal_coe]
  -- the reparametrization for which `g` is uniformly close to `f ∘ φ`
  unfold cmpEDist at hg
  obtain ⟨φ, hφ⟩ := iInf_lt_iff.1 hg
  have hgφ : ∀ t, dist (g t) (f (φ t)) < min ε d := fun t =>
    edist_lt_ofReal.1 (lt_of_le_of_lt (le_iSup (fun t => edist (g t) (f (φ t))) t) hφ)
  -- `g` has left `U` by the time `φ⁻¹ s`
  have hσle : pathExitTime U g ≤ (φ.symm s : ℝ≥0∞) := by
    apply exitTime_le_of_not_mem
    apply hout
    have h2 := hgφ (φ.symm s)
    rw [OrderIso.apply_symm_apply] at h2
    exact lt_of_lt_of_le h2 (min_le_right _ _)
  have hσfin : pathExitTime U g ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hσle
  set σ : ℝ≥0 := (pathExitTime U g).toNNReal with hσdef
  have hσ : pathExitTime U g = σ := (ENNReal.coe_toNNReal hσfin).symm
  have hσs : φ σ ≤ s := by
    have h3 : σ ≤ φ.symm s := by
      rw [hσ] at hσle
      exact_mod_cast hσle
    exact (OrderIso.le_symm_apply φ).1 h3
  -- `g` stays in `U` while `φ t + η / 2 ≤ τ`
  have hstay : ∀ t, φ t + η / 2 ≤ τ → g t ∈ U := fun t ht =>
    hin (φ t) ht (g t) (lt_of_lt_of_le (hgφ t) (min_le_right _ _))
  have hτσ : τ < φ σ + η := by
    by_contra hcon
    rw [not_lt] at hcon
    have hhalf : η / 2 ≤ τ := (half_le_self (zero_le : (0 : ℝ≥0) ≤ η)).trans (le_add_self.trans hcon)
    have hv : φ σ < τ - η / 2 :=
      lt_tsub_iff_right.2 (lt_of_lt_of_le (by gcongr; exact half_lt_self hη) hcon)
    have hu : ((φ.symm (τ - η / 2) : ℝ≥0) : ℝ≥0∞) ≤ σ := by
      rw [← hσ]
      apply le_exitTime_of_forall_le_mem
      intro t ht
      apply hstay
      calc φ t + η / 2 ≤ (τ - η / 2) + η / 2 := by gcongr; exact (OrderIso.le_symm_apply φ).1 ht
        _ = τ := tsub_add_cancel_of_le hhalf
    have h4 : τ - η / 2 ≤ φ σ := (OrderIso.symm_apply_le φ).1 (by exact_mod_cast hu)
    exact absurd h4 (not_le.2 hv)
  -- the two stopped paths
  have hstopg : ∀ t, stopAtExit U g t = g (min t σ) := by
    intro t
    simp only [stopAtExit, hσfin, ↓reduceIte, hσdef]
  have hstopf : ∀ t, stopAtExit U f t = f (min t τ) := by
    intro t
    simp only [stopAtExit, hfin, ↓reduceIte, hτdef]
  -- the pointwise bound along `φ`
  have hbound : ∀ t, dist (stopAtExit U g t) (stopAtExit U f (φ t)) < 2 * ε := by
    intro t
    rw [hstopg, hstopf]
    have hm : φ (min t σ) = min (φ t) (φ σ) := φ.monotone.map_min
    have e1 : dist (g (min t σ)) (f (min (φ t) (φ σ))) < ε := by
      rw [← hm]
      exact lt_of_lt_of_le (hgφ _) (min_le_left _ _)
    have hclose : dist (min (φ t) (φ σ)) (min (φ t) τ) < η := by
      rw [NNReal.dist_eq, NNReal.coe_min, NNReal.coe_min]
      refine lt_of_le_of_lt (abs_min_sub_min_le_max _ _ _ _) ?_
      rw [sub_self, abs_zero, max_eq_right (abs_nonneg _)]
      have hup : (φ σ : ℝ) < τ + η := by
        have h5 : φ σ < τ + η := lt_of_le_of_lt hσs hs.2
        exact_mod_cast h5
      have hlo : (τ : ℝ) < φ σ + η := by exact_mod_cast hτσ
      rw [abs_sub_lt_iff]
      constructor <;> linarith
    have e2 : dist (f (min (φ t) (φ σ))) (f (min (φ t) τ)) ≤ ε :=
      hmod _ ((min_le_right _ _).trans (hσs.trans hsT)) _
        ((min_le_right _ _).trans (hs.1.le.trans hsT)) hclose
    calc dist (g (min t σ)) (f (min (φ t) τ))
        ≤ dist (g (min t σ)) (f (min (φ t) (φ σ))) + dist (f (min (φ t) (φ σ))) (f (min (φ t) τ)) :=
          dist_triangle _ _ _
      _ < ε + ε := add_lt_add_of_lt_of_le e1 e2
      _ = 2 * ε := by ring
  unfold cmpEDist
  exact (iInf_le _ φ).trans (iSup_le fun t => (edist_lt_ofReal.2 (hbound t)).le)

/-- The quantitative continuity of the stopped path with a strict bound: under the hypotheses of
`cmpEDist_stopAtExit_le_of_modulus` and `0 < ε`, the stopped paths are at curve distance less than `3 ε`. -/
theorem cmpEDist_stopAtExit_lt_of_modulus {U : Set ℂ} {f g : ℝ≥0 → ℂ} {τ s η T : ℝ≥0} {ε d : ℝ}
    (hτ : pathExitTime U f = τ) (hη : 0 < η) (hε : 0 < ε)
    (hmod : ∀ t ≤ T, ∀ t' ≤ T, dist t t' < η → dist (f t) (f t') ≤ ε)
    (hs : s ∈ Ioo τ (τ + η)) (hsT : s ≤ T)
    (hout : ∀ w, dist w (f s) < d → w ∉ U)
    (hin : ∀ t, t + η / 2 ≤ τ → ∀ w, dist w (f t) < d → w ∈ U)
    (hg : cmpEDist g f < ENNReal.ofReal (min ε d)) :
    cmpEDist (stopAtExit U g) (stopAtExit U f) < ENNReal.ofReal (3 * ε) :=
  lt_of_le_of_lt (cmpEDist_stopAtExit_le_of_modulus hτ hη hmod hs hsT hout hin hg)
    ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith))

end MatedCRT.StopAtExitCmp
