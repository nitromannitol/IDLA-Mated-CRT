import MatedCRT.FirstPass.S6j.LitUniformStartInvariance
import MatedCRT.FirstPass.S3t.LBMRegular

/-!
# Continuity of the stopped path for the distance of curves modulo time parametrization

Let `U ⊆ ℂ` be open and let `f : [0, ∞) → ℂ` be a continuous path which leaves `U` at a finite time `τ` and exits
regularly: it visits the complement of `closure U` at times arbitrarily close to `τ` from above
(`MatedCRT.TruncatedLaws.RegularExit`). Then the stopping map `g ↦ stopAtExit U g` is continuous at `f` for the
distance `cmpEDist` of curves modulo time parametrization: if `g` is close to `f` modulo parametrization, then `g`
stopped at its own exit time from `U` is close to `f` stopped at `τ`. No regularity of `g` is needed.

The proof keeps the reparametrization `φ` for which `g` is uniformly close to `f ∘ φ`. Up to time `τ - η/2` the
path `f` stays in a compact subset of `U`, so `g` has not left `U` before the time `φ⁻¹(τ - η/2)`; some time
`s ∈ (τ, τ + η)` has `f s ∉ closure U`, so `g` has left `U` by the time `φ⁻¹(s)`. Hence the exit time `σ` of `g`
satisfies `|φ(σ) - τ| < η`, and the uniform continuity of `f` on `[0, τ + 1]` controls the remaining error.

This is the deterministic half of the passage from paths to paths stopped at the exit of a domain in the
uniform-start invariance principle (`MatedCRT.GMS21UniformStartInput`); planar Brownian motion started inside a disc
exits it regularly almost surely.

## Main statements

* `MatedCRT.StopAtExitCmp.cmpEDist_stopAtExit_lt_of_frequently`: the continuity, with the regular exit written out.
* `MatedCRT.StopAtExitCmp.cmpEDist_stopAtExit_lt_of_regularExit`: the same under `RegularExit U f`.
-/

open Set Filter Topology Metric HarmonicBalls
open scoped ENNReal NNReal

namespace MatedCRT.StopAtExitCmp

/-- A path outside `U` at time `t` has left `U` by time `t`. -/
theorem exitTime_le_of_not_mem {U : Set ℂ} {g : ℝ≥0 → ℂ} {t : ℝ≥0} (h : g t ∉ U) :
    pathExitTime U g ≤ t :=
  sInf_le ⟨t, rfl, h⟩

/-- Before its exit time a path is in `U`. -/
theorem mem_of_lt_exitTime {U : Set ℂ} {g : ℝ≥0 → ℂ} {t : ℝ≥0} (h : (t : ℝ≥0∞) < pathExitTime U g) :
    g t ∈ U := by
  by_contra hg
  exact absurd (exitTime_le_of_not_mem hg) (not_le.mpr h)

/-- A path that stays in `U` up to time `u` has not left `U` before time `u`. -/
theorem le_exitTime_of_forall_le_mem {U : Set ℂ} {g : ℝ≥0 → ℂ} {u : ℝ≥0} (h : ∀ t ≤ u, g t ∈ U) :
    (u : ℝ≥0∞) ≤ pathExitTime U g := by
  unfold pathExitTime
  refine le_sInf ?_
  rintro _ ⟨t, rfl, ht⟩
  by_contra hlt
  exact ht (h t (ENNReal.coe_lt_coe.mp (not_le.mp hlt)).le)

/-- **Continuity of the stopped path modulo time parametrization.** Let `U` be open and let `f` be a continuous
path which leaves `U` at a finite time `τ` and visits the complement of `closure U` at times arbitrarily close to
`τ` from above. For every `ε > 0` there is `δ > 0` such that every path `g` within curve distance `δ` of `f` has,
once stopped at its exit time from `U`, curve distance less than `ε` from `f` stopped at `τ`. -/
theorem cmpEDist_stopAtExit_lt_of_frequently {U : Set ℂ} (hU : IsOpen U) {f : ℝ≥0 → ℂ} (hf : Continuous f)
    (hfin : pathExitTime U f ≠ ⊤)
    (hreg : ∃ᶠ t in 𝓝[>] (pathExitTime U f).toNNReal, f t ∉ closure U) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ g : ℝ≥0 → ℂ, cmpEDist g f < ENNReal.ofReal δ →
      cmpEDist (stopAtExit U g) (stopAtExit U f) < ENNReal.ofReal ε := by
  set τ : ℝ≥0 := (pathExitTime U f).toNNReal with hτdef
  have hτ : pathExitTime U f = τ := (ENNReal.coe_toNNReal hfin).symm
  -- uniform continuity of `f` on `[0, τ + 1]`
  obtain ⟨η₀, hη₀, hη₀f⟩ := Metric.uniformContinuousOn_iff.1
    ((isCompact_Icc (a := (0 : ℝ≥0)) (b := τ + 1)).uniformContinuousOn_of_continuous hf.continuousOn)
    (ε / 3) (by linarith)
  set η : ℝ≥0 := ⟨min η₀ 1, le_min hη₀.le zero_le_one⟩ with hηdef
  have hηpos : 0 < η := NNReal.coe_pos.1 (lt_min hη₀ one_pos)
  have hη1 : η ≤ 1 := by
    rw [← NNReal.coe_le_coe, NNReal.coe_one]
    exact min_le_right _ _
  have hηη₀ : (η : ℝ) ≤ η₀ := min_le_left _ _
  -- a time `s ∈ (τ, τ + η)` with `f s ∉ closure U`, and a ball around `f s` outside `closure U`
  obtain ⟨s, hs_out, hs_mem⟩ : ∃ s, f s ∉ closure U ∧ s ∈ Ioo τ (τ + η) :=
    (hreg.and_eventually (Ioo_mem_nhdsGT (lt_add_of_pos_right τ hηpos))).exists
  obtain ⟨d₁, hd₁, hball⟩ := Metric.isOpen_iff.1 isClosed_closure.isOpen_compl (f s) hs_out
  -- up to time `τ - η / 2`, `f` stays in a compact subset of `U`
  have hA : IsCompact (Icc (0 : ℝ≥0) τ ∩ {t : ℝ≥0 | t + η / 2 ≤ τ}) :=
    isCompact_Icc.inter_right (isClosed_le (continuous_id.add continuous_const) continuous_const)
  have hKU : f '' (Icc (0 : ℝ≥0) τ ∩ {t : ℝ≥0 | t + η / 2 ≤ τ}) ⊆ U := by
    rintro _ ⟨t, ⟨_, ht⟩, rfl⟩
    apply mem_of_lt_exitTime
    rw [hτ]
    exact_mod_cast lt_of_lt_of_le (lt_add_of_pos_right t (half_pos hηpos)) ht
  obtain ⟨d₂, hd₂, hthick⟩ := (hA.image hf).exists_thickening_subset_open hU hKU
  refine ⟨min (ε / 3) (min d₁ d₂), lt_min (by linarith) (lt_min hd₁ hd₂), fun g hg => ?_⟩
  -- the reparametrization for which `g` is uniformly close to `f ∘ φ`
  unfold cmpEDist at hg
  obtain ⟨φ, hφ⟩ := iInf_lt_iff.1 hg
  have hgφ : ∀ t, dist (g t) (f (φ t)) < min (ε / 3) (min d₁ d₂) := fun t =>
    edist_lt_ofReal.1 (lt_of_le_of_lt (le_iSup (fun t => edist (g t) (f (φ t))) t) hφ)
  -- `g` has left `U` by the time `φ⁻¹ s`
  have hσle : pathExitTime U g ≤ (φ.symm s : ℝ≥0∞) := by
    apply exitTime_le_of_not_mem
    intro hmem
    have h1 : dist (g (φ.symm s)) (f s) < d₁ := by
      have h2 := hgφ (φ.symm s)
      rw [OrderIso.apply_symm_apply] at h2
      exact lt_of_lt_of_le h2 ((min_le_right _ _).trans (min_le_left _ _))
    exact hball (mem_ball.2 h1) (subset_closure hmem)
  have hσfin : pathExitTime U g ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hσle
  set σ : ℝ≥0 := (pathExitTime U g).toNNReal with hσdef
  have hσ : pathExitTime U g = σ := (ENNReal.coe_toNNReal hσfin).symm
  have hσs : φ σ ≤ s := by
    have h3 : σ ≤ φ.symm s := by
      rw [hσ] at hσle
      exact_mod_cast hσle
    exact (OrderIso.le_symm_apply φ).1 h3
  -- `g` stays in `U` while `φ t + η / 2 ≤ τ`
  have hstay : ∀ t, φ t + η / 2 ≤ τ → g t ∈ U := by
    intro t ht
    apply hthick
    refine mem_thickening_iff.2 ⟨f (φ t), ⟨φ t, ⟨⟨zero_le, le_self_add.trans ht⟩, ht⟩, rfl⟩, ?_⟩
    exact lt_of_lt_of_le (hgφ t) ((min_le_right _ _).trans (min_le_right _ _))
  have hτσ : τ < φ σ + η := by
    by_contra hcon
    rw [not_lt] at hcon
    have hhalf : η / 2 ≤ τ := (half_le_self (zero_le : (0 : ℝ≥0) ≤ η)).trans (le_add_self.trans hcon)
    have hv : φ σ < τ - η / 2 :=
      lt_tsub_iff_right.2 (lt_of_lt_of_le (by gcongr; exact half_lt_self hηpos) hcon)
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
  have hbound : ∀ t, dist (stopAtExit U g t) (stopAtExit U f (φ t)) < 2 * (ε / 3) := by
    intro t
    rw [hstopg, hstopf]
    have hm : φ (min t σ) = min (φ t) (φ σ) := φ.monotone.map_min
    have e1 : dist (g (min t σ)) (f (min (φ t) (φ σ))) < ε / 3 := by
      rw [← hm]
      exact lt_of_lt_of_le (hgφ _) (min_le_left _ _)
    have hclose : dist (min (φ t) (φ σ)) (min (φ t) τ) < η₀ := by
      rw [NNReal.dist_eq, NNReal.coe_min, NNReal.coe_min]
      refine lt_of_le_of_lt (abs_min_sub_min_le_max _ _ _ _) ?_
      rw [sub_self, abs_zero, max_eq_right (abs_nonneg _)]
      refine lt_of_lt_of_le ?_ hηη₀
      have hup : (φ σ : ℝ) < τ + η := by
        have h5 : φ σ < τ + η := lt_of_le_of_lt hσs hs_mem.2
        exact_mod_cast h5
      have hlo : (τ : ℝ) < φ σ + η := by exact_mod_cast hτσ
      rw [abs_sub_lt_iff]
      constructor <;> linarith
    have e2 : dist (f (min (φ t) (φ σ))) (f (min (φ t) τ)) < ε / 3 := by
      refine hη₀f _ ⟨zero_le, ?_⟩ _ ⟨zero_le, (min_le_right _ _).trans le_self_add⟩ hclose
      exact (min_le_right _ _).trans
        (hσs.trans (le_of_lt (lt_of_lt_of_le hs_mem.2 (by gcongr))))
    calc dist (g (min t σ)) (f (min (φ t) τ))
        ≤ dist (g (min t σ)) (f (min (φ t) (φ σ))) + dist (f (min (φ t) (φ σ))) (f (min (φ t) τ)) :=
          dist_triangle _ _ _
      _ < ε / 3 + ε / 3 := add_lt_add e1 e2
      _ = 2 * (ε / 3) := by ring
  have hle : cmpEDist (stopAtExit U g) (stopAtExit U f) ≤ ENNReal.ofReal (2 * (ε / 3)) := by
    unfold cmpEDist
    exact (iInf_le _ φ).trans (iSup_le fun t => (edist_lt_ofReal.2 (hbound t)).le)
  exact lt_of_le_of_lt hle ((ENNReal.ofReal_lt_ofReal_iff hε).2 (by linarith))

/-- **Continuity of the stopped path at a regular exit.** If `U` is open and the continuous path `f` leaves `U` at
a finite time and exits regularly (`RegularExit U f`), then `g ↦ stopAtExit U g` is continuous at `f` for the
distance `cmpEDist` of curves modulo time parametrization. -/
theorem cmpEDist_stopAtExit_lt_of_regularExit {U : Set ℂ} (hU : IsOpen U) {f : ℝ≥0 → ℂ} (hf : Continuous f)
    (hfin : pathExitTime U f ≠ ⊤) (hreg : MatedCRT.TruncatedLaws.RegularExit U f) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ g : ℝ≥0 → ℂ, cmpEDist g f < ENNReal.ofReal δ →
      cmpEDist (stopAtExit U g) (stopAtExit U f) < ENNReal.ofReal ε :=
  cmpEDist_stopAtExit_lt_of_frequently hU hf hfin (hreg.resolve_left hfin) hε

end MatedCRT.StopAtExitCmp
