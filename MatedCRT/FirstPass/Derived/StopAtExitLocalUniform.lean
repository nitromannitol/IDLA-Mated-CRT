import MatedCRT.FirstPass.Derived.StopAtExitLevyProkhorov

/-!
# Continuity of the stopped curve class for locally uniform convergence

The curve class of a planar path stopped at its first exit time from an open set `U`
(`MatedCRT.StopAtExitLevyProkhorov.stoppedExitCurve`) is a continuous function of the path, for the topology of
locally uniform convergence on `C(ℝ≥0, ℂ)` and the distance of curves modulo time parametrization, at every
path that leaves `U` at a finite time and exits regularly (it visits the complement of `closure U` at times
arbitrarily close to the exit time from above).

The closeness `cmpEDist g f < δ` of `StopAtExitCmp.cmpEDist_stopAtExit_lt_of_frequently` involves all times.
Here only the times up to a fixed horizon `T` are used: a path `g` within `δ` of `f` up to time `T` is
extended after time `T` by a translate of `f`, which does not change the exit time since `g` has left `U` before
`T`.

## Main statements

* `MatedCRT.StopAtExitCmp.exists_forall_cmpEDist_stopAtExit_lt_of_dist_lt`: the quantitative statement with a
  finite time horizon.
* `MatedCRT.StopAtExitCmp.continuousAt_stoppedExitCurve_of_regularExit`: continuity of `stoppedExitCurve U` at a
  path with finite exit time and regular exit, for the compact-open topology.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology Metric HarmonicBalls MarkovProcess
open scoped ENNReal NNReal

namespace MatedCRT.StopAtExitCmp

/-- If `h` leaves `U` only at times at which `g` has already left `U`, then `g` has the smaller exit time. -/
theorem pathExitTime_le_of_forall_not_mem {U : Set ℂ} {g h : ℝ≥0 → ℂ}
    (H : ∀ t, h t ∉ U → pathExitTime U g ≤ t) : pathExitTime U g ≤ pathExitTime U h := by
  change pathExitTime U g ≤ sInf {s : ℝ≥0∞ | ∃ t : ℝ≥0, s = (t : ℝ≥0∞) ∧ h t ∉ U}
  refine le_sInf ?_
  rintro _ ⟨t, rfl, ht⟩
  exact H t ht

/-- Two paths that agree up to a time `T` by which one of them has left `U` have the same exit time from `U`. -/
theorem pathExitTime_eq_of_eqOn_of_not_mem {U : Set ℂ} {g h : ℝ≥0 → ℂ} {T t₀ : ℝ≥0}
    (hgh : ∀ t ≤ T, g t = h t) (ht₀ : t₀ ≤ T) (hg : g t₀ ∉ U) :
    pathExitTime U g = pathExitTime U h := by
  have hh : h t₀ ∉ U := (hgh t₀ ht₀) ▸ hg
  have key : ∀ {a b : ℝ≥0 → ℂ}, (∀ t ≤ T, a t = b t) → a t₀ ∉ U → b t₀ ∉ U →
      pathExitTime U a ≤ pathExitTime U b := by
    intro a b hab ha hb
    refine pathExitTime_le_of_forall_not_mem fun t ht => ?_
    by_cases htT : t ≤ T
    · exact exitTime_le_of_not_mem (by rwa [hab t htT])
    · exact (exitTime_le_of_not_mem ha).trans (by exact_mod_cast (ht₀.trans (not_le.mp htT).le))
  exact le_antisymm (key hgh hg hh) (key (fun t ht => (hgh t ht).symm) hh hg)

/-- Two paths that agree up to a time `T` by which one of them has left `U` have the same stopped path. -/
theorem stopAtExit_eq_of_eqOn_of_not_mem {U : Set ℂ} {g h : ℝ≥0 → ℂ} {T t₀ : ℝ≥0}
    (hgh : ∀ t ≤ T, g t = h t) (ht₀ : t₀ ≤ T) (hg : g t₀ ∉ U) :
    stopAtExit U g = stopAtExit U h := by
  have hexit := pathExitTime_eq_of_eqOn_of_not_mem hgh ht₀ hg
  have hle : pathExitTime U g ≤ (T : ℝ≥0∞) :=
    (exitTime_le_of_not_mem hg).trans (by exact_mod_cast ht₀)
  have hne : pathExitTime U g ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hle
  funext t
  unfold stopAtExit
  rw [← hexit]
  simp only [hne, ↓reduceIte]
  have hT : (pathExitTime U g).toNNReal ≤ T := by
    simpa using ENNReal.toNNReal_mono ENNReal.coe_ne_top hle
  exact hgh _ ((min_le_right _ _).trans hT)

/-- **Continuity of the stopped path modulo time parametrization, for closeness up to a finite time.** Let `U`
be open and let `f` be a continuous path which leaves `U` at a finite time and visits the complement of
`closure U` at times arbitrarily close to its exit time from above. For every `ε > 0` there are a time `T` and
`δ > 0` such that every path `g` with `|g t - f t| < δ` for `t ≤ T` leaves `U` at a finite time and, stopped at
its exit time, has curve distance less than `ε` from `f` stopped at its exit time. -/
theorem exists_forall_cmpEDist_stopAtExit_lt_of_dist_lt {U : Set ℂ} (hU : IsOpen U) {f : ℝ≥0 → ℂ}
    (hf : Continuous f) (hfin : pathExitTime U f ≠ ⊤)
    (hreg : ∃ᶠ t in 𝓝[>] (pathExitTime U f).toNNReal, f t ∉ closure U) {ε : ℝ} (hε : 0 < ε) :
    ∃ (T : ℝ≥0) (δ : ℝ), 0 < δ ∧ ∀ g : ℝ≥0 → ℂ, (∀ t ≤ T, dist (g t) (f t) < δ) →
      pathExitTime U g ≠ ⊤ ∧ cmpEDist (stopAtExit U g) (stopAtExit U f) < ENNReal.ofReal ε := by
  obtain ⟨δ₁, hδ₁, H⟩ := cmpEDist_stopAtExit_lt_of_frequently hU hf hfin hreg hε
  obtain ⟨t₀, ht₀⟩ := hreg.exists
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 (isClosed_closure (s := U)).isOpen_compl (f t₀) ht₀
  refine ⟨t₀, min (δ₁ / 2) r, lt_min (by positivity) hr, fun g hg => ?_⟩
  have hgt₀ : g t₀ ∉ U := fun hmem =>
    hball (mem_ball.2 ((hg t₀ le_rfl).trans_le (min_le_right _ _))) (subset_closure hmem)
  have hgfin : pathExitTime U g ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.coe_ne_top (exitTime_le_of_not_mem hgt₀)
  refine ⟨hgfin, ?_⟩
  set g' : ℝ≥0 → ℂ := fun t => if t ≤ t₀ then g t else f t + (g t₀ - f t₀) with hg'
  have hg'g : ∀ t ≤ t₀, g t = g' t := fun t ht => by simp [hg', ht]
  have hg'f : ∀ t, dist (g' t) (f t) ≤ δ₁ / 2 := by
    intro t
    by_cases ht : t ≤ t₀
    · simp only [hg', ht, ↓reduceIte]
      exact ((hg t ht).trans_le ((min_le_left _ _))).le
    · simp only [hg', ht, ↓reduceIte]
      rw [dist_eq_norm, add_sub_cancel_left, ← dist_eq_norm]
      exact ((hg t₀ le_rfl).trans_le (min_le_left _ _)).le
  have hcmp : cmpEDist g' f < ENNReal.ofReal δ₁ :=
    calc cmpEDist g' f ≤ ⨆ t, edist (g' t) (f ((OrderIso.refl ℝ≥0) t)) := iInf_le _ (OrderIso.refl ℝ≥0)
      _ ≤ ENNReal.ofReal (δ₁ / 2) :=
        iSup_le fun t => by
          rw [edist_dist]
          exact ENNReal.ofReal_le_ofReal (hg'f t)
      _ < ENNReal.ofReal δ₁ := (ENNReal.ofReal_lt_ofReal_iff hδ₁).2 (by linarith)
  have h1 := H g' hcmp
  rwa [← stopAtExit_eq_of_eqOn_of_not_mem hg'g le_rfl hgt₀] at h1

/-- **Continuity of the stopped curve class for locally uniform convergence.** The map sending a planar
continuous path to the curve class of the path stopped at its first exit time from the open set `U` is continuous,
for the compact-open topology on paths and the distance of curves modulo time parametrization, at every path
that leaves `U` at a finite time and exits regularly. -/
theorem continuousAt_stoppedExitCurve_of_regularExit {U : Set ℂ} (hU : IsOpen U) {X : ContinuousPath ℂ}
    (hfin : pathExitTime U ⇑X ≠ ⊤) (hreg : MatedCRT.TruncatedLaws.RegularExit U ⇑X) :
    ContinuousAt (StopAtExitLevyProkhorov.stoppedExitCurve U) X := by
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨T, δ, hδ, H⟩ := exists_forall_cmpEDist_stopAtExit_lt_of_dist_lt hU X.continuous hfin
    (hreg.resolve_left hfin) hε
  have hunif := (ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.1
    (tendsto_id : Tendsto (id : ContinuousPath ℂ → ContinuousPath ℂ) (𝓝 X) (𝓝 X))) (Icc 0 T)
    isCompact_Icc
  rw [Metric.tendstoUniformlyOn_iff] at hunif
  filter_upwards [hunif δ hδ] with Y hY
  obtain ⟨hYfin, hY2⟩ := H Y (fun t ht => by
    rw [dist_comm]
    exact hY t ⟨bot_le, ht⟩)
  rw [← edist_lt_ofReal]
  have h := StopAtExitCurveClass.cmpEDist_stopAtExit_eq_edist_normalizedPrefixCurve U U Y X hYfin hfin
  unfold StopAtExitLevyProkhorov.stoppedExitCurve
  rw [← h]
  exact hY2

end MatedCRT.StopAtExitCmp
