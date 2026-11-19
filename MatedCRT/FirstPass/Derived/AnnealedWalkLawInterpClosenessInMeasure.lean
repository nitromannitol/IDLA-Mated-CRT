import MatedCRT.FirstPass.Derived.WalkLawInterpClosenessInMeasure
import MatedCRT.FirstPass.Derived.AnnealedWalksRandomStart

/-!
# The walk law at the walk position against the interpolated law, in probability, under the annealed law

For the embedded walk of Theorem 2.11 observed at the lattice time `j_n / m_n` (`m_n = m_{ε_n}`) the walk is at
the vertex `x = (X_n)_{j_n}`, and the Markov step compares the quenched walk law `Q^{ε_n}(x)` with the interpolated
law `P̃^{ε_n}` evaluated at the position `η(ε_n x)` of the vertex (BG20 Lemma 7.4, Markov part).  On the product space
`annealedWalksAt` of the annealed laws of the walks started at the random vertices `k_n`, the distance
`LP(Q^{ε_n}(x), P̃^{ε_n}_{η(ε_n x)})` tends to `0` in probability, provided

* the walk laws are equicontinuous in law (`hEqLaw`) and the cell diameters tend to `0` in probability (`hdiam`),
  both under the environment law `S.P`, and
* the walk position is tight under the annealed law (`htight`).

The coordinate `ω` of `p n` has law `S.P` (`annealedWalksAt_map_fst`), so the two environment bounds transfer to the
annealed space; the position bound is the explicit hypothesis `htight`.
-/

namespace MatedCRT.FirstPass.Derived

open MeasureTheory ProbabilityTheory Filter Topology Set Metric LatticeProb Preorder
open MarkovProcess (ContinuousPath)
open scoped NNReal ENNReal

attribute [local instance] LatticeProb.dUnifMetricSpace

variable {Ω : Type} [MeasurableSpace Ω]

/-- The environment coordinate of the `n`-th factor of the product space `annealedWalksAt` has law `S.P`. -/
theorem annealedWalksAt_map_fst {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {S : MatedCRTEnv Ω}
    (hS : S.IsValid 𝒮 γ) [IsProbabilityMeasure S.P] (ε : ℕ → ℝ) {k : ℕ → Ω → ℤ}
    (hk : ∀ n, Measurable (k n)) (n : ℕ) :
    (annealedWalksAt hS ε hk).map (fun p : ℕ → Ω × (ℕ → ℤ) => (p n).1) = S.P := by
  have h := annealedWalksAt_map_eval hS ε hk n
  have e : (fun p : ℕ → Ω × (ℕ → ℤ) => (p n).1) = Prod.fst ∘ (fun p => p n) := rfl
  rw [e, ← Measure.map_map measurable_fst (measurable_pi_apply n), h]
  exact Measure.fst_compProd _ _

/-- A bound for an event of the environment transfers to the annealed product space. -/
theorem annealedWalksAt_preimage_fst_le {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {S : MatedCRTEnv Ω}
    (hS : S.IsValid 𝒮 γ) [IsProbabilityMeasure S.P] (ε : ℕ → ℝ) {k : ℕ → Ω → ℤ}
    (hk : ∀ n, Measurable (k n)) (n : ℕ) (A : Set Ω) :
    annealedWalksAt hS ε hk {p : ℕ → Ω × (ℕ → ℤ) | (p n).1 ∈ A} ≤ S.P A := by
  have hfm : Measurable fun p : ℕ → Ω × (ℕ → ℤ) => (p n).1 :=
    measurable_fst.comp (measurable_pi_apply n)
  have h := Measure.le_map_apply (μ := annealedWalksAt hS ε hk) hfm.aemeasurable A
  rw [annealedWalksAt_map_fst hS ε hk n] at h
  exact h

/-- **The quenched walk law at the walk position against the interpolated law, in probability, under the
annealed law.**  Under `hEqLaw` and `hdiam` (for the environment law `S.P`) and the tightness `htight` of the
walk position `η(ε_n (X_n)_{j_n})` under `annealedWalksAt`, the Lévy–Prokhorov distance of `Q^{ε_n}((X_n)_{j_n})`
and `P̃^{ε_n}_{η(ε_n (X_n)_{j_n})}` tends to `0` in probability under `annealedWalksAt`. -/
theorem tendstoInMeasure_levyProkhorovDist_annealedWalksAt_walkPathLaw_interpWalkLaw
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    [IsProbabilityMeasure S.P] {η' : Ω → C(ℝ, ℂ)} (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω)
    {ε : ℕ → ℝ} (hε0 : ∀ n, 0 < ε n) (hε : Tendsto ε atTop (𝓝 0))
    (hEqLaw : ∀ R a : ℝ, 0 < a → ∃ δ > 0, ∀ᶠ n in atTop,
      S.P {ω | ENNReal.ofReal a < walkLawModulus S η' (ε n) R δ ω} ≤ ENNReal.ofReal a)
    (hdiam : ∀ R a : ℝ, 0 < a →
      Tendsto (fun n => S.P {ω | ENNReal.ofReal a < maxCellDiam (ε n) (⇑(η' ω)) R}) atTop (𝓝 0))
    {k : ℕ → Ω → ℤ} (hk : ∀ n, Measurable (k n)) (j : ℕ → ℕ)
    (htight : ∀ r : ℝ, 0 < r → ∃ R : ℝ, ∀ᶠ n in atTop,
      annealedWalksAt hS ε hk {p : ℕ → Ω × (ℕ → ℤ) |
        R < ‖vertexPoint (ε n) (⇑(η' (p n).1)) (lastState (j n) (frestrictLe (j n) (p n).2))‖} ≤
        ENNReal.ofReal r) :
    TendstoInMeasure (annealedWalksAt hS ε hk)
      (fun n (p : ℕ → Ω × (ℕ → ℤ)) => levyProkhorovDist
        (walkPathLaw S (fun ω => vertexPoint (ε n) (⇑(η' ω))) (S.mε_nonneg (ε n)) (ε n)
          (lastState (j n) (frestrictLe (j n) (p n).2)) (p n).1 : Measure (ContinuousPath ℂ))
        (interpWalkLaw S η' (ε n) (p n).1
          (vertexPoint (ε n) (⇑(η' (p n).1)) (lastState (j n) (frestrictLe (j n) (p n).2))) :
          Measure (ContinuousPath ℂ))) atTop (fun _ => 0) := by
  have hgoodp : ∀ᵐ p ∂(annealedWalksAt hS ε hk), ∀ n,
      (∀ z, ∃ U ∈ 𝓝 z, {k : ℤ | ∃ y ∈ U,
        interpWeight (fun k => cell (ε n) (⇑(η' (p n).1)) k) (ε n) k y ≠ 0}.Finite) ∧
      ∀ z, ∃ k : ℤ, interpWeight (fun k => cell (ε n) (⇑(η' (p n).1)) k) (ε n) k z ≠ 0 := by
    rw [ae_all_iff]
    intro n
    have h1 := hS.ae_interpWeight_good hae (hε0 n)
    have hfm : Measurable fun p : ℕ → Ω × (ℕ → ℤ) => (p n).1 :=
      measurable_fst.comp (measurable_pi_apply n)
    exact ae_of_ae_map hfm.aemeasurable (by rw [annealedWalksAt_map_fst hS ε hk n]; exact h1)
  have hnn : ∀ μ ν : Measure (ContinuousPath ℂ), 0 ≤ levyProkhorovDist μ ν :=
    fun _ _ => ENNReal.toReal_nonneg
  rw [tendstoInMeasure_iff_dist]
  intro θ hθ
  rw [ENNReal.tendsto_nhds_zero]
  intro r' hr'
  obtain ⟨r, hr0, hrr'⟩ : ∃ r : ℝ, 0 < r ∧ ENNReal.ofReal r ≤ r' := by
    rcases eq_or_ne r' ⊤ with h | h
    · exact ⟨1, one_pos, by rw [h]; exact le_top⟩
    · exact ⟨r'.toReal, ENNReal.toReal_pos hr'.ne' h, (ENNReal.ofReal_toReal h).le⟩
  obtain ⟨a', ha'0, ha'r, ha'θ⟩ : ∃ a' : ℝ, 0 < a' ∧ a' ≤ r / 3 ∧ a' < θ :=
    ⟨min (r / 3) (θ / 2), lt_min (by linarith) (by linarith), min_le_left _ _,
      (min_le_right _ _).trans_lt (by linarith)⟩
  obtain ⟨R, hR⟩ := htight (r / 3) (by linarith)
  obtain ⟨δ, hδ0, hδ⟩ := hEqLaw R a' ha'0
  obtain ⟨δ', hδ'0, hδ'δ, hδ'1⟩ : ∃ δ' : ℝ, 0 < δ' ∧ δ' ≤ δ ∧ δ' ≤ 1 :=
    ⟨min δ 1, lt_min hδ0 one_pos, min_le_left _ _, min_le_right _ _⟩
  have hD' : ∀ᶠ n in atTop, S.P {ω | ENNReal.ofReal (δ' / 4) < maxCellDiam (ε n) (⇑(η' ω)) R}
      ≤ ENNReal.ofReal (r / 3) :=
    (ENNReal.tendsto_nhds_zero.1 (hdiam R (δ' / 4) (by linarith))) _
      (ENNReal.ofReal_pos.2 (by linarith))
  have hεs : ∀ᶠ n in atTop, ε n < δ' / 2 := hε.eventually (eventually_lt_nhds (by linarith))
  filter_upwards [hδ, hD', hεs, hR] with n hn1 hn2 hn3 hn4
  refine (measure_mono_ae (t :=
      {p : ℕ → Ω × (ℕ → ℤ) | ENNReal.ofReal a' < walkLawModulus S η' (ε n) R δ (p n).1} ∪
      {p : ℕ → Ω × (ℕ → ℤ) | ENNReal.ofReal (δ' / 4) < maxCellDiam (ε n) (⇑(η' (p n).1)) R} ∪
      {p : ℕ → Ω × (ℕ → ℤ) |
        R < ‖vertexPoint (ε n) (⇑(η' (p n).1)) (lastState (j n) (frestrictLe (j n) (p n).2))‖})
      ?_).trans ?_
  · filter_upwards [hgoodp] with p hp hmem
    by_contra hnot
    have h2 : ¬ ENNReal.ofReal a' < walkLawModulus S η' (ε n) R δ (p n).1 :=
      fun h => hnot (Or.inl (Or.inl h))
    have h3 : ¬ ENNReal.ofReal (δ' / 4) < maxCellDiam (ε n) (⇑(η' (p n).1)) R :=
      fun h => hnot (Or.inl (Or.inr h))
    have h4 : ¬ R < ‖vertexPoint (ε n) (⇑(η' (p n).1))
        (lastState (j n) (frestrictLe (j n) (p n).2))‖ := fun h => hnot (Or.inr h)
    obtain ⟨hloc, hpos⟩ := hp n
    have hLP := pathLevyProkhorovEDist_walkPathLaw_interpWalkLaw_le S η' (hε0 n).le hloc hpos
      (R := R) (δ := δ) (d := δ' / 4) (a := a') (by linarith) (by linarith) (by linarith)
      ha'0.le (not_lt.1 h3) (not_lt.1 h2) (not_lt.1 h4)
    rw [pathLevyProkhorovEDist_eq_ofReal_dist, ENNReal.ofReal_le_ofReal_iff ha'0.le,
      LevyProkhorov.dist_probabilityMeasure_def] at hLP
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hnn _ _)] at hmem
    exact absurd hmem (not_le.2 (hLP.trans_lt ha'θ))
  · refine (measure_union_le _ _).trans ?_
    refine (add_le_add (measure_union_le _ _) hn4).trans ?_
    have hA := annealedWalksAt_preimage_fst_le hS ε hk n
      {ω | ENNReal.ofReal a' < walkLawModulus S η' (ε n) R δ ω}
    have hB := annealedWalksAt_preimage_fst_le hS ε hk n
      {ω | ENNReal.ofReal (δ' / 4) < maxCellDiam (ε n) (⇑(η' ω)) R}
    have hr3 : (0 : ℝ) ≤ r / 3 := by linarith
    calc _ ≤ ENNReal.ofReal (r / 3) + ENNReal.ofReal (r / 3) + ENNReal.ofReal (r / 3) :=
          add_le_add (add_le_add (hA.trans (hn1.trans (ENNReal.ofReal_le_ofReal ha'r)))
            (hB.trans hn2)) le_rfl
      _ = ENNReal.ofReal r := by
          rw [← ENNReal.ofReal_add hr3 hr3, ← ENNReal.ofReal_add (by linarith) hr3]
          congr 1
          ring
      _ ≤ r' := hrr'

/-- **The closeness hypothesis of the Markov step on the product space.**  The statement of the hypothesis
`hclose` of `ae_markovAt_of_walk_markov_step_at` for the quenched walk laws `v n = η(ε_n ·)`, `m n = m_{ε_n}`
and a family `K` with `K (d n ω) = P̃^{ε_n}(ω)` (`hKd`): the Lévy–Prokhorov distance of the quenched walk law at
the position `(X_n)_{j_n}` and `K (d n)` at the position of the interpolated walk at the time `j_n / m_n` tends to
`0` in probability under `annealedWalksAt`. -/
theorem tendstoInMeasure_levyProkhorovDist_annealedWalksAt_hclose
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    [IsProbabilityMeasure S.P] {η' : Ω → C(ℝ, ℂ)} (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω)
    {ε : ℕ → ℝ} (hε0 : ∀ n, 0 < ε n) (hε : Tendsto ε atTop (𝓝 0))
    (hEqLaw : ∀ R a : ℝ, 0 < a → ∃ δ > 0, ∀ᶠ n in atTop,
      S.P {ω | ENNReal.ofReal a < walkLawModulus S η' (ε n) R δ ω} ≤ ENNReal.ofReal a)
    (hdiam : ∀ R a : ℝ, 0 < a →
      Tendsto (fun n => S.P {ω | ENNReal.ofReal a < maxCellDiam (ε n) (⇑(η' ω)) R}) atTop (𝓝 0))
    {k : ℕ → Ω → ℤ} (hk : ∀ n, Measurable (k n)) (j : ℕ → ℕ)
    (htight : ∀ r : ℝ, 0 < r → ∃ R : ℝ, ∀ᶠ n in atTop,
      annealedWalksAt hS ε hk {p : ℕ → Ω × (ℕ → ℤ) |
        R < ‖vertexPoint (ε n) (⇑(η' (p n).1)) (lastState (j n) (frestrictLe (j n) (p n).2))‖} ≤
        ENNReal.ofReal r)
    {S₀ : Type*} {d : ℕ → Ω → S₀} {K : S₀ → C(ℂ, ProbabilityMeasure (ContinuousPath ℂ))}
    (hKd : ∀ n ω z, K (d n ω) z = interpWalkLaw S η' (ε n) ω z)
    {v : ℕ → Ω → ℤ → ℂ} (hv : v = fun n ω => vertexPoint (ε n) (⇑(η' ω)))
    {m : ℕ → ℝ} (hm : ∀ n, 0 < m n) (hmε : m = fun n => S.mε (ε n)) :
    TendstoInMeasure (annealedWalksAt hS ε hk)
      (fun n (p : ℕ → Ω × (ℕ → ℤ)) => levyProkhorovDist
        (walkPathLaw S (v n) (hm n).le (ε n) (lastState (j n) (frestrictLe (j n) (p n).2)) (p n).1 :
          Measure (ContinuousPath ℂ))
        (K (d n (p n).1) (interpPathCM (v n (p n).1) (hm n).le (p n).2
          ((j n / m n : ℝ).toNNReal)) : Measure (ContinuousPath ℂ))) atTop 0 := by
  subst hv hmε
  have h := tendstoInMeasure_levyProkhorovDist_annealedWalksAt_walkPathLaw_interpWalkLaw hS hae hε0 hε
    hEqLaw hdiam hk j htight
  refine h.congr' (Filter.Eventually.of_forall fun n => ae_of_all _ fun p => ?_)
    (ae_of_all _ fun _ => rfl)
  dsimp only
  have e1 := interpPathCM_at_stepTime (vertexPoint (ε n) (⇑(η' (p n).1))) (hm n) (p n).2 (j n)
  rw [e1, hKd]
  try rfl

end MatedCRT.FirstPass.Derived
