import MatedCRT.FirstPass.Derived.DegreeCutoffMassTight

/-!
# The cell diameters near `B_R` tend to `0` in probability (BG20 Lemma 7.6, step C2)

Let `S` be a valid environment and `ε_n → 0`. Almost surely the space-filling curve `η` is continuous and proper
(`η(t) → ∞` as `|t| → ∞`, `IsValid.ae_tendsto_cocompact`). For such a curve the times `t` with
`η(t) ∈ B̄_{R+1}` lie in a compact interval `[-T, T]`, so every cell `H^ε_k = η([ε(k-1), εk])` meeting `B_{R+1}`
is the image of an interval of length `ε` inside `[-T-1, T+1]` once `ε < 1`; uniform continuity of `η` on
`[-T-1, T+1]` then bounds the diameter of `H^ε_k` uniformly in `k`. Hence `diam^ε_R → 0` almost surely. The event
`{diam^ε_R > a}` is the preimage of an open subset of `C(ℝ, ℂ)` (compact-open topology), hence measurable for the
measurable version of the curve given by the mating-of-trees coupling (`IsValid.matingOfTrees`), and almost sure
convergence gives convergence in probability.

* `ofReal_lt_maxCellDiam_iff`, `isOpen_setOf_ofReal_lt_maxCellDiam`: `{η | diam^ε_R(η) > a}` is open;
* `exists_maxCellDiam_le`: for a continuous proper curve, `diam^ε_R ≤ a` for all `ε` small enough;
* `hdiam_of_isValid`: for every valid environment, `P[diam^{ε_n}_R > a] → 0` (the hypothesis `hdiam` of
  `tendstoInMeasure_reversibilityPairing_degreeCutoffMeasure`);
* `hmass_of_degreeMeasureConvergence_of_isValid`,
  `tendstoInMeasure_reversibilityPairing_degreeCutoffMeasure_of_isValid`,
  `tendstoInMeasure_reversibilityPairing_degreeCutoffMeasure_of_D27_of_isValid`: the results of
  `DegreeCutoffMassTight` and `ReversibilityPairingDiscrete` without the hypothesis `hdiam`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Metric LatticeProb
open MarkovProcess (ContinuousPath)
open scoped NNReal ENNReal

namespace MatedCRT.FirstPass.Derived

/-- For a continuous curve, `diam^ε_R(η) > a ≥ 0` iff some parameter interval `[ε(k-1), εk]` contains a time `s`
with `η(s) ∈ B_{R+1}` and two times `t, u` with `|η(t) - η(u)| > a`. -/
theorem ofReal_lt_maxCellDiam_iff {ε R a : ℝ} {η : ℝ → ℂ} (hη : Continuous η) (ha : 0 ≤ a) :
    ENNReal.ofReal a < maxCellDiam ε η R ↔ ∃ k : ℤ,
      (∃ s ∈ Icc (ε * ((k : ℝ) - 1)) (ε * k), η s ∈ ball (0 : ℂ) (R + 1)) ∧
        ∃ t ∈ Icc (ε * ((k : ℝ) - 1)) (ε * k), ∃ u ∈ Icc (ε * ((k : ℝ) - 1)) (ε * k),
          a < dist (η t) (η u) := by
  simp only [maxCellDiam, cell, lt_iSup_iff, exists_prop]
  refine exists_congr fun k => and_congr ?_ ?_
  · constructor
    · rintro ⟨_, ⟨s, hs, rfl⟩, hz⟩
      exact ⟨s, hs, hz⟩
    · rintro ⟨s, hs, hz⟩
      exact ⟨η s, mem_image_of_mem η hs, hz⟩
  · rw [ENNReal.ofReal_lt_ofReal_iff_of_nonneg ha]
    have hb : Bornology.IsBounded (η '' Icc (ε * ((k : ℝ) - 1)) (ε * k)) :=
      (isCompact_Icc.image hη).isBounded
    constructor
    · intro h
      by_contra hne
      refine absurd (Metric.diam_le_of_forall_dist_le ha ?_) (not_le.mpr h)
      rintro _ ⟨t, ht, rfl⟩ _ ⟨u, hu, rfl⟩
      exact not_lt.mp fun h' => hne ⟨t, ht, u, hu, h'⟩
    · rintro ⟨t, ht, u, hu, h⟩
      exact h.trans_le (Metric.dist_le_diam_of_mem hb (mem_image_of_mem η ht) (mem_image_of_mem η hu))

/-- The event `{diam^ε_R > a}` (`a ≥ 0`) is an open subset of `C(ℝ, ℂ)` for the compact-open topology. -/
theorem isOpen_setOf_ofReal_lt_maxCellDiam (ε R : ℝ) {a : ℝ} (ha : 0 ≤ a) :
    IsOpen {η : C(ℝ, ℂ) | ENNReal.ofReal a < maxCellDiam ε (⇑η) R} := by
  have hset : {η : C(ℝ, ℂ) | ENNReal.ofReal a < maxCellDiam ε (⇑η) R} =
      ⋃ k : ℤ, (⋃ s ∈ Icc (ε * ((k : ℝ) - 1)) (ε * k), {η : C(ℝ, ℂ) | η s ∈ ball (0 : ℂ) (R + 1)}) ∩
        ⋃ t ∈ Icc (ε * ((k : ℝ) - 1)) (ε * k), ⋃ u ∈ Icc (ε * ((k : ℝ) - 1)) (ε * k),
          {η : C(ℝ, ℂ) | a < dist (η t) (η u)} := by
    ext η
    simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff, exists_prop, ofReal_lt_maxCellDiam_iff η.continuous ha]
  rw [hset]
  refine isOpen_iUnion fun k => (isOpen_biUnion fun s _ => ?_).inter
    (isOpen_biUnion fun t _ => isOpen_biUnion fun u _ => ?_)
  · exact isOpen_ball.preimage (continuous_eval_const s)
  · exact isOpen_lt continuous_const ((continuous_eval_const t).dist (continuous_eval_const u))

/-- For a proper curve `η` (`η(t) → ∞` as `|t| → ∞`), the times `s` with `|η(s)| ≤ r` are bounded. -/
theorem exists_abs_le_of_norm_le {η : ℝ → ℂ} (hprop : Tendsto η (cocompact ℝ) (cocompact ℂ)) (r : ℝ) :
    ∃ T : ℝ, ∀ s, ‖η s‖ ≤ r → |s| ≤ T := by
  obtain ⟨K, hK, hKc⟩ := Filter.mem_cocompact.1 (hprop (isCompact_closedBall (0 : ℂ) r).compl_mem_cocompact)
  obtain ⟨T, hT⟩ := hK.isBounded.subset_closedBall 0
  refine ⟨T, fun s hs => ?_⟩
  have hsK : s ∈ K := by
    by_contra hsK
    exact hKc hsK (mem_closedBall_zero_iff.2 hs)
  simpa [Real.norm_eq_abs] using mem_closedBall_zero_iff.1 (hT hsK)

/-- **The cell diameters near `B_R` of a continuous proper curve tend to `0`**: for `a > 0` there is `δ > 0` such
that every cell `η([ε(k-1), εk])` meeting `B_{R+1}` has diameter at most `a` whenever `ε < δ`. -/
theorem exists_maxCellDiam_le {η : ℝ → ℂ} (hη : Continuous η)
    (hprop : Tendsto η (cocompact ℝ) (cocompact ℂ)) (R : ℝ) {a : ℝ} (ha : 0 < a) :
    ∃ δ > 0, ∀ ε : ℝ, ε < δ → maxCellDiam ε η R ≤ ENNReal.ofReal a := by
  obtain ⟨T, hT⟩ := exists_abs_le_of_norm_le hprop (R + 1)
  obtain ⟨δ₀, hδ₀, hδ⟩ := Metric.uniformContinuousOn_iff.1
    ((isCompact_Icc (a := -(T + 1)) (b := T + 1)).uniformContinuousOn_of_continuous hη.continuousOn) a ha
  refine ⟨min δ₀ 1, lt_min hδ₀ one_pos, fun ε hε => ?_⟩
  have hε₀ : ε < δ₀ := hε.trans_le (min_le_left _ _)
  have hε₁ : ε < 1 := hε.trans_le (min_le_right _ _)
  unfold maxCellDiam
  refine iSup₂_le fun k hk => ENNReal.ofReal_le_ofReal ?_
  obtain ⟨_, ⟨s, hs, rfl⟩, hsR⟩ := hk
  obtain ⟨hs1, hs2⟩ := abs_le.1 (hT s (mem_ball_zero_iff.1 hsR).le)
  have hkε : ε * ((k : ℝ) - 1) = ε * k - ε := by ring
  have hmem : ∀ t ∈ Icc (ε * ((k : ℝ) - 1)) (ε * k), t ∈ Icc (-(T + 1)) (T + 1) := by
    intro t ht
    obtain ⟨hs3, hs4⟩ := hs
    obtain ⟨ht1, ht2⟩ := ht
    constructor <;> linarith
  refine Metric.diam_le_of_forall_dist_le ha.le ?_
  rintro _ ⟨t, ht, rfl⟩ _ ⟨u, hu, rfl⟩
  refine (hδ t (hmem t ht) u (hmem u hu) ?_).le
  rw [Real.dist_eq, abs_lt]
  obtain ⟨ht1, ht2⟩ := ht
  obtain ⟨hu1, hu2⟩ := hu
  constructor <;> linarith

variable {Ω : Type} [MeasurableSpace Ω]

/-- If almost every `ω` lies in only finitely many of the measurable sets `A n`, then `μ(A n) → 0` for a finite
measure `μ`. -/
theorem tendsto_measure_of_ae_eventually_notMem {μ : Measure Ω} [IsFiniteMeasure μ] {A : ℕ → Set Ω}
    (hA : ∀ n, MeasurableSet (A n)) (h : ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, ω ∉ A n) :
    Tendsto (fun n => μ (A n)) atTop (𝓝 0) := by
  have hlim := tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure atTop MeasurableSet.empty hA
    (h.mono fun ω hω => hω.mono fun n hn => iff_of_false hn (notMem_empty ω))
  rwa [measure_empty] at hlim

/-- **The cell diameters near `B_R` tend to `0` in probability, for every valid environment** (the hypothesis
`hdiam` of `tendstoInMeasure_reversibilityPairing_degreeCutoffMeasure`). Let `S` be a valid environment, `η'` a
version of its curve and `ε_n → 0`. Then for all `R` and `a > 0`, `P[diam^{ε_n}_R > a] → 0`, where `diam^ε_R` is
the largest diameter of the cells `η'([ε(k-1), εk])` meeting `B_{R+1}` (`maxCellDiam`). -/
theorem hdiam_of_isValid {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    {η' : Ω → C(ℝ, ℂ)} (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0)) :
    ∀ R a : ℝ, 0 < a →
      Tendsto (fun n => S.P {ω | ENNReal.ofReal a < maxCellDiam (ε n) (⇑(η' ω)) R}) atTop (𝓝 0) := by
  intro R a ha
  have := hS.isProbabilityMeasure
  obtain ⟨_, _, _, _, _, _, _, _, _, η'', _, hC, htie⟩ := hS.matingOfTrees
  have hm : Measurable η'' := hC.measurable_curves.2.1
  have hEq : ∀ᵐ ω ∂S.P, η' ω = η'' ω := by
    filter_upwards [hae, htie] with ω h1 h2
    exact DFunLike.coe_injective (h1.trans h2.1.symm)
  have hA : ∀ n, MeasurableSet {ω | ENNReal.ofReal a < maxCellDiam (ε n) (⇑(η'' ω)) R} := fun n =>
    hm (isOpen_setOf_ofReal_lt_maxCellDiam (ε n) R ha.le).measurableSet
  have hlim : Tendsto (fun n => S.P {ω | ENNReal.ofReal a < maxCellDiam (ε n) (⇑(η'' ω)) R}) atTop
      (𝓝 0) := by
    refine tendsto_measure_of_ae_eventually_notMem hA ?_
    filter_upwards [hS.ae_tendsto_cocompact, htie] with ω hprop h2
    rw [← h2.1] at hprop
    obtain ⟨δ, hδ, hle⟩ := exists_maxCellDiam_le (η'' ω).continuous hprop R ha
    filter_upwards [hε.eventually (gt_mem_nhds hδ)] with n hn
    exact not_lt.2 (hle (ε n) hn)
  refine hlim.congr fun n => measure_congr ?_
  filter_upwards [hEq] with ω h
  rw [h]

/-- **The mass of the cutoff degree measure is bounded in probability, for every valid environment**:
`hmass_of_degreeMeasureConvergence` with the convergence of the cell diameters supplied by `hdiam_of_isValid`. -/
theorem hmass_of_degreeMeasureConvergence_of_isValid {𝒮 : SpaceFillingSLEModel}
    (hD27 : DegreeMeasureConvergenceStmt 𝒮) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) {η' : Ω → C(ℝ, ℂ)} (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω)
    {ψ : ℂ → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) (hψ0 : ∀ z, 0 ≤ ψ z)
    {ε : ℕ → ℝ} (hε0 : ∀ n, 0 < ε n) (hε : Tendsto ε atTop (𝓝 0)) :
    ∀ a : ℝ, 0 < a → ∃ C : ℝ, ∀ᶠ n in atTop,
      S.P {ω | C < ((degreeCutoffMeasure (S.mult (ε n) ω) (ε n) (vertexPoint (ε n) (⇑(η' ω))) ψ).mass : ℝ)}
        ≤ ENNReal.ofReal a :=
  hmass_of_degreeMeasureConvergence hD27 hγ hγ2 hS hae hψ hψc hψ0 hε0 hε (hdiam_of_isValid hS hae hε)

/-- **The reversibility pairing at the cutoff degree measure tends to `0` in probability, for every valid
environment** (BG20 Lemma 7.6 without Lemma 7.7, step C2): `tendstoInMeasure_reversibilityPairing_degreeCutoffMeasure`
with the convergence of the cell diameters supplied by `hdiam_of_isValid`. -/
theorem tendstoInMeasure_reversibilityPairing_degreeCutoffMeasure_of_isValid {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) {η' : Ω → C(ℝ, ℂ)} (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω)
    (hlf : ∀ᵐ ω ∂S.P, ∀ ε : ℝ, 0 < ε → IsLocallyFiniteMult (S.mult ε ω))
    {f g ψ : ℂ → ℝ} (hfb : ∃ C, ∀ z, |f z| ≤ C) {Kf : ℝ≥0} (hfl : LipschitzWith Kf f)
    (hgb : ∃ C, ∀ z, |g z| ≤ C) {Kg : ℝ≥0} (hgl : LipschitzWith Kg g)
    (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) (hψ0 : ∀ z, 0 ≤ ψ z)
    (hψ1 : EqOn ψ 1 (tsupport f ∪ tsupport g))
    {ε : ℕ → ℝ} (hε0 : ∀ n, 0 < ε n) (hε : Tendsto ε atTop (𝓝 0))
    {t : ℕ → ℝ≥0} {T : ℝ≥0} (htT : ∀ n, t n ≤ T) (htN : ∀ n, ∃ N : ℕ, S.mε (ε n) * (t n : ℝ) = N)
    (hEqLaw : ∀ R a : ℝ, 0 < a → ∃ δ > 0, ∀ᶠ n in atTop,
      S.P {ω | ENNReal.ofReal a < walkLawModulus S η' (ε n) R δ ω} ≤ ENNReal.ofReal a)
    (hmass : ∀ a : ℝ, 0 < a → ∃ C : ℝ, ∀ᶠ n in atTop,
      S.P {ω | C < ((degreeCutoffMeasure (S.mult (ε n) ω) (ε n) (vertexPoint (ε n) (⇑(η' ω))) ψ).mass : ℝ)}
        ≤ ENNReal.ofReal a) :
    TendstoInMeasure S.P (fun n ω => reversibilityPairing f g ψ
        (degreeCutoffMeasure (S.mult (ε n) ω) (ε n) (vertexPoint (ε n) (⇑(η' ω))) ψ)
        (interpWalkLaw S η' (ε n) ω) (t n)) atTop (fun _ => 0) :=
  tendstoInMeasure_reversibilityPairing_degreeCutoffMeasure hS hae hlf hfb hfl hgb hgl hψ hψc hψ0 hψ1
    hε0 hε htT htN hEqLaw (hdiam_of_isValid hS hae hε) hmass

/-- **The reversibility pairing at the cutoff degree measure tends to `0` in probability, from Lemma 2.10, for every
valid environment** (BG20 Lemma 7.6 without Lemma 7.7, step C2):
`tendstoInMeasure_reversibilityPairing_degreeCutoffMeasure_of_D27` with the convergence of the cell diameters
supplied by `hdiam_of_isValid`, for `γ ∈ (0, 2)`. -/
theorem tendstoInMeasure_reversibilityPairing_degreeCutoffMeasure_of_D27_of_isValid {𝒮 : SpaceFillingSLEModel}
    (hD27 : DegreeMeasureConvergenceStmt 𝒮) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) {η' : Ω → C(ℝ, ℂ)} (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω)
    (hlf : ∀ᵐ ω ∂S.P, ∀ ε : ℝ, 0 < ε → IsLocallyFiniteMult (S.mult ε ω))
    {f g ψ : ℂ → ℝ} (hfb : ∃ C, ∀ z, |f z| ≤ C) {Kf : ℝ≥0} (hfl : LipschitzWith Kf f)
    (hgb : ∃ C, ∀ z, |g z| ≤ C) {Kg : ℝ≥0} (hgl : LipschitzWith Kg g)
    (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) (hψ0 : ∀ z, 0 ≤ ψ z)
    (hψ1 : EqOn ψ 1 (tsupport f ∪ tsupport g))
    {ε : ℕ → ℝ} (hε0 : ∀ n, 0 < ε n) (hε : Tendsto ε atTop (𝓝 0))
    {t : ℕ → ℝ≥0} {T : ℝ≥0} (htT : ∀ n, t n ≤ T) (htN : ∀ n, ∃ N : ℕ, S.mε (ε n) * (t n : ℝ) = N)
    (hEqLaw : ∀ R a : ℝ, 0 < a → ∃ δ > 0, ∀ᶠ n in atTop,
      S.P {ω | ENNReal.ofReal a < walkLawModulus S η' (ε n) R δ ω} ≤ ENNReal.ofReal a) :
    TendstoInMeasure S.P (fun n ω => reversibilityPairing f g ψ
        (degreeCutoffMeasure (S.mult (ε n) ω) (ε n) (vertexPoint (ε n) (⇑(η' ω))) ψ)
        (interpWalkLaw S η' (ε n) ω) (t n)) atTop (fun _ => 0) :=
  tendstoInMeasure_reversibilityPairing_degreeCutoffMeasure_of_D27 hD27 hγ hγ2 hS hae hlf hfb hfl hgb hgl hψ hψc
    hψ0 hψ1 hε0 hε htT htN hEqLaw (hdiam_of_isValid hS hae hε)

end MatedCRT.FirstPass.Derived
