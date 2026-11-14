import MatedCRT.FirstPass.Derived.ReversibilityPairingDiscrete
import MatedCRT.FirstPass.Derived.CellDiameterEvent

/-!
# The modulus of continuity in law of the interpolated quenched walk (Berestycki–Gwynne (2020), Prop. 6.1)

For the interpolated quenched walk law `P̃^ε = interpWalkLaw S η' ε : Ω → C(ℂ, Prob(ContinuousPath ℂ))`:

* `pathLevyProkhorovEDist_interpWalkLaw_le`: the deterministic estimate.  If every cell meeting `B_{R+1}`
  has diameter at most `d`, if the vertex-indexed modulus `ω^ε_R(δ)` of the quenched walk laws is at most
  `a`, and `ρ + 2 (ε + d) ≤ δ`, then `LP(P̃^ε_z, P̃^ε_w) ≤ a` for all `|z| ≤ R`, `|z - w| ≤ ρ` (the mixture bound
  of Lattice-Probability applied twice).
* `exists_delta_eventually_interpWalkLaw_modulus`: if the vertex-indexed modulus is small with high probability
  for all large `n` (`hEqLaw`, from the cone scaling), so is the modulus of `P̃^{ε_n}` on `B_L`, with the scale
  `δ` independent of `n`; the cell diameters tend to `0` in probability by Lemma 2.4.
-/

namespace MatedCRT.FirstPass.Derived

open MeasureTheory ProbabilityTheory Filter Topology Set Metric LatticeProb
open MarkovProcess (ContinuousPath)
open scoped NNReal ENNReal

variable {Ω : Type} [MeasurableSpace Ω]

/-- The vertex-indexed modulus is monotone in the scale. -/
theorem walkLawModulus_mono (S : MatedCRTEnv Ω) (η' : Ω → C(ℝ, ℂ)) (ε R : ℝ) {δ δ' : ℝ} (h : δ ≤ δ')
    (ω : Ω) : walkLawModulus S η' ε R δ ω ≤ walkLawModulus S η' ε R δ' ω := by
  unfold walkLawModulus
  refine iSup_mono fun j => iSup_mono fun k => ?_
  exact iSup_mono' fun hjk => ⟨⟨hjk.1, hjk.2.1, hjk.2.2.trans h⟩, le_rfl⟩

/-- **The interpolated walk law at two nearby points** (BG20 Prop. 6.1, step 3): on the event where the
interpolation is defined, if the cells meeting `B_{R+1}` have diameter at most `d`, `ω^ε_R(δ) ≤ a`,
`ρ + 2 (ε + d) ≤ δ` and `ρ + ε + d < 1`, then `LP(P̃^ε_z, P̃^ε_w) ≤ a` for `|z| ≤ R` and `|z - w| ≤ ρ`. -/
theorem pathLevyProkhorovEDist_interpWalkLaw_le (S : MatedCRTEnv Ω) (η' : Ω → C(ℝ, ℂ))
    {ε : ℝ} (hε : 0 ≤ ε) {ω : Ω}
    (hloc : ∀ z, ∃ U ∈ 𝓝 z, {k : ℤ | ∃ y ∈ U, interpWeight (fun k => cell ε (⇑(η' ω)) k) ε k y ≠ 0}.Finite)
    (hpos : ∀ z, ∃ k : ℤ, interpWeight (fun k => cell ε (⇑(η' ω)) k) ε k z ≠ 0)
    {R δ d a ρ : ℝ} (hd0 : 0 ≤ d) (hρ : 0 ≤ ρ) (hδ : ρ + 2 * (ε + d) ≤ δ) (h1 : ρ + ε + d < 1)
    (ha : 0 ≤ a) (hD : maxCellDiam ε (⇑(η' ω)) R ≤ ENNReal.ofReal d)
    (hmod : walkLawModulus S η' ε R δ ω ≤ ENNReal.ofReal a)
    {z w : ℂ} (hz : ‖z‖ ≤ R) (hzw : dist z w ≤ ρ) :
    pathLevyProkhorovEDist (interpWalkLaw S η' ε ω z) (interpWalkLaw S η' ε ω w) ≤ ENNReal.ofReal a := by
  let : PseudoMetricSpace (ContinuousPath ℂ) := dUnifPseudoMetric
  have hOMS : @OpensMeasurableSpace (ContinuousPath ℂ)
      (@UniformSpace.toTopologicalSpace _ (@PseudoMetricSpace.toUniformSpace _ ‹_›)) _ :=
    opensMeasurableSpace_dUnif
  have key : ∀ z' : ℂ, ‖z'‖ ≤ R + ρ → ∀ k : ℤ,
      Metric.infDist z' (cell ε (⇑(η' ω)) k) < ε →
      dist z' (vertexPoint ε (⇑(η' ω)) k) < ε + d ∧
        vertexPoint ε (⇑(η' ω)) k ∈ ball (0 : ℂ) (R + 1) := by
    intro z' hz' k hk
    have hvk : vertexPoint ε (⇑(η' ω)) k ∈ cell ε (⇑(η' ω)) k :=
      ⟨ε * k, ⟨mul_le_mul_of_nonneg_left (by linarith) hε, le_rfl⟩, rfl⟩
    obtain ⟨y, hy, hyz⟩ := (Metric.infDist_lt_iff ⟨_, hvk⟩).1 hk
    have hbdd : Bornology.IsBounded (cell ε (⇑(η' ω)) k) :=
      (isCompact_Icc.image (η' ω).continuous).isBounded
    have hyk := Metric.dist_le_diam_of_mem hbdd hy hvk
    have hz0 := dist_zero_right z'
    have hyball : y ∈ ball (0 : ℂ) (R + 1) := by
      rw [mem_ball]
      have h2 := dist_triangle y z' 0
      have h3 := dist_comm y z'
      linarith
    have hdiam : Metric.diam (cell ε (⇑(η' ω)) k) ≤ d := by
      have h := (le_iSup₂ (f := fun k (_ : (cell ε (⇑(η' ω)) k ∩ ball (0 : ℂ) (R + 1)).Nonempty) =>
        ENNReal.ofReal (Metric.diam (cell ε (⇑(η' ω)) k))) k ⟨y, hy, hyball⟩).trans hD
      exact (ENNReal.ofReal_le_ofReal_iff hd0).1 h
    have hzk : dist z' (vertexPoint ε (⇑(η' ω)) k) < ε + d := by
      have := dist_triangle z' y (vertexPoint ε (⇑(η' ω)) k)
      linarith
    refine ⟨hzk, ?_⟩
    rw [mem_ball]
    have h2 := dist_triangle (vertexPoint ε (⇑(η' ω)) k) z' 0
    have h3 := dist_comm (vertexPoint ε (⇑(η' ω)) k) z'
    linarith
  have hw : ‖w‖ ≤ R + ρ := by
    have h := dist_triangle w z 0
    rw [dist_comm w z, dist_zero_right, dist_zero_right] at h
    linarith
  have hQ : ∀ k k' : ℤ, Metric.infDist z (cell ε (⇑(η' ω)) k) < ε →
      Metric.infDist w (cell ε (⇑(η' ω)) k') < ε →
      levyProkhorovDist
        (walkPathLaw S (fun ω => vertexPoint ε (⇑(η' ω))) (S.mε_nonneg ε) ε k' ω :
          Measure (ContinuousPath ℂ))
        (walkPathLaw S (fun ω => vertexPoint ε (⇑(η' ω))) (S.mε_nonneg ε) ε k ω :
          Measure (ContinuousPath ℂ)) ≤ a := by
    intro k k' hk hk'
    obtain ⟨hzk, hkball⟩ := key z (by linarith) k hk
    obtain ⟨hwk, hk'ball⟩ := key w hw k' hk'
    have hdist : dist (vertexPoint ε (⇑(η' ω)) k') (vertexPoint ε (⇑(η' ω)) k) ≤ δ := by
      have t1 := dist_triangle (vertexPoint ε (⇑(η' ω)) k') w (vertexPoint ε (⇑(η' ω)) k)
      have t2 := dist_triangle w z (vertexPoint ε (⇑(η' ω)) k)
      have t3 := dist_comm (vertexPoint ε (⇑(η' ω)) k') w
      have t4 := dist_comm w z
      linarith
    have hm : pathLevyProkhorovEDist
        (walkPathLaw S (fun ω => vertexPoint ε (⇑(η' ω))) (S.mε_nonneg ε) ε k' ω)
        (walkPathLaw S (fun ω => vertexPoint ε (⇑(η' ω))) (S.mε_nonneg ε) ε k ω)
          ≤ walkLawModulus S η' ε R δ ω :=
      le_iSup₂_of_le k' k (le_iSup_of_le ⟨hk'ball, hkball, hdist⟩ le_rfl)
    exact ENNReal.toReal_le_of_le_ofReal ha (hm.trans hmod)
  have hL1 : ∀ k' : ℤ, Metric.infDist w (cell ε (⇑(η' ω)) k') < ε →
      levyProkhorovDist
        (walkPathLaw S (fun ω => vertexPoint ε (⇑(η' ω))) (S.mε_nonneg ε) ε k' ω :
          Measure (ContinuousPath ℂ))
        (interpLaw (fun k => cell ε (⇑(η' ω)) k) ε hloc hpos
          (fun k => walkPathLaw S (fun ω => vertexPoint ε (⇑(η' ω))) (S.mε_nonneg ε) ε k ω) z :
          Measure (ContinuousPath ℂ)) ≤ a :=
    fun k' hk' => levyProkhorovDist_interpLaw_le hloc hpos
      (fun k => walkPathLaw S (fun ω => vertexPoint ε (⇑(η' ω))) (S.mε_nonneg ε) ε k ω)
      (walkPathLaw S (fun ω => vertexPoint ε (⇑(η' ω))) (S.mε_nonneg ε) ε k' ω) z ha
      (fun k hk => hQ k k' hk hk')
  have hL2 := levyProkhorovDist_interpLaw_le hloc hpos
    (fun k => walkPathLaw S (fun ω => vertexPoint ε (⇑(η' ω))) (S.mε_nonneg ε) ε k ω)
    (interpLaw (fun k => cell ε (⇑(η' ω)) k) ε hloc hpos
      (fun k => walkPathLaw S (fun ω => vertexPoint ε (⇑(η' ω))) (S.mε_nonneg ε) ε k ω) z) w ha
    (fun k' hk' => by rw [levyProkhorovDist_comm]; exact hL1 k' hk')
  rw [interpWalkLaw_eq_of_good S η' hloc hpos z, interpWalkLaw_eq_of_good S η' hloc hpos w]
  show levyProkhorovEDist _ _ ≤ _
  rw [← ENNReal.ofReal_toReal (levyProkhorovEDist_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hL2

/-- **The modulus of continuity in law of the interpolated walk, eventually in `n`** (BG20 Prop. 6.1, step 3).
From the equicontinuity in law of the vertex laws (`hEq`, the output of the cone scaling step) and the
convergence to `0` in probability of the cell diameters: for every `L > 1` there is one scale `δ > 0` such
that, for all large `n`, with probability at least `1 - 1/L` the laws `P̃^{ε_n}_z`, `P̃^{ε_n}_w` with
`|z|, |w| ≤ L`, `|z - w| ≤ δ` are at Lévy–Prokhorov distance at most `1/L`. -/
theorem exists_delta_eventually_interpWalkLaw_modulus {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) {η' : Ω → C(ℝ, ℂ)}
    (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) {eps : ℕ → ℝ} (hε0 : ∀ n, 0 < eps n)
    (hε : Tendsto eps atTop (𝓝 0))
    (hEq : ∀ R a : ℝ, 0 < a → ∃ δ > 0, ∀ᶠ n in atTop,
      S.P {ω | ENNReal.ofReal a < walkLawModulus S η' (eps n) R δ ω} ≤ ENNReal.ofReal a)
    {L : ℝ} (hL : 1 < L) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n in atTop,
      S.P {ω | ∃ z w : ℂ, dist z 0 ≤ L ∧ dist w 0 ≤ L ∧ dist z w ≤ δ ∧
        1 / L < (pathLevyProkhorovEDist (interpWalkLaw S η' (eps n) ω z)
          (interpWalkLaw S η' (eps n) ω w)).toReal} ≤ ENNReal.ofReal (1 / L) := by
  have hLpos : 0 < L := by linarith
  have ha : 0 < 1 / (2 * L) := by positivity
  obtain ⟨δ0, hδ0, hev0⟩ := hEq L (1 / (2 * L)) ha
  obtain ⟨δ1, hδ1def⟩ : ∃ δ1 : ℝ, δ1 = min δ0 1 := ⟨_, rfl⟩
  have hδ1 : 0 < δ1 := by rw [hδ1def]; exact lt_min hδ0 one_pos
  have hδ10 : δ1 ≤ δ0 := by rw [hδ1def]; exact min_le_left _ _
  have hδ11 : δ1 ≤ 1 := by rw [hδ1def]; exact min_le_right _ _
  refine ⟨δ1 / 2, half_pos hδ1, ?_⟩
  have hεn : Tendsto eps atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.2 ⟨hε, Eventually.of_forall hε0⟩
  have hdiam := (MatedCRT.CellDiameterEvent.tendsto_prob_maxCellDiam_nhdsWithin hS hae L (δ1 / 8) (by positivity)).comp hεn
  have hev1 : ∀ᶠ n in atTop, S.P {ω | ENNReal.ofReal (δ1 / 8) < maxCellDiam (eps n) (⇑(η' ω)) L} <
      ENNReal.ofReal (1 / (2 * L)) := hdiam.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 ha))
  have hev2 : ∀ᶠ n in atTop, eps n < δ1 / 8 := hε.eventually (gt_mem_nhds (by positivity))
  filter_upwards [hev0, hev1, hev2] with n h0 h1 h2
  have hgood := hS.ae_interpWeight_good hae (hε0 n)
  have hN : S.P {ω | ¬ ((∀ z, ∃ U ∈ 𝓝 z, {k : ℤ | ∃ y ∈ U,
      interpWeight (fun k => cell (eps n) (⇑(η' ω)) k) (eps n) k y ≠ 0}.Finite) ∧
      ∀ z, ∃ k : ℤ, interpWeight (fun k => cell (eps n) (⇑(η' ω)) k) (eps n) k z ≠ 0)} = 0 :=
    ae_iff.1 hgood
  have hsub : {ω | ∃ z w : ℂ, dist z 0 ≤ L ∧ dist w 0 ≤ L ∧ dist z w ≤ δ1 / 2 ∧
        1 / L < (pathLevyProkhorovEDist (interpWalkLaw S η' (eps n) ω z)
          (interpWalkLaw S η' (eps n) ω w)).toReal} ⊆
      ({ω | ENNReal.ofReal (1 / (2 * L)) < walkLawModulus S η' (eps n) L δ0 ω} ∪
        {ω | ENNReal.ofReal (δ1 / 8) < maxCellDiam (eps n) (⇑(η' ω)) L}) ∪
      {ω | ¬ ((∀ z, ∃ U ∈ 𝓝 z, {k : ℤ | ∃ y ∈ U,
        interpWeight (fun k => cell (eps n) (⇑(η' ω)) k) (eps n) k y ≠ 0}.Finite) ∧
        ∀ z, ∃ k : ℤ, interpWeight (fun k => cell (eps n) (⇑(η' ω)) k) (eps n) k z ≠ 0)} := by
    rintro ω ⟨z, w, hz, hw, hzw, hlt⟩
    by_contra hcon
    simp only [mem_union, mem_ofPred_eq, not_or, not_lt, not_not] at hcon
    obtain ⟨⟨hmod, hD⟩, hloc, hpos⟩ := hcon
    have hmod' : walkLawModulus S η' (eps n) L δ1 ω ≤ ENNReal.ofReal (1 / (2 * L)) :=
      (walkLawModulus_mono S η' (eps n) L hδ10 ω).trans hmod
    have hdet := pathLevyProkhorovEDist_interpWalkLaw_le S η' (hε0 n).le hloc hpos
      (R := L) (δ := δ1) (d := δ1 / 8) (a := 1 / (2 * L)) (ρ := δ1 / 2) (by positivity) (by positivity)
      (by linarith) (by linarith) ha.le hD hmod' (z := z) (w := w)
      (by rwa [← dist_zero_right]) hzw
    have hle := ENNReal.toReal_le_of_le_ofReal ha.le hdet
    have : 1 / (2 * L) < 1 / L := by
      rw [div_lt_div_iff₀ (by positivity) hLpos]
      nlinarith
    linarith
  have hsum : ENNReal.ofReal (1 / (2 * L)) + ENNReal.ofReal (1 / (2 * L)) = ENNReal.ofReal (1 / L) := by
    rw [← ENNReal.ofReal_add ha.le ha.le]
    congr 1
    field_simp
    ring
  calc _ ≤ _ := measure_mono hsub
    _ ≤ _ := measure_union_le _ _
    _ ≤ (S.P {ω | ENNReal.ofReal (1 / (2 * L)) < walkLawModulus S η' (eps n) L δ0 ω} +
          S.P {ω | ENNReal.ofReal (δ1 / 8) < maxCellDiam (eps n) (⇑(η' ω)) L}) +
        S.P {ω | ¬ ((∀ z, ∃ U ∈ 𝓝 z, {k : ℤ | ∃ y ∈ U,
          interpWeight (fun k => cell (eps n) (⇑(η' ω)) k) (eps n) k y ≠ 0}.Finite) ∧
          ∀ z, ∃ k : ℤ, interpWeight (fun k => cell (eps n) (⇑(η' ω)) k) (eps n) k z ≠ 0)} :=
        add_le_add (measure_union_le _ _) le_rfl
    _ ≤ (ENNReal.ofReal (1 / (2 * L)) + ENNReal.ofReal (1 / (2 * L))) + 0 :=
        add_le_add (add_le_add h0 h1.le) (le_of_eq hN)
    _ = ENNReal.ofReal (1 / L) := by rw [add_zero, hsum]

end MatedCRT.FirstPass.Derived
