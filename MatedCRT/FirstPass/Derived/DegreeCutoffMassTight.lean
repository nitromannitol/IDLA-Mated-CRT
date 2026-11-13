import MatedCRT.FirstPass.Derived.ReversibilityPairingDiscrete
import MatedCRT.FirstPass.Derived.DegreeWeightedMeasureCells
import MatedCRT.FirstPass.LPBridge.LQGTestIntegralMeasurable
import MatedCRT.Draft.Section2

/-!
# The mass of the cutoff degree measure is bounded in probability (BG20 Lemma 7.6, step C2)

Let `S` be a valid environment, `ψ ≥ 0` a continuous compactly supported cutoff with `supp ψ ⊆ B̄_R`, and
`ν^ε = Σ_x ε deg^ε(x) ψ(η(εx)) δ_{η(εx)}` the cutoff degree measure (`degreeCutoffMeasure`). Each cell `H^ε_x` has
`μ_h`-mass `ε` (area parametrization), so when the cells `H^ε_x` with `η(εx) ∈ supp ψ` have diameter at most `1`,
the mass of `ν^ε` is at most `sup ψ · ∫ χ dμ^ε_h` for a bump `χ = 1` on `B̄_{R+1}`, where `μ^ε_h` is the measure
equal to `deg^ε(x) μ_h` on each cell (`degreeWeightedMeasure`). By Lemma 2.10 (`DegreeMeasureConvergenceStmt`),
`∫ χ dμ^ε_h → 6 ∫ χ dμ_h` in probability, and `ω ↦ ∫ χ dμ_h` is an almost everywhere measurable real random
variable (`frozenLQGTestIntegralMeasurable_holds`), hence bounded in probability.

* `mass_degreeCutoffMeasure`: the mass of `ν^ε` is the sum of its weights;
* `mass_degreeCutoffMeasure_le_integral_degreeWeightedMeasure`: the deterministic bound
  `ν^ε(ℂ) ≤ sup ψ · ∫ χ dμ^ε_h`;
* `hmass_of_degreeMeasureConvergence`: the mass of `ν^{ε_n}` is bounded in probability along `ε_n → 0⁺`, given
  Lemma 2.10 and the convergence of the cell diameters near `supp ψ` to `0` in probability;
* `tendstoInMeasure_reversibilityPairing_degreeCutoffMeasure_of_D27`: the reversibility pairing at the cutoff
  degree measure tends to `0` in probability, with the mass bound supplied by Lemma 2.10.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Metric LatticeProb
open MarkovProcess (ContinuousPath)
open scoped NNReal ENNReal

namespace MatedCRT.FirstPass.Derived

/-- The mass of the cutoff degree measure `ν = Σ_{x ∈ W} ε deg(x) ψ(v x) δ_{v x}` is the sum of its weights over the
window `W` of the vertices with `v x ∈ supp ψ`. -/
theorem mass_degreeCutoffMeasure (m : ℤ → ℤ → ℕ) {ε : ℝ} (hε : 0 ≤ ε) (v : ℤ → ℂ) {ψ : ℂ → ℝ}
    (hψ0 : ∀ z, 0 ≤ ψ z) :
    ((degreeCutoffMeasure m ε v ψ).mass : ℝ) =
      ∑ k ∈ vertexWindow v (tsupport ψ), degreeCutoffWeight m ε v ψ k := by
  have hc : ∀ k, 0 ≤ degreeCutoffWeight m ε v ψ k :=
    fun k => mul_nonneg (mul_nonneg hε (Nat.cast_nonneg _)) (hψ0 _)
  have h1 : ((degreeCutoffMeasure m ε v ψ).mass : ℝ) =
      ∫ _z, (1 : ℝ) ∂((degreeCutoffMeasure m ε v ψ : FiniteMeasure ℂ) : Measure ℂ) := by
    rw [integral_const, smul_eq_mul, mul_one, measureReal_def, ← FiniteMeasure.ennreal_mass,
      ENNReal.coe_toReal]
  rw [h1]
  show ∫ _z, (1 : ℝ) ∂(atomicMeasure (vertexWindow v (tsupport ψ)) (degreeCutoffWeight m ε v ψ) v) = _
  rw [integral_atomicMeasure _ hc]
  simp

/-- **The mass of the cutoff degree measure against the degree-weighted measure.** Let `η` be area-parametrized for
`μ` and proper, `ε > 0`, `0 ≤ ψ ≤ C_ψ` compactly supported with `supp ψ ⊆ B̄_R`, and `χ ≥ 0` continuous, compactly
supported and `1` on `B̄_{R+1}`. If the cells `H^ε_k` with `η(εk) ∈ supp ψ` have diameter at most `1`, then
`ν^ε(ℂ) = Σ_{η(εk) ∈ supp ψ} ε deg(k) ψ(η(εk)) ≤ C_ψ ∫ χ dμ^ε`: each such cell lies in `B̄_{R+1}` and has
`μ`-mass `ε = ∫_{H^ε_k} χ dμ`. -/
theorem mass_degreeCutoffMeasure_le_integral_degreeWeightedMeasure {m : ℤ → ℤ → ℕ} {ε : ℝ}
    {η : ℝ → ℂ} {μ : Measure ℂ} (hpar : IsAreaParametrized μ η)
    (hp : Tendsto η (cocompact ℝ) (cocompact ℂ)) (hε : 0 < ε) {ψ : ℂ → ℝ} (hψ0 : ∀ z, 0 ≤ ψ z)
    (hψc : HasCompactSupport ψ) {Cψ : ℝ} (hCψ : ∀ z, ψ z ≤ Cψ) {R : ℝ}
    (hψR : tsupport ψ ⊆ closedBall (0 : ℂ) R) {χ : ℂ → ℝ} (hχ : Continuous χ)
    (hχc : HasCompactSupport χ) (hχ0 : ∀ z, 0 ≤ χ z)
    (hχ1 : ∀ z ∈ closedBall (0 : ℂ) (R + 1), χ z = 1)
    (hdiam : ∀ k, vertexPoint ε η k ∈ tsupport ψ → diam (cell ε η k) ≤ 1) :
    ((degreeCutoffMeasure m ε (vertexPoint ε η) ψ).mass : ℝ) ≤
      Cψ * ∫ x, χ x ∂degreeWeightedMeasure m ε η μ := by
  have hη : Continuous η := hpar.1
  have hCψ0 : 0 ≤ Cψ := (hψ0 0).trans (hCψ 0)
  have hfinW : (vertexPoint ε η ⁻¹' tsupport ψ).Finite :=
    vertexPoint_preimage_finite hε hη hp hψc.isCompact
  have hvk : ∀ k, vertexPoint ε η k ∈ cell ε η k := fun k =>
    ⟨ε * k, ⟨mul_le_mul_of_nonneg_left (by linarith) hε.le, le_rfl⟩, rfl⟩
  have hcm : ∀ k, MeasurableSet (cell ε η k) := fun k => (isCompact_cell hη ε k).isClosed.measurableSet
  obtain ⟨t, ht⟩ : ∃ t : Finset ℤ, ∀ k, k ∈ t ↔ (cell ε η k ∩ tsupport χ).Nonempty :=
    ⟨(cellVertices_finite_of_isCompact hη hp hε hχc.isCompact).toFinset, fun k => by
      rw [Set.Finite.mem_toFinset]
      rfl⟩
  have hvan : ∀ k ∉ t, ∀ x ∈ cell ε η k, χ x = 0 := by
    intro k hk x hx
    by_contra h
    exact hk ((ht k).2 ⟨x, hx, subset_tsupport χ h⟩)
  have hint : ∀ k ∈ t, IntegrableOn χ (cell ε η k) μ := fun k _ => hpar.integrableOn_cell hε hχ k
  rw [integral_degreeWeightedMeasure_eq_sum hχ hη t hvan hint,
    mass_degreeCutoffMeasure m hε.le (vertexPoint ε η) hψ0, Finset.mul_sum]
  have hR : ∀ k, vertexPoint ε η k ∈ tsupport ψ → ‖vertexPoint ε η k‖ ≤ R := fun k hk => by
    simpa [mem_closedBall, dist_zero_right] using hψR hk
  have hcell : ∀ k, vertexPoint ε η k ∈ tsupport ψ → ∫ x in cell ε η k, χ x ∂μ = ε := by
    intro k hk
    have hsub : ∀ x ∈ cell ε η k, χ x = 1 := by
      intro x hx
      refine hχ1 x ?_
      have hd : dist x (vertexPoint ε η k) ≤ 1 :=
        (dist_le_diam_of_mem (isCompact_cell hη ε k).isBounded hx (hvk k)).trans (hdiam k hk)
      rw [mem_closedBall, dist_zero_right]
      have h1 : ‖x‖ ≤ ‖vertexPoint ε η k‖ + dist x (vertexPoint ε η k) := by
        rw [dist_eq_norm]
        calc ‖x‖ = ‖vertexPoint ε η k + (x - vertexPoint ε η k)‖ := by rw [add_sub_cancel]
          _ ≤ ‖vertexPoint ε η k‖ + ‖x - vertexPoint ε η k‖ := norm_add_le _ _
      linarith [hR k hk]
    rw [setIntegral_congr_fun (hcm k) hsub, setIntegral_const, smul_eq_mul, mul_one, measureReal_def,
      hpar.measure_cell hε k, ENNReal.toReal_ofReal hε.le]
  have hWt : vertexWindow (vertexPoint ε η) (tsupport ψ) ⊆ t := by
    intro k hk
    rw [mem_vertexWindow hfinW] at hk
    refine (ht k).2 ⟨vertexPoint ε η k, hvk k, subset_tsupport χ ?_⟩
    rw [Function.mem_support, hχ1 _ (by rw [mem_closedBall, dist_zero_right]; linarith [hR k hk])]
    exact one_ne_zero
  calc ∑ k ∈ vertexWindow (vertexPoint ε η) (tsupport ψ), degreeCutoffWeight m ε (vertexPoint ε η) ψ k
      ≤ ∑ k ∈ vertexWindow (vertexPoint ε η) (tsupport ψ),
          Cψ * ((matedDeg m k : ℝ) * ∫ x in cell ε η k, χ x ∂μ) := by
        refine Finset.sum_le_sum fun k hk => ?_
        rw [mem_vertexWindow hfinW] at hk
        rw [hcell k hk]
        have hdeg : (matedDeg m k : ℝ) = (mdeg m k : ℝ) := rfl
        rw [hdeg, degreeCutoffWeight]
        have h0 : 0 ≤ ε * (mdeg m k : ℝ) := mul_nonneg hε.le (Nat.cast_nonneg _)
        calc ε * (mdeg m k : ℝ) * ψ (vertexPoint ε η k) ≤ ε * (mdeg m k : ℝ) * Cψ :=
              mul_le_mul_of_nonneg_left (hCψ _) h0
          _ = Cψ * ((mdeg m k : ℝ) * ε) := by ring
    _ ≤ ∑ k ∈ t, Cψ * ((matedDeg m k : ℝ) * ∫ x in cell ε η k, χ x ∂μ) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg hWt fun k _ _ => ?_
        exact mul_nonneg hCψ0 (mul_nonneg (Nat.cast_nonneg _)
          (setIntegral_nonneg (hcm k) fun x _ => hχ0 x))

variable {Ω : Type} [MeasurableSpace Ω]

/-- **The mass of the cutoff degree measure is bounded in probability** (the hypothesis `hmass` of
`tendstoInMeasure_reversibilityPairing_degreeCutoffMeasure`). Let `S` be a valid environment with `γ ∈ (0, 2)`,
`η'` a version of its curve, `ψ ≥ 0` continuous and compactly supported, and `ε_n → 0⁺`. Assume Lemma 2.10
(`DegreeMeasureConvergenceStmt`) and that the cell diameters near `B_{R+1}` tend to `0` in probability (`hdiam`, as
in `tendstoInMeasure_reversibilityPairing_degreeCutoffMeasure`). Then for every `a > 0` there is `C` with
`P[ν^{ε_n}(ℂ) > C] ≤ a` for all large `n`. -/
theorem hmass_of_degreeMeasureConvergence {𝒮 : SpaceFillingSLEModel}
    (hD27 : DegreeMeasureConvergenceStmt 𝒮) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) {η' : Ω → C(ℝ, ℂ)} (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω)
    {ψ : ℂ → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) (hψ0 : ∀ z, 0 ≤ ψ z)
    {ε : ℕ → ℝ} (hε0 : ∀ n, 0 < ε n) (hε : Tendsto ε atTop (𝓝 0))
    (hdiam : ∀ R a : ℝ, 0 < a →
      Tendsto (fun n => S.P {ω | ENNReal.ofReal a < maxCellDiam (ε n) (⇑(η' ω)) R}) atTop (𝓝 0)) :
    ∀ a : ℝ, 0 < a → ∃ C : ℝ, ∀ᶠ n in atTop,
      S.P {ω | C < ((degreeCutoffMeasure (S.mult (ε n) ω) (ε n) (vertexPoint (ε n) (⇑(η' ω))) ψ).mass : ℝ)}
        ≤ ENNReal.ofReal a := by
  intro a ha
  have := hS.isProbabilityMeasure
  have ha3 : 0 < a / 3 := by linarith
  obtain ⟨Cψ, hCψ⟩ : ∃ C, ∀ z, ψ z ≤ C := by
    obtain ⟨C, hC⟩ := hψ.bounded_above_of_compact_support hψc
    exact ⟨C, fun z => (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hC z)⟩
  have hCψ0 : 0 ≤ Cψ := (hψ0 0).trans (hCψ 0)
  obtain ⟨R, hR⟩ := hψc.isCompact.isBounded.subset_closedBall 0
  obtain ⟨χ, hχ1, -, hχc, hχ01⟩ := exists_continuous_one_zero_of_isCompact
    (isCompact_closedBall (0 : ℂ) (R + 1)) isClosed_empty (disjoint_empty _)
  -- the limit `6 ∫ χ dμ_h` is an a.e. measurable real random variable, hence bounded in probability
  have hYm : AEMeasurable (fun ω => 6 * ∫ x, χ x ∂S.μ ω) S.P :=
    (MatedCRT.frozenLQGTestIntegralMeasurable_holds γ hγ hγ2 Ω S.P S.hC S.hcirc S.μ
      ⟨hS.isProbabilityMeasure, hS.isQuantumCone, hS.isLQGMeasure⟩ χ χ.continuous hχc).const_mul 6
  have hYY' := hYm.ae_eq_mk
  obtain ⟨M, hM⟩ : ∃ M : ℕ, S.P {ω | (M : ℝ) < hYm.mk _ ω} ≤ ENNReal.ofReal (a / 3) := by
    have hanti : Antitone (fun M : ℕ => {ω | (M : ℝ) < hYm.mk _ ω}) := by
      intro i j hij ω hω
      exact lt_of_le_of_lt (Nat.cast_le.2 hij) (show (j : ℝ) < hYm.mk _ ω from hω)
    have hempty : (⋂ M : ℕ, {ω | (M : ℝ) < hYm.mk _ ω}) = ∅ := by
      refine subset_empty_iff.1 fun ω hω => ?_
      obtain ⟨M, hM⟩ := exists_nat_ge (hYm.mk _ ω)
      exact absurd (mem_iInter.1 hω M) (not_lt.2 hM)
    have hlim := tendsto_measure_iInter_atTop (μ := S.P)
      (fun M : ℕ => (measurableSet_lt measurable_const hYm.measurable_mk).nullMeasurableSet) hanti
      ⟨0, measure_ne_top _ _⟩
    rw [hempty, measure_empty] at hlim
    exact (hlim.eventually (ge_mem_nhds (ENNReal.ofReal_pos.2 ha3))).exists
  -- Lemma 2.10 along `ε_n` for the bump `χ`, and the cell diameters
  have hε' : Tendsto ε atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.2 ⟨hε, Eventually.of_forall hε0⟩
  have hdev := ((hD27 γ hγ hγ2 Ω S hS χ χ.continuous hχc 1 one_pos).comp hε').eventually
    (ge_mem_nhds (ENNReal.ofReal_pos.2 ha3))
  have hdia := (hdiam R 1 one_pos).eventually (ge_mem_nhds (ENNReal.ofReal_pos.2 ha3))
  have hG : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω ∧ IsAreaParametrized (S.μ ω) (S.η ω) ∧
      Tendsto (S.η ω) (cocompact ℝ) (cocompact ℂ) ∧ 6 * ∫ x, χ x ∂S.μ ω = hYm.mk _ ω := by
    filter_upwards [hae, hS.isAreaParametrized, hS.ae_tendsto_cocompact, hYY'] with ω h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  refine ⟨Cψ * (M + 1), ?_⟩
  filter_upwards [hdev, hdia] with n hn1 hn2
  have hsub : {ω | Cψ * (M + 1) <
      ((degreeCutoffMeasure (S.mult (ε n) ω) (ε n) (vertexPoint (ε n) (⇑(η' ω))) ψ).mass : ℝ)} ≤ᵐ[S.P]
      ({ω | ENNReal.ofReal 1 < maxCellDiam (ε n) (⇑(η' ω)) R} ∪
        {ω | 1 < |∫ x, χ x ∂degreeWeightedMeasure (S.mult (ε n) ω) (ε n) (S.η ω) (S.μ ω) -
          6 * ∫ x, χ x ∂S.μ ω|}) ∪ {ω | (M : ℝ) < hYm.mk _ ω} := by
    filter_upwards [hG] with ω hg hω
    obtain ⟨h1, h2, h3, h4⟩ := hg
    by_contra hnot
    have hd : maxCellDiam (ε n) (⇑(η' ω)) R ≤ ENNReal.ofReal 1 :=
      not_lt.1 fun h => hnot (Or.inl (Or.inl h))
    have hdv : |∫ x, χ x ∂degreeWeightedMeasure (S.mult (ε n) ω) (ε n) (S.η ω) (S.μ ω) -
        6 * ∫ x, χ x ∂S.μ ω| ≤ 1 :=
      not_lt.1 fun h => hnot (Or.inl (Or.inr h))
    have hY : hYm.mk _ ω ≤ (M : ℝ) := not_lt.1 fun h => hnot (Or.inr h)
    rw [h1] at hd
    have hdiamk : ∀ k, vertexPoint (ε n) (S.η ω) k ∈ tsupport ψ →
        diam (cell (ε n) (S.η ω) k) ≤ 1 := by
      intro k hk
      have hne : (cell (ε n) (S.η ω) k ∩ ball (0 : ℂ) (R + 1)).Nonempty := by
        refine ⟨vertexPoint (ε n) (S.η ω) k,
          ⟨ε n * k, ⟨mul_le_mul_of_nonneg_left (by linarith) (hε0 n).le, le_rfl⟩, rfl⟩, ?_⟩
        have := hR hk
        rw [mem_closedBall] at this
        rw [mem_ball]
        linarith
      have hle : ENNReal.ofReal (diam (cell (ε n) (S.η ω) k)) ≤ ENNReal.ofReal 1 :=
        (le_iSup₂ (f := fun (k : ℤ) (_ : (cell (ε n) (S.η ω) k ∩ ball (0 : ℂ) (R + 1)).Nonempty) =>
          ENNReal.ofReal (diam (cell (ε n) (S.η ω) k))) k hne).trans hd
      exact (ENNReal.ofReal_le_ofReal_iff zero_le_one).1 hle
    have hmass := mass_degreeCutoffMeasure_le_integral_degreeWeightedMeasure (m := S.mult (ε n) ω) h2 h3
      (hε0 n) hψ0 hψc hCψ hR χ.continuous hχc (fun z => (hχ01 z).1) (fun z hz => hχ1 hz) hdiamk
    have hω' : Cψ * (M + 1) <
        ((degreeCutoffMeasure (S.mult (ε n) ω) (ε n) (vertexPoint (ε n) (S.η ω)) ψ).mass : ℝ) := by
      rw [← h1]
      exact hω
    have hX : ∫ x, χ x ∂degreeWeightedMeasure (S.mult (ε n) ω) (ε n) (S.η ω) (S.μ ω) ≤ M + 1 := by
      have := (abs_le.1 hdv).2
      linarith
    have := mul_le_mul_of_nonneg_left hX hCψ0
    linarith
  calc _ ≤ S.P (({ω | ENNReal.ofReal 1 < maxCellDiam (ε n) (⇑(η' ω)) R} ∪
        {ω | 1 < |∫ x, χ x ∂degreeWeightedMeasure (S.mult (ε n) ω) (ε n) (S.η ω) (S.μ ω) -
          6 * ∫ x, χ x ∂S.μ ω|}) ∪ {ω | (M : ℝ) < hYm.mk _ ω}) := measure_mono_ae hsub
    _ ≤ S.P {ω | ENNReal.ofReal 1 < maxCellDiam (ε n) (⇑(η' ω)) R} +
        S.P {ω | 1 < |∫ x, χ x ∂degreeWeightedMeasure (S.mult (ε n) ω) (ε n) (S.η ω) (S.μ ω) -
          6 * ∫ x, χ x ∂S.μ ω|} + S.P {ω | (M : ℝ) < hYm.mk _ ω} :=
        (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
    _ ≤ ENNReal.ofReal (a / 3) + ENNReal.ofReal (a / 3) + ENNReal.ofReal (a / 3) :=
        add_le_add (add_le_add hn2 hn1) hM
    _ = ENNReal.ofReal a := by
        rw [← ENNReal.ofReal_add ha3.le ha3.le, ← ENNReal.ofReal_add (by linarith) ha3.le]
        congr 1
        ring

/-- **The reversibility pairing at the cutoff degree measure tends to `0` in probability, from Lemma 2.10**
(BG20 Lemma 7.6 without Lemma 7.7, step C2). `tendstoInMeasure_reversibilityPairing_degreeCutoffMeasure` with the
bound in probability on the mass of `ν^{ε_n}` supplied by Lemma 2.10 (`DegreeMeasureConvergenceStmt`) through
`hmass_of_degreeMeasureConvergence`, for `γ ∈ (0, 2)`. -/
theorem tendstoInMeasure_reversibilityPairing_degreeCutoffMeasure_of_D27 {𝒮 : SpaceFillingSLEModel}
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
      S.P {ω | ENNReal.ofReal a < walkLawModulus S η' (ε n) R δ ω} ≤ ENNReal.ofReal a)
    (hdiam : ∀ R a : ℝ, 0 < a →
      Tendsto (fun n => S.P {ω | ENNReal.ofReal a < maxCellDiam (ε n) (⇑(η' ω)) R}) atTop (𝓝 0)) :
    TendstoInMeasure S.P (fun n ω => reversibilityPairing f g ψ
        (degreeCutoffMeasure (S.mult (ε n) ω) (ε n) (vertexPoint (ε n) (⇑(η' ω))) ψ)
        (interpWalkLaw S η' (ε n) ω) (t n)) atTop (fun _ => 0) :=
  tendstoInMeasure_reversibilityPairing_degreeCutoffMeasure hS hae hlf hfb hfl hgb hgl hψ hψc hψ0 hψ1
    hε0 hε htT htN hEqLaw hdiam
    (hmass_of_degreeMeasureConvergence hD27 hγ hγ2 hS hae hψ hψc hψ0 hε0 hε hdiam)

end MatedCRT.FirstPass.Derived
