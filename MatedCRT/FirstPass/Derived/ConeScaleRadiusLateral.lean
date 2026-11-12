import MatedCRT.FirstPass.Derived.ConeScaleRadiusMeasurable
import MatedCRT.FirstPass.Derived.ConeLateralDilation
import MatedCRT.FirstPass.Derived.ConeLateralContinuity
import LatticeProb.Prob.RandomIndexInvariance

/-!
# The lateral part of a quantum cone at the random scale radius

For a `γ`-quantum cone the cone scale radius `R_b` is a function of the radial process alone (almost surely), the
lateral part is independent of the radial process, and the lateral circle averages are invariant in law under every
fixed dilation `x ↦ R x` (`map_lateralCircle_dilate_cone`).  Here it is shown that the invariance persists at the
random radius `R_b`, jointly with the radial process: for finitely many circles `q_1, …, q_k` avoiding the origin,
the pair (radial process, lateral circle averages along the circles `R_b q_j`) has the product law
(radial process) ⊗ (lateral circle averages along the circles `q_j`).

The proof discretises the radius, `R_b ≈ ⌈2^n R_b⌉ / 2^n`, so that the index of the dilation takes countably many
values (exact invariance by independence), and passes to the limit `n → ∞` by the almost sure continuity of the
lateral circle averages on the nonsingular circles (`LatticeProb.map_pair_randomIndex_of_indepFun` and
`LatticeProb.map_pair_eq_of_tendsto_ae`).

The scale radius is read from the radial pair through rational radii only (`radScale`), which makes it a
*measurable* function of the radial pair although the supremum over all radii is not.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set HarmonicBalls
open scoped NNReal ENNReal Classical

namespace MatedCRT.FirstPass.Derived

/-- The radial process of a field as a pair of paths `(t ↦ h_{e^{-t}}(0), s ↦ h_{e^s}(0))`. -/
abbrev RadialPair : Type := (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ)

/-- The circle average at the origin `h_r(0)` read off a radial pair. -/
noncomputable def radLevel (p : RadialPair) (r : ℝ) : ℝ :=
  if 1 ≤ r then p.2 (Real.toNNReal (Real.log r)) else p.1 (Real.toNNReal (-Real.log r))

lemma radLevel_radialProcess (hc : ℝ → ℂ → ℝ) {r : ℝ} (hr : 0 < r) :
    radLevel (radialProcess hc) r = hc r 0 := by
  unfold radLevel radialProcess
  by_cases h1 : 1 ≤ r
  · have hl : 0 ≤ Real.log r := Real.log_nonneg h1
    simp only [h1, ↓reduceIte, Real.coe_toNNReal _ hl, Real.exp_log hr]
  · have hl : 0 ≤ -Real.log r := by
      have := Real.log_neg hr (not_le.1 h1)
      linarith
    simp only [h1, ↓reduceIte, Real.coe_toNNReal _ hl, neg_neg, Real.exp_log hr]

lemma measurable_radLevel (r : ℝ) : Measurable fun p : RadialPair => radLevel p r := by
  by_cases h1 : 1 ≤ r
  · simp only [radLevel, h1, ↓reduceIte]
    exact (measurable_pi_apply _).comp measurable_snd
  · simp only [radLevel, h1, ↓reduceIte]
    exact (measurable_pi_apply _).comp measurable_fst

/-- The countable event of `lt_scaleRadius_iff`, on radial pairs. -/
def radWitness (γ b x : ℝ) : Set RadialPair :=
  {p | ∃ n m : ℕ, ∀ k : ℕ, ∃ q : ℚ, (q : ℝ) ∈ Ioo (x + 1 / ((n : ℝ) + 1)) (x + m + 2) ∧
        radLevel p q + lqgQ γ * Real.log q - γ⁻¹ * Real.log b < 1 / ((k : ℝ) + 1)}

lemma measurableSet_radWitness (γ b : ℝ) {x : ℝ} (hx : 0 ≤ x) : MeasurableSet (radWitness γ b x) :=
  measurableSet_scaleRadius_witness (hcirc := fun (p : RadialPair) r (_ : ℂ) => radLevel p r) γ b
    (fun r _ _ => measurable_radLevel r) hx

lemma radialProcess_mem_radWitness_iff (γ b : ℝ) (hc : ℝ → ℂ → ℝ) {x : ℝ} (hx : 0 ≤ x) :
    radialProcess hc ∈ radWitness γ b x ↔ ∃ n m : ℕ, ∀ k : ℕ, ∃ q : ℚ,
      (q : ℝ) ∈ Ioo (x + 1 / ((n : ℝ) + 1)) (x + m + 2) ∧
        hc q 0 + lqgQ γ * Real.log q - γ⁻¹ * Real.log b < 1 / ((k : ℝ) + 1) := by
  have hq0 : ∀ (n m : ℕ) (q : ℚ), (q : ℝ) ∈ Ioo (x + 1 / ((n : ℝ) + 1)) (x + m + 2) → 0 < (q : ℝ) := by
    intro n m q hq
    have : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith [hq.1]
  constructor
  · rintro ⟨n, m, h⟩
    refine ⟨n, m, fun k => ?_⟩
    obtain ⟨q, hq, hlt⟩ := h k
    refine ⟨q, hq, ?_⟩
    rwa [radLevel_radialProcess hc (hq0 n m q hq)] at hlt
  · rintro ⟨n, m, h⟩
    refine ⟨n, m, fun k => ?_⟩
    obtain ⟨q, hq, hlt⟩ := h k
    refine ⟨q, hq, ?_⟩
    rwa [radLevel_radialProcess hc (hq0 n m q hq)]

/-- The cone scale radius as a function of the radial pair, through rational radii only: the supremum of the
nonnegative rationals `q` whose witness event holds. -/
noncomputable def radScale (γ b : ℝ) (p : RadialPair) : ℝ :=
  ⨆ q : ℚ, if 0 ≤ (q : ℝ) ∧ p ∈ radWitness γ b q then (q : ℝ) else 0

lemma measurable_radScale (γ b : ℝ) : Measurable (radScale γ b) := by
  have hq : ∀ q : ℚ, Measurable fun p : RadialPair =>
      if 0 ≤ (q : ℝ) ∧ p ∈ radWitness γ b q then (q : ℝ) else 0 := by
    intro q
    by_cases hq : 0 ≤ (q : ℝ)
    · have hs : MeasurableSet (radWitness γ b q) := measurableSet_radWitness γ b hq
      have : (fun p : RadialPair => if 0 ≤ (q : ℝ) ∧ p ∈ radWitness γ b q then (q : ℝ) else 0) =
          (radWitness γ b q).indicator (fun _ => (q : ℝ)) := by
        ext p
        simp [Set.indicator, hq]
      rw [this]
      exact measurable_const.indicator hs
    · simp [hq]
  have := Measurable.iSup hq
  convert this using 1
  ext p
  simp only [radScale]

/-- **The scale radius is a measurable function of the radial pair, almost surely.** -/
lemma radScale_radialProcess_ae {Ω : Type*} [MeasurableSpace Ω] {γ : ℝ} {P : Measure Ω}
    [IsProbabilityMeasure P] {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (h : IsQuantumCone γ P hC hcirc) (b : ℝ) :
    ∀ᵐ ω ∂P, radScale γ b (radialProcess (hcirc ω)) = coneScaleRadius γ (hcirc ω) b := by
  filter_upwards [h.ae_continuousOn_circle, ae_coneScaleRadius_spec hγ0 hγ2 h b] with ω h1 h2
  obtain ⟨hR, hs1, hs2⟩ := h2
  have key : ∀ q : ℚ, 0 ≤ (q : ℝ) →
      (radialProcess (hcirc ω) ∈ radWitness γ b q ↔ (q : ℝ) < coneScaleRadius γ (hcirc ω) b) := by
    intro q hq
    rw [radialProcess_mem_radWitness_iff γ b _ hq]
    exact (lt_scaleRadius_iff h1 hs1 hs2 hq).symm
  have hbdd : BddAbove (range fun q : ℚ =>
      if 0 ≤ (q : ℝ) ∧ radialProcess (hcirc ω) ∈ radWitness γ b q then (q : ℝ) else 0) := by
    refine ⟨coneScaleRadius γ (hcirc ω) b, ?_⟩
    rintro _ ⟨q, rfl⟩
    by_cases hq : 0 ≤ (q : ℝ) ∧ radialProcess (hcirc ω) ∈ radWitness γ b q
    · simp only [hq, and_self, ↓reduceIte]
      exact ((key q hq.1).1 hq.2).le
    · simp only [hq, ↓reduceIte]
      exact hR.le
  unfold radScale
  apply le_antisymm
  · refine ciSup_le fun q => ?_
    by_cases hq : 0 ≤ (q : ℝ) ∧ radialProcess (hcirc ω) ∈ radWitness γ b q
    · simp only [hq, and_self, ↓reduceIte]
      exact ((key q hq.1).1 hq.2).le
    · simp only [hq, ↓reduceIte]
      exact hR.le
  · by_contra hlt
    rw [not_le] at hlt
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (max_lt hlt hR)
    have hq0 : 0 ≤ (q : ℝ) := (le_max_right _ _).trans hq1.le
    have hqW : radialProcess (hcirc ω) ∈ radWitness γ b q := (key q hq0).2 hq2
    have hle := le_ciSup hbdd q
    have hterm : (if 0 ≤ (q : ℝ) ∧ radialProcess (hcirc ω) ∈ radWitness γ b q then (q : ℝ) else 0) = q := by
      simp only [hq0, hqW, and_self, ↓reduceIte]
    simp only [hterm] at hle
    exact absurd (hle.trans_lt ((le_max_left _ _).trans_lt hq1)) (lt_irrefl _)


/-- The dilation `(r, z) ↦ (R r, R z)` of the nonsingular circles for every real `R` (the identity for `R ≤ 0`). -/
noncomputable def dilateTot (R : ℝ) (p : NonsingularCircle) : NonsingularCircle :=
  if hR : 0 < R then dilateCircle hR p else p

lemma dilateTot_of_pos {R : ℝ} (hR : 0 < R) (p : NonsingularCircle) : dilateTot R p = dilateCircle hR p := by
  simp only [dilateTot, hR, ↓reduceDIte]

lemma tendsto_dilateTot {Rn : ℕ → ℝ} {R : ℝ} (hR : 0 < R) (hn : ∀ n, 0 < Rn n)
    (hlim : Tendsto Rn atTop (𝓝 R)) (p : NonsingularCircle) :
    Tendsto (fun n => dilateTot (Rn n) p) atTop (𝓝 (dilateTot R p)) := by
  have e : (fun n => dilateTot (Rn n) p) = fun n => dilateCircle (hn n) p :=
    funext fun n => dilateTot_of_pos (hn n) p
  rw [e, dilateTot_of_pos hR]
  refine tendsto_subtype_rng.2 ?_
  refine Tendsto.prodMk_nhds (tendsto_subtype_rng.2 ?_) ?_
  · exact hlim.mul_const _
  · exact ((Complex.continuous_ofReal.tendsto R).comp hlim).mul_const _

/-- The dyadic dilation radius `max i 1 / 2^n` (positive for every integer index `i`). -/
noncomputable def dyadicRadius (n : ℕ) (i : ℤ) : ℝ := ((max i 1 : ℤ) : ℝ) / 2 ^ n

lemma dyadicRadius_pos (n : ℕ) (i : ℤ) : 0 < dyadicRadius n i := by
  have h1 : (0 : ℤ) < max i 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have h2 : (0 : ℝ) < ((max i 1 : ℤ) : ℝ) := by exact_mod_cast h1
  exact div_pos h2 (by positivity)

lemma tendsto_dyadicRadius_ceil {R : ℝ} (hR : 0 < R) :
    Tendsto (fun n : ℕ => dyadicRadius n ⌈(2 : ℝ) ^ n * R⌉) atTop (𝓝 R) := by
  have hpos : ∀ n : ℕ, (1 : ℤ) ≤ ⌈(2 : ℝ) ^ n * R⌉ := fun n => by
    have : 0 < (2 : ℝ) ^ n * R := by positivity
    exact Int.ceil_pos.2 this
  have heq : ∀ n : ℕ, dyadicRadius n ⌈(2 : ℝ) ^ n * R⌉ = (⌈(2 : ℝ) ^ n * R⌉ : ℝ) / 2 ^ n := fun n => by
    simp only [dyadicRadius, max_eq_left (hpos n)]
  have hlo : ∀ n : ℕ, R ≤ dyadicRadius n ⌈(2 : ℝ) ^ n * R⌉ := fun n => by
    rw [heq n, le_div_iff₀ (by positivity)]
    calc R * 2 ^ n = 2 ^ n * R := mul_comm _ _
      _ ≤ _ := Int.le_ceil _
  have hhi : ∀ n : ℕ, dyadicRadius n ⌈(2 : ℝ) ^ n * R⌉ ≤ R + (1 / 2) ^ n := fun n => by
    rw [heq n, div_le_iff₀ (by positivity)]
    have h1 := Int.ceil_lt_add_one ((2 : ℝ) ^ n * R)
    have h2 : (R + (1 / 2 : ℝ) ^ n) * 2 ^ n = 2 ^ n * R + 1 := by
      rw [add_mul, one_div, inv_pow, inv_mul_cancel₀ (by positivity)]
      ring
    rw [h2]
    exact h1.le
  have hup : Tendsto (fun n : ℕ => R + (1 / 2 : ℝ) ^ n) atTop (𝓝 R) := by
    have h0 : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have := (tendsto_const_nhds (x := R)).add h0
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup hlo hhi

/-- The values of a function on nonsingular circles along the dilated circles `R q_j`. -/
noncomputable def dilVec {k : ℕ} (q : Fin k → NonsingularCircle) (R : ℝ) (l : NonsingularCircle → ℝ) : Fin k → ℝ :=
  fun j => l (dilateTot R (q j))

lemma measurable_dilVec {k : ℕ} (q : Fin k → NonsingularCircle) (R : ℝ) : Measurable (dilVec q R) :=
  Measurable.of_eval fun _ => measurable_pi_apply _

/-- **The lateral part of a quantum cone at the random scale radius (finite-dimensional form).**  For finitely many
circles `q_1, …, q_k` avoiding the origin, the pair (radial process, lateral circle averages along the dilated
circles `R_b q_j`) has the product law (radial process) ⊗ (lateral circle averages along the circles `q_j`). -/
theorem map_radial_dilatedLateral_vec {Ω : Type} [MeasurableSpace Ω] {γ : ℝ} {P : Measure Ω}
    [IsProbabilityMeasure P] {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (h : IsQuantumCone γ P hC hcirc) (b : ℝ) {k : ℕ}
    (q : Fin k → NonsingularCircle) :
    P.map (fun ω => (radialProcess (hcirc ω), dilVec q (coneScaleRadius γ (hcirc ω) b)
        (projCircle (lateralProcess (hC ω) (hcirc ω))))) =
      (P.map fun ω => radialProcess (hcirc ω)).prod
        (P.map fun ω => fun j => projCircle (lateralProcess (hC ω) (hcirc ω)) (q j)) := by
  have hXm : Measurable fun ω => radialProcess (hcirc ω) :=
    Measurable.prodMk
      (Measurable.of_eval fun t => h.measurable_circle _ _ (Real.exp_pos _))
      (Measurable.of_eval fun s => h.measurable_circle _ _ (Real.exp_pos _))
  have hLae : AEMeasurable (fun ω => lateralProcess (hC ω) (hcirc ω)) P :=
    MatedCRT.ConeMeanZeroRestriction.lateralProcessAEMeasurable_holds.1 γ Ω P hC hcirc inferInstance h
  have hYae : AEMeasurable (fun ω => projCircle (lateralProcess (hC ω) (hcirc ω))) P :=
    measurable_projCircle.comp_aemeasurable hLae
  have hind : IndepFun (fun ω => radialProcess (hcirc ω))
      (fun ω => projCircle (lateralProcess (hC ω) (hcirc ω))) P :=
    h.indep.comp measurable_id measurable_projCircle
  have hρ : Measurable (radScale γ b) := measurable_radScale γ b
  have hk : ∀ n : ℕ, Measurable fun p : RadialPair => ⌈(2 : ℝ) ^ n * radScale γ b p⌉ := fun n =>
    Int.measurable_ceil.comp (measurable_const.mul hρ)
  have hTm : ∀ (n : ℕ) (i : ℤ), Measurable (dilVec q (dyadicRadius n i)) := fun n i => measurable_dilVec q _
  have hinv : ∀ (n : ℕ) (i : ℤ),
      (P.map fun ω => projCircle (lateralProcess (hC ω) (hcirc ω))).map (dilVec q (dyadicRadius n i)) =
        P.map fun ω => fun j => projCircle (lateralProcess (hC ω) (hcirc ω)) (q j) := by
    intro n i
    have hR := dyadicRadius_pos n i
    have e1 : (fun ω => dilVec q (dyadicRadius n i) (projCircle (lateralProcess (hC ω) (hcirc ω)))) =
        fun ω => (fun l : NonsingularCircle → ℝ => fun j => l (q j))
          (projCircleDil hR (lateralProcess (hC ω) (hcirc ω))) := by
      funext ω j
      simp only [dilVec, projCircleDil, dilateTot_of_pos hR]
    have hvec : Measurable (fun l : NonsingularCircle → ℝ => fun j => l (q j)) :=
      Measurable.of_eval fun _ => measurable_pi_apply _
    calc (P.map fun ω => projCircle (lateralProcess (hC ω) (hcirc ω))).map (dilVec q (dyadicRadius n i))
        = P.map (fun ω => dilVec q (dyadicRadius n i) (projCircle (lateralProcess (hC ω) (hcirc ω)))) :=
          (map_comp_aemeasurable (hTm n i) hYae).symm
      _ = P.map (fun ω => (fun l : NonsingularCircle → ℝ => fun j => l (q j))
            (projCircleDil hR (lateralProcess (hC ω) (hcirc ω)))) := congrArg P.map e1
      _ = (P.map fun ω => projCircleDil hR (lateralProcess (hC ω) (hcirc ω))).map
            (fun l : NonsingularCircle → ℝ => fun j => l (q j)) :=
          map_comp_aemeasurable hvec ((measurable_projCircleDil hR).comp_aemeasurable hLae)
      _ = (P.map fun ω => projCircle (lateralProcess (hC ω) (hcirc ω))).map
            (fun l : NonsingularCircle → ℝ => fun j => l (q j)) := by
          rw [map_lateralCircle_dilate_cone h hR]
      _ = P.map fun ω => fun j => projCircle (lateralProcess (hC ω) (hcirc ω)) (q j) :=
          (map_comp_aemeasurable hvec hYae).symm
  obtain ⟨V, hVdef⟩ : ∃ V : ℕ → Ω → (Fin k → ℝ), ∀ n ω, V n ω =
      dilVec q (dyadicRadius n ⌈(2 : ℝ) ^ n * radScale γ b (radialProcess (hcirc ω))⌉)
        (projCircle (lateralProcess (hC ω) (hcirc ω))) := ⟨_, fun _ _ => rfl⟩
  have hA : ∀ n, P.map (fun ω => (radialProcess (hcirc ω), V n ω)) =
      (P.map fun ω => radialProcess (hcirc ω)).prod
        (P.map fun ω => fun j => projCircle (lateralProcess (hC ω) (hcirc ω)) (q j)) := by
    intro n
    have := LatticeProb.map_pair_randomIndex_of_indepFun (P := P) hXm.aemeasurable hYae hind (hk n)
      (T := fun i => dilVec q (dyadicRadius n i)) (hTm n) (hinv n)
    simpa only [hVdef] using this
  have hVm : ∀ n, AEMeasurable (V n) P := by
    intro n
    have hT2 : Measurable (fun r : ℤ × (NonsingularCircle → ℝ) => dilVec q (dyadicRadius n r.1) r.2) :=
      measurable_from_prod_countable_right (fun i => hTm n i)
    have hΦ : Measurable (fun p : RadialPair × (NonsingularCircle → ℝ) =>
        dilVec q (dyadicRadius n ⌈(2 : ℝ) ^ n * radScale γ b p.1⌉) p.2) :=
      hT2.comp (((hk n).comp measurable_fst).prodMk measurable_snd)
    have := hΦ.comp_aemeasurable (hXm.aemeasurable.prodMk hYae)
    have e : V n = _ := funext (hVdef n)
    rw [e]
    exact this
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun n => V n ω) atTop
      (𝓝 (dilVec q (coneScaleRadius γ (hcirc ω) b) (projCircle (lateralProcess (hC ω) (hcirc ω))))) := by
    filter_upwards [ae_continuous_lateralCircle_cone h, ae_coneScaleRadius_spec hγ0 hγ2 h b,
      radScale_radialProcess_ae hγ0 hγ2 h b] with ω hcont hspec hrho
    have hR := hspec.1
    have hRn := tendsto_dyadicRadius_ceil hR
    rw [tendsto_pi_nhds]
    intro j
    have h1 := tendsto_dilateTot hR (fun n => dyadicRadius_pos n _) hRn (q j)
    have h2 := (hcont.tendsto _).comp h1
    simp only [hVdef, hrho, dilVec]
    exact h2
  exact LatticeProb.map_pair_eq_of_tendsto_ae hXm hVm hA hlim

end MatedCRT.FirstPass.Derived
