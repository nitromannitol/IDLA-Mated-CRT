import MatedCRT.Proofs.Sec3.KilledOccupation.ClockIdentificationConcrete
import MatedCRT.Proofs.Sec3.KilledOccupation.RegClockFun
import MatedCRT.Proofs.Sec3.KilledOccupation.ConeGFFTransfer
import MatedCRT.Proofs.Sec3.KilledOccupation.ClockExitLIntegral
import MatedCRT.Proofs.Sec3.KilledOccupation.RegClockApprox
import MatedCRT.Defs.Setting

/-!
# Annealed Cauchy bound for the regularized clock (Appendix B, the occupation clock)

The clock gap `clockGapFun` between two regularization parameters on dyadic scales, for the coupled law
`clockAnnealedLaw = (P ⊗ P_y).map (ω, b) ↦ (ψ ω, b)` of the circle-average family `ψ ω` and the Brownian motion `b`
started at `y`, with the exit time `σ = exitNN z r` of the ball `ball z r` (Duplantier-Sheffield; Berestycki-Powell).

* `tendsto_clockGap_of_quenched` (from the quenched bound): if the quenched bound `ae_quenched_clockGap_le` holds
  `P`-a.e., the annealed gap tends to zero in `clockAnnealedLaw` (dominated convergence via the Giry measurability and
  `tendsto_measure_iInter_atTop` on the exit-time tails).
* `ae_quenched_clockGap_le`: for `P`-a.e. field, the quenched gap is bounded by the Brownian tail `P_y{T < σ}`
  plus any `δ > 0`, eventually along dyadic scales. It uses the pointwise agreement of `regClockFun` with
  `lqgClockApprox` (`regClockFun_eq_ofReal_lqgClockApprox`) and the convergence in `P_y`-probability of the LQG
  clock approximations (`IsLQGClock`).
* `tendsto_clockGap_annealed` (under the standing hypotheses) and `tendsto_clockGap_cone` (the cone instance, from
  `MatedCRTEnv.IsValid`: `isQuantumCone`, `isLQGClock`, `isProbabilityMeasure`).
-/

open MeasureTheory Set Filter Topology HarmonicBalls MarkovProcess Metric
open scoped ENNReal NNReal

namespace MatedCRT.KilledOccupation

/-- The circle-average family `ψ ω q = hcirc ω q.1.1 q.1.2` on the unit disk index set. -/
noncomputable def clockPsi {Ω : Type*} (hcirc : Ω → ℝ → ℂ → ℝ) (ω : Ω) : UnitDiskCircleIndex → ℝ :=
  fun q => hcirc ω q.1.1 q.1.2

/-- The coupled law `M = (P ⊗ P_y).map (ω, b) ↦ (ψ ω, b)`. -/
noncomputable def clockAnnealedLaw {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (hcirc : Ω → ℝ → ℂ → ℝ)
    (y : ℂ) : Measure ((UnitDiskCircleIndex → ℝ) × ContinuousPath ℂ) :=
  (P.prod (planarBrownianMotion y)).map (fun p => (clockPsi hcirc p.1, p.2))

lemma measurable_clockAnnealedMap {Ω : Type*} [MeasurableSpace Ω] {hcirc : Ω → ℝ → ℂ → ℝ}
    (hmeas : ∀ (r' : ℝ) (z' : ℂ), 0 < r' → Measurable fun ω => hcirc ω r' z') :
    Measurable fun p : Ω × ContinuousPath ℂ => (clockPsi hcirc p.1, p.2) :=
  ((measurable_unitDiskCircle hcirc hmeas).comp measurable_fst).prodMk measurable_snd

/-- Annealed Cauchy property from the quenched bound (binder `hL2`): the annealed gap tends to zero. -/
theorem tendsto_clockGap_of_quenched {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (γ : ℝ) (z y : ℂ) (r : ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (hmeas : ∀ (r' : ℝ) (z' : ℂ), 0 < r' → Measurable fun ω => hcirc ω r' z')
    (hL2 : ∀ᵐ ω ∂P, ∀ T : ℕ, ∀ η : ℝ, 0 < η → ∀ δ : ℝ, 0 < δ → ∀ᶠ p : ℕ × ℕ in atTop,
      planarBrownianMotion y {b | ENNReal.ofReal η <
          clockGapFun γ (exitNN z r) (dyadicScale p.1) (dyadicScale p.2) (clockPsi hcirc ω, b)} ≤
        planarBrownianMotion y {b | (T : ℝ≥0) < exitNN z r b} + ENNReal.ofReal δ) :
    ∀ η : ℝ, 0 < η → Tendsto (fun p : ℕ × ℕ => clockAnnealedLaw P hcirc y
      {x | ENNReal.ofReal η < clockGapFun γ (exitNN z r) (dyadicScale p.1) (dyadicScale p.2) x})
      atTop (𝓝 0) := by
  intro η hη
  have hσm : Measurable (exitNN z r) := measurable_exitNN z r
  have hψ : Measurable (clockPsi hcirc) := measurable_unitDiskCircle hcirc hmeas
  let G : ℕ → ℕ → Set ((UnitDiskCircleIndex → ℝ) × ContinuousPath ℂ) := fun n m =>
    {x | ENNReal.ofReal η < clockGapFun γ (exitNN z r) (dyadicScale n) (dyadicScale m) x}
  have hG : ∀ n m, MeasurableSet (G n m) := fun n m =>
    measurableSet_lt measurable_const (measurable_clockGapFun γ _ hσm _ _)
  let g : ℕ → ℕ → Ω → ℝ≥0∞ := fun n m ω =>
    planarBrownianMotion y (Prod.mk (clockPsi hcirc ω) ⁻¹' G n m)
  have hgm : ∀ n m, Measurable (g n m) := fun n m =>
    (measurable_measure_prodMk_left (hG n m)).comp hψ
  have hM : ∀ n m, clockAnnealedLaw P hcirc y (G n m) = ∫⁻ ω, g n m ω ∂P := fun n m => by
    rw [clockAnnealedLaw, Measure.map_apply (measurable_clockAnnealedMap hmeas) (hG n m),
      Measure.prod_apply (measurable_clockAnnealedMap hmeas (hG n m))]
    rfl
  let H : ℕ → Ω → ℝ≥0∞ := fun N ω =>
    ⨆ p : {p : ℕ × ℕ // N ≤ p.1 ∧ N ≤ p.2}, g p.1.1 p.1.2 ω
  have hHm : ∀ N, Measurable (H N) := fun N => Measurable.iSup fun p => hgm p.1.1 p.1.2
  have hHle : ∀ N ω, H N ω ≤ 1 := fun N ω => iSup_le fun p => prob_le_one
  have hHanti : Antitone H := by
    intro N N' hNN' ω
    exact iSup_le fun p => le_iSup_of_le ⟨p.1, le_trans hNN' p.2.1, le_trans hNN' p.2.2⟩ le_rfl
  -- the tail probabilities of the exit time tend to zero
  have hT : Tendsto (fun T : ℕ => planarBrownianMotion y {b | (T : ℝ≥0) < exitNN z r b}) atTop (𝓝 0) := by
    have hanti : Antitone (fun T : ℕ => {b : ContinuousPath ℂ | (T : ℝ≥0) < exitNN z r b}) := by
      intro T T' hTT' b hb
      have hb' : (T' : ℝ≥0) < exitNN z r b := hb
      show (T : ℝ≥0) < exitNN z r b
      exact lt_of_le_of_lt (by exact_mod_cast hTT') hb'
    have hmeas' : ∀ T : ℕ, NullMeasurableSet {b : ContinuousPath ℂ | (T : ℝ≥0) < exitNN z r b}
        (planarBrownianMotion y) := fun T =>
      (measurableSet_lt measurable_const hσm).nullMeasurableSet
    have h := tendsto_measure_iInter_atTop (μ := planarBrownianMotion y) hmeas' hanti
      ⟨0, measure_ne_top _ _⟩
    have hempty : (⋂ T : ℕ, {b : ContinuousPath ℂ | (T : ℝ≥0) < exitNN z r b}) = ∅ := by
      ext b
      simp only [mem_iInter, Set.mem_ofPred_eq, mem_empty_iff_false, iff_false, not_forall, not_lt]
      obtain ⟨T, hT⟩ := exists_nat_gt (exitNN z r b)
      exact ⟨T, hT.le⟩
    rw [hempty, measure_empty] at h
    exact h
  -- for almost every ω, the tail infimum is below every P_y{T < σ}
  have hae : ∀ᵐ ω ∂P, ∀ T : ℕ, ⨅ N, H N ω ≤ planarBrownianMotion y {b | (T : ℝ≥0) < exitNN z r b} := by
    filter_upwards [hL2] with ω hω
    intro T
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    have hev := hω T η hη (ε : ℝ) (by exact_mod_cast hε)
    obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop_prod_self'.1 hev
    refine (iInf_le _ N₀).trans ?_
    refine iSup_le fun p => ?_
    have hp := hN₀ p.1.1 p.2.1 p.1.2 p.2.2
    rw [ENNReal.ofReal_coe_nnreal] at hp
    exact hp
  have hzero : ∀ᵐ ω ∂P, ⨅ N, H N ω = 0 := by
    filter_upwards [hae] with ω hω
    exact le_antisymm (ge_of_tendsto hT (Filter.Eventually.of_forall fun T => hω T)) zero_le
  have hfin0 : ∫⁻ ω, H 0 ω ∂P ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top ((lintegral_mono fun ω => hHle 0 ω).trans_eq (by simp))
  have hint : ∫⁻ ω, ⨅ N, H N ω ∂P = ⨅ N, ∫⁻ ω, H N ω ∂P :=
    lintegral_iInf (fun N => hHm N) hHanti hfin0
  have hzero_int : ⨅ N, ∫⁻ ω, H N ω ∂P = 0 := by
    rw [← hint, lintegral_congr_ae hzero, lintegral_zero]
  refine ENNReal.tendsto_nhds_zero.2 fun ε hε => ?_
  obtain ⟨N, hN⟩ := iInf_lt_iff.1 (show ⨅ N, ∫⁻ ω, H N ω ∂P < ε by rw [hzero_int]; exact hε)
  have hfst : Tendsto (Prod.fst : ℕ × ℕ → ℕ) atTop atTop := by
    have h := (Filter.tendsto_fst : Tendsto (Prod.fst : ℕ × ℕ → ℕ) (atTop ×ˢ atTop) atTop)
    rwa [Filter.prod_atTop_atTop_eq] at h
  have hsnd : Tendsto (Prod.snd : ℕ × ℕ → ℕ) atTop atTop := by
    have h := (Filter.tendsto_snd : Tendsto (Prod.snd : ℕ × ℕ → ℕ) (atTop ×ˢ atTop) atTop)
    rwa [Filter.prod_atTop_atTop_eq] at h
  filter_upwards [(hfst.eventually (eventually_ge_atTop N)).and (hsnd.eventually (eventually_ge_atTop N))]
    with p hp
  show clockAnnealedLaw P hcirc y (G p.1 p.2) ≤ ε
  rw [hM]
  calc ∫⁻ ω, g p.1 p.2 ω ∂P ≤ ∫⁻ ω, H N ω ∂P :=
        lintegral_mono fun ω => le_iSup_of_le ⟨p, hp⟩ le_rfl
    _ ≤ ε := hN.le

lemma tendsto_fst_nat_prod : Tendsto (Prod.fst : ℕ × ℕ → ℕ) atTop atTop := by
  have h := (Filter.tendsto_fst : Tendsto (Prod.fst : ℕ × ℕ → ℕ) (atTop ×ˢ atTop) atTop)
  rwa [Filter.prod_atTop_atTop_eq] at h

lemma tendsto_snd_nat_prod : Tendsto (Prod.snd : ℕ × ℕ → ℕ) atTop atTop := by
  have h := (Filter.tendsto_snd : Tendsto (Prod.snd : ℕ × ℕ → ℕ) (atTop ×ˢ atTop) atTop)
  rwa [Filter.prod_atTop_atTop_eq] at h

lemma abs_sub_le_of_two_bounds {a b F η : ℝ} (h1 : |a - F| < η / 2) (h2 : |b - F| < η / 2) :
    |a - b| ≤ η := by
  have h := abs_sub_le a F b
  rw [abs_sub_comm F b] at h
  linarith

/-- Quenched Cauchy property: for almost every field `ω`, the quenched clock gap is small in `P_y`-probability, uniformly in
the pair of regularization parameters along dyadic scales (Cauchy property of the clocks `lqgClockApprox`). -/
theorem ae_quenched_clockGap_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (γ ρ : ℝ) (hρ : ρ < 1) (z y : ℂ) (r : ℝ) (hr : 0 < r) (hball : ball z r ⊆ ball 0 ρ) (hy : y ∈ ball z r)
    (hcirc : Ω → ℝ → ℂ → ℝ) (F : Ω → ContinuousPath ℂ → ℝ≥0 → ℝ)
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun p : ℝ × ℂ => hcirc ω p.1 p.2) (Set.Ioi 0 ×ˢ Set.univ))
    (hclk : ∀ᵐ ω ∂P, IsLQGClock planarBrownianMotion γ (hcirc ω) y (F ω) ∧
      ∀ᵐ b ∂(planarBrownianMotion y), IsTimeChangeClock (F ω b)) :
    ∀ᵐ ω ∂P, ∀ T : ℕ, ∀ η : ℝ, 0 < η → ∀ δ : ℝ, 0 < δ → ∀ᶠ p : ℕ × ℕ in atTop,
      planarBrownianMotion y {b | ENNReal.ofReal η <
          clockGapFun γ (exitNN z r) (dyadicScale p.1) (dyadicScale p.2) (clockPsi hcirc ω, b)} ≤
        planarBrownianMotion y {b | (T : ℝ≥0) < exitNN z r b} + ENNReal.ofReal δ := by
  filter_upwards [hcont, hclk] with ω hωc hωk
  intro T η hη δ hδ
  have hA := hωk.1 (T : ℝ≥0) (η / 2) (half_pos hη)
  have hdyad : Tendsto (fun k : ℕ => HarmonicBalls.dyadicScale k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hsmall : ∀ᶠ k : ℕ in atTop, HarmonicBalls.dyadicScale k < 1 - ρ :=
    hdyad.eventually (gt_mem_nhds (by linarith))
  have hAsmall := hA.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 (half_pos hδ)))
  have hev := ((tendsto_fst_nat_prod.eventually hsmall).and (tendsto_snd_nat_prod.eventually hsmall)).and
    ((tendsto_fst_nat_prod.eventually hAsmall).and (tendsto_snd_nat_prod.eventually hAsmall))
  have h0 : planarBrownianMotion y {b | ¬ b 0 = y} = 0 := ae_iff.1 (ae_planarBrownianMotion_eval_zero y)
  let A : ℕ → Set (ContinuousPath ℂ) := fun k =>
    {b | ∃ t ≤ (T : ℝ≥0), η / 2 ≤ |lqgClockApprox γ (hcirc ω) (dyadicScale k) b t - F ω b t|}
  filter_upwards [hev] with p hp
  obtain ⟨⟨hn, hm⟩, hAn, hAm⟩ := hp
  have hsub : {b | ENNReal.ofReal η < clockGapFun γ (exitNN z r) (dyadicScale p.1) (dyadicScale p.2)
      (clockPsi hcirc ω, b)} ⊆ ((({b | (T : ℝ≥0) < exitNN z r b} ∪ A p.1) ∪ A p.2) ∪ {b | ¬ b 0 = y}) := by
    intro b hb
    by_cases h1 : (T : ℝ≥0) < exitNN z r b
    · exact Or.inl (Or.inl (Or.inl h1))
    by_cases h0' : b 0 = y
    swap
    · exact Or.inr h0'
    by_cases hAn' : b ∈ A p.1
    · exact Or.inl (Or.inl (Or.inr hAn'))
    by_cases hAm' : b ∈ A p.2
    · exact Or.inl (Or.inr hAm')
    exfalso
    have hn' : ∀ t ≤ (T : ℝ≥0), |lqgClockApprox γ (hcirc ω) (dyadicScale p.1) b t - F ω b t| < η / 2 :=
      fun t ht => lt_of_not_ge fun h => hAn' ⟨t, ht, h⟩
    have hm' : ∀ t ≤ (T : ℝ≥0), |lqgClockApprox γ (hcirc ω) (dyadicScale p.2) b t - F ω b t| < η / 2 :=
      fun t ht => lt_of_not_ge fun h => hAm' ⟨t, ht, h⟩
    have hgap : clockGapFun γ (exitNN z r) (dyadicScale p.1) (dyadicScale p.2) (clockPsi hcirc ω, b)
        ≤ ENNReal.ofReal η := by
      refine iSup_le fun q => ?_
      have ht : min (q : ℝ≥0) (exitNN z r b) ≤ (T : ℝ≥0) :=
        le_trans (min_le_right _ _) (not_lt.1 h1)
      have eL : regClockFun γ (dyadicScale p.1) (clockPsi hcirc ω) (exitNN z r) b (q : ℝ≥0) =
          ENNReal.ofReal (lqgClockApprox γ (hcirc ω) (dyadicScale p.1) b (min (q : ℝ≥0) (exitNN z r b))) :=
        regClockFun_eq_ofReal_lqgClockApprox (γ := γ) (ρ := ρ) (dyadicScale_pos p.1) hn hωc hr hball hy h0'
          (q : ℝ≥0)
      have eM : regClockFun γ (dyadicScale p.2) (clockPsi hcirc ω) (exitNN z r) b (q : ℝ≥0) =
          ENNReal.ofReal (lqgClockApprox γ (hcirc ω) (dyadicScale p.2) b (min (q : ℝ≥0) (exitNN z r b))) :=
        regClockFun_eq_ofReal_lqgClockApprox (γ := γ) (ρ := ρ) (dyadicScale_pos p.2) hm hωc hr hball hy h0'
          (q : ℝ≥0)
      calc ennDist (regClockFun γ (dyadicScale p.1) (clockPsi hcirc ω) (exitNN z r) b (q : ℝ≥0))
            (regClockFun γ (dyadicScale p.2) (clockPsi hcirc ω) (exitNN z r) b (q : ℝ≥0))
          = ennDist (ENNReal.ofReal (lqgClockApprox γ (hcirc ω) (dyadicScale p.1) b (min (q : ℝ≥0) (exitNN z r b))))
              (ENNReal.ofReal (lqgClockApprox γ (hcirc ω) (dyadicScale p.2) b (min (q : ℝ≥0) (exitNN z r b)))) := by
            rw [eL, eM]
        _ ≤ ENNReal.ofReal |lqgClockApprox γ (hcirc ω) (dyadicScale p.1) b (min (q : ℝ≥0) (exitNN z r b)) -
              lqgClockApprox γ (hcirc ω) (dyadicScale p.2) b (min (q : ℝ≥0) (exitNN z r b))| :=
            ennDist_ofReal_le _ _
        _ ≤ ENNReal.ofReal η :=
            ENNReal.ofReal_le_ofReal (abs_sub_le_of_two_bounds (hn' _ ht) (hm' _ ht))
    exact absurd hb (not_lt.2 hgap)
  have hU : planarBrownianMotion y ((({b | (T : ℝ≥0) < exitNN z r b} ∪ A p.1) ∪ A p.2)) ≤
      planarBrownianMotion y {b | (T : ℝ≥0) < exitNN z r b} + planarBrownianMotion y (A p.1) +
        planarBrownianMotion y (A p.2) :=
    (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
  calc planarBrownianMotion y {b | ENNReal.ofReal η < clockGapFun γ (exitNN z r) (dyadicScale p.1)
          (dyadicScale p.2) (clockPsi hcirc ω, b)}
      ≤ planarBrownianMotion y ((({b | (T : ℝ≥0) < exitNN z r b} ∪ A p.1) ∪ A p.2) ∪ {b | ¬ b 0 = y}) :=
        measure_mono hsub
    _ ≤ planarBrownianMotion y ((({b | (T : ℝ≥0) < exitNN z r b} ∪ A p.1) ∪ A p.2)) +
          planarBrownianMotion y {b | ¬ b 0 = y} := measure_union_le _ _
    _ ≤ (planarBrownianMotion y {b | (T : ℝ≥0) < exitNN z r b} + planarBrownianMotion y (A p.1) +
          planarBrownianMotion y (A p.2)) + planarBrownianMotion y {b | ¬ b 0 = y} :=
        add_le_add hU le_rfl
    _ = planarBrownianMotion y {b | (T : ℝ≥0) < exitNN z r b} + planarBrownianMotion y (A p.1) +
          planarBrownianMotion y (A p.2) := by rw [h0, add_zero]
    _ ≤ planarBrownianMotion y {b | (T : ℝ≥0) < exitNN z r b} + ENNReal.ofReal (δ / 2) +
          ENNReal.ofReal (δ / 2) := add_le_add (add_le_add le_rfl hAn.le) hAm.le
    _ = planarBrownianMotion y {b | (T : ℝ≥0) < exitNN z r b} + ENNReal.ofReal δ := by
        rw [add_assoc, ← ENNReal.ofReal_add (half_pos hδ).le (half_pos hδ).le, add_halves]

/-- Annealed Cauchy property: the annealed clock gap tends to zero (the quenched bound is
`ae_quenched_clockGap_le`). -/
theorem tendsto_clockGap_annealed {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (γ ρ : ℝ) (hρ : ρ < 1) (z y : ℂ) (r : ℝ) (hr : 0 < r) (hball : ball z r ⊆ ball 0 ρ) (hy : y ∈ ball z r)
    (hcirc : Ω → ℝ → ℂ → ℝ) (F : Ω → ContinuousPath ℂ → ℝ≥0 → ℝ)
    (hmeas : ∀ (r' : ℝ) (z' : ℂ), 0 < r' → Measurable fun ω => hcirc ω r' z')
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun p : ℝ × ℂ => hcirc ω p.1 p.2) (Set.Ioi 0 ×ˢ Set.univ))
    (hclk : ∀ᵐ ω ∂P, IsLQGClock planarBrownianMotion γ (hcirc ω) y (F ω) ∧
      ∀ᵐ b ∂(planarBrownianMotion y), IsTimeChangeClock (F ω b)) :
    ∀ η : ℝ, 0 < η → Tendsto (fun p : ℕ × ℕ => clockAnnealedLaw P hcirc y
      {x | ENNReal.ofReal η < clockGapFun γ (exitNN z r) (dyadicScale p.1) (dyadicScale p.2) x})
      atTop (𝓝 0) :=
  tendsto_clockGap_of_quenched P γ z y r hcirc hmeas
    (ae_quenched_clockGap_le P γ ρ hρ z y r hr hball hy hcirc F hcont hclk)

/-- The cone instance of the annealed Cauchy property: the hypotheses for `S.hcirc`, `S.clock` from `S.IsValid`. -/
theorem tendsto_clockGap_cone {Ω : Type} [MeasurableSpace Ω] (𝒮 : SpaceFillingSLEModel) (γ ρ : ℝ)
    (hρ : ρ < 1) (z y : ℂ) (r : ℝ) (hr : 0 < r) (hball : ball z r ⊆ ball 0 ρ) (hy : y ∈ ball z r)
    (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ) :
    ∀ η : ℝ, 0 < η → Tendsto (fun p : ℕ × ℕ => clockAnnealedLaw S.P S.hcirc y
      {x | ENNReal.ofReal η < clockGapFun γ (exitNN z r) (dyadicScale p.1) (dyadicScale p.2) x})
      atTop (𝓝 0) := by
  have := hS.isProbabilityMeasure
  exact tendsto_clockGap_annealed S.P γ ρ hρ z y r hr hball hy S.hcirc S.clock
    hS.isQuantumCone.measurable_circle hS.isQuantumCone.ae_continuousOn_circle
    (hS.isLQGClock.mono fun ω h => h y)

end MatedCRT.KilledOccupation
