import LatticeProb.Prob.CauchyInProbabilitySubseq
import MatedCRT.Proofs.Sec3.KilledOccupation.RegClockApprox
import MatedCRT.Proofs.Sec3.KilledOccupation.LimClockFun
import MatedCRT.Proofs.Sec3.KilledOccupation.ClockAnnealedCauchy

/-!
# Identification of the limit clock: Borel-Cantelli transfer from a product measure

Let `P` be a measure on `Ω`, `Q` a measure on `Z`, and `ψ : Ω → Y` measurable. The image `M` of `P ⊗ Q` under
`(ω, b) ↦ (ψ ω, b)` is the joint law of the field and the path. If the events `{ofReal ((1/2)^k) < D k}` have `M`-mass at
most `ofReal ((1/2)^k)`, the first Borel-Cantelli lemma (`LatticeProb.ae_eventually_le_of_prob_le`) gives `M`-almost
every point eventually below the level, and Fubini for the product measure (`Measure.ae_ae_of_ae_prod`) gives the
statement for `P`-almost every `ω` and `Q`-almost every `b`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal
open _root_.HarmonicBalls MarkovProcess

namespace MatedCRT.KilledOccupation

/-- Borel-Cantelli transfer from the image `((P ⊗ Q).map fun p ↦ (ψ p.1, p.2))` of a product measure: if the
`k`-th events have mass at most `(1/2)^k`, then for `P`-almost every `ω` and `Q`-almost every `b`, `D k (ψ ω, b)`
is eventually at most `(1/2)^k`. -/
theorem ae_ae_eventually_le_of_map_prob_le {Ω Y Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]
    [MeasurableSpace Z] (P : Measure Ω) (Q : Measure Z) [SFinite Q] (ψ : Ω → Y) (hψ : Measurable ψ)
    (D : ℕ → Y × Z → ℝ≥0∞)
    (hD : ∀ k, ((P.prod Q).map fun p : Ω × Z => (ψ p.1, p.2)) {x | ENNReal.ofReal ((1 / 2) ^ k) < D k x}
        ≤ ENNReal.ofReal ((1 / 2) ^ k)) :
    ∀ᵐ ω ∂P, ∀ᵐ b ∂Q, ∀ᶠ k in atTop, D k (ψ ω, b) ≤ ENNReal.ofReal ((1 / 2) ^ k) := by
  have hf : Measurable fun p : Ω × Z => (ψ p.1, p.2) :=
    (hψ.comp measurable_fst).prodMk measurable_snd
  have h1 : ∀ᵐ x ∂((P.prod Q).map fun p : Ω × Z => (ψ p.1, p.2)),
      ∀ᶠ k in atTop, D k x ≤ ENNReal.ofReal ((1 / 2) ^ k) :=
    LatticeProb.ae_eventually_le_of_prob_le _ D hD
  have h2 : ∀ᵐ p ∂(P.prod Q), ∀ᶠ k in atTop, D k (ψ p.1, p.2) ≤ ENNReal.ofReal ((1 / 2) ^ k) :=
    ae_of_ae_map hf.aemeasurable h1
  exact Measure.ae_ae_of_ae_prod h2

/-- Choice of a strictly increasing subsequence `k` along which, for `μ`-almost every `x`, eventually in `j` the point
`x` avoids the `j`-th event `E (k j) j`: the event `E (k j) j` is chosen with mass at most `(1/2)^j`, and the first
Borel-Cantelli lemma (`MeasureTheory.ae_eventually_notMem`) gives the conclusion. -/
theorem exists_strictMono_ae_eventually_notMem {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (E : ℕ → ℕ → Set X) (h : ∀ j : ℕ, Tendsto (fun k => μ (E k j)) atTop (𝓝 0)) :
    ∃ k : ℕ → ℕ, StrictMono k ∧ ∀ᵐ x ∂μ, ∀ᶠ j in atTop, x ∉ E (k j) j := by
  have hN : ∀ j : ℕ, ∃ N : ℕ, ∀ m ≥ N, μ (E m j) < ENNReal.ofReal ((1 / 2 : ℝ) ^ j) := by
    intro j
    have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal ((1 / 2 : ℝ) ^ j) := by
      rw [ENNReal.ofReal_pos]; positivity
    exact eventually_atTop.1 ((h j).eventually (gt_mem_nhds hpos))
  choose N hN using hN
  have hstrict : StrictMono fun j : ℕ => j + ∑ i ∈ Finset.range (j + 1), N i := by
    refine strictMono_nat_of_lt_succ fun j => ?_
    have h1 := Finset.sum_range_succ N (j + 1)
    show j + ∑ i ∈ Finset.range (j + 1), N i < j + 1 + ∑ i ∈ Finset.range (j + 1 + 1), N i
    omega
  have hge : ∀ j : ℕ, N j ≤ j + ∑ i ∈ Finset.range (j + 1), N i := fun j => by
    have : N j ≤ ∑ i ∈ Finset.range (j + 1), N i :=
      Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.self_mem_range_succ j)
    omega
  have hbd : ∀ j : ℕ, μ (E (j + ∑ i ∈ Finset.range (j + 1), N i) j) ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ j) :=
    fun j => (hN j _ (hge j)).le
  have hgeom : ∑' j : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ j) ≠ ∞ := by
    have hr : ENNReal.ofReal (1 / 2) < 1 := by
      rw [ENNReal.ofReal_lt_one]; norm_num
    simp_rw [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    rw [ENNReal.tsum_geometric]
    exact ENNReal.inv_ne_top.2 (tsub_pos_of_lt hr).ne'
  refine ⟨fun j => j + ∑ i ∈ Finset.range (j + 1), N i, hstrict, ?_⟩
  have hsum : ∑' j : ℕ, μ (E (j + ∑ i ∈ Finset.range (j + 1), N i) j) ≠ ∞ :=
    ne_top_of_le_ne_top hgeom (ENNReal.tsum_le_tsum hbd)
  exact ae_eventually_notMem hsum

/-- A real sequence whose consecutive gaps are eventually at most `(1/2)^m` and which converges along a subsequence
converges: the shifted sequence is Cauchy (geometric gaps), so it converges to the limit of the subsequence. -/
theorem tendsto_of_subseq_of_gap_le_geometric_two {x : ℕ → ℝ} {L : ℝ} {k : ℕ → ℕ} (hk : StrictMono k)
    (hgap : ∀ᶠ m in atTop, |x m - x (m + 1)| ≤ (1 / 2 : ℝ) ^ m)
    (hsub : Tendsto (fun j => x (k j)) atTop (𝓝 L)) : Tendsto x atTop (𝓝 L) := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 hgap
  have hcauchy : CauchySeq fun m => x (m + N) := by
    refine cauchySeq_of_le_geometric_two (C := 2) fun m => ?_
    show dist (x (m + N)) (x (m + 1 + N)) ≤ 2 / 2 / 2 ^ m
    rw [Real.dist_eq, show m + 1 + N = m + N + 1 by omega]
    have h1 := hN (m + N) (by omega)
    have h2 : (1 / 2 : ℝ) ^ (m + N) ≤ (1 / 2 : ℝ) ^ m :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    have h3 : (2 : ℝ) / 2 / 2 ^ m = (1 / 2 : ℝ) ^ m := by
      rw [div_pow, one_pow]; ring
    rw [h3]
    exact h1.trans h2
  have hlim : Tendsto (fun m => x (m + N)) atTop (𝓝 L) := by
    have hf : Tendsto (fun j => k j - N) atTop atTop :=
      tendsto_atTop_mono (fun j => by show j - N ≤ k j - N; have h : j ≤ k j := hk.id_le j; omega) (tendsto_sub_atTop_nat N)
    have ha : Tendsto ((fun m => x (m + N)) ∘ fun j => k j - N) atTop (𝓝 L) := by
      refine hsub.congr' ?_
      filter_upwards [hk.tendsto_atTop.eventually_ge_atTop N] with j hj
      simp only [Function.comp]
      rw [Nat.sub_add_cancel hj]
    exact tendsto_nhds_of_cauchySeq_of_subseq hcauchy hf ha
  exact (tendsto_add_atTop_iff_nat N).1 hlim

/-- The real value of the nonnegative rational `q.toNNRat` for a nonnegative rational `q`. -/
lemma toNNRat_cast_eq_real (q : ℚ) (hq : 0 ≤ q) : (((q.toNNRat : ℚ≥0) : ℝ≥0) : ℝ) = (q : ℝ) := by
  have hn : (0 : ℝ) ≤ (q.num : ℝ) := by exact_mod_cast Rat.num_nonneg.2 hq
  rw [NNRat.cast_def]
  simp [Rat.toNNRat, hq]
  rw [Rat.cast_def, abs_of_nonneg hn]

/-- Density of the nonnegative rationals in `ℝ≥0`, from `exists_rat_btwn`. -/
lemma exists_nnrat_btwn_nnreal {s t : ℝ≥0} (h : s < t) : ∃ q : ℚ≥0, s < (q : ℝ≥0) ∧ (q : ℝ≥0) < t := by
  obtain ⟨q, h1, h2⟩ := exists_rat_btwn (show (s : ℝ) < (t : ℝ) from NNReal.coe_lt_coe.2 h)
  have hq : (0 : ℚ) ≤ q := by
    have : (0 : ℝ) ≤ (s : ℝ) := s.2
    exact_mod_cast (le_trans this h1.le)
  refine ⟨q.toNNRat, ?_, ?_⟩
  · rw [← NNReal.coe_lt_coe, toNNRat_cast_eq_real q hq]; exact h1
  · rw [← NNReal.coe_lt_coe, toNNRat_cast_eq_real q hq]; exact h2

/-- The infimum over the rational times `q > s` of the value `F (min q c)` of a continuous nondecreasing clock is the
value at `min s c`: monotonicity gives `≥`, and right continuity together with the density of `ℚ≥0` gives `≤`. This is
the pointwise identity behind `limClockFun = F (min s σ)` for the limit clock. -/
theorem iInf_rat_gt_ofReal_eq {F : ℝ≥0 → ℝ} (hmono : Monotone F) (hcont : Continuous F) (c s : ℝ≥0) :
    (⨅ q : {q : ℚ≥0 // s < (q : ℝ≥0)}, ENNReal.ofReal (F (min (q.1 : ℝ≥0) c))) = ENNReal.ofReal (F (min s c)) := by
  apply le_antisymm
  · have hgt : ∀ t : ℝ≥0, s < t →
        (⨅ q : {q : ℚ≥0 // s < (q : ℝ≥0)}, ENNReal.ofReal (F (min (q.1 : ℝ≥0) c))) ≤
          ENNReal.ofReal (F (min t c)) := by
      intro t ht
      obtain ⟨q, hsq, hqt⟩ := exists_nnrat_btwn_nnreal ht
      exact (iInf_le _ ⟨q, hsq⟩).trans (ENNReal.ofReal_le_ofReal (hmono (min_le_min hqt.le le_rfl)))
    have hlim : Tendsto (fun t : ℝ≥0 => ENNReal.ofReal (F (min t c))) (𝓝[>] s)
        (𝓝 (ENNReal.ofReal (F (min s c)))) :=
      ((ENNReal.continuous_ofReal.comp (hcont.comp (continuous_id.min continuous_const))).tendsto s).mono_left
        nhdsWithin_le_nhds
    exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun t ht => hgt t ht)
  · exact le_iInf fun q => ENNReal.ofReal_le_ofReal (hmono (min_le_min q.2.le le_rfl))

/-- Almost sure subsequential convergence from convergence in measure, uniformly on bounded time intervals: if for every
`T` and `η > 0` the `μ`-mass of `{∃ t ≤ T, η ≤ |a m b t - F b t|}` tends to `0` along `m`, then along a strictly increasing
subsequence `k` of `n`, for `μ`-almost every `b`, `a (n (k j)) b t → F b t` for every `t`. This is the first step of the
identification of the limit clock (the quenched convergence in probability of `IsLQGClock` gives the hypothesis). -/
theorem ae_tendsto_subseq_of_tendsto_measure {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (a : ℕ → X → ℝ≥0 → ℝ) (F : X → ℝ≥0 → ℝ) (n : ℕ → ℕ) (hn : StrictMono n)
    (h : ∀ (T : ℝ≥0) (η : ℝ), 0 < η →
      Tendsto (fun m => μ {b | ∃ t ≤ T, η ≤ |a m b t - F b t|}) atTop (𝓝 0)) :
    ∃ k : ℕ → ℕ, StrictMono k ∧
      ∀ᵐ b ∂μ, ∀ t : ℝ≥0, Tendsto (fun j => a (n (k j)) b t) atTop (𝓝 (F b t)) := by
  have hE : ∀ j : ℕ, Tendsto (fun k => μ {b | ∃ t ≤ (j : ℝ≥0), (1 / 2 : ℝ) ^ j ≤ |a (n k) b t - F b t|})
      atTop (𝓝 0) := fun j =>
    (h (j : ℝ≥0) ((1 / 2 : ℝ) ^ j) (by positivity)).comp hn.tendsto_atTop
  obtain ⟨k, hk, hae⟩ := exists_strictMono_ae_eventually_notMem μ
    (fun k j => {b | ∃ t ≤ (j : ℝ≥0), (1 / 2 : ℝ) ^ j ≤ |a (n k) b t - F b t|}) hE
  refine ⟨k, hk, ?_⟩
  filter_upwards [hae] with b hb
  intro t
  have hev : ∀ᶠ j in atTop, |a (n (k j)) b t - F b t| ≤ (1 / 2 : ℝ) ^ j := by
    filter_upwards [hb, eventually_ge_atTop ⌈t⌉₊] with j hj hjt
    have htj : t ≤ (j : ℝ≥0) := le_trans (Nat.le_ceil t) (by exact_mod_cast hjt)
    by_contra hc
    exact hj ⟨t, htj, (not_le.1 hc).le⟩
  have h0 : Tendsto (fun j : ℕ => (1 / 2 : ℝ) ^ j) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have h1 : Tendsto (fun j => a (n (k j)) b t - F b t) atTop (𝓝 0) :=
    squeeze_zero_norm' (by filter_upwards [hev] with j hj; rwa [Real.norm_eq_abs]) h0
  exact tendsto_sub_nhds_zero_iff.1 h1

/-- If the consecutive ennDist-gaps of the nonnegative sequence `ofReal (x m)` are eventually at most `(1/2)^m` and
a subsequence converges to `L`, the `limsup` of `ofReal (x m)` is `ofReal L`. This is the form used at each rational
time in the identification of the limit clock, where the Borel-Cantelli gap bound is available (`clockGapFun`
dominates `ennDist` at each rational time). -/
theorem limsup_ofReal_eq_of_gap {x : ℕ → ℝ} {L : ℝ} {k : ℕ → ℕ} (hk : StrictMono k) (hx : ∀ m, 0 ≤ x m)
    (hgap : ∀ᶠ m in atTop,
      ennDist (ENNReal.ofReal (x m)) (ENNReal.ofReal (x (m + 1))) ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ m))
    (hsub : Tendsto (fun j => x (k j)) atTop (𝓝 L)) :
    Filter.limsup (fun m => ENNReal.ofReal (x m)) atTop = ENNReal.ofReal L := by
  have hgap' : ∀ᶠ m in atTop, |x m - x (m + 1)| ≤ (1 / 2 : ℝ) ^ m := by
    filter_upwards [hgap] with m hm
    have h1 : ENNReal.ofReal |x m - x (m + 1)| ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ m) :=
      (ofReal_le_ennDist_ofReal (η := |x m - x (m + 1)|) (hx m) (hx (m + 1)) le_rfl).trans hm
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h1
  have hT : Tendsto x atTop (𝓝 L) := tendsto_of_subseq_of_gap_le_geometric_two hk hgap' hsub
  exact ((ENNReal.continuous_ofReal.tendsto L).comp hT).limsup_eq

/-- Borel-Cantelli for the clock gap. Under the hypothesis `hbd` that the
image `M` of `P ⊗ planarBrownianMotion y` under `(ω, b) ↦ (ψ ω, b)` gives the events `{ofReal ((1/2)^k) < gap k}` mass at
most `(1/2)^k`, for `P`-almost every `ω` and `planarBrownianMotion y`-almost every `b` the clock gap at the scales
`ε k`, `ε (k+1)` is eventually at most `(1/2)^k`. -/
theorem ae_ae_eventually_clockGap_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (y : ℂ) (γ : ℝ)
    (σ : ContinuousPath ℂ → ℝ≥0) (ε : ℕ → ℝ) (ψ : Ω → UnitDiskCircleIndex → ℝ) (hψ : Measurable ψ)
    (hbd : ∀ k : ℕ, ((P.prod (planarBrownianMotion y)).map fun p : Ω × ContinuousPath ℂ => (ψ p.1, p.2))
        {x | ENNReal.ofReal ((1 / 2 : ℝ) ^ k) < clockGapFun γ σ (ε k) (ε (k + 1)) x}
          ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ k)) :
    ∀ᵐ ω ∂P, ∀ᵐ b ∂planarBrownianMotion y, ∀ᶠ k in atTop,
      clockGapFun γ σ (ε k) (ε (k + 1)) (ψ ω, b) ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ k) :=
  ae_ae_eventually_le_of_map_prob_le P (planarBrownianMotion y) ψ hψ
    (fun k => clockGapFun γ σ (ε k) (ε (k + 1))) hbd

/-- Identification of the limit clock. Let the field `hcirc ω` have a.s. continuous circle averages
(`hcont`) and let `F ω` be an LQG clock of `hcirc ω` for the planar Brownian motion from `y`, in the sense of
`IsLQGClock` (`hclk`). Let `n` be a strictly increasing sequence of scales with `dyadicScale (n 0) < 1 - ρ`, and assume
the summable bounds `hbd` for the gaps of the regularized clocks at the scales `dyadicScale (n k)`. Then for
`P`-almost every `ω` and `planarBrownianMotion y`-almost every `b`, the limit clock `limClockFun` of the regularized
clocks along `n` is the clock `F ω b` stopped at the exit time `exitNN z r b` (Duplantier-Sheffield, quantum clock of the
LQG measure; Berestycki-Powell, Gaussian free field circle averages). -/
theorem ae_limClockFun_eq_clock {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ ρ r : ℝ) (z y : ℂ) (hr : 0 < r)
    (hball : Metric.ball z r ⊆ Metric.ball 0 ρ) (hy : y ∈ Metric.ball z r)
    (hcirc : Ω → ℝ → ℂ → ℝ) (F : Ω → ContinuousPath ℂ → ℝ≥0 → ℝ)
    (hmeas : ∀ (r : ℝ) (z : ℂ), 0 < r → Measurable fun ω => hcirc ω r z)
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun p : ℝ × ℂ => hcirc ω p.1 p.2) (Set.Ioi 0 ×ˢ Set.univ))
    (hclk : ∀ᵐ ω ∂P, IsLQGClock planarBrownianMotion γ (hcirc ω) y (F ω) ∧
      ∀ᵐ b ∂planarBrownianMotion y, IsTimeChangeClock (F ω b))
    (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : dyadicScale (n 0) < 1 - ρ)
    (hbd : ∀ k : ℕ, ((P.prod (planarBrownianMotion y)).map fun p : Ω × ContinuousPath ℂ =>
        ((fun ω (q : UnitDiskCircleIndex) => hcirc ω q.1.1 q.1.2) p.1, p.2))
        {x | ENNReal.ofReal ((1 / 2 : ℝ) ^ k) <
          clockGapFun γ (exitNN z r) (dyadicScale (n k)) (dyadicScale (n (k + 1))) x}
          ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ k)) :
    ∀ᵐ ω ∂P, ∀ᵐ b ∂planarBrownianMotion y, ∀ s : ℝ≥0,
      limClockFun γ (fun k => dyadicScale (n k)) (fun q : UnitDiskCircleIndex => hcirc ω q.1.1 q.1.2)
        (exitNN z r) b s = ENNReal.ofReal (F ω b (min s (exitNN z r b))) := by
  have hanti : ∀ m k : ℕ, m ≤ k → dyadicScale k ≤ dyadicScale m := fun m k hmk => by
    unfold dyadicScale
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hmk
  have hεpos : ∀ k : ℕ, 0 < dyadicScale (n k) := fun k => by
    unfold dyadicScale
    positivity
  have hεlt : ∀ k : ℕ, dyadicScale (n k) < 1 - ρ := fun k =>
    lt_of_le_of_lt (hanti _ _ (hn.monotone (Nat.zero_le k))) hn0
  have hψ : Measurable fun ω (q : UnitDiskCircleIndex) => hcirc ω q.1.1 q.1.2 :=
    measurable_unitDiskCircle hcirc hmeas
  have hL6 := ae_ae_eventually_clockGap_le P y γ (exitNN z r) (fun k => dyadicScale (n k))
    (fun ω (q : UnitDiskCircleIndex) => hcirc ω q.1.1 q.1.2) hψ hbd
  filter_upwards [hL6, hcont, hclk] with ω h6 hωc hωk
  obtain ⟨hlq, hTC⟩ := hωk
  obtain ⟨k, hk, hsub⟩ := ae_tendsto_subseq_of_tendsto_measure (planarBrownianMotion y)
    (fun m b t => lqgClockApprox γ (hcirc ω) (dyadicScale m) b t) (F ω) n hn
    (fun T η hη => hlq T η hη)
  filter_upwards [hsub, ae_planarBrownianMotion_eval_zero y, hTC, h6] with b hb hb0 hT hb6
  intro s
  have hq : ∀ q : ℚ≥0, Filter.limsup (fun m => regClockFun γ (dyadicScale (n m))
      (fun q : UnitDiskCircleIndex => hcirc ω q.1.1 q.1.2) (exitNN z r) b (q : ℝ≥0)) Filter.atTop =
      ENNReal.ofReal (F ω b (min (q : ℝ≥0) (exitNN z r b))) := by
    intro q
    have hL0 : ∀ m : ℕ, regClockFun γ (dyadicScale (n m))
        (fun q : UnitDiskCircleIndex => hcirc ω q.1.1 q.1.2) (exitNN z r) b (q : ℝ≥0) =
        ENNReal.ofReal (lqgClockApprox γ (hcirc ω) (dyadicScale (n m)) b
          (min (q : ℝ≥0) (exitNN z r b))) := fun m =>
      regClockFun_eq_ofReal_lqgClockApprox (hεpos m) (hεlt m) hωc hr hball hy hb0 (q : ℝ≥0)
    have hfun : (fun m => regClockFun γ (dyadicScale (n m))
        (fun q : UnitDiskCircleIndex => hcirc ω q.1.1 q.1.2) (exitNN z r) b (q : ℝ≥0)) =
        fun m => ENNReal.ofReal (lqgClockApprox γ (hcirc ω) (dyadicScale (n m)) b
          (min (q : ℝ≥0) (exitNN z r b))) := funext hL0
    have hgap : ∀ᶠ m in Filter.atTop,
        ennDist (ENNReal.ofReal (lqgClockApprox γ (hcirc ω) (dyadicScale (n m)) b (min (q : ℝ≥0) (exitNN z r b))))
          (ENNReal.ofReal (lqgClockApprox γ (hcirc ω) (dyadicScale (n (m + 1))) b
            (min (q : ℝ≥0) (exitNN z r b)))) ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ m) := by
      filter_upwards [hb6] with m hm
      rw [← hL0 m, ← hL0 (m + 1)]
      exact (le_iSup (fun q' : ℚ≥0 => ennDist (regClockFun γ (dyadicScale (n m))
        (fun q : UnitDiskCircleIndex => hcirc ω q.1.1 q.1.2) (exitNN z r) b (q' : ℝ≥0))
        (regClockFun γ (dyadicScale (n (m + 1)))
        (fun q : UnitDiskCircleIndex => hcirc ω q.1.1 q.1.2) (exitNN z r) b (q' : ℝ≥0))) q).trans hm
    rw [hfun]
    exact limsup_ofReal_eq_of_gap hk (fun m => lqgClockApprox_nonneg (hεpos m) (hcirc ω) b _) hgap
      (hb (min (q : ℝ≥0) (exitNN z r b)))
  have hiInf : (⨅ q : {q : ℚ≥0 // s < (q : ℝ≥0)}, Filter.limsup (fun m => regClockFun γ (dyadicScale (n m))
      (fun q : UnitDiskCircleIndex => hcirc ω q.1.1 q.1.2) (exitNN z r) b (q.1 : ℝ≥0)) Filter.atTop) =
      ⨅ q : {q : ℚ≥0 // s < (q : ℝ≥0)}, ENNReal.ofReal (F ω b (min (q.1 : ℝ≥0) (exitNN z r b))) :=
    iInf_congr fun q => hq q.1
  show (⨅ q : {q : ℚ≥0 // s < (q : ℝ≥0)}, Filter.limsup (fun m => regClockFun γ (dyadicScale (n m))
      (fun q : UnitDiskCircleIndex => hcirc ω q.1.1 q.1.2) (exitNN z r) b (q.1 : ℝ≥0)) Filter.atTop) = _
  rw [hiInf]
  exact iInf_rat_gt_ofReal_eq hT.strictMono.monotone hT.continuous (exitNN z r b) s

/-- The quantum cone instance of the identification of the limit clock. For a valid mated-CRT environment `S` there
is a strictly increasing sequence `n` of dyadic scales, with `dyadicScale (n 0) < 1 - ρ`, such that the consecutive gaps
of the regularized clocks satisfy the summable bounds under the coupled law `clockAnnealedLaw S.P S.hcirc y` of the
circle averages and the planar Brownian motion from `y`, and such that the limit clock along `n` is the clock `S.clock`
of Liouville Brownian motion stopped at the exit time of `ball z r`. The bounds are part of the conclusion because they
depend only on the coupled law, so they hold for any field with the same law of circle averages. -/
theorem exists_strictMono_ae_limClockFun_eq_clock_cone {Ω : Type} [MeasurableSpace Ω] (𝒮 : SpaceFillingSLEModel)
    (γ ρ : ℝ) (hρ : ρ < 1) (z y : ℂ) (r : ℝ) (hr : 0 < r) (hball : Metric.ball z r ⊆ Metric.ball 0 ρ)
    (hy : y ∈ Metric.ball z r) (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ) :
    ∃ n : ℕ → ℕ, StrictMono n ∧ dyadicScale (n 0) < 1 - ρ ∧
      (∀ k : ℕ, clockAnnealedLaw S.P S.hcirc y
        {x | ENNReal.ofReal ((1 / 2 : ℝ) ^ k) <
          clockGapFun γ (exitNN z r) (dyadicScale (n k)) (dyadicScale (n (k + 1))) x}
          ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ k)) ∧
      ∀ᵐ ω ∂S.P, ∀ᵐ b ∂planarBrownianMotion y, ∀ s : ℝ≥0,
        limClockFun γ (fun k => dyadicScale (n k)) (clockPsi S.hcirc ω) (exitNN z r) b s =
          ENNReal.ofReal (S.clock ω b (min s (exitNN z r b))) := by
  have hanti : ∀ m k : ℕ, m ≤ k → dyadicScale k ≤ dyadicScale m := fun m k hmk => by
    unfold dyadicScale
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hmk
  obtain ⟨n₀, hn₀⟩ : ∃ n₀ : ℕ, dyadicScale n₀ < 1 - ρ := by
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (sub_pos.2 hρ) (by norm_num : (1 / 2 : ℝ) < 1)
    refine ⟨m, ?_⟩
    unfold dyadicScale
    simpa using hm
  obtain ⟨n, hn, hn0, hbd⟩ := LatticeProb.exists_strictMono_prob_le_of_cauchy (clockAnnealedLaw S.P S.hcirc y)
    (fun a b => clockGapFun γ (exitNN z r) (dyadicScale a) (dyadicScale b))
    (tendsto_clockGap_cone 𝒮 γ ρ hρ z y r hr hball hy S hS) n₀
  have hn0' : dyadicScale (n 0) < 1 - ρ := lt_of_le_of_lt (hanti _ _ hn0) hn₀
  exact ⟨n, hn, hn0', hbd,
    ae_limClockFun_eq_clock S.P γ ρ r z y hr hball hy S.hcirc S.clock hS.isQuantumCone.measurable_circle
      hS.isQuantumCone.ae_continuousOn_circle (hS.isLQGClock.mono fun ω h => h y) n hn hn0' hbd⟩

end MatedCRT.KilledOccupation
