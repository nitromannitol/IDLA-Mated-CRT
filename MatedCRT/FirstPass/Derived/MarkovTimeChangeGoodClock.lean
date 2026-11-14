import MatedCRT.FirstPass.Derived.MarkovTimeChangePCAF
import LatticeProb.Prob.CrossingTimesStrictInverse

/-!
# The regularized half-clock of a Markovian time-changed planar Brownian motion is a good clock

For a family of measurable functionals `F_s` reading the inverse crossing clock off the clock-read path, the
regularized half-clock `regularize (rawClock F)` of the planar Brownian path is almost surely strictly
increasing and unbounded (`GoodClock`), provided the inverse crossing clock is almost surely finite (a good
crossing clock) and strictly increasing and unbounded along the nonnegative rationals
(`LatticeProb.InvClockStrict`).

* `clockStrictSet F`: the clock-read paths whose half-clock skeleton is strictly increasing and unbounded along
  the nonnegative rationals; `measurableSet_clockStrictSet`: it is measurable;
* `ae_clockRead_mem_clockStrictSet`, `ae_halfRead_mem_clockStrictSet`: the clock-read path, hence the
  half-speed reading of the planar Brownian path, lies in it almost surely;
* `strictMono_regularize_rawClock`, `tendsto_regularize_rawClock`: along such a path the regularized
  half-clock is strictly increasing and tends to infinity;
* `goodClock_regularize_rawClock`: the regularized half-clock is a good clock for the planar Brownian laws;
  `ae_strictMono_regularize_rawClock`, `ae_tendsto_regularize_rawClock`: its two halves.
-/

open MeasureTheory MarkovProcess Filter Topology
open scoped NNReal ENNReal

namespace MatedCRT

open PlanarBrownianSpace

/-- The clock-read paths whose half-clock skeleton is strictly increasing and unbounded along the nonnegative
rationals. -/
def clockStrictSet (F : ℝ≥0 → (ℝ≥0 → EuclideanSpace ℝ (Fin 2)) → ℝ) :
    Set (ℝ≥0 → EuclideanSpace ℝ (Fin 2)) :=
  {f | (∀ p q : ℚ≥0, p < q → clockSkel F f p < clockSkel F f q) ∧
    ∀ n : ℕ, ∃ q : ℚ≥0, (n : ℝ≥0) ≤ clockSkel F f q}

/-- **The set of paths with a strictly increasing, unbounded skeleton is measurable.** -/
theorem measurableSet_clockStrictSet {F : ℝ≥0 → (ℝ≥0 → EuclideanSpace ℝ (Fin 2)) → ℝ}
    (hF : ∀ s, Measurable (F s)) : MeasurableSet (clockStrictSet F) := by
  have hm : ∀ q : ℚ≥0, Measurable fun f : ℝ≥0 → EuclideanSpace ℝ (Fin 2) => clockSkel F f q :=
    fun q => measurable_real_toNNReal.comp ((hF _).const_mul _)
  have h1 : MeasurableSet {f : ℝ≥0 → EuclideanSpace ℝ (Fin 2) |
      ∀ p q : ℚ≥0, p < q → clockSkel F f p < clockSkel F f q} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun p => MeasurableSet.iInter fun q => MeasurableSet.iInter fun _ =>
      measurableSet_lt (hm p) (hm q)
  have h2 : MeasurableSet {f : ℝ≥0 → EuclideanSpace ℝ (Fin 2) |
      ∀ n : ℕ, ∃ q : ℚ≥0, (n : ℝ≥0) ≤ clockSkel F f q} := by
    simp only [Set.ofPred_forall, Set.ofPred_exists]
    exact MeasurableSet.iInter fun n => MeasurableSet.iUnion fun q =>
      measurableSet_le measurable_const (hm q)
  exact h1.inter h2

/-- **Almost surely the skeleton of the clock-read path is strictly increasing and unbounded.**  For a
measure `μ` on paths such that almost surely the crossing clock is good and the inverse crossing clock is
strictly increasing and unbounded along the rationals (`LatticeProb.InvClockStrict`), and such that the
functionals `F_s` read the inverse crossing clock off the clock-read path, almost surely the clock-read path
lies in `clockStrictSet F`. -/
theorem ae_clockRead_mem_clockStrictSet {μ : Measure C(ℝ≥0, EuclideanSpace ℝ (Fin 2))} {m : ℝ≥0∞}
    {F : ℝ≥0 → (ℝ≥0 → EuclideanSpace ℝ (Fin 2)) → ℝ}
    (hgood : ∀ᵐ x ∂μ, LatticeProb.GoodClock (LatticeProb.crossClock m fun u => x u))
    (hstrict : ∀ᵐ x ∂μ, LatticeProb.InvClockStrict m x)
    (hFA : ∀ s : ℝ≥0, ∀ᵐ x ∂μ, (LatticeProb.pathClockInv m x s).toReal =
      F s fun t => LatticeProb.clockPath m (fun u => x u) t) :
    ∀ᵐ x ∂μ, LatticeProb.clockRead m x ∈ clockStrictSet F := by
  have hq : ∀ᵐ x ∂μ, ∀ q : ℚ≥0, (LatticeProb.pathClockInv m x (2 * (q : ℝ≥0))).toReal =
      F (2 * (q : ℝ≥0)) (LatticeProb.clockRead m x) :=
    ae_all_iff.2 fun q => hFA (2 * (q : ℝ≥0))
  filter_upwards [hgood, hstrict, hq] with x hg hs hx
  have hfin : ∀ t : ℝ≥0, LatticeProb.pathClockInv m x t ≠ ⊤ := fun t => (hg.clockInv_lt_top t).ne
  have hpos : ∀ t : ℝ≥0, 0 ≤ 2⁻¹ * (LatticeProb.pathClockInv m x t).toReal :=
    fun t => mul_nonneg (by norm_num) ENNReal.toReal_nonneg
  have hsk : ∀ q : ℚ≥0, clockSkel F (LatticeProb.clockRead m x) q =
      Real.toNNReal (2⁻¹ * (LatticeProb.pathClockInv m x (2 * (q : ℝ≥0))).toReal) := by
    intro q
    unfold clockSkel
    rw [← hx q]
  have e2 : ∀ r : ℚ≥0, ((2 * r : ℚ≥0) : ℝ≥0) = 2 * (r : ℝ≥0) := fun r => by norm_cast
  show _ ∧ _
  refine ⟨fun p q hpq => ?_, fun n => ?_⟩
  · have h2 : 2 * p < 2 * q := by gcongr
    have hlt := hs.1 _ _ h2
    rw [e2, e2] at hlt
    have hlt' := (ENNReal.toReal_lt_toReal (hfin _) (hfin _)).2 hlt
    rw [hsk, hsk, ← NNReal.coe_lt_coe, Real.coe_toNNReal _ (hpos _), Real.coe_toNNReal _ (hpos _)]
    linarith
  · obtain ⟨q, hq⟩ := hs.2 (2 * n)
    refine ⟨q, ?_⟩
    have hle : LatticeProb.pathClockInv m x q ≤ LatticeProb.pathClockInv m x (2 * (q : ℝ≥0)) :=
      LatticeProb.clockInv_mono (LatticeProb.crossClock m fun u => x u)
        (by rw [two_mul]; exact le_add_of_nonneg_right zero_le)
    have h1 := ENNReal.toReal_mono (hfin _) (hq.trans hle)
    rw [ENNReal.toReal_natCast] at h1
    push_cast at h1
    rw [hsk, ← NNReal.coe_le_coe, Real.coe_toNNReal _ (hpos _)]
    push_cast
    linarith

/-- **The transfer of the strict, unbounded skeleton to the planar Brownian path.** -/
theorem ae_halfRead_mem_clockStrictSet {μ : Measure C(ℝ≥0, EuclideanSpace ℝ (Fin 2))}
    {ν : Measure (ContinuousPath ℂ)} {m : ℝ≥0∞}
    {F : ℝ≥0 → (ℝ≥0 → EuclideanSpace ℝ (Fin 2)) → ℝ} (hF : ∀ s, Measurable (F s))
    (hmap : μ.map (LatticeProb.clockRead m) = ν.map halfRead)
    (hgood : ∀ᵐ x ∂μ, LatticeProb.GoodClock (LatticeProb.crossClock m fun u => x u))
    (hstrict : ∀ᵐ x ∂μ, LatticeProb.InvClockStrict m x)
    (hFA : ∀ s : ℝ≥0, ∀ᵐ x ∂μ, (LatticeProb.pathClockInv m x s).toReal =
      F s fun t => LatticeProb.clockPath m (fun u => x u) t) :
    ∀ᵐ w ∂ν, halfRead w ∈ clockStrictSet F :=
  ae_halfRead_mem_of_ae_clockRead hmap (measurableSet_clockStrictSet hF)
    (ae_clockRead_mem_clockStrictSet hgood hstrict hFA)

/-- A strictly increasing skeleton is nondecreasing. -/
theorem monotone_clockSkel_of_mem_clockStrictSet {F : ℝ≥0 → (ℝ≥0 → EuclideanSpace ℝ (Fin 2)) → ℝ}
    {f : ℝ≥0 → EuclideanSpace ℝ (Fin 2)} (h : f ∈ clockStrictSet F) : Monotone (clockSkel F f) := by
  obtain ⟨hs, -⟩ := h
  intro p q hpq
  rcases hpq.eq_or_lt with rfl | hlt
  · exact le_rfl
  · exact (hs p q hlt).le

/-- Along a path whose half-reading lies in `clockStrictSet F`, the regularized half-clock is the right limit
of the skeleton along the nonnegative rationals. -/
theorem regularize_rawClock_eq_nnratRightInf {F : ℝ≥0 → (ℝ≥0 → EuclideanSpace ℝ (Fin 2)) → ℝ}
    {w : ContinuousPath ℂ} (h : halfRead w ∈ clockStrictSet F) (t : ℝ≥0) :
    regularize (rawClock F) t w = LatticeProb.nnratRightInf (clockSkel F (halfRead w)) t := by
  have hmono := monotone_clockSkel_of_mem_clockStrictSet h
  unfold regularize
  split_ifs with hc
  · rfl
  · exact absurd (fun p q hpq => hmono hpq) hc

/-- **Along a path with a strictly increasing skeleton the regularized half-clock is strictly increasing.**
Between `s < t` lie two rationals `p < q`, and `A s ≤ a p < a q ≤ A t`. -/
theorem strictMono_regularize_rawClock {F : ℝ≥0 → (ℝ≥0 → EuclideanSpace ℝ (Fin 2)) → ℝ}
    {w : ContinuousPath ℂ} (h : halfRead w ∈ clockStrictSet F) :
    StrictMono fun t => regularize (rawClock F) t w := by
  have hfun := regularize_rawClock_eq_nnratRightInf h
  have hmono := monotone_clockSkel_of_mem_clockStrictSet h
  obtain ⟨hs, -⟩ := h
  intro s t hst
  obtain ⟨p, hsp, hpt⟩ := LatticeProb.exists_nnrat_between_nnreal hst
  obtain ⟨q, hpq, hqt⟩ := LatticeProb.exists_nnrat_between_nnreal hpt
  have hpq' : p < q := by exact_mod_cast hpq
  show regularize (rawClock F) s w < regularize (rawClock F) t w
  rw [hfun, hfun]
  calc LatticeProb.nnratRightInf (clockSkel F (halfRead w)) s ≤ clockSkel F (halfRead w) p :=
        LatticeProb.nnratRightInf_le hsp
    _ < clockSkel F (halfRead w) q := hs p q hpq'
    _ ≤ LatticeProb.nnratRightInf (clockSkel F (halfRead w)) t :=
        LatticeProb.le_nnratRightInf hmono hqt.le

/-- **Along a path with an unbounded skeleton the regularized half-clock tends to infinity.** -/
theorem tendsto_regularize_rawClock {F : ℝ≥0 → (ℝ≥0 → EuclideanSpace ℝ (Fin 2)) → ℝ}
    {w : ContinuousPath ℂ} (h : halfRead w ∈ clockStrictSet F) :
    Tendsto (fun t => regularize (rawClock F) t w) atTop atTop := by
  have hfun := regularize_rawClock_eq_nnratRightInf h
  have hmono := monotone_clockSkel_of_mem_clockStrictSet h
  obtain ⟨-, hu⟩ := h
  refine tendsto_atTop_atTop_of_monotone (regularize_monotone (rawClock F) w) fun b => ?_
  obtain ⟨n, hn⟩ := exists_nat_ge b
  obtain ⟨q, hq⟩ := hu n
  refine ⟨q, ?_⟩
  show b ≤ regularize (rawClock F) q w
  rw [hfun]
  exact hn.trans (hq.trans (LatticeProb.le_nnratRightInf hmono le_rfl))

/-- **The regularized half-clock is a good clock** as soon as, under every planar Brownian law, the half-speed
reading of the path almost surely has a strictly increasing, unbounded skeleton. -/
theorem goodClock_regularize_rawClock_of_ae {F : ℝ≥0 → (ℝ≥0 → EuclideanSpace ℝ (Fin 2)) → ℝ}
    (h : ∀ z, ∀ᵐ w ∂planarLaw z, halfRead w ∈ clockStrictSet F) :
    GoodClock planarLaw (regularize (rawClock F)) := fun z => by
  filter_upwards [h z] with w hw
  exact ⟨strictMono_regularize_rawClock hw, tendsto_regularize_rawClock hw⟩

/-- **The regularized half-clock of a Markovian time-changed planar Brownian motion is a good clock.**  Let
`μ z` be laws of Euclidean paths whose clock-read path has the law of the half-speed reading of planar Brownian
motion from `z` (`hmap`), with almost surely good crossing clock (`hgood`) and inverse crossing clock strictly
increasing and unbounded along the rationals (`hstrict`), and let the measurable functionals `F_s` read the
inverse crossing clock off the clock-read path (`hFA`).  Then, almost surely under every planar Brownian law,
`t ↦ regularize (rawClock F) t` is strictly increasing and tends to infinity. -/
theorem goodClock_regularize_rawClock {μ : ℂ → Measure C(ℝ≥0, EuclideanSpace ℝ (Fin 2))} {m : ℝ≥0∞}
    {F : ℝ≥0 → (ℝ≥0 → EuclideanSpace ℝ (Fin 2)) → ℝ} (hF : ∀ s, Measurable (F s))
    (hmap : ∀ z, (μ z).map (LatticeProb.clockRead m) = (planarLaw z).map halfRead)
    (hgood : ∀ z, ∀ᵐ x ∂(μ z), LatticeProb.GoodClock (LatticeProb.crossClock m fun u => x u))
    (hstrict : ∀ z, ∀ᵐ x ∂(μ z), LatticeProb.InvClockStrict m x)
    (hFA : ∀ z (s : ℝ≥0), ∀ᵐ x ∂(μ z), (LatticeProb.pathClockInv m x s).toReal =
      F s fun t => LatticeProb.clockPath m (fun u => x u) t) :
    GoodClock planarLaw (regularize (rawClock F)) :=
  goodClock_regularize_rawClock_of_ae fun z =>
    ae_halfRead_mem_clockStrictSet hF (hmap z) (hgood z) (hstrict z) (hFA z)

/-- **The regularized half-clock is almost surely strictly increasing** (first half of
`goodClock_regularize_rawClock`). -/
theorem ae_strictMono_regularize_rawClock {μ : ℂ → Measure C(ℝ≥0, EuclideanSpace ℝ (Fin 2))}
    {m : ℝ≥0∞} {F : ℝ≥0 → (ℝ≥0 → EuclideanSpace ℝ (Fin 2)) → ℝ} (hF : ∀ s, Measurable (F s))
    (hmap : ∀ z, (μ z).map (LatticeProb.clockRead m) = (planarLaw z).map halfRead)
    (hgood : ∀ z, ∀ᵐ x ∂(μ z), LatticeProb.GoodClock (LatticeProb.crossClock m fun u => x u))
    (hstrict : ∀ z, ∀ᵐ x ∂(μ z), LatticeProb.InvClockStrict m x)
    (hFA : ∀ z (s : ℝ≥0), ∀ᵐ x ∂(μ z), (LatticeProb.pathClockInv m x s).toReal =
      F s fun t => LatticeProb.clockPath m (fun u => x u) t) (z : ℂ) :
    ∀ᵐ w ∂planarLaw z, StrictMono fun t => regularize (rawClock F) t w :=
  (goodClock_regularize_rawClock hF hmap hgood hstrict hFA z).mono fun _ hw => hw.1

/-- **The regularized half-clock almost surely tends to infinity** (second half of
`goodClock_regularize_rawClock`). -/
theorem ae_tendsto_regularize_rawClock {μ : ℂ → Measure C(ℝ≥0, EuclideanSpace ℝ (Fin 2))}
    {m : ℝ≥0∞} {F : ℝ≥0 → (ℝ≥0 → EuclideanSpace ℝ (Fin 2)) → ℝ} (hF : ∀ s, Measurable (F s))
    (hmap : ∀ z, (μ z).map (LatticeProb.clockRead m) = (planarLaw z).map halfRead)
    (hgood : ∀ z, ∀ᵐ x ∂(μ z), LatticeProb.GoodClock (LatticeProb.crossClock m fun u => x u))
    (hstrict : ∀ z, ∀ᵐ x ∂(μ z), LatticeProb.InvClockStrict m x)
    (hFA : ∀ z (s : ℝ≥0), ∀ᵐ x ∂(μ z), (LatticeProb.pathClockInv m x s).toReal =
      F s fun t => LatticeProb.clockPath m (fun u => x u) t) (z : ℂ) :
    ∀ᵐ w ∂planarLaw z, Tendsto (fun t => regularize (rawClock F) t w) atTop atTop :=
  (goodClock_regularize_rawClock hF hmap hgood hstrict hFA z).mono fun _ hw => hw.2

end MatedCRT
