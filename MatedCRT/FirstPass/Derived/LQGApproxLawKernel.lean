import MatedCRT.FirstPass.Derived.LQGApproxPathKernel
import MatedCRT.FirstPass.Derived.LQGClockApproxMeasurable
import MatedCRT.FirstPass.Derived.FieldCoordinateCircleAverages
import MatedCRT.FirstPass.Derived.ContinuousMapLimitSelection
import MatedCRT.FirstPass.Derived.ProbabilityMeasurePolish

/-!
# Approximating Liouville Brownian motion law kernels and a Borel law-field selection

Let `x : LQGMetric.CoordJ → ℝ` be the Polish coordinates of a whole-plane distribution and
`coordCircleAverage x r z` its circle-average process. For a Borel set `G` of coordinates on which the circle
averages at every dyadic radius `ε_n = 2^{-n}` (`dyadicScale n`) are continuous in the center, the approximating
LQG clock `A_n(b, t) = ∫_0^t ε_n^{γ²/2} e^{γ h_{ε_n}(b_s)} ds + 2^{-n} t` (`lqgApproxClockPlus`) is a time-change
clock for every continuous path `b`, and the time-changed path `t ↦ b (A_n(b, ·)⁻¹(t))` is continuous in `b`.
Its law under planar Brownian motion from `z` is the approximating path law `Q_n(x, z)`. Off `G` the law of the
constant path at `z` is used.

The time-changed path is jointly Borel in the coordinates and the Brownian path: its evaluation at time `t` is
`b (A_n(x, b, ·)⁻¹(t))`, and `{A_n(x, b, ·)⁻¹(t) ≤ s} = {t ≤ A_n(x, b, s)}` for a time-change clock. Hence
`x ↦ Q_n(x, z)` is Borel for the evaluation σ-algebra on probability measures. The Liouville Brownian motion law
field `K_γ(x) ∈ C(ℂ, P(C(ℝ≥0, ℂ)))` is selected as the limit of `n ↦ Q_n(x, z_j)` along a dense sequence `z_j`
of the plane (`limitSelection`); it is Borel in `x`, and it is the continuous law field `L` whenever
`Q_n(x, z_j) → L(z_j)` for every `j`.

## Main statements

* `MatedCRT.approxLawKernel`, `MatedCRT.measurable_approxLawKernel`: the approximating path-law kernels `Q_n`.
* `MatedCRT.tendsto_approxLawKernel`: on `G`, `Q_n(x, z)` converges weakly to the law of the Liouville Brownian
  motion path of an LQG clock of the circle averages of `x`.
* `MatedCRT.lbmLawFieldSelection`, `MatedCRT.measurable_lbmLawFieldSelection`,
  `MatedCRT.lbmLawFieldSelection_eq`: the Borel selection `K_γ` of the law field.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set MarkovProcess
open _root_.HarmonicBalls
open scoped NNReal

namespace MatedCRT

/-! ### The time-change clock inverse -/

/-- For a time-change clock `f`, `f⁻¹(t) ≤ s` if and only if `t ≤ f(s)`. -/
theorem clockInverse_le_iff_of_isTimeChangeClock {f : ℝ≥0 → ℝ} (hf : IsTimeChangeClock f) (t s : ℝ≥0) :
    _root_.HarmonicBalls.clockInverse f t ≤ s ↔ (t : ℝ) ≤ f s := by
  obtain ⟨u, hu⟩ := IsTimeChangeClock.surjective_toNNReal hf t
  change Real.toNNReal (f u) = t at hu
  subst hu
  have hfu : 0 ≤ f u := by
    simpa [hf.map_zero] using hf.strictMono.monotone (show 0 ≤ u from bot_le)
  rw [clockInverse_clockValue hf.map_zero hf.strictMono, Real.coe_toNNReal _ hfu]
  exact hf.strictMono.le_iff_le.symm

/-- The inverse of a measurable family of time-change clocks is measurable in the parameter at every time. -/
theorem measurable_clockInverse_of_isTimeChangeClock {Y : Type*} [MeasurableSpace Y] {A : Y → ℝ≥0 → ℝ}
    (hA : ∀ y, IsTimeChangeClock (A y)) (hm : ∀ s, Measurable fun y => A y s) (t : ℝ≥0) :
    Measurable fun y => _root_.HarmonicBalls.clockInverse (A y) t := by
  refine measurable_of_Iic fun s => ?_
  have h : (fun y => _root_.HarmonicBalls.clockInverse (A y) t) ⁻¹' Iic s = {y | (t : ℝ) ≤ A y s} := by
    ext y
    exact clockInverse_le_iff_of_isTimeChangeClock (hA y) t s
  rw [h]
  exact measurableSet_le measurable_const (hm s)

/-! ### Circle averages on a good set of coordinates -/

section GoodSet

variable {G : Set (LQGMetric.CoordJ → ℝ)}

open Classical in
/-- The circle-average process of the coordinates `x` on the set `G`, and the zero process off `G`. -/
noncomputable def coordCircleAverageOn (G : Set (LQGMetric.CoordJ → ℝ)) (x : LQGMetric.CoordJ → ℝ) :
    ℝ → ℂ → ℝ :=
  if x ∈ G then coordCircleAverage x else fun _ _ => 0

theorem coordCircleAverageOn_of_mem {x : LQGMetric.CoordJ → ℝ} (hx : x ∈ G) :
    coordCircleAverageOn G x = coordCircleAverage x := by
  simp only [coordCircleAverageOn, hx, ↓reduceIte]

theorem coordCircleAverageOn_of_notMem {x : LQGMetric.CoordJ → ℝ} (hx : x ∉ G) :
    coordCircleAverageOn G x = fun (_ : ℝ) (_ : ℂ) => (0 : ℝ) := by
  simp only [coordCircleAverageOn, hx, ↓reduceIte]

/-- The circle averages on a Borel set `G` are jointly Borel in the coordinates and the center at every radius. -/
theorem measurable_coordCircleAverageOn (hG : MeasurableSet G) (r : ℝ) :
    Measurable fun q : (LQGMetric.CoordJ → ℝ) × ℂ => coordCircleAverageOn G q.1 r q.2 := by
  classical
  have hdec : Measurable fun q : (LQGMetric.CoordJ → ℝ) × ℂ => (q.1, r, q.2) :=
    measurable_fst.prodMk (measurable_const.prodMk measurable_snd)
  have h1 : Measurable fun q : (LQGMetric.CoordJ → ℝ) × ℂ => coordCircleAverage q.1 r q.2 := by
    have h := measurable_coordCircleAverage.comp hdec
    simp only [Function.comp_def] at h
    exact h
  have heq : (fun q : (LQGMetric.CoordJ → ℝ) × ℂ => coordCircleAverageOn G q.1 r q.2) =
      fun q => if q.1 ∈ G then coordCircleAverage q.1 r q.2 else 0 := by
    funext q
    by_cases hq : q.1 ∈ G
    · simp only [coordCircleAverageOn_of_mem hq, hq, ↓reduceIte]
    · simp only [coordCircleAverageOn_of_notMem hq, hq, ↓reduceIte]
  rw [heq]
  exact Measurable.ite (measurable_fst hG) h1 measurable_const

/-- If the circle averages are continuous in the center at every dyadic radius on `G`, then so are the circle
averages on `G` for all coordinates. -/
theorem continuous_coordCircleAverageOn
    (hGc : ∀ x ∈ G, ∀ n : ℕ, Continuous (coordCircleAverage x (dyadicScale n)))
    (x : LQGMetric.CoordJ → ℝ) (n : ℕ) : Continuous (coordCircleAverageOn G x (dyadicScale n)) := by
  by_cases hx : x ∈ G
  · rw [coordCircleAverageOn_of_mem hx]
    exact hGc x hx n
  · rw [coordCircleAverageOn_of_notMem hx]
    exact continuous_const

/-- The approximating Liouville Brownian motion path `t ↦ b (A_n(x, b, ·)⁻¹(t))` of the circle averages on `G`, as
a function of the coordinates `x` and the Brownian path `b`. -/
noncomputable def approxLBMPathOn (γ : ℝ) (G : Set (LQGMetric.CoordJ → ℝ)) (n : ℕ)
    (p : (LQGMetric.CoordJ → ℝ) × ContinuousPath ℂ) : ContinuousPath ℂ :=
  lbmContinuousPath (lqgApproxClockPlus γ (coordCircleAverageOn G p.1) n) p.2

theorem preimage_approxLBMPathOn (γ : ℝ) (n : ℕ) (x : LQGMetric.CoordJ → ℝ) (A : Set (ContinuousPath ℂ)) :
    Prod.mk x ⁻¹' (approxLBMPathOn γ G n ⁻¹' A) =
      lbmContinuousPath (lqgApproxClockPlus γ (coordCircleAverageOn G x) n) ⁻¹' A :=
  rfl

/-- **Joint measurability of the approximating time-changed path** in the coordinates and the Brownian path. -/
theorem measurable_approxLBMPathOn (hG : MeasurableSet G)
    (hGc : ∀ x ∈ G, ∀ n : ℕ, Continuous (coordCircleAverage x (dyadicScale n))) (γ : ℝ) (n : ℕ) :
    Measurable (approxLBMPathOn γ G n) := by
  have hA : ∀ p : (LQGMetric.CoordJ → ℝ) × ContinuousPath ℂ,
      IsTimeChangeClock (lqgApproxClockPlus γ (coordCircleAverageOn G p.1) n p.2) := fun p =>
    isTimeChangeClock_lqgApproxClockPlus (continuous_coordCircleAverageOn hGc p.1 n) p.2
  have hm : ∀ s : ℝ≥0, Measurable fun p : (LQGMetric.CoordJ → ℝ) × ContinuousPath ℂ =>
      lqgApproxClockPlus γ (coordCircleAverageOn G p.1) n p.2 s := fun s =>
    LQGClockApproxMeasurable.measurable_lqgClockApprox_add_field (measurable_coordCircleAverageOn hG) γ
      (dyadicScale n) s
  refine ContinuousMap.measurable_iff_eval.2 fun t => ?_
  have heq : (fun p : (LQGMetric.CoordJ → ℝ) × ContinuousPath ℂ => approxLBMPathOn γ G n p t) =
      fun p => p.2 (_root_.HarmonicBalls.clockInverse
        (lqgApproxClockPlus γ (coordCircleAverageOn G p.1) n p.2) t) := by
    funext p
    rw [approxLBMPathOn, lbmContinuousPath_of_isTimeChangeClock (hA p)]
    rfl
  rw [heq]
  exact measurable_path_eval_pair.comp
    (measurable_snd.prodMk (measurable_clockInverse_of_isTimeChangeClock hA hm t))

end GoodSet

/-! ### The approximating path-law kernels -/

/-- The law of the constant path at `z`. -/
noncomputable def constPathLaw (z : ℂ) : ProbabilityMeasure (ContinuousPath ℂ) :=
  diracProba (ContinuousMap.const ℝ≥0 z : ContinuousPath ℂ)

/-- The law of the constant path depends continuously on its value. -/
theorem continuous_constPathLaw : Continuous constPathLaw :=
  (continuous_diracProba (X := ContinuousPath ℂ)).comp ContinuousMap.continuous_const'

/-- The field `z ↦ δ_{const z}` of laws of constant paths, a continuous law field. -/
noncomputable def constPathLawField : C(ℂ, ProbabilityMeasure (ContinuousPath ℂ)) :=
  ⟨constPathLaw, continuous_constPathLaw⟩

theorem coe_planarBrownianPathLaw (z : ℂ) {g : ContinuousPath ℂ → ContinuousPath ℂ}
    (hg : AEMeasurable g (planarBrownianMotion z)) :
    (planarBrownianPathLaw z g hg : Measure (ContinuousPath ℂ)) = Measure.map g (planarBrownianMotion z) :=
  rfl

open Classical in
/-- **The approximating path-law kernel `Q_n(x, z)`.** For coordinates `x ∈ G` whose circle averages at the dyadic
radius `ε_n = 2^{-n}` (`dyadicScale n`) are continuous in the center, `Q_n(x, z)` is the law under planar Brownian
motion from `z` of the time-changed path `t ↦ b (A_n(b, ·)⁻¹(t))` of the approximating LQG clock
`A_n(b, t) = ∫_0^t ε_n^{γ²/2} e^{γ h_{ε_n}(b_s)} ds + 2^{-n} t` of `h_{ε_n} = coordCircleAverage x ε_n`. Otherwise it
is the law of the constant path at `z`. -/
noncomputable def approxLawKernel (γ : ℝ) (G : Set (LQGMetric.CoordJ → ℝ)) (n : ℕ) (x : LQGMetric.CoordJ → ℝ)
    (z : ℂ) : ProbabilityMeasure (ContinuousPath ℂ) :=
  if h : x ∈ G ∧ Continuous (coordCircleAverage x (dyadicScale n)) then
    planarBrownianPathLaw z (lbmContinuousPath (lqgApproxClockPlus γ (coordCircleAverage x) n))
      (measurable_lbmContinuousPath_lqgApproxClockPlus (γ := γ) (hε := coordCircleAverage x) (n := n)
        h.2).aemeasurable
  else constPathLaw z

section Kernel

variable {γ : ℝ} {G : Set (LQGMetric.CoordJ → ℝ)} {n : ℕ} {x : LQGMetric.CoordJ → ℝ}

theorem approxLawKernel_of_mem (z : ℂ) (hx : x ∈ G) (hc : Continuous (coordCircleAverage x (dyadicScale n))) :
    approxLawKernel γ G n x z =
      planarBrownianPathLaw z (lbmContinuousPath (lqgApproxClockPlus γ (coordCircleAverage x) n))
        (measurable_lbmContinuousPath_lqgApproxClockPlus (γ := γ) (hε := coordCircleAverage x) (n := n)
          hc).aemeasurable := by
  rw [approxLawKernel, dite_eq_left ⟨hx, hc⟩]

theorem approxLawKernel_of_notMem (z : ℂ) (hx : x ∉ G) : approxLawKernel γ G n x z = constPathLaw z := by
  simp only [approxLawKernel, hx, false_and, ↓reduceDIte]

/-- **Measurability of the approximating kernels in the field.** For a Borel set `G` of coordinates whose circle
averages are continuous at every dyadic radius, `x ↦ Q_n(x, z)` is Borel. -/
theorem measurable_approxLawKernel (hG : MeasurableSet G)
    (hGc : ∀ x ∈ G, ∀ n : ℕ, Continuous (coordCircleAverage x (dyadicScale n))) (n : ℕ) (z : ℂ) :
    Measurable fun x => approxLawKernel γ G n x z := by
  classical
  have hΨ := measurable_approxLBMPathOn hG hGc γ n
  have hμ : Measurable fun x : LQGMetric.CoordJ → ℝ =>
      ((approxLawKernel γ G n x z : ProbabilityMeasure (ContinuousPath ℂ)) : Measure (ContinuousPath ℂ)) := by
    refine Measure.measurable_of_measurable_coe _ fun A hA => ?_
    have heq : (fun x : LQGMetric.CoordJ → ℝ =>
        ((approxLawKernel γ G n x z : ProbabilityMeasure (ContinuousPath ℂ)) : Measure (ContinuousPath ℂ)) A) =
        fun x => if x ∈ G then planarBrownianMotion z (Prod.mk x ⁻¹' (approxLBMPathOn γ G n ⁻¹' A))
          else ((constPathLaw z : ProbabilityMeasure (ContinuousPath ℂ)) : Measure (ContinuousPath ℂ)) A := by
      funext x
      by_cases hx : x ∈ G
      · simp only [hx, ↓reduceIte]
        rw [approxLawKernel_of_mem z hx (hGc x hx n), coe_planarBrownianPathLaw,
          Measure.map_apply (measurable_lbmContinuousPath_lqgApproxClockPlus (γ := γ) (hGc x hx n)) hA,
          preimage_approxLBMPathOn, coordCircleAverageOn_of_mem hx]
      · simp only [hx, ↓reduceIte]
        rw [approxLawKernel_of_notMem z hx]
    rw [heq]
    exact Measurable.ite hG (measurable_measure_prodMk_left (hΨ hA)) measurable_const
  intro s hs
  obtain ⟨t, ht, rfl⟩ := hs
  exact hμ ht

/-- **Weak convergence of the approximating kernels on `G`.** If `x ∈ G` and `F` is an LQG clock of planar Brownian
motion from `z` for the circle averages of `x` which is almost surely a time-change clock, then `Q_n(x, z)`
converges weakly to the law of the Liouville Brownian motion path `t ↦ b (F(b)⁻¹(t))`. -/
theorem tendsto_approxLawKernel (hGc : ∀ x ∈ G, ∀ n : ℕ, Continuous (coordCircleAverage x (dyadicScale n)))
    (hx : x ∈ G) {z : ℂ} {F : ContinuousPath ℂ → ℝ≥0 → ℝ}
    (hF : IsLQGClock planarBrownianMotion γ (coordCircleAverage x) z F)
    (hFc : ∀ᵐ b ∂planarBrownianMotion z, IsTimeChangeClock (F b)) :
    Tendsto (fun n => approxLawKernel γ G n x z) atTop
      (𝓝 (planarBrownianPathLaw z (lbmContinuousPath F) (aemeasurable_lbmContinuousPath hF hFc (hGc x hx)))) := by
  refine (tendsto_planarBrownianPathLaw_lqgApproxClockPlus hF hFc (hGc x hx)).congr fun n => ?_
  rw [approxLawKernel_of_mem z hx (hGc x hx n)]

end Kernel

/-! ### Borel selection of the law field -/

/-- A fixed dense sequence of points of the plane. -/
noncomputable def complexDenseSeq : ℕ → ℂ :=
  TopologicalSpace.denseSeq ℂ

theorem denseRange_complexDenseSeq : DenseRange complexDenseSeq :=
  TopologicalSpace.denseRange_denseSeq ℂ

/-- **The Borel selection `K_γ` of the Liouville Brownian motion law field.** Where every sequence
`n ↦ Q_n(x, z_j)` along the dense sequence `z_j = complexDenseSeq j` converges and the limits extend to a continuous
law field, `K_γ(x)` is that field; elsewhere it is the field of laws of constant paths. -/
noncomputable def lbmLawFieldSelection (γ : ℝ) (G : Set (LQGMetric.CoordJ → ℝ)) :
    (LQGMetric.CoordJ → ℝ) → C(ℂ, ProbabilityMeasure (ContinuousPath ℂ)) :=
  limitSelection complexDenseSeq (approxLawKernel γ G) constPathLawField

section Selection

variable {γ : ℝ} {G : Set (LQGMetric.CoordJ → ℝ)}

/-- The law-field selection `K_γ` is Borel for the Borel σ-algebra of the compact-open topology. -/
theorem measurable_lbmLawFieldSelection (hG : MeasurableSet G)
    (hGc : ∀ x ∈ G, ∀ n : ℕ, Continuous (coordCircleAverage x (dyadicScale n))) :
    Measurable (lbmLawFieldSelection γ G) :=
  measurable_limitSelection denseRange_complexDenseSeq fun n j =>
    measurable_approxLawKernel hG hGc n (complexDenseSeq j)

/-- If `Q_n(x, z_j) → L(z_j)` for every point `z_j` of the dense sequence and a continuous law field `L`, then
`K_γ(x) = L`. -/
theorem lbmLawFieldSelection_eq {x : LQGMetric.CoordJ → ℝ} {L : C(ℂ, ProbabilityMeasure (ContinuousPath ℂ))}
    (hL : ∀ j, Tendsto (fun n => approxLawKernel γ G n x (complexDenseSeq j)) atTop
      (𝓝 (L (complexDenseSeq j)))) :
    lbmLawFieldSelection γ G x = L :=
  limitSelection_eq denseRange_complexDenseSeq hL

end Selection

end MatedCRT
