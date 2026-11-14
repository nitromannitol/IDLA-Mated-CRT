import MatedCRT.FirstPass.Derived.MarkovTimeChangeInfinity
import LatticeProb.Prob.MarkovAtMap
import LatticeProb.Prob.CrossingTimesClock15

/-!
# Markovian time-changed planar Brownian motions in half-speed Euclidean coordinates

A Markovian time-changed planar Brownian motion `P` (Definitions 7.1-7.2 of Berestycki-Gwynne, typed in
`MatedCRT.IsMarkovTCBM`) lives on `C([0,∞), ℂ)` with the planar Brownian laws of generator `Δ / 2`.  The
Lattice-Probability statements about crossing clocks of time-changed Brownian motions are written for
`EuclideanSpace ℝ (Fin d)` with the Brownian motion of generator `Δ / (2 d)`, which for `d = 2` is the planar
Brownian motion run at half speed.  This file transports `P` to those coordinates:

* `halfPath x = (u ↦ toEuclid (x (u / 2)))`, a continuous map of path spaces;
* `euclidFamily P y = (P (toEuclid⁻¹ y)).map halfPath`, a continuous family of path laws on
  `C([0,∞), ℝ²)`, Markovian at every time when `P` is (`markovAt_euclidFamily`, from the transport of the
  Markov property along continuous maps of path spaces);
* `IsMarkovTCBM.exists_coupling_euclid`: the coupling of Definition 7.2 in these coordinates, with `τ_u → ∞`
  and a Brownian motion of `LatticeProb.IsBrownianSpace 2` with everywhere continuous, strongly measurable
  paths;
* `IsMarkovTCBM.exists_clockFunctional`: the crossing clock of the half-speed path is a fixed measurable
  functional of the clock-read path, almost surely under every `euclidFamily P y`, with the shift identity.
-/

open MeasureTheory MarkovProcess Filter Topology ProbabilityTheory
open scoped NNReal ENNReal

namespace MatedCRT

open PlanarBrownianSpace

/-- The half-speed Euclidean reading `u ↦ toEuclid (x (u / 2))` of a planar path. -/
noncomputable def halfPath (x : ContinuousPath ℂ) : C(ℝ≥0, EuclideanSpace ℝ (Fin 2)) :=
  (⟨toEuclid, toEuclid.continuous⟩ : C(ℂ, EuclideanSpace ℝ (Fin 2))).comp
    (x.comp ⟨fun u => 2⁻¹ * u, continuous_const.mul continuous_id⟩)

@[simp] lemma halfPath_apply (x : ContinuousPath ℂ) (u : ℝ≥0) :
    halfPath x u = toEuclid (x (2⁻¹ * u)) := rfl

lemma continuous_halfPath : Continuous halfPath :=
  (ContinuousMap.continuous_postcomp _).comp (ContinuousMap.continuous_precomp _)

/-- The half-speed Euclidean reading of a planar path as a function on `ℝ≥0`. -/
noncomputable def halfRead (x : ContinuousPath ℂ) : ℝ≥0 → EuclideanSpace ℝ (Fin 2) :=
  fun u => halfPath x u

lemma measurable_halfRead : Measurable halfRead :=
  measurable_pi_iff.mpr fun u => ((continuous_eval_const u).comp continuous_halfPath).measurable

/-- The family of path laws `P` of planar paths, read at half speed in Euclidean coordinates. -/
noncomputable def euclidFamily (P : PathLawFamily) (y : EuclideanSpace ℝ (Fin 2)) :
    ProbabilityMeasure C(ℝ≥0, EuclideanSpace ℝ (Fin 2)) :=
  (P (toEuclid.symm y)).map halfPath

lemma euclidFamily_apply (P : PathLawFamily) (y : EuclideanSpace ℝ (Fin 2)) :
    (euclidFamily P y : Measure C(ℝ≥0, EuclideanSpace ℝ (Fin 2))) =
      (P (toEuclid.symm y) : Measure (ContinuousPath ℂ)).map halfPath := by
  simp [euclidFamily]

theorem continuous_euclidFamily (P : PathLawFamily) : Continuous (euclidFamily P) :=
  (ProbabilityMeasure.continuous_map continuous_halfPath).comp
    (P.continuous.comp toEuclid.symm.continuous)

/-- **The Markov property is inherited by the half-speed Euclidean family.** -/
theorem markovAt_euclidFamily {P : PathLawFamily} (h : IsMarkovianPathFamily P)
    (y : EuclideanSpace ℝ (Fin 2)) (t : ℝ≥0) : LatticeProb.MarkovAt (euclidFamily P) y t := by
  have key := LatticeProb.MarkovAt.map_paths (K := ⇑P) (K' := euclidFamily P)
    (continuous_euclidFamily P) (z := toEuclid.symm y) (s := 2⁻¹ * t) (s' := t)
    (h (toEuclid.symm y) (2⁻¹ * t)) halfPath continuous_halfPath toEuclid
    (fun w => by rw [euclidFamily_apply, LinearIsometryEquiv.symm_apply_apply])
    (fun x => by
      refine ContinuousMap.ext fun u => ?_
      simp [LatticeProb.stopPath_apply, mul_min_of_nonneg _ _ (zero_le : (0 : ℝ≥0) ≤ 2⁻¹)])
    (fun x => by
      refine ContinuousMap.ext fun u => ?_
      simp [mul_add])
    (fun x => rfl)
  rw [LinearIsometryEquiv.apply_symm_apply] at key
  exact key

/-- Translating a Brownian motion started at `0` gives a Brownian motion started at `y`. -/
theorem isBrownianSpace_add_const {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {d : ℕ}
    {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)} (hB : LatticeProb.IsBrownianSpace d 0 B P)
    (y : EuclideanSpace ℝ (Fin d)) :
    LatticeProb.IsBrownianSpace d y (fun t ω => y + B t ω) P where
  start := by
    filter_upwards [hB.start] with ω h
    simp [h]
  coord i := by
    have e : (fun (t : ℝ≥0) ω => Real.sqrt d * ((y + B t ω) i - y i)) =
        fun t ω => Real.sqrt d * (B t ω i - (0 : EuclideanSpace ℝ (Fin d)) i) := by
      funext t ω
      simp
    rw [e]
    exact hB.coord i
  indep := by
    have h := hB.indep.comp (fun i (p : ℝ≥0 → ℝ) => fun t => y i + p t)
      (fun i => measurable_pi_iff.2 fun t => measurable_const.add (measurable_pi_apply t))
    exact h

/-- Independence is preserved by composition with a measurable map of known law. -/
theorem iIndepFun_comp_map {ι : Type*} [Fintype ι] {Ω Ω' β : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] [MeasurableSpace β] {P' : Measure Ω'} {Q : Measure Ω}
    [IsProbabilityMeasure Q] {X : ι → Ω' → β} (hX : ∀ i, Measurable (X i))
    (h : iIndepFun X P') {Y : Ω → Ω'} (hY : Measurable Y) (hlaw : Q.map Y = P') :
    iIndepFun (fun i ω => X i (Y ω)) Q := by
  subst hlaw
  have : IsProbabilityMeasure (Q.map Y) :=
    ⟨by rw [Measure.map_apply hY MeasurableSet.univ, Set.preimage_univ, measure_univ]⟩
  rw [iIndepFun_iff_map_fun_eq_pi_map
    (f := fun i ω => X i (Y ω)) (fun i => ((hX i).comp hY).aemeasurable)]
  rw [iIndepFun_iff_map_fun_eq_pi_map (fun i => (hX i).aemeasurable)] at h
  have e1 : Q.map (fun ω i => X i (Y ω)) = (Q.map Y).map (fun ω' i => X i ω') := by
    rw [Measure.map_map (measurable_pi_iff.2 hX) hY]
    rfl
  rw [e1, h]
  congr 1
  funext i
  rw [Measure.map_map (hX i) hY]
  rfl

/-- **Planar Brownian motion as `IsBrownianSpace 2 0`, for a measurable map of planar law.** -/
theorem isBrownianSpace_halfSpeedPath_of_map (z : ℂ) {Ω : Type*} [MeasurableSpace Ω]
    {Q : Measure Ω} [IsProbabilityMeasure Q] {Y : Ω → ContinuousPath ℂ} (hY : Measurable Y)
    (hlaw : Q.map Y = planarLaw z) :
    LatticeProb.IsBrownianSpace 2 0 (fun t ω => halfSpeedPath z t (Y ω)) Q := by
  have hB := isBrownianSpace_halfSpeedPath z
  have hL : HasLaw Y (HarmonicBalls.planarBrownianMotion z) Q := ⟨hY.aemeasurable, hlaw⟩
  refine ⟨?_, fun i => isBrownianReal_comp_hasLaw (hB.coord i) hL, ?_⟩
  · have := hB.start
    rw [← hL.map_eq] at this
    exact ae_of_ae_map hY.aemeasurable this
  · refine iIndepFun_comp_map (X := fun (i : Fin 2) (b : ContinuousPath ℂ) (t : ℝ≥0) =>
      halfSpeedPath z t b i) (fun i => ?_) hB.indep hY hlaw
    refine measurable_pi_iff.2 fun t => ?_
    have hc : Continuous fun w : ℂ => (toEuclid (w - z)) i :=
      (EuclideanSpace.proj i).continuous.comp (toEuclid.continuous.comp
        (continuous_id.sub continuous_const))
    exact hc.measurable.comp (measurable_eval_path (2⁻¹ * t))

/-- **The coupling of Definition 7.2 in half-speed Euclidean coordinates.** For a Markovian time-changed
planar Brownian motion, for every starting point `y` of `ℝ²` there is a probability space carrying a
Brownian motion `B` of `IsBrownianSpace 2 y` with continuous, strongly measurable paths, a process `τ`
continuous, strictly increasing, from `0` and unbounded, and `X` with `X_u = B_{τ_u}` whose law is
`euclidFamily P y`; the law of `B`, as a measure on `ℝ≥0 → ℝ²`, is the law of the half-speed Euclidean
reading `halfRead` of the planar Brownian motion started at `toEuclid.symm y`. -/
theorem IsMarkovTCBM.exists_coupling_euclid {P : PathLawFamily} (h : IsMarkovTCBM P)
    (y : EuclideanSpace ℝ (Fin 2)) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (Q : Measure Ω) (_ : IsProbabilityMeasure Q)
      (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin 2)) (τ : Ω → ℝ≥0 → ℝ≥0)
      (X : Ω → C(ℝ≥0, EuclideanSpace ℝ (Fin 2))),
      LatticeProb.IsBrownianSpace 2 y B Q ∧ (∀ t, StronglyMeasurable (B t)) ∧
      (∀ ω, Continuous fun t => B t ω) ∧ AEMeasurable X Q ∧
      (∀ᵐ ω ∂Q, Continuous (τ ω) ∧ StrictMono (τ ω) ∧ τ ω 0 = 0 ∧ Tendsto (τ ω) atTop atTop ∧
        ∀ u, X ω u = B (τ ω u) ω) ∧
      (euclidFamily P y : Measure C(ℝ≥0, EuclideanSpace ℝ (Fin 2))) = Q.map X ∧
      Q.map (fun ω t => B t ω) = (planarLaw (toEuclid.symm y)).map halfRead := by
  obtain ⟨Ω, mΩ, Q, hQ, B, X, τ, hBm, hXm, hBlaw, hτ, hPz⟩ :=
    h.exists_coupling_tendsto (toEuclid.symm y)
  have hB0 : Measurable (hBm.mk B) := hBm.measurable_mk
  have hBB0 : B =ᵐ[Q] hBm.mk B := hBm.ae_eq_mk
  have hlaw : Q.map (hBm.mk B) = planarLaw (toEuclid.symm y) := by
    rw [← Measure.map_congr hBB0]
    exact hBlaw
  have hBS := isBrownianSpace_add_const (isBrownianSpace_halfSpeedPath_of_map _ hB0 hlaw) y
  have hEq : (fun (t : ℝ≥0) ω => y + halfSpeedPath (toEuclid.symm y) t (hBm.mk B ω)) =
      fun t ω => halfPath (hBm.mk B ω) t := by
    funext t ω
    rw [halfPath_apply]
    simp only [halfSpeedPath, map_sub, LinearIsometryEquiv.apply_symm_apply]
    abel
  rw [hEq] at hBS
  have hev : ∀ t, Measurable fun ω => halfPath (hBm.mk B ω) t := fun t =>
    ((continuous_eval_const t).comp continuous_halfPath).measurable.comp hB0
  refine ⟨Ω, mΩ, Q, hQ, fun t ω => halfPath (hBm.mk B ω) t,
    fun ω u => 2 * τ ω (2⁻¹ * u), fun ω => halfPath (X ω), hBS,
    fun t => (hev t).stronglyMeasurable, fun ω => (halfPath (hBm.mk B ω)).continuous,
    continuous_halfPath.measurable.comp_aemeasurable hXm, ?_, ?_, ?_⟩
  · filter_upwards [hτ, hBB0] with ω ⟨hc, hs, h0, ht, hX⟩ hb
    refine ⟨continuous_const.mul (hc.comp (continuous_const.mul continuous_id)),
      fun u v huv => ?_, by simp [h0], ?_, fun u => ?_⟩
    · have h1 : 2⁻¹ * u < 2⁻¹ * v := mul_lt_mul_of_pos_left huv (by norm_num)
      exact mul_lt_mul_of_pos_left (hs h1) (by norm_num)
    · exact (tendsto_id.const_mul_atTop' (by norm_num)).comp
        (ht.comp (tendsto_id.const_mul_atTop' (by norm_num)))
    · simp only [halfPath_apply, hX, ← hb]
      rw [← mul_assoc, inv_mul_cancel₀ (by norm_num), one_mul]
  · rw [euclidFamily_apply, hPz, AEMeasurable.map_map_of_aemeasurable continuous_halfPath.aemeasurable hXm]
    rfl
  · rw [← hlaw, AEMeasurable.map_map_of_aemeasurable measurable_halfRead.aemeasurable hB0.aemeasurable]
    rfl

/-- The coupling of `exists_coupling_euclid` without the identification of the law of `B`, in the form
required by the lemmas on crossing clocks of time-changed Brownian motions. -/
theorem IsMarkovTCBM.exists_coupling_euclid_core {P : PathLawFamily} (h : IsMarkovTCBM P)
    (y : EuclideanSpace ℝ (Fin 2)) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (Q : Measure Ω) (_ : IsProbabilityMeasure Q)
      (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin 2)) (τ : Ω → ℝ≥0 → ℝ≥0)
      (X : Ω → C(ℝ≥0, EuclideanSpace ℝ (Fin 2))),
      LatticeProb.IsBrownianSpace 2 y B Q ∧ (∀ t, StronglyMeasurable (B t)) ∧
      (∀ ω, Continuous fun t => B t ω) ∧ AEMeasurable X Q ∧
      (∀ᵐ ω ∂Q, Continuous (τ ω) ∧ StrictMono (τ ω) ∧ τ ω 0 = 0 ∧ Tendsto (τ ω) atTop atTop ∧
        ∀ u, X ω u = B (τ ω u) ω) ∧
      (euclidFamily P y : Measure C(ℝ≥0, EuclideanSpace ℝ (Fin 2))) = Q.map X := by
  obtain ⟨Ω, mΩ, Q, hQ, B, τ, X, h1, h2, h3, h4, h5, h6, -⟩ := h.exists_coupling_euclid y
  exact ⟨Ω, mΩ, Q, hQ, B, τ, X, h1, h2, h3, h4, h5, h6⟩

/-- **The adapted functional of the crossing clock of a Markovian time-changed planar Brownian motion.**
There is a threshold `m ∈ (0, ∞)` such that for every `s ≥ 0` the inverse crossing clock `A_s` of the
half-speed Euclidean path is, almost surely under every `euclidFamily P y`, one fixed measurable functional `F`
of the path read in its crossing clock, and the increments of `t ↦ A_t` are produced by the same functional on
the shifted clock-read path. -/
theorem IsMarkovTCBM.exists_clockFunctional {P : PathLawFamily} (h : IsMarkovTCBM P) :
    ∃ m : ℝ≥0∞, 0 < m ∧ m < ⊤ ∧ ∀ s : ℝ≥0,
      ∃ F : (ℝ≥0 → EuclideanSpace ℝ (Fin 2)) → ℝ, Measurable F ∧
      (∀ y, ∀ᵐ x ∂(euclidFamily P y : Measure C(ℝ≥0, EuclideanSpace ℝ (Fin 2))),
        (LatticeProb.pathClockInv m x s).toReal =
          F fun t => LatticeProb.clockPath m (fun u => x u) t) ∧
      ∀ y (t : ℝ≥0), ∀ᵐ x ∂(euclidFamily P y : Measure C(ℝ≥0, EuclideanSpace ℝ (Fin 2))),
        (LatticeProb.pathClockInv m x (t + s)).toReal = (LatticeProb.pathClockInv m x t).toReal +
          F fun q => LatticeProb.clockPath m (fun u => x u) (t + q) := by
  obtain ⟨m, hm0, hmt, hm⟩ := LatticeProb.exists_clockFunctional_timeChangedBM.{0} 2 (by norm_num)
  exact ⟨m, hm0, hmt, hm (continuous_euclidFamily P) (markovAt_euclidFamily h.2)
    (fun y => h.exists_coupling_euclid_core y)⟩

end MatedCRT
