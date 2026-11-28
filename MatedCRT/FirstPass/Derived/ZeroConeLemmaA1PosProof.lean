import MatedCRT.FirstPass.Derived.ZeroConeLemmaA1Restricted
import LatticeProb.Prob.ZeroOne

/-!
# Lemma A.1 and Remark A.2 of Gwynne–Miller–Sheffield for the zero cone and its curve

This file proves `ZeroConeLemmaA1Pos D hγ` (`ZeroConeLemmaA1Restricted.lean`) for every mating-of-trees coupling `D`
and `γ ∈ (0, 2)` (`zeroConeLemmaA1Pos`), from two statements about general objects:

* `ZeroConeCircleAverageLemmaA1`: Lemma A.1 of Gwynne–Miller–Sheffield (arXiv:1705.11161,
  `notes/refs/1705.11161.txt` lines 1952-1956) for the circle-average embedding of the `0`-quantum cone built from
  any whole-plane GFF and any two independent standard Brownian motions independent of it;
* `IGFieldDilationMixing`: the circle-average array (at positive radii) of a whole-plane GFF normalized by
  `h_1(0) = 0` plus an independent uniform constant on `[0, 2πχ)` is mixing under the normalized dilation by `2`
  (`igDilationStep γ 2`), the dilation of the field followed by the shift by the multiple of `2πχ` which brings the
  unit-circle average back into `[0, 2πχ)` (Miller–Sheffield, IG IV §2.2.1; the GFF modulo constants).

The second clause of `ZeroConeLemmaA1Pos` (the curve form of Remark A.2) is derived as follows (written answer
`notes/fp-gaps/CODEX-MQ-sbl-17.md`, lines 23-47).

1. `measurePreserving_igDilationStep`: the normalized dilation by any `s > 0` preserves the law of the circle-average
   array, by the scale invariance of the normalized whole-plane GFF and the uniformity of `(U + h_s(0)) mod 2πχ`
   given the field (proved here, following `Sec1.map_affineReroot_igCurve`).
2. The coordinate change of imaginary geometry of the coupling (`IsMatingOfTreesCoupling.igMap`, in the form
   `Sec1.igMap_scale_normalized_identity`) gives, almost surely, `Φ(T K) = affineReroot 0 2 0 ηL`, where `K` is the
   array of the coupling, `T = igDilationStep γ 2` and `Φ` is the curve map (answer, lines 40-45).
3. For a functional `g` as in the clause, `g ∘ Φ` is therefore almost surely invariant under the measure-preserving
   mixing map `T`, hence almost surely constant (`exists_ae_eq_const_of_mixing`; answer, line 47). Only the
   invariance of `g` at the single pair `(C, z) = (2, 0)` is used.

The first clause is `ZeroConeCircleAverageLemmaA1` at the zero-cone data `(X₀, B₀, B₀')` of the coupling (answer,
lines 7-22).
-/

set_option autoImplicit false

noncomputable section

namespace MatedCRT

open MeasureTheory ProbabilityTheory Set Filter Topology ReflectedGMS.GMS MatedCRTHarmonic
open MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.GMS4b
open scoped NNReal ENNReal

/-! ### Invariant functions of a mixing transformation -/

/-- **An almost surely invariant function of a mixing measure-preserving map is almost surely constant.** If `T`
preserves the probability measure `μ` and is mixing (`μ(A ∩ T^{-n} B) → μ(A) μ(B)` for all measurable `A`, `B`),
then every invariant measurable set has measure `0` or `1` (`μ(A) = μ(A ∩ T^{-n} A) → μ(A)²`), so `T` is ergodic and
an almost surely `T`-invariant measurable real function is almost surely constant (Walters, *An introduction to
ergodic theory*, §1.7 and Theorem 1.6). -/
theorem exists_ae_eq_const_of_mixing {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {T : α → α} (hT : MeasurePreserving T μ μ)
    (hmix : ∀ S₁ S₂ : Set α, MeasurableSet S₁ → MeasurableSet S₂ →
      Tendsto (fun n : ℕ => μ (S₁ ∩ T^[n] ⁻¹' S₂)) atTop (𝓝 (μ S₁ * μ S₂)))
    {G : α → ℝ} (hG : Measurable G) (hinv : G ∘ T =ᵐ[μ] G) :
    ∃ c : ℝ, G =ᵐ[μ] Function.const α c := by
  have herg : Ergodic T μ := by
    refine ⟨hT, LatticeProb.preErgodic_of_prob_eq_zero_or_one ?_⟩
    intro A hA hAinv
    have hit : ∀ n : ℕ, T^[n] ⁻¹' A = A := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih => rw [Function.iterate_succ, Set.preimage_comp, ih, hAinv]
    have hlim := hmix A A hA hA
    simp only [hit, Set.inter_self] at hlim
    have heq : μ A = μ A * μ A := tendsto_nhds_unique tendsto_const_nhds hlim
    by_cases h0 : μ A = 0
    · exact Or.inl h0
    · refine Or.inr ((ENNReal.mul_right_inj h0 (measure_ne_top μ A)).1 ?_)
      rw [mul_one]
      exact heq.symm
  exact herg.ae_eq_const_of_ae_eq_comp₀ hG.nullMeasurable hinv

/-! ### The circle-average array of the imaginary-geometry field and its normalized dilation -/

/-- The circle-average array `(ρ, w) ↦ u + h_ρ(w)` of a field `h` plus a constant `u` at positive radii, set to `0`
at radii `ρ ≤ 0` (which the curve map of `IsMatingOfTreesCoupling.igMap` ignores). -/
def igPosCircleProcess (h : Field) (u : ℝ) : ℝ × ℂ → ℝ :=
  fun x => if 0 < x.1 then u + LQGMetric.circleAvg h x.1 x.2 else 0

/-- **The normalized dilation by `s` of a circle-average array modulo `2πχ`**: the array of `h(s ·)` at positive
radii, `(ρ, w) ↦ f(sρ, sw)`, shifted by the multiple of `2πχ` which brings its unit-circle average at `0`,
`f(s, 0)`, into `[0, 2πχ)`. On the array of `(h, U)` it is the array of the normalized pair
`(h(s ·) − h_s(0), (U + h_s(0)) mod 2πχ)` (Miller–Sheffield, IG IV §2.2.1; `notes/fp-gaps/CODEX-MQ-sbl-17.md`,
lines 25-27). -/
def igDilationStep (γ s : ℝ) (f : ℝ × ℂ → ℝ) : ℝ × ℂ → ℝ :=
  fun x => if 0 < x.1 then
    f (s * x.1, (s : ℂ) * x.2) - ((⌊f (s, 0) / (2 * Real.pi * igChi γ)⌋ : ℤ) : ℝ) * (2 * Real.pi * igChi γ)
    else 0

/-- The normalized dilated field `h(s ·) − h_s(0)`. -/
def igNormalizedDilation (s : ℝ) (h : Field) : Field :=
  LQGMetric.addConst (LQGMetric.affineComp s 0 h) (-LQGMetric.circleAvg h s 0)

theorem igPosCircleProcess_of_pos (h : Field) (u : ℝ) {x : ℝ × ℂ} (hx : 0 < x.1) :
    igPosCircleProcess h u x = u + LQGMetric.circleAvg h x.1 x.2 := by
  simp only [igPosCircleProcess, hx, ↓reduceIte]

theorem igPosCircleProcess_of_nonpos (h : Field) (u : ℝ) {x : ℝ × ℂ} (hx : ¬ 0 < x.1) :
    igPosCircleProcess h u x = 0 := by
  simp only [igPosCircleProcess, hx, ↓reduceIte]

theorem igDilationStep_of_nonpos (γ s : ℝ) (f : ℝ × ℂ → ℝ) {x : ℝ × ℂ} (hx : ¬ 0 < x.1) :
    igDilationStep γ s f x = 0 := by
  simp only [igDilationStep, hx, ↓reduceIte]

theorem igDilationStep_igPosCircleProcess_of_pos (γ : ℝ) {s : ℝ} (hs : 0 < s) (h : Field) (u : ℝ)
    {x : ℝ × ℂ} (hx : 0 < x.1) :
    igDilationStep γ s (igPosCircleProcess h u) x =
      u + LQGMetric.circleAvg h (s * x.1) ((s : ℂ) * x.2) -
        ((⌊(u + LQGMetric.circleAvg h s 0) / (2 * Real.pi * igChi γ)⌋ : ℤ) : ℝ) * (2 * Real.pi * igChi γ) := by
  have hsx : 0 < s * x.1 := mul_pos hs hx
  simp only [igDilationStep, igPosCircleProcess, hx, hsx, hs, ↓reduceIte]

theorem curry_igPosCircleProcess_of_pos (h : Field) (u : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    Function.curry (igPosCircleProcess h u) ρ = fun w => LQGMetric.circleAvg h ρ w + u := by
  funext w
  simp only [Function.curry_apply, igPosCircleProcess, hρ, ↓reduceIte]
  exact add_comm _ _

theorem curry_igDilationStep_two_of_pos (γ : ℝ) (h : Field) (u : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    Function.curry (igDilationStep γ 2 (igPosCircleProcess h u)) ρ = fun w =>
      LQGMetric.circleAvg h (2 * ρ) (((2 : ℝ) : ℂ) * w) - LQGMetric.circleAvg h 2 0 +
        (u + LQGMetric.circleAvg h 2 0 -
          ((⌊(u + LQGMetric.circleAvg h 2 0) / (2 * Real.pi * igChi γ)⌋ : ℤ) : ℝ) *
            (2 * Real.pi * igChi γ)) := by
  funext w
  rw [Function.curry_apply, igDilationStep_igPosCircleProcess_of_pos γ two_pos h u (x := (ρ, w)) hρ]
  ring

theorem measurable_igPosCircleProcess :
    Measurable fun q : Field × ℝ => igPosCircleProcess q.1 q.2 := by
  refine measurable_pi_iff.2 fun x => ?_
  by_cases hx : 0 < x.1
  · simp only [igPosCircleProcess, hx, ↓reduceIte]
    exact measurable_snd.add ((LQGMetric.measurable_circleAvg_left x.1 x.2).comp measurable_fst)
  · simp only [igPosCircleProcess, hx, ↓reduceIte]
    exact measurable_const

theorem measurable_igPosCircleProcess_comp {Ω' : Type} [MeasurableSpace Ω'] {h : Ω' → Field}
    {u : Ω' → ℝ} (hh : Measurable h) (hu : Measurable u) :
    Measurable fun ω => igPosCircleProcess (h ω) (u ω) := by
  refine measurable_pi_iff.2 fun x => ?_
  by_cases hx : 0 < x.1
  · simp only [igPosCircleProcess, hx, ↓reduceIte]
    exact hu.add ((LQGMetric.measurable_circleAvg_left x.1 x.2).comp hh)
  · simp only [igPosCircleProcess, hx, ↓reduceIte]
    exact measurable_const

theorem aemeasurable_igPosCircleProcess {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'}
    {h : Ω' → Field} {u : Ω' → ℝ} (hh : Measurable h) (hu : AEMeasurable u P') :
    AEMeasurable (fun ω => igPosCircleProcess (h ω) (u ω)) P' := by
  refine (measurable_igPosCircleProcess_comp hh hu.measurable_mk).aemeasurable.congr ?_
  filter_upwards [hu.ae_eq_mk] with ω hω
  simp only [hω]

theorem measurable_igDilationStep (γ s : ℝ) : Measurable (igDilationStep γ s) := by
  refine measurable_pi_iff.2 fun x => ?_
  by_cases hx : 0 < x.1
  · simp only [igDilationStep, hx, ↓reduceIte]
    exact (measurable_pi_apply (s * x.1, (s : ℂ) * x.2)).sub
      (((measurable_of_countable (fun k : ℤ => (k : ℝ))).comp
        (Int.measurable_floor.comp ((measurable_pi_apply ((s, 0) : ℝ × ℂ)).div_const _))).mul_const _)
  · simp only [igDilationStep, hx, ↓reduceIte]
    exact measurable_const

theorem measurable_igNormalizedDilation (s : ℝ) : Measurable (igNormalizedDilation s) := by
  refine LQGMetric.measurable_distOn_iff.2 fun φ => ?_
  simp only [igNormalizedDilation, LQGMetric.GFFInv.addConst_apply]
  exact ((LQGMetric.measurable_distOn_apply φ).comp (LQGMetric.measurable_affineComp s 0)).add
    ((LQGMetric.measurable_circleAvg_left s 0).neg.const_mul _)

/-- A random variable whose law is the uniform law on `[0, 2πχ)` is almost surely measurable. -/
theorem aemeasurable_of_map_eq_igUniform {γ : ℝ} {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {u : Ω' → ℝ}
    (hulaw : P'.map u = volume[|Ico (0 : ℝ) (2 * Real.pi * igChi γ)]) : AEMeasurable u P' := by
  have hulaw' : P'.map u = LatticeProb.uniformIco (2 * Real.pi * igChi γ) := hulaw
  by_contra hne
  obtain ⟨x, hx⟩ : ∃ x : ℝ, P'.map u = Measure.dirac x :=
    ⟨_, Measure.map_of_not_aemeasurable_of_ne_zero hne (IsProbabilityMeasure.ne_zero P')⟩
  have h1 : LatticeProb.uniformIco (2 * Real.pi * igChi γ) {x} = 0 :=
    ProbabilityTheory.cond_absolutelyContinuous (Real.volume_singleton)
  rw [← hulaw', hx, Measure.dirac_apply_of_mem (Set.mem_singleton x)] at h1
  exact one_ne_zero h1

/-! ### The normalized dilation preserves the law of the array -/

/-- **The dilated array is a modification of the array of the normalized pair.** At each fixed `x`, almost surely,
the normalized dilation by `s` of the array of `(h, u)` agrees at `x` with the array of
`(h(s ·) − h_s(0), (u + h_s(0)) mod 2πχ)`. -/
theorem ae_igDilationStep_igPosCircleProcess {γ s : ℝ} (hs : 0 < s) (hp : 0 < 2 * Real.pi * igChi γ)
    {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} {h : Ω' → Field}
    (hh : LQGMetric.IsWholePlaneGFF h P') (u : Ω' → ℝ) (x : ℝ × ℂ) :
    ∀ᵐ ω ∂P', igDilationStep γ s (igPosCircleProcess (h ω) (u ω)) x =
      igPosCircleProcess (igNormalizedDilation s (h ω))
        (toIcoMod hp 0 (u ω + LQGMetric.circleAvg (h ω) s 0)) x := by
  by_cases hx : 0 < x.1
  · have hA := LQGMetric.CircleAvg.ae_circleAvg_addConst (hh.affineComp hs 0) x.2 hx
    have hB := LQGMetric.CircleAvg.ae_circleAvg_affineComp (hh.affineComp hs 0) hx x.2
    have hC := LQGMetric.CircleAvg.ae_circleAvg_affineComp hh (mul_pos hs hx) ((s : ℂ) * x.2)
    filter_upwards [hA, hB, hC] with ω hAω hBω hCω
    rw [igDilationStep_igPosCircleProcess_of_pos γ hs _ _ hx, igPosCircleProcess_of_pos _ _ hx,
      igNormalizedDilation, hAω, ← hBω, LQGMetric.GM.affineComp_comp hx.ne' hs.ne', add_zero, hCω]
    simp only [toIcoMod, toIcoDiv_eq_floor, sub_zero, zsmul_eq_mul]
    ring
  · refine Filter.Eventually.of_forall fun ω => ?_
    rw [igDilationStep_of_nonpos γ s _ hx, igPosCircleProcess_of_nonpos _ _ hx]

/-- **The normalized pair has the law of the pair** (scale invariance of the normalized whole-plane GFF and
uniformity of `(u + h_s(0)) mod 2πχ` given the field). -/
theorem map_igNormalizedDilation_pair {γ s : ℝ} (hs : 0 < s) (hp : 0 < 2 * Real.pi * igChi γ)
    {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} {h : Ω' → Field} {u : Ω' → ℝ}
    (hh : LQGMetric.IsNormalizedWPGFF h P') (hum : Measurable u)
    (hulaw : P'.map u = LatticeProb.uniformIco (2 * Real.pi * igChi γ)) (hind : IndepFun u h P') :
    P'.map (fun ω => (igNormalizedDilation s (h ω), toIcoMod hp 0 (u ω + LQGMetric.circleAvg (h ω) s 0))) =
      P'.map (fun ω => (h ω, u ω)) := by
  have hP : IsProbabilityMeasure P' := hh.1.gaussian.isProbabilityMeasure
  have hhm : Measurable h := hh.1.measurable
  have ham : Measurable fun g : Field => LQGMetric.circleAvg g s 0 := LQGMetric.measurable_circleAvg_left s 0
  have hGm := measurable_igNormalizedDilation s
  have hGI : Measurable fun ω => igNormalizedDilation s (h ω) := by
    simpa only [Function.comp_def] using hGm.comp hhm
  have hVm : Measurable fun ω => toIcoMod hp 0 (u ω + LQGMetric.circleAvg (h ω) s 0) := by
    simpa only [Function.comp_def, Pi.add_apply] using
      (LatticeProb.measurable_toIcoMod_zero hp).comp (hum.add (ham.comp hhm))
  have hVI := LatticeProb.indepFun_toIcoMod_add_uniformIco hp hum hhm hulaw hind ham
  have hVG := LatticeProb.indepFun_toIcoMod_add_uniformIco_comp hp hum hhm hulaw hind ham hGm
  rw [(indepFun_iff_map_prod_eq_prod_map_map hGI.aemeasurable hVm.aemeasurable).1 hVG.symm,
    (indepFun_iff_map_prod_eq_prod_map_map hhm.aemeasurable hum.aemeasurable).1 hind.symm]
  congr 1
  · exact LQGMetric.CircleAvg.map_affine_sub_circleAvg hh hs 0
  · rw [hVI.1, hulaw]

theorem measurePreserving_igDilationStep_of_measurable {γ s : ℝ} (hs : 0 < s)
    (hp : 0 < 2 * Real.pi * igChi γ) {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} {h : Ω' → Field}
    {u : Ω' → ℝ} (hh : LQGMetric.IsNormalizedWPGFF h P') (hum : Measurable u)
    (hulaw : P'.map u = LatticeProb.uniformIco (2 * Real.pi * igChi γ)) (hind : IndepFun u h P') :
    MeasurePreserving (igDilationStep γ s) (P'.map fun ω => igPosCircleProcess (h ω) (u ω))
      (P'.map fun ω => igPosCircleProcess (h ω) (u ω)) := by
  have hP : IsProbabilityMeasure P' := hh.1.gaussian.isProbabilityMeasure
  have hhm : Measurable h := hh.1.measurable
  have ham : Measurable fun g : Field => LQGMetric.circleAvg g s 0 := LQGMetric.measurable_circleAvg_left s 0
  have hTm := measurable_igDilationStep γ s
  have hKm : Measurable fun ω => igPosCircleProcess (h ω) (u ω) := measurable_igPosCircleProcess_comp hhm hum
  have hTK : Measurable fun ω => igDilationStep γ s (igPosCircleProcess (h ω) (u ω)) := by
    simpa only [Function.comp_def] using hTm.comp hKm
  have hGI : Measurable fun ω => igNormalizedDilation s (h ω) := by
    simpa only [Function.comp_def] using (measurable_igNormalizedDilation s).comp hhm
  have hVm : Measurable fun ω => toIcoMod hp 0 (u ω + LQGMetric.circleAvg (h ω) s 0) := by
    simpa only [Function.comp_def, Pi.add_apply] using
      (LatticeProb.measurable_toIcoMod_zero hp).comp (hum.add (ham.comp hhm))
  have hYm : Measurable fun ω => igPosCircleProcess (igNormalizedDilation s (h ω))
      (toIcoMod hp 0 (u ω + LQGMetric.circleAvg (h ω) s 0)) :=
    measurable_igPosCircleProcess_comp hGI hVm
  have hlaw1 : P'.map (fun ω => igDilationStep γ s (igPosCircleProcess (h ω) (u ω))) =
      P'.map (fun ω => igPosCircleProcess (igNormalizedDilation s (h ω))
        (toIcoMod hp 0 (u ω + LQGMetric.circleAvg (h ω) s 0))) :=
    map_eq_of_forall_ae_eq (X := fun x ω => igDilationStep γ s (igPosCircleProcess (h ω) (u ω)) x)
      (Y := fun x ω => igPosCircleProcess (igNormalizedDilation s (h ω))
        (toIcoMod hp 0 (u ω + LQGMetric.circleAvg (h ω) s 0)) x)
      hTK.aemeasurable hYm.aemeasurable fun x => ae_igDilationStep_igPosCircleProcess hs hp hh.1 u x
  have hlaw2 : P'.map (fun ω => igPosCircleProcess (igNormalizedDilation s (h ω))
      (toIcoMod hp 0 (u ω + LQGMetric.circleAvg (h ω) s 0))) =
      P'.map fun ω => igPosCircleProcess (h ω) (u ω) := by
    have e1 := Measure.map_map measurable_igPosCircleProcess (hGI.prodMk hVm) (μ := P')
    have e2 := Measure.map_map measurable_igPosCircleProcess (hhm.prodMk hum) (μ := P')
    simp only [Function.comp_def] at e1 e2
    rw [← e1, ← e2, map_igNormalizedDilation_pair hs hp hh hum hulaw hind]
  refine ⟨hTm, ?_⟩
  rw [Measure.map_map hTm hKm, Function.comp_def, hlaw1, hlaw2]

/-- **The normalized dilation preserves the law of the circle-average array of the whole-plane GFF modulo `2πχ`.**
Let `h` be a whole-plane GFF normalized by `h_1(0) = 0` and `u` an independent uniform variable on `[0, 2πχ)`. For
every `s > 0`, the array of `(h, u)` and its normalized dilation by `s` have the same law: the field
`h(s ·) − h_s(0)` has the law of `h` (scale invariance), `(u + h_s(0)) mod 2πχ` is uniform and independent of `h`,
and at each fixed positive radius and centre the circle average of `h(s ·) − h_s(0)` is almost surely
`h_{sρ}(sw) − h_s(0)`. -/
theorem measurePreserving_igDilationStep {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) 2) {s : ℝ} (hs : 0 < s)
    {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} {h : Ω' → Field} {u : Ω' → ℝ}
    (hh : LQGMetric.IsNormalizedWPGFF h P')
    (hulaw : P'.map u = volume[|Ico (0 : ℝ) (2 * Real.pi * igChi γ)]) (hind : IndepFun h u P') :
    MeasurePreserving (igDilationStep γ s) (P'.map fun ω => igPosCircleProcess (h ω) (u ω))
      (P'.map fun ω => igPosCircleProcess (h ω) (u ω)) := by
  have hP : IsProbabilityMeasure P' := hh.1.gaussian.isProbabilityMeasure
  have hp : 0 < 2 * Real.pi * igChi γ := by
    have := Sec1.igChi_pos hγ.1 hγ.2
    positivity
  have huae : AEMeasurable u P' := aemeasurable_of_map_eq_igUniform hulaw
  have hu'law : P'.map (huae.mk u) = LatticeProb.uniformIco (2 * Real.pi * igChi γ) := by
    rw [← Measure.map_congr huae.ae_eq_mk]
    exact hulaw
  have hind' : IndepFun (huae.mk u) h P' := (hind.congr (ae_eq_refl _) huae.ae_eq_mk).symm
  have hμ : (P'.map fun ω => igPosCircleProcess (h ω) (u ω)) =
      P'.map fun ω => igPosCircleProcess (h ω) (huae.mk u ω) := by
    refine Measure.map_congr ?_
    filter_upwards [huae.ae_eq_mk] with ω hω
    simp only [hω]
  rw [hμ]
  exact measurePreserving_igDilationStep_of_measurable hs hp hh huae.measurable_mk hu'law hind'

/-! ### The two statements on general objects -/

/-- **Mixing of the whole-plane GFF modulo `2πχ` under dilation** (the whole-plane GFF analogue of Lemma A.1 in
Remark A.2 of Gwynne–Miller–Sheffield, arXiv:1705.11161, `notes/refs/1705.11161.txt` lines 1958-1964, in the mixing
form of the written answer `notes/fp-gaps/CODEX-MQ-sbl-17.md`, lines 25-38: Miller–Sheffield, IG IV, §2.2.1, and the
log-covariance of the whole-plane GFF, Duplantier–Miller–Sheffield, Lemma 4.9 and §4.3). PENDING TRUTH CHECK.

Let `h` be a whole-plane GFF normalized by `h_1(0) = 0` and `u` an independent uniform variable on `[0, 2πχ)`,
`χ = 2/γ − γ/2`, and let `μ` be the law of the circle-average array of `h + u` at positive radii
(`igPosCircleProcess`). The normalized dilation by `2` (`igDilationStep γ 2`), which preserves `μ`
(`measurePreserving_igDilationStep`), is mixing for `μ`: `μ(S₁ ∩ T^{-n} S₂) → μ(S₁) μ(S₂)` for all measurable `S₁`,
`S₂`. -/
def IGFieldDilationMixing (γ : ℝ) (_hγ : γ ∈ Ioo (0 : ℝ) 2) : Prop :=
  ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') (h : Ω' → Field) (u : Ω' → ℝ),
    LQGMetric.IsNormalizedWPGFF h P' →
    P'.map u = volume[|Ico (0 : ℝ) (2 * Real.pi * igChi γ)] → IndepFun h u P' →
    ∀ S₁ S₂ : Set (ℝ × ℂ → ℝ), MeasurableSet S₁ → MeasurableSet S₂ →
      Tendsto (fun n : ℕ => (P'.map fun ω => igPosCircleProcess (h ω) (u ω))
          (S₁ ∩ (igDilationStep γ 2)^[n] ⁻¹' S₂)) atTop
        (𝓝 ((P'.map fun ω => igPosCircleProcess (h ω) (u ω)) S₁ *
          (P'.map fun ω => igPosCircleProcess (h ω) (u ω)) S₂))

/-- **Lemma A.1 of Gwynne–Miller–Sheffield for the circle-average embedding of the `0`-quantum cone**
(arXiv:1705.11161, `notes/refs/1705.11161.txt` lines 1952-1956; proof in Appendix A, lines 1966-2100; identification
of the Lean field with the circle-average embedding).
It remains a named input of the theorems that use it; its proof from Lemma A.4 of arXiv:1705.11161
(`ZeroConeLemmaA4`) is not yet in Lean.

Let `X₀'` be a whole-plane GFF and `b`, `b'` standard Brownian motions, with `X₀'` independent of `(b, b')` and `b`
independent of `b'`, and let `h = coneField X₀' (coneRadial γ 0 b b')` be the circle-average embedding of the
`0`-quantum cone that they define (`zeroConeFieldOf`). Every bounded, non-negative, measurable functional `F` of `h`
which is almost surely invariant under all the coordinate changes `h ↦ h(C · + z) + Q log C`, `C > 0`, `z ∈ ℂ`
(A.1), is almost surely equal to a deterministic constant. -/
def ZeroConeCircleAverageLemmaA1 (γ : ℝ) (_hγ : γ ∈ Ioo (0 : ℝ) 2) : Prop :=
  ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') (X₀' : Ω' → Field) (b b' : ℝ≥0 → Ω' → ℝ),
    IsProbabilityMeasure P' → LQGMetric.IsWholePlaneGFF X₀' P' → IsBrownianReal b P' → IsBrownianReal b' P' →
    IndepFun X₀' (fun ω => ((fun t => b t ω), (fun t => b' t ω))) P' →
    IndepFun (fun ω t => b t ω) (fun ω t => b' t ω) P' →
    ∀ F : Field → ℝ, Measurable F → (∃ M : ℝ, ∀ h, F h ≤ M) → (∀ h, 0 ≤ F h) →
      (∀ᵐ ω ∂P', ∀ C : ℝ, 0 < C → ∀ z : ℂ,
        F (lqgSimilarityField γ C z (zeroConeFieldOf γ X₀' b b' ω)) = F (zeroConeFieldOf γ X₀' b b' ω)) →
      ∃ c : ℝ, ∀ᵐ ω ∂P', F (zeroConeFieldOf γ X₀' b b' ω) = c

/-! ### The two clauses of `ZeroConeLemmaA1Pos` -/

section Coupling

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- **The curve map at the normalized dilation by `2`.** Almost surely the curve map `Φ` of the coupling sends the
array of `(hIG₀, U)` to `ηL` and its normalized dilation by `2` to `affineReroot 0 2 0 ηL`. -/
theorem exists_igMap_igDilationStep_two
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    ∃ Φ : (ℝ → ℂ → ℝ) → C(ℝ, ℂ), Measurable Φ ∧
      (∀ᵐ ω ∂P, Φ (Function.curry (igPosCircleProcess (hIG₀ ω) (U ω))) = ηL ω) ∧
      ∀ᵐ ω ∂P, Φ (Function.curry (igDilationStep γ 2 (igPosCircleProcess (hIG₀ ω) (U ω)))) =
        affineReroot 0 2 0 (ηL ω) := by
  obtain ⟨Φ, hΦm, hign, hrep, hcov, -⟩ := D.igMap
  have htr : ∀ᵐ ω ∂P, Tendsto (ηL ω) (cocompact ℝ) (cocompact ℂ) :=
    D.spaceFilling.mono fun ω hω => hω.2.1
  have hwit := Sec1.igMap_scale_normalized_identity P γ
    (fun ω ρ w => LQGMetric.circleAvg (hIG₀ ω) ρ w + U ω) ηL Φ hrep hcov htr 2 two_pos
    (fun ω (r : ℝ) (w : ℂ) => LQGMetric.circleAvg (hIG₀ ω) (2 * r) (((2 : ℝ) : ℂ) * w))
    (fun ω => LQGMetric.circleAvg (hIG₀ ω) 2 0) U (fun ω r w => rfl)
  refine ⟨Φ, hΦm, ?_, ?_⟩
  · filter_upwards [hrep] with ω hω
    refine (hign _ _ ?_).trans hω.symm
    intro ρ hρ
    exact curry_igPosCircleProcess_of_pos (hIG₀ ω) (U ω) hρ
  · filter_upwards [hwit] with ω hω
    refine (hign _ _ ?_).trans hω
    intro ρ hρ
    exact curry_igDilationStep_two_of_pos γ (hIG₀ ω) (U ω) hρ

/-- **Dilation ergodicity of whole-plane space-filling SLE** (the curve form of Remark A.2 of arXiv:1705.11161 used
at lines 1188-1193; `notes/fp-gaps/CODEX-MQ-sbl-17.md`, lines 40-47). For a mating-of-trees coupling with
`γ ∈ (0, 2)`, a measurable functional `g` of the curve with `g(affineReroot 0 2 0 ηL) = g(ηL)` almost surely is almost
surely constant. -/
theorem ae_eq_const_of_affineReroot_two_invariant
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (hmix : IGFieldDilationMixing γ hγ) {g : C(ℝ, ℂ) → ℝ} (hg : Measurable g)
    (hinv : ∀ᵐ ω ∂P, g (affineReroot 0 2 0 (ηL ω)) = g (ηL ω)) :
    ∃ c : ℝ, ∀ᵐ ω ∂P, g (ηL ω) = c := by
  have hP : IsProbabilityMeasure P := D.isProbabilityMeasure
  obtain ⟨hh, hUlaw, hind⟩ := D.igField
  have hUae : AEMeasurable U P := aemeasurable_of_map_eq_igUniform hUlaw
  have hKp : AEMeasurable (fun ω => igPosCircleProcess (hIG₀ ω) (U ω)) P :=
    aemeasurable_igPosCircleProcess hh.1.measurable hUae
  obtain ⟨Φ, hΦm, h1, h2⟩ := exists_igMap_igDilationStep_two D
  have hcurry : Measurable (Function.curry : (ℝ × ℂ → ℝ) → ℝ → ℂ → ℝ) :=
    measurable_pi_iff.2 fun r => measurable_pi_iff.2 fun w => measurable_pi_apply (r, w)
  have hGm : Measurable fun f : ℝ × ℂ → ℝ => g (Φ (Function.curry f)) := by
    simpa only [Function.comp_def] using hg.comp (hΦm.comp hcurry)
  have h3 : ∀ᵐ ω ∂P, g (Φ (Function.curry (igDilationStep γ 2 (igPosCircleProcess (hIG₀ ω) (U ω))))) =
      g (Φ (Function.curry (igPosCircleProcess (hIG₀ ω) (U ω)))) := by
    filter_upwards [h1, h2, hinv] with ω h1ω h2ω hiω
    exact (congrArg g h2ω).trans (hiω.trans (congrArg g h1ω).symm)
  have hμP : IsProbabilityMeasure (P.map fun ω => igPosCircleProcess (hIG₀ ω) (U ω)) :=
    (Measure.isProbabilityMeasure_map_iff hKp).2 inferInstance
  have hT := measurePreserving_igDilationStep hγ (two_pos : (0 : ℝ) < 2) hh hUlaw hind
  have hmixT := hmix P hIG₀ U hh hUlaw hind
  have hinvμ : (fun f : ℝ × ℂ → ℝ => g (Φ (Function.curry f))) ∘ igDilationStep γ 2
      =ᵐ[P.map fun ω => igPosCircleProcess (hIG₀ ω) (U ω)] fun f => g (Φ (Function.curry f)) :=
    (ae_map_iff hKp (measurableSet_eq_fun (hGm.comp hT.measurable) hGm)).2 h3
  obtain ⟨c, hc⟩ := exists_ae_eq_const_of_mixing hT hmixT hGm hinvμ
  refine ⟨c, ?_⟩
  filter_upwards [ae_of_ae_map hKp hc, h1] with ω hω h1ω
  exact (congrArg g h1ω.symm).trans hω

/-- **`ZeroConeLemmaA1Pos` from Lemma A.1 for the circle-average zero cone and the dilation mixing of the
whole-plane GFF modulo `2πχ`.** The first clause is `ZeroConeCircleAverageLemmaA1` at the zero-cone data
`(X₀, B₀, B₀')` of the coupling; the second clause follows from the invariance at the single pair `(C, z) = (2, 0)`
(`ae_eq_const_of_affineReroot_two_invariant`). -/
theorem zeroConeLemmaA1Pos (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (hA1 : ZeroConeCircleAverageLemmaA1 γ hγ)
    (hmix : IGFieldDilationMixing γ hγ) : ZeroConeLemmaA1Pos D hγ := by
  unfold ZeroConeLemmaA1Pos
  refine ⟨fun F hF hM h0 hinv => ?_, fun g hg _ _ hinv => ?_⟩
  · exact hA1 P X₀ B₀ B₀' D.isProbabilityMeasure D.gff₀ D.bm_B₀ D.bm_B₀' D.indep_cone₀.1
      D.indep_cone₀.2 F hF hM h0 hinv
  · exact ae_eq_const_of_affineReroot_two_invariant D hγ hmix hg (hinv 2 two_pos 0)

end Coupling

end MatedCRT
