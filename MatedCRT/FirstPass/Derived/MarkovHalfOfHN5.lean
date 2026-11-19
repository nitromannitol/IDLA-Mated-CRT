import MatedCRT.FirstPass.Derived.AnnealedWalksJointConvergence
import MatedCRT.FirstPass.Derived.WalkPositionSupNorm
import MatedCRT.FirstPass.Derived.MarkovStepPathLawFamily
import MatedCRT.FirstPass.Derived.AnnealedWalkLawInterpClosenessAtPoint
import MatedCRT.FirstPass.Derived.AnnealedWalkLawInterpClosenessInMeasure
import MatedCRT.FirstPass.Derived.StartVertexAtPoint
import MatedCRT.FirstPass.Derived.MaxCellDiamTendsto
import MatedCRT.FirstPass.Derived.InterpolatedLawAssembly
import MatedCRT.FirstPass.Derived.InterpolatedLawWiring
import MatedCRT.FirstPass.Derived.LBMReversibilityOfLimit
import LatticeProb.Prob.TightnessOfContinuousFunctional

/-!
# The Markov property of the subsequential limits of the interpolated walk laws

The Markov half of Berestycki–Gwynne (2020), Lemma 7.4: if the interpolated quenched walk laws `P̃^{ε_n}`
converge in law (as random elements of the space of continuous families of path laws) to `ν₂`, then for every
`(z₀, t)` the limit family `s` has the Markov property at `(z₀, t)` for `ν₂`-almost every `s`.

The proof chains the landed steps: the datum `D_n` (a measurable version of `P̃^{ε_n}`) converges in law
(by hypothesis); the quenched walk law from the random starting vertex is close in probability to
`P̃^{ε_n}_{z₀}` (equicontinuity in law, `hEqLaw`, and cell diameters); hence the pair (datum, walk) converges in
law to `ν₂ ⊗ₘ (s ↦ s z₀)`; this gives the tightness of the walk position; and the quenched walk law at the
lattice time `⌊m_{ε_n} t⌋ / m_{ε_n}` is close to the datum evaluated at the position of the walk.  The
hypotheses `hEqLaw` and `m_{ε_n} → ∞` are the conclusions of the uniform-start invariance principle, kept explicit.

* `ae_markovAt_of_tendsto_law_interpWalkLaw`: the Markov property at a fixed `(z₀, t)`.
-/

set_option autoImplicit false

namespace MatedCRT.FirstPass.Derived

open MeasureTheory ProbabilityTheory Filter Topology Set Metric LatticeProb Preorder
open MarkovProcess (ContinuousPath)
open scoped NNReal ENNReal BoundedContinuousFunction

attribute [local instance] LatticeProb.dUnifMetricSpace

variable {Ω : Type} [MeasurableSpace Ω]

/-- A property holding almost surely for the environment holds almost surely for the environment coordinate
`(p n).1` of the annealed product space. -/
theorem ae_annealedWalksAt_of_ae {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {S : MatedCRTEnv Ω}
    (hS : S.IsValid 𝒮 γ) [IsProbabilityMeasure S.P] (ε : ℕ → ℝ) {k : ℕ → Ω → ℤ}
    (hk : ∀ n, Measurable (k n)) (n : ℕ) {P : Ω → Prop} (h : ∀ᵐ ω ∂S.P, P ω) :
    ∀ᵐ p ∂annealedWalksAt hS ε hk, P (p n).1 := by
  have hfm : Measurable fun p : ℕ → Ω × (ℕ → ℤ) => (p n).1 := measurable_fst.comp (measurable_pi_apply n)
  refine ae_of_ae_map hfm.aemeasurable ?_
  rwa [annealedWalksAt_map_fst hS ε hk n]

/-- The lattice time `⌊m t⌋ / m` as a nonnegative real. -/
theorem toNNReal_floor_div_eq_latticeTime {m : ℝ} (hm : 0 < m) (t : ℝ≥0) :
    ((⌊m * t⌋₊ : ℕ) / m : ℝ).toNNReal = latticeTime m t := by
  apply NNReal.coe_injective
  rw [Real.coe_toNNReal _ (div_nonneg (Nat.cast_nonneg _) hm.le)]
  simp [latticeTime, NNReal.coe_div, Real.coe_toNNReal _ hm.le]

/-- **The Markov property of a subsequential limit of the interpolated walk laws at a fixed `(z₀, t)`**
(BG20 Lemma 7.4, Markov part).  If `P̃^{ε_n} = interpWalkLaw S η' ε_n` converges in law to `ν₂`, the quenched
walk laws are equicontinuous in law (`hEqLaw`) and `m_{ε_n} → ∞`, then `ν₂`-almost every `s` has the Markov
property at `(z₀, t)`. -/
theorem ae_markovAt_of_tendsto_law_interpWalkLaw {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {S : MatedCRTEnv Ω}
    (hS : S.IsValid 𝒮 γ) {η' : Ω → C(ℝ, ℂ)} (hη' : Measurable η')
    (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) {ε : ℕ → ℝ} (hε0 : ∀ n, 0 < ε n) (hε : Tendsto ε atTop (𝓝 0))
    (hEqLaw : ∀ R a : ℝ, 0 < a → ∃ δ > 0, ∀ᶠ n in atTop,
      S.P {ω | ENNReal.ofReal a < walkLawModulus S η' (ε n) R δ ω} ≤ ENNReal.ofReal a)
    (hmpos : ∀ n, 0 < S.mε (ε n)) (hmε : Tendsto (fun n => S.mε (ε n)) atTop atTop)
    {ν₂ : Measure PathLawFamily} [IsProbabilityMeasure ν₂]
    (hlaw : ∀ f : PathLawFamily →ᵇ ℝ,
      Tendsto (fun n => ∫ ω, f (interpWalkLaw S η' (ε n) ω) ∂S.P) atTop (𝓝 (∫ P, f P ∂ν₂)))
    (z₀ : ℂ) (t : ℝ≥0) : ∀ᵐ s ∂ν₂, MarkovAt (⇑(s : PathLawFamily)) z₀ t := by
  have := hS.isProbabilityMeasure
  let : PseudoMetricSpace PathLawFamily := TopologicalSpace.pseudoMetrizableSpacePseudoMetric PathLawFamily
  let : MeasurableSpace (LevyProkhorov (ProbabilityMeasure C(ℝ≥0, ℂ))) := borel _
  have : BorelSpace (LevyProkhorov (ProbabilityMeasure C(ℝ≥0, ℂ))) := ⟨rfl⟩
  -- a measurable version of the datum
  have haem := fun n => aemeasurable_interpWalkLaw hS hη' hae (hε0 n)
  let d' : ℕ → Ω → PathLawFamily := fun n => (haem n).mk (interpWalkLaw S η' (ε n))
  have hd'm : ∀ n, Measurable (d' n) := fun n => (haem n).measurable_mk
  have hd'ae : ∀ n, ∀ᵐ ω ∂S.P, interpWalkLaw S η' (ε n) ω = d' n ω := fun n => (haem n).ae_eq_mk
  have hlawD : ∀ f : PathLawFamily →ᵇ ℝ,
      Tendsto (fun n => ∫ ω, f (d' n ω) ∂S.P) atTop (𝓝 (∫ s, f s ∂ν₂)) := by
    intro f
    refine (hlaw f).congr fun n => integral_congr_ae ?_
    filter_upwards [hd'ae n] with ω h
    rw [h]
  -- the random starting vertices
  obtain ⟨k, hk, -, hz₀⟩ := MatedCRTEnv.IsValid.exists_measurable_startVertex_mem_cell hS hae hε0 z₀
  have hv : ∀ n, Measurable fun ω => vertexPoint (ε n) (⇑(η' ω)) := fun n =>
    measurable_vertexPoint_curve hη' (ε n)
  have hm : ∀ n, 0 < (fun n => S.mε (ε n)) n := hmpos
  -- the kernel `s ↦ s z₀`
  have hκm : Measurable fun s : PathLawFamily => (s z₀ : ProbabilityMeasure C(ℝ≥0, ℂ)) :=
    (continuous_eval_const z₀).measurable
  let κ₀ : Kernel PathLawFamily C(ℝ≥0, ℂ) :=
    { toFun := fun s => ((s z₀ : ProbabilityMeasure C(ℝ≥0, ℂ)) : Measure C(ℝ≥0, ℂ))
      measurable' := measurable_subtype_coe.comp hκm }
  have : IsMarkovKernel κ₀ := ⟨fun s => (s z₀).prop⟩
  -- the quenched walk law from the random start is close to the datum at `z₀`
  have hstart := tendstoInMeasure_levyProkhorovDist_annealedWalksAt_walkPathLaw_interpWalkLaw_start hS hae
    hε0 hε hEqLaw (hdiam_of_isValid hS hae hε) hk hz₀
  have hcloseE3 : TendstoInMeasure (annealedWalksAt hS ε hk)
      (fun n (p : ℕ → Ω × (ℕ → ℤ)) => levyProkhorovDist
        (walkPathLaw S (fun ω => vertexPoint (ε n) (⇑(η' ω))) (hm n).le (ε n) (k n (p n).1) (p n).1 :
          Measure C(ℝ≥0, ℂ))
        ((fun s : PathLawFamily => s z₀) (d' n (p n).1) : Measure C(ℝ≥0, ℂ))) atTop 0 := by
    refine hstart.congr' (Filter.Eventually.of_forall fun n => ?_) (ae_of_all _ fun _ => rfl)
    filter_upwards [ae_annealedWalksAt_of_ae hS ε hk n (hd'ae n)] with p hp
    simp only [hp]
  have hE3 := tendsto_integral_annealedWalksAt_of_levyProkhorov_close (S₀ := PathLawFamily) hS ε hk hv hm
    hd'm hlawD (π := fun s : PathLawFamily => s z₀) (continuous_eval_const z₀) hcloseE3
    (κ₀ := κ₀) (fun s => rfl)
  -- the lattice times
  let j : ℕ → ℕ := fun n => ⌊S.mε (ε n) * t⌋₊
  have hjt : ∀ n, (((j n : ℕ) / S.mε (ε n) : ℝ).toNNReal) = latticeTime (S.mε (ε n)) t := fun n =>
    toNNReal_floor_div_eq_latticeTime (hmpos n) t
  have hs : Tendsto (fun n => (((j n : ℕ) / S.mε (ε n) : ℝ).toNNReal)) atTop (𝓝 t) := by
    have := tendsto_latticeTime (m := fun n => S.mε (ε n)) (c := fun n => (S.mε (ε n))⁻¹)
      (Eventually.of_forall fun n => ⟨hmpos n, le_rfl⟩) hmε.inv_tendsto_atTop t
    exact this.congr fun n => (hjt n).symm
  have hsT : ∀ n, (((j n : ℕ) / S.mε (ε n) : ℝ).toNNReal) ≤ t := fun n => by
    rw [hjt n]
    exact latticeTime_le (S.mε_nonneg (ε n)) t
  -- the tightness of the walk position
  have hfst : ∀ n, Measurable fun p : ℕ → Ω × (ℕ → ℤ) => (p n).1 := fun n =>
    measurable_fst.comp (measurable_pi_apply n)
  have hXm : ∀ n, Measurable fun p : ℕ → Ω × (ℕ → ℤ) =>
      (d' n (p n).1, interpPathCM (vertexPoint (ε n) (⇑(η' (p n).1))) (hm n).le (p n).2) := fun n =>
    ((hd'm n).comp (hfst n)).prodMk
      ((measurable_interpPathCM_uncurry (hm n).le).comp
        (((hv n).comp (hfst n)).prodMk (measurable_snd.comp (measurable_pi_apply n))))
  have htight : ∀ r : ℝ, 0 < r → ∃ R : ℝ, ∀ᶠ n in atTop,
      annealedWalksAt hS ε hk {p : ℕ → Ω × (ℕ → ℤ) |
        R < ‖vertexPoint (ε n) (⇑(η' (p n).1)) (lastState (j n) (frestrictLe (j n) (p n).2))‖} ≤
        ENNReal.ofReal r := by
    intro r hr
    obtain ⟨R, hR⟩ := exists_forall_eventually_measure_lt_le_of_tendsto_integral
      (μ := fun _ => annealedWalksAt hS ε hk)
      (X := fun n (p : ℕ → Ω × (ℕ → ℤ)) =>
        (d' n (p n).1, interpPathCM (vertexPoint (ε n) (⇑(η' (p n).1))) (hm n).le (p n).2))
      (fun n => (hXm n).aemeasurable) (ν := ν₂ ⊗ₘ κ₀) hE3
      (Φ := fun q : PathLawFamily × C(ℝ≥0, ℂ) => supNormUpTo t q.2)
      ((continuous_supNormUpTo t).comp continuous_snd) hr
    refine ⟨R, hR.mono fun n hn => le_trans (measure_mono fun p hp => ?_) hn⟩
    exact lt_of_lt_of_le hp (norm_vertex_le_supNormUpTo_interpPathCM
      (vertexPoint (ε n) (⇑(η' (p n).1))) (hm n) (p n).2 (j n) (hsT n))
  -- the quenched walk law at the walk position against the datum
  have hE2 := tendstoInMeasure_levyProkhorovDist_annealedWalksAt_hclose hS hae hε0 hε hEqLaw
    (hdiam_of_isValid hS hae hε) hk j htight (S₀ := PathLawFamily) (d := fun n ω => interpWalkLaw S η' (ε n) ω)
    (K := fun s => s) (fun _ _ _ => rfl) (v := fun n ω => vertexPoint (ε n) (⇑(η' ω)))
    rfl (m := fun n => S.mε (ε n)) hm rfl
  have hclose : TendstoInMeasure (annealedWalksAt hS ε hk)
      (fun n (p : ℕ → Ω × (ℕ → ℤ)) => levyProkhorovDist
        (walkPathLaw S (fun ω => vertexPoint (ε n) (⇑(η' ω))) (hm n).le (ε n)
          (lastState (j n) (frestrictLe (j n) (p n).2)) (p n).1 : Measure C(ℝ≥0, ℂ))
        (d' n (p n).1 (interpPathCM (vertexPoint (ε n) (⇑(η' (p n).1))) (hm n).le (p n).2
          ((j n / S.mε (ε n) : ℝ).toNNReal)) : Measure C(ℝ≥0, ℂ))) atTop 0 := by
    refine hE2.congr' (Filter.Eventually.of_forall fun n => ?_) (ae_of_all _ fun _ => rfl)
    filter_upwards [ae_annealedWalksAt_of_ae hS ε hk n (hd'ae n)] with p hp
    simp only [hp]
  exact ae_markovAt_pathLawFamily_of_walk_markov_step_at hS ε hk (v := fun n ω => vertexPoint (ε n) (⇑(η' ω)))
    hv hm j hd'm (ν := ν₂ ⊗ₘ κ₀) hE3 hs hsT hclose (νD := ν₂) (κ₀ := κ₀) rfl (fun s => rfl)

end MatedCRT.FirstPass.Derived
