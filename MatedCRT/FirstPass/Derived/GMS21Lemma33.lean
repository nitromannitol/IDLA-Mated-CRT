import MatedCRT.FirstPass.Derived.GMS21LocalCellConfiguration
import LatticeProb.Prob.CountablePhaseImageLimit
import LatticeProb.Prob.CountablePhaseTransport

/-!
# Lemma 3.3 of Gwynne–Miller–Sheffield: cell configurations from a common reconstruction

Gwynne–Miller–Sheffield (arXiv:1705.11161), Lemma 3.3 and its proof (p. 24-25). Let `U ⊂ U'` be open sets, let `η`
be a space-filling curve sampled independently of the random measures `μ₁`, `μ₂`, let `σ_{k-1} < τ_k` be the
successive exits from `U'` and entrances in `U` of `η`, `A_k = η([σ_{k-1}, τ_k])` for `k = 1, …, K`, and
`A = ⋃_k A_k`. The proof of Lemma 3.3 rests on three facts:

* on an event of probability tending to one, the cell configuration at mesh `1/n` is a function of `η`,
  `μ_i|U' \ A` and the residues `s^n_{k,i} ∈ [0, 1/n)` of the masses `μ_i(A_k)` modulo `n⁻¹ ℤ + n⁻¹ θ_i`, through a
  reconstruction map which is the same for `i = 1, 2`;
* the laws of `(η, μ₁|U' \ A)` and `(η, μ₂|U' \ A)` are mutually absolutely continuous;
* given the outer data, the conditional law of `(μ_i(A_1), …, μ_i(A_K))` is absolutely continuous with respect to
  Lebesgue measure, so that the conditional law of the residues becomes uniform on `[0, 1/n]^K` as `n → ∞`.

This file proves the conclusion of Lemma 3.3, uniform mutual absolute continuity as `n → ∞` (Definition 3.2), from
these three facts for general random data. Each side is described by a marked phase vector
`⟨K, ((Y, θ), M)⟩ : CountablePhaseSpace (Y × ℝ)`: the number `K` of the sets `A_k`, the outer data `Y`, the phase
`θ` and the masses `M = (μ_i(A_k))_k`. The scaled residues `n s^n_{k,i}` are the fractional parts
`fract(n M_k - θ)` (`countablePhaseMap n markPhase`); the reconstruction map reads the outer data and the residues
(`forgetPhase` removes the phase from the mark). The asymptotic uniformity of the residues is
`LatticeProb.tendsto_tvDist_countablePhaseMap_image`; laws are compared in total variation
(`QuantumZipper.TV.tvDist`).

## Main statements

* `IsPhaseReconstruction`: the three facts of the proof of Lemma 3.3 for two sequences of configurations.
* `uniformlyMutuallyAbsolutelyContinuous_of_isPhaseReconstruction`: Lemma 3.3 from these facts.
* `localConfigUniformlyMutuallyAbsolutelyContinuous_of_isPhaseReconstruction`: the same for the local configurations
  near the annuli `B_R(0) \ closedBall 0 α` (`LocalConfigUniformlyMutuallyAbsolutelyContinuous`).
* `IsApproxPhaseReconstruction`: the same facts with cutoffs `m`, the reconstruction holding on events
  `countOuter Z ∈ G m` of the outer data of probability at least `1 - 1/(m+1)`; the phase in the mark may be zero or
  an independent uniform phase.
* `uniformlyMutuallyAbsolutelyContinuous_of_isApproxPhaseReconstruction` and
  `localConfigUniformlyMutuallyAbsolutelyContinuous_of_isApproxPhaseReconstruction`: the conclusion of Lemma 3.3
  from these facts.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace MatedCRT

open LatticeProb

/-! ### Uniform absolute continuity under images and small perturbations -/

section UniformAbsoluteContinuity

variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]

/-- **Images.** Uniform absolute continuity as `n → ∞` is preserved by measurable maps. -/
theorem UniformlyAbsolutelyContinuous.map_measurable {Ω' : ℕ → Type*} [∀ n, MeasurableSpace (Ω' n)]
    {P Q : ∀ n, Measure (Ω n)} (h : UniformlyAbsolutelyContinuous P Q) (f : ∀ n, Ω n → Ω' n)
    (hf : ∀ n, Measurable (f n)) :
    UniformlyAbsolutelyContinuous (fun n => (P n).map (f n)) (fun n => (Q n).map (f n)) := by
  intro p hp0 hp1
  obtain ⟨q, hq0, hq1, N, hN⟩ := h p hp0 hp1
  refine ⟨q, hq0, hq1, N, fun n hn E hE hQE => ?_⟩
  rw [Measure.map_apply (hf n) hE] at hQE ⊢
  exact hN n hn _ (hf n hE) hQE

/-- **Small perturbations in total variation.** If `{P' n}` is uniformly absolutely continuous as `n → ∞` with
respect to `{Q' n}`, and `P n`, `Q n` are at total variation distance tending to `0` from `P' n`, `Q' n`, then `{P n}`
is uniformly absolutely continuous as `n → ∞` with respect to `{Q n}`. -/
theorem UniformlyAbsolutelyContinuous.of_tendsto_tvDist {P P' Q Q' : ∀ n, Measure (Ω n)}
    (h : UniformlyAbsolutelyContinuous P' Q')
    (hP : Tendsto (fun n => QuantumZipper.TV.tvDist (P n) (P' n)) atTop (𝓝 0))
    (hQ : Tendsto (fun n => QuantumZipper.TV.tvDist (Q n) (Q' n)) atTop (𝓝 0)) :
    UniformlyAbsolutelyContinuous P Q := by
  intro p hp0 hp1
  obtain ⟨p', hpp', hp'1⟩ := exists_between hp1
  obtain ⟨q', hq'0, hq'1, N, hN⟩ := h p' (hp0.trans hpp') hp'1
  obtain ⟨q, hq'q, hq1⟩ := exists_between hq'1
  have hQe : ∀ᶠ n in atTop, QuantumZipper.TV.tvDist (Q n) (Q' n) < p' - p :=
    hQ.eventually (gt_mem_nhds (tsub_pos_of_lt hpp'))
  have hPe : ∀ᶠ n in atTop, QuantumZipper.TV.tvDist (P n) (P' n) < q - q' :=
    hP.eventually (gt_mem_nhds (tsub_pos_of_lt hq'q))
  obtain ⟨M, hM⟩ := eventually_atTop.1 ((hQe.and hPe).and (eventually_ge_atTop N))
  refine ⟨q, hq'0.trans hq'q, hq1, M, fun n hn E hE hQE => ?_⟩
  obtain ⟨⟨hQn, hPn⟩, hNn⟩ := hM n hn
  have h1 : Q' n E ≤ p' := by
    have hle := QuantumZipper.TV.le_tvDist' (μ := Q n) (ν := Q' n) hE
    calc Q' n E ≤ Q n E + QuantumZipper.TV.tvDist (Q n) (Q' n) := tsub_le_iff_left.1 hle
      _ ≤ p + (p' - p) := add_le_add hQE hQn.le
      _ = p' := add_tsub_cancel_of_le hpp'.le
  have h2 := hN n hNn E hE h1
  have hle := QuantumZipper.TV.le_tvDist (μ := P n) (ν := P' n) hE
  calc P n E ≤ P' n E + QuantumZipper.TV.tvDist (P n) (P' n) := tsub_le_iff_left.1 hle
    _ ≤ q' + (q - q') := add_le_add h2 hPn.le
    _ = q := add_tsub_cancel_of_le hq'q.le

end UniformAbsoluteContinuity

/-- **Laws of two random variables which agree outside a small event.** The total variation distance of the laws of
`f` and `g` is at most the (outer) probability that `f ≠ g`. -/
theorem tvDist_map_le_measure_ne {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S] (P : Measure Ω)
    {f g : Ω → S} (hf : AEMeasurable f P) (hg : AEMeasurable g P) :
    QuantumZipper.TV.tvDist (P.map f) (P.map g) ≤ P {ω | f ω ≠ g ω} := by
  have key : ∀ u v : Ω → S, AEMeasurable u P → AEMeasurable v P → ∀ s : Set S, MeasurableSet s →
      P.map u s - P.map v s ≤ P {ω | u ω ≠ v ω} := by
    intro u v hu hv s hs
    rw [Measure.map_apply_of_aemeasurable hu hs, Measure.map_apply_of_aemeasurable hv hs]
    refine tsub_le_iff_left.2 ?_
    calc P (u ⁻¹' s) ≤ P (v ⁻¹' s ∪ {ω | u ω ≠ v ω}) := by
          refine measure_mono fun ω hω => ?_
          by_cases huv : u ω = v ω
          · left
            show v ω ∈ s
            rw [← huv]
            exact hω
          · exact Or.inr huv
      _ ≤ P (v ⁻¹' s) + P {ω | u ω ≠ v ω} := measure_union_le _ _
  have hset : {ω | g ω ≠ f ω} = {ω | f ω ≠ g ω} := by
    ext ω
    exact ne_comm
  unfold QuantumZipper.TV.tvDist
  refine iSup₂_le fun s hs => sup_le (key f g hf hg s hs) ?_
  have h2 := key g f hg hf s hs
  rwa [hset] at h2

/-! ### Marked phase vectors -/

section Marks

variable {Y : Type*}

/-- The phase of the mark `(y, θ)` of a marked phase vector, the same for every coordinate: the residues of the
coordinates `M_k` are `fract(n M_k - θ)`. -/
def markPhase (k : ℕ) (e : Y × ℝ) : Fin k → ℝ := fun _ => e.2

/-- The marked phase vector with the phase removed from its mark. -/
def forgetPhase (x : CountablePhaseSpace (Y × ℝ)) : CountablePhaseSpace Y :=
  ⟨x.1, (x.2.1.1, x.2.2)⟩

/-- The number of coordinates and the outer data of a marked phase vector. -/
def countOuter (x : CountablePhaseSpace (Y × ℝ)) : ℕ × Y :=
  (x.1, x.2.1.1)

/-- The marked phase vector `⟨K, (e, (M_0, …, M_{K-1}))⟩`. -/
def mkPhaseVector {E : Type*} (K : ℕ) (e : E) (M : ℕ → ℝ) : CountablePhaseSpace E :=
  ⟨K, (e, fun j : Fin K => M j)⟩

end Marks

section MarksMeasurable

variable {Y : Type*} [MeasurableSpace Y]

/-- A map on marked phase vectors is measurable as soon as it is measurable on each coordinate count. -/
theorem measurable_of_countablePhase {E β : Type*} [MeasurableSpace E] [MeasurableSpace β]
    {f : CountablePhaseSpace E → β} (hf : ∀ k : ℕ, Measurable fun p : E × (Fin k → ℝ) => f ⟨k, p⟩) :
    Measurable f := by
  intro s hs
  change MeasurableSet[⨅ i : ℕ, (inferInstance : MeasurableSpace (E × (Fin i → ℝ))).map
    (Sigma.mk i)] (f ⁻¹' s)
  rw [MeasurableSpace.measurableSet_iInf]
  intro i
  exact hf i hs

theorem measurable_sigmaMk_countablePhase {E : Type*} [MeasurableSpace E] (k : ℕ) :
    Measurable (@Sigma.mk ℕ (fun j => E × (Fin j → ℝ)) k) :=
  (measurableEmbedding_countablePhase_inject k).measurable

theorem measurable_markPhase (k : ℕ) : Measurable (markPhase (Y := Y) k) :=
  measurable_pi_iff.2 fun _ => measurable_snd

theorem measurable_forgetPhase : Measurable (forgetPhase (Y := Y)) :=
  measurable_of_countablePhase fun k =>
    (measurable_sigmaMk_countablePhase k).comp
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd)

theorem measurable_countOuter : Measurable (countOuter (Y := Y)) :=
  measurable_of_countablePhase fun _ =>
    measurable_const.prodMk (measurable_fst.comp measurable_fst)

/-- A random marked phase vector with measurable count, mark and coordinates is measurable. -/
theorem measurable_mkPhaseVector {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E] {K : Ω → ℕ}
    {e : Ω → E} {M : Ω → ℕ → ℝ} (hK : Measurable K) (he : Measurable e) (hM : Measurable M) :
    Measurable fun ω => mkPhaseVector (K ω) (e ω) (M ω) := by
  intro s hs
  have hs' : ∀ n : ℕ, MeasurableSet ((@Sigma.mk ℕ (fun j => E × (Fin j → ℝ)) n) ⁻¹' s) :=
    fun n => measurable_sigmaMk_countablePhase n hs
  have heq : (fun ω => mkPhaseVector (K ω) (e ω) (M ω)) ⁻¹' s =
      ⋃ n : ℕ, K ⁻¹' {n} ∩ (fun ω => (e ω, fun j : Fin n => M ω j)) ⁻¹'
        ((@Sigma.mk ℕ (fun j => E × (Fin j → ℝ)) n) ⁻¹' s) := by
    ext ω
    simp only [mem_preimage, mem_iUnion, mem_inter_iff, mem_singleton_iff]
    constructor
    · intro hω
      exact ⟨K ω, rfl, hω⟩
    · rintro ⟨n, hn, hω⟩
      subst hn
      exact hω
  rw [heq]
  refine MeasurableSet.iUnion fun n => (hK (measurableSet_singleton n)).inter ?_
  have hm : Measurable fun ω => (e ω, fun j : Fin n => M ω j) :=
    he.prodMk (measurable_pi_iff.2 fun j => (measurable_pi_apply (j : ℕ)).comp hM)
  exact hm (hs' n)

/-- The resampled law of a marked phase vector is a probability measure. -/
theorem isProbabilityMeasure_uniformized {E : Type*} [MeasurableSpace E]
    (μ : Measure (CountablePhaseSpace E)) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (countableUniformPhaseKernel ∘ₘ μ) := by
  constructor
  rw [Measure.bind_apply MeasurableSet.univ (Kernel.aemeasurable _)]
  simp only [measure_univ, lintegral_const, one_mul]

/-- The uniform resampling of the coordinates, followed by the removal of the phase, depends only on the number of
coordinates and the outer data. -/
theorem countableUniformPhaseKernel_forgetPhase_apply {s : Set (CountablePhaseSpace Y)}
    (hs : MeasurableSet s) (x : CountablePhaseSpace (Y × ℝ)) :
    countableUniformPhaseKernel x (forgetPhase ⁻¹' s) =
      unitCubeMeasure (Fin x.1) {u | (⟨x.1, (x.2.1.1, u)⟩ : CountablePhaseSpace Y) ∈ s} := by
  obtain ⟨k, e, v⟩ := x
  have hS : MeasurableSet ((@Sigma.mk ℕ (fun j => (Y × ℝ) × (Fin j → ℝ)) k) ⁻¹'
      (forgetPhase ⁻¹' s)) :=
    measurable_sigmaMk_countablePhase k (measurable_forgetPhase hs)
  rw [countableUniformPhaseKernel_apply, Measure.map_apply (measurable_sigmaMk_countablePhase k)
    (measurable_forgetPhase hs)]
  unfold markResamplingKernel
  rw [Kernel.prod_apply, Kernel.deterministic_apply, Kernel.const_apply, Measure.dirac_prod,
    Measure.map_apply measurable_prodMk_left hS]
  rfl

/-- **The resampled laws inherit the absolute continuity of the outer data.** If the law of the number of
coordinates and the outer data under `μ` is absolutely continuous with respect to that under `ν`, the same holds for
the laws obtained by resampling the coordinates uniformly and removing the phase. -/
theorem absolutelyContinuous_uniformized_forgetPhase {μ ν : Measure (CountablePhaseSpace (Y × ℝ))}
    (h : μ.map countOuter ≪ ν.map countOuter) :
    (countableUniformPhaseKernel ∘ₘ μ).map forgetPhase ≪
      (countableUniformPhaseKernel ∘ₘ ν).map forgetPhase := by
  refine Measure.AbsolutelyContinuous.mk fun s hs hνs => ?_
  have hg : Measurable fun z : ℕ × Y =>
      unitCubeMeasure (Fin z.1) {u | (⟨z.1, (z.2, u)⟩ : CountablePhaseSpace Y) ∈ s} := by
    refine measurable_from_prod_countable_right fun k => ?_
    have h1 : Measurable fun y : Y => unitCubeMeasure (Fin k)
        (Prod.mk y ⁻¹' ((@Sigma.mk ℕ (fun j => Y × (Fin j → ℝ)) k) ⁻¹' s)) :=
      measurable_measure_prodMk_left (measurable_sigmaMk_countablePhase k hs)
    exact h1
  have key : ∀ ρ : Measure (CountablePhaseSpace (Y × ℝ)),
      (countableUniformPhaseKernel ∘ₘ ρ).map forgetPhase s =
        ∫⁻ z, unitCubeMeasure (Fin z.1) {u | (⟨z.1, (z.2, u)⟩ : CountablePhaseSpace Y) ∈ s}
          ∂(ρ.map countOuter) := by
    intro ρ
    rw [Measure.map_apply measurable_forgetPhase hs,
      Measure.bind_apply (measurable_forgetPhase hs) (Kernel.aemeasurable _),
      lintegral_map hg measurable_countOuter]
    refine lintegral_congr fun x => ?_
    exact countableUniformPhaseKernel_forgetPhase_apply hs x
  rw [key] at hνs ⊢
  rw [lintegral_eq_zero_iff hg] at hνs ⊢
  exact h.ae_le hνs

end MarksMeasurable

/-! ### Lemma 3.3 -/

section Lemma33

variable {Ω₁ Ω₂ Y S : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] [MeasurableSpace Y]
  [MeasurableSpace S]

/-- **One side of the proof of Lemma 3.3.** If the configuration `C n` agrees with the reconstruction `Ψ n` of the
outer data and the residues of the marked phase vector `Z` outside events of probability tending to `0`, and the
conditional law of the coordinates of `Z` given its mark is absolutely continuous with respect to Lebesgue measure,
then the law of `C n` is at total variation distance tending to `0` from the reconstruction of the law of `Z` with
coordinates resampled uniformly. -/
theorem tendsto_tvDist_map_phaseReconstruction {P : Measure Ω₁} [IsProbabilityMeasure P]
    {Z : Ω₁ → CountablePhaseSpace (Y × ℝ)} (hZ : AEMeasurable Z P) (Ψ : ℕ → CountablePhaseSpace Y → S)
    (hΨ : ∀ n, Measurable (Ψ n)) {C : ℕ → Ω₁ → S} (hC : ∀ n, AEMeasurable (C n) P)
    (hrec : Tendsto (fun n : ℕ =>
      P {ω | C n ω ≠ Ψ n (forgetPhase (countablePhaseMap (n : ℝ) markPhase (Z ω)))}) atTop (𝓝 0))
    (hac : ∀ k : ℕ,
      let ν := (P.map Z).comap (@Sigma.mk ℕ (fun j => (Y × ℝ) × (Fin j → ℝ)) k)
      ν ≪ (ν.map Prod.fst).prod (volume : Measure (Fin k → ℝ))) :
    Tendsto (fun n : ℕ => QuantumZipper.TV.tvDist (P.map (C n))
      (((countableUniformPhaseKernel ∘ₘ P.map Z).map forgetPhase).map (Ψ n))) atTop (𝓝 0) := by
  have hPZ : IsProbabilityMeasure (P.map Z) :=
    (Measure.isProbabilityMeasure_map_iff hZ).2 inferInstance
  have _hU : IsProbabilityMeasure (countableUniformPhaseKernel ∘ₘ P.map Z) :=
    isProbabilityMeasure_uniformized _
  have hθ : ∀ (_ : ℕ) (k : ℕ), Measurable (markPhase (Y := Y) k) := fun _ k => measurable_markPhase k
  have hph : ∀ n : ℕ, Measurable (countablePhaseMap (n : ℝ) (markPhase (Y := Y))) :=
    fun n => measurable_countablePhaseMap _ _ (hθ n)
  have hf : ∀ n, Measurable (Ψ n ∘ forgetPhase) := fun n => (hΨ n).comp measurable_forgetPhase
  have hB := tendsto_tvDist_countablePhaseMap_image (P.map Z) hac (fun n : ℕ => (n : ℝ))
    tendsto_natCast_atTop_atTop (fun _ => markPhase) hθ (fun n => Ψ n ∘ forgetPhase) hf
  have hD : ∀ n : ℕ, ((P.map Z).map (countablePhaseMap (n : ℝ) markPhase)).map (Ψ n ∘ forgetPhase) =
      P.map (fun ω => Ψ n (forgetPhase (countablePhaseMap (n : ℝ) markPhase (Z ω)))) := by
    intro n
    rw [Measure.map_map (hf n) (hph n),
      AEMeasurable.map_map_of_aemeasurable ((hf n).comp (hph n)).aemeasurable hZ]
    rfl
  have hR : ∀ n : ℕ, (countableUniformPhaseKernel ∘ₘ P.map Z).map (Ψ n ∘ forgetPhase) =
      ((countableUniformPhaseKernel ∘ₘ P.map Z).map forgetPhase).map (Ψ n) := by
    intro n
    rw [Measure.map_map (hΨ n) measurable_forgetPhase]
  have hB' : Tendsto (fun n : ℕ => QuantumZipper.TV.tvDist
      (P.map (fun ω => Ψ n (forgetPhase (countablePhaseMap (n : ℝ) markPhase (Z ω)))))
      (((countableUniformPhaseKernel ∘ₘ P.map Z).map forgetPhase).map (Ψ n))) atTop (𝓝 0) :=
    hB.congr fun n => by simp only [hD n, hR n]
  have hA : Tendsto (fun n : ℕ => QuantumZipper.TV.tvDist (P.map (C n))
      (P.map (fun ω => Ψ n (forgetPhase (countablePhaseMap (n : ℝ) markPhase (Z ω)))))) atTop
      (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hrec (fun _ => bot_le)
      fun n => ?_
    exact tvDist_map_le_measure_ne P (hC n) (((hf n).comp (hph n)).comp_aemeasurable hZ)
  have hsum := hA.add hB'
  rw [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ => bot_le)
    fun n => ?_
  exact QuantumZipper.TV.tvDist_triangle

/-- **The facts of the proof of Lemma 3.3** (Gwynne–Miller–Sheffield, arXiv:1705.11161, p. 24-25) for configurations
`C₁ n` under `P₁` and `C₂ n` under `P₂` at mesh `1/n`, described by the marked phase vectors
`Zᵢ = ⟨K, ((Y, θ), M)⟩` (number of the sets `A_k`, outer data, phase, masses `μ_i(A_k)`) and the reconstruction maps
`Ψ n`, the same for both sides. -/
structure IsPhaseReconstruction (P₁ : Measure Ω₁) (C₁ : ℕ → Ω₁ → S) (P₂ : Measure Ω₂) (C₂ : ℕ → Ω₂ → S)
    (Z₁ : Ω₁ → CountablePhaseSpace (Y × ℝ)) (Z₂ : Ω₂ → CountablePhaseSpace (Y × ℝ))
    (Ψ : ℕ → CountablePhaseSpace Y → S) : Prop where
  aemeasurable_mark_left : AEMeasurable Z₁ P₁
  aemeasurable_mark_right : AEMeasurable Z₂ P₂
  measurable_recon : ∀ n, Measurable (Ψ n)
  aemeasurable_left : ∀ n, AEMeasurable (C₁ n) P₁
  aemeasurable_right : ∀ n, AEMeasurable (C₂ n) P₂
  /-- The configuration is the reconstruction from the outer data and the residues on events of probability
  tending to one (p. 25 of the text). -/
  recon_left : Tendsto (fun n : ℕ =>
    P₁ {ω | C₁ n ω ≠ Ψ n (forgetPhase (countablePhaseMap (n : ℝ) markPhase (Z₁ ω)))}) atTop (𝓝 0)
  recon_right : Tendsto (fun n : ℕ =>
    P₂ {ω | C₂ n ω ≠ Ψ n (forgetPhase (countablePhaseMap (n : ℝ) markPhase (Z₂ ω)))}) atTop (𝓝 0)
  /-- Given the mark, the conditional law of the masses is absolutely continuous with respect to Lebesgue measure
  (p. 25). -/
  ac_left : ∀ k : ℕ,
    let ν := (P₁.map Z₁).comap (@Sigma.mk ℕ (fun j => (Y × ℝ) × (Fin j → ℝ)) k)
    ν ≪ (ν.map Prod.fst).prod (volume : Measure (Fin k → ℝ))
  ac_right : ∀ k : ℕ,
    let ν := (P₂.map Z₂).comap (@Sigma.mk ℕ (fun j => (Y × ℝ) × (Fin j → ℝ)) k)
    ν ≪ (ν.map Prod.fst).prod (volume : Measure (Fin k → ℝ))
  /-- The laws of the number of the sets `A_k` and the outer data are mutually absolutely continuous
  (p. 25). -/
  mark_left_right : (P₁.map Z₁).map countOuter ≪ (P₂.map Z₂).map countOuter
  mark_right_left : (P₂.map Z₂).map countOuter ≪ (P₁.map Z₁).map countOuter

/-- **Lemma 3.3 of Gwynne–Miller–Sheffield** (arXiv:1705.11161, p. 24): under the facts of its proof
(`IsPhaseReconstruction`), the laws of the configurations `C₁ n` and `C₂ n` are uniformly mutually absolutely
continuous as `n → ∞` (Definition 3.2). -/
theorem uniformlyMutuallyAbsolutelyContinuous_of_isPhaseReconstruction {P₁ : Measure Ω₁}
    {P₂ : Measure Ω₂} [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂] {C₁ : ℕ → Ω₁ → S}
    {C₂ : ℕ → Ω₂ → S} {Z₁ : Ω₁ → CountablePhaseSpace (Y × ℝ)} {Z₂ : Ω₂ → CountablePhaseSpace (Y × ℝ)}
    {Ψ : ℕ → CountablePhaseSpace Y → S} (h : IsPhaseReconstruction P₁ C₁ P₂ C₂ Z₁ Z₂ Ψ) :
    UniformlyMutuallyAbsolutelyContinuous (Ω := fun _ => S) (fun n => P₁.map (C₁ n))
      (fun n => P₂.map (C₂ n)) := by
  have hT₁ := tendsto_tvDist_map_phaseReconstruction h.aemeasurable_mark_left Ψ h.measurable_recon
    h.aemeasurable_left h.recon_left h.ac_left
  have hT₂ := tendsto_tvDist_map_phaseReconstruction (Ω₁ := Ω₂) h.aemeasurable_mark_right Ψ
    h.measurable_recon h.aemeasurable_right h.recon_right h.ac_right
  have hP₁Z : IsProbabilityMeasure (P₁.map Z₁) :=
    (Measure.isProbabilityMeasure_map_iff h.aemeasurable_mark_left).2 inferInstance
  have hP₂Z : IsProbabilityMeasure (P₂.map Z₂) :=
    (Measure.isProbabilityMeasure_map_iff h.aemeasurable_mark_right).2 inferInstance
  have hU₁ : IsProbabilityMeasure (countableUniformPhaseKernel ∘ₘ P₁.map Z₁) :=
    isProbabilityMeasure_uniformized _
  have hU₂ : IsProbabilityMeasure (countableUniformPhaseKernel ∘ₘ P₂.map Z₂) :=
    isProbabilityMeasure_uniformized _
  have hρ₁ : IsProbabilityMeasure ((countableUniformPhaseKernel ∘ₘ P₁.map Z₁).map forgetPhase) :=
    (Measure.isProbabilityMeasure_map_iff measurable_forgetPhase.aemeasurable).2 hU₁
  have hρ₂ : IsProbabilityMeasure ((countableUniformPhaseKernel ∘ₘ P₂.map Z₂).map forgetPhase) :=
    (Measure.isProbabilityMeasure_map_iff measurable_forgetPhase.aemeasurable).2 hU₂
  have hconst := uniformlyMutuallyAbsolutelyContinuous_const
    (absolutelyContinuous_uniformized_forgetPhase h.mark_left_right)
    (absolutelyContinuous_uniformized_forgetPhase h.mark_right_left)
  exact ⟨(hconst.1.map_measurable Ψ h.measurable_recon).of_tendsto_tvDist hT₁ hT₂,
    (hconst.2.map_measurable Ψ h.measurable_recon).of_tendsto_tvDist hT₂ hT₁⟩

end Lemma33

/-- **Lemma 3.3 of Gwynne–Miller–Sheffield for the local configurations near annuli.** If for all `0 < α < R` the
local configurations near `B_R(0) \ closedBall 0 α` of the embedded data `X₁ n` and `X₂ n` at mesh `1/n` satisfy the
facts of the proof of Lemma 3.3 (`IsPhaseReconstruction`), then their laws are uniformly mutually absolutely
continuous as `n → ∞`. -/
theorem localConfigUniformlyMutuallyAbsolutelyContinuous_of_isPhaseReconstruction
    {Ω₁ Ω₂ Y : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] [MeasurableSpace Y]
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
    {X₁ : ℕ → Ω₁ → C(ℝ, ℂ) × (ℤ → ℤ → ℕ)} {X₂ : ℕ → Ω₂ → C(ℝ, ℂ) × (ℤ → ℤ → ℕ)}
    (Z₁ : ℝ → ℝ → Ω₁ → CountablePhaseSpace (Y × ℝ)) (Z₂ : ℝ → ℝ → Ω₂ → CountablePhaseSpace (Y × ℝ))
    (Ψ : ℝ → ℝ → ℕ → CountablePhaseSpace Y → LocalConfig)
    (h : ∀ α R : ℝ, 0 < α → α < R →
      IsPhaseReconstruction P₁
        (fun n ω => localConfig (ball (0 : ℂ) R \ closedBall (0 : ℂ) α) (vertexData (1 / (n : ℝ)) (X₁ n ω)))
        P₂
        (fun n ω => localConfig (ball (0 : ℂ) R \ closedBall (0 : ℂ) α) (vertexData (1 / (n : ℝ)) (X₂ n ω)))
        (Z₁ α R) (Z₂ α R) (Ψ α R)) :
    LocalConfigUniformlyMutuallyAbsolutelyContinuous P₁ X₁ P₂ X₂ :=
  fun α R hα hαR => uniformlyMutuallyAbsolutelyContinuous_of_isPhaseReconstruction (h α R hα hαR)

/-! ### Reconstruction on events of probability close to one

In the comparison of the `γ`-cone with the zero cone, the configuration near an annulus is recovered from the outer
data and the residues only on an event of the curve of probability at least `1 - 1/(m+1)`, for cutoffs depending on
`m`. The event is a condition `countOuter Z ∈ G m` on the outer data; given it, the reconstruction holds with
probability tending to one. Restricting to the event, transferring by total variation and the equivalence of the
resampled laws, and letting `m → ∞` gives uniform mutual absolute continuity. -/

section ApproxReconstruction

/-- The number of coordinates and the outer data of a phase vector. -/
def countOuterOf {Y : Type*} (x : CountablePhaseSpace Y) : ℕ × Y :=
  (x.1, x.2.1)

variable {Ω Y S : Type*} [MeasurableSpace Ω] [MeasurableSpace Y] [MeasurableSpace S]

/-- The law of the outer data together with residues resampled uniformly on `[0, 1)^K`. -/
def uniformizedLaw (P : Measure Ω) (Z : Ω → CountablePhaseSpace (Y × ℝ)) :
    Measure (CountablePhaseSpace Y) :=
  (countableUniformPhaseKernel ∘ₘ P.map Z).map forgetPhase

theorem isProbabilityMeasure_uniformizedLaw {P : Measure Ω} [IsProbabilityMeasure P]
    {Z : Ω → CountablePhaseSpace (Y × ℝ)} (hZ : AEMeasurable Z P) :
    IsProbabilityMeasure (uniformizedLaw P Z) := by
  have hPZ : IsProbabilityMeasure (P.map Z) :=
    (Measure.isProbabilityMeasure_map_iff hZ).2 inferInstance
  have hU : IsProbabilityMeasure (countableUniformPhaseKernel ∘ₘ P.map Z) :=
    isProbabilityMeasure_uniformized _
  exact (Measure.isProbabilityMeasure_map_iff measurable_forgetPhase.aemeasurable).2 hU

theorem measurable_countOuterOf : Measurable (countOuterOf (Y := Y)) :=
  measurable_of_countablePhase fun _ => measurable_const.prodMk measurable_fst

omit [MeasurableSpace Y] in
theorem countOuterOf_forgetPhase_countablePhaseMap (a : ℝ) (x : CountablePhaseSpace (Y × ℝ)) :
    countOuterOf (forgetPhase (countablePhaseMap a markPhase x)) = countOuter x := by
  obtain ⟨k, e, v⟩ := x
  rfl

/-- **Asymptotic uniformity of the residues.** If the conditional law of the coordinates given the mark is absolutely
continuous with respect to Lebesgue measure, the law of the outer data and the residues at mesh `1/n` converges in
total variation to the law with the residues resampled uniformly. -/
theorem tendsto_tvDist_map_forgetPhase_countablePhaseMap {P : Measure Ω} [IsProbabilityMeasure P]
    {Z : Ω → CountablePhaseSpace (Y × ℝ)} (hZ : AEMeasurable Z P)
    (hac : ∀ k : ℕ,
      let ν := (P.map Z).comap (@Sigma.mk ℕ (fun j => (Y × ℝ) × (Fin j → ℝ)) k)
      ν ≪ (ν.map Prod.fst).prod (volume : Measure (Fin k → ℝ))) :
    Tendsto (fun n : ℕ => QuantumZipper.TV.tvDist
      (P.map fun ω => forgetPhase (countablePhaseMap (n : ℝ) markPhase (Z ω)))
      (uniformizedLaw P Z)) atTop (𝓝 0) := by
  have hPZ : IsProbabilityMeasure (P.map Z) :=
    (Measure.isProbabilityMeasure_map_iff hZ).2 inferInstance
  have hph : ∀ n : ℕ, Measurable (countablePhaseMap (n : ℝ) (markPhase (Y := Y))) :=
    fun n => measurable_countablePhaseMap _ _ fun k => measurable_markPhase k
  have hB := tendsto_tvDist_countablePhaseMap_image (P.map Z) hac (fun n : ℕ => (n : ℝ))
    tendsto_natCast_atTop_atTop (fun _ => markPhase) (fun _ k => measurable_markPhase k)
    (fun _ => forgetPhase) fun _ => measurable_forgetPhase
  refine hB.congr fun n => ?_
  congr 1
  rw [Measure.map_map measurable_forgetPhase (hph n),
    AEMeasurable.map_map_of_aemeasurable (measurable_forgetPhase.comp (hph n)).aemeasurable hZ]
  rfl

/-- **Upper bound through the reconstruction.** The probability that the configuration `C` lies in `F` is at most
the probability of the bad event `countOuter Z ∉ G`, plus the probability that the reconstruction fails on the good
event, plus the mass under `ρ` of the outer data and residues in the good event reconstructed into `F`, plus the total
variation distance from `ρ` of the law of the outer data and the residues. -/
theorem map_apply_le_reconstruction {P : Measure Ω} {C : Ω → S} (hC : AEMeasurable C P)
    {Z : Ω → CountablePhaseSpace (Y × ℝ)} (hZ : AEMeasurable Z P) {Ψ : CountablePhaseSpace Y → S}
    (hΨ : Measurable Ψ) {G : Set (ℕ × Y)} (hG : MeasurableSet G) (a : ℝ)
    (ρ : Measure (CountablePhaseSpace Y)) {F : Set S} (hF : MeasurableSet F) :
    P.map C F ≤ P {ω | countOuter (Z ω) ∉ G} +
      P {ω | countOuter (Z ω) ∈ G ∧ C ω ≠ Ψ (forgetPhase (countablePhaseMap a markPhase (Z ω)))} +
      (ρ (countOuterOf ⁻¹' G ∩ Ψ ⁻¹' F) + QuantumZipper.TV.tvDist
        (P.map fun ω => forgetPhase (countablePhaseMap a markPhase (Z ω))) ρ) := by
  have hph : Measurable (countablePhaseMap a (markPhase (Y := Y))) :=
    measurable_countablePhaseMap _ _ fun k => measurable_markPhase k
  have hR : AEMeasurable (fun ω => forgetPhase (countablePhaseMap a markPhase (Z ω))) P :=
    (measurable_forgetPhase.comp hph).comp_aemeasurable hZ
  have hA : MeasurableSet (countOuterOf ⁻¹' G ∩ Ψ ⁻¹' F) :=
    (measurable_countOuterOf hG).inter (hΨ hF)
  have hsub : C ⁻¹' F ⊆ ({ω | countOuter (Z ω) ∉ G} ∪
      {ω | countOuter (Z ω) ∈ G ∧ C ω ≠ Ψ (forgetPhase (countablePhaseMap a markPhase (Z ω)))}) ∪
      (fun ω => forgetPhase (countablePhaseMap a markPhase (Z ω))) ⁻¹'
        (countOuterOf ⁻¹' G ∩ Ψ ⁻¹' F) := by
    intro ω hω
    by_cases hg : countOuter (Z ω) ∈ G
    · by_cases hc : C ω = Ψ (forgetPhase (countablePhaseMap a markPhase (Z ω)))
      · refine Or.inr ⟨?_, ?_⟩
        · show countOuterOf (forgetPhase (countablePhaseMap a markPhase (Z ω))) ∈ G
          rw [countOuterOf_forgetPhase_countablePhaseMap]
          exact hg
        · show Ψ (forgetPhase (countablePhaseMap a markPhase (Z ω))) ∈ F
          rw [← hc]
          exact hω
      · exact Or.inl (Or.inr ⟨hg, hc⟩)
    · exact Or.inl (Or.inl hg)
  have hle := QuantumZipper.TV.le_tvDist
    (μ := P.map fun ω => forgetPhase (countablePhaseMap a markPhase (Z ω))) (ν := ρ) hA
  rw [Measure.map_apply_of_aemeasurable hR hA] at hle
  rw [Measure.map_apply_of_aemeasurable hC hF]
  exact (measure_mono hsub).trans ((measure_union_le _ _).trans
    (add_le_add (measure_union_le _ _) (tsub_le_iff_left.1 hle)))

/-- **Lower bound through the reconstruction.** The mass under `ρ` of the outer data and residues in the good event
reconstructed into `F` is at most the probability that the configuration `C` lies in `F`, plus the probability that
the reconstruction fails on the good event, plus the total variation distance from `ρ` of the law of the outer data
and the residues. -/
theorem le_map_apply_add_reconstruction {P : Measure Ω} {C : Ω → S} (hC : AEMeasurable C P)
    {Z : Ω → CountablePhaseSpace (Y × ℝ)} (hZ : AEMeasurable Z P) {Ψ : CountablePhaseSpace Y → S}
    (hΨ : Measurable Ψ) {G : Set (ℕ × Y)} (hG : MeasurableSet G) (a : ℝ)
    (ρ : Measure (CountablePhaseSpace Y)) {F : Set S} (hF : MeasurableSet F) :
    ρ (countOuterOf ⁻¹' G ∩ Ψ ⁻¹' F) ≤ P.map C F +
      P {ω | countOuter (Z ω) ∈ G ∧ C ω ≠ Ψ (forgetPhase (countablePhaseMap a markPhase (Z ω)))} +
      QuantumZipper.TV.tvDist (P.map fun ω => forgetPhase (countablePhaseMap a markPhase (Z ω))) ρ := by
  have hph : Measurable (countablePhaseMap a (markPhase (Y := Y))) :=
    measurable_countablePhaseMap _ _ fun k => measurable_markPhase k
  have hR : AEMeasurable (fun ω => forgetPhase (countablePhaseMap a markPhase (Z ω))) P :=
    (measurable_forgetPhase.comp hph).comp_aemeasurable hZ
  have hA : MeasurableSet (countOuterOf ⁻¹' G ∩ Ψ ⁻¹' F) :=
    (measurable_countOuterOf hG).inter (hΨ hF)
  have hsub : (fun ω => forgetPhase (countablePhaseMap a markPhase (Z ω))) ⁻¹'
      (countOuterOf ⁻¹' G ∩ Ψ ⁻¹' F) ⊆ C ⁻¹' F ∪
      {ω | countOuter (Z ω) ∈ G ∧ C ω ≠ Ψ (forgetPhase (countablePhaseMap a markPhase (Z ω)))} := by
    intro ω hω
    obtain ⟨hg, hψ⟩ := hω
    have hg' : countOuter (Z ω) ∈ G := by
      rw [← countOuterOf_forgetPhase_countablePhaseMap a (Z ω)]
      exact hg
    by_cases hc : C ω = Ψ (forgetPhase (countablePhaseMap a markPhase (Z ω)))
    · left
      show C ω ∈ F
      rw [hc]
      exact hψ
    · exact Or.inr ⟨hg', hc⟩
  have hle := QuantumZipper.TV.le_tvDist'
    (μ := P.map fun ω => forgetPhase (countablePhaseMap a markPhase (Z ω))) (ν := ρ) hA
  rw [Measure.map_apply_of_aemeasurable hR hA] at hle
  rw [Measure.map_apply_of_aemeasurable hC hF]
  exact (tsub_le_iff_left.1 hle).trans
    (add_le_add ((measure_mono hsub).trans (measure_union_le _ _)) le_rfl)

end ApproxReconstruction

section ApproxLemma33

variable {Ω₁ Ω₂ S : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] [MeasurableSpace S]
  {Y : ℕ → Type*} [∀ m, MeasurableSpace (Y m)]

/-- **One direction of Lemma 3.3 from reconstructions on events of probability close to one.** For every cutoff
`m`, let the configurations `C₁ n`, `C₂ n` be recovered by a common map `Ψ m n` from the outer data and the residues
of the marked phase vectors `Z₁ m`, `Z₂ m`, with probability tending to one on the good events
`countOuter (Zᵢ m) ∈ G m`, the good event of the second side having probability at least `1 - 1/(m+1)`. If the
conditional laws of the coordinates given the marks are absolutely continuous with respect to Lebesgue measure and
the law of the number of coordinates and the outer data of the second side is absolutely continuous with respect to
that of the first side, then the laws of `C₁ n` are uniformly absolutely continuous as `n → ∞` with respect to the
laws of `C₂ n`. -/
theorem uniformlyAbsolutelyContinuous_of_approxPhaseReconstruction {P₁ : Measure Ω₁}
    {P₂ : Measure Ω₂} [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂] {C₁ : ℕ → Ω₁ → S}
    {C₂ : ℕ → Ω₂ → S} {Z₁ : ∀ m, Ω₁ → CountablePhaseSpace (Y m × ℝ)}
    {Z₂ : ∀ m, Ω₂ → CountablePhaseSpace (Y m × ℝ)} {Ψ : ∀ m, ℕ → CountablePhaseSpace (Y m) → S}
    {G : ∀ m, Set (ℕ × Y m)}
    (hZ₁ : ∀ m, AEMeasurable (Z₁ m) P₁) (hZ₂ : ∀ m, AEMeasurable (Z₂ m) P₂)
    (hΨ : ∀ m n, Measurable (Ψ m n)) (hG : ∀ m, MeasurableSet (G m))
    (hC₁ : ∀ n, AEMeasurable (C₁ n) P₁) (hC₂ : ∀ n, AEMeasurable (C₂ n) P₂)
    (hgood₂ : ∀ m, P₂ {ω | countOuter (Z₂ m ω) ∉ G m} ≤ ((m : ℝ≥0∞) + 1)⁻¹)
    (hrec₁ : ∀ m, Tendsto (fun n : ℕ => P₁ {ω | countOuter (Z₁ m ω) ∈ G m ∧
      C₁ n ω ≠ Ψ m n (forgetPhase (countablePhaseMap (n : ℝ) markPhase (Z₁ m ω)))}) atTop (𝓝 0))
    (hrec₂ : ∀ m, Tendsto (fun n : ℕ => P₂ {ω | countOuter (Z₂ m ω) ∈ G m ∧
      C₂ n ω ≠ Ψ m n (forgetPhase (countablePhaseMap (n : ℝ) markPhase (Z₂ m ω)))}) atTop (𝓝 0))
    (hac₁ : ∀ m k,
      let ν := (P₁.map (Z₁ m)).comap (@Sigma.mk ℕ (fun j => (Y m × ℝ) × (Fin j → ℝ)) k)
      ν ≪ (ν.map Prod.fst).prod (volume : Measure (Fin k → ℝ)))
    (hac₂ : ∀ m k,
      let ν := (P₂.map (Z₂ m)).comap (@Sigma.mk ℕ (fun j => (Y m × ℝ) × (Fin j → ℝ)) k)
      ν ≪ (ν.map Prod.fst).prod (volume : Measure (Fin k → ℝ)))
    (h₂₁ : ∀ m, (P₂.map (Z₂ m)).map countOuter ≪ (P₁.map (Z₁ m)).map countOuter) :
    UniformlyAbsolutelyContinuous (Ω := fun _ => S) (fun n => P₁.map (C₁ n))
      (fun n => P₂.map (C₂ n)) := by
  intro p hp0 hp1
  -- the gap `1 - p` exceeds `3 b`
  obtain ⟨b, hb0, hab⟩ : ∃ b : ℝ≥0∞, 0 < b ∧ b + b + b < 1 - p := by
    have ha0 : (1 - p : ℝ≥0∞) ≠ 0 := (tsub_pos_of_lt hp1).ne'
    have haT : (1 - p : ℝ≥0∞) ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
    have hc0 : 0 < (1 - p) / 2 := ENNReal.half_pos ha0
    have hcT : (1 - p) / 2 ≠ ∞ := ENNReal.div_ne_top haT two_ne_zero
    refine ⟨(1 - p) / 2 / 2, ENNReal.half_pos hc0.ne', ?_⟩
    calc (1 - p) / 2 / 2 + (1 - p) / 2 / 2 + (1 - p) / 2 / 2
        = (1 - p) / 2 + (1 - p) / 2 / 2 := by rw [ENNReal.add_halves]
      _ < (1 - p) / 2 + (1 - p) / 2 :=
        ENNReal.add_lt_add_left hcT (ENNReal.half_lt_self hc0.ne' hcT)
      _ = 1 - p := ENNReal.add_halves _
  -- the cutoff `m`: the bad event of the second side has probability at most `b`
  obtain ⟨m, hm⟩ := ENNReal.exists_inv_nat_lt hb0.ne'
  have hbad : P₂ {ω | countOuter (Z₂ m ω) ∉ G m} ≤ b :=
    (hgood₂ m).trans ((ENNReal.inv_le_inv.2 le_self_add).trans hm.le)
  -- the resampled laws: sets of small mass under the first have small mass under the second
  have hρ₁ := isProbabilityMeasure_uniformizedLaw (hZ₁ m)
  have hρ₂ := isProbabilityMeasure_uniformizedLaw (hZ₂ m)
  obtain ⟨d, hd0, hd⟩ := LatticeProb.exists_measure_le_of_absolutelyContinuous
    (uniformizedLaw P₂ (Z₂ m)) (uniformizedLaw P₁ (Z₁ m))
    (absolutelyContinuous_uniformized_forgetPhase (h₂₁ m)) hb0
  obtain ⟨d', hd'0, hd'1, hd'⟩ : ∃ d' : ℝ≥0∞, 0 < d' ∧ d' ≤ 1 ∧ ∀ T,
      uniformizedLaw P₁ (Z₁ m) T ≤ d' → uniformizedLaw P₂ (Z₂ m) T ≤ b :=
    ⟨min d 1, lt_min hd0 one_pos, min_le_right _ _, fun T hT => hd T (hT.trans (min_le_left _ _))⟩
  have hd'2 : 0 < d' / 2 := ENNReal.half_pos hd'0.ne'
  -- the reconstruction errors and the total variation distances are eventually small
  have ht₁ := ((hrec₁ m).add (tendsto_tvDist_map_forgetPhase_countablePhaseMap (hZ₁ m)
    (hac₁ m))).eventually
      (gt_mem_nhds (show (0 : ℝ≥0∞) + 0 < d' / 2 by rw [add_zero]; exact hd'2))
  have ht₂ := ((hrec₂ m).add (tendsto_tvDist_map_forgetPhase_countablePhaseMap (hZ₂ m)
    (hac₂ m))).eventually (gt_mem_nhds (show (0 : ℝ≥0∞) + 0 < b by rw [add_zero]; exact hb0))
  obtain ⟨N, hN⟩ := eventually_atTop.1 (ht₁.and ht₂)
  refine ⟨1 - d' / 2, tsub_pos_of_lt ?_,
    ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hd'2.ne', N, fun n hn E hE hQE => ?_⟩
  · exact (ENNReal.half_lt_self hd'0.ne' (ne_top_of_le_ne_top ENNReal.one_ne_top hd'1)).trans_le
      hd'1
  dsimp only at hQE ⊢
  obtain ⟨h₁n, h₂n⟩ := hN n hn
  have hL₁ : IsProbabilityMeasure (P₁.map (C₁ n)) :=
    (Measure.isProbabilityMeasure_map_iff (hC₁ n)).2 inferInstance
  have hL₂ : IsProbabilityMeasure (P₂.map (C₂ n)) :=
    (Measure.isProbabilityMeasure_map_iff (hC₂ n)).2 inferInstance
  -- under the second side the complement of `E` has probability at least `1 - p`
  have hc₂ : 1 - p ≤ P₂.map (C₂ n) Eᶜ := by
    rw [prob_compl_eq_one_sub hE]
    exact tsub_le_tsub_left hQE 1
  have hI := map_apply_le_reconstruction (hC₂ n) (hZ₂ m) (hΨ m n) (hG m) (n : ℝ)
    (uniformizedLaw P₂ (Z₂ m)) hE.compl
  have hII := le_map_apply_add_reconstruction (hC₁ n) (hZ₁ m) (hΨ m n) (hG m) (n : ℝ)
    (uniformizedLaw P₁ (Z₁ m)) hE.compl
  -- hence the resampled law of the first side gives mass more than `d'` to the reconstructed event
  have hA : d' < uniformizedLaw P₁ (Z₁ m) (countOuterOf ⁻¹' G m ∩ Ψ m n ⁻¹' Eᶜ) := by
    refine not_le.1 fun hle => lt_irrefl (1 - p) ?_
    have key : ∀ x y z w : ℝ≥0∞, x ≤ b → y + w ≤ b → z ≤ b → x + y + (z + w) ≤ b + b + b := by
      intro x y z w hx hyw hz
      calc x + y + (z + w) = x + (y + w) + z := by ring
        _ ≤ b + b + b := add_le_add (add_le_add hx hyw) hz
    exact (hc₂.trans (hI.trans (key _ _ _ _ hbad h₂n.le (hd' _ hle)))).trans_lt hab
  -- under the first side the complement of `E` has probability at least `d' / 2`
  have hc₁ : d' / 2 ≤ P₁.map (C₁ n) Eᶜ := by
    refine not_lt.1 fun hlt => lt_irrefl d' ?_
    have key : ∀ x y z : ℝ≥0∞, x ≤ d' / 2 → y + z ≤ d' / 2 → x + y + z ≤ d' := by
      intro x y z hx hyz
      rw [add_assoc, ← ENNReal.add_halves d']
      exact add_le_add hx hyz
    exact hA.trans_le (hII.trans (key _ _ _ hlt.le h₁n.le))
  have hE' : P₁.map (C₁ n) E = 1 - P₁.map (C₁ n) Eᶜ := by
    rw [prob_compl_eq_one_sub hE, ENNReal.sub_sub_cancel ENNReal.one_ne_top prob_le_one]
  rw [hE']
  exact tsub_le_tsub_left hc₁ 1

/-- **The facts of the proof of Lemma 3.3 with cutoffs.** For every cutoff `m`, the configurations `C₁ n` under
`P₁` and `C₂ n` under `P₂` at mesh `1/n` are recovered by a common map `Ψ m n` from the outer data and the residues
of the marked phase vectors `Z₁ m`, `Z₂ m` (number of coordinates, outer data, phase, coordinates), with probability
tending to one on the good events `countOuter (Zᵢ m) ∈ G m` of probability at least `1 - 1/(m+1)`. -/
structure IsApproxPhaseReconstruction (P₁ : Measure Ω₁) (C₁ : ℕ → Ω₁ → S) (P₂ : Measure Ω₂)
    (C₂ : ℕ → Ω₂ → S) (Z₁ : ∀ m, Ω₁ → CountablePhaseSpace (Y m × ℝ))
    (Z₂ : ∀ m, Ω₂ → CountablePhaseSpace (Y m × ℝ)) (Ψ : ∀ m, ℕ → CountablePhaseSpace (Y m) → S)
    (G : ∀ m, Set (ℕ × Y m)) : Prop where
  aemeasurable_mark_left : ∀ m, AEMeasurable (Z₁ m) P₁
  aemeasurable_mark_right : ∀ m, AEMeasurable (Z₂ m) P₂
  measurable_recon : ∀ m n, Measurable (Ψ m n)
  measurableSet_good : ∀ m, MeasurableSet (G m)
  aemeasurable_left : ∀ n, AEMeasurable (C₁ n) P₁
  aemeasurable_right : ∀ n, AEMeasurable (C₂ n) P₂
  /-- The good events have probability at least `1 - 1/(m+1)`. -/
  good_left : ∀ m, P₁ {ω | countOuter (Z₁ m ω) ∉ G m} ≤ ((m : ℝ≥0∞) + 1)⁻¹
  good_right : ∀ m, P₂ {ω | countOuter (Z₂ m ω) ∉ G m} ≤ ((m : ℝ≥0∞) + 1)⁻¹
  /-- On the good events the configuration is the reconstruction with probability tending to one. -/
  recon_left : ∀ m, Tendsto (fun n : ℕ => P₁ {ω | countOuter (Z₁ m ω) ∈ G m ∧
    C₁ n ω ≠ Ψ m n (forgetPhase (countablePhaseMap (n : ℝ) markPhase (Z₁ m ω)))}) atTop (𝓝 0)
  recon_right : ∀ m, Tendsto (fun n : ℕ => P₂ {ω | countOuter (Z₂ m ω) ∈ G m ∧
    C₂ n ω ≠ Ψ m n (forgetPhase (countablePhaseMap (n : ℝ) markPhase (Z₂ m ω)))}) atTop (𝓝 0)
  /-- Given the mark, the conditional law of the coordinates is absolutely continuous with respect to Lebesgue
  measure. -/
  ac_left : ∀ m k,
    let ν := (P₁.map (Z₁ m)).comap (@Sigma.mk ℕ (fun j => (Y m × ℝ) × (Fin j → ℝ)) k)
    ν ≪ (ν.map Prod.fst).prod (volume : Measure (Fin k → ℝ))
  ac_right : ∀ m k,
    let ν := (P₂.map (Z₂ m)).comap (@Sigma.mk ℕ (fun j => (Y m × ℝ) × (Fin j → ℝ)) k)
    ν ≪ (ν.map Prod.fst).prod (volume : Measure (Fin k → ℝ))
  /-- The laws of the number of coordinates and the outer data are mutually absolutely continuous. -/
  mark_left_right : ∀ m, (P₁.map (Z₁ m)).map countOuter ≪ (P₂.map (Z₂ m)).map countOuter
  mark_right_left : ∀ m, (P₂.map (Z₂ m)).map countOuter ≪ (P₁.map (Z₁ m)).map countOuter

/-- **Lemma 3.3 of Gwynne–Miller–Sheffield from reconstructions on events of probability close to one**
(arXiv:1705.11161, p. 24, Definition 3.2): under `IsApproxPhaseReconstruction`, the laws of the configurations
`C₁ n` and `C₂ n` are uniformly mutually absolutely continuous as `n → ∞`. -/
theorem uniformlyMutuallyAbsolutelyContinuous_of_isApproxPhaseReconstruction {P₁ : Measure Ω₁}
    {P₂ : Measure Ω₂} [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂] {C₁ : ℕ → Ω₁ → S}
    {C₂ : ℕ → Ω₂ → S} {Z₁ : ∀ m, Ω₁ → CountablePhaseSpace (Y m × ℝ)}
    {Z₂ : ∀ m, Ω₂ → CountablePhaseSpace (Y m × ℝ)} {Ψ : ∀ m, ℕ → CountablePhaseSpace (Y m) → S}
    {G : ∀ m, Set (ℕ × Y m)} (h : IsApproxPhaseReconstruction P₁ C₁ P₂ C₂ Z₁ Z₂ Ψ G) :
    UniformlyMutuallyAbsolutelyContinuous (Ω := fun _ => S) (fun n => P₁.map (C₁ n))
      (fun n => P₂.map (C₂ n)) :=
  ⟨uniformlyAbsolutelyContinuous_of_approxPhaseReconstruction h.aemeasurable_mark_left
      h.aemeasurable_mark_right h.measurable_recon h.measurableSet_good h.aemeasurable_left
      h.aemeasurable_right h.good_right h.recon_left h.recon_right h.ac_left h.ac_right
      h.mark_right_left,
    uniformlyAbsolutelyContinuous_of_approxPhaseReconstruction h.aemeasurable_mark_right
      h.aemeasurable_mark_left h.measurable_recon h.measurableSet_good h.aemeasurable_right
      h.aemeasurable_left h.good_left h.recon_right h.recon_left h.ac_right h.ac_left
      h.mark_left_right⟩

end ApproxLemma33

/-- **Lemma 3.3 of Gwynne–Miller–Sheffield for the local configurations near annuli, with cutoffs.** If for all
`0 < α < R` the local configurations near `B_R(0) \ closedBall 0 α` of the embedded data `X₁ n` and `X₂ n` at mesh
`1/n` satisfy `IsApproxPhaseReconstruction`, then their laws are uniformly mutually absolutely continuous as
`n → ∞`. -/
theorem localConfigUniformlyMutuallyAbsolutelyContinuous_of_isApproxPhaseReconstruction
    {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] {Y : ℝ → ℝ → ℕ → Type*}
    [∀ α R m, MeasurableSpace (Y α R m)] {P₁ : Measure Ω₁} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₁]
    [IsProbabilityMeasure P₂] {X₁ : ℕ → Ω₁ → C(ℝ, ℂ) × (ℤ → ℤ → ℕ)}
    {X₂ : ℕ → Ω₂ → C(ℝ, ℂ) × (ℤ → ℤ → ℕ)}
    (Z₁ : ∀ α R m, Ω₁ → CountablePhaseSpace (Y α R m × ℝ))
    (Z₂ : ∀ α R m, Ω₂ → CountablePhaseSpace (Y α R m × ℝ))
    (Ψ : ∀ α R m, ℕ → CountablePhaseSpace (Y α R m) → LocalConfig)
    (G : ∀ α R m, Set (ℕ × Y α R m))
    (h : ∀ α R : ℝ, 0 < α → α < R →
      IsApproxPhaseReconstruction P₁
        (fun n ω => localConfig (ball (0 : ℂ) R \ closedBall (0 : ℂ) α) (vertexData (1 / (n : ℝ)) (X₁ n ω)))
        P₂
        (fun n ω => localConfig (ball (0 : ℂ) R \ closedBall (0 : ℂ) α) (vertexData (1 / (n : ℝ)) (X₂ n ω)))
        (Z₁ α R) (Z₂ α R) (Ψ α R) (G α R)) :
    LocalConfigUniformlyMutuallyAbsolutelyContinuous P₁ X₁ P₂ X₂ :=
  fun α R hα hαR => uniformlyMutuallyAbsolutelyContinuous_of_isApproxPhaseReconstruction (h α R hα hαR)

end MatedCRT
