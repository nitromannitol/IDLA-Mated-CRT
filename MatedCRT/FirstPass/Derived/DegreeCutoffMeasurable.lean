import MatedCRT.FirstPass.Derived.MaxCellDiamTendsto
import MatedCRT.Proofs.MatingOfTrees.AdjacentCells
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.DegreeMeasurable

/-!
# Local finiteness and measurability of the cutoff degree measure (BG20 Lemma 7.6, step C2)

Two inputs of the convergence of the reversibility pairing at the cutoff degree measure
`ν^ε = Σ_x ε deg^ε(x) ψ(η(εx)) δ_{η(εx)}` are supplied here for every valid environment.

**Local finiteness.** Under the mating-of-trees coupling, adjacent vertices of `𝒢^ε` have intersecting cells for all
`ε > 0` simultaneously (the argument of `adjacentCellsMeetAeStep`, which uses no constraint on `γ`), and the curve is
continuous and proper; hence `𝒢^ε` is almost surely locally finite for every `ε > 0`
(`ae_isLocallyFiniteMult_of_isValid`). The corollaries `..._of_walkLaw` are the results of `MaxCellDiamTendsto`
without the local finiteness hypothesis.

**Measurability in the Lévy-Prokhorov metric.** For finitely many atoms, the Lévy-Prokhorov distance between
`Σ_{x ∈ s} c x δ_{p x}` and `Σ_{x ∈ s} c' x δ_{p' x}` is at most `Σ_{x ∈ s} (|p x - p' x| + |c x - c' x|)`
(`levyProkhorovEDist_atomicMeasure_le`), so the finite atomic measure depends continuously on its weights and atoms.
Almost surely only finitely many vertices `x` have `η(εx) ∈ supp ψ`, so `ν^ε` is the eventually constant limit of its
truncations to `|x| ≤ N`, each a continuous function of finitely many measurable coordinates of the environment
(the degrees and the measurable version of the curve). For any Borel σ-algebra on the Lévy-Prokhorov space of finite
measures on `ℂ`, `ω ↦ ν^ε(ω)` is therefore almost everywhere measurable
(`aemeasurable_levyProkhorov_degreeCutoffMeasure`): the hypothesis `hμ` of
`tendsto_integral_levyProkhorov_projection_of_tendstoInMeasure_levyProkhorovDist` (Lattice-Probability).
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Metric LatticeProb
open MarkovProcess (ContinuousPath)
open scoped NNReal ENNReal

namespace MatedCRT.FirstPass.Derived

/-! ### Local finiteness of the mated-CRT map for every valid environment -/

section LocallyFinite

variable {Ω : Type} [MeasurableSpace Ω]

/-- For every valid environment, almost surely, for every `ε > 0`, adjacent vertices of `𝒢^ε` have intersecting
cells `η([ε(j-1), εj]) ∩ η([ε(k-1), εk]) ≠ ∅` (mating-of-trees merge rule; no constraint on `γ` is used). -/
theorem ae_cellsMeet_of_isValid {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {S : MatedCRTEnv Ω}
    (hS : S.IsValid 𝒮 γ) :
    ∀ᵐ ω ∂S.P, ∀ ε : ℝ, 0 < ε → ∀ j k : ℤ, S.mult ε ω j k ≠ 0 →
      (cell ε (S.η ω) j ∩ cell ε (S.η ω) k).Nonempty := by
  obtain ⟨X, X₀, hIG₀, B, B', B₀, B₀', U, ηL, η', η₀, hC, htie⟩ := hS.matingOfTrees
  have hdist := ae_of_ae_map hC.measurable_curves.2.2.2.aemeasurable
    (MatedCRTHarmonic.MatedCRT.ae_locMinDistinct hC.boundaryLawBM)
  filter_upwards [hdist, hC.merge, htie] with ω hdist hmerge htie
  intro ε hε j k hedge
  have hLd : ∀ x y, x ≠ y → IsLocalMin (fun t => (S.bm ω t).1) x →
      IsLocalMin (fun t => (S.bm ω t).1) y → (S.bm ω x).1 ≠ (S.bm ω y).1 := by
    simpa [MatedCRTHarmonic.MatedCRT.lrCoord] using hdist 0
  have hRd : ∀ x y, x ≠ y → IsLocalMin (fun t => (S.bm ω t).2) x →
      IsLocalMin (fun t => (S.bm ω t).2) y → (S.bm ω x).2 ≠ (S.bm ω y).2 := by
    simpa [MatedCRTHarmonic.MatedCRT.lrCoord] using hdist 1
  have hLm : ∀ s t, MatedCRTHarmonic.MatedCRT.DirectRel (fun u => (S.bm ω u).1) s t →
      S.η ω s = S.η ω t := by
    intro s t h
    rw [← htie.1]
    exact hmerge s t (Or.inl h)
  have hRm : ∀ s t, MatedCRTHarmonic.MatedCRT.DirectRel (fun u => (S.bm ω u).2) s t →
      S.η ω s = S.η ω t := by
    intro s t h
    rw [← htie.1]
    exact hmerge s t (Or.inr h)
  exact cells_meet_of_bmEdgeCount hε.le (S.bm ω).continuous.fst (S.bm ω).continuous.snd
    hLd hRd hLm hRm hedge

/-- **The mated-CRT map is locally finite, for every valid environment**: almost surely `𝒢^ε` is locally finite for
every `ε > 0`. -/
theorem ae_isLocallyFiniteMult_of_isValid {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {S : MatedCRTEnv Ω}
    (hS : S.IsValid 𝒮 γ) : ∀ᵐ ω ∂S.P, ∀ ε : ℝ, 0 < ε → IsLocallyFiniteMult (S.mult ε ω) := by
  filter_upwards [ae_cellsMeet_of_isValid hS, hS.ae_tendsto_cocompact, hS.isAreaParametrized]
    with ω hmeet hp hap
  intro ε hε
  exact isLocallyFiniteMult_of_cells_meet hap.1 hp hε (hmeet ε hε)

/-- **The reversibility pairing at the cutoff degree measure tends to `0` in probability, for every valid
environment** (BG20 Lemma 7.6 without Lemma 7.7, step C2): `tendstoInMeasure_reversibilityPairing_degreeCutoffMeasure`
with the convergence of the cell diameters and the local finiteness supplied by `hdiam_of_isValid` and
`ae_isLocallyFiniteMult_of_isValid`. -/
theorem tendstoInMeasure_reversibilityPairing_degreeCutoffMeasure_of_walkLaw {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) {η' : Ω → C(ℝ, ℂ)} (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω)
    {f g ψ : ℂ → ℝ} (hfb : ∃ C, ∀ z, |f z| ≤ C) {Kf : ℝ≥0} (hfl : LipschitzWith Kf f)
    (hgb : ∃ C, ∀ z, |g z| ≤ C) {Kg : ℝ≥0} (hgl : LipschitzWith Kg g)
    (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) (hψ0 : ∀ z, 0 ≤ ψ z)
    (hψ1 : EqOn ψ 1 (tsupport f ∪ tsupport g))
    {ε : ℕ → ℝ} (hε0 : ∀ n, 0 < ε n) (hε : Tendsto ε atTop (𝓝 0))
    {t : ℕ → ℝ≥0} {T : ℝ≥0} (htT : ∀ n, t n ≤ T) (htN : ∀ n, ∃ N : ℕ, S.mε (ε n) * (t n : ℝ) = N)
    (hEqLaw : ∀ R a : ℝ, 0 < a → ∃ δ > 0, ∀ᶠ n in atTop,
      S.P {ω | ENNReal.ofReal a < walkLawModulus S η' (ε n) R δ ω} ≤ ENNReal.ofReal a)
    (hmass : ∀ a : ℝ, 0 < a → ∃ C : ℝ, ∀ᶠ n in atTop,
      S.P {ω | C < ((degreeCutoffMeasure (S.mult (ε n) ω) (ε n) (vertexPoint (ε n) (⇑(η' ω))) ψ).mass : ℝ)}
        ≤ ENNReal.ofReal a) :
    TendstoInMeasure S.P (fun n ω => reversibilityPairing f g ψ
        (degreeCutoffMeasure (S.mult (ε n) ω) (ε n) (vertexPoint (ε n) (⇑(η' ω))) ψ)
        (interpWalkLaw S η' (ε n) ω) (t n)) atTop (fun _ => 0) :=
  tendstoInMeasure_reversibilityPairing_degreeCutoffMeasure_of_isValid hS hae
    (ae_isLocallyFiniteMult_of_isValid hS) hfb hfl hgb hgl hψ hψc hψ0 hψ1 hε0 hε htT htN hEqLaw hmass

/-- **The reversibility pairing at the cutoff degree measure tends to `0` in probability, from Lemma 2.10, for every
valid environment** (BG20 Lemma 7.6 without Lemma 7.7, step C2):
`tendstoInMeasure_reversibilityPairing_degreeCutoffMeasure_of_D27` with the convergence of the cell diameters and the
local finiteness supplied by `hdiam_of_isValid` and `ae_isLocallyFiniteMult_of_isValid`, for `γ ∈ (0, 2)`. -/
theorem tendstoInMeasure_reversibilityPairing_degreeCutoffMeasure_of_D27_of_walkLaw
    {𝒮 : SpaceFillingSLEModel} (hD27 : DegreeMeasureConvergenceStmt 𝒮) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) {η' : Ω → C(ℝ, ℂ)} (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω)
    {f g ψ : ℂ → ℝ} (hfb : ∃ C, ∀ z, |f z| ≤ C) {Kf : ℝ≥0} (hfl : LipschitzWith Kf f)
    (hgb : ∃ C, ∀ z, |g z| ≤ C) {Kg : ℝ≥0} (hgl : LipschitzWith Kg g)
    (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) (hψ0 : ∀ z, 0 ≤ ψ z)
    (hψ1 : EqOn ψ 1 (tsupport f ∪ tsupport g))
    {ε : ℕ → ℝ} (hε0 : ∀ n, 0 < ε n) (hε : Tendsto ε atTop (𝓝 0))
    {t : ℕ → ℝ≥0} {T : ℝ≥0} (htT : ∀ n, t n ≤ T) (htN : ∀ n, ∃ N : ℕ, S.mε (ε n) * (t n : ℝ) = N)
    (hEqLaw : ∀ R a : ℝ, 0 < a → ∃ δ > 0, ∀ᶠ n in atTop,
      S.P {ω | ENNReal.ofReal a < walkLawModulus S η' (ε n) R δ ω} ≤ ENNReal.ofReal a) :
    TendstoInMeasure S.P (fun n ω => reversibilityPairing f g ψ
        (degreeCutoffMeasure (S.mult (ε n) ω) (ε n) (vertexPoint (ε n) (⇑(η' ω))) ψ)
        (interpWalkLaw S η' (ε n) ω) (t n)) atTop (fun _ => 0) :=
  tendstoInMeasure_reversibilityPairing_degreeCutoffMeasure_of_D27_of_isValid hD27 hγ hγ2 hS hae
    (ae_isLocallyFiniteMult_of_isValid hS) hfb hfl hgb hgl hψ hψc hψ0 hψ1 hε0 hε htT htN hEqLaw

end LocallyFinite

/-! ### Finite atomic measures in the Lévy-Prokhorov metric -/

section Atomic

variable {ι : Type*}

/-- The finite atomic measure `Σ_{x ∈ s} c x δ_{p x}` (weights `max (c x) 0`) as a finite measure on `ℂ`. -/
noncomputable def atomicFiniteMeasure (s : Finset ι) (c : ι → ℝ) (p : ι → ℂ) : FiniteMeasure ℂ :=
  ⟨atomicMeasure s c p, ⟨atomicMeasure_univ_lt_top s c p⟩⟩

theorem degreeCutoffMeasure_eq_atomicFiniteMeasure (m : ℤ → ℤ → ℕ) (ε : ℝ) (v : ℤ → ℂ) (ψ : ℂ → ℝ) :
    degreeCutoffMeasure m ε v ψ = atomicFiniteMeasure (vertexWindow v (tsupport ψ)) (degreeCutoffWeight m ε v ψ) v :=
  rfl

/-- Adding atoms of nonpositive weight does not change the finite atomic measure. -/
theorem atomicFiniteMeasure_eq_of_subset {s t : Finset ι} (hst : s ⊆ t) {c : ι → ℝ} (p : ι → ℂ)
    (h0 : ∀ x ∈ t, x ∉ s → c x ≤ 0) : atomicFiniteMeasure s c p = atomicFiniteMeasure t c p := by
  apply FiniteMeasure.toMeasure_injective
  show atomicMeasure s c p = atomicMeasure t c p
  unfold atomicMeasure
  refine Finset.sum_subset hst fun x hx hxs => ?_
  rw [ENNReal.ofReal_eq_zero.2 (h0 x hx hxs), zero_smul]

/-- Moving each atom by less than `r` and changing the weights: `Σ c x δ_{p x}(B) ≤ Σ c' x δ_{p' x}(B^r) +
Σ |c x - c' x|`, where `B^r` is the open `r`-thickening of `B`. -/
theorem atomicMeasure_apply_le_thickening (s : Finset ι) (c c' : ι → ℝ) {p p' : ι → ℂ} {B : Set ℂ}
    (hB : MeasurableSet B) {r : ℝ} (hr : ∀ x ∈ s, dist (p x) (p' x) < r) :
    atomicMeasure s c p B ≤
      atomicMeasure s c' p' (thickening r B) + ENNReal.ofReal (∑ x ∈ s, |c x - c' x|) := by
  have hT : MeasurableSet (thickening r B) := isOpen_thickening.measurableSet
  rw [atomicMeasure, atomicMeasure, Measure.finsetSum_apply, Measure.finsetSum_apply,
    ENNReal.ofReal_sum_of_nonneg (fun x _ => abs_nonneg _), ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun x hx => ?_
  rw [Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul, Measure.dirac_apply' _ hB,
    Measure.dirac_apply' _ hT]
  by_cases h : p x ∈ B
  · have h' : p' x ∈ thickening r B := mem_thickening_iff.2 ⟨p x, h, by rw [dist_comm]; exact hr x hx⟩
    rw [indicator_of_mem h, indicator_of_mem h', Pi.one_apply, Pi.one_apply, mul_one, mul_one]
    calc ENNReal.ofReal (c x) ≤ ENNReal.ofReal (c' x + |c x - c' x|) :=
          ENNReal.ofReal_le_ofReal (by linarith [le_abs_self (c x - c' x)])
      _ ≤ ENNReal.ofReal (c' x) + ENNReal.ofReal |c x - c' x| := ENNReal.ofReal_add_le
  · rw [indicator_of_notMem h, mul_zero]
    positivity

/-- **The Lévy-Prokhorov distance between finite atomic measures**:
`d_LP(Σ_{x ∈ s} c x δ_{p x}, Σ_{x ∈ s} c' x δ_{p' x}) ≤ Σ_{x ∈ s} (|p x - p' x| + |c x - c' x|)`. -/
theorem levyProkhorovEDist_atomicMeasure_le (s : Finset ι) (c c' : ι → ℝ) (p p' : ι → ℂ) :
    levyProkhorovEDist (atomicMeasure s c p) (atomicMeasure s c' p') ≤
      ENNReal.ofReal (∑ x ∈ s, (dist (p x) (p' x) + |c x - c' x|)) := by
  set δ := ∑ x ∈ s, (dist (p x) (p' x) + |c x - c' x|)
  have hnn : ∀ x ∈ s, 0 ≤ dist (p x) (p' x) + |c x - c' x| := fun x _ =>
    add_nonneg dist_nonneg (abs_nonneg _)
  have hδ0 : 0 ≤ δ := Finset.sum_nonneg hnn
  have hd : ∀ x ∈ s, dist (p x) (p' x) ≤ δ := fun x hx =>
    (le_add_of_nonneg_right (abs_nonneg _)).trans
      (Finset.single_le_sum (f := fun x => dist (p x) (p' x) + |c x - c' x|) hnn hx)
  have hc : ∑ x ∈ s, |c x - c' x| ≤ δ := Finset.sum_le_sum fun x _ => le_add_of_nonneg_left dist_nonneg
  have hc' : ∑ x ∈ s, |c' x - c x| ≤ δ :=
    (Finset.sum_congr rfl fun x _ => abs_sub_comm (c' x) (c x)).trans_le hc
  apply levyProkhorovEDist_le_of_forall
  intro ε B hε hεt hB
  have hεr : δ < ε.toReal := (ENNReal.ofReal_lt_iff_lt_toReal hδ0 hεt.ne).1 hε
  refine ⟨(atomicMeasure_apply_le_thickening s c c' (p := p) (p' := p') hB
      fun x hx => (hd x hx).trans_lt hεr).trans
    (add_le_add le_rfl ((ENNReal.ofReal_le_ofReal hc).trans hε.le)),
    (atomicMeasure_apply_le_thickening s c' c (p := p') (p' := p) hB fun x hx => ?_).trans
    (add_le_add le_rfl ((ENNReal.ofReal_le_ofReal hc').trans hε.le))⟩
  rw [dist_comm]
  exact (hd x hx).trans_lt hεr

/-- The finite atomic measure is a continuous function of its weights and atoms, for the Lévy-Prokhorov metric. -/
theorem continuous_levyProkhorov_atomicFiniteMeasure (s : Finset ι) :
    Continuous fun q : (ι → ℝ) × (ι → ℂ) => LevyProkhorov.ofMeasure (atomicFiniteMeasure s q.1 q.2) := by
  rw [continuous_iff_continuousAt]
  intro q
  rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
  have hg : Continuous fun q' : (ι → ℝ) × (ι → ℂ) =>
      ∑ x ∈ s, (dist (q'.2 x) (q.2 x) + |q'.1 x - q.1 x|) :=
    continuous_finsetSum _ fun x _ =>
      (((continuous_apply x).comp continuous_snd).dist continuous_const).add
        (((continuous_apply x).comp continuous_fst).sub continuous_const).abs
  have hg0 : Tendsto (fun q' : (ι → ℝ) × (ι → ℂ) =>
      ∑ x ∈ s, (dist (q'.2 x) (q.2 x) + |q'.1 x - q.1 x|)) (𝓝 q) (𝓝 0) := by
    have h := hg.tendsto q
    simp only [dist_self, sub_self, abs_zero, add_zero, Finset.sum_const_zero] at h
    exact h
  refine squeeze_zero (fun _ => dist_nonneg) (fun q' => ?_) hg0
  rw [LevyProkhorov.dist_finiteMeasure_def]
  show (levyProkhorovEDist (atomicMeasure s q'.1 q'.2) (atomicMeasure s q.1 q.2)).toReal ≤ _
  exact ENNReal.toReal_le_of_le_ofReal (Finset.sum_nonneg fun x _ => add_nonneg dist_nonneg (abs_nonneg _))
    (levyProkhorovEDist_atomicMeasure_le s q'.1 q.1 q'.2 q.2)

/-- For any Borel σ-algebra on the Lévy-Prokhorov space of finite measures on `ℂ`, a finite atomic measure with
measurable weights and atoms (countably many indices) is measurable. -/
theorem measurable_levyProkhorov_atomicFiniteMeasure [Countable ι]
    [MeasurableSpace (LevyProkhorov (FiniteMeasure ℂ))] [BorelSpace (LevyProkhorov (FiniteMeasure ℂ))]
    {α : Type*} [MeasurableSpace α] (s : Finset ι) {c : α → ι → ℝ} {p : α → ι → ℂ} (hc : Measurable c)
    (hp : Measurable p) : Measurable fun a => LevyProkhorov.ofMeasure (atomicFiniteMeasure s (c a) (p a)) :=
  (continuous_levyProkhorov_atomicFiniteMeasure s).measurable.comp (hc.prodMk hp)

end Atomic

/-! ### Measurability of the cutoff degree measure -/

section Measurable

variable {Ω : Type} [MeasurableSpace Ω]

/-- If only finitely many vertices lie in `supp ψ`, the cutoff degree measure is its truncation to any finite set of
vertices containing them. -/
theorem degreeCutoffMeasure_eq_atomicFiniteMeasure_of_subset {m : ℤ → ℤ → ℕ} {ε : ℝ} {v : ℤ → ℂ}
    {ψ : ℂ → ℝ} (h : (v ⁻¹' tsupport ψ).Finite) {t : Finset ℤ} (ht : vertexWindow v (tsupport ψ) ⊆ t) :
    degreeCutoffMeasure m ε v ψ = atomicFiniteMeasure t (degreeCutoffWeight m ε v ψ) v := by
  rw [degreeCutoffMeasure_eq_atomicFiniteMeasure]
  refine atomicFiniteMeasure_eq_of_subset ht v fun x _ hx => ?_
  rw [mem_vertexWindow h] at hx
  simp [degreeCutoffWeight, image_eq_zero_of_notMem_tsupport hx]

/-- **The cutoff degree measure is measurable in the Lévy-Prokhorov metric, for every valid environment.** Let `S`
be a valid environment, `η'` a version of its curve, `ψ` measurable with compact support and `ε > 0`. For any Borel
σ-algebra on the Lévy-Prokhorov space of finite measures on `ℂ`, the map
`ω ↦ ν^ε(ω) = Σ_x ε deg^ε(x) ψ(η'(εx)) δ_{η'(εx)}` is almost everywhere measurable. -/
theorem aemeasurable_levyProkhorov_degreeCutoffMeasure
    [MeasurableSpace (LevyProkhorov (FiniteMeasure ℂ))] [BorelSpace (LevyProkhorov (FiniteMeasure ℂ))]
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    {η' : Ω → C(ℝ, ℂ)} (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω)
    {ψ : ℂ → ℝ} (hψ : Measurable ψ) (hψc : HasCompactSupport ψ) {ε : ℝ} (hε : 0 < ε) :
    AEMeasurable (fun ω => LevyProkhorov.ofMeasure
      (degreeCutoffMeasure (S.mult ε ω) ε (vertexPoint ε (⇑(η' ω))) ψ)) S.P := by
  obtain ⟨_, _, _, _, _, _, _, _, _, η'', _, hC, htie⟩ := hS.matingOfTrees
  have hm : Measurable η'' := hC.measurable_curves.2.1
  have hEq : ∀ᵐ ω ∂S.P, η' ω = η'' ω := by
    filter_upwards [hae, htie] with ω h1 h2
    exact DFunLike.coe_injective (h1.trans h2.1.symm)
  have hv : Measurable fun ω => vertexPoint ε (⇑(η'' ω)) :=
    measurable_pi_iff.2 fun k =>
      ((continuous_eval_const (ε * (k : ℝ)) : Continuous fun f : C(ℝ, ℂ) => f (ε * (k : ℝ)))).measurable.comp hm
  have hc : Measurable fun ω => degreeCutoffWeight (S.mult ε ω) ε (vertexPoint ε (⇑(η'' ω))) ψ := by
    refine measurable_pi_iff.2 fun k => ?_
    have hdeg : Measurable fun ω => (mdeg (S.mult ε ω) k : ℝ) :=
      (measurable_from_nat (f := ((↑) : ℕ → ℝ))).comp (hS.measurable_mdeg ε k)
    show Measurable fun ω => ε * (mdeg (S.mult ε ω) k : ℝ) * ψ (vertexPoint ε (⇑(η'' ω)) k)
    exact (measurable_const.mul hdeg).mul (hψ.comp ((measurable_pi_apply k).comp hv))
  have hlim : ∀ᵐ ω ∂S.P, Tendsto (fun N : ℕ => LevyProkhorov.ofMeasure (atomicFiniteMeasure
      (Finset.Icc (-(N : ℤ)) N) (degreeCutoffWeight (S.mult ε ω) ε (vertexPoint ε (⇑(η'' ω))) ψ)
      (vertexPoint ε (⇑(η'' ω))))) atTop
      (𝓝 (LevyProkhorov.ofMeasure (degreeCutoffMeasure (S.mult ε ω) ε (vertexPoint ε (⇑(η'' ω))) ψ))) := by
    filter_upwards [hS.ae_tendsto_cocompact, htie] with ω hprop h2
    rw [← h2.1] at hprop
    have hfin := vertexPoint_preimage_finite hε (η'' ω).continuous hprop hψc.isCompact
    refine tendsto_atTop_of_eventually_const (i₀ := (vertexWindow (vertexPoint ε (⇑(η'' ω)))
      (tsupport ψ)).sup Int.natAbs) fun N hN => ?_
    rw [degreeCutoffMeasure_eq_atomicFiniteMeasure_of_subset hfin (t := Finset.Icc (-(N : ℤ)) N)]
    intro k hk
    have h1 : |k| ≤ (N : ℤ) := by
      rw [Int.abs_eq_natAbs]
      exact_mod_cast (Finset.le_sup (f := Int.natAbs) hk).trans hN
    exact Finset.mem_Icc.2 (abs_le.1 h1)
  have hg : AEMeasurable (fun ω => LevyProkhorov.ofMeasure
      (degreeCutoffMeasure (S.mult ε ω) ε (vertexPoint ε (⇑(η'' ω))) ψ)) S.P :=
    aemeasurable_of_tendsto_metrizable_ae atTop
      (fun N : ℕ =>
        (measurable_levyProkhorov_atomicFiniteMeasure (Finset.Icc (-(N : ℤ)) N) hc hv).aemeasurable) hlim
  refine hg.congr ?_
  filter_upwards [hEq] with ω h
  rw [h]

/-- **The hypothesis `hμ` of the projection lemma for the cutoff degree measure**: along `ε_n > 0`, every
`ω ↦ ν^{ε_n}(ω)` is almost everywhere measurable in the Lévy-Prokhorov metric (the binder `hμ` of
`tendsto_integral_levyProkhorov_projection_of_tendstoInMeasure_levyProkhorovDist`, Lattice-Probability). -/
theorem hμ_degreeCutoffMeasure_of_isValid
    [MeasurableSpace (LevyProkhorov (FiniteMeasure ℂ))] [BorelSpace (LevyProkhorov (FiniteMeasure ℂ))]
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    {η' : Ω → C(ℝ, ℂ)} (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω)
    {ψ : ℂ → ℝ} (hψ : Measurable ψ) (hψc : HasCompactSupport ψ) {ε : ℕ → ℝ} (hε0 : ∀ n, 0 < ε n) :
    ∀ n, AEMeasurable (fun ω => LevyProkhorov.ofMeasure
      (degreeCutoffMeasure (S.mult (ε n) ω) (ε n) (vertexPoint (ε n) (⇑(η' ω))) ψ)) S.P :=
  fun n => aemeasurable_levyProkhorov_degreeCutoffMeasure hS hae hψ hψc (hε0 n)

end Measurable

end MatedCRT.FirstPass.Derived
