import MatedCRT.FirstPass.S6r.OneTest.SrwStrongMarkov

/-!
# Strong Markov property with an `𝓕_T`-measurable parameter (parametric test)

The test ball `D₀ = B_{c₀R}(x)` and the exit time `σ_D` of its discrete interior depend on the radius
`R` and the centre `x`, which are chosen at the shell hit. The post-`T` occupation count is then
`∑_{n < σ_{ρ}} 1{X_{T+n} ∉ A}` with a parameter `ρ` that is `𝓕_T`-measurable (not a function of the post-`T` path).

This file proves `StrongMarkovAtParam`: the strong Markov property at `T` for functionals `G (ρ ω) (post-T path)`.
Route as in `SrwStrongMarkov`: the fixed-time identity is proved on rectangles `C₁ × C₂` of `P × path` (the two
measures `map (ρ, θ_k)` and `bind (x ↦ (ρ, P^{x_k}))` agree there by the set form `srwLaw_markov_state` applied
to `S ∩ ρ⁻¹C₁`), then extended by `ext_of_generate_finite`. Parameter space `P` is any measurable space.
-/

open MeasureTheory Set Filter Function
open scoped ENNReal

namespace MatedCRT
namespace Lemma68Window

open Lemma68WalkBridge

variable {P : Type*} [MeasurableSpace P]

/-- For `B ∈ 𝓕_T`, the slice `B ∩ {T = k}` lies in `𝓕_k`. -/
theorem measurableSet_coordFiltration_inter_eq {T : (ℕ → ℤ) → ℕ∞} (hT : IsStoppingTime coordFiltration T)
    {B : Set (ℕ → ℤ)} (hB : MeasurableSet[hT.measurableSpace] B) (k : ℕ) :
    MeasurableSet[coordFiltration k] (B ∩ {w | T w = (k : ℕ∞)}) := by
  have h1 : MeasurableSet[coordFiltration k] (B ∩ {w | T w ≤ (k : ℕ∞)}) := hB.2 k
  have h2 : MeasurableSet[coordFiltration k] {w | T w = (k : ℕ∞)} :=
    hT.measurableSet_eq_of_countable k
  have heq : B ∩ {w | T w = (k : ℕ∞)} = (B ∩ {w | T w ≤ (k : ℕ∞)}) ∩ {w | T w = (k : ℕ∞)} := by
    ext w
    simp only [mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨hw, he⟩
      exact ⟨⟨hw, he.le⟩, he⟩
    · rintro ⟨⟨hw, _⟩, he⟩
      exact ⟨hw, he⟩
  rw [heq]
  exact h1.inter h2

/-- The fixed-time Markov identity on a rectangle `C₁ × C₂`, the set step of `lintegral_shift_fixed_param`. -/
theorem measure_rect_fixed (m : ℤ → ℤ → ℕ) (a : ℤ) {ρ : (ℕ → ℤ) → P}
    {k : ℕ} {S : Set (ℕ → ℤ)} (hρS : ∀ C : Set P, MeasurableSet C → MeasurableSet[coordFiltration k] (S ∩ ρ ⁻¹' C))
    {C1 : Set P} {C2 : Set (ℕ → ℤ)} (hC1 : MeasurableSet C1) (hC2 : MeasurableSet C2) :
    srwLaw m a ((fun w => (ρ w, WalkPotential.pathShift k w)) ⁻¹' (C1 ×ˢ C2) ∩ S)
      = ∫⁻ w in ρ ⁻¹' C1 ∩ S, srwLaw m (w k) C2 ∂srwLaw m a := by
  obtain ⟨F, hF, hpre⟩ := exists_preimage_pathHist (hρS C1 hC1)
  have hM := srwLaw_markov_state m a k (fun _ => C2) (fun _ => hC2) hF
  have hset : (fun w => (ρ w, WalkPotential.pathShift k w)) ⁻¹' (C1 ×ˢ C2) ∩ S
      = MatedCRT.pathHist k ⁻¹' F ∩ WalkPotential.pathShift k ⁻¹' C2 := by
    rw [hpre]
    ext x
    simp only [mem_inter_iff, mem_preimage, mem_prod]
    tauto
  have hset2 : ρ ⁻¹' C1 ∩ S = MatedCRT.pathHist k ⁻¹' F := by
    rw [hpre, Set.inter_comm]
  rw [hset, hset2]
  exact hM

/-- **Fixed-time Markov property with a parameter**, lower-integral form:
`E[H(ρ, θ_k) ; S] = E[ ∫ H(ρ, x) P^{X_k}(dx) ; S]` for `S ∈ 𝓕_k` with `ρ` splitting `S` into `𝓕_k`-sets. -/
theorem lintegral_shift_fixed_param (m : ℤ → ℤ → ℕ) (a : ℤ) {ρ : (ℕ → ℤ) → P} (hρ : Measurable ρ)
    {k : ℕ} {S : Set (ℕ → ℤ)}
    (hρS : ∀ C : Set P, MeasurableSet C → MeasurableSet[coordFiltration k] (S ∩ ρ ⁻¹' C))
    {H : P × (ℕ → ℤ) → ℝ≥0∞} (hH : Measurable H) :
    ∫⁻ w in S, H (ρ w, WalkPotential.pathShift k w) ∂srwLaw m a
      = ∫⁻ w in S, (∫⁻ x, H (ρ w, x) ∂srwLaw m (w k)) ∂srwLaw m a := by
  have hθ : Measurable (WalkPotential.pathShift k) := MatedCRT.walk_measurable_pathShift k
  have hΦ : Measurable (fun w : ℕ → ℤ => (ρ w, WalkPotential.pathShift k w)) := hρ.prodMk hθ
  have hF : ∀ E : Set (P × (ℕ → ℤ)), MeasurableSet E →
      Measurable (fun q : P × ℤ => srwLaw m q.2 (Prod.mk q.1 ⁻¹' E)) := by
    intro E hE
    refine measurable_from_prod_countable_left fun b => ?_
    exact measurable_measure_prodMk_left (ν := srwLaw m b) hE
  have hQ : Measurable (fun (w : ℕ → ℤ) => (srwLaw m (w k)).map (fun x => (ρ w, x))) := by
    refine Measure.measurable_of_measurable_coe _ fun E hE => ?_
    have hc : Measurable ((fun q : P × ℤ => srwLaw m q.2 (Prod.mk q.1 ⁻¹' E)) ∘ (fun w : ℕ → ℤ => (ρ w, w k))) :=
      (hF E hE).comp (hρ.prodMk (measurable_pi_apply k))
    have heq : (fun w : ℕ → ℤ => (srwLaw m (w k)).map (fun x => (ρ w, x)) E)
        = fun w => srwLaw m (w k) (Prod.mk (ρ w) ⁻¹' E) :=
      funext fun w => Measure.map_apply measurable_prodMk_left hE
    rw [heq]
    exact hc
  have hrect : ∀ C1 : Set P, ∀ C2 : Set (ℕ → ℤ), MeasurableSet C1 → MeasurableSet C2 →
      ((srwLaw m a).restrict S).map (fun w => (ρ w, WalkPotential.pathShift k w)) (C1 ×ˢ C2)
        = (((srwLaw m a).restrict S).bind (fun w => (srwLaw m (w k)).map (fun x => (ρ w, x))))
            (C1 ×ˢ C2) := by
    intro C1 C2 hC1 hC2
    have hC12 : MeasurableSet (C1 ×ˢ C2) := hC1.prod hC2
    rw [Measure.map_apply hΦ hC12, Measure.bind_apply hC12 hQ.aemeasurable,
      Measure.restrict_apply (hΦ hC12)]
    have hinner : ∀ w : ℕ → ℤ, (srwLaw m (w k)).map (fun x => (ρ w, x)) (C1 ×ˢ C2)
        = (ρ ⁻¹' C1).indicator (fun w => srwLaw m (w k) C2) w := by
      intro w
      by_cases h : ρ w ∈ C1
      · have hpre : (fun x => (ρ w, x)) ⁻¹' (C1 ×ˢ C2) = C2 := by
          ext x; simp [h]
        rw [Measure.map_apply measurable_prodMk_left hC12, hpre,
          Set.indicator_of_mem (show w ∈ ρ ⁻¹' C1 from h)]
      · have hpre : (fun x => (ρ w, x)) ⁻¹' (C1 ×ˢ C2) = ∅ := by
          ext x; simp [h]
        rw [Measure.map_apply measurable_prodMk_left hC12, hpre,
          Set.indicator_of_notMem (show w ∉ ρ ⁻¹' C1 from h)]
        simp
    rw [lintegral_congr hinner, lintegral_indicator (hρ hC1), Measure.restrict_restrict (hρ hC1)]
    exact measure_rect_fixed m a hρS hC1 hC2
  have hmeas : ((srwLaw m a).restrict S).map (fun w => (ρ w, WalkPotential.pathShift k w))
      = ((srwLaw m a).restrict S).bind (fun w => (srwLaw m (w k)).map (fun x => (ρ w, x))) := by
    refine ext_of_generate_finite _ generateFrom_prod.symm isPiSystem_prod ?_ ?_
    · rintro _ ⟨C1, hC1, C2, hC2, rfl⟩
      exact hrect C1 C2 hC1 hC2
    · have h := hrect Set.univ Set.univ MeasurableSet.univ MeasurableSet.univ
      rwa [Set.univ_prod_univ] at h
  calc ∫⁻ w in S, H (ρ w, WalkPotential.pathShift k w) ∂srwLaw m a
      = ∫⁻ z, H z ∂(((srwLaw m a).restrict S).map (fun w => (ρ w, WalkPotential.pathShift k w))) :=
        (lintegral_map hH hΦ).symm
    _ = ∫⁻ z, H z ∂(((srwLaw m a).restrict S).bind
          (fun w => (srwLaw m (w k)).map (fun x => (ρ w, x)))) := by rw [hmeas]
    _ = ∫⁻ w, (∫⁻ z, H z ∂(srwLaw m (w k)).map (fun x => (ρ w, x))) ∂((srwLaw m a).restrict S) :=
        Measure.lintegral_bind hQ.aemeasurable hH.aemeasurable
    _ = ∫⁻ w in S, (∫⁻ x, H (ρ w, x) ∂srwLaw m (w k)) ∂srwLaw m a :=
        lintegral_congr fun w => lintegral_map hH measurable_prodMk_left

/-- Measurability in the parameter of the lower integral `(p, b) ↦ ∫ H(p, x) P^b(dx)`. -/
theorem measurable_lintegral_param (m : ℤ → ℤ → ℕ) {H : P × (ℕ → ℤ) → ℝ≥0∞} (hH : Measurable H) :
    Measurable (fun q : P × ℤ => ∫⁻ x, H (q.1, x) ∂srwLaw m q.2) := by
  refine measurable_from_prod_countable_left fun b => ?_
  exact hH.lintegral_prod_right' (ν := srwLaw m b)

/-- The decomposition over the value of `T`, with the parameter `ρ` (cf. `lintegral_postTime`). -/
theorem lintegral_postTime_param (m : ℤ → ℤ → ℕ) (a : ℤ) {T : (ℕ → ℤ) → ℕ∞}
    (hT : IsStoppingTime coordFiltration T) {ρ : (ℕ → ℤ) → P}
    (hρ : Measurable[hT.measurableSpace] ρ) {H : P × (ℕ → ℤ) → ℝ≥0∞} (hH : Measurable H)
    {B : Set (ℕ → ℤ)} (hB : MeasurableSet[hT.measurableSpace] B) :
    ∫⁻ w in B, {w | T w < ⊤}.indicator (fun w => H (ρ w, postTimePath (fun n w => w n) T w)) w ∂srwLaw m a
      = ∫⁻ w in B, {w | T w < ⊤}.indicator
          (fun w => ∫⁻ x, H (ρ w, x) ∂srwLaw m (w (T w).toNat)) w ∂srwLaw m a := by
  have hρm : Measurable ρ := hρ.mono hT.measurableSpace_le le_rfl
  have hBlt : MeasurableSet {w | T w < ⊤} := by
    rw [setOf_lt_top_eq_iUnion T]
    exact MeasurableSet.iUnion fun k => coordFiltration.le k _ (hT.measurableSet_le k)
  have hBk_m : ∀ k : ℕ, MeasurableSet (B ∩ {w | T w = (k : ℕ∞)}) := fun k =>
    coordFiltration.le k _ (measurableSet_coordFiltration_inter_eq hT hB k)
  have hsplit : ∀ g : (ℕ → ℤ) → ℝ≥0∞, ∫⁻ w in B, {w | T w < ⊤}.indicator g w ∂srwLaw m a
      = ∑' k : ℕ, ∫⁻ w in B ∩ {w | T w = (k : ℕ∞)}, g w ∂srwLaw m a := by
    intro g
    have hset : {w | T w < ⊤} ∩ B = ⋃ k : ℕ, B ∩ {w | T w = (k : ℕ∞)} := by
      ext w
      simp only [mem_inter_iff, mem_ofPred_eq, mem_iUnion]
      constructor
      · rintro ⟨hlt, hw⟩
        obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 hlt.ne
        exact ⟨k, hw, hk.symm⟩
      · rintro ⟨k, hw, hk⟩
        exact ⟨by rw [hk]; exact ENat.natCast_lt_top k, hw⟩
    have hdisj : Pairwise (Disjoint on fun k : ℕ => B ∩ {w | T w = (k : ℕ∞)}) := by
      intro k k' hkk'
      refine Set.disjoint_left.2 fun w hw hw' => hkk' ?_
      have h1 : T w = (k : ℕ∞) := hw.2
      have h2 : T w = (k' : ℕ∞) := hw'.2
      exact_mod_cast h1.symm.trans h2
    rw [lintegral_indicator hBlt, Measure.restrict_restrict hBlt, hset,
      lintegral_iUnion hBk_m hdisj]
  rw [hsplit, hsplit]
  refine tsum_congr fun k => ?_
  have hk : ∀ w, T w = (k : ℕ∞) → (T w).toNat = k := fun w h => by rw [h]; simp
  have hpost : ∀ w, T w = (k : ℕ∞) →
      postTimePath (fun n w => w n) T w = WalkPotential.pathShift k w := fun w h => by
    funext n
    simp only [postTimePath, WalkPotential.pathShift, hk w h]
  have hρS : ∀ C : Set P, MeasurableSet C →
      MeasurableSet[coordFiltration k] (B ∩ {w | T w = (k : ℕ∞)} ∩ ρ ⁻¹' C) := by
    intro C hC
    have h := measurableSet_coordFiltration_inter_eq hT (hB.inter (hρ hC)) k
    have heq : B ∩ {w | T w = (k : ℕ∞)} ∩ ρ ⁻¹' C = (B ∩ ρ ⁻¹' C) ∩ {w | T w = (k : ℕ∞)} := by
      ext w
      simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq]
      tauto
    rw [heq]
    exact h
  calc ∫⁻ w in B ∩ {w | T w = (k : ℕ∞)}, H (ρ w, postTimePath (fun n w => w n) T w) ∂srwLaw m a
      = ∫⁻ w in B ∩ {w | T w = (k : ℕ∞)}, H (ρ w, WalkPotential.pathShift k w) ∂srwLaw m a :=
        setLIntegral_congr_fun (hBk_m k) fun w hw => by rw [hpost w hw.2]
    _ = ∫⁻ w in B ∩ {w | T w = (k : ℕ∞)}, (∫⁻ x, H (ρ w, x) ∂srwLaw m (w k)) ∂srwLaw m a :=
        lintegral_shift_fixed_param m a hρm hρS hH
    _ = ∫⁻ w in B ∩ {w | T w = (k : ℕ∞)}, ∫⁻ x, H (ρ w, x) ∂srwLaw m (w (T w).toNat) ∂srwLaw m a :=
        setLIntegral_congr_fun (hBk_m k) fun w hw => by rw [hk w hw.2]

/-- The candidate `w ↦ 1_{T<∞} g(ρ w, X_T w)` is `𝓕_T`-measurable (`X_T` the stopped coordinate). -/
theorem measurable_stopped_indicator_param {T : (ℕ → ℤ) → ℕ∞} (hT : IsStoppingTime coordFiltration T)
    {ρ : (ℕ → ℤ) → P} (hρ : Measurable[hT.measurableSpace] ρ)
    {β : Type*} [MeasurableSpace β] [Zero β] (g : P × ℤ → β) (hg : Measurable g) :
    Measurable[hT.measurableSpace]
      (fun w => {w | T w < ⊤}.indicator (fun w => g (ρ w, w (T w).toNat)) w) := by
  have hprog : IsStronglyProgressive coordFiltration (fun (n : ℕ) (w : ℕ → ℤ) => w n) :=
    StronglyAdapted.isStronglyProgressive_of_discrete fun n => (coord_measurable n).stronglyMeasurable
  have hst : Measurable[hT.measurableSpace] (stoppedValue (fun (n : ℕ) (w : ℕ → ℤ) => w n) T) :=
    measurable_stoppedValue hprog hT
  have hlt : MeasurableSet[hT.measurableSpace] {w | T w < ⊤} := by
    rw [setOf_lt_top_eq_iUnion T]
    exact MeasurableSet.iUnion fun k => hT.measurableSet_le' k
  have hfun : (fun w => {w | T w < ⊤}.indicator (fun w => g (ρ w, w (T w).toNat)) w)
      = {w | T w < ⊤}.indicator
          (fun w => g (ρ w, stoppedValue (fun (n : ℕ) (w : ℕ → ℤ) => w n) T w)) := by
    funext w
    by_cases h : T w < ⊤
    · obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 h.ne
      simp [Set.indicator, stoppedValue, ← hk]
    · simp [Set.indicator, h]
  rw [hfun]
  exact (hg.comp (hρ.prodMk hst)).indicator hlt

/-- **Strong Markov property at `T` with an `𝓕_T`-measurable parameter** (parametric test):
on `{T < ∞}`, `E[G(ρ, θ_T) | 𝓕_T] = E_{X_T}[G(ρ, ·)]` for the simple random walk `P^a = srwLaw m a`. -/
def StrongMarkovAtParam (m : ℤ → ℤ → ℕ) (a : ℤ) {T : (ℕ → ℤ) → ℕ∞} (hT : IsStoppingTime coordFiltration T)
    (ρ : (ℕ → ℤ) → P) (G : P → (ℕ → ℤ) → ℝ) : Prop :=
  ∀ᵐ ω ∂srwLaw m a,
    (srwLaw m a)[{ω' | T ω' < ⊤}.indicator (fun ω' => G (ρ ω') (postTimePath (fun n w => w n) T ω'))
      | hT.measurableSpace] ω
    = {ω' | T ω' < ⊤}.indicator (fun ω' => ∫ x, G (ρ ω') x ∂srwLaw m (ω' (T ω').toNat)) ω

/-- The strong Markov property with the parameter `ρ`, for measurable nonnegative `G`; the integrability `hint` of the
post-`T` functional is a named hypothesis. -/
theorem strongMarkovAt_param (m : ℤ → ℤ → ℕ) (a : ℤ) {T : (ℕ → ℤ) → ℕ∞}
    (hT : IsStoppingTime coordFiltration T) {ρ : (ℕ → ℤ) → P} (hρ : Measurable[hT.measurableSpace] ρ)
    {G : P → (ℕ → ℤ) → ℝ} (hG : Measurable (fun q : P × (ℕ → ℤ) => G q.1 q.2)) (hG0 : ∀ p w, 0 ≤ G p w)
    (hint : Integrable
      ({w | T w < ⊤}.indicator (fun w => G (ρ w) (postTimePath (fun n w => w n) T w))) (srwLaw m a)) :
    StrongMarkovAtParam m a hT ρ G := by
  unfold StrongMarkovAtParam
  have hρm : Measurable ρ := hρ.mono hT.measurableSpace_le le_rfl
  have hH : Measurable (fun q : P × (ℕ → ℤ) => ENNReal.ofReal (G q.1 q.2)) :=
    ENNReal.measurable_ofReal.comp hG
  let gE : P × ℤ → ℝ≥0∞ := fun q => ∫⁻ x, ENNReal.ofReal (G q.1 x) ∂srwLaw m q.2
  let φ : (ℕ → ℤ) → ℝ≥0∞ := fun w => {w | T w < ⊤}.indicator (fun w => gE (ρ w, w (T w).toNat)) w
  have hgEm : Measurable gE := measurable_lintegral_param m hH
  have hφm : Measurable[hT.measurableSpace] φ := measurable_stopped_indicator_param hT hρ gE hgEm
  have hφm' : Measurable φ := hφm.mono hT.measurableSpace_le le_rfl
  have hnn : ∀ w, 0 ≤ {w | T w < ⊤}.indicator (fun w => G (ρ w) (postTimePath (fun n w => w n) T w)) w :=
    fun w => Set.indicator_nonneg (fun w _ => hG0 _ _) w
  have hkey : ∀ B, MeasurableSet[hT.measurableSpace] B →
      ∫⁻ w in B, ENNReal.ofReal
          ({w | T w < ⊤}.indicator (fun w => G (ρ w) (postTimePath (fun n w => w n) T w)) w) ∂srwLaw m a
        = ∫⁻ w in B, φ w ∂srwLaw m a := by
    intro B hB
    have h1 := lintegral_postTime_param m a hT hρ hH hB
    have hind : ∀ w, ENNReal.ofReal
        ({w | T w < ⊤}.indicator (fun w => G (ρ w) (postTimePath (fun n w => w n) T w)) w)
        = {w | T w < ⊤}.indicator
            (fun w => ENNReal.ofReal (G (ρ w) (postTimePath (fun n w => w n) T w))) w := by
      intro w
      by_cases h : w ∈ {w | T w < ⊤} <;> simp [h]
    simp only [hind]
    exact h1
  have hGp : ∀ p, Measurable (G p) := fun p => hG.comp (measurable_prodMk_left (x := p))
  have hgR : ∀ p b, ∫ x, G p x ∂srwLaw m b = (gE (p, b)).toReal := fun p b =>
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (hG0 p)) (hGp p).aestronglyMeasurable
  have hfinint : ∫⁻ w, φ w ∂srwLaw m a ≠ ⊤ := by
    have h := hkey Set.univ (@MeasurableSet.univ _ hT.measurableSpace)
    rw [Measure.restrict_univ] at h
    rw [← h]
    refine ne_top_of_lt (lt_of_eq_of_lt (lintegral_congr fun w => ?_) hint.2)
    exact (Real.enorm_eq_ofReal (hnn w)).symm
  have hφae : ∀ᵐ w ∂srwLaw m a, φ w < ⊤ := ae_lt_top' hφm'.aemeasurable hfinint
  have hcR : (fun w => (φ w).toReal) = fun w =>
      {w | T w < ⊤}.indicator (fun ω' => ∫ x, G (ρ ω') x ∂srwLaw m (ω' (T ω').toNat)) w := by
    funext w
    by_cases h : T w < ⊤
    · simp [Set.indicator, h, φ, hgR]
    · simp [Set.indicator, h, φ]
  have hg_int : ∀ s, MeasurableSet[hT.measurableSpace] s → srwLaw m a s < ⊤ →
      IntegrableOn (fun w => (φ w).toReal) s (srwLaw m a) := by
    intro s _ _
    exact integrable_toReal_of_lintegral_ne_top hφm'.aemeasurable
      (ne_top_of_le_ne_top hfinint (setLIntegral_le_lintegral s φ))
  have hg_eq : ∀ s, MeasurableSet[hT.measurableSpace] s → srwLaw m a s < ⊤ →
      ∫ w in s, (φ w).toReal ∂srwLaw m a
        = ∫ w in s, {w | T w < ⊤}.indicator (fun w => G (ρ w) (postTimePath (fun n w => w n) T w)) w
            ∂srwLaw m a := by
    intro s hs _
    rw [integral_toReal hφm'.aemeasurable (ae_restrict_of_ae hφae),
      integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hnn)
        hint.aestronglyMeasurable.restrict, hkey s hs]
  have hgm : AEStronglyMeasurable[hT.measurableSpace] (fun w => (φ w).toReal) (srwLaw m a) :=
    ((ENNReal.measurable_toReal.comp hφm).stronglyMeasurable).aestronglyMeasurable
  have hae := ae_eq_condExp_of_forall_setIntegral_eq hT.measurableSpace_le hint hg_int hg_eq hgm
  filter_upwards [hae] with w hw
  exact hw.symm.trans (congrFun hcR w)

/-- Measurability of the parametric occupation count `(p, w) ↦ ∑_{n < σ_p(w)} 1{w_n ∉ A}`. -/
theorem measurable_occCount_param (A : Set ℤ) {σ : P → (ℕ → ℤ) → ℕ}
    (hσ : Measurable (fun q : P × (ℕ → ℤ) => σ q.1 q.2)) :
    Measurable (fun q : P × (ℕ → ℤ) => occCount A (σ q.1) q.2) := by
  have hF : Measurable (fun p : ℕ × (P × (ℕ → ℤ)) =>
      ∑ n ∈ Finset.range p.1, Aᶜ.indicator (fun _ => (1 : ℝ)) (p.2.2 n)) := by
    refine measurable_from_prod_countable_right fun k => ?_
    exact Finset.measurable_sum (Finset.range k) fun n _ =>
      (Measurable.of_discrete (f := Aᶜ.indicator (fun _ : ℤ => (1 : ℝ)))).comp
        ((measurable_pi_apply n).comp measurable_snd)
  exact hF.comp (hσ.prodMk measurable_id)

/-- **Strong Markov property at `T` for the parametric occupation count `V = ∑_{n<σ_ρ} 1{X_{T+n} ∉ A}`.** -/
theorem strongMarkovAt_occCount_param (m : ℤ → ℤ → ℕ) (a : ℤ) (A : Set ℤ) {σ : P → (ℕ → ℤ) → ℕ}
    (hσ : Measurable (fun q : P × (ℕ → ℤ) => σ q.1 q.2)) {T : (ℕ → ℤ) → ℕ∞}
    (hT : IsStoppingTime coordFiltration T) {ρ : (ℕ → ℤ) → P} (hρ : Measurable[hT.measurableSpace] ρ)
    (hint : Integrable ({w | T w < ⊤}.indicator
      (fun w => occCount A (σ (ρ w)) (postTimePath (fun n w => w n) T w))) (srwLaw m a)) :
    StrongMarkovAtParam m a hT ρ (fun p => occCount A (σ p)) :=
  strongMarkovAt_param m a hT hρ (measurable_occCount_param A hσ)
    (fun p w => occCount_nonneg A (σ p) w) hint

/-- **Strong Markov property at `T` for the square of the parametric occupation count** (second moment). -/
theorem strongMarkovAt_occCount_sq_param (m : ℤ → ℤ → ℕ) (a : ℤ) (A : Set ℤ) {σ : P → (ℕ → ℤ) → ℕ}
    (hσ : Measurable (fun q : P × (ℕ → ℤ) => σ q.1 q.2)) {T : (ℕ → ℤ) → ℕ∞}
    (hT : IsStoppingTime coordFiltration T) {ρ : (ℕ → ℤ) → P} (hρ : Measurable[hT.measurableSpace] ρ)
    (hint : Integrable ({w | T w < ⊤}.indicator
      (fun w => occCount A (σ (ρ w)) (postTimePath (fun n w => w n) T w) ^ 2)) (srwLaw m a)) :
    StrongMarkovAtParam m a hT ρ (fun p w => occCount A (σ p) w ^ 2) :=
  strongMarkovAt_param m a hT hρ ((measurable_occCount_param A hσ).pow_const 2)
    (fun _ _ => sq_nonneg _) hint

end Lemma68Window
end MatedCRT
