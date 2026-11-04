import MatedCRT.Proofs.Sec4.ConvergenceDivisible.CellMeasurable
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.MatedLeastMeasurable

/-! # Local stability of the selected cell -/

namespace MatedCRT

open Set Metric Filter Topology MeasureTheory

/-- On a bounded open set, the least-index cell is locally stable when points
are restricted to the selected cell. -/
theorem vertexOf_locally_eq_on_cell {ε : ℝ} {η : ℝ → ℂ}
    (hη : Continuous η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    (hε : 0 < ε) {D : Set ℂ} (hD : IsOpen D) (hb : Bornology.IsBounded D)
    {x : ℂ} {k : ℤ} (hx : x ∈ D)
    (hleast : ∀ j < k, x ∉ cell ε η j) :
    ∃ U : Set ℂ, IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U, y ∈ cell ε η k → vertexOf ε η y = k := by
  let A : Set ℤ := {j | j ∈ cellVertices ε η D ∧ j < k}
  have hA : A.Finite := (Tightness.cellVertices_finite hη hp hε hb).subset (fun _ hj => hj.1)
  let F : Set ℂ := ⋃ j ∈ A, cell ε η j
  have hF : IsClosed F := hA.isClosed_biUnion fun j _ => (isCompact_Icc.image hη).isClosed
  have hxF : x ∉ F := by
    simp only [F, mem_iUnion, not_exists]
    intro j hj
    exact hleast j hj.2
  refine ⟨D ∩ Fᶜ, hD.inter hF.isOpen_compl, ⟨hx, hxF⟩, ?_⟩
  intro y hy hyk
  have hfin : {j : ℤ | y ∈ cell ε η j}.Finite :=
    (Tightness.cellVertices_finite hη hp hε hb).subset fun j hj => ⟨y, hj, hy.1⟩
  have hlow : ∀ j < k, y ∉ cell ε η j := by
    intro j hj hyj
    apply hy.2
    exact mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨⟨⟨y, hyj, hy.1⟩, hj⟩, hyj⟩⟩
  apply le_antisymm
  · exact csInf_le hfin.bddBelow hyk
  · apply le_csInf ⟨k, hyk⟩
    intro j hj
    exact le_of_not_gt (fun h => hlow j h hj)

/-- Rational time, clipped to the time interval of a cell. -/
def cellSample (ε : ℝ) (η : ℝ → ℂ) (k : ℤ) (q : ℚ) : ℂ :=
  η (max (ε * (k - 1)) (min (q : ℝ) (ε * k)))

theorem cellSample_mem {ε : ℝ} {η : ℝ → ℂ} (hε : 0 < ε) (k : ℤ) (q : ℚ) :
    cellSample ε η k q ∈ cell ε η k := by
  have hab : ε * ((k : ℝ) - 1) ≤ ε * k := by nlinarith
  refine ⟨_, ⟨le_max_left _ _, max_le hab (min_le_right _ _)⟩, rfl⟩

/-- Rational clipped times give a dense family in each cell. -/
theorem cell_subset_closure_samples {ε : ℝ} {η : ℝ → ℂ}
    (hη : Continuous η) (k : ℤ) :
    cell ε η k ⊆ closure (range (cellSample ε η k)) := by
  let g : ℝ → ℂ := fun t => η (max (ε * (k - 1)) (min t (ε * k)))
  have hg : Continuous g := hη.comp (continuous_const.max (continuous_id.min continuous_const))
  have hd : closure (range ((↑) : ℚ → ℝ)) = univ := Rat.denseRange_cast.closure_range
  intro x hx
  obtain ⟨t, ht, rfl⟩ := hx
  have ht' : g t ∈ closure (g '' range ((↑) : ℚ → ℝ)) :=
    image_closure_subset_closure_image hg ⟨t, by rw [hd]; trivial, rfl⟩
  have heq : g t = η t := by simp [g, max_eq_right ht.1, min_eq_left ht.2]
  rw [heq] at ht'
  change η t ∈ closure (range (fun q : ℚ => η (max (ε * (k - 1)) (min (q : ℝ) (ε * k)))))
  simpa [g, ← range_comp'] using ht'

/-- A strict deviation from a continuous function can be detected on any
dense family of sample points in each cell. -/
theorem exists_deviation_iff_cell_samples {ε : ℝ} {η : ℝ → ℂ}
    (hη : Continuous η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    (hsurj : Function.Surjective η) (hε : 0 < ε)
    {D : Set ℂ} (hD : IsOpen D) (hb : Bornology.IsBounded D)
    {ι : Type} (s : ℤ → ι → ℂ) (hs : ∀ k i, s k i ∈ cell ε η k)
    (hdense : ∀ k, cell ε η k ⊆ closure (range (s k)))
    (u : ℤ → ℝ) {f : ℂ → ℝ} (hf : ContinuousOn f D) (δ : ℝ) :
    (∃ x ∈ D, δ < |u (vertexOf ε η x) - f x|) ↔
      ∃ k i, s k i ∈ D ∧ vertexOf ε η (s k i) = k ∧ δ < |u k - f (s k i)| := by
  constructor
  · rintro ⟨x, hx, hdev⟩
    let k := vertexOf ε η x
    have hxk : x ∈ cell ε η k := Tightness.mem_cell_vertexOf hη hp hsurj hε x
    have hfin : {j : ℤ | x ∈ cell ε η j}.Finite :=
      (Tightness.cellVertices_finite hη hp hε hb).subset fun j hj => ⟨x, hj, hx⟩
    have hleast : ∀ j < k, x ∉ cell ε η j := by
      intro j hj hjx
      exact (not_le_of_gt hj) (csInf_le hfin.bddBelow hjx)
    obtain ⟨U, hU, hxU, hstable⟩ := vertexOf_locally_eq_on_cell hη hp hε hD hb hx hleast
    let V : Set ℂ := D ∩ (fun y => |u k - f y|) ⁻¹' Ioi δ
    have hV : IsOpen V := ((continuousOn_const.sub hf).abs).isOpen_inter_preimage hD isOpen_Ioi
    have hxV : x ∈ V := ⟨hx, hdev⟩
    obtain ⟨y, hyUV, hyRange⟩ := mem_closure_iff.mp (hdense k hxk) (U ∩ V) (hU.inter hV) ⟨hxU, hxV⟩
    obtain ⟨i, rfl⟩ := hyRange
    exact ⟨k, i, hyUV.2.1, hstable _ hyUV.1 (hs k i), hyUV.2.2⟩
  · rintro ⟨k, i, hiD, hik, hidev⟩
    refine ⟨s k i, hiD, ?_⟩
    simpa [hik] using hidev

/-- For a jointly measurable continuum function that is almost surely
continuous on a bounded open domain, the strict deviation event is null
measurable whenever the vertex values are measurable. -/
theorem MatedCRTEnv.IsValid.nullMeasurableSet_exists_cell_deviation
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    {ε : ℝ} (hε : 0 < ε) {D : Set ℂ} (hD : IsOpen D)
    (hb : Bornology.IsBounded D) (u : Ω → ℤ → ℝ)
    (hu : ∀ k, Measurable fun ω => u ω k)
    (f : Ω × ℂ → ℝ) (hf : Measurable f)
    (hfc : ∀ᵐ ω ∂S.P, ContinuousOn (fun x => f (ω, x)) D) (δ : ℝ) :
    NullMeasurableSet {ω | ∃ x ∈ D, δ < |u ω (vertexOf ε (S.η ω) x) - f (ω, x)|} S.P := by
  classical
  obtain ⟨X, X₀, hIG₀, B, B', B₀, B₀', U, ηL, η', η₀, hc, hbridge⟩ := hS.matingOfTrees
  obtain ⟨V, hV, hVa⟩ := hS.exists_measurable_vertexOf hε
  let s : Ω → ℤ → ℚ → ℂ := fun ω k q => cellSample ε (η' ω) k q
  have hs : ∀ k q, Measurable fun ω => s ω k q := by
    intro k q
    exact (continuous_eval_const _).measurable.comp hc.measurable_curves.2.1
  let E : Set Ω := {ω | ∃ k q, s ω k q ∈ D ∧ V (ω, s ω k q) = k ∧
    δ < |u ω k - f (ω, s ω k q)|}
  have hE : MeasurableSet E := by
    have hq : ∀ k q, MeasurableSet {ω | s ω k q ∈ D ∧ V (ω, s ω k q) = k ∧
        δ < |u ω k - f (ω, s ω k q)|} := by
      intro k q
      have hp : Measurable (fun ω => (ω, s ω k q)) := measurable_id.prodMk (hs k q)
      exact (hD.measurableSet.preimage (hs k q)).inter
        ((measurableSet_eq_fun (hV.comp hp) measurable_const).inter
        (measurableSet_lt measurable_const (((hu k).sub (hf.comp hp)).abs)))
    convert MeasurableSet.iUnion (fun k : ℤ => MeasurableSet.iUnion (fun q : ℚ => hq k q)) using 1
    ext ω
    simp [E]
  apply hE.nullMeasurableSet.congr
  filter_upwards [hbridge, hVa, hS.ae_tendsto_cocompact, hS.isAreaParametrized, hfc] with ω hη hvertex hp harea hcont
  have heq := exists_deviation_iff_cell_samples harea.1 hp harea.2.2.1 hε hD hb
    (cellSample ε (S.η ω)) (cellSample_mem hε)
    (cell_subset_closure_samples harea.1) (u ω) hcont δ
  apply propext
  change (∃ k q, s ω k q ∈ D ∧ V (ω, s ω k q) = k ∧
    δ < |u ω k - f (ω, s ω k q)|) ↔ _
  simpa [s, hη.1, hvertex] using heq.symm

/-- The same conclusion holds on a measurable event on which continuity holds
almost surely; outside that event the continuum function is immaterial. -/
theorem MatedCRTEnv.IsValid.nullMeasurableSet_exists_cell_deviation_on_event
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    {ε : ℝ} (hε : 0 < ε) {D : Set ℂ} (hD : IsOpen D)
    (hb : Bornology.IsBounded D) (u : Ω → ℤ → ℝ)
    (hu : ∀ k, Measurable fun ω => u ω k)
    (f : Ω × ℂ → ℝ) (hf : Measurable f) (E : Set Ω) (hE : MeasurableSet E)
    (hfc : ∀ᵐ ω ∂S.P, ω ∈ E → ContinuousOn (fun x => f (ω, x)) D) (δ : ℝ) :
    NullMeasurableSet {ω | ω ∈ E ∧ ∃ x ∈ D,
      δ < |u ω (vertexOf ε (S.η ω) x) - f (ω, x)|} S.P := by
  classical
  let g : Ω × ℂ → ℝ := fun p => if p.1 ∈ E then f p else 0
  have hg : Measurable g := hf.ite (hE.preimage measurable_fst) measurable_const
  have hgc : ∀ᵐ ω ∂S.P, ContinuousOn (fun x => g (ω, x)) D := by
    filter_upwards [hfc] with ω hω
    by_cases h : ω ∈ E
    · simpa [g, h] using hω h
    · simpa [g, h] using (continuousOn_const : ContinuousOn (fun _ : ℂ => (0 : ℝ)) D)
  have h := hS.nullMeasurableSet_exists_cell_deviation hε hD hb u hu g hg hgc δ
  have heq : E ∩ {ω | ∃ x ∈ D, δ < |u ω (vertexOf ε (S.η ω) x) - g (ω, x)|} =
      {ω | ω ∈ E ∧ ∃ x ∈ D, δ < |u ω (vertexOf ε (S.η ω) x) - f (ω, x)|} := by
    ext ω
    by_cases hω : ω ∈ E <;> simp [g, hω]
  rw [← heq]
  exact hE.nullMeasurableSet.inter h

/-- Spatial deviation from the actual rescaled mated least supersolution is
null measurable once the continuum function and the restriction event are
measurable and local finiteness holds almost surely. -/
theorem MatedCRTEnv.IsValid.nullMeasurableSet_matedLeast_deviation_on_event
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (hγ : 0 < γ) (hγ' : γ < 2) {ε : ℝ} (hε : 0 < ε)
    (ρ t : ℝ) (ht : 0 < t)
    (hlf : ∀ᵐ ω ∂S.P, ∀ b, {c | S.mult ε ω b c ≠ 0}.Finite)
    {D : Set ℂ} (hD : IsOpen D) (hb : Bornology.IsBounded D)
    (f : Ω × ℂ → ℝ) (hf : Measurable f) (E : Set Ω) (hE : MeasurableSet E)
    (hfc : ∀ᵐ ω ∂S.P, ω ∈ E → ContinuousOn (fun x => f (ω, x)) D) (δ : ℝ) :
    NullMeasurableSet {ω | ω ∈ E ∧ ∃ x ∈ D,
      δ < |rescaledMatedLeastSupersolution S ρ t ε ω x - f (ω, x)|} S.P := by
  let w : ℤ → Ω → ℝ := fun k ω =>
    matedLeastSupersolution (S.mult ε ω) ε (S.η ω) ρ t k
  have hw : ∀ k, AEMeasurable (w k) S.P := fun k =>
    hS.aemeasurable_matedLeastSupersolution hγ hγ' hε ρ t ht k hlf
  let u : Ω → ℤ → ℝ := fun ω k => (S.mε ε)⁻¹ * (hw k).mk (w k) ω
  have hu : ∀ k, Measurable fun ω => u ω k := fun k =>
    measurable_const.mul (hw k).measurable_mk
  have huae : ∀ᵐ ω ∂S.P, ∀ k, u ω k = (S.mε ε)⁻¹ * w k ω := by
    filter_upwards [ae_all_iff.mpr (fun k => (hw k).ae_eq_mk.symm)] with ω hω
    intro k
    simp [u, hω]
  have h := hS.nullMeasurableSet_exists_cell_deviation_on_event hε hD hb u hu f hf E hE hfc δ
  apply h.congr
  filter_upwards [huae] with ω hω
  apply propext
  simp [hω, rescaledMatedLeastSupersolution, rescale, w]

end MatedCRT
