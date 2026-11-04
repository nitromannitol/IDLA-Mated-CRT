import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.Topology.Metrizable.Basic

/-! # Measurable versions of continuous random fields -/

open Set Filter MeasureTheory Topology TopologicalSpace

namespace MatedCRT

/-- A random field with almost surely continuous sample paths and almost
everywhere measurable point evaluations has a jointly measurable version. -/
theorem exists_jointlyMeasurable_of_ae_continuous
    {Ω X : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [TopologicalSpace X] [MetrizableSpace X] [MeasurableSpace X]
    [SecondCountableTopology X] [BorelSpace X]
    (f : Ω → X → ℝ)
    (hf : ∀ x, AEMeasurable (fun ω => f ω x) P)
    (hc : ∀ᵐ ω ∂P, Continuous (f ω)) :
    ∃ g : Ω × X → ℝ, Measurable g ∧ ∀ᵐ ω ∂P, ∀ x, g (ω, x) = f ω x := by
  classical
  let h_id : StronglyMeasurable (id : X → X) := stronglyMeasurable_id
  let a : ℕ → SimpleFunc X X := h_id.approx
  let v : X → Ω → ℝ := fun x => (hf x).mk (fun ω => f ω x)
  let u : ℕ → Ω × X → ℝ := fun n p => v (a n p.2) p.1
  have hu : ∀ n, Measurable (u n) := by
    intro n
    have hv : Measurable (fun p : (a n).range × Ω => v p.1 p.2) := by
      have : (fun p : (a n).range × Ω => v p.1 p.2) =
          (fun p : Ω × (a n).range => v p.2 p.1) ∘ Prod.swap := rfl
      rw [this, @measurable_swap_iff Ω (a n).range ℝ]
      exact measurable_from_prod_countable_left (fun x => (hf x).measurable_mk)
    have ha : Measurable (fun p : Ω × X =>
        ((⟨a n p.2, SimpleFunc.mem_range_self _ _⟩ : (a n).range), p.1)) :=
      ((a n).measurable.comp measurable_snd).subtype_mk.prodMk measurable_fst
    exact hv.comp ha
  let g : Ω × X → ℝ := fun p => limUnder atTop (fun n => u n p)
  have hg : Measurable g := (StronglyMeasurable.limUnder
    (fun n => (hu n).stronglyMeasurable)).measurable
  have hsample : ∀ᵐ ω ∂P, ∀ n (x : (a n).range), v x ω = f ω x := by
    apply ae_all_iff.mpr
    intro n
    apply ae_all_iff.mpr
    intro x
    exact (hf x).ae_eq_mk.symm
  refine ⟨g, hg, ?_⟩
  filter_upwards [hc, hsample] with ω hcont hs
  intro x
  have hlim : Tendsto (fun n => u n (ω, x)) atTop (𝓝 (f ω x)) := by
    have h := (hcont.tendsto x).comp (h_id.tendsto_approx x)
    convert h using 1
    ext n
    exact hs n ⟨a n x, SimpleFunc.mem_range_self _ _⟩
  exact hlim.limUnder_eq

/-- On a measurable event, continuity on a measurable spatial domain and
measurable point evaluations give a jointly measurable version on that domain. -/
theorem exists_jointlyMeasurable_on_event
    {Ω X : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [TopologicalSpace X] [MetrizableSpace X] [MeasurableSpace X]
    [SecondCountableTopology X] [BorelSpace X]
    (D : Set X) (hD : MeasurableSet D) (x₀ : X) (hx₀ : x₀ ∈ D)
    (E : Set Ω) (hE : MeasurableSet E) (f : Ω → X → ℝ)
    (hf : ∀ x, AEMeasurable (fun ω => f ω x) P)
    (hc : ∀ᵐ ω ∂P, ω ∈ E → ContinuousOn (f ω) D) :
    ∃ g : Ω × X → ℝ, Measurable g ∧
      ∀ᵐ ω ∂P, ω ∈ E → ∀ x ∈ D, g (ω, x) = f ω x := by
  classical
  let F : Ω → D → ℝ := fun ω x => if ω ∈ E then f ω x else 0
  have hF : ∀ x, AEMeasurable (fun ω => F ω x) P := by
    intro x
    refine ⟨fun ω => if ω ∈ E then (hf x).mk (fun ω => f ω x) ω else 0,
      (hf x).measurable_mk.ite hE measurable_const, ?_⟩
    filter_upwards [(hf x).ae_eq_mk] with ω hω
    simp [F, hω]
  have hFc : ∀ᵐ ω ∂P, Continuous (F ω) := by
    filter_upwards [hc] with ω hω
    by_cases h : ω ∈ E
    · have heq : F ω = fun x : D => f ω x := by funext x; simp [F, h]
      rw [heq]
      exact (hω h).comp_continuous continuous_subtype_val (fun x : D => x.property)
    · simpa [F, h] using (continuous_const : Continuous (fun _ : D => (0 : ℝ)))
  obtain ⟨g, hg, hgae⟩ := exists_jointlyMeasurable_of_ae_continuous P F hF hFc
  let r : X → D := fun x => ⟨if x ∈ D then x else x₀, by split_ifs with h; exact h; exact hx₀⟩
  have hr : Measurable r := by
    apply Measurable.subtype_mk
    exact measurable_id.ite hD measurable_const
  refine ⟨fun p => g (p.1, r p.2), hg.comp (measurable_fst.prodMk (hr.comp measurable_snd)), ?_⟩
  filter_upwards [hgae] with ω hω hωE x hx
  simpa [r, hx, F, hωE] using hω ⟨x, hx⟩

end MatedCRT
