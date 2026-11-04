import MatedCRT.Proofs.Sec3.UniformConvergenceGreenKernel.EnvironmentMeasurability
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.CellMeasurable

/-! # Environment-measurable vertex containing a point -/

namespace MatedCRT

open Set Filter Topology MeasureTheory

/-- A measurable choice of the least cell containing a point agrees with
`vertexOf` for continuous proper surjective curves. -/
theorem exists_measurable_vertexOf_curve {ε : ℝ} (hε : 0 < ε) :
    ∃ V : C(ℝ, ℂ) × ℂ → ℤ, Measurable V ∧
      ∀ (η : C(ℝ, ℂ)) (x : ℂ), Tendsto η (cocompact ℝ) (cocompact ℂ) →
        Function.Surjective η → V (η, x) = vertexOf ε η x := by
  classical
  let A : ℤ → Set (C(ℝ, ℂ) × ℂ) := fun k => {p | p.2 ∈ cell ε p.1 k}
  have hA : ∀ k, MeasurableSet (A k) := fun k =>
    (isClosed_curve_cell_graph ε k).measurableSet
  let P : (C(ℝ, ℂ) × ℂ) → ℤ → Prop := fun p k => p ∈ A k ∧ ∀ j < k, p ∉ A j
  have hP : ∀ k, MeasurableSet {p | P p k} := by
    intro k
    convert (hA k).inter (MeasurableSet.iInter fun j => MeasurableSet.iInter fun (_ : j < k) => (hA j).compl) using 1
    ext p
    simp [P]
  let Q : (C(ℝ, ℂ) × ℂ) → ℕ → Prop := fun p n => P p (Tightness.intEnum n)
  have hchoice : ∀ p, ∃ n, Q p n ∨ ¬∃ n, Q p n := by
    intro p
    by_cases h : ∃ n, Q p n
    · obtain ⟨n, hn⟩ := h
      exact ⟨n, Or.inl hn⟩
    · exact ⟨0, Or.inr h⟩
  have hexists : MeasurableSet {p | ∃ n, Q p n} := by
    convert MeasurableSet.iUnion (fun n => hP (Tightness.intEnum n)) using 1
    ext p
    simp [Q]
  have hfind : Measurable (fun p => Nat.find (hchoice p)) :=
    measurable_find hchoice (fun n => (hP _).union hexists.compl)
  let V : C(ℝ, ℂ) × ℂ → ℤ := fun p => Tightness.intEnum (Nat.find (hchoice p))
  refine ⟨V, (measurable_of_countable Tightness.intEnum).comp hfind, ?_⟩
  intro η x hp hsurj
  let a : ℤ := vertexOf ε η x
  have hcell : x ∈ cell ε η a :=
    Tightness.mem_cell_vertexOf η.continuous hp hsurj hε x
  have hfinite : {j : ℤ | x ∈ cell ε η j}.Finite :=
    (Tightness.cellVertices_finite η.continuous hp hε (Bornology.isBounded_singleton (x := x))).subset
      (fun j hj => ⟨x, hj, rfl⟩)
  have hleast : ∀ j, x ∈ cell ε η j → a ≤ j := fun j hj => csInf_le hfinite.bddBelow hj
  have hPa : P (η, x) a := by
    constructor
    · exact hcell
    · intro j hj hmem
      exact (not_le_of_gt hj) (hleast j hmem)
  obtain ⟨n, hn⟩ := Tightness.intEnum_surjective a
  have hQ : ∃ n, Q (η, x) n := ⟨n, by simpa [Q, hn] using hPa⟩
  have hspec := Nat.find_spec (hchoice (η, x))
  have hPv : P (η, x) (V (η, x)) := hspec.resolve_right (fun h => h hQ)
  have hvcell : x ∈ cell ε η (V (η, x)) := hPv.1
  apply le_antisymm ?_ (hleast _ hvcell)
  by_contra h
  exact hPv.2 a (lt_of_not_ge h) hPa.1

/-- For a fixed point, the vertex containing it has an environment-measurable
version. -/
theorem MatedCRTEnv.IsValid.exists_envSigma_measurable_vertexOf
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    {ε : ℝ} (hε : 0 < ε) (x : ℂ) :
    ∃ a : Ω → ℤ, Measurable[S.envSigma] a ∧
      ∀ᵐ ω ∂S.P, a ω = vertexOf ε (S.η ω) x := by
  obtain ⟨η, hηm, hη⟩ := hS.exists_envSigma_measurable_curve
  obtain ⟨V, hVm, hV⟩ := exists_measurable_vertexOf_curve hε
  refine ⟨fun ω => V (η ω, x), hVm.comp (hηm.prodMk measurable_const), ?_⟩
  filter_upwards [hη, hS.ae_tendsto_cocompact, hS.isAreaParametrized] with ω hω hp ha
  have hp' : Tendsto (η ω) (cocompact ℝ) (cocompact ℂ) := by rwa [hω]
  have hs' : Function.Surjective (η ω) := by rw [hω]; exact ha.2.2.1
  rw [hV (η ω) x hp' hs', hω]

end MatedCRT
