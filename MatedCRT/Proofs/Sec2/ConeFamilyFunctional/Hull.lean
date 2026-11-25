import Mathlib.MeasureTheory.Constructions.Polish.Basic
import LatticeProb.Prob.AnalyticUniversalMeasurable

/-!
# Null sets of a projection from a product with a factor of real coordinates

Let `Y` be a Polish space with its Borel σ-algebra, `ι` any index type, and `Q` a finite measure on `Y × (ι → ℝ)`
(product σ-algebra). If almost surely `x.1 ∉ S`, then `S` is null for the image of `Q` under the first projection
(`map_fst_apply_eq_zero`).

A measurable subset `N` of `Y × (ι → ℝ)` depends on countably many coordinates `J ⊆ ι` (`exists_countable_restrict`:
such sets form a σ-algebra containing the generators). Take `N ⊇ {x | x.1 ∈ S}` measurable and null. The set
`T₀ = {y | ∀ v, (y, v) ∈ N₀}` contains `S` and its complement is the projection of a Borel subset of the standard Borel
space `Y × (J → ℝ)`, an analytic set, hence null-measurable (Lusin; Kechris, Theorem 21.10). Its preimage lies in
`N`, so `T₀` is null.
-/

namespace MatedCRT

open MeasureTheory Set

namespace ConeFamilyFunctional

/-- The restriction of the real coordinates to `J`. -/
def restrictCoords {Y ι : Type*} (J : Set ι) (x : Y × (ι → ℝ)) : Y × (J → ℝ) := (x.1, fun j => x.2 j)

theorem measurable_restrictCoords {Y ι : Type*} [MeasurableSpace Y] (J : Set ι) :
    Measurable (restrictCoords (Y := Y) J) :=
  measurable_fst.prodMk (measurable_pi_iff.2 fun j => (measurable_pi_apply (j : ι)).comp measurable_snd)

/-- **Measurable sets of `Y × (ι → ℝ)` depend on countably many coordinates.** -/
theorem exists_countable_restrict {Y ι : Type*} [MeasurableSpace Y] {N : Set (Y × (ι → ℝ))}
    (hN : MeasurableSet N) : ∃ J : Set ι, J.Countable ∧ ∃ N₀ : Set (Y × (J → ℝ)), MeasurableSet N₀ ∧
      N = restrictCoords J ⁻¹' N₀ := by
  classical
  let C : MeasurableSpace (Y × (ι → ℝ)) :=
    { MeasurableSet' := fun N => ∃ J : Set ι, J.Countable ∧ ∃ N₀ : Set (Y × (J → ℝ)), MeasurableSet N₀ ∧
        N = restrictCoords J ⁻¹' N₀
      measurableSet_empty := ⟨∅, countable_empty, ∅, MeasurableSet.empty, rfl⟩
      measurableSet_compl := by
        rintro N ⟨J, hJ, N₀, hN₀, rfl⟩
        exact ⟨J, hJ, N₀ᶜ, hN₀.compl, rfl⟩
      measurableSet_iUnion := by
        intro f hf
        choose J hJ N₀ hN₀ hfeq using hf
        let K : Set ι := ⋃ n, J n
        have hsub : ∀ n, J n ⊆ K := fun n => subset_iUnion J n
        let res : ∀ n, Y × (K → ℝ) → Y × (J n → ℝ) := fun n p => (p.1, fun j => p.2 ⟨j, hsub n j.2⟩)
        have hres : ∀ n, Measurable (res n) := fun n =>
          measurable_fst.prodMk (measurable_pi_iff.2 fun j => (measurable_pi_apply _).comp measurable_snd)
        refine ⟨K, countable_iUnion hJ, ⋃ n, res n ⁻¹' N₀ n, MeasurableSet.iUnion fun n => hres n (hN₀ n), ?_⟩
        ext x
        simp only [mem_iUnion, mem_preimage]
        exact exists_congr fun n => by rw [hfeq n]; rfl }
  have hle : (Prod.instMeasurableSpace : MeasurableSpace (Y × (ι → ℝ))) ≤ C := by
    change MeasurableSpace.comap Prod.fst _ ⊔ MeasurableSpace.comap Prod.snd _ ≤ C
    refine sup_le ?_ ?_
    · rintro _ ⟨s, hs, rfl⟩
      exact ⟨∅, countable_empty, Prod.fst ⁻¹' s, measurable_fst hs, rfl⟩
    · rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup]
      refine iSup_le fun i => ?_
      rw [MeasurableSpace.comap_comp]
      rintro _ ⟨U, hU, rfl⟩
      refine ⟨{i}, countable_singleton i, (fun p : Y × (({i} : Set ι) → ℝ) => p.2 ⟨i, rfl⟩) ⁻¹' U,
        (measurable_pi_apply _).comp measurable_snd hU, rfl⟩
  exact hle _ hN

/-- **Null sets of the first projection.** -/
theorem map_fst_apply_eq_zero {Y ι : Type*} [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y]
    [BorelSpace Y] {Q : Measure (Y × (ι → ℝ))} [IsFiniteMeasure Q] {S : Set Y} (h : ∀ᵐ x ∂Q, x.1 ∉ S) :
    Q.map Prod.fst S = 0 := by
  classical
  have hnull : Q {x | x.1 ∈ S} = 0 := by
    rw [ae_iff] at h
    simpa using h
  set N := toMeasurable Q {x : Y × (ι → ℝ) | x.1 ∈ S} with hNdef
  have hNm : MeasurableSet N := measurableSet_toMeasurable _ _
  have hN0 : Q N = 0 := by rw [measure_toMeasurable]; exact hnull
  obtain ⟨J, hJ, N₀, hN₀, hNeq⟩ := exists_countable_restrict hNm
  have : Countable J := hJ.to_subtype
  let T₀ : Set Y := {y | ∀ v : J → ℝ, (y, v) ∈ N₀}
  have hST : S ⊆ T₀ := by
    intro y hy v
    let p : ι → ℝ := fun i => if h : i ∈ J then v ⟨i, h⟩ else 0
    have hp : (y, p) ∈ N := subset_toMeasurable _ _ (show (y, p).1 ∈ S from hy)
    rw [hNeq, mem_preimage] at hp
    have hr : restrictCoords J (y, p) = (y, v) :=
      Prod.ext rfl (funext fun j => by simp [restrictCoords, p])
    rwa [hr] at hp
  have hTc : T₀ᶜ = Prod.fst '' N₀ᶜ := by
    ext y
    simp only [T₀, mem_compl_iff, mem_ofPred_eq, not_forall, mem_image, Prod.exists, exists_and_right,
      exists_eq_right]
  have hTnm : NullMeasurableSet T₀ (Q.map Prod.fst) := by
    have hA : AnalyticSet (Prod.fst '' N₀ᶜ) := hN₀.compl.analyticSet_image measurable_fst
    rw [← compl_compl T₀, hTc]
    exact (LatticeProb.AnalyticSet.nullMeasurableSet (Q.map Prod.fst) hA).compl
  have hT0 : Q.map Prod.fst T₀ = 0 := by
    rw [Measure.map_apply₀ measurable_fst.aemeasurable hTnm]
    refine measure_mono_null (fun x hx => ?_) hN0
    rw [hNeq]
    exact hx (fun j => x.2 j)
  exact measure_mono_null hST hT0

end ConeFamilyFunctional

end MatedCRT
