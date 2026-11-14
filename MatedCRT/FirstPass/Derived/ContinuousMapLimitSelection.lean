import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import LatticeProb.Topology.PolishContinuousMap

/-!
# Borel selection of a continuous field as the limit on a dense sequence

Let `B` be a Polish space, `zs : ℕ → ℂ` a sequence with dense range and `Q n x z ∈ B` a family of
approximations, measurable in `x` at each point `zs j`. We construct a Borel map `x ↦ K(x) ∈ C(ℂ, B)`
(compact-open topology, Borel σ-algebra `ContinuousMap.measurableSpace`) which equals the
continuous field `L` whenever `Q n x (zs j) → L (zs j)` for every `j`.

The evaluation map `e : C(ℂ, B) → B^ℕ`, `e(K)_j = K(zs j)`, is continuous, and injective because a
continuous map into a Hausdorff space is determined by its values on a dense set. As `C(ℂ, B)` is
Polish (`LatticeProb.polishSpace_continuousMap`), the Lusin–Souslin theorem
(`Continuous.measurableEmbedding`) makes `e` a measurable embedding, so `Function.extend e id K₀`
is a Borel inverse of `e` on its range, equal to the default field `K₀` off the range.

* `limitCoord`: the limit of `n ↦ Q n x z` where it exists, a default value elsewhere; it is
  measurable since the convergence set is Borel (`MeasureTheory.measurableSet_exists_tendsto`) and
  the limit of measurable maps into a metrizable space is measurable.
* `limitSelection`: on the Borel set where all coordinates `Q n x (zs j)` converge, the continuous
  field whose values at the points `zs j` are the coordinatewise limits (when there is one);
  the default field `K₀` elsewhere.
* `measurable_limitSelection`: `limitSelection zs Q K₀` is Borel measurable.
* `limitSelection_eq`: if `Q n x (zs j) → L (zs j)` for every `j`, then `limitSelection zs Q K₀ x = L`.
-/

namespace MatedCRT

open Filter Topology MeasureTheory

variable {X B : Type*} [TopologicalSpace B]

section Coordinate

open Classical in
/-- The limit of the sequence `n ↦ Q n x z` in `B` where it converges (a chosen limit), and the
default value `d` where it does not converge. -/
noncomputable def limitCoord (Q : ℕ → X → ℂ → B) (z : ℂ) (d : B) (x : X) : B :=
  if h : ∃ c, Tendsto (fun n => Q n x z) atTop (𝓝 c) then h.choose else d

/-- Where `n ↦ Q n x z` converges to `c` in a Hausdorff space, `limitCoord` is `c`. -/
theorem limitCoord_eq_of_tendsto [T2Space B] {Q : ℕ → X → ℂ → B} {z : ℂ} {d : B} {x : X} {c : B}
    (h : Tendsto (fun n => Q n x z) atTop (𝓝 c)) : limitCoord Q z d x = c := by
  unfold limitCoord
  split_ifs with hx
  · exact tendsto_nhds_unique hx.choose_spec h
  · exact absurd ⟨c, h⟩ hx

/-- Where `n ↦ Q n x z` does not converge, `limitCoord` is the default value. -/
theorem limitCoord_eq_of_not_exists {Q : ℕ → X → ℂ → B} {z : ℂ} {d : B} {x : X}
    (hx : ¬ ∃ c, Tendsto (fun n => Q n x z) atTop (𝓝 c)) : limitCoord Q z d x = d := by
  simp only [limitCoord, hx, ↓reduceDIte]

/-- For a Polish space `B`, the coordinatewise limit is measurable: the convergence set is Borel and,
on it, the limit of the measurable maps `x ↦ Q n x z` into the metrizable space `B` is measurable. -/
theorem measurable_limitCoord [MeasurableSpace X] [PolishSpace B] [MeasurableSpace B] [BorelSpace B]
    (Q : ℕ → X → ℂ → B) (z : ℂ) (d : B) (hQ : ∀ n, Measurable fun x => Q n x z) :
    Measurable (limitCoord Q z d) := by
  have hS : MeasurableSet {x | ∃ c, Tendsto (fun n => Q n x z) atTop (𝓝 c)} :=
    measurableSet_exists_tendsto hQ
  refine measurable_of_restrict_of_restrict_compl hS ?_ ?_
  · refine measurable_of_tendsto_metrizable
      (f := fun n (x : {x | ∃ c, Tendsto (fun n => Q n x z) atTop (𝓝 c)}) => Q n x.1 z)
      (fun n => (hQ n).comp measurable_subtype_coe) (tendsto_pi_nhds.2 fun x => ?_)
    obtain ⟨c, hc⟩ := x.2
    rw [Set.domRestrict_apply, limitCoord_eq_of_tendsto hc]
    exact hc
  · have hconst : ({x | ∃ c, Tendsto (fun n => Q n x z) atTop (𝓝 c)}ᶜ).domRestrict (limitCoord Q z d) =
        fun _ => d := by
      funext x
      exact limitCoord_eq_of_not_exists x.2
    rw [hconst]
    exact measurable_const

end Coordinate

section Evaluation

variable (zs : ℕ → ℂ)

/-- Evaluation of a continuous map `K : C(ℂ, B)` along the sequence `zs`: `e(K)_j = K(zs j)`. -/
def evalAlong (K : C(ℂ, B)) : ℕ → B := fun j => K (zs j)

theorem continuous_evalAlong : Continuous (evalAlong (B := B) zs) :=
  continuous_pi fun j => (by fun_prop : Continuous fun K : C(ℂ, B) => K (zs j))

/-- A continuous map into a Hausdorff space is determined by its values on the dense sequence `zs`. -/
theorem injective_evalAlong [T2Space B] {zs : ℕ → ℂ} (hzs : DenseRange zs) :
    Function.Injective (evalAlong (B := B) zs) := by
  intro K L hKL
  have h : (K : ℂ → B) = L :=
    Continuous.ext_on (show Dense (Set.range zs) from hzs) K.continuous L.continuous
      (by rintro _ ⟨j, rfl⟩; exact congrFun hKL j)
  exact ContinuousMap.ext (congrFun h)

/-- For `B` Polish, evaluation along a dense sequence is a measurable embedding of `C(ℂ, B)` into
`B^ℕ` (Lusin–Souslin: `C(ℂ, B)` is Polish and the evaluation map is continuous and injective). -/
theorem measurableEmbedding_evalAlong [PolishSpace B] [MeasurableSpace B] [BorelSpace B]
    {zs : ℕ → ℂ} (hzs : DenseRange zs) : MeasurableEmbedding (evalAlong (B := B) zs) := by
  have : PolishSpace C(ℂ, B) := LatticeProb.polishSpace_continuousMap ℂ B
  exact (continuous_evalAlong zs).measurableEmbedding (injective_evalAlong hzs)

end Evaluation

section Selection

/-- The sequence of coordinatewise limits `j ↦ lim_n Q n x (zs j)` (default `K₀ (zs j)` where the
coordinate does not converge). -/
noncomputable def limitSeq (zs : ℕ → ℂ) (Q : ℕ → X → ℂ → B) (K₀ : C(ℂ, B)) (x : X) : ℕ → B :=
  fun j => limitCoord Q (zs j) (K₀ (zs j)) x

theorem measurable_limitSeq [MeasurableSpace X] [PolishSpace B] [MeasurableSpace B] [BorelSpace B]
    {zs : ℕ → ℂ}
    {Q : ℕ → X → ℂ → B} (K₀ : C(ℂ, B)) (hQ : ∀ n j, Measurable fun x => Q n x (zs j)) :
    Measurable (limitSeq zs Q K₀) :=
  Measurable.of_eval fun j => measurable_limitCoord Q (zs j) (K₀ (zs j)) fun n => hQ n j

open Classical in
/-- **Borel selection of the limiting continuous field.** On the set of `x` where every coordinate
`n ↦ Q n x (zs j)` converges, `limitSelection zs Q K₀ x` is the continuous field `K` with
`K (zs j) = lim_n Q n x (zs j)` for all `j`, when such a field exists (it is then unique if `zs` has
dense range); it is the default field `K₀` otherwise. -/
noncomputable def limitSelection (zs : ℕ → ℂ) (Q : ℕ → X → ℂ → B) (K₀ : C(ℂ, B)) : X → C(ℂ, B) :=
  {x | ∀ j, ∃ c, Tendsto (fun n => Q n x (zs j)) atTop (𝓝 c)}.piecewise
    (fun x => Function.extend (evalAlong zs) id (fun _ => K₀) (limitSeq zs Q K₀ x)) (fun _ => K₀)

/-- The limit selection is Borel measurable for the Borel σ-algebra of the compact-open topology on
`C(ℂ, B)`, when `B` is Polish and the approximations are measurable at the points of a dense
sequence. -/
theorem measurable_limitSelection [MeasurableSpace X] [PolishSpace B] [MeasurableSpace B] [BorelSpace B]
    {zs : ℕ → ℂ} {Q : ℕ → X → ℂ → B} {K₀ : C(ℂ, B)} (hzs : DenseRange zs)
    (hQ : ∀ n j, Measurable fun x => Q n x (zs j)) : Measurable (limitSelection zs Q K₀) := by
  have hconv : MeasurableSet {x | ∀ j, ∃ c, Tendsto (fun n => Q n x (zs j)) atTop (𝓝 c)} := by
    have h : {x | ∀ j, ∃ c, Tendsto (fun n => Q n x (zs j)) atTop (𝓝 c)} =
        ⋂ j, {x | ∃ c, Tendsto (fun n => Q n x (zs j)) atTop (𝓝 c)} := by
      ext x
      simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    rw [h]
    exact MeasurableSet.iInter fun j => measurableSet_exists_tendsto fun n => hQ n j
  rw [limitSelection]
  exact Measurable.piecewise hconv
    (((measurableEmbedding_evalAlong hzs).measurable_extend measurable_id measurable_const).comp
      (measurable_limitSeq K₀ hQ)) measurable_const

open Classical in
/-- If `Q n x (zs j) → L (zs j)` for every `j`, for a continuous field `L` and a dense sequence `zs`,
then the limit selection at `x` is `L`. -/
theorem limitSelection_eq [T2Space B] {zs : ℕ → ℂ} {Q : ℕ → X → ℂ → B} {K₀ : C(ℂ, B)}
    (hzs : DenseRange zs) {x : X} {L : C(ℂ, B)}
    (hL : ∀ j, Tendsto (fun n => Q n x (zs j)) atTop (𝓝 (L (zs j)))) :
    limitSelection zs Q K₀ x = L := by
  have hseq : limitSeq zs Q K₀ x = evalAlong zs L :=
    funext fun j => limitCoord_eq_of_tendsto (hL j)
  have hmem : x ∈ {x | ∀ j, ∃ c, Tendsto (fun n => Q n x (zs j)) atTop (𝓝 c)} :=
    fun j => ⟨_, hL j⟩
  have h1 : limitSelection zs Q K₀ x =
      Function.extend (evalAlong zs) id (fun _ => K₀) (limitSeq zs Q K₀ x) :=
    Set.piecewise_eq_of_mem _ _ _ hmem
  rw [h1, hseq]
  exact (injective_evalAlong hzs).extend_apply id _ L

end Selection

end MatedCRT
