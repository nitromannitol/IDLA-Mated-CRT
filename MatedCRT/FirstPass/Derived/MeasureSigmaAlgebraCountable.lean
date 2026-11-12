import Mathlib

/-!
# The σ-algebra of locally finite measures on `ℂ` is countably generated

There is a countable family `U n` of open subsets of `ℂ` (the finite intersections of the members of a
countable basis together with the balls `ball 0 k`) such that every measurable set `S` of measures,
intersected with the locally finite measures, is the preimage of a Borel set of `ℕ → ℝ≥0∞` under
`m ↦ (m (U n))ₙ`.

Proof: the sets with this property form a σ-algebra `traceSigma U` on `Measure ℂ`; by a Dynkin
argument on the π-system `{U n}` (localised to the balls `ball 0 k`, on which locally finite measures
are finite, to treat complements) every evaluation `m ↦ m A` is measurable for `traceSigma U`, which
is therefore finer than the σ-algebra of `Measure ℂ`.
-/

namespace MatedCRT.FirstPass.Derived

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal

/-- The sets of measures that are determined, among the locally finite measures, by the masses
`m (U n)`. -/
private abbrev traceSigma (U : ℕ → Set ℂ) : MeasurableSpace (Measure ℂ) where
  MeasurableSet' S := ∃ T : Set (ℕ → ℝ≥0∞), MeasurableSet T ∧
    S ∩ {m | IsLocallyFiniteMeasure m} =
      (fun (m : Measure ℂ) (n : ℕ) => m (U n)) ⁻¹' T ∩ {m | IsLocallyFiniteMeasure m}
  measurableSet_empty := ⟨∅, MeasurableSet.empty, by simp⟩
  measurableSet_compl := by
    rintro S ⟨T, hT, h⟩
    refine ⟨Tᶜ, hT.compl, ?_⟩
    ext m
    have hm := Set.ext_iff.1 h m
    simp only [mem_inter_iff, mem_ofPred_eq, mem_compl_iff, mem_preimage] at hm ⊢
    tauto
  measurableSet_iUnion := by
    intro f hf
    choose T hT h using hf
    refine ⟨⋃ i, T i, MeasurableSet.iUnion hT, ?_⟩
    ext m
    have hm := fun i => Set.ext_iff.1 (h i) m
    simp only [mem_inter_iff, mem_ofPred_eq, mem_iUnion, mem_preimage] at hm ⊢
    constructor
    · rintro ⟨⟨i, hi⟩, hlf⟩
      exact ⟨⟨i, ((hm i).1 ⟨hi, hlf⟩).1⟩, hlf⟩
    · rintro ⟨⟨i, hi⟩, hlf⟩
      exact ⟨⟨i, ((hm i).2 ⟨hi, hlf⟩).1⟩, hlf⟩

/-- A type synonym of `Measure ℂ` carrying the σ-algebra `traceSigma U`. -/
private def MeasTrace (_U : ℕ → Set ℂ) : Type := Measure ℂ

private noncomputable instance (U : ℕ → Set ℂ) : MeasurableSpace (MeasTrace U) := traceSigma U

/-- The mass of `A` as a function on `MeasTrace U`. -/
private noncomputable def MeasTrace.mass (U : ℕ → Set ℂ) (A : Set ℂ) : MeasTrace U → ℝ≥0∞ :=
  fun m => (show Measure ℂ from m) A

private theorem MeasTrace.measurableSet_iff (U : ℕ → Set ℂ) (S : Set (MeasTrace U)) :
    MeasurableSet S ↔ ∃ T : Set (ℕ → ℝ≥0∞), MeasurableSet T ∧
      (show Set (Measure ℂ) from S) ∩ {m | IsLocallyFiniteMeasure m} =
        (fun (m : Measure ℂ) (n : ℕ) => m (U n)) ⁻¹' T ∩ {m | IsLocallyFiniteMeasure m} :=
  Iff.rfl

private theorem MeasTrace.measurable_mass_U (U : ℕ → Set ℂ) (n : ℕ) :
    Measurable (MeasTrace.mass U (U n)) := by
  intro B hB
  exact (MeasTrace.measurableSet_iff U _).2 ⟨(fun x : ℕ → ℝ≥0∞ => x n) ⁻¹' B,
    measurable_pi_apply n hB, rfl⟩

private theorem MeasTrace.measurable_congr {U : ℕ → Set ℂ} {f g : MeasTrace U → ℝ≥0∞}
    (hg : Measurable g)
    (hfg : ∀ m : Measure ℂ, IsLocallyFiniteMeasure m → f m = g m) : Measurable f := by
  intro B hB
  obtain ⟨T, hT, h⟩ := (MeasTrace.measurableSet_iff U _).1 (hg hB)
  refine (MeasTrace.measurableSet_iff U _).2 ⟨T, hT, ?_⟩
  rw [← h]
  ext m
  show (f m ∈ B ∧ IsLocallyFiniteMeasure (show Measure ℂ from m)) ↔
    (g m ∈ B ∧ IsLocallyFiniteMeasure (show Measure ℂ from m))
  have hm := hfg (show Measure ℂ from m)
  constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨?_, h2⟩
  · rwa [← hm h2]
  · rwa [hm h2]

/-- Evaluation of a measurable set is `traceSigma`-measurable, granted that the family `U` is a
π-system of open sets generating the Borel σ-algebra and containing the balls `ball 0 k`. -/
private theorem MeasTrace.measurable_mass (U : ℕ → Set ℂ)
    (hinter : ∀ a b, ∃ c, U c = U a ∩ U b) (hball : ∀ k : ℕ, ∃ c, U c = ball (0 : ℂ) k)
    (hgen : (inferInstance : MeasurableSpace ℂ) = MeasurableSpace.generateFrom (range U))
    (A : Set ℂ) (hA : MeasurableSet A) : Measurable (MeasTrace.mass U A) := by
  have hπ : IsPiSystem (range U) := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ _
    obtain ⟨c, hc⟩ := hinter a b
    exact ⟨c, hc⟩
  have key : ∀ A, MeasurableSet A → ∀ k : ℕ,
      Measurable (fun m : MeasTrace U => MeasTrace.mass U (A ∩ ball (0 : ℂ) k) m) := by
    intro A hA
    refine MeasurableSpace.induction_on_inter
      (C := fun A _ => ∀ k : ℕ, Measurable (MeasTrace.mass U (A ∩ ball (0 : ℂ) k)))
      hgen hπ ?_ ?_ ?_ ?_ A hA
    · intro k
      have : MeasTrace.mass U (∅ ∩ ball (0 : ℂ) k) = fun _ => 0 := by
        funext m
        change (show Measure ℂ from m) (∅ ∩ ball (0 : ℂ) k) = 0
        rw [empty_inter]
        exact measure_empty
      rw [this]
      exact measurable_const
    · rintro t ⟨n, rfl⟩ k
      obtain ⟨b, hb⟩ := hball k
      obtain ⟨c, hc⟩ := hinter n b
      rw [← hb, ← hc]
      exact MeasTrace.measurable_mass_U U c
    · intro t ht ih k
      have hball_meas : Measurable (MeasTrace.mass U (ball (0 : ℂ) k)) := by
        obtain ⟨b, hb⟩ := hball k
        rw [← hb]
        exact MeasTrace.measurable_mass_U U b
      refine MeasTrace.measurable_congr
        (g := fun m => MeasTrace.mass U (ball (0 : ℂ) k) m - MeasTrace.mass U (t ∩ ball (0 : ℂ) k) m)
        (hball_meas.sub (ih k)) ?_
      intro m hm
      have hfin : m (t ∩ ball (0 : ℂ) k) ≠ ∞ :=
        ne_top_of_le_ne_top (measure_ball_lt_top (μ := m) (x := (0 : ℂ)) (r := k)).ne
          (measure_mono inter_subset_right)
      have h := measure_inter_add_sdiff (μ := m) (ball (0 : ℂ) k) ht
      have hdiff : ball (0 : ℂ) k \ t = tᶜ ∩ ball (0 : ℂ) k := by
        rw [sdiff_eq, inter_comm]
      rw [hdiff, inter_comm] at h
      exact ENNReal.eq_sub_of_add_eq hfin (by rw [add_comm]; exact h)
    · intro f hdisj hfm ih k
      have hmass : MeasTrace.mass U ((⋃ i, f i) ∩ ball (0 : ℂ) k) =
          fun m => ∑' i, MeasTrace.mass U (f i ∩ ball (0 : ℂ) k) m := by
        funext m
        simp only [MeasTrace.mass]
        rw [iUnion_inter]
        exact measure_iUnion
          (fun i j hij => ((hdisj hij).mono inter_subset_left inter_subset_left))
          (fun i => (hfm i).inter measurableSet_ball)
      rw [hmass]
      exact Measurable.tsum (fun i => ih i k)
  have hsup' : ∀ m : Measure ℂ, m A = ⨆ k : ℕ, m (A ∩ ball (0 : ℂ) k) := by
    intro m
    have hmono : Monotone (fun k : ℕ => A ∩ ball (0 : ℂ) k) := fun i j hij =>
      inter_subset_inter_right _ (ball_subset_ball (by exact_mod_cast hij))
    rw [← hmono.measure_iUnion, ← inter_iUnion, Metric.iUnion_ball_nat, inter_univ]
  have hsup : MeasTrace.mass U A = fun m => ⨆ k : ℕ, MeasTrace.mass U (A ∩ ball (0 : ℂ) k) m := by
    funext m
    exact hsup' m
  rw [hsup]
  exact Measurable.iSup (fun k => key A hA k)

/-- There is a countable family of open subsets of `ℂ` whose masses generate, on the locally finite
measures, the σ-algebra of `Measure ℂ`. -/
theorem exists_countable_openMass_generation :
    ∃ U : ℕ → Set ℂ, (∀ n, IsOpen (U n)) ∧ ∀ S : Set (Measure ℂ), MeasurableSet S →
      ∃ T : Set (ℕ → ℝ≥0∞), MeasurableSet T ∧
        S ∩ {m | IsLocallyFiniteMeasure m} =
          (fun (m : Measure ℂ) (n : ℕ) => m (U n)) ⁻¹' T ∩ {m | IsLocallyFiniteMeasure m} := by
  classical
  obtain ⟨W, hW⟩ := ((countable_countableBasis ℂ).union
    (countable_range (fun k : ℕ => ball (0 : ℂ) k))).exists_eq_range
      ⟨ball (0 : ℂ) ((0 : ℕ) : ℝ), Or.inr ⟨0, rfl⟩⟩
  have hWopen : ∀ i, IsOpen (W i) := by
    intro i
    have : W i ∈ countableBasis ℂ ∪ range (fun k : ℕ => ball (0 : ℂ) k) := by
      rw [hW]; exact mem_range_self i
    rcases this with h | ⟨k, hk⟩
    · exact isOpen_of_mem_countableBasis h
    · rw [← hk]; exact isOpen_ball
  have hWbasis : ∀ b ∈ countableBasis ℂ, ∃ j, W j = b := by
    intro b hb
    have : b ∈ range W := by rw [← hW]; exact Or.inl hb
    obtain ⟨j, hj⟩ := this
    exact ⟨j, hj⟩
  have hWball : ∀ k : ℕ, ∃ j, W j = ball (0 : ℂ) k := by
    intro k
    have : ball (0 : ℂ) k ∈ range W := by rw [← hW]; exact Or.inr ⟨k, rfl⟩
    obtain ⟨j, hj⟩ := this
    exact ⟨j, hj⟩
  let P : Finset ℕ → Set ℂ := fun F => ⋂ i ∈ F, W i
  obtain ⟨U, hU⟩ := (countable_range P).exists_eq_range ⟨P ∅, mem_range_self _⟩
  have hPU : ∀ F, ∃ n, U n = P F := by
    intro F
    have : P F ∈ range U := by rw [← hU]; exact mem_range_self F
    obtain ⟨n, hn⟩ := this
    exact ⟨n, hn⟩
  have hUP : ∀ n, ∃ F, P F = U n := by
    intro n
    have : U n ∈ range P := by rw [hU]; exact mem_range_self n
    obtain ⟨F, hF⟩ := this
    exact ⟨F, hF⟩
  have hUopen : ∀ n, IsOpen (U n) := by
    intro n
    obtain ⟨F, hF⟩ := hUP n
    rw [← hF]
    exact isOpen_biInter_finset (fun i _ => hWopen i)
  have hinter : ∀ a b, ∃ c, U c = U a ∩ U b := by
    intro a b
    obtain ⟨F, hF⟩ := hUP a
    obtain ⟨G, hG⟩ := hUP b
    obtain ⟨c, hc⟩ := hPU (F ∪ G)
    refine ⟨c, ?_⟩
    rw [hc, ← hF, ← hG]
    ext x
    simp only [P, mem_iInter, mem_inter_iff, Finset.mem_union]
    constructor
    · intro h
      exact ⟨fun i hi => h i (Or.inl hi), fun i hi => h i (Or.inr hi)⟩
    · rintro ⟨h1, h2⟩ i (hi | hi)
      · exact h1 i hi
      · exact h2 i hi
  have hball : ∀ k : ℕ, ∃ c, U c = ball (0 : ℂ) k := by
    intro k
    obtain ⟨j, hj⟩ := hWball k
    obtain ⟨c, hc⟩ := hPU {j}
    exact ⟨c, by rw [hc]; simp [P, hj]⟩
  have hgen : (inferInstance : MeasurableSpace ℂ) = MeasurableSpace.generateFrom (range U) := by
    apply le_antisymm
    · rw [BorelSpace.measurable_eq (α := ℂ),
        (isBasis_countableBasis ℂ).borel_eq_generateFrom]
      apply MeasurableSpace.generateFrom_le
      intro b hb
      obtain ⟨j, hj⟩ := hWbasis b hb
      obtain ⟨c, hc⟩ := hPU {j}
      apply MeasurableSpace.measurableSet_generateFrom
      exact ⟨c, by rw [hc]; simp [P, hj]⟩
    · apply MeasurableSpace.generateFrom_le
      rintro _ ⟨n, rfl⟩
      exact (hUopen n).measurableSet
  refine ⟨U, hUopen, fun S hS => ?_⟩
  have hid : Measurable (fun m : MeasTrace U => (show Measure ℂ from m)) :=
    Measure.measurable_of_measurable_coe _ (fun A hA =>
      MeasTrace.measurable_mass U hinter hball hgen A hA)
  have h := (MeasTrace.measurableSet_iff U _).1 (hid hS)
  exact h

end MatedCRT.FirstPass.Derived
