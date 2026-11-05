import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.VagueOpenExist

/-!
# Vague limits on the whole plane from a countable family of test functions

A countable family `F` of continuous compactly supported functions on `ℂ` which is uniformly dense, with support
control, among all continuous compactly supported functions (`IsDenseTestFamilyC`), exists
(`exists_denseTestFamilyC`); if a sequence of measures, finite on compacts, has convergent integrals against every
member of `F`, it has convergent integrals against every continuous compactly supported function
(`tendsto_of_denseTestFamilyC`), hence a vague limit on `ℂ` (Bonanno's `exists_isVagueLimitOn_of_tendsto_open`,
Riesz-Markov-Kakutani). Adapted from Bonanno's `QuantumZipper.VagueH` (upper half-plane), with the exhaustion by the
closed balls `closedBall 0 n` of `ℂ`.
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace MatedCRT
namespace VagueWholePlane

/-- A continuous compactly supported function on `ℂ`. -/
def IsTestC (f : ℂ → ℝ) : Prop := Continuous f ∧ HasCompactSupport f

theorem IsTestC.integrable {μ : Measure ℂ} {f : ℂ → ℝ} (hf : IsTestC f) (hμ : μ (tsupport f) < ∞) :
    Integrable f μ :=
  QuantumZipper.VagueOpen.integrable_of_testFun hf.1 hf.2 hμ

/-- A countable family of test functions, uniformly dense with support control, and with dominating bumps. -/
def IsDenseTestFamilyC (F : Set (ℂ → ℝ)) : Prop :=
  (∀ f ∈ F, IsTestC f) ∧ ∀ f, IsTestC f → ∃ K, IsCompact K ∧ tsupport f ⊆ K ∧
    (∃ φ ∈ F, (∀ z, 0 ≤ φ z) ∧ ∀ z ∈ K, 1 ≤ φ z) ∧
    ∀ η > 0, ∃ g ∈ F, tsupport g ⊆ K ∧ ∀ z, |f z - g z| ≤ η

theorem tendsto_of_denseTestFamilyC {μs : ℕ → Measure ℂ}
    (hfin : ∀ K, IsCompact K → ∀ᶠ k in atTop, μs k K < ∞) {F : Set (ℂ → ℝ)}
    (hF : IsDenseTestFamilyC F)
    (hconv : ∀ f ∈ F, ∃ l, Tendsto (fun k => ∫ z, f z ∂(μs k)) atTop (𝓝 l))
    (f : ℂ → ℝ) (hf : IsTestC f) :
    ∃ l, Tendsto (fun k => ∫ z, f z ∂(μs k)) atTop (𝓝 l) := by
  obtain ⟨K, hK, hfK, ⟨φ, hφF, hφ0, hφ1⟩, happrox⟩ := hF.2 f hf
  have hφ := hF.1 φ hφF
  obtain ⟨lφ, hlφ⟩ := hconv φ hφF
  refine cauchySeq_tendsto_of_complete (Metric.cauchySeq_iff.2 fun ε hε => ?_)
  set B := |lφ| + 1 with hB
  have hB0 : 0 < B := by positivity
  set η := ε / (4 * B) with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨g, hgF, hgK, hfg⟩ := happrox η hη0
  have hg := hF.1 g hgF
  obtain ⟨lg, hlg⟩ := hconv g hgF
  obtain ⟨N1, hN1⟩ := Metric.cauchySeq_iff.1 hlg.cauchySeq (ε / 2) (by positivity)
  have hev : ∀ᶠ k in atTop, |∫ z, f z ∂(μs k) - ∫ z, g z ∂(μs k)| ≤ ε / 4 := by
    have hbφ : ∀ᶠ k in atTop, ∫ z, φ z ∂(μs k) < B :=
      hlφ.eventually (gt_mem_nhds (by rw [hB]; linarith [le_abs_self lφ]))
    filter_upwards [hfin K hK, hfin _ hφ.2.isCompact, hbφ] with k hkK hkφ hkb
    have hif : Integrable f (μs k) := hf.integrable ((measure_mono hfK).trans_lt hkK)
    have hig : Integrable g (μs k) := hg.integrable ((measure_mono hgK).trans_lt hkK)
    have hiφ : Integrable φ (μs k) := hφ.integrable hkφ
    have hpt : ∀ z, |f z - g z| ≤ η * φ z := by
      intro z
      by_cases hz : z ∈ K
      · calc |f z - g z| ≤ η := hfg z
          _ = η * 1 := (mul_one η).symm
          _ ≤ η * φ z := mul_le_mul_of_nonneg_left (hφ1 z hz) hη0.le
      · rw [image_eq_zero_of_notMem_tsupport (fun h => hz (hfK h)),
          image_eq_zero_of_notMem_tsupport (fun h => hz (hgK h)), sub_zero, abs_zero]
        exact mul_nonneg hη0.le (hφ0 z)
    calc |∫ z, f z ∂(μs k) - ∫ z, g z ∂(μs k)| = |∫ z, (f z - g z) ∂(μs k)| := by
          rw [integral_sub hif hig]
      _ ≤ ∫ z, |f z - g z| ∂(μs k) := abs_integral_le_integral_abs
      _ ≤ ∫ z, η * φ z ∂(μs k) :=
          integral_mono (hif.sub hig).abs (hiφ.const_mul η) hpt
      _ = η * ∫ z, φ z ∂(μs k) := integral_const_mul _ _
      _ ≤ η * B := mul_le_mul_of_nonneg_left hkb.le hη0.le
      _ = ε / 4 := by rw [hη]; field_simp
  obtain ⟨N2, hN2⟩ := eventually_atTop.1 hev
  refine ⟨max N1 N2, fun m hm n hn => ?_⟩
  have h1 := hN2 m (le_of_max_le_right hm)
  have h2 := hN2 n (le_of_max_le_right hn)
  have h3 := hN1 m (le_of_max_le_left hm) n (le_of_max_le_left hn)
  rw [Real.dist_eq] at h3 ⊢
  calc |∫ z, f z ∂(μs m) - ∫ z, f z ∂(μs n)|
      ≤ |∫ z, f z ∂(μs m) - ∫ z, g z ∂(μs m)| + |∫ z, g z ∂(μs m) - ∫ z, g z ∂(μs n)| +
        |∫ z, g z ∂(μs n) - ∫ z, f z ∂(μs n)| := by
        have := abs_sub_le (∫ z, f z ∂(μs m)) (∫ z, g z ∂(μs m)) (∫ z, f z ∂(μs n))
        have := abs_sub_le (∫ z, g z ∂(μs m)) (∫ z, g z ∂(μs n)) (∫ z, f z ∂(μs n))
        linarith
    _ < ε / 4 + ε / 2 + ε / 4 := by
        rw [abs_sub_comm (∫ z, g z ∂(μs n))]
        linarith
    _ = ε := by ring

/-- A bump `φ_n ≥ 0`, `φ_n = 1` on `closedBall 0 n`, compactly supported. -/
theorem exists_bump_closedBall (n : ℕ) :
    ∃ φ : ℂ → ℝ, IsTestC φ ∧ (∀ z, 0 ≤ φ z) ∧ ∀ z ∈ closedBall (0 : ℂ) n, 1 ≤ φ z := by
  obtain ⟨φ, hφ1, -, hφc, hφr⟩ := exists_continuous_one_zero_of_isCompact (X := ℂ)
    (isCompact_closedBall (0 : ℂ) n) (isOpen_ball (x := (0 : ℂ)) (ε := (n : ℝ) + 1)).isClosed_compl
    (Set.disjoint_left.2 fun z hz hzt => hzt (mem_ball.2 (lt_of_le_of_lt (mem_closedBall.1 hz) (by linarith))))
  exact ⟨φ, ⟨φ.continuous, hφc⟩, fun z => (hφr z).1, fun z hz => by rw [hφ1 hz]; rfl⟩

/-- For each `n`, a countable family of test functions supported in `closedBall 0 n`, uniformly dense among the test
functions supported there. -/
theorem exists_dense_closedBall (n : ℕ) :
    ∃ D : Set (ℂ → ℝ), D.Countable ∧ (∀ g ∈ D, IsTestC g ∧ tsupport g ⊆ closedBall (0 : ℂ) n) ∧
      ∀ f, IsTestC f → tsupport f ⊆ closedBall (0 : ℂ) n → ∀ η > 0, ∃ g ∈ D, ∀ z, |f z - g z| ≤ η := by
  classical
  have : CompactSpace (closedBall (0 : ℂ) n) := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  let T : Set C(closedBall (0 : ℂ) n, ℝ) :=
    {F | ∃ f : ℂ → ℝ, (IsTestC f ∧ tsupport f ⊆ closedBall (0 : ℂ) n) ∧ ∀ x : closedBall (0 : ℂ) n, F x = f x}
  obtain ⟨c, hcT, hcc, hTc⟩ :=
    (TopologicalSpace.IsSeparable.of_separableSpace T).exists_countable_dense_subset
  let w : C(closedBall (0 : ℂ) n, ℝ) → (ℂ → ℝ) := fun F => if h : F ∈ T then h.choose else 0
  have hw : ∀ F ∈ T, (IsTestC (w F) ∧ tsupport (w F) ⊆ closedBall (0 : ℂ) n) ∧
      ∀ x : closedBall (0 : ℂ) n, F x = w F x := by
    intro F hF
    simp only [w, hF, ↓reduceDIte]
    exact hF.choose_spec
  refine ⟨w '' c, hcc.image w, ?_, ?_⟩
  · rintro g ⟨F, hF, rfl⟩
    exact (hw F (hcT hF)).1
  · intro f hf hfK η hη
    let F : C(closedBall (0 : ℂ) n, ℝ) := ⟨fun x => f x, hf.1.comp continuous_subtype_val⟩
    have hFT : F ∈ T := ⟨f, ⟨hf, hfK⟩, fun x => rfl⟩
    obtain ⟨G, hGc, hFG⟩ := Metric.mem_closure_iff.1 (hTc hFT) η hη
    obtain ⟨⟨hgt, hgK⟩, hGw⟩ := hw G (hcT hGc)
    refine ⟨w G, ⟨G, hGc, rfl⟩, fun z => ?_⟩
    by_cases hz : z ∈ closedBall (0 : ℂ) n
    · have h1 := ContinuousMap.dist_apply_le_dist (f := F) (g := G) ⟨z, hz⟩
      rw [Real.dist_eq] at h1
      have e1 : F ⟨z, hz⟩ = f z := rfl
      rw [e1, hGw ⟨z, hz⟩] at h1
      exact h1.trans hFG.le
    · rw [image_eq_zero_of_notMem_tsupport (fun h => hz (hfK h)),
        image_eq_zero_of_notMem_tsupport (fun h => hz (hgK h)), sub_zero, abs_zero]
      exact hη.le

/-- **A countable dense test family on `ℂ` exists.** -/
theorem exists_denseTestFamilyC : ∃ F : Set (ℂ → ℝ), F.Countable ∧ IsDenseTestFamilyC F := by
  choose D hDc hDt hDa using exists_dense_closedBall
  choose φ hφt hφ0 hφ1 using exists_bump_closedBall
  refine ⟨⋃ n, (D n ∪ {φ n}), countable_iUnion fun n => (hDc n).union (countable_singleton _), ?_, ?_⟩
  · intro f hf
    obtain ⟨n, hn⟩ := mem_iUnion.1 hf
    rcases hn with hn | hn
    · exact (hDt n f hn).1
    · rw [mem_singleton_iff.1 hn]
      exact hφt n
  · intro f hf
    obtain ⟨r, hr⟩ := (isBounded_iff_subset_closedBall (0 : ℂ)).1 hf.2.isCompact.isBounded
    obtain ⟨n, hn⟩ := exists_nat_ge r
    have hfn : tsupport f ⊆ closedBall (0 : ℂ) n := hr.trans (closedBall_subset_closedBall hn)
    refine ⟨closedBall (0 : ℂ) n, isCompact_closedBall _ _, hfn,
      ⟨φ n, mem_iUnion.2 ⟨n, Or.inr rfl⟩, hφ0 n, hφ1 n⟩, fun η hη => ?_⟩
    obtain ⟨g, hgD, hg⟩ := hDa n f hf hfn η hη
    exact ⟨g, mem_iUnion.2 ⟨n, Or.inl hgD⟩, (hDt n g hgD).2, hg⟩

/-- **Vague limit on `ℂ` from a dense countable family.** -/
theorem exists_isVagueLimitOn_univ_of_family {μs : ℕ → Measure ℂ}
    (hfin : ∀ K, IsCompact K → ∀ᶠ k in atTop, μs k K < ∞) {F : Set (ℂ → ℝ)} (hF : IsDenseTestFamilyC F)
    (hconv : ∀ f ∈ F, ∃ l, Tendsto (fun k => ∫ z, f z ∂(μs k)) atTop (𝓝 l)) :
    ∃ μ, QuantumZipper.IsVagueLimitOn univ μs μ :=
  QuantumZipper.VagueOpen.exists_isVagueLimitOn_of_tendsto_open isOpen_univ (fun K hK _ => hfin K hK)
    fun f hf hfc _ => tendsto_of_denseTestFamilyC hfin hF hconv f ⟨hf, hfc⟩

end VagueWholePlane
end MatedCRT
