import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.RandomMeshVertex

/-! # Measurable random-mesh representatives on a common event -/

namespace MatedCRT

open Set MeasureTheory Filter Topology

/-- The event on which the measurable cell representative agrees with
    `vertexOf` is independent of the mesh sequence, random mesh, and point. -/
theorem MatedCRTEnv.IsValid.exists_commonEvent_measurable_vertexOf
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) :
    ∃ B : Set Ω, (∀ᵐ ω ∂S.P, ω ∈ B) ∧
      ∀ (e : ℕ → ℝ), (∀ j, 0 < e j) → ∀ (E : Ω → ℝ),
        Measurable[S.envSigma] E → (∀ ω, E ω ∈ range e) →
        ∃ a : Ω → ℂ → ℤ, (∀ x, Measurable[S.envSigma] fun ω => a ω x) ∧
          ∀ ω ∈ B, ∀ x, a ω x = vertexOf (E ω) (S.η ω) x := by
  classical
  obtain ⟨η, hηm, hη⟩ := hS.exists_envSigma_measurable_curve
  let B : Set Ω := {ω | (η ω : ℝ → ℂ) = S.η ω ∧
    Tendsto (S.η ω) (cocompact ℝ) (cocompact ℂ) ∧
    Function.Surjective (S.η ω)}
  have hB : ∀ᵐ ω ∂S.P, ω ∈ B := by
    filter_upwards [hη, hS.ae_tendsto_cocompact, hS.isAreaParametrized] with ω hω hp ha
    exact ⟨hω, hp, ha.2.2.1⟩
  refine ⟨B, hB, ?_⟩
  intro e he E hEm hEr
  choose V hVm hV using fun j => exists_measurable_vertexOf_curve (he j)
  have hex : ∀ ω, ∃ j, E ω = e j := fun ω => by
    obtain ⟨j, hj⟩ := hEr ω
    exact ⟨j, hj.symm⟩
  let I : Ω → ℕ := fun ω => Nat.find (hex ω)
  have hI : Measurable[S.envSigma] I := by
    let : MeasurableSpace Ω := S.envSigma
    exact Tightness.measurable_natFind hex (fun j => hEm (measurableSet_singleton (e j)))
  let a : Ω → ℂ → ℤ := fun ω x => V (I ω) (η ω, x)
  refine ⟨a, ?_, ?_⟩
  · intro x
    let : MeasurableSpace Ω := S.envSigma
    exact Tightness.measurable_comp_nat (fun j => (hVm j).comp (hηm.prodMk measurable_const)) hI
  · intro ω hω x
    have hp : Tendsto (η ω) (cocompact ℝ) (cocompact ℂ) := by rw [hω.1]; exact hω.2.1
    have hs : Function.Surjective (η ω) := by rw [hω.1]; exact hω.2.2
    dsimp [a]
    rw [hV (I ω) (η ω) x hp hs, hω.1, ← Nat.find_spec (hex ω)]

/-- A common environment event supports measurable diagonal selection for every
    countable family of fields, meshes, and spatial sample points. -/
theorem MatedCRTEnv.IsValid.exists_commonEvent_diagonal_rescale_randomMesh
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) :
    ∃ B : Set Ω, (∀ᵐ ω ∂S.P, ω ∈ B) ∧
      ∀ (e : ℕ → ℝ) (_he : ∀ j, 0 < e j) (E : Ω → ℕ → ℝ),
        (∀ n, Measurable[S.envSigma] fun ω => E ω n) →
        (∀ ω n, E ω n ∈ range e) →
      ∀ (u : ℕ → Ω → ℕ → ℤ → ℝ),
        (∀ j n a, Measurable[S.envSigma] fun ω => u j ω n a) →
      ∀ (x : ℕ → ℂ), ∃ Φ : Ω → ℕ → ℕ,
        (∀ k, Measurable[S.envSigma] fun ω => Φ ω k) ∧
        ∀ ω ∈ B, StrictMono (Φ ω) ∧ ∀ j i,
          (∃ M : ℝ, ∀ᶠ n in atTop,
            |rescale (S.mε (E ω n)) (E ω n) (S.η ω) (u j ω n) (x i)| ≤ M) →
          ∃ l : ℝ, Tendsto (fun k => rescale (S.mε (E ω (Φ ω k))) (E ω (Φ ω k))
            (S.η ω) (u j ω (Φ ω k)) (x i)) atTop (𝓝 l) := by
  classical
  obtain ⟨B, hB, hrep⟩ := hS.exists_commonEvent_measurable_vertexOf
  refine ⟨B, hB, ?_⟩
  intro e he E hEm hEr u hu x
  choose a ham hae using fun n => hrep e he (fun ω => E ω n) (hEm n) (fun ω => hEr ω n)
  let f : Ω → ℕ → ℕ → ℝ := fun ω n c =>
    (S.mε (E ω n))⁻¹ * u c.unpair.1 ω n (a n ω (x c.unpair.2))
  have hfm : ∀ n c, Measurable[S.envSigma] fun ω => f ω n c := by
    intro n c
    have hm : Measurable[S.envSigma] (fun ω => (S.mε (E ω n))⁻¹) :=
      @Tightness.measurable_comp_range Ω S.envSigma e (fun ω => E ω n) (hEm n)
        (fun ω => hEr ω n) (fun ε _ => (S.mε ε)⁻¹) (fun _ => measurable_const)
    have huv : Measurable[S.envSigma] (fun ω => u c.unpair.1 ω n (a n ω (x c.unpair.2))) := by
      let : MeasurableSpace Ω := S.envSigma
      exact measurable_countable_evaluation (fun ω => a n ω (x c.unpair.2))
        (ham n _) (fun b ω => u c.unpair.1 ω n b) (hu c.unpair.1 n)
    exact hm.mul huv
  have hfa : ∀ ω ∈ B, ∀ n c, f ω n c =
      rescale (S.mε (E ω n)) (E ω n) (S.η ω) (u c.unpair.1 ω n) (x c.unpair.2) := by
    intro ω hω n c
    simp [f, rescale, hae n ω hω]
  obtain ⟨Φ, hΦm, hΦ⟩ := @Tightness.exists_measurable_diagonal_subseq Ω S.envSigma f hfm
  refine ⟨Φ, hΦm, ?_⟩
  intro ω hω
  refine ⟨(hΦ ω).1, ?_⟩
  intro j i hb
  let c := Nat.pair j i
  have hb' : ∃ M : ℝ, ∀ᶠ n in atTop, |f ω n c| ≤ M := by
    obtain ⟨M, hM⟩ := hb
    refine ⟨M, hM.mono fun n hn => ?_⟩
    simpa [hfa ω hω n c, c] using hn
  obtain ⟨l, hl⟩ := (hΦ ω).2 c hb'
  exact ⟨l, by simpa only [hfa ω hω, c, Nat.unpair_pair] using hl⟩

end MatedCRT
