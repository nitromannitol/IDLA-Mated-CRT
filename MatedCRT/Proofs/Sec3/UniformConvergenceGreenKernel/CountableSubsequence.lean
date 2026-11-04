import MatedCRT.Proofs.Sec3.UniformConvergenceGreenKernel.SmoothTests

/-! # A common subsequence for countably many tests -/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric HarmonicBalls
open scoped ContDiff

private noncomputable def chooseSubsequence {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : ℕ → ℕ → Ω → ℝ) (Y : ℕ → Ω → ℝ)
    (h : ∀ i, TendstoInMeasure P (F i) atTop (Y i)) (i : ℕ) (φ : ℕ → ℕ) : ℕ → ℕ := by
  classical
  exact if hφ : StrictMono φ then
    Classical.choose ((h i).comp hφ.tendsto_atTop).exists_seq_tendsto_ae
  else id

private theorem chooseSubsequence_spec {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : ℕ → ℕ → Ω → ℝ) (Y : ℕ → Ω → ℝ)
    (h : ∀ i, TendstoInMeasure P (F i) atTop (Y i)) (i : ℕ) (φ : ℕ → ℕ)
    (hφ : StrictMono φ) :
    StrictMono (chooseSubsequence P F Y h i φ) ∧
      ∀ᵐ sample ∂P, Tendsto (fun n => F i (φ (chooseSubsequence P F Y h i φ n)) sample)
        atTop (𝓝 (Y i sample)) := by
  simpa only [chooseSubsequence, dite_eq_left hφ, Function.comp_def] using
    (Classical.choose_spec ((h i).comp hφ.tendsto_atTop).exists_seq_tendsto_ae)

private noncomputable def stages {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : ℕ → ℕ → Ω → ℝ) (Y : ℕ → Ω → ℝ)
    (h : ∀ i, TendstoInMeasure P (F i) atTop (Y i)) : ℕ → ℕ → ℕ
  | 0 => id
  | i + 1 => stages P F Y h i ∘ chooseSubsequence P F Y h i (stages P F Y h i)

private theorem stages_strictMono {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : ℕ → ℕ → Ω → ℝ) (Y : ℕ → Ω → ℝ)
    (h : ∀ i, TendstoInMeasure P (F i) atTop (Y i)) : ∀ i, StrictMono (stages P F Y h i)
  | 0 => strictMono_id
  | i + 1 => (stages_strictMono P F Y h i).comp
      (chooseSubsequence_spec P F Y h i _ (stages_strictMono P F Y h i)).1

private theorem stages_nested {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : ℕ → ℕ → Ω → ℝ) (Y : ℕ → Ω → ℝ)
    (h : ∀ i, TendstoInMeasure P (F i) atTop (Y i)) (i : ℕ) :
    ∀ j, i ≤ j → ∀ n, ∃ m, n ≤ m ∧ stages P F Y h j n = stages P F Y h i m := by
  intro j hij
  induction j, hij using Nat.le_induction with
  | base => exact fun n => ⟨n, le_rfl, rfl⟩
  | succ j hij ih =>
    intro n
    let q := chooseSubsequence P F Y h j (stages P F Y h j)
    obtain ⟨m, hm, he⟩ := ih (q n)
    have hq : StrictMono q := (chooseSubsequence_spec P F Y h j _
      (stages_strictMono P F Y h j)).1
    exact ⟨m, (hq.id_le n).trans hm, he⟩

/-- Countably many sequences converging in measure have a common deterministic
subsequence along which all converge almost surely. -/
theorem exists_subseq_ae_of_countable_tendstoInMeasure
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : ℕ → ℕ → Ω → ℝ) (Y : ℕ → Ω → ℝ)
    (h : ∀ i, TendstoInMeasure P (F i) atTop (Y i)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ sample ∂P, ∀ i,
      Tendsto (fun n => F i (φ n) sample) atTop (𝓝 (Y i sample)) := by
  let stage := stages P F Y h
  let φ : ℕ → ℕ := fun n => stage (n + 1) n
  have hmono : StrictMono φ := by
    refine strictMono_nat_of_lt_succ fun n => ?_
    show stage (n + 1) n < stage (n + 1)
      (chooseSubsequence P F Y h (n + 1) (stage (n + 1)) (n + 1))
    exact stages_strictMono P F Y h (n + 1)
      (lt_of_lt_of_le n.lt_succ_self
        ((chooseSubsequence_spec P F Y h (n + 1) _
          (stages_strictMono P F Y h (n + 1))).1.id_le _))
  refine ⟨φ, hmono, ?_⟩
  have hstage : ∀ i, ∀ᵐ sample ∂P,
      Tendsto (fun n => F i (stage (i + 1) n) sample) atTop (𝓝 (Y i sample)) := by
    intro i
    exact (chooseSubsequence_spec P F Y h i _ (stages_strictMono P F Y h i)).2
  filter_upwards [ae_all_iff.mpr hstage] with sample hsample
  intro i
  have hlim := hsample i
  rw [Filter.tendsto_atTop'] at hlim ⊢
  intro s hs
  obtain ⟨N, hN⟩ := hlim s hs
  refine ⟨max i N, fun n hn => ?_⟩
  obtain ⟨m, hm, he⟩ := stages_nested P F Y h (i + 1) (n + 1)
    (Nat.succ_le_succ (le_of_max_le_left hn)) n
  show F i (stage (n + 1) n) sample ∈ s
  change F i (stages P F Y h (n + 1) n) sample ∈ s
  rw [he]
  exact hN m ((le_of_max_le_right hn).trans hm)

/-- A countable family of convergences in probability admits an almost-sure
subsequence along any mesh sequence. -/
theorem exists_subseq_ae_of_countable_tendstoInProbability
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : ℕ → ℝ → Ω → ℝ) (Y : ℕ → Ω → ℝ)
    (h : ∀ i, TendstoInProbability P (F i) (Y i))
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝[>] 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ sample ∂P, ∀ i,
      Tendsto (fun n => F i (ε (φ n)) sample) atTop (𝓝 (Y i sample)) := by
  exact exists_subseq_ae_of_countable_tendstoInMeasure P (fun i n => F i (ε n)) Y
    (fun i => (h i).tendstoInMeasure_sequence hε)

/-- Two countable families of convergences in probability admit the same
almost-sure subsequence. -/
theorem exists_subseq_ae_of_two_countable_tendstoInProbability
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F G : ℕ → ℝ → Ω → ℝ) (Y Z : ℕ → Ω → ℝ)
    (hF : ∀ i, TendstoInProbability P (F i) (Y i))
    (hG : ∀ i, TendstoInProbability P (G i) (Z i))
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝[>] 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ sample ∂P, ∀ i,
      Tendsto (fun n => F i (ε (φ n)) sample) atTop (𝓝 (Y i sample)) ∧
      Tendsto (fun n => G i (ε (φ n)) sample) atTop (𝓝 (Z i sample)) := by
  obtain ⟨φ, hφ, hFae⟩ := exists_subseq_ae_of_countable_tendstoInProbability P F Y hF ε hε
  obtain ⟨ψ, hψ, hGae⟩ := exists_subseq_ae_of_countable_tendstoInProbability P G Z hG
    (fun n => ε (φ n)) (hε.comp hφ.tendsto_atTop)
  refine ⟨φ ∘ ψ, hφ.comp hψ, ?_⟩
  filter_upwards [hFae, hGae] with sample hFsample hGsample
  intro i
  exact ⟨(hFsample i).comp hψ.tendsto_atTop, hGsample i⟩

/-- A countable family of smooth tests admits a common subsequence for both
weighted-degree and Green-occupation integral convergence. -/
theorem smooth_tests_integrals_ae_subsequence (𝒮 : SpaceFillingSLEModel)
    (h210 : DegreeMeasureConvergenceStmt 𝒮) (h34 : IntegralConvergenceGreenFunctionStmt 𝒮)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {r : ℝ} {z y : ℂ} (hr : 0 < r) (hball : ball z r ⊆ ball 0 ρ)
    (hy : y ∈ ball z r) (f : ℕ → ℂ → ℝ) (hf : ∀ i, ContDiff ℝ ∞ (f i))
    (hfc : ∀ i, HasCompactSupport (f i)) (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝[>] 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ sample ∂S.P, ∀ i,
      Tendsto (fun n => ∫ x, f i x ∂degreeWeightedMeasure (S.mult (ε (φ n)) sample)
        (ε (φ n)) (S.η sample) (S.μ sample)) atTop
        (𝓝 (6 * ∫ x, f i x ∂S.μ sample)) ∧
      Tendsto (fun n => (S.mε (ε (φ n)))⁻¹ *
        ∑' x : cellVertices (ε (φ n)) (S.η sample) (ball z r),
          greenFn (S.mult (ε (φ n)) sample)
            (interiorCellVertices (ε (φ n)) (S.η sample) (ball z r))
            (vertexOf (ε (φ n)) (S.η sample) y) x *
              f i (vertexPoint (ε (φ n)) (S.η sample) x)) atTop
        (𝓝 (S.c₀ * ∫ x in ball z r, greenFunction (ball z r) y x * f i x ∂S.μ sample)) := by
  exact exists_subseq_ae_of_two_countable_tendstoInProbability S.P _ _ _ _
    (fun i => h210 γ hγ hγ2 Ω S hS (f i) (hf i).continuous (hfc i))
    (fun i => integralConvergenceGreenFunction_smooth_test 𝒮 h34 hγ hγ2 hρ hρ1 S hS
      hr hball hy (f i) (hf i) (hfc i)) ε hε

end MatedCRT
