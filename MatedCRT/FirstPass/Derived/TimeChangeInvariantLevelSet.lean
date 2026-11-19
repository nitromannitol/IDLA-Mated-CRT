import MatedCRT.FirstPass.Derived.TimeChangeInvariantTruncation

/-!
# Level sets of the density of an invariant measure of the time change

Let `A` be a PCAF of planar Brownian motion with a good clock, `P_u = timeChangeKernel A u` the kernel of the time
change and `μ_A` the Revuz measure.  For a `σ`-finite measure `ν` invariant for the time change put `λ = ν + μ_A`,
`f = dν/dλ`, and for `a ∈ [0, ∞)` let `F = {f > a}`.  Then `λ` restricted to `F` and `λ` restricted to `Fᶜ` are
invariant for the time change.

The densities `φ_n = min (n (f - a), 1)` are differences `min (n f, n a + 1) - min (n f, n a)` of truncations, which
are invariant (`bind_timeChangeKernel_withDensity_min_eq`); cancelling the `σ`-finite measure `min (n f, n a) λ`
shows that `φ_n λ` is invariant, and `φ_n` increases to the indicator of `F`, so that the monotone convergence
theorem gives the invariance of `λ` restricted to `F`.  Cancelling `λ` restricted to `F` in the invariant measure
`λ` gives the invariance of `λ` restricted to `Fᶜ`.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

namespace MatedCRT

open MarkovProcess _root_.HarmonicBalls

/-- An increasing limit of densities giving invariant measures of a kernel gives an invariant measure. -/
theorem comp_withDensity_iSup_eq {α : Type*} [MeasurableSpace α] {K : Kernel α α} {L : Measure α}
    {g : ℕ → α → ℝ≥0∞} (hg : ∀ n, Measurable (g n)) (hmono : Monotone g)
    (h : ∀ n, K ∘ₘ L.withDensity (g n) = L.withDensity (g n)) :
    K ∘ₘ L.withDensity (fun x => ⨆ n, g n x) = L.withDensity (fun x => ⨆ n, g n x) := by
  ext S hS
  have hKS : Measurable fun x => K x S := Kernel.measurable_coe K hS
  have h1 : ∀ n, ∫⁻ x, g n x * K x S ∂L = ∫⁻ x in S, g n x ∂L := fun n => by
    rw [show ∫⁻ x, g n x * K x S ∂L = ∫⁻ x, (g n * fun x => K x S) x ∂L from rfl,
      ← lintegral_withDensity_eq_lintegral_mul₀ (hg n).aemeasurable hKS.aemeasurable,
      ← Measure.bind_apply hS (Kernel.aemeasurable _), h n, withDensity_apply _ hS]
  rw [Measure.bind_apply hS (Kernel.aemeasurable _), withDensity_apply _ hS,
    lintegral_withDensity_eq_lintegral_mul₀ (Measurable.iSup hg).aemeasurable hKS.aemeasurable]
  simp only [Pi.mul_apply]
  calc ∫⁻ x, (⨆ n, g n x) * K x S ∂L = ∫⁻ x, ⨆ n, g n x * K x S ∂L := by
        congr 1; funext x; rw [ENNReal.iSup_mul]
    _ = ⨆ n, ∫⁻ x, g n x * K x S ∂L :=
        lintegral_iSup (fun n => (hg n).mul hKS) fun n m hnm x => by
          dsimp only; gcongr; exact hmono hnm x
    _ = ⨆ n, ∫⁻ x in S, g n x ∂L := by simp only [h1]
    _ = ∫⁻ x in S, ⨆ n, g n x ∂L := (lintegral_iSup hg hmono).symm

/-- The truncation `min (n t, n a + 1)` is the sum of `min (n (t - a), 1)` and `min (n t, n a)`. -/
theorem min_natCast_mul_eq_add (t a : ℝ≥0∞) (n : ℕ) :
    min ((n : ℝ≥0∞) * t) (n * a + 1) = min ((n : ℝ≥0∞) * (t - a)) 1 + min ((n : ℝ≥0∞) * t) (n * a) := by
  rcases le_or_gt t a with h | h
  · have hle : (n : ℝ≥0∞) * t ≤ n * a := by gcongr
    rw [tsub_eq_zero_of_le h, mul_zero, min_eq_left zero_le_one, zero_add, min_eq_left hle,
      min_eq_left (hle.trans le_self_add)]
  · have hle : (n : ℝ≥0∞) * a ≤ n * t := by gcongr
    rw [min_eq_right hle, ENNReal.mul_sub (fun _ _ => ENNReal.natCast_ne_top n), ← min_add_add_right,
      tsub_add_cancel_of_le hle, add_comm 1]

/-- The densities `min (n (f - a), 1)` increase with `n`. -/
theorem monotone_min_natCast_mul_tsub {α : Type*} (f : α → ℝ≥0∞) (a : ℝ≥0∞) :
    Monotone fun (n : ℕ) (x : α) => min ((n : ℝ≥0∞) * (f x - a)) 1 := fun n m hnm x => by
  dsimp only
  gcongr

/-- The densities `min (n (f - a), 1)` increase to the indicator of `{f > a}`. -/
theorem iSup_min_natCast_mul_tsub {α : Type*} (f : α → ℝ≥0∞) (a : ℝ≥0∞) (x : α) :
    ⨆ n : ℕ, min ((n : ℝ≥0∞) * (f x - a)) 1 = {y | a < f y}.indicator 1 x := by
  by_cases h : a < f x
  · rw [indicator_of_mem (show x ∈ {y | a < f y} from h), Pi.one_apply]
    refine le_antisymm (iSup_le fun n => min_le_right _ _) ?_
    obtain ⟨n, hn⟩ := ENNReal.exists_nat_mul_gt (tsub_pos_of_lt h).ne' ENNReal.one_ne_top
    exact le_iSup_of_le n (le_min hn.le le_rfl)
  · rw [indicator_of_notMem (show x ∉ {y | a < f y} from h), tsub_eq_zero_of_le (not_lt.1 h)]
    simp

/-- **Level sets of the density of an invariant measure**: for `ν` `σ`-finite and invariant for the time change,
`λ = ν + μ_A`, `f = dν/dλ` and `a ∈ [0, ∞)`, the restriction of `λ` to `{f > a}` is invariant for the time
change. -/
theorem bind_timeChangeKernel_restrict_levelSet_eq {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsPCAF planarLaw A) (hG : GoodClock planarLaw A) {ν : Measure ℂ} [SigmaFinite ν]
    (hν : ∀ u, timeChangeKernel A u ∘ₘ ν = ν) (a : ℝ≥0) (u : ℝ≥0) :
    timeChangeKernel A u ∘ₘ (ν + revuz planarLaw A).restrict
        {x | (a : ℝ≥0∞) < ν.rnDeriv (ν + revuz planarLaw A) x} =
      (ν + revuz planarLaw A).restrict {x | (a : ℝ≥0∞) < ν.rnDeriv (ν + revuz planarLaw A) x} := by
  have : SigmaFinite (revuz planarLaw A) := sigmaFinite_revuz hA hG
  set L := ν + revuz planarLaw A with hL
  set f := ν.rnDeriv L with hf
  have hfm : Measurable f := Measure.measurable_rnDeriv _ _
  set φ : ℕ → ℂ → ℝ≥0∞ := fun n x => min ((n : ℝ≥0∞) * (f x - a)) 1 with hφdef
  have hφm : ∀ n, Measurable (φ n) := fun n =>
    (measurable_const.mul (hfm.sub measurable_const)).min measurable_const
  have hφ : ∀ n, timeChangeKernel A u ∘ₘ L.withDensity (φ n) = L.withDensity (φ n) := by
    intro n
    have h1 := bind_timeChangeKernel_withDensity_min_eq hA hG hν (n : ℝ≥0∞) (n * a + 1) u
    have h2 := bind_timeChangeKernel_withDensity_min_eq hA hG hν (n : ℝ≥0∞) (n * a) u
    rw [← hL, ← hf] at h1 h2
    set g₂ : ℂ → ℝ≥0∞ := fun x => min ((n : ℝ≥0∞) * f x) ((n * a : ℝ≥0) : ℝ≥0∞) with hg₂
    have hg₂m : Measurable g₂ := (measurable_const.mul hfm).min measurable_const
    have hsplit : L.withDensity (fun x => min ((n : ℝ≥0∞) * f x) ((n * a + 1 : ℝ≥0) : ℝ≥0∞)) =
        L.withDensity (φ n) + L.withDensity g₂ := by
      rw [← withDensity_add_right _ hg₂m]
      congr 1
      funext x
      simp only [hφdef, hg₂, Pi.add_apply]
      push_cast
      exact min_natCast_mul_eq_add (f x) a n
    have : SigmaFinite (L.withDensity g₂) :=
      SigmaFinite.withDensity_of_ne_top' fun x => ((min_le_right _ _).trans_lt ENNReal.coe_lt_top).ne
    rw [← Measure.add_left_inj (L.withDensity g₂), ← hsplit]
    conv_lhs => rw [← h2]
    rw [← Measure.comp_add, ← hsplit, h1]
  have hF : L.restrict {x | (a : ℝ≥0∞) < f x} = L.withDensity (fun x => ⨆ n, φ n x) := by
    rw [← withDensity_indicator_one (measurableSet_lt measurable_const hfm)]
    congr 1
    funext x
    exact (iSup_min_natCast_mul_tsub f a x).symm
  rw [hF]
  exact comp_withDensity_iSup_eq hφm (monotone_min_natCast_mul_tsub f a) hφ

/-- **Complements of level sets of the density of an invariant measure**: for `ν` `σ`-finite and invariant for the
time change, `λ = ν + μ_A`, `f = dν/dλ` and `a ∈ [0, ∞)`, the restriction of `λ` to `{f ≤ a}` is invariant for the
time change. -/
theorem bind_timeChangeKernel_restrict_levelSet_compl_eq {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsPCAF planarLaw A) (hG : GoodClock planarLaw A) {ν : Measure ℂ} [SigmaFinite ν]
    (hν : ∀ u, timeChangeKernel A u ∘ₘ ν = ν) (a : ℝ≥0) (u : ℝ≥0) :
    timeChangeKernel A u ∘ₘ (ν + revuz planarLaw A).restrict
        {x | (a : ℝ≥0∞) < ν.rnDeriv (ν + revuz planarLaw A) x}ᶜ =
      (ν + revuz planarLaw A).restrict {x | (a : ℝ≥0∞) < ν.rnDeriv (ν + revuz planarLaw A) x}ᶜ := by
  have : SigmaFinite (revuz planarLaw A) := sigmaFinite_revuz hA hG
  have hF := bind_timeChangeKernel_restrict_levelSet_eq hA hG hν a u
  set L := ν + revuz planarLaw A with hL
  set F := {x | (a : ℝ≥0∞) < ν.rnDeriv L x} with hFdef
  have hFm : MeasurableSet F := measurableSet_lt measurable_const (Measure.measurable_rnDeriv _ _)
  have hLinv : timeChangeKernel A u ∘ₘ L = L :=
    bind_timeChangeKernel_add_eq hν (bind_timeChangeKernel_revuz_eq hA hG) u
  rw [← Measure.add_left_inj (L.restrict F)]
  conv_lhs => rw [← hF]
  rw [← Measure.comp_add, Measure.restrict_compl_add_restrict hFm, hLinv]

end MatedCRT
