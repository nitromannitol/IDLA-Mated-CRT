import MatedCRT.Proofs.Sec3.UniformConvergenceGreenKernel.KernelMonotonicity
import MatedCRT.Proofs.Sec5.StoppedSurplusSteps

/-!
# Layer-potential reduction for `StoppedLayerPotentialStep` (steps2-r2, Section 9)

Source: `notes/wpn-steps2/steps2-r2.tex`, target proof lines 3617-3744 (finite-potential domination and the
outer-probability reduction), with its inputs at 3371-3615. The declaration reduced here is
`MatedCRT.StoppedLayerPotentialStep` (`Proofs/Sec5/StoppedSurplusSteps.lean:68`). Its layer sum is
`∑ᶠ b ∈ A \ D, greenKernel m A a b` with `greenKernel = greenFn / mdeg`: there is no further division by degree.

Proved here, with no hypothesis beyond those displayed:

* Part 1 (`sum_greenKernel_le_four_mul_potential`, `finsum_greenKernel_le_four_mul_potential`): the finite Green
  comparison `∑_{b ∈ E} g_A(a,b) ≤ 4 ∑_{b ∈ S} f(b) G_D(a,b)` for finite `A ⊆ D`, `E ⊆ S`, when the uncovered-cell
  cutoff satisfies `f ≥ 1/4` on `E` (steps2-r2 eq:layercutoff). It uses domain monotonicity of the kernel
  (`greenKernel_mono_of_finite`), positive degree (`greenKernel ≤ greenFn`) and `greenFn ≥ 0`.
* Part 2 (`tendsToOneOn_layer_of_domination`): the `r`-then-`n`-then-`ε` outer-probability argument (steps2-r2
  3700-3744), with the cutoff, core, Harnack and fixed-center inputs entering only as the named hypotheses
  `hZ`, `hJ`, `hdom`.
-/

namespace MatedCRT

open MeasureTheory Filter Topology Set
open scoped ENNReal

/-- **Part 1 (finite Green comparison, `Finset` form).** For finite domains `A ⊆ D` and finite vertex sets `E ⊆ S`,
with `f ≥ 0` on `S` and `f ≥ 1/4` on `E` (the uncovered-cell cutoff, steps2-r2 eq:layercutoff),
`∑_{b ∈ E} g_A(a,b) ≤ 4 ∑_{b ∈ S} f(b) G_D(a,b)`, where `g = G / mdeg` is the degree-normalized kernel.
Positive degree gives `g_D ≤ G_D`; domain monotonicity gives `g_A ≤ g_D`; `G_D ≥ 0`. -/
theorem sum_greenKernel_le_four_mul_potential {m : ℤ → ℤ → ℕ} {A D : Set ℤ}
    (hlf : ∀ a, {b | m a b ≠ 0}.Finite) (hcons : ∀ a, m a (a + 1) ≠ 0)
    (hA : A.Finite) (hD : D.Finite) (hAD : A ⊆ D) (a : ℤ) (E S : Finset ℤ) (hES : E ⊆ S)
    (f : ℤ → ℝ) (hf0 : ∀ b ∈ S, 0 ≤ f b) (hf : ∀ b ∈ E, 1 / 4 ≤ f b) :
    ∑ b ∈ E, greenKernel m A a b ≤ 4 * ∑ b ∈ S, f b * greenFn m D a b := by
  have h1 : ∀ b ∈ E, greenKernel m A a b ≤ 4 * (f b * greenFn m D a b) := by
    intro b hb
    have hdeg : (1 : ℝ) ≤ (mdeg m b : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.2 (mdeg_pos_of_ne_zero hlf (hcons b)).ne'
    have hG : 0 ≤ greenFn m D a b := greenFn_nonnegative m D a b
    have hkern : greenKernel m D a b ≤ greenFn m D a b := by
      unfold greenKernel
      exact div_le_self hG hdeg
    have hfb : (1 : ℝ) ≤ 4 * f b := by linarith [hf b hb]
    calc greenKernel m A a b ≤ greenKernel m D a b :=
          greenKernel_mono_of_finite hlf hcons hA hD hAD a b
      _ ≤ greenFn m D a b := hkern
      _ ≤ (4 * f b) * greenFn m D a b := le_mul_of_one_le_left hG hfb
      _ = 4 * (f b * greenFn m D a b) := by ring
  calc ∑ b ∈ E, greenKernel m A a b ≤ ∑ b ∈ E, 4 * (f b * greenFn m D a b) := Finset.sum_le_sum h1
    _ = 4 * ∑ b ∈ E, f b * greenFn m D a b := by rw [Finset.mul_sum]
    _ ≤ 4 * ∑ b ∈ S, f b * greenFn m D a b :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum_of_subset_of_nonneg hES
          (fun b hb _ => mul_nonneg (hf0 b hb) (greenFn_nonnegative m D a b)))
        (by norm_num)

/-- **Part 1 (finite Green comparison, `finsum` form).** The same bound for the `finsum` layer sum of
`StoppedLayerPotentialStep`, over finite sets `E ⊆ S` (on `{t < T}` the set `A` is finite by properness). -/
theorem finsum_greenKernel_le_four_mul_potential {m : ℤ → ℤ → ℕ} {A D E S : Set ℤ}
    (hlf : ∀ a, {b | m a b ≠ 0}.Finite) (hcons : ∀ a, m a (a + 1) ≠ 0)
    (hA : A.Finite) (hD : D.Finite) (hAD : A ⊆ D) (hE : E.Finite) (hS : S.Finite) (hES : E ⊆ S)
    (f : ℤ → ℝ) (hf0 : ∀ b ∈ S, 0 ≤ f b) (hf : ∀ b ∈ E, 1 / 4 ≤ f b) (a : ℤ) :
    ∑ᶠ b ∈ E, greenKernel m A a b ≤ 4 * ∑ᶠ b ∈ S, f b * greenFn m D a b := by
  rw [finsum_mem_eq_finite_toFinset_sum _ hE, finsum_mem_eq_finite_toFinset_sum _ hS]
  refine sum_greenKernel_le_four_mul_potential hlf hcons hA hD hAD a hE.toFinset hS.toFinset ?_ f ?_ ?_
  · intro b hb
    exact hS.mem_toFinset.2 (hES (hE.mem_toFinset.1 hb))
  · intro b hb
    exact hf0 b (hS.mem_toFinset.1 hb)
  · intro b hb
    exact hf b (hE.mem_toFinset.1 hb)

/-- **Part 2 (outer-probability reduction, `r`-then-`n`-then-`ε`).** Notation: `A ε ω` is the layer set `V^ε(Λ_t)`,
`L ε ω a` the layer sum `∑_{b ∈ E} g_A(a,b)` (rescaled), `G ε n r` the good event of the cutoff/core/Harnack components
at level `(n, r)`, `Z r ω` the small local potential (first term of steps2-r2 3700-3712) and `Q ε n r ω` the
finite-center potential (second term, `p⁻¹ max_j H_{ε,n}(a^ε_{y_j})`).

Named hypotheses (none is the target estimate):
* `hZ`: small local potentials, `P(F ∩ {c < Z_r}) < η` for some `r` below `r₀`;
* `hJ`: for such `r`, some `n` makes `P(F ∩ {c < Q_{ε,n,r}}) < η` and `P(F ∩ G_{ε,n,r}ᶜ) < η` for all small `ε`
  (fixed-center convergence and the continuum limit `n → ∞`);
* `hdom`: on the good event, `ε L ≤ 4 Z_r + 4 Q_{ε,n,r}` for every starting vertex, for small `ε`
  (Part 1 with the cutoff, then the finite-center Harnack inequality).

Conclusion: the layer target `{∀ a ∈ A ε ω, L ε ω a ≤ κ / ε}` holds in the `TendsToOneOn` sense on `F`. -/
theorem tendsToOneOn_layer_of_domination {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (F : Set Ω)
    (A : ℝ → Ω → Set ℤ) (L : ℝ → Ω → ℤ → ℝ) (G : ℝ → ℕ → ℝ → Set Ω)
    (Z : ℝ → Ω → ℝ) (Q : ℝ → ℕ → ℝ → Ω → ℝ) (r₀ : ℝ) (κ : ℝ) (hκ : 0 < κ)
    (hZ : ∀ c : ℝ, 0 < c → ∀ η : ℝ≥0∞, 0 < η → ∃ r : ℝ, 0 < r ∧ r < r₀ ∧
      P (F ∩ {ω | c < Z r ω}) < η)
    (hJ : ∀ c : ℝ, 0 < c → ∀ η : ℝ≥0∞, 0 < η → ∀ r : ℝ, 0 < r → r < r₀ → ∃ n : ℕ,
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), P (F ∩ {ω | c < Q ε n r ω}) < η) ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), P (F ∩ (G ε n r)ᶜ) < η))
    (hdom : ∀ r : ℝ, 0 < r → r < r₀ → ∀ n : ℕ, ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ ω ∈ F ∩ G ε n r,
      ∀ a ∈ A ε ω, ε * L ε ω a ≤ 4 * Z r ω + 4 * Q ε n r ω) :
    TendsToOneOn P F (fun ε => {ω | ∀ a ∈ A ε ω, L ε ω a ≤ κ / ε}) := by
  dsimp only [TendsToOneOn]
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  have hη3 : (0 : ℝ≥0∞) < η / 3 := ENNReal.div_pos_iff.2 ⟨hη.ne', by norm_num⟩
  obtain ⟨r, hr, hrr₀, hZr⟩ := hZ (κ / 8) (div_pos hκ (by norm_num)) (η / 3) hη3
  obtain ⟨n, hQn, hGn⟩ := hJ (κ / 8) (div_pos hκ (by norm_num)) (η / 3) hη3 r hr hrr₀
  filter_upwards [hQn, hGn, hdom r hr hrr₀ n, eventually_mem_nhdsWithin] with ε hQε hGε hdε hεpos
  have hεpos' : 0 < ε := hεpos
  have hsub : F ∩ {ω | ∀ a ∈ A ε ω, L ε ω a ≤ κ / ε}ᶜ ⊆
      (F ∩ (G ε n r)ᶜ) ∪ (F ∩ {ω | κ / 8 < Z r ω}) ∪ (F ∩ {ω | κ / 8 < Q ε n r ω}) := by
    rintro ω ⟨hF, hbad⟩
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall] at hbad
    obtain ⟨a, haA, hLa⟩ := hbad
    by_cases hG : ω ∈ G ε n r
    · by_cases hZω : κ / 8 < Z r ω
      · exact Or.inl (Or.inr ⟨hF, hZω⟩)
      · by_cases hQω : κ / 8 < Q ε n r ω
        · exact Or.inr ⟨hF, hQω⟩
        · exfalso
          have h := hdε ω ⟨hF, hG⟩ a haA
          push Not at hZω hQω
          have hL : κ < L ε ω a * ε := (div_lt_iff₀ hεpos').1 (not_le.1 hLa)
          linarith [mul_comm ε (L ε ω a)]
    · exact Or.inl (Or.inl ⟨hF, hG⟩)
  have hU : P (F ∩ {ω | ∀ a ∈ A ε ω, L ε ω a ≤ κ / ε}ᶜ) ≤
      P (F ∩ (G ε n r)ᶜ) + P (F ∩ {ω | κ / 8 < Z r ω}) + P (F ∩ {ω | κ / 8 < Q ε n r ω}) :=
    (measure_mono hsub).trans
      ((measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl))
  calc P (F ∩ {ω | ∀ a ∈ A ε ω, L ε ω a ≤ κ / ε}ᶜ)
      ≤ P (F ∩ (G ε n r)ᶜ) + P (F ∩ {ω | κ / 8 < Z r ω}) + P (F ∩ {ω | κ / 8 < Q ε n r ω}) := hU
    _ ≤ η / 3 + η / 3 + η / 3 := add_le_add (add_le_add hGε.le hZr.le) hQε.le
    _ = η := ENNReal.add_thirds η

end MatedCRT
