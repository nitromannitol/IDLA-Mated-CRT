import MatedCRT.Proofs.Sec3.UniformConvergenceGreenKernel.KernelMonotonicity
import MatedCRT.Proofs.Sec5.StoppedSurplusSteps
import MatedCRT.Proofs.Sec7.OdometerBoundMass.Laplacian

/-!
# Layer-potential reduction for `StoppedLayerPotentialStep`

The target is the finite-potential domination and the outer-probability reduction, with its inputs as named hypotheses. The declaration reduced here is
`MatedCRT.StoppedLayerPotentialStep` (`Proofs/Sec5/StoppedSurplusSteps.lean:68`). Its layer sum is
`∑ᶠ b ∈ A \ D, greenKernel m A a b` with `greenKernel = greenFn / mdeg`: there is no further division by degree.

Proved here, with no hypothesis beyond those displayed:

* Part 1 (`sum_greenKernel_le_four_mul_potential`, `finsum_greenKernel_le_four_mul_potential`): the finite Green
  comparison `∑_{b ∈ E} g_A(a,b) ≤ 4 ∑_{b ∈ S} f(b) G_D(a,b)` for finite `A ⊆ D`, `E ⊆ S`, when the uncovered-cell
  cutoff satisfies `f ≥ 1/4` on `E`. It uses domain monotonicity of the kernel
  (`greenKernel_mono_of_finite`), positive degree (`greenKernel ≤ greenFn`) and `greenFn ≥ 0`.
* Part 2 (`tendsToOneOn_layer_of_domination`): the `r`-then-`n`-then-`ε` outer-probability argument, with the cutoff, core, Harnack and fixed-center inputs entering only as named hypotheses.

Part 3 defines the discrete potential `layerPotential` (`H_{ε,n}`, in the normalization and
sum set of `IntegralConvergenceGreenFunctionStmt`) and four residual Steps: `LayerCutoffCoreStep`,
`LayerFiniteCenterHarnackStep`, `LayerExitMassSmallStep`, `LayerFixedCenterStep`. Each is stated with the six
antecedents of `StoppedLayerPotentialStep` as premises, as in `StoppedSurplusSteps.lean`. None is proved here.
-/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

/-! ### Part 1: finite Green comparison -/

/-- **Part 1 (finite Green comparison, `Finset` form).** For finite domains `A ⊆ D` and finite vertex sets `E ⊆ S`,
with `f ≥ 0` on `S` and `f ≥ 1/4` on `E` (the uncovered-cell cutoff),
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

/-! ### Part 2: outer-probability reduction (`r`-then-`n`-then-`ε`) -/

/-- **Part 2 (outer-probability reduction, `r`-then-`n`-then-`ε`).** Notation: `A ε ω` is the vertex set
`V^ε(Λ_t)`, `L ε ω a` the layer sum `∑_{b ∈ E} g_A(a,b)`, `G ε n r` the good event of the cutoff, core, Harnack and
exit-time components at level `(n, r)`, `Z r ω` the small local potential (the first term,
in `ℝ≥0∞` since the exit-time bound is an `ℝ≥0∞` inequality) and `Q ε n r ω` the finite-center potential.

Named hypotheses (none is the target estimate):
* `hZ`: small local potentials, `P(F ∩ {c < Z_r}) < η` for some `r < r₀`;
* `hJ`: for such `r`, some `n` makes `P(F ∩ {c < Q_{ε,n,r}}) < η` and `P(F ∩ G_{ε,n,r}ᶜ) < η` for small `ε`
  (fixed-center convergence, the continuum limit `n → ∞`, and the good-event probabilities);
* `hdom`: on the good event, `ε L ≤ 4 Z_r + 4 Q_{ε,n,r}` for every starting vertex, for small `ε`.

Conclusion: the layer target `{∀ a ∈ A ε ω, L ε ω a ≤ κ / ε}` holds in the `TendsToOneOn` sense on `F`. -/
theorem tendsToOneOn_layer_of_domination {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (F : Set Ω)
    (A : ℝ → Ω → Set ℤ) (L : ℝ → Ω → ℤ → ℝ) (G : ℝ → ℕ → ℝ → Set Ω)
    (Z : ℝ → Ω → ℝ≥0∞) (Q : ℝ → ℕ → ℝ → Ω → ℝ≥0∞) (r₀ κ : ℝ) (hκ : 0 < κ)
    (hZ : ∀ c : ℝ≥0∞, 0 < c → ∀ η : ℝ≥0∞, 0 < η → ∃ r : ℝ, 0 < r ∧ r < r₀ ∧
      P (F ∩ {ω | c < Z r ω}) < η)
    (hJ : ∀ c : ℝ≥0∞, 0 < c → ∀ η : ℝ≥0∞, 0 < η → ∀ r : ℝ, 0 < r → r < r₀ → ∃ n : ℕ,
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), P (F ∩ {ω | c < Q ε n r ω}) < η) ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), P (F ∩ (G ε n r)ᶜ) < η))
    (hdom : ∀ r : ℝ, 0 < r → r < r₀ → ∀ n : ℕ, ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ ω ∈ F ∩ G ε n r,
      ∀ a ∈ A ε ω, ENNReal.ofReal (ε * L ε ω a) ≤ 4 * Z r ω + 4 * Q ε n r ω) :
    TendsToOneOn P F (fun ε => {ω | ∀ a ∈ A ε ω, L ε ω a ≤ κ / ε}) := by
  dsimp only [TendsToOneOn]
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  have hη3 : (0 : ℝ≥0∞) < η / 3 := ENNReal.div_pos_iff.2 ⟨hη.ne', by norm_num⟩
  have hc : (0 : ℝ≥0∞) < ENNReal.ofReal (κ / 8) :=
    ENNReal.ofReal_pos.2 (div_pos hκ (by norm_num))
  have hkey : (4 : ℝ≥0∞) * ENNReal.ofReal (κ / 8) + 4 * ENNReal.ofReal (κ / 8) = ENNReal.ofReal κ := by
    rw [← add_mul, show (4 : ℝ≥0∞) + 4 = ENNReal.ofReal 8 from by rw [ENNReal.ofReal_ofNat]; norm_num,
      ← ENNReal.ofReal_mul (p := 8) (by norm_num)]
    congr 1
    ring
  obtain ⟨r, hr, hrr₀, hZr⟩ := hZ _ hc (η / 3) hη3
  obtain ⟨n, hQn, hGn⟩ := hJ _ hc (η / 3) hη3 r hr hrr₀
  filter_upwards [hQn, hGn, hdom r hr hrr₀ n, eventually_mem_nhdsWithin] with ε hQε hGε hdε hεpos
  have hεpos' : 0 < ε := hεpos
  have hsub : F ∩ {ω | ∀ a ∈ A ε ω, L ε ω a ≤ κ / ε}ᶜ ⊆
      (F ∩ (G ε n r)ᶜ) ∪ (F ∩ {ω | ENNReal.ofReal (κ / 8) < Z r ω}) ∪
        (F ∩ {ω | ENNReal.ofReal (κ / 8) < Q ε n r ω}) := by
    rintro ω ⟨hF, hbad⟩
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall] at hbad
    obtain ⟨a, haA, hLa⟩ := hbad
    by_cases hG : ω ∈ G ε n r
    · by_cases hZω : ENNReal.ofReal (κ / 8) < Z r ω
      · exact Or.inl (Or.inr ⟨hF, hZω⟩)
      · by_cases hQω : ENNReal.ofReal (κ / 8) < Q ε n r ω
        · exact Or.inr ⟨hF, hQω⟩
        · exfalso
          have h := hdε ω ⟨hF, hG⟩ a haA
          push Not at hZω hQω
          have h2 : ENNReal.ofReal (ε * L ε ω a) ≤ ENNReal.ofReal κ := by
            calc ENNReal.ofReal (ε * L ε ω a) ≤ 4 * Z r ω + 4 * Q ε n r ω := h
              _ ≤ 4 * ENNReal.ofReal (κ / 8) + 4 * ENNReal.ofReal (κ / 8) :=
                add_le_add (by gcongr) (by gcongr)
              _ = ENNReal.ofReal κ := hkey
          have h3 : ε * L ε ω a ≤ κ := (ENNReal.ofReal_le_ofReal_iff hκ.le).1 h2
          have hL : κ < L ε ω a * ε := (div_lt_iff₀ hεpos').1 (not_le.1 hLa)
          linarith [mul_comm ε (L ε ω a)]
    · exact Or.inl (Or.inl ⟨hF, hG⟩)
  have hU : P (F ∩ {ω | ∀ a ∈ A ε ω, L ε ω a ≤ κ / ε}ᶜ) ≤
      P (F ∩ (G ε n r)ᶜ) + P (F ∩ {ω | ENNReal.ofReal (κ / 8) < Z r ω}) +
        P (F ∩ {ω | ENNReal.ofReal (κ / 8) < Q ε n r ω}) :=
    (measure_mono hsub).trans
      ((measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl))
  calc P (F ∩ {ω | ∀ a ∈ A ε ω, L ε ω a ≤ κ / ε}ᶜ)
      ≤ P (F ∩ (G ε n r)ᶜ) + P (F ∩ {ω | ENNReal.ofReal (κ / 8) < Z r ω}) +
          P (F ∩ {ω | ENNReal.ofReal (κ / 8) < Q ε n r ω}) := hU
    _ ≤ η / 3 + η / 3 + η / 3 := add_le_add (add_le_add hGε.le hZr.le) hQε.le
    _ = η := ENNReal.add_thirds η

/-! ### Part 3: the discrete potential and the residual Steps -/

/-- The discrete potential `H^ε_f(a) = ε ∑_{x ∈ V^ε(B_ρ)} G_{B_ε}(a, x) f(z_x)` (`H_{ε,n}`
with `f = f_n`). It uses the sum set and the Green domain of `IntegralConvergenceGreenFunctionStmt` (with `z = 0`,
`r = ρ`): the domain `interiorCellVertices ε η (ball 0 ρ) = ballInterior ε η ρ` is `B_ε`, and `greenFn` is the
unnormalized expected number of visits (it vanishes off the domain). -/
noncomputable def layerPotential {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ρ ε : ℝ)
    (f : Ω → ℂ → ℝ) (ω : Ω) (a : ℤ) : ℝ :=
  ε * ∑' x : cellVertices ε (S.η ω) (ball 0 ρ),
    greenFn (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball 0 ρ)) a x * f ω (vertexPoint ε (S.η ω) x)

/-- **Residual Step (cutoffs and core).** Under the six antecedents of
`StoppedLayerPotentialStep`, there are cutoffs `f_n : Ω → ℂ → ℝ` with values in `[0, 1]`, measurable in the
environment `σ`-algebra, Hölder on `B_ρ`, with `f_n → 0` `μ_ω`-almost everywhere for `ω ∈ {t < T}`; and for each
`η > 0` some `N` gives, for `n ≥ N`, `P(F ∩ {∃ b ∈ E^ε_t, f_n(z_b) < 1/4}) < η` for all small `ε` (uncovered cells lie where the cutoff is at least `1/4`). Not proved: the earlier-time full-mass core and the
measurable cutoffs are an unimplemented component. -/
def LayerCutoffCoreStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  DiscreteLaplacianBoundCorrectedStmt 𝒮 → MaximumPrincipleStmt 𝒮 →
  ConvergenceDivisibleStmt 𝒮 → UniformConvergenceGreenKernelStmt 𝒮 → ExitTimeUpperBoundStmt 𝒮 →
  IntegralConvergenceGreenFunctionStmt 𝒮 →
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) →
  ∀ t : ℝ, 0 < t →
  ∃ f : ℕ → Ω → ℂ → ℝ,
    (∀ n ω x, 0 ≤ f n ω x ∧ f n ω x ≤ 1) ∧
    (∀ n x, Measurable[S.envSigma] fun ω => f n ω x) ∧
    (∀ n ω, IsHolderContinuousOn (f n ω) (ball 0 ρ)) ∧
    (∀ ω ∈ {ω | t < clusterExitTime (Λ ω) ρ},
      ∀ᵐ x ∂(S.μ ω), Tendsto (fun n => f n ω x) atTop (𝓝 0)) ∧
    ∀ η : ℝ≥0∞, 0 < η → ∃ N : ℕ, ∀ n ≥ N, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      S.P ({ω | t < clusterExitTime (Λ ω) ρ} ∩
        {ω | ∃ b ∈ cellVertices ε (S.η ω) (Λ ω t) \ matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t,
          f n ω (vertexPoint ε (S.η ω) b) < 1 / 4}) < η

/-- **Residual Step (finite-center Harnack).** Under the six
antecedents, for each small deterministic `r` there are finitely many centers `Y ⊆ B_{ρ/2}` whose `r/4`-balls cover
`B̄_{2ρ/5}`, a constant `p ∈ (0, 1/2]`, and good events `G_ε` with `P(F ∩ G_εᶜ) → 0`, such that on `F ∩ G_ε` every
layer vertex `a` has a centre `y ∈ Y` with `|z_a - y| < r/4`, `a ∈ V^ε(B_{3r}(y))`, and for every cutoff-type
function `0 ≤ g ≤ 1`,
`H_g(a) ≤ ε E_a[τ_{int V^ε(B_{3r}(y))}] + p⁻¹ H_g(a^ε_y)`.
This is the first-step/strong-Markov decomposition with a nonnegative harmonic function on the disk `B_{3r}(y)` and the
annulus-disconnection estimate. Not proved here: the disconnection input is not yet an `External` Prop (see report). -/
def LayerFiniteCenterHarnackStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  DiscreteLaplacianBoundCorrectedStmt 𝒮 → MaximumPrincipleStmt 𝒮 →
  ConvergenceDivisibleStmt 𝒮 → UniformConvergenceGreenKernelStmt 𝒮 → ExitTimeUpperBoundStmt 𝒮 →
  IntegralConvergenceGreenFunctionStmt 𝒮 →
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) →
  ∀ t : ℝ, 0 < t → ∀ r : ℝ, 0 < r → r < ρ / 6 →
  ∃ (Y : Finset ℂ) (p : ℝ) (G : ℝ → Set Ω), 0 < p ∧ p ≤ 1 / 2 ∧ (∀ y ∈ Y, y ∈ ball (0 : ℂ) (ρ / 2)) ∧
    (∀ z ∈ closedBall (0 : ℂ) (2 * ρ / 5), ∃ y ∈ Y, dist z y < r / 4) ∧
    TendsToOneOn S.P {ω | t < clusterExitTime (Λ ω) ρ} G ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ ω ∈ {ω | t < clusterExitTime (Λ ω) ρ} ∩ G ε,
        ∀ a ∈ cellVertices ε (S.η ω) (Λ ω t), ∃ y ∈ Y, dist (vertexPoint ε (S.η ω) a) y < r / 4 ∧
          a ∈ cellVertices ε (S.η ω) (ball y (3 * r)) ∧
          ∀ g : Ω → ℂ → ℝ, (∀ ω x, 0 ≤ g ω x ∧ g ω x ≤ 1) →
            ENNReal.ofReal (layerPotential S ρ ε g ω a) ≤
              ENNReal.ofReal ε *
                  expectedExitTime (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball y (3 * r))) a +
                ENNReal.ofReal p⁻¹ * ENNReal.ofReal (layerPotential S ρ ε g ω (vertexOf ε (S.η ω) y))

/-- **Residual Step (logarithmic potential of the exit masses).** Under the six
antecedents, the exit-time mass `𝓜(B_{4r}(z))` (`largestExitTimeRV`) is uniformly small over the centres `z ∈ B_ρ`
in probability as `r → 0`: for every finite `K ≠ ∞`, `c > 0`, `η > 0`, `s > 0` there is `r < s` with
`P(F ∩ {c < K · sup_{z ∈ B_ρ} 𝓜(B_{4r}(z))}) < η`. Not proved: the cone ball-mass input is not yet an `External`
Prop (see report). -/
def LayerExitMassSmallStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  DiscreteLaplacianBoundCorrectedStmt 𝒮 → MaximumPrincipleStmt 𝒮 →
  ConvergenceDivisibleStmt 𝒮 → UniformConvergenceGreenKernelStmt 𝒮 → ExitTimeUpperBoundStmt 𝒮 →
  IntegralConvergenceGreenFunctionStmt 𝒮 →
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) →
  ∀ t : ℝ, 0 < t → ∀ K : ℝ≥0∞, K ≠ ⊤ → ∀ c : ℝ≥0∞, 0 < c → ∀ η : ℝ≥0∞, 0 < η → ∀ s : ℝ, 0 < s →
  ∃ r : ℝ, 0 < r ∧ r < s ∧
    S.P ({ω | t < clusterExitTime (Λ ω) ρ} ∩
      {ω | c < K * ⨆ z ∈ ball (0 : ℂ) ρ, largestExitTimeRV (S.μ ω) (ball z (4 * r))}) < η

/-- **Residual Step (fixed-centre convergence and continuum limit).** Under the
six antecedents and `MepsScalingInput`, for cutoffs `f_n` as in `LayerCutoffCoreStep` and finitely many fixed centres
`Y ⊆ B_ρ`, the finite-centre potential `∑_{y ∈ Y} H_{f_n}(a^ε_y)` is small in probability for large `n` and small
`ε`: for every `K ≠ ∞`, `c > 0`, `η > 0` there is `N` with `P(F ∩ {c < K ∑_{y ∈ Y} H_{f_n}(a^ε_y)}) < η` for
`n ≥ N` and small `ε`. Not proved: it combines `IntegralConvergenceGreenFunctionStmt` with `ε m_ε ≤ C` and the
continuum limit `∫ G_ρ f_n dμ → 0`. -/
def LayerFixedCenterStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  MepsScalingInput 𝒮 →
  DiscreteLaplacianBoundCorrectedStmt 𝒮 → MaximumPrincipleStmt 𝒮 →
  ConvergenceDivisibleStmt 𝒮 → UniformConvergenceGreenKernelStmt 𝒮 → ExitTimeUpperBoundStmt 𝒮 →
  IntegralConvergenceGreenFunctionStmt 𝒮 →
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) →
  ∀ t : ℝ, 0 < t →
  ∀ f : ℕ → Ω → ℂ → ℝ, (∀ n ω x, 0 ≤ f n ω x ∧ f n ω x ≤ 1) →
    (∀ n x, Measurable[S.envSigma] fun ω => f n ω x) →
    (∀ n ω, IsHolderContinuousOn (f n ω) (ball 0 ρ)) →
    (∀ ω ∈ {ω | t < clusterExitTime (Λ ω) ρ},
      ∀ᵐ x ∂(S.μ ω), Tendsto (fun n => f n ω x) atTop (𝓝 0)) →
  ∀ Y : Finset ℂ, (∀ y ∈ Y, y ∈ ball (0 : ℂ) ρ) →
  ∀ K : ℝ≥0∞, K ≠ ⊤ → ∀ c : ℝ≥0∞, 0 < c → ∀ η : ℝ≥0∞, 0 < η →
  ∃ N : ℕ, ∀ n ≥ N, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
    S.P ({ω | t < clusterExitTime (Λ ω) ρ} ∩
      {ω | c < K * ∑ y ∈ Y, ENNReal.ofReal (layerPotential S ρ ε (f n) ω (vertexOf ε (S.η ω) y))}) < η


/-! ### Part 4: assembly into `StoppedLayerPotentialStep` -/

/-- Left multiplication by an `ℝ≥0∞` constant is monotone. -/
theorem mul_le_mul_left_enn {a b c : ℝ≥0∞} (h : b ≤ c) : a * b ≤ a * c :=
  mul_le_mul_of_nonneg_left h (zero_le)

/-- The discrete potential is a finite sum over the Green domain `B_ε`: the sum over the vertex set of the ball
reduces to the domain, since `greenFn` vanishes off its domain. -/
theorem layerPotential_eq_finsum {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ρ ε : ℝ)
    (f : Ω → ℂ → ℝ) (ω : Ω) (a : ℤ) (hD : (interiorCellVertices ε (S.η ω) (ball 0 ρ)).Finite) :
    layerPotential S ρ ε f ω a = ε * ∑ᶠ b ∈ interiorCellVertices ε (S.η ω) (ball 0 ρ),
      f ω (vertexPoint ε (S.η ω) b) * greenFn (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball 0 ρ)) a b := by
  unfold layerPotential
  congr 1
  have hsub := tsum_subtype (cellVertices ε (S.η ω) (ball 0 ρ))
    (fun x : ℤ => greenFn (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball 0 ρ)) a x *
      f ω (vertexPoint ε (S.η ω) x))
  rw [hsub, tsum_eq_sum (s := hD.toFinset) ?_, finsum_mem_eq_finite_toFinset_sum _ hD]
  · refine Finset.sum_congr rfl fun b hb => ?_
    have hbD : b ∈ interiorCellVertices ε (S.η ω) (ball 0 ρ) := hD.mem_toFinset.1 hb
    rw [Set.indicator_of_mem (sdiff_subset hbD)]
    ring
  · intro b hb
    have hbD : b ∉ interiorCellVertices ε (S.η ω) (ball 0 ρ) := fun h => hb (hD.mem_toFinset.2 h)
    simp [MatedCRT.Sec7.greenFn_eq_zero_of_not_mem_right (S.mult ε ω) a hbD]

/-- `ε ↦ C ε^p` tends to `0` along `𝓝[>] 0` for `p > 0`, after `ENNReal.ofReal`. -/
theorem tendsto_ofReal_const_mul_rpow (C p : ℝ) (hp : 0 < p) :
    Tendsto (fun ε : ℝ => ENNReal.ofReal (C * ε ^ p)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have h1 : Tendsto (fun ε : ℝ => C * ε ^ p) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h := ((Real.continuousAt_rpow_const 0 p (Or.inr hp.le)).tendsto).const_mul C
    rw [Real.zero_rpow hp.ne', mul_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun ε : ℝ => ENNReal.ofReal (C * ε ^ p)) (𝓝[>] (0 : ℝ)) (𝓝 (ENNReal.ofReal 0)) :=
    (ENNReal.continuous_ofReal.tendsto 0).comp h1
  rw [ENNReal.ofReal_zero] at h2
  exact h2

/-- The exit-time clause of `ExitTimeUpperBoundStmt` (clause 2) at mesh `ε`: for every disk `D ⊆ B_ρ` and every vertex
`a` of its cells, `E_a[τ_{int V^ε(D)}] ≤ C ε⁻¹ 𝓜(B_{ε^α}(D))`. -/
def layerExitGood {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ρ α C ε : ℝ) : Set Ω :=
  {ω | ∀ D : Set ℂ, D ⊆ ball 0 ρ → ∀ a ∈ cellVertices ε (S.η ω) D,
    expectedExitTime (S.mult ε ω) (interiorCellVertices ε (S.η ω) D) a ≤
      ENNReal.ofReal (C * ε⁻¹) * largestExitTimeRV (S.μ ω) (thickening (ε ^ α) D)}

/-- The complement of `layerExitGood` has small probability for small meshes, by `PolyHighProb` of the exit event. -/
theorem layerExitGood_prob_small {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ρ α C : ℝ)
    {E : ℝ → Set Ω} (hP : HarmonicBalls.PolyHighProb S.P E)
    (hE : ∀ ε : ℝ, ∀ ω ∈ E ε, ω ∈ layerExitGood S ρ α C ε) :
    ∀ η : ℝ≥0∞, 0 < η → ∀ᶠ ε in 𝓝[>] (0 : ℝ), S.P (layerExitGood S ρ α C ε)ᶜ < η := by
  intro η hη
  obtain ⟨q, hq, C', r₀, hr₀, hC'⟩ := hP
  have hlim := (tendsto_order.1 (tendsto_ofReal_const_mul_rpow C' q hq)).2 η hη
  filter_upwards [hlim, Ioo_mem_nhdsGT hr₀] with ε hε hε0
  calc S.P (layerExitGood S ρ α C ε)ᶜ ≤ S.P (E ε)ᶜ :=
        measure_mono fun ω hω hE' => hω (hE ε ω hE')
    _ ≤ ENNReal.ofReal (C' * ε ^ q) := hC' ε hε0.1 hε0.2
    _ < η := hε

/-- Small cells: if the cells of the vertices of `B_ρ` have diameter at most `ρ / 2`, then the vertices of a
set `L ⊆ B_{ρ/3}` lie in the interior `ballInterior ε η ρ` of the Green domain. -/
theorem layerVertices_subset_ballInterior {η : ℝ → ℂ} {L : Set ℂ} {ε ρ : ℝ} (hη : Continuous η)
    (hL : L ⊆ ball 0 (ρ / 3)) (hρ : 0 < ρ)
    (hsmall : ∀ k ∈ cellVertices ε η (ball 0 ρ), diam (cell ε η k) ≤ ρ / 2) :
    cellVertices ε η L ⊆ ballInterior ε η ρ := by
  intro b hb
  refine StoppedLLowerBound.mem_ballInterior_of_cell_subset ?_
    (StoppedLLowerBound.cell_subset_ball_of_mem_cellVertices hη hL (half_pos hρ).le (by linarith) hsmall hb)
  obtain ⟨y, hy⟩ := hb
  exact ⟨y, hy.1⟩

/-- A disk `B_{3r}(y)` with `y ∈ B_{ρ/2}` and `r < ρ/6` lies in `B_ρ`. -/
theorem ball_three_subset_of_center {y : ℂ} {ρ r : ℝ} (hy : y ∈ ball (0 : ℂ) (ρ / 2)) (hr : r < ρ / 6) :
    ball y (3 * r) ⊆ ball (0 : ℂ) ρ := by
  have hy' : dist y 0 < ρ / 2 := hy
  intro x hx
  rw [mem_ball] at hx ⊢
  calc dist x 0 ≤ dist x y + dist y 0 := dist_triangle x y 0
    _ < 3 * r + ρ / 2 := add_lt_add hx hy'
    _ ≤ ρ := by linarith

/-- The `δ`-thickening of `B_{3r}(y)` lies in `B_{4r}(y)` when `0 ≤ δ ≤ r`. -/
theorem thickening_ball_three_subset {y : ℂ} {r δ : ℝ} (hδ : δ ≤ r) :
    thickening δ (ball y (3 * r)) ⊆ ball y (4 * r) := by
  intro x hx
  obtain ⟨z, hz, hxz⟩ := Metric.mem_thickening_iff.1 hx
  rw [mem_ball] at hz ⊢
  calc dist x y ≤ dist x z + dist z y := dist_triangle x z y
    _ < δ + 3 * r := add_lt_add hxz hz
    _ ≤ r + 3 * r := by linarith
    _ = 4 * r := by ring

/-- The almost-sure environment facts used on `{t < T}`: regularity of every mesh, area parametrization of the
measure, and the cone-harmonic family. -/
def layerGoodOutcome {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (Λ : Ω → ℝ → Set ℂ) : Set Ω :=
  {ω | (∀ ε : ℝ, 0 < ε → IsRegularMatedMap (S.mult ε ω) ε (S.η ω)) ∧
    IsAreaParametrized (S.μ ω) (S.η ω) ∧ IsConeHarmonicBallFamily (S.μ ω) (Λ ω)}

/-- The small-cell event at mesh `ε` (the event of `IsValid.probTendsToOne_small_cells` with `d = ρ / 2`). -/
def layerSmallCells {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ρ ε : ℝ) : Set Ω :=
  {ω | ∀ k ∈ cellVertices ε (S.η ω) (ball 0 ρ), diam (cell ε (S.η ω) k) ≤ ρ / 2}

/-- **Assembly.** `StoppedLayerPotentialStep 𝒮` (`Proofs/Sec5/StoppedSurplusSteps.lean:68`) from the four residual
Steps and the literature scaling input `MepsScalingInput 𝒮` (`External/SLE.lean:63`), with the six antecedents of
`StoppedLayerPotentialStep` retained as premises of the residual Steps. The layer sum is the actual
`greenKernel`-sum of the target (no extra division by degree). Proof: Part 2 with the `r`-then-`n`-then-`ε`
choices, Part 1 for the domination `ε L ≤ 4 H` on the good event, the Harnack inequality, the exit-time clause 2 of the
antecedent `ExitTimeUpperBoundStmt`, and the small-cell and regularity facts of the mesh. -/
theorem stoppedLayerPotentialStep_of_layerSteps (𝒮 : SpaceFillingSLEModel)
    (hCut : LayerCutoffCoreStep 𝒮) (hHarn : LayerFiniteCenterHarnackStep 𝒮)
    (hExit : LayerExitMassSmallStep 𝒮) (hFixed : LayerFixedCenterStep 𝒮)
    (hMeps : MepsScalingInput 𝒮) : StoppedLayerPotentialStep 𝒮 := by
  intro h1 h2 h3 h4 h5 h6 γ hγ hγ2 ρ hρ hρ1 Ω _ S hS Λ hΛ t ht κ hκ
  have : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  obtain ⟨f, hf01, hfmeas, hfhol, hfconv, hcut⟩ :=
    hCut h1 h2 h3 h4 h5 h6 γ hγ hγ2 ρ hρ hρ1 Ω S hS Λ hΛ t ht
  choose! Y p G hp0 hp1 hYball hYcov hGt hGdom using
    fun r hr hr6 => hHarn h1 h2 h3 h4 h5 h6 γ hγ hγ2 ρ hρ hρ1 Ω S hS Λ hΛ t ht r hr hr6
  obtain ⟨α, hα, hCC⟩ := h5 γ hγ hγ2
  obtain ⟨C, hC0, hCb⟩ := hCC ρ hρ hρ1
  have hPoly := hCb Ω S hS
  have hAS : ∀ᵐ ω ∂S.P, ω ∈ layerGoodOutcome S Λ :=
    (ae_isRegularMatedMap (adjacentCellsMeetAeStep 𝒮) hγ hγ2 hS).and (hS.isAreaParametrized.and hΛ)
  have hASnull : S.P (layerGoodOutcome S Λ)ᶜ = 0 := ae_iff.1 hAS
  have hSmall : ProbTendsToOne S.P (layerSmallCells S ρ) :=
    hS.probTendsToOne_small_cells ρ (ρ / 2) (half_pos hρ)
  have hExitTend := layerExitGood_prob_small S ρ α C hPoly
    (fun ε ω hω D hD a ha => (hω.2 D hD a ha).2)
  let Z : ℝ → Ω → ℝ≥0∞ := fun r ω =>
    ENNReal.ofReal C * ⨆ z ∈ ball (0 : ℂ) ρ, largestExitTimeRV (S.μ ω) (ball z (4 * r))
  let Q : ℝ → ℕ → ℝ → Ω → ℝ≥0∞ := fun ε n r ω =>
    ENNReal.ofReal (p r)⁻¹ *
      ∑ y ∈ Y r, ENNReal.ofReal (layerPotential S ρ ε (f n) ω (vertexOf ε (S.η ω) y))
  let G' : ℝ → ℕ → ℝ → Set Ω := fun ε n r =>
    {ω | (∀ b ∈ cellVertices ε (S.η ω) (Λ ω t) \ matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t,
            1 / 4 ≤ f n ω (vertexPoint ε (S.η ω) b)) ∧
      ω ∈ G r ε ∧ ω ∈ layerExitGood S ρ α C ε ∧ ω ∈ layerGoodOutcome S Λ ∧ ω ∈ layerSmallCells S ρ ε}
  -- the `Z`-side: the exit-mass smallness of the residual Step
  have hZ : ∀ c : ℝ≥0∞, 0 < c → ∀ η : ℝ≥0∞, 0 < η → ∃ r : ℝ, 0 < r ∧ r < ρ / 6 ∧
      S.P ({ω | t < clusterExitTime (Λ ω) ρ} ∩ {ω | c < Z r ω}) < η := by
    intro c hc η hη
    obtain ⟨r, hr, hrs, hP⟩ := hExit h1 h2 h3 h4 h5 h6 γ hγ hγ2 ρ hρ hρ1 Ω S hS Λ hΛ t ht
      (ENNReal.ofReal C) ENNReal.ofReal_ne_top c hc η hη (ρ / 6) (div_pos hρ (by norm_num))
    exact ⟨r, hr, hrs, hP⟩
  -- the `Q`-side: fixed-centre smallness and the good-event probabilities
  have hJ : ∀ c : ℝ≥0∞, 0 < c → ∀ η : ℝ≥0∞, 0 < η → ∀ r : ℝ, 0 < r → r < ρ / 6 → ∃ n : ℕ,
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), S.P ({ω | t < clusterExitTime (Λ ω) ρ} ∩ {ω | c < Q ε n r ω}) < η) ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), S.P ({ω | t < clusterExitTime (Λ ω) ρ} ∩ (G' ε n r)ᶜ) < η) := by
    intro c hc η hη r hr hr6
    obtain ⟨N1, hN1⟩ := hFixed hMeps h1 h2 h3 h4 h5 h6 γ hγ hγ2 ρ hρ hρ1 Ω S hS Λ hΛ t ht f hf01
      hfmeas hfhol hfconv (Y r) (fun y hy => Metric.ball_subset_ball (by linarith) (hYball r hr hr6 y hy))
      (ENNReal.ofReal (p r)⁻¹) ENNReal.ofReal_ne_top c hc η hη
    have hη2 : (0 : ℝ≥0∞) < η / 2 / 2 :=
      ENNReal.div_pos_iff.2 ⟨(ENNReal.div_pos_iff.2 ⟨hη.ne', by norm_num⟩).ne', by norm_num⟩
    obtain ⟨N2, hN2⟩ := hcut (η / 2 / 2) hη2
    have hn1 : N1 ≤ N1 + N2 := Nat.le_add_right _ _
    have hn2 : N2 ≤ N1 + N2 := Nat.le_add_left _ _
    refine ⟨N1 + N2, hN1 _ hn1, ?_⟩
    have hcutev := hN2 _ hn2
    have hGev := (tendsto_order.1 (hGt r hr hr6)).2 (η / 2 / 2) hη2
    have hexev := hExitTend (η / 2 / 2) hη2
    have hsmev := (tendsto_order.1 hSmall).2 (η / 2 / 2) hη2
    have hθ : η / 2 / 2 + η / 2 / 2 + η / 2 / 2 + η / 2 / 2 = η := by
      calc η / 2 / 2 + η / 2 / 2 + η / 2 / 2 + η / 2 / 2
          = (η / 2 / 2 + η / 2 / 2) + (η / 2 / 2 + η / 2 / 2) := by ac_rfl
        _ = η / 2 + η / 2 := by rw [ENNReal.add_halves (η / 2)]
        _ = η := ENNReal.add_halves η
    filter_upwards [hcutev, hGev, hexev, hsmev] with ε hcε hGε hEε hSε
    have hincl : {ω | t < clusterExitTime (Λ ω) ρ} ∩ (G' ε (N1 + N2) r)ᶜ ⊆
        (((({ω | t < clusterExitTime (Λ ω) ρ} ∩
              {ω | ∃ b ∈ cellVertices ε (S.η ω) (Λ ω t) \ matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t,
                f (N1 + N2) ω (vertexPoint ε (S.η ω) b) < 1 / 4}) ∪
            ({ω | t < clusterExitTime (Λ ω) ρ} ∩ (G r ε)ᶜ)) ∪ (layerExitGood S ρ α C ε)ᶜ) ∪
          (layerSmallCells S ρ ε)ᶜ) ∪ (layerGoodOutcome S Λ)ᶜ := by
      rintro ω ⟨hF, hωG⟩
      by_cases hae : ω ∈ layerGoodOutcome S Λ
      · by_cases hsm : ω ∈ layerSmallCells S ρ ε
        · by_cases hex : ω ∈ layerExitGood S ρ α C ε
          · by_cases hGr : ω ∈ G r ε
            · have hcf : ∃ b ∈ cellVertices ε (S.η ω) (Λ ω t) \ matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t,
                  f (N1 + N2) ω (vertexPoint ε (S.η ω) b) < 1 / 4 := by
                by_contra hcf
                push Not at hcf
                exact hωG ⟨hcf, hGr, hex, hae, hsm⟩
              exact Or.inl (Or.inl (Or.inl (Or.inl ⟨hF, hcf⟩)))
            · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨hF, hGr⟩)))
          · exact Or.inl (Or.inl (Or.inr hex))
        · exact Or.inl (Or.inr hsm)
      · exact Or.inr hae
    have hmeas : S.P ({ω | t < clusterExitTime (Λ ω) ρ} ∩ (G' ε (N1 + N2) r)ᶜ) ≤
        S.P ({ω | t < clusterExitTime (Λ ω) ρ} ∩
            {ω | ∃ b ∈ cellVertices ε (S.η ω) (Λ ω t) \ matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t,
              f (N1 + N2) ω (vertexPoint ε (S.η ω) b) < 1 / 4}) +
          S.P ({ω | t < clusterExitTime (Λ ω) ρ} ∩ (G r ε)ᶜ) + S.P (layerExitGood S ρ α C ε)ᶜ +
          S.P (layerSmallCells S ρ ε)ᶜ + S.P (layerGoodOutcome S Λ)ᶜ := by
      refine (measure_mono hincl).trans ?_
      refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
      refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
      refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
      exact measure_union_le _ _
    have hsum : S.P ({ω | t < clusterExitTime (Λ ω) ρ} ∩
            {ω | ∃ b ∈ cellVertices ε (S.η ω) (Λ ω t) \ matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t,
              f (N1 + N2) ω (vertexPoint ε (S.η ω) b) < 1 / 4}) +
          S.P ({ω | t < clusterExitTime (Λ ω) ρ} ∩ (G r ε)ᶜ) + S.P (layerExitGood S ρ α C ε)ᶜ +
          S.P (layerSmallCells S ρ ε)ᶜ < η := by
      rw [← hθ]
      exact ENNReal.add_lt_add (ENNReal.add_lt_add (ENNReal.add_lt_add hcε hGε) hEε) hSε
    rw [hASnull, add_zero] at hmeas
    exact lt_of_le_of_lt hmeas hsum
  -- the domination `ε L ≤ 4 Z + 4 Q` on the good event, for small meshes
  have hdom : ∀ r : ℝ, 0 < r → r < ρ / 6 → ∀ n : ℕ, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∀ ω ∈ {ω | t < clusterExitTime (Λ ω) ρ} ∩ G' ε n r, ∀ a ∈ cellVertices ε (S.η ω) (Λ ω t),
        ENNReal.ofReal (ε * ∑ᶠ b ∈ cellVertices ε (S.η ω) (Λ ω t) \ matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t,
          greenKernel (S.mult ε ω) (cellVertices ε (S.η ω) (Λ ω t)) a b) ≤
          4 * Z r ω + 4 * Q ε n r ω := by
    intro r hr hr6 n
    have hα' : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ^ α ≤ r := by
      have ht0 : Tendsto (fun ε : ℝ => ε ^ α) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
        have h := (Real.continuousAt_rpow_const 0 α (Or.inr hα.le)).tendsto
        rw [Real.zero_rpow hα.ne'] at h
        exact h.mono_left nhdsWithin_le_nhds
      exact ((tendsto_order.1 ht0).2 r hr).mono fun ε hε => hε.le
    filter_upwards [hGdom r hr hr6, hα', eventually_mem_nhdsWithin] with ε hHε hαε hεpos
    have hε : 0 < ε := hεpos
    rintro ω ⟨hFω, hGω⟩ a ha
    obtain ⟨hcutω, hGrω, hexω, haeω, hsmω⟩ := hGω
    obtain ⟨y, hyY, -, hay, hHy⟩ := hHε ω ⟨hFω, hGrω⟩ a ha
    have hyball : y ∈ ball (0 : ℂ) (ρ / 2) := hYball r hr hr6 y hyY
    have hd := haeω.1 ε hε
    have hD : (ballInterior ε (S.η ω) ρ).Finite := hd.finite_ballInterior
    have harea := haeω.2.1
    have hfam := haeω.2.2
    have hΛt : Λ ω t ⊆ ball 0 (ρ / 3) :=
      IDLALowerBound.subset_ball_div_three_of_lt_clusterExitTime hfam.2.1.monotoneOn ht hFω
    have hAD : cellVertices ε (S.η ω) (Λ ω t) ⊆ ballInterior ε (S.η ω) ρ :=
      layerVertices_subset_ballInterior harea.1 hΛt hρ hsmω
    have hA : (cellVertices ε (S.η ω) (Λ ω t)).Finite := hD.subset hAD
    have hE : (cellVertices ε (S.η ω) (Λ ω t) \ matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t).Finite :=
      hA.subset sdiff_subset
    have hES : cellVertices ε (S.η ω) (Λ ω t) \ matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t ⊆
        ballInterior ε (S.η ω) ρ := sdiff_subset.trans hAD
    have hP1 := finsum_greenKernel_le_four_mul_potential hd.locallyFinite hd.succ hA hD hAD hE hD hES
      (fun b => f n ω (vertexPoint ε (S.η ω) b)) (fun b _ => (hf01 n ω _).1) (fun b hb => hcutω b hb) a
    have hL : ε * (∑ᶠ b ∈ cellVertices ε (S.η ω) (Λ ω t) \ matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t,
          greenKernel (S.mult ε ω) (cellVertices ε (S.η ω) (Λ ω t)) a b) ≤
        4 * layerPotential S ρ ε (f n) ω a := by
      rw [layerPotential_eq_finsum S ρ ε (f n) ω a hD]
      calc _ ≤ ε * (4 * ∑ᶠ b ∈ interiorCellVertices ε (S.η ω) (ball 0 ρ),
            f n ω (vertexPoint ε (S.η ω) b) * greenFn (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball 0 ρ)) a b) :=
            mul_le_mul_of_nonneg_left hP1 hε.le
        _ = _ := by ring
    have hH := hHy (f n) (hf01 n)
    have hexit := hexω (ball y (3 * r)) (ball_three_subset_of_center hyball hr6) a hay
    have hthick : largestExitTimeRV (S.μ ω) (thickening (ε ^ α) (ball y (3 * r))) ≤
        largestExitTimeRV (S.μ ω) (ball y (4 * r)) :=
      largestExitTimeRV_mono (S.μ ω) (thickening_ball_three_subset hαε)
    have hsup : largestExitTimeRV (S.μ ω) (ball y (4 * r)) ≤
        ⨆ z ∈ ball (0 : ℂ) ρ, largestExitTimeRV (S.μ ω) (ball z (4 * r)) :=
      le_iSup₂ (f := fun z (_ : z ∈ ball (0 : ℂ) ρ) => largestExitTimeRV (S.μ ω) (ball z (4 * r))) y
        (Metric.ball_subset_ball (by linarith) hyball)
    have hεne : ε ≠ 0 := hε.ne'
    have hEZ : ENNReal.ofReal ε *
        expectedExitTime (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball y (3 * r))) a ≤ Z r ω := by
      calc ENNReal.ofReal ε *
            expectedExitTime (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball y (3 * r))) a
          ≤ ENNReal.ofReal ε * (ENNReal.ofReal (C * ε⁻¹) *
              largestExitTimeRV (S.μ ω) (thickening (ε ^ α) (ball y (3 * r)))) :=
            mul_le_mul_left_enn hexit
        _ = ENNReal.ofReal C * largestExitTimeRV (S.μ ω) (thickening (ε ^ α) (ball y (3 * r))) := by
            rw [← mul_assoc, ← ENNReal.ofReal_mul hε.le, show ε * (C * ε⁻¹) = C by field_simp]
        _ ≤ ENNReal.ofReal C * largestExitTimeRV (S.μ ω) (ball y (4 * r)) :=
            mul_le_mul_left_enn hthick
        _ ≤ Z r ω := mul_le_mul_left_enn hsup
    have hQy : ENNReal.ofReal (p r)⁻¹ *
        ENNReal.ofReal (layerPotential S ρ ε (f n) ω (vertexOf ε (S.η ω) y)) ≤ Q ε n r ω :=
      mul_le_mul_left_enn (Finset.single_le_sum
        (f := fun y' => ENNReal.ofReal (layerPotential S ρ ε (f n) ω (vertexOf ε (S.η ω) y')))
        (fun _ _ => zero_le) hyY)
    have h4 : ENNReal.ofReal (ε * (∑ᶠ b ∈ cellVertices ε (S.η ω) (Λ ω t) \ matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t,
          greenKernel (S.mult ε ω) (cellVertices ε (S.η ω) (Λ ω t)) a b)) ≤
        4 * ENNReal.ofReal (layerPotential S ρ ε (f n) ω a) := by
      calc _ ≤ ENNReal.ofReal (4 * layerPotential S ρ ε (f n) ω a) := ENNReal.ofReal_le_ofReal hL
        _ = 4 * ENNReal.ofReal (layerPotential S ρ ε (f n) ω a) := by
          rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
    calc _ ≤ 4 * ENNReal.ofReal (layerPotential S ρ ε (f n) ω a) := h4
      _ ≤ 4 * (ENNReal.ofReal ε *
            expectedExitTime (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball y (3 * r))) a +
          ENNReal.ofReal (p r)⁻¹ *
            ENNReal.ofReal (layerPotential S ρ ε (f n) ω (vertexOf ε (S.η ω) y))) :=
          mul_le_mul_left_enn hH
      _ ≤ 4 * (Z r ω + Q ε n r ω) := mul_le_mul_left_enn (add_le_add hEZ hQy)
      _ = 4 * Z r ω + 4 * Q ε n r ω := mul_add _ _ _
  exact tendsToOneOn_layer_of_domination S.P {ω | t < clusterExitTime (Λ ω) ρ}
    (fun ε ω => cellVertices ε (S.η ω) (Λ ω t))
    (fun ε ω a => ∑ᶠ b ∈ cellVertices ε (S.η ω) (Λ ω t) \ matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t,
      greenKernel (S.mult ε ω) (cellVertices ε (S.η ω) (Λ ω t)) a b)
    G' Z Q (ρ / 6) κ hκ hZ hJ hdom

end MatedCRT
