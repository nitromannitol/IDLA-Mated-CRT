import MatedCRT.Proofs.Sec5.StoppedSurplusSteps
import MatedCRT.Proofs.Sec5.MeanValueInequality.CellRepresentative
import MatedCRT.Proofs.Sec4.DivSandpileLowerBound.SourceVertex
import MatedCRT.Proofs.Infra.MatingOfTrees

/-!
# The exterior bound off `V^ε(Λ_t)`: the deterministic core (E-c1-5, `StoppedSurplusExteriorStep`)

For one sample point and one mesh `ε`, write `w̃ = matedLeastSupersolution` and `G = ε⁻¹ g^ε_{B_ρ}(0, ·)`, so that
`(t/ε) g^ε_{B_ρ}(0, ·) = t G` and the stopped surplus is `v = w̃ + t G`. Then:

* off `V^ε(B_ρ) \ V^ε(∂B_ρ)` (the vertices `ballInterior`), `w̃ ≤ 0` and the Green term vanishes, so `v ≤ 0`;
* for a vertex `a ∈ ballInterior` outside `V^ε(Λ_t)`, its cell `H^ε_a` lies in `B_ρ` (connectedness of the cell) and
  misses `Λ_t`. Its representative point `x` (with `a^ε_x = a`) satisfies `w̄(x) + t G_{B_ρ}(0, x) ≤ 0`, because the
  cluster is open, so `cluster ⊆ int cl cluster = Λ_t` (HB (c)). Theorem 4.1 and Lemma 3.3 (on the annulus
  `s ≤ |y| < ρ`, where `s` is a radius with `B_s(0) ⊆ Λ_t`) then give `m_ε⁻¹ v(a) ≤ δ + t δ'`.

The probabilistic assembly (that `B_s(0) ⊆ Λ_t` for a deterministic `s` with probability close to one) is not here: it
needs the origin input reported in ESCALATIONS E-c1-5.
-/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace StoppedExterior

/-- A walk never visits a vertex outside `A` before its exit time. -/
theorem visitsBeforeExit_eq_zero {A : Set ℤ} {b : ℤ} (hb : b ∉ A) (x : ℕ → ℤ) :
    visitsBeforeExit A b x = 0 := by
  classical
  unfold visitsBeforeExit
  refine ENNReal.tsum_eq_zero.2 fun n => ?_
  split_ifs with h
  · exfalso
    have hnA : x n ∈ A := by
      by_contra hnA
      have hex : ∃ k, x k ∉ A := ⟨n, hnA⟩
      have hle : vExitTime A x ≤ (n : ℕ∞) := by
        have hfm := Nat.find_min' hex hnA
        simpa [vExitTime, hex] using hfm
      exact absurd h.1 (not_lt.2 hle)
    exact hb (h.2 ▸ hnA)
  · rfl

/-- The Green kernel `g_A(a, b) = G_A(a, b) / deg(b)` vanishes when `b ∉ A`. -/
theorem greenKernel_eq_zero_of_not_mem {m : ℤ → ℤ → ℕ} {A : Set ℤ} {a b : ℤ} (hb : b ∉ A) :
    greenKernel m A a b = 0 := by
  unfold greenKernel greenFn
  simp [visitsBeforeExit_eq_zero hb]

/-- The Green kernel is nonnegative. -/
theorem greenKernel_nonneg (m : ℤ → ℤ → ℕ) (A : Set ℤ) (a b : ℤ) : 0 ≤ greenKernel m A a b := by
  unfold greenKernel greenFn
  exact div_nonneg ENNReal.toReal_nonneg (Nat.cast_nonneg _)

/-- An infimum of values of a set containing `0` (at `a`) is at most `0`, bounded below or not. -/
theorem discreteLeastSupersolution_le_zero {α : Type*} (m : α → α → ℕ) (V W : Set α) (𝔯 φ : α → ℝ) (a : α)
    (h𝔯 : ∀ b, 0 ≤ 𝔯 b) (hφ : ∀ b ∈ W, φ b ≤ 0) :
    discreteLeastSupersolution m V W 𝔯 φ a ≤ 0 := by
  unfold discreteLeastSupersolution
  by_cases hb : BddBelow ((fun u : α → ℝ => u a) '' {u | (∀ b ∈ V, mLaplacian m u b ≤ 𝔯 b) ∧ ∀ b ∈ W, φ b ≤ u b})
  · refine csInf_le hb ⟨0, ⟨fun b _ => ?_, fun b hb' => ?_⟩, rfl⟩
    · simpa [mLaplacian] using h𝔯 b
    · simpa using hφ b hb'
  · exact (Real.sInf_of_not_bddBelow hb).le

/-- The discrete least supersolution `w̃^ε_t` is nonpositive. -/
theorem matedLeastSupersolution_le_zero {m : ℤ → ℤ → ℕ} {ε : ℝ} {η : ℝ → ℂ} {ρ t : ℝ}
    (hε : 0 < ε) (ht : 0 < t) (a : ℤ) : matedLeastSupersolution m ε η ρ t a ≤ 0 := by
  unfold matedLeastSupersolution
  refine discreteLeastSupersolution_le_zero _ _ _ _ _ a (fun b => inv_nonneg.2 (Nat.cast_nonneg _)) fun b _ => ?_
  unfold matedObstacle
  rw [neg_mul]
  exact neg_nonpos.2 (mul_nonneg (div_nonneg ht.le hε.le) (greenKernel_nonneg _ _ _ _))

/-- Outside `ballInterior` the stopped surplus is nonpositive (the Green term vanishes there). -/
theorem matedLeastSupersolution_add_green_le_of_not_mem {m : ℤ → ℤ → ℕ} {ε : ℝ} {η : ℝ → ℂ} {ρ t : ℝ}
    (hε : 0 < ε) (ht : 0 < t) {a : ℤ} (ha : a ∉ ballInterior ε η ρ) :
    matedLeastSupersolution m ε η ρ t a + t / ε * greenKernel m (ballInterior ε η ρ) 0 a ≤ 0 := by
  rw [greenKernel_eq_zero_of_not_mem ha, mul_zero, add_zero]
  exact matedLeastSupersolution_le_zero hε ht a

/-- **Continuum surplus off `Λ_t`.** If `Λ_t = int cl cluster` (HB (c)) and `w̄` is continuous on `cl B_ρ`, then
`w̄ + t G_{B_ρ}(0, ·) ≤ 0` at each `x ∈ B_ρ \ (Λ_t ∪ {0})`: otherwise `x` lies in the open set
`{y ∈ B_ρ \ {0} : 0 < w̄(y) + t G(0, y)} ⊆ cluster`, hence in `int cl cluster = Λ_t`. -/
theorem leastSupersolution_add_green_le_zero {μ : Measure ℂ} {ρ t : ℝ} {Λ : Set ℂ}
    (hρ : 0 < ρ) (hΛ : Λ = interior (closure (HarmonicBalls.cluster μ ρ 0 t)))
    (hcont : ContinuousOn (HarmonicBalls.leastSupersolution μ ρ 0 t) (closedBall 0 ρ))
    {x : ℂ} (hx : x ∈ ball (0 : ℂ) ρ) (hx0 : x ≠ 0) (hxΛ : x ∉ Λ) :
    HarmonicBalls.leastSupersolution μ ρ 0 t x + t * HarmonicBalls.greenFunction (ball 0 ρ) 0 x ≤ 0 := by
  by_contra hpos
  have hpos' : 0 < HarmonicBalls.leastSupersolution μ ρ 0 t x +
      t * HarmonicBalls.greenFunction (ball 0 ρ) 0 x := not_le.1 hpos
  have hp0 : (0 : ℂ) ∈ ball (0 : ℂ) ρ := by simpa using hρ
  have hG : ContinuousOn (HarmonicBalls.greenFunction (ball 0 ρ) 0) {(0 : ℂ)}ᶜ :=
    HarmonicBalls.continuousOn_greenFunction_ball hp0
  have hF : ContinuousOn (fun y => HarmonicBalls.leastSupersolution μ ρ 0 t y +
      t * HarmonicBalls.greenFunction (ball 0 ρ) 0 y) (ball (0 : ℂ) ρ ∩ {(0 : ℂ)}ᶜ) := by
    refine ContinuousOn.add ?_ (continuousOn_const.mul ?_)
    · exact hcont.mono (fun y hy => ball_subset_closedBall hy.1)
    · exact hG.mono (fun y hy => hy.2)
  have hU : IsOpen (ball (0 : ℂ) ρ ∩ {(0 : ℂ)}ᶜ ∩
      (fun y => HarmonicBalls.leastSupersolution μ ρ 0 t y +
        t * HarmonicBalls.greenFunction (ball 0 ρ) 0 y) ⁻¹' Ioi 0) :=
    hF.isOpen_inter_preimage (isOpen_ball.inter isOpen_compl_singleton) isOpen_Ioi
  have hsub : ball (0 : ℂ) ρ ∩ {(0 : ℂ)}ᶜ ∩
      (fun y => HarmonicBalls.leastSupersolution μ ρ 0 t y +
        t * HarmonicBalls.greenFunction (ball 0 ρ) 0 y) ⁻¹' Ioi 0 ⊆
      interior (closure (HarmonicBalls.cluster μ ρ 0 t)) := by
    refine interior_maximal ?_ hU
    intro y hy
    apply subset_closure
    refine ⟨hy.1.1, Or.inr ?_⟩
    have h1 : (0 : ℝ) < HarmonicBalls.leastSupersolution μ ρ 0 t y +
        t * HarmonicBalls.greenFunction (ball 0 ρ) 0 y := hy.2
    have h2 : -t * HarmonicBalls.greenFunction (ball 0 ρ) 0 y =
        -(t * HarmonicBalls.greenFunction (ball 0 ρ) 0 y) := by ring
    rw [h2]
    linarith
  apply hxΛ
  rw [hΛ]
  exact hsub ⟨⟨hx, hx0⟩, hpos'⟩

/-- A cell of a vertex of `ballInterior` lies in `B_ρ`: the cell is connected, meets `B_ρ`, and misses the frontier
of `B_ρ` (so it cannot cross the sphere). -/
theorem cell_subset_ball_of_mem_ballInterior {ε ρ : ℝ} {η : ℝ → ℂ} (hη : Continuous η) {a : ℤ}
    (ha : a ∈ ballInterior ε η ρ) : cell ε η a ⊆ ball (0 : ℂ) ρ := by
  have ha' : a ∈ cellVertices ε η (ball 0 ρ) ∧ a ∉ cellVertices ε η (frontier (ball (0 : ℂ) ρ)) := ha
  obtain ⟨hball, hfr⟩ := ha'
  have hconn : IsPreconnected (cell ε η a) := isPreconnected_Icc.image η hη.continuousOn
  have hdisj : Disjoint (ball (0 : ℂ) ρ) (closure (ball (0 : ℂ) ρ))ᶜ :=
    Set.disjoint_left.2 fun z hz hz' => hz' (subset_closure hz)
  have hcover : cell ε η a ⊆ ball (0 : ℂ) ρ ∪ (closure (ball (0 : ℂ) ρ))ᶜ := by
    intro z hz
    by_cases hzb : z ∈ ball (0 : ℂ) ρ
    · exact Or.inl hzb
    · refine Or.inr fun hzc => hfr ⟨z, hz, ?_⟩
      exact ⟨hzc, by rw [isOpen_ball.interior_eq]; exact hzb⟩
  exact hconn.subset_left_of_subset_union isOpen_ball isClosed_closure.isOpen_compl hdisj hcover hball

/-- **Real-number core of the exterior bound.** If `rW = m⁻¹ W`, `rG = m⁻¹ G`, `|rW − c w̄| ≤ δ`, `|rG − c ḡ| ≤ δ'`
and `w̄ + t ḡ ≤ 0`, then `W + t G ≤ m (δ + t δ')`. -/
theorem exterior_real_bound {mε c t δ δ' Wa Ga rW rG wbar gbar : ℝ} (hmε : 0 < mε) (hc : 0 ≤ c) (ht : 0 ≤ t)
    (hrW : rW = mε⁻¹ * Wa) (hrG : rG = mε⁻¹ * Ga)
    (hW : |rW - c * wbar| ≤ δ) (hG : |rG - c * gbar| ≤ δ') (hf : wbar + t * gbar ≤ 0) :
    Wa + t * Ga ≤ mε * (δ + t * δ') := by
  have h1 : rW ≤ c * wbar + δ := by linarith [(abs_le.1 hW).2]
  have h2 : rG ≤ c * gbar + δ' := by linarith [(abs_le.1 hG).2]
  have h3 : t * rG ≤ t * (c * gbar + δ') := mul_le_mul_of_nonneg_left h2 ht
  have h4 : c * (wbar + t * gbar) ≤ 0 := by nlinarith
  have e : mε⁻¹ * (Wa + t * Ga) = rW + t * rG := by rw [hrW, hrG]; ring
  have h5 : mε⁻¹ * (Wa + t * Ga) ≤ δ + t * δ' := by
    have e2 : c * wbar + t * (c * gbar + δ') = c * (wbar + t * gbar) + t * δ' := by ring
    linarith
  have h6 := mul_le_mul_of_nonneg_left h5 hmε.le
  rwa [← mul_assoc, mul_inv_cancel₀ hmε.ne', one_mul] at h6

/-- **Exterior bound at one vertex, deterministic core.** Fix a sample point and a mesh `ε`. Suppose:
* `0 ∈ Λ_t` with the ball `B_s(0) ⊆ Λ_t` (`hpole`), and `Λ_t = int cl cluster` with `w̄` continuous on `cl B_ρ`;
* on `B_ρ`, the rescaled least supersolution is within `δ` of `c w̄` (Theorem 4.1, at this sample point);
* on the annulus `{s ≤ |y| < ρ}`, the rescaled Green kernel `ε⁻¹ g^ε_{B_ρ}(0, ·)` is within `δ'` of `c G_{B_ρ}(0, ·)`
  (Lemma 3.3, at this sample point, with the pole `a^ε_0 = 0`).
Then for every vertex `a ∈ ballInterior` outside `V^ε(Λ_t)`, the stopped surplus satisfies
`w̃^ε_t(a) + (t/ε) g^ε_{B_ρ}(0, a) ≤ m_ε (δ + t δ')`. -/
theorem exterior_vertex_bound {μ : Measure ℂ} {η : ℝ → ℂ} {m : ℤ → ℤ → ℕ} {ε ρ t s c δ δ' mε : ℝ}
    {Λ : Set ℂ} (hε : 0 < ε) (ht : 0 < t) (hρ : 0 < ρ) (hs : 0 < s) (hc : 0 ≤ c) (hmε : 0 < mε)
    (hη : IsAreaParametrized μ η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    (hv0 : vertexOf ε η 0 = 0)
    (hΛ : Λ = interior (closure (HarmonicBalls.cluster μ ρ 0 t)))
    (hcont : ContinuousOn (HarmonicBalls.leastSupersolution μ ρ 0 t) (closedBall 0 ρ))
    (hpole : ball (0 : ℂ) s ⊆ Λ)
    (hW : ∀ y ∈ ball (0 : ℂ) ρ, |rescale mε ε η (matedLeastSupersolution m ε η ρ t) y -
      c * HarmonicBalls.leastSupersolution μ ρ 0 t y| ≤ δ)
    (hG : ∀ y ∈ ball (0 : ℂ) ρ, s ≤ ‖y‖ →
      |rescale mε ε η (fun b => ε⁻¹ * greenKernel m (interiorCellVertices ε η (ball 0 ρ)) (vertexOf ε η 0) b) y -
        c * HarmonicBalls.greenFunction (ball 0 ρ) 0 y| ≤ δ')
    {a : ℤ} (ha : a ∈ ballInterior ε η ρ) (ha' : a ∉ cellVertices ε η Λ) :
    matedLeastSupersolution m ε η ρ t a + t / ε * greenKernel m (ballInterior ε η ρ) 0 a ≤
      mε * (δ + t * δ') := by
  rw [hv0] at hG
  obtain ⟨x, hxcell, hxa⟩ := exists_vertexOf_eq_of_area_parametrized hη hp hε a
  have hxball : x ∈ ball (0 : ℂ) ρ := cell_subset_ball_of_mem_ballInterior hη.1 ha hxcell
  have hxΛ : x ∉ Λ := fun hx => ha' ⟨x, hxcell, hx⟩
  have hs0 : (0 : ℂ) ∈ ball (0 : ℂ) s := by simpa using hs
  have hx0 : x ≠ 0 := fun h => hxΛ (hpole (by rw [h]; exact hs0))
  have hsx : s ≤ ‖x‖ := by
    by_contra h
    have hlt : ‖x‖ < s := not_le.1 h
    exact hxΛ (hpole (by rw [mem_ball_zero_iff]; exact hlt))
  have hf := leastSupersolution_add_green_le_zero hρ hΛ hcont hxball hx0 hxΛ
  have hrW : rescale mε ε η (matedLeastSupersolution m ε η ρ t) x =
      mε⁻¹ * matedLeastSupersolution m ε η ρ t a := by
    simp [rescale, hxa]
  have hrG : rescale mε ε η (fun b => ε⁻¹ * greenKernel m (interiorCellVertices ε η (ball 0 ρ)) 0 b) x =
      mε⁻¹ * (ε⁻¹ * greenKernel m (ballInterior ε η ρ) 0 a) := by
    simp [rescale, hxa, ballInterior]
  have key := exterior_real_bound hmε hc ht.le hrW hrG (hW x hxball) (hG x hxball hsx) hf
  have e : t / ε * greenKernel m (ballInterior ε η ρ) 0 a =
      t * (ε⁻¹ * greenKernel m (ballInterior ε η ρ) 0 a) := by ring
  rw [e]
  exact key

/-- **Abstract assembly of the exterior bound.** The bad set is contained in the complement of the pole event, the
two convergence events, and the complement of `Good` (a null set); each has the required limit or bound. -/
theorem tendsToOneOn_of_pole_and_limits {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F Good : Set Ω) (hGood : P Goodᶜ = 0) (E Pole : ℝ → Set Ω) (B41 : ℝ → Set Ω) (B33 : ℝ → ℝ → Set Ω)
    (hpole : ∀ η : ℝ≥0∞, 0 < η → ∃ s : ℝ, 0 < s ∧ P (F ∩ (Pole s)ᶜ) ≤ η)
    (h41 : Tendsto (fun ε => P (F ∩ B41 ε)) (𝓝[>] 0) (𝓝 0))
    (h33 : ∀ s : ℝ, 0 < s → Tendsto (fun ε => P (F ∩ B33 ε s)) (𝓝[>] 0) (𝓝 0))
    (hsub : ∀ s : ℝ, 0 < s → ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ ω ∈ F ∩ Pole s ∩ Good,
      ω ∉ B41 ε → ω ∉ B33 ε s → ω ∈ E ε) :
    TendsToOneOn P F E := by
  unfold TendsToOneOn
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  have hη3 : (0 : ℝ≥0∞) < η / 3 := ENNReal.div_pos_iff.2 ⟨hη.ne', by norm_num⟩
  obtain ⟨s, hs, hPs⟩ := hpole (η / 3) hη3
  filter_upwards [ENNReal.tendsto_nhds_zero.1 h41 (η / 3) hη3,
    ENNReal.tendsto_nhds_zero.1 (h33 s hs) (η / 3) hη3, hsub s hs] with ε h41ε h33ε hsubε
  have hsub' : F ∩ (E ε)ᶜ ⊆ (F ∩ (Pole s)ᶜ) ∪ (F ∩ B41 ε) ∪ (F ∩ B33 ε s) ∪ Goodᶜ := by
    intro ω hω
    obtain ⟨hF, hEω⟩ := hω
    by_cases hG : ω ∈ Good
    · by_cases hP : ω ∈ Pole s
      · by_cases h1 : ω ∈ B41 ε
        · exact Or.inl (Or.inl (Or.inr ⟨hF, h1⟩))
        · by_cases h2 : ω ∈ B33 ε s
          · exact Or.inl (Or.inr ⟨hF, h2⟩)
          · exact absurd (hsubε ω ⟨⟨hF, hP⟩, hG⟩ h1 h2) hEω
      · exact Or.inl (Or.inl (Or.inl ⟨hF, hP⟩))
    · exact Or.inr hG
  calc P (F ∩ (E ε)ᶜ) ≤ P ((F ∩ (Pole s)ᶜ) ∪ (F ∩ B41 ε) ∪ (F ∩ B33 ε s) ∪ Goodᶜ) := measure_mono hsub'
    _ ≤ P (F ∩ (Pole s)ᶜ) + P (F ∩ B41 ε) + P (F ∩ B33 ε s) + P Goodᶜ :=
        (measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans
          (add_le_add ((measure_union_le _ _)) le_rfl)) le_rfl)
    _ ≤ η / 3 + η / 3 + η / 3 + 0 :=
        add_le_add (add_le_add (add_le_add hPs h41ε) h33ε) (le_of_eq hGood)
    _ = η := by rw [add_zero, ENNReal.add_thirds]

/-- **`StoppedSurplusExteriorStep` from the origin hypothesis.** The explicit hypothesis `hpole` (the origin
neighbourhood: for each `η > 0` there is `s > 0` with `P[t < T, B_s(0) ⊄ Λ_t] ≤ η`) is the input reported in
ESCALATIONS E-c1-5 (b); `hmeps` is the External input `MepsScalingInput` (eq:meps-scaling). -/
theorem stoppedSurplusExterior_of_origin (𝒮 : SpaceFillingSLEModel) (hmeps : MepsScalingInput 𝒮)
    (hpole : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) →
      ∀ t : ℝ, 0 < t → ∀ η : ℝ≥0∞, 0 < η → ∃ s : ℝ, 0 < s ∧
        S.P ({ω | t < clusterExitTime (Λ ω) ρ} ∩ {ω | ¬ ball (0 : ℂ) s ⊆ Λ ω t}) ≤ η) :
    StoppedSurplusExteriorStep 𝒮 := by
  intro _ _ h41 h33 _ _ γ hγ hγ2 ρ hρ hρ1 Ω _ S hS Λ hΛ t ht κ hκ
  obtain ⟨C, hC1, hCS⟩ := hmeps γ hγ hγ2
  obtain ⟨ε₀, hε₀, hmεb⟩ := hCS Ω S hS
  have hC0 : 0 < C := by linarith
  have hm0 : 0 ≤ S.m₀ := by
    unfold MatedCRTEnv.m₀ medianOf
    exact Real.sInf_nonneg fun m hm => hm.1
  have hc : 0 ≤ S.c₀ / 6 := by
    unfold MatedCRTEnv.c₀
    exact div_nonneg (div_nonneg (by norm_num) hm0) (by norm_num)
  have hδ : 0 < κ / (2 * C * (1 + t)) := by positivity
  have hδsum : κ / (2 * C * (1 + t)) + t * (κ / (2 * C * (1 + t))) = κ / (2 * C) := by
    field_simp
  -- the almost sure facts
  have hgood : ∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω) ∧ IsAreaParametrized (S.μ ω) (S.η ω) ∧
      (∀ ε : ℝ, 0 < ε → vertexOf ε (S.η ω) 0 = 0) ∧ Tendsto (S.η ω) (cocompact ℝ) (cocompact ℂ) :=
    hΛ.and (hS.isAreaParametrized.and
      ((MatedCRTEnv.IsValid.ae_vertexOf_zero_eq_zero hS).and
        (MatedCRTEnv.IsValid.ae_tendsto_cocompact hS)))
  set Good : Set Ω := {ω | IsConeHarmonicBallFamily (S.μ ω) (Λ ω) ∧ IsAreaParametrized (S.μ ω) (S.η ω) ∧
    (∀ ε : ℝ, 0 < ε → vertexOf ε (S.η ω) 0 = 0) ∧ Tendsto (S.η ω) (cocompact ℝ) (cocompact ℂ)} with hGoodDef
  have hGoodnull : S.P Goodᶜ = 0 := ae_iff.1 hgood
  set δ : ℝ := κ / (2 * C * (1 + t)) with hδdef
  -- the three events
  set B41 : ℝ → Set Ω := fun ε => {ω | t < clusterExitTime (Λ ω) ρ ∧ ∃ x ∈ ball (0 : ℂ) ρ,
    δ < |rescaledMatedLeastSupersolution S ρ t ε ω x -
      S.c₀ / 6 * HarmonicBalls.leastSupersolution (S.μ ω) ρ 0 t x|} with hB41def
  set O : ℝ → Set ℂ := fun s => {y | y ∈ ball (0 : ℂ) ρ ∧ min s (ρ / 2) ≤ ‖y‖} with hOdef
  set B33 : ℝ → ℝ → Set Ω := fun ε s => {ω | ¬ ∀ x ∈ O s,
    |rescale (S.mε ε) ε (S.η ω) (fun a => ε⁻¹ *
      greenKernel (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball 0 ρ)) (vertexOf ε (S.η ω) 0) a) x -
      S.c₀ / 6 * HarmonicBalls.greenFunction (ball 0 ρ) 0 x| ≤ δ} with hB33def
  have hO_pos : ∀ s : ℝ, 0 < s → 0 < min s (ρ / 2) := fun s hs => lt_min hs (by linarith)
  have hOsub : ∀ s : ℝ, 0 < s → O s ⊆ closedBall (0 : ℂ) ρ \ {0} := by
    intro s hs y hy
    refine ⟨ball_subset_closedBall hy.1, fun h => ?_⟩
    rw [mem_singleton_iff] at h
    have hy2 := hy.2
    rw [h, norm_zero] at hy2
    exact absurd hy2 (not_le.2 (hO_pos s hs))
  have hOinf : ∀ s : ℝ, 0 < s → 0 < infDist (0 : ℂ) (O s) := by
    intro s hs
    have hm := hO_pos s hs
    have hy0 : (((min s (ρ / 2)) : ℝ) : ℂ) ∈ O s :=
      ⟨mem_ball_zero_iff.2 (by
          rw [Complex.norm_real, Real.norm_of_nonneg hm.le]
          linarith [min_le_right s (ρ / 2)]),
        le_of_eq (by rw [Complex.norm_real, Real.norm_of_nonneg hm.le])⟩
    have hle : min s (ρ / 2) ≤ infDist (0 : ℂ) (O s) :=
      (Metric.le_infDist ⟨_, hy0⟩).2 fun y hy => by
        rw [dist_zero_left]
        exact hy.2
    linarith
  refine tendsToOneOn_of_pole_and_limits S.P {ω | t < clusterExitTime (Λ ω) ρ} Good hGoodnull
    (fun ε => {ω | ∀ x ∉ cellVertices ε (S.η ω) (Λ ω t), matedLeastSupersolution (S.mult ε ω) ε (S.η ω) ρ t x +
      t / ε * greenKernel (S.mult ε ω) (ballInterior ε (S.η ω) ρ) 0 x ≤ κ / ε})
    (fun s => {ω | ball (0 : ℂ) s ⊆ Λ ω t}) B41 B33 ?_ ?_ ?_ ?_
  · exact hpole γ hγ hγ2 ρ hρ hρ1 Ω S hS Λ hΛ t ht
  · have hB41 := h41 γ hγ hγ2 ρ hρ hρ1 Ω S hS Λ hΛ t ht δ hδ
    have hsub41 : ∀ ε : ℝ, ({ω | t < clusterExitTime (Λ ω) ρ} : Set Ω) ∩ B41 ε = B41 ε :=
      fun ε => Set.inter_eq_right.2 (fun ω hω => hω.1)
    exact Tendsto.congr (fun ε => congrArg S.P (hsub41 ε).symm) hB41
  · intro s hs
    have hP33 := h33 γ hγ hγ2 ρ hρ hρ1 Ω S hS ρ 0 0 hρ subset_rfl (mem_ball_self hρ) δ hδ (O s)
      (hOsub s hs) (hOinf s hs)
    refine ENNReal.tendsto_nhds_zero.2 fun η hη => ?_
    filter_upwards [ENNReal.tendsto_nhds_zero.1 hP33 η hη] with ε hε
    exact le_trans (measure_mono Set.inter_subset_right) hε
  · intro s hs
    have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ ε < ε₀ := by
      filter_upwards [Ioo_mem_nhdsGT hε₀] with ε hε
      exact ⟨hε.1, hε.2⟩
    filter_upwards [hev] with ε hεε
    obtain ⟨hε, hεε₀⟩ := hεε
    intro ω hω h1 h2
    obtain ⟨⟨hF, hPole⟩, hGω⟩ := hω
    obtain ⟨hΛω, hηω, hv0ω, hcocω⟩ := hGω
    have hT : t < clusterExitTime (Λ ω) ρ := hF
    have hΛt : Λ ω t ⊆ ball 0 (ρ / 3) :=
      IDLALowerBound.subset_ball_div_three_of_lt_clusterExitTime hΛω.2.1.monotoneOn ht hT
    obtain ⟨hΛeq, hcont, -⟩ := hΛω.2.2 t (ρ / 3) ht (by linarith) hΛt ρ (by linarith)
    have hPole' : ball (0 : ℂ) (min s (ρ / 2)) ⊆ Λ ω t :=
      (ball_subset_ball (min_le_left _ _)).trans hPole
    have hW : ∀ y ∈ ball (0 : ℂ) ρ, |rescale (S.mε ε) ε (S.η ω)
        (matedLeastSupersolution (S.mult ε ω) ε (S.η ω) ρ t) y -
        S.c₀ / 6 * HarmonicBalls.leastSupersolution (S.μ ω) ρ 0 t y| ≤ δ := by
      intro y hy
      by_contra hlt
      exact h1 ⟨hF, y, hy, not_le.1 hlt⟩
    have hG' : ∀ y ∈ ball (0 : ℂ) ρ, min s (ρ / 2) ≤ ‖y‖ →
        |rescale (S.mε ε) ε (S.η ω) (fun b => ε⁻¹ *
          greenKernel (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball 0 ρ)) (vertexOf ε (S.η ω) 0) b) y -
          S.c₀ / 6 * HarmonicBalls.greenFunction (ball 0 ρ) 0 y| ≤ δ := by
      intro y hy hyO
      exact not_not.1 h2 y ⟨hy, hyO⟩
    intro x hx
    have hmεb' := hmεb ε hε hεε₀
    have hmpos : 0 < S.mε ε := lt_of_lt_of_le (by positivity) hmεb'.1
    by_cases hxB : x ∈ ballInterior ε (S.η ω) ρ
    · have hbound := exterior_vertex_bound hε ht hρ (hO_pos s hs) hc hmpos hηω hcocω (hv0ω ε hε)
        hΛeq hcont hPole' hW hG' hxB hx
      calc matedLeastSupersolution (S.mult ε ω) ε (S.η ω) ρ t x +
            t / ε * greenKernel (S.mult ε ω) (ballInterior ε (S.η ω) ρ) 0 x
          ≤ S.mε ε * (δ + t * δ) := hbound
        _ ≤ (C * ε⁻¹) * (δ + t * δ) := mul_le_mul_of_nonneg_right hmεb'.2 (by positivity)
        _ = κ / (2 * ε) := by
          rw [hδsum]
          field_simp
        _ ≤ κ / ε := by
          apply div_le_div_of_nonneg_left hκ.le hε
          linarith
    · exact le_trans (matedLeastSupersolution_add_green_le_of_not_mem hε ht hxB) (div_nonneg hκ.le hε.le)

end StoppedExterior

/-! ### Origin measurability and the exterior step (ESCALATIONS E-c1-5 (b)) -/

/-- **Origin measurability (named input, E-c1-5 (b)).** For `t > 0` and `s > 0` the inclusion event
`{ω | ¬ B_s(0) ⊆ Λ_t(ω)}` is null-measurable for `S.P`. Almost surely `Λ_t` is open and contains the pole `0`
(`IsHarmonicBall`), so these events decrease to a null set as `s ↓ 0`, and continuity from above needs their
measurability. The paper does not state it, and `ConeFamilyAEMeasurableStep` (`Steps/Sec2/ConeHarmonicBalls.lean`)
gives only almost-everywhere measurability of the family process. Consumed by `origin_of_nullMeasurable`. -/
def ConeOriginNullMeasurableStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) →
  ∀ t : ℝ, 0 < t → ∀ s : ℝ, 0 < s → NullMeasurableSet {ω | ¬ ball (0 : ℂ) s ⊆ Λ ω t} S.P

/-- The origin neighbourhood `hpole` of `StoppedExterior.stoppedSurplusExterior_of_origin`, proved from
`ConeOriginNullMeasurableStep`: the events `E_n = {¬ B_{1/(n+1)}(0) ⊆ Λ_t}` decrease to a null set (almost surely
`Λ_t` is open and contains `0`), so `P(E_n) → 0` by continuity from above, and
`{t < T} ∩ {¬ B_s(0) ⊆ Λ_t} ⊆ E_n` for `s = 1/(n+1)`. -/
theorem origin_of_nullMeasurable (𝒮 : SpaceFillingSLEModel) (hmeas : ConeOriginNullMeasurableStep 𝒮) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
    ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
    ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) →
    ∀ t : ℝ, 0 < t → ∀ η : ℝ≥0∞, 0 < η → ∃ s : ℝ, 0 < s ∧
      S.P ({ω | t < clusterExitTime (Λ ω) ρ} ∩ {ω | ¬ ball (0 : ℂ) s ⊆ Λ ω t}) ≤ η := by
  intro γ hγ hγ2 _ _ _ Ω _ S hS Λ hΛ t ht η hη
  have := hS.isProbabilityMeasure
  let E : ℕ → Set Ω := fun n => {ω | ¬ ball (0 : ℂ) (1 / ((n : ℝ) + 1)) ⊆ Λ ω t}
  have hE : ∀ n : ℕ, NullMeasurableSet (E n) S.P := fun n =>
    hmeas γ hγ hγ2 Ω S hS Λ hΛ t ht (1 / ((n : ℝ) + 1)) (by positivity)
  have hanti : Antitone E := by
    intro n m hnm ω hω
    show ¬ ball (0 : ℂ) (1 / ((n : ℝ) + 1)) ⊆ Λ ω t
    intro h
    apply (show ¬ ball (0 : ℂ) (1 / ((m : ℝ) + 1)) ⊆ Λ ω t from hω)
    have hnm' : (n : ℝ) ≤ m := by exact_mod_cast hnm
    exact (Metric.ball_subset_ball (one_div_le_one_div_of_le (by positivity) (by linarith))).trans h
  have hae : ∀ᵐ ω ∂S.P, ∃ s : ℝ, 0 < s ∧ ball (0 : ℂ) s ⊆ Λ ω t := by
    filter_upwards [hΛ] with ω hω
    obtain ⟨hHB, -, -⟩ := hω
    obtain ⟨hopen, h0, -⟩ := hHB t ht
    obtain ⟨s, hs, hsub⟩ := Metric.isOpen_iff.1 hopen 0 h0
    exact ⟨s, hs, hsub⟩
  have hnull : S.P (⋂ n, E n) = 0 := by
    refine measure_mono_null (fun ω hω => ?_) (ae_iff.1 hae)
    show ¬ ∃ s : ℝ, 0 < s ∧ ball (0 : ℂ) s ⊆ Λ ω t
    rintro ⟨s, hs, hsub⟩
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hs
    have hωn : ¬ ball (0 : ℂ) (1 / ((n : ℝ) + 1)) ⊆ Λ ω t := mem_iInter.1 hω n
    exact hωn ((Metric.ball_subset_ball hn.le).trans hsub)
  have hlim := tendsto_measure_iInter_atTop (fun n => hE n) hanti ⟨0, measure_ne_top _ _⟩
  have hlt : S.P (⋂ n, E n) < η := by rw [hnull]; exact hη
  obtain ⟨n, hn⟩ := ((tendsto_order.1 hlim).2 η hlt).exists
  exact ⟨1 / ((n : ℝ) + 1), by positivity, (measure_mono Set.inter_subset_right).trans hn.le⟩

/-- **`StoppedSurplusExteriorStep` from the origin measurability input** (E-c1-5 (b)). The remaining explicit
hypothesis is the External input `MepsScalingInput` (eq:meps-scaling). -/
theorem stoppedSurplusExterior_of_nullMeasurableOrigin (𝒮 : SpaceFillingSLEModel) (hmeps : MepsScalingInput 𝒮)
    (hmeas : ConeOriginNullMeasurableStep 𝒮) : StoppedSurplusExteriorStep 𝒮 :=
  StoppedExterior.stoppedSurplusExterior_of_origin 𝒮 hmeps (origin_of_nullMeasurable 𝒮 hmeas)

end MatedCRT
