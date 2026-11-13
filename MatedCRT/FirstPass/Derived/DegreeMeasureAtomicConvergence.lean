import MatedCRT.FirstPass.Derived.DegreeWeightedMeasureCells
import MatedCRT.FirstPass.Derived.DegreeWeightedMeasureCompactSupport
import MatedCRT.Draft.Section2
import MatedCRT.FirstPass.Derived.ReversibilityPairingDiscrete

/-!
# The cutoff atomic degree measure converges to `6 ψ μ_h` in probability

For the `ε`-mated-CRT map of a valid environment, with vertex positions `v_k = η(εk)`, a continuous
compactly supported cutoff `ψ ≥ 0` and the finite window `W` of the vertices with `v_k ∈ supp ψ`,
the atomic measure `ν^ε = Σ_{k ∈ W} ε deg^ε(k) ψ(v_k) δ_{v_k}` satisfies
`∫ f dν^ε → 6 ∫ f ψ dμ_h` in probability for every continuous `f`.

The proof transfers Lemma 2.10 (BG20 Corollary A.6: `∫ g dμ^ε_h → 6 ∫ g dμ_h` in probability, for the
measure `μ^ε_h` equal to `deg^ε(k) μ_h` on each cell `H^ε_k`) from `μ^ε_h` to the atomic `ν^ε`. Each
cell has `μ_h`-mass `ε`, so `∫ f ψ dμ^ε_h` and `∫ f dν^ε` differ by at most the oscillation of `f ψ`
over the cells meeting `supp ψ` times `ε Σ_k deg^ε(k)` over those cells; the oscillation is small
when the cells are small (uniform continuity of `f ψ`), and the degree mass is at most
`∫ χ dμ^ε_h` for a bump `χ = 1` near `supp ψ`, which is bounded in probability by Lemma 2.10 again.

* `abs_integral_atomicDegreeMeasure_sub_le`: the deterministic comparison of `∫ f dν^ε` and
  `∫ f ψ dμ^ε_h`;
* `tendstoInProbability_integral_atomicDegreeMeasure`: the convergence in probability, from Lemma
  2.10 for the environment and the convergence of the cell diameters near `supp ψ` to `0` in
  probability;
* `tendstoInProbability_integral_atomicDegreeMeasure_of_stmt`: the same from `DegreeMeasureConvergenceStmt`;
* `tendstoInProbability_integral_degreeCutoffMeasure`: the same for the cutoff degree measure
  `degreeCutoffMeasure` at the vertex positions of a continuous version `η'` of the curve, with the
  cell diameters controlled through `maxCellDiam`.
-/

open Set Metric MeasureTheory Filter Topology
open scoped ENNReal

namespace MatedCRT.FirstPass.Derived

/-- **Atomic replacement of the degree-weighted measure.** Let `η` be area-parametrized for `μ` and
proper, `ε > 0`, `ψ ≥ 0` continuous with `supp ψ ⊆ B̄_R`, and `s` the vertices `k` with
`v_k = η(εk) ∈ supp ψ`. Let `χ ≥ 0` be continuous, compactly supported and `1` on `B_{R+1}`. If every
cell meeting `B_{R+1}` has diameter at most `d < 1` and `|f ψ (x) - f ψ (y)| ≤ θ` whenever
`|x - y| ≤ d`, then the atomic measure `Σ_{k ∈ s} ε deg(k) ψ(v_k) δ_{v_k}` and the degree-weighted
measure `μ^ε_h` satisfy `|∫ f dν - ∫ f ψ dμ^ε_h| ≤ θ ∫ χ dμ^ε_h`. -/
theorem abs_integral_atomicDegreeMeasure_sub_le {m : ℤ → ℤ → ℕ} {ε : ℝ} {η : ℝ → ℂ}
    {μ : Measure ℂ} (hpar : IsAreaParametrized μ η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    (hε : 0 < ε) {ψ : ℂ → ℝ} (hψ : Continuous ψ) (hψ0 : ∀ z, 0 ≤ ψ z) {R : ℝ}
    (hψR : tsupport ψ ⊆ closedBall (0 : ℂ) R) (s : Finset ℤ)
    (hs : ∀ k, k ∈ s ↔ vertexPoint ε η k ∈ tsupport ψ) {f : ℂ → ℝ} (hf : Continuous f)
    {χ : ℂ → ℝ} (hχ : Continuous χ) (hχc : HasCompactSupport χ) (hχ0 : ∀ z, 0 ≤ χ z)
    (hχ1 : ∀ z ∈ ball (0 : ℂ) (R + 1), χ z = 1) {d θ : ℝ} (hd0 : 0 ≤ d) (hd1 : d < 1)
    (hdiam : ∀ k, (cell ε η k ∩ ball (0 : ℂ) (R + 1)).Nonempty → diam (cell ε η k) ≤ d)
    (hmod : ∀ x y, dist x y ≤ d → |f x * ψ x - f y * ψ y| ≤ θ) :
    |∫ x, f x ∂LatticeProb.atomicMeasure s
        (fun k => ε * (mdeg m k : ℝ) * ψ (vertexPoint ε η k)) (vertexPoint ε η) -
      ∫ x, f x * ψ x ∂degreeWeightedMeasure m ε η μ| ≤
      θ * ∫ x, χ x ∂degreeWeightedMeasure m ε η μ := by
  have hη : Continuous η := hpar.1
  have hθ : 0 ≤ θ := (abs_nonneg _).trans (hmod 0 0 (by rw [dist_self]; exact hd0))
  have hv : ∀ k, vertexPoint ε η k ∈ cell ε η k := fun k =>
    ⟨ε * k, ⟨mul_le_mul_of_nonneg_left (by linarith) hε.le, le_rfl⟩, rfl⟩
  have hRR : closedBall (0 : ℂ) R ⊆ ball (0 : ℂ) (R + 1) := closedBall_subset_ball (by linarith)
  -- the vertices whose cells meet `B̄_R`
  obtain ⟨t, hmemt⟩ : ∃ t : Finset ℤ, ∀ k, k ∈ t ↔ (cell ε η k ∩ closedBall (0 : ℂ) R).Nonempty :=
    have h := cellVertices_finite_of_isCompact hη hp hε (isCompact_closedBall (0 : ℂ) R)
    ⟨h.toFinset, fun k => h.mem_toFinset⟩
  have hdt : ∀ k ∈ t, ∀ x ∈ cell ε η k, ∀ y ∈ cell ε η k, dist x y ≤ d := by
    intro k hk x hx y hy
    obtain ⟨z, hz, hzR⟩ := (hmemt k).1 hk
    exact (dist_le_diam_of_mem (isCompact_cell hη ε k).isBounded hx hy).trans
      (hdiam k ⟨z, hz, hRR hzR⟩)
  -- `f ψ` vanishes on the cells outside `t`
  have hvan : ∀ k ∉ t, ∀ x ∈ cell ε η k, f x * ψ x = 0 := by
    intro k hk x hx
    have hψx : ψ x = 0 := by
      by_contra h
      exact hk ((hmemt k).2 ⟨x, hx, hψR (subset_tsupport ψ h)⟩)
    rw [hψx, mul_zero]
  have hcore : |∫ x, f x * ψ x ∂degreeWeightedMeasure m ε η μ -
      ε * ∑ k ∈ t, (matedDeg m k : ℝ) * (f (vertexPoint ε η k) * ψ (vertexPoint ε η k))| ≤
      ε * ∑ k ∈ t, (matedDeg m k : ℝ) * θ :=
    hpar.abs_integral_degreeWeightedMeasure_sub_le hε (hf.mul hψ) t hvan (vertexPoint ε η)
      (fun _ => θ) fun k hk x hx => hmod x _ (hdt k hk x hx _ (hv k))
  -- the atomic integral is `ε Σ_{k ∈ t} deg(k) f(v_k) ψ(v_k)`
  have hst : s ⊆ t := fun k hk => (hmemt k).2 ⟨_, hv k, hψR ((hs k).1 hk)⟩
  have hatom : ∫ x, f x ∂LatticeProb.atomicMeasure s
      (fun k => ε * (mdeg m k : ℝ) * ψ (vertexPoint ε η k)) (vertexPoint ε η) =
      ε * ∑ k ∈ t, (matedDeg m k : ℝ) * (f (vertexPoint ε η k) * ψ (vertexPoint ε η k)) := by
    rw [LatticeProb.integral_atomicMeasure s
      (c := fun k => ε * (mdeg m k : ℝ) * ψ (vertexPoint ε η k))
      (fun k => mul_nonneg (mul_nonneg hε.le (Nat.cast_nonneg _)) (hψ0 _)) (vertexPoint ε η) f,
      Finset.mul_sum]
    calc ∑ k ∈ s, ε * (mdeg m k : ℝ) * ψ (vertexPoint ε η k) * f (vertexPoint ε η k)
        = ∑ k ∈ s, ε * ((matedDeg m k : ℝ) *
            (f (vertexPoint ε η k) * ψ (vertexPoint ε η k))) :=
          Finset.sum_congr rfl fun k _ => by simp only [matedDeg]; ring
      _ = ∑ k ∈ t, ε * ((matedDeg m k : ℝ) *
            (f (vertexPoint ε η k) * ψ (vertexPoint ε η k))) := by
          refine Finset.sum_subset hst fun k _ hk => ?_
          rw [image_eq_zero_of_notMem_tsupport fun h => hk ((hs k).2 h)]
          ring
  -- `ε Σ_{k ∈ t} deg(k) ≤ ∫ χ dμ^ε_h`
  obtain ⟨R', hR'⟩ := hχc.isCompact.isBounded.subset_closedBall (0 : ℂ)
  obtain ⟨t', hmemt'⟩ : ∃ t' : Finset ℤ,
      ∀ k, k ∈ t' ↔ (cell ε η k ∩ closedBall (0 : ℂ) R').Nonempty :=
    have h := cellVertices_finite_of_isCompact hη hp hε (isCompact_closedBall (0 : ℂ) R')
    ⟨h.toFinset, fun k => h.mem_toFinset⟩
  have hvanχ : ∀ k ∉ t', ∀ x ∈ cell ε η k, χ x = 0 := by
    intro k hk x hx
    by_contra h
    exact hk ((hmemt' k).2 ⟨x, hx, hR' (subset_tsupport χ h)⟩)
  have hχeq := integral_degreeWeightedMeasure_eq_sum (m := m) (μ := μ) hχ hη t' hvanχ
    (fun k _ => hpar.integrableOn_cell hε hχ k)
  have htt' : t ⊆ t' := by
    intro k hk
    obtain ⟨z, hz, hzR⟩ := (hmemt k).1 hk
    refine (hmemt' k).2 ⟨z, hz, hR' (subset_tsupport χ ?_)⟩
    rw [Function.mem_support, hχ1 z (hRR hzR)]
    exact one_ne_zero
  have hcellχ : ∀ k ∈ t, ∫ x in cell ε η k, χ x ∂μ = ε := by
    intro k hk
    obtain ⟨z, hz, hzR⟩ := (hmemt k).1 hk
    have h1 : ∀ x ∈ cell ε η k, χ x = 1 := fun x hx => hχ1 x (by
      have h2 := hdt k hk x hx z hz
      have h3 : dist z 0 ≤ R := mem_closedBall.1 hzR
      exact mem_ball.2 (lt_of_le_of_lt (dist_triangle x z 0) (by linarith)))
    have h := hpar.abs_setIntegral_cell_sub_le hε hχ k (w := vertexPoint ε η k) (K := 0)
      fun x hx => by rw [h1 x hx, h1 _ (hv k), sub_self, abs_zero]
    rw [h1 _ (hv k), mul_one, mul_zero] at h
    exact sub_eq_zero.1 (abs_nonpos_iff.1 h)
  have hmass : ε * ∑ k ∈ t, (matedDeg m k : ℝ) ≤ ∫ x, χ x ∂degreeWeightedMeasure m ε η μ := by
    rw [hχeq, Finset.mul_sum]
    calc ∑ k ∈ t, ε * (matedDeg m k : ℝ)
        = ∑ k ∈ t, (matedDeg m k : ℝ) * ∫ x in cell ε η k, χ x ∂μ :=
          Finset.sum_congr rfl fun k hk => by rw [hcellχ k hk, mul_comm]
      _ ≤ ∑ k ∈ t', (matedDeg m k : ℝ) * ∫ x in cell ε η k, χ x ∂μ :=
          Finset.sum_le_sum_of_subset_of_nonneg htt' fun k _ _ =>
            mul_nonneg (Nat.cast_nonneg _) (integral_nonneg fun x => hχ0 x)
  rw [hatom, abs_sub_comm]
  calc |∫ x, f x * ψ x ∂degreeWeightedMeasure m ε η μ -
        ε * ∑ k ∈ t, (matedDeg m k : ℝ) * (f (vertexPoint ε η k) * ψ (vertexPoint ε η k))|
      ≤ ε * ∑ k ∈ t, (matedDeg m k : ℝ) * θ := hcore
    _ = θ * (ε * ∑ k ∈ t, (matedDeg m k : ℝ)) := by rw [← Finset.sum_mul]; ring
    _ ≤ θ * ∫ x, χ x ∂degreeWeightedMeasure m ε η μ := mul_le_mul_of_nonneg_left hmass hθ

/-- **The cutoff atomic degree measure converges to `6 ψ μ_h`** (C3 of the reversibility argument;
BG20 Corollary A.6 transferred from `μ^ε_h` to the atomic measure). On a valid environment, assume
Lemma 2.10 for it (`∫ g dμ^ε_h → 6 ∫ g dμ_h` in probability for continuous compactly supported `g`)
and that the diameters of the cells meeting each ball `B_{R+1}` tend to `0` in probability. Let
`ψ ≥ 0` be continuous with compact support and `W ε ω` a.s. the vertices `k` with
`η(εk) ∈ supp ψ`. Then for every continuous `f`,
`∫ f d(Σ_{k ∈ W} ε deg^ε(k) ψ(η(εk)) δ_{η(εk)}) → 6 ∫ f ψ dμ_h` in probability. -/
theorem tendstoInProbability_integral_atomicDegreeMeasure {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    (hS : S.IsValid 𝒮 γ)
    (hD27 : ∀ g : ℂ → ℝ, Continuous g → HasCompactSupport g → TendstoInProbability S.P
      (fun ε ω => ∫ x, g x ∂degreeWeightedMeasure (S.mult ε ω) ε (S.η ω) (S.μ ω))
      (fun ω => 6 * ∫ x, g x ∂S.μ ω))
    {ψ : ℂ → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) (hψ0 : ∀ z, 0 ≤ ψ z)
    (W : ℝ → Ω → Finset ℤ)
    (hW : ∀ᵐ ω ∂S.P, ∀ ε : ℝ, 0 < ε → ∀ k, k ∈ W ε ω ↔ vertexPoint ε (S.η ω) k ∈ tsupport ψ)
    (hdiam : ∀ R a : ℝ, 0 < a → Tendsto (fun ε => S.P {ω | ∃ k : ℤ,
      (cell ε (S.η ω) k ∩ ball (0 : ℂ) (R + 1)).Nonempty ∧ a < diam (cell ε (S.η ω) k)})
      (𝓝[>] 0) (𝓝 0))
    {f : ℂ → ℝ} (hf : Continuous f) :
    TendstoInProbability S.P
      (fun ε ω => ∫ x, f x ∂LatticeProb.atomicMeasure (W ε ω)
        (fun k => ε * (mdeg (S.mult ε ω) k : ℝ) * ψ (vertexPoint ε (S.η ω) k))
        (vertexPoint ε (S.η ω)))
      (fun ω => 6 * ∫ x, f x * ψ x ∂S.μ ω) := by
  have := hS.isProbabilityMeasure
  obtain ⟨R₀, hR₀⟩ := hψc.isCompact.isBounded.subset_closedBall (0 : ℂ)
  obtain ⟨R, hR0, hψR⟩ : ∃ R : ℝ, 0 ≤ R ∧ tsupport ψ ⊆ closedBall (0 : ℂ) R :=
    ⟨max R₀ 0, le_max_right _ _, hR₀.trans (closedBall_subset_closedBall (le_max_left _ _))⟩
  -- a bump `χ`: `1` on `B_{R+1}`, compactly supported
  obtain ⟨χ, hχ, hχc, hχ0, hχ1⟩ : ∃ χ : ℂ → ℝ, Continuous χ ∧ HasCompactSupport χ ∧
      (∀ x, 0 ≤ χ x) ∧ ∀ x ∈ ball (0 : ℂ) (R + 1), χ x = 1 := by
    let b : ContDiffBump (0 : ℂ) := ⟨R + 1, R + 2, by linarith, by linarith⟩
    have hrIn : b.rIn = R + 1 := rfl
    exact ⟨fun x => b x, b.continuous, b.hasCompactSupport, fun x => b.nonneg,
      fun x hx => b.one_of_mem_closedBall (by rw [hrIn]; exact ball_subset_closedBall hx)⟩
  have hφ : Continuous fun x => f x * ψ x := hf.mul hψ
  have hφc : HasCompactSupport fun x => f x * ψ x := hψc.mul_left (f := f)
  have hZ : AEMeasurable (fun ω => 6 * ∫ x, χ x ∂S.μ ω) S.P :=
    (frozenLQGTestIntegralMeasurable_holds γ hγ hγ2 Ω S.P S.hC S.hcirc S.μ
      ⟨hS.isProbabilityMeasure, hS.isQuantumCone, hS.isLQGMeasure⟩ χ hχ hχc).const_mul 6
  -- the almost sure event: `η` area-parametrized and proper, `W` the window of `supp ψ`
  have hgood : ∀ᵐ ω ∂S.P, (IsAreaParametrized (S.μ ω) (S.η ω) ∧
      Tendsto (S.η ω) (cocompact ℝ) (cocompact ℂ)) ∧
      ∀ ε' : ℝ, 0 < ε' → ∀ k, k ∈ W ε' ω ↔ vertexPoint ε' (S.η ω) k ∈ tsupport ψ := by
    filter_upwards [hS.isAreaParametrized, hS.ae_tendsto_cocompact, hW] with ω h1 h2 h3
    exact ⟨⟨h1, h2⟩, h3⟩
  have hgood0 : S.P {ω | (IsAreaParametrized (S.μ ω) (S.η ω) ∧
      Tendsto (S.η ω) (cocompact ℝ) (cocompact ℂ)) ∧
      ∀ ε' : ℝ, 0 < ε' → ∀ k, k ∈ W ε' ω ↔ vertexPoint ε' (S.η ω) k ∈ tsupport ψ}ᶜ = 0 :=
    mem_ae_iff.1 hgood
  refine tendstoInProbability_of_approx hZ (hD27 χ hχ hχc) fun θ hθ => ?_
  -- the cell scale `d` adapted to the modulus of continuity of `f ψ` at level `θ`
  obtain ⟨δ, hδ0, hδ⟩ := Metric.uniformContinuous_iff.1
    (hφc.uniformContinuous_of_continuous hφ) θ hθ
  obtain ⟨d, hd0, hd1, hdδ⟩ : ∃ d : ℝ, 0 < d ∧ d < 1 ∧ d < δ :=
    ⟨min (δ / 2) (1 / 2), lt_min (half_pos hδ0) one_half_pos,
      (min_le_right _ _).trans_lt (by norm_num), (min_le_left _ _).trans_lt (half_lt_self hδ0)⟩
  have hmod : ∀ x y, dist x y ≤ d → |f x * ψ x - f y * ψ y| ≤ θ := fun x y hxy => by
    have h := hδ (hxy.trans_lt hdδ)
    rw [Real.dist_eq] at h
    exact h.le
  refine ⟨fun ε ω => ∫ x, f x * ψ x ∂degreeWeightedMeasure (S.mult ε ω) ε (S.η ω) (S.μ ω),
    fun ω => 6 * ∫ x, f x * ψ x ∂S.μ ω,
    fun ε => {ω | ((IsAreaParametrized (S.μ ω) (S.η ω) ∧
      Tendsto (S.η ω) (cocompact ℝ) (cocompact ℂ)) ∧
      ∀ ε' : ℝ, 0 < ε' → ∀ k, k ∈ W ε' ω ↔ vertexPoint ε' (S.η ω) k ∈ tsupport ψ) ∧
      ∀ k, (cell ε (S.η ω) k ∩ ball (0 : ℂ) (R + 1)).Nonempty → diam (cell ε (S.η ω) k) ≤ d},
    hD27 _ hφ hφc, ?_, ?_⟩
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hdiam R d hd0)
      (fun _ => zero_le) fun ε => ?_
    refine (measure_mono (t := {ω | (IsAreaParametrized (S.μ ω) (S.η ω) ∧
        Tendsto (S.η ω) (cocompact ℝ) (cocompact ℂ)) ∧
        ∀ ε' : ℝ, 0 < ε' → ∀ k, k ∈ W ε' ω ↔ vertexPoint ε' (S.η ω) k ∈ tsupport ψ}ᶜ ∪
        {ω | ∃ k : ℤ, (cell ε (S.η ω) k ∩ ball (0 : ℂ) (R + 1)).Nonempty ∧
          d < diam (cell ε (S.η ω) k)}) fun ω hω => ?_).trans
      ((measure_union_le _ _).trans (le_of_eq ?_))
    · by_cases hg : (IsAreaParametrized (S.μ ω) (S.η ω) ∧
          Tendsto (S.η ω) (cocompact ℝ) (cocompact ℂ)) ∧
          ∀ ε' : ℝ, 0 < ε' → ∀ k, k ∈ W ε' ω ↔ vertexPoint ε' (S.η ω) k ∈ tsupport ψ
      · refine Or.inr ?_
        by_contra hne
        refine hω (show _ ∧ _ from ⟨hg, fun k hk => ?_⟩)
        by_contra hlt
        exact hne ⟨k, hk, not_le.1 hlt⟩
      · exact Or.inl hg
    · rw [hgood0, zero_add]
  · filter_upwards [self_mem_nhdsWithin] with ε hε0
    rintro ω ⟨⟨⟨hpar, hp⟩, hWω⟩, hsmall⟩
    have hε : (0 : ℝ) < ε := hε0
    refine ⟨?_, ?_⟩
    · exact (abs_integral_atomicDegreeMeasure_sub_le hpar hp hε hψ hψ0 hψR (W ε ω) (hWω ε hε)
        hf hχ hχc hχ0 hχ1 hd0.le hd1 hsmall hmod).trans
        (mul_le_mul_of_nonneg_left (le_abs_self _) hθ.le)
    · simp only [sub_self, abs_zero]
      exact mul_nonneg hθ.le (abs_nonneg _)

/-- `tendstoInProbability_integral_atomicDegreeMeasure` with Lemma 2.10 given as
`DegreeMeasureConvergenceStmt`. -/
theorem tendstoInProbability_integral_atomicDegreeMeasure_of_stmt {𝒮 : SpaceFillingSLEModel}
    (hD27 : DegreeMeasureConvergenceStmt 𝒮) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ω : Type}
    [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    {ψ : ℂ → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) (hψ0 : ∀ z, 0 ≤ ψ z)
    (W : ℝ → Ω → Finset ℤ)
    (hW : ∀ᵐ ω ∂S.P, ∀ ε : ℝ, 0 < ε → ∀ k, k ∈ W ε ω ↔ vertexPoint ε (S.η ω) k ∈ tsupport ψ)
    (hdiam : ∀ R a : ℝ, 0 < a → Tendsto (fun ε => S.P {ω | ∃ k : ℤ,
      (cell ε (S.η ω) k ∩ ball (0 : ℂ) (R + 1)).Nonempty ∧ a < diam (cell ε (S.η ω) k)})
      (𝓝[>] 0) (𝓝 0))
    {f : ℂ → ℝ} (hf : Continuous f) :
    TendstoInProbability S.P
      (fun ε ω => ∫ x, f x ∂LatticeProb.atomicMeasure (W ε ω)
        (fun k => ε * (mdeg (S.mult ε ω) k : ℝ) * ψ (vertexPoint ε (S.η ω) k))
        (vertexPoint ε (S.η ω)))
      (fun ω => 6 * ∫ x, f x * ψ x ∂S.μ ω) :=
  tendstoInProbability_integral_atomicDegreeMeasure hγ hγ2 hS (hD27 γ hγ hγ2 Ω S hS) hψ hψc hψ0
    W hW hdiam hf

/-- Convergence in probability is unchanged when the random variables are modified, for all `ε` at
once, off a null set. -/
private theorem tendstoInProbability_of_ae_forall_eq {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X X' : ℝ → Ω → ℝ} {Y : Ω → ℝ} (h : TendstoInProbability P X Y)
    (hXX' : ∀ᵐ ω ∂P, ∀ ε, X ε ω = X' ε ω) : TendstoInProbability P X' Y := by
  intro δ hδ
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (h δ hδ)
    (fun _ => zero_le) fun ε => measure_mono_ae ?_
  filter_upwards [hXX'] with ω hω hlt
  show δ < |X ε ω - Y ω|
  rw [hω ε]
  exact hlt

/-- **The cutoff degree measure converges to `6 ψ μ_h`**: `tendstoInProbability_integral_atomicDegreeMeasure`
for `degreeCutoffMeasure`, the atomic measure `Σ ε deg^ε(k) ψ(v_k) δ_{v_k}` over the vertices with
`v_k ∈ supp ψ`, at the vertex positions `v_k = η'(εk)` of a continuous version `η'` of the curve, and
with the diameters of the cells meeting `B_{R+1}` controlled through `maxCellDiam`. -/
theorem tendstoInProbability_integral_degreeCutoffMeasure {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    (hS : S.IsValid 𝒮 γ)
    (hD27 : ∀ g : ℂ → ℝ, Continuous g → HasCompactSupport g → TendstoInProbability S.P
      (fun ε ω => ∫ x, g x ∂degreeWeightedMeasure (S.mult ε ω) ε (S.η ω) (S.μ ω))
      (fun ω => 6 * ∫ x, g x ∂S.μ ω))
    {η' : Ω → C(ℝ, ℂ)} (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω)
    {ψ : ℂ → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) (hψ0 : ∀ z, 0 ≤ ψ z)
    (hdiam : ∀ R a : ℝ, 0 < a →
      Tendsto (fun ε => S.P {ω | ENNReal.ofReal a < maxCellDiam ε (⇑(η' ω)) R}) (𝓝[>] 0) (𝓝 0))
    {f : ℂ → ℝ} (hf : Continuous f) :
    TendstoInProbability S.P
      (fun ε ω => ∫ x, f x ∂(degreeCutoffMeasure (S.mult ε ω) ε (vertexPoint ε (⇑(η' ω))) ψ :
        Measure ℂ))
      (fun ω => 6 * ∫ x, f x * ψ x ∂S.μ ω) := by
  have hW : ∀ᵐ ω ∂S.P, ∀ ε : ℝ, 0 < ε → ∀ k,
      k ∈ vertexWindow (vertexPoint ε (⇑(η' ω))) (tsupport ψ) ↔
        vertexPoint ε (S.η ω) k ∈ tsupport ψ := by
    filter_upwards [hae, hS.ae_tendsto_cocompact] with ω h hp ε hε k
    have hp' : Tendsto (⇑(η' ω)) (cocompact ℝ) (cocompact ℂ) := by rw [h]; exact hp
    rw [mem_vertexWindow (vertexPoint_preimage_finite hε (η' ω).continuous hp' hψc.isCompact), h]
  have hdiam' : ∀ R a : ℝ, 0 < a → Tendsto (fun ε => S.P {ω | ∃ k : ℤ,
      (cell ε (S.η ω) k ∩ ball (0 : ℂ) (R + 1)).Nonempty ∧ a < diam (cell ε (S.η ω) k)})
      (𝓝[>] 0) (𝓝 0) := by
    intro R a ha
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hdiam R a ha)
      (fun _ => zero_le) fun ε => measure_mono_ae ?_
    filter_upwards [hae] with ω h
    rintro ⟨k, hk, hlt⟩
    show ENNReal.ofReal a < maxCellDiam ε (⇑(η' ω)) R
    rw [h]
    exact ((ENNReal.ofReal_lt_ofReal_iff (ha.trans hlt)).2 hlt).trans_le
      (le_iSup₂ (f := fun k (_ : (cell ε (S.η ω) k ∩ ball (0 : ℂ) (R + 1)).Nonempty) =>
        ENNReal.ofReal (diam (cell ε (S.η ω) k))) k hk)
  have H : TendstoInProbability S.P
      (fun ε ω => ∫ x, f x ∂LatticeProb.atomicMeasure
        (vertexWindow (vertexPoint ε (⇑(η' ω))) (tsupport ψ))
        (fun k => ε * (mdeg (S.mult ε ω) k : ℝ) * ψ (vertexPoint ε (S.η ω) k))
        (vertexPoint ε (S.η ω)))
      (fun ω => 6 * ∫ x, f x * ψ x ∂S.μ ω) :=
    tendstoInProbability_integral_atomicDegreeMeasure hγ hγ2 hS hD27 hψ hψc hψ0
      (fun ε ω => vertexWindow (vertexPoint ε (⇑(η' ω))) (tsupport ψ)) hW hdiam' hf
  refine tendstoInProbability_of_ae_forall_eq H ?_
  filter_upwards [hae] with ω h ε
  rw [← h]
  rfl

end MatedCRT.FirstPass.Derived
