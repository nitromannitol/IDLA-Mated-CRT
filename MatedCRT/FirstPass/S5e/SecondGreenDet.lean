import MatedCRT.FirstPass.S5e.KillSet
import MatedCRT.FirstPass.S5c.GreenRatio
import MatedCRT.FirstPass.S5d.StoppedFirstGreenInputs
import MatedCRT.Proofs.Sec5.IDLALowerBound.Stopped
import MatedCRT.Proofs.Sec5.LLowerBound.GreenMonotonicity

/-!
# The deterministic second Green inequality of the stopped clause (FIRST PASS, S5e)

Pathwise core of the second Green inequality (correction [C21], proof of Proposition 5.1, tex 2368-2372; referee notes
§5.3 and CHATGPT-idla-C20-C21-referee.md lines 252-300). For one scale `ε`, one outcome `ω` and one target `a` of the
stopped clause (`stoppedTargetSet`), with the killing set `I = stoppedKillSet`:

* `G_I(a,a) ≤ ε^{-1/2}`: domain monotonicity from `I ⊆ V^ε(B_ρ) \ V^ε(∂B_ρ)` and the crude bound (Draft 2.15);
* `∑_{b∈I} g_I(a,b) ≥ mr ε^{-1}`: the killing set contains `V^ε(B_s(η a))` (the Lemma 2.16 ball `B_r(η a)`,
  `r = δ/4`, is in `I` by `interiorCellVertices_subset_stoppedKillSet`), each of these vertices has `g ≥ 1` (Draft 2.16),
  and the cells covering the ball `B_s(η a)` have mass `ε` (`IsAreaParametrized`);
* `ε^{-1/4} ≤ ∑_{b∈I} G_I(b,a)/G_I(a,a)`: `MatedCRT.S5c.green_ratio_ge_quarter` (reversibility, `deg(a) ≥ 1`).

The probabilistic assembly is in `SecondGreenStep.lean`.
-/

open MeasureTheory Set Metric Filter Topology

namespace MatedCRT.S5e

/-- Each cell has `μ`-mass `ε` (`IsAreaParametrized`: `μ(η[a,b]) = b - a`). -/
lemma cell_measure_eq_ofReal {μ : Measure ℂ} {η : ℝ → ℂ} (hap : IsAreaParametrized μ η) {ε : ℝ} (hε : 0 < ε)
    (k : ℤ) : μ (cell ε η k) = ENNReal.ofReal ε := by
  unfold cell
  rw [hap.2.2.2 (ε * ((k : ℝ) - 1)) (ε * (k : ℝ)) (mul_lt_mul_of_pos_left (by linarith) hε)]
  congr 1
  ring

/-- Mass counting: a set covered by the cells of a finite vertex set `A` has mass at most `#A · ε`. -/
lemma measure_le_card_mul_of_cover {μ : Measure ℂ} {η : ℝ → ℂ} (hap : IsAreaParametrized μ η) {ε : ℝ}
    (hε : 0 < ε) {A : Set ℤ} (hA : A.Finite) {B : Set ℂ} (hB : B ⊆ fillCells ε η A) :
    μ B ≤ ENNReal.ofReal ((hA.toFinset.card : ℝ) * ε) := by
  have hset : fillCells ε η A = ⋃ k ∈ hA.toFinset, cell ε η k := by
    ext x
    simp [fillCells, Set.Finite.mem_toFinset]
  refine (measure_mono hB).trans ?_
  rw [hset]
  refine (measure_biUnion_finset_le _ _).trans ?_
  simp only [cell_measure_eq_ofReal hap hε]
  rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

/-- A set of mass at least `mr`, covered by the cells of a finite vertex set `A`, forces `mr ≤ #A · ε`. -/
lemma le_card_mul_of_mass {μ : Measure ℂ} {η : ℝ → ℂ} (hap : IsAreaParametrized μ η) {ε : ℝ} (hε : 0 < ε)
    {A : Set ℤ} (hA : A.Finite) {B : Set ℂ} (hB : B ⊆ fillCells ε η A) {mr : ℝ}
    (hmr : ENNReal.ofReal mr ≤ μ B) : mr ≤ (hA.toFinset.card : ℝ) * ε :=
  (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (Nat.cast_nonneg _) hε.le)).1
    (hmr.trans (measure_le_card_mul_of_cover hap hε hA hB))

/-- If a cell meets `B(z, R)` and has diameter at most `s`, every point of the cell is within `s + R` of `z`. -/
lemma dist_lt_of_cell {η : ℝ → ℂ} {ε s R : ℝ} {k : ℤ} {z : ℂ}
    (hd : ∀ x ∈ cell ε η k, ∀ y ∈ cell ε η k, dist x y ≤ s) (hz : (cell ε η k ∩ ball z R).Nonempty) :
    ∀ y ∈ cell ε η k, dist y z < s + R := by
  obtain ⟨x, hxc, hxb⟩ := hz
  intro y hy
  have h1 := hd y hy x hxc
  have h2 : dist x z < R := mem_ball.1 hxb
  have h3 := dist_triangle y x z
  linarith

/-- The vertex of a cell lies in that cell (`η(εk) ∈ η([ε(k-1), εk])`). -/
lemma vertexPoint_mem_cell {η : ℝ → ℂ} {ε : ℝ} (hε : 0 < ε) (k : ℤ) :
    vertexPoint ε η k ∈ cell ε η k :=
  ⟨ε * k, ⟨mul_le_mul_of_nonneg_left (by linarith) hε.le, le_refl _⟩, rfl⟩

/-- `exp (2C) ≤ Q` gives `2C ≤ log Q`. -/
lemma two_C_le_log {C Q : ℝ} (hQ : Real.exp (2 * C) ≤ Q) : 2 * C ≤ Real.log Q := by
  have h := Real.log_le_log (Real.exp_pos _) hQ
  rwa [Real.log_exp] at h

/-- Draft 2.16 (`GreenKernelLowerBoundStmt`) at radius `r` gives `g_J(a,b) ≥ 1` for a vertex `b` whose point is within
`2s` of `η(a)`, when `2 s e^{2C} ≤ r` and `ε ≤ e^{-2C}`. -/
lemma one_le_of_kernel_bound {C ε r s K : ℝ} {x y : ℂ} (hC : 0 < C) (hε : 0 < ε)
    (hεC : ε ≤ Real.exp (-(2 * C))) (hsr : 2 * s * Real.exp (2 * C) ≤ r)
    (hxy : dist x y ≤ 2 * s)
    (hK : C⁻¹ * Real.log (if x = y then ε⁻¹ else min (r / ‖x - y‖) ε⁻¹) - 1 ≤ K) : 1 ≤ K := by
  have hε0 : ε ≠ 0 := hε.ne'
  have hC0 : C ≠ 0 := hC.ne'
  have hεinv : Real.exp (2 * C) ≤ ε⁻¹ := by
    have h1 : Real.exp (2 * C) * ε ≤ 1 := by
      calc Real.exp (2 * C) * ε ≤ Real.exp (2 * C) * Real.exp (-(2 * C)) :=
            mul_le_mul_of_nonneg_left hεC (Real.exp_pos _).le
        _ = 1 := by rw [← Real.exp_add]; simp
    calc Real.exp (2 * C) = Real.exp (2 * C) * ε * ε⁻¹ := by field_simp
      _ ≤ 1 * ε⁻¹ := mul_le_mul_of_nonneg_right h1 (inv_nonneg.2 hε.le)
      _ = ε⁻¹ := one_mul _
  have hC2 : C⁻¹ * (2 * C) = 2 := by field_simp
  have hlog : 2 * C ≤ Real.log (if x = y then ε⁻¹ else min (r / ‖x - y‖) ε⁻¹) := by
    split_ifs with hxy'
    · exact two_C_le_log hεinv
    · rw [dist_eq_norm] at hxy
      have hpos : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hxy')
      have hr' : Real.exp (2 * C) ≤ r / ‖x - y‖ := by
        rw [le_div_iff₀ hpos]
        calc Real.exp (2 * C) * ‖x - y‖ ≤ Real.exp (2 * C) * (2 * s) :=
              mul_le_mul_of_nonneg_left hxy (Real.exp_pos _).le
          _ = 2 * s * Real.exp (2 * C) := by ring
          _ ≤ r := hsr
      exact two_C_le_log (le_min hr' hεinv)
  have h2 : 2 ≤ C⁻¹ * Real.log (if x = y then ε⁻¹ else min (r / ‖x - y‖) ε⁻¹) := by
    calc (2 : ℝ) = C⁻¹ * (2 * C) := hC2.symm
      _ ≤ C⁻¹ * Real.log (if x = y then ε⁻¹ else min (r / ‖x - y‖) ε⁻¹) :=
          mul_le_mul_of_nonneg_left hlog (inv_nonneg.2 hC.le)
  linarith

/-- Domain monotonicity of the Green function (`greenFn_mono_of_firstStep`, both domains finite). -/
lemma greenFn_mono_of_domain {m : ℤ → ℤ → ℕ} {A B : Set ℤ} (hlf : ∀ a, {b | m a b ≠ 0}.Finite)
    (hcons : ∀ a, m a (a + 1) ≠ 0) (hA : A.Finite) (hB : B.Finite) (hAB : A ⊆ B) (a b : ℤ) :
    greenFn m A a b ≤ greenFn m B a b :=
  greenFn_mono_of_firstStep hlf hcons hA hAB
    (fun c => WalkPotential.mLaplacian_greenFn hlf hcons hA c)
    (fun c => WalkPotential.mLaplacian_greenFn hlf hcons hB c) a b

/-- Domain monotonicity of the Green kernel `g = G / deg`. -/
lemma greenKernel_mono_of_domain {m : ℤ → ℤ → ℕ} {A B : Set ℤ} (hlf : ∀ a, {b | m a b ≠ 0}.Finite)
    (hcons : ∀ a, m a (a + 1) ≠ 0) (hA : A.Finite) (hB : B.Finite) (hAB : A ⊆ B) (a b : ℤ) :
    greenKernel m A a b ≤ greenKernel m B a b := by
  unfold greenKernel
  exact div_le_div_of_nonneg_right (greenFn_mono_of_domain hlf hcons hA hB hAB a b) (Nat.cast_nonneg _)

/-- The Green kernel is nonnegative. -/
lemma greenKernel_nonneg' (m : ℤ → ℤ → ℕ) (A : Set ℤ) (a b : ℤ) : 0 ≤ greenKernel m A a b := by
  unfold greenKernel greenFn
  exact div_nonneg ENNReal.toReal_nonneg (Nat.cast_nonneg _)

/-- A finite vertex set `F ⊆ I` on which the kernel is at least `1` has at most `∑_{b∈I} g_I(a,b)` vertices. -/
lemma card_le_tsum_kernel {m : ℤ → ℤ → ℕ} {I F : Set ℤ} (hI : I.Finite) (hF : F ⊆ I) (hFf : F.Finite) (a : ℤ)
    (hone : ∀ b ∈ F, 1 ≤ greenKernel m I a b) :
    (hFf.toFinset.card : ℝ) ≤ ∑' b : I, greenKernel m I a b := by
  rw [tsum_subtype_eq_sum_finite hI (greenKernel m I a)]
  have hsub : hFf.toFinset ⊆ hI.toFinset := by
    intro b hb
    rw [Set.Finite.mem_toFinset] at hb ⊢
    exact hF hb
  calc (hFf.toFinset.card : ℝ) = ∑ _b ∈ hFf.toFinset, (1 : ℝ) := by simp
    _ ≤ ∑ b ∈ hFf.toFinset, greenKernel m I a b :=
        Finset.sum_le_sum fun b hb => hone b ((Set.Finite.mem_toFinset _).1 hb)
    _ ≤ ∑ b ∈ hI.toFinset, greenKernel m I a b :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun b _ _ => greenKernel_nonneg' m I a b

/-- The first-moment bound `mr ε⁻¹ ≤ ∑_{b∈I} g_I(a,b)`: the cells covering `B_s(η a)` have mass `ε`, and the killing
set contains them, each with `g_I(a,b) ≥ 1`. -/
lemma mass_div_le_tsum_kernel {μ : Measure ℂ} {η : ℝ → ℂ} (hap : IsAreaParametrized μ η) {ε : ℝ} (hε : 0 < ε)
    {m : ℤ → ℤ → ℕ} {I : Set ℤ} (hI : I.Finite) (a : ℤ) {s mr : ℝ}
    (hF : cellVertices ε η (ball (vertexPoint ε η a) s) ⊆ I)
    (hone : ∀ b ∈ cellVertices ε η (ball (vertexPoint ε η a) s), 1 ≤ greenKernel m I a b)
    (hmr : ENNReal.ofReal mr ≤ μ (ball (vertexPoint ε η a) s)) :
    mr * ε⁻¹ ≤ ∑' b : I, greenKernel m I a b := by
  have hFf : (cellVertices ε η (ball (vertexPoint ε η a) s)).Finite := hI.subset hF
  have h1 := le_card_mul_of_mass hap hε hFf
    (IDLALowerBound.subset_fillCells_cellVertices hε hap.2.2.1 _) hmr
  have h2 := card_le_tsum_kernel hI hF hFf a hone
  calc mr * ε⁻¹ ≤ (hFf.toFinset.card : ℝ) := by
        rw [mul_inv_le_iff₀ hε]
        exact h1
    _ ≤ _ := h2

/-- `Λ_t ⊆ B_{ρ/3}` for `0 < t < T`, from the definition of the cluster exit time. -/
lemma subset_third_ball_of_lt {Λ : ℝ → Set ℂ} {ρ t : ℝ} (hmono : MonotoneOn Λ (Ioi 0)) (ht : 0 < t)
    (hT : t < clusterExitTime Λ ρ) : Λ t ⊆ ball 0 (ρ / 3) := by
  have hT' : t < sSup {s : ℝ | 0 < s ∧ Λ s ⊆ ball 0 (ρ / 3)} := hT
  have hne : {s : ℝ | 0 < s ∧ Λ s ⊆ ball 0 (ρ / 3)}.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h, Real.sSup_empty] at hT'
    linarith
  obtain ⟨s, ⟨hs0, hs⟩, hts⟩ := exists_lt_of_lt_csSup hne hT'
  intro x hx
  exact hs (hmono ht hs0 hts.le hx)

/-- **The pathwise second Green inequality of the stopped clause** (correction [C21], tex 2368-2372; referee §5.3).
At one scale `ε` and one outcome `ω`, with `r = δ/4`, `s = r e^{-2C}/6` and a mass bound `mr` on the balls `B_s(z)`,
`z ∈ B̄_ρ`: every target `a ∈ V^ε(B⁻_δ(Λ_t))` satisfies `ε^{-1/4} ≤ ∑_{b∈I} G_I(b,a) / G_I(a,a)`, with
`I = stoppedKillSet`. The hypotheses `hG15`, `hG16`, `hdiam` are the Draft 2.15, 2.16, 2.8 events at `ω`; `hfloor` is the
floor at level `δ/2` (the new probabilistic input `StoppedFloorHalfStep`). -/
theorem secondGreen_pointwise {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (Λ : Ω → ℝ → Set ℂ) (ω : Ω)
    {ρ t δ ε C ω₀ r s mr : ℝ}
    (hap : IsAreaParametrized (S.μ ω) (S.η ω))
    (hpath : StoppedPathwiseInputs S Λ ρ t ε ω)
    (hmono : MonotoneOn (Λ ω) (Ioi 0))
    (hδ : 0 < δ) (hδρ : δ < ρ) (hρ : 0 < ρ) (ht : 0 < t) (hT : t < clusterExitTime (Λ ω) ρ)
    (hε : 0 < ε) (hC : 0 < C) (hεC : ε ≤ Real.exp (-(2 * C)))
    (hr : r = δ / 4) (hs : s = r * Real.exp (-(2 * C)) / 6)
    (hεr : ε ^ ω₀ ≤ r)
    (hfloor : ∀ k : ℤ, (cell ε (S.η ω) k ∩ innerNbhd (δ / 2) (Λ ω t)).Nonempty →
      0 < stoppedOdometer (S.mult ε ω) ε (S.η ω) ρ t k)
    (hdiam : ∀ k : ℤ, (cell ε (S.η ω) k ∩ ball 0 ρ).Nonempty →
      ∀ x ∈ cell ε (S.η ω) k, ∀ y ∈ cell ε (S.η ω) k, dist x y ≤ s)
    (hG15 : ∀ a ∈ cellVertices ε (S.η ω) (ball 0 ρ), ∀ b ∈ cellVertices ε (S.η ω) (ball 0 ρ),
      greenFn (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball 0 ρ)) a b ≤ ε ^ (-(1 / 2 : ℝ)))
    (hG16 : ∀ a ∈ cellVertices ε (S.η ω) (ball 0 (ρ - ε ^ ω₀)), ∀ r' : ℝ, ε ^ ω₀ ≤ r' →
      r' ≤ infDist (vertexPoint ε (S.η ω) a) (sphere 0 ρ) →
      ∀ b ∈ cellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) a) (r' / 3)),
        C⁻¹ * Real.log (if vertexPoint ε (S.η ω) a = vertexPoint ε (S.η ω) b then ε⁻¹
          else min (r' / ‖vertexPoint ε (S.η ω) a - vertexPoint ε (S.η ω) b‖) ε⁻¹) - 1 ≤
        greenKernel (S.mult ε ω)
          (interiorCellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) a) r')) a b)
    (hmr : ∀ z ∈ closedBall (0 : ℂ) ρ, ENNReal.ofReal mr ≤ S.μ ω (ball z s))
    (hmrε : ε ^ (1 / 4 : ℝ) ≤ mr) :
    ∀ a ∈ stoppedTargetSet S Λ δ t ε ω,
      ε ^ (-(1 / 4 : ℝ)) ≤
        (∑' b : stoppedKillSet S Λ ρ t ε ω, greenFn (S.mult ε ω) (stoppedKillSet S Λ ρ t ε ω) b a) /
          greenFn (S.mult ε ω) (stoppedKillSet S Λ ρ t ε ω) a a := by
  obtain ⟨hsymm, hlf, hcons, -, hVfin, -, -⟩ := hpath
  -- constants
  have hr0 : 0 < r := by rw [hr]; linarith
  have hexp0 : 0 < Real.exp (-(2 * C)) := Real.exp_pos _
  have hexp1 : Real.exp (-(2 * C)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hs0 : 0 < s := by rw [hs]; exact div_pos (mul_pos hr0 hexp0) (by norm_num)
  have hsr6 : s ≤ r / 6 := by
    rw [hs]
    have : r * Real.exp (-(2 * C)) ≤ r * 1 := mul_le_mul_of_nonneg_left hexp1 hr0.le
    linarith
  have hsr : 2 * s * Real.exp (2 * C) ≤ r := by
    have hEE : Real.exp (2 * C) * Real.exp (-(2 * C)) = 1 := by rw [← Real.exp_add]; simp
    calc 2 * s * Real.exp (2 * C) = r / 3 * (Real.exp (2 * C) * Real.exp (-(2 * C))) := by
          rw [hs]; ring
      _ = r / 3 := by rw [hEE]; ring
      _ ≤ r := by linarith
  have hsr_le : s ≤ r := by linarith
  have hrs : r + s ≤ δ / 2 := by linarith
  have hsρ : s < ρ / 3 := by linarith
  have hρω : ρ / 3 ≤ ρ - ε ^ ω₀ := by linarith
  have hΛsub : Λ ω t ⊆ ball 0 (ρ / 3) := subset_third_ball_of_lt hmono ht hT
  have hΛball : Λ ω t ⊆ ball 0 ρ := fun x hx => ball_subset_ball (show ρ / 3 ≤ ρ by linarith) (hΛsub hx)
  -- finiteness of the killing set and of the interior of `B_ρ`
  have hIsub : stoppedKillSet S Λ ρ t ε ω ⊆ cellVertices ε (S.η ω) (ball 0 ρ) := by
    intro k hk
    obtain ⟨-, -, x, hx1, hx2⟩ := hk
    exact ⟨x, hx1, hΛball hx2⟩
  have hI : (stoppedKillSet S Λ ρ t ε ω).Finite := hVfin.subset hIsub
  have hJρ : (interiorCellVertices ε (S.η ω) (ball 0 ρ)).Finite := hVfin.subset fun k hk => hk.1
  have hIJ : stoppedKillSet S Λ ρ t ε ω ⊆ interiorCellVertices ε (S.η ω) (ball 0 ρ) := by
    intro k hk
    refine ⟨hIsub hk, ?_⟩
    rintro ⟨y, hy, hysph⟩
    rw [frontier_ball (0 : ℂ) hρ.ne', mem_sphere] at hysph
    obtain ⟨-, -, x, hx1, hx2⟩ := hk
    have hdk := hdiam k ⟨x, hx1, hΛball hx2⟩
    have := dist_lt_of_cell hdk ⟨x, hx1, hΛsub hx2⟩ y hy
    linarith
  -- the target points
  intro a ha'
  have ha := ha'
  obtain ⟨xa, hxa_cell, hxa_inn⟩ := ha'
  have hxaΛ : xa ∈ Λ ω t := hxa_inn.1
  have hxa3 : xa ∈ ball (0 : ℂ) (ρ / 3) := hΛsub hxaΛ
  have hxa_ball : xa ∈ ball (0 : ℂ) ρ := ball_subset_ball (show ρ / 3 ≤ ρ by linarith) hxa3
  have hxa_cellρ : (cell ε (S.η ω) a ∩ ball 0 ρ).Nonempty := ⟨xa, hxa_cell, hxa_ball⟩
  have hdA : ∀ x ∈ cell ε (S.η ω) a, ∀ y ∈ cell ε (S.η ω) a, dist x y ≤ s := hdiam a hxa_cellρ
  have hvA : vertexPoint ε (S.η ω) a ∈ cell ε (S.η ω) a := vertexPoint_mem_cell hε a
  have hA3 : ∀ y ∈ cell ε (S.η ω) a, dist y 0 < s + ρ / 3 :=
    dist_lt_of_cell hdA ⟨xa, hxa_cell, hxa3⟩
  have hvA_ball : dist (vertexPoint ε (S.η ω) a) 0 < s + ρ / 3 := hA3 _ hvA
  have hvA_mem : vertexPoint ε (S.η ω) a ∈ closedBall (0 : ℂ) ρ := by
    rw [mem_closedBall]
    linarith
  have hr_inf : r ≤ infDist (vertexPoint ε (S.η ω) a) (sphere 0 ρ) := by
    rw [Metric.le_infDist ⟨(ρ : ℂ), by rw [mem_sphere, dist_zero_right, Complex.norm_real,
      Real.norm_of_nonneg hρ.le]⟩]
    intro y hy
    rw [mem_sphere] at hy
    rw [dist_comm]
    linarith [dist_triangle y (vertexPoint ε (S.η ω) a) 0]
  -- the target lies in the killing domain, via the deterministic inclusion of `V^ε(B_r(η a))`
  have hdiamR : ∀ k : ℤ, (cell ε (S.η ω) k ∩ ball (vertexPoint ε (S.η ω) a) r).Nonempty →
      ∀ x ∈ cell ε (S.η ω) k, ∀ y ∈ cell ε (S.η ω) k, dist x y ≤ s := by
    intro k hk
    obtain ⟨z, hzc, hzb⟩ := hk
    refine hdiam k ⟨z, hzc, ?_⟩
    rw [mem_ball] at hzb ⊢
    have := dist_triangle z (vertexPoint ε (S.η ω) a) 0
    linarith
  have hJsub : interiorCellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) a) r) ⊆
      stoppedKillSet S Λ ρ t ε ω :=
    interiorCellVertices_subset_stoppedKillSet S Λ ω a hε hρ hδ hr0 hrs hT hΛsub hfloor ha hdiamR
  have ha_int : a ∈ interiorCellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) a) r) := by
    refine ⟨⟨vertexPoint ε (S.η ω) a, hvA, mem_ball_self hr0⟩, ?_⟩
    rintro ⟨y, hy, hysph⟩
    rw [frontier_ball _ hr0.ne', mem_sphere] at hysph
    have := hdA y hy _ hvA
    linarith
  have ha_I : a ∈ stoppedKillSet S Λ ρ t ε ω := hJsub ha_int
  have hJ_fin : (interiorCellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) a) r)).Finite :=
    hI.subset hJsub
  have hF_sub : cellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) a) s) ⊆
      interiorCellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) a) r) := by
    intro k hk
    obtain ⟨z, hzc, hzb⟩ := hk
    have hdk := hdiamR k ⟨z, hzc, ball_subset_ball hsr_le hzb⟩
    refine ⟨⟨z, hzc, ball_subset_ball hsr_le hzb⟩, ?_⟩
    rintro ⟨y, hy, hysph⟩
    rw [frontier_ball _ hr0.ne', mem_sphere] at hysph
    have := dist_lt_of_cell hdk ⟨z, hzc, hzb⟩ y hy
    linarith
  have hone : ∀ b ∈ cellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) a) s),
      1 ≤ greenKernel (S.mult ε ω) (stoppedKillSet S Λ ρ t ε ω) a b := by
    intro b hb
    obtain ⟨z, hzc, hzb⟩ := hb
    have hz0 : z ∈ ball (0 : ℂ) ρ := by
      rw [mem_ball] at hzb ⊢
      have := dist_triangle z (vertexPoint ε (S.η ω) a) 0
      linarith
    have hb_r : b ∈ cellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) a) (r / 3)) :=
      ⟨z, hzc, ball_subset_ball (show s ≤ r / 3 by linarith) hzb⟩
    have hG := hG16 a ⟨xa, hxa_cell, ball_subset_ball hρω hxa3⟩ r
      hεr hr_inf b hb_r
    have hdb := hdiam b ⟨z, hzc, hz0⟩ (vertexPoint ε (S.η ω) b) (vertexPoint_mem_cell hε b) z hzc
    have hxy : dist (vertexPoint ε (S.η ω) a) (vertexPoint ε (S.η ω) b) ≤ 2 * s := by
      have h1 := dist_triangle (vertexPoint ε (S.η ω) a) z (vertexPoint ε (S.η ω) b)
      have h2 := dist_comm z (vertexPoint ε (S.η ω) a)
      have h3 := dist_comm z (vertexPoint ε (S.η ω) b)
      rw [mem_ball] at hzb
      linarith
    exact le_trans (one_le_of_kernel_bound hC hε hεC hsr hxy hG)
      (greenKernel_mono_of_domain hlf hcons hJ_fin hI hJsub a b)
  have hq := mass_div_le_tsum_kernel hap hε hI a (hF_sub.trans hJsub) hone (hmr _ hvA_mem)
  have hden : greenFn (S.mult ε ω) (stoppedKillSet S Λ ρ t ε ω) a a ≤ ε ^ (-(1 / 2 : ℝ)) :=
    le_trans (greenFn_mono_of_domain hlf hcons hI hJρ hIJ a a) (hG15 a hxa_cellρ a hxa_cellρ)
  exact S5c.green_ratio_ge_quarter hsymm hlf hcons hI ha_I hε hq hmrε hden

end MatedCRT.S5e
