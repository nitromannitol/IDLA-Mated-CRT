import MatedCRT.FirstPass.S5c.InteriorGreen
import MatedCRT.FirstPass.S5c.MassCluster
import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.CellIntegral
import MatedCRT.Proofs.Sec5.LLowerBound.GreenMonotonicity

/-!
# FIRST PASS, mass count of the interior ball (GAP 2, operator note 20:31): Step 4 of CHATGPT-q3-questions §1.4

Step 4 (eqs. (15)-(17)). The quantum mass of a ball `B_R(z)` is at most the number of cells indexed by `V^ε(B_R(z))`
times `ε`, because these cells cover the ball (every point lies in a cell, by surjectivity of `η`, Lemma
`exists_mem_cell_of_surj`) and every cell has mass `ε` (`measure_cell_of_area_parametrized`). Hence
`#V^ε(B_R(z)) ≥ m_r ε⁻¹` whenever `m_r ≤ μ_h(B_R(z))` (eq. (16)). A finite net gives `m_r ≤ μ_h(B_{cr}(z))` from the
net balls (eq. (15), `mass_ball_ge_of_net`). The Green sum `q_I(a) = ∑_{b∈I} g_I(a,b)` dominates the count, since
`g_I ≥ 0` on `I` and `g_I ≥ 1` on `V^ε(B_{cr}(z))` (Step 3, eq. (12)); this is eq. (17), `mass_le_green_sum`.
Not in this file: the almost-sure positivity `m_r > 0` (eq. (14)).
-/

namespace MatedCRT.S5c

open MeasureTheory Set Metric
open scoped ENNReal

/-- **Every point of the plane lies in a cell** (cells indexed by `k` are `η([ε(k-1), εk])`): if `η` is surjective,
then every `w ∈ ℂ` lies in some cell. Used for the covering of a ball by the cells of its vertices (§1.4 Step 4). -/
theorem exists_mem_cell_of_surj {ε : ℝ} {η : ℝ → ℂ} (hε : 0 < ε) (hsurj : Function.Surjective η) (w : ℂ) :
    ∃ k : ℤ, w ∈ cell ε η k := by
  obtain ⟨t, rfl⟩ := hsurj w
  have h1 : t / ε ≤ (⌈t / ε⌉ : ℝ) := Int.le_ceil _
  have h2 : (⌈t / ε⌉ : ℝ) < t / ε + 1 := Int.ceil_lt_add_one _
  have h3 : t ≤ (⌈t / ε⌉ : ℝ) * ε := (div_le_iff₀ hε).1 h1
  have h4 : ((⌈t / ε⌉ : ℝ) - 1) * ε < t := (lt_div_iff₀ hε).1 (by linarith)
  refine ⟨⌈t / ε⌉, ?_⟩
  unfold cell
  exact ⟨t, ⟨by linarith, by linarith⟩, rfl⟩

/-- **Finite sums over a finite domain**: the tsum over the subtype `I` is the Finset sum over `hI.toFinset`. -/
theorem tsum_subtype_eq_sum_of_finite {I : Set ℤ} (hI : I.Finite) (g : ℤ → ℝ) :
    ∑' b : I, g b = ∑ b ∈ hI.toFinset, g b := by
  rw [tsum_subtype I g, tsum_eq_sum (s := hI.toFinset)
    (fun b hb => Set.indicator_of_notMem (fun h => hb (hI.mem_toFinset.2 h)) g)]
  exact Finset.sum_congr rfl fun b hb => Set.indicator_of_mem (hI.mem_toFinset.1 hb) g

/-- **Count below a nonnegative sum** (§1.4 Step 4, eq. (17)): if `V ⊆ I` with `I` finite, `g ≥ 0` on `I` and `g ≥ 1` on
`V`, then `#V ≤ ∑_{b∈I} g(b)`. -/
theorem card_le_sum_of_ge_one {g : ℤ → ℝ} {I V : Set ℤ} (hI : I.Finite) (hVI : V ⊆ I)
    (hg0 : ∀ b ∈ I, 0 ≤ g b) (hg1 : ∀ b ∈ V, 1 ≤ g b) :
    (V.ncard : ℝ) ≤ ∑ b ∈ hI.toFinset, g b := by
  have hVf : V.Finite := hI.subset hVI
  calc (V.ncard : ℝ) = ∑ _b ∈ hVf.toFinset, (1 : ℝ) := by
        rw [Set.ncard_eq_toFinset_card V hVf, Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ ∑ b ∈ hVf.toFinset, g b :=
        Finset.sum_le_sum fun b hb => hg1 b (hVf.mem_toFinset.1 hb)
    _ ≤ ∑ b ∈ hI.toFinset, g b :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (fun b hb => hI.mem_toFinset.2 (hVI (hVf.mem_toFinset.1 hb)))
          (fun b hb _ => hg0 b (hI.mem_toFinset.1 hb))

/-- **Net lemma** (§1.4 Step 4, eq. (15)): if a finite net `t` covers the centre `z` by balls of radius `R/2` and every net
ball has mass at least `m_r`, then `μ_h(B_R(z)) ≥ m_r`. -/
theorem mass_ball_ge_of_net {μ : Measure ℂ} {R mr : ℝ} {t : Set ℂ} {z : ℂ}
    (hzt : z ∈ ⋃ x ∈ t, ball x (R / 2)) (hnet : ∀ x ∈ t, ENNReal.ofReal mr ≤ μ (ball x (R / 2))) :
    ENNReal.ofReal mr ≤ μ (ball z R) := by
  obtain ⟨x, hxt, hzx⟩ := mem_iUnion₂.1 hzt
  refine (hnet x hxt).trans (measure_mono (ball_subset_ball' ?_))
  have := mem_ball.1 hzx
  linarith [dist_comm x z]

/-- **Mass count of a ball** (§1.4 Step 4, eq. (16)): if the cells of `V^ε(B_R(z))` cover `B_R(z)` (η surjective), each of
mass `ε` (`hap`), and `V^ε(B_R(z))` is finite, then `m_r ε⁻¹ ≤ #V^ε(B_R(z))` whenever `m_r ≤ μ_h(B_R(z))`. -/
theorem card_ge_mass_div {μ : Measure ℂ} {η : ℝ → ℂ} {ε R mr : ℝ} {z : ℂ} (hap : IsAreaParametrized μ η)
    (hε : 0 < ε) (hsurj : Function.Surjective η) (hfin : (cellVertices ε η (ball z R)).Finite)
    (hmr : ENNReal.ofReal mr ≤ μ (ball z R)) :
    mr * ε⁻¹ ≤ ((cellVertices ε η (ball z R)).ncard : ℝ) := by
  set V := cellVertices ε η (ball z R) with hV
  have hcov : ball z R ⊆ fillCells ε η V := by
    intro x hx
    obtain ⟨k, hk⟩ := exists_mem_cell_of_surj hε hsurj x
    exact mem_iUnion₂.2 ⟨k, ⟨x, hk, hx⟩, hk⟩
  have hcm : ∀ k : ℤ, μ (cell ε η k) ≤ ENNReal.ofReal ε :=
    fun k => (measure_cell_of_area_parametrized hap hε k).le
  have hcard : (V.ncard : ℝ) ≤ ((V.ncard : ℝ) * ε) / ε := by
    rw [mul_div_assoc, div_self hε.ne', mul_one]
  have h1 : ENNReal.ofReal mr ≤ ENNReal.ofReal ((V.ncard : ℝ) * ε) :=
    hmr.trans ((measure_mono hcov).trans (measure_fillCells_le_of_card hε hfin hcm hcard))
  have h2 : mr ≤ (V.ncard : ℝ) * ε :=
    (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (Nat.cast_nonneg _) hε.le)).1 h1
  calc mr * ε⁻¹ ≤ ((V.ncard : ℝ) * ε) * ε⁻¹ := mul_le_mul_of_nonneg_right h2 (inv_nonneg.2 hε.le)
    _ = (V.ncard : ℝ) := by rw [mul_assoc, mul_inv_cancel₀ hε.ne', mul_one]

/-- **Green sum dominates the mass count** (§1.4 Steps 3-5, eqs. (12), (16), (17)). For the vertex `a` with `z = η(a)`
and `I = K_ε(B_r(z))`, and `m_r ≤ μ_h(B_{cr}(z))`: `m_r ε⁻¹ ≤ ∑_{b∈I} g_I(a,b)`. The hypotheses are those of
`one_le_greenKernel_interior` (Step 3) together with the surjectivity of `η`, the area parametrization of `μ_h` and the
mass bound `hmr`. -/
theorem mass_le_green_sum {μ : Measure ℂ} {m : ℤ → ℤ → ℕ} {η : ℝ → ℂ} {ε d C c r mr : ℝ} {a : ℤ}
    (hap : IsAreaParametrized μ η) (hsurj : Function.Surjective η)
    (hr : 0 < r) (hε : 0 < ε) (hc6 : c ≤ 1 / 6) (hd : d ≤ c * r) (hC : 0 < C)
    (h4c : 4 * c ≤ Real.exp (-(2 * C))) (hεC : ε ≤ Real.exp (-(2 * C)))
    (hlf : ∀ x, {y | m x y ≠ 0}.Finite) (hcons : ∀ x, m x (x + 1) ≠ 0)
    (hIfin : (interiorCellVertices ε η (ball (vertexPoint ε η a) r)).Finite)
    (hdiam : ∀ k : ℤ, (cell ε η k ∩ ball (vertexPoint ε η a) (r / 2)).Nonempty →
      ∀ x ∈ cell ε η k, ∀ y ∈ cell ε η k, dist x y ≤ d)
    (hvert : ∀ k : ℤ, vertexPoint ε η k ∈ cell ε η k)
    (hGlow : ∀ b' ∈ cellVertices ε η (ball (vertexPoint ε η a) (r / 2 / 3)),
      C⁻¹ * Real.log (if vertexPoint ε η a = vertexPoint ε η b' then ε⁻¹
          else min ((r / 2) / ‖vertexPoint ε η a - vertexPoint ε η b'‖) ε⁻¹) - 1 ≤
        greenKernel m (interiorCellVertices ε η (ball (vertexPoint ε η a) (r / 2))) a b')
    (hmr : ENNReal.ofReal mr ≤ μ (ball (vertexPoint ε η a) (c * r))) :
    mr * ε⁻¹ ≤ ∑' b : interiorCellVertices ε η (ball (vertexPoint ε η a) r),
      greenKernel m (interiorCellVertices ε η (ball (vertexPoint ε η a) r)) a b := by
  set z := vertexPoint ε η a with hz
  set I := interiorCellVertices ε η (ball z r) with hI_def
  have hdlt : d < r / 2 := by
    have := mul_le_mul_of_nonneg_right hc6 hr.le
    linarith
  have hcr2 : c * r ≤ r / 2 := by
    have := mul_le_mul_of_nonneg_right hc6 hr.le
    linarith
  have hVI : cellVertices ε η (ball z (c * r)) ⊆ I := by
    intro k hk
    apply cellVertices_half_ball_subset_interior hr hdlt hdiam
    obtain ⟨y, hyc, hyb⟩ := hk
    exact ⟨y, hyc, ball_subset_ball hcr2 hyb⟩
  have hfinV : (cellVertices ε η (ball z (c * r))).Finite := hIfin.subset hVI
  have hcount := card_ge_mass_div hap hε hsurj hfinV hmr
  have hg0 : ∀ b ∈ I, 0 ≤ greenKernel m I a b :=
    fun b _ => div_nonneg (greenFn_nonnegative m I a b) (Nat.cast_nonneg _)
  have hg1 : ∀ b ∈ cellVertices ε η (ball z (c * r)), 1 ≤ greenKernel m I a b :=
    fun b hb => one_le_greenKernel_interior hr hε hc6 hd hC h4c hεC hlf hcons hIfin hdiam hvert hGlow hb
  have hsum := card_le_sum_of_ge_one (g := fun b => greenKernel m I a b) hIfin hVI hg0 hg1
  calc mr * ε⁻¹ ≤ ((cellVertices ε η (ball z (c * r))).ncard : ℝ) := hcount
    _ ≤ ∑ b ∈ hIfin.toFinset, greenKernel m I a b := hsum
    _ = ∑' b : I, greenKernel m I a b := (tsum_subtype_eq_sum_of_finite hIfin (fun b => greenKernel m I a b)).symm

end MatedCRT.S5c
