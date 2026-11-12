import MatedCRT.FirstPass.Derived.MatedCRTGraphBridge
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS3.Cells

/-!
# The cell sum over a ball from the localized integral of the density `u^ε`

For a cellular embedding `H` of the mated-CRT multigraph with the cells `H_k = η([ε (k - 1), ε k])`, the
density `u^ε = ∑_k deg(k) diam(H_k)² 1_{H_k} / area(H_k)` of Gwynne-Miller-Sheffield (GMS19, eq. (2.12))
integrates over each cell to `deg(k) diam(H_k)²` (the cells overlap in null sets). Consequently the cell sum
`∑_{k ∈ T} deg(k) diam(H_k)²` over a finite set `T` of vertices whose cells lie in a set `D` is at most
`∫_D u^ε`. This is the deterministic step that turns the localized integral estimate of GMS19, Prop. 2.10,
for the constant test function `f = 1` into the ball bound used for the Green kernel estimate of BG20,
Lemma 5.3 (Step 3):

* `sum_ofReal_cellDiam_sq_mul_deg_le_lintegral_uDens`: the cell sum is at most `∫_D u^ε`, in `ℝ≥0∞`;
* `sum_mdeg_mul_diam_sq_le_of_lintegral_bound`: if `∫_D u^ε ≤ A area(D) + η`, the real cell sum, with
  the degree `mdeg m` of the edge multiplicity `m` of the map, is at most `A area(D) + η`;
* `sum_mdeg_mul_diam_sq_le_of_ball`: the cells of vertices of `V(B_r(z))` of diameter at most `r` lie in
  `B_{2r}(z)`, so the cell sum is at most `4 π A r² + η` when `∫_{B_{2r}(z)} u^ε ≤ A area(B_{2r}(z)) + η`.
-/

set_option autoImplicit false

noncomputable section

open Set Metric MeasureTheory
open scoped ENNReal

namespace MatedCRT

section Cells

variable {V E : Type*} {G : MatedCRTHarmonic.LFMultigraph V E} {o : V}
  (H : MatedCRTHarmonic.CellularEmbedding G o)

/-- The cell sum `∑_{x ∈ T} deg(x) diam(H_x)²` of a finite set of vertices whose cells lie in `D` is at
most `∫_D u^ε`, since `∫_{H_x} u^ε = deg(x) diam(H_x)²` and the cells overlap in null sets. -/
theorem sum_ofReal_cellDiam_sq_mul_deg_le_lintegral_uDens (T : Finset V) {D : Set ℂ}
    (hT : ∀ x ∈ T, H.cell x ⊆ D) :
    ∑ x ∈ T, ENNReal.ofReal (MatedCRTHarmonic.GMS3.cellDiam H x ^ 2 * G.deg x) ≤
      ∫⁻ z in D, MatedCRTHarmonic.GMS3.uDens H z :=
  calc ∑ x ∈ T, ENNReal.ofReal (MatedCRTHarmonic.GMS3.cellDiam H x ^ 2 * G.deg x)
      = ∑ x ∈ T, ∫⁻ z in H.cell x, MatedCRTHarmonic.GMS3.uDens H z :=
        Finset.sum_congr rfl fun x _ => (MatedCRTHarmonic.GMS3.setLIntegral_cell_uDens H x).symm
    _ = ∫⁻ z in ⋃ x ∈ T, H.cell x, MatedCRTHarmonic.GMS3.uDens H z :=
        (MatedCRTHarmonic.GMS3.setLIntegral_biUnion_cell H T _).symm
    _ ≤ ∫⁻ z in D, MatedCRTHarmonic.GMS3.uDens H z :=
        lintegral_mono_set (iUnion₂_subset hT)

end Cells

section Mated

variable {E : Type*} {G : MatedCRTHarmonic.LFMultigraph ℤ E} {o : ℤ}
  (H : MatedCRTHarmonic.CellularEmbedding G o)

/-- **The cell sum from the localized integral bound.**  For a cellular embedding `H` of the multigraph of
the edge multiplicity `m` with the cells `H_k = η([ε (k - 1), ε k])`, a finite set `T` of vertices whose
cells lie in a bounded set `D`, and the localized integral bound `∫_D u^ε ≤ A area(D) + η` (the
conclusion of GMS19, Prop. 2.10, for the test function `f = 1`), the cell sum
`∑_{k ∈ T} deg(k) diam(H_k)²` is at most `A area(D) + η`. -/
theorem sum_mdeg_mul_diam_sq_le_of_lintegral_bound {ε : ℝ} {η : ℝ → ℂ} {m : ℤ → ℤ → ℕ}
    (hdeg : ∀ x, G.deg x = mdeg m x) (hH : ∀ x, H.cell x = cell ε η x) (T : Finset ℤ)
    {D : Set ℂ} (hD : Bornology.IsBounded D) (hT : ∀ k ∈ T, cell ε η k ⊆ D) {A tol : ℝ}
    (hA : 0 ≤ A) (htol : 0 ≤ tol)
    (hP : ∫⁻ z in D, MatedCRTHarmonic.GMS3.uDens H z ≤
      ENNReal.ofReal A * volume D + ENNReal.ofReal tol) :
    ∑ k ∈ T, (mdeg m k : ℝ) * diam (cell ε η k) ^ 2 ≤ A * (volume D).toReal + tol := by
  have hvol : volume D ≠ ⊤ := hD.measure_lt_top.ne
  have hnn : ∀ k ∈ T, 0 ≤ (mdeg m k : ℝ) * diam (cell ε η k) ^ 2 :=
    fun k _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  have h1 := sum_ofReal_cellDiam_sq_mul_deg_le_lintegral_uDens H T
    (fun x hx => (hH x).symm ▸ hT x hx)
  have h2 : ∑ x ∈ T, ENNReal.ofReal (MatedCRTHarmonic.GMS3.cellDiam H x ^ 2 * G.deg x) =
      ENNReal.ofReal (∑ k ∈ T, (mdeg m k : ℝ) * diam (cell ε η k) ^ 2) := by
    rw [ENNReal.ofReal_sum_of_nonneg hnn]
    refine Finset.sum_congr rfl fun k _ => ?_
    unfold MatedCRTHarmonic.GMS3.cellDiam
    rw [hH k, hdeg k, mul_comm]
  have h3 : ENNReal.ofReal A * volume D + ENNReal.ofReal tol =
      ENNReal.ofReal (A * (volume D).toReal + tol) := by
    rw [ENNReal.ofReal_add (mul_nonneg hA ENNReal.toReal_nonneg) htol,
      ENNReal.ofReal_mul hA, ENNReal.ofReal_toReal hvol]
  rw [h2] at h1
  have h4 := h1.trans (hP.trans h3.le)
  exact (ENNReal.ofReal_le_ofReal_iff (add_nonneg (mul_nonneg hA ENNReal.toReal_nonneg) htol)).1 h4

/-- **The cell sum of a ball.**  If the vertices of `T` have cells meeting `B_r(z)` of diameter at most `r`
(`η` continuous), the cells lie in `B_{2r}(z)`, so under the localized integral bound
`∫_{B_{2r}(z)} u^ε ≤ A area(B_{2r}(z)) + η` the cell sum `∑_{k ∈ T} deg(k) diam(H_k)²` is at most
`4 π A r² + η`. -/
theorem sum_mdeg_mul_diam_sq_le_of_ball {ε : ℝ} {η : ℝ → ℂ} {m : ℤ → ℤ → ℕ}
    (hdeg : ∀ x, G.deg x = mdeg m x) (hH : ∀ x, H.cell x = cell ε η x) (hη : Continuous η)
    (T : Finset ℤ) {z : ℂ} {r : ℝ} (hr : 0 < r) (hT : ∀ k ∈ T, k ∈ cellVertices ε η (ball z r))
    (hsz : ∀ k ∈ T, diam (cell ε η k) ≤ r) {A tol : ℝ} (hA : 0 ≤ A) (htol : 0 ≤ tol)
    (hP : ∫⁻ w in ball z (2 * r), MatedCRTHarmonic.GMS3.uDens H w ≤
      ENNReal.ofReal A * volume (ball z (2 * r)) + ENNReal.ofReal tol) :
    ∑ k ∈ T, (mdeg m k : ℝ) * diam (cell ε η k) ^ 2 ≤ 4 * Real.pi * A * r ^ 2 + tol := by
  have hsub : ∀ k ∈ T, cell ε η k ⊆ ball z (2 * r) := by
    intro k hk w hw
    obtain ⟨y, hyc, hyb⟩ := hT k hk
    have hbdd : Bornology.IsBounded (cell ε η k) :=
      (isCompact_Icc.image hη).isBounded
    have h1 : dist w y ≤ diam (cell ε η k) := dist_le_diam_of_mem hbdd hw hyc
    have h2 : dist y z < r := mem_ball.1 hyb
    rw [mem_ball]
    calc dist w z ≤ dist w y + dist y z := dist_triangle _ _ _
      _ < 2 * r := by linarith [hsz k hk]
  have key := sum_mdeg_mul_diam_sq_le_of_lintegral_bound H hdeg hH T isBounded_ball hsub hA htol hP
  have hv : (volume (ball z (2 * r))).toReal = Real.pi * (2 * r) ^ 2 := by
    rw [Complex.volume_ball, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (by linarith), ENNReal.coe_toReal, NNReal.coe_real_pi]
    ring
  rw [hv] at key
  calc _ ≤ A * (Real.pi * (2 * r) ^ 2) + tol := key
    _ = 4 * Real.pi * A * r ^ 2 + tol := by ring

end Mated

end MatedCRT
