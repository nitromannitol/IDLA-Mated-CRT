import MatedCRT.FirstPass.S4S6c.HoneInputsDirect

/-!
# The binders `hdiam` and `hVol` of `hone_exitQ_walk_of_env_direct` (task fp-S4S6c-hdiam-hvol; worker z10)

Replacement inputs for two binders of `hone_exitQ_walk_of_env_direct` (HoneInputsDirect.lean), each stated with
exactly the type it replaces, so that the consumer can take them unchanged.

* `hdiam_of_mesh68` (replaces the binder `hdiam`, HoneInputsDirect.lean:100): the test-ball cell bound
  `diam (cell k') ≤ c₀ R_k` for every cell meeting `B(v, R_k/4)`, `v = vertexPoint (ω (T k ω))`. It comes from a mesh
  bound `diam (cell k') ≤ ε^κ` on the ball `B_{ρ'}` that contains the test balls (`ρ' ≥ ρc + 3/8`), the scale
  `10 ε^{ω₀} ≤ r` (Lemma 6.8 setting, Constants.lean:9) with `r² ≤ R_k`, the exponent inequality `2ω₀ < κ` and the
  smallness `ε ≤ (100 c₀)^{1/(κ − 2ω₀)}`, and the walk hypothesis that the cell of the walk state meets `B_{ρc}`.
* `hvol_of_direct68` (replaces the binder `hVol`, HoneInputsDirect.lean:110): the two local volume conclusions that
  `hone_exitQ_walk_of_env` takes from `hVol` (HoneInputs.lean:149 at `δ = c₀R_k`, HoneInputs.lean:155 at `δ = R_k/4`),
  taken as direct binders at the random radii.

No frozen statement is touched. No hypothesis of the consumer is weakened: `hdiam_of_mesh68` needs the mesh bound on a
larger ball than the walk ball `B_{ρc}`, and `hvol_of_direct68` needs the two direct bounds at random radii; see the report.
-/

namespace MatedCRT

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology

namespace Lemma68Window

/-- **Pointwise test-ball cell bound (mesh form).** Let `a` be a vertex whose cell meets `B_{ρc}` (the walk state),
`v = vertexPoint ε η a` its vertex point, `κ` the cell-size exponent (`κ = 2/(2+γ)² − ζ` in Lemma 2.8), and `ρ' ≥ ρc + 3/8`.
If every cell meeting `B_{ρ'}` has diameter `≤ ε^κ`, `2ω₀ < κ`, `ε ≤ (100 c₀)^{1/(κ − 2ω₀)}`, and the test radius `R`
satisfies `(10 ε^{ω₀})² ≤ r² ≤ R ≤ 1`, then every cell meeting `B(v, R/4)` has diameter `≤ c₀ R`.

Proof: `ε^κ = ε^{2ω₀} ε^{κ−2ω₀} ≤ ε^{2ω₀} · 100 c₀ ≤ c₀ R` (since `100 ε^{2ω₀} ≤ R`); the vertex point lies within `ε^κ`
of the cell point `p₀ ∈ B_{ρc}`, so every point of `B(v, R/4)` lies in `B_{ρc + 1/4 + 1/24} ⊆ B_{ρ'}`. -/
theorem diam_cell_le_of_mesh68 {γ ρc : ℝ} (K : Constants68 γ ρc) {ε : ℝ} {η : ℝ → ℂ} (hη : Continuous η) (hε : 0 < ε)
    {κ : ℝ} (hκ : 2 * K.ω < κ) (hεsm : ε ≤ (100 * K.c0) ^ (1 / (κ - 2 * K.ω)))
    {ρ' : ℝ} (hρ' : ρc + 3 / 8 ≤ ρ')
    (hmesh : ∀ k' : ℤ, (cell ε η k' ∩ ball (0 : ℂ) ρ').Nonempty → diam (cell ε η k') ≤ ε ^ κ)
    (a : ℤ) (hwalk : (cell ε η a ∩ ball (0 : ℂ) ρc).Nonempty)
    {r R : ℝ} (hr10 : 10 * ε ^ K.ω ≤ r) (hRr : r ^ 2 ≤ R) (hR1 : R ≤ 1) :
    ∀ k' : ℤ, (cell ε η k' ∩ ball (vertexPoint ε η a) (R / 4)).Nonempty → diam (cell ε η k') ≤ K.c0 * R := by
  have hd : 0 < κ - 2 * K.ω := by linarith
  have hc100 : 0 ≤ 100 * K.c0 := by linarith [K.hc0]
  -- the exponent smallness `ε^{κ−2ω₀} ≤ 100 c₀`
  have hsmall : ε ^ (κ - 2 * K.ω) ≤ 100 * K.c0 :=
    calc ε ^ (κ - 2 * K.ω)
        ≤ ((100 * K.c0) ^ (1 / (κ - 2 * K.ω))) ^ (κ - 2 * K.ω) := Real.rpow_le_rpow hε.le hεsm hd.le
      _ = 100 * K.c0 := by
          rw [← Real.rpow_mul hc100, one_div_mul_cancel hd.ne', Real.rpow_one]
  -- the exponent split `ε^κ = ε^{2ω₀} ε^{κ−2ω₀}`
  have hsplit : ε ^ κ = ε ^ (2 * K.ω) * ε ^ (κ - 2 * K.ω) := by
    rw [← Real.rpow_add hε]
    congr 1
    ring
  -- the scale `100 ε^{2ω₀} ≤ r² ≤ R`
  have hsq : (ε ^ K.ω) ^ 2 = ε ^ (2 * K.ω) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hε.le]
    congr 1
    push_cast
    ring
  have hR100 : 100 * ε ^ (2 * K.ω) ≤ R := by
    have h0 : 0 ≤ 10 * ε ^ K.ω := mul_nonneg (by norm_num) (Real.rpow_nonneg hε.le _)
    have h1 : (10 * ε ^ K.ω) ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ h0 hr10 2
    have h2 : (10 * ε ^ K.ω) ^ 2 = 100 * ε ^ (2 * K.ω) := by
      rw [mul_pow, hsq]
      norm_num
    linarith
  have hpow : 0 ≤ ε ^ (2 * K.ω) := Real.rpow_nonneg hε.le _
  -- the cell bound `ε^κ ≤ c₀ R`
  have hκR : ε ^ κ ≤ K.c0 * R := by
    rw [hsplit]
    have h1 : ε ^ (2 * K.ω) * ε ^ (κ - 2 * K.ω) ≤ ε ^ (2 * K.ω) * (100 * K.c0) :=
      mul_le_mul_of_nonneg_left hsmall hpow
    have h2 : K.c0 * (100 * ε ^ (2 * K.ω)) ≤ K.c0 * R := mul_le_mul_of_nonneg_left hR100 K.hc0.le
    nlinarith [h1, h2]
  have hc0R : K.c0 * R ≤ 1 / 24 := le_trans (mul_le_of_le_one_right K.hc0.le hR1) K.hc0'
  have hεκ : ε ^ κ ≤ 1 / 24 := le_trans hκR hc0R
  -- the walk vertex lies within `ε^κ` of a point of `B_{ρc}`
  obtain ⟨p0, hp0c, hp0b⟩ := hwalk
  have hcρ : ρc ≤ ρ' := by linarith
  have hvd : dist (vertexPoint ε η a) p0 ≤ ε ^ κ :=
    (dist_le_diam_cell_direct hη a (vertexPoint_mem_cell_direct hε a) hp0c).trans
      (hmesh a ⟨p0, hp0c, ball_subset_ball hcρ hp0b⟩)
  have hp0n : dist p0 0 < ρc := by
    rw [dist_zero_right]
    exact mem_ball_zero_iff.mp hp0b
  intro k' ⟨q, hqc, hqb⟩
  have hqρ : q ∈ ball (0 : ℂ) ρ' := by
    rw [mem_ball_zero_iff]
    have hq1 : dist q (vertexPoint ε η a) < R / 4 := Metric.mem_ball.mp hqb
    have t1 : dist q 0 ≤ dist q (vertexPoint ε η a) + dist (vertexPoint ε η a) 0 := dist_triangle _ _ _
    have t2 : dist (vertexPoint ε η a) 0 ≤ dist (vertexPoint ε η a) p0 + dist p0 0 := dist_triangle _ _ _
    rw [← dist_zero_right]
    linarith
  exact (hmesh k' ⟨q, hqc, hqρ⟩).trans hκR

/-- **`hdiam` of `hone_exitQ_walk_of_env_direct` from a mesh bound.** Same type as the binder `hdiam`
(HoneInputsDirect.lean:100). The mesh bound is on the ball `B_{ρ'}` (`ρ' ≥ ρc + 3/8`) that contains the walk ball
`B_{ρc}` together with the test balls `B(v, R/4)`, not on the whole plane. The walk hypothesis `hWalk` is the cell form of
`hWalk` (HoneInputsDirect.lean:78): the cell of the walk state meets `B_{ρc}`. -/
theorem hdiam_of_mesh68 {γ ρc : ℝ} (K : Constants68 γ ρc) (ε : ℝ) (η : ℝ → ℂ) (hη : Continuous η) (hε : 0 < ε)
    {κ : ℝ} (hκ : 2 * K.ω < κ) (hεsm : ε ≤ (100 * K.c0) ^ (1 / (κ - 2 * K.ω)))
    {ρ' : ℝ} (hρ' : ρc + 3 / 8 ≤ ρ')
    (hmesh : ∀ k' : ℤ, (cell ε η k' ∩ ball (0 : ℂ) ρ').Nonempty → diam (cell ε η k') ≤ ε ^ κ)
    {A : Set ℤ} {τU : (ℕ → ℤ) → ℕ∞} {T : ℕ → (ℕ → ℤ) → ℕ∞} {R : ℕ → (ℕ → ℤ) → ℝ} {r : ℝ}
    (hr10 : 10 * ε ^ K.ω ≤ r)
    (hRr : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU, r ^ 2 ≤ R k ω ∧ R k ω ≤ 1)
    (hWalk : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      (cell ε η (ω (T k ω).toNat) ∩ ball (0 : ℂ) ρc).Nonempty) :
    ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU, ∀ k' : ℤ,
      (cell ε η k' ∩ ball (vertexPoint ε η (ω (T k ω).toNat)) (R k ω / 4)).Nonempty →
        diam (cell ε η k') ≤ K.c0 * R k ω := by
  intro k ω hω
  exact diam_cell_le_of_mesh68 K hη hε hκ hεsm hρ' hmesh _ (hWalk k ω hω) hr10 (hRr k ω hω).1 (hRr k ω hω).2

/-- **The two local volume conclusions of `hone_exitQ_walk_of_env` from direct bounds.** The consumer
(HoneInputs.lean:149 and :155) uses `hVol` only at `δ = c₀R_k` with centre `v = vertexPoint (ω (T k ω))`, and at
`δ = R_k/4` with every centre `y ∈ B_{1−R_k/4}`. Taking these two bounds as binders at the random radii gives the real
inequality of `hvol` (HoneInputs.lean:140) and the `ENNReal` inequality of `hvol2` (HoneInputs.lean:152). -/
theorem hvol_of_direct68 {γ ρc : ℝ} (K : Constants68 γ ρc) (ε : ℝ) (η : ℝ → ℂ) {μ : Measure ℂ}
    [IsFiniteMeasureOnCompacts μ] {A : Set ℤ} {τU : (ℕ → ℤ) → ℕ∞} {T : ℕ → (ℕ → ℤ) → ℕ∞}
    {R : ℕ → (ℕ → ℤ) → ℝ}
    (hVolC : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ENNReal.ofReal ((K.c0 * R k ω) ^ K.βm) ≤ μ (ball (vertexPoint ε η (ω (T k ω).toNat)) (K.c0 * R k ω)))
    (hVolY : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ∀ y ∈ ball (0 : ℂ) (1 - R k ω / 4), ENNReal.ofReal ((R k ω / 4) ^ K.βm) ≤ μ (ball y (R k ω / 4))) :
    (∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      (K.c0 * R k ω) ^ K.βm ≤ (μ (ball (vertexPoint ε η (ω (T k ω).toNat)) (K.c0 * R k ω))).toReal) ∧
    (∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ∀ y ∈ ball (0 : ℂ) (1 - R k ω / 4), ENNReal.ofReal ((R k ω / 4) ^ K.βm) ≤ μ (ball y (R k ω / 4))) := by
  refine ⟨fun k ω hω => ?_, hVolY⟩
  exact (ENNReal.ofReal_le_iff_le_toReal (measure_ball_lt_top (μ := μ)).ne).mp (hVolC k ω hω)

end Lemma68Window

end MatedCRT

#print axioms MatedCRT.Lemma68Window.diam_cell_le_of_mesh68
#print axioms MatedCRT.Lemma68Window.hdiam_of_mesh68
#print axioms MatedCRT.Lemma68Window.hvol_of_direct68
