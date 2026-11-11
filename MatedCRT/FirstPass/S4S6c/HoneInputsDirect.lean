import MatedCRT.FirstPass.S4S6c.HoneInputs
import MatedCRT.Proofs.Infra.LocallyFinite

open HarmonicBalls (annulus)

/-!
# The hone of `exitQ_le_pow` at the walk-centred test end, with the direct inputs discharged from good events


`hone_exitQ_walk_of_env_direct` is `hone_exitQ_walk_of_env` (HoneInputs.lean:39) with the direct inputs
`hL29`, `hcell`, `hh` discharged, and `hfinE`, `hdiam` still binders. The new good-event hypotheses are
environment-level, at the fixed environment `(η, μ)` and scale `ε`, and are restrictions of the Draft good events:

* `hCountGood`: the lower half of Lemma 2.9 (`CountingMeasureConvergenceStmt`, Draft/Section2.lean:143) at `f ≡ 1`,
  for every `D ⊆ B_{ρc}` and every choice `w` of cell points;
* `hCellGood`: the upper half of Lemma 2.8 (`CellSizeEstimateStmt`, Draft/Section2.lean:131) at radius `ρc`, with
  exponent `2/(2+γ)² − ζc`; and `hεcell`, the smallness of that exponent against the scale range `rmin`.

The walk-centred test ball `B(v, c₀R)`, `v = η(a)`, `a = ω(T)`, is inside `B_{ρc}`: the vertex cell of `a` meets
`B_{ρc − ε^ω}` (`hWalk`), has diameter `≤ ε^θ ≤ R/100` (`hCellGood`), and `infDist(v, ∂B_{ρc}) ≥ R/8` (`hWalk`);
connectedness of `B(v, R/8)` then gives `B(v, R/8) ⊆ B_{ρc}` (`ball_subset_ball0_of_sphere_far`).
-/

namespace MatedCRT

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology

/-- A ball `B(v, r)` whose points are all at distance `≥ r` from a sphere `∂B_ρ` and which contains a point `p` of `B_ρ`
at distance `< r` from `v` lies in `B_ρ` (connectedness of the ball, Armitage-Gardiner style disconnection argument). -/
theorem ball_subset_ball0_of_sphere_far {v p : ℂ} {r ρ : ℝ}
    (hfar : ∀ x ∈ sphere (0 : ℂ) ρ, r ≤ dist v x) (hp : ‖p‖ < ρ) (hvp : dist v p < r) :
    ball v r ⊆ ball (0 : ℂ) ρ := by
  have hsub : ball v r ⊆ ball (0 : ℂ) ρ ∪ {x : ℂ | ρ < ‖x‖} := by
    intro x hx
    rcases lt_trichotomy ‖x‖ ρ with h | h | h
    · exact Or.inl (mem_ball_zero_iff.mpr h)
    · have hxs : x ∈ sphere (0 : ℂ) ρ := mem_sphere_zero_iff_norm.mpr h
      exact absurd (hfar x hxs) (not_le.mpr (by rw [dist_comm]; exact mem_ball.mp hx))
    · exact Or.inr h
  have hdisj : Disjoint (ball (0 : ℂ) ρ) {x : ℂ | ρ < ‖x‖} :=
    Set.disjoint_left.mpr fun x hx hx' =>
      absurd (mem_ball_zero_iff.mp hx) (not_lt.mpr (le_of_lt (show ρ < ‖x‖ from hx')))
  exact IsPreconnected.subset_left_of_subset_union isOpen_ball (isOpen_lt continuous_const continuous_norm)
    hdisj hsub ⟨p, mem_ball.mpr (by rw [dist_comm]; exact hvp), mem_ball_zero_iff.mpr hp⟩
    (convex_ball v r).isPreconnected

namespace Lemma68Window

open Lemma68WalkBridge (coordFiltration)

/-- A cell `H^ε_k = η([(k-1)ε, kε])` is compact, as the continuous image of a compact interval. -/
theorem cell_isCompact_direct {ε : ℝ} {η : ℝ → ℂ} (hη : Continuous η) (k : ℤ) : IsCompact (cell ε η k) := by
  unfold cell
  exact isCompact_Icc.image hη

/-- The vertex point `η(εk)` lies in its own cell (`ε > 0`). -/
theorem vertexPoint_mem_cell_direct {ε : ℝ} {η : ℝ → ℂ} (hε : 0 < ε) (k : ℤ) :
    vertexPoint ε η k ∈ cell ε η k := by
  unfold cell vertexPoint
  exact ⟨ε * k, ⟨by nlinarith, le_rfl⟩, rfl⟩

/-- The diameter of a cell bounds the distance of any two of its points. -/
theorem dist_le_diam_cell_direct {ε : ℝ} {η : ℝ → ℂ} (hη : Continuous η) (k : ℤ) {p q : ℂ}
    (hp : p ∈ cell ε η k) (hq : q ∈ cell ε η k) : dist p q ≤ diam (cell ε η k) :=
  dist_le_diam_of_mem (cell_isCompact_direct hη k).isBounded hp hq

/-- A choice of one cell point per vertex of `V^ε(D)`, in `H^ε_k ∩ cl(D)` (Lemma 2.9 requires this choice). -/
theorem exists_cellPoint_choice_direct {ε : ℝ} {η : ℝ → ℂ} (D : Set ℂ) :
    ∃ w : ℤ → ℂ, ∀ k ∈ cellVertices ε η D, w k ∈ cell ε η k ∩ closure D := by
  classical
  refine ⟨fun k => if h : (cell ε η k ∩ D).Nonempty then h.some else 0, fun k hk => ?_⟩
  have h' : (cell ε η k ∩ D).Nonempty := hk
  dsimp only
  simp only [h', ↓reduceDIte]
  exact ⟨h'.some_mem.1, subset_closure h'.some_mem.2⟩

/-- **The hone of `exitQ_le_pow` at the walk-centred test end, direct inputs discharged from good events.**
Same conclusion as `hone_exitQ_walk_of_env`. Removed binders: `hL29` (derived from `hCountGood`), `hcell` and `hh`
(derived from `hCellGood` and `hεcell`, with `H := ε^θ`). New good-event binders: `hCountGood`, `hCellGood`, `hεcell`,
with the exponent parameter `ζc`. Kept binders: `hfinE` and `hdiam` (the test balls `B(v, R/4)` leave the good-event
domain `B_{ρc}`), and all configuration, moment and sparsity binders of `hone_exitQ_walk_of_env`. -/
theorem hone_exitQ_walk_of_env_direct {γ ρc : ℝ} (K : Constants68 γ ρc) (ε : ℝ) (η : ℝ → ℂ) (hη : Continuous η)
    (hprop : Tendsto η (cocompact ℝ) (cocompact ℂ)) (hε : 0 < ε) (hεc : ε ≤ 16 * K.c0)
    {μ : Measure ℂ} [IsFiniteMeasureOnCompacts μ] (hμNull : ∀ v : ℂ, μ {v} = 0)
    (m : ℤ → ℤ → ℕ) (a : ℤ) (A : Set ℤ) (hA : MeasurableSet A) (n : ℕ) {τU : (ℕ → ℤ) → ℕ∞}
    {r q0 q α C_exit C_good Dbl C : ℝ} {N_cov : ℕ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hq0c : q0 ≤ (1 / 4 : ℝ) ^ 2 / (4 * C)) (hq : q = q0 / (1 + Real.log (1 / r)) ^ 2)
    (hC : 0 < C) (hCw : 32 * C_exit ^ 2 * ((1 + (N_cov : ℝ) * Real.log 4) * C_good) ^ 2 * Dbl ^ 2 ≤ C)
    (hCg : 0 ≤ C_good)
    {T : ℕ → (ℕ → ℤ) → ℕ∞} (hT : ∀ k, IsStoppingTime coordFiltration (T k))
    {R : ℕ → (ℕ → ℤ) → ℝ} (hR : ∀ k, Measurable[(hT k).measurableSpace] (R k))
    (hmom1 : ∀ k, Integrable ({w | T k w < ⊤}.indicator
      (fun w => ((ballExitSigma ε η (walkParam ε η (R k) (T k) w)
        (postTimePath (fun n w => w n) (T k) w) : ℕ) : ℝ))) (srwLaw m a))
    (hmom2 : ∀ k, Integrable ({w | T k w < ⊤}.indicator
      (fun w => ((ballExitSigma ε η (walkParam ε η (R k) (T k) w)
        (postTimePath (fun n w => w n) (T k) w) : ℕ) : ℝ) ^ 2)) (srwLaw m a))
    (hRr : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU, r ^ 2 ≤ R k ω ∧ R k ω ≤ 1)
    (hdiam : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU, ∀ k' : ℤ,
      (cell ε η k' ∩ ball (vertexPoint ε η (ω (T k ω).toNat)) (R k ω / 4)).Nonempty →
        diam (cell ε η k') ≤ K.c0 * R k ω)
    (hsp : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU, ∀ w : ℂ,
      ((A ∩ cellVertices ε η (ball w (K.c0 * R k ω))).ncard : ℝ)
        < K.s1 * (K.c0 * R k ω) ^ (2 * K.βm) / ε)
    -- scale range of the good event: every walk test radius satisfies `rmin ≤ c₀ R` (configuration input)
    (rmin : ℝ)
    (hRmin : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU, rmin ≤ K.c0 * R k ω)
    -- good event of the volume lower bound (lower half of `VolumeGrowthStmt`, all scales in `[rmin, 1/4]`)
    (hVol : ∀ δ : ℝ, rmin ≤ δ → δ ≤ 1 / 4 → ∀ z ∈ ball (0 : ℂ) (1 - δ),
      ENNReal.ofReal (δ ^ K.βm) ≤ μ (ball z δ))
    -- good event of the lower Green bound (second conjunct of `GreenKernelLowerBoundStmt`)
    (hGreen : ∀ a ∈ cellVertices ε η (ball 0 (ρc - ε ^ K.ω)), ∀ r : ℝ, ε ^ K.ω ≤ r →
      r ≤ infDist (vertexPoint ε η a) (sphere 0 ρc) →
      ∀ b ∈ cellVertices ε η (ball (vertexPoint ε η a) (r / 3)),
      K.C⁻¹ * Real.log (if vertexPoint ε η a = vertexPoint ε η b then ε⁻¹
            else min (r / ‖vertexPoint ε η a - vertexPoint ε η b‖) ε⁻¹) - 1
          ≤ greenKernel m (interiorCellVertices ε η (ball (vertexPoint ε η a) r)) a b)
    -- the walk state lies in the domain of the good Green bound, with margin `R/8` to `∂B_ρ` (configuration input)
    (hWalk : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ω (T k ω).toNat ∈ cellVertices ε η (ball 0 (ρc - ε ^ K.ω)) ∧ ε ^ K.ω ≤ R k ω / 8 ∧
        R k ω / 8 ≤ infDist (vertexPoint ε η (ω (T k ω).toNat)) (sphere 0 ρc))
    -- NEW good-event input: lower half of Lemma 2.9 (`CountingMeasureConvergenceStmt`) at `f ≡ 1`, for `D ⊆ B_{ρc}`
    (hCountGood : ∀ D : Set ℂ, D ⊆ ball (0 : ℂ) ρc → ∀ w : ℤ → ℂ,
      (∀ k ∈ cellVertices ε η D, w k ∈ cell ε η k ∩ closure D) →
      ε⁻¹ * ∫ _ in D, (1 : ℝ) ∂μ - ε ^ (-1 + α) ≤ ∑' _ : cellVertices ε η D, (1 : ℝ))
    -- NEW good-event input: upper half of Lemma 2.8 (`CellSizeEstimateStmt`) at radius `ρc`, exponent `2/(2+γ)² − ζc`
    (ζc : ℝ) (hζc0 : 0 < ζc) (hζc1 : ζc < 1)
    (hCellGood : ∀ k' : ℤ, (cell ε η k' ∩ ball (0 : ℂ) ρc).Nonempty →
      diam (cell ε η k') ≤ ε ^ (2 / (2 + γ) ^ 2 - ζc))
    -- NEW configuration input: the cell-size exponent is below the scale range `rmin` (ε small, as in Lemma 2.8's `ε → 0`)
    (hεcell : ε ^ (2 / (2 + γ) ^ 2 - ζc) ≤ rmin / 100)
    (hfinE : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      expectedExitTime m (interiorCellVertices ε η (ball (vertexPoint ε η (ω (T k ω).toNat)) (R k ω / 4)))
        (ω (T k ω).toNat) ≠ ⊤)
    (hsc : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      4 * ε ^ α ≤ (μ (ball (vertexPoint ε η (ω (T k ω).toNat)) (K.c0 * R k ω))).toReal)
    {Z : ℕ → (ℕ → ℤ) → ℂ}
    (hεα : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU, ε ^ α ≤ R k ω / 100)
    (hεmass : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ε ^ α ≤ (R k ω / 4) ^ K.βm)
    (hb : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ω (T k ω).toNat ∈ cellVertices ε η (sphere (Z k ω) (4 * R k ω / 3)))
    (hx1 : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ‖vertexPoint ε η (ω (T k ω).toNat)‖ < 1 - R k ω / 4)
    (hmomS : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ∀ D : Set ℂ, MeasurableSet D → D ⊆ ball 0 1 → ENNReal.ofReal (ε ^ α) ≤ μ D →
      ∀ a ∈ cellVertices ε η D, ∀ N : ℕ,
        exitTimeMoment m (interiorCellVertices ε η D) a N ≤
          ENNReal.ofReal (N.factorial * C_exit ^ N * ε ^ (-(N : ℝ))) *
            (⨆ z' ∈ D, ∫⁻ w in Metric.thickening (ε ^ α) D,
              ENNReal.ofReal (Real.log (1 / ‖z' - w‖) + 1) ∂μ) ^ N)
    (hgood : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      IsGoodAnnulusEvent μ K.c0 C_good (R k ω) (Z k ω))
    (hN : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ∀ (R' : ℝ) (z' : ℂ), 0 < R' → ∃ t : Finset ℂ, t.card ≤ N_cov ∧
        (∀ v ∈ t, v ∈ annulus z' R' (2 * R')) ∧ annulus z' R' (2 * R') ⊆ ⋃ v ∈ t, ball v R')
    (hpos : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      0 < ⨅ w ∈ annulus (Z k ω) (R k ω) (2 * R k ω), μ (ball w (K.c0 * R k ω)))
    (hdbl : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      (μ (ball (vertexPoint ε η (ω (T k ω).toNat)) (3 * K.c0 * R k ω))).toReal
        ≤ Dbl * (μ (ball (vertexPoint ε η (ω (T k ω).toNat)) (K.c0 * R k ω))).toReal) :
    ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a, x ∈ prefixSet (fun (j : ℕ) (y : ℕ → ℤ) => y j) A (T k) τU →
      (srwLaw m a)[(testFailSet (fun (j : ℕ) (y : ℕ → ℤ) => y j) A (T k)
        (testEndExit ε η (walkParam ε η (R k) (T k)) (T k))).indicator (fun _ => (1 : ℝ)) | (hT k).measurableSpace] x
        ≤ 1 - q := by
  classical
  -- the single exponent `θ = 2/(2+γ)² − ζc` of the cell-size good event
  -- (1) every vertex cell of the walk has diameter `≤ ε^θ`, from `hCellGood` (its cell meets `B_{ρc}` by `hWalk`)
  have hcellD : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ∀ p ∈ cell ε η (ω (T k ω).toNat), ∀ q ∈ cell ε η (ω (T k ω).toNat), dist p q ≤ ε ^ (2 / (2 + γ) ^ 2 - ζc) := by
    intro k ω hω p hp q hq
    obtain ⟨⟨x, hxc, hxb⟩, -, -⟩ := hWalk k ω hω
    have hxρ : x ∈ ball (0 : ℂ) ρc := by
      have h1 := mem_ball_zero_iff.mp hxb
      have h0 := Real.rpow_pos_of_pos hε K.ω
      exact mem_ball_zero_iff.mpr (by linarith)
    exact (dist_le_diam_cell_direct hη _ hp hq).trans (hCellGood _ ⟨x, hxc, hxρ⟩)
  -- (2) the diameter bound is below `R/100`, from `hεcell` and `rmin ≤ c₀R ≤ R`
  have hsmallAll : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ε ^ (2 / (2 + γ) ^ 2 - ζc) ≤ R k ω / 100 := by
    intro k ω hω
    have hRpos : 0 < R k ω := lt_of_lt_of_le (pow_pos hr 2) (hRr k ω hω).1
    have hrmin : rmin ≤ R k ω :=
      le_trans (hRmin k ω hω) (mul_le_of_le_one_left hRpos.le (by linarith [K.hc0']))
    linarith
  -- (3) the lower counting bound (`hL29`) at the walk test ball `B(v, c₀R)`, from `hCountGood`
  have hL29' : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ε⁻¹ * (μ (ball (vertexPoint ε η (ω (T k ω).toNat)) (K.c0 * R k ω))).toReal - ε ^ (-1 + α)
        ≤ ((cellVertices ε η (ball (vertexPoint ε η (ω (T k ω).toNat)) (K.c0 * R k ω))).ncard : ℝ) := by
    intro k ω hω
    obtain ⟨⟨p, hpc, hpb⟩, -, hW3⟩ := hWalk k ω hω
    have hRpos : 0 < R k ω := lt_of_lt_of_le (pow_pos hr 2) (hRr k ω hω).1
    have hpnorm : ‖p‖ < ρc := by
      have h1 := mem_ball_zero_iff.mp hpb
      have h0 := Real.rpow_pos_of_pos hε K.ω
      linarith
    have hvp : dist (vertexPoint ε η (ω (T k ω).toNat)) p < R k ω / 8 := by
      have h1 := hcellD k ω hω _ (vertexPoint_mem_cell_direct hε _) p hpc
      have h2 := hsmallAll k ω hω
      linarith
    have hfar : ∀ x ∈ sphere (0 : ℂ) ρc, R k ω / 8 ≤ dist (vertexPoint ε η (ω (T k ω).toNat)) x :=
      fun x hx => le_trans hW3 (infDist_le_dist_of_mem hx)
    have hD : ball (vertexPoint ε η (ω (T k ω).toNat)) (K.c0 * R k ω) ⊆ ball (0 : ℂ) ρc :=
      (ball_subset_ball (by nlinarith [K.hc0'])).trans
        (ball_subset_ball0_of_sphere_far hfar hpnorm hvp)
    obtain ⟨w, hw⟩ := exists_cellPoint_choice_direct (ε := ε) (η := η)
      (ball (vertexPoint ε η (ω (T k ω).toNat)) (K.c0 * R k ω))
    have hfinD : (cellVertices ε η (ball (vertexPoint ε η (ω (T k ω).toNat)) (K.c0 * R k ω))).Finite :=
      (cellVertices_finite_of_isCompact hη hprop hε (isCompact_closedBall (0 : ℂ) ρc)).subset
        (fun k' hk' => Set.Nonempty.mono (inter_subset_inter_right _ (hD.trans ball_subset_closedBall)) hk')
    have hc := hCountGood _ hD w hw
    have hint : ∫ _ in ball (vertexPoint ε η (ω (T k ω).toNat)) (K.c0 * R k ω), (1 : ℝ) ∂μ
        = (μ (ball (vertexPoint ε η (ω (T k ω).toNat)) (K.c0 * R k ω))).toReal := by
      rw [setIntegral_const, smul_eq_mul, mul_one]
      rfl
    have hsum : ∑' _ : cellVertices ε η (ball (vertexPoint ε η (ω (T k ω).toNat)) (K.c0 * R k ω)), (1 : ℝ)
        = ((cellVertices ε η (ball (vertexPoint ε η (ω (T k ω).toNat)) (K.c0 * R k ω))).ncard : ℝ) := by
      have := hfinD.fintype
      rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
        ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    rw [hint, hsum] at hc
    exact hc
  -- the direct inputs of `hone_exitQ_walk_of_env`: `hL29`, `hcell` and `hh` (with `H := ε^θ`) are discharged
  exact hone_exitQ_walk_of_env K ε η hη hprop hε hεc hμNull m a A hA n hr hr1 hq0c hq hC hCw hCg hT hR hmom1 hmom2
    hRr hdiam hsp rmin hRmin hVol hGreen hWalk hfinE hL29' hsc hεα hεmass hb (H := fun _ _ => ε ^ (2 / (2 + γ) ^ 2 - ζc))
    (fun k ω hω p hp q hq => hcellD k ω hω p hp q hq) (fun k ω hω => hsmallAll k ω hω) hx1 hmomS hgood hN hpos hdbl

end Lemma68Window

end MatedCRT

#print axioms MatedCRT.Lemma68Window.hone_exitQ_walk_of_env_direct
