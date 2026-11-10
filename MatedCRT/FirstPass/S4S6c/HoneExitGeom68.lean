import MatedCRT.FirstPass.S6n
import MatedCRT.Proofs.WalkPotential.Markov
import MatedCRT.Proofs.Infra.RandomWalk
import MatedCRT.FirstPass.S4S6c.ShellHoneInst68
import MatedCRT.FirstPass.S4S6c.ShellDbl68
import MatedCRT.FirstPass.S4S6c.ExitPath68
import MatedCRT.FirstPass.S4S6c.TraceInputs68
import MatedCRT.FirstPass.S4S6c.WindowMult68

/-!
# The exit geometry of the one-test hone (fp-S4S6c-hone-exit-geometry)

Binders of `shellOneTest_of_direct` (ShellHoneInst68.lean:53):

* `hb` (l.121): the cell of the exit vertex meets `∂B_{4R/3}(Z_k)`. Its deterministic core is
  `cell_meets_sphere_of_exit`: an interior vertex `k'` adjacent to the non-interior vertex `k` gives a point of
  `H_k ∩ ∂B` (`ExitPath68.exit_closure_meets_sphere`, ExitPath68.lean:27, in closure form), and the cell is closed
  (`cell_isCompact`, S6n.lean:289). The binder `hb` itself is not discharged here: it quantifies over every path in
  `prefixSet`, which carries no adjacency between consecutive vertices (see the report).
* `hdbl` (after l.139): `hdbl_of_exit_geom` discharges it from `hb`, `hWalk`, `hCellGood`, `hεcell`, `hRmin`, `hgood`
  and `hDbl : C_good ≤ Dbl`. The exit vertex `x = η(ε X_T)` lies in the cell `H_{X_T}`, which meets `∂B_{4R/3}(Z_k)`
  and has diameter at most `c₀R/100`; hence `x ∈ 𝔸_{R,2R}(Z_k)` and `B_{3c₀R}(x) ⊆ 𝔸_{R,2R}(Z_k)` (with `c₀ ≤ 1/24`),
  and the good-annulus event gives the doubling bound (`measure_three_le_of_good_annulus`, ShellDbl68.lean:30).
-/

open HarmonicBalls (annulus)
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology

namespace MatedCRT
namespace Lemma68HoneExitGeom

open MatedCRT.Lemma68WalkBridge (coordFiltration)
open MatedCRT.Lemma68ChainCore MatedCRT.Lemma68ShellChain MatedCRT.Lemma68Guard10 DyadicCutoff68
open MatedCRT.Lemma68Window MatedCRT.Lemma68Omega MatedCRT.Lemma68GeometryId MatedCRT.Lemma68Admissible
open MatedCRT.Lemma68ConstOrder
open MatedCRT.Lemma68ShellPath MatedCRT.Lemma68WalkBridge MatedCRT.Lemma68ChainAe
open MatedCRT.Lemma68OmegaStop MatedCRT.Lemma68ExitAe MatedCRT.Lemma68ShellIdent

/-- **The deterministic core of `hb`.** If the vertex `k'` is interior to `B_ρ(c)` (`interiorCellVertices`,
Defs/Map.lean), `m k' k ≠ 0` with the closures of adjacent cells meeting, and `k` is not interior, then the cell
`H_k` meets the sphere `∂B_ρ(c)`. This is the closure form `ExitPath68.exit_closure_meets_sphere` with the
closedness of the compact cell (`cell_isCompact`, S6n.lean:289). The step "the cell at the exit time meets its
boundary" is CHATGPT-229 l.674-690 (proof of Lemma 6.8, corrected [C26]). -/
theorem cell_meets_sphere_of_exit {ε : ℝ} {η : ℝ → ℂ} (hη : Continuous η)
    {m : ℤ → ℤ → ℕ} {c : ℂ} {ρ : ℝ} {k' k : ℤ}
    (hadj : ∀ u v, m u v ≠ 0 → (closure (cell ε η u) ∩ closure (cell ε η v)).Nonempty)
    (hk' : k' ∈ interiorCellVertices ε η (ball c ρ)) (hmk : m k' k ≠ 0)
    (hnot : k ∉ interiorCellVertices ε η (ball c ρ)) :
    (cell ε η k ∩ Metric.sphere c ρ).Nonempty := by
  have hconn : ∀ v, IsPreconnected (cell ε η v) := fun v =>
    isPreconnected_Icc.image _ hη.continuousOn
  obtain ⟨p, hp1, hp2⟩ := ExitPath68.exit_closure_meets_sphere hconn hadj hk' hmk hnot
  exact ⟨p, by rwa [(MatedCRT.Lemma68C12Geom.cell_isCompact hη k).isClosed.closure_eq] at hp1, hp2⟩

/-- **The doubling bound of the exit test ball, from the good annulus (`hdbl` of `shellOneTest_of_direct`).**
The binders `hb`, `hWalk`, `hCellGood`, `hεcell`, `hRmin`, `hRr`, `hgood` are those of `shellOneTest_of_direct`
(ShellHoneInst68.lean:53-140). The extra hypothesis `hDbl : C_good ≤ Dbl` is the minimal binder change: the doubling
constant must dominate the good-annulus constant (the caller takes `Dbl = shellDbl68 C_good`, ShellConstOrder68.lean:125). -/
theorem hdbl_of_exit_geom {γ ρc ζc : ℝ} (K : Constants68 γ ρc) {ε : ℝ} {η : ℝ → ℂ} (hη : Continuous η)
    (hε : 0 < ε) {μ : Measure ℂ} [IsFiniteMeasureOnCompacts μ]
    {A : Set ℤ} {τU : (ℕ → ℤ) → ℕ∞} {Kset : Set ℂ} {Rf : ℂ → ℝ} {r s d : ℝ} {Z : ℕ → (ℕ → ℤ) → ℂ}
    {C_good Dbl : ℝ} (hr : 0 < r) (hCg : 0 ≤ C_good) (hDbl : C_good ≤ Dbl)
    (hRr : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU,
      r ^ 2 ≤ Rf (shellCentre ε η Kset r s d k ω) ∧ Rf (shellCentre ε η Kset r s d k ω) ≤ 1)
    (rmin : ℝ)
    (hRmin : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU,
      rmin ≤ K.c0 * Rf (shellCentre ε η Kset r s d k ω))
    (hWalk : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU,
      ω (shellExit ε η Kset r s d Rf k ω).toNat ∈ cellVertices ε η (ball 0 (ρc - ε ^ K.ω)) ∧
        ε ^ K.ω ≤ Rf (shellCentre ε η Kset r s d k ω) / 8 ∧
        Rf (shellCentre ε η Kset r s d k ω) / 8 ≤
          infDist (vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat)) (sphere 0 ρc))
    (hCellGood : ∀ k' : ℤ, (cell ε η k' ∩ ball (0 : ℂ) (ρc + 3 / 8)).Nonempty →
      diam (cell ε η k') ≤ ε ^ (2 / (2 + γ) ^ 2 - ζc))
    (hεcell : ε ^ (2 / (2 + γ) ^ 2 - ζc) ≤ rmin / 100)
    (hgood : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU,
      IsGoodAnnulusEvent μ K.c0 C_good (Rf (shellCentre ε η Kset r s d k ω)) (Z k ω))
    (hb : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU,
      ω (shellExit ε η Kset r s d Rf k ω).toNat ∈
        cellVertices ε η (sphere (Z k ω) (4 * Rf (shellCentre ε η Kset r s d k ω) / 3))) :
    ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU,
      (μ (ball (vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat))
        (3 * K.c0 * Rf (shellCentre ε η Kset r s d k ω)))).toReal
        ≤ Dbl * (μ (ball (vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat))
          (K.c0 * Rf (shellCentre ε η Kset r s d k ω)))).toReal := by
  intro k ω hω
  have hR0 : 0 < Rf (shellCentre ε η Kset r s d k ω) :=
    lt_of_lt_of_le (pow_pos hr 2) (hRr k ω hω).1
  have hpow : 0 ≤ ε ^ K.ω := Real.rpow_nonneg hε.le _
  -- the exit cell meets the ball `B_{ρc+3/8}` (from `hWalk`), so its diameter is small (`hCellGood`, `hεcell`, `hRmin`)
  have hWv : (cell ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat) ∩
      ball (0 : ℂ) (ρc - ε ^ K.ω)).Nonempty := (hWalk k ω hω).1
  have hmeet : (cell ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat) ∩
      ball (0 : ℂ) (ρc + 3 / 8)).Nonempty := by
    obtain ⟨p, hp1, hp2⟩ := hWv
    exact ⟨p, hp1, ball_subset_ball (by linarith) hp2⟩
  have hdiam : diam (cell ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat)) ≤
      K.c0 * Rf (shellCentre ε η Kset r s d k ω) / 100 := by
    have h1 := hCellGood _ hmeet
    have h2 := hRmin k ω hω
    linarith
  -- the exit cell meets `∂B_{4R/3}(Z k ω)` (`hb`), and the exit vertex lies in that cell
  obtain ⟨p, hpc, hps⟩ : (cell ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat) ∩
      sphere (Z k ω) (4 * Rf (shellCentre ε η Kset r s d k ω) / 3)).Nonempty := hb k ω hω
  have hdist_p : dist p (Z k ω) = 4 * Rf (shellCentre ε η Kset r s d k ω) / 3 := mem_sphere.1 hps
  have hx : vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat) ∈
      cell ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat) :=
    MatedCRT.Lemma68C12Geom.vertexPoint_mem_cell hε.le _
  have hbdd : Bornology.IsBounded (cell ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat)) :=
    (MatedCRT.Lemma68C12Geom.cell_isCompact hη _).isBounded
  have hxp : dist (vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat)) p ≤
      K.c0 * Rf (shellCentre ε η Kset r s d k ω) / 100 :=
    (dist_le_diam_of_mem hbdd hx hpc).trans hdiam
  have habs : |dist (vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat)) (Z k ω) -
      4 * Rf (shellCentre ε η Kset r s d k ω) / 3| ≤
      K.c0 * Rf (shellCentre ε η Kset r s d k ω) / 100 := by
    have h := abs_dist_sub_le (vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat)) p (Z k ω)
    rw [hdist_p] at h
    exact h.trans hxp
  obtain ⟨hl, hu⟩ := abs_le.1 habs
  -- numerical margins: `c₀ R ≤ R/24`
  have ht : K.c0 * Rf (shellCentre ε η Kset r s d k ω) ≤ Rf (shellCentre ε η Kset r s d k ω) / 24 := by
    have := mul_le_mul_of_nonneg_right K.hc0' hR0.le
    linarith
  have ht0 : 0 ≤ K.c0 * Rf (shellCentre ε η Kset r s d k ω) := mul_nonneg K.hc0.le hR0.le
  -- the exit vertex lies in the annulus `𝔸_{R,2R}(Z k ω)`
  have hx_ann : vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat) ∈
      annulus (Z k ω) (Rf (shellCentre ε η Kset r s d k ω)) (2 * Rf (shellCentre ε η Kset r s d k ω)) := by
    show _ ∈ Metric.ball (Z k ω) (2 * Rf (shellCentre ε η Kset r s d k ω)) \
      Metric.closedBall (Z k ω) (Rf (shellCentre ε η Kset r s d k ω))
    refine ⟨?_, ?_⟩
    · rw [mem_ball]
      linarith
    · intro h
      rw [mem_closedBall] at h
      linarith
  -- the ball `B_{3c₀R}(x)` lies in the annulus
  have hsub : ball (vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat))
      (3 * K.c0 * Rf (shellCentre ε η Kset r s d k ω)) ⊆
      annulus (Z k ω) (Rf (shellCentre ε η Kset r s d k ω)) (2 * Rf (shellCentre ε η Kset r s d k ω)) := by
    intro w hw
    rw [mem_ball] at hw
    have h3 : 3 * K.c0 * Rf (shellCentre ε η Kset r s d k ω) =
        3 * (K.c0 * Rf (shellCentre ε η Kset r s d k ω)) := by ring
    have h1 := dist_triangle w (vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat)) (Z k ω)
    have h2 : dist (vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat)) (Z k ω) ≤
        dist w (vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat)) + dist w (Z k ω) := by
      have := dist_triangle (vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat)) w (Z k ω)
      rwa [dist_comm (vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat)) w] at this
    show w ∈ Metric.ball (Z k ω) (2 * Rf (shellCentre ε η Kset r s d k ω)) \
      Metric.closedBall (Z k ω) (Rf (shellCentre ε η Kset r s d k ω))
    refine ⟨?_, ?_⟩
    · rw [mem_ball]
      linarith
    · intro h
      rw [mem_closedBall] at h
      linarith
  -- the doubling bound from the good annulus, then passage to `toReal`
  have hm := MatedCRT.Lemma68ShellDbl.measure_three_le_of_good_annulus (μ := μ) K.hc0
    (by linarith [K.hc0']) hR0 (hgood k ω hω) hx_ann hsub
  have hm' : μ (ball (vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat))
      (3 * K.c0 * Rf (shellCentre ε η Kset r s d k ω))) ≤
      ENNReal.ofReal Dbl * μ (ball (vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat))
        (K.c0 * Rf (shellCentre ε η Kset r s d k ω))) :=
    hm.trans (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hDbl) zero_le)
  have hfin : μ (ball (vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat))
      (K.c0 * Rf (shellCentre ε η Kset r s d k ω))) ≠ ⊤ :=
    (measure_ball_lt_top).ne
  calc (μ (ball (vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat))
          (3 * K.c0 * Rf (shellCentre ε η Kset r s d k ω)))).toReal
      ≤ (ENNReal.ofReal Dbl * μ (ball (vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat))
          (K.c0 * Rf (shellCentre ε η Kset r s d k ω)))).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) hm'
    _ = Dbl * (μ (ball (vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat))
          (K.c0 * Rf (shellCentre ε η Kset r s d k ω)))).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hCg.trans hDbl)]

/-! ## Step adjacency of the simple random walk, almost surely (operator item 2)

`srwStep m v` (Defs/RandomWalk.lean:47) is the normalized edge measure `∑_b m(v,b) δ_b` when `v` has positive finite
degree; otherwise it is the Dirac mass at `v` (a junk branch). So the adjacency claim needs the degree hypothesis
`hdeg`: every vertex has `edgeMeasure m v univ ≠ 0` and `≠ ⊤`. -/

/-- The edge measure of the set of non-neighbours of `a` is zero: `∑_c m(a,c) δ_c` charges only `{c | m a c ≠ 0}`. -/
theorem edgeMeasure_zero_set (m : ℤ → ℤ → ℕ) (a : ℤ) :
    edgeMeasure m a {c | m a c = 0} = 0 := by
  unfold edgeMeasure
  rw [Measure.sum_apply _ MeasurableSet.of_discrete]
  refine ENNReal.tsum_eq_zero.2 fun c => ?_
  by_cases h : m a c = 0
  · simp [h]
  · have hc : c ∉ {c : ℤ | m a c = 0} := h
    simp [Measure.smul_apply, Measure.dirac_apply', hc]

/-- Under `hdeg`, the one-step law of the walk from `a` gives no mass to the non-neighbours of `a`. -/
theorem srwStep_zero_set_null (m : ℤ → ℤ → ℕ) {a : ℤ}
    (hdeg : edgeMeasure m a univ ≠ 0 ∧ edgeMeasure m a univ ≠ ⊤) :
    srwStep m a {c | m a c = 0} = 0 := by
  unfold srwStep
  split_ifs
  rw [ProbabilityTheory.cond_apply MeasurableSet.univ, Set.univ_inter, edgeMeasure_zero_set, mul_zero]

/-- The event that the walk's `j`-th step is not along an edge is measurable. -/
theorem measurableSet_stepZero (m : ℤ → ℤ → ℕ) (j : ℕ) :
    MeasurableSet {y : ℕ → ℤ | m (y j) (y (j + 1)) = 0} := by
  have hpair : Measurable fun y : ℕ → ℤ => (y j, y (j + 1)) :=
    (measurable_pi_apply j).prodMk (measurable_pi_apply (j + 1))
  have hm : Measurable fun p : ℤ × ℤ => m p.1 p.2 := Measurable.of_discrete
  exact (hm.comp hpair) (measurableSet_singleton 0)

/-- The `j`-th step of simple random walk never leaves the edges: `srwLaw m a {m (y j) (y (j+1)) = 0} = 0`,
by induction on `j` with the first-step decomposition `srwLaw_apply_eq_lintegral`. -/
theorem srwLaw_stepZero_null (m : ℤ → ℤ → ℕ)
    (hdeg : ∀ v, edgeMeasure m v univ ≠ 0 ∧ edgeMeasure m v univ ≠ ⊤) (j : ℕ) :
    ∀ a : ℤ, srwLaw m a {y | m (y j) (y (j + 1)) = 0} = 0 := by
  induction j with
  | zero =>
    intro a
    rw [srwLaw_apply_eq_lintegral m a (measurableSet_stepZero m 0)]
    have hpre : pathCons a ⁻¹' {y : ℕ → ℤ | m (y 0) (y (0 + 1)) = 0} = {y | m a (y 0) = 0} := by
      ext y
      simp [pathCons]
    rw [hpre]
    have hae : ∀ᵐ b ∂srwStep m a, b ∉ {c : ℤ | m a c = 0} :=
      ae_iff.2 (by simpa using srwStep_zero_set_null m (hdeg a))
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [hae] with b hb
    have hae2 : ∀ᵐ y ∂srwLaw m b, y ∉ {y : ℕ → ℤ | m a (y 0) = 0} := by
      filter_upwards [srwLaw_ae_start m b] with y hy
      intro hmem
      exact hb (show m a b = 0 by rw [← hy]; exact hmem)
    simpa using ae_iff.1 hae2
  | succ j ih =>
    intro a
    rw [srwLaw_apply_eq_lintegral m a (measurableSet_stepZero m (j + 1))]
    have hpre : pathCons a ⁻¹' {y : ℕ → ℤ | m (y (j + 1)) (y (j + 1 + 1)) = 0} =
        {y | m (y j) (y (j + 1)) = 0} := by
      ext y
      simp [pathCons]
    rw [hpre]
    simp [ih]

/-- **Step adjacency of simple random walk, almost surely.** Under the degree hypothesis `hdeg`, almost every path
of `srwLaw m a` moves along an edge at every step: `m (w j) (w (j+1)) ≠ 0` for all `j`. -/
theorem srwLaw_step_ae_adjacent (m : ℤ → ℤ → ℕ)
    (hdeg : ∀ v, edgeMeasure m v univ ≠ 0 ∧ edgeMeasure m v univ ≠ ⊤) (a : ℤ) :
    ∀ᵐ w ∂srwLaw m a, ∀ j : ℕ, m (w j) (w (j + 1)) ≠ 0 := by
  rw [ae_all_iff]
  intro j
  rw [ae_iff]
  simpa using srwLaw_stepZero_null m hdeg j a

/-! ## `hb` in the almost-sure form (operator item 3)

The deterministic core is `cell_meets_sphere_of_exit`. Along a path with step adjacency, the exit time `T = t` is
finite (`prefixSet` gives `T < τU`). Either the exit is at the hit time (excluded by the named hypothesis `hhit`, the
hit-cell interiority, operator request 64e), or `hit ≤ t - 1`; then `x (t-1)` is interior, `x t` is not, and the
exit cell meets the sphere. The centre is the grid centre `shellCentre`; `hZ` identifies it with `Z`. -/

/-- **`hb` almost surely.** The exit-cell-meets-sphere claim of `hb` (ShellHoneInst68.lean:121), for almost every
walk from `a`, from step adjacency (`srwLaw_step_ae_adjacent`), the closed-cell adjacency `hadj` of the multiplicity
`m`, the identification `hZ : Z = shellCentre` and the hit-cell interiority `hhit` (named hypotheses). -/
theorem hb_ae_of_walk {ε : ℝ} {η : ℝ → ℂ} (hη : Continuous η) (Kset : Set ℂ) {Rf : ℂ → ℝ} {r s d : ℝ}
    {A : Set ℤ} {τU : (ℕ → ℤ) → ℕ∞} {Z : ℕ → (ℕ → ℤ) → ℂ}
    (m : ℤ → ℤ → ℕ) (a : ℤ) (n : ℕ)
    (hdeg : ∀ v, edgeMeasure m v univ ≠ 0 ∧ edgeMeasure m v univ ≠ ⊤)
    (hadj : ∀ u v, m u v ≠ 0 → (closure (cell ε η u) ∩ closure (cell ε η v)).Nonempty)
    (hZ : ∀ k x, Z k x = shellCentre ε η Kset r s d k x)
    (hhit : ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a,
      x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU →
      ∀ t : ℕ, shellHit ε η Kset r s k x = (t : ℕ∞) →
        x t ∈ interiorCellVertices ε η
          (ball (shellCentre ε η Kset r s d k x) (4 * Rf (shellCentre ε η Kset r s d k x) / 3))) :
    ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a,
      x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU →
        x (shellExit ε η Kset r s d Rf k x).toNat ∈
          cellVertices ε η (sphere (Z k x) (4 * Rf (shellCentre ε η Kset r s d k x) / 3)) := by
  intro k hk
  filter_upwards [srwLaw_step_ae_adjacent m hdeg a, hhit k hk] with x hxadj hxhit hpre
  have hT : shellExit ε η Kset r s d Rf k x ≠ ⊤ := ne_top_of_lt hpre.1
  obtain ⟨t, ht⟩ := ENat.ne_top_iff_exists.1 hT
  set P : ℕ → Prop := fun q => shellHit ε η Kset r s k x ≤ (q : ℕ∞) ∧
    x q ∉ interiorCellVertices ε η
      (ball (shellCentre ε η Kset r s d k x) (4 * Rf (shellCentre ε η Kset r s d k x) / 3)) with hPdef
  have hTP : shellExit ε η Kset r s d Rf k x = firstTime P := rfl
  have hPt : P t := by
    have h := MatedCRT.Lemma68ShellPath.firstTime_toNat_spec (P := P) (by rw [← hTP]; exact hT)
    have htoNat : (firstTime P).toNat = t := by
      rw [← hTP, ← ht]
      simp
    rwa [htoNat] at h
  have hmin : ∀ q < t, ¬ P q := by
    intro q hq hPq
    have h1 : firstTime P ≤ (q : ℕ∞) := (MatedCRT.Lemma68Omega.firstTime_le_iff P q).2 ⟨q, le_rfl, hPq⟩
    rw [← hTP, ← ht] at h1
    exact absurd (by exact_mod_cast h1) (not_le.2 hq)
  have hxt : x (shellExit ε η Kset r s d Rf k x).toNat = x t := by
    rw [← ht]
    simp
  rw [hxt, hZ]
  by_cases hitT : shellHit ε η Kset r s k x = (t : ℕ∞)
  · exact absurd (hxhit hpre t hitT) hPt.2
  · have hle : shellHit ε η Kset r s k x ≤ (t : ℕ∞) := hPt.1
    have hlt : shellHit ε η Kset r s k x < (t : ℕ∞) := lt_of_le_of_ne hle hitT
    cases t with
    | zero => exact absurd hlt (by simp)
    | succ q =>
      have hlt' : shellHit ε η Kset r s k x < (q : ℕ∞) + 1 := by exact_mod_cast hlt
      have hq : shellHit ε η Kset r s k x ≤ (q : ℕ∞) := (ENat.lt_add_one_iff (ENat.natCast_ne_top q)).1 hlt'
      have hinQ : x q ∈ interiorCellVertices ε η
          (ball (shellCentre ε η Kset r s d k x) (4 * Rf (shellCentre ε η Kset r s d k x) / 3)) := by
        by_contra hc
        exact hmin q (Nat.lt_succ_self q) ⟨hq, hc⟩
      obtain ⟨p, hp1, hp2⟩ := cell_meets_sphere_of_exit hη hadj hinQ (hxadj q) hPt.2
      exact ⟨p, hp1, hp2⟩

/-! ## `hdbl` with the constant `shellDbl68 C_good` (operator item 1, chat 237 section 4)

The conclusion is the chat 237 form `≤ shellDbl68 C_good * (μ B_{c₀R}(x)).toReal`. It carries no extra hypothesis on
`Dbl`: the binder `hdbl` of `shellOneTest_of_direct` with a free `Dbl` is NOT this statement. It is the binder with
`Dbl := shellDbl68 C_good`. -/

/-- **The doubling bound with the constant `shellDbl68 C_good`.** The geometry of `hdbl_of_exit_geom` (same binders,
same proof of the inclusions) and `measure_three_le_shellDbl68` (ShellDbl68.lean:70). -/
theorem hdbl_of_exit_geom_237 {γ ρc ζc : ℝ} (K : Constants68 γ ρc) {ε : ℝ} {η : ℝ → ℂ} (hη : Continuous η)
    (hε : 0 < ε) {μ : Measure ℂ} [IsFiniteMeasureOnCompacts μ]
    {A : Set ℤ} {τU : (ℕ → ℤ) → ℕ∞} {Kset : Set ℂ} {Rf : ℂ → ℝ} {r s d : ℝ} {Z : ℕ → (ℕ → ℤ) → ℂ}
    {C_good : ℝ} (hr : 0 < r)
    (hRr : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU,
      r ^ 2 ≤ Rf (shellCentre ε η Kset r s d k ω) ∧ Rf (shellCentre ε η Kset r s d k ω) ≤ 1)
    (rmin : ℝ)
    (hRmin : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU,
      rmin ≤ K.c0 * Rf (shellCentre ε η Kset r s d k ω))
    (hWalk : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU,
      ω (shellExit ε η Kset r s d Rf k ω).toNat ∈ cellVertices ε η (ball 0 (ρc - ε ^ K.ω)) ∧
        ε ^ K.ω ≤ Rf (shellCentre ε η Kset r s d k ω) / 8 ∧
        Rf (shellCentre ε η Kset r s d k ω) / 8 ≤
          infDist (vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat)) (sphere 0 ρc))
    (hCellGood : ∀ k' : ℤ, (cell ε η k' ∩ ball (0 : ℂ) (ρc + 3 / 8)).Nonempty →
      diam (cell ε η k') ≤ ε ^ (2 / (2 + γ) ^ 2 - ζc))
    (hεcell : ε ^ (2 / (2 + γ) ^ 2 - ζc) ≤ rmin / 100)
    (hgood : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU,
      IsGoodAnnulusEvent μ K.c0 C_good (Rf (shellCentre ε η Kset r s d k ω)) (Z k ω))
    (hb : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU,
      ω (shellExit ε η Kset r s d Rf k ω).toNat ∈
        cellVertices ε η (sphere (Z k ω) (4 * Rf (shellCentre ε η Kset r s d k ω) / 3))) :
    ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (shellExit ε η Kset r s d Rf k) τU,
      (μ (ball (vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat))
        (3 * K.c0 * Rf (shellCentre ε η Kset r s d k ω)))).toReal
        ≤ MatedCRT.Lemma68ConstOrder.shellDbl68 C_good *
          (μ (ball (vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat))
            (K.c0 * Rf (shellCentre ε η Kset r s d k ω)))).toReal := by
  intro k ω hω
  have hR0 : 0 < Rf (shellCentre ε η Kset r s d k ω) :=
    lt_of_lt_of_le (pow_pos hr 2) (hRr k ω hω).1
  have hpow : 0 ≤ ε ^ K.ω := Real.rpow_nonneg hε.le _
  have hWv : (cell ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat) ∩
      ball (0 : ℂ) (ρc - ε ^ K.ω)).Nonempty := (hWalk k ω hω).1
  have hmeet : (cell ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat) ∩
      ball (0 : ℂ) (ρc + 3 / 8)).Nonempty := by
    obtain ⟨p, hp1, hp2⟩ := hWv
    exact ⟨p, hp1, ball_subset_ball (by linarith) hp2⟩
  have hdiam : diam (cell ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat)) ≤
      K.c0 * Rf (shellCentre ε η Kset r s d k ω) / 100 := by
    have h1 := hCellGood _ hmeet
    have h2 := hRmin k ω hω
    linarith
  obtain ⟨p, hpc, hps⟩ : (cell ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat) ∩
      sphere (Z k ω) (4 * Rf (shellCentre ε η Kset r s d k ω) / 3)).Nonempty := hb k ω hω
  have hdist_p : dist p (Z k ω) = 4 * Rf (shellCentre ε η Kset r s d k ω) / 3 := mem_sphere.1 hps
  have hx : vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat) ∈
      cell ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat) :=
    MatedCRT.Lemma68C12Geom.vertexPoint_mem_cell hε.le _
  have hbdd : Bornology.IsBounded (cell ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat)) :=
    (MatedCRT.Lemma68C12Geom.cell_isCompact hη _).isBounded
  have hxp : dist (vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat)) p ≤
      K.c0 * Rf (shellCentre ε η Kset r s d k ω) / 100 :=
    (dist_le_diam_of_mem hbdd hx hpc).trans hdiam
  have habs : |dist (vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat)) (Z k ω) -
      4 * Rf (shellCentre ε η Kset r s d k ω) / 3| ≤
      K.c0 * Rf (shellCentre ε η Kset r s d k ω) / 100 := by
    have h := abs_dist_sub_le (vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat)) p (Z k ω)
    rw [hdist_p] at h
    exact h.trans hxp
  obtain ⟨hl, hu⟩ := abs_le.1 habs
  have ht : K.c0 * Rf (shellCentre ε η Kset r s d k ω) ≤ Rf (shellCentre ε η Kset r s d k ω) / 24 := by
    have := mul_le_mul_of_nonneg_right K.hc0' hR0.le
    linarith
  have ht0 : 0 ≤ K.c0 * Rf (shellCentre ε η Kset r s d k ω) := mul_nonneg K.hc0.le hR0.le
  have hx_ann : vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat) ∈
      annulus (Z k ω) (Rf (shellCentre ε η Kset r s d k ω)) (2 * Rf (shellCentre ε η Kset r s d k ω)) := by
    show _ ∈ Metric.ball (Z k ω) (2 * Rf (shellCentre ε η Kset r s d k ω)) \
      Metric.closedBall (Z k ω) (Rf (shellCentre ε η Kset r s d k ω))
    refine ⟨?_, ?_⟩
    · rw [mem_ball]
      linarith
    · intro h
      rw [mem_closedBall] at h
      linarith
  have hsub : ball (vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat))
      (3 * K.c0 * Rf (shellCentre ε η Kset r s d k ω)) ⊆
      annulus (Z k ω) (Rf (shellCentre ε η Kset r s d k ω)) (2 * Rf (shellCentre ε η Kset r s d k ω)) := by
    intro w hw
    rw [mem_ball] at hw
    have h3 : 3 * K.c0 * Rf (shellCentre ε η Kset r s d k ω) =
        3 * (K.c0 * Rf (shellCentre ε η Kset r s d k ω)) := by ring
    have h1 := dist_triangle w (vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat)) (Z k ω)
    have h2 : dist (vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat)) (Z k ω) ≤
        dist w (vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat)) + dist w (Z k ω) := by
      have := dist_triangle (vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat)) w (Z k ω)
      rwa [dist_comm (vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat)) w] at this
    show w ∈ Metric.ball (Z k ω) (2 * Rf (shellCentre ε η Kset r s d k ω)) \
      Metric.closedBall (Z k ω) (Rf (shellCentre ε η Kset r s d k ω))
    refine ⟨?_, ?_⟩
    · rw [mem_ball]
      linarith
    · intro h
      rw [mem_closedBall] at h
      linarith
  have hD0 : 0 ≤ MatedCRT.Lemma68ConstOrder.shellDbl68 C_good := by
    unfold MatedCRT.Lemma68ConstOrder.shellDbl68
    exact le_trans zero_le_one (le_max_left _ _)
  have hm := MatedCRT.Lemma68ShellDbl.measure_three_le_shellDbl68 K.hc0
    (by linarith [K.hc0']) hR0 (hgood k ω hω) hx_ann hsub
  have hfin : μ (ball (vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat))
      (K.c0 * Rf (shellCentre ε η Kset r s d k ω))) ≠ ⊤ :=
    (measure_ball_lt_top).ne
  calc (μ (ball (vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat))
          (3 * K.c0 * Rf (shellCentre ε η Kset r s d k ω)))).toReal
      ≤ (ENNReal.ofReal (MatedCRT.Lemma68ConstOrder.shellDbl68 C_good) *
          μ (ball (vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat))
            (K.c0 * Rf (shellCentre ε η Kset r s d k ω)))).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) hm
    _ = MatedCRT.Lemma68ConstOrder.shellDbl68 C_good *
          (μ (ball (vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat))
            (K.c0 * Rf (shellCentre ε η Kset r s d k ω)))).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hD0]

/-- **The one-test doubling bound at one walk and one shell (fp-S4S6c-B1-assembly-ae).** The pointwise form of
`hdbl_of_exit_geom_237` at the shell `k` and the walk `ω`, with the cell-control radius `ρ'` (`ρc ≤ ρ'`) in place of
`ρc + 3/8`: the exit cell meets `B_{ρc - ε^ω}` (`hWalk`), hence `B_{ρ'}`. The hypotheses are the instances at `(k, ω)`
of those of `hdbl_of_exit_geom_237`, so that they can be taken almost surely in the walk (`ae_all_iff`). -/
theorem hdbl_of_exit_geom_path {γ ρc ζc : ℝ} (K : Constants68 γ ρc) {ε : ℝ} {η : ℝ → ℂ} (hη : Continuous η)
    (hε : 0 < ε) {μ : Measure ℂ} [IsFiniteMeasureOnCompacts μ]
    {Kset : Set ℂ} {Rf : ℂ → ℝ} {r s d : ℝ} {Z : ℕ → (ℕ → ℤ) → ℂ}
    {C_good : ℝ} (hr : 0 < r) (k : ℕ) (ω : ℕ → ℤ) (ρ' : ℝ) (hρ' : ρc ≤ ρ')
    (hRr_x : r ^ 2 ≤ Rf (shellCentre ε η Kset r s d k ω) ∧ Rf (shellCentre ε η Kset r s d k ω) ≤ 1)
    (rmin : ℝ)
    (hRmin_x : rmin ≤ K.c0 * Rf (shellCentre ε η Kset r s d k ω))
    (hWalk_x : ω (shellExit ε η Kset r s d Rf k ω).toNat ∈ cellVertices ε η (ball 0 (ρc - ε ^ K.ω)) ∧
      ε ^ K.ω ≤ Rf (shellCentre ε η Kset r s d k ω) / 8 ∧
      Rf (shellCentre ε η Kset r s d k ω) / 8 ≤
        infDist (vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat)) (sphere 0 ρc))
    (hCellGood : ∀ k' : ℤ, (cell ε η k' ∩ ball (0 : ℂ) ρ').Nonempty →
      diam (cell ε η k') ≤ ε ^ (2 / (2 + γ) ^ 2 - ζc))
    (hεcell : ε ^ (2 / (2 + γ) ^ 2 - ζc) ≤ rmin / 100)
    (hgood_x : IsGoodAnnulusEvent μ K.c0 C_good (Rf (shellCentre ε η Kset r s d k ω)) (Z k ω))
    (hb_x : ω (shellExit ε η Kset r s d Rf k ω).toNat ∈
      cellVertices ε η (sphere (Z k ω) (4 * Rf (shellCentre ε η Kset r s d k ω) / 3))) :
    (μ (ball (vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat))
        (3 * K.c0 * Rf (shellCentre ε η Kset r s d k ω)))).toReal
      ≤ MatedCRT.Lemma68ConstOrder.shellDbl68 C_good *
        (μ (ball (vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat))
          (K.c0 * Rf (shellCentre ε η Kset r s d k ω)))).toReal := by
  have hR0 : 0 < Rf (shellCentre ε η Kset r s d k ω) :=
    lt_of_lt_of_le (pow_pos hr 2) hRr_x.1
  have hpow : 0 ≤ ε ^ K.ω := Real.rpow_nonneg hε.le _
  have hWv : (cell ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat) ∩
      ball (0 : ℂ) (ρc - ε ^ K.ω)).Nonempty := hWalk_x.1
  have hmeet : (cell ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat) ∩
      ball (0 : ℂ) ρ').Nonempty := by
    obtain ⟨p, hp1, hp2⟩ := hWv
    exact ⟨p, hp1, ball_subset_ball (by linarith) hp2⟩
  have hdiam : diam (cell ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat)) ≤
      K.c0 * Rf (shellCentre ε η Kset r s d k ω) / 100 := by
    have h1 := hCellGood _ hmeet
    have h2 := hRmin_x
    linarith
  obtain ⟨p, hpc, hps⟩ : (cell ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat) ∩
      sphere (Z k ω) (4 * Rf (shellCentre ε η Kset r s d k ω) / 3)).Nonempty := hb_x
  have hdist_p : dist p (Z k ω) = 4 * Rf (shellCentre ε η Kset r s d k ω) / 3 := mem_sphere.1 hps
  have hx : vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat) ∈
      cell ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat) :=
    MatedCRT.Lemma68C12Geom.vertexPoint_mem_cell hε.le _
  have hbdd : Bornology.IsBounded (cell ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat)) :=
    (MatedCRT.Lemma68C12Geom.cell_isCompact hη _).isBounded
  have hxp : dist (vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat)) p ≤
      K.c0 * Rf (shellCentre ε η Kset r s d k ω) / 100 :=
    (dist_le_diam_of_mem hbdd hx hpc).trans hdiam
  have habs : |dist (vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat)) (Z k ω) -
      4 * Rf (shellCentre ε η Kset r s d k ω) / 3| ≤
      K.c0 * Rf (shellCentre ε η Kset r s d k ω) / 100 := by
    have h := abs_dist_sub_le (vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat)) p (Z k ω)
    rw [hdist_p] at h
    exact h.trans hxp
  obtain ⟨hl, hu⟩ := abs_le.1 habs
  have ht : K.c0 * Rf (shellCentre ε η Kset r s d k ω) ≤ Rf (shellCentre ε η Kset r s d k ω) / 24 := by
    have := mul_le_mul_of_nonneg_right K.hc0' hR0.le
    linarith
  have ht0 : 0 ≤ K.c0 * Rf (shellCentre ε η Kset r s d k ω) := mul_nonneg K.hc0.le hR0.le
  have hx_ann : vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat) ∈
      annulus (Z k ω) (Rf (shellCentre ε η Kset r s d k ω)) (2 * Rf (shellCentre ε η Kset r s d k ω)) := by
    show _ ∈ Metric.ball (Z k ω) (2 * Rf (shellCentre ε η Kset r s d k ω)) \
      Metric.closedBall (Z k ω) (Rf (shellCentre ε η Kset r s d k ω))
    refine ⟨?_, ?_⟩
    · rw [mem_ball]
      linarith
    · intro h
      rw [mem_closedBall] at h
      linarith
  have hsub : ball (vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat))
      (3 * K.c0 * Rf (shellCentre ε η Kset r s d k ω)) ⊆
      annulus (Z k ω) (Rf (shellCentre ε η Kset r s d k ω)) (2 * Rf (shellCentre ε η Kset r s d k ω)) := by
    intro w hw
    rw [mem_ball] at hw
    have h3 : 3 * K.c0 * Rf (shellCentre ε η Kset r s d k ω) =
        3 * (K.c0 * Rf (shellCentre ε η Kset r s d k ω)) := by ring
    have h1 := dist_triangle w (vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat)) (Z k ω)
    have h2 : dist (vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat)) (Z k ω) ≤
        dist w (vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat)) + dist w (Z k ω) := by
      have := dist_triangle (vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat)) w (Z k ω)
      rwa [dist_comm (vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat)) w] at this
    show w ∈ Metric.ball (Z k ω) (2 * Rf (shellCentre ε η Kset r s d k ω)) \
      Metric.closedBall (Z k ω) (Rf (shellCentre ε η Kset r s d k ω))
    refine ⟨?_, ?_⟩
    · rw [mem_ball]
      linarith
    · intro h
      rw [mem_closedBall] at h
      linarith
  have hD0 : 0 ≤ MatedCRT.Lemma68ConstOrder.shellDbl68 C_good := by
    unfold MatedCRT.Lemma68ConstOrder.shellDbl68
    exact le_trans zero_le_one (le_max_left _ _)
  have hm := MatedCRT.Lemma68ShellDbl.measure_three_le_shellDbl68 K.hc0
    (by linarith [K.hc0']) hR0 (hgood_x) hx_ann hsub
  have hfin : μ (ball (vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat))
      (K.c0 * Rf (shellCentre ε η Kset r s d k ω))) ≠ ⊤ :=
    (measure_ball_lt_top).ne
  calc (μ (ball (vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat))
          (3 * K.c0 * Rf (shellCentre ε η Kset r s d k ω)))).toReal
      ≤ (ENNReal.ofReal (MatedCRT.Lemma68ConstOrder.shellDbl68 C_good) *
          μ (ball (vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat))
            (K.c0 * Rf (shellCentre ε η Kset r s d k ω)))).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) hm
    _ = MatedCRT.Lemma68ConstOrder.shellDbl68 C_good *
          (μ (ball (vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat))
            (K.c0 * Rf (shellCentre ε η Kset r s d k ω)))).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hD0]

#print axioms MatedCRT.Lemma68HoneExitGeom.hdbl_of_exit_geom_path
/-- **The one-test doubling bound, split exponent (q4, fp-S4S6c-goodenv-local).** The copy of `hdbl_of_exit_geom_path` with the walk second conjunct `ε ^ κ ≤ R/8`, κ = `2 / (2 + γ) ^ 2 - ζc` (exponent split, chat 239 l.747-800); the proof does not use that conjunct. The pointwise form of
`hdbl_of_exit_geom_237` at the shell `k` and the walk `ω`, with the cell-control radius `ρ'` (`ρc ≤ ρ'`) in place of
`ρc + 3/8`: the exit cell meets `B_{ρc - ε^ω}` (`hWalk`), hence `B_{ρ'}`. The hypotheses are the instances at `(k, ω)`
of those of `hdbl_of_exit_geom_237`, so that they can be taken almost surely in the walk (`ae_all_iff`). -/
theorem hdbl_of_exit_geom_path_split {γ ρc ζc : ℝ} (K : Constants68 γ ρc) {ε : ℝ} {η : ℝ → ℂ} (hη : Continuous η)
    (hε : 0 < ε) {μ : Measure ℂ} [IsFiniteMeasureOnCompacts μ]
    {Kset : Set ℂ} {Rf : ℂ → ℝ} {r s d : ℝ} {Z : ℕ → (ℕ → ℤ) → ℂ}
    {C_good : ℝ} (hr : 0 < r) (k : ℕ) (ω : ℕ → ℤ) (ρ' : ℝ) (hρ' : ρc ≤ ρ')
    (hRr_x : r ^ 2 ≤ Rf (shellCentre ε η Kset r s d k ω) ∧ Rf (shellCentre ε η Kset r s d k ω) ≤ 1)
    (rmin : ℝ)
    (hRmin_x : rmin ≤ K.c0 * Rf (shellCentre ε η Kset r s d k ω))
    (hWalk_x : ω (shellExit ε η Kset r s d Rf k ω).toNat ∈ cellVertices ε η (ball 0 (ρc - ε ^ K.ω)) ∧
      ε ^ (2 / (2 + γ) ^ 2 - ζc) ≤ Rf (shellCentre ε η Kset r s d k ω) / 8 ∧
      Rf (shellCentre ε η Kset r s d k ω) / 8 ≤
        infDist (vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat)) (sphere 0 ρc))
    (hCellGood : ∀ k' : ℤ, (cell ε η k' ∩ ball (0 : ℂ) ρ').Nonempty →
      diam (cell ε η k') ≤ ε ^ (2 / (2 + γ) ^ 2 - ζc))
    (hεcell : ε ^ (2 / (2 + γ) ^ 2 - ζc) ≤ rmin / 100)
    (hgood_x : IsGoodAnnulusEvent μ K.c0 C_good (Rf (shellCentre ε η Kset r s d k ω)) (Z k ω))
    (hb_x : ω (shellExit ε η Kset r s d Rf k ω).toNat ∈
      cellVertices ε η (sphere (Z k ω) (4 * Rf (shellCentre ε η Kset r s d k ω) / 3))) :
    (μ (ball (vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat))
        (3 * K.c0 * Rf (shellCentre ε η Kset r s d k ω)))).toReal
      ≤ MatedCRT.Lemma68ConstOrder.shellDbl68 C_good *
        (μ (ball (vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat))
          (K.c0 * Rf (shellCentre ε η Kset r s d k ω)))).toReal := by
  have hR0 : 0 < Rf (shellCentre ε η Kset r s d k ω) :=
    lt_of_lt_of_le (pow_pos hr 2) hRr_x.1
  have hpow : 0 ≤ ε ^ K.ω := Real.rpow_nonneg hε.le _
  have hWv : (cell ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat) ∩
      ball (0 : ℂ) (ρc - ε ^ K.ω)).Nonempty := hWalk_x.1
  have hmeet : (cell ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat) ∩
      ball (0 : ℂ) ρ').Nonempty := by
    obtain ⟨p, hp1, hp2⟩ := hWv
    exact ⟨p, hp1, ball_subset_ball (by linarith) hp2⟩
  have hdiam : diam (cell ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat)) ≤
      K.c0 * Rf (shellCentre ε η Kset r s d k ω) / 100 := by
    have h1 := hCellGood _ hmeet
    have h2 := hRmin_x
    linarith
  obtain ⟨p, hpc, hps⟩ : (cell ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat) ∩
      sphere (Z k ω) (4 * Rf (shellCentre ε η Kset r s d k ω) / 3)).Nonempty := hb_x
  have hdist_p : dist p (Z k ω) = 4 * Rf (shellCentre ε η Kset r s d k ω) / 3 := mem_sphere.1 hps
  have hx : vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat) ∈
      cell ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat) :=
    MatedCRT.Lemma68C12Geom.vertexPoint_mem_cell hε.le _
  have hbdd : Bornology.IsBounded (cell ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat)) :=
    (MatedCRT.Lemma68C12Geom.cell_isCompact hη _).isBounded
  have hxp : dist (vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat)) p ≤
      K.c0 * Rf (shellCentre ε η Kset r s d k ω) / 100 :=
    (dist_le_diam_of_mem hbdd hx hpc).trans hdiam
  have habs : |dist (vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat)) (Z k ω) -
      4 * Rf (shellCentre ε η Kset r s d k ω) / 3| ≤
      K.c0 * Rf (shellCentre ε η Kset r s d k ω) / 100 := by
    have h := abs_dist_sub_le (vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat)) p (Z k ω)
    rw [hdist_p] at h
    exact h.trans hxp
  obtain ⟨hl, hu⟩ := abs_le.1 habs
  have ht : K.c0 * Rf (shellCentre ε η Kset r s d k ω) ≤ Rf (shellCentre ε η Kset r s d k ω) / 24 := by
    have := mul_le_mul_of_nonneg_right K.hc0' hR0.le
    linarith
  have ht0 : 0 ≤ K.c0 * Rf (shellCentre ε η Kset r s d k ω) := mul_nonneg K.hc0.le hR0.le
  have hx_ann : vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat) ∈
      annulus (Z k ω) (Rf (shellCentre ε η Kset r s d k ω)) (2 * Rf (shellCentre ε η Kset r s d k ω)) := by
    show _ ∈ Metric.ball (Z k ω) (2 * Rf (shellCentre ε η Kset r s d k ω)) \
      Metric.closedBall (Z k ω) (Rf (shellCentre ε η Kset r s d k ω))
    refine ⟨?_, ?_⟩
    · rw [mem_ball]
      linarith
    · intro h
      rw [mem_closedBall] at h
      linarith
  have hsub : ball (vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat))
      (3 * K.c0 * Rf (shellCentre ε η Kset r s d k ω)) ⊆
      annulus (Z k ω) (Rf (shellCentre ε η Kset r s d k ω)) (2 * Rf (shellCentre ε η Kset r s d k ω)) := by
    intro w hw
    rw [mem_ball] at hw
    have h3 : 3 * K.c0 * Rf (shellCentre ε η Kset r s d k ω) =
        3 * (K.c0 * Rf (shellCentre ε η Kset r s d k ω)) := by ring
    have h1 := dist_triangle w (vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat)) (Z k ω)
    have h2 : dist (vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat)) (Z k ω) ≤
        dist w (vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat)) + dist w (Z k ω) := by
      have := dist_triangle (vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat)) w (Z k ω)
      rwa [dist_comm (vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat)) w] at this
    show w ∈ Metric.ball (Z k ω) (2 * Rf (shellCentre ε η Kset r s d k ω)) \
      Metric.closedBall (Z k ω) (Rf (shellCentre ε η Kset r s d k ω))
    refine ⟨?_, ?_⟩
    · rw [mem_ball]
      linarith
    · intro h
      rw [mem_closedBall] at h
      linarith
  have hD0 : 0 ≤ MatedCRT.Lemma68ConstOrder.shellDbl68 C_good := by
    unfold MatedCRT.Lemma68ConstOrder.shellDbl68
    exact le_trans zero_le_one (le_max_left _ _)
  have hm := MatedCRT.Lemma68ShellDbl.measure_three_le_shellDbl68 K.hc0
    (by linarith [K.hc0']) hR0 (hgood_x) hx_ann hsub
  have hfin : μ (ball (vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat))
      (K.c0 * Rf (shellCentre ε η Kset r s d k ω))) ≠ ⊤ :=
    (measure_ball_lt_top).ne
  calc (μ (ball (vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat))
          (3 * K.c0 * Rf (shellCentre ε η Kset r s d k ω)))).toReal
      ≤ (ENNReal.ofReal (MatedCRT.Lemma68ConstOrder.shellDbl68 C_good) *
          μ (ball (vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat))
            (K.c0 * Rf (shellCentre ε η Kset r s d k ω)))).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) hm
    _ = MatedCRT.Lemma68ConstOrder.shellDbl68 C_good *
          (μ (ball (vertexPoint ε η (ω (shellExit ε η Kset r s d Rf k ω).toNat))
            (K.c0 * Rf (shellCentre ε η Kset r s d k ω)))).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hD0]


#print axioms MatedCRT.Lemma68HoneExitGeom.hdbl_of_exit_geom_path_split


/-! ## Environment inputs of `hb`, discharged (fp-S4S6c-walk-env-adjacency)

For a valid environment `S` and `ε > 0`, the edge multiplicity `m = S.mult ε ω` of the mated-CRT map satisfies, almost
surely in `ω`, the deterministic hypotheses `hdeg` and `hadj` of `hb_ae_of_walk`. -/

/-- **Degree of the mated-CRT map, almost surely (operator item 1).** For a valid environment `S` and `ε > 0`, almost
surely in `ω`, every vertex `v` of the multigraph `S.mult ε ω` has `edgeMeasure m v univ ≠ 0` and `≠ ⊤`. Proof: local
finiteness and consecutive adjacency (`Lemma68WindowMult.hmult_of_valid68`) give `edgeMeasure_univ`, which identifies
the total mass with the degree `mdeg m v`; the degree is nonzero because of the neighbour `v + 1`
(`mdeg_ne_zero_of_ne_zero`), and the degree is a natural number, so it is not `⊤`. -/
theorem hdeg_of_valid {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂S.P, ∀ v : ℤ, edgeMeasure (S.mult ε ω) v univ ≠ 0 ∧ edgeMeasure (S.mult ε ω) v univ ≠ ⊤ := by
  filter_upwards [MatedCRT.Lemma68WindowMult.hmult_of_valid68 hγ0 hγ2 S hS hε] with ω hω
  obtain ⟨hlf, hsucc⟩ := hω
  intro v
  rw [edgeMeasure_univ hlf v]
  exact ⟨by exact_mod_cast mdeg_ne_zero_of_ne_zero hlf (hsucc v), ENNReal.natCast_ne_top _⟩

/-- **Closed-cell adjacency of the mated-CRT map, almost surely (operator item 2).** For a valid environment `S` and
`ε > 0`, almost surely in `ω`, every edge `S.mult ε ω u v ≠ 0` joins vertices whose closed cells meet. Proof: the open
cells of adjacent vertices meet almost surely (`TraceInputs68.ae_adjacent`), and the closed-cell form is
`TraceInputs68.closure_cells_meet_of_mult`. -/
theorem hadj_of_valid {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂S.P, ∀ u v : ℤ, S.mult ε ω u v ≠ 0 →
      (closure (cell ε (S.η ω) u) ∩ closure (cell ε (S.η ω) v)).Nonempty := by
  filter_upwards [TraceInputs68.ae_adjacent hγ0 hγ2 S hS] with ω hω
  exact TraceInputs68.closure_cells_meet_of_mult (hω ε hε)
/-- **The hit cell lies in the interior of the `4R/3`-ball (operator request 64e).** Let `t = shellHit`, the first time
the walk's cell meets the two-sided shell `Σ_{k+1}`. The centre `shellCentre` is the grid rounding of `vertexPoint (x t)`,
so it is within `d / 100` of that vertex (`dist_gridRound_le`); the cell of `x t` has diameter at most `d / 100`
(`CellDiamLe`, the mesh). If the window radius at the centre is at least `d`, every point of the cell lies within
`2 d / 100 < 4 R / 3` of the centre. So the cell meets the open ball and misses its frontier sphere
(`frontier_ball`: the frontier of a ball is its sphere). Terminology: Armitage-Gardiner (balls and their frontier). -/
theorem shellHit_interior_of_mesh {ε : ℝ} {η : ℝ → ℂ} (hε : 0 < ε) (Kset : Set ℂ) {r s d : ℝ} {R : ℂ → ℝ}
    (hd : 0 < d) (hmesh : CellDiamLe ε η (d / 100) Set.univ) (k : ℕ) (x : ℕ → ℤ)
    (hR : d ≤ R (shellCentre ε η Kset r s d k x)) (t : ℕ)
    (ht : shellHit ε η Kset r s k x = (t : ℕ∞)) :
    x t ∈ interiorCellVertices ε η
      (ball (shellCentre ε η Kset r s d k x) (4 * R (shellCentre ε η Kset r s d k x) / 3)) := by
  have hdt : (shellHit ε η Kset r s k x).toNat = t := by rw [ht]; simp
  have hcdef : shellCentre ε η Kset r s d k x
      = MatedCRT.Lemma68Window.gridRound (d / 100) (vertexPoint ε η (x t)) := by
    unfold shellCentre
    rw [hdt]
  have hpc : dist (shellCentre ε η Kset r s d k x) (vertexPoint ε η (x t)) ≤ d / 100 := by
    rw [hcdef]
    exact MatedCRT.Lemma68Window.dist_gridRound_le (by linarith) _
  have hpcell : vertexPoint ε η (x t) ∈ cell ε η (x t) :=
    ⟨ε * ((x t : ℤ) : ℝ), ⟨by nlinarith [hε], le_rfl⟩, rfl⟩
  have hRpos : 0 < R (shellCentre ε η Kset r s d k x) := lt_of_lt_of_le hd hR
  have hball : ∀ z ∈ cell ε η (x t), dist z (shellCentre ε η Kset r s d k x)
      < 4 * R (shellCentre ε η Kset r s d k x) / 3 := by
    intro z hz
    have h1 : dist z (vertexPoint ε η (x t)) ≤ d / 100 :=
      hmesh (x t) ⟨vertexPoint ε η (x t), hpcell, Set.mem_univ _⟩ z hz _ hpcell
    have h2 := dist_triangle z (vertexPoint ε η (x t)) (shellCentre ε η Kset r s d k x)
    rw [dist_comm (vertexPoint ε η (x t)) (shellCentre ε η Kset r s d k x)] at h2
    linarith
  have hR3 : 0 < 4 * R (shellCentre ε η Kset r s d k x) / 3 := by linarith
  refine ⟨⟨vertexPoint ε η (x t), hpcell, Metric.mem_ball.2 (hball _ hpcell)⟩, ?_⟩
  rintro ⟨z, hz, hzf⟩
  rw [frontier_ball _ hR3.ne'] at hzf
  exact absurd (Metric.mem_sphere.1 hzf) (ne_of_lt (hball z hz))

/-- **`shellHit_interior_of_mesh` at the hit vertex (path-level, q4 fp-S4S6c-goodenv-local).** The univ mesh is used only
on the cell of the hit vertex `x t`, so the binder `hmesh` (univ form) is replaced by the cell diameter bound `hcell` on
that cell. The walk supplies `hcell` up to its exit time (`Lemma68PathMesh.diam_upto_vExitTime`, PathMesh68.lean),
which is why the hit time must not exceed the exit time there. -/
theorem shellHit_interior_of_cellDiam {ε : ℝ} {η : ℝ → ℂ} (hε : 0 < ε) (Kset : Set ℂ) {r s d : ℝ} {R : ℂ → ℝ}
    (hd : 0 < d) (k : ℕ) (x : ℕ → ℤ)
    (hR : d ≤ R (shellCentre ε η Kset r s d k x)) (t : ℕ)
    (ht : shellHit ε η Kset r s k x = (t : ℕ∞))
    (hcell : ∀ p ∈ cell ε η (x t), ∀ q ∈ cell ε η (x t), dist p q ≤ d / 100) :
    x t ∈ interiorCellVertices ε η
      (ball (shellCentre ε η Kset r s d k x) (4 * R (shellCentre ε η Kset r s d k x) / 3)) := by
  have hdt : (shellHit ε η Kset r s k x).toNat = t := by rw [ht]; simp
  have hcdef : shellCentre ε η Kset r s d k x
      = MatedCRT.Lemma68Window.gridRound (d / 100) (vertexPoint ε η (x t)) := by
    unfold shellCentre
    rw [hdt]
  have hpc : dist (shellCentre ε η Kset r s d k x) (vertexPoint ε η (x t)) ≤ d / 100 := by
    rw [hcdef]
    exact MatedCRT.Lemma68Window.dist_gridRound_le (by linarith) _
  have hpcell : vertexPoint ε η (x t) ∈ cell ε η (x t) :=
    ⟨ε * ((x t : ℤ) : ℝ), ⟨by nlinarith [hε], le_rfl⟩, rfl⟩
  have hRpos : 0 < R (shellCentre ε η Kset r s d k x) := lt_of_lt_of_le hd hR
  have hball : ∀ z ∈ cell ε η (x t), dist z (shellCentre ε η Kset r s d k x)
      < 4 * R (shellCentre ε η Kset r s d k x) / 3 := by
    intro z hz
    have h1 : dist z (vertexPoint ε η (x t)) ≤ d / 100 :=
      hcell z hz (vertexPoint ε η (x t)) hpcell
    have h2 := dist_triangle z (vertexPoint ε η (x t)) (shellCentre ε η Kset r s d k x)
    rw [dist_comm (vertexPoint ε η (x t)) (shellCentre ε η Kset r s d k x)] at h2
    linarith
  have hR3 : 0 < 4 * R (shellCentre ε η Kset r s d k x) / 3 := by linarith
  refine ⟨⟨vertexPoint ε η (x t), hpcell, Metric.mem_ball.2 (hball _ hpcell)⟩, ?_⟩
  rintro ⟨z, hz, hzf⟩
  rw [frontier_ball _ hR3.ne'] at hzf
  exact absurd (Metric.mem_sphere.1 hzf) (ne_of_lt (hball z hz))

/-- **`hb` almost surely from the mesh and the window radius (operator request 64e closed).** This replaces
`hb_ae_valid_centre`: the hit-cell interiority `hhit` is no longer named. It follows from `hmesh` (the grid mesh
`CellDiamLe ε (S.η ω) (d / 100)`) and `hR` (the window radius at the shell centre is at least `d`, which holds where the
centre is eligible for the window). The guard `G` is a predicate of the environment; in the B1 application it is
`ω ∈ E ∧ FullAdmAt`. The centre is `shellCentre` with the family `Kset ω`, `Rf ω`, `τU ω`. -/
theorem hb_ae_valid_centre_mesh {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {ε : ℝ} (hε : 0 < ε) (Kset : Ω → Set ℂ) {Rf : Ω → ℂ → ℝ} {r s d : ℝ}
    {A : Set ℤ} {τU : Ω → (ℕ → ℤ) → ℕ∞} (a : ℤ) (n : ℕ) (G : Ω → Prop) (hd : 0 < d)
    (hmesh : ∀ᵐ ω ∂S.P, CellDiamLe ε (S.η ω) (d / 100) Set.univ)
    (hR : ∀ᵐ ω ∂S.P, G ω → ∀ k ≤ n, ∀ᵐ x ∂srwLaw (S.mult ε ω) a,
      x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A
          (shellExit ε (S.η ω) (Kset ω) r s d (Rf ω) k) (τU ω) →
        d ≤ Rf ω (shellCentre ε (S.η ω) (Kset ω) r s d k x)) :
    ∀ᵐ ω ∂S.P, G ω → ∀ k ≤ n, ∀ᵐ x ∂srwLaw (S.mult ε ω) a,
      x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A
          (shellExit ε (S.η ω) (Kset ω) r s d (Rf ω) k) (τU ω) →
        x (shellExit ε (S.η ω) (Kset ω) r s d (Rf ω) k x).toNat ∈
          cellVertices ε (S.η ω) (sphere (shellCentre ε (S.η ω) (Kset ω) r s d k x)
            (4 * Rf ω (shellCentre ε (S.η ω) (Kset ω) r s d k x) / 3)) := by
  filter_upwards [TraceInputs68.ae_continuous_eta hS, hdeg_of_valid hγ0 hγ2 S hS hε,
    hadj_of_valid hγ0 hγ2 S hS hε, hmesh, hR] with ω hη hdeg hadj hm hRω
  intro hG
  have hhit : ∀ k ≤ n, ∀ᵐ x ∂srwLaw (S.mult ε ω) a,
      x ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A
          (shellExit ε (S.η ω) (Kset ω) r s d (Rf ω) k) (τU ω) →
      ∀ t : ℕ, shellHit ε (S.η ω) (Kset ω) r s k x = (t : ℕ∞) →
        x t ∈ interiorCellVertices ε (S.η ω)
          (ball (shellCentre ε (S.η ω) (Kset ω) r s d k x)
            (4 * Rf ω (shellCentre ε (S.η ω) (Kset ω) r s d k x) / 3)) :=
    fun k hk => (hRω hG k hk).mono fun x hx hxm t ht =>
      shellHit_interior_of_mesh hε (Kset ω) hd hm k x (hx hxm) t ht
  exact hb_ae_of_walk (Z := fun k x => shellCentre ε (S.η ω) (Kset ω) r s d k x) hη (Kset ω)
    (S.mult ε ω) a n hdeg hadj (fun _ _ => rfl) hhit

#print axioms MatedCRT.Lemma68HoneExitGeom.shellHit_interior_of_mesh
#print axioms MatedCRT.Lemma68HoneExitGeom.hdeg_of_valid
#print axioms MatedCRT.Lemma68HoneExitGeom.hadj_of_valid

#print axioms MatedCRT.Lemma68HoneExitGeom.cell_meets_sphere_of_exit
#print axioms MatedCRT.Lemma68HoneExitGeom.hdbl_of_exit_geom
#print axioms MatedCRT.Lemma68HoneExitGeom.srwLaw_step_ae_adjacent
#print axioms MatedCRT.Lemma68HoneExitGeom.hb_ae_of_walk
#print axioms MatedCRT.Lemma68HoneExitGeom.hdbl_of_exit_geom_237

end Lemma68HoneExitGeom
end MatedCRT
