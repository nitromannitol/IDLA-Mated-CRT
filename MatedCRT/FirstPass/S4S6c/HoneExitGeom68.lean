import MatedCRT.FirstPass.S6n
import MatedCRT.FirstPass.S4S6c.ShellHoneInst68
import MatedCRT.FirstPass.S4S6c.ShellDbl68
import MatedCRT.FirstPass.S4S6c.ExitPath68

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

#print axioms MatedCRT.Lemma68HoneExitGeom.cell_meets_sphere_of_exit
#print axioms MatedCRT.Lemma68HoneExitGeom.hdbl_of_exit_geom

end Lemma68HoneExitGeom
end MatedCRT
