import MatedCRT.FirstPass.Derived.HarnackAssembly
import MatedCRT.Proofs.Sec5.StoppedPoleFiniteComparison

/-!
# The Harnack bound on circles for the Green kernel of a disk centred at the pole

Berestycki-Gwynne, *Random walks on mated-CRT planar maps and Liouville Brownian motion*, proof of Lemma 4.4, the
bound (4.13) (from ibid. Proposition 3.8): for the Green kernel `g = g_{B_r(η(b))}(b, ·)` of the domain
`V^ε(B_r(η(b))) \ V^ε(∂B_r(η(b)))`, the ring event of ibid. Lemma 3.10 at a grid point near `η(b)` gives
`g(y) ≤ p⁻¹ g(y')` for all `y, y' ∈ V^ε(∂B_s(η(b)))`, `s ≤ r/4`.

* `exists_mem_cell_dist_ge_of_not_mem_interior_ball`: a vertex outside `V^ε(B_r(c)) \ V^ε(∂B_r(c))` has a cell
  point at distance at least `r` from `c`.
* `exists_ringData_ball`: a grid point `z'` within `h` of `η(b)` and a radius `(√2)^a ∈ (s, 3(s + 2h)/2)` such that
  the circle `∂B_s(η(b))` lies in the shell `A_{(√2)^a/2, (√2)^a}(z')`, the cell of `b` in `B_{(√2)^a/4}(z')`, and
  every vertex outside the Green domain of `B_r(η(b))` has a cell point outside `B̄_{2(√2)^a}(z')`.
* `greenKernel_le_inv_mul_of_ringEvents_ball`: the Harnack bound `g_B(b, y) ≤ p⁻¹ g_B(b, y')` on
  `V^ε(∂B_s(η(b)))` for `B` the Green domain of `B_r(η(b))`, from the ring event at that grid data.
-/

namespace MatedCRT

open Set Metric

/-- A vertex outside the Green domain `V^ε(B_r(c)) \ V^ε(∂B_r(c))` has a cell point at distance at least `r`
from `c`. -/
theorem exists_mem_cell_dist_ge_of_not_mem_interior_ball {ε : ℝ} (hε : 0 ≤ ε) (η : ℝ → ℂ) {c : ℂ} {r : ℝ}
    (hr : r ≠ 0) {k : ℤ} (hk : k ∉ interiorCellVertices ε η (ball c r)) :
    ∃ x ∈ cell ε η k, r ≤ dist x c := by
  unfold interiorCellVertices at hk
  by_cases h1 : k ∈ cellVertices ε η (ball c r)
  · have h2 : k ∈ cellVertices ε η (frontier (ball c r)) := by
      by_contra h2
      exact hk ⟨h1, h2⟩
    obtain ⟨x, hx, hxf⟩ := h2
    rw [frontier_ball _ hr, mem_sphere] at hxf
    exact ⟨x, hx, hxf.ge⟩
  · have hx := vertexPoint_mem_cell hε η k
    refine ⟨vertexPoint ε η k, hx, ?_⟩
    by_contra hlt
    exact h1 ⟨vertexPoint ε η k, hx, mem_ball.2 (not_le.1 hlt)⟩

/-- **Grid data for the circle `∂B_s(η(b))` inside the disk `B_r(η(b))`**, `s ≤ r/4`. -/
theorem exists_ringData_ball {ε : ℝ} (hε : 0 ≤ ε) (η : ℝ → ℂ) {δ h s r : ℝ} (hh : 0 < h) {b : ℤ}
    (hdiam : ∀ x ∈ cell ε η b, ∀ x' ∈ cell ε η b, dist x x' ≤ δ)
    (hs1 : 10 * h ≤ s) (hs2 : s ≤ r / 4) (hδ1 : δ + h ≤ s / 4) :
    ∃ m n a : ℤ, dist (vertexPoint ε η b) (latticePt h m n) ≤ h ∧ s < sqrt2Pow a ∧
      sqrt2Pow a < 3 / 2 * (s + 2 * h) ∧
      (∀ x : ℂ, dist x (vertexPoint ε η b) = s →
        sqrt2Pow a / 2 < dist x (latticePt h m n) ∧ dist x (latticePt h m n) < sqrt2Pow a) ∧
      (∀ x ∈ cell ε η b, dist x (latticePt h m n) < sqrt2Pow a / 4) ∧
      (∀ k, k ∉ interiorCellVertices ε η (ball (vertexPoint ε η b) r) →
        ∃ x ∈ cell ε η k, 2 * sqrt2Pow a < dist x (latticePt h m n)) := by
  have hz := vertexPoint_mem_cell hε η b
  set z := vertexPoint ε η b with hzdef
  obtain ⟨m, n, hmn⟩ := LatticeProb.exists_lattice_point_norm_sub_le hh z
  have hzz : dist z (latticePt h m n) ≤ h := by rw [dist_eq_norm]; exact hmn
  have hqlo : 1 < Real.sqrt 2 := (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  have hqhi : Real.sqrt 2 < 3 / 2 := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  have hxpos : 0 < s + 2 * h := by linarith
  obtain ⟨a, ha1, ha2⟩ := LatticeProb.exists_le_zpow_lt hqlo hxpos
  have hs' : sqrt2Pow a < 3 / 2 * (s + 2 * h) := by
    unfold sqrt2Pow
    calc Real.sqrt 2 ^ a < Real.sqrt 2 * (s + 2 * h) := ha2
      _ < 3 / 2 * (s + 2 * h) := mul_lt_mul_of_pos_right hqhi hxpos
  have hs'lo : s + 2 * h ≤ sqrt2Pow a := ha1
  refine ⟨m, n, a, hzz, by linarith, hs', ?_, ?_, ?_⟩
  · intro x hx
    have d1 := dist_triangle x z (latticePt h m n)
    have d2 := dist_triangle x (latticePt h m n) z
    rw [dist_comm (latticePt h m n) z] at d2
    constructor <;> linarith
  · intro x hx
    have d1 := dist_triangle x z (latticePt h m n)
    have d2 := hdiam x hx z hz
    linarith
  · intro k hk
    have hr : r ≠ 0 := by intro h0; linarith
    obtain ⟨x, hx, hxd⟩ := exists_mem_cell_dist_ge_of_not_mem_interior_ball hε η hr hk
    refine ⟨x, hx, ?_⟩
    have d1 := dist_triangle x (latticePt h m n) z
    rw [dist_comm (latticePt h m n) z] at d1
    linarith

/-- **Harnack bound on circles for the Green kernel of a disk centred at the pole** (Berestycki-Gwynne, the
bound (4.13) in the proof of Lemma 4.4). Let `B` be the Green domain `V^ε(B_r(η(b))) \ V^ε(∂B_r(η(b)))` and
`10h ≤ s ≤ r/4`, `δ + h ≤ s/4` with `δ` bounding the diameter of the cell of `b`. If the ring event of Lemma 3.10
holds with probability `p` at every grid point within `h` of `η(b)` and every radius `(√2)^a ∈ (s, 3(s + 2h)/2)`,
then `g_B(b, y) ≤ p⁻¹ g_B(b, y')` for all `y, y' ∈ V^ε(∂B_s(η(b)))`. -/
theorem greenKernel_le_inv_mul_of_ringEvents_ball {ε : ℝ} (hε : 0 ≤ ε) {η : ℝ → ℂ} (hη : Continuous η)
    {m : ℤ → ℤ → ℕ} (hsymm : ∀ a b, m a b = m b a) (hlf : IsLocallyFiniteMult m)
    (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0)
    (hedge : ∀ j k : ℤ, m j k ≠ 0 → (cell ε η j ∩ cell ε η k).Nonempty)
    {δ h p r s : ℝ} (hh : 0 < h) (hp : 0 < p) {b : ℤ}
    (hB : (interiorCellVertices ε η (ball (vertexPoint ε η b) r)).Finite)
    (hdiam : ∀ x ∈ cell ε η b, ∀ x' ∈ cell ε η b, dist x x' ≤ δ)
    (hs1 : 10 * h ≤ s) (hs2 : s ≤ r / 4) (hδ1 : δ + h ≤ s / 4)
    (hring : ∀ m' n' a' : ℤ, dist (vertexPoint ε η b) (latticePt h m' n') ≤ h → s < sqrt2Pow a' →
      sqrt2Pow a' < 3 / 2 * (s + 2 * h) → RingSeparates m ε η p (latticePt h m' n') (sqrt2Pow a')) :
    ∀ y ∈ cellVertices ε η (sphere (vertexPoint ε η b) s),
    ∀ y' ∈ cellVertices ε η (sphere (vertexPoint ε η b) s),
      greenKernel m (interiorCellVertices ε η (ball (vertexPoint ε η b) r)) b y ≤
        p⁻¹ * greenKernel m (interiorCellVertices ε η (ball (vertexPoint ε η b) r)) b y' := by
  intro y hy y' hy'
  obtain ⟨m', n', a', hzz, hslo, hshi, hcirc, hcellb, hout⟩ := exists_ringData_ball hε η hh hdiam hs1 hs2 hδ1
  have hring' := hring m' n' a' hzz hslo hshi
  have hr0 : 0 < r := by linarith
  have hδ0 : δ < r := by linarith
  have hbB : b ∈ interiorCellVertices ε η (ball (vertexPoint ε η b) r) := by
    refine ⟨⟨vertexPoint ε η b, vertexPoint_mem_cell hε η b, mem_ball_self hr0⟩, ?_⟩
    rintro ⟨x, hx, hxf⟩
    rw [frontier_ball _ hr0.ne', mem_sphere] at hxf
    have := hdiam x hx _ (vertexPoint_mem_cell hε η b)
    linarith
  obtain ⟨xa, hxa, hxad⟩ := hy
  obtain ⟨xy, hxy, hxyd⟩ := hy'
  rw [mem_sphere] at hxad hxyd
  obtain ⟨hxa1, hxa2⟩ := hcirc xa hxad
  obtain ⟨hxy1, hxy2⟩ := hcirc xy hxyd
  have hs'pos : 0 < sqrt2Pow a' := by linarith
  have hshell : ∀ x : ℂ, sqrt2Pow a' / 2 < dist x (latticePt h m' n') →
      dist x (latticePt h m' n') < sqrt2Pow a' → x ∈ ringShell (latticePt h m' n') (sqrt2Pow a') := by
    intro x h1 h2
    exact ⟨mem_ball.2 h2, fun hx => absurd (mem_closedBall.1 hx) (not_le.2 h1)⟩
  have hyA : y ∈ cellVertices ε η (ringShell (latticePt h m' n') (sqrt2Pow a')) :=
    ⟨xa, hxa, hshell xa hxa1 hxa2⟩
  have hy'A : y' ∈ cellVertices ε η (ringShell (latticePt h m' n') (sqrt2Pow a')) :=
    ⟨xy, hxy, hshell xy hxy1 hxy2⟩
  have key := mul_greenKernel_le_of_ringSeparation hε hη hlf hcons hedge hB hbB (a := y') (y := y)
    (p := p) hp.le (z := latticePt h m' n') (r₁ := sqrt2Pow a' / 4) (r₂ := 2 * sqrt2Pow a')
    (I₀ := ringBarrier ε η (latticePt h m' n') (sqrt2Pow a'))
    (A := cellVertices ε η (ringShell (latticePt h m' n') (sqrt2Pow a')))
    (subset_refl _) hyA
    ⟨xa, hxa, by linarith, by linarith⟩ ⟨xy, hxy, by linarith, by linarith⟩
    ⟨vertexPoint ε η b, vertexPoint_mem_cell hε η b, hcellb _ (vertexPoint_mem_cell hε η b)⟩
    (fun k hk => by
      obtain ⟨x, hx, hxd⟩ := hout k hk
      exact ⟨x, hx, Or.inr hxd⟩)
    (hring' y' hy'A)
  rw [greenKernel_symm_pole hsymm hlf hcons hB b y, greenKernel_symm_pole hsymm hlf hcons hB b y']
  calc greenKernel m (interiorCellVertices ε η (ball (vertexPoint ε η b) r)) y b
      = p⁻¹ * (p * greenKernel m (interiorCellVertices ε η (ball (vertexPoint ε η b) r)) y b) := by
        field_simp
    _ ≤ p⁻¹ * greenKernel m (interiorCellVertices ε η (ball (vertexPoint ε η b) r)) y' b :=
        mul_le_mul_of_nonneg_left key (inv_nonneg.2 hp.le)

end MatedCRT
