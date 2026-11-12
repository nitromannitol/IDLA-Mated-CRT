import MatedCRT.FirstPass.Derived.HarnackRingGeometry
import MatedCRT.FirstPass.Derived.HarnackRingSeparation

/-!
# Harnack ratio for the Green kernel on circles: deterministic assembly

Deterministic part of Berestycki–Gwynne (2020), Proposition 3.8.  Fix a mesh `h` and a lower radius `s₀`.  Suppose that
for every lattice point `z' = h (m + n i)` and every radius `s' = (√2)^a` (in the range of Lemma 3.11), the ring event of
Lemma 3.10 holds with probability parameter `p`: from every vertex of the open shell `A_{s'/2,s'}(z')` the simple random
walk disconnects the vertices of the shell from the vertices whose cells meet `∂B_{s'/4}(z') ∪ ∂B_{2s'}(z')`, before
hitting those vertices, with probability at least `p`.  Then for every vertex `b` of `B_ρ` whose cell has diameter at
most `δ`, every circle `∂B_s(η(εb))` with `s₀ ≤ s ≤ (1-ρ)/8`, and all vertices `a, y` of that circle,
`g_B(a, b) ≤ p⁻¹ g_B(y, b)`, for the killing domain `B = V(B_{(1+ρ)/2}) \ V(∂B_{(1+ρ)/2})`.
-/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Set Metric
open scoped ENNReal
open MatedCRTHarmonic MatedCRTHarmonic.HarmonicInfinity MatedCRTHarmonic.Markov

/-- The open shell `A_{s/2,s}(z) = B_s(z) \ B̄_{s/2}(z)`. -/
def ringShell (z : ℂ) (s : ℝ) : Set ℂ := ball z s \ closedBall z (s / 2)

/-- The vertices whose cells meet `∂B_{s/4}(z) ∪ ∂B_{2s}(z)` (the set `I₀` of Lemma 3.10). -/
def ringBarrier (ε : ℝ) (η : ℝ → ℂ) (z : ℂ) (s : ℝ) : Set ℤ :=
  cellVertices ε η (sphere z (s / 4)) ∪ cellVertices ε η (sphere z (2 * s))

/-- The ring event of Lemma 3.10 at `(z, s)` with parameter `p`: from every vertex of the shell `A_{s/2,s}(z)`, the walk
on `m` disconnects the shell vertices from `ringBarrier`, before hitting it, with probability at least `p`. -/
def RingSeparates (m : ℤ → ℤ → ℕ) (ε : ℝ) (η : ℝ → ℂ) (p : ℝ) (z : ℂ) (s : ℝ) : Prop :=
  ∀ x ∈ cellVertices ε η (ringShell z s), ENNReal.ofReal p ≤ srwLaw m x
    {ξ | GraphSeparates (srwGraph m) (traceBefore (id : ℤ → ℤ) (ringBarrier ε η z s) ξ)
      (cellVertices ε η (ringShell z s)) (ringBarrier ε η z s)}

/-- A vertex of a circle `∂B_s(z)` (with `s ≠ 0`) has a cell point at distance exactly `s` from `z`. -/
theorem exists_mem_cell_dist_eq_of_mem_cellVertices_frontier {ε : ℝ} {η : ℝ → ℂ} {z : ℂ} {s : ℝ}
    (hs : s ≠ 0) {a : ℤ} (ha : a ∈ cellVertices ε η (frontier (ball z s))) :
    ∃ x ∈ cell ε η a, dist x z = s := by
  obtain ⟨x, hx, hxf⟩ := ha
  rw [frontier_ball _ hs] at hxf
  exact ⟨x, hx, mem_sphere.1 hxf⟩

/-- **Harnack ratio for the Green kernel on a circle, from the ring events.** -/
theorem greenKernel_le_inv_mul_of_ringEvents {ε : ℝ} (hε : 0 ≤ ε) {η : ℝ → ℂ} (hη : Continuous η)
    {m : ℤ → ℤ → ℕ} (hlf : IsLocallyFiniteMult m) (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0)
    (hedge : ∀ j k : ℤ, m j k ≠ 0 → (cell ε η j ∩ cell ε η k).Nonempty)
    {ρ δ h s₀ p : ℝ} (hρ : 0 < ρ) (hh : 0 < h) (hp : 0 < p)
    (hB : (interiorCellVertices ε η (ball (0 : ℂ) ((1 + ρ) / 2))).Finite)
    (hdiam : ∀ b ∈ cellVertices ε η (ball (0 : ℂ) ρ), ∀ x ∈ cell ε η b, ∀ x' ∈ cell ε η b, dist x x' ≤ δ)
    (hs₀ : 10 * h ≤ s₀) (hδ : δ + h ≤ s₀ / 4)
    (hring : ∀ m' n' a' : ℤ, ‖latticePt h m' n'‖ < (1 + ρ) / 2 → s₀ ≤ sqrt2Pow a' →
      2 * sqrt2Pow a' ≤ (1 + ρ) / 2 - ‖latticePt h m' n'‖ →
      RingSeparates m ε η p (latticePt h m' n') (sqrt2Pow a')) :
    ∀ b ∈ cellVertices ε η (ball (0 : ℂ) ρ), ∀ s : ℝ, s₀ ≤ s → s ≤ (1 - ρ) / 8 →
      ∀ a ∈ cellVertices ε η (frontier (ball (vertexPoint ε η b) s)),
      ∀ y ∈ cellVertices ε η (frontier (ball (vertexPoint ε η b) s)),
        greenKernel m (interiorCellVertices ε η (ball (0 : ℂ) ((1 + ρ) / 2))) a b ≤
          p⁻¹ * greenKernel m (interiorCellVertices ε η (ball (0 : ℂ) ((1 + ρ) / 2))) y b := by
  intro b hb s hs0 hs1 a ha y hy
  have hspos : 0 < s := by linarith
  have hρ1 : ρ < 1 := by linarith
  have hδs : δ + h ≤ s / 4 := by linarith
  obtain ⟨m', n', a', hz'n, hss', hr2, hcirc, hcellb, hout⟩ :=
    exists_ringData hε η hρ hh hb (hdiam b hb) (by linarith) hs1 hδs
  have hz'b : ‖latticePt h m' n'‖ < (1 + ρ) / 2 := by linarith
  have hring' := hring m' n' a' hz'b (by linarith) hr2.le
  have hbB : b ∈ interiorCellVertices ε η (ball (0 : ℂ) ((1 + ρ) / 2)) :=
    mem_interiorCellVertices_of_diam η (by linarith) (by linarith) (by linarith) hb (hdiam b hb)
  obtain ⟨xa, hxa, hxad⟩ := exists_mem_cell_dist_eq_of_mem_cellVertices_frontier hspos.ne' ha
  obtain ⟨xy, hxy, hxyd⟩ := exists_mem_cell_dist_eq_of_mem_cellVertices_frontier hspos.ne' hy
  obtain ⟨hxa1, hxa2⟩ := hcirc xa hxad
  obtain ⟨hxy1, hxy2⟩ := hcirc xy hxyd
  have hshell : ∀ x : ℂ, sqrt2Pow a' / 2 < dist x (latticePt h m' n') →
      dist x (latticePt h m' n') < sqrt2Pow a' → x ∈ ringShell (latticePt h m' n') (sqrt2Pow a') := by
    intro x h1 h2
    exact ⟨mem_ball.2 h2, fun hx => absurd (mem_closedBall.1 hx) (not_le.2 h1)⟩
  have hs'pos : 0 < sqrt2Pow a' := by linarith
  have haA : a ∈ cellVertices ε η (ringShell (latticePt h m' n') (sqrt2Pow a')) :=
    ⟨xa, hxa, hshell xa hxa1 hxa2⟩
  have hyA : y ∈ cellVertices ε η (ringShell (latticePt h m' n') (sqrt2Pow a')) :=
    ⟨xy, hxy, hshell xy hxy1 hxy2⟩
  have key := mul_greenKernel_le_of_ringSeparation hε hη hlf hcons hedge hB hbB (a := y) (y := a)
    (p := p) hp.le (z := latticePt h m' n') (r₁ := sqrt2Pow a' / 4) (r₂ := 2 * sqrt2Pow a')
    (I₀ := ringBarrier ε η (latticePt h m' n') (sqrt2Pow a'))
    (A := cellVertices ε η (ringShell (latticePt h m' n') (sqrt2Pow a')))
    (subset_refl _) haA
    ⟨xa, hxa, by linarith, by linarith⟩ ⟨xy, hxy, by linarith, by linarith⟩
    ⟨vertexPoint ε η b, vertexPoint_mem_cell hε η b, hcellb _ (vertexPoint_mem_cell hε η b)⟩
    (fun k hk => by
      obtain ⟨x, hx, hxd⟩ := hout k hk
      exact ⟨x, hx, Or.inr hxd⟩)
    (hring' y hyA)
  calc greenKernel m (interiorCellVertices ε η (ball (0 : ℂ) ((1 + ρ) / 2))) a b
      = p⁻¹ * (p * greenKernel m (interiorCellVertices ε η (ball (0 : ℂ) ((1 + ρ) / 2))) a b) := by
        field_simp
    _ ≤ p⁻¹ * greenKernel m (interiorCellVertices ε η (ball (0 : ℂ) ((1 + ρ) / 2))) y b :=
        mul_le_mul_of_nonneg_left key (inv_nonneg.2 hp.le)

end MatedCRT
