import MatedCRT.FirstPass.Derived.SrwRingAssembly
import MatedCRT.FirstPass.Derived.SrwRingGeometry
import MatedCRT.FirstPass.Derived.HarnackRingGeometry

/-!
# The per-pair ring estimate on a sphere

Berestycki–Gwynne (2020), Lemma 3.10 in the form (3.21), specialised to the data that the Harnack inequality for the
Green function needs.  Fix a sphere `∂B_s(z)`, a grid centre `z'` with `|z - z'| ≤ h` and the grid circles of radii
`a ∈ [s - 3h, s - 2h)`, `b ∈ (s + 2h, s + 3h]` around `z'` (`exists_ringGrid` picks lattice data of mesh `h`), where
`δ ≤ h` bounds the diameter of the cells near the sphere and `300 h ≤ s`.
For a barrier `I = P ∪ O` consisting of cells inside `B_{a/4}(z')` and cells having a point farther than `T` from `z'`,
the per-pair estimate (`srwLaw_ringPair_lower`) gives, for every pair of vertices `x, y` whose cells meet the sphere,
the lower bound `p₀ p₁` for the probability that the trace of simple random walk from `x` before the first visit to
`I` separates `y` from `I`, provided the edge-end walk follows a polar template itinerary from the vertices meeting the
two grid circles with probability at least `p₀`, and satisfies the event of Lemma 3.11 from the vertices meeting
`B_{s/5}(w)`, `w ∈ ∂B_s(z)`, with probability at least `p₁`.
-/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Set Metric
open scoped ENNReal
open MatedCRTHarmonic MatedCRTHarmonic.HarmonicInfinity MatedCRTHarmonic.Markov MatedCRTHarmonic.CellFamily
open MatedCRTHarmonic.GMSMain.T15A

section Sphere

variable {ε : ℝ} {ω : MatedCRTHarmonic.MatedCRT.Path2} (h : MatedCRTHarmonic.MatedCRT.IsLocallyFinite ε ω)
include h

/-- **The per-pair ring estimate for two vertices of a sphere** (see the module documentation). -/
theorem srwLaw_ringPair_lower_sphere (hε : 0 ≤ ε) {o : ℤ}
    (H : CellularEmbedding (MatedCRTHarmonic.MatedCRT.graph ε ω h) o)
    (hlf : IsLocallyFiniteMult (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2)))
    (hcons : ∀ k : ℤ, bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2) k (k + 1) ≠ 0)
    {z z' : ℂ} {s h₀ δ T a b : ℝ} (hh : 0 < h₀) (hδ : 0 ≤ δ) (hδh : δ ≤ h₀) (hhs : 300 * h₀ ≤ s)
    (ha1 : s - 3 * h₀ ≤ a) (ha2 : a < s - 2 * h₀) (hb1 : s + 2 * h₀ < b) (hb2 : b ≤ s + 3 * h₀)
    (hzz : dist z z' ≤ h₀)
    (hdiam : ∀ k, (H.cell k ∩ ball z' (6 * b / 5)).Nonempty →
      ∀ x ∈ H.cell k, ∀ x' ∈ H.cell k, dist x x' ≤ δ)
    {P O : Set ℤ} (hP : ∀ k ∈ P, ∀ q ∈ H.cell k, dist q z' ≤ a / 4)
    (hO : ∀ k ∈ O, ∃ q ∈ H.cell k, T < dist q z') (hT : 6 * b / 5 + δ ≤ T)
    (hT2 : 7 * s / 5 + h₀ ≤ T) {p₀ p₁ : ℝ≥0∞}
    (hItin : ∀ c, (c = a ∨ c = b) → ∀ y ∈ verticesMeeting H.cell (sphere z' c),
      p₀ ≤ (MatedCRTHarmonic.MatedCRT.graph ε ω h).walkLaw y
        {ξ | PolarTemplateItinerary H z' c ((MatedCRTHarmonic.MatedCRT.graph ε ω h).vertexPath ξ)})
    (h311 : ∀ w ∈ sphere z s, ∀ y ∈ verticesMeeting H.cell (ball w (s / 5)),
      p₁ ≤ (MatedCRTHarmonic.MatedCRT.graph ε ω h).walkLaw y
        {ξ | Lemma311Event (MatedCRTHarmonic.MatedCRT.graph ε ω h) H.cell w (s / 5)
          ((MatedCRTHarmonic.MatedCRT.graph ε ω h).vertexPath ξ)})
    {x y : ℤ} (hx : ∃ q ∈ H.cell x, dist q z = s) (hy : ∃ q ∈ H.cell y, dist q z = s) :
    p₀ * p₁ ≤ srwLaw (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2)) x
      {ξ | GraphSeparates (srwGraph (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2)))
        (traceBefore (id : ℤ → ℤ) (P ∪ O) ξ) {y} (P ∪ O)} := by
  obtain ⟨w, hwy, hwz⟩ := hy
  obtain ⟨q0, hq0x, hq0z⟩ := hx
  have hwz' : w ∈ sphere z s := mem_sphere.2 hwz
  have ha : 0 < a := by linarith
  have hab : a ≤ b := by linarith
  have hw1 : dist w z' ≤ s + h₀ := by
    have := dist_triangle w z z'
    linarith
  have hw2 : s - h₀ ≤ dist w z' := by
    have := dist_triangle w z' z
    rw [dist_comm z' z] at this
    linarith
  have hwn : ‖w - z'‖ = dist w z' := (dist_eq_norm w z').symm
  obtain ⟨hIcirc, hIann, hIfar⟩ := ringPair_barrier_geometry H (z' := z') (w := w) (a := a)
    (b := b) (r := s / 5) (δ := δ) (T := T) ha hab hδ hdiam hP hO hT (by rw [hwn]; linarith)
    (by rw [hwn]; linarith)
  have hxA : x ∈ LatticeProb.LQG.annulusCells H.cell z' a b := by
    have hq0' : dist q0 z' ≤ s + h₀ := by
      have := dist_triangle q0 z z'
      linarith
    have hq0'' : s - h₀ ≤ dist q0 z' := by
      have := dist_triangle q0 z' z
      rw [dist_comm z' z] at this
      linarith
    intro q hq
    have hd : dist q q0 ≤ δ := hdiam x ⟨q0, hq0x, mem_ball.2 (by linarith)⟩ q hq q0 hq0x
    have h1 := dist_triangle q q0 z'
    have h2 := dist_triangle q0 q z'
    rw [dist_comm q0 q] at h2
    constructor <;> linarith
  exact srwLaw_ringPair_lower h hε H hlf hcons (z' := z') (w := w) (a := a) (b := b)
    (r := s / 5) ha (by linarith) (by linarith) (by linarith) (by linarith) (by rw [hwn, abs_le]; constructor <;> linarith)
    (by rw [hwn, abs_le]; constructor <;> linarith) (finite_annulusCells H z' _ _) hIcirc hIann hIfar hItin
    (h311 w hwz') hxA hwy

end Sphere

/-- **Grid data for the ring estimate**: a lattice centre of mesh `h` within `h` of `z`, and integer radii `h ℓ_a`,
`h ℓ_b` in the windows `[s - 3h, s - 2h)` and `(s + 2h, s + 3h]`. -/
theorem exists_ringGrid {h₀ : ℝ} (hh : 0 < h₀) (z : ℂ) (s : ℝ) :
    ∃ m n la lb : ℤ, dist z (latticePt h₀ m n) ≤ h₀ ∧ s - 3 * h₀ ≤ h₀ * la ∧ h₀ * la < s - 2 * h₀ ∧
      s + 2 * h₀ < h₀ * lb ∧ h₀ * lb ≤ s + 3 * h₀ := by
  obtain ⟨m, n, hmn⟩ := LatticeProb.exists_lattice_point_norm_sub_le hh z
  refine ⟨m, n, ⌈(s - 3 * h₀) / h₀⌉, ⌊(s + 3 * h₀) / h₀⌋, by rw [dist_eq_norm]; exact hmn, ?_, ?_, ?_, ?_⟩
  · have h1 := Int.le_ceil ((s - 3 * h₀) / h₀)
    rw [div_le_iff₀ hh] at h1
    linarith
  · have h1 := Int.ceil_lt_add_one ((s - 3 * h₀) / h₀)
    have h2 := mul_lt_mul_of_pos_right h1 hh
    have h3 : ((s - 3 * h₀) / h₀ + 1) * h₀ = s - 2 * h₀ := by field_simp; ring
    linarith
  · have h1 := Int.sub_one_lt_floor ((s + 3 * h₀) / h₀)
    have h2 := mul_lt_mul_of_pos_right h1 hh
    have h3 : ((s + 3 * h₀) / h₀ - 1) * h₀ = s + 2 * h₀ := by field_simp; ring
    linarith
  · have h1 := Int.floor_le ((s + 3 * h₀) / h₀)
    rw [le_div_iff₀ hh] at h1
    linarith

end MatedCRT

#print axioms MatedCRT.srwLaw_ringPair_lower_sphere
#print axioms MatedCRT.exists_ringGrid
