import MatedCRT.FirstPass.S2g.PlateauZero
import HarmonicBalls.Proofs.Sec5.SupersolutionScaling

/-!
# Deterministic scaling of the plateau radii (fp-S2h, z1, round 11)

CHATGPT-cone-good-set.md Section 5.3 (42)-(43), deterministic part. For `ν' = c • (dilation by k⁻¹)_* ν` the cluster
satisfies `cluster ν' R 0 (c t) = k⁻¹ • cluster ν (k R) 0 t` (HB `cluster_comp_real_smul`, Proofs/Sec5/SupersolutionScaling),
so the raw radii scale by `k⁻¹` and the disc radius by `k`.
-/

namespace MatedCRT

open MeasureTheory Metric Set
open scoped ENNReal Pointwise

/-- The raw radius of the cluster of `ν` in the real disc `B_R` at time `t` with pole `0` (CHATGPT (36), real radius). -/
noncomputable def rawRadiusR (ν : Measure ℂ) (R : ℝ) (t : ℝ) : ℝ :=
  sSup ((fun x : ℂ => ‖x‖) '' closure (HarmonicBalls.cluster ν R 0 t))

/-- Raw radii under the dilation `ν ↦ c • (k⁻¹ •)_* ν`: the time is multiplied by `c`, the disc by `k`, and the radius
is divided by `k`. -/
theorem rawRadiusR_smul {ν : Measure ℂ} {c k R t : ℝ} (hk : 0 < k) (hc : 0 < c) (ht : 0 ≤ t) :
    rawRadiusR (ENNReal.ofReal c • Measure.map (fun x : ℂ => k⁻¹ • x) ν) R (c * t) =
      k⁻¹ * rawRadiusR ν (k * R) t := by
  unfold rawRadiusR
  rw [HarmonicBalls.cluster_comp_real_smul (z := 0) hk hc ht, smul_zero]
  set S := HarmonicBalls.cluster ν (k * R) 0 t with hS
  have hpre : (fun x : ℂ => k • x) ⁻¹' S = (fun x : ℂ => k⁻¹ • x) '' S := by
    ext x
    constructor
    · intro hx
      exact ⟨k • x, hx, inv_smul_smul₀ hk.ne' x⟩
    · rintro ⟨y, hy, rfl⟩
      show k • (k⁻¹ • y) ∈ S
      rw [smul_inv_smul₀ hk.ne']
      exact hy
  have hcl : closure ((fun x : ℂ => k⁻¹ • x) '' S) = (fun x : ℂ => k⁻¹ • x) '' closure S :=
    ((Homeomorph.smulOfNeZero k⁻¹ (inv_ne_zero hk.ne')).image_closure S).symm
  have himg : (fun x : ℂ => ‖x‖) '' ((fun x : ℂ => k⁻¹ • x) '' closure S) =
      (fun y : ℝ => k⁻¹ • y) '' ((fun x : ℂ => ‖x‖) '' closure S) := by
    rw [Set.image_image, Set.image_image]
    congr 1
    funext x
    simp only [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hk, smul_eq_mul]
  rw [hpre, hcl, himg, Set.image_smul, Real.sSup_smul_of_nonneg (inv_nonneg.2 hk.le), smul_eq_mul]


/-- Time monotonicity of the clusters with pole `0` (HB Draft `ClusterMononeStmt`, Lemma 3.3, pathwise). -/
def ClusterMonoAt (ν : Measure ℂ) : Prop :=
  ∀ t₁ t₂ r : ℝ, 0 < t₁ → t₁ ≤ t₂ → 0 < r →
    HarmonicBalls.cluster ν r 0 t₁ ⊆ HarmonicBalls.cluster ν r 0 t₂

/-- Compatibility of the clusters across discs with pole `0` (HB Lemma 3.5, pathwise; HB Draft `ClusterCompatibilityStmt`). -/
def ClusterCompatAt (ν : Measure ℂ) : Prop :=
  ∀ t : ℝ, 0 < t → ∀ s₁ R : ℝ, 0 < s₁ → s₁ ≤ R → ∀ s₂ ∈ Icc s₁ R,
    closure (HarmonicBalls.cluster ν s₂ 0 t) ⊆ ball 0 s₁ →
      ∀ s ∈ Icc s₁ R, HarmonicBalls.cluster ν s 0 t = HarmonicBalls.cluster ν s₂ 0 t

theorem bddAbove_norm_closure_cluster (ν : Measure ℂ) (R t : ℝ) :
    BddAbove ((fun x : ℂ => ‖x‖) '' closure (HarmonicBalls.cluster ν R 0 t)) := by
  refine ⟨R, ?_⟩
  rintro y ⟨z, hz, rfl⟩
  have hsub : closure (HarmonicBalls.cluster ν R 0 t) ⊆ closedBall (0 : ℂ) R :=
    closure_minimal (fun y hy => mem_closedBall_zero_iff.2 (mem_ball_zero_iff.1 hy.1).le) isClosed_closedBall
  exact mem_closedBall_zero_iff.1 (hsub hz)

theorem norm_le_rawRadiusR {ν : Measure ℂ} {R t : ℝ} {x : ℂ}
    (hx : x ∈ closure (HarmonicBalls.cluster ν R 0 t)) : ‖x‖ ≤ rawRadiusR ν R t :=
  le_csSup (bddAbove_norm_closure_cluster ν R t) ⟨x, hx, rfl⟩

theorem rawRadiusR_nonneg (ν : Measure ℂ) (R t : ℝ) : 0 ≤ rawRadiusR ν R t :=
  Real.sSup_nonneg (by rintro _ ⟨x, _, rfl⟩; exact norm_nonneg x)

theorem zero_mem_cluster_of_pos (ν : Measure ℂ) {R t : ℝ} (hR : 0 < R) :
    (0 : ℂ) ∈ HarmonicBalls.cluster ν R 0 t :=
  ⟨mem_ball_self hR, Or.inl rfl⟩

theorem rawRadiusR_mono {ν : Measure ℂ} (hmono : ClusterMonoAt ν) {R t₁ t₂ : ℝ} (hR : 0 < R) (h1 : 0 < t₁)
    (h12 : t₁ ≤ t₂) : rawRadiusR ν R t₁ ≤ rawRadiusR ν R t₂ := by
  unfold rawRadiusR
  refine csSup_le_csSup (bddAbove_norm_closure_cluster ν R t₂) ?_
    (Set.image_mono (closure_mono (hmono t₁ t₂ R h1 h12 hR)))
  exact ⟨‖(0 : ℂ)‖, Set.mem_image_of_mem _ (subset_closure (zero_mem_cluster_of_pos ν hR))⟩

theorem rawRadiusR_eq_of_compat {ν : Measure ℂ} (hcompat : ClusterCompatAt ν) {s₁ R s₂ t : ℝ} (ht : 0 < t)
    (hs₁ : 0 < s₁) (hs₁R : s₁ ≤ R) (hs₂ : s₂ ∈ Icc s₁ R) (hball : closure (HarmonicBalls.cluster ν s₂ 0 t) ⊆ ball 0 s₁)
    (s : ℝ) (hs : s ∈ Icc s₁ R) : rawRadiusR ν s t = rawRadiusR ν s₂ t := by
  unfold rawRadiusR
  rw [hcompat t ht s₁ R hs₁ hs₁R s₂ hs₂ hball s hs]

theorem rawRadius_eq_rawRadiusR (ν : Measure ℂ) (N : ℕ) (p : ℝ) : rawRadius ν N p = rawRadiusR ν N p := rfl

/-- Plateau radii under the dilation `ν ↦ c • (k⁻¹ •)_* ν` (CHATGPT (42)-(43), pathwise): `r` is a plateau radius of the
dilated measure exactly when `k r` is a plateau radius of `ν`, under the cluster monotonicity and compatibility of `ν`. -/
theorem mem_plateauRadii_smul_iff {ν : Measure ℂ} (hmono : ClusterMonoAt ν) (hcompat : ClusterCompatAt ν)
    {c k : ℝ} (hk : 0 < k) (hc : 0 < c) (r : ℝ) :
    r ∈ plateauRadii (ENNReal.ofReal c • Measure.map (fun x : ℂ => k⁻¹ • x) ν) ↔ k * r ∈ plateauRadii ν := by
  constructor
  · rintro ⟨N, hN, p, q, hp, hpq, hrN, hrp, hrq⟩
    have hp' : (0 : ℝ) < (p : ℝ) := hp
    have hq' : (0 : ℝ) < (q : ℝ) := lt_trans hp hpq
    have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hpc : (0 : ℝ) < (p : ℝ) / c := div_pos hp' hc
    have hqc : (0 : ℝ) < (q : ℝ) / c := div_pos hq' hc
    have hu : (p : ℝ) / c < (q : ℝ) / c := div_lt_div_of_pos_right hpq hc
    have hcp : c * ((p : ℝ) / c) = (p : ℝ) := by field_simp
    have hcq : c * ((q : ℝ) / c) = (q : ℝ) := by field_simp
    have e1 : rawRadiusR ν (k * N) ((p : ℝ) / c) = k * r := by
      have h := rawRadiusR_smul (ν := ν) (R := N) (t := (p : ℝ) / c) hk hc hpc.le
      rw [hcp] at h
      rw [rawRadius_eq_rawRadiusR] at hrp
      rw [← hrp, h]
      field_simp
    have e2 : rawRadiusR ν (k * N) ((q : ℝ) / c) = k * r := by
      have h := rawRadiusR_smul (ν := ν) (R := N) (t := (q : ℝ) / c) hk hc hqc.le
      rw [hcq] at h
      rw [rawRadius_eq_rawRadiusR] at hrq
      rw [← hrq, h]
      field_simp
    have hkr : 0 ≤ k * r := by rw [← e1]; exact rawRadiusR_nonneg _ _ _
    have hkN : 0 < k * (N : ℝ) := mul_pos hk hNr
    have hkrN' : k * r < k * (N : ℝ) := mul_lt_mul_of_pos_left hrN hk
    set N'' : ℕ := ⌈k * (N : ℝ)⌉₊ with hN''
    have hkN'' : k * (N : ℝ) ≤ (N'' : ℝ) := Nat.le_ceil _
    have hN''pos : 0 < N'' := Nat.ceil_pos.2 hkN
    have hN''R : (0 : ℝ) < (N'' : ℝ) := by exact_mod_cast hN''pos
    set s₁ : ℝ := (k * r + k * (N : ℝ)) / 2 with hs₁
    have hs₁pos : 0 < s₁ := by rw [hs₁]; linarith
    have hs₁lt : s₁ < k * (N : ℝ) := by rw [hs₁]; linarith
    have hball : ∀ u : ℝ, rawRadiusR ν (k * N) u = k * r → 0 < u →
        closure (HarmonicBalls.cluster ν (k * N) 0 u) ⊆ ball 0 s₁ := by
      intro u hu _ x hx
      rw [mem_ball_zero_iff]
      have := norm_le_rawRadiusR hx
      rw [hu] at this
      linarith
    have hr_upper : ∀ u : ℝ, 0 < u → rawRadiusR ν (k * N) u = k * r → rawRadiusR ν (N'' : ℝ) u = k * r := by
      intro u hu0 hu
      have hb := hball u hu hu0
      have hcomp := rawRadiusR_eq_of_compat hcompat hu0 hs₁pos (by linarith) ⟨hs₁lt.le, hkN''⟩ hb
        (N'' : ℝ) ⟨by linarith, le_rfl⟩
      rw [hcomp, hu]
    have hu1 := hr_upper ((p : ℝ) / c) hpc e1
    have hu2 := hr_upper ((q : ℝ) / c) hqc e2
    obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn hu
    obtain ⟨b, hb1, hb2⟩ := exists_rat_btwn ha2
    have hab : (a : ℝ) < (b : ℝ) := hb1
    have hapos : (0 : ℝ) < (a : ℝ) := lt_trans hpc ha1
    have hbpos : (0 : ℝ) < (b : ℝ) := lt_trans hapos hab
    have hNpos' : 0 < N'' := hN''pos
    have hRpos : (0 : ℝ) < (N'' : ℝ) := hN''R
    have ra : rawRadiusR ν (N'' : ℝ) (a : ℝ) = k * r := by
      apply le_antisymm
      · have h := rawRadiusR_mono hmono hRpos hapos ha2.le
        rw [hu2] at h
        exact h
      · have h := rawRadiusR_mono hmono hRpos hpc ha1.le
        rw [hu1] at h
        exact h
    have rb : rawRadiusR ν (N'' : ℝ) (b : ℝ) = k * r := by
      apply le_antisymm
      · have h := rawRadiusR_mono hmono hRpos hbpos hb2.le
        rw [hu2] at h
        exact h
      · have h := rawRadiusR_mono (t₂ := (b : ℝ)) hmono hRpos hpc (by linarith)
        rw [hu1] at h
        exact h
    refine ⟨N'', hNpos', a, b, hapos, hab, ?_, ?_, ?_⟩
    · linarith
    · rw [rawRadius_eq_rawRadiusR]; exact ra
    · rw [rawRadius_eq_rawRadiusR]; exact rb
  · rintro ⟨N, hN, p, q, hp, hpq, hkrN, hkp, hkq⟩
    rw [rawRadius_eq_rawRadiusR] at hkp hkq
    have hp' : (0 : ℝ) < (p : ℝ) := hp
    have hq' : (0 : ℝ) < (q : ℝ) := lt_trans hp hpq
    have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hkr0 : 0 ≤ k * r := by rw [← hkp]; exact rawRadiusR_nonneg _ _ _
    set N' : ℕ := ⌈(N : ℝ) / k⌉₊ with hN'
    have hN'ge : (N : ℝ) / k ≤ (N' : ℝ) := Nat.le_ceil _
    have hN'pos : 0 < N' := Nat.ceil_pos.2 (div_pos hNr hk)
    have hN'R : (0 : ℝ) < (N' : ℝ) := by exact_mod_cast hN'pos
    have hrN' : r < (N' : ℝ) := by
      have h1 : r < (N : ℝ) / k := by rw [lt_div_iff₀ hk]; linarith
      linarith
    have hNR' : (N : ℝ) ≤ k * (N' : ℝ) := by
      have h := (div_le_iff₀ hk).1 hN'ge
      linarith
    have hR'pos : 0 < k * (N' : ℝ) := mul_pos hk hN'R
    set s₁ : ℝ := (k * r + (N : ℝ)) / 2 with hs₁
    have hs₁pos : 0 < s₁ := by rw [hs₁]; linarith
    have hs₁lt : s₁ < (N : ℝ) := by rw [hs₁]; linarith
    have hs₁R : s₁ ≤ k * (N' : ℝ) := by linarith
    have hball : ∀ u : ℝ, rawRadiusR ν N u = k * r →
        closure (HarmonicBalls.cluster ν (N : ℝ) 0 u) ⊆ ball 0 s₁ := by
      intro u hu x hx
      rw [mem_ball_zero_iff]
      have h := norm_le_rawRadiusR hx
      rw [hu] at h
      linarith
    have hup : ∀ u : ℝ, 0 < u → rawRadiusR ν N u = k * r →
        rawRadiusR ν (k * (N' : ℝ)) u = k * r := by
      intro u hu0 hu
      have hc := rawRadiusR_eq_of_compat (s₂ := (N : ℝ)) (t := u) hcompat hu0 hs₁pos hs₁R
        ⟨hs₁lt.le, hNR'⟩ (hball u hu) (k * (N' : ℝ)) ⟨hs₁R, le_rfl⟩
      rw [hc, hu]
    have hp_up := hup p hp' hkp
    have hq_up := hup q hq' hkq
    have hcpq : c * (p : ℝ) < c * (q : ℝ) := mul_lt_mul_of_pos_left hpq hc
    obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn hcpq
    obtain ⟨b, hb1, hb2⟩ := exists_rat_btwn ha2
    have hab : (a : ℝ) < (b : ℝ) := hb1
    have hcp0 : 0 < c * (p : ℝ) := mul_pos hc hp'
    have hapos : (0 : ℝ) < (a : ℝ) := lt_trans hcp0 ha1
    have hbpos : (0 : ℝ) < (b : ℝ) := lt_trans hapos hab
    have hua : (p : ℝ) < (a : ℝ) / c := by rw [lt_div_iff₀ hc]; linarith [mul_comm c (p : ℝ)]
    have hua' : (a : ℝ) / c < (q : ℝ) := by rw [div_lt_iff₀ hc]; linarith [mul_comm c (q : ℝ)]
    have hub : (p : ℝ) < (b : ℝ) / c := by rw [lt_div_iff₀ hc]; linarith [mul_comm c (p : ℝ)]
    have hub' : (b : ℝ) / c < (q : ℝ) := by rw [div_lt_iff₀ hc]; linarith [mul_comm c (q : ℝ)]
    have ra_mid : rawRadiusR ν (k * (N' : ℝ)) ((a : ℝ) / c) = k * r := by
      apply le_antisymm
      · have h := rawRadiusR_mono hmono hR'pos (div_pos hapos hc) hua'.le
        rw [hq_up] at h
        exact h
      · have h := rawRadiusR_mono hmono hR'pos hp' hua.le
        rw [hp_up] at h
        exact h
    have rb_mid : rawRadiusR ν (k * (N' : ℝ)) ((b : ℝ) / c) = k * r := by
      apply le_antisymm
      · have h := rawRadiusR_mono hmono hR'pos (div_pos hbpos hc) hub'.le
        rw [hq_up] at h
        exact h
      · have h := rawRadiusR_mono hmono hR'pos hp' hub.le
        rw [hp_up] at h
        exact h
    have hnu_a : rawRadiusR (ENNReal.ofReal c • Measure.map (fun x : ℂ => k⁻¹ • x) ν) (N' : ℝ) (a : ℝ) = r := by
      have h := rawRadiusR_smul (ν := ν) (R := (N' : ℝ)) (t := (a : ℝ) / c) hk hc (div_pos hapos hc).le
      have hca : c * ((a : ℝ) / c) = (a : ℝ) := by field_simp
      rw [hca] at h
      rw [h, ra_mid, ← mul_assoc, inv_mul_cancel₀ hk.ne', one_mul]
    have hnu_b : rawRadiusR (ENNReal.ofReal c • Measure.map (fun x : ℂ => k⁻¹ • x) ν) (N' : ℝ) (b : ℝ) = r := by
      have h := rawRadiusR_smul (ν := ν) (R := (N' : ℝ)) (t := (b : ℝ) / c) hk hc (div_pos hbpos hc).le
      have hcb : c * ((b : ℝ) / c) = (b : ℝ) := by field_simp
      rw [hcb] at h
      rw [h, rb_mid, ← mul_assoc, inv_mul_cancel₀ hk.ne', one_mul]
    refine ⟨N', hN'pos, a, b, hapos, hab, hrN', ?_, ?_⟩
    · rw [rawRadius_eq_rawRadiusR]
      exact hnu_a
    · rw [rawRadius_eq_rawRadiusR]
      exact hnu_b

end MatedCRT
