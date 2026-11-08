module

public import LDPC.Theorems.SharedQueries
public import LDPC.Theorems.CombinedFolding
public import LDPC.Theorems.Protocol

/-!
# Paper statements

Write n=|L|, m=|R| and d=2(1−γ)δn. The few-violations lemma gives radius d/2
and error 1/|F|. The main folding theorem removes that premise at radius
t=(1−3γ−ε)d/2 and error m/|F|. Check sampling retains radius d/2 and gives
error 1/|F|+(1−α)^Q. The margin γδn≥1 supplies the rounding conditions.
-/

@[expose] public section
open scoped ProbabilityTheory
namespace SmoothLDPC.Paper

variable {L R F : Type} [Fintype L] [Fintype R] [Fintype F]
    [Nonempty L] [Nonempty R] [DecidableEq L] [DecidableEq R]
    [Field F] [DecidableEq F] {G : TannerGraph L R}
    {c k : ℕ} {γ δ ε : ℚ}

/-- The main technical lemma: fixed jointly far inputs with few violated checks
have at most one strictly close fold at radius d/2=(1−γ)δn. -/
theorem main_technical_lemma [SampleableType F] (H : G.WeightedSystem F)
    (hG : G.IsExpander c k γ δ) (hc : 0 < c) (hγ0 : 0 ≤ γ)
    (hε0 : 0 < ε) (hε : ε < 1 - 3 * γ)
    (hmargin : 1 ≤ γ * (δ * Fintype.card L))
    (u v : L → F) (hfar : PairFar H.code ((1 - γ) * δ * Fintype.card L) u v)
    (hbad : ((H.badChecks u v).card : ℚ) ≤
      ((1 - 3 * γ - ε) * k * ((1 - γ) * δ * Fintype.card L) /
        Fintype.card L) * Fintype.card R) :
    Pr{let r ← $ᵗ F}[GoodFold H.code ((1 - γ) * δ * Fintype.card L) u v r] ≤
      (Fintype.card F : ENNReal)⁻¹ := by
  classical
  have hs := half_distance_smoothness hG hc hγ0
    (by linarith : γ < 1 - 2 * γ - ε)
    (by linarith : 1 - 2 * γ - ε < 1 - 2 * γ) hmargin H
  have hα : (1 - 2 * γ - ε - γ) * k *
      ((1 - γ) * δ * Fintype.card L) / Fintype.card L =
      (1 - 3 * γ - ε) * k * ((1 - γ) * δ * Fintype.card L) /
        Fintype.card L := by ring
  rw [hα] at hs
  exact prEvent_uniformSample_le_inv_of_card_le_one _
    (theorem_8_card H hs u v hfar hbad)

/-- The main folding theorem combines the few-check lemma with a union bound
on canceled checks. The two cases are fixed before the uniform challenge. -/
theorem folding [SampleableType F] (H : G.WeightedSystem F)
    (hG : G.IsExpander c k γ δ) (hc : 0 < c) (hγ0 : 0 ≤ γ)
    (hε0 : 0 < ε) (hε : ε < 1 - 3 * γ)
    (hmargin : 1 ≤ γ * (δ * Fintype.card L))
    (u v : L → F) (hfar : PairFar H.code ((1 - γ) * δ * Fintype.card L) u v) :
    Pr{let r ← $ᵗ F}[
      GoodFold H.code ((1 - 3 * γ - ε) * ((1 - γ) * δ * Fintype.card L)) u v r] ≤
      (Fintype.card R : ENNReal) / Fintype.card F := by
  have hs := half_distance_smoothness hG hc hγ0
    (by linarith : γ < 1 - 2 * γ - ε)
    (by linarith : 1 - 2 * γ - ε < 1 - 2 * γ) hmargin H
  apply Protocol.combined_folding_of_smooth H hG.toIsRegular hc hs ?_ ?_ u v hfar
  · have hx : 0 ≤ δ * Fintype.card L := by
      by_contra hn
      have hprod := mul_nonpos_of_nonneg_of_nonpos hγ0 (le_of_not_ge hn)
      linarith
    have hP : 0 ≤ (1 - γ) * δ * Fintype.card L := by
      have := mul_nonneg (show 0 ≤ 1 - γ by linarith) hx
      nlinarith
    exact mul_le_of_le_one_left hP (by linarith)
  · have hscale := G.regular_scale hG.toIsRegular
      ((1 - 3 * γ - ε) * ((1 - γ) * δ * Fintype.card L))
    have heq : (c : ℚ) * ((1 - 3 * γ - ε) * ((1 - γ) * δ * Fintype.card L)) =
        ((1 - 2 * γ - ε - γ) * k * ((1 - γ) * δ * Fintype.card L) /
          Fintype.card L) * Fintype.card R := by
      calc
        _ = _ := hscale.symm
        _ = _ := by ring
    exact heq.le

/-- The standard Ligero test uses the main folding radius t and Q independent
coordinate openings. The response precedes the coordinate samples. -/
theorem ligero [SampleableType F] [SampleableType L] (H : G.WeightedSystem F)
    (hG : G.IsExpander c k γ δ) (hc : 0 < c) (hγ0 : 0 ≤ γ)
    (hε0 : 0 < ε) (hε : ε < 1 - 3 * γ)
    (hmargin : 1 ≤ γ * (δ * Fintype.card L))
    (u v : L → F) (hfar : PairFar H.code ((1 - γ) * δ * Fintype.card L) u v)
    (response : F → L → F) (Q : ℕ) :
    Pr{let r ← $ᵗ F; let sample ← $ᵗ (Fin Q → L)}[
      Protocol.FoldOnlyAccept H u v response r sample] ≤
      (Fintype.card R : ENNReal) / Fintype.card F +
        ENNReal.ofReal (1 - (((1 - 3 * γ - ε) *
          ((1 - γ) * δ * Fintype.card L) : ℚ) : ℝ) / Fintype.card L)^Q := by
  classical
  let t : ℚ := (1 - 3 * γ - ε) * ((1 - γ) * δ * Fintype.card L)
  have hP : 0 ≤ (1 - γ) * δ * Fintype.card L := by
    have : 0 < (δ * Fintype.card L : ℚ) := by
      by_contra hn
      have hprod := mul_nonpos_of_nonneg_of_nonpos hγ0 (le_of_not_gt hn)
      linarith
    nlinarith
  have ht : t ≤ Fintype.card L :=
    (mul_le_of_le_one_left hP (by linarith)).trans hfar.radius_lt_card.le
  apply (prEvent_bind_bind_le_add_of_not ($ᵗ F) _ (GoodFold H.code t u v) _
    (ε := ENNReal.ofReal (1 - (t : ℝ) / Fintype.card L)^Q) fun r hr => by
      simpa only [hr, if_false, zero_add] using
        Protocol.fold_only_response_probability_le H ht u v response r Q).trans
  exact add_le_add (folding H hG hc hγ0 hε0 hε hmargin u v hfar) le_rfl


/-- Sampling constraints: the margin derives the ceiling condition, and one set
of neighborhood openings tests both parity and folding consistency. -/
theorem check_sampling (H : G.WeightedSystem F)
    (hG : G.IsExpander c k γ δ) (hc : 0 < c) (hγ0 : 0 ≤ γ)
    (hε0 : 0 < ε) (hε : ε < 1 - 3 * γ)
    (hmargin : 1 ≤ γ * (δ * Fintype.card L)) :
    Protocol.SharedSoundness H ((1 - γ) * δ * Fintype.card L)
      ((1 - 3 * γ - ε) * k * ((1 - γ) * δ * Fintype.card L) / Fintype.card L) := by
  let P : ℚ := (1 - γ) * δ * Fintype.card L
  let α : ℚ := (1 - 3 * γ - ε) * k * P / Fintype.card L
  change Protocol.SharedSoundness H P α
  let _ := SampleableType.ofFintype F; let _ := SampleableType.ofFintype R
  intro u v hfar response Q
  have hx : 0 ≤ δ * Fintype.card L := by
    by_contra hn
    have hprod := mul_nonpos_of_nonneg_of_nonpos hγ0 (le_of_not_ge hn)
    linarith
  have hP : 0 ≤ P := by
    dsimp only [P]
    simpa only [mul_assoc] using mul_nonneg (show 0 ≤ 1 - γ by linarith) hx
  have hceil : (Nat.ceil P : ℚ) ≤ δ * Fintype.card L := by
    have hnext := Nat.ceil_lt_add_one hP
    dsimp only [P] at hnext
    nlinarith
  have hs : IsSmooth H α P P := by
    have h := half_distance_smoothness hG hc hγ0
      (by linarith : γ < 1 - 2 * γ - ε)
      (by linarith : 1 - 2 * γ - ε < 1 - 2 * γ) hmargin H
    have heq : (1 - 2 * γ - ε - γ) * k *
        ((1 - γ) * δ * Fintype.card L) / Fintype.card L = α := by
      dsimp only [α, P]
      ring
    rwa [heq] at h
  have hscale : α * Fintype.card R = (1 - 3 * γ - ε) * c * P := by
    dsimp only [α]
    calc
      _ = ((k : ℚ) * ((1 - 3 * γ - ε) * P) / Fintype.card L) *
          Fintype.card R := by ring
      _ = _ := by rw [G.regular_scale hG.toIsRegular]; ring
  have hdetect : α * Fintype.card R ≤ (1 - γ) * c * P := by
    rw [hscale]
    have hcoef : 1 - 3 * γ - ε ≤ 1 - γ := by linarith
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_right hcoef (mul_nonneg (show (0 : ℚ) ≤ c by positivity) hP)
  -- A far pair forces P<n; no separate block-length hypothesis is needed.
  have hN : Nat.ceil P ≤ Fintype.card L := Nat.ceil_le.mpr hfar.radius_lt_card.le
  obtain ⟨S, _, hS⟩ := Finset.exists_subset_card_eq
    (show Nat.ceil P ≤ (Finset.univ : Finset L).card by simpa using hN)
  have hexp := hG.expansion S (by simpa [hS] using hceil)
  have hbound : (1 - γ) * c * P ≤ Fintype.card R := calc
    _ ≤ (1 - γ) * c * Nat.ceil P :=
      mul_le_mul_of_nonneg_left (Nat.le_ceil P)
        (mul_nonneg (by linarith) (by positivity))
    _ ≤ (G.neighborhood S).card := by simpa [hS] using hexp
    _ ≤ _ := by exact_mod_cast Finset.card_le_univ (G.neighborhood S)
  have hm : (0 : ℚ) < Fintype.card R := by exact_mod_cast Fintype.card_pos
  have hα : α ≤ 1 := by nlinarith [hdetect.trans hbound]
  exact (Protocol.shared_soundness_of_expansion H hG hs (by linarith) hα hceil hdetect)
    u v hfar response Q

/-- A hybrid verifier uses separate samples for input parity and uniform-column
fold consistency. Direct parity queries retain the half-distance radius without
requiring neighborhood sampling for the consistency test. This is an additional
consequence of the paper's technical lemma, not one of its stated protocols. -/
theorem hybrid_sampling [SampleableType F] [SampleableType R] [SampleableType L]
    (H : G.WeightedSystem F)
    (hG : G.IsExpander c k γ δ) (hc : 0 < c) (hγ0 : 0 ≤ γ)
    (hε0 : 0 < ε) (hε : ε < 1 - 3 * γ)
    (hmargin : 1 ≤ γ * (δ * Fintype.card L))
    (u v : L → F) (hfar : PairFar H.code ((1 - γ) * δ * Fintype.card L) u v)
    (response : F → L → F) (Qp Qs : ℕ) :
    Pr{let r ← $ᵗ F; let samples ← $ᵗ ((Fin Qp → R) × (Fin Qs → L))}[
      Protocol.Accept H u v response r samples.1 samples.2] ≤
      max ((Fintype.card F : ENNReal)⁻¹ +
        ENNReal.ofReal (1 - (((1 - γ) * δ * Fintype.card L : ℚ) : ℝ) /
          Fintype.card L)^Qs)
        (ENNReal.ofReal (1 - (((1 - 3 * γ - ε) * k *
          ((1 - γ) * δ * Fintype.card L) / Fintype.card L : ℚ) : ℝ))^Qp) := by
  classical
  let P : ℚ := (1 - γ) * δ * Fintype.card L
  let α : ℚ := (1 - 3 * γ - ε) * k * P / Fintype.card L
  by_cases hb : ((H.badChecks u v).card : ℚ) ≤ α * Fintype.card R
  · apply le_trans _ (le_max_left _ _)
    apply (prEvent_bind_bind_le_add_of_not ($ᵗ F) _ (GoodFold H.code P u v) _
      (ε := ENNReal.ofReal (1 - (P : ℝ) / Fintype.card L)^Qs) ?_).trans
    · exact add_le_add
        (main_technical_lemma H hG hc hγ0 hε0 hε hmargin u v hfar hb) le_rfl
    · intro r hr
      have hle := prEvent_mono
        ($ᵗ ((Fin Qp → R) × (Fin Qs → L)))
        (fun samples => Protocol.Accept H u v response r samples.1 samples.2)
        (fun samples => Protocol.FoldOnlyAccept H u v response r samples.2)
        (fun _ h => h.2)
      apply hle.trans
      rw [SampleableType.prEvent_uniformSample_prod]
      apply prEvent_bind_bind_le_of_forall_le
      intro checks
      have hr' : ¬ GoodFold H.code ((1 - γ) * δ * Fintype.card L) u v r := hr
      simpa only [hr', if_false, zero_add] using Protocol.fold_only_response_probability_le H
        hfar.radius_lt_card.le u v response r Qs
  · apply le_trans _ (le_max_right _ _)
    apply prEvent_bind_bind_le_of_forall_le
    intro r
    have hle := prEvent_mono
      ($ᵗ ((Fin Qp → R) × (Fin Qs → L)))
      (fun samples => Protocol.Accept H u v response r samples.1 samples.2)
      (fun samples => MCA.parityAccept H u v samples.1) (fun _ h => h.1)
    rw [SampleableType.prEvent_uniformSample_fst] at hle
    have hcount := Finset.card_le_univ (H.badChecks u v)
    have hm : (0 : ℚ) < Fintype.card R := by exact_mod_cast Fintype.card_pos
    have hα : α ≤ 1 := by
      have : ((H.badChecks u v).card : ℚ) ≤ Fintype.card R := by exact_mod_cast hcount
      nlinarith [lt_of_not_ge hb]
    exact hle.trans (Protocol.miss_checks_le (H.badChecks u v) α hα
      (le_of_not_ge hb) Qp)

end SmoothLDPC.Paper
