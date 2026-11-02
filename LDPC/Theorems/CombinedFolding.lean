module

public import LDPC.PaperLemmas.CombinedFolding
public import LDPC.PaperLemmas.Applications

/-! The standard Ligero test, retaining its |R|/|F| folding error.
The shared-query alternative is in Theorems.SharedQueries. -/
@[expose] public section
open scoped ProbabilityTheory
namespace SmoothLDPC.Protocol
attribute [local instance] Classical.propDecidable

variable {L R F : Type} [Fintype L] [DecidableEq L] [Nonempty L]
    [Fintype R] [DecidableEq R] [Nonempty R]
    [Field F] [DecidableEq F] [Fintype F] {G : TannerGraph L R}

omit [Nonempty R] [Fintype F] in
/-- A claimed codeword fixed before the coordinate samples survives only by
being a close fold, or by all samples missing the disagreement set. -/
theorem fold_only_response_probability_le (H : G.WeightedSystem F) {θ : ℚ}
    (hθn : θ ≤ Fintype.card L) (u v : L → F) (response : F → L → F)
    (r : F) (Q : ℕ) :
    Pr_{let sample ← $ᵖ (Fin Q → L)}[FoldOnlyAccept H u v response r sample] ≤
      (if GoodFold H.code θ u v r then 1 else 0) +
        ENNReal.ofReal (1 - (θ : ℝ) / Fintype.card L)^Q := by
  classical
  by_cases hg : GoodFold H.code θ u v r
  · simp only [hg, if_true]
    exact (Probability.prob_le_one _ _).trans le_self_add
  · simp only [hg, if_false, zero_add]
    by_cases hc : response r ∈ H.code
    · have hfar : θ ≤ (distance (u + r • v) (response r) : ℚ) := by
        by_contra hn
        exact hg ⟨response r, hc, lt_of_not_ge hn⟩
      let B := support (u + r • v - response r)
      have himp : ∀ sample : Fin Q → L, FoldOnlyAccept H u v response r sample →
          ∀ q, sample q ∈ Finset.univ \ B := by
        intro sample h q
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
        intro hi
        have hne : u (sample q) + r * v (sample q) ≠ response r (sample q) := by
          simpa [B, mem_support, sub_eq_zero, smul_eq_mul] using hi
        exact hne (h.2 q)
      have hmiss := miss_checks_le B (θ / Fintype.card L)
        ((div_le_one (by positivity)).mpr hθn)
        (by rwa [div_mul_cancel₀ _ (by positivity)]) Q
      have hbound := (Probability.Pr_le_Pr_of_implies ($ᵖ (Fin Q → L)) _ _ himp).trans hmiss
      simpa only [Rat.cast_div, Rat.cast_natCast] using hbound
    · rw [Probability.prob_eq_zero_of_forall_not ($ᵖ (Fin Q → L))
        (fun sample => FoldOnlyAccept H u v response r sample) (fun _ h => hc h.1)]
      positivity

/-- The original coordinate-only verifier, with the paper's explicit |R|/|F| term. -/
theorem fold_only_soundness_of_smooth (H : G.WeightedSystem F)
    {c k : ℕ} {α P ρ θ : ℚ}
    (hreg : G.IsRegular c k) (hc : 0 < c) (hs : IsSmooth H α P ρ)
    (hθ : θ ≤ ρ) (hθn : θ ≤ Fintype.card L)
    (hthreshold : (c : ℚ) * θ ≤ α * Fintype.card R)
    (u v : L → F) (hfar : PairFar H.code P u v)
    (response : F → L → F) (Q : ℕ) :
    Pr_{let r ← $ᵖ F; let sample ← $ᵖ (Fin Q → L)}[
      FoldOnlyAccept H u v response r sample] ≤
      (Fintype.card R : ENNReal) / Fintype.card F +
        ENNReal.ofReal (1 - (θ : ℝ) / Fintype.card L)^Q := by
  classical
  let g : F → ENNReal := fun r =>
    Pr_{let sample ← $ᵖ (Fin Q → L)}[FoldOnlyAccept H u v response r sample]
  have hsplit : Pr_{let r ← $ᵖ F; let sample ← $ᵖ (Fin Q → L)}[
      FoldOnlyAccept H u v response r sample] = ∑' r, ($ᵖ F) r * g r :=
    Probability.prob_tsum_form_split_first _ _
  rw [hsplit]
  apply (Probability.tsum_prob_le_add ($ᵖ F) g (GoodFold H.code θ u v) _
    (fun r => fold_only_response_probability_le H hθn u v response r Q)).trans
  exact add_le_add (combined_folding_of_smooth H hreg hc hs hθ hthreshold u v hfar) le_rfl

/-- Integer-cutoff variant of the main folding theorem. -/
theorem combined_folding_paper_parameters (H : G.WeightedSystem F)
    {c k K : ℕ} {γ δ ε : ℚ}
    (hG : G.IsExpander c k γ δ) (hc : 0 < c) (hk : 0 < k) (hKpos : 0 < K)
    (hγ0 : 0 ≤ γ) (hε0 : 0 < ε) (hε : ε < 1 - 3 * γ)
    (hK : (K : ℚ) ≤ δ * Fintype.card L)
    (u v : L → F) (hfar : PairFar H.code ((1 - γ) * K) u v) :
    Pr_{let r ← $ᵖ F}[
      GoodFold H.code ((1 - 3 * γ - ε) * ((1 - γ) * K)) u v r] ≤
      (Fintype.card R : ENNReal) / Fintype.card F := by
  have hτ := ligero_threshold_choice γ ε hε0 hε
  have hα := ligero_alpha_choice γ ε (Fintype.card L) k K
    Fintype.card_pos hk hKpos hε0 hε
  have hs := proposition_7 hG hc hγ0 hτ.1 hτ.2 hK hα.2 H
  apply combined_folding_of_smooth H hG.toIsRegular hc hs ?_ ?_ u v hfar
  · have hρ : (0 : ℚ) ≤ (1 - γ) * K := mul_nonneg (by linarith) (by positivity)
    exact mul_le_of_le_one_left hρ (by linarith)
  · have hscale := G.regular_scale hG.toIsRegular ((1 - 3 * γ - ε) * ((1 - γ) * K))
    have heq : (c : ℚ) * ((1 - 3 * γ - ε) * ((1 - γ) * K)) =
        ((1 - 3 * γ - ε) * k * ((1 - γ) * K) / Fintype.card L) * Fintype.card R := by
      calc
        _ = (((k : ℚ) * ((1 - 3 * γ - ε) * ((1 - γ) * K)) / Fintype.card L) *
            Fintype.card R) := hscale.symm
        _ = _ := by ring
    exact heq.le

end SmoothLDPC.Protocol
