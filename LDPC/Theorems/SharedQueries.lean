module

public import LDPC.PaperLemmas.SharedQueries
public import LDPC.PaperLemmas.Applications

/-! The paper's check-sampling verifier.
The response is fixed after the challenge and before the sampled checks.
The same openings serve parity and folding consistency. -/
@[expose] public section
open scoped ProbabilityTheory
namespace SmoothLDPC.Protocol

variable {L R F : Type} [Fintype L] [DecidableEq L] [Nonempty L]
    [Fintype R] [DecidableEq R] [Nonempty R]
    [Field F] [DecidableEq F] [Fintype F] {G : TannerGraph L R}

omit [Nonempty L] in
/-- The exact shared-query acceptance bound, with its graph detection interface explicit. -/
theorem shared_soundness_of_smooth (H : G.WeightedSystem F) {P ρ α : ℚ}
    (hs : IsSmooth H α P ρ) (hα : α ≤ 1)
    (hdetect : ∀ S : Finset L, ρ ≤ S.card → α * Fintype.card R ≤ (G.neighborhood S).card) :
    SharedSoundness H P α := by
  classical
  intro u v hfar response Q
  by_cases hb : ((H.badChecks u v).card : ℚ) ≤ α * Fintype.card R
  · let g : F → ENNReal := fun r =>
      Pr_{let sample ← $ᵖ (Fin Q → R)}[SharedAccept H u v response r sample]
    have hsplit : Pr_{let r ← $ᵖ F; let sample ← $ᵖ (Fin Q → R)}[
        SharedAccept H u v response r sample] = ∑' r, ($ᵖ F) r * g r :=
      LegacyProbability.prob_tsum_form_split_first _ _
    rw [hsplit]
    apply (LegacyProbability.tsum_prob_le_add ($ᵖ F) g (GoodFold H.code ρ u v) _
      (fun r => shared_response_probability_le H hα hdetect u v response r Q)).trans
    exact add_le_add
      (LegacyProbability.prob_uniform_le_inv_of_card_le_one _ (theorem_8_card H hs u v hfar hb)) le_rfl
  · have hmany := LegacyProbability.Pr_seq_le_of_forall_le ($ᵖ (Fin Q → R)) ($ᵖ F)
      (fun sample r => SharedAccept H u v response r sample)
      (fun r => shared_acceptance_le_of_many H hα u v (le_of_not_ge hb) response r Q)
    exact hmany.trans le_add_self

omit [Nonempty L] in
/-- Expansion supplies neighborhood detection at the paper's explicit ceiling condition. -/
theorem shared_soundness_of_expansion (H : G.WeightedSystem F) {c k : ℕ} {γ δ ρ α P : ℚ}
    (hG : G.IsExpander c k γ δ) (hs : IsSmooth H α P ρ)
    (hγ : γ ≤ 1) (hα : α ≤ 1)
    (hceil : (Nat.ceil ρ : ℚ) ≤ δ * Fintype.card L)
    (hdetect : α * Fintype.card R ≤ (1 - γ) * c * ρ) :
    SharedSoundness H P α :=
  shared_soundness_of_smooth H hs hα
    (neighborhood_detection_of_expansion hG hγ hceil hdetect)

/-- Integer-cutoff check-sampling parameters. The generic ceiling condition is
explicit here; Paper.check_sampling derives it from γδn≥1 at the unrounded radius. -/
theorem shared_query_paper_parameters (H : G.WeightedSystem F)
    {c k K : ℕ} {γ δ ε : ℚ}
    (hG : G.IsExpander c k γ δ) (hc : 0 < c) (hk : 0 < k) (hKpos : 0 < K)
    (hγ0 : 0 ≤ γ) (hε0 : 0 < ε) (hε : ε < 1 - 3 * γ)
    (hK : (K : ℚ) ≤ δ * Fintype.card L) (hKn : K ≤ Fintype.card L)
    (hceil : (Nat.ceil ((1 - γ) * K) : ℚ) ≤ δ * Fintype.card L) :
    SharedSoundness H ((1 - γ) * K)
      ((1 - 3 * γ - ε) * k * ((1 - γ) * K) / Fintype.card L) := by
  have hτ := ligero_threshold_choice γ ε hε0 hε
  have hα := ligero_alpha_choice γ ε (Fintype.card L) k K
    Fintype.card_pos hk hKpos hε0 hε
  have hs := proposition_7 hG hc hγ0 hτ.1 hτ.2 hK hα.2 H
  apply shared_soundness_of_expansion H hG hs (by linarith)
    (smoothness_alpha_lt_one hG hc hγ0 hτ.1 hτ.2 hK hKn hα.2).le hceil
  have hscale :
      ((1 - 3 * γ - ε) * k * ((1 - γ) * K) / Fintype.card L) * Fintype.card R =
        (1 - 3 * γ - ε) * c * ((1 - γ) * K) := by
    calc
      _ = (1 - 3 * γ - ε) *
          (((k : ℚ) * ((1 - γ) * K) / Fintype.card L) * Fintype.card R) := by ring
      _ = _ := by rw [G.regular_scale hG.toIsRegular]; ring
  rw [hscale]
  have hρ : (0 : ℚ) ≤ (1 - γ) * K := mul_nonneg (by linarith) (by positivity)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (by linarith : 1 - 3 * γ - ε ≤ 1 - γ) (by positivity)) hρ

end SmoothLDPC.Protocol
