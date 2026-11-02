module

public import LDPC.Helpers.SpotSampling
public import LDPC.Helpers.ParitySampling
public import LDPC.PaperLemmas.Folding

/-! Two-case verifier soundness: few violations use the structural gap;
many violations are detected on the original input columns, without a
union bound over parity-check cancellations in the fold. -/
@[expose] public section
open scoped ProbabilityTheory
namespace SmoothLDPC.Protocol
attribute [local instance] Classical.propDecidable

variable {L R F : Type} [Fintype L] [DecidableEq L] [Nonempty L]
    [Fintype R] [DecidableEq R] [Nonempty R]
    [Field F] [DecidableEq F] [Fintype F] {G : TannerGraph L R}

omit [Fintype F] [Nonempty L] [Nonempty R] [DecidableEq F] in
/-- Honest input codewords and their actual fold pass every possible query sample. -/
theorem accept_honest (H : G.WeightedSystem F) (u v : L → F)
    (hu : u ∈ H.code) (hv : v ∈ H.code) (r : F) {Qp Qs : ℕ}
    (checks : Fin Qp → R) (coords : Fin Qs → L) :
    Accept H u v (fun z => u + z • v) r checks coords := by
  have hucheck : H.check u = 0 := hu
  have hvcheck : H.check v = 0 := hv
  refine ⟨?_, H.code.add_mem hu (H.code.smul_mem r hv), ?_⟩
  · simp [MCA.parityAccept, TannerGraph.WeightedSystem.badChecks, hucheck, hvcheck]
  · intro i
    rfl

omit [Fintype F] in
/-- A fixed response that is not a close codeword must survive coordinate
sampling by missing at least s mismatches. -/
theorem response_probability_le (H : G.WeightedSystem F) (u v : L → F)
    (response : F → L → F) (r : F) (s Qp Qs : ℕ) :
    Pr_{let samples ← $ᵖ ((Fin Qp → R) × (Fin Qs → L))}[
      Accept H u v response r samples.1 samples.2] ≤
      (if GoodFold H.code s u v r then 1 else 0) +
        (((Fintype.card L - s : ℕ) : ENNReal) / Fintype.card L)^Qs := by
  classical
  by_cases hg : GoodFold H.code s u v r
  · simp only [hg, if_true]
    exact (Probability.prob_le_one _ _).trans (le_self_add)
  · simp only [hg, if_false, zero_add]
    rw [Probability.prob_split_uniform_sampling_of_prod]
    apply Probability.Pr_seq_le_of_forall_le
    intro checks
    by_cases hc : response r ∈ H.code
    · have hfar : s ≤ distance (u + r • v) (response r) := by
        by_contra hn
        apply hg
        exact ⟨response r, hc, by exact_mod_cast (Nat.lt_of_not_ge hn)⟩
      exact (Probability.Pr_le_Pr_of_implies ($ᵖ (Fin Qs → L))
        (fun coords => Accept H u v response r checks coords)
        (spotAccept u v r (response r)) (fun _ h => h.2.2)).trans
        (spotAccept_probability_le u v r (response r) Qs s hfar)
    · have hz := Probability.prob_eq_zero_of_forall_not ($ᵖ (Fin Qs → L))
        (fun coords => Accept H u v response r checks coords) (fun _ h => hc h.2.1)
      rw [hz]
      positivity

/-- Few violations give the one-seed folding error plus the spot-query error. -/
theorem acceptance_le_of_few (H : G.WeightedSystem F) {α P : ℚ} {s : ℕ}
    (hs : IsSmooth H α P s) (u v : L → F) (hfar : PairFar H.code P u v)
    (hbad : ((H.badChecks u v).card : ℚ) ≤ α * Fintype.card R)
    (response : F → L → F) (Qp Qs : ℕ) :
    Pr_{let r ← $ᵖ F; let samples ← $ᵖ ((Fin Qp → R) × (Fin Qs → L))}[
      Accept H u v response r samples.1 samples.2] ≤
      (Fintype.card F : ENNReal)⁻¹ +
        (((Fintype.card L - s : ℕ) : ENNReal) / Fintype.card L)^Qs := by
  classical
  let g : F → ENNReal := fun r =>
    Pr_{let samples ← $ᵖ ((Fin Qp → R) × (Fin Qs → L))}[
      Accept H u v response r samples.1 samples.2]
  have hsplit : Pr_{let r ← $ᵖ F; let samples ← $ᵖ ((Fin Qp → R) × (Fin Qs → L))}[
      Accept H u v response r samples.1 samples.2] =
      ∑' r, ($ᵖ F) r * g r := Probability.prob_tsum_form_split_first _ _
  rw [hsplit]
  apply (Probability.tsum_prob_le_add ($ᵖ F) g (GoodFold H.code s u v)
    _ (fun r => response_probability_le H u v response r s Qp Qs)).trans
  exact add_le_add
    (Probability.prob_uniform_le_inv_of_card_le_one _
      (theorem_8_card H hs u v hfar hbad)) le_rfl

omit [DecidableEq F] in
/-- Many violated checks are detected directly, regardless of the response. -/
theorem acceptance_le_of_many (H : G.WeightedSystem F) (u v : L → F)
    (response : F → L → F) (Qp Qs t : ℕ) (hb : t ≤ (H.badChecks u v).card) :
    Pr_{let r ← $ᵖ F; let samples ← $ᵖ ((Fin Qp → R) × (Fin Qs → L))}[
      Accept H u v response r samples.1 samples.2] ≤
      (((Fintype.card R - t : ℕ) : ENNReal) / Fintype.card R)^Qp := by
  classical
  apply Probability.Pr_seq_le_of_forall_le
  intro r
  have hle := Probability.Pr_le_Pr_of_implies
    ($ᵖ ((Fin Qp → R) × (Fin Qs → L)))
    (fun samples => Accept H u v response r samples.1 samples.2)
    (fun samples => MCA.parityAccept H u v samples.1) (fun _ h => h.1)
  rw [Probability.prob_marginalization_first_of_prod] at hle
  exact hle.trans (MCA.parityAccept_probability_le H u v Qp t hb)

end SmoothLDPC.Protocol
