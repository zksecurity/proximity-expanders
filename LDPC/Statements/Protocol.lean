module

public import LDPC.Statements.MCA

/-! The information-theoretic verifier after the inputs are fixed by commitment.
A response is chosen from the field challenge, before either query sample.
Code membership is checked exactly; commitment binding and the implementation
of that membership check are outside this experiment. -/

@[expose] public section
open scoped ProbabilityTheory
namespace SmoothLDPC.Protocol

variable {L R F : Type} [Fintype L] [DecidableEq L]
    [Fintype R] [DecidableEq R] [Field F] [DecidableEq F]
    {G : TannerGraph L R}

/-- All coordinate samples agree with the claimed fold. -/
def spotAccept (u v : L → F) (r : F) (claimed : L → F)
    {Q : ℕ} (sample : Fin Q → L) : Prop :=
  ∀ i, u (sample i) + r * v (sample i) = claimed (sample i)

/-- The verifier tests both input columns at sampled checks, exact code
membership of the response, and folding consistency at sampled coordinates. -/
def Accept (H : G.WeightedSystem F) (u v : L → F) (response : F → L → F)
    {Qp Qs : ℕ} (r : F) (checks : Fin Qp → R) (coords : Fin Qs → L) : Prop :=
  MCA.parityAccept H u v checks ∧ response r ∈ H.code ∧
    spotAccept u v r (response r) coords

/-- Uniform soundness over fixed inputs, every challenge-dependent response,
and both query budgets. The radius s is an absolute integer threshold. -/
def Soundness [Fintype F] [Nonempty L] [Nonempty R]
    (H : G.WeightedSystem F) (P : ℚ) (s t : ℕ) : Prop :=
  ∀ (u v : L → F), PairFar H.code P u v →
    ∀ (response : F → L → F) (Qp Qs : ℕ),
    Pr_{let r ← $ᵖ F; let samples ← $ᵖ ((Fin Qp → R) × (Fin Qs → L))}[
      Accept H u v response r samples.1 samples.2] ≤
      max ((Fintype.card F : ENNReal)⁻¹ +
        (((Fintype.card L - s : ℕ) : ENNReal) / Fintype.card L)^Qs)
        ((((Fintype.card R - t : ℕ) : ENNReal) / Fintype.card R)^Qp)

end SmoothLDPC.Protocol
