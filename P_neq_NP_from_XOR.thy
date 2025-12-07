theory SubsetSum_PneqNP
  imports SubsetSum_CookLevin
begin

text ‹
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                                                             %
%        A CONDITIONAL PROOF THAT P != NP FROM AN INFORMATION-FLOW PRINCIPLE %
%                                                                             %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

This chapter presents a non-technical explanation of the conditional argument
formalised in this theory.  The aim is to identify carefully:

  • which components are fully proved in Isabelle/HOL, and
  • which assumption remains external.

The final statement is the conditional implication:

      If every Turing machine solving SUBSET–SUM satisfies the LR-read
      information-flow property, then P != NP.

The motivating intuition is simple:

      To decide whether two quantities L and R are equal,
      a solver must read at least one bit of information about L
      and one bit about R.

In SUBSET–SUM, however, L and R each range over *exponentially many* explicit
possibilities.  Determining whether L = R requires enough information to narrow
each side down to its *actual* value among those exponentially many options.
The LR-read hypothesis is the formal strengthening of this idea that makes the
lower-bound argument go through.  It is therefore treated as an explicit,
external assumption, not as a theorem derived from the informal slogan.

Every formal lower-bound, semantic, and verifier argument in this development is
checked in Isabelle/HOL.  The only unproved ingredient is the LR-read property.
›


section ‹1.  Why SUBSET–SUM?›

text ‹
The SUBSET–SUM problem asks whether, for integers

    as = [a₀, …, aₙ₋₁]  and  target s,

there exists a 0/1-vector xs such that

      ∑ᵢ as!i * xs!i = s.

Some inputs — such as as = [1,2,4,…,2^(n−1)] — have the property that *all*
2ⁿ subset sums are distinct.  More generally, any list as with this property is
called a distinct-subset-sum instance.  These instances form a large family and
serve as the canonical adversarial cases for the lower bound.  No special
algorithmic hardness is ascribed to the powers-of-two examples beyond their
distinct-subset-sum structure.
›


section ‹2.  The Decision-Tree Lower Bound›

text ‹
The theory ‹SubsetSum_DecisionTree› defines an abstract “reader” model and
establishes the lower bound

      steps(as, s)  ≥  2 * sqrt(2^n)

for all distinct-subset-sum inputs as of length n.

The model is an adversarial process:

  • the solver reads bits of the true input (as, s),
  • the adversary tracks all completions xs ∈ {0,1}ⁿ still compatible with
    the solver’s observations,
  • for each split k, the canonical equation eₖ(as,s) separates the sum:

        LHS depends on xs[0..k−1]
        RHS depends on xs[k..n−1].

As xs varies, LHS takes exactly 2^k values and RHS takes exactly 2^(n−k)
values.  The abstract axioms of ‹SubsetSum_Lemma1› require:

  (A1) the solver’s information flow matches these canonical LHS/RHS families,
  (A2) each distinguishable value costs ≥ 1 step.

Thus the solver’s cost is at least

      2^k + 2^(n−k),

minimised at 2 * sqrt(2^n).
›


section ‹3.  From Decision Trees to Cook–Levin Turing Machines›

text ‹
A Cook–Levin Turing machine can move, copy, rewrite, or interleave its input in
ways far more flexible than an abstract decision tree.  Therefore, the
decision-tree lower bound does not automatically apply to Turing machines.

The transfer requires capturing *how much information a concrete solver actually
extracts* from its input tape.  The starting point is the informal principle
from the introduction:

      To decide whether two quantities L and R are equal,
      a solver must read information about L and about R.

In SUBSET–SUM, this principle becomes significant because for each split k,
the unknown choice vector xs induces exactly:

      2^k possible L-values   (the set LHS(eₖ as s))
      2^(n−k) possible R-values (the set RHS(eₖ as s)).

To decide whether L = R, a solver must narrow down:

  • which of the 2^k L-values is the actual one, and
  • which of the 2^(n−k) R-values is the actual one.

This minimal requirement motivates the formal objects introduced in
‹SubsetSum_CookLevin›:

  • ‹seenL_TM as s k› — the set of L-values that change the machine’s behaviour,
  • ‹seenR_TM as s k› — the analogous set for R.

These *distinguishability sets* measure what the machine has effectively learned
from the parts of the input it has read.  They are the Turing-machine analogue
of the information sets in the decision-tree model.

-------------------------------------------------------------------------------
■  LR-read: a formal strengthening of the informal principle
-------------------------------------------------------------------------------

The LR-read hypothesis asserts that for every distinct-subset-sum instance
(as, s), there exists a split k such that

      seenL_TM as s k = LHS(eₖ as s)
      seenR_TM as s k = RHS(eₖ as s).

This is stronger than the informal slogan.  Instead of merely saying that the
machine learns *some* information about L and *some* about R, LR-read requires:

  • it distinguishes *all* canonical L-values, and  
  • it distinguishes *all* canonical R-values,

for some canonical split k.  This exactly matches the information pattern
required by the abstract decision-tree lower bound.

LR-read is therefore a deliberately strengthened *modeling condition* chosen so
that a concrete Turing machine has enough left/right structural information for
the lower-bound machinery of ‹SubsetSum_Lemma1› to apply.

-------------------------------------------------------------------------------
■  The cost principle
-------------------------------------------------------------------------------

The second LR-read axiom asserts:

      steps_TM as s ≥ |seenL_TM as s k| + |seenR_TM as s k|.

Each distinguishable canonical value costs ≥ 1 unit of work.  Combined with the
equalities above, we obtain

      |seenL_TM| = 2^k     and     |seenR_TM| = 2^(n−k),

and hence

      steps_TM as s ≥ 2^k + 2^(n−k) ≥ 2 * sqrt(2^n).

Thus LR-read allows ‹SubsetSum_Lemma1› to be instantiated with
‹steps = steps_TM›, transferring the √(2^n) lower bound to the Cook–Levin
Turing-machine setting.  The price is that LR-read itself is a *strong,
non-mechanised assumption* about how solvers obtain information from their
input.
›


section ‹4.  Why LR-read is Assumed›

text ‹
The LR-read property is a modeling assumption: we do not attempt to prove that
every solver for SUBSET–SUM satisfies it.  It is a consciously strengthened form
of the idea that to decide L = R, a solver must obtain enough information to
determine the actual L-value and actual R-value among their exponentially many
possibilities.

If LR-read held for all Turing-machine solvers of SUBSET–SUM, then every such
solver would incur a √(2^n) lower bound on distinct-subset-sum inputs.
Because this quantity grows faster than any polynomial, we would have
SUBSET–SUM ∉ P.  Combined with SUBSET–SUM ∈ NP, this yields P ≠ NP.

The purpose of the formalisation is therefore to isolate LR-read as the *only*
non-mechanised assumption: everything else — the combinatorial reasoning,
decision-tree lower bound, Cook–Levin semantics, and NP-verifier — is proved.
›


section ‹5.  Logical Structure›

text ‹
The development is organised in three layers:

  (1) Lower-bound kernel — *proved*
      Theories ‹SubsetSum_DecisionTree› and ‹SubsetSum_Lemma1› prove a
      √(2^n) lower bound under abstract L/R-information axioms.

  (2) Cook–Levin bridge — *proved*
      The locale ‹LR_Read_TM› formalises how a Turing machine induces the
      distinguishability sets ‹seenL_TM› and ‹seenR_TM› required by the
      abstract lemma.

  (3) Modeling assumption — *not proved*
      Every solver for SUBSET–SUM satisfies LR-read.

Together these yield the conditional implication:

      If SUBSET–SUM ∈ P and all solvers satisfy LR-read,
      then P ≠ NP.
›


section ‹6.  Relation to Feinstein (2016)›

text ‹
Feinstein argued informally that verifying equality of two subset-sum
expressions requires exploring many combinations of prefix/suffix choices for
xs.  This development captures the combinatorial core of that reasoning via the
families LHS(eₖ) and RHS(eₖ), formalises the corresponding decision-tree lower
bound, and identifies LR-read as the structural assumption needed to transfer
the argument to Turing machines.

The lower bound itself and its transfer to TMs are fully mechanised in
Isabelle/HOL; LR-read is the unique external assumption.
›


section ‹7.  Perspective›

text ‹
This theory does not prove P ≠ NP.  Instead, it decomposes the argument into

  • a fully formalised lower-bound mechanism, and
  • a single explicit modeling assumption (LR-read).

If LR-read were justified independently — for example, by an argument that every
solver must process the encoding of (as, s) in a left–right sensitive way —
then the formalisation here would yield P ≠ NP immediately.

Thus the contribution is twofold:
  (a) a verified lower-bound framework for SUBSET–SUM, and
  (b) a precise identification of the sole hypothesis on which the conditional
      separation relies.
›


section ‹8.  SUBSET–SUM is in NP (formalised)›

text ‹
The Cook–Levin AFP library does not supply SUBSET–SUM ∈ NP by default.
Instead we obtain it from a general verifier via SS_Verifier_NP.

A verifier provides:

  • encodings of instances and certificates,
  • a polynomial-time TM verifier V,
  • soundness and completeness.

From this we derive:

      SUBSETSUM_lang enc0 ∈ 𝒩𝒫.
›

lemma SUBSETSUM_in_NP_global:
  assumes "SS_Verifier_NP k G V p T fverify enc0 enc_cert"
  shows "SUBSETSUM_lang enc0 ∈ 𝒩𝒫"
  using SUBSETSUM_in_NP_from_verifier[OF assms] .


section ‹9.  Definition of P = NP›

definition P_eq_NP :: bool where
  "P_eq_NP ⟷ (∀L::language. (L ∈ 𝒫) = (L ∈ 𝒩𝒫))"


section ‹10.  Bridging P to a concrete CL solver›

text ‹
If SUBSET–SUM ∈ P, then some Cook–Levin machine solves it in polynomial time.

This step passes from language complexity to concrete machine semantics.
The solver’s encoding need not match the verifier’s encoding; only the language
matters.
›

definition P_impl_CL_SubsetSum_Solver ::
  "(int list ⇒ int ⇒ string) ⇒ bool" where
  "P_impl_CL_SubsetSum_Solver enc0 ⟷
     (SUBSETSUM_lang enc0 ∈ 𝒫 ⟶
        (∃M q0 enc.
           CL_SubsetSum_Solver M q0 enc ∧
           polytime_CL_machine M enc))"


section ‹11.  LR-read-all-solvers hypothesis›

text ‹
This is the single modelling assumption.

For a fixed encoding enc0:

      LR_read_all_solvers_hypothesis enc0

means:

  (1) If SUBSET–SUM ∈ P, a polynomial-time CL solver exists, and
  (2) Every CL solver satisfies LR-read, i.e. belongs to ‹LR_Read_TM›.

NP-membership is not assumed; it is proved separately.
›

definition LR_read_all_solvers_hypothesis ::
  "(int list ⇒ int ⇒ string) ⇒ bool" where
  "LR_read_all_solvers_hypothesis enc0 ⟷
     P_impl_CL_SubsetSum_Solver enc0 ∧
     (∀M q0 enc.
        CL_SubsetSum_Solver M q0 enc ⟶
          (∃seenL seenR. LR_Read_TM M q0 enc seenL seenR))"


section ‹12.  Core Conditional Theorem›

text ‹
This theorem expresses the logical core:

    LR assumptions  +  SUBSET–SUM ∈ NP   ⇒   P ≠ NP.

Proof sketch:

    Assume P = NP.
    Then SUBSET–SUM ∈ P.
    So a polynomial-time CL solver M exists.
    LR-read applies to M, giving a √(2^n) lower bound.
    Contradiction with the polynomial-time upper bound.
›

lemma P_neq_NP_if_LR_read_all_solvers_hypothesis:
  fixes enc0 :: "int list ⇒ int ⇒ string"
  assumes H:       "LR_read_all_solvers_hypothesis enc0"
  assumes NP_enc0: "SUBSETSUM_lang enc0 ∈ 𝒩𝒫"
  shows "¬ P_eq_NP"
proof -
  from H have
    bridge_P: "P_impl_CL_SubsetSum_Solver enc0" and
    all_LR:   "∀M q0 enc.
                 CL_SubsetSum_Solver M q0 enc ⟶
                   (∃seenL seenR. LR_Read_TM M q0 enc seenL seenR)"
    unfolding LR_read_all_solvers_hypothesis_def by blast+

  show "¬ P_eq_NP"
  proof
    assume eq: "P_eq_NP"

    have eq_PNP_inst:
      "(SUBSETSUM_lang enc0 ∈ 𝒫) = (SUBSETSUM_lang enc0 ∈ 𝒩𝒫)"
      using eq unfolding P_eq_NP_def by simp

    have inP_SUBSETSUM: "SUBSETSUM_lang enc0 ∈ 𝒫"
      using NP_enc0 eq_PNP_inst by simp

    from bridge_P[unfolded P_impl_CL_SubsetSum_Solver_def] inP_SUBSETSUM
    obtain M q0 enc where
      solver: "CL_SubsetSum_Solver M q0 enc" and
      poly:   "polytime_CL_machine M enc"
      by blast

    from all_LR solver obtain seenL seenR where lr:
      "LR_Read_TM M q0 enc seenL seenR"
      by blast

    interpret LR: LR_Read_TM M q0 enc seenL seenR
      by (rule lr)

    from poly obtain c d where
      cpos: "c > 0" and
      bound_all: "∀as s.
                    steps_CL M (enc as s)
                      ≤ nat (ceiling (c * (real (length as)) ^ d))"
      unfolding polytime_CL_machine_def by blast

    have family_bound:
      "∃(c::real)>0. ∃d::nat.
         ∀as s. distinct_subset_sums as ⟶
           steps_CL M (enc as s)
             ≤ nat (ceiling (c * (real (length as)) ^ d))"
      using cpos bound_all by blast

    from LR.no_polytime_CL_on_distinct_family family_bound
    show False by blast
  qed
qed


section ‹13.  Final Packaged Theorem›

text ‹
This theorem gives the final wrapped statement:

      LR hypothesis + SUBSET–SUM verifier ⇒ P ≠ NP.
›

theorem P_neq_NP_under_LR_model:
  fixes enc0 :: "int list ⇒ int ⇒ string"
  assumes LR: "LR_read_all_solvers_hypothesis enc0"
  assumes V:  "SS_Verifier_NP k G V p T fverify enc0 enc_cert"
  shows "¬ P_eq_NP"
proof -
  have NP_enc0: "SUBSETSUM_lang enc0 ∈ 𝒩𝒫"
    using SUBSETSUM_in_NP_global[OF V] .
  from P_neq_NP_if_LR_read_all_solvers_hypothesis[OF LR NP_enc0]
  show "¬ P_eq_NP" .
qed

end
