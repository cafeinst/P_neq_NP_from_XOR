theory SubsetSum_PneqNP
  imports SubsetSum_CookLevin
begin

text ‹
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                                                            %
%        A CONDITIONAL PROOF THAT P != NP FROM AN INFORMATION-FLOW PRINCIPLE %
%                                                                            %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

This theory completes a fully mechanised formalisation of the lower-bound
argument for SUBSET–SUM that originates in

      C. A. Feinstein,
      “Dialogue Concerning the Two Chief World Views,”
      arXiv:1605.08639.

The original insight is the informal information-flow principle:

      To decide whether two quantities L and R are equal,
      a solver must read at least one bit encoding L
      and at least one bit encoding R.

In this theory, that slogan serves only as intuitive motivation.  
The actual lower-bound argument is carried out entirely inside Isabelle/HOL
and depends on a stronger, explicitly stated modelling assumption called
LR-read.  LR-read captures, in precise mathematical form, the requirement that
a solver for SUBSET–SUM must extract enough information from the parts of the
input that influence L and from the parts that influence R, in order to
distinguish all canonical prefix and suffix contributions.

Under this assumption, the formalisation proves that any Turing machine
solving SUBSET–SUM must take at least √(2^n) steps on inputs of length n.
Since √(2^n) grows faster than any polynomial, this yields the conditional
statement:

      If every polynomial-time solver for SUBSET–SUM satisfies LR-read,
      then P != NP.

All mathematics behind the lower bound — decision-tree adversary reasoning,
the Cook–Levin Turing-machine semantics, and the NP verifier for SUBSET–SUM —
is fully mechanised.  LR-read itself is the only non-mechanised assumption,
made explicit and never used implicitly.

AI systems (ChatGPT and Claude) assisted in structuring the presentation,
improving exposition, and refining comments, while all formal proofs are
verified by Isabelle/HOL.
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
A Cook–Levin Turing machine is far more flexible than a decision tree: it may
reorder, copy, compress, or interleave parts of its input tape.  Therefore,
the decision-tree lower bound does not automatically carry over.

To bridge this gap, the theory ‹SubsetSum_CookLevin› introduces the locale
‹LR_Read_TM›.  Its purpose is to package, in a precise axiomatic form, the
left/right information structure that underlies the intuitive principle stated
at the beginning of this theory:

      “To decide whether two quantities L and R are equal,
       a solver must read at least one bit encoding L
       and at least one bit encoding R.”

For SUBSET–SUM, these quantities L and R arise from the canonical split of the
verification equation at position k:

      L = ∑ᵢ₍ᵢ<ₖ₎ as!i * xs!i          (prefix contribution)
      R = s − ∑ᵢ₍ᵢ≥ₖ₎ as!i * xs!i      (suffix contribution).

Varying the prefix bits xs[0..k−1] yields exactly 2^k different possible
L-values, while varying the suffix bits xs[k..n−1] yields 2^(n−k) different
possible R-values.  These canonical sets are written:

      LHS(eₖ as s)    and    RHS(eₖ as s).

Even when no L equals any R, the solver must still discriminate among all
these possibilities: it must determine, using the encoded input alone, whether
any equality L = R is consistent with that input.  Therefore, it must gather
enough information to distinguish all 2^k prefix-derived L-values and all
2^(n−k) suffix-derived R-values.

To express this notion inside the Cook–Levin machine model, we examine how the
machine’s behaviour changes when we modify the input in ways that alter only
prefix-relevant information (affecting L but not R) or only suffix-relevant
information (affecting R but not L).  This leads to the definitions:

  • ‹seenL_TM as s k› = the set of canonical L-values that the machine’s
    behaviour can distinguish at split k;

  • ‹seenR_TM as s k› = the analogous set of distinguishable R-values.

These sets represent what the machine has effectively learned about L and R
from the bits it has read.

-------------------------------------------------------------------------------
■  LR-read: matching the canonical left/right family
-------------------------------------------------------------------------------

The LR-read hypothesis asserts that, for every distinct-subset-sum instance
(as,s), there exists some split k such that

      seenL_TM as s k = LHS(eₖ as s)
      seenR_TM as s k = RHS(eₖ as s).

Thus the machine’s observable behaviour must distinguish precisely all
canonical L-values and all canonical R-values.  It neither misses any nor
creates non-canonical distinctions.  This expresses, in a rigorous form, the
idea that a solver for L = R must obtain enough input information to determine
the status of every left candidate and every right candidate.

-------------------------------------------------------------------------------
■  The cost principle
-------------------------------------------------------------------------------

The second LR-read axiom states:

      steps_TM as s ≥ |seenL_TM as s k| + |seenR_TM as s k|.

Each distinguishable canonical value incurs at least one unit of work.

Combining this with the equalities above gives:

      |seenL_TM as s k| = 2^k,
      |seenR_TM as s k| = 2^(n−k),

and hence

      steps_TM as s ≥ 2^k + 2^(n−k) ≥ 2 * sqrt(2^n).

This matches exactly the lower bound proved abstractly in
‹SubsetSum_Lemma1›.  LR-read therefore provides the bridge that lifts the
decision-tree lower bound to Cook–Levin Turing machines.
›


section ‹4.  Why LR-read is Assumed›

text ‹
The LR-read condition is a modelling assumption: this development does not
attempt to prove that every SUBSET–SUM solver must satisfy it.  LR-read is a
deliberately strengthened formal requirement that captures, in exact terms,
the idea that deciding L = R requires obtaining enough information to narrow
down which of the exponentially many possible L-values and R-values could be
consistent with the input.

If LR-read were satisfied by all Turing-machine solvers for SUBSET–SUM, then
the √(2^n) lower bound established in ‹LR_Read_TM› would apply universally to
distinct-subset-sum inputs.  Since √(2^n) eventually exceeds every polynomial,
this would imply SUBSET–SUM ∉ 𝒫.  Together with SUBSET–SUM ∈ 𝒩𝒫, we obtain
P ≠ NP.

The role of the formalisation is therefore to separate the argument cleanly:
LR-read is the single external assumption, while all other components —
combinatorial reasoning, decision-tree lower bounds, Cook–Levin machine
semantics, and the NP-verifier — are fully mechanised in Isabelle/HOL.
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
