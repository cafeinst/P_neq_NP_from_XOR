theory SubsetSum_PneqNP
  imports SubsetSum_CookLevin
begin

text ‹
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                                                             %
%      A CONDITIONAL PROOF THAT P ≠ NP FROM AN INFORMATION-FLOW PRINCIPLE     %
%                                                                             %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

This theory completes a mechanised formalisation of the lower-bound argument for
SUBSET–SUM originating in

    C. A. Feinstein,
    “Dialogue Concerning the Two Chief World Views,”
    arXiv:1605.08639.

The development begins from a simple and intuitively compelling information-flow
principle:

      To decide whether two quantities L and R are equal,
      a solver must obtain some information about L
      and some information about R.

In the SUBSET–SUM setting, this principle takes on a precise combinatorial form.
For each split position k, the canonical decomposition eₖ(as, s) rewrites the
verification equation into two independent collections of candidate contributions:

      LHS(eₖ as s)     of size 2^k,
      RHS(eₖ as s)     of size 2^(n − k),

arising respectively from all prefix-choices and all suffix-choices of the
unknown selection vector xs.  Determining whether a solution exists is
equivalent to determining whether these two sets intersect.

A crucial observation is that **each** element of LHS(eₖ) and **each** element of
RHS(eₖ) corresponds to a different feasible completion of xs.  Before the solver
has read the input, all such completions are consistent with the instance; none
may be discarded a priori.  Therefore, in the worst case, a correct solver must
acquire enough information to distinguish *every* canonical L-value and *every*
canonical R-value.  Otherwise, it cannot rule out the possibility that an
unexamined L equals an unexamined R.

This explains why the informal information principle forces the solver to
distinguish all canonical candidates: every undistinguished candidate is a live
possibility, and eliminating all possibilities except the true one requires
distinguishing them one by one.

When this informational requirement is expressed inside the Cook–Levin
Turing-machine framework, it becomes the LR-read property: a structural
assumption asserting that, for some split k, the machine’s observable behaviour
distinguishes exactly the canonical left and right candidate sets LHS(eₖ) and
RHS(eₖ).  LR-read is the single assumption needed to transfer the abstract
decision-tree lower bound to the Turing-machine model.

Under LR-read, the formalisation proves that any solver must take at least

      2 · sqrt(2^n)

steps on distinct-subset-sum inputs of length n.  Since this quantity grows
faster than any polynomial, we obtain the conditional implication:

      If every polynomial-time solver for SUBSET–SUM satisfies LR-read,
      then P ≠ NP.

All mathematical components except LR-read itself are fully mechanised in
Isabelle/HOL: the decision-tree adversary argument, the Cook–Levin machine
semantics (from the AFP’s Cook–Levin library), and the NP verifier for
SUBSET–SUM.  LR-read is the single explicit information-flow hypothesis that
links these components.

AI systems (ChatGPT and Claude) assisted in improving the exposition and
organisation of the informal text; all formal proofs are verified by Isabelle/HOL.
›


section ‹1.  Why SUBSET–SUM?›

text ‹
Our interest in SUBSET–SUM begins with a basic information principle:

      To decide whether two quantities L and R are equal,
      a solver must obtain some information about L
      and some information about R.

In SUBSET–SUM, each 0/1-choice vector xs determines the value

      ∑ᵢ as!i * xs!i,

and for distinct-subset-sum instances these values are all different.
Thus each xs represents a *distinct candidate contribution* to the equation.

Splitting the sum at a position k separates these contributions into two
canonical candidate families:

      LHS(eₖ as s)    determined by xs[0..k−1],
      RHS(eₖ as s)    determined by xs[k..n−1].

If we treat the elements of LHS(eₖ) and RHS(eₖ) as *independent candidates*,
then solvability at split k is equivalent to asking whether these two sets
intersect.  Crucially, for distinct-subset-sum instances, **each element in each
set corresponds to a different feasible choice of xs**, and the solver has no
prior information about which choices are viable.

Therefore, to determine whether any intersection exists, the solver must be able
to distinguish all relevant candidates on both sides.  This informational
perspective—the idea that the solver must gather enough data to rule out or
confirm each independent candidate L- and R-value—is what ultimately drives the
lower-bound argument in the remainder of the theory.
›


section ‹2.  The Decision-Tree Lower Bound›

text ‹
  We briefly recall the abstract lower bound developed in the theory
  ‹SubsetSum_DecisionTree›; see that file for full details and proofs.

  In the reader model, a solver gradually acquires information about the
  unknown choice vector xs, while an adversary tracks all choices still
  compatible with the solver’s observations.  For each split position k, the
  canonical decomposition eₖ(as, s) induces two families of candidate
  contributions

      LHS(eₖ as s)    and    RHS(eₖ as s),

  arising respectively from all prefix-choices and all suffix-choices of xs.

  Two abstract axioms are imposed on this model:

    • ‹coverage› — on each distinct-subset-sum instance there exists a split
      k such that the solver’s “seen” sets coincide with the canonical
      families LHS(eₖ as s) and RHS(eₖ as s);

    • ‹cost› — the solver must spend at least one unit of work for every
      candidate value it distinguishes on either side.

  From these assumptions alone, the locale ‹SubsetSum_Lemma1› proves that at
  the relevant split k we have

      steps(as, s)  ≥  2^k + 2^(n − k),

  and therefore, after minimising over k,

      steps(as, s)  ≥  2 · sqrt(2^n).

  No mention of Turing machines or encodings is needed at this stage; the
  argument is entirely combinatorial.  The remainder of the present theory
  explains how this abstract lower bound is transported into the Cook–Levin
  machine model.
›


section ‹3.  From Decision Trees to Cook–Levin Turing Machines›

text ‹
The abstract √(2^n) lower bound from Section 2 applies to a reader model that
directly exposes which canonical candidate values LHS(eₖ as s) and RHS(eₖ as s)
the solver has distinguished.  A Cook–Levin Turing machine, however, is much
more flexible: it may reorder, copy, compress, or hash its input, and none of
this internal bookkeeping corresponds directly to the abstract “seen” sets of
the reader model.

To transport the abstract lower bound into the Cook–Levin setting, the theory
‹SubsetSum_CookLevin› introduces the locale ‹LR_Read_TM›.  It provides a way to
*interpret* a Turing machine’s observable behaviour in terms of two effective
distinguishability sets

      seenL_TM as s k    and    seenR_TM as s k,

which play the role of the abstract seenL/seenR of ‹SubsetSum_Lemma1›.
Roughly speaking, these sets measure what the machine has effectively learned
about prefix-determined and suffix-determined contributions at split position k.

The LR-read assumptions assert that, for each distinct-subset-sum instance,
there exists a split k such that

      seenL_TM as s k = LHS(eₖ as s)
      seenR_TM as s k = RHS(eₖ as s),

and that distinguishing each candidate value costs at least one step:

      steps_TM as s ≥ |seenL_TM as s k| + |seenR_TM as s k|.

With these two statements in place, the abstract reader lemma applies
verbatim with steps = steps_TM and seenL/seenR = seenL_TM/seenR_TM, yielding
for Turing machines exactly the same lower bound as in the reader model:

      steps_TM as s ≥ 2 · sqrt(2^n).

Thus the role of ‹LR_Read_TM› is purely structural: it aligns the observable
behaviour of a Cook–Levin machine with the information pattern that drives the
decision-tree lower bound.  Once this alignment is postulated, the transfer of
the √(2^n) bound is immediate.
›


section ‹4.  Why LR-read is Assumed›

text ‹
Unlike in the decision-tree model, LR-read cannot be derived from general
adversary arguments in the unrestricted Turing-machine setting.  The reason is
fundamental: a Turing machine begins its computation with the *entire* input
visible on its tape and is free to reorganise it internally in arbitrary ways.
An adversary has no control over how the machine structures or processes this
information once the computation starts.

A helpful analogy is the following.  In a hidden-information card game, a player
learns one card at a time while the opponent keeps the remaining cards concealed;
adversary arguments succeed precisely because the opponent controls which cards
remain hidden.  In contrast, a Turing machine begins with all cards face up.  It
may sort, copy, compress, and combine these cards internally, and an adversary
cannot force it to derive information according to any particular pattern — in
particular, not according to the canonical L/R split underlying SUBSET–SUM.

For this reason, LR-read is introduced explicitly as a *modelling assumption*
capturing a specific information-flow discipline: at some split k, the machine's
behaviour must distinguish exactly the canonical candidate sets LHS(eₖ) and
RHS(eₖ).  This assumption is the bridge that allows the abstract lower bound to
apply to Turing machines; it is not expected to follow from generic adversarial
reasoning.
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

  (3) Modeling assumption — not proved
      Every Cook–Levin Turing-machine solver for SUBSET–SUM (with encoding enc0)
      satisfies LR-read.

Together these yield the conditional implication:

      If SUBSET–SUM ∈ P and all solvers satisfy LR-read,
      then P ≠ NP.
›


section ‹6.  Relation to Feinstein (2016)›

text ‹
Feinstein’s 2016 paper emphasises an informational viewpoint: verifying a
candidate equality requires analysing contributions coming from two independent
parts of a decomposed expression.  For SUBSET–SUM, the canonical split eₖ(as, s)
exhibits exactly such a decomposition into prefix-determined and
suffix-determined contributions.

This formalisation captures that insight in two layers:

  • In the abstract reader model, the families LHS(eₖ as s) and RHS(eₖ as s)
    are treated as independent candidate sets.  The axioms of
    ‹SubsetSum_Lemma1› express the requirement that a solver must distinguish
    all candidates on both sides, yielding the √(2^n) lower bound.

  • In the Turing-machine model, the locale ‹LR_Read_TM› provides the structural
    assumption that the machine’s observable behaviour distinguishes exactly
    these same canonical families at some split k.  Once LR-read is assumed,
    the abstract lower bound transfers directly to Turing machines.

Thus the formal development isolates the combinatorial kernel of Feinstein’s
argument while making explicit the single structural hypothesis (LR-read)
required to connect it to Turing-machine computation.
›


section ‹7.  Perspective›

text ‹
The development provides a conditional lower-bound framework for SUBSET–SUM
within the Cook–Levin Turing-machine model.  All mathematically substantial
components — the decision-tree adversary argument, the Cook–Levin operational
semantics, and NP-membership via an explicit verifier — are fully formalised in
Isabelle/HOL.

The only non-mechanised ingredient is the LR-read assumption.  It encapsulates a
specific information-flow principle: any solver must obtain enough information
about both the prefix-determined and suffix-determined candidate contributions
to determine whether a solution exists.  When LR-read is postulated for all
polynomial-time solvers, the √(2^n) lower bound contradicts any polynomial
upper bound, yielding the conditional implication:

      If every polynomial-time solver for SUBSET–SUM satisfies LR-read,
      then P ≠ NP.

In this way, the formalisation separates the purely combinatorial content of the
lower bound from the modelling assumption under which it applies to Turing
machines.
›


section ‹8.  SUBSET–SUM is in NP (formalised)›

text ‹
  The technical work showing that SUBSET–SUM belongs to ‹𝒩𝒫› has already been
  carried out in ‹SubsetSum_CookLevin›.  There we introduced the locale
  ‹SS_Verifier_NP›, which packages an arbitrary NP-style verifier for
  SUBSET–SUM (instance and certificate encodings, a polynomial-time verifier
  machine, and soundness/completeness assumptions), and proved the lemma

      SUBSETSUM_in_NP_from_verifier :
        SS_Verifier_NP k G V p T fverify enc0 enc_cert
        ⟹ SUBSETSUM_lang enc0 ∈ 𝒩𝒫.

  In the present theory we simply reuse that result under a slightly more
  convenient name:
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
