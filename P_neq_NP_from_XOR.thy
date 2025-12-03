theory SubsetSum_PneqNP
  imports SubsetSum_CookLevin
begin

text ‹

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                                                            %
%                A CONDITIONAL PROOF THAT  P ≠ NP  FROM A                    %
%           STRUCTURAL LR–READ ASSUMPTION ON SUBSET–SUM SOLVERS              %
%                                                                            %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

This chapter presents the conceptual, mathematical, and philosophical
background to the formalisation developed in this theory. The central goal
is to explain—in clear, non-technical language—the structure of the
argument, which portions are fully formalised in Isabelle/HOL, and which
portion is assumed as an axiom due to deep complexity-theoretic reasons.

The technical machinery of this chapter realises, in verified form,
a conditional statement of the following kind:

     *If every polynomial-time Turing machine that solves SUBSET-SUM
      satisfies a certain natural information-use property
      (the LR–read property), then P ≠ NP.*

The information-use property in question has an intuitive
computational meaning:

     **When a machine decides whether two quantities L and R are equal,
       it must look at at least one bit of the part of the input that
       encodes L, and at least one bit of the part that encodes R.**

The argument originates from a 2016 paper of Craig A. Feinstein:

   • C. A. Feinstein,  
     “Dialogue Concerning the Two Chief World Views,”  
     arXiv:1605.08639.

This Isabelle/HOL development extracts and formalises the *lower-bound
core* of that paper in a precise, modular, and fully verified way.

Along the way, the author received assistance from two AI systems—
**ChatGPT** (OpenAI) and **Claude AI** (Anthropic)—primarily in generating
explanatory text, improving accessibility, and refining the presentation
of structural assumptions.  All proofs included in this repository are
fully verified by Isabelle/HOL.

Before describing the results, we begin with the computational
intuitions.

-------------------------------------------------------------------------------
1.  Why SUBSET-SUM?
-------------------------------------------------------------------------------

Among NP-complete problems, SUBSET-SUM has a particularly simple
combinatorial structure: for a list of integers `as = [a₀, a₁, ..., aₙ₋₁]`
and target `s`, the question is whether one can choose a 0/1 vector `xs`
such that

          a₀·xs₀  +  ⋯  +  aₙ₋₁·xsₙ₋₁  =  s.

The key combinatorial fact is that, for certain carefully chosen lists
(as constructed in SubsetSum_DecisionTree), *all* 2ⁿ possible subset
sums are distinct. These are the **hard instances**: no two subsets have
the same sum.

On such instances, deciding whether a particular sum equals s requires a
nontrivial amount of information about xs. This observation forms the
foundation for the adversary argument.

-------------------------------------------------------------------------------
2.  The Decision-Tree Lower Bound (recap)
-------------------------------------------------------------------------------

The theory SubsetSum_DecisionTree defines an abstract reader model for
SUBSET-SUM and proves the lower bound

      steps as s ≥ 2 * √(2^n)

on the hard family of length-n instances with distinct subset sums.

Informally, the model views a computation as an adversary game:

  • The algorithm reads bits of the *real* input (as, s).  
  • An adversary maintains “virtual completions” xs ∈ {0,1}ⁿ that are
    consistent with everything the algorithm has seen so far.  
  • For each split k, the canonical equation eₖ(as, s) has a left-hand
    side L(xs) depending on the first k bits and a right-hand side R(xs)
    depending on the remaining n − k bits.

As xs varies, the possible L- and R-values form sets LHS(eₖ) and RHS(eₖ)
of sizes 2ᵏ and 2ⁿ⁻ᵏ.  The algorithm never reads xs directly; these sets
are a way of tracking how many “virtual worlds” remain indistinguishable
given what has been read from (as, s).  The abstract axioms state that

  • for some split k, the algorithm’s information flow aligns with the
    canonical LHS/RHS decomposition; and  

  • each distinct L- or R-value that must be distinguished costs at
    least one unit of work.

On the hard family with distinct subset sums this yields

      steps as s ≥ 2ᵏ + 2ⁿ⁻ᵏ

for some k ≤ n, and minimising this expression over k gives

      steps as s ≥ 2 * √(2^n).

All of this is proved once and for all in SubsetSum_DecisionTree and
exposed via the locale SubsetSum_Lemma1. The present theory does not
reprove the lower bound; it only transports it to Turing machines under
the LR–read assumption.

-------------------------------------------------------------------------------
3.  From Decision Trees to Turing Machines
-------------------------------------------------------------------------------

A Cook–Levin Turing machine is more flexible than a decision tree:
  • it may encode the input arbitrarily,  
  • it may read bits in any order,  
  • it may interleave, compress, or duplicate portions of the encoding.

Thus, even though we have *proven* that any decision-tree needs at least
2√(2ⁿ) reads, this does not automatically imply the same statement for
Turing machines.

The bridge between these models is encapsulated in the locale
LR_Read_TM, which formalises a simple requirement:

    **A solver for SUBSET-SUM must actually read information from both
       the region encoding the left side of the deciding equation
       and from the region encoding the right side.**

Inside LR_Read_TM, this requirement is expressed via abstract “seen”
sets that satisfy the axioms of SubsetSum_Lemma1, so the √(2ⁿ) lower
bound carries over to the Cook–Levin step-count of any solver satisfying
LR–read.

-------------------------------------------------------------------------------
4.  Why LR–Read is Assumed, Not Proven
-------------------------------------------------------------------------------

The locale P_neq_NP_LR_Model includes, as an explicit assumption, that
every polynomial-time SUBSET-SUM solver satisfies the LR–read property:
when processing instances with distinct subset sums, the solver must
extract some information about the “left’’ part and some information
about the “right’’ part of the deciding equation.

This principle is **not proved** in this development — it is *axiomatised*.
The reason is straightforward:

    **If one could prove that every P-time SUBSET-SUM solver must
       satisfy LR–read, then one would immediately obtain P ≠ NP.**

Within the locale LR_Read_TM, the LR–read property implies a
Ω(√(2ⁿ)) lower bound on the distinct-subset-sums family.  A *universal*
LR–read theorem would therefore rule out the existence of any
polynomial-time algorithm for SUBSET-SUM, and since SUBSET-SUM is
NP-complete, this would yield P ≠ NP.  Proving such a universal property
is thus expected to be at least as hard as resolving P vs NP itself.

There is also a conceptual justification following ideas of Gregory Chaitin,
who argues that mathematics is inherently incomplete and that certain deep
computational principles may not be derivable within existing axiomatic
systems without introducing new axioms.  See:

      G. J. Chaitin, "Thoughts on the Riemann Hypothesis,"
      arXiv:math/0306042 (2003).

The LR–read principle fits naturally into this viewpoint. It expresses a
fundamental information-flow constraint: to determine whether L = R, one
must obtain information about both L and R.  While this seems intuitively
necessary, proving it holds universally for all polynomial-time algorithms
would require techniques beyond those currently available.  Treating it
as an explicit axiom therefore clarifies the logical structure of the
argument rather than weakening it.

Everything else in this development — the √(2ⁿ) lower bound, the
decision-tree instantiation, and the Cook–Levin bridge — is fully
verified in Isabelle/HOL.  The **only** non-proven component is the
universal validity of LR–read, which is intentionally left as a clear
and explicit assumption.  This axiom is falsifiable: exhibiting a
polynomial-time SUBSET-SUM solver that demonstrably violates LR–read
would refute it, while leaving the verified lower-bound kernel intact.

-------------------------------------------------------------------------------
5.  The Logical Structure of the Isabelle Development
-------------------------------------------------------------------------------

The Isabelle formalisation splits cleanly into three layers:

(1) **Formal lower-bound kernel (fully proven)**  
    From SubsetSum_DecisionTree and abstract reader assumptions,  
    we prove:

         steps ≥ 2√(2^n)

    on the hard family of instances with distinct subset sums.

(2) **Cook–Levin bridge (fully formal on the TM side)**  
    We encode SUBSET-SUM as a Cook–Levin Turing machine input,  
    show that SUBSETSUM_lang enc0 lies in 𝒩𝒫, and define LR_Read_TM
    as the Turing-machine analogue of the abstract reader model.

(3) **One explicit modelling assumption (axiom)**  
    If SUBSET-SUM ∈ P, then there exists a polynomial-time solver whose
    behaviour satisfies the LR–read property.

This is the only place where we assume anything not formally justified.
Everything else is mechanised.

Under these assumptions, we obtain the main conditional statement:

      **If SUBSET-SUM lies in P and every such solver satisfies LR–read,
        then P ≠ NP.**

Equivalently, relative to the modelling assumptions packaged in
the locale P_neq_NP_LR_Model:

      **If every polynomial-time SUBSET-SUM solver can be represented
         as an equation-based solver and every such solver satisfies
         the LR–read property, then P ≠ NP.**

-------------------------------------------------------------------------------
6.  Relationship to Feinstein (2016)
-------------------------------------------------------------------------------

Feinstein’s original paper proposed an informal argument that SUBSET-SUM
requires exponential time because verifying equality of the “left” and
“right” sums requires inspecting many possible configurations.

This Isabelle development isolates the *exact* combinatorial content
of that argument, formalises it rigorously in the decision-tree model,
and identifies the **one** structural assumption needed to transfer the
argument to Turing machines.

The result is a more precise, modular, and verifiable form of the
original intuition.

-------------------------------------------------------------------------------
7.  Philosophical Perspective and Natural Proofs
-------------------------------------------------------------------------------

This work can be viewed as an example of Chaitin’s thesis that certain
deep computational truths may require additional axioms beyond those
typically considered in mathematics.

The LR–read assumption expresses a fundamental asymmetry between
information and ignorance:

    “One cannot determine the relationship between two quantities
     without extracting information about each one.”

This is arguably more a law of computation than a theorem, and our
formalisation shows how such a principle can be cleanly integrated into
a rigorous mathematical framework.

This formalisation is not intended as a proof of P ≠ NP.  Rather, it
provides a fully verified framework in which the classical adversary
lower bound for SUBSET-SUM can be transported to the Cook–Levin model,
conditional on a single, clearly stated structural assumption: the
LR–read property.

In light of the Natural Proofs barrier (Razborov–Rudich, 1997), a
universal information-use principle of this form is widely believed
to be unprovable in ZFC by currently known “natural’’ techniques,
without conflicting with standard cryptographic assumptions.  Accordingly,
the formalisation should be viewed as a case study in identifying the
precise informational axiom required for this style of adversary
argument, rather than as progress toward resolving P vs NP.

The lower-bound kernel itself is fully mechanised and may prove reusable
in future developments.

-------------------------------------------------------------------------------
8.  The Final Conditional Theorem
-------------------------------------------------------------------------------

The main theorem of SubsetSum_PneqNP is:

    **Assuming that every polynomial-time SUBSET-SUM solver satisfies LR–read,
      we have P ≠ NP.**

This shows that a very simple, very natural informational principle
—one likely unprovable for deep reasons—bridges the gap between the
formal combinatorial lower-bound core and a full separation of
complexity classes.

The contribution of this AFP entry is therefore twofold:

  • a fully formalised lower-bound engine for SUBSET-SUM (independent
    of unproven assumptions), and

  • a transparent, honest top-level axiom that pinpoints exactly which
    structural fact is needed to conclude P ≠ NP.

This approach does not claim to *prove* P ≠ NP outright, but it provides
a powerful blueprint:

**identify the minimal structural axiom needed, formalise everything
around it, and expose precisely what remains to be shown.**
›

definition P_eq_NP :: bool where
  "P_eq_NP ⟷ (∀L::language. (L ∈ 𝒫) = (L ∈ 𝒩𝒫))"

text ‹
  --------------------------------------------------------------------------
  ■ The LR–read assumption in the formal development
  --------------------------------------------------------------------------

  Sections 4–5 above explain the informal meaning and motivation of the
  LR–read principle and why it is treated as an assumption rather than a
  theorem.  In this section we only record **where** LR–read appears in
  the Isabelle formalisation and how it is encoded in locales.

  ● LR_Read_TM: the abstract LR–read interface for a single solver
  --------------------------------------------------------------------------

  In the theory SubsetSum_CookLevin, the locale LR_Read_TM describes a
  Cook–Levin Turing machine M with encoding enc whose behaviour aligns
  with the canonical LHS/RHS value sets from the abstract lower-bound
  theory.  Its assumptions are:

    • a coverage axiom coverage_TM saying that on every hard instance
      (with distinct subset sums) there exists a split index k such that
      the “seen” sets seenL_TM as s k and seenR_TM as s k coincide with
      the canonical sets LHS (e_k as s k) and RHS (e_k as s k);

    • a cost axiom steps_lb_TM saying that each seen L/R-value contributes
      at least one unit of work:
        steps_TM as s ≥ card (seenL_TM as s k) + card (seenR_TM as s k).

  Inside this locale we interpret the abstract locale
  SubsetSum_Lemma1 steps_TM seenL_TM seenR_TM, and therefore inherit the
  √(2ⁿ) lower bound and the “no polynomial-time bound on the hard family”
  corollaries for any machine satisfying LR_Read_TM.

  In other words: **LR_Read_TM is the formal LR–read property for a single
  solver.**  Anything inside this locale automatically satisfies the
  decision-tree lower bound.

  ● Eq_ReadLR_SubsetSum_Solver: equation-based solvers
  --------------------------------------------------------------------------

  The locale Eq_ReadLR_SubsetSum_Solver (also in SubsetSum_CookLevin)
  describes solvers that decide SUBSET-SUM by comparing two “sides”
  lhs as s and rhs as s of an equation, with disjoint input zones
  L_zone as s and R_zone as s that encode these sides.

  Its key assumption must_read_LR says that, on any distinct-subset-sums
  instance, the machine’s read set intersects both zones:

      read0_TM as s ∩ L_zone as s ≠ {} and
      read0_TM as s ∩ R_zone as s ≠ {}.

  This is an explicit, concrete “must read from left and right” condition.
  It is still weaker and more model-dependent than LR_Read_TM, and it
  does not yet mention the canonical LHS/RHS sets.

  ● How the LR–read assumptions imply “If LR–read holds for all P-time
    solvers, then P ≠ NP”
  --------------------------------------------------------------------------

  The locale P_neq_NP_LR_Model packages three meta-assumptions that
  jointly allow the √(2ⁿ) lower bound from LR_Read_TM to be lifted to
  a full conditional “P ≠ NP” statement.  These assumptions are:

    (A1)  SUBSET-SUM ∈ NP for the chosen encoding enc0.
          This is fully verified using an explicit NP verifier.

    (A2)  If SUBSET-SUM ∈ P, then there exists *some* polynomial-time solver
          whose behaviour fits the semantic interface Eq_ReadLR_SubsetSum_Solver.
          In this interface, correctness is expressed by an equation
            lhs as s = rhs as s
          and the machine’s reading behaviour respects a designated
          “L-zone / R-zone’’ partition of the input.

          This is a modelling assumption: it does **not** claim that every
          P-time solver for SUBSET-SUM admits such a representation.  
          It asserts only that, *if* SUBSET-SUM lies in P, then there exists
          at least one polynomial-time solver whose semantics can be cast
          in this equation-based form.  This provides a bridge from
          “SUBSET-SUM ∈ P’’ to the structural LR–read framework.

    (A3)  Every such equation-based polynomial-time solver satisfies the
          LR-read interface LR_Read_TM for some seenL and seenR.
          This *is the LR–read assumption*.

  Inside the locale, these assumptions combine as follows:

    • From (A1), SUBSET-SUM ∈ NP.  
      Under the temporary assumption P = NP, we conclude SUBSET-SUM ∈ P.

    • From (A2), SUBSET-SUM ∈ P yields the existence of a polynomial-time
      equation-based solver.

    • From (A3), any such solver must satisfy LR-read.
      But every solver satisfying LR-read inherits the √(2ⁿ) lower bound
      from LR_Read_TM, and therefore cannot be polynomial-time on the
      distinct-subset-sums family.

      Hence (A3) contradicts the polynomial-time requirement from (A2).

  The locale theorem P_neq_NP_from_LR formalises exactly this reasoning:
  under assumptions (A1)–(A3), the hypothesis P = NP leads to a contradiction.
  Therefore:

          **If every polynomial-time SUBSET-SUM solver satisfies LR–read,
             then P ≠ NP.**

  The Isabelle development therefore isolates the LR–read property as the
  *single structural assumption* required to turn the fully mechanised
  lower-bound kernel into a full separation of P and NP.
›

locale P_neq_NP_LR_Model =
  fixes enc0     :: "int list ⇒ int ⇒ string"
    and k        :: nat              (* number of tapes for the NP TM *)
    and q0V      :: nat              (* start state for the NP verifier V *)
    and V        :: machine          (* NP-style Turing machine *)
    and p        :: "nat ⇒ nat"
    and T        :: "nat ⇒ nat"
    and fverify  :: "string ⇒ string"
    and enc_cert :: "int list ⇒ int ⇒ int list ⇒ string"
  assumes SS_verifier:
    "SS_Verifier_NP k q0V V p T fverify enc0 enc_cert"
  assumes P_impl_eq_readlr_CL_global:
    "SUBSETSUM_lang enc0 ∈ 𝒫 ⟹
       ∃M q0 enc lhs rhs L_zone R_zone.
         Eq_ReadLR_SubsetSum_Solver M q0 enc lhs rhs L_zone R_zone ∧
         polytime_CL_machine M enc"
  assumes eq_to_LR_Read_TM_global:
    "⋀M q0 enc lhs rhs L_zone R_zone.
       Eq_ReadLR_SubsetSum_Solver M q0 enc lhs rhs L_zone R_zone ⟹
       polytime_CL_machine M enc ⟹
       (∃seenL seenR. LR_Read_TM M q0 enc seenL seenR)"
begin

lemma SUBSETSUM_in_NP_global:
  "SUBSETSUM_lang enc0 ∈ 𝒩𝒫"
  using SUBSETSUM_in_NP_from_verifier[OF SS_verifier] .

lemma no_polytime_eq_readlr_solver:
  shows "¬ (∃M q0 enc lhs rhs L_zone R_zone.
              Eq_ReadLR_SubsetSum_Solver M q0 enc lhs rhs L_zone R_zone ∧
              polytime_CL_machine M enc)"
proof
  assume ex:
    "∃M q0 enc lhs rhs L_zone R_zone.
       Eq_ReadLR_SubsetSum_Solver M q0 enc lhs rhs L_zone R_zone ∧
       polytime_CL_machine M enc"
  then obtain M q0 enc lhs rhs L_zone R_zone where
    solver: "Eq_ReadLR_SubsetSum_Solver M q0 enc lhs rhs L_zone R_zone" and
    poly:   "polytime_CL_machine M enc"
    by blast

  text ‹Use the bridge: any such equation-based solver gives an LR_Read_TM.›
  from eq_to_LR_Read_TM_global[OF solver poly]
  obtain seenL seenR where lr: "LR_Read_TM M q0 enc seenL seenR"
    by blast

  interpret LR: LR_Read_TM M q0 enc seenL seenR
    by (rule lr)

  text ‹From polynomial-time on all inputs we deduce an (assumed)
    polynomial bound on the distinct-subset-sums family.›

  from poly obtain c d where
    cpos: "c > 0" and
    bound_all: "∀as s. steps_CL M (enc as s)
                       ≤ nat (ceiling (c * (real (length as)) ^ d))"
    unfolding polytime_CL_machine_def by blast

  have family_bound:
    "∃(c::real)>0. ∃d::nat.
       ∀as s. distinct_subset_sums as ⟶
         steps_CL M (enc as s)
           ≤ nat (ceiling (c * (real (length as)) ^ d))"
    using cpos bound_all by blast

  text ‹But LR_Read_TM’s inherited lower bound says no such polynomial
    bound exists on the distinct-subset-sums family.›
  from LR.no_polytime_CL_on_distinct_family family_bound
  show False by blast
qed

theorem P_neq_NP_from_LR:
  "¬ P_eq_NP"
proof
  assume eq: P_eq_NP

  have eq_PNP_inst:
    "(SUBSETSUM_lang enc0 ∈ 𝒫) = (SUBSETSUM_lang enc0 ∈ 𝒩𝒫)"
    using eq unfolding P_eq_NP_def by simp

  have inP_SUBSETSUM: "SUBSETSUM_lang enc0 ∈ 𝒫"
  proof -
    have "SUBSETSUM_lang enc0 ∈ 𝒩𝒫"
      by (rule SUBSETSUM_in_NP_global)
    thus ?thesis
      using eq_PNP_inst by simp
  qed

  text ‹By the modelling assumption, this yields an equation-based,
    polynomial-time Cook–Levin solver for SUBSET-SUM.›
  from P_impl_eq_readlr_CL_global[OF inP_SUBSETSUM]
  obtain M q0 enc lhs rhs L_zone R_zone where
    solver: "Eq_ReadLR_SubsetSum_Solver M q0 enc lhs rhs L_zone R_zone" and
    poly:   "polytime_CL_machine M enc"
    by blast

  text ‹Package this solver as a witness for the existential that
    no_polytime_eq_readlr_solver forbids.›
  have ex_solver:
    "∃M q0 enc lhs rhs L_zone R_zone.
       Eq_ReadLR_SubsetSum_Solver M q0 enc lhs rhs L_zone R_zone ∧
       polytime_CL_machine M enc"
    using solver poly by blast

  from no_polytime_eq_readlr_solver ex_solver
  show False by blast
qed

end  (* context P_neq_NP_LR_Model *)

text ‹Non-locale exported version:

  If some encoding enc0 and assumptions
  P_neq_NP_LR_Model enc0 hold, then P ≠ NP.
›

theorem P_neq_NP_from_LR_global:
  assumes "P_neq_NP_LR_Model enc0 k G V p T fverify enc_cert"
  shows "¬ P_eq_NP"
proof -
  interpret P_neq_NP_LR_Model enc0 k G V p T fverify enc_cert by fact
  from P_neq_NP_from_LR show ?thesis .
qed

end  (* theory *)
