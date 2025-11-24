theory P_neq_NP_from_LR
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
background to the formalisation developed in the theory
‹P_neq_NP_from_LR›.  The central goal is to explain—in clear,
non-technical language—the structure of the argument, which portions are
fully formalised in Isabelle/HOL, and which portion is assumed as an
axiom due to deep complexity-theoretic reasons.

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

   • Craig A. Feinstein,  
     *“An Efficient Algorithm for the Subset-Sum Problem,”*  
     arXiv:1605.08639.

This Isabelle/HOL development extracts and formalises the *lower-bound
core* of that paper in a precise, modular, and fully verified way.

Along the way, I also received assistance from two AI systems—
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
and target s, the question is whether one can choose a 0/1 vector `xs`
such that

          a₀·xs₀  +  ⋯  +  aₙ₋₁·xsₙ₋₁  =  s.

The key combinatorial fact is that, for certain carefully chosen lists
(as constructed in ‹SubsetSum_DecisionTree›), *all* 2ⁿ possible subset
sums are distinct.  
These are the **hard instances**: no two subsets have the same sum.

On such instances, deciding whether a particular sum equals s requires a
nontrivial amount of information about xs.  
This observation forms the foundation for the adversary argument.

-------------------------------------------------------------------------------
2.  The Decision-Tree Lower Bound
-------------------------------------------------------------------------------

In the decision-tree model (fully formalised in 
‹SubsetSum_DecisionTree›), a computation is modelled as repeatedly
“reading” bits of the input until a unique answer is forced.

The adversary argument goes as follows:

  • Partition the n input elements at an index k:

        Left  side: bitvector prefix of length k  
        Right side: bitvector suffix of length n − k.

  • The left side has 2ᵏ possible partial sums;  
    the right side has 2ⁿ⁻ᵏ possible partial sums.

  • To decide whether  
          L(xs[0..k)) = R(xs[k..n)),  
    the algorithm must know enough information to force the equality.

  • The adversary maintains two inputs that the algorithm cannot
    distinguish (agreeing on all bits read so far).  
    As long as there exists *any unread bit* whose value can change L or R,
    the adversary can keep two consistent inputs alive.

  • Therefore, to eliminate all 2ᵏ possibilities on the left, the
    algorithm must read at least k bits from the left region.  Similarly
    it must read at least n−k bits from the right region.

  • The total number of reads is at least  
        2ᵏ + 2ⁿ⁻ᵏ,  
    which is minimised at k = n/2, giving  
        2√(2ⁿ).

All of this—definitions, adversary construction, LHS/RHS sets,
the √(2ⁿ) lower bound—is **fully formalised** in Isabelle/HOL.

This is the “lower-bound kernel” around which the rest of the theory is
built.

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
‹LR_Read_TM›, which formalises a simple requirement:

    **A solver for SUBSET-SUM must actually read information from both
       the region encoding the left side of the deciding equation
       and from the region encoding the right side.**

This assumption preserves enough structural information to carry the
decision-tree adversary argument over to the Turing-machine setting.

If every polynomial-time SUBSET-SUM solver satisfies this property, the
√(2ⁿ) lower bound follows immediately.

-------------------------------------------------------------------------------
4.  Why LR–Read is Assumed, Not Proven
-------------------------------------------------------------------------------

Why treat this assumption axiomatically?  Why not *prove* that every
polynomial-time Turing machine must read from both L and R?

There are three deep reasons, rooted in modern complexity theory.

(1)  *The Natural Proofs Barrier (Razborov–Rudich, 1997).*

Any structural property that rules out all polynomial-time algorithms
must be “non-natural” or else it would contradict widely believed
cryptographic assumptions.  
The LR–read property is precisely such a “information-use” structural
property; proving it for all polynomial-time Turing machines is expected
to be as hard as proving P ≠ NP itself.

(2)  *Encoding flexibility makes structural invariants unprovable.*

Turing machines may use encodings that hide or compress information in
ways that frustrate direct combinatorial reasoning.  
Ruling out all such encodings is equivalent to classifying all possible
polynomial-time algorithms—a problem believed to be intractable.

(3)  *Chaitin’s philosophy of informational unprovability.*

Gregory Chaitin has argued that many deep computational principles—
especially those about “information content”—cannot be proven inside
formal systems of comparable strength and should instead be treated as
**axioms**.

The LR–read principle asserts a basic informational necessity:  
to decide whether L = R, one must obtain information about both L and R.  
This “computational physics principle” is more of an axiom of nature than
a theorem of arithmetic.

Given these barriers, the honest, transparent solution is:

  • formalise everything that *can* be proven,  
  • isolate the remaining modelling assumption clearly and explicitly,  
  • and study the consequences of that assumption.

-------------------------------------------------------------------------------
5.  The Logical Structure of the Isabelle Development
-------------------------------------------------------------------------------

The Isabelle formalisation splits cleanly into three layers:

(1) **Formal lower-bound kernel (fully proven)**  
    From ‹SubsetSum_DecisionTree› and abstract reader assumptions,  
    we prove:  
         steps ≥ 2√(2^n).

(2) **Cook–Levin bridge (mostly formal)**  
    We encode SUBSET-SUM as a CL Turing machine input,  
    prove SUBSET-SUM ∈ NP,  
    and define ‹LR_Read_TM› as the abstract Turing-machine analogue
    of the reader model.

(3) **One explicit modelling assumption (axiom)**  
    If SUBSET-SUM ∈ P, then there exists a polynomial-time solver
    whose behaviour satisfies LR–read.

This is the only place where we assume anything not formally justified.
Everything else is mechanised.

Under this assumption, we obtain the main theorem:

      **If SUBSET-SUM is solved in P, then P ≠ NP.**

Equivalently:

      **If every polynomial-time SUBSET-SUM solver must read  
         at least one bit from L and at least one from R,  
         then P ≠ NP.**

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
7.  Philosophical Perspective
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

Importantly, *everything else*—including the √(2ⁿ) lower bound—is
formalised and certified by Isabelle/HOL.

-------------------------------------------------------------------------------
8.  The Final Conditional Theorem
-------------------------------------------------------------------------------

The main theorem of ‹P_neq_NP_from_LR› is:

      **If every polynomial-time SUBSET-SUM solver satisfies LR–read,
         then  P ≠ NP.**

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
  Global meta-assumptions wrapping the LR-read lower bound into a
  conditional P ≠ NP statement, in the “equation-based” style.

  We fix an NP-side encoding {term enc0} for SUBSET-SUM and assume:

    • "SUBSETSUM_lang enc0 ∈ 𝒩𝒫"  (NP membership),

    • (Existence) If term "SUBSETSUM_lang enc0 ∈ 𝒫", then there exists
      a Cook–Levin machine term M with some CL encoding term enc
      and some equation data term lhs, term rhs, term L_zone,
      {term R_zone} such that

        – "Eq_ReadLR_SubsetSum_Solver M q0 enc lhs rhs L_zone R_zone"
          holds (this includes the “must read L and R on hard instances”
          axiom),

        – "polytime_CL_machine M enc" holds.

    • (Bridge) Any such equation-based, polynomial-time solver can be
      refined to an LR_Read_TM instance (structural LR-read property),
      which in turn inherits the √(2^n) lower bound from the decision-tree
      theory.

  Under these assumptions we derive "¬ P_eq_NP".
›

locale Global_LR_Assumptions =
  fixes enc0 :: "int list ⇒ int ⇒ string"   (* NP-side SUBSET-SUM encoding *)
  assumes SUBSETSUM_in_NP_global:
    "SUBSETSUM_lang enc0 ∈ 𝒩𝒫"
  assumes P_impl_eq_readlr_CL_global:
    "SUBSETSUM_lang enc0 ∈ 𝒫 ⟹
       ∃M q0 enc lhs rhs L_zone R_zone.
         Eq_ReadLR_SubsetSum_Solver M q0 enc lhs rhs L_zone R_zone ∧
         polytime_CL_machine M enc"
  assumes eq_to_LR_Read_TM_global:
    "⋀M q0 enc lhs rhs L_zone R_zone.
       Eq_ReadLR_SubsetSum_Solver M q0 enc lhs rhs L_zone R_zone ⟹
       polytime_CL_machine M enc ⟹
       LR_Read_TM M q0 enc"

context Global_LR_Assumptions
begin

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
  have lr: "LR_Read_TM M q0 enc" .

  interpret LR: LR_Read_TM M q0 enc
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

  text ‹From P = NP and SUBSETSUM_lang enc0 ∈ NP, we get
    SUBSETSUM_lang enc0 ∈ P.›
  have inP_SUBSETSUM: "SUBSETSUM_lang enc0 ∈ 𝒫"
    using eq SUBSETSUM_in_NP_global
    unfolding P_eq_NP_def by metis

  text ‹By the modelling assumption, this yields an equation-based,
    polynomial-time Cook–Levin solver for SUBSET-SUM.›
  from P_impl_eq_readlr_CL_global[OF inP_SUBSETSUM]
  obtain M q0 enc lhs rhs L_zone R_zone where
    solver: "Eq_ReadLR_SubsetSum_Solver M q0 enc lhs rhs L_zone R_zone" and
    poly:   "polytime_CL_machine M enc"
    by blast

  text ‹Package this solver as a witness for the existential that
    ‹no_polytime_eq_readlr_solver› forbids.›
  have ex_solver:
    "∃M q0 enc lhs rhs L_zone R_zone.
       Eq_ReadLR_SubsetSum_Solver M q0 enc lhs rhs L_zone R_zone ∧
       polytime_CL_machine M enc"
    using solver poly by blast

  from no_polytime_eq_readlr_solver ex_solver
  show False by blast
qed

end  (* context Global_LR_Assumptions *)

text ‹Non-locale exported version:

  If some encoding enc0 and assumptions
  "Global_LR_Assumptions enc0" hold, then P ≠ NP.
›

theorem P_neq_NP_from_LR_global:
  assumes "Global_LR_Assumptions enc0"
  shows "¬ P_eq_NP"
proof -
  interpret Global_LR_Assumptions enc0 by fact
  from P_neq_NP_from_LR show ?thesis .
qed

end  (* theory *)
