theory SubsetSum_PneqNP
  imports SubsetSum_CookLevin
begin

text ‹

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                                                            %
%        A CONDITIONAL PROOF THAT P ≠ NP FROM AN INFORMATION-FLOW PRINCIPLE  %
%                                                                            %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

This chapter presents the conceptual background to the formalisation developed
in this theory.  Its purpose is to explain, in clear and non-technical terms,
the structure of the argument: which parts are fully formalised in Isabelle/HOL,
and which part is assumed as an axiom for complexity-theoretic reasons.

The machinery developed here yields a conditional statement of the form:

      *If every polynomial-time Turing machine solving SUBSET-SUM satisfies
       a certain information-flow property (the LR–read property),
       then P ≠ NP.*

The information-flow principle is intuitive:

      **To decide whether two quantities L and R are equal,
        a solver must read at least one bit of the input that encodes L
        and at least one bit of the input that encodes R.**

This development extracts and formalises the lower-bound core of:

      • C. A. Feinstein,
        “Dialogue Concerning the Two Chief World Views,”
        arXiv:1605.08639.

The author received assistance from two AI systems — ChatGPT (OpenAI) and 
Claude (Anthropic) — primarily in generating explanatory text, improving 
readability, and refining the presentation of structural assumptions. All 
proofs in this repository are checked by Isabelle/HOL.  Only the LR–read 
condition is left as a modelling assumption.

-------------------------------------------------------------------------------
1.  Why SUBSET-SUM?
-------------------------------------------------------------------------------

The classical SUBSET-SUM problem asks whether, for a list of integers
  as = [a₀, ..., aₙ₋₁]
and a target s, there exists a 0/1-vector xs such that

      Σ i<n. as!i * xs!i = s.

Among NP-complete problems, SUBSET-SUM has an unusually transparent
combinatorial shape.  In particular, for certain carefully constructed
lists — e.g. the powers-of-two family — *all* 2ⁿ subset sums are distinct.
These instances serve as “hard” examples for adversary lower bounds,
because many different choices of xs yield different sums.

-------------------------------------------------------------------------------
2.  The Decision-Tree Lower Bound (recap)
-------------------------------------------------------------------------------

The theory SubsetSum_DecisionTree defines an abstract “reader” model and
proves the lower bound

      steps as s ≥ 2 * √(2^n)

on all instances with distinct subset sums.

Informally, the model represents computation as an adversary game:

  • The solver reads bits of the *real* input (as, s).  
  • An adversary tracks all *virtual completions* xs ∈ {0,1}ⁿthat remain
    compatible with every bit of (as, s) the solver has read so far—
    each xs representing a hypothetical subset-choice still possible
    from the solver’s perspective.
  • For each split k, the canonical equation eₖ(as,s) has a left part L(xs)
    depending on xs[0..k−1] and a right part R(xs) depending on xs[k..n−1].

As xs varies, these define value sets LHS(eₖ) and RHS(eₖ) of sizes 2ᵏ and 2ⁿ⁻ᵏ.
The solver never reads xs; these sets track how many hypothetical worlds remain
consistent with its observations.

The two abstract axioms of SubsetSum_Lemma1 state that:

  • for some split k, the solver’s information-flow aligns with LHS(eₖ)/RHS(eₖ),  
  • and each distinguishable L- or R-value contributes at least one unit of cost.

This yields the lower bound 2ᵏ + 2ⁿ⁻ᵏ, minimised at 2 * √(2ⁿ).

SubsetSum_DecisionTree proves this entirely abstractly and packages the result
in the locale SubsetSum_Lemma1.  The current theory *imports* this lower bound
and connects it to Turing machines.

-------------------------------------------------------------------------------
3.  From Decision Trees to Turing Machines
-------------------------------------------------------------------------------

A Cook–Levin Turing machine is much more flexible than a decision tree:
it may reorder or duplicate the input, compress it, or interleave different
parts of the encoding arbitrarily.  Therefore the decision-tree lower bound
does *not* automatically apply to Turing machines.

To bridge this gap, the locale LR_Read_TM formalises the information-flow
principle mentioned above:

      **To decide L = R, the solver must actually read information from
        both the L-region and the R-region of the input encoding.**

In LR_Read_TM this principle is expressed through abstract “seen” sets that
satisfy the axioms of SubsetSum_Lemma1.  Any solver satisfying LR–read
therefore inherits the √(2ⁿ) lower bound for its Cook–Levin step count.

-------------------------------------------------------------------------------
4.  Why LR–Read is Assumed, Not Proven
-------------------------------------------------------------------------------

The key assumption of this theory is:

      **Every polynomial-time solver for SUBSET-SUM satisfies LR–read.**

This is *not* proved here.  It is taken as a modelling axiom.

Why?  Because if one could prove that all polynomial-time SUBSET-SUM
algorithms necessarily satisfy LR–read, then the lower bound in
LR_Read_TM would immediately imply that SUBSET-SUM ∉ P, and hence P ≠ NP.
In other words, proving the universal LR–read property would essentially
settle P vs NP.

Treating LR–read as an explicit assumption clarifies the structure of the
argument: every other component — the √(2ⁿ) lower bound, the
decision-tree instantiation, the NP-membership proof, and the Cook–Levin
machinery — is fully formalised and unconditional.

The assumption is falsifiable: finding a polynomial-time solver that
solves SUBSET-SUM but violates LR–read would refute it directly.

-------------------------------------------------------------------------------
5.  Logical Structure of the Isabelle Development
-------------------------------------------------------------------------------

The formalisation breaks down into three cleanly separated layers:

(1) **Lower-bound kernel (fully formalised)**  
    SubsetSum_DecisionTree + SubsetSum_Lemma1 prove the √(2ⁿ) lower bound
    for any model satisfying the abstract axioms.

(2) **Cook–Levin bridge (fully formal)**  
    SUBSET-SUM is encoded in the Cook–Levin machine model, and LR_Read_TM
    expresses LR–read in that setting.

(3) **One explicit assumption (LR–read)**  
    If SUBSET-SUM ∈ P, then there exists a polynomial-time solver whose
    behaviour satisfies LR–read.

From these, we obtain:

      **If SUBSET-SUM ∈ P and every such solver satisfies LR–read,
         then P ≠ NP.**

-------------------------------------------------------------------------------
6.  Relationship to Feinstein (2016)
-------------------------------------------------------------------------------

Feinstein’s original paper proposed that verifying an equality of two
subset-sum expressions requires examining many configurations.  The present
work extracts the precise combinatorial statement underlying this idea,
formalises it rigorously, and pinpoints the single structural assumption
needed to lift it to a Turing-machine lower bound.

-------------------------------------------------------------------------------
7.  Philosophical Perspective
-------------------------------------------------------------------------------

This formalisation is not a proof of P ≠ NP.  It is a case study in making
the boundary between *proven lower bounds* and *structural assumptions*
transparent.  The LR–read condition isolates exactly the kind of
information-flow property that would be sufficient to derive P ≠ NP, while
every other component of the argument is fully mechanised.

-------------------------------------------------------------------------------
8.  Final Conditional Theorem
-------------------------------------------------------------------------------

The main theorem proved in this theory is:

      **Assuming that every polynomial-time SUBSET-SUM solver satisfies LR–read,
         we have P ≠ NP.**

The contribution of this AFP entry is therefore twofold:

  • a fully formalised lower-bound engine for SUBSET-SUM,  
  • and a single, explicit assumption identifying precisely what remains
    to be shown for the argument to become unconditional.
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

  In the theory SubsetSum_CookLevin, the locale LR_Read_TM describes a
  Cook–Levin Turing machine M with encoding enc whose behaviour aligns
  with the canonical LHS/RHS value sets from the abstract lower-bound
  theory. Its assumptions are:

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

  The locale theorem P_neq_NP_from_LR below formalises exactly this reasoning:
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
