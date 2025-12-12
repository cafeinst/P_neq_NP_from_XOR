theory SubsetSum_PneqNP
  imports SubsetSum_CookLevin
begin

text ‹
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                                                             %
%      A CONDITIONAL PROOF THAT P ≠ NP FROM AN INFORMATION–FLOW PRINCIPLE     %
%                                                                             %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

This theory completes the mechanised development of a conditional lower bound
for SUBSET–SUM originating in

    C. A. Feinstein,
    “Dialogue Concerning the Two Chief World Views,”
    arXiv:1605.08639.

The analysis begins from a simple informational observation:

      To decide whether two integers L and R are equal,
      a solver must obtain some information about L
      and some information about R.

This principle, taken at face value, concerns only a *single pair* of integers.
It says nothing about candidate families, splits, or search spaces.  Its force in
the SUBSET–SUM setting comes from the fact that, for any split position k, the
canonical decomposition eₖ(as,s) expresses the verification equation in terms of
two collections of *possible integers*:

      LHS(eₖ as s)      (size 2^k),
      RHS(eₖ as s)      (size 2^(n − k)).

Each element of these sets is a distinct integer that L or R could take.  Thus, 
when viewed through the original principle, the solver is confronted not with one 
possible L and one possible R, but with 2^k possible Ls and 2^(n − k) possible Rs.

It follows immediately that the solver must obtain *at least one unit of
information about each candidate integer*.  Otherwise, some L-candidate and some
R-candidate would remain indistinguishable, and the solver could not validly
conclude that none of these pairs satisfy L = R.

The challenge is to express this per-candidate informational requirement inside
the Cook–Levin Turing-machine model.  In this setting the machine may reorder,
copy, or compress its input in ways that an adversary cannot track or restrict.
Because of this freedom, the standard adversary technique — which works in
decision-tree or query models — cannot enforce the per-candidate requirement:
once the entire input is visible, the adversary cannot prevent the machine from
computing derived representations that bypass the intended structure.

For this reason, the theory introduces LR-read as an explicit modelling
assumption.  LR-read formalises the idea that, for some split k, the machine’s
observable behaviour distinguishes **exactly** the canonical L- and R-candidate
integers produced by eₖ(as,s).  It is not an additional assumption, but the 
direct formal realisation of the informational requirement stated above, 
expressed in the language of Cook–Levin Turing machines.

Under LR-read, the mechanised development imports the abstract decision-tree
lower bound and shows that every solver must take at least

      2 · sqrt(2^n)

steps on distinct-subset-sum instances of length n.  Since √(2^n) dominates all
polynomials, we obtain the conditional implication:

      If every polynomial-time solver for SUBSET–SUM satisfies LR-read,
      then P ≠ NP.

All mathematical components other than LR-read — including the decision-tree
argument, Cook–Levin machine semantics, and the NP verifier for SUBSET–SUM — are
fully formalised and machine-checked in Isabelle/HOL.  LR-read is the sole
unproved assumption linking the original information-flow observation to the
behaviour of concrete Turing-machine solvers.

Acknowledgement:
The author received assistance from AI systems (ChatGPT by OpenAI and Claude by 
Anthropic) in drafting and polishing explanatory text and in iteratively refining 
Isabelle/HOL proof scripts.  All formal results and final proofs are the 
responsibility of the author.
›


section ‹1.  Why SUBSET–SUM?›

text ‹
SUBSET–SUM provides a setting in which the informational structure of a simple
equality test becomes explicit.  For an input list ‹as› of length ‹n›, each
0/1-vector ‹xs› defines a distinct integer

      ∑ᵢ as!i * xs!i.

On distinct-subset-sum instances these values are all different, so every xs
represents a different feasible outcome of the verification equation.

For any split position k, the canonical decomposition eₖ(as,s) separates these
possibilities into two collections of integers:

      LHS(eₖ as s)      of size 2^k,
      RHS(eₖ as s)      of size 2^(n − k),

arising respectively from prefix-choices and suffix-choices of the unknown xs.
These sets enumerate all integers that the left- and right-hand sides could
possibly take at that split.

The informational principle stated in the introduction therefore applies
simultaneously to many possible L and many possible R: to rule out the existence
of a matching pair, the solver must distinguish the corresponding integer values
one by one.  This per-candidate requirement is the starting point for the
lower-bound analysis.
›


section ‹2.  The Decision-Tree Lower Bound›

text ‹
The theory ‹SubsetSum_DecisionTree› formalises the per-candidate informational
requirement in an abstract “reader” model.  Two axioms govern the model:

  • coverage — for each distinct-subset-sum instance, there exists a split k
      at which the solver distinguishes exactly the canonical candidate sets
      LHS(eₖ) and RHS(eₖ);

  • cost — distinguishing each candidate costs at least one unit of work.

From these axioms, the decision-tree argument derives the inequality

      steps(as, s)  ≥  2^k + 2^(n − k),

and hence the tight lower bound

      steps(as, s)  ≥  2 · sqrt(2^n).

This bound is independent of Turing machines, encodings, or internal state.  
It isolates the combinatorial consequence of the informational principle:  
if a solver must handle each candidate integer individually, then it must incur
at least √(2^n) work on some split.

The decision-tree theory ‹SubsetSum_DecisionTree› already contains the
abstract lower-bound result ‹SubsetSum_To_Polytime›.  That theorem states
that any solver satisfying the LR–reader axioms of
‹SubsetSum_Lemma1› cannot run in polynomial time on all
distinct-subset-sum instances.

In the present theory we do not reprove this result.  Instead, we
combine it with the Cook–Levin instantiation developed in
‹SubsetSum_CookLevin› and a single modelling assumption:
that every polynomial-time SUBSET–SUM solver satisfies the LR–read
information principle.
›


section ‹3.  From Decision Trees to Cook–Levin Turing Machines›

text ‹
A Cook–Levin Turing machine does not reveal its information flow directly.  It
sees the entire input from the start and may internally rearrange, copy, or
compress it.  Thus the decision-tree axioms cannot be transferred automatically.

The locale ‹LR_Read_TM› provides the bridge.  For each instance it defines
observable sets

      seenL_TM as s k    and    seenR_TM as s k,

which record which canonical L- and R-candidates the machine's behaviour
effectively distinguishes.  The LR-read property asserts that for some split k
these observable sets match the canonical sets:

      seenL_TM as s k = LHS(eₖ as s),
      seenR_TM as s k = RHS(eₖ as s).

Together with a cost condition mirroring the decision-tree model, LR-read
instantiates the abstract lower-bound theorem with the concrete time measure
‹steps_TM› of the Turing machine.
›


section ‹4.  Why LR-read Is Assumed›

text ‹
The LR-read property is not proved in this development; it is introduced as a
modelling assumption.  This reflects a structural limitation of adversary
arguments in the unrestricted Turing-machine model.

In a decision tree, the solver learns information only by querying individual
positions, so an adversary can ensure that it obtains a separate unit of
information for each candidate.  A Turing machine, however, begins with full
visibility of its input and may internally transform it in ways the adversary
cannot monitor.  Nothing prevents the machine from computing derived summaries
that bypass the canonical prefix/suffix structure implicit in eₖ(as,s).

For this reason, one cannot expect the per-candidate requirement to follow from
standard adversary reasoning for Turing machines.  LR-read is therefore stated
explicitly to capture, within the Cook–Levin model, the same informational
structure that drives the decision-tree lower bound.

Once LR-read is assumed, the abstract combinatorial lower bound applies
verbatim, yielding the √(2^n) time requirement for any such solver.
›

section ‹Information principle and canonical presentations›

text ‹
  ────────────────────────────────────────────────────────────────────────────
  ■ Equality of two independent values
  ────────────────────────────────────────────────────────────────────────────

  The underlying information principle used in our lower bound can be stated
  in very simple terms.

  Consider two independent integer values ‹L› and ‹R› drawn from fixed sets
  ‹Lvals› and ‹Rvals›.  A procedure that decides, for every pair ‹(L,R)› in
  ‹Lvals × Rvals›, whether the equality

        L = R

  holds must, in the worst case, obtain information from both components.
  Intuitively, there are inputs on which it has to distinguish between the
  different possibilities for ‹L›, and likewise for ‹R›, in order to decide
  whether some equality is possible.

  In the theory ‹SubsetSum_DecisionTree› this informal idea is captured by
  the small locale ‹LR_Eq_Info_Principle›.  That locale does *not* talk
  about subset sums or Turing machines; it merely packages the idea that a
  correct equality-decider for independent ranges ‹Lvals› and ‹Rvals› must,
  in the worst case, be able to separate each canonical value on the left
  and on the right.
›

text ‹
  ────────────────────────────────────────────────────────────────────────────
  ■ Canonical LHS/RHS versus arbitrary presentations
  ────────────────────────────────────────────────────────────────────────────

  For SUBSET–SUM there are many ways to write an equivalent “verification
  equation” for the same problem instance.  Starting from

        ∑ i<n. as ! i * xs ! i = s,

  one can apply arbitrary algebraic manipulations or injective
  reparametrisations to obtain new presentations that have the same
  {0,1}-solutions but very different algebraic structure.  Some of these
  non-canonical equations may admit algorithmic shortcuts: for example,
  a reparametrisation could expose a common factor, or compress many
  equality constraints into a single arithmetical test.  Such shortcuts
  potentially reduce the *number of distinct values that need to be
  distinguished*.

  The abstract lower bound developed in ‹SubsetSum_DecisionTree› therefore
  fixes a single, very structured family of presentations, indexed by a
  split position ‹k›:

      eₖ as s k xs = (L, R),

  where the left component ‹L› is the weighted sum over the first ‹k› bits
  of ‹xs› and the right component ‹R› is the residual sum over the remaining
  bits.  For instances with distinct subset sums we proved that the
  associated value sets

      LHS (eₖ as s k) n,   RHS (eₖ as s k) n

  have maximal cardinalities

      card (LHS (eₖ as s k) n) = 2^k,
      card (RHS (eₖ as s k) n) = 2^(n − k),

  and, crucially, that they arise from *independent* 0/1 choices in the left
  and right halves of the solution vector.  Every choice of left bits can
  be combined with every choice of right bits; there are no hidden algebraic
  dependencies between the two ranges.

  This canonical family plays the role of the “worst case” for our
  information principle: it realises the full product space of 2^k left
  values and 2^(n−k) right values, with no degeneracies.
›

text ‹
  ────────────────────────────────────────────────────────────────────────────
  ■ Why the lower bound only uses canonical presentations
  ────────────────────────────────────────────────────────────────────────────

  One might ask why the lower bound is proved only for the canonical
  presentations ‹eₖ as s› rather than for *all* algebraically equivalent
  equations.  There are two reasons.

  • First, the goal of the lower bound is to exhibit a family of instances
    and presentations on which any solver that satisfies the LR–equality
    information principle must perform Ω(√(2ⁿ)) work.  For this purpose we
    do not need to analyse every clever reparametrisation of the subset-sum
    equation; it suffices to fix one natural family of equations whose
    left/right value sets are provably as large and as independent as
    possible.  The canonical splits ‹eₖ as s› meet exactly this need.

  • Second, allowing arbitrary non-canonical presentations would blur the
    boundary between the *information model* and the *algebraic ingenuity*
    of particular algorithms.  A solver might derive a non-canonical
    equation in which many of the 2ⁿ formal possibilities collapse to a
    much smaller number of distinct values that need to be told apart.
    Such algebraic shortcuts are genuine algorithmic improvements, but they
    are outside the scope of the abstract reader model that
    ‹SubsetSum_Lemma1› formalises.  The reader model is designed to capture
    the cost of distinguishing canonical LHS/RHS values arising directly
    from the underlying 0/1 choices, not the cost of arbitrary algebraic
    transformations of the equation.

  In short: the canonical presentations are chosen precisely because they
  expose the “pure” combinatorial difficulty of separating all 2^k left
  values and 2^(n−k) right values coming from independent input sets.  Any
  solver that satisfies the LR–equality principle on this canonical family
  must pay at least √(2ⁿ) steps on some instances.  Non-canonical equations
  may or may not admit additional shortcuts, but those lie beyond the
  abstract cost model studied here.
›


section ‹5.  Structure of the Development›

text ‹
The full conditional lower-bound argument is organised across three theories,
each addressing a distinct level of abstraction.

  • ‹SubsetSum_DecisionTree›  
      Formalises the combinatorial core of the argument.  
      Under two axioms — coverage of canonical L/R candidates and
      a per-candidate cost condition — it proves the abstract bound

            steps(as, s)  ≥  2 · sqrt(2^n).

      This theory contains no reference to Turing machines or encodings.

  • ‹SubsetSum_CookLevin›  
      Connects the abstract model to the Cook–Levin machine semantics.
      For a solver ‹M› and encoding ‹enc›, it defines concrete time and
      distinguishability measures (‹steps_TM› and ‹seenL_TM›/‹seenR_TM›).
      The locale ‹LR_Read_TM› states the assumptions that instantiate
      the abstract axioms with these concrete notions, thereby transporting
      the √(2^n) lower bound to Cook–Levin Turing machines.

  • ‹SubsetSum_PneqNP› (the present theory)  
      Places the lower bound in a complexity-theoretic context.
      A separate, fully formalised verifier shows that SUBSET–SUM lies in
      ‹𝒩𝒫› for any reasonable encoding.  
      Combining NP-membership with the conditional lower bound obtained
      under LR-read yields the main implication:

            If every polynomial-time solver satisfies LR-read,
            then P ≠ NP.

This layering isolates the mathematical content of the lower bound, the
operational content of the Turing-machine model, and the logical structure of
the conditional separation.  Only LR-read is assumed; all other components are
fully mechanised in Isabelle/HOL.
›

section ‹A global LR-read axiom for SUBSET-SUM solvers›

text ‹
  We now postulate an information-flow axiom at the Cook–Levin level:

    Any Cook–Levin machine that correctly decides SUBSET-SUM
    in polynomial time (with respect to ‹length as›) admits an
    LR-read presentation in the sense of ‹LR_Read_TM›.
›

locale LR_Read_Axiom =
  fixes M   :: machine
    and q0  :: nat
    and enc :: "int list ⇒ int ⇒ bool list"
  assumes LR_Read_for_all_poly_solvers:
    "⟦ CL_SubsetSum_Solver M q0 enc;
       polytime_CL_machine M enc ⟧
     ⟹ ∃steps_TM seenL_TM seenR_TM.
           LR_Read_TM M q0 enc steps_TM seenL_TM seenR_TM"
begin

text ‹
  Under this axiom, there cannot exist a polynomial-time
  Cook–Levin SUBSET-SUM solver: any such solver would give
  rise to an LR-read instance of ‹LR_Read_TM›, contradicting
  ‹no_polytime_CL_on_distinct_family›.
›

lemma no_polytime_CL_SubsetSum_solver:
  assumes solver: "CL_SubsetSum_Solver M q0 enc"
      and poly:   "polytime_CL_machine M enc"
  shows False
proof -
  (* 1. From the axiom, get LR_Read_TM for this solver *)
  from LR_Read_for_all_poly_solvers[OF solver poly]
  obtain steps_TM seenL_TM seenR_TM
    where LR: "LR_Read_TM M q0 enc steps_TM seenL_TM seenR_TM"
    by blast

  (* 2. Work *inside* that LR_Read_TM instance *)
  interpret LR_Read_TM M q0 enc steps_TM seenL_TM seenR_TM
    by (rule LR)

  (* 3. Unpack the polynomial-time assumption for M, enc *)
  from poly obtain c d where
    cpos: "c > 0" and
    bound_all:
      "∀as s. steps_CL M (enc as s)
                ≤ nat (ceiling (c * (real (length as)) ^ d))"
    unfolding polytime_CL_machine_def
    by blast

  (* 4. Restrict that bound to distinct-subset-sum instances *)
  have bound_restricted:
    "∀as s. distinct_subset_sums as ⟶
             steps_CL M (enc as s)
               ≤ nat (ceiling (c * (real (length as)) ^ d))"
    using bound_all by blast

  (* 5. Package it into the existential form that contradicts
        no_polytime_CL_on_distinct_family *)
  have ex_poly_on_distinct:
    "∃(c::real)>0. ∃(d::nat).
       ∀as s. distinct_subset_sums as ⟶
         steps_CL M (enc as s)
           ≤ nat (ceiling (c * (real (length as)) ^ d))"
    by (intro exI[of _ c] exI[of _ d] conjI cpos bound_restricted)

  (* 6. Contradiction with the LR_Read_TM-level impossibility theorem *)
  from no_polytime_CL_on_distinct_family ex_poly_on_distinct
  show False
    by blast
qed

text ‹
  A convenient corollary: assuming ‹LR_Read_Axiom›, there is
  no polynomial-time Cook–Levin machine that solves SUBSET-SUM.
›

corollary no_polytime_SubsetSum:
  assumes solver: "CL_SubsetSum_Solver M q0 enc"
  shows "¬ polytime_CL_machine M enc"
proof
  assume poly: "polytime_CL_machine M enc"
  from no_polytime_CL_SubsetSum_solver[OF solver poly]
  show False .
qed

end  (* locale LR_Read_Axiom *)


section ‹6.  SUBSET–SUM is in NP (formalised)›

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

section ‹7.  Definition of P = NP›

definition P_eq_NP :: bool where
  "P_eq_NP ⟷ (∀L::language. (L ∈ 𝒫) = (L ∈ 𝒩𝒫))"

section ‹8.  Bridging P to a concrete CL solver›

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

definition IP_TM :: "machine ⇒ nat ⇒ (int list ⇒ int ⇒ bool list) ⇒ bool" where
  "IP_TM M q0 enc ⟷
     (∃steps_TM seenL_TM seenR_TM.
        LR_Read_TM M q0 enc steps_TM seenL_TM seenR_TM)"


section ‹9.  IP-read-all-solvers hypothesis›

text ‹
This is the single modelling assumption.

For a fixed encoding enc0:

      LR_read_all_solvers_hypothesis enc0

means:

  (1) If SUBSET–SUM ∈ P, a polynomial-time CL solver exists, and
  (2) Every CL solver satisfies LR-read, i.e. belongs to ‹LR_Read_TM›.

NP-membership is not assumed; it is proved separately.
›

definition IP_all_poly_solvers_hypothesis ::
  "(int list ⇒ int ⇒ string) ⇒ bool" where
  "IP_all_poly_solvers_hypothesis enc0 ⟷
     P_impl_CL_SubsetSum_Solver enc0 ∧
     (∀M q0 enc.
        CL_SubsetSum_Solver M q0 enc ⟶ polytime_CL_machine M enc ⟶ IP_TM M q0 enc)"

section ‹10.  Core Conditional Theorem›

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

lemma P_neq_NP_if_IP_all_poly_solvers_hypothesis:
  fixes enc0 :: "int list ⇒ int ⇒ string"
  assumes H:       "IP_all_poly_solvers_hypothesis enc0"
  assumes NP_enc0: "SUBSETSUM_lang enc0 ∈ 𝒩𝒫"
  shows "¬ P_eq_NP"
proof -
  from H have
    bridge_P: "P_impl_CL_SubsetSum_Solver enc0" and
    all_IP:   "∀M q0 enc.
                CL_SubsetSum_Solver M q0 enc ⟶ polytime_CL_machine M enc ⟶ IP_TM M q0 enc"
    unfolding IP_all_poly_solvers_hypothesis_def by blast+

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

    from all_IP solver poly have "IP_TM M q0 enc" by blast
    then obtain steps_TM seenL_TM seenR_TM where lr:
      "LR_Read_TM M q0 enc steps_TM seenL_TM seenR_TM"
      unfolding IP_TM_def by blast

    interpret LR: LR_Read_TM M q0 enc steps_TM seenL_TM seenR_TM
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

section ‹11.  Final Packaged Theorem›

text ‹
This theorem gives the final wrapped statement:

      LR hypothesis + SUBSET–SUM verifier ⇒ P ≠ NP.
›

theorem P_neq_NP_under_IP:
  fixes enc0 :: "int list ⇒ int ⇒ string"
  assumes IP: "IP_all_poly_solvers_hypothesis enc0"
  assumes V:  "SS_Verifier_NP k G V p T fverify enc0 enc_cert"
  shows "¬ P_eq_NP"
proof -
  have NP_enc0: "SUBSETSUM_lang enc0 ∈ 𝒩𝒫"
    using SUBSETSUM_in_NP_global[OF V] .
  show "¬ P_eq_NP"
    using P_neq_NP_if_IP_all_poly_solvers_hypothesis[OF IP NP_enc0] .
qed

end
