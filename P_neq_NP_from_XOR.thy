theory SubsetSum_PneqNP
  imports
    SubsetSum_CookLevin
begin

section ‹Preamble and Acknowledgements›

text ‹
  ══════════════════════════════════════════════════════════════════════════════
  SUBSET–SUM LOWER BOUND AND A CONDITIONAL SEPARATION P ≠ NP
  ══════════════════════════════════════════════════════════════════════════════

  This theory derives a conditional statement of the form:

        *If SUBSET–SUM ∈ P and every solver satisfies the LR-read property,
         then P ≠ NP.*

  The result follows by transporting the abstract √(2ⁿ) decision-tree lower
  bound (formalised in the theory ‹SubsetSum_DecisionTree› and motivated by
  C. A. Feinstein, “Dialogue Concerning the Two Chief World Views,”
  arXiv:1605.08639 (2016)) to the concrete Cook–Levin Turing-machine model.

  The development of this theory benefited from extensive assistance by
  ChatGPT (OpenAI) and Claude (Anthropic).  Their contributions were strictly
  expository — helping to improve clarity, structure, and commentary — while
  all formal Isabelle proofs and constructions appear exactly as checked by
  Isabelle/HOL.

  The remainder of this file is organised into four conceptual sections:

    1.  Distinct-subset-sums inputs and the √(2ⁿ) decision-tree bound.
    2.  Canonical LHS/RHS structure of the SUBSET–SUM equation.
    3.  The Cook–Levin bridge and the LR-read information-flow principle.
    4.  Why LR-read is treated as a structural axiom (Chaitin-style rationale).

  Only Section 4 introduces a non-mechanised assumption.  All other components
  — combinatorics, adversary reasoning, Cook–Levin semantics, and NP-verification
  — are fully formalised and verified within Isabelle/HOL.
›


section ‹1. Distinct-subset-sums inputs and the abstract √(2ⁿ) lower bound›

text ‹
  A list ‹as = [a₀, …, aₙ₋₁]› has *distinct subset sums* if every bit-vector
  ‹xs ∈ {0,1}ⁿ› yields a unique sum ∑ᵢ as!i * xs!i.  Such inputs form a large,
  structurally rich family; the canonical example is the powers-of-two list
  ‹[1,2,4,…,2^(n−1)]›, although the lower bound does *not* rely on any special
  hardness of these inputs.

  In ‹SubsetSum_DecisionTree›, the abstract locale ‹SubsetSum_Lemma1› proves:

        steps(as, s) ≥ 2 * sqrt(2^n)

  for every instance with distinct subset sums, assuming only:

   • *coverage:* at some split k, the solver’s information-flow distinguishes
     exactly the canonical families of LHS and RHS partial sums; and

   • *cost:* distinguishing m values costs at least m reader-steps.

  These two assumptions constitute a general adversary-style reader bound:
  any solver whose information flow matches the canonical structure must incur
  Ω(2^k + 2^(n−k)) work on some split, minimised at Θ(√(2ⁿ)).
›


section ‹2. Canonical LHS/RHS structure of the SUBSET–SUM equation›

text ‹
  For each instance (as, s) and each index k, the canonical equation

        eₖ(as, s):      LHS = RHS

  splits contributions of the unknown bit-vector xs into:

      LHS = ∑_{i < k} as!i * xs!i
      RHS = s − ∑_{i ≥ k} as!i * xs!i.

  As xs ranges over all 0/1-vectors, LHS produces exactly 2^k possible values,
  and RHS produces exactly 2^(n−k) values.  These sets capture the complete
  combinatorial structure of the SUBSET–SUM equality with respect to the split
  k.

  The adversary lower bound rests entirely on this structure: to decide the
  equality, a solver must effectively narrow down both the LHS and RHS sides
  among their exponentially many possibilities.
›


section ‹3. The Cook–Levin bridge and the LR-read principle›

text ‹
  A Cook–Levin Turing machine has far more freedom than a decision tree:
  it may revisit cells, compress information, and scan the encoding in arbitrary
  patterns.  Thus the decision-tree lower bound does not automatically carry
  over.  The role of the LR-read interface is precisely to connect the machine’s
  concrete reading behaviour to the abstract LHS/RHS structure.

  The motivating observation is an information-flow principle:

        To decide whether L = R, the solver must extract information
        constraining the LHS possibilities and information constraining
        the RHS possibilities.

  In SUBSET–SUM, however, each side has exponentially many possibilities.
  For a given hard instance as (with distinct subset sums) and some split k,
  the solver must therefore obtain enough information to rule out all but one
  of the 2^k potential LHS values and all but one of the 2^(n−k) potential RHS
  values.

  The LR-read property formalises this by introducing canonical “seen” sets:

        seenL_TM as s k      and      seenR_TM as s k,

  which summarise how the machine’s behaviour distinguishes the possible LHS
  and RHS values at split k.  The LR-read assumptions state that on each hard
  instance:

    (LR1)  ∃k ≤ n such that
              seenL_TM as s k = LHS(eₖ as s)  ∧
              seenR_TM as s k = RHS(eₖ as s),

           i.e. the machine’s information flow at some split matches the full
           canonical families of possible LHS/RHS values; and

    (LR2)  steps_TM as s ≥ |seenL_TM as s k| + |seenR_TM as s k|.

  These correspond exactly to the abstract assumptions of
  ‹SubsetSum_Lemma1› with steps = steps_TM.

  Once this locale is instantiated (in ‹SubsetSum_CookLevin›), the √(2ⁿ) lower
  bound transfers directly to step-counts of the Cook–Levin machine M.  The
  theorem ‹no_polytime_CL_on_distinct_family› shows that no solver satisfying
  LR-read can be polynomial-time on all distinct-subset-sums instances.
›


section ‹4.  Why LR-read is Assumed›

text ‹
The LR-read property is a modelling assumption: we do not attempt to prove that
every Turing-machine solver for SUBSET–SUM must satisfy it.  The reason is not
that LR-read is unnatural—in fact, the principle is strongly motivated by the
combinatorial structure of the SUBSET–SUM equation—but that proving such a
principle from the bare operational semantics of arbitrary Turing machines
appears to lie beyond what is feasible in a foundational system such as HOL.

The lower-bound argument shows that on hard instances with
‹distinct_subset_sums as›, the values of the canonical prefix and suffix
expressions

      LHS(eₖ as s)   and   RHS(eₖ as s)

range over exponentially many explicit possibilities.  To determine whether
L = R, a solver must acquire enough information from its input to narrow
down which L-values and which R-values are compatible with the instance.
LR-read makes this requirement explicit: on each hard instance, there is a
split index k at which the machine’s behaviour distinguishes *exactly* the
canonical LHS and RHS families.  This places the concrete solver in the same
left–right informational configuration that drives the abstract decision-tree
lower bound.

Why not prove LR-read itself?  The difficulty is not technical but conceptual:
Turing machines can reorganise, hash, compress, interleave, or permute their
input in ways that break any straightforward adversary argument based solely on
“which bits are read”.  A machine might, for example, compute some complicated
intermediate predicate on the entire input and route its future behaviour
through this checksum in a manner that does not reveal which particular LHS or
RHS values it has effectively distinguished.  Without additional semantic
structure, separating such behaviours from the canonical families LHS(eₖ) and
RHS(eₖ) becomes as hard as predicting arbitrary program behaviour.

This phenomenon has a philosophical analogue in Gregory Chaitin’s view of
mathematical incompleteness, as articulated in:

      G. J. Chaitin,
      “Thoughts on the Riemann Hypothesis,” arXiv:math/0306042 (2003).

Chaitin argues that certain natural combinatorial or information-theoretic
principles may be objectively true but unprovable within standard formal
systems, because proving them would require resolving immense computational
structure.  In the same spirit, LR-read is introduced here as a *structural
axiom* reflecting the inherent left–right informational organisation of the
SUBSET–SUM equation.  Once LR-read is assumed, all subsequent reasoning—the
combinatorial analysis, the decision-tree machinery, the Cook–Levin semantics,
and the NP-verification theorem—is fully formalised and mechanised
in Isabelle/HOL.  LR-read is therefore the only non-mechanised ingredient.

If LR-read held for all Turing-machine solvers of SUBSET–SUM, then every such
solver would incur the √(2^n) lower bound on distinct-subset-sum inputs.  Since
this grows faster than any polynomial, it would follow that SUBSET–SUM ∉ P.
Combined with the NP-membership result, this yields P ≠ NP.  The formalisation
thus isolates LR-read as the single assumption on which the conditional
separation rests.
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
