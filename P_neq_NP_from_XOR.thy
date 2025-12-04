theory SubsetSum_PneqNP
  imports SubsetSum_CookLevin
begin

text ‹
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                                                            %
%        A CONDITIONAL PROOF THAT P != NP FROM AN INFORMATION-FLOW PRINCIPLE %
%                                                                            %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

This chapter explains, in non-technical terms, the structure of the conditional
argument formalised in this theory.  The goal is to state clearly which parts of
the development are fully proved in Isabelle/HOL, and which part is assumed as a
modeling axiom.

The main result has the following form:

      If every Turing machine solving SUBSET-SUM satisfies a certain
      information-flow property (the LR-read property), then P != NP.

The information-flow principle is intuitive:

      To decide whether two quantities L and R are equal, a solver must read
      at least one bit of the input that encodes L and at least one bit of the
      input that encodes R.

This development formalises the lower-bound core of:

      C. A. Feinstein,
      "Dialogue Concerning the Two Chief World Views",
      arXiv:1605.08639.

The author of this formalisation received assistance from two AI systems —
ChatGPT (OpenAI) and Claude (Anthropic). Their assistance consisted of
drafting and refining explanatory text, improving the readability of the
introduction and comments, and helping diagnose or structure Isabelle/HOL
proof scripts. All proofs in this theory have been verified directly by Isabelle/HOL.
The only non-proved ingredient is the LR-read assumption, which is exposed 
explicitly as a modeling hypothesis.

-------------------------------------------------------------------------------
1.  Why SUBSET-SUM?
-------------------------------------------------------------------------------

The SUBSET-SUM problem asks whether, for a list of integers
  as = [a0, ..., a_(n-1)]
and a target s, there exists a 0/1-vector xs such that

      sum_{i < n} as!i * xs!i = s.

Among NP-complete problems, SUBSET-SUM has a particularly transparent
combinatorial structure.  For well-chosen inputs — for example, as being
powers of two — all 2^n subset sums are distinct.  These instances serve as the
canonical hard family for adversarial lower-bound arguments.

-------------------------------------------------------------------------------
2.  The Decision-Tree Lower Bound
-------------------------------------------------------------------------------

The theory SubsetSum_DecisionTree defines an abstract "reader" model and
proves the lower bound

      steps(as, s) >= 2 * sqrt(2^n)

on all instances with distinct subset sums.

The model views computation as an adversary game:

  • The solver reads bits of the real input (as, s).
  • An adversary tracks all virtual completions xs in {0,1}^n that remain
    compatible with everything the solver has read.
  • For each split k, the canonical equation e_k(as, s) decomposes the sum
    into a left part depending on xs[0 .. k-1] and a right part depending on
    xs[k .. n-1].

As xs varies, these define sets LHS(e_k) and RHS(e_k) of sizes 2^k and 2^(n-k).
The abstract axioms of SubsetSum_Lemma1 state that:

  • the solver's information flow aligns with LHS(e_k) and RHS(e_k) for some k;
  • each distinguishable L- or R-value costs at least one unit of work.

This yields the lower bound 2^k + 2^(n-k), minimised at 2 * sqrt(2^n).

-------------------------------------------------------------------------------
3.  From Decision Trees to Turing Machines
-------------------------------------------------------------------------------

A Cook–Levin Turing machine is more flexible than a decision tree: it may
reorder, compress, or duplicate the input arbitrarily.  The decision-tree
bound does not automatically carry over.

To bridge the gap, the locale LR_Read_TM formalises the key information-flow
property:

      To decide L = R, the solver must actually read information from both
      the L-zone and the R-zone of the input encoding.

Inside LR_Read_TM, the "seen" sets satisfy the axioms of SubsetSum_Lemma1, so
every solver with LR-read inherits the sqrt(2^n) lower bound for its
Cook–Levin step count.

-------------------------------------------------------------------------------
4.  Why LR-read is Assumed
-------------------------------------------------------------------------------

The central assumption of this theory is:

      Every Turing-machine solver for SUBSET-SUM satisfies the LR-read property.

This is not proved.  It is a modeling axiom.

If one could prove that all SUBSET-SUM solvers necessarily satisfy LR-read,
then the lower bound in LR_Read_TM would imply SUBSET-SUM not in P, and hence
P != NP.  The purpose of this theory is to isolate LR-read as the single
nontrivial assumption needed to convert the formal lower bound into a full
complexity separation.

-------------------------------------------------------------------------------
5.  Logical Structure of the Development
-------------------------------------------------------------------------------

The formalisation separates into three layers:

(1) Lower-bound kernel (proved)
      SubsetSum_DecisionTree + SubsetSum_Lemma1 give a sqrt(2^n) lower bound
      for any model satisfying the abstract axioms.

(2) Cook–Levin bridge (proved)
      SUBSET-SUM is represented in the Cook–Levin Turing-machine framework.
      LR_Read_TM expresses LR-read for machines in that model.

(3) One explicit modeling assumption (LR-read)
      Every solver for SUBSET-SUM satisfies LR-read.

Together these yield the conditional statement:

      If SUBSET-SUM is in P and every solver satisfies LR-read,
      then P != NP.

-------------------------------------------------------------------------------
6.  Relation to Feinstein (2016)
-------------------------------------------------------------------------------

Feinstein's original argument suggested that verifying an equality of two
subset-sum expressions intrinsically requires exploring many configurations.
This development extracts the underlying combinatorial principle, formalises
the decision-tree lower bound, and identifies LR-read as the exact structural
assumption required to derive a Turing-machine lower bound.

-------------------------------------------------------------------------------
7.  Perspective
-------------------------------------------------------------------------------

This is not a proof of P != NP.  It is a clean demonstration of how a
lower-bound argument separates into a mechanised core and one explicit
modeling hypothesis.  Should LR-read be justified independently, the
separation P != NP would follow mechanically.

-------------------------------------------------------------------------------
8.  Final Conditional Theorem
-------------------------------------------------------------------------------

The main theorem proved here is:

      Assuming that every SUBSET-SUM solver satisfies LR-read,
      we have P != NP.

The contribution is therefore twofold:
  (a) a fully formalised lower-bound engine for SUBSET-SUM, and
  (b) a single, transparent assumption specifying exactly what remains
      to be shown for the argument to become unconditional.

  ---------------------------------------------------------------------------
  SUBSET–SUM is in NP (formalised)
  ---------------------------------------------------------------------------

  The Cook–Levin AFP library does not provide “SUBSET–SUM ∈ NP” as a built-in
  fact.  Instead, the NP-membership result must be *derived* from a verifier
  machine packaged by `SS_Verifier_NP`.

  This verifier machine gives:

     • an explicit certificate encoding,
     • a polynomial-time verifier Turing machine,
     • correctness (accepts iff the subset-sum equation holds).

  From the existence of such a verifier we obtain:

       SUBSETSUM_lang enc0 ∈ 𝒩𝒫.

  This is the standard NP-definition: NP = languages with polynomial-time
  verifiers.  Thus this lemma is the canonical "SUBSET–SUM is in NP" statement
  in the Cook–Levin framework.
›

lemma SUBSETSUM_in_NP_global:
  assumes "SS_Verifier_NP k G V p T fverify enc0 enc_cert"
  shows "SUBSETSUM_lang enc0 ∈ 𝒩𝒫"
  using SUBSETSUM_in_NP_from_verifier[OF assms] .


text ‹
  ---------------------------------------------------------------------------
  P = NP (definition)
  ---------------------------------------------------------------------------

  This definition is the usual one: P = NP means that *every* language is in P
  iff it is in NP.  We use a direct quantification over languages to keep the
  statement fully abstract.
›

definition P_eq_NP :: bool where
  "P_eq_NP ⟷ (∀L::language. (L ∈ 𝒫) = (L ∈ 𝒩𝒫))"


text ‹
  ---------------------------------------------------------------------------
  If SUBSET–SUM is in P, then some CL Turing machine solves it in polytime.
  ---------------------------------------------------------------------------

  This definition is the necessary “bridge” from *function-space complexity*
  (P/NP over string languages) to *machine semantics* in the Cook–Levin world.

  `P_impl_CL_SubsetSum_Solver enc0` means:

       If SUBSETSUM_lang enc0 ∈ P,
       then there exists a concrete Turing machine M (in the CL model)
       that solves it in polynomial time.

  This connects the *language-level* assumption “SUBSET–SUM is in P”
  to a *machine-level* solver that can be analysed using the LR-Read locale
  and the step-count.

  Note that the encoding `enc` used by the concrete Cook–Levin machine
  need not coincide with `enc0`; the definition only demands that *some*
  CL-machine/encoding pair solves the same underlying SUBSET-SUM instances
  in polynomial time.
›

definition P_impl_CL_SubsetSum_Solver ::
  "(int list ⇒ int ⇒ string) ⇒ bool" where
  "P_impl_CL_SubsetSum_Solver enc0 ⟷
     (SUBSETSUM_lang enc0 ∈ 𝒫 ⟶
        (∃M q0 enc.
           CL_SubsetSum_Solver M q0 enc ∧
           polytime_CL_machine M enc))"


text ‹
  ---------------------------------------------------------------------------
  LR_read_all_solvers_hypothesis (the single modelling assumption)
  ---------------------------------------------------------------------------

  IMPORTANT:
  This is no longer a Boolean *constant* asserting “∃ enc0 …”.
  It is now a *predicate* in the encoding `enc0`.

  The intended interpretation is:

      Fix an encoding enc0.
      Assume that every solver for SUBSET–SUM under this encoding
      satisfies LR-read.

  Formally:

     LR_read_all_solvers_hypothesis enc0  ≡
        (1) If SUBSET–SUM is in P, then some CL solver exists, AND
        (2) Every CL solver satisfies LR-Read.

  Note: SUBSET–SUM ∈ NP is *not* built into this hypothesis, because
        we prove NP-membership externally from `SS_Verifier_NP`.

  This makes the logic cleaner: the hypothesis expresses exactly the LR
  assumption and the P→“machine exists” bridge, while the NP fact is derived
  separately from the verifier.
›

definition LR_read_all_solvers_hypothesis ::
  "(int list ⇒ int ⇒ string) ⇒ bool" where
  "LR_read_all_solvers_hypothesis enc0 ⟷
     P_impl_CL_SubsetSum_Solver enc0 ∧
     (∀M q0 enc.
        CL_SubsetSum_Solver M q0 enc ⟶
          (∃seenL seenR. LR_Read_TM M q0 enc seenL seenR))"

text ‹
  ---------------------------------------------------------------------------
  Core conditional theorem:
      LR assumption + SUBSET–SUM ∈ NP  ⇒  P != NP
  ---------------------------------------------------------------------------

  This lemma isolates the logical heart of the argument.

  Inputs:
     (1) LR_read_all_solvers_hypothesis enc0
          — every solver satisfies LR-read (modelling axiom)
     (2) SUBSETSUM_lang enc0 ∈ NP
          — derived separately from SS_Verifier_NP

  Output:
     P != NP.

  The proof is by contradiction:
     assume P = NP,
     deduce that SUBSET–SUM ∈ P,
     therefore get a polynomial-time solver M,
     apply LR-read,
     obtain a lower bound ≥ sqrt(2^n),
     contradict polynomial time.
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


text ‹
  ---------------------------------------------------------------------------
  Final packaged theorem (convenience statement)
  ---------------------------------------------------------------------------

  This wraps the previous lemma together with SUBSETSUM_in_NP_global.

  If the user *already* has a verifier `SS_Verifier_NP` for the encoding enc0,
  then this theorem states the main result in a single line:

       LR hypothesis  +
       SUBSET–SUM verifier
       ⇒  P != NP.

  This theorem is logically redundant, but extremely useful
  as the “headline statement” of the entire development.
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

end  (* theory *)
