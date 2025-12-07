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
argument formalised in this theory.  The goal is to identify precisely:

  • which components are fully proved in Isabelle/HOL, and
  • which assumption — the LR-read hypothesis — remains external.

The main result has the form:

      If every Turing machine solving SUBSET–SUM satisfies the LR-read
      information-flow property, then P != NP.

The information-flow principle is intuitive:

      To decide whether two quantities L and R are equal,
      a solver must read at least one bit of the input encoding L
      and at least one bit encoding R.

This formalisation extracts and isolates the lower-bound mechanism behind:

      C. A. Feinstein,
      "Dialogue Concerning the Two Chief World Views",
      arXiv:1605.08639.

AI systems (ChatGPT and Claude) assisted in structuring and improving comments.
Every formal proof is verified by Isabelle/HOL.  The *only* non-proved ingredient
is the LR-read assumption, which is made explicit and never used implicitly.
›


section ‹1.  Why SUBSET–SUM?›

text ‹
The SUBSET–SUM problem asks whether for integers

    as = [a₀, …, aₙ₋₁]   and   target s

there exists a 0/1-vector xs such that

      ∑ᵢ as!i * xs!i = s.

For certain inputs — for example, as = [1,2,4,…,2ⁿ⁻¹] — all 2ⁿ subset sums are
distinct.  More generally, any list as whose subset sums are all different is
called a distinct-subset-sum instance.  The lower-bound argument focuses on the *class* 
of such instances as the canonical adversarial family: they realise the maximal number 2ⁿ 
of different subset sums, but no special algorithmic hardness is assumed for the 
powers-of-two examples beyond this property.
›


section ‹2.  The Decision-Tree Lower Bound›

text ‹
The theory SubsetSum_DecisionTree defines an abstract “reader” model and proves:

      steps(as, s)  ≥  2 * sqrt(2^n)

for all lists as of length n having distinct subset sums.

The model is an adversary game:

  • the solver reads bits of the true input (as, s),
  • the adversary tracks all virtual completions xs ∈ {0,1}ⁿ still compatible,
  • for each split k, the canonical equation eₖ(as,s) decomposes the sum:

        LHS depends on xs[0..k−1] and
        RHS depends on xs[k..n−1].

As xs ranges, LHS and RHS vary over sets of sizes 2^k and 2^(n−k).  
The axioms of SubsetSum_Lemma1 require:

  (A1) the solver’s information flow matches these canonical LHS/RHS sets  
  (A2) each distinguishable value costs ≥ 1 step.

Thus:

      steps ≥ 2^k + 2^(n−k),

minimised at 2 * sqrt(2^n).
›


section ‹3.  From Decision Trees to Cook–Levin Turing Machines›

text ‹
A Cook–Levin Turing machine is far more flexible than a decision tree: it may
scan, move, rewrite, or revisit input cells arbitrarily.  Thus the abstract
decision-tree lower bound does *not* automatically apply to machines.  To
transfer it, we must express the same information-flow constraints inside the
Cook–Levin model.

This bridge is provided by the locale ‹LR_Read_TM›.

──────────────────────────────────────────────────────────────────────────────
Informal principle
──────────────────────────────────────────────────────────────────────────────

    “To decide L = R, a solver must actually read information
     coming from the L-zone and from the R-zone of the input encoding.”

If two different L-values always drive the solver along the same execution
path, then the solver has *not* extracted information from the L-zone: those
L-values are behaviourally indistinguishable.  The same reasoning applies to
the R-zone.

──────────────────────────────────────────────────────────────────────────────
Turning the informal idea into a precise requirement
──────────────────────────────────────────────────────────────────────────────

Inside ‹LR_Read_TM›, this idea is made concrete by defining, for each split
index k:

  • ‹seenL_TM as s k› — the set of canonical LHS values the machine
    behaviourally distinguishes when we vary only the prefix bits of a virtual
    completion xs;

  • ‹seenR_TM as s k› — the corresponding set of distinguishable RHS values
    obtained by varying only the suffix bits of xs.

These sets capture exactly what the machine has *learned* from the L-zone and
the R-zone of the encoded input.

The LR-read hypothesis strengthens the informal principle into a precise
requirement: on every distinct-subset-sum instance (as, s) there exists some k
such that

      seenL_TM as s k = LHS(eₖ as s)
      seenR_TM as s k = RHS(eₖ as s).

At this “critical split,” the machine’s behaviour distinguishes *all* and only
the canonical LHS/RHS values arising from varying prefix/suffix bits of xs.
This is the exact formal counterpart of the slogan “the solver really reads the
L-zone and the R-zone.”

──────────────────────────────────────────────────────────────────────────────
Cost axiom
──────────────────────────────────────────────────────────────────────────────

A second LR-Read axiom captures the cost principle:

      steps_TM as s ≥ |seenL_TM as s k| + |seenR_TM as s k|.

Each distinguishable L-value costs at least one unit of work, and so does each
distinguishable R-value.

──────────────────────────────────────────────────────────────────────────────
Recovering the decision-tree lower bound
──────────────────────────────────────────────────────────────────────────────

For distinct-subset-sum inputs we know:

      |LHS(eₖ as s)| = 2^k,
      |RHS(eₖ as s)| = 2^(n − k).

Therefore, when the LR-read equalities hold, we obtain

      steps_TM as s ≥ 2^k + 2^(n − k) ≥ 2 * sqrt(2^n).

Hence the Cook–Levin machine inherits *exactly* the √(2^n) lower bound from
the abstract decision-tree model.  The locale ‹LR_Read_TM› is the mechanism
that allows us to instantiate ‹SubsetSum_Lemma1› with concrete Cook–Levin TM
data.
›


section ‹4.  Why LR-read is Assumed›

text ‹
The LR-read property is a modeling assumption: we do not attempt to prove that
every SUBSET–SUM solver satisfies it.  We state it explicitly and use it as a
hypothesis.

If LR-read held for all Turing machines solving SUBSET–SUM, then the √(2^n)
lower bound established in ‹LR_Read_TM› would apply universally.  Since √(2^n)
grows faster than any polynomial, this would imply SUBSET–SUM ∉ P.  Combined
with SUBSET–SUM ∈ NP, we would conclude P ≠ NP.

The purpose of this formalisation is therefore to isolate LR-read as the *only*
non-mechanised ingredient: the combinatorial reasoning, decision-tree lower
bound, Cook–Levin semantics, and NP-verifier are all fully formalised.
›


section ‹5.  Logical Structure›

text ‹
The development is organised in three layers:

  (1) Lower-bound kernel — *proved*  
      Theories ‹SubsetSum_DecisionTree› and ‹SubsetSum_Lemma1› prove a
      √(2^n) lower bound under abstract L/R-information axioms.

  (2) Cook–Levin bridge — *proved*  
      The locale ‹LR_Read_TM› formalises how the behaviour of a concrete
      Turing machine induces the distinguishability sets ‹seenL_TM› and
      ‹seenR_TM› needed to instantiate the abstract lemma.

  (3) Modeling assumption — *not proved*  
      Every solver for SUBSET–SUM satisfies LR-read.

Together these yield the conditional statement:

      If SUBSET–SUM ∈ P and all solvers satisfy LR-read,
      then P ≠ NP.
›


section ‹6.  Relation to Feinstein (2016)›

text ‹
Feinstein argued informally that verifying equality of two subset-sum
expressions requires exploring many combinations of prefix/suffix choices for
xs.  This development captures the combinatorial essence of that reasoning via
the families LHS(eₖ) and RHS(eₖ), formalises the corresponding
decision-tree lower bound, and identifies LR-read as the precise structural
assumption needed to lift the argument to Turing machines.

The decision-tree lower bound and its transfer to TMs are fully mechanised in
Isabelle/HOL; LR-read is the only external assumption.
›


section ‹7.  Perspective›

text ‹
This theory does not prove P ≠ NP.  Instead, it decomposes the argument into

  • a fully formalised lower-bound engine, and  
  • a single explicit modeling assumption (LR-read).

If LR-read were justified independently—by an argument that every solver must
process the encoding of (as, s) in a left–right sensitive way—then the
formalisation here would yield P ≠ NP automatically.

The contribution of this work is therefore twofold:
  (a) a verified lower-bound framework for SUBSET–SUM, and
  (b) a clear identification of the one hypothesis on which the conditional
      separation relies.
›


section ‹8.  SUBSET–SUM is in NP (formalised)›

text ‹
The Cook–Levin AFP library does not provide SUBSET–SUM ∈ NP by default.
Instead, we derive it via a general verifier packaged by SS_Verifier_NP.

A verifier gives:

  • explicit encodings of instances and certificates,
  • a polynomial-time Turing-machine verifier V,
  • soundness and completeness.

From such a verifier we prove:

      SUBSETSUM_lang enc0 ∈ 𝒩𝒫,

which is the standard NP characterisation.
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
If SUBSET–SUM ∈ P, then some Cook–Levin Turing machine solves it in polynomial
time.  This bridge moves from:

    language complexity  →  machine semantics.

The encoding used by the solver need not equal the verifier’s enc0.  Only the
underlying language matters.
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
This is the single modeling assumption.

For a fixed encoding enc0:

      LR_read_all_solvers_hypothesis enc0

means:

  (1) If SUBSET–SUM ∈ P, then a CL solver exists, and  
  (2) Every CL solver satisfies LR-read — i.e. belongs to ‹LR_Read_TM›.

NP-membership is *not* assumed here; it is proved separately via the verifier.
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
This theorem expresses the logical heart of the argument:

    LR assumptions  +  SUBSET–SUM ∈ NP   ⇒   P ≠ NP.

Proof sketch:

    Assume P = NP.
    Then SUBSET–SUM ∈ P.
    So a polynomial-time CL solver M exists.
    LR-read applies to M, giving a √(2^n) lower bound.
    Contradicting the assumed polynomial-time upper bound.
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
This theorem provides the one-line final result:

      LR hypothesis + SUBSET–SUM verifier  ⇒  P ≠ NP.

It simply wraps the earlier lemma together with SUBSETSUM_in_NP_global.
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
