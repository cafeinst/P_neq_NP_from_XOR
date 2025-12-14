theory SubsetSum_PneqNP
  imports SubsetSum_CookLevin
begin

text ‹
Where the idea comes from.

This development is inspired by the informal lower-bound discussion in
C. A. Feinstein, “Dialogue Concerning the Two Chief World Views,” arXiv:1605.08639.
The paper is used as motivation only: no statement from it is imported as a formal fact.
Instead, we isolate one explicit modelling principle and formalise it in Isabelle/HOL—
an information-flow requirement that treats deciding whether an equality L=R can hold 
as a two-sided task. Everything derivable from the standard Cook–Levin Turing-machine 
semantics is proved. The remaining ingredient—capturing the “LR-read” structure needed 
to transfer the abstract decision-tree lower bound—is stated openly as a modelling 
hypothesis.
›

text ‹
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                                                             %
%      A CONDITIONAL PROOF THAT P ≠ NP FROM AN INFORMATION–FLOW PRINCIPLE     %
%                                                                             %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

A reader-friendly summary of the logical structure:

(1) An abstract lower bound.
    In SubsetSum_DecisionTree we prove that any solver satisfying a simple
    reader-style information condition must take Ω(√(2^n)) steps on
    distinct-subset-sums instances.

(2) Transfer to Cook–Levin machines.
    In SubsetSum_CookLevin we show that any Cook–Levin machine that both
    solves SUBSET–SUM and satisfies LR_read inherits this lower bound.

(3) A single modelling bridge.
    Because Cook–Levin machines may preprocess and reorganise the encoding 
    arbitrarily, LR_read is not a semantic consequence of the model and must be 
    assumed explicitly.  We therefore state one global hypothesis:

        Every polynomial-time SUBSET–SUM solver admits an LR-read presentation.

    Formally, this assumption is packaged below as
    ‹LR_read_all_poly_solvers_hypothesis enc0›.

(4) Final implication.
    Under this hypothesis, combining SUBSET–SUM ∈ NP with the consequence of 
    P = NP (namely SUBSET–SUM ∈ P) yields ¬(P = NP).

Acknowledgement:
The author received assistance from AI systems (ChatGPT by OpenAI and Claude by
Anthropic) in drafting explanatory text and in iteratively refining Isabelle/HOL
proof scripts. All formal results and final proofs are the responsibility of the
author.
›
section ‹1. Roadmap›

text ‹
This file has three conceptual moves.

  A. State the bridge assumption (LR_read) cleanly.
     This is the only non-derived hypothesis used in the final theorem.

  B. Use it to rule out polynomial-time Cook–Levin solvers for SUBSET–SUM.
     (Because Cook–Levin + LR-read already implies an exponential lower bound.)

  C. Combine that with “SUBSET–SUM ∈ NP” and “P = NP ⇒ SUBSET–SUM ∈ P”
     to conclude ¬(P = NP).
›

section ‹2. What exactly is the LR_read assumption?›

text ‹
Think first about the elementary task: deciding whether two integers L and R
are equal.

At the most basic level, correctness requires information from both sides.
If a solver never distinguishes one side, an adversary can vary that unseen
value while keeping all observed information fixed, causing the solver to
behave identically even though the truth of L=R changes.

By itself, this principle concerns only a single pair of integers.  Its force
in the SUBSET–SUM setting comes from the canonical split of the verification
equation.

For any split position k, the decomposition eₖ(as,s) yields two families of
possible integer values:

  • LHS(eₖ as s) — 2^k possible left-hand values,
  • RHS(eₖ as s) — 2^(n − k) possible right-hand values.

In a reader-style information-flow model (captured later by LR_read), 
correctness is represented as requiring that, for some split k, the solver’s 
observable behaviour distinguishes all canonical candidates on both sides.  
If some candidate were never distinguished, the solver could not reliably 
tell the difference between instances with and without a valid equality.

Viewed through the basic information principle, a reader-style model therefore 
imposes a per-candidate requirement: for some split position k, the solver’s 
observable behaviour must effectively distinguish every possible numerical 
value on both the left and right sides. If two canonical candidates were never 
distinguished, an adversary could keep the solver’s observations fixed while 
choosing hidden subsets that differ in whether an equality L=R exists. In this 
model, correctness is represented as forcing all canonical candidates to be 
separated.

This requirement is what drives the abstract reader lower bound developed
earlier.

In the Cook–Levin Turing-machine model, however, a machine may preprocess and
reorganise its input arbitrarily.  The per-candidate structure exposed by the
canonical split need not remain visible to a standard adversary argument.

The predicate LR_read captures exactly this missing structure.  It asserts
that, for some split k, the machine’s observable behaviour distinguishes
precisely the canonical LHS and RHS candidate values induced by eₖ(as,s).

Under LR_read, the abstract decision-tree lower bound transfers to
Cook–Levin machines, yielding a lower bound of

    Ω(√(2^n))

steps on distinct-subset-sums instances of length n.
›


section ‹3. A global LR-read axiom for Cook–Levin solvers›

text ‹
We now state the key bridge axiom in a very direct form:

  If a Cook–Levin machine M correctly decides SUBSET–SUM
  and runs in polynomial time, then it satisfies LR_Read_TM
  for some choice of observable “seen” sets and a step counter.

Once we have LR_Read_TM, the contradiction with polynomial time is already
proved in SubsetSum_CookLevin (as no_polytime_CL_on_distinct_family).
We present the implication ‘polytime solver ⇒ LR_Read_TM’ first as a 
locale-local axiom (for a fixed machine), and later package it as a global 
hypothesis quantified over all machines.
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
Main consequence inside this locale:

  Under LR_Read_Axiom, *no* polynomial-time Cook–Levin SUBSET–SUM solver exists.

Reason: if M were polynomial-time, the axiom gives LR_Read_TM for M, and the
Cook–Levin development already shows that LR_Read_TM implies an exponential
lower bound on distinct-subset-sums instances.
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


section ‹4. SUBSET–SUM is in NP (formalised)›

text ‹
We reuse the verifier-based NP result from SubsetSum_CookLevin.

Interpretation:
if you provide a standard NP verifier package (SS_Verifier_NP),
then the language SUBSETSUM_lang enc0 belongs to NP.
›

lemma SUBSETSUM_in_NP_global:
  assumes "SS_Verifier_NP k G V p T fverify enc0 enc_cert"
  shows "SUBSETSUM_lang enc0 ∈ 𝒩𝒫"
  using SUBSETSUM_in_NP_from_verifier[OF assms] .

section ‹5. Definition of P = NP›

text ‹
We use the usual language-theoretic definition:
P = NP means every language is in P exactly when it is in NP.
›

definition P_eq_NP :: bool where
  "P_eq_NP ⟷ (∀L::language. (L ∈ 𝒫) = (L ∈ 𝒩𝒫))"

section ‹6. From “SUBSET–SUM ∈ P” to an actual Cook–Levin solver›

text ‹
This is just a bridge from *language complexity* to *machine existence*:

If SUBSET–SUM (with instance encoding enc0) is in P,
then there exists some Cook–Levin machine M with some Boolean encoding enc
that decides SUBSET–SUM and runs in polynomial time.

We keep this separate because the solver’s encoding enc need not equal the
verifier’s encoding enc0; only the *language* matters.
›

definition P_impl_CL_SubsetSum_Solver ::
  "(int list ⇒ int ⇒ string) ⇒ bool" where
  "P_impl_CL_SubsetSum_Solver enc0 ⟷
     (SUBSETSUM_lang enc0 ∈ 𝒫 ⟶
        (∃M q0 enc.
           CL_SubsetSum_Solver M q0 enc ∧
           polytime_CL_machine M enc))"

definition admits_LR_read_TM :: 
  "machine ⇒ nat ⇒ (int list ⇒ int ⇒ bool list) ⇒ bool" where
  "admits_LR_read_TM M q0 enc ⟷
     (∃steps_TM seenL_TM seenR_TM.
        LR_Read_TM M q0 enc steps_TM seenL_TM seenR_TM)"


section ‹7. LR_read-read-all-solvers hypothesis›

text ‹
This is the one modelling assumption used in the final theorem.

LR_read_all_poly_solvers_hypothesis enc0 consists of two parts:

  (A) P-to-machine bridge:
      If SUBSET–SUM (with encoding enc0) is in P, then some polynomial-time
      Cook–Levin solver exists.

  (B) Information-flow bridge (the real “LR_read” content):
      Every such polynomial-time solver admits LR-read, i.e. satisfies 
      admits_LR_read_TM.

NP membership is *not* part of LR_read; NP membership is proved separately via the
verifier lemma in Section 4.
›

definition LR_read_all_poly_solvers_hypothesis ::
  "(int list ⇒ int ⇒ string) ⇒ bool" where
  "LR_read_all_poly_solvers_hypothesis enc0 ⟷
     P_impl_CL_SubsetSum_Solver enc0 ∧
     (∀M q0 enc.
        CL_SubsetSum_Solver M q0 enc ⟶ polytime_CL_machine M enc ⟶ 
        admits_LR_read_TM M q0 enc)"

section ‹8. Core Conditional Theorem›

text ‹
Core idea in one paragraph:

Assume P = NP.  Since SUBSET–SUM is in NP, it would then be in P.
So there would exist a polynomial-time Cook–Levin solver M.
By LR_read, M admits LR-read.  But SubsetSum_CookLevin already proves that
LR-read solvers cannot be polynomial time.  Contradiction.  Therefore ¬(P = NP).
›

lemma P_neq_NP_if_LR_read_all_poly_solvers_hypothesis:
  fixes enc0 :: "int list ⇒ int ⇒ string"
  assumes H:       "LR_read_all_poly_solvers_hypothesis enc0"
  assumes NP_enc0: "SUBSETSUM_lang enc0 ∈ 𝒩𝒫"
  shows "¬ P_eq_NP"
proof -
  from H have
    bridge_P: "P_impl_CL_SubsetSum_Solver enc0" and
    all_LR_read:   "∀M q0 enc.
      CL_SubsetSum_Solver M q0 enc ⟶ polytime_CL_machine M enc ⟶ 
      admits_LR_read_TM M q0 enc"
    unfolding LR_read_all_poly_solvers_hypothesis_def by blast+

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

    from all_LR_read solver poly have "admits_LR_read_TM M q0 enc" by blast
    then obtain steps_TM seenL_TM seenR_TM where lr:
      "LR_Read_TM M q0 enc steps_TM seenL_TM seenR_TM"
      unfolding admits_LR_read_TM_def by blast

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

section ‹9. Final Packaged Theorem›

text ‹
Final packaged statement:

  If LR_read holds (for enc0) and you have an NP verifier for SUBSET–SUM (for enc0),
  then ¬(P = NP).

So the development isolates exactly one remaining “informational” point:
whether polynomial-time SUBSET–SUM solvers must satisfy LR-read.
›

theorem P_neq_NP_under_LR_read:
  fixes enc0 :: "int list ⇒ int ⇒ string"
  assumes LR_read: "LR_read_all_poly_solvers_hypothesis enc0"
  assumes V:  "SS_Verifier_NP k G V p T fverify enc0 enc_cert"
  shows "¬ P_eq_NP"
proof -
  have NP_enc0: "SUBSETSUM_lang enc0 ∈ 𝒩𝒫"
    using SUBSETSUM_in_NP_global[OF V] .
  show "¬ P_eq_NP"
    using P_neq_NP_if_LR_read_all_poly_solvers_hypothesis[OF LR_read NP_enc0] .
qed

end
