theory SubsetSum_PneqNP
  imports SubsetSum_CookLevin
begin

text ‹
Where the idea comes from.

This development is inspired by the informal lower-bound discussion in

  C. A. Feinstein, “Dialogue Concerning the Two Chief World Views,” arXiv:1605.08639.

The paper is used purely as motivation: no statement from it is imported as a
formal fact.  Instead, we extract a single modelling principle suggested by the
informal reasoning and formalise it in Isabelle/HOL—an information-flow
requirement governing how a solver must obtain and use information in order to
decide whether an equality ‹L = R› can hold.

Everything that is needed from the standard Cook–Levin Turing-machine semantics 
is proved explicitly. The remaining ingredient—an additional interface property 
exposing the left/right candidate structure required to transfer the abstract 
decision-tree bound—is stated openly as a modelling hypothesis (LR-read).
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
    information-flow condition (formalised there as a candidate-distinguishing 
    information-flow assumption) must take Ω(√(2^n)) steps on 
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
This file has three conceptual stages.

  A. State the bridge assumption (LR_read) cleanly.
     This is the only non-derived hypothesis used in the final theorem.

  B. Use it to rule out polynomial-time Cook–Levin solvers for SUBSET–SUM.
     (Because Cook–Levin + LR-read implies an Ω(√(2^n)) lower bound on a distinct family.)

  C. Combine that with “SUBSET–SUM ∈ NP” and “P = NP ⇒ SUBSET–SUM ∈ P”
     to conclude ¬(P = NP).
›

section ‹2. What exactly is the LR_read assumption?›

text ‹
Begin with the elementary task of deciding whether two integers ‹L› and ‹R›
are equal.

When ‹L› and ‹R› are accessible only through queries, correctness requires that
a solver obtain information from *both* sides.  If one side were never distinguished 
in the solver’s observable behaviour, an adversary could vary that unseen value while 
keeping all observed information fixed, causing the solver to behave identically even
though the truth of ‹L = R› changes.

By itself, this observation concerns only a *single pair* of integers.
Its relevance to SUBSET–SUM comes from the canonical split of the verification
equation.

For any split position ‹k›, the decomposition ‹eₖ(as,s)› gives rise to two
families of possible integer values:

  • ‹LHS(eₖ as s)› — up to ‹2^k› possible left-hand values,
  • ‹RHS(eₖ as s)› — up to ‹2^(n − k)› possible right-hand values.

Each element of these sets is a concrete integer that the left-hand or
right-hand side of the equation *could* take under some hidden choice of the
0/1 vector ‹xs› consistent with the same instance ‹(as,s)›.

In an information-flow (reader-style) model, correctness is expressed by
requiring that, for some split ‹k›, the solver’s *observable behaviour*
distinguish all canonical candidates on both sides.  If some candidate value
were never distinguished, the solver could not reliably tell the difference
between instances with and without a valid equality.

Viewed through the basic equality principle, this yields a per-candidate
requirement: for some split position ‹k›, a correct solver must effectively
distinguish *every* possible numerical value in both
‹LHS(eₖ as s)› and ‹RHS(eₖ as s)›.  Otherwise, an adversary could keep the
solver’s observations fixed while choosing hidden subsets that differ in
whether an equality ‹L = R› exists.

This per-candidate requirement is exactly what drives the abstract reader
lower bound proved earlier.

The difficulty arises when we move to the Cook–Levin Turing-machine model.
A machine may read its entire input and then preprocess it freely—reordering,
copying, or compressing information, or computing derived representations.
As a result, the canonical left/right structure exposed by the split
‹eₖ(as,s)› need not remain visible at the level of individual machine steps,
and the standard adversary argument no longer enforces per-candidate
distinction.

The predicate ‹LR_read› captures precisely this missing structure.
It asserts that, for some split position ‹k›, the machine’s observable
behaviour exposes exactly the canonical left-hand and right-hand candidate
values induced by ‹eₖ(as,s)›.

Under this assumption, the abstract decision-tree lower bound transfers to
Cook–Levin machines, yielding a lower bound of

    Ω(√(2^n))

steps on distinct-subset-sums instances of length ‹n›.
›

section ‹3. Why LR_read is assumed rather than proved›

text ‹
A natural question is why the LR_read predicate is not proved directly
from the Cook–Levin Turing-machine semantics.

The reason is conceptual rather than technical.

The Cook–Levin model allows a machine to preprocess, compress, and
reorganise its input arbitrarily before performing any semantic
distinctions.  Nothing in the bare execution semantics enforces a
one-to-one correspondence between observable behaviour and the
canonical left/right candidate values induced by the subset-sum
decomposition eₖ(as,s).

As a result, the abstract reader-style information principle used in
SubsetSum_DecisionTree — which reasons in terms of distinguishing
individual candidate values — does not automatically transfer to the
Cook–Levin model.  Nothing in the bare Cook–Levin execution semantics
forces a machine’s observable behaviour to expose these distinctions.

Establishing LR_read from first principles would require an additional 
structural theorem about how polynomial-time solvers must expose 
left/right information in their observable behaviour. This does not 
follow from the bare Cook–Levin execution semantics developed here, so 
we state LR_read explicitly as a modelling hypothesis.

The contribution of the formalisation is to show that:

  • once LR_read is assumed,
    the exponential lower bound follows *formally*; and

  • LR_read is the *only* non-derived assumption used in the final
    implication ¬(P = NP).

In this sense, the theory isolates a single, sharply-defined
information-flow principle as the exact point at which the P versus NP
question hinges.
›

section ‹4. A global LR-read axiom for Cook–Levin solvers›

text ‹
We now state the key bridge axiom in a very direct form:

  If a Cook–Levin machine M correctly decides SUBSET–SUM
  and runs in polynomial time, then it satisfies LR_Read_TM
  for some choice of observable “seen” sets and a step counter.

Intuitively, seenL_TM and seenR_TM record which canonical LHS/RHS candidates
are distinguished by the machine’s observable behaviour. Here LR_Read_TM is 
the concrete machine-level formalisation of the informal LR_read principle 
described above. 

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
  assumes poly_solver_admits_LR_Read:
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
  from poly_solver_admits_LR_Read[OF solver poly]
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


section ‹5. SUBSET–SUM is in NP (formalised)›

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

section ‹6. Definition of P = NP›

text ‹
We use the usual language-theoretic definition:
P = NP means every language is in P exactly when it is in NP.
›

definition P_eq_NP :: bool where
  "P_eq_NP ⟷ (∀L::language. (L ∈ 𝒫) = (L ∈ 𝒩𝒫))"

section ‹7. From “SUBSET–SUM ∈ P” to an actual Cook–Levin solver›

text ‹
This is just a bridge from *language complexity* to *machine existence*:

If SUBSET–SUM (with instance encoding enc0) is in P,
then there exists some Cook–Levin machine M with some Boolean encoding enc
that decides SUBSET–SUM and runs in polynomial time.

We keep this separate because the solver’s encoding enc need not equal the
verifier’s encoding enc0; only the *language* matters.

Here enc0 is the string encoding used to define the language SUBSETSUM_lang enc0, 
while the Cook–Levin solver may use its own Boolean encoding enc. The bridge 
axiom only relates the language, not the concrete encodings.
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


section ‹8. Global LR_read hypothesis›

text ‹
This is the one modelling assumption used in the final theorem.

LR_read_all_poly_solvers_hypothesis enc0 consists of two parts:

  (A) A realisability axiom linking the complexity class P to Cook–Levin machines:
      If SUBSET–SUM (with encoding enc0) is in P, then there exists a
      polynomial-time Cook–Levin solver for it.

  (B) Information-flow bridge (the real “LR_read” content):
      Every such polynomial-time Cook–Levin solver admits LR-read, i.e.
      satisfies admits_LR_read_TM, exposing the canonical left/right
      per-candidate structure required by the abstract lower bound.

NP membership is not part of LR_read; it is proved separately via the
verifier construction in Section 5.
›

definition LR_read_all_poly_solvers_hypothesis ::
  "(int list ⇒ int ⇒ string) ⇒ bool" where
  "LR_read_all_poly_solvers_hypothesis enc0 ⟷
     P_impl_CL_SubsetSum_Solver enc0 ∧
     (∀M q0 enc.
        CL_SubsetSum_Solver M q0 enc ⟶ polytime_CL_machine M enc ⟶ 
        admits_LR_read_TM M q0 enc)"

section ‹9. Core Conditional Theorem›

text ‹
Core idea in one paragraph:

Assume P = NP.  Since SUBSET–SUM is in NP, it would then be in P.
So there would exist a polynomial-time Cook–Levin solver M.
By LR_read, M admits LR-read.  But SubsetSum_CookLevin already proves that
LR-read Cook–Levin solvers incur the Ω(√(2^n)) lower bound on a distinct family, 
hence are not polynomial-time.  Contradiction.  Therefore ¬(P = NP). Equivalently: 
the development proves LR_read_all_poly_solvers_hypothesis enc0 ⟹ ¬ P_eq_NP.
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

section ‹10. Final Packaged Theorem›

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
