theory SubsetSum_PneqNP
  imports SubsetSum_CookLevin
begin

text ‹
This theory completes the mechanised development of a *conditional* lower bound
for SUBSET–SUM originating in

    C. A. Feinstein,
    “Dialogue Concerning the Two Chief World Views,”
    arXiv:1605.08639.

The present file assembles the final logical implication from components
formalised in earlier theories.  The lower bound itself is derived under an
explicit information-flow assumption (LR-read); no unconditional separation
result is claimed.
›

text ‹
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                                                             %
%      A CONDITIONAL PROOF THAT P ≠ NP FROM AN INFORMATION–FLOW PRINCIPLE     %
%                                                                             %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

This theory packages the final logical implication of the development:

    (IP hypothesis)  +  (SUBSET–SUM ∈ 𝒩𝒫)   ⟹   P ≠ NP.

The mechanised lower bound itself is proved elsewhere:

  • ‹SubsetSum_DecisionTree› proves an abstract √(2^n) lower bound in a
    “reader” model, from two axioms:
      (coverage) at some split k the solver distinguishes the full canonical
                 LHS/RHS candidate families;
      (cost)     each distinguished candidate costs ≥ 1 unit of work.

  • ‹SubsetSum_CookLevin› instantiates that abstract model inside the
    Cook–Levin Turing-machine semantics via the locale ‹LR_Read_TM›.

What is *not* derived from Cook–Levin semantics is the bridge itself: a
polynomial-time solver might internally transform its input in ways that do not
expose the canonical left/right candidate structure.  Therefore this theory
isolates the bridge as a single modelling hypothesis (IP), stated below.

All remaining ingredients — the decision-tree bound, the Cook–Levin execution
semantics, and a verifier-based NP statement for SUBSET–SUM — are formalised in
Isabelle/HOL.  The only non-derived assumption in the final implication is the
IP hypothesis.

Acknowledgement:
The author received assistance from AI systems (ChatGPT by OpenAI and Claude by
Anthropic) in drafting explanatory text and in iteratively refining Isabelle/HOL
proof scripts.  All formal results and final proofs are the responsibility of
the author.
›
section ‹1. Overview›

text ‹
This file is structured as follows.

  • ‹Roadmap and the role of the IP assumption›
      States what is proved (a conditional implication) and what is assumed
      (the LR-read / IP bridge).

  • ‹A global LR-read axiom for SUBSET-SUM solvers›
      Introduces a locale packaging the information-flow axiom and derives the
      contradiction with the Cook–Levin lower bound for any purported
      polynomial-time solver.

  • ‹SUBSET–SUM is in NP (formalised)›
      Reuses the verifier-to-NP lemma from ‹SubsetSum_CookLevin›.

  • ‹Definition of P = NP›
      Fixes the Boolean abbreviation ‹P_eq_NP›.

  • ‹Bridging P to a concrete CL solver›
      Bridges “SUBSET–SUM ∈ 𝒫” to existence of a polynomial-time Cook–Levin
      solver, and defines ‹IP_TM› (“admits an LR-read presentation”).

  • ‹IP-read-all-solvers hypothesis›
      States the single global modelling assumption ‹IP_all_poly_solvers_hypothesis›.

  • ‹Core Conditional Theorem› and ‹Final Packaged Theorem›
      Derive ‹¬ P_eq_NP› from the IP hypothesis plus the NP statement for
      SUBSET–SUM.
›

section ‹2. Roadmap and the role of the IP assumption›

text ‹
Scope and limitations.

The result proved in this theory is a *conditional* implication.  It does not
assert that LR-read holds for all polynomial-time Turing machines, nor does it
claim that SUBSET–SUM is hard under arbitrary encodings or cost measures.

In particular:

  • The size parameter throughout is ‹length as›, not the bit-length of the
    integers in ‹as› or of their encoding.

  • The LR-read property is not derived from Cook–Levin semantics alone; it is
    postulated as an explicit information-flow condition.

  • The conclusion ‹¬ P_eq_NP› follows only under the hypothesis that *every*
    polynomial-time SUBSET–SUM solver satisfies LR-read (the IP hypothesis).

These restrictions are deliberate.  They isolate the informational content of
the lower bound from unrelated encoding or machine-model issues.
›

text ‹
The decision-tree argument works with a canonical split presentation eₖ(as,s),
whose left and right value ranges have sizes 2^k and 2^(n−k) on
distinct-subset-sum instances.  The abstract reader axioms capture the idea that
a solver must effectively distinguish these candidates, incurring ≥ 1 unit of
work per candidate, yielding the √(2^n) lower bound.

In the Cook–Levin model, a machine may preprocess its input freely, so the
canonical candidate structure is not automatically reflected in observable
behaviour.  The locale ‹LR_Read_TM› expresses the bridge as a hypothesis about
what the machine’s behaviour “covers”.  The IP hypothesis below asserts that
every polynomial-time solver admits such an LR-read presentation.
›

text ‹
Why canonical presentations suffice.

The lower bound argument does not depend on a solver literally using the
canonical split equation ‹eₖ(as,s)› or explicitly enumerating the corresponding
‹LHS› and ‹RHS› sets.  Rather, the canonical presentation serves as a *semantic
normal form*: on distinct-subset-sum instances, every correct solver must
distinguish exactly the same family of possible left- and right-hand values,
up to renaming or internal representation.

Thus restricting attention to canonical presentations does not lose generality.
Any solver that decides the equality problem must, in effect, acquire
information sufficient to separate all canonical candidates.  The LR-read / IP
hypothesis formalises the assumption that this unavoidable information flow is
reflected at the level of observable behaviour in the Cook–Levin model.
›

text ‹
Why IP is an information-flow assumption (the “L = R needs both sides” idea).

Fix any split position ‹k› and consider the canonical split equation ‹eₖ(as,s)›.
On a distinct-subset-sum instance, this equation induces two *families* of
possible values:

  • ‹LHS (eₖ as s k) (length as)›  has size ‹2^k›,
  • ‹RHS (eₖ as s k) (length as)›  has size ‹2^(n−k)›.

A solver does not see the hidden choice vector ‹xs›.  Therefore, from the
solver’s point of view, the left-hand quantity ‹L› could be *any* value in the
LHS family, and the right-hand quantity ‹R› could be *any* value in the RHS
family.

The basic informational principle is:

  To decide whether ‹L = R›, a solver must obtain some information about the
  actual value of ‹L› and some information about the actual value of ‹R›.

In the SUBSET–SUM setting, this means that a correct solver must extract
sufficient information from the instance to distinguish among the many
possible candidate values on both sides of some split presentation.

If, for example, the solver never distinguishes between two distinct LHS
candidates, then there exist hidden choice vectors that realise those two
candidates while inducing identical observable behaviour on the RHS side.
From the solver’s point of view, these cases are indistinguishable, even
though the existence of an equality ‹L = R› differs between them. Thus, 
without obtaining information about both sides, the solver cannot soundly 
decide the existence of an equality.

The locale ‹LR_Read_TM› is the formal Cook–Levin-level expression of this
two-sided information requirement: it postulates observable “coverage” of the
canonical LHS/RHS candidate families (for some split) and charges at least one
unit of work per distinguished candidate.  The IP hypothesis used later in this
file asserts that every polynomial-time Cook–Levin SUBSET–SUM solver admits such
an LR-read presentation.
›

section ‹3. A global LR-read axiom for SUBSET-SUM solvers›

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


section ‹4. SUBSET–SUM is in NP (formalised)›

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

section ‹5. Definition of P = NP›

definition P_eq_NP :: bool where
  "P_eq_NP ⟷ (∀L::language. (L ∈ 𝒫) = (L ∈ 𝒩𝒫))"

section ‹6. Bridging P to a concrete CL solver›

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

text ‹
  Terminology.

  In this theory we use “IP” purely as a *bridge hypothesis* about Cook–Levin
  machines: it says that polynomial-time SUBSET–SUM solvers admit an LR-read
  presentation (i.e. they instantiate ‹LR_Read_TM› for suitable observables).

  This “IP hypothesis” is not the decision-tree reader axiom itself, and it is
  not a statement about NP membership.  NP membership is handled independently
  via the verifier locale ‹SS_Verifier_NP›.
›

section ‹7. IP-read-all-solvers hypothesis›

text ‹
This is the single modelling assumption used in the final implication.

For a fixed instance encoding ‹enc0›, the predicate
‹IP_all_poly_solvers_hypothesis enc0› abbreviates two bridge statements:

  (1) (P-to-machine bridge)
      If the language ‹SUBSETSUM_lang enc0› lies in ‹𝒫›, then there exists a
      Cook–Levin machine ‹M› with some Boolean encoding ‹enc› that decides
      SUBSET–SUM correctly and runs in polynomial time (measured in ‹length as›).

  (2) (Information-flow bridge)
      Every such polynomial-time Cook–Levin solver admits an LR-read
      presentation, i.e. it satisfies ‹IP_TM› and hence instantiates the locale
      ‹LR_Read_TM› for some choices of ‹steps_TM›, ‹seenL_TM› and ‹seenR_TM›.

NP-membership is *not* assumed here; it is proved separately via a verifier.
›

definition IP_all_poly_solvers_hypothesis ::
  "(int list ⇒ int ⇒ string) ⇒ bool" where
  "IP_all_poly_solvers_hypothesis enc0 ⟷
     P_impl_CL_SubsetSum_Solver enc0 ∧
     (∀M q0 enc.
        CL_SubsetSum_Solver M q0 enc ⟶ polytime_CL_machine M enc ⟶ IP_TM M q0 enc)"

section ‹8. Core Conditional Theorem›

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

text ‹
Interpretation of the final theorem.

The theorem ‹P_neq_NP_under_IP› should be read as a *logical reduction*:
it shows that any proof of P = NP must violate at least one of the following:

  • the verifier-based NP characterization of SUBSET–SUM;
  • the Cook–Levin execution semantics;
  • the decision-tree lower bound proved in ‹SubsetSum_DecisionTree›;
  • or the LR-read information principle.

Thus the development does not claim to settle P versus NP outright.
Instead, it precisely identifies LR-read as the single remaining point
at which the intuitive information-flow argument must be justified or refuted.
›

section ‹9. Final Packaged Theorem›

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
