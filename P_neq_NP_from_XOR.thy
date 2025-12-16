theory SubsetSum_PneqNP
  imports SubsetSum_CookLevin
begin

text \<open>
\paragraph{Where the idea comes from.}

This development is inspired by the informal lower-bound discussion in

\begin{quote}
C.\ A.\ Feinstein, \emph{``Dialogue Concerning the Two Chief World Views,''}
arXiv:1605.08639.
\end{quote}

The paper is used purely as motivation: no statement from it is imported as a
formal fact.  Instead, we extract a single modelling principle suggested by the
informal reasoning and formalise it in Isabelle/HOL: an information-flow
requirement governing how a solver must obtain and use information in order to
decide whether an equality \verb|L = R| can hold.

Everything required from the standard Cook--Levin Turing-machine semantics is
proved explicitly.  The remaining ingredient --- an additional interface
property exposing the left/right candidate structure needed to transfer the
abstract decision-tree bound --- is stated openly as a modelling hypothesis
(\emph{LR-read}).
\<close>

text \<open>
\bigskip
\begin{center}
\textbf{A conditional proof that $\mathcal{P} \neq \mathcal{NP}$ from an information-flow principle}
\end{center}
\bigskip

\paragraph{A reader-friendly summary of the logical structure.}

\begin{enumerate}
\item \textbf{An abstract lower bound.}
  In \verb|SubsetSum_DecisionTree| we prove that any solver satisfying a simple
  information-flow condition (formalised there as a candidate-distinguishing
  assumption) must take $\Omega(\sqrt{2^n})$ steps on instances with
  \verb|distinct_subset_sums as|.

\item \textbf{Transfer to Cook--Levin machines.}
  In \verb|SubsetSum_CookLevin| we show that any Cook--Levin machine that
  decides SUBSET--SUM and satisfies \emph{LR-read} inherits this lower bound.

\item \textbf{A single modelling bridge.}
  Because Cook--Levin machines may preprocess and reorganise the encoding
  arbitrarily, \emph{LR-read} is not a semantic consequence of the model and
  must be assumed explicitly.  We therefore state one global hypothesis:

  \begin{quote}
  Every polynomial-time SUBSET--SUM solver admits an LR-read presentation.
  \end{quote}

  Formally, this assumption is packaged below as
  \verb|LR_read_all_poly_solvers_hypothesis enc0|.

\item \textbf{Final implication.}
  Under this hypothesis, combining SUBSET--SUM $\in \mathcal{NP}$ with the
  consequence of $\mathcal{P} = \mathcal{NP}$ (namely SUBSET--SUM $\in \mathcal{P}$)
  yields $\neg(\mathcal{P} = \mathcal{NP})$.
\end{enumerate}

\paragraph{Acknowledgement.}
The author received assistance from AI systems (ChatGPT by OpenAI and Claude by
Anthropic) in drafting explanatory text and in iteratively refining Isabelle/HOL
proof scripts.  All formal results and final proofs are the responsibility of
the author.
\<close>

section \<open>Roadmap\<close>

text \<open>
This file has three conceptual stages.

\begin{itemize}
\item We state the bridge assumption \emph{LR-read} cleanly.
      This is the only non-derived hypothesis used in the final theorem.

\item We use this assumption to rule out polynomial-time Cook--Levin solvers
      for SUBSET--SUM, by transferring an
      \(\Omega(\sqrt{2^n})\) lower bound to the machine level on a canonical
      family of instances.

\item We combine this with the facts that SUBSET--SUM lies in
      \(\mathcal{NP}\) and that \(\mathcal{P} = \mathcal{NP}\) implies
      SUBSET--SUM \(\in \mathcal{P}\), yielding the conclusion
      \(\neg(\mathcal{P} = \mathcal{NP})\).
\end{itemize}
\<close>

section \<open>The LR-read assumption\<close>

text \<open>
We begin with the elementary task of deciding whether two integers
\verb|L| and \verb|R| are equal.

When \verb|L| and \verb|R| are accessible only through queries, correctness
requires that a solver obtain information from \emph{both} sides.  If one
side were never distinguished in the solver's observable behaviour, an
adversary could vary that unseen value while keeping all observed
information fixed, causing the solver to behave identically even though
the truth of \verb|L = R| changes.

By itself, this observation concerns only a single pair of integers.
Its relevance to SUBSET--SUM arises from the canonical split of the
verification equation.

For any split position \verb|k|, the decomposition \verb|e_k (as, s)|
gives rise to two families of possible integer values:

\begin{itemize}
\item \verb|LHS (e_k as s k)|, containing up to \verb|2^k| left-hand values;
\item \verb|RHS (e_k as s k)|, containing up to \verb|2^(n - k)| right-hand values.
\end{itemize}

Each element of these sets is a concrete integer that the left-hand or
right-hand side of the equation could take under some hidden choice of
the Boolean vector \verb|xs| consistent with the same instance
\verb|(as, s)|.

In an information-flow (reader-style) model, correctness is expressed by
requiring that, for some split position \verb|k|, the solver's observable
behaviour distinguish all canonical candidates on both sides.  If some
candidate value were never distinguished, the solver could not reliably
tell the difference between instances with and without a valid equality.

Viewed through this basic equality principle, we obtain a per-candidate
requirement: for some split position \verb|k|, a correct solver must
effectively distinguish every possible numerical value in both
\verb|LHS (e_k as s k)| and \verb|RHS (e_k as s k)|.  Otherwise, an
adversary could keep the solver's observations fixed while choosing hidden
subsets that differ in whether an equality \verb|L = R| exists.

This per-candidate requirement is exactly what drives the abstract reader
lower bound proved earlier.
\<close>

section \<open>Why LR-read is assumed rather than proved\<close>

text \<open>
A natural question is why the predicate \verb|LR_read| is not proved
directly from the Cook--Levin Turing-machine semantics.

The reason is conceptual rather than technical.

The Cook--Levin model permits a machine to preprocess, compress, and
reorganise its input arbitrarily before performing any semantic
distinctions.  Nothing in the execution semantics alone enforces a
correspondence between a machine's observable behaviour and the canonical
left/right candidate values induced by the subset-sum decomposition
\verb|e_k (as, s)|.

As a result, the abstract information-flow principle used in
\verb|SubsetSum_DecisionTree|, which reasons in terms of distinguishing
individual candidate values, does not directly transfer to the
Cook--Levin model.  The semantics do not require a machine's observable
behaviour to expose these distinctions at the level needed for a
per-candidate adversary argument.

Establishing \verb|LR_read| from first principles would therefore require
an additional structural theorem about polynomial-time Turing machines,
namely that any such machine deciding equality-type problems admits a
presentation in which canonical left-hand and right-hand candidate values
are separately observable.  This does not follow from the Cook--Levin
execution semantics developed here and is therefore stated explicitly as a
modelling hypothesis.

The contribution of the present formalisation is to show that:

\begin{itemize}
\item once \verb|LR_read| is assumed, the exponential lower bound follows
      formally; and
\item \verb|LR_read| is the only non-derived assumption used in the final
      conditional implication \verb|¬ P_eq_NP|.
\end{itemize}

In this sense, the theory isolates a single, sharply defined
information-flow predicate as the exact point on which the present
conditional implication hinges.

From a methodological perspective, the role played by \verb|LR_read| is
not unusual in complexity-theoretic lower-bound arguments.  Most known
unconditional lower bounds are proved relative to models that impose
explicit or implicit structural restrictions on how information may be
accessed or combined, such as monotonicity, bounded fan-in, fixed
communication partitions, read-once conditions, or explicit query
interfaces.

The present formalisation differs only in that this restriction is made
explicit as a separate predicate rather than being built silently into
the computational model.  Once stated, the resulting lower bound follows
formally.
\<close>

section \<open>A global LR-read axiom for Cook--Levin solvers\<close>

text \<open>
We now state the key bridge axiom in a direct form.

If a Cook--Levin machine \verb|M| correctly decides SUBSET--SUM and runs in
polynomial time, then it satisfies the locale \verb|LR_Read_TM| for some
choice of observable ``seen'' sets and a step counter.

Intuitively, \verb|seenL_TM| and \verb|seenR_TM| record which canonical
left-hand and right-hand candidates are distinguished by the machine's
observable behaviour.  The locale \verb|LR_Read_TM| is the concrete
machine-level formalisation of the informal LR-read principle described
above.

Once \verb|LR_Read_TM| holds, the contradiction with polynomial time is
already established in \verb|SubsetSum_CookLevin| (as
\verb|no_polytime_CL_on_distinct_family|).  We therefore first present the
implication ``polynomial-time solver implies LR-read'' as a locale-local
axiom for a fixed machine, and later package it as a global hypothesis
quantified over all machines.
\<close>

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

text \<open>
Main consequence inside this locale.

Under the assumption \emph{LR\_Read\_Axiom}, there exists no polynomial-time
Cook--Levin solver for SUBSET--SUM.

The reason is as follows.  If a Cook--Levin machine \verb|M| were to decide
SUBSET--SUM in polynomial time, the axiom would yield an instance of
\verb|LR_Read_TM| for \verb|M|.  However, the Cook--Levin development already
establishes that \verb|LR_Read_TM| implies an exponential lower bound on the
machine's running time on the family of instances with
\verb|distinct_subset_sums as|.

Thus the LR-read assumption, when combined with polynomial-time solvability,
leads to a contradiction inside this locale.
\<close>

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

text \<open>
A convenient corollary is that, assuming \verb|LR_Read_Axiom|, there exists
no polynomial-time Cook--Levin machine that solves SUBSET--SUM.
\<close>

corollary no_polytime_SubsetSum:
  assumes solver: "CL_SubsetSum_Solver M q0 enc"
  shows "¬ polytime_CL_machine M enc"
proof
  assume poly: "polytime_CL_machine M enc"
  from no_polytime_CL_SubsetSum_solver[OF solver poly]
  show False .
qed

end  (* locale LR_Read_Axiom *)

section \<open>SUBSET--SUM is in NP (formalised)\<close>

text \<open>
We reuse the verifier-based NP result established in
\verb|SubsetSum_CookLevin|.

In particular, if a standard NP verifier package
\verb|SS_Verifier_NP| is provided, then the language
\verb|SUBSETSUM_lang enc0| belongs to the class
\(\mathcal{NP}\).
\<close>

lemma SUBSETSUM_in_NP_global:
  assumes "SS_Verifier_NP k G V p T fverify enc0 enc_cert"
  shows "SUBSETSUM_lang enc0 ∈ 𝒩𝒫"
  using SUBSETSUM_in_NP_from_verifier[OF assms] .

section \<open>Definition of \(\mathcal{P} = \mathcal{NP}\)\<close>

text \<open>
We use the standard language-theoretic definition.

The equality \(\mathcal{P} = \mathcal{NP}\) means that a language belongs to
\(\mathcal{P}\) if and only if it belongs to \(\mathcal{NP}\).
\<close>

definition P_eq_NP :: bool where
  "P_eq_NP ⟷ (∀L::language. (L ∈ 𝒫) = (L ∈ 𝒩𝒫))"

section \<open>From \(\mathcal{P}\)-membership to a Cook--Levin solver\<close>

text \<open>
This section provides a bridge from \emph{language complexity} to
\emph{machine existence}.

If SUBSET--SUM (with instance encoding \verb|enc0|) belongs to
\(\mathcal{P}\), then there exists a Cook--Levin Turing machine \verb|M|,
together with some Boolean encoding \verb|enc|, such that \verb|M| decides
SUBSET--SUM correctly and runs in polynomial time.

We keep this bridge explicit because the solver's encoding \verb|enc| need
not coincide with the language-level encoding \verb|enc0|.  Only the
language \verb|SUBSETSUM_lang enc0| is relevant to the complexity-theoretic
statement.

Here \verb|enc0| is the string encoding used to define the language
\verb|SUBSETSUM_lang enc0|, while the Cook--Levin solver may operate on its
own Boolean encoding \verb|enc|.  The bridge axiom therefore relates only
the language, not the concrete encodings.
\<close>

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


section \<open>Global LR\_read hypothesis\<close>

text \<open>
This section states the single modelling assumption used in the final
conditional implication.

The predicate \verb|LR_read_all_poly_solvers_hypothesis enc0| consists of
two logically distinct components.

\begin{itemize}
\item \emph{Realisability bridge (complexity to machines).}
      If SUBSET--SUM (with instance encoding \verb|enc0|) belongs to
      \(\mathcal{P}\), then there exists a Cook--Levin Turing machine that
      decides SUBSET--SUM and runs in polynomial time.

\item \emph{Information-flow bridge (the LR-read content).}
      Every such polynomial-time Cook--Levin solver admits an LR-read
      presentation, that is, it satisfies
      \verb|admits_LR_read_TM| and therefore exposes the canonical
      left/right per-candidate structure required to transfer the
      abstract decision-tree lower bound.
\end{itemize}

No NP-membership assumption is included in this hypothesis.
Membership of SUBSET--SUM in \(\mathcal{NP}\) is established independently,
via the verifier construction formalised earlier.
\<close>

definition LR_read_all_poly_solvers_hypothesis ::
  "(int list ⇒ int ⇒ string) ⇒ bool" where
  "LR_read_all_poly_solvers_hypothesis enc0 ⟷
     P_impl_CL_SubsetSum_Solver enc0 ∧
     (∀M q0 enc.
        CL_SubsetSum_Solver M q0 enc ⟶ polytime_CL_machine M enc ⟶ 
        admits_LR_read_TM M q0 enc)"

section \<open>Core conditional theorem\<close>

text \<open>
The core argument can be summarised in a single paragraph.

Assume \(\mathcal{P} = \mathcal{NP}\).
Since SUBSET--SUM belongs to \(\mathcal{NP}\), it would then also belong to
\(\mathcal{P}\).
By the realisability component of
\verb|LR_read_all_poly_solvers_hypothesis enc0|,
there would therefore exist a polynomial-time Cook--Levin Turing machine
\verb|M| that decides SUBSET--SUM.

By the information-flow component of the same hypothesis, the machine
\verb|M| admits an LR-read presentation.
However, the development in \verb|SubsetSum_CookLevin| already establishes
that any LR-read Cook--Levin solver for SUBSET--SUM incurs an
\(\Omega(\sqrt{2^n})\) lower bound on a family of instances with
\verb|distinct_subset_sums|, and hence cannot run in polynomial time.

This contradiction shows that the assumptions cannot all hold simultaneously.
Formally, the theory proves the implication
\[
  \verb|LR_read_all_poly_solvers_hypothesis enc0| \;\Longrightarrow\;
  \neg (\mathcal{P} = \mathcal{NP}).
\]
\<close>

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

section \<open>Final packaged theorem\<close>

text \<open>
The final result can now be stated in a single packaged form.

If the LR-read hypothesis holds for the instance encoding \verb|enc0|, and
if SUBSET--SUM admits an NP verifier with respect to \verb|enc0|, then
\[
  \neg (\mathcal{P} = \mathcal{NP}).
\]

Equivalently, the development shows that the following assumptions are
jointly inconsistent:

\begin{itemize}
\item SUBSET--SUM lies in \(\mathcal{NP}\) (witnessed by a verifier);
\item every polynomial-time Cook--Levin solver for SUBSET--SUM admits an
      LR-read presentation; and
\item \(\mathcal{P} = \mathcal{NP}\).
\end{itemize}

Thus the entire argument isolates a single remaining informational question:
whether polynomial-time SUBSET--SUM solvers must satisfy the LR-read
information-flow condition.  All other components of the argument are
fully formalised within Isabelle/HOL.
\<close>

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
