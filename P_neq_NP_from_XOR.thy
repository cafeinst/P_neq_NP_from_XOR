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
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
■  The Problem
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

The SUBSET–SUM problem asks: given a list of integers

    as = [a₀, …, aₙ₋₁]   and   target s,

does there exist a 0/1-vector xs such that

      ∑ᵢ as!i * xs!i = s ?

In other words, can we select a subset of the weights that sums to exactly s?

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
■  Why This Problem Is Interesting for Lower Bounds
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

SUBSET–SUM has a crucial structural property: for certain carefully chosen
weight lists, every different choice of subset produces a *different* sum.

**Definition:** A weight list as has *distinct subset sums* if no two different
0/1-vectors produce the same sum:

    xs ≠ ys  ⟹  ∑ᵢ as!i * xs!i  ≠  ∑ᵢ as!i * ys!i

When this property holds, the mapping from choice-vectors to sums is injective,
so there are exactly 2ⁿ distinct possible sums (one for each of the 2ⁿ subsets).

**Example:** The list as = [1, 2, 4, 8, …, 2ⁿ⁻¹] has distinct subset sums
because each choice-vector corresponds to a unique binary number.  More
generally, any "superincreasing" sequence (where each weight exceeds the sum of
all previous weights) has this property.

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
■  The Adversarial Family
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

The lower-bound argument focuses on the *class* of instances with distinct
subset sums.  These instances realize the maximal combinatorial complexity:
2ⁿ different outcomes that must somehow be distinguished.

**Key point:** We do NOT claim that specific instances like [1,2,4,…,2ⁿ⁻¹] are
algorithmically hard in the usual sense.  In fact, these power-of-two instances
are *easy*—a solver can simply read the binary representation of s to determine
which subset was chosen.

Rather, we use the distinct-subset-sums property as a *combinatorial witness*:
it guarantees that n weights can encode 2ⁿ distinct possibilities, providing
the raw material for an information-theoretic lower bound.  The argument will
show that *under certain assumptions about how algorithms work* (the LR-read
assumptions), distinguishing among these 2ⁿ possibilities requires √(2ⁿ) steps.

Whether real algorithms must follow those assumptions is the open question.

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
■  Why Not a Harder NP-Complete Problem?
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

SUBSET–SUM is chosen for its mathematical simplicity and clean structure.  The
verification equation

      ∑ᵢ as!i * xs!i = s

naturally splits into "left" and "right" parts at any position k:

      ∑ᵢ₍ᵢ<ₖ₎ as!i * xs!i  +  ∑ᵢ₍ᵢ≥ₖ₎ as!i * xs!i  =  s

            ↑ L side ↑              ↑ R side ↑

This canonical splitting is the foundation of the adversarial argument.  More
complex NP-complete problems lack such a clean bipartite structure, making them
harder to formalize while providing no additional insight.

The goal is not to prove SUBSET–SUM specifically is hard, but to use it as a
*test case* for whether information-theoretic arguments can yield unconditional
complexity lower bounds.
›


section ‹2.  The Decision-Tree Lower Bound›

text ‹
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
■  The Abstract Reader Model
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

The theory SubsetSum_DecisionTree defines an abstract "reader" model and proves:

      steps(as, s)  ≥  2 * sqrt(2^n)

for all lists as of length n having distinct subset sums.

**The computational model:**

The solver is a decision tree that interacts with the true instance (as, s) via
two oracles:

  • A "left oracle" that answers queries about values from the L side
  • A "right oracle" that answers queries about values from the R side

At each node, the tree chooses to query one oracle at one index, receives a
Boolean answer, and branches accordingly.  At leaves, it outputs accept/reject.

**Crucial distinction:** The tree queries the *real instance* (as, s).  The
choice-vectors xs ∈ {0,1}ⁿ are NOT part of the input.  They are *virtual
completions* used by the adversary's analysis to track which hypothetical
answers remain consistent with what the tree has learned so far.

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
■  The Canonical Split and LHS/RHS Sets
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

For a split position k (where 0 ≤ k ≤ n), we define the canonical equation eₖ:

      eₖ(as, s, xs) = (L, R)

where
      L = ∑ᵢ₍ᵢ<ₖ₎ as!i * xs!i           (sum using first k weights)
      R = s - ∑ᵢ₍ᵢ≥ₖ₎ as!i * xs!i       (residual from last n-k weights)

The original equation holds (sum of all weights equals s) if and only if L = R
in this representation.

As xs ranges over all 2ⁿ possible 0/1-vectors:
  • L takes on |LHS(eₖ)| distinct values, determined by the first k bits
  • R takes on |RHS(eₖ)| distinct values, determined by the last n-k bits

**When as has distinct subset sums:**
  • |LHS(eₖ)| = 2^k      (each of the 2^k prefix choices gives a unique L)
  • |RHS(eₖ)| = 2^(n-k)  (each of the 2^(n-k) suffix choices gives a unique R)
  • |LHS(eₖ)| × |RHS(eₖ)| = 2^n

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
■  The Adversary Argument
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

The model is an adversary game between the solver (decision tree) and an
adversary who tracks "virtual completions":

**Setup:** At the start, all 2ⁿ choice-vectors xs ∈ {0,1}ⁿ are potentially
consistent with the (as, s) the adversary will reveal.

**Invariant:** After each oracle query, the adversary maintains the set of
xs-vectors still consistent with all answers given so far.  For a split k,
these consistent vectors induce:
  • A set of "possible L-values" still in play
  • A set of "possible R-values" still in play

**Coverage requirement:** For the decision tree to correctly decide whether
(as, s) is a yes-instance, it must eventually:
  • Rule out all but one possible L-value, AND
  • Rule out all but one possible R-value

at some split k.  Otherwise, multiple (L, R) pairs remain consistent, some
making L = R true and others making it false, so the tree cannot give the
right answer.

**Cost principle:** Each oracle query can eliminate at most some of the possible
L-values or R-values.  To go from 2^k possible L-values down to 1 requires
enough queries to distinguish among 2^k options.  The axioms of the model
require that this costs at least 2^k steps (not just log(2^k) = k steps).

This is the strong assumption of the decision-tree model: no compression, no
clever shortcuts—each distinguishable value costs one unit of work.

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
■  The Mathematical Result
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

The abstract framework (locale SubsetSum_Lemma1) assumes:

  (A1) **Coverage:** For some split k, the solver's information flow matches
       the canonical LHS/RHS sets at that split.

  (A2) **Cost:** steps ≥ |LHS(eₖ)| + |RHS(eₖ)| at that split.

From these axioms, the framework proves:

      steps  ≥  2^k + 2^(n-k)  ≥  2 * sqrt(2^n)

where the last inequality uses the arithmetic-geometric mean:

      (2^k + 2^(n-k))/2  ≥  sqrt(2^k × 2^(n-k))  =  sqrt(2^n)

**What this bound means:**

In the decision-tree model with the stated coverage and cost axioms, solving
distinct-subset-sums instances of length n requires exponentially many
(specifically, √(2ⁿ) ≈ 2^(n/2)) queries.  This is an information-theoretic
lower bound based on the combinatorial structure of the problem.

**What remains to show:**

Whether these axioms (especially coverage and linear cost) apply to *real*
computational models like Turing machines.  The decision tree is an abstract
model designed to make the information-flow argument clean; Turing machines
can do many things decision trees cannot (arithmetic, random access, state-based
compression).  Bridging this gap requires additional assumptions, formalized
in the LR_Read_TM locale.
›


section ‹3.  From Decision Trees to Cook–Levin Turing Machines›

text ‹
A Cook–Levin Turing machine is far more flexible than a decision tree: it may
reorder, compress, or duplicate parts of the input, and it can perform
arithmetic and state-based computation.  Decision-tree lower bounds therefore
do not automatically carry over to the Turing-machine model.

To bridge this gap, the theory ‹SubsetSum_CookLevin› introduces the locale
‹LR_Read_TM›.  Its purpose is to connect the abstract reader-style quantities
from ‹SubsetSum_Lemma1› to concrete objects living in the Cook–Levin
framework:

  • ‹steps_TM as s› is the running time of a fixed machine ‹M› on the encoding
    of the instance ‹(as, s)›,

  • ‹seenL_TM as s k› and ‹seenR_TM as s k› are sets of canonical L- and
    R-values associated with a split position ‹k›.

Informally, the guiding principle is:

      “To decide whether L = R, a solver must extract information
       from both the L-zone and the R-zone of the input encoding.”

For subset-sum, splitting at position ‹k› rewrites the verification equation as

      ∑ᵢ₍ᵢ<ₖ₎ as!i * xs!i  =  s - ∑ᵢ₍ᵢ≥ₖ₎ as!i * xs!i
              ↑ L side ↑              ↑      R side      ↑

If the weights ‹as› have distinct subset sums, then as the choice-vector
‹xs ∈ {0,1}ⁿ› ranges over all possibilities, the LHS and RHS each take on
a family of distinct values determined by disjoint blocks of bits in ‹xs›:

  • ‹LHS (eₖ as s)› is the set of all L-values induced by varying the prefix
    bits ‹xs[0..k−1]›,

  • ‹RHS (eₖ as s)› is the set of all R-values induced by varying the suffix
    bits ‹xs[k..n−1]›.

In the decision-tree model, the reader interacts explicitly with these families.
For a Turing machine, we instead look at what the machine’s behaviour can
distinguish.

  • ‹seenL_TM as s k› collects those canonical L-values at split ‹k› that lead
    to measurably different machine behaviour (different reads, states, or
    outputs) when the instance is varied accordingly;

  • ‹seenR_TM as s k› is defined symmetrically for R-values.

These sets therefore measure how many different L- and R-values the machine has
effectively “told apart” at position ‹k›.

The LR-read assumptions in ‹LR_Read_TM› impose two key requirements:

  (LR1)  **Canonical alignment.**  On every instance with distinct subset sums
        there exists some split ‹k ≤ length as› such that

          seenL_TM as s k = LHS (e_k as s k) (length as)
          seenR_TM as s k = RHS (e_k as s k) (length as).

        Thus, at a critical split, the machine’s distinguishable L-/R-values
        coincide exactly with the canonical families used by the abstract
        argument.  The machine neither ignores any canonical possibility nor
        distinguishes extra, non-canonical values: its information flow follows
        the same combinatorial pattern as the decision-tree reader.

  (LR2)  **Linear cost.**  For all ‹as, s, k› we have

          steps_TM as s ≥ |seenL_TM as s k| + |seenR_TM as s k|.

        Distinguishing many L-/R-values is assumed to cost at least one unit of
        work per distinguishable value.  This mirrors the abstract “each
        distinguishable value costs ≥ 1 step” axiom in ‹SubsetSum_Lemma1›.

Given (LR1) and (LR2), we can instantiate the abstract locale
‹SubsetSum_Lemma1› with

      steps  = steps_TM,
      seenL  = seenL_TM,
      seenR  = seenR_TM.

For lists ‹as› with distinct subset sums, the cardinalities of the canonical
families satisfy

      |LHS (e_k as s k)| = 2^k,      |RHS (e_k as s k)| = 2^(n−k),

and hence

      |LHS| + |RHS| ≥ 2 * sqrt (2^n)

by the arithmetic–geometric mean inequality.  Combining this with (LR2) yields

      steps_TM as s ≥ 2 * sqrt ((2::real) ^ n)

for all distinct-subset-sum ‹as› of length ‹n›.

Formally, the locale ‹LR_Read_TM› carries out this instantiation and imports
the lower bound as theorems

      ‹subset_sum_sqrt_lower_bound_TM›  and
      ‹no_polytime_CL_on_distinct_family›,

which are the TM-level versions of the decision-tree lower bound.  A more
global summary of what is and is not proved appears in Section ‹5›.
›


section ‹4.  Why LR-read is Assumed›

text ‹
The central modelling assumption of this development is:

      **Every Turing-machine solver for SUBSET–SUM satisfies LR-read.**

This claim is *not* proved in Isabelle/HOL; it is an external hypothesis about
the structure of all possible algorithms and encodings for SUBSET–SUM.

Recall from Section ‹3› that LR-read has two components:

  • **Exact canonical alignment**: for each distinct-subset-sum instance there
    exists a split ‹k› where the sets of L- and R-values that the machine
    effectively distinguishes coincide exactly with the canonical families

          seenL_TM as s k = LHS (e_k as s k) (length as)
          seenR_TM as s k = RHS (e_k as s k) (length as),

    so that the machine’s information flow aligns perfectly with the
    L/R-splitting used in the decision-tree argument.

  • **Linear distinguishability cost**:

          steps_TM as s ≥ |seenL_TM as s k| + |seenR_TM as s k|,

    asserting that distinguishing many canonical values costs at least one unit
    of work per value.

These conditions are plausible if one imagines a solver that explicitly
“recovers” the same LHS/RHS families that drive the abstract reader model:
to verify ‹L = R›, the solver must in some sense inspect information from both
sides, and each distinguishable possibility seems to require its own effort.
However, general Turing machines can in principle:

  • work in a different coordinate system where L and R information is
    intertwined or compressed,

  • use arithmetic on the target ‹s› and the weights ‹as› to extract bits in
    bulk or in indirect ways,

  • exploit encodings where the L- and R-zones are not cleanly separated on
    the tape.

In such situations, it is far from obvious that the machine’s distinguishable
values must line up with the canonical ‹LHS›/‹RHS› sets, or that the running
time must scale linearly in their cardinalities.

From a complexity-theoretic perspective, this is exactly the hard part: LR-read
is a *global* structural restriction on all algorithms for SUBSET–SUM.  The
present theory does not attempt to justify it; instead, it treats LR-read as
a clear, explicit hypothesis and explores its consequences.

Under this hypothesis, the formal development shows:

  • any single Cook–Levin Turing machine satisfying LR-read inherits the
    √(2ⁿ) lower bound on instances with distinct subset sums (via
    ‹LR_Read_TM›), and

  • if in addition every polynomial-time SUBSET–SUM solver were required to
    satisfy LR-read, then SUBSET–SUM could not lie in ‹𝒫›, and hence we would
    obtain a separation ‹P ≠ NP›.

The remaining sections make this dependency precise, and Section ‹5› summarises
the three-layer structure (abstract kernel, Cook–Levin bridge, and universal
LR-read hypothesis) on which the conditional result rests.
›


section ‹5.  Logical Structure›

text ‹
This section summarises the logical architecture of the development and makes
clear which parts are fully proved and which part remains an explicit
assumption.

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
■  Three-Layer Architecture
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

The overall structure can be viewed in three layers:

┌─────────────────────────────────────────────────────────────────────────┐
│  LAYER 1: Abstract Lower-Bound Kernel                    [PROVED]      │
│                                                                       │
│  Theory: ‹SubsetSum_DecisionTree›                                    │
│  Locale: ‹SubsetSum_Lemma1›                                          │
│                                                                       │
│  Assumes:                                                            │
│    • an abstract step function ‹steps›,                              │
│    • abstract “seen” families ‹seenL›, ‹seenR›,                      │
│    • axioms:                                                         │
│        coverage_ex:  ∃k. seenL = LHS(eₖ), seenR = RHS(eₖ)            │
│        steps_lb:     steps ≥ |seenL| + |seenR|                       │
│                                                                       │
│  Proves:                                                             │
│    steps(as, s) ≥ 2 * sqrt (2^n) for distinct-subset-sum inputs      │
│                                                                       │
│  Status:                                                             │
│    ✓ purely combinatorial                                            │
│    ✓ fully mechanised in Isabelle/HOL                                │
└─────────────────────────────────────────────────────────────────────────┘

The proof uses only the combinatorics of distinct subset sums and the
arithmetic–geometric mean inequality; it does not refer to any concrete
computational model.

┌─────────────────────────────────────────────────────────────────────────┐
│  LAYER 2: Cook–Levin Bridge                              [PROVED]      │
│                                                                       │
│  Theory: ‹SubsetSum_CookLevin›                                       │
│  Locale: ‹LR_Read_TM›                                               │
│                                                                       │
│  Defines:                                                            │
│    • ‹steps_TM›, ‹seenL_TM›, ‹seenR_TM› from a fixed machine ‹M›     │
│      and encoding ‹enc›,                                            │
│                                                                       │
│  Assumes (LR-read for this ‹M›):                                     │
│    • canonical alignment at some split ‹k›,                          │
│    • linear cost: steps_TM ≥ |seenL_TM| + |seenR_TM|.                │
│                                                                       │
│  Proves:                                                             │
│    • Layer 1 axioms hold with ‹steps = steps_TM›,                    │
│      ‹seenL = seenL_TM›, ‹seenR = seenR_TM›,                         │
│    • therefore ‹steps_TM as s ≥ 2 * sqrt (2^n)› on hard instances,   │
│      and no single polynomial can bound ‹steps_TM› on all            │
│      distinct-subset-sum inputs.                                     │
│                                                                       │
│  Status:                                                             │
│    ✓ fully mechanised implication “LR-read ⇒ inherits lower bound”   │
│    ✓ conditional on LR-read for this particular solver ‹M›           │
└─────────────────────────────────────────────────────────────────────────┘

Layer 2 shows that, for any fixed machine satisfying LR-read, the abstract
kernel from Layer 1 applies and yields a √(2ⁿ) lower bound.  This is still
a conditional statement: it does not assert that every solver satisfies LR-read,
only that LR-read suffices to trigger the bound.

┌─────────────────────────────────────────────────────────────────────────┐
│  LAYER 3: Universal LR-Read Hypothesis                  [ASSUMED]     │
│                                                                       │
│  Theory: ‹SubsetSum_PneqNP›                                          │
│                                                                       │
│  Hypothesis (‹LR_read_all_solvers_hypothesis enc0›):                 │
│    • If SUBSET–SUM ∈ ‹𝒫› (for some encoding ‹enc0›), then there      │
│      exists a Cook–Levin solver ‹M› with polynomial running time;    │
│    • Every such solver ‹M› satisfies LR-read, i.e. belongs to        │
│      ‹LR_Read_TM› for some ‹seenL›, ‹seenR›.                         │
│                                                                       │
│  Together with:                                                      │
│    • SUBSET–SUM ∈ ‹𝒩𝒫› (proved via ‹SS_Verifier_NP›),                │
│                                                                       │
│  this implies the core conditional theorem:                          │
│                                                                       │
│      LR_read_all_solvers_hypothesis enc0  ⟹  ¬ P_eq_NP.             │
│                                                                       │
│  Status:                                                             │
│    ✗ not proved in this development                                  │
│    ✗ a substantive modelling assumption about all solvers            │
└─────────────────────────────────────────────────────────────────────────┘

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
■  What Is and Is Not Established
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Summarising the status of the main statements:

  ✓ Fully proved in Isabelle/HOL:

    • The abstract √(2ⁿ) lower bound in ‹SubsetSum_Lemma1› under the
      coverage and cost axioms;

    • The Cook–Levin bridge: any machine satisfying LR-read (for given
      ‹as, s› and ‹enc›) satisfies these axioms, and therefore inherits
      the lower bound on distinct-subset-sum inputs;

    • SUBSET–SUM ∈ ‹𝒩𝒫› for suitable encodings ‹enc0› via the
      ‹SS_Verifier_NP› locale;

    • The conditional implication:

          LR_read_all_solvers_hypothesis enc0  ⟹  ¬ P_eq_NP.

  ✗ Not proved (and currently open):

    • That every Turing-machine solver for SUBSET–SUM satisfies LR-read
      for its chosen encoding;

    • That LR-read is an unavoidable or “natural” constraint on real
      algorithms or encodings;

    • P ≠ NP as an unconditional statement.

The value of the present formalisation is therefore not to claim a proof of
P ≠ NP, but to decompose one proposed strategy into:

  • a fully mechanised lower-bound engine, and

  • a single, sharply stated modelling hypothesis (LR-read) on which the
    conditional separation depends.

Any future progress on the LR-read hypothesis—whether in the direction of
justifying it, refuting it, or replacing it by a weaker but still sufficient
property—can be plugged directly into this framework, with the rest of the
argument already verified by Isabelle/HOL.
›


section ‹6.  Relation to Feinstein (2016)›

text ‹
Feinstein argued that checking equality of two subset-sum expressions requires
probing many configurations.  This formalisation isolates the combinatorial
core, constructs the decision-tree lower bound, and identifies LR-read as the
precise structural assumption required to transfer the argument to Turing
machines.
›


section ‹7.  Perspective›

text ‹
This is not a proof of P ≠ NP.  
It is a decomposition:

  • one fully formalised lower-bound engine, and  
  • one explicit, clearly stated modeling hypothesis (LR-read).

If LR-read is ever justified independently, the separation P ≠ NP would follow
mechanically.
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
