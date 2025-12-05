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
reorder, compress, or duplicate parts of the input.  Decision-tree lower bounds
do not automatically carry over.

To bridge the gap, SubsetSum_CookLevin defines the locale LR_Read_TM.

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
■  The Intuitive Principle
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

The key informal idea is:

      "To decide whether two quantities L and R are equal, the solver must 
       actually read information coming from the L-zone and from the R-zone 
       of the input encoding."

For subset-sum, when we split at position k, the verification equation becomes:

      ∑(first k weights × choices)  =  target - ∑(last n-k weights × choices)
              ↑ L side ↑                              ↑ R side ↑

If a solver never examines the L side, it cannot determine which of the 2^k 
possible L-values it is dealing with—and similarly for the R side.  A correct
solver must therefore extract enough information to pin down both sides.

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
■  Formalizing "Information Extraction" for Turing Machines
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

The challenge: A Turing machine does not directly compute L and R.  Instead, it
reads bits from an encoded input ‹enc as s› and makes state transitions.  How do
we formalize what the machine "knows" about L and R?

**Definition (distinguishability):**

We say the machine *distinguishes* two L-values v₁ and v₂ if changing the input
from an instance with L = v₁ to one with L = v₂ (while keeping everything else
fixed) causes different machine behavior—different bits read, different states
visited, or different final outputs.

The set ‹seenL_TM as s k› collects all L-values at split k that the machine's
behavior can distinguish when run on instance (as, s).  If the machine cannot
tell v₁ from v₂ apart, they are treated as equivalent and only one representative
enters the set.

Symmetrically, ‹seenR_TM as s k› tracks distinguishable R-values.

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
■  The LR-Read Assumption (Exact Alignment)
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Inside LR_Read_TM, the informal principle becomes an exact mathematical
requirement: for some split k, we require

      seenL_TM as s k  =  LHS(eₖ as s)   and
      seenR_TM as s k  =  RHS(eₖ as s).

Here LHS(eₖ as s) is the set of ALL possible L-values that can arise at split k
as the choice-vector xs ranges over {0,1}ⁿ, and similarly for RHS.

**Why equality, not just subset?**

- Superset (seenL_TM ⊇ LHS):  Every possible L-value is distinguishable to
  the machine.  This direction is *necessary*: if the machine cannot distinguish
  two different L-values that lead to different answers, it might err.

- Subset (seenL_TM ⊆ LHS):  The machine distinguishes nothing beyond the
  canonical L-values defined by the split.  This direction is the *strong
  modeling assumption*: it says the machine's internal view of the problem
  aligns exactly with the mathematical split into L and R.

**What this equality means:**

The machine's information extraction perfectly matches the canonical mathematical
split—no more, no less.  The machine does not, for instance, distinguish 2^n
arbitrary patterns in the encoding that have nothing to do with subset-sum
structure; instead, its distinguishing power is *precisely* the 2^k canonical
L-values and 2^(n-k) canonical R-values.

This is a strong constraint on *how* algorithms can work.  It rules out solvers
that:
  • compress or hash the L and R information together,
  • use arithmetic on the target s to bypass bit-by-bit inspection,
  • distinguish values in a non-canonical coordinate system.

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
■  The Cost Principle (Linear Distinguishability Cost)
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

A second axiom in LR_Read_TM states:

      steps_TM as s  ≥  |seenL_TM as s k| + |seenR_TM as s k|.

**Rationale:** Each distinguishable value requires reading *something* from the
input.  If the machine distinguishes 2^k different L-values, it must have
extracted enough information to tell them apart, which requires computational
work.

**The strong form:** The axiom claims that distinguishing N values costs at
least N *steps*, not just log(N) bits of information.  This would hold if:
  • each step reveals at most one bit of information, AND
  • the machine must explicitly "touch" each distinguishable value.

This is natural in the decision-tree model (where each query reveals one bit and
each value requires its own query), but it is a *modeling assumption* for Turing
machines.  Real machines might:
  • use arithmetic or hashing to process many values in one step,
  • compress information so that N values require only log(N) space/time,
  • exploit structure in the encoding to avoid exhaustive enumeration.

The axiom constrains the algorithm's strategy: it must pay linear cost in the
size of the seen-sets, ruling out clever shortcuts.

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
■  How These Assumptions Yield the Lower Bound
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Given the two LR-read axioms, we can instantiate the abstract locale
SubsetSum_Lemma1 from the decision-tree theory:

(1) From the equality assumption:
      |seenL_TM as s k| = |LHS(eₖ as s)| = 2^k,
      |seenR_TM as s k| = |RHS(eₖ as s)| = 2^(n-k).

(2) The product constraint:
      |seenL_TM| × |seenR_TM| = 2^k × 2^(n-k) = 2^n.

(3) By the arithmetic-geometric mean inequality:
      |seenL_TM| + |seenR_TM|  ≥  2 √(|seenL_TM| × |seenR_TM|)
                                =  2 √(2^n).

(4) By the cost axiom:
      steps_TM as s  ≥  |seenL_TM| + |seenR_TM|  ≥  2 √(2^n).

This is the same √(2^n) lower bound derived in the decision-tree model, now
applied to Cook–Levin machines—but only for those machines satisfying the
LR-read assumptions.

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
■  What Is and Isn't Proven
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

**Proven in Isabelle:**
  • The mathematical implication: IF a machine satisfies the LR-read axioms,
    THEN its step-count is at least 2√(2^n) on hard instances.
  • The instantiation: the LR-read axioms are sufficient to trigger the
    decision-tree lower-bound machinery.

**NOT proven:**
  • That any actual Turing-machine solver for subset-sum must satisfy LR-read.
  • That the LR-read assumptions are "natural" or "unavoidable" properties of
    computation.
  • That real algorithms cannot circumvent these assumptions via compression,
    arithmetic, or alternative representations.

The LR-read property is a *modeling hypothesis*.  It restricts the class of
algorithms under consideration to those whose information flow aligns with the
canonical L/R split and whose cost scales linearly with distinguishability.

If this hypothesis holds for all subset-sum solvers, the √(2^n) lower bound
proves that subset-sum ∉ P, and therefore P ≠ NP.  If any solver violates
LR-read (for example, by using arithmetic on s to extract bits without reading
them sequentially, or by processing L and R information in compressed or
interleaved form), then the lower bound does not apply to that solver.

The value of this formalization is not that it proves P ≠ NP unconditionally,
but that it isolates LR-read as the *precise* structural assumption required
to make the argument work.  Every other component is fully mechanized in
Isabelle; only the LR-read hypothesis remains as an external premise.
›

section ‹4.  Why LR-read is Assumed›

text ‹
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
■  The Central Question
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

The central assumption of this entire development is:

      **Every Turing-machine solver for SUBSET–SUM satisfies LR-read.**

This is *not* proven.  It is a modeling axiom about how computation works.

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
■  What LR-Read Means
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Recall from Section 3 that LR-read has two components:

**1. Exact canonical alignment:**

For some split k, the machine's behavior distinguishes exactly the canonical
LHS and RHS value sets:

      seenL_TM as s k  =  LHS(eₖ as s)    (all 2^k possible L-values)
      seenR_TM as s k  =  RHS(eₖ as s)    (all 2^(n-k) possible R-values)

This rules out machines whose internal representation doesn't align with the
canonical L/R split—for example, machines that work in a different coordinate
system, or that compress L and R information together.

**2. Linear distinguishability cost:**

      steps_TM as s  ≥  |seenL_TM as s k| + |seenR_TM as s k|

This rules out machines that can distinguish many values in sublinear time—
for example, via hashing, arithmetic shortcuts, or compressed representations.

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
■  Why This Is Plausible (Intuitive Argument)
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

The informal intuition is appealing:

    "To verify L = R, you must examine both L and R.  You can't tell whether
     two quantities are equal without looking at both of them."

For the canonical split at position k:
  • L depends only on the first k weights and choices
  • R depends only on the last n-k weights and choices
  • They are "informationally separated" in the input encoding

So examining L requires reading bits from one part of the encoding, and
examining R requires reading bits from another part.  If the encoding spatially
separates these regions, any algorithm must visit both regions.

Moreover, if there are 2^k possible L-values, you need enough "queries" or
"inspection steps" to distinguish among them—intuitively, at least 2^k bits of
information, which requires at least 2^k steps if each step yields one bit.

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
■  Why This Might Be False (Counterarguments)
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Despite its intuitive appeal, LR-read might not hold for all solvers:

**1. Alternative representations:**

A machine might use a coordinate system where L and R information is interleaved
or combined.  For example, it might compute hash values or checksums that depend
on both L and R simultaneously, rather than separating them.

The canonical split eₖ is mathematically natural but computationally arbitrary—
there's no law requiring machines to respect it.

**2. Arithmetic shortcuts:**

For instances like as = [1, 2, 4, …, 2ⁿ⁻¹], a machine can solve SUBSET–SUM by
treating s as a binary number and reading its bits directly (via division and
modulo operations), without ever separating L and R in the sense required by
LR-read.

More generally, a machine might perform arithmetic on s to extract information
in compressed form, rather than reading individual encoding bits.

**3. Sublinear information extraction:**

The linear-cost axiom (steps ≥ 2^k + 2^(n-k)) assumes that distinguishing N
values costs N steps.  But in many models:
  • Distinguishing N values requires only log(N) bits of information
  • A single arithmetic operation can extract log(N) bits
  • Hashing or indexing can access specific values in O(1) time

The decision-tree model, where each query reveals exactly one bit about one
value, is special.  Real computation is more flexible.

**4. Encoding dependence:**

LR-read is defined relative to a specific encoding enc.  Different encodings of
the same mathematical problem can have radically different properties.  An
adversarial encoding might spatially separate L and R, making LR-read necessary,
but a clever encoding might interleave or redundantly represent information,
allowing algorithms to bypass the L/R separation.

The assumption tacitly requires that *all* "reasonable" encodings force LR-read,
but this isn't proven.

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
■  The Circularity Issue
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

There is a deeper problem: LR-read is *at least as strong* as the conclusion
we want to prove.

The argument has the form:
  • Assume: all solvers satisfy LR-read
  • Conclude: SUBSET–SUM requires √(2ⁿ) time, so P ≠ NP

But we could equally well say:
  • Assume: SUBSET–SUM requires √(2ⁿ) time
  • Conclude: all solvers must satisfy something like LR-read

In other words, the "assumption" is really just another way of stating the
desired conclusion.  We haven't explained *why* computation must follow the
LR-read pattern; we've simply packaged that claim as a hypothesis.

This is similar to proving "if all sorting algorithms compare every pair of
elements, then sorting requires Ω(n²) comparisons."  True, but uninformative—
the premise is false (many algorithms use fewer comparisons), and proving the
implication doesn't advance our understanding.

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
■  What Would Justify LR-Read?
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

To make LR-read a useful assumption rather than a restatement of the conclusion,
we would need an *independent* argument that it must hold, such as:

**1. Encoding-based argument:**

Prove that for *any* encoding satisfying certain natural properties (polynomial
length, efficiently decodable, preserving problem structure), the L and R
information must be spatially separated in a way that forces LR-read behavior.

This would shift the question to: "what are reasonable encoding properties?"
but it would at least separate the encoding theory from the algorithm analysis.

**2. Information-theoretic argument:**

Prove that distinguishing 2ⁿ possibilities *fundamentally* requires extracting
n bits of information, and that Turing machines can extract at most O(1) bits
per step, making √(2ⁿ) steps necessary.

This faces obstacles from communication complexity and circuit lower bounds,
which show that such arguments are difficult and require strong assumptions
about the computational model.

**3. Restricted model:**

Prove LR-read for a restricted class of algorithms (e.g., "oblivious" algorithms
that always read input in the same pattern, or "comparison-based" algorithms
that only compare values).

This is more achievable but less interesting—it only gives conditional lower
bounds for the restricted class, not for all algorithms.

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
■  The Value of This Formalization Despite the Gap
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Even though LR-read is not proven, this formalization has value:

**Conceptual clarity:**

It isolates *exactly* what must be shown to make information-theoretic lower
bounds work.  Before this formalization, the gap between "intuitively, you must
read both sides" and "provably, all algorithms require exponential time" was
vague.  Now we have a precise statement: prove LR-read, and the rest follows
mechanically.

**Proof engineering:**

Everything except LR-read is fully verified in Isabelle.  If someone later finds
a way to prove LR-read (or a weakened version sufficient for a lower bound),
this machinery is ready to go.  The formalization serves as a "proof template"
awaiting its key missing lemma.

**Negative result:**

By making LR-read explicit, we can also see more clearly *why* it's hard to
prove.  It requires constraining the internal structure of all possible
algorithms, which is exactly what the natural proofs barrier and other
complexity-theoretic obstacles suggest is fundamentally difficult.

This helps explain why 50+ years of attempts to prove P ≠ NP have failed: the
missing ingredient is not a clever combinatorial argument but a deep theorem
about the nature of computation itself.

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
■  Summary
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

LR-read is assumed because:
  ✗ We cannot currently prove it from first principles
  ✗ It may not even be true for all algorithms/encodings
  ✓ It precisely captures the missing ingredient for the lower-bound argument
  ✓ Making it explicit clarifies what would be needed for a proof of P ≠ NP

The formalization's value is not in proving P ≠ NP unconditionally, but in
*isolating the bottleneck* and turning a vague intuition ("you must examine
both sides") into a precise mathematical statement that can be studied,
challenged, and potentially proven or refined in future work.
›


section ‹5.  Logical Structure›

text ‹
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
■  The Three-Layer Architecture
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

The development consists of three conceptual layers, with clear boundaries
between what is proven and what is assumed:


┌─────────────────────────────────────────────────────────────────────────┐
│  LAYER 1: Abstract Lower-Bound Kernel                    [FULLY PROVEN] │
│                                                                           │
│  Theory: SubsetSum_DecisionTree                                          │
│  Locale: SubsetSum_Lemma1                                                │
│                                                                           │
│  Proves: IF an algorithm satisfies two abstract axioms                   │
│             (coverage + cost)                                             │
│          THEN steps(as, s) ≥ 2√(2ⁿ) on hard instances                    │
│                                                                           │
│  Method: Combinatorial counting + AM-GM inequality                       │
│                                                                           │
│  Status: ✓ Fully verified in Isabelle/HOL                                │
│          ✓ Mathematically unconditional                                  │
│          ✓ Makes no claims about real computation                        │
└─────────────────────────────────────────────────────────────────────────┘
                                     ↓
                      (instantiate axioms with TM objects)
                                     ↓
┌─────────────────────────────────────────────────────────────────────────┐
│  LAYER 2: Cook–Levin Bridge                              [FULLY PROVEN] │
│                                                                           │
│  Theory: SubsetSum_CookLevin                                             │
│  Locale: LR_Read_TM                                                      │
│                                                                           │
│  Proves: IF a Turing machine satisfies LR-read                           │
│          THEN it satisfies the Layer 1 axioms                            │
│          THEREFORE it inherits the 2√(2ⁿ) lower bound                    │
│                                                                           │
│  Method: Show that LR-read implies coverage + cost                       │
│                                                                           │
│  Status: ✓ Fully verified in Isabelle/HOL                                │
│          ✓ Conditional on LR-read (explicitly parameterized)             │
│          ✓ Makes no claim that LR-read is necessary or natural           │
└─────────────────────────────────────────────────────────────────────────┘
                                     ↓
                  (apply to all possible TM solvers)
                                     ↓
┌─────────────────────────────────────────────────────────────────────────┐
│  LAYER 3: Universal Claim                                  [ASSUMED]    │
│                                                                           │
│  Theory: SubsetSum_PneqNP                                                │
│  Statement: Every TM solver for SUBSET–SUM satisfies LR-read            │
│                                                                           │
│  Implies: SUBSET–SUM ∉ P, therefore P ≠ NP                               │
│                                                                           │
│  Status: ✗ NOT proven                                                    │
│          ✗ NOT obviously true                                            │
│          ✗ May be false for clever algorithms/encodings                  │
│          ? Subject of ongoing investigation                              │
└─────────────────────────────────────────────────────────────────────────┘

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
■  What Each Layer Contributes
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

**Layer 1: Pure mathematics**

This layer is model-agnostic.  It defines abstract functions steps, seenL,
seenR and two axioms:

  coverage_ex: ∃k. seenL as s k = LHS(eₖ) ∧ seenR as s k = RHS(eₖ)
  steps_lb:    steps as s ≥ |seenL as s k| + |seenR as s k|

From these axioms alone, it derives steps ≥Continue2√(2ⁿ) using:
• Cardinality of LHS and RHS (depends on distinct subset sums)
• AM-GM inequality (2^k + 2^(n-k) ≥ 2√(2ⁿ))
This is a hypothetical-conditional proof: "in any world where these axioms
hold, this bound follows."  It makes no claim about whether such a world exists.
Layer 2: Computational interpretation
This layer interprets the abstract axioms in terms of Turing machine behavior:
steps_TM as s    := steps_CL M (enc as s)     [machine's runtime]
seenL_TM as s k  := [values M's behavior distinguishes on L side]
seenR_TM as s k  := [values M's behavior distinguishes on R side]
The locale LR_Read_TM assumes these concrete definitions satisfy the Layer 1
axioms.  It then invokes Layer 1's theorem to conclude:
"Any TM satisfying LR-read requires 2√(2ⁿ) steps on hard instances."
This is still conditional—it's an implication, not an existence claim.  We've
shown that if such a machine exists, then it must be slow.
Layer 3: Universal quantification
This layer makes the existential claim:
"All TM solvers for SUBSET–SUM satisfy LR-read."
Combined with Layer 2, this would prove:
• All TM solvers require 2√(2ⁿ) time on hard instances
• Therefore no polynomial-time solver exists
• Therefore SUBSET–SUM ∉ P
• Therefore P ≠ NP (since SUBSET–SUM ∈ NP)
But Layer 3's claim is not proven.  It's a hypothesis about the structure of
all possible algorithms.  The formalization makes this hypothesis explicit via
the definition LR_read_all_solvers_hypothesis.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
■  The Proof Obligations
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
To complete the argument for P ≠ NP, one would need to discharge the Layer 3
assumption.  This requires proving:
∀M, q₀, enc. CL_SubsetSum_Solver M q₀ enc
⟹  ∃seenL, seenR. LR_Read_TM M q₀ enc seenL seenR
In words: "for every correct Turing-machine solver, there exist concrete
definitions of seenL and seenR such that the LR-read axioms hold."
This is a universal claim over an infinite space of possible machines and
encodings.  Standard approaches to such claims include:
1. Direct construction:
Given an arbitrary machine M, explicitly construct seenL_TM and seenR_TM
from M's transition function and prove they satisfy LR-read.
Challenge: M might not cleanly separate L and R information—it might
compress, interleave, or transform the representation in arbitrary ways.
2. Indirect argument:
Prove that any machine violating LR-read must give wrong answers on some
instance.
Challenge: This requires showing that checking L = R fundamentally requires
the LR-read information flow, but clever encodings might allow shortcuts.
3. Model restriction:
Restrict to a subclass of machines (e.g., "oblivious" or "comparison-based")
where LR-read can be proven, then argue this restriction is without loss of
generality.
Challenge: Proving "WLOG" for algorithm classes is notoriously difficult—
any restriction might exclude the clever algorithm that solves the problem
efficiently.
None of these approaches has succeeded yet, which is why Layer 3 remains
an assumption.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
■  Comparison to Other Conditional Results
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Many important theorems in complexity theory are conditional:
• P ≠ NP ⟹ NP ≠ coNP
• Strong exponential time hypothesis ⟹ 3-SAT requires 2^(n-o(n)) time
• Hardness of factoring ⟹ RSA is secure
These are valuable because:
✓ The assumptions are well-studied conjectures, not ad-hoc conditions
✓ The implications connect different areas (giving a web of consequences)
✓ Disproving the assumption would itself be a major result
The present work is different:
LR-read ⟹ P ≠ NP
✗ LR-read is not a standard conjecture; it's introduced for this proof
✗ LR-read is at least as strong as P ≠ NP (arguably a restatement)
✗ Disproving LR-read would just mean "we found an algorithm violating it"
which is expected anyway
So this conditional result is less informative than standard complexity-theoretic
reductions.  Its value lies elsewhere: in clarifying what needs to be proven.
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
■  Practical Implications of the Layered Structure
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
For mechanized verification:
The layered design is excellent software engineering.  Each layer has a clean
interface (locale signature) and clear dependencies.  If Layer 3 were ever
proven, the mechanized Layers 1-2 would immediately produce a verified proof
of P ≠ NP with no additional verification burden.
For mathematical understanding:
The separation clarifies where the difficulty lies.  It's NOT in:
• The combinatorial counting (Layer 1)
• The decision-tree to Turing-machine translation (Layer 2)
The difficulty is entirely in Layer 3: proving that all algorithms must follow
a particular information-flow pattern.  This is a computational claim, not
a combinatorial claim, which explains why techniques from graph theory,
number theory, or discrete math have not sufficed.
For future work:
The structure suggests research directions:
• Can Layer 3 be proven for restricted algorithm classes?
• Can LR-read be weakened while preserving the lower bound?
• Are there alternative structural properties (not LR-read) that also imply
the Layer 1 axioms?
• Can we prove Layer 3 is unprovable via certain techniques (e.g., showing
it requires overcoming the natural proofs barrier)?
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
■  Summary: What Is and Isn't Established
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
✓  Proven: The mathematical implication chain (Layers 1-2)
✓  Proven: The formal machinery connecting decision trees to TMs
✓  Proven: The 2√(2ⁿ) bound under explicit axioms
✗  Not proven: That any real algorithm satisfies those axioms (Layer 3)
✗  Not proven: That LR-read is a reasonable or necessary constraint
✗  Not proven: P ≠ NP (unconditionally)
?  Open question: Can Layer 3 be proven, weakened, or circumvented?
?  Open question: Is this approach fundamentally limited by known barriers?
The formalization's contribution is making this structure explicit and precise,
turning a vague research program into a concrete proof obligation.
›

section ‹5.  Logical Structure›

text ‹
The development consists of three layers:

(1)  Lower-bound kernel — *proved*
        SubsetSum_DecisionTree and SubsetSum_Lemma1 give a √(2^n) bound
        from abstract axioms.

(2)  Cook–Levin bridge — *proved*
        LR_Read_TM shows how a solver’s information flow induces the
        seenL_TM / seenR_TM sets required by the abstract axioms.

(3)  Modeling assumption — *not proved*
        Every solver must satisfy LR-read.

Together:

      If SUBSET–SUM ∈ P and all solvers satisfy LR-read, then P ≠ NP.
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
