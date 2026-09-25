### A refutation of the conjecture that all complete lattices can be represented as sets of fixed points of Scott continuous transformations of powersets

On Sunday, September 6, 2006, GPT-6-Astra has produced what seems to be a refutation of the conjecture that 
all complete lattices can be represented as sets of fixed points of Scott continuous transformations of powersets.
It's time to start documenting all these: the road to the solution, the upcoming checks and verifications that all details are correct, and so on.

I'd like to start with documenting the tentative counterexample itself.

***

**HEADLINE THEOREM** (due to GPT-6-Astra, with mild improvement from myself assisted by other AIs):

The lattice of open sets of $(\omega_1)^{\mathbb N}$ (that is, the Baire space of weight $\aleph_1$ equipped with product topology)
cannot be obtained as the set of fixed points of a Scott continuous transformation of a powerset.

***

[gpt-6-astra-solution.md](gpt-6-astra-solution.md) - the original solution by GPT-6 Astra (a bit less than 10 min of thinking, ChatGPT Plus web interface, Max thinking setting)

The essence of the solution is as follows. Recall relatively little known (new to me) definitions of a _countably directed set_ and an $\aleph_1$-_compact element_ 
(this is a variation of the standard notions of directed sets and compact elements, obtained when those notions are pushed towards higher cardinality).

Establish a **lemma** that all elements of ${Fix}(f),\quad f:\mathcal P(S)\to\mathcal P(S)\text{ Scott continuous}$ are the exact upper bounds
of sets of approximating them $\aleph_1$-compact elements (this is the a variation of the standard notion of algebraicity of a domain,
obtained when this notion is  pushed towards higher cardinality).

***

detailed proof of the Lemma (and also Lean 4 verification materials): [aleph-one-algebraicity-lemma](aleph-one-algebraicity-lemma)

Literature research on the origins of the notions of _countably directed set_, an $\aleph_1$-_compact element_, and $\aleph_1$-_algebraicity_:

https://chatgpt.com/share/6aa8e73b-5a3c-83ea-97c8-aca8df3e9888

Interestingly enough, the earliest published text might be the one by Bob Flagg: “$\kappa$-continuous lattices and comprehension principles for Frege structures,” _Annals of Pure and Applied Logic_ **36** (1987), 1–16. (new to me, although I am aware of many of his papers)

***

Then build an example of a complete lattice where this " $\aleph_1$-algebraicity" does not hold. This will be a counterexample (note that **the case of
complete lattices whose Scott topologies have countable bases remains open**, the example which is being build here is larger than that).

The counterexample itself is partially inspired by a recent paper _"The complete Boolean algebra of regular open sets in real line is not sober"_,
[https://arxiv.org/abs/2608.00408](https://arxiv.org/abs/2608.00408), and the Astra's interest in this paper comes from my earlier discussions with
other models.

Consider a construction from descriptive set theory, namely the Baire space of weight $\aleph_1$ (all that is new to me), $(\omega_1)^{\mathbb N}$:
[https://en.wikipedia.org/wiki/Baire_space_(set_theory)](https://en.wikipedia.org/wiki/Baire_space_(set_theory)) (section "Weight").

Consider the complete lattice (actually a complete Boolean algebra) of the regular open sets of $(\omega_1)^{\mathbb N}$.

Establish a **theorem** that this complete lattice is not " $\aleph_1$-algebraic". More strongly, _none of its elements_ except the bottom element (the empty set)
is $\aleph_1$-compact.

***

Thinking further and discussing with Claude Opus 5 convinced me that it's enough to consider the complete lattice of open sets of $(\omega_1)^{\mathbb N}$,
the complication of focusing specifically on regular open sets is unnecessary. For that complete lattice, it is also correct that none of its
elements except the empty set is $\aleph_1$-compact.

I have started to accumulate the relevant materials here: [non-aleph-one-algebraicity-example](non-aleph-one-algebraicity-example)

***

The combination of this theorem and the lemma above proves that the complete lattice of the regular open sets of $(\omega_1)^{\mathbb N}$
is a counterexample to the conjecture that every complete lattice is isomorphic to some $\mathrm{Fix}(f)$, where
$f:\mathcal P(S)\to\mathcal P(S)$ is Scott continuous and $\mathcal P(S)$ is the powerset of some set $S$.
