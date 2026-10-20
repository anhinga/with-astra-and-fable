 
## Question

Hi, I have a question. Is logic the same in topoi and quasi-topoi, or are there differences?

## Answer

I’ll check the categorical-logic references, especially how the internal language of a quasitopos differs from that of a topos.

Both support intuitionistic reasoning, but a quasitopos can lack “unique choice”: a relation assigning exactly one output to every input need not define a morphism. I’m checking a small example that makes this distinction concrete.

**They share an intuitionistic logical core, but their usual internal logics differ in an important way: in a quasitopos, a total, single-valued relation need not determine a morphism.** This is the possible failure of *unique choice*, also called *function comprehension*. [https://www.cambridge.org/core/journals/mathematical-structures-in-computer-science/article/effectiveness-and-continuity-in-intuitionistic-quasitoposes-of-assemblies/C8A43E59CD4FD8B4C51E3675E74BC44D](https://www.cambridge.org/core/journals/mathematical-structures-in-computer-science/article/effectiveness-and-continuity-in-intuitionistic-quasitoposes-of-assemblies/C8A43E59CD4FD8B4C51E3675E74BC44D)

The underlying distinction concerns which subobjects represent predicates:

| Feature | Topos | Quasitopos |
|---|---|---|
| Predicates on $A$ | All subobjects of $A$ | Strong subobjects of $A$ |
| Truth-value object $\Omega$ | Classifies all subobjects | Classifies strong subobjects |
| Logical operations | Intuitionistic connectives and quantifiers | Intuitionistic connectives and quantifiers |
| Total, single-valued relations | Always graphs of morphisms | Need not be graphs of morphisms |

In a quasitopos, strong subobjects coincide with regular subobjects—those representable as equalizers. They form Heyting algebras, and $\Omega^A$ provides a type of predicates on $A$, so higher-order quantification is still available. genui{"citation":{"refs":["turn3view2","turn2view1"]}}

To see the logical difference explicitly, consider

$$
\bigl(\forall x:A\;\exists!y:B\;R(x,y)\bigr)
\;\Longrightarrow\;
\exists f:B^A\;\forall x:A\;R(x,f(x)).
$$

This principle holds in every topos but can fail in a quasitopos. It is much weaker than the usual axiom of choice: the output is already uniquely specified, so there is no choice among competing witnesses. Nevertheless, turning that specification into a morphism is additional structure. genui{"citation":{"ref":"turn3view1"}}

**A concrete example makes this surprisingly tangible.** Consider the category of sets equipped with a reflexive binary relation, with relation-preserving functions as morphisms. This is a quasitopos. Its strong subobjects are subsets equipped with the induced relation. The category is discussed in Schröder’s paper, §1.3. genui{"citation":{"ref":"turn4view0"}}

Here is a two-element example within that category. Take
\[
A=(\{0,1\},\text{every pair is related}),\qquad
B=(\{0,1\},\text{only equal elements are related}).
\]
Define the predicate \(R\) on \(A\times B\) by the subset
\[
R=\{(0,0),(1,1)\},
\]
equipped with its induced relation.

Every element of \(A\) has exactly one corresponding element of \(B\), so internally
\[
\forall x:A\;\exists!y:B\;R(x,y)
\]
holds. But the required function would send \(0\mapsto0\) and \(1\mapsto1\), which **does not preserve the relations**: \(0\) and \(1\) are related in \(A\), while their images are unrelated in \(B\). Indeed, every morphism \(A\to B\) must be constant. Thus this functional relation has no corresponding morphism.

Categorically, the obstruction is easy to locate. For a total, single-valued relation \(R\hookrightarrow A\times B\), the projection \(R\to A\) is both epic and monic. In a topos, it is therefore invertible, giving the desired map
\[
A\xrightarrow{\;\pi_A^{-1}\;}R\xrightarrow{\;\pi_B\;}B.
\]
A quasitopos can have morphisms that are both epic and monic without being invertible; the projection in this example is one.

An additional observation from this example: its strong-subobject lattices are ordinary powersets, hence **Boolean**. So even classical predicate logic can coexist with this failure of unique choice.

There is also a terminology caveat: quasitopoi have a first-order internal logic using **all** subobjects. The comparison above uses their customary higher-order logic based on **strong** subobjects; specifying which interpretation is intended matters. Schröder explicitly distinguishes these in Remark 1.2. genui{"citation":{"ref":"turn3view0"}}
