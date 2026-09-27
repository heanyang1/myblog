---
layout: post
title:  "Understanding Type Systems with Category Theory"
---

In the beginning of [the assignments 6 of Stanford CS242](https://stanford-cs242.github.io/f19/assignments/assign6/), there is a quote from [linear logic's Wikipedia page](https://en.wikipedia.org/wiki/Linear_logic):
> "In terms of simple denotational models, linear logic may be seen as refining the interpretation of intuitionistic logic by replacing cartesian (closed) categories by symmetric monoidal (closed) categories ..."

This feels like an abstract nonsense to me when learning CS242, but after learning some basics of category theory, I realized that this does capture the essence of linear logic and linear types. In fact, I think symmetric monoidal closed categories is *the only correct way* to understand linear type systems like the one in Rust [^lambda].

[^lambda]: There is [a similar claim](https://math.ucr.edu/home/baez/act_course/lecture_2.html) by John Baez that he can only understand lambda calculus via (probably cartesian closed) categories.

In the next several posts, I'll try to decipher the sentence so it can be digested by us mortals. I'll assume that you are familiar with the concepts in [my previous post about category theory](/myblog/2026/08/09/dfa-with-category-theory.html).

## Cartesian Closed Category

We should first know what cartesian closed category is and why it's related to type systems.

**Definition.**\label{def:ccc} A *cartesian closed category* (CCC) is a category \(\mathcal{C}\) that:
1. has a terminal object,
2. is closed under product, i.e.
   1. for every objects \(X,Y\) in \(\mathcal{C}\), \(X\times Y\) exists and is an object of \(\mathcal{C}\),
   2. for every morphisms \(f:X\to Y,g:Z\to W\) in \(\mathcal{C}\), \(f\times g:X\times Y\to Z\times W\) is a morphism in \(\mathcal{C}\), and
3. for every object \(Y\) in \(\mathcal{C}\), the functor \(-\times Y:\mathcal{C}\to\mathcal{C}\) (that maps object \(X\) to \(X\times Y\) and morphism \(f\) to \(f\times\mathrm{id}_Y\)) has a right adjoint.

Here's an example of CCC:

**Proposition.**\label{prop:set-ccc} \(\mathsf{Set}\) is cartesian closed.

*proof.* In \(\mathsf{Set}\), any singleton set (the set with one element) can be its terminal object. Let \(S=\{s\}\) be the singleton set we have chosen, then
1. for every set \(X\), there is a function \(X\to S\) that maps everything in \(X\) to \(s\).
2. Suppose (on the contrary) that there are two functions \(f,g:X\to S\) and \(f\neq g\), then there exists \(x\in S\) such that \(f(x)\neq g(x)\), which means \(S\) has at least two different elements (contradiction).

In \(\mathsf{Set}\), the product is cartesian product. It's trivial that \(\mathsf{Set}\) is closed under product.

The right adjoint of \(-\times Y\) can be defined by the *exponential functor* \(-^Y\) that maps \(X\) to \(X^Y=\{f|f:Y\to X\}\) and \(f:X\to Z\) to a function \(f^Y:X^Y\to Z^Y\) such that
\[f^Y(g)=f\circ g\in Z^Y,\quad\forall g\in X^Y.\]

For simplicity, we use \(L\) and \(R\) to denote \(-\times Y\) and \(-^Y\) respectively.

We'll use \ref{lem:adjunction-unit-counit} in previous post to prove that \(L\dashv R\), which means we need to provide two natural transformation \(\varepsilon,\eta\) whose components
\[\varepsilon_X:X^Y\times Y\to X,\quad\eta_Z:Z\to(Z\times Y)^Y\]
have the following properties:
1. For every set \(Z\), if there is a function \(f:Z\times Y\to X\), then there is a unique function \(g:Z\to X^Y\) such that \(f=\varepsilon_X\circ Lg=\varepsilon_X\circ(g\times\mathrm{id}_Y)\).
2. For every set \(X\), if there is a function \(g:Z\to X^Y\), then there is a unique function \(f:Z\times Y\to X\) such that \(g=Rf\circ\eta_Z=f^Y\circ\eta_Z\).

We claim that these two functions are what we want:
1. \(\varepsilon_X\) takes in a function \(h:Y\to X\in X^Y\) and an element \(y\in Y\), and apply \(h\) to \(y\) to get a element in \(X\).
2. \(\eta_Z\) takes in an element \(z\in Z\) and create a function that inputs \(y\in Y\) and outputs \((z,y)\).

We only prove \(\varepsilon\) here, and \(\eta\) is similar.

(Existence) The curried version of \(f\) has the signature \(Z\to X^Y\) and \(f=\varepsilon_X\circ(g\times\mathrm{id}_Y)\).

(Uniqueness) Assume (on the countrary) that there are more than two functions \(g_1,g_2:Z\to X^Y\) such that \(g_1\neq g_2\) and \(f=\varepsilon_X\circ(g_1\times\mathrm{id}_Y)=\varepsilon_X\circ(g_2\times\mathrm{id}_Y)\). Because \(g_1\neq g_2\), therefore there exists \(z\in Z\) such that \(g_1(z)\neq g_2(z)\), therefore there exists \(y\in Y\) such that
\[(g_1(z))(y)\neq(g_2(z))(y)\Rightarrow (\varepsilon_X\circ(g_1\times\mathrm{id}_Y))(z,y)\neq(\varepsilon_X\circ(g_2\times\mathrm{id}_Y))(z,y),\]

Which contradicts \(\varepsilon_X\circ(g_1\times\mathrm{id}_Y)=\varepsilon_X\circ(g_2\times\mathrm{id}_Y)\).

(Naturality) For every function \(f:X_1\to X_2\), consider a pair \((g,y)\in X_1^Y\times Y\). Because
\[f\circ\varepsilon_{X_1}((g,y))=f(\varepsilon_{X_1}((g,y)))=f(g(y)),\]
\[\varepsilon_{X_2}\circ(f^Y\times\mathrm{id}_Y)((g,y))=\varepsilon_{X_2}((f\circ g,y))=f(g(y)),\]
therefore the naturality square for \(\varepsilon\)
\[
\begin{CD}
X_1^Y\times Y @>(f^Y\times\mathrm{id}_Y)>> X_2^Y\times Y \\
@V\varepsilon_{X_1}VV @VV{\varepsilon_{X_2}}V \\
X_1 @>>f> X_2
\end{CD}
\]
commutes. \(\Box\)

## Curry-Howard Correspondence

Here are some more examples of CCC. The first one is about logic.

**Example.**\label{ex:logic-ccc} A simplified [intuitionistic logic](https://en.wikipedia.org/wiki/Intuitionistic_logic) can be defined as CCC:
1. The objects are propositions.
2. A morphism between two objects \(P_1,P_2\) is a proof "If \(P_1\), then \(P_2\)".
3. There is a \(\top\) proposition that for every proposition \(P\), there is exactly one morphism \(P\to\top\).
4. The product is given by conjunction \(\land\) and propositions are \(\land\)-closed. For morphisms \(f:P_1\to P_2,g:Q_1\to Q_2\), the proof \(f\times g:(P_1\land Q_1)\to(P_2\land Q_2)\) can be constructed easily.
5. For every proposition \(P\), the functor \(-\land P\) has right adjoint, denoted as \(P\Rightarrow -\).

The counit of the adjunction \(\varepsilon_Q:(P\Rightarrow Q)\land P\to Q\) is called *modus ponens*.

The axiom schemas inside intuitionistic logic can be transformed into restrictions when constructing rules. For example, the rule
\[\frac{P\land Q}{P}\tag{eq:conjunction-elimination}\]
becomes the restrictions that for every proposition \(P,Q\), there is a morphism \(P\land Q\to P\). \(\Box\)

Perhaps the most useful example (for programmers) is that type systems can be modeled as CCC.

**Example.**\label{ex:type-ccc} A simplified type system for lambda calculus is a CCC:
1. The objects are types.
2. A morphism between two objects \(\tau_1,\tau_2\) is a function with type \(\tau_1\to\tau_2\).
3. There is a `unit` type that for every type \(\tau\), there is exactly one morphism from \(\tau\) to `unit`.
4. The product is given by the product type \(\times\) and types are \(\times\)-closed. For morphisms \(f:\tau_1\to \tau_2,g:\omega_1\to \omega_2\), the proof \(f\times g:(\tau_1\times\omega_1)\to(\tau_2\times\omega_2)\) can be constructed easily.
5. For every type \(\tau\), the right adjoint to \(-\times\tau\) is \(-^\tau\), where \(\tau_1^{\tau_2}\) is the type of function \(\tau_2\to\tau_1\).

The proof of \(-\times\tau\dashv-^\tau\) is similar to \ref{prop:set-ccc}. As we have seen in \ref{prop:set-ccc}, the counit of the adjunction is related to evaluating functions.

The restriction given by the equation \eqref{eq:conjunction-elimination} in logic also exists here, by translating the typing rule
\[\frac{e:\tau_L\times\tau_R}{e.L:\tau_L}.\Box\]

We can go further and claim that: as categories, these two systems can be isomorphic.

**Definition.**\label{def:category-isomorphism} Let \(\mathcal{C}_1,\mathcal{C_2}\) be categories. \(\mathcal{C}_1\) is *isomorphic* to \(\mathcal{C_2}\) iff there are two functors \(F:\mathcal{C}_1\to\mathcal{C}_2,G:\mathcal{C}_2\to\mathcal{C}_1\) such that \(G\circ F=\mathrm{id}_{\mathcal{C}_1},F\circ G=\mathrm{id}_{\mathcal{C}_2}\).

**Theorem.**\label{thm:ccc-isomorphism} The CCC of intuitionistic logic in \ref{ex:logic-ccc} (denoted as \(\mathcal{C}_1\)) is isomorphic to the CCC of the \ref{ex:type-ccc} (denoted as \(\mathcal{C}_2\)).

I can only provide a proof sketch here because the proof requires a long list of all axiom schemas and type checking rules and requires tools like F-algebra, which needs another post to explain.

*proof sketch.* We can choose a set of axiom schemas and type checking rules so that they "looks similar". Then there is a functor \(F:\mathcal{C}_1\to\mathcal{C}_2\) that
1. Maps \(\top\) to `unit`.
2. For every proposition \(P,Q\), \(F(P\land Q)=FP\times FQ\) and \(F(P\Rightarrow Q)=(FQ)^{FP}\).
3. If there is a morphism \(P\to Q\) in \(\mathcal{C}_1\), we can write down its proof tree and directly translated it into a type checking tree, and use it as \(FP\to FQ\) in \(\mathcal{C}_2\).

Similarly, we can define another functor \(G:\mathcal{C}_2\to\mathcal{C}_1\). Proving \(G\circ F=\mathrm{id}_{\mathcal{C}_1},F\circ G=\mathrm{id}_{\mathcal{C}_2}\) will just be trivial.

\ref{thm:ccc-isomorphism} can be generalized to the [Curry-Howard correspondence](https://en.wikipedia.org/wiki/Curry%E2%80%93Howard_correspondence), which says that the intuitionistic logic systems and type systems in the real world are also isomorphic, and serves as the fundation of [Rocq](https://rocq-prover.org/) and [Lean](https://lean-lang.org). Unfortunately these systems can't be simply modeled as CCC because they have more structures like variables and context.

## Outro

We have studied the CCC and its relation to intuistic logic and simply typed lambda calculus. Next time we will continue with monoidal category, linear logic and linear type system.

Curry-Howard correspondence is much deeper than what we have discussed today. There's a [brief introduction to the entire thing](https://cs3110.github.io/textbook/chapters/adv/curry-howard.html) in Cornell CS3110 if you are interested.

I'm stopping here because I'm running out of time this weekend after fixing problems in adjunction definition, and I will be on the vacation next week without my laptop. You may also need to re-read the previous post to learn the correct definition of adjunction.
