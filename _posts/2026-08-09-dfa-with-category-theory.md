---
layout: post
title:  "Data Flow Analysis with Category Theory"
series: static-analysis
---

> I won't write any updates to this post here because there are too many. See the git history if you are curious about what's happened.

When writing the previous post, I realized that lattices are just categories and I can avoid reinventing wheels by directly using some well-known theorems in category theory. So before proving the soundness of sign analysis, I'd like to take a little detour about category theory and how it can be used to understand the problem.

The goal of this post is to introduce adjunctions in category theory, which plays an important role in the soundness proof of DFA. If you know what adjunction is, feel free to skip this post. If not, you don't need to read any additional materials (this post should be self-contained), and there is a reading list at the end of this post to cover what's missing here.

This post is handwritten with some exceptions:
- Some of the diagrams are drawn by AI.
- I used AI to formalize this post in Lean4 and I'll mention some of its proofs. Here's [the entire proof](https://github.com/heanyang1/proofs/blob/main/Proofs/Adjunctions.lean)

## Basic Concepts

**Category.** A *category* \(\mathcal{C}\) contains the following things:
- A set [^set_theory] of *objects* \(\mathrm{Ob}(\mathcal{C})\),
- A set of *morphisms* (or *arrows*) \(\mathrm{Mor}(\mathcal{C})\). For every \(X,Y\in\mathrm{Ob}(\mathcal{C})\), there is a set of morphisms \(\mathcal{C}(X,Y)\) (or \(\mathrm{Hom}_{\mathcal{C}}(X,Y)\)) called *hom-set*,
- For every \(X\in\mathrm{Ob}(\mathcal{C})\), there is an *identity morphism* \(\mathrm{id}_X\in\mathcal{C}(X,X)\),
- For every \(X,Y,Z\in\mathrm{Ob}(\mathcal{C})\), and for every \(f\in\mathcal{C}(X,Y),g\in\mathcal{C}(Y,Z)\), there is a composition morphism \(g\circ f\in\mathcal{C}(X,Z)\), such that
  - for every morphism \(f,g,h\), \((f\circ g)\circ h=f\circ(g\circ h)\),
  - for every morphism \(f\in\mathcal{C}(X,Y)\), \(f\circ\mathrm{id}_X=f=\mathrm{id}_Y\circ f\).

[^set_theory]: The "set" here will cause some trouble when defining the category \(\mathsf{Set}\) and \( \mathsf{Cat}\), whose objects won't fit into a set. I'll assume that there is no such issue and (probably) resolve them in later posts by introducing universes.

Here are some examples of categories:
- We can define a category \(\mathsf{Set}\) where the object are sets and morphisms are functions.
- Given the set \(S\), the *discrete category* \( \mathsf{Disc}(S)\) is the category whose objects are \(S\) and morphisms are \(\{ \mathrm{id}_x|x\in S\}\).
- The *dual* of a category \(\mathcal{C}\) (denoted as \(\mathcal{C}^{\mathrm{op}}\)) contains every object of \(\mathcal{C}\), and there is a morphism \(X\to Y\) in \(\mathcal{C}^{\mathrm{op}}\) iff there is a morphism \(Y\to X\) in \(\mathcal{C}\).
- For lattice \(L\), we define objects as elements of \(L\) and morphism as the partial order: for \(x,y\in L\), if \(x\sqsubseteq y\), then there is a morphism \(x\to y\). The identity morphism and composition is given by the reflexivity and transitivity of the partial order. Note that the hom-set of lattices are either \(\varnothing\) or a set with one element (such category is called *thin category*).

**Isomorphism.** Let \( \mathcal{C}\) be a category and \(c,c'\) be its objects. There is an *isomorphism* between \(c\) and \(c'\) (denoted as \(c\cong c'\)) iff there are two morphisms \(f:c\to c',g:c'\to c\) such that \(f\circ g= \mathrm{id}_{c'},g\circ f= \mathrm{id}_c\).

In \(\mathsf{Set}\), every bijection is isomorphism.

In a lattice, by antisymmetry, if \(x\cong y\), then \(x=y\).

**Functors.** Let \(\mathcal{C},\mathcal{C}'\) be categories. A *functor* \(F:\mathcal{C}\to \mathcal{C}'\) has:
- A function \(F:\mathrm{Ob}(\mathcal{C})\to\mathrm{Ob}(\mathcal{C}')\),
- A function \(F:\mathrm{Mor}(\mathcal{C})\to\mathrm{Mor}(\mathcal{C}')\) that
  - preserves morphisms, i.e. for every \(X,Y\in\mathrm{Ob}(\mathcal{C})\), there is a function \(F|_{\mathcal{C}(X,Y)}:\mathcal{C}(X,Y)\to\mathcal{C}'(FX,FY)\),
  - preserves identity and composition, i.e. for morphisms \(f,g\), \(F(f\circ g)=Ff\circ Fg\), and for object \(X\), \(F\mathrm{id}_X=\mathrm{id}_{FX}\).

I'm using some conventions here when it doesn't introduce ambiguity:
1. The function \(F\) should actually be two functions, one applies to objects, the other applies to morphisms.
2. The braces in function applications are sometimes omitted.

Some examples of functors:
- The *identity functor* \( \mathrm{id}_{ \mathcal{C}}\) on category \( \mathcal{C}\) maps every object and morphism to itself.
- For every functor \(F: \mathcal{C}\to \mathcal{C}'\), there is a dual functor \(F^{\mathrm{op}}: \mathcal{C}^{\mathrm{op}}\to (\mathcal{C}')^{\mathrm{op}}\) such that \(F^{\mathrm{op}}f^{\mathrm{op}}=(Ff)^{\mathrm{op}}\) for every morphism \(f\in \mathcal{C}\).
- A function between lattices is a functor iff it preserves morphisms, which means it's a monotone function.

For functors \(F: \mathcal{C}_1\to \mathcal{C}_2,G: \mathcal{C}_2\to \mathcal{C}_3\), the *composition* of \(F\) and \(G\) is a functor \(G\circ F: \mathcal{C}_1\to \mathcal{C}_3\) whose functions are the composition of \(F\) and \(G\) (Verify that it's a functor if you are interested).

Using categories and functors, we can construct a category of categories \( \mathsf{Cat}\) where the objects are categories and morphisms are functors.

**Natural transformations.** The *natural transformation* \(\theta\) between two functors \(F,G:\mathcal{C}\to \mathcal{C}'\) is a set of morphisms \(\{\theta_X\in\mathcal{C}'(FX,GX)|X\in\mathrm{Ob}(\mathcal{C})\}\) such that for every morphism \(f:X\to Y\in\mathrm{Mor}(\mathcal{C})\), \(\theta_Y\circ Ff=Gf\circ\theta_X\).

We can draw the objects and morphisms as the following *diagram*, and \(\theta_Y\circ Ff=Gf\circ\theta_X\) is equivalent to the claim that the following diagram commutes:
\[
\begin{CD}
FX @>\theta_X>> GX \\
@VFfVV @VVGfV \\
FY @>>\theta_Y> GY
\end{CD}
\]

For functors \(F,G,H: \mathcal{C}_1\to \mathcal{C}_2\) and natural transformations \(\alpha:F\to G,\beta:G\to H\), the *(vertical) composition* [^composition] of \(\alpha\) and \(\beta\) is a natural transformation \(\beta\circ\alpha:F\to H\) where for every \(c\in \mathcal{C},(\beta\circ\alpha)_c=\beta_c\circ\alpha_c\) (Verify that it's a natural transformation if you are interested).

[^composition]: There is another kind of composition called *horizontal composition*. It's not used in this post, and every \(\circ\) means vertical composition.

The functors from \( \mathcal{C}_1\to \mathcal{C}_2\) forms a category \(\mathcal{C}_2^{\mathcal{C}_1}\). Its morphisms are natural transformations between functors. In lattice theory, it's the lattice of monotone map between two lattices.

In lattice theory, the map lattice \(S\to L\) contains any map from set \(S\) to lattice \(L\). Such map is a functor \(\mathsf{Disc}(S)\to L\), so we can construct the category of map lattices as \(L^{ \mathsf{Disc}(S)}\).

**Product Categories.** Let \(I\) be a set and \(\{ \mathcal{C}_i|i\in I\}\) be a set of categories. The *product category* \(\prod_{i\in I} \mathcal{C}_i\) is defined as:
- \( \mathrm{Ob}(\prod_{i\in I} \mathcal{C}_i)=\prod_{i\in I} \mathrm{Ob}(\mathcal{C}_i)\),
- \((\prod_{i\in I} \mathcal{C}_i)(\prod_{i\in I}X_i,\prod_{i\in I}Y_i)=\prod_{i\in I}\mathcal{C}_i(X_i,Y_i)\).

If \(I=\{1,2,\dots,n\}\), then \(\prod_{i\in I} \mathcal{C}_i\) can be written as \( \mathcal{C}_1\times\dots\times \mathcal{C}_n\) and its objects are tuples \((X_1,\dots,X_n)\).

## Universal Constructions

A category may contain some special objects whose definition involves every other objects in the category. Such definitions are called *universal constructions*.

**Initial and terminal objects.** The *initial object* in a category \( \mathcal{C}\) is an object \(c\) where for every \(c'\in \mathrm{Ob}( \mathcal{C})\), there is a unique morphism \(c\to c'\).

The *terminal object* in \( \mathcal{C}\) is the initial object in \( \mathcal{C}^{ \mathrm{op}}\), which essentially means for every \(c'\in \mathrm{Ob}( \mathcal{C})\), there is a unique morphism \(c'\to c\).

The initial and terminal of two objects are unique up to isomorphism, i.e. if both \(c\) and \(c'\) are initial/terminal object in \( \mathcal{C}\), then \(c\) and \(c'\) are isomorphic.

*proof.* By definition of initial object, there is a unique morphism \(f:c\to c'\), \(g:c'\to c\), \( \mathrm{id}_c:c\to c\), and \( \mathrm{id}_{c'}:c'\to c'\).

Since \(f\circ g:c'\to c'\) and the morphism from \(c'\) to \(c'\) is unique, therefore \(f\circ g= \mathrm{id}_{c'}\).

Similarly, \(g\circ f= \mathrm{id}_c\). Therefore \(c\cong c'\). \(\Box\)

Initial and terminal objects may not exist in general, but they always exist in a lattice, which is the \(\perp\) and \(\top\) of the lattice.

**Products and coproducts.** Let \( \mathcal{C}\) be a category and \(A\) be the set of its objects. The *product* over \(A\) is an object \(x\) such that
1. For every \(a\in A\), there is a morphism \(f_a:x\to a\),
2. For every \(b\in \mathrm{Ob}( \mathcal{C})\), if for every \(a\in A\), there is a morphism \(g_a:b\to a\), then there is a unique morphism \(f:b\to x\) such that for every \(a\in A\), \(g_a=f_a\circ f\).

The product is unique up to isomorphism, therefore we can use a symbol \(\prod A\) to define it.

\(x\) is the *coproduct* over a set \(A\) (denoted as \(\coprod A\)) iff \(x=\prod A\) in \( \mathcal{C}^{ \mathrm{op}}\).

In lattice, we can define the meets \(\sqcap A\) as the product \(\prod A\) and joins \(\sqcup A\) as the coproduct \(\coprod A\).

The objects constructed in this section are special cases of *limits and colimits*. The definition goes beyond the category \( \mathcal{C}\) and makes some proofs much harder, and is not necessary in lattices, so I'll not include it here.

## Bifunctors

**Bifunctors.** A *bifunctor* is a functor between the product category of two category and a category. Specifically, let \(\mathcal{C}_1,\mathcal{C}_2,\mathcal{D}\) be categories, then any functor \(F:\mathcal{C}_1\times\mathcal{C}_2\to\mathcal{D}\) is a bifunctor.

Bifunctors are usually represented by infix notations. For example, \(C_1FC_2\) means \(F(C_1,C_2)\) for bifunctors \(F:\mathcal{C}_1\times\mathcal{C}_2\to\mathcal{D}\). I'll only use infix notations when the symbol itself is infix notation (e.g. \(\times\)).

Given a bifunctor \(F:\mathcal{C}_1\times\mathcal{C}_2\to\mathcal{D}\), we can construct a functor \(F(*,Y):\mathcal{C_1}\to\mathcal{D}\) for every object \(Y\in\mathcal{C}_2\) by mapping an object \(X\) to \(F(X,Y)\) and a morphism \(f\) to \(F(f,\mathrm{id}_Y)\). The functorality can be reduced to the functorality of \(F\).

Similarly, we can define a functor \(F(X,*):\mathcal{C_2}\to\mathcal{D}\) for every object \(X\in\mathcal{C}_1\). \(F(*,Y)\) and \(F(X,*)\) are related:

**Proposition.**\label{prop:bifunctor-commute} For the bifunctor \(F:\mathcal{C}_1\times\mathcal{C}_2\to\mathcal{D}\) and \(f:X_1\to X_2\in\mathrm{Mor}(\mathcal{C}_1),g:Y_1\to Y_2\in\mathrm{Mor}(\mathcal{C}_2)\), the following diagram commutes:
\[
\begin{CD}
F(X_1,Y_1) @>F(f,\mathrm{id}_{Y_1})>> F(X_2,Y_1) \\
@VF(\mathrm{id}_{X_1},g)VV @VVF(\mathrm{id}_{X_2},g)V \\
F(X_1,Y_2) @>F(f,\mathrm{id}_{Y_2})>> F(X_2,Y_2)
\end{CD}
\]

*proof.* By functorality of \(F\),
\[F(f,\mathrm{id}_{Y_2})\circ F(\mathrm{id}_{X_1},g)=F(f\circ\mathrm{id}_{X_1},\mathrm{id}_{Y_2}\circ g)=F(f,g),\tag{eq:bifunctor-commute}\]
\[F(\mathrm{id}_{X_2},g)\circ F(f,\mathrm{id}_{Y_1})=F(\mathrm{id}_{X_2}\circ f,g\circ\mathrm{id}_{Y_1})=F(f,g),\]
hence the two paths are the same. \(\Box\)

The converse is true:

**Proposition.**\label{prop:bifunctor-construct} If we have a functor \(F_Y:\mathcal{C}_1\to \mathcal{D}\) for every \(Y\in\mathrm{Ob}(\mathcal{C}_2)\) and \(F_X:\mathcal{C}_2\to \mathcal{D}\) for every \(X\in\mathrm{Ob}(\mathcal{C}_1)\) such that
1. \(F_Y X=F_X Y\) for every \(X\in\mathrm{Ob}(\mathcal{C}_1)\), \(Y\in\mathrm{Ob}(\mathcal{C}_2)\),
2. for every \(f:X_1\to X_2\in\mathrm{Mor}(\mathcal{C}_1),g:Y_1\to Y_2\in\mathrm{Mor}(\mathcal{C}_2)\), \(F_{Y_2}f\circ F_{X_1}g=F_{X_2}g\circ F_{Y_1}f\),

then we can construct a bifunctor \(F:\mathcal{C}_1\times\mathcal{C}_2\to\mathcal{D}\) by mapping object \((X,Y)\) to \(F_XY\) and morphism \((f,g)\) to \(F_{Y_2}f\circ F_{X_1}g\).

*proof.* We need to prove the functorality of \(F\): for every morphism \(f_1:X_1\to X_2,f_2:X_2\to X_3\in\mathrm{Mor}(\mathcal{C}_1)\), \(g_1:Y_1\to Y_2,g_2:Y_2\to Y_3\in\mathrm{Mor}(\mathcal{C}_2)\),
\[F((f_2,g_2)\circ (f_1,g_1))=F(f_2,g_2)\circ F(f_1,g_1).\]

Here's the step by step derivation:
\[\begin{aligned}
F((f_2,g_2)\circ (f_1,g_1)) & =F(f_2\circ f_1,g_2\circ g_1) \\
& =F_{Y_3}(f_2\circ f_1)\circ F_{X_1}(g_2\circ g_1) & (\text{By definition of }F) \\
& =F_{Y_3}f_2\circ F_{Y_3}f_1\circ F_{X_1}g_2\circ F_{X_1}g_1 & (\text{By functorality of }F_{Y_3},F_{X_1}) \\
& =F_{Y_3}f_2\circ F_{X_2}g_2\circ F_{Y_3}f_1\circ F_{X_1}g_1 & (\text{Using the second requirement}) \\
& =F(f_2,g_2)\circ F(f_1,g_1)\ \Box & (\text{By definition of }F)
\end{aligned}\]

Bifunctors are functors by definition, so there can be natural transformations between two bifunctors. The naturality can be reduced to the naturality of their functors:

**Proposition.**\label{prop:bifunctor-natural} Let \(F,G:\mathcal{C}_1\times\mathcal{C}_2\to\mathcal{D}\) be bifunctors and \(\alpha\) be a set of morphisms \(\{\alpha_{X,Y}\in\mathcal{D}(F(X,Y),G(X,Y))|X\in\mathrm{Ob}(\mathcal{C}_1),Y\in\mathrm{Ob}(\mathcal{C}_2)\}\). \(\alpha\) is natural transformation iff both of the following are true:
1. for every object \(X\) in \(\mathcal{C}_1\), \(\alpha_X=\{\alpha_{X,Y}\in\mathcal{D}(F(X,Y),G(X,Y))|Y\in\mathrm{Ob}(\mathcal{C}_2)\}\) is natural transformation between \(F(X,*)\) and \(G(X,*)\),
2. for every object \(Y\) in \(\mathcal{C}_2\), \(\alpha_Y=\{\alpha_{X,Y}\in\mathcal{D}(F(X,Y),G(X,Y))|X\in\mathrm{Ob}(\mathcal{C}_1)\}\) is natural transformation between \(F(*,Y)\) and \(G(*,Y)\).

*proof.* (\(\Rightarrow\)) if \(\alpha\) is natural transformation, then for every morphism \(f:(X_1,Y_1)\to(X_2,Y_2)\) in \(\mathcal{C}_1\times\mathcal{C}_2\),
\[
\begin{CD}
F(X_1,Y_1) @>\alpha_{X_1,Y_1}>> G(X_1,Y_1) \\
@VFfVV @VVGfV \\
F(X_2,Y_2) @>>\alpha_{X_2,Y_2}> G(X_2,Y_2)
\end{CD}
\]
commutes.

Therefore for every object \(X\) in \(\mathcal{C}_1\), for every morphism \(f:Y_1\to Y_2\) in \(\mathcal{C}_2\),
\[
\begin{CD}
F(X,Y_1) @>\alpha_{X,Y_1}>> G(X,Y_1) \\
@VF(\mathrm{id}_{X}\times f)VV @VVG(\mathrm{id}_{X}\times f)V \\
F(X,Y_2) @>>\alpha_{X,Y_2}> G(X,Y_2)
\end{CD}
\]
commutes, which means \(\alpha_X\) is natural transformation. Similarly \(\alpha_Y\) is natural transformation.

(\(\Leftarrow\)) Using the equation \ref{eq:bifunctor-commute} backwards, then we have a decomposition of every morphism \((f,g):(X_1,Y_1)\to(X_2,Y_2)\) in \(\mathcal{C}_1\times\mathcal{C}_2\). Then the diagram
\[
\begin{CD}
F(X_1,Y_1) @>\alpha_{X_1,Y_1}>> G(X_1,Y_1) \\
@VF(f,\mathrm{id}_{Y_1})VV @VVG(f,\mathrm{id}_{Y_1})V \\
F(X_2,Y_1) @>\alpha_{X_2,Y_1}>> G(X_2,Y_1) \\
@VF(\mathrm{id}_{X_2},g)VV @VVG(\mathrm{id}_{X_2},g)V \\
F(X_2,Y_2) @>>\alpha_{X_2,Y_2}> G(X_2,Y_2)
\end{CD}
\]
commutes because the two requirements are satisfied. \(\Box\)

Here are some examples of bifunctor:
1. The product bifunctor \(\times\) that maps two objects \((X,Y)\) to \(X\times Y\) in the category \(\mathcal{C}_1\times\mathcal{C}_2\) and two morphisms \((f,g)\) to \(f\times g\).
2. The hom-set in a category \(\mathcal{C}\) forms a bifunctor \(\mathcal{C}(*,*):\mathcal{C}^{\mathrm{op}}\times\mathcal{C}\to \mathsf{Set}\) (for simplicity, \(\mathcal{C}(*,*)\) is denoted as \(\hom\) later). For \(X\in\mathrm{Ob}(\mathcal{C}^{\mathrm{op}})=\mathrm{Ob}(\mathcal{C})\) (\(\mathcal{C}\) and \(\mathcal{C}^{\mathrm{op}}\) are the same in terms of objects) and \(Y\in\mathrm{Ob}(\mathcal{C})\), \(\hom(X,Y)=\mathcal{C}(X,Y)\). For every morphisms \(f:X_1\to X_2\) in \(\mathcal{C}^{\mathrm{op}}\) and \(g:Y_1\to Y_2\) in \(\mathcal{C}\), \(\hom(f,g)\) is a function \(\mathcal{C}(X_1,Y_1)\to\mathcal{C}(X_2,Y_2)\) that maps morphism \(h:X_1\to Y_1\) to \(g\circ h\circ f^{\mathrm{op}}:X_2\to Y_2\).

## Adjunctions

We can generalize the \(\hom\) functor above to handle two related categories at once.

**Adjunctions.** Let \(\mathcal{C},\mathcal{D}\) be two categories, \(L:\mathcal{D}\to\mathcal{C},R:\mathcal{C}\to\mathcal{D}\) be functors like the following diagram:
```tikz
\documentclass[tikz]{standalone}
\usepackage{amsmath,amssymb}
\begin{document}
\begin{tikzpicture}
  \node (D) at (2.2,0) {$\mathcal{D}$};
  \node (C) at (0,0)   {$\mathcal{C}$};
  \draw[->] (D) to[bend left=30] node[above] {$L$} (C);
  \draw[->] (C) to[bend left=30] node[above] {$R$} (D);
\end{tikzpicture}
\end{document}
```

Consider the following two bifunctors:
1. \(\mathcal{C}(L*,*):\mathcal{C}\times\mathcal{D}^{\mathrm{op}}\to\mathsf{Set}\) that maps an object \((c,d)\) to \(\mathcal{C}(Ld,c)\) and a morphism \((f,g):(c,d)\to(c',d')\) to a function that maps morphism \(h:Ld\to c\) to \(f\circ h\circ Lg^{\mathrm{op}}:Ld'\to c'\),
2. \(\mathcal{D}(*,R*):\mathcal{C}\times\mathcal{D}^{\mathrm{op}}\to\mathsf{Set}\) that maps an object \((c,d)\) to \(\mathcal{D}(d,Rc)\) and a morphism \((f,g):(c,d)\to(c',d')\) to a function that maps morphism \(h:d\to Rc\) to \(Rf\circ h\circ g^{\mathrm{op}}:d'\to Rc'\).

If there is a isomorphism \(\varphi:\mathcal{C}(L*,*)\cong\mathcal{D}(*,R*)\) in the category of bifunctors \(\mathsf{Set}^{\mathcal{C}\times\mathcal{D}^{\mathrm{op}}}\), then the tuple of functors and the isomorphism \((L,R,\varphi)\) forms an *adjunction*. \(L\) is called *the left adjoint to* \(R\) and \(R\) is called *the right adjoint to* \(L\), or just written as \(L\dashv R\). \(\Box\)

Let's unpack the definition:
- An isomorphism \(\varphi\) between the two (bi)functors \(\mathcal{C}(L*,*)\) and \(\mathcal{D}(*,R*)\) in the category of (bi)functors are a pair of natural transformations \(\varphi:\mathcal{C}(L*,*)\to\mathcal{D}(*,R*)\) and \(\varphi^{-1}:\mathcal{D}(*,R*)\to\mathcal{C}(L*,*)\) such that \(\varphi\circ\varphi^{-1}=\mathrm{id}_{\mathcal{D}(*,R*)}\), \(\varphi^{-1}\circ\varphi=\mathrm{id}_{\mathcal{C}(L*,*)}\).
- \(\varphi\) is a set of morphisms \(\{\varphi_{c,d}:\mathcal{C}(Ld,c)\to\mathcal{D}(d,Rc)|(c,d)\in\mathcal{C}\times\mathcal{D}^{\mathrm{op}}\}\). Using \ref{prop:bifunctor-natural}, the naturality holds iff the following two squares commutes for every \(g:c\to c'\) in \(\mathcal{C}\) and \(h:d\to d'\) in \(\mathcal{D}^{\mathrm{op}}\) (where \(\mathcal{C}(Ld,g)\) is the shorthand of \((\mathcal{C}(L*,*))(*,d)g\) [^unpack] and so on):

\[
\begin{CD}
\mathcal{C}(Ld,c) @>\varphi_{c,d}>> \mathcal{D}(d,Rc) \\
@V\mathcal{C}(Ld,g)VV @VV\mathcal{D}(d,Rg)V \\
\mathcal{C}(Ld,c') @>>\varphi_{c',d}> \mathcal{D}(d,Rc')
\end{CD}
\quad\quad\quad
\begin{CD}
\mathcal{C}(Ld,c) @>\varphi_{c,d}>> \mathcal{D}(d,Rc) \\
@A\mathcal{C}(Lh^{\mathrm{op}},c)AA @AA\mathcal{D}(h^{\mathrm{op}},Rc)A \\
\mathcal{C}(Ld',c) @>>\varphi_{c,d'}> \mathcal{D}(d',Rc)
\end{CD}
\tag{eq:adjunction-naturality}
\]

[^unpack]: If you find \((\mathcal{C}(L*,*))(*,d)g\) confusing, let \(F:=\mathcal{C}(L*,*)\) and the expression becomes \(F(*,d)g\). Now it should be clear that it's a functor applies to the morphism \(g\).

- There are similar naturality claims about \(\varphi^{-1}\).
- \(\varphi\circ\varphi^{-1}=\mathrm{id}_{\mathcal{D}(*,R*)}\), \(\varphi^{-1}\circ\varphi=\mathrm{id}_{\mathcal{C}(L*,*)}\) means for every \((c,d)\) in \(\mathcal{C}\times\mathcal{D}^{\mathrm{op}}\), \(\varphi_{c,d}\circ\varphi^{-1}_{c,d}=\mathrm{id}_{\mathcal{D}(d,Rc)}\) and \(\varphi^{-1}_{c,d}\circ\varphi_{c,d}=\mathrm{id}_{\mathcal{C}(Ld,c)}\), which means \(\mathcal{C}(Ld,c)\cong\mathcal{D}(d,Rc)\) and \(\varphi_{c,d}\) is the isomorphism.

There is an equivalent definition of the adjunctions that are handy when proving things. You don't need to understand its proof to understand the topic, so I'll put it in the appendix.

**Lemma.**\label{lem:adjunction-unit-counit} Let \(\mathcal{C},\mathcal{D}\) be categories and \(L:\mathcal{D}\to\mathcal{C},R:\mathcal{C}\to\mathcal{D}\) be functors. \(L\dashv R\) iff both of the claims are true:
1. There is a natural transformation \(\varepsilon:L\circ R\to\mathrm{id}_{\mathcal{C}}\) (called *counit*) such that for every object \(c\) in \(\mathcal{C}\) and object \(d\) in \(\mathcal{D}\), if there is a morphism \(f:Ld\to c\), then there is a unique morphism \(g:d\to Rc\) such that \(f=\varepsilon_c\circ Lg\), i.e. the triangle on the right commutes:
```tikz
\documentclass[tikz]{standalone}
\usepackage{amsmath,amssymb}
\begin{document}
\begin{tikzpicture}
  \node (d)   at (0,2.4)    {$d$};
  \node (Ld)  at (3.6,2.4)  {$Ld$};
  \node (Rc)  at (0,0)      {$Rc$};
  \node (LRc) at (3.6,0)    {$(L\circ R)c$};
  \node (c)   at (6.8,0)    {$c$};
  \draw[->] (d) to node[left] {$g$} (Rc);
  \draw[->] (Ld) to node[left] {$Lg$} (LRc);
  \draw[->] (Ld) to node[sloped,above] {$f$} (c);
  \draw[->] (LRc) to node[below] {$\varepsilon_c$} (c);
\end{tikzpicture}
\end{document}
```
2. There is a natural transformation \(\eta:\mathrm{id}_{\mathcal{D}}\to R\circ L\) (called *unit*) such that for every object \(d\) in \(\mathcal{D}\) and object \(c\) in \(\mathcal{C}\), if there is a morphism \(g:d\to Rc\), then there is a unique morphism \(f:Ld\to c\) such that \(g=Rf\circ \eta_d\).

The following are the direct results of adjunctions:

**Proposition**\label{prop:right-adjoint-terminal} (Right adjoints preserves terminal objects). For an adjunction \((L,R, \varphi)\) between categories \(\mathcal{C},\mathcal{D}\), if terminal objects exists in both categories and \(c\) is the terminal object in \( \mathcal{C}\), then \(Rc\) is the terminal object in \( \mathcal{D}\).

*proof.* For every object \(d\in \mathrm{Ob}( \mathcal{D})\), because \(c\) is terminal object of \( \mathcal{C}\), therefore there exists unique morphism \( Ld\to c\), therefore \(\mathcal{C}(Ld,c)\) will have exactly one morphism.

Because \( \varphi_{c,d}:\mathcal{C}(Ld,c)\cong\mathcal{D}(d,Rc)\), therefore \(\mathcal{D}(d,Rc)\) will also have exactly one morphism. This is true for every \(d\in \mathrm{Ob}( \mathcal{D})\), hence \(Rc\) is the terminal object in \( \mathcal{D}\). \(\Box\)

**Proposition**\label{prop:right-adjoint-product} (Right adjoints preserves product). For an adjunction \((L,R, \varphi)\) between categories \(\mathcal{C},\mathcal{D}\) and \(C\subseteq \mathrm{Ob}( \mathcal{C})\), if \(\prod C\) exists, then \(\prod\{Rc|c\in C\}\) also exists, and \(\prod\{Rc|c\in C\}=R(\prod C)\).

*proof.* By definition of \(\prod\{Rc|c\in C\}\), we need to prove that:
1. For every \(Rc\in\{Rc'|c'\in C\}\), there is a morphism \(f'_{Rc}:R(\prod C)\to Rc\),
2. For every \(d\in \mathrm{Ob}( \mathcal{D})\), if for every \(Rc\in\{Rc'|c'\in C\}\), there is a morphism \(g'_{Rc}:d\to Rc\), then there is a unique morphism \(f':d\to R(\prod C)\) such that for every \(c\in C\), \(g'_{Rc}=f'_{Rc}\circ f'\).

The first claim can be proved by applying \(R\) to the definition of \(\prod C\). Let's focus on the second one.

Because \((L,R,\varphi)\) is the adjunction, therefore for every \(c,d\), \( \mathcal{C}(Ld,c)\cong \mathcal{D}(d,Rc)\). Therefore if there is a morphism \(d\to Rc\) in \( \mathcal{D}\), then there is a morphism \(Ld\to c\) in \( \mathcal{C}\).

By definition of \(\prod C\), because for every \(c\in C\), there is a morphism \(g_c:Ld\to c\), therefore there exists a unique morphism \(f:Ld\to\prod C\) such that \(g_c=f_c\circ f\), where \(f_c\) is the morphism \(\prod C\to c\).

Because \(f\) is unique, therefore \( \mathcal{C}(Ld,\prod C)\) is a singleton set, therefore \( \mathcal{D}(d,R(\prod C))\) is also a singleton set, which means there is a unique \(f':d\to R(\prod C)\). We can get the equation \(g'_{Rc}=f'_{Rc}\circ f\) by connecting \(f'\) and \(R\) applied to the morphism \(\prod C\to c\). \(\Box\)

Similarly, we can prove that left adjoints preserves initial objects and coproducts.

The converse of \ref{prop:right-adjoint-product} is also true for lattices: between two complete lattices, we can construct an adjunction pair from a functor that preserves product.

**Proposition.**\label{prop:lattice-adjunction} Let \( \mathcal{C}, \mathcal{D}\) be complete lattices and \(R: \mathcal{C}\to \mathcal{D}\) be a functor. If for every \(C\subseteq \mathrm{Ob}( \mathcal{C})\), \(\prod\{Rc|c\in C\}=R(\prod C)\), then there exists a functor \(L\) and natural isomorphism \( \varphi\) such that \(L\) and \(R\) forms an adjunction pair.

*proof.* We define the left adjoint \(L: \mathcal{D}\to \mathcal{C}\) as
\[L:d\mapsto\prod\{c|c\in \mathrm{Ob}( \mathcal{C}),d\to Rc\}\]
and define the unit \(\eta\) and counit \( \varepsilon\).

Because \(R\) preserves product, therefore for every \(d\in \mathrm{Ob}( \mathcal{D})\),
\[(R\circ L)d=R(Ld)=R\left(\prod\{c|d\to Rc\}\right)=\prod\{Rc|d\to Rc\}.\]

For every \(d'\in \{Rc|d\to Rc\}\), there is a morphism \(d\to d'\). By definition of product, there exists a unique morphism \(d\to\prod\{Rc|d\to Rc\}=(R\circ L)d\). We can use this morphism as \(\eta_d\).

For every \(c\in \mathrm{Ob}( \mathcal{C})\),
\[(L\circ R)c=L(Rc)=\prod\{c'|Rc\to Rc'\}.\]

Because \(R\,\mathrm{id}_c:Rc\to Rc\), therefore \(c\in\{c'|Rc\to Rc'\}\), therefore there is a morphism \(\prod\{c'|Rc\to Rc'\}\to c\). We can use this morphism as \( \varepsilon_c\).

Because \( \mathcal{C}, \mathcal{D}\) are lattices, therefore \(\eta\) and \( \varepsilon\) automatically becomes natural transformations. Using the first definition, we know that \(L\) and \(R\) forms an adjunction pair. \(\Box\)

\ref{prop:lattice-adjunction} doesn't hold in general because we may choose an arbitrary morphism \(\prod\{c'|Rc\to Rc'\}\to c\) that make the diagram not commute.

The following propositions allow us to create adjunction pairs on product and map lattices easily.

**Proposition.**\label{prop:adjunction-product} Let \(\mathcal{C}_1, \mathcal{D}_1, \mathcal{C}_2, \mathcal{D}_2\) be categories and \(L_1: \mathcal{D}_1\to \mathcal{C}_1,R_1: \mathcal{C}_1\to \mathcal{D}_1, L_2: \mathcal{D}_2\to \mathcal{C}_2,R_2: \mathcal{C}_2\to \mathcal{D}_2\) be functors. If \(L_1\dashv R_1\), \(L_2\dashv R_2\), then \(L_1\times L_2\dashv R_1\times R_2\).

*proof*. I'm getting lazy by this point and decided to let an AI agent write a proof in Lean4:
```lean
-- Imports and universes are omitted

-- Defines categories and adjunctions. The notation is a bit weird but understandable.
-- BTW, you can view the definition by hovering on the symbol if you are using VSCode
variable {C₁ : Type u₁} [Category.{v₁} C₁] {D₁ : Type u₂} [Category.{v₂} D₁]
  {C₂ : Type u₃} [Category.{v₃} C₂] {D₂ : Type u₄} [Category.{v₄} D₂]
  {L₁ : D₁ ⥤ C₁} {R₁ : C₁ ⥤ D₁} (adj₁ : L₁ ⊣ R₁)
  {L₂ : D₂ ⥤ C₂} {R₂ : C₂ ⥤ D₂} (adj₂ : L₂ ⊣ R₂)

-- The proposition is "proved" by constructing an adjunction pair using the first definition
-- `L₁.prod L₂` is a functor from `D₁.prod D₂` to `C₁.prod C₂` that maps `(d.1 d.2)` to `(L₁ d.1, L₂ d.2)`
def Adjunction.prod : L₁.prod L₂ ⊣ R₁.prod R₂ where
  unit :=
    { -- A natural transformation is defined by a function mapping a object to a morphism equipped with the naturality equation.
      -- Our function applies (d.1, d.2) to (unit₁ d.1, unit₂ d.2)
      app := fun d => (adj₁.unit.app d.1, adj₂.unit.app d.2)
      naturality := fun {d d'} f => by
        ext -- skips too many details
        · exact adj₁.unit.naturality f.1
        · exact adj₂.unit.naturality f.2 }
  counit :=
    { app := fun c => (adj₁.counit.app c.1, adj₂.counit.app c.2)
      naturality := fun {c c'} f => by
        ext
        · exact adj₁.counit.naturality f.1
        · exact adj₂.counit.naturality f.2 }
```

The naturality proof is like an "It's trivial" in math textbook. Let me explain it in detail.

Let the unit we have defined be \(\eta=(\eta_1,\eta_2)\) and we need to prove that for every morphism \(f:(d_1,d_2)\to (d_1',d_2')=(f_1,f_2)\) on \(\mathcal{D}_1\times \mathcal{D}_2\),
\[\eta\circ f (d_1,d_2)=(R'\circ L') f\circ\eta(d_1,d_2).\]

This is an identity on \(\mathcal{D}_1\times \mathcal{D}_2\) [^identity], and the `ext` tactic split this target into identities on \(\mathcal{D}_1\) and \(\mathcal{D}_2\) respectively:
\[\eta_1\circ f_1\ d_1=((R'_1\circ L'_1) f_1)\circ\eta_1\ d_1,\quad\eta_2\circ f_2\ d_2=((R'_2\circ L'_2) f_2)\circ\eta_2\ d_2,\]
where \(R'_1\) is the first component of \(R'\) and so on.

[^identity]: Actually it's an identity on morphisms (i.e. there is no \((d_1,d_2)\)) if you wiew it in Lean InfoView. I'm just making things easier to understand here.

By definition, \(L_1'\) maps any object \(d\in \mathrm{Ob}(\mathcal{D})\) to \(L_1 d\), so \(L_1'=L_1\). Similarly \(L_2'=L_2,R_1'=R_1\) and \(R_2'=R_2\). The equations above reduces to the naturality of the unit of \(L_1\dashv R_1\) and \(L_2\dashv R_2\). The counit is similar. \(\Box\)

**Proposition.**\label{prop:adjunction-functor-category} Let \( \mathcal{I}, \mathcal{C}, \mathcal{D}\) be categories and \(L: \mathcal{D}\to \mathcal{C},R: \mathcal{C}\to \mathcal{D}\) be functors. If \(L\) and \(R\) forms an adjunction pair, then there exists functors \(L': \mathcal{D}^{\mathcal{I}}\to \mathcal{C}^\mathcal{I}\) and \(R': \mathcal{C}^{\mathcal{I}}\to \mathcal{D}^\mathcal{I}\) such that \(L',R'\) forms an adjunction pair.

*proof*. Used LLM and got a "trivial answer" again:
```lean
variable (I : Type u₅) [Category.{v₅} I]
  {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {L : D ⥤ C} {R : C ⥤ D} (adj : L ⊣ R)

def Adjunction.postcompose :
    (whiskeringRight I D C).obj L ⊣ (whiskeringRight I C D).obj R where
  unit :=
    { app := fun X => whiskerLeft X adj.unit
      naturality := by intros; ext; simp }
  counit :=
    { app := fun F => whiskerLeft F adj.counit
      naturality := by intros; ext; simp }
```

The explaination:
1. `(whiskeringRight I D C).obj` is a functor \((\mathcal{D}\to \mathcal{C})\to((\mathcal{I}\to \mathcal{D})\to(\mathcal{I}\to \mathcal{C}))\) that maps a functor \(F:\mathcal{D}\to\mathcal{C}\) to a functor \(G:(\mathcal{I}\to \mathcal{D})\to(\mathcal{I}\to \mathcal{C})\) that maps a functor \(H:\mathcal{I}\to \mathcal{D}\) to a functor \(F\circ H\).
2. We use `(whiskeringRight I D C).obj L` as the left adjoint \(L'\). It maps functor \(X:\mathcal{I}\to\mathcal{D}\) to \(L\circ X\).
3. Similarly, we use `(whiskeringRight I C D).obj R` as the right adjoint \(R'\).
4. To construct the unit, we need a function that maps an object \(X\) in \(\mathcal{D}^{\mathcal{I}}\) to a morphism \(X\to (R'\circ L') X\) in \(\mathcal{D}^{\mathcal{I}}\). It's given by `whiskerLeft X adj.unit`, which means lifting (whiskering) the unit \(\mathrm{id}_{\mathcal{D}}\to R\circ L\) to \(\mathrm{id}_{\mathcal{D}}\circ X\to (R\circ L)\circ X\). It exploits the fact that \(X\) is a morphism \(\mathcal{I}\to\mathcal{D}\).
   - Lean4 did some bookkeeping behind the scene: \(X\) is equivalent to \(\mathrm{id}_{\mathcal{D}}\circ X\) and \((R\circ L)\circ X\) is equivalent to \(R'(L'X)\) in \(\mathcal{D}^{\mathcal{I}}\).

The naturality proof is completely useless from understanding perspective, so let's prove it ourselves.

For every morphism \(f:X\to Y\) in \(\mathcal{D}^{\mathcal{I}}\), we need to prove
\[\eta_Y\circ f=(R'\circ L')f\circ \eta_X.\]

The both sides of the equation are morphisms in \(\mathcal{D}^{\mathcal{I}}\), which are natural transformations, so we can prove that for every \(i\in \mathrm{Ob}(\mathcal{I})\),
\[(\eta_Y\circ f)_i=((R'\circ L')f\circ \eta_X)_i.\]

By definition of the composition of natural transformations, we have
\[(\eta_Y)_i\circ f_i=((R'\circ L')f)_i\circ(\eta_X)_i.\]

\(\eta_Y:Y\to (R'\circ L')Y=R\circ L\circ Y\) is a natural transformation between functors \(Y\) and \(R\circ L\circ Y\), so \((\eta_Y)_i\) is a morphism \(Y\, i\to R\circ L\circ Y\, i\) in \(\mathcal{D}\). Similarly, the goal reduces to the following square:
\[
\begin{CD}
X\, i @>f_i>> Y\, i \\
@V\eta_XVV @VV\eta_YV \\
R\circ L\circ X\, i @>>((R'\circ L')f)_i> R\circ L\circ Y\, i
\end{CD}
\]
which holds by the naturality of the unit of \(L\dashv R\). \(\Box\)

## Further Reading

Most of the definition in this post are from the following materials:
- [Bartosz Milewski's *Category Theory for Programmers*](https://bartoszmilewski.com/2014/10/28/category-theory-for-programmers-the-preface/) is a good starting point for programmers who have forgotten most of their college level math.
- Reading Saunders Mac Lane's *Categories For the Working Mathematician* is the canonical way to learn category theory. You should be able to understand the first 4 chapters after reading this post.
- [MIT 18.S097](https://ocw.mit.edu/courses/18-s097-applied-category-theory-january-iap-2019/) taught by David Spivak and Brendan Fong is a harder tutorial with more real-world examples.
- If you are *really* good at math and happens to know Chinese, check out the first few chapters of [Wenwei Li's *Methods of algebra: Volume 1*](https://www.wwli.asia/docs/books#%E4%BB%A3%E6%95%B0%E5%AD%A6%E6%96%B9%E6%B3%95%E5%8D%B7%E4%B8%80-methods-of-algebra-volume-1-in-chinese).

## Appendix: Equivalence Proof

(\(\varphi\Rightarrow\varepsilon,\eta\)) Given \(\varphi\), the simplest way to construct that has ths same "signature" as \(\eta:\mathrm{id}_\mathcal{D}\to R\circ L\) is to pass identity morphism \( \mathrm{id}_{Ld}\) to \(\varphi_{Ld,d}\), i.e.
\[\eta=\{\varphi_{Ld,d}\ \mathrm{id}_{Ld}\in \mathcal{D}(d,R(Ld))|d\in \mathrm{Ob}( \mathcal{D})\},\]
and this is the unit we wanted.

For every \(g:d\to d'\), we apply \(Lg\) to the left of diagram \eqref{eq:adjunction-naturality} and \(g^\mathrm{op}\) to the diagram on the right to form the following commute diagram:
\[
\begin{CD}
\mathcal{C}(Ld,Ld) @>\mathcal{C}(Ld,Lg)>> \mathcal{C}(Ld,Ld') @<\mathcal{C}(Lg^{\mathrm{op}},Ld')<< \mathcal{C}(Ld',Ld') \\
@V\varphi_{Ld,d} VV @VV\varphi_{Ld',d} V @VV\varphi_{Ld',d'} V \\
\mathcal{D}(d,R(Ld)) @>\mathcal{D}(d,R(Lg))>> \mathcal{D}(d,R(Ld')) @<\mathcal{D}(g^\mathrm{op},R(Ld'))<< \mathcal{D}(d',R(Ld'))
\end{CD}
\]

The objects in the diagram are sets and morphisms are functions, so we can apply the functions to specific elements in the sets. Applying the left square to \(\mathrm{id}_{Ld}\) yields:
\[
\begin{aligned}
    & (\mathcal{D}(d,R(Lg))\circ\varphi_{Ld,d})\ \mathrm{id}_{Ld}=(\varphi_{Ld',d}\circ\mathcal{C}(Ld,Lg))\ \mathrm{id}_{Ld} \\
    & \Rightarrow\mathcal{D}(d,R(Lg))\ \eta_d=\varphi_{Ld',d}(\mathcal{C}(Ld,Lg)\ \mathrm{id}_{Ld}), \\
    & \Rightarrow(\mathcal{D}(*,R*)(*,d)Lg)\ \eta_d=\varphi_{Ld',d}((\mathcal{C}(L*,*)(*,d)Lg)\ \mathrm{id}_{Ld}), \\
    & (\mathcal{D}(g^\mathrm{op},R(Ld'))\circ\varphi_{Ld',d'})\ \mathrm{id}_{Ld}=(\varphi_{Ld',d'}\circ\mathcal{C}(Lg^{\mathrm{op}},Ld))\ \mathrm{id}_{Ld'} \\
    & \Rightarrow\mathcal{D}(g^\mathrm{op},R(Ld'))\eta_{d'}=\varphi_{Ld',d'}(\mathcal{C}(Lg^{\mathrm{op}},Ld)\ \mathrm{id}_{Ld'}) \\
    & \Rightarrow(\mathcal{D}(*,R*)(Ld',*)g^\mathrm{op})\eta_{d'}=\varphi_{Ld',d'}((\mathcal{C}(L*,*)(Ld,*)g^{\mathrm{op}})\ \mathrm{id}_{Ld'}).
\end{aligned}
\]

\(\mathcal{D}(*,R*)(*,d)\) is a functor that maps morphism \(Lg\) to \(\mathcal{D}(*,R*)(Lg,\mathrm{id}_d)\), which is a function that maps morphism \(\eta_d:\) to
\[R(Lg)\circ \eta_d\circ(\mathrm{id}_d)^{\mathrm{op}}=R(Lg)\circ \eta_d.\]

Similarly,
\[(\mathcal{D}(*,R*)(Ld',*)g^\mathrm{op})\eta_{d'}=R(\mathrm{id}_{Ld'})\circ\eta_{d'}\circ(g^{\mathrm{op}})^{\mathrm{op}}=\eta_{d'}\circ g,\]
\[(\mathcal{C}(L*,*)(*,d)Lg)\mathrm{id}_{Ld}=Lg\circ\mathrm{id}_{Ld}\circ L(\mathrm{id}_d)^{\mathrm{op}}=Lg,\]
\[(\mathcal{C}(L*,*)(Ld,*)g^{\mathrm{op}})\ \mathrm{id}_{Ld'}=\mathrm{id}_{Ld}\circ \mathrm{id}_{Ld'}\circ L(g^{\mathrm{op}})^{\mathrm{op}}=Lg,\]
therefore
\[R(Lg)\circ\eta_d=\eta_{d'}\circ g,\]
therefore \(\eta\) is a natural transformation.

Similarly, we can define
\[\varepsilon=\{\varphi_{c,Rc}^{-1}\ \mathrm{id}_{Rc}\in \mathcal{C}(L(Rc),c)|c\in\mathrm{Ob}( \mathcal{C})\}\]
and prove that it's a natural transformation.

Finally, we need to prove that \(\varepsilon\) and \(\eta\) satisfies the two requirements.

By diagram \ref{eq:adjunction-naturality}, for every \(f:Ld\to c\), the diagram
\[
\begin{CD}
\mathcal{C}(Ld,Ld) @>\varphi_{Ld,d}>> \mathcal{D}(d,R(Ld)) \\
@V\mathcal{C}(Ld,f)VV @VV\mathcal{D}(d,Rf)V \\
\mathcal{C}(Ld,c) @>>\varphi_{c,d}> \mathcal{D}(d,Rc)
\end{CD}
\]
commutes. Using the same trick as above, we have
\[\begin{aligned}
& (\varphi_{c,d}\circ\mathcal{C}(Ld,f))\mathrm{id}_{Ld}=(\mathcal{D}(d,Rf)\circ\varphi_{Ld,d})\mathrm{id}_{Ld} \\
& \Rightarrow \varphi_{c,d}(f\circ\mathrm{id}_{Ld}\circ L\mathrm{id}_{d})=\mathcal{D}(d,Rf)(\eta_d) \\
& \Rightarrow \varphi_{c,d}(f)=Rf\circ\eta_d.
\end{aligned}\]

Similarly, we have \(\varphi^{-1}_{c,d}(f)=\varepsilon_c\circ Lf\).

Therefore we can let \(g=\varphi_{c,d}(f)\) in the second requirement and \(f=\varphi^{-1}_{c,d}(g)\) in the first requirement. The uniqueness is guaranteed because \(\varphi_{c,d}\) is isomorphism.

(\(\eta,\varepsilon\Rightarrow\varphi\)) Given \(\eta,\varepsilon\), For every \(c\in\mathcal{C},d\in\mathcal{D}\), we can construct a function \(\varphi_{c,d}:\mathcal{C}(Ld,c)\to\mathcal{D}(d,Rc)\) that maps \(f:Ld\to c\) to \(Rf\circ\eta_d\).

The requirement 2 says that for every morphism \(g\in\mathcal{D}(d,Rc)\), there is exactly one morphism \(f\in\mathcal{C}(Ld,c)\) such that \(g=\varphi_{c,d}(f)\), therefore \(\varphi_{c,d}\) is a bijection and thus an isomorphism.

Next we need to prove that for every \(g:c\to c'\in \mathrm{Mor}( \mathcal{C}),h:d'\to d\in \mathrm{Mor}( \mathcal{D}^{ \mathrm{op}})\), diagram \eqref{eq:adjunction-naturality} commutes.

Because for every morphism \(f\in\mathcal{C}(Ld,c)\),
\[
\begin{aligned}
    (\mathcal{D}(d,Rg)\circ\varphi_{c,d})f & =\mathcal{D}(d,Rg)(Rf\circ\eta_d) \\
    & =Rg\circ(Rf\circ\eta_d) \\
    & =R(g\circ f)\circ\eta_d \\
    & =\varphi_{c,d}(g\circ f) \\
    & =\varphi_{c',d}(g\circ f) & (\varphi\text{ is independent on the choice of }c) \\
    & =\varphi_{c',d}(\mathcal{C}(Ld,g)f) \\
    & =(\varphi_{c',d}\circ\mathcal{C}(Ld,g))f,
\end{aligned}
\]
therefore the first diagram commutes.

Because for every morphism \(f\in\mathcal{C}(Ld',c)\),
\[
\begin{aligned}
    (\mathcal{D}(h,Rc)\circ\varphi_{c,d'})f & =\mathcal{D}(h,Rc)(Rf\circ\eta_{d'}) \\
    & =(Rf\circ\eta_{d'})\circ h^{ \mathrm{op}} \\
    & =Rf\circ(\eta_{d'}\circ h^{ \mathrm{op}}) \\
    & =Rf\circ((R\circ L)h^{ \mathrm{op}}\circ\eta_d) & (\text{see diagram \eqref{eq:eta-naturality}}) \\
    & =R(f\circ L(h^{ \mathrm{op}}))\circ\eta_d & (\text{by functorality}) \\
    & =R(f\circ (L^{\mathrm{op}}h)^{ \mathrm{op}})\circ\eta_d & (\text{note that }h\in \mathrm{Mor}( \mathcal{D}^{ \mathrm{op}})) \\
    & =\varphi_{c,d}(f\circ(L^{ \mathrm{op}}h)^{ \mathrm{op}}) \\
    & =(\varphi_{c,d}\circ\mathcal{D}(L^{ \mathrm{op}}h,c))f,
\end{aligned}
\]
where the diagram \eqref{eq:eta-naturality} commutes by the naturality of \(\eta\):
\[
\begin{CD}
d @>h^{ \mathrm{op}}>> d' \\
@V\eta_d VV @VV\eta_{d'} V \\
(R\circ L)d @>>(R\circ L)h^{ \mathrm{op}}> (R\circ L)d'
\end{CD}
\tag{eq:eta-naturality}\]

Therefore the second diagram commutes.

There is a useful by-product of the proof:

**Corollary.**\label{cor:adjunction-formula} Let \(\eta,\varepsilon\) be the unit and counit of the adjunction pair \((L,R,\varphi)\), then
\[\varphi_{c,d}(f)=Rf\circ\eta_d,\quad\varphi^{-1}_{c,d}(f)=\varepsilon_c\circ Lf.\]

