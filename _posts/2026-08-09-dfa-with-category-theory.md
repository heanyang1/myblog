---
layout: post
title:  "Data Flow Analysis with Category Theory (Part 2)"
---

> This is the second post of a series about me learning static analysis. Here's [the previous post](/myblog/2026/07/19/data-flow-analysis-with-stapl.html).

When writing the previous post, I realized that lattices are just categories and I can avoid reinventing wheels by directly using some well-known theorems in category theory. So before proving the soundness of sign analysis, I'd like to take a little detour about category theory and how it can be used to understand the problem.

If you are familiar with things like adjunctions and limits, feel free to skip this post. If not, you don't need to read any additional materials (this post should be self-contained), although I'll recommend you to read other books since this post only cover what is needed in DFA. [^update]

[^update]: On the other hand, I haven't finished the soundness proof, so things in this post is just the tools being used so far, and maybe I'll add more content to this post later.

I used AI to draw some of the diagrams in this post. Everything else is handwritten.

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

In a lattice, by reflectivity, if \(x\cong y\), then \(x=y\).

**Functors.** Let \(\mathcal{C},\mathcal{C}'\) be categories. A *functor* \(F:\mathcal{C}\to \mathcal{C}'\) has:
- A function \(F:\mathrm{Ob}(\mathcal{C})\to\mathrm{Ob}(\mathcal{C}')\),
- A function \(F:\mathrm{Mor}(\mathcal{C})\to\mathrm{Mor}(\mathcal{C}')\) that
  - preserves morphisms, i.e. for every \(X,Y\in\mathrm{Ob}(\mathcal{C})\), there is a surjection \(F|_{\mathcal{C}(X,Y)}:\mathcal{C}(X,Y)\to\mathcal{C}'(FX,FY)\),
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

**Natural transformations.** The *natural transformation* \(\theta\) between two functors \(F,G:\mathcal{C}\to \mathcal{C}'\) is a set of morphisms \(\{\theta_X\in\mathcal{C}(FX,GX)|X\in\mathrm{Ob}(\mathcal{C})\}\) such that for every morphism \(f:X\to Y\in\mathrm{Mor}(\mathcal{C})\), \(\theta_Y\circ Ff=Gf\circ\theta_X\).

We can draw the objects and morphisms as the following *diagram*, and \(\theta_Y\circ Ff=Gf\circ\theta_X\) is equivalent to the claim that the following diagram commutes:
\[
\begin{CD}
FX @>\theta_X>> GX \\
@VFfVV @VVGfV \\
FY @>>\theta_Y> GY
\end{CD}
\]

In a lattice, every diagram commutes, so every two functors equipped with a map from object to morphisms can be natural transformation.

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

## Adjunctions

**Hom-functors.** The hom-set in a category \(\mathcal{C}\) forms a functor \(\mathcal{C}(*,Y):\mathcal{C}^{\mathrm{op}}\to \mathsf{Set}\) given any \(Y\in\mathcal{C}\):
- \(\mathcal{C}(*,Y)\) maps object \(X\) in \( \mathrm{Ob}(\mathcal{C}^{\mathrm{op}})\) to a hom-set \(\mathcal{C}(X,Y)\).
- For every morphism \(f:X\to X'\) in \(\mathcal{C}^{\mathrm{op}}\), we reverse its arrow and get a morphism \(f^{\mathrm{op}}:X'\to X\) in \(\mathcal{C}\), and define the morphism \(\mathcal{C}(*,Y)(f):\mathcal{C}(X,Y)\to\mathcal{C}(X',Y)\) as: for every morphism \(g\in\mathcal{C}(X,Y)\), \(\mathcal{C}(*,Y)(f)(g)=g\circ f^{\mathrm{op}}\in\mathcal{C}(X',Y) \) (Verify the functorality if you are interested).

Similarly, we can fix the source of the hom-set to get a functor \(\mathcal{C}(X,*):\mathcal{C}\to \mathsf{Set}\). The details are left as exercises.

For simplicity, we define \(\mathcal{C}(f,Y):=\mathcal{C}(*,Y)(f)\) and \(\mathcal{C}(X,f):=\mathcal{C}(X,*)(f)\). If \(X,Y, \mathcal{C}\) are well-defined in the context, then we'll further shorten it as \(f^*:=\mathcal{C}(f,Y)\) and \(f_*:=\mathcal{C}(X,f)\).

**Adjunctions.** Let \(\mathcal{C},\mathcal{D}\) be two categories, \(L:\mathcal{D}\to\mathcal{C},R:\mathcal{C}\to\mathcal{D}\) be functors like the following diagram:
{% graphviz %}
digraph {
    rankdir = RL;
    D->C [label="L"];
    C->D [label="R"];
}
{% endgraphviz %}

The following claims are equivalent:
1. There are two natural transformations \(\eta: \mathrm{id}_{ \mathcal{D}}\to R\circ L\) (called *unit*) and \( \varepsilon:L\circ R\to \mathrm{id}_{\mathcal{C}}\) (called *counit*),
2. For every \(c\in \mathrm{Ob}( \mathcal{C}),d\in \mathrm{Ob}(\mathcal{D})\), there is an isomorphism \(\varphi_{c,d}:\mathcal{C}(Ld,c)\cong\mathcal{D}(d,Rc)\) such that for every \(g:c\to c'\in \mathrm{Mor}( \mathcal{C}),h:d'\to d\in \mathrm{Mor}( \mathcal{D}^{ \mathrm{op}})\), the following diagrams commute:

\[
\begin{CD}
\mathcal{C}(Ld,c) @>\varphi_{c,d}>> \mathcal{D}(d,Rc) \\
@Vg_*VV @VV(Rg)_*V \\
\mathcal{C}(Ld,c') @>>\varphi_{c',d}> \mathcal{D}(d,Rc')
\end{CD}
\qquad
\begin{CD}
\mathcal{C}(Ld,c) @>\varphi_{c,d}>> \mathcal{D}(d,Rc) \\
@A(L^{\mathrm{op}}h)^*AA @AAh^*A \\
\mathcal{C}(Ld',c) @>>\varphi_{c,d'}> \mathcal{D}(d',Rc)
\end{CD}
\tag{2}\]

The tuple of functors and the isomorphism \((L,R,\varphi)\) is called an *adjunction*. \(L\) is called *the left adjoint to* \(R\) and \(R\) is called *the right adjoint to* \(L\).

You don't need to understand the equivalence proof to understand the topic, so I'll put it in the appendix A.

The following are the direct results of adjunctions:

**Proposition 1** (Right adjoints preserves terminal objects). For an adjunction \((L,R, \varphi)\) between categories \(\mathcal{C},\mathcal{D}\), if terminal objects exists in both categories and \(c\) is the terminal object in \( \mathcal{C}\), then \(Rc\) is the terminal object in \( \mathcal{D}\).

*proof.* For every object \(d\in \mathrm{Ob}( \mathcal{D})\), because \(c\) is initial object of \( \mathcal{C}\), therefore there exists unique morphism \( Ld\to c\), therefore \(\mathcal{C}(Ld,c)\) will have exactly one morphism.

Because \( \varphi_{c,d}:\mathcal{C}(Ld,c)\cong\mathcal{D}(d,Rc)\), therefore \(\mathcal{D}(d,Rc)\) will also have exactly one morphism. This is true for every \(d\in \mathrm{Ob}( \mathcal{D})\), hence \(Rc\) is the terminal object in \( \mathcal{D}\). \(\Box\)

**Proposition 2** (Right adjoints preserves product). For an adjunction \((L,R, \varphi)\) between categories \(\mathcal{C},\mathcal{D}\) and \(C\subseteq \mathrm{Ob}( \mathcal{C})\), if \(\prod C\) exists, then \(\prod\{Rc|c\in C\}\) also exists, and \(\prod\{Rc|c\in C\}=R(\prod C)\).

*proof.* By definition of \(\prod\{Rc|c\in C\}\), we need to prove that:
1. For every \(Rc\in\{Rc'|c'\in C\}\), there is a morphism \(f'_{Rc}:R(\prod C)\to Rc\),
2. For every \(d\in \mathrm{Ob}( \mathcal{D})\), if for every \(Rc\in\{Rc'|c'\in C\}\), there is a morphism \(g'_{Rc}:d\to Rc\), then there is a unique morphism \(f':d\to R(\prod C)\) such that for every \(c\in C\), \(g'_{Rc}=f'_{Rc}\circ f'\).

The first claim can be proved by applying \(R\) to the definition of \(\prod C\). Let's focus on the second one.

Because \((L,R,\varphi)\) is the adjunction, therefore for every \(c,d\), \( \mathcal{C}(Ld,c)\cong \mathcal{D}(d,Rc)\). Therefore if there is a morphism \(d\to Rc\) in \( \mathcal{D}\), then there is a morphism \(Ld\to c\) in \( \mathcal{C}\).

By definition of \(\prod C\), because for every \(c\in C\), there is a morphism \(g_c:Ld\to c\), therefore there exists a unique morphism \(f:Ld\to\prod C\) such that \(g_c=f_c\circ f\), where \(f_c\) is the morphism \(\prod C\to c\).

Because \(f\) is unique, therefore \( \mathcal{C}(Ld,\prod C)\) is a singleton set, therefore \( \mathcal{D}(d,R(\prod C))\) is also a singleton set, which means there is a unique \(f':d\to R(\prod C)\). We can get the equation \(g'_{Rc}=f'_{Rc}\circ f\) by connecting \(f'\) and \(R\) applied to the morphism \(\prod C\to c\). \(\Box\)

Similarly, we can prove that left adjoints preserves initial objects and coproducts.

## Further Reading

Most of the definition in this post are from the following materials:
- [Bartosz Milewski's *Category Theory for Programmers*](https://bartoszmilewski.com/2014/10/28/category-theory-for-programmers-the-preface/) is a good starting point for programmers who have forgotten most of their college level math.
- [MIT 18.S097](https://ocw.mit.edu/courses/18-s097-applied-category-theory-january-iap-2019/) taught by David Spivak and Brendan Fong is a harder tutorial with more real-world examples.
- If you are *really* good at math and happens to know Chinese, check out the first few chapters of [Wenwei Li's *Methods of algebra: Volume 1*](https://www.wwli.asia/docs/books#%E4%BB%A3%E6%95%B0%E5%AD%A6%E6%96%B9%E6%B3%95%E5%8D%B7%E4%B8%80-methods-of-algebra-volume-1-in-chinese).

## Appendix: Equivalence Proof

**Lemma 2.** Let \(\mathcal{C},\mathcal{D}\) be two categories, \(L:\mathcal{D}\to\mathcal{C},R:\mathcal{C}\to\mathcal{D}\), \(\eta: \mathrm{id}_{ \mathcal{D}}\to R\circ L\) and \( \varepsilon:L\circ R\to \mathrm{id}_{\mathcal{C}}\) be the unit and counit, then for every \(c\in \mathrm{Ob}( \mathcal{C}),d\in \mathrm{Ob}( \mathcal{D})\),
\[ \varepsilon_{Ld}\circ L(\eta_d)= \mathrm{id}_{Ld},\quad R( \varepsilon_c)\circ\eta_{Rc}= \mathrm{id}_{Rc}.\]

*proof.* By definition of \(\eta\), there are morphisms \(\eta_d:d\to (R\circ L)d\) and \(L(\eta_d):Ld\to(L\circ R\circ L)d=(L\circ R)Ld\).

By definition of \( \varepsilon\), there are morphisms \( \varepsilon_{Ld}:(L\circ R)Ld\to Ld\). Composing \( \varepsilon_{Ld}\) and \(L(\eta_d)\), then we have a morphism \(Ld\to Ld\). The other equation is similar. \(\Box\)

*Equivalence proof.* (2 \(\Rightarrow\) 1) Given \(\varphi_{c,d}\) for every \(c,d\), the simplest way to construct that has ths same "signature" as \(\eta:I_\mathcal{D}\to R\circ L\) is to pass identity morphism \( \mathrm{id}_{Ld}\) to \(\varphi_{Ld,d}(d,Ld)\), i.e.
\[\eta=\{\varphi_{Ld,d}(d,Ld)\ \mathrm{id}_{Ld}\in \mathcal{D}(d,R(Ld))|d\in \mathrm{Ob}( \mathcal{D})\},\]
and this is the unit we wanted.

By diagram (2), for every \(g:d\to d'\), the following diagram commutes:
\[
\begin{CD}
\mathcal{C}(Ld,Ld) @>(Lg)_*>> \mathcal{C}(Ld,Ld') @<(L^{\mathrm{op}}(g^\mathrm{op}))^*<< \mathcal{C}(Ld',Ld') \\
@V\varphi_{Ld,d} VV @VV\varphi_{Ld',d} V @VV\varphi_{Ld',d} V \\
\mathcal{D}(d,R(Ld)) @>>(R(Lg))_*> \mathcal{D}(d,R(Ld')) @<(g^\mathrm{op})^*<< \mathcal{D}(d',R(Ld'))
\end{CD}
\]

The objects in the diagram are sets and morphisms are functions, so we can apply the functions to specific elements in the sets. Applying the left square to \(\mathrm{id}_{Ld}\) and the right square to \(\mathrm{id}_{Ld'}\) yields (the subscripts in \( \varphi\) are omitted):
\[
\begin{aligned}
    & (\mathcal{D}(d,(R\circ L)g)\circ\varphi(d,Ld))\ \mathrm{id}_{Ld}=(\varphi(d,Ld')\circ\mathcal{C}(Ld,Lg))\ \mathrm{id}_{Ld} \\
    & \Rightarrow\mathcal{D}(d,(R\circ L)g)\ \eta\ d=\varphi(d,Ld')(\mathcal{C}(Ld,Lg)\ \mathrm{id}_{Ld}), \\
    & (\mathcal{D}(g^\mathrm{op},(R\circ L)d')\circ\varphi(d',Ld'))\ \mathrm{id}_{Ld'}=(\varphi(d,Ld')\circ\mathcal{C}(L^{\mathrm{op}}(g^\mathrm{op}),Ld'))\ \mathrm{id}_{Ld'} \\
    & \Rightarrow\mathcal{D}(g^\mathrm{op},(R\circ L)d')\ \eta\ d'=\varphi(d,Ld')(\mathcal{C}((Lg)^\mathrm{op},Ld')\ \mathrm{id}_{Ld'}).
\end{aligned}
\]

By definition of hom-functors,
\[\mathcal{C}(Ld,Lg)\ \mathrm{id}_{Ld}=Lg\circ\mathrm{id}_{Ld}=Lg=\mathrm{id}_{Ld'}\circ((Lg)^\mathrm{op})^\mathrm{op}=\mathcal{C}(L(g^\mathrm{op}),Ld')\ \mathrm{id}_{Ld'},\]
\[\mathcal{D}(d,(R\circ L)g)\ \eta\ d=((R\circ L) g)\circ(\eta\ d),\quad\mathcal{D}(g^\mathrm{op},(R\circ L)d')\ \eta\ d'=(\eta\ d')\circ g,\]

Therefore
\[((R\circ L) g)\circ(\eta\ d)=(\eta\ d')\circ g,\]
therefore \(\eta\) is a natural transformation, thus it is a unit.

Similarly, we can define
\[\varepsilon=\{(\varphi_{c,Rc})^{-1}(Rc,c)\ \mathrm{id}_{Rc}\in \mathcal{C}(L(Rc),c)|c\in\mathrm{Ob}( \mathcal{C})\}\]
and prove that it's a counit.

(1 \(\Rightarrow\) 2) Given \(\eta,\varepsilon\), For every \(c\in\mathcal{C},d\in\mathcal{D}\), we can construct two mappings \(\varphi_{c,d}:\mathcal{C}(Ld,c)\to\mathcal{D}(d,Rc)\) and \(\psi_{c,d}:\mathcal{D}(d,Rc)\to\mathcal{C}(Ld,c)\) where:
\[\varphi_{c,d}:f\mapsto Rf\circ\eta_d,\quad\psi_{c,d}:f\mapsto\varepsilon_c\circ Lf,\]
and claim that:
- (a) For every \(g:c\to c'\in \mathrm{Mor}( \mathcal{C}),h:d'\to d\in \mathrm{Mor}( \mathcal{D}^{ \mathrm{op}})\), diagram (2) commutes,
- (b) \(\psi_{c,d}\circ \varphi_{c,d}= \mathrm{id}_{\mathcal{C}(Ld,c)},\varphi_{c,d}\circ\psi_{c,d}=\mathrm{id}_{\mathcal{D}(d,Rc)}\), therefore \( \varphi_{c,d}\) is an isomorphism.

(a) Because for every morphism \(f\in\mathcal{C}(Ld,c)\),
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
    & =Rf\circ((R\circ L)h^{ \mathrm{op}}\circ\eta_d) & (\text{see diagram (A.1)}) \\
    & =R(f\circ L(h^{ \mathrm{op}}))\circ\eta_d & (\text{by functorality}) \\
    & =R(f\circ (L^{\mathrm{op}}h)^{ \mathrm{op}})\circ\eta_d & (\text{note that }h\in \mathrm{Mor}( \mathcal{C}^{ \mathrm{op}})) \\
    & =\varphi_{c,d}(f\circ(L^{ \mathrm{op}}h)^{ \mathrm{op}}) \\
    & =(\varphi_{c,d}\circ\mathcal{D}(L^{ \mathrm{op}}h,c))f,
\end{aligned}
\]
where the diagram (A.1) commutes by the naturality of \(\eta\):
\[
\begin{CD}
d @>h^{ \mathrm{op}}>> d' \\
@V\eta_d VV @VV\eta_{d'} V \\
(R\circ L)d @>>(R\circ L)h^{ \mathrm{op}}> (R\circ L)d'
\end{CD}
\tag{A.1}\]

Therefore the second diagram commutes.

(b) For every \(c\in\mathcal{C},d\in\mathcal{D},f\in \mathcal{C}(Ld,c)\),
\[
\begin{aligned}
    (\psi_{c,d}\circ \varphi_{c,d})f & =\varepsilon_c\circ L(Rf\circ\eta_d) \\
    & =(\varepsilon_c\circ L(Rf))\circ L(\eta_d) \\
    & =(f\circ\varepsilon_{Ld})\circ L(\eta_d) & (\text{see diagram (A.2)}) \\
    & =f\circ(\varepsilon_{Ld}\circ L(\eta_d)) \\
    & =f, & (\text{by Lemma 2})
\end{aligned}
\]
where the diagram (A.2) commutes by the naturality of \(\varepsilon\):
\[
\begin{CD}
(L\circ R\circ L)d @>>(L\circ R)f> (L\circ R)c \\
@V\varepsilon_{Ld} VV @VV\varepsilon_c V \\
Ld @>f>> c
\end{CD}
\tag{A.2}\]

For every \(c\in\mathcal{C},d\in\mathcal{D},f\in \mathcal{D}(d,Rc)\),
\[
\begin{aligned}
    (\varphi_{c,d}\circ \psi_{c,d})(f) & =R(\varepsilon_c\circ Lf')\circ\eta_d \\
    & =R(\varepsilon_c)\circ(R(Lf')\circ\eta_d) \\
    & =R(\varepsilon_c)\circ(\eta_{Rc}\circ f') & (\text{see diagram (A.3)}) \\
    & =(R(\varepsilon_c)\circ\eta_{Rc})\circ f'=f' & (\text{by Lemma 2})
\end{aligned}
\]
where the diagram (A.3) commutes by the naturality of \(\eta\):
\[
\begin{CD}
d @>f>> Rc \\
@V\eta_{d} VV @VV\eta_{Rc} V \\
(R\circ L)d @>>(R\circ L)f> (R\circ L\circ R)c
\end{CD}
\tag{A.3}\]

Therefore \( \varphi_{c,d}\) is isomorphism. \(\Box\)
