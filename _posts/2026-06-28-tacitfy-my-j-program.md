---
layout: post
title:  "Tacitfy My J Program"
---

I need to have a break from the HM type inference crusade, so today I'm doing something different: refactoring the program I wrote at [my very first blog post](/myblog/2026/03/14/wave-function-collapse-algorithm-in-j.html) and learn more about tacit programming J.

As a person from functional programming background, I'll use concepts in FP to explain things I learned.

Here's our patient:
{% highlight j %}
load 'files'
image =: 0 ". freadr 'image.txt'
max =: 1 + >./ , image
new_state =: 3 : '(y, max) $ 1'
edge_list =: 4 : ',/ |: > x; y|.x'
unit =: 4 : '(i.y) = x +/ . * (1{y), 1'
adj_mat =: 3 : '+./ (image edge_list y) (unit"1) 2 $ max'
entropy =: 3 : '+/ - y * 2 ^. y'
count =: 4 : '+/ y = , x'
prior =: image count"_ 0 i. max
posterior =: 3 : '(% +/) y * prior'
replace_zero =: 3 : 'y + _ * 0 =/ y'
entropy_mat =: 3 : 'replace_zero entropy"1 posterior"1 y'
min_mask =: 3 : 'y = <./ , y'
first =: 3 : '(i.$y) = (,y) i. 1'
collapse_mask =: 3 : 'first min_mask entropy_mat y'
roulette =: 3 : '(((? 2147483647) % 2147483647) < +/\ y) I. 1'
elem_mask =: 3 : '(i.max) ="_ 0 roulette"1 posterior"1 y'
collapse =: 3 : '(y * -. collapse_mask y) + (elem_mask y) * collapse_mask y'
unions =: 4 : '((-y) |. x) (+./ . *)"1 _ adj_mat y'
neighbors =: 4 2 $ 0 1 0 _1 1 0 _1 0
propagation =: 3 : '*./ y , y unions"_ 1 neighbors'
valid_or_reset =: 3 : 'y >: *./ , +./"1 y'
iter =: 3 : 'valid_or_reset propagation collapse y'
continue =: 3 : '-. *./ , 1 = +/"1 y'
loop =: iter ^: continue ^: _
get_image =: 3 : 'y (I."1) 1'
(": get_image loop new_state 10 10) fwrites 'output.txt'
{% endhighlight %}

## Currying

The verb `new_state` creates an array with dimension `(y, max)`:
{% highlight j %}
new_state =: 3 : '(y, max) $ 1'
{% endhighlight %}

It can be decomposed into a function that concatenates `y` and `max` and a function that create arrays of ones. Both of them should be a monad that is made by "partially applies a dyad to a noun". In functional languages, this is done automatically by currying the binary function. In J, we use [`&` (bond)](https://code.jsoftware.com/wiki/Vocabulary/ampm) conjunction [^note1]. `&` can be used to apply both left and right of a dyad: `(x&v) y` or `(v&y) x` can be used to represent `x v y`.

[^note1]: The name "conjunction" is neat in the sense that it does what the conjunction in natural language do: combine different words to form a new phrase. As an extra challenge to the reader, try to find natural language analogies of the J conjunctions introduced in this post.

Here are the "curried" verbs:
{% highlight j %}
ones =: $&1
append_max =: ,&max
{% endhighlight %}

We can use [`@` (atop)](https://code.jsoftware.com/wiki/Vocabulary/at) [^note2] conjunction to compose verbs here. Here's the tacit definition of `new_state`:
{% highlight j %}
new_state =: $&1 @ (,&max)
{% endhighlight %}

[^note2]: I suppose `@` is inspired by \(\circ\) (the math notation for function composition). `@@` is also the shortcut for \(\circ\) in the [LaTeX Workshop extension](https://github.com/James-Yu/LaTeX-Workshop/wiki/Intellisense#handy-mathematical-helpers).

Exercise for readers: tacitfy `get_image` using an `&`.

## Ranking Problem

We may be tempted to write our `entropy` function
{% highlight j %}
entropy =: 3 : '+/ - y * 2 ^. y'
{% endhighlight %}
as:
{% highlight j %}
w =: 3 : 'y * 2 ^. y' NB. We will handle this later
entropy =: +/ @ - @ w
{% endhighlight %}

However, this won't work:
{% highlight j %}
entropy 0.1 0.2 0.7 NB. returns 0.332193 0.464386 0.360201, WTF?
{% endhighlight %}

That's because `u @ v` is *not* the function composition of `u` and `v`. The *real* function composition is [`@:` (at)](https://code.jsoftware.com/wiki/Vocabulary/atco), in that `(u @: v) y` is `u v y`, and `(u @ v) y` is actually `(u @ v)"v y` [^note3].

[^note3]: This is probably a design flaw of J: people should understand `@:` before being exposed to `@`, but everyone is writing `@` because it's shorter. The [J primer](https://code.jsoftware.com/wiki/Help/Primer/094_Tacit_definition) is also misleading, saying that `(u @ v) y` is `u v y`.

In our entropy example, `w 0.1 0.2 0.7` is a list, and we run `-` and `+/` on every element of the list, so it becomes `0.332193 0.464386 0.360201`. Our entropy function should really be:
{% highlight j %}
entropy =: +/ @: - @ w NB. `- @ w` and `- @: w` are the same.
{% endhighlight %}

We can use `@` in `new_state` because `(,&max)` has rank infinity, so `@` and `@:` are the same.

Exercise for readers: tacitfy following verbs using `@` or `@:`:
1. `entropy_mat`
2. `collapse_mask`

## Hook

[Hook](https://code.jsoftware.com/wiki/Vocabulary/hook) conjunction lets you combine two verbs and use it as one verb.

Dyadic hooks are invisible in implicit J, in other words, the following two verbs are equivalent:
{% highlight j %}
count1 =: 4 : '+/ y  = ,  x' NB. evaluates `, x`, then evaluates `y = (,x)`
count2 =: 4 : '+/ y (= ,) x' NB. evaluates `y v x` where `v =: =,`
{% endhighlight %}

The problem of `count` is the parameter is reversed. We can use [`~` (reflex)](https://code.jsoftware.com/wiki/Vocabulary/tilde) to reverse its parameter:
{% highlight j %}
count =: +/ @ (=,)~
{% endhighlight %}

You can nest hooks if there are more than two verbs. Say you have the following train:
```
x v_1 v_2 ... v_n y NB. x and y are nouns, v_i are verbs
```

We first add the parenthesis omitted:
```
x (v_1 (v_2 ... (v_n y))...)
```

By stripping away two layers of parenthesis, we can create a hook:
```
x (v_1 v_2) (v_3 ... (v_n y)...)
```

`(v_1 v_2)` and `v_3` can be made into another hook:
```
x ((v_1 v_2) v_3) (v_4 ... (v_n y)...)
```

The combined hook continues to absorb the verbs and eventually there is only one verb left:
```
x ((((v_1 v_2) v_3) ...) v_n) y
```

Monadic hooks are specialized version of dyadic hooks where `x` are equal to `y`. For example,
{% highlight j %}
min_mask =: 3 : 'y = <./ , y'
{% endhighlight %}

Can be refactored to
{% highlight j %}
min_mask =: (= <./),
{% endhighlight %}

Note that `(= <./)` acts as a dyadic hook and its `x` and `y` are the original `y` and `,y` respectively.

Exercise for readers: tacitfy `valid_or_reset` using hooks.

## Fork

[Fork](https://code.jsoftware.com/wiki/Vocabulary/fork) combines a tree of verbs into one verb.

Let's use fork to finish the `entropy` verb:
{% highlight j %}
w =: 3 : 'y * 2 ^. y' NB. tacify me
entropy =: +/ @: - @ w
{% endhighlight %}

`x (f g h) y` is equivalent to `(x f y) g (x h y)`, or
```
     g
    / \
   /   \
  f     h
 / \   / \
x   y x   y
```

We can write an AST of `w`:
```
  *
 / \
y   ^.
   / \
  2   y
```

To use the fork conjunction, we must have a full binary tree like this one:
```
     *
    / \
   /   \
  v     ^.
 / \   / \
2   y 2   y
```

Where `2 v y` is `y`, which is the behavior of the [`]` (right)](https://code.jsoftware.com/wiki/Vocabulary/squarert) verb.

Therefore
{% highlight j %}
w =: 2&(] * ^.)
entropy =: +/ @: - @ (2&(] * ^.))
{% endhighlight %}

We can also use monadic fork to solve it. `(f g h) y` is equivalent to `(f y) g (h y)`, or
```
     g
    / \
   /   \
  f     h
   \     \
    y     y
```

To use the fork conjunction, we rewrite the AST using `&` and [`]` (same)](https://code.jsoftware.com/wiki/Vocabulary/squarert):
```
     *
    / \
   /   \
  ]     (2&^.)
   \     \
    y     y
```

Hence
{% highlight j %}
w =: ] * (2&^.)
{% endhighlight %}

Exercise for readers:
1. Tacitfy `edge_list` using fork.
2. Prove that you can always use a fork whenever you need a hook.

## Modifier Train

We can generalize the idea of fork by replacing verbs with other kinds of words. For example, a NVV fork `N v w` where `N` is a noun `v,w` are verbs has the following AST:
```
  v
 / \
N   w
   / \
  x   y
```

Let's take a look at `first`:
{% highlight j %}
first =: 3 : '(i.$y) = (,y) i. 1'
{% endhighlight %}

To begin with, we decomposed it with a fork:
{% highlight j %}
first =: (i. @: $) = w
w =: 3 : '(,y) i. 1'
{% endhighlight %}

`w` has the following AST:
```
  i.
 / \
,   1
 \
  y
```

To use the NVV fork, we swap the parameters of `i.` using `~`:
```
  i.~
 / \
1   ,
     \
      y
```

So we have
{% highlight j %}
w = 1 i.~ ,
first =: (i. @: $) = 1 i.~ ,
{% endhighlight %}

Such generalized fork are called modifier trains. You can find more examples of modifier trains [here](https://code.jsoftware.com/wiki/Vocabulary/ModifierTrains).

Exercise for readers: Tacitfy `posterior` with a NVV fork.

## Nested Forks

You can nest forks to form a large AST. The AST looks like a Huffman tree of verbs (see the vocabulary page of fork for the AST).

The verb
{% highlight j %}
replace_zero =: 3 : 'y + _ * 0 =/ y'
{% endhighlight %}
has AST
```
  +
 / \
y   *
   / \
  _   =/
     / \
    0   y
```

We can fit the AST into three forks:
```
   +
  / \
 /   \
]     *
 \   / \
  y _   =/
       / \
      0   ]
           \
            y
```

So this becomes
{% highlight j %}
replace_zero =: ] + _ * 0 =/ ]
{% endhighlight %}

Exercise for readers: To tacitfy `unit`, we split it using a fork:
{% highlight j %}
unit =: inc = idx_unit
inc =: 4 : 'i.y' NB. We will handle this later
idx_unit =: 4 : 'x +/ . * (1{y), 1'
{% endhighlight %}

Tacitfy `idx_unit` using nested forks.

## Cap the Fork

Let's finish the `inc` verb above:
{% highlight j %}
inc =: 4 : 'i.y'
{% endhighlight %}

Suppose we want to use a dyadic fork:
```
   i.
    \
     ]
    / \
   x   y
```
and we realize that the AST doesn't have the left branch. A way to resolve this is to use the dummy verb [`[:` (cap)](https://code.jsoftware.com/wiki/Vocabulary/squarelfco). `x ([: u v) y` is equivalent to `u (x v y)`, or
```
   u
    \
     v
    / \
   x   y
```
which is exactly what we want. So
{% highlight j %}
inc =: [: i. ]
{% endhighlight %}

You can achieve the same result using `@:` since `x (u @: v) y` is also `u (x v y)`.

## Tacit Translator

J has a tacit translator that translates implicit definition to tacit definition. You can use it by defining a verb as `13` instead of `3` or `4`:
{% highlight j %}
   count =: 13 : '+/ y = , x'
   count
[: +/ ] = [: , [
{% endhighlight %}

The translator almost always generates forks, so it may not be useful in finding the real structure of the program.

## Outro

- In general, to tacitfy a sentence, you write down its AST, do some pattern matching with the conjunctions and dummy verbs like `]`.
- Tacit programming isn't *that* hard (if you just want to use it daily). I managed to learn and write this post that covers most of the basics in two days, without an LLM [^note4].

[^note4]: I doubt that LLMs can help me learn any array language, given that the training data is so sparse. Building an RAG on array language docs sounds like a good idea to promote the languages.

## Appendix: Solutions to the Exercises

{% highlight j %}
get_image =: (I."1)&1
entropy_mat =: replace_zero @: entropy"1 @: posterior"1
collapse_mask =: first @: min_mask @: entropy_mat
valid_or_reset =: ((>: *./) ,) +./"1
edge_list =: ,/ @: |: > @: [ ; |.~
posterior =: (% +/) @: (prior * ])
idx_unit =: [ +/ . * 1 ,~ 1 {  ]
{% endhighlight %}

****
