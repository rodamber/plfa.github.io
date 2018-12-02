---
src       : src/plfa/Induction.lagda
title     : "Induction: Proof by Induction"
layout    : page
prev      : /Naturals/
permalink : /Induction/
next      : /Relations/
---

<pre class="Agda">{% raw %}<a id="155" class="Keyword">module</a> <a id="162" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}" class="Module">plfa.Induction</a> <a id="177" class="Keyword">where</a>{% endraw %}</pre>

> Induction makes you feel guilty for getting something out of nothing
> ... but it is one of the greatest ideas of civilization.
> -- Herbert Wilf

Now that we've defined the naturals and operations upon them, our next
step is to learn how to prove properties that they satisfy.  As hinted
by their name, properties of _inductive datatypes_ are proved by
_induction_.


## Imports

We require equality as in the previous chapter, plus the naturals
and some operations upon them.  We also import a couple of new operations,
`cong`, `sym`, and `_≡⟨_⟩_`, which are explained below.
<pre class="Agda">{% raw %}<a id="788" class="Keyword">import</a> <a id="795" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="833" class="Symbol">as</a> <a id="836" class="Module">Eq</a>
<a id="839" class="Keyword">open</a> <a id="844" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html" class="Module">Eq</a> <a id="847" class="Keyword">using</a> <a id="853" class="Symbol">(</a><a id="854" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">_≡_</a><a id="857" class="Symbol">;</a> <a id="859" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a><a id="863" class="Symbol">;</a> <a id="865" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#1056" class="Function">cong</a><a id="869" class="Symbol">;</a> <a id="871" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#838" class="Function">sym</a><a id="874" class="Symbol">)</a>
<a id="876" class="Keyword">open</a> <a id="881" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3840" class="Module">Eq.≡-Reasoning</a> <a id="896" class="Keyword">using</a> <a id="902" class="Symbol">(</a><a id="903" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3941" class="Function Operator">begin_</a><a id="909" class="Symbol">;</a> <a id="911" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3999" class="Function Operator">_≡⟨⟩_</a><a id="916" class="Symbol">;</a> <a id="918" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4058" class="Function Operator">_≡⟨_⟩_</a><a id="924" class="Symbol">;</a> <a id="926" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4239" class="Function Operator">_∎</a><a id="928" class="Symbol">)</a>
<a id="930" class="Keyword">open</a> <a id="935" class="Keyword">import</a> <a id="942" href="https://agda.github.io/agda-stdlib/Data.Nat.html" class="Module">Data.Nat</a> <a id="951" class="Keyword">using</a> <a id="957" class="Symbol">(</a><a id="958" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="959" class="Symbol">;</a> <a id="961" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a><a id="965" class="Symbol">;</a> <a id="967" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a><a id="970" class="Symbol">;</a> <a id="972" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">_+_</a><a id="975" class="Symbol">;</a> <a id="977" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#433" class="Primitive Operator">_*_</a><a id="980" class="Symbol">;</a> <a id="982" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#320" class="Primitive Operator">_∸_</a><a id="985" class="Symbol">)</a>{% endraw %}</pre>


## Properties of operators

Operators pop up all the time, and mathematicians have agreed
on names for some of the most common properties.

* _Identity_.   Operator `+` has left identity `0` if `0 + n ≡ n`, and
  right identity `0` if `n + 0 ≡ n`, for all `n`. A value that is both
  a left and right identity is just called an identity. Identity is also
  sometimes called _unit_.

* _Associativity_.   Operator `+` is associative if the location
  of parentheses does not matter: `(m + n) + p ≡ m + (n + p)`,
  for all `m`, `n`, and `p`.

* _Commutatitivity_.   Operator `+` is commutative if order of
  arguments does not matter: `m + n ≡ n + m`, for all `m` and `n`.

* _Distributivity_.   Operator `*` distributes over operator `+` from the
  left if `(m + n) * p ≡ (m * p) + (n * p)`, for all `m`, `n`, and `p`,
  and from the right if `m * (p + q) ≡ (m * p) + (m * q)`, for all `m`,
  `p`, and `q`.

Addition has identity `0` and multiplication has identity `1`;
addition and multiplication are both associative and commutative;
and multiplication distributes over addition.

If you ever bump into an operator at a party, you now know how
to make small talk, by asking whether it has a unit and is
associative or commutative.  If you bump into two operators, you
might ask them if one distributes over the other.

Less frivolously, if you ever bump into an operator while reading a
technical paper, this gives you a way to orient yourself, by checking
whether or not it has an identity, is associative or commutative, or
distributes over another operator.  A careful author will often call
out these properties---or their lack---for instance by pointing out
that a newly introduced operator is associative but not commutative.

#### Exercise `operators` {#operators}

Give another example of a pair of operators that have an identity
and are associative, commutative, and distribute over one another.

Give an example of an operator that has an identity and is
associative but is not commutative.


## Associativity

One property of addition is that it is _associative_, that is, that the
location of the parentheses does not matter:

    (m + n) + p ≡ m + (n + p)

Here `m`, `n`, and `p` are variables that range over all natural numbers.

We can test the proposition by choosing specific numbers for the three
variables.
<pre class="Agda">{% raw %}<a id="3343" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#3343" class="Function">_</a> <a id="3345" class="Symbol">:</a> <a id="3347" class="Symbol">(</a><a id="3348" class="Number">3</a> <a id="3350" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="3352" class="Number">4</a><a id="3353" class="Symbol">)</a> <a id="3355" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="3357" class="Number">5</a> <a id="3359" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="3361" class="Number">3</a> <a id="3363" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="3365" class="Symbol">(</a><a id="3366" class="Number">4</a> <a id="3368" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="3370" class="Number">5</a><a id="3371" class="Symbol">)</a>
<a id="3373" class="Symbol">_</a> <a id="3375" class="Symbol">=</a>
  <a id="3379" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3941" class="Function Operator">begin</a>
    <a id="3389" class="Symbol">(</a><a id="3390" class="Number">3</a> <a id="3392" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="3394" class="Number">4</a><a id="3395" class="Symbol">)</a> <a id="3397" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="3399" class="Number">5</a>
  <a id="3403" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3999" class="Function Operator">≡⟨⟩</a>
    <a id="3411" class="Number">7</a> <a id="3413" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="3415" class="Number">5</a>
  <a id="3419" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3999" class="Function Operator">≡⟨⟩</a>
    <a id="3427" class="Number">12</a>
  <a id="3432" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3999" class="Function Operator">≡⟨⟩</a>
    <a id="3440" class="Number">3</a> <a id="3442" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="3444" class="Number">9</a>
  <a id="3448" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3999" class="Function Operator">≡⟨⟩</a>
    <a id="3456" class="Number">3</a> <a id="3458" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="3460" class="Symbol">(</a><a id="3461" class="Number">4</a> <a id="3463" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="3465" class="Number">5</a><a id="3466" class="Symbol">)</a>
  <a id="3470" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4239" class="Function Operator">∎</a>{% endraw %}</pre>
Here we have displayed the computation as a chain of equations,
one term to a line.  It is often easiest to read such chains from the top down
until one reaches the simplest term (in this case, `12`), and
then from the bottom up until one reaches the same term.

The test reveals that associativity is perhaps not as obvious as first
it appears.  Why should `7 + 5` be the same as `3 + 9`?  We might want
to gather more evidence, testing the proposition by choosing other
numbers.  But---since there are an infinite number of
naturals---testing can never be complete.  Is there any way we can be
sure that associativity holds for _all_ the natural numbers?

The answer is yes! We can prove a property holds for all naturals using
_proof by induction_.


## Proof by induction

Recall the definition of natural numbers consists of a _base case_
which tells us that `zero` is a natural, and an _inductive case_
which tells us that if `m` is a natural then `suc m` is also a natural.

Proof by induction follows the structure of this definition.  To prove
a property of natural numbers by induction, we need prove two cases.
First is the _base case_, where we show the property holds for `zero`.
Second is the _inductive case_, where we assume the property holds for
an arbitrary natural `m` (we call this the _inductive hypothesis_), and
then show that the property must also hold for `suc m`.

If we write `P m` for a property of `m`, then what we need to
demonstrate are the following two inference rules:

    ------
    P zero

    P m
    ---------
    P (suc m)

Let's unpack these rules.  The first rule is the base case, and
requires we show that property `P` holds for `zero`.  The second rule
is the inductive case, and requires we show that if we assume the
inductive hypothesis---namely that `P` holds for `m`---then it follows that
`P` also holds for `suc m`.

Why does this work?  Again, it can be explained by a creation story.
To start with, we know no properties.

    -- in the beginning, no properties are known

Now, we apply the two rules to all the properties we know about.  The
base case tells us that `P zero` holds, so we add it to the set of
known properties.  The inductive case tells us that if `P m` holds (on
the day before today) then `P (suc m)` also holds (today).  We didn't
know about any properties before today, so the inductive case doesn't
apply.

    -- on the first day, one property is known
    P zero

Then we repeat the process, so on the next day we know about all the
properties from the day before, plus any properties added by the rules.
The base case tells us that `P zero` holds, but we already
knew that. But now the inductive case tells us that since `P zero`
held yesterday, then `P (suc zero)` holds today.

    -- on the second day, two properties are known
    P zero
    P (suc zero)

And we repeat the process again. Now the inductive case
tells us that since `P zero` and `P (suc zero)` both hold, then
`P (suc zero)` and `P (suc (suc zero))` also hold. We already knew about
the first of these, but the second is new.

    -- on the third day, three properties are known
    P zero
    P (suc zero)
    P (suc (suc zero))

You've got the hang of it by now.

    -- on the fourth day, four properties are known
    P zero
    P (suc zero)
    P (suc (suc zero))
    P (suc (suc (suc zero)))

The process continues.  On the _n_'th day there will be _n_ distinct
properties that hold.  The property of every natural number will appear
on some given day.  In particular, the property `P n` first appears on
day _n+1_.


## Our first proof: associativity

To prove associativity, we take `P m` to be the property

    (m + n) + p ≡ m + (n + p)

Here `n` and `p` are arbitrary natural numbers, so if we can show the
equation holds for all `m` it will also hold for all `n` and `p`.
The appropriate instances of the inference rules are:

    -------------------------------
    (zero + n) + p ≡ zero + (n + p)

    (m + n) + p ≡ m + (n + p)
    ---------------------------------
    (suc m + n) + p ≡ suc m + (n + p)

If we can demonstrate both of these, then associativity of addition
follows by induction.

Here is the proposition's statement and proof.
<pre class="Agda">{% raw %}<a id="+-assoc"></a><a id="7705" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7705" class="Function">+-assoc</a> <a id="7713" class="Symbol">:</a> <a id="7715" class="Symbol">∀</a> <a id="7717" class="Symbol">(</a><a id="7718" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7718" class="Bound">m</a> <a id="7720" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7720" class="Bound">n</a> <a id="7722" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7722" class="Bound">p</a> <a id="7724" class="Symbol">:</a> <a id="7726" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="7727" class="Symbol">)</a> <a id="7729" class="Symbol">→</a> <a id="7731" class="Symbol">(</a><a id="7732" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7718" class="Bound">m</a> <a id="7734" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="7736" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7720" class="Bound">n</a><a id="7737" class="Symbol">)</a> <a id="7739" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="7741" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7722" class="Bound">p</a> <a id="7743" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="7745" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7718" class="Bound">m</a> <a id="7747" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="7749" class="Symbol">(</a><a id="7750" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7720" class="Bound">n</a> <a id="7752" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="7754" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7722" class="Bound">p</a><a id="7755" class="Symbol">)</a>
<a id="7757" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7705" class="Function">+-assoc</a> <a id="7765" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="7770" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7770" class="Bound">n</a> <a id="7772" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7772" class="Bound">p</a> <a id="7774" class="Symbol">=</a>
  <a id="7778" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3941" class="Function Operator">begin</a>
    <a id="7788" class="Symbol">(</a><a id="7789" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="7794" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="7796" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7770" class="Bound">n</a><a id="7797" class="Symbol">)</a> <a id="7799" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="7801" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7772" class="Bound">p</a>
  <a id="7805" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3999" class="Function Operator">≡⟨⟩</a>
    <a id="7813" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7770" class="Bound">n</a> <a id="7815" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="7817" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7772" class="Bound">p</a>
  <a id="7821" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3999" class="Function Operator">≡⟨⟩</a>
   <a id="7828" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="7833" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="7835" class="Symbol">(</a><a id="7836" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7770" class="Bound">n</a> <a id="7838" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="7840" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7772" class="Bound">p</a><a id="7841" class="Symbol">)</a>
  <a id="7845" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4239" class="Function Operator">∎</a>
<a id="7847" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7705" class="Function">+-assoc</a> <a id="7855" class="Symbol">(</a><a id="7856" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="7860" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7860" class="Bound">m</a><a id="7861" class="Symbol">)</a> <a id="7863" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7863" class="Bound">n</a> <a id="7865" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7865" class="Bound">p</a> <a id="7867" class="Symbol">=</a>
  <a id="7871" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3941" class="Function Operator">begin</a>
    <a id="7881" class="Symbol">(</a><a id="7882" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="7886" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7860" class="Bound">m</a> <a id="7888" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="7890" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7863" class="Bound">n</a><a id="7891" class="Symbol">)</a> <a id="7893" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="7895" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7865" class="Bound">p</a>
  <a id="7899" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3999" class="Function Operator">≡⟨⟩</a>
    <a id="7907" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="7911" class="Symbol">(</a><a id="7912" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7860" class="Bound">m</a> <a id="7914" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="7916" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7863" class="Bound">n</a><a id="7917" class="Symbol">)</a> <a id="7919" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="7921" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7865" class="Bound">p</a>
  <a id="7925" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3999" class="Function Operator">≡⟨⟩</a>
    <a id="7933" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="7937" class="Symbol">((</a><a id="7939" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7860" class="Bound">m</a> <a id="7941" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="7943" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7863" class="Bound">n</a><a id="7944" class="Symbol">)</a> <a id="7946" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="7948" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7865" class="Bound">p</a><a id="7949" class="Symbol">)</a>
  <a id="7953" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4058" class="Function Operator">≡⟨</a> <a id="7956" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#1056" class="Function">cong</a> <a id="7961" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="7965" class="Symbol">(</a><a id="7966" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7705" class="Function">+-assoc</a> <a id="7974" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7860" class="Bound">m</a> <a id="7976" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7863" class="Bound">n</a> <a id="7978" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7865" class="Bound">p</a><a id="7979" class="Symbol">)</a> <a id="7981" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4058" class="Function Operator">⟩</a>
    <a id="7987" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="7991" class="Symbol">(</a><a id="7992" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7860" class="Bound">m</a> <a id="7994" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="7996" class="Symbol">(</a><a id="7997" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7863" class="Bound">n</a> <a id="7999" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="8001" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7865" class="Bound">p</a><a id="8002" class="Symbol">))</a>
  <a id="8007" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3999" class="Function Operator">≡⟨⟩</a>
    <a id="8015" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="8019" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7860" class="Bound">m</a> <a id="8021" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="8023" class="Symbol">(</a><a id="8024" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7863" class="Bound">n</a> <a id="8026" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="8028" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7865" class="Bound">p</a><a id="8029" class="Symbol">)</a>
  <a id="8033" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4239" class="Function Operator">∎</a>{% endraw %}</pre>
We have named the proof `+-assoc`.  In Agda, identifiers can consist of
any sequence of characters not including spaces or the characters `@.(){};_`.

Let's unpack this code.  The signature states that we are
defining the identifier `+-assoc` which provides evidence for the
proposition:

    ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)

The upside down A is pronounced "for all", and the proposition
asserts that for all natural numbers `m`, `n`, and `p` that
the equation `(m + n) + p ≡ m + (n + p)` holds.  Evidence for the proposition
is a function that accepts three natural numbers, binds them to `m`, `n`, and `p`,
and returns evidence for the corresponding instance of the equation.

For the base case, we must show:

    (zero + n) + p ≡ zero + (n + p)

Simplifying both sides with the base case of addition yields the equation:

    n + p ≡ n + p

This holds trivially.  Reading the chain of equations in the base case of the proof,
the top and bottom of the chain match the two sides of the equation to
be shown, and reading down from the top and up from the bottom takes us to
`n + p` in the middle.  No justification other than simplification is required.

For the inductive case, we must show:

    (suc m + n) + p ≡ suc m + (n + p)

Simplifying both sides with the inductive case of addition yields the equation:

    suc ((m + n) + p) ≡ suc (m + (n + p))

This in turn follows by prefacing `suc` to both sides of the induction
hypothesis:

    (m + n) + p ≡ m + (n + p)

Reading the chain of equations in the inductive case of the proof, the
top and bottom of the chain match the two sides of the equation to be
shown, and reading down from the top and up from the bottom takes us
to the simplified equation above. The remaining equation, does not follow
from simplification alone, so we use an additional operator for chain
reasoning, `_≡⟨_⟩_`, where a justification for the equation appears
within angle brackets.  The justification given is:

    ⟨ cong suc (+-assoc m n p) ⟩

Here, the recursive invocation `+-assoc m n p` has as its type the
induction hypothesis, and `cong suc` prefaces `suc` to each side to
yield the needed equation.

A relation is said to be a _congruence_ for a given function if it is
preserved by applying that function.  If `e` is evidence that `x ≡ y`,
then `cong f e` is evidence that `f x ≡ f y`, for any function `f`.

Here the inductive hypothesis is not assumed, but instead proved by a
recursive invocation of the function we are defining, `+-assoc m n p`.
As with addition, this is well founded because associativity of
larger numbers is proved in terms of associativity of smaller numbers.
In this case, `assoc (suc m) n p` is proved using `assoc m n p`.
The correspondence between proof by induction and definition by
recursion is one of the most appealing aspects of Agda.


## Our second proof: commutativity

Another important property of addition is that it is _commutative_, that is,
that the order of the operands does not matter:

    m + n ≡ n + m

The proof requires that we first demonstrate two lemmas.

### The first lemma

The base case of the definition of addition states that zero
is a left-identity:

    zero + n ≡ n

Our first lemma states that zero is also a right-identity:

    m + zero ≡ m

Here is the lemma's statement and proof.
<pre class="Agda">{% raw %}<a id="+-identityʳ"></a><a id="11368" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11368" class="Function">+-identityʳ</a> <a id="11380" class="Symbol">:</a> <a id="11382" class="Symbol">∀</a> <a id="11384" class="Symbol">(</a><a id="11385" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11385" class="Bound">m</a> <a id="11387" class="Symbol">:</a> <a id="11389" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="11390" class="Symbol">)</a> <a id="11392" class="Symbol">→</a> <a id="11394" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11385" class="Bound">m</a> <a id="11396" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="11398" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="11403" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="11405" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11385" class="Bound">m</a>
<a id="11407" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11368" class="Function">+-identityʳ</a> <a id="11419" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="11424" class="Symbol">=</a>
  <a id="11428" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3941" class="Function Operator">begin</a>
    <a id="11438" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="11443" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="11445" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>
  <a id="11452" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3999" class="Function Operator">≡⟨⟩</a>
    <a id="11460" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>
  <a id="11467" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4239" class="Function Operator">∎</a>
<a id="11469" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11368" class="Function">+-identityʳ</a> <a id="11481" class="Symbol">(</a><a id="11482" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="11486" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11486" class="Bound">m</a><a id="11487" class="Symbol">)</a> <a id="11489" class="Symbol">=</a>
  <a id="11493" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3941" class="Function Operator">begin</a>
    <a id="11503" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="11507" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11486" class="Bound">m</a> <a id="11509" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="11511" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>
  <a id="11518" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3999" class="Function Operator">≡⟨⟩</a>
    <a id="11526" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="11530" class="Symbol">(</a><a id="11531" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11486" class="Bound">m</a> <a id="11533" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="11535" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a><a id="11539" class="Symbol">)</a>
  <a id="11543" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4058" class="Function Operator">≡⟨</a> <a id="11546" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#1056" class="Function">cong</a> <a id="11551" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="11555" class="Symbol">(</a><a id="11556" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11368" class="Function">+-identityʳ</a> <a id="11568" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11486" class="Bound">m</a><a id="11569" class="Symbol">)</a> <a id="11571" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4058" class="Function Operator">⟩</a>
    <a id="11577" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="11581" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11486" class="Bound">m</a>
  <a id="11585" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4239" class="Function Operator">∎</a>{% endraw %}</pre>
The signature states that we are defining the identifier `+-identityʳ` which
provides evidence for the proposition:

    ∀ (m : ℕ) → m + zero ≡ m

Evidence for the proposition is a function that accepts a natural
number, binds it to `m`, and returns evidence for the corresponding
instance of the equation.  The proof is by induction on `m`.

For the base case, we must show:

    zero + zero ≡ zero

Simplifying with the base case of addition, this is straightforward.

For the inductive case, we must show:

    (suc m) + zero = suc m

Simplifying both sides with the inductive case of addition yields the equation:

    suc (m + zero) = suc m

This in turn follows by prefacing `suc` to both sides of the induction
hypothesis:

    m + zero ≡ m

Reading the chain of equations down from the top and up from the bottom
takes us to the simplified equation above.  The remaining
equation has the justification:

    ⟨ cong suc (+-identityʳ m) ⟩

Here, the recursive invocation `+-identityʳ m` has as its type the
induction hypothesis, and `cong suc` prefaces `suc` to each side to
yield the needed equation.  This completes the first lemma.

### The second lemma

The inductive case of the definition of addition pushes `suc` on the
first argument to the outside:

    suc m + n ≡ suc (m + n)

Our second lemma does the same for `suc` on the second argument:

    m + suc n ≡ suc (m + n)

Here is the lemma's statement and proof.
<pre class="Agda">{% raw %}<a id="+-suc"></a><a id="13041" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#13041" class="Function">+-suc</a> <a id="13047" class="Symbol">:</a> <a id="13049" class="Symbol">∀</a> <a id="13051" class="Symbol">(</a><a id="13052" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#13052" class="Bound">m</a> <a id="13054" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#13054" class="Bound">n</a> <a id="13056" class="Symbol">:</a> <a id="13058" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="13059" class="Symbol">)</a> <a id="13061" class="Symbol">→</a> <a id="13063" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#13052" class="Bound">m</a> <a id="13065" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="13067" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="13071" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#13054" class="Bound">n</a> <a id="13073" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="13075" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="13079" class="Symbol">(</a><a id="13080" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#13052" class="Bound">m</a> <a id="13082" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="13084" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#13054" class="Bound">n</a><a id="13085" class="Symbol">)</a>
<a id="13087" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#13041" class="Function">+-suc</a> <a id="13093" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="13098" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#13098" class="Bound">n</a> <a id="13100" class="Symbol">=</a>
  <a id="13104" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3941" class="Function Operator">begin</a>
    <a id="13114" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="13119" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="13121" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="13125" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#13098" class="Bound">n</a>
  <a id="13129" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3999" class="Function Operator">≡⟨⟩</a>
    <a id="13137" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="13141" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#13098" class="Bound">n</a>
  <a id="13145" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3999" class="Function Operator">≡⟨⟩</a>
    <a id="13153" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="13157" class="Symbol">(</a><a id="13158" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="13163" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="13165" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#13098" class="Bound">n</a><a id="13166" class="Symbol">)</a>
  <a id="13170" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4239" class="Function Operator">∎</a>
<a id="13172" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#13041" class="Function">+-suc</a> <a id="13178" class="Symbol">(</a><a id="13179" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="13183" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#13183" class="Bound">m</a><a id="13184" class="Symbol">)</a> <a id="13186" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#13186" class="Bound">n</a> <a id="13188" class="Symbol">=</a>
  <a id="13192" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3941" class="Function Operator">begin</a>
    <a id="13202" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="13206" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#13183" class="Bound">m</a> <a id="13208" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="13210" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="13214" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#13186" class="Bound">n</a>
  <a id="13218" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3999" class="Function Operator">≡⟨⟩</a>
    <a id="13226" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="13230" class="Symbol">(</a><a id="13231" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#13183" class="Bound">m</a> <a id="13233" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="13235" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="13239" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#13186" class="Bound">n</a><a id="13240" class="Symbol">)</a>
  <a id="13244" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4058" class="Function Operator">≡⟨</a> <a id="13247" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#1056" class="Function">cong</a> <a id="13252" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="13256" class="Symbol">(</a><a id="13257" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#13041" class="Function">+-suc</a> <a id="13263" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#13183" class="Bound">m</a> <a id="13265" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#13186" class="Bound">n</a><a id="13266" class="Symbol">)</a> <a id="13268" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4058" class="Function Operator">⟩</a>
    <a id="13274" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="13278" class="Symbol">(</a><a id="13279" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="13283" class="Symbol">(</a><a id="13284" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#13183" class="Bound">m</a> <a id="13286" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="13288" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#13186" class="Bound">n</a><a id="13289" class="Symbol">))</a>
  <a id="13294" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3999" class="Function Operator">≡⟨⟩</a>
    <a id="13302" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="13306" class="Symbol">(</a><a id="13307" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="13311" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#13183" class="Bound">m</a> <a id="13313" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="13315" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#13186" class="Bound">n</a><a id="13316" class="Symbol">)</a>
  <a id="13320" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4239" class="Function Operator">∎</a>{% endraw %}</pre>
The signature states that we are defining the identifier `+-suc` which provides
evidence for the proposition:

    ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)

Evidence for the proposition is a function that accepts two natural numbers,
binds them to `m` and `n`, and returns evidence for the corresponding instance
of the equation.  The proof is by induction on `m`.

For the base case, we must show:

    zero + suc n ≡ suc (zero + n)

Simplifying with the base case of addition, this is straightforward.

For the inductive case, we must show:

    suc m + suc n ≡ suc (suc m + n)

Simplifying both sides with the inductive case of addition yields the equation:

    suc (m + suc n) ≡ suc (suc (m + n))

This in turn follows by prefacing `suc` to both sides of the induction
hypothesis:

    m + suc n ≡ suc (m + n)

Reading the chain of equations down from the top and up from the bottom
takes us to the simplified equation in the middle.  The remaining
equation has the justification:

    ⟨ cong suc (+-suc m n) ⟩

Here, the recursive invocation `+-suc m n` has as its type the
induction hypothesis, and `cong suc` prefaces `suc` to each side to
yield the needed equation.  This completes the second lemma.

### The proposition

Finally, here is our proposition's statement and proof.
<pre class="Agda">{% raw %}<a id="+-comm"></a><a id="14630" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#14630" class="Function">+-comm</a> <a id="14637" class="Symbol">:</a> <a id="14639" class="Symbol">∀</a> <a id="14641" class="Symbol">(</a><a id="14642" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#14642" class="Bound">m</a> <a id="14644" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#14644" class="Bound">n</a> <a id="14646" class="Symbol">:</a> <a id="14648" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="14649" class="Symbol">)</a> <a id="14651" class="Symbol">→</a> <a id="14653" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#14642" class="Bound">m</a> <a id="14655" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="14657" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#14644" class="Bound">n</a> <a id="14659" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="14661" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#14644" class="Bound">n</a> <a id="14663" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="14665" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#14642" class="Bound">m</a>
<a id="14667" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#14630" class="Function">+-comm</a> <a id="14674" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#14674" class="Bound">m</a> <a id="14676" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="14681" class="Symbol">=</a>
  <a id="14685" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3941" class="Function Operator">begin</a>
    <a id="14695" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#14674" class="Bound">m</a> <a id="14697" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="14699" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>
  <a id="14706" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4058" class="Function Operator">≡⟨</a> <a id="14709" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11368" class="Function">+-identityʳ</a> <a id="14721" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#14674" class="Bound">m</a> <a id="14723" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4058" class="Function Operator">⟩</a>
    <a id="14729" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#14674" class="Bound">m</a>
  <a id="14733" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3999" class="Function Operator">≡⟨⟩</a>
    <a id="14741" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="14746" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="14748" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#14674" class="Bound">m</a>
  <a id="14752" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4239" class="Function Operator">∎</a>
<a id="14754" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#14630" class="Function">+-comm</a> <a id="14761" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#14761" class="Bound">m</a> <a id="14763" class="Symbol">(</a><a id="14764" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="14768" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#14768" class="Bound">n</a><a id="14769" class="Symbol">)</a> <a id="14771" class="Symbol">=</a>
  <a id="14775" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3941" class="Function Operator">begin</a>
    <a id="14785" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#14761" class="Bound">m</a> <a id="14787" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="14789" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="14793" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#14768" class="Bound">n</a>
  <a id="14797" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4058" class="Function Operator">≡⟨</a> <a id="14800" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#13041" class="Function">+-suc</a> <a id="14806" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#14761" class="Bound">m</a> <a id="14808" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#14768" class="Bound">n</a> <a id="14810" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4058" class="Function Operator">⟩</a>
    <a id="14816" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="14820" class="Symbol">(</a><a id="14821" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#14761" class="Bound">m</a> <a id="14823" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="14825" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#14768" class="Bound">n</a><a id="14826" class="Symbol">)</a>
  <a id="14830" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4058" class="Function Operator">≡⟨</a> <a id="14833" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#1056" class="Function">cong</a> <a id="14838" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="14842" class="Symbol">(</a><a id="14843" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#14630" class="Function">+-comm</a> <a id="14850" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#14761" class="Bound">m</a> <a id="14852" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#14768" class="Bound">n</a><a id="14853" class="Symbol">)</a> <a id="14855" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4058" class="Function Operator">⟩</a>
    <a id="14861" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="14865" class="Symbol">(</a><a id="14866" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#14768" class="Bound">n</a> <a id="14868" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="14870" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#14761" class="Bound">m</a><a id="14871" class="Symbol">)</a>
  <a id="14875" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3999" class="Function Operator">≡⟨⟩</a>
    <a id="14883" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="14887" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#14768" class="Bound">n</a> <a id="14889" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="14891" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#14761" class="Bound">m</a>
  <a id="14895" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4239" class="Function Operator">∎</a>{% endraw %}</pre>
The first line states that we are defining the identifier
`+-comm` which provides evidence for the proposition:

    ∀ (m n : ℕ) → m + n ≡ n + m

Evidence for the proposition is a function that accepts two
natural numbers, binds them to `m` and `n`, and returns evidence for the
corresponding instance of the equation.  The proof is by
induction on `n`.  (Not on `m` this time!)

For the base case, we must show:

    m + zero ≡ zero + m

Simplifying both sides with the base case of addition yields the equation:

    m + zero ≡ m

The the remaining equation has the justification `⟨ +-identityʳ m ⟩`,
which invokes the first lemma.

For the inductive case, we must show:

    m + suc n ≡ suc n + m

Simplifying both sides with the inductive case of addition yields the equation:

    m + suc n ≡ suc (n + m)

We show this in two steps.  First, we have:

    m + suc n ≡ suc (m + n)

which is justified by the second lemma, `⟨ +-suc m n ⟩`.  Then we
have

    suc (m + n) ≡ suc (n + m)

which is justified by congruence and the induction hypothesis,
`⟨ cong suc (+-comm m n) ⟩`.  This completes the proof.

Agda requires that identifiers are defined before they are used,
so we must present the lemmas before the main proposition, as we
have done above.  In practice, one will often attempt to prove
the main proposition first, and the equations required to do so
will suggest what lemmas to prove.


## Our first corollary: rearranging {#sections}

We can apply associativity to rearrange parentheses however we like.
Here is an example.
<pre class="Agda">{% raw %}<a id="+-rearrange"></a><a id="16461" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16461" class="Function">+-rearrange</a> <a id="16473" class="Symbol">:</a> <a id="16475" class="Symbol">∀</a> <a id="16477" class="Symbol">(</a><a id="16478" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16478" class="Bound">m</a> <a id="16480" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16480" class="Bound">n</a> <a id="16482" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16482" class="Bound">p</a> <a id="16484" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16484" class="Bound">q</a> <a id="16486" class="Symbol">:</a> <a id="16488" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="16489" class="Symbol">)</a> <a id="16491" class="Symbol">→</a> <a id="16493" class="Symbol">(</a><a id="16494" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16478" class="Bound">m</a> <a id="16496" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="16498" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16480" class="Bound">n</a><a id="16499" class="Symbol">)</a> <a id="16501" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="16503" class="Symbol">(</a><a id="16504" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16482" class="Bound">p</a> <a id="16506" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="16508" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16484" class="Bound">q</a><a id="16509" class="Symbol">)</a> <a id="16511" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="16513" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16478" class="Bound">m</a> <a id="16515" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="16517" class="Symbol">(</a><a id="16518" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16480" class="Bound">n</a> <a id="16520" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="16522" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16482" class="Bound">p</a><a id="16523" class="Symbol">)</a> <a id="16525" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="16527" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16484" class="Bound">q</a>
<a id="16529" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16461" class="Function">+-rearrange</a> <a id="16541" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16541" class="Bound">m</a> <a id="16543" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16543" class="Bound">n</a> <a id="16545" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16545" class="Bound">p</a> <a id="16547" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16547" class="Bound">q</a> <a id="16549" class="Symbol">=</a>
  <a id="16553" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3941" class="Function Operator">begin</a>
    <a id="16563" class="Symbol">(</a><a id="16564" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16541" class="Bound">m</a> <a id="16566" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="16568" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16543" class="Bound">n</a><a id="16569" class="Symbol">)</a> <a id="16571" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="16573" class="Symbol">(</a><a id="16574" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16545" class="Bound">p</a> <a id="16576" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="16578" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16547" class="Bound">q</a><a id="16579" class="Symbol">)</a>
  <a id="16583" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4058" class="Function Operator">≡⟨</a> <a id="16586" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7705" class="Function">+-assoc</a> <a id="16594" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16541" class="Bound">m</a> <a id="16596" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16543" class="Bound">n</a> <a id="16598" class="Symbol">(</a><a id="16599" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16545" class="Bound">p</a> <a id="16601" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="16603" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16547" class="Bound">q</a><a id="16604" class="Symbol">)</a> <a id="16606" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4058" class="Function Operator">⟩</a>
    <a id="16612" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16541" class="Bound">m</a> <a id="16614" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="16616" class="Symbol">(</a><a id="16617" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16543" class="Bound">n</a> <a id="16619" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="16621" class="Symbol">(</a><a id="16622" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16545" class="Bound">p</a> <a id="16624" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="16626" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16547" class="Bound">q</a><a id="16627" class="Symbol">))</a>
  <a id="16632" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4058" class="Function Operator">≡⟨</a> <a id="16635" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#1056" class="Function">cong</a> <a id="16640" class="Symbol">(</a><a id="16641" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16541" class="Bound">m</a> <a id="16643" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+_</a><a id="16645" class="Symbol">)</a> <a id="16647" class="Symbol">(</a><a id="16648" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#838" class="Function">sym</a> <a id="16652" class="Symbol">(</a><a id="16653" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7705" class="Function">+-assoc</a> <a id="16661" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16543" class="Bound">n</a> <a id="16663" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16545" class="Bound">p</a> <a id="16665" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16547" class="Bound">q</a><a id="16666" class="Symbol">))</a> <a id="16669" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4058" class="Function Operator">⟩</a>
    <a id="16675" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16541" class="Bound">m</a> <a id="16677" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="16679" class="Symbol">((</a><a id="16681" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16543" class="Bound">n</a> <a id="16683" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="16685" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16545" class="Bound">p</a><a id="16686" class="Symbol">)</a> <a id="16688" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="16690" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16547" class="Bound">q</a><a id="16691" class="Symbol">)</a>
  <a id="16695" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4058" class="Function Operator">≡⟨</a> <a id="16698" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#838" class="Function">sym</a> <a id="16702" class="Symbol">(</a><a id="16703" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#7705" class="Function">+-assoc</a> <a id="16711" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16541" class="Bound">m</a> <a id="16713" class="Symbol">(</a><a id="16714" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16543" class="Bound">n</a> <a id="16716" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="16718" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16545" class="Bound">p</a><a id="16719" class="Symbol">)</a> <a id="16721" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16547" class="Bound">q</a><a id="16722" class="Symbol">)</a> <a id="16724" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4058" class="Function Operator">⟩</a>
    <a id="16730" class="Symbol">(</a><a id="16731" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16541" class="Bound">m</a> <a id="16733" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="16735" class="Symbol">(</a><a id="16736" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16543" class="Bound">n</a> <a id="16738" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="16740" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16545" class="Bound">p</a><a id="16741" class="Symbol">))</a> <a id="16744" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="16746" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16547" class="Bound">q</a>
  <a id="16750" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4239" class="Function Operator">∎</a>{% endraw %}</pre>
No induction is required, we simply apply associativity twice.
A few points are worthy of note.

First, addition associates to the left, so `m + (n + p) + q`
stands for `(m + (n + p)) + q`.

Second, we use `sym` to interchange the sides of an equation.
Proposition `+-assoc n p q` shifts parentheses from right to left:

    (n + p) + q ≡ n + (p + q)

To shift them the other way, we use `sym (+-assoc m n p)`:

    n + (p + q) ≡ (n + p) + q

In general, if `e` provides evidence for `x ≡ y` then `sym e` provides
evidence for `y ≡ x`.

Third, Agda supports a variant of the _section_ notation introduced by
Richard Bird.  We write `(x +_)` for the function that applied to `y`
returns `x + y`.  Thus, applying the congruence `cong (m +_)` takes
the above equation into

    m + (n + (p + q)) ≡ m + ((n + p) + q)

Similarly, we write `(_+ x)` for the function that applied to `y`
returns `y + x`; the same works for any infix operator.



## Creation, one last time

Returning to the proof of associativity, it may be helpful to view the inductive
proof (or, equivalently, the recursive definition) as a creation story.  This
time we are concerned with judgements asserting associativity.

     -- in the beginning, we know nothing about associativity

Now, we apply the rules to all the judgements we know about.  The base
case tells us that `(zero + n) + p ≡ zero + (n + p)` for every natural
`n` and `p`.  The inductive case tells us that if `(m + n) + p ≡ m +
(n + p)` (on the day before today) then
`(suc m + n) + p ≡ suc m + (n + p)` (today).
We didn't know any judgments about associativity before today, so that
rule doesn't give us any new judgments.

    -- on the first day, we know about associativity of 0
    (0 + 0) + 0 ≡ 0 + (0 + 0)   ...   (0 + 4) + 5 ≡ 0 + (4 + 5)   ...

Then we repeat the process, so on the next day we know about all the
judgements from the day before, plus any judgements added by the rules.
The base case tells us nothing new, but now the inductive case adds
more judgements.

    -- on the second day, we know about associativity of 0 and 1
    (0 + 0) + 0 ≡ 0 + (0 + 0)   ...   (0 + 4) + 5 ≡ 0 + (4 + 5)   ...
    (1 + 0) + 0 ≡ 1 + (0 + 0)   ...   (1 + 4) + 5 ≡ 1 + (4 + 5)   ...

And we repeat the process again.

    -- on the third day, we know about associativity of 0, 1, and 2
    (0 + 0) + 0 ≡ 0 + (0 + 0)   ...   (0 + 4) + 5 ≡ 0 + (4 + 5)   ...
    (1 + 0) + 0 ≡ 1 + (0 + 0)   ...   (1 + 4) + 5 ≡ 1 + (4 + 5)   ...
    (2 + 0) + 0 ≡ 2 + (0 + 0)   ...   (2 + 4) + 5 ≡ 2 + (4 + 5)   ...

You've got the hang of it by now.

    -- on the fourth day, we know about associativity of 0, 1, 2, and 3
    (0 + 0) + 0 ≡ 0 + (0 + 0)   ...   (0 + 4) + 5 ≡ 0 + (4 + 5)   ...
    (1 + 0) + 0 ≡ 1 + (0 + 0)   ...   (1 + 4) + 5 ≡ 1 + (4 + 5)   ...
    (2 + 0) + 0 ≡ 2 + (0 + 0)   ...   (2 + 4) + 5 ≡ 2 + (4 + 5)   ...
    (3 + 0) + 0 ≡ 3 + (0 + 0)   ...   (3 + 4) + 5 ≡ 3 + (4 + 5)   ...

The process continues.  On the _m_'th day we will know all the
judgements where the first number is less than _m_.

There is also a completely finite approach to generating the same equations,
which is left as an exercise for the reader.

#### Exercise `finite-+-assoc` (stretch) {#finite-plus-assoc}

Write out what is known about associativity of addition on each of the first four
days using a finite story of creation, as
[earlier]({{ site.baseurl }}{% link out/plfa/Naturals.md%}#finite-creation)

## Associativity with rewrite

There is more than one way to skin a cat.  Here is a second proof of
associativity of addition in Agda, using `rewrite` rather than chains of
equations.
<pre class="Agda">{% raw %}<a id="+-assoc′"></a><a id="20352" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#20352" class="Function">+-assoc′</a> <a id="20361" class="Symbol">:</a> <a id="20363" class="Symbol">∀</a> <a id="20365" class="Symbol">(</a><a id="20366" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#20366" class="Bound">m</a> <a id="20368" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#20368" class="Bound">n</a> <a id="20370" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#20370" class="Bound">p</a> <a id="20372" class="Symbol">:</a> <a id="20374" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="20375" class="Symbol">)</a> <a id="20377" class="Symbol">→</a> <a id="20379" class="Symbol">(</a><a id="20380" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#20366" class="Bound">m</a> <a id="20382" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="20384" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#20368" class="Bound">n</a><a id="20385" class="Symbol">)</a> <a id="20387" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="20389" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#20370" class="Bound">p</a> <a id="20391" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="20393" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#20366" class="Bound">m</a> <a id="20395" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="20397" class="Symbol">(</a><a id="20398" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#20368" class="Bound">n</a> <a id="20400" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="20402" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#20370" class="Bound">p</a><a id="20403" class="Symbol">)</a>
<a id="20405" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#20352" class="Function">+-assoc′</a> <a id="20414" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>    <a id="20422" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#20422" class="Bound">n</a> <a id="20424" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#20424" class="Bound">p</a>                          <a id="20451" class="Symbol">=</a>  <a id="20454" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a>
<a id="20459" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#20352" class="Function">+-assoc′</a> <a id="20468" class="Symbol">(</a><a id="20469" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="20473" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#20473" class="Bound">m</a><a id="20474" class="Symbol">)</a> <a id="20476" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#20476" class="Bound">n</a> <a id="20478" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#20478" class="Bound">p</a>  <a id="20481" class="Keyword">rewrite</a> <a id="20489" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#20352" class="Function">+-assoc′</a> <a id="20498" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#20473" class="Bound">m</a> <a id="20500" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#20476" class="Bound">n</a> <a id="20502" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#20478" class="Bound">p</a>  <a id="20505" class="Symbol">=</a>  <a id="20508" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a>{% endraw %}</pre>

For the base case, we must show:

    (zero + n) + p ≡ zero + (n + p)

Simplifying both sides with the base case of addition yields the equation:

    n + p ≡ n + p

This holds trivially. The proof that a term is equal to itself is written `refl`.

For the inductive case, we must show:

    (suc m + n) + p ≡ suc m + (n + p)

Simplifying both sides with the inductive case of addition yields the equation:

    suc ((m + n) + p) ≡ suc (m + (n + p))

After rewriting with the inductive hypothesis these two terms are equal, and the
proof is again given by `refl`.  Rewriting by a given equation is indicated by
the keyword `rewrite` followed by a proof of that equation.  Rewriting avoids
not only chains of equations but also the need to invoke `cong`.


## Commutativity with rewrite

Here is a second proof of commutativity of addition, using `rewrite` rather than
chains of equations.
<pre class="Agda">{% raw %}<a id="+-identity′"></a><a id="21427" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#21427" class="Function">+-identity′</a> <a id="21439" class="Symbol">:</a> <a id="21441" class="Symbol">∀</a> <a id="21443" class="Symbol">(</a><a id="21444" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#21444" class="Bound">n</a> <a id="21446" class="Symbol">:</a> <a id="21448" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="21449" class="Symbol">)</a> <a id="21451" class="Symbol">→</a> <a id="21453" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#21444" class="Bound">n</a> <a id="21455" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="21457" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="21462" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="21464" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#21444" class="Bound">n</a>
<a id="21466" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#21427" class="Function">+-identity′</a> <a id="21478" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="21483" class="Symbol">=</a> <a id="21485" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a>
<a id="21490" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#21427" class="Function">+-identity′</a> <a id="21502" class="Symbol">(</a><a id="21503" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="21507" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#21507" class="Bound">n</a><a id="21508" class="Symbol">)</a> <a id="21510" class="Keyword">rewrite</a> <a id="21518" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#21427" class="Function">+-identity′</a> <a id="21530" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#21507" class="Bound">n</a> <a id="21532" class="Symbol">=</a> <a id="21534" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a>

<a id="+-suc′"></a><a id="21540" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#21540" class="Function">+-suc′</a> <a id="21547" class="Symbol">:</a> <a id="21549" class="Symbol">∀</a> <a id="21551" class="Symbol">(</a><a id="21552" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#21552" class="Bound">m</a> <a id="21554" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#21554" class="Bound">n</a> <a id="21556" class="Symbol">:</a> <a id="21558" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="21559" class="Symbol">)</a> <a id="21561" class="Symbol">→</a> <a id="21563" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#21552" class="Bound">m</a> <a id="21565" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="21567" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="21571" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#21554" class="Bound">n</a> <a id="21573" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="21575" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="21579" class="Symbol">(</a><a id="21580" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#21552" class="Bound">m</a> <a id="21582" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="21584" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#21554" class="Bound">n</a><a id="21585" class="Symbol">)</a>
<a id="21587" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#21540" class="Function">+-suc′</a> <a id="21594" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="21599" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#21599" class="Bound">n</a> <a id="21601" class="Symbol">=</a> <a id="21603" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a>
<a id="21608" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#21540" class="Function">+-suc′</a> <a id="21615" class="Symbol">(</a><a id="21616" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="21620" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#21620" class="Bound">m</a><a id="21621" class="Symbol">)</a> <a id="21623" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#21623" class="Bound">n</a> <a id="21625" class="Keyword">rewrite</a> <a id="21633" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#21540" class="Function">+-suc′</a> <a id="21640" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#21620" class="Bound">m</a> <a id="21642" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#21623" class="Bound">n</a> <a id="21644" class="Symbol">=</a> <a id="21646" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a>

<a id="+-comm′"></a><a id="21652" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#21652" class="Function">+-comm′</a> <a id="21660" class="Symbol">:</a> <a id="21662" class="Symbol">∀</a> <a id="21664" class="Symbol">(</a><a id="21665" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#21665" class="Bound">m</a> <a id="21667" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#21667" class="Bound">n</a> <a id="21669" class="Symbol">:</a> <a id="21671" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="21672" class="Symbol">)</a> <a id="21674" class="Symbol">→</a> <a id="21676" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#21665" class="Bound">m</a> <a id="21678" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="21680" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#21667" class="Bound">n</a> <a id="21682" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="21684" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#21667" class="Bound">n</a> <a id="21686" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="21688" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#21665" class="Bound">m</a>
<a id="21690" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#21652" class="Function">+-comm′</a> <a id="21698" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#21698" class="Bound">m</a> <a id="21700" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="21705" class="Keyword">rewrite</a> <a id="21713" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#21427" class="Function">+-identity′</a> <a id="21725" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#21698" class="Bound">m</a> <a id="21727" class="Symbol">=</a> <a id="21729" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a>
<a id="21734" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#21652" class="Function">+-comm′</a> <a id="21742" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#21742" class="Bound">m</a> <a id="21744" class="Symbol">(</a><a id="21745" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="21749" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#21749" class="Bound">n</a><a id="21750" class="Symbol">)</a> <a id="21752" class="Keyword">rewrite</a> <a id="21760" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#21540" class="Function">+-suc′</a> <a id="21767" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#21742" class="Bound">m</a> <a id="21769" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#21749" class="Bound">n</a> <a id="21771" class="Symbol">|</a> <a id="21773" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#21652" class="Function">+-comm′</a> <a id="21781" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#21742" class="Bound">m</a> <a id="21783" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#21749" class="Bound">n</a> <a id="21785" class="Symbol">=</a> <a id="21787" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a>{% endraw %}</pre>
In the final line, rewriting with two equations is
indicated by separating the two proofs of the relevant equations by a
vertical bar; the rewrite on the left is performed before that on the
right.


## Building proofs interactively

It is instructive to see how to build the alternative proof of
associativity using the interactive features of Agda in Emacs.
Begin by typing

    +-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
    +-assoc′ m n p = ?

The question mark indicates that you would like Agda to help with
filling in that part of the code.  If you type `C-c C-l` (control-c
followed by control-l), the question mark will be replaced.

    +-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
    +-assoc′ m n p = { }0

The empty braces are called a _hole_, and 0 is a number used for
referring to the hole.  The hole may display highlighted in green.
Emacs will also create a new window at the bottom of the screen
displaying the text

    ?0 : ((m + n) + p) ≡ (m + (n + p))

This indicates that hole 0 is to be filled in with a proof of
the stated judgement.

We wish to prove the proposition by induction on `m`.  Move
the cursor into the hole and type `C-c C-c`.  You will be given
the prompt:

    pattern variables to case (empty for split on result):

Typing `m` will cause a split on that variable, resulting
in an update to the code.

    +-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
    +-assoc′ zero n p = { }0
    +-assoc′ (suc m) n p = { }1

There are now two holes, and the window at the bottom tells you what
each is required to prove:

    ?0 : ((zero + n) + p) ≡ (zero + (n + p))
    ?1 : ((suc m + n) + p) ≡ (suc m + (n + p))

Going into hole 0 and typing `C-c C-,` will display the text:

    Goal: (n + p) ≡ (n + p)
    ————————————————————————————————————————————————————————————
    p : ℕ
    n : ℕ

This indicates that after simplification the goal for hole 0 is as
stated, and that variables `p` and `n` of the stated types are
available to use in the proof.  The proof of the given goal is
trivial, and going into the goal and typing `C-c C-r` will fill it in.
Typing `C-c C-l` renumbers the remaining hole to 0:

    +-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
    +-assoc′ zero n p = refl
    +-assoc′ (suc m) n p = { }0

Going into the new hole 0 and typing `C-c C-,` will display the text:

    Goal: suc ((m + n) + p) ≡ suc (m + (n + p))
    ————————————————————————————————————————————————————————————
    p : ℕ
    n : ℕ
    m : ℕ

Again, this gives the simplified goal and the available variables.
In this case, we need to rewrite by the induction
hypothesis, so let's edit the text accordingly:

    +-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
    +-assoc′ zero n p = refl
    +-assoc′ (suc m) n p rewrite +-assoc′ m n p = { }0

Going into the remaining hole and typing `C-c C-,` will display the text:

    Goal: suc (m + (n + p)) ≡ suc (m + (n + p))
    ————————————————————————————————————————————————————————————
    p : ℕ
    n : ℕ
    m : ℕ

The proof of the given goal is trivial, and going into the goal and
typing `C-c C-r` will fill it in, completing the proof:

    +-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
    +-assoc′ zero n p = refl
    +-assoc′ (suc m) n p rewrite +-assoc′ m n p = refl


#### Exercise `+-swap` (recommended) {#plus-swap} 

Show

    m + (n + p) ≡ n + (m + p)

for all naturals `m`, `n`, and `p`. No induction is needed,
just apply the previous results which show addition
is associative and commutative.

#### Exercise `*-distrib-+` (recommended) {#times-distrib-plus}

Show multiplication distributes over addition, that is,

    (m + n) * p ≡ m * p + n * p

for all naturals `m`, `n`, and `p`.

#### Exercise `*-assoc` (recommended) {#times-assoc}

Show multiplication is associative, that is,

    (m * n) * p ≡ m * (n * p)

for all naturals `m`, `n`, and `p`.

#### Exercise `*-comm` {#times-comm}

Show multiplication is commutative, that is,

    m * n ≡ n * m

for all naturals `m` and `n`.  As with commutativity of addition,
you will need to formulate and prove suitable lemmas.

#### Exercise `0∸n≡0` {#zero-monus}

Show

    zero ∸ n ≡ zero

for all naturals `n`. Did your proof require induction?

#### Exercise `∸-+-assoc` {#monus-plus-assoc}

Show that monus associates with addition, that is,

    m ∸ n ∸ p ≡ m ∸ (n + p)

for all naturals `m`, `n`, and `p`.

#### Exercise `Bin-laws` (stretch) {#Bin-laws}

Recall that 
Exercise [Bin]({{ site.baseurl }}{% link out/plfa/Naturals.md%}#Bin)
defines a datatype of bitstrings representing natural numbers
<pre class="Agda">{% raw %}<a id="26370" class="Keyword">data</a> <a id="Bin"></a><a id="26375" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#26375" class="Datatype">Bin</a> <a id="26379" class="Symbol">:</a> <a id="26381" class="PrimitiveType">Set</a> <a id="26385" class="Keyword">where</a>
  <a id="Bin.nil"></a><a id="26393" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#26393" class="InductiveConstructor">nil</a> <a id="26397" class="Symbol">:</a> <a id="26399" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#26375" class="Datatype">Bin</a>
  <a id="Bin.x0_"></a><a id="26405" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#26405" class="InductiveConstructor Operator">x0_</a> <a id="26409" class="Symbol">:</a> <a id="26411" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#26375" class="Datatype">Bin</a> <a id="26415" class="Symbol">→</a> <a id="26417" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#26375" class="Datatype">Bin</a>
  <a id="Bin.x1_"></a><a id="26423" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#26423" class="InductiveConstructor Operator">x1_</a> <a id="26427" class="Symbol">:</a> <a id="26429" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#26375" class="Datatype">Bin</a> <a id="26433" class="Symbol">→</a> <a id="26435" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#26375" class="Datatype">Bin</a>{% endraw %}</pre>
and asks you to define functions

    inc   : Bin → Bin
    to    : ℕ → Bin
    from  : Bin → ℕ

Consider the following laws, where `n` ranges over naturals and `x`
over bitstrings.

    from (inc x) ≡ suc (from x)
    to (from x) ≡ x
    from (to n) ≡ n

For each law: if it holds, prove; if not, give a counterexample.


## Standard library

Definitions similar to those in this chapter can be found in the standard library.
<pre class="Agda">{% raw %}<a id="26890" class="Keyword">import</a> <a id="26897" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html" class="Module">Data.Nat.Properties</a> <a id="26917" class="Keyword">using</a> <a id="26923" class="Symbol">(</a><a id="26924" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#7678" class="Function">+-assoc</a><a id="26931" class="Symbol">;</a> <a id="26933" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#7834" class="Function">+-identityʳ</a><a id="26944" class="Symbol">;</a> <a id="26946" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#7575" class="Function">+-suc</a><a id="26951" class="Symbol">;</a> <a id="26953" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#8011" class="Function">+-comm</a><a id="26959" class="Symbol">)</a>{% endraw %}</pre>

## Unicode

This chapter uses the following unicode.

    ∀  U+2200  FOR ALL (\forall, \all)
    ʳ  U+02B3  MODIFIER LETTER SMALL R (\^r)
    ′  U+2032  PRIME (\')
    ″  U+2033  DOUBLE PRIME (\')
    ‴  U+2034  TRIPLE PRIME (\')
    ⁗  U+2057  QUADRUPLE PRIME (\')

Similar to `\r`, the command `\^r` gives access to a variety of
superscript rightward arrows, and also a superscript letter `r`.
The command `\'` gives access to a range of primes (`′ ″ ‴ ⁗`).
