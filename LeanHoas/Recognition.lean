import LeanHoas.Setup

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "You Have Built This Before" =>
%%%
number := false
tag := "built-this-before"
%%%

Sooner or later, a large enough application grows a language, whether
anyone planned one or not. It is called business rules, formulas, filters,
policies, templates, or workflows. It starts with plain expressions:

```
price * quantity
```

Then someone needs a local value:

```
let discount = customer.discount in price * (1 - discount)
```

or a condition checked for each item:

```
orders.filter(order => order.total > limit)
```

Now one part of the expression introduces a name, `discount` or `order`,
and another part uses it. That is variable binding. If you have built such a
system, you have implemented it, perhaps without calling it that, and you
have met its questions. Which `order` does this `order` refer to when rules
are nested? What happens when one rule is plugged into another and both use
the name `x`? When are two rules the same rule with different names? These
questions have precise answers, worked out long ago, and a precise
vocabulary; this book uses both.{margin}[Embedding Python or JavaScript
avoids writing binding yourself, but gives up what made a small language
attractive: rules that can be inspected, stored, checked, and transformed.]

The examples so far were deliberately mundane. Now we throw away prices,
orders, and workflows, and keep only the mechanism that causes the trouble:
names, and the constructs that introduce them. What remains is the
λ-calculus, with three constructs and nothing else:

 * `var x` refers to a name introduced somewhere else.
 * `lam x b` introduces `x` and lets the body `b` refer to it: a function
   with parameter `x`, traditionally written `λx. b`, in Lean `fun x => b`.
 * `app f a` applies a function to an argument.

The arrow in `order => order.total > limit` is a `lam`, and
`let x = e in b` is `app (lam x b) e`. The λ-calculus does not solve anyone's
business problem. It isolates the part of it we want to study, the way a
laboratory organism keeps the mechanism of interest and little else.
