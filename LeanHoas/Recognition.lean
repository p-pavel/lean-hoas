import LeanHoas.Setup

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "You Have Built This Before" =>
%%%
number := false
tag := "built-this-before"
%%%

Take the rules language inside a billing, pricing, or workflow system. This
section retells its usual history, because the history is the problem this
book is about.

# Expressions Are Easy

It starts with plain expressions:

```
price * quantity
```

Every programmer knows what to do. Parse the text into a tree, an _abstract
syntax tree_:

```
Mul(Field("price"), Field("quantity"))
```

Then write an evaluator: a recursive function over the tree, one case per
kind of node. Printing, validation, and simple optimizations are recursive
functions of the same shape. It works, and it feels clean. Every subtree
needs only one thing from outside, the record being evaluated, and it is the
same record for every subtree. You can lift a subtree out, cache it, or move
it elsewhere, and it still means the same.

# The Edge

Then someone needs a local value:{margin}[Spreadsheet `LET`, SQL `WITH`, or
an assignment followed by `return` all have this shape.]

```
let discount = customer.discount in price * (1 - discount)
```

or a condition checked for each item:

```
orders.filter(order => order.total > limit)
```

It looks like one more kind of node. It is not. Before, context came from
outside and was the same everywhere. Now the tree creates context partway
down: one part of the expression introduces a name, `discount` or `order`,
and another part uses it. What `order` means depends on where in the tree
you stand, so a subtree can no longer be moved, copied, or compared without
knowing which binders are above it.

This is the edge where expressions stop being formulas and start being
programs. Crossing it is not a matter of more careful programming; the
problem itself changes. The trap is that this transition often happens
without anyone deciding to design a language. This book cares about one
consequence of crossing that line: once the little language has binders,
representing variables becomes surprisingly subtle. The problem has a name,
_variable binding_, and a construct that introduces a name, such as `let` or
`order =>`, is a _binder_.

# Now What?

Typically the evaluator grows an environment, a map from names to values,
extended on the way into each binder. Then the reports start:

 * A rule that works alone breaks when nested, because an inner `order`
   hides the outer one it needed. Or a callback runs later and sees whatever
   `order` the shared environment holds by then, not the one in force where
   it was written. Both are questions of _scope_: which binder does a use of
   a name belong to?{margin}[Resolving a name where the code was written is
   _lexical scope_; resolving it where the code runs is _dynamic scope_.
   Nearly every modern language chose lexical scope.]
 * Someone inlines one rule into another. The inlined rule refers to an
   outer `x`, but it lands inside a rule that defines its own `x`, and
   silently starts meaning that one. Inlining is _substitution_, and this
   failure is called _capture_; the first chapter reproduces it in a few
   lines.
 * Caching, deduplication, and change detection treat two rules as
   different although they differ only in the names of their local
   variables: `o => o.total` versus `order => order.total`. Deciding when
   two rules are the same up to such renaming is called _α-equivalence_.

These are not signs of sloppy work. They are the known symptoms of this
problem, and each has a name and a standard treatment.

# The Usual Ways Out

Teams usually take one of a few routes. Some forbid nesting, reserve magic
names like `$it` or `$1`, keep a global "current order" that is set and
reset around each call, or paste rule text into other rule text and parse it
again: fixes that hold until the next requirement. Some give every local
variable a globally unique id, which holds until a rule is copied. Others
replace each name by a position: how many binders up its definition sits.
Renaming problems disappear, and off-by-one errors take their place; that
route has a name too, _de Bruijn indices_, and it is the second chapter.

And many give up and embed a general-purpose language such as Python,
JavaScript, or Lua. Binding is then correct, because the host language does
it. But the rules become opaque code: they can be run, but no longer
inspected, compared, or transformed.

The last route has the right instinct. Letting the host language do the
binding is the idea of this book. What it gives up is rules that remain
data, and the book wins much of that back: keep the tree for everything
except binders, and use a host-language function only where a name is
introduced. That is _higher-order abstract syntax_. The book first tries it
naively, and then makes it work inside Lean's logic.

# The Core

Now throw away prices, orders, and workflows, and keep only the mechanism
that causes the trouble: names, where they are introduced, and where they
are used. That core is the λ-calculus (lambda calculus), and it has three
constructs:

 * `var x` is a use of the name `x`.
 * `lam x b` introduces `x` and lets the body `b` refer to it: a function
   with parameter `x`, traditionally written `λx. b`, in Lean `fun x => b`.
 * `app f a` applies a function to an argument.

In these terms, the λ-calculus part of `order => order.total > limit` is
`lam order b`, where the body `b` is `order.total > limit`. Each `order`
inside `b` is a `var order`, and handing that function to `filter` is an
`app`. Likewise, `let x = e in b` behaves like `app (lam x b) e`: make a
one-parameter function with body `b`, and call it on `e`.

The λ-calculus does not solve anyone's business problem. It isolates the
part of it we want to study, the way a laboratory organism keeps the
mechanism of interest and little else. The next chapter builds it in Lean,
names first, and shows where it breaks.
