#import "@local/ebnf:0.1.0": *
#import "/includes.typ": *

== Introduction <section-imp-introduction>
The Imp language was devised to work as a simple example of an imperative
language; albeit having a handful of syntactic constructs, it clearly is a
Turing complete language.

=== Syntax <subsection-imp-introduction-syntax>
The syntax of the Imp language can be described in a handful of EBNF rules,
as shown in @imp-syntax-rules.

// @TODO - ebnf package
#figure(
  ebnf(((nt: "aexp", rule: alt(([$n$], [id], [$a_1 + a_2$]))), (
    nt: "bexp",
    rule: alt(([$b$], [$a_1 < a_2$], [$not b$], [$b_1 and b_2$])),
  ), (nt: "command", rule: alt((
    [skip],
    [id $<-$ *aexp*],
    [$c_1 ; c_2$],
    [if *bexp* then $c_1$ else $c_2$],
    [while *bexp* do c],
  ))),)),
  caption: "Syntax rules for the Imp language",
  supplement: "Table",
)<imp-syntax-rules>

The syntactic elements of this language are three: _commands_, _arithmetic expressions_, _boolean expressions_ and _identifiers_. Given its simple nature,
it is easy to give an abstract representation for its concrete syntax: all of
them can be represented with simple datatypes enclosing all the information of
the syntactic rules, as shown in #coderef(<code-ident>), #coderef(<code-aexp>),
#coderef(<code-bexp>) and #coderef(<code-command>).

#grid(columns: (auto, auto, auto), gutter: 4pt,
mycode(ref: <code-ident>, "https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Imp/Syntax/Ident.agda#L15")[
//typstfmt::off
```hs
Ident : Set
Ident = String
```
//typstfmt::on
    ],

    mycode(ref: <code-aexp>, "https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Imp/Syntax/Core.agda#L13")[
//typstfmt::off
```hs
data AExp : Set where
 const : (n : ℤ)  
  -> AExp
 var   : (id : Ident) 
  -> AExp
 plus  : (a₁ a₂ : AExp) 
  -> AExp
```
//typstfmt::on
    ],
    mycode(ref: <code-bexp>, "https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Imp/Syntax/Core.agda#L18")[
//typstfmt::off
```hs
data BExp : Set where
 const : (b : Bool) 
  -> BExp
 le    : (a₁ a₂ : AExp) 
  -> BExp
 not   : (b : BExp) 
  -> BExp
 and   : (b₁ b₂ : BExp) 
  -> BExp
```
//typstfmt::on
    ])
#mycode(ref: <code-command>, "https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Imp/Syntax/Core.agda#L24")[
//typstfmt::off
```hs
data Command : Set where
 skip   : Command
 assign : (id : Ident) -> (a : AExp) -> Command
 seq    : (c₁ c₂ : Command) -> Command
 ifelse : (b : BExp) -> (c₁ c₂ : Command) -> Command
 while  : (b : BExp) -> (c : Command) -> Command
```
//typstfmt::on
    ]
=== Stores<subsection-imp-stores>
Identifiers in Imp have an important role. Identifiers can be initialized or
uninitialized (see @imp-semantics for a more detailed reasoning about their
role) and their value, if any, can change in time. We need a means to keep
track of identifiers and their value: this means is the `Store`, which we
define in this section, while also giving some useful definition. Stores are
defined as shown in #coderef(<code-store>), that is, partial maps made total
with the use of the `Maybe` monad.
#mycode(ref: <code-store>,
 "https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Imp/Syntax/Ident.agda#L18")[
 //typstfmt::off
```hs
Store : Set
Store = Ident -> Maybe ℤ 
```
//typstfmt::on
]
We now proceed to show some basic definition of _partial maps_. 
1. *in-store predicate* let $id$ be an identifier and $sigma$ be a store. To say that
  $id$ is in $sigma$ we write $ id in sigma$; in other terms, it's the same as
  $exists space v in ZZ, sigma id equiv "just" v$.
2. *empty store* we define the empty store as $emptyset$. For this special store,
  it is always $forall id, id in emptyset -> bot$ or $forall id, emptyset id equiv "nothing"$.
  #mycode(ref: <code-store-empty>, "https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Imp/Syntax/Ident.agda#L21")[
//typstfmt::off
```hs
empty : Store 
empty = λ _ -> nothing
```
//typstfmt::on
  ]
3. *adding an identifier* let $id : "Ident"$ be an identifier and $v : ZZ$ be a
  value. We denote the insertion of the pair $(id, v)$ in a store $sigma$ as $(id , v) arrow.r.bar sigma$.
  #mycode(ref: <code-store-update>, "https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Imp/Syntax/Ident.agda#L24" )[
//typstfmt::off
```hs
update : (id₁ : Ident) -> (v : ℤ) -> (s : Store) -> Store 
update id₁ v s id₂ with id₁ == id₂
... | true = (just v) 
... | false = (s id₂)
```
//typstfmt::on
  ]
4. *joining two stores* let $sigma_1$ and $sigma_2$ be two stores. We define the
  store that contains an $id$ if $id in sigma_1$ or $id in sigma_2$ as $sigma_1 union sigma_2$.
  Notice that the join operation is not commutative, as it may be that

  #align(center, 
  $exists id, exists space v_1, exists space v_2, v_1 eq.not v_2 and sigma_1 id equiv "just" v_1 and sigma_2 id equiv "just" v_2$
  )
  #mycode(ref: <code-store-join>, "https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Imp/Syntax/Ident.agda#L29" )[
//typstfmt::off
```hs
join : (s₁ s₂ : Store) -> Store
join s₁ s₂ id with (s₁ id) 
... | just v = just v
... | nothing = s₂ id
```
//typstfmt::on
  ]
5. *merging two stores* let $sigma_1$ and $sigma_2$ be two stores. We define the
  store that contains an $id$ if and only if $sigma_1 id equiv "just" v$ and $sigma_2 id equiv "just" v$ as $sigma_1 sect sigma_2$.
  #mycode(ref: <code-store-merge>, "https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Imp/Syntax/Ident.agda#L34" )[
//typstfmt::off
```hs
merge : (s₁ s₂ : Store) -> Store
merge s₁ s₂ = λ id -> (s₁ id) >>= λ v₁ -> (s₂ id) >>= λ v₂ -> if (⌊ v₁ ≟ v₂ ⌋) then just v₁ else nothing
```
//typstfmt::on
  ]
#definition[
    Let $sigma_1$ and $sigma_2$ be two stores. We define the unvalued inclusion
    between them as

    $ forall id, paren.l space exists space z, space sigma_1 id equiv "just" z space paren.r -> paren.l space exists space z, space sigma_2 id equiv "just" z space paren.r $

    and we denote it with $sigma_1 space ∻ space sigma_2$. 
    In Agda: 
#mycode("https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Imp/Syntax/Ident.agda#L83C1-L84C82")[
// typstfmt::off
    ```hs 
 _∻_ : Store -> Store -> Set
 x ∻ x₁ = ∀ {id : Ident} -> (∃ λ z -> x id ≡ just z) 
            -> (∃ λ z -> x₁ id ≡ just z)
    ```
// typstfmt::on
]
<imp-def-store-tilde-inclusion>
  ]

#theorem(name: "Transitivity of ∻ ")[
#mycode(proof: <proof-tilde-transitive>, "https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Imp/Syntax/Ident.agda#L86")[
// typstfmt::off
```hs 
∻-trans : ∀ {s₁ s₂ s₃ : Store} (h₁ : s₁ ∻ s₂) (h₂ : s₂ ∻ s₃) -> s₁ ∻ s₃
```
// typstfmt::on
] <imp-thm-store-tilde-transitive> ]

