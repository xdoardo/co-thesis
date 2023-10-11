#import "@local/ebnf:0.1.0": *
#import "/includes.typ": *

== Introduction <section-imp-introduction>
=== Syntax <subsection-imp-introduction-syntax>
The syntax of the Imp language can be described in a handful of EBNF rules,
as shown in @imp-syntax-rules.

#ebnf("Imp", label: <imp-syntax-rules>, rules: (
  aexp: (
    (rule: [$n$], comment: [integer constant]), 
    (rule: [id], comment: [identifiers]), 
    (rule: [$a_1 + a_2$], comment: [sum])
  ),
  bexp: (
    (rule: [$b$], comment: [boolean constant]),
    (rule: [$a_1 < a_2$], comment: [integer inequality]),
    (rule: [$not b$], comment: [boolean negation]), 
    (rule: [$b_1 and b_2$], comment: [logical and])
  ),
  command: (
    (rule: [skip], comment: [nop]),
    (rule: [id $<-$ *aexp*], comment: [assignment]),
    (rule: [$c_1 ; c_2$], comment: [sequence]),
    (rule: [if *bexp* then $c_1$ else $c_2$], comment: [conditional]),
    (rule: [while *bexp* do c], comment: [loop]),
  ),
))

The syntactic elements of this language are _commands_, _arithmetic
expressions_, _boolean expressions_ and _identifiers_. Given its simple nature,
it is easy to give an abstract representation for its concrete syntax: all of
the elements can be represented with simple datatypes enclosing all the
information embedded in the syntactic rules, as shown in @code-ident, @code-aexp,
@code-bexp and @code-command.

#tablex(columns: (50%, 50%), 
auto-hlines: false, 
auto-vlines: false,
mycode(label: <code-ident>, "https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Imp/Syntax/Ident.agda#L15")[
//typstfmt::off
```hs
Ident : Set
Ident = String
```
//typstfmt::on
    ],
mycode(label: <code-aexp>, "https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Imp/Syntax/Core.agda#L13")[
//typstfmt::off
```hs
data AExp : Set where
 const : (n : ℤ)  -> AExp
 var   : (id : Ident) -> AExp
 plus  : (a₁ a₂ : AExp) -> AExp
```
//typstfmt::on
],
colspanx(2,
mycode(label: <code-bexp>, "https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Imp/Syntax/Core.agda#L18")[
//typstfmt::off
```hs
data BExp : Set where
 const : (b : Bool) -> BExp
 le    : (a₁ a₂ : AExp) -> BExp
 not   : (b : BExp) -> BExp
 and   : (b₁ b₂ : BExp) -> BExp
```
//typstfmt::on
]))
#mycode(label: <code-command>, "https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Imp/Syntax/Core.agda#L24")[
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
role) and their value, if any, can change in time. We need a way to keep track
of identifiers and their value: this tool is the `Store`. Stores are defined as
shown in @code-store, that is, as _partial maps_ with the use of the `Maybe` monad.
#mycode(label: <code-store>,
 "https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Imp/Syntax/Ident.agda#L18")[
  //typstfmt::off
```hs
Store : Set
Store = Ident -> Maybe ℤ
```
//typstfmt::on
]
We now proceed to show basic definitions over partial maps.
1. *in-store predicate*: let $id$ be an identifier and $sigma$ be a store. To say that
  $id$ is in $sigma$ we write $ id in sigma$; in other terms, it is the same as
  $exists space v in ZZ, sigma id equiv "just" v$.
2. *empty store*: we denote the empty store as $emptyset$. For this special store,
  it is always $forall id, id in emptyset -> bot$ or $forall id, emptyset id equiv "nothing"$.
  #mycode(label: <code-store-empty>, "https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Imp/Syntax/Ident.agda#L21")[
//typstfmt::off
```hs
empty : Store
empty = λ _ -> nothing
```
//typstfmt::on
  ]
3. *adding an identifier*: let $id$ be an identifier and $v : ZZ$ be a
  value. We denote the insertion of the pair $(id, v)$ in a store $sigma$ as $(id , v) arrow.r.bar sigma$.
  #mycode(label: <code-store-update>, "https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Imp/Syntax/Ident.agda#L24" )[
//typstfmt::off
```hs
update : (id₁ : Ident) -> (v : ℤ) -> (s : Store) -> Store
update id₁ v s id₂ with id₁ == id₂
... | true = (just v)
... | false = (s id₂)
```
//typstfmt::on
  ]
4. *joining two stores*: let $sigma_1$ and $sigma_2$ be two stores. We define the
  store that contains an $id$ if $id in sigma_1$ or $id in sigma_2$ as $sigma_1 union sigma_2$.
  Notice that the join operation is not commutative, as it may be that

  #align(center,
  $exists id, exists space v_1, exists space v_2, v_1 eq.not v_2 and sigma_1 id equiv "just" v_1 and sigma_2 id equiv "just" v_2$
  )
  #mycode(label: <code-store-join>, "https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Imp/Syntax/Ident.agda#L29" )[
//typstfmt::off
```hs
join : (s₁ s₂ : Store) -> Store
join s₁ s₂ id with (s₁ id)
... | just v = just v
... | nothing = s₂ id
```
//typstfmt::on
  ]
5. *merging two stores*: let $sigma_1$ and $sigma_2$ be two stores. We define the
  store that contains an $id$ if and only if $sigma_1 id equiv "just" v$ and $sigma_2 id equiv "just" v$ as $sigma_1 sect sigma_2$.
  #mycode(label: <code-store-merge>, "https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Imp/Syntax/Ident.agda#L34" )[
//typstfmt::off
```hs
merge : (s₁ s₂ : Store) -> Store
merge s₁ s₂ = 
  λ id -> (s₁ id) >>= 
    λ v₁ -> (s₂ id) >>= 
      λ v₂ -> if (⌊ v₁ ≟ v₂ ⌋) then just v₁ else nothing 
---               ^ decidable boolean equality for integers
```
//typstfmt::on
  ]
#definition(label: <def-imp-store-tilde-inclusion>)[
    Let $sigma_1$ and $sigma_2$ be two stores. We define a new relation between them as

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
]]

And we prove the transitivity of this new relation: 
#theorem(name: "Transitivity of ∻ ", label: <thm-imp-store-tilde-transitive>)[
#mycode(proof: <proof-tilde-transitive>, "https://github.com/ecmma/co-thesis/blob/master/agda/lujon/Imp/Syntax/Ident.agda#L86")[
// typstfmt::off
```hs
∻-trans : ∀ {s₁ s₂ s₃ : Store} (h₁ : s₁ ∻ s₂) (h₂ : s₂ ∻ s₃) -> s₁ ∻ s₃
```
// typstfmt::on
]]

