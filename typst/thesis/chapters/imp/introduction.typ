#import "@local/ebnf:0.1.0": *
#import "/includes.typ": *

== Introduction <section-imp-introduction>
The Imp language was devised to work as a simple example of an imperative
language; albeit having a handful of syntactic constructs, it's clearly a Turing
complete language.

=== Syntax <subsection-imp-introduction-syntax>
The syntax of the Imp language is can be described in a handful of EBNF rules,
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

The syntactic elements of this language are three: _commands_, _arithmetic
expressions_ and _boolean expressions_. Given its simple nature, it's easy to
give an abstract representation for its concrete syntax: all three can be
represented with simple datatypes enclosing all the information of the syntactic
rule.

Another important atomic element of Imp are _identifiers_. Identifiers can
mutate in time and, when misused, cause errors during the execution of programs:
in fact, there is no way to enforce the programmer to use only initialized
identifiers merely by syntax rules -- it would take a context-sensitive grammar
to achieve so, at least. A concept related to identifiers is that of _stores_,
which are conceptually instantaneous descriptions of the state of identifiers in
the ideal machine executing the program.

We now show how we implemented the syntactic elements of Imp in Agda and show a
handful of trivial properties: in @code-imp-stores-idents we show the datatypes
for identifiers and stores, while in @code-imp-expressions we show the datatypes
for the other syntactic constructs.

#figure(
  tablex(
    columns: 2,
    align: center + horizon,
    auto-vlines: false,
    auto-hlines: false,
    [```hs
                Ident : Set
                Ident = String
              ```],
    [
      ```hs
          Store : Set
          Store = Ident -> Maybe ℤ
          ```
    ],
  ),
  caption: "Datatypes for identifiers and stores",
  supplement: "Listing",
)<code-imp-stores-idents>

Notice that the implementation of `Store`s reflect the behaviour described
earlier in that they are intended as functions from `Ident` to `Maybe ℤ`.

#figure(tablex(
  columns: 2,
  align: center + horizon,
  auto-vlines: false,
  auto-hlines: false,
  [```hs
            data AExp : Set where
             const : (n : ℤ) -> AExp
             var   : (id : Ident) -> AExp
             plus  : (a₁ a₂ : AExp) -> AExp
            ```],
  [```hs
            data BExp : Set where
             const : (b : Bool) -> BExp
             le    : (a₁ a₂ : AExp) -> BExp
             not   : (b : BExp) -> BExp
             and   : (b₁ b₂ : BExp) -> BExp
            ```],
  colspanx(2)[```hs
            data Command : Set where
             skip   : Command
             assign : (id : Ident) -> (a : AExp) -> Command
             seq    : (c₁ c₂ : Command) -> Command
             ifelse : (b : BExp) -> (c₁ c₂ : Command) -> Command
             while  : (b : BExp) -> (c : Command) -> Command
            ```],
), 
  caption: "Datatype for expressions of Imp", 
  supplement: "Listing"
)<code-imp-expressions>

=== Properties of stores<subsection-imp-introduction-store-properties>
The first properties we show regard stores. We equip stores with the trivial operations 
of adding an identifier, merging two stores and joining two stores, as shown in @code-imp-stores.

#figure(
```hs 
 empty : Store 
 empty = λ _ -> nothing 
 update : (id₁ : Ident) -> (v : ℤ) -> (s : Store) -> Store 
 update id₁ v s id₂ 
  with id₁ == id₂ 
 ... | true = (just v) 
 ... | false = (s id₂)
 join : (s₁ s₂ : Store) -> Store 
 join s₁ s₂ id 
  with (s₁ id) 
 ... | just v = just v 
 ... | nothing = s₂ id 
 merge : (s₁ s₂ : Store) -> Store 
 merge s₁ s₂ = 
  λ id -> (s₁ id) >>= 
   λ v₁ -> (s₂ id) >>= 
    λ v₂ -> if (⌊ v₁ ≟ v₂ ⌋) then just v₁ else nothing
```,
caption: "Operations on stores")<code-imp-stores>

// @TODO: Change "inclusion"!
A trivial property of stores is that of unvalued inclusion, that is, a property
stating that if an identifier has a value in a store $sigma_1$, then it also
has a value (not necessarily the same) in another store $sigma_2$:

#property(name: "Unvalued store inclusion")[
Let $sigma_1$ and $sigma_2$ be two stores. We define the unvalued inclusion between them as

$ forall id,  paren.l space exists space z, space sigma_1 id equiv "just" z space paren.r  -> paren.l space exists space z, space sigma_2 id equiv "just" z space paren.r $

and we denote it with $sigma_1 space subset.eq.sq^u space sigma_2$.
In Agda: 
```hs
_⊑ᵘ_ : Store -> Store -> Set 
σ₁ ⊑ᵘ σ₂ = ∀ {id : Ident} -> (∃ λ z -> σ₁ id ≡ just z) -> (∃ λ z -> σ₂ id ≡ just z) 
```
<imp-property-store-unvalued-inclusion>
]

We equip  #thmref(<imp-property-store-unvalued-inclusion>)[Property] with a notion of transitivity. 

#theorem(name: "Transitivity of unvalued store inclusion")[
 Let $sigma_1$, $sigma_2$ and $sigma_3$ be three stores. Then 

 $ sigma_1 subset.eq.sq^u sigma_2 and sigma_2 subset.eq.sq^u sigma_3 -> sigma_1 subset.eq.sq^u sigma_3 $
  
 In Agda: 
```hs
⊑ᵘ-trans : ∀ {σ₁ σ₂ σ₃ : Store} (h₁ : σ₁ ⊑ᵘ σ₂) (h₂ : σ₂ ⊑ᵘ σ₃) -> σ₁ ⊑ᵘ σ₃
⊑ᵘ-trans h₁ h₂ id∈σ₁ = h₂ (h₁ id∈σ₁) 
```
]

The operations we define on stores are multiple: adding an identifier paired
with a value to a store, removing an identifier from a store, joining stores and
merging stores. We now define notations:

1. *in-store predicate* let $id : "Ident"$ and $sigma : "Store"$. To say that
  $id$ is in $sigma$ we write $ id in sigma$; in other terms, it's the same as
  $exists space v in ZZ, sigma id equiv "just" v$.
2. *empty store* we define the empty store as $emptyset$. For this special store,
  it is always $forall id, id in emptyset -> bot$ or $forall id, emptyset id equiv "nothing"$.
3. *adding an identifier* let $id : "Ident"$ be an identifier and $v : ZZ$ be a
  value. We denote the insertion of the pair $(id, v)$ in a store $sigma$ as $(id , v) arrow.r.bar sigma$.
4. *joining two stores* let $sigma_1$ and $sigma_2$ be two stores. We define the
  store that contains an $id$ if $id in sigma_1$ or $id in sigma_2$ as $sigma_1 union sigma_2$.
  Notice that the join operation is not commutative, as it may be that
  $ exists id, exists space v_1, exists space v_2, v_1 eq.not v_2 and sigma_1 id equiv "just" v_1 and sigma_2 id equiv "just" v_2 $
5. *merging two stores* let $sigma_1$ and $sigma_2$ be two stores. We define the
  store that contains an $id$ if and only if $sigma_1 id equiv "just" v$ and $sigma_2 id equiv "just" v$ as $sigma_1 sect sigma_2$.

=== Properties of expressions<subsection-imp-introduction-expressions-properties>
The properties of expressions we show here regard the syntactic relation
between elements. The property we define is that of _subterm relation_. In
Agda, as will be shown in the definitions, these properties are implemented as
datatypes. Properties #thmref(<imp-property-command-subterm>),
#thmref(<imp-property-bool-subterm>) and #thmref(<imp-property-arith-subterm>)
will be used later to relate semantic aspects of subterms with that of the
containing term itself or vice versa.

#property(name: "Arithmetic subterms")[
  Let $a_1$ and $a_2$ be arithmetic expressions.

  Then
  $ a_1 space subset.eq.sq^a "plus" space a_1 space a_2 $
  $ a_2 space subset.eq.sq^a "plus" space a_1 space a_2 $

 In Agda: 
 ```hs
data _⊏ᵃ_ : AExp -> AExp -> Set where 
  plus-l : (a a₁ : AExp) -> a ⊏ᵃ (plus a a₁)
  plus-r : (a a₁ : AExp) -> a₁ ⊏ᵃ (plus a a₁)
 ```
 <imp-property-arith-subterm>
]

#property(
  name: "Boolean subterms",
)[
    Let $a_1$ and $a_2$ be arithmetic expressions and $b_1$ and $b_2$ be boolean
    expressions.

    Then
    $ a_1 space subset.eq.sq^b "le" space a_1 space a_2 $
    $ a_2 space subset.eq.sq^b "le" space a_1 space a_2 $
    $ b_1 space subset.eq.sq^b "and" space b_1 space b_2 $
    $ b_2 space subset.eq.sq^b "and" space b_1 space b_2 $
    $ b_1 space subset.eq.sq^b "not" space b_1 $

In Agda: 
```hs
data _⊑ᵇ_  : {A : Set} -> A -> BExp -> Set where
 not : (b : BExp) -> b ⊑ᵇ (not b)
 and-l : (b₁ b₂ : BExp) -> b₁ ⊑ᵇ (and b₁ b₂)
 and-r : (b₁ b₂ : BExp) -> b₂ ⊑ᵇ (and b₁ b₂)
 le-l : (a₁ a₂ : AExp) -> a₁ ⊑ᵇ (le a₁ a₂)
 le-r : (a₁ a₂ : AExp) -> a₂ ⊑ᵇ (le a₁ a₂)
```
 <imp-property-bool-subterm>
]

#property(
  name: "Command subterms",
)[
    Let $id$ be an identifier, $a$ be an arithmetic expressions, $b$ be a boolean
    expression and $c_1$ and $c_2$ be commands.

    Then
    $ a space subset.eq.sq^c "assign" space id space a $
    $ c_1 space subset.eq.sq^c "seq" space c_1 space c_2 $
    $ c_2 space subset.eq.sq^c "seq" space c_1 space c_2 $
    $ b space subset.eq.sq^c "if" space b space space c_1 space c_2 $
    $ c_1 space subset.eq.sq^c "if" space b space c_1 space c_2 $
    $ c_2 space subset.eq.sq^c "if" space b space c_1 space c_2 $
    $ b space subset.eq.sq^c "while" space b space c_1 $
    $ c_1 space subset.eq.sq^c "while" space b space c_1 $

 In Agda:
 ```hs
 data _⊑ᶜ_ : {A : Set} -> A -> Command -> Set where
  assign : (id : Ident) (a : AExp) -> a ⊑ᶜ (assign id a)
  seq-l : (c₁ c₂ : Command) -> c₁ ⊑ᶜ (seq c₁ c₂)
  seq-r : (c₁ c₂ : Command) -> c₂ ⊑ᶜ (seq c₁ c₂)
  ifelse-b : (b : BExp) -> (c₁ c₂ : Command) -> b ⊑ᶜ (ifelse b c₁ c₂)
  ifelse-l : (b : BExp) -> (c₁ c₂ : Command) -> c₁ ⊑ᶜ (ifelse b c₁ c₂)
  ifelse-r : (b : BExp) -> (c₁ c₂ : Command) -> c₂ ⊑ᶜ (ifelse b c₁ c₂)
  while-b : (b : BExp) -> (c : Command) -> b ⊑ᶜ (while b c)
  while-c : (b : BExp) -> (c : Command) -> c ⊑ᶜ (while b c)

 ```
 <imp-property-command-subterm>
]

