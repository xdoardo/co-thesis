---
theme: apple-basic
colorSchema: 'dark'
layout: intro
title: MiniAgda
---

# MiniAgda 
Terminazione e produttività con *sized-types*.

<div class="absolute bottom-10">
  <span class="font-700">
    Edoardo Marangoni
  </span>
</div>

<div class="absolute bottom-10 right-10">
  <span class="font-700">
    <SlideCurrentNo /> / <SlidesTotal />
  </span>
</div>


--- 
layout: default
---

# Agenda 

<br>
<br>

* ## Introduzione
  Controlli di terminazione e produttività, approcci alternativi
* ## Sized-types 
  *Intuizione* dei sized-types e perché MiniAgda
* ## Tipi induttivi 
  Regole (intuitive) per il controllo della terminazione e implementazione del
  controllo di terminazione in MiniAgda
* ## Tipi co-induttivi
  *Guardedness* non tipata (sintattica) e tipata.

<div class="absolute bottom-10 right-10">
  <span class="font-700">
    <SlideCurrentNo /> / <SlidesTotal />
  </span>
</div>
---
layout: default
---
# Introduzione 
* ## Induzione 
``` coq
Inductive Nat : Set := 
  | zero : Nat
  | suc : Nat -> Nat.
```
* ## Co-Induzione
``` coq
CoInductive NatStream := cons {
  hd: nat ; 
  tail: NatStream
}.
```
<div class="absolute bottom-10 right-10">
  <span class="font-700">
    <SlideCurrentNo /> / <SlidesTotal />
  </span>
</div>
---
layout: default
---
# Introduzione 

Oltre ai motivi di consistenza logica, in un linguaggio con tipi dipendenti la
**totalità** è necessaria anche per assicurare la terminazione della fase di
type-checking. 
``` agda
 fooIsTrue : foo == true
 fooIsTrue = refl
```
Per mostrare che `refl` sia una dimostrazione del fatto che `foo == true`, Agda
impiega il type checker per mostrare che `foo` sia effettivamente
"riscrivibile" in `true`; se `foo` non termina, allora nemmeno il type-checker
termina.

Alcuni controlli implementati in Agda: 
* Type checking 
* Coverage checking
* <u>Termination checking</u>
* <u>Productivity</u> (via guardedness)

<div class="absolute bottom-10">
(dalla <a href="https://wiki.portal.chalmers.se/agda/ReferenceManual/Totality">
documentazione di Agda</a>)
</div>

<div class="absolute bottom-10 right-10">
  <span class="font-700">
    <SlideCurrentNo /> / <SlidesTotal />
  </span>
</div>

---
layout: default
---

# Introduzione 
Ci concentriamo su *terminazione* e *produttività*, ossia due criteri per
decidere se permettere delle definizioni di funzione ricorsive e co-ricorsive
in linguaggi totali. 

* ## Terminazione
*"Not all recursive functions are permitted - Agda accepts only these recursive
schemas that it can mechanically prove terminating."* 
[ <a href="https://wiki.portal.chalmers.se/agda/ReferenceManual/Totality#Terminationchecking">
ref</a> ]

* ## Produttività 
*"..Instead of termination we require productivity, which means that the next
portion can always be produced in finite time. A simple criterion for
productivity which can be checked syntactically is guardedness.."*
[ <a href="https://arxiv.org/pdf/1012.4896.pdf">
ref</a> ]

<div class="absolute bottom-10 right-10">
  <span class="font-700">
    <SlideCurrentNo /> / <SlidesTotal />
  </span>
</div>

---
layout: default
---

# Terminazione 
In Agda, il controllo di terminazione permette la definizione di funzioni
ricorsive primitive e di funzioni strutturalmente ricorsive.

*"..a given argument must be exactly one constructor smaller in each recursive call.."*

``` agda 
-- Primitive recursion
plus : Nat -> Nat -> Nat
plus zero    m = m
plus (suc n) m = suc (plus n m)
```

*"..we require recursive calls to be on a (strict) subexpression of the
argument; this is more general that just taking away one constructor at a time.
It also means that arguments may decrease in an lexicographic order - this can
be thought of as nested primitive recursion..."*
``` agda
-- Structural recursion
ack : Nat -> Nat -> Nat
ack zero    m       = suc m
ack (suc n) zero    = ack n (suc zero)
ack (suc n) (suc m) = ack n (ack (suc n) m)
```

<div class="absolute bottom-10 right-10">
  <span class="font-700">
    <SlideCurrentNo /> / <SlidesTotal />
  </span>
</div>

---
layout: default
---

# Produttività
In Agda, il controllo della produttività di una funzione co-ricorsiva è basato
sulla *guardedness* della definizione, ossia richiediamo che la definizione di
una funzione (la parte destra) sia un (co-)costruttore e che ogni chiamata
ricorsiva sia direttamente "sotto" esso.

Queste definizioni sono accettate: 
``` coq
CoFixpoint repeat (A:Type) (a:A): Stream := cons _ a (repeat _ a).
Compute hd (repeat _ 0). (* = 0 *)
Compute hd (tail (repeat _ 0)). (* = 0 *)

CoFixpoint countFrom (f :nat): Stream := cons _ f (countFrom (f + 1)).
Compute hd (countFrom  0). (* = 0*)
Compute hd (tail (countFrom 0)). (* = 1*)
Compute hd (tail (tail (countFrom 0))). (* = 2*)
```

<div class="absolute bottom-10 right-10">
  <span class="font-700">
    <SlideCurrentNo /> / <SlidesTotal />
  </span>
</div>

---
layout: quote
---
# "The **untyped** approaches have some shortcomings, including the sensitivity of the termination checker to syntactical reformulations of the programs, and a lack of means to propagate size information through function calls."
<a href="https://arxiv.org/abs/1012.4896">A. Abel, MiniAgda</a>

<div class="absolute bottom-10 right-10">
  <span class="font-700">
    <SlideCurrentNo /> / <SlidesTotal />
  </span>
</div>

---
layout: section
---
# Sized-types

Approccio **tipato**: annotiamo i tipi con una *size* (o
*taglia*) che esprime un'informazione sulla dimensione dei valori di quel tipo.
MiniAgda è "la prima implementazione *matura* di un sistema con sized-types".

<a href="https://arxiv.org/abs/1012.4896">A. Abel, MiniAgda</a>
<div class="absolute bottom-10 right-10">
  <span class="font-700">
    <SlideCurrentNo /> / <SlidesTotal />
  </span>
</div>

--- 
layout: default
---
# Tipi induttivi 

<br>
<br>
<br>
<br>

## Intuizione
* Associamo una *taglia* $i$ ad ogni tipo induttivo $D$;
* Controlliamo che la taglia diminuisce nelle chiamate ricorsive.

<div class="absolute bottom-10 right-10">
  <span class="font-700">
    <SlideCurrentNo /> / <SlidesTotal />
  </span>
</div>

--- 
layout: default
---
# Implementazione: altezza 
L'**altezza** di un elemento $d \in D$ è il *numero di costruttori* di $d$.
Possiamo immaginare $d$ come un albero in cui i nodi sono i costruttori.

  jasdjajds

<div class="absolute right-50">
  <span class="font-700">
    <img src="/figures/tree_cons.png" width="50" height="100">
  </span>
</div>

<div class="absolute bottom-10 right-10">
  <span class="font-700">
    <SlideCurrentNo /> / <SlidesTotal />
  </span>
</div>


---
layout: image-right
image: '/figures/tree_cons.png'
---

# Slide Title
## Slide Subtitle

* Slide bullet text
