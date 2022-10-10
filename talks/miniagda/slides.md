---
theme: myTheme
paginate: true
marp: true
markdown.marp.breaks: "off"
---

<style>
{
  font-size: 25px
}
</style>

<!-- _footer: Edoardo Marangoni -->
<!-- _class: lead -->
# MiniAgda 
Terminazione e produttività con *sized-types*.

---

<!-- _class: agenda -->
## Agenda 
- **Introduzione**
- **Tipi induttivi**
  *Controllare la terminazione. Regole (intuitive) per il controllo della terminazione e implementazione in MiniAgda.*
- **Tipi co-induttivi**
  *Controllare la produttività. Guardedness non tipata (sintattica) e tipata.*

---

## Introduzione 
Nei proof assistant, la totalità è necessaria per mantenere la **consistenza** del sistema: se, infatti, ammettiamo definizioni ricorsive non terminanti, si possono dimostrari teoremi falsi.
``` coq
Unset Guard Checking.
Fixpoint bad (x : nat) := 1 + (bad x).

Axiom bad_ax : forall x, bad x = 1 + (bad x).

Theorem n_neq_sn : forall (x:nat), (x = S x) -> False.
Proof. intros.  induction x.
  + inversion H.
  + inversion H.  apply IHx in H1. assumption.
Qed.

Theorem zero_eq_one: 0 = 1.
  assert (bad 0 = 1 + (bad 0)).
  + apply bad_ax.
  + destruct bad; simpl in H.
    * assumption.
    * apply n_neq_sn in H. exfalso. assumption.
Qed.
```

---
## Introduzione
Oltre ai motivi di consistenza logica, in un linguaggio con tipi dipendenti la **totalità** è necessaria anche per assicurare la terminazione della fase di type-checking.

``` agda
 fooIsTrue : foo == true
 fooIsTrue = refl
```
Per mostrare che `refl` sia una dimostrazione del fatto che `foo == true`, Agda impiega il type checker per mostrare che `foo` sia effettivamente "riscrivibile" in `true`; se `foo` non termina, allora nemmeno il type-checker termina. Ci concentriamo su **terminazione** e **produttività**, ossia due criteri per decidere se permettere delle definizioni di funzione ricorsive e co-ricorsive in linguaggi totali. 

---

## Tipi induttivi

Esempio basilare in Coq
``` coq 
Inductive Nat : Type := 
  | zero : Nat 
  | succ : Nat -> Nat

(* ricorsione primitiva *)
Fixpoint minus (x y : Nat) : Nat := 
  match x with 
  | zero => zero 
  | succ x' => match y with 
               | zero => succ x'
               | succ y' => minus x' y' 
               end
  end.

(* termina? *)
Fixpoint div (x y : Nat) :  Nat := z
match x with 
| zero => zero
| succ x' => succ (div (minus x y) y)
end.
```
---

## Tipi induttivi
...e in Agda
``` agda
data Nat : Set where 
  zero : Nat 
  succ : Nat -> Nat 

-- ricorsione primitiva
minus : Nat -> Nat -> Nat 
minus zero _ = zero
minus (succ x) zero = succ x
minus (succ x) (succ y) = minus x y

-- termina?
div : Nat -> Nat -> Nat 
div zero _ = zero 
div (succ x) y = succ (div (minus x y) y)
```

Le definizioni di `div` ovviamente terminano: vengono accettate?

---

<!-- _class: fact -->
## no
``` coq
Cannot guess decreasing argument of fix.
```
``` agda
Termination checking failed for the following functions:
  div
Problematic calls:
  div (minus x y) y
```
Coq e Agda basano il controllo della terminazione sulla sintassi e non sono pertanto in grado di catturare informazioni semantiche rilevanti.

*"The **untyped** approaches have some shortcomings, including the sensitivity of the termination checker to syntactical reformulations of the programs, and a lack of means to propagate size information through function calls."*  [[A. Abel, MiniAgda]](https://arxiv.org/abs/1012.4896)

---

## Tipi induttivi: terminazione (in agda) 

 Non tutte le funzioni ricorsive sono permesse: Agda, per esempio, accetta solo quegli schemi ricorsivi che riesce a dimostrare terminanti. 

- **Ricorsione primitiva**
Un argomento di una chiamata ricorsiva deve essere *esattamente* più piccola "di un costruttore".
``` agda 
plus : Nat -> Nat -> Nat
plus zero    m = m
plus (suc n) m = suc (plus n m)
```
- **Ricorsione strutturale**
Un argomento di una chiamata ricorsiva deve essere una *sottoespressione*.
``` agda
fib : Nat -> Nat
  fib zero          = zero
  fib (suc zero)    = suc zero
  fib (suc (suc n)) = plus (fib n) (fib (suc n))
```
[[ref]](https://wiki.portal.chalmers.se/agda/ReferenceManual/Totality#Terminationchecking)

---

## Sized-types: intuizione
Sono un approccio **tipato**: annotiamo i tipi con una *size* (o *taglia*) che esprime un'informazione sulla dimensione dei valori di quel tipo. MiniAgda è "la prima implementazione *matura* di un sistema con sized-types". [[ref]](https://arxiv.org/abs/1012.4896)

Per quanto riguarda la terminazione, l'idea di base è la seguente:
- Associamo una *taglia* $i$ ad ogni tipo induttivo $D$;
- Controlliamo che la taglia diminuisca nelle chiamate ricorsive.

---
## Tipi induttivi sized: implementazione
- **Altezza**
L'**altezza** di un elemento induttivo $d \in D$ è il *numero di costruttori* di $d$. Possiamo immaginare $d$ come un albero in cui i nodi sono i costruttori: per esempio, l'altezza di un numero naturale $n$ è $n+1$ (perché c'è il costruttore $zero$ come foglia con $n$ costruttori $succ$).

- **Taglia**
Dato un certo tipo induttivo $D$ associamo ad esso una taglia $i$, ottenendo un tipo $D^i$ che contiene solo quei $d$ la cui altezza **è minore** di $i$; in altre parole, ogni $d \in D^i$ ha un'altezza che ha come **upper bound** la taglia $i$.

- **Rappresentazione**
In un linguaggio d.t. possiamo modellare la taglia come un tipo $Size$ con un successore $\$: Size \rightarrow Size$; i *sized-types* sono quindi membri di $Size \rightarrow Set$. 

---

## Tipi induttivi sized: implementazione 

- **Sottotipi**
Siccome le taglie sono upper bound dell'altezza di un elemento, viene naturale la regola di sottotipizzazione $D^i \leq D^{\$i} \leq \cdots \leq D^{\omega}$ dove $D^{\omega}$ è un elemento la cui altezza è ignota.

- **Parametricità**
Le taglie sono utili sono durante il type checking e devono essere rimosse una volta concluso. Pertanto, i risultati di una funzione non devono essere dipendenti dalle taglie.

- **Dot patterns**
E' necessario utilizzare dei *pattern inaccessibili* per evitare la non-linearità del lato sinistro del pattern match. 

- **Size patterns**
Introduciamo i *size patterns* $i > j$ per legare una variabile $j$ e "ricordarsi" che $i > j$.

---
## Tipi induttivi sized: esempio
``` agda
-- Naturali *sized*
data SNat : Size -> Set where
  zero : {i : Size} -> SNat (↑ i) -- In Agda l'operatore successore sulle taglie è ↑ 
  succ : {i : Size} -> SNat (i) -> SNat (↑ i) 

--                                   | taglia sconosciuta (ω)
--                                   v 
minus : {i : Size} -> SNat i -> SNat ∞ -> SNat i
minus zero y = zero
minus x zero  = x
-- anche se `minus x y` ha una taglia strettamente minore di i, il tipo del
-- risultato è SNat i (e questo caso, `minus x y`, è ben tipato per
-- sottotipizzazione); in altre parole, l'informazione che in questo caso il
-- risultato ha taglia strettamente minore di x è persa. 
minus (succ x) (succ y) = minus x y 

-- Divisione euclidea *sized*
div : {i : Size} -> SNat i -> SNat ∞ -> SNat i
div zero y = zero
div (succ x) y = succ (div (minus x y) y)
-- Siccome x ha taglia `j<i`, lo stesso vale anche per `minus x y`: la chiamata
-- ricorsiva a `div` avviene sulla taglia `j` strettamente minore di `i`; questo
-- permette di dimostrare la terminazione della funzione.
```

---
## Tipi induttivi sized: esempio (2)
``` agda
data List (A : Set) : Set where
  nil : List A 
  cons : A -> List A -> List A

mapList : {A : Set} -> {B : Set} -> (A -> B) -> List A -> List B
mapList f nil = nil 
mapList f (cons a x) = cons (f a) (mapList f x)

data Rose (A : Set) : Size → Set where
  rose : {i : Size} -> A -> List (Rose A i) → Rose A (↑ i)

mapRose : {A : Set} -> {B : Set} -> (A -> B) -> {i : Size} -> Rose A i -> Rose B i
mapRose f (rose a rs) = rose (f a) (mapList (mapRose f) rs)
```

Senza *sized-types*: 
``` agda
Termination checking failed for the following functions:
  mapRose
Problematic calls:
  mapRose f
```

---

## Tipi co-induttivi
Nonostante sia necessaria la totalità, possiamo lo stesso "osservare" oggetti infiniti tramite la *co-induzione*, concetto duale all'induzione. L'esempio principale dei tipi co-induttivi è quello degli *stream*. Esempio basilare in Coq
``` coq
CoInductive Stream {A: Type} : Type := cons { hd: A; tail: Stream }.
CoFixpoint countFrom (n:nat) := cons nat n (countFrom (n+1)). (* =*> (cons n (cons n+1 (cons n+2 (...)))) *)
Compute hd (countFrom 0). (* = 0 *)
Compute hd (tail (countFrom 0)). (* = 1 *)
Compute hd (tail (tail (countFrom 0))). (* = 2 *)
```
...e in Agda 
``` agda
record Stream (A : Set) : Set where
  coinductive
  field
    head : A
    tail : Stream A

countFrom : Nat -> Stream Nat 
head (countFrom x) = x  -- Agda usa i co-patterns!
tail (countFrom x) = countFrom (suc x)
```

---
## Tipi co-induttivi: produttività 
Non possiamo richiedere la *terminazione* di una funzione come `countFrom`; invece, richiediamo la **produttività**: 
*"[...] we require productivity, which means that the next portion can always be produced in finite time. A simple criterion for productivity which can be checked syntactically is guardedness.."* [[ref]](https://arxiv.org/pdf/1012.4896.pdf)

Possiamo immaginare il duale dell'altezza di un oggetto induttivo come la **profondità**


---

# Produttività
In Agda, il controllo della produttività di una funzione co-ricorsiva è basato
sulla *guardedness* della definizione, ossia richiediamo che la definizione di
una funzione (la parte destra) sia un (co-)costruttore e che ogni chiamata
ricorsiva sia direttamente "sotto" esso.

---
---
## Tipi co-induttivi 
Questa definizione è accettata per *guardedness*:
``` agda 
repeat : (A : Set) -> (a:A) -> Stream A 
repeat A a = cons A a (repeat A a)
```

Questa dipende da $f$:
``` agda 
repeatf : (A : Set) -> (a:A) -> Stream A 
repeatf A a = cons A a (f repeat A a)
```
se $f$ è, esempio, $tail$, la definizione si riduce a sé stessa dopo una ricorsione: 
```
tail (repeat a) -> tail (a :: tail repeat a) -> tail repeat a -> ...
```
se invece $f$ mantiene la lunghezza dello stream o la incrementa, `repeatf` è
produttiva; i controlli puramente sintattici, però, non possono catturare
questo aspetto.

---
## Tipi co-induttivi: implementazione
* ## Profondità
La **profondità** di un elemento coinduttivo $d \in D$ è il *numero di
co-costruttori* di $d$. Uno stream interamente costruito avrà profondità $\omega$.

* ## Taglia 
Indiciamo quindi il tipo $D$ con $i$ ottenendo un tipo $D^i$ che contiene solo
quei $d$ la cui altezza **è maggiore** di $i$; in altre parole, la taglia $i$
di un tipo coinduttivo $D^i$ è un **lower bound** dell'altezza degli elementi
di $D^i$.

``` agda
codata NatStream : Size -> Set
  cons : (i : Size) -> Nat -> NatStream i -> NatStream ($ i)

hd : (i : Size) -> NatStream $i -> Nat
hd i (cons .i a s) = a

tl : (i : Size) -> NatStream $i -> NatStream i
tl i (cons .i a s) = s
```
---
## Tipi co-induttivi: produttività
La funzione `repeat` con i sized-types:
``` agda
repeat: Nat -> (i:Size) -> NatStream i
repeat n ($i) = cons i n (repeat n i)
```
Assumiamo che `repeat n i` produca uno stream *ben definito* di profondità $i$
e automaticamente mostriamo che `repeat n ($i)` produce uno stream di
profondità $n+1$. 

* ## Successor pattern
Perché possiamo fare il matching su `($i)`? 
Se `j = ($i) = n + 1` allora $i =
n$; se `j = ω`, allora `i = ω`; se `j = 0`, allora possiamo produrre ciò che
vogliamo.
