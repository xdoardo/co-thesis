#import "@preview/polylux:0.3.1": *
#import "@preview/prooftrees:0.1.0"
#import "@preview/tablex:0.0.5": tablex, rowspanx, colspanx

#import themes.simple: *

#set text(font: "Roslindale Deck")
#show heading.where(level: 1): set text(font: "Roslindale Deck")
#show heading.where(level: 2): set text(font: "Roslindale Deck")

#show: simple-theme.with(background: rgb(255, 244, 233), foreground: black)

#title-slide[
  #text(size: 50pt, [*Program Transformations in the Delay Monad*])

  #text(
    size: 20pt,
    underline([A Case Study for Coinduction via Copatterns and Sized Types]),
  )
  #v(1em)

  Edoardo Marangoni

  #text(size: 15pt, [_Università Statale di Milano_])

]

#set text(font: "EB Garamond")
#show raw: set text(font: "PragmataPro Mono Liga", size: 20pt)

#pagebreak()

#align(center + horizon, [= Introduzione])

#slide[
  == Contesto
  - Trasformazioni:
    - Funzioni con input e output listati di linguaggi di programmazione
    - Se input e output sono nello stesso linguaggio si chiamo _source to source_
    - Altrimenti _source to target_

  - Compilatori:
    - _Trasformano_ i programmi in input
    - Ottimizzano, riducono o modificano il listato del programma in input
]

#slide[
  == Contesto
  - GCC: decine di milioni di LoCs, \~30 ottimizzazioni
  

  - LLVM: centinaia di migliaia di LoCs, \~40 ottimizzazioni


  - Ottimizzazioni, passaggio critico:  
    - Zhou, Ren, Gao and Jiang nel 2021 trovano \~57K bug in GCC e \~22K in LLVM
    - Yang, Chen, Eide and Regehr nel 2011 trovano input per cui alcuni compilatori generavano output sbagliato
]

#slide[
  == Contesto
  

  - Le trasformazioni non devono cambiare il significato del programma
  

  - Non basta la "buona fede" nel programmatore
  

  - E' necessario *dimostrare* che la trasformazione è _safe_
  
  - Stato dell'arte: CompCert
   - Leroy et al
   - Compilatore C
   - 16 trasformazioni e 10 linguaggi intermedi
   - Ogni passaggio verificato formalmente in Coq, un proof assistant
]

#slide[
  == Contesto

  Dati:
  

  1. Linguaggio di programmazione (e.g. C)
  

  2. Trasformazioni sui programmi del linguaggio di programmazione
  

  Vogliamo:
  

  3. Strumento formale per dimostrare che la trasformazione non cambia il _significato_ del programma

  4. Mantenimento dei comportamenti _osservabili_: convergenza, I/O..
]

#align(center + horizon, [= Semantiche e comportamenti])

#slide[
  == Semantiche
  

  - Strumento matematico per modellare il comportamento di un programma

  - Per i nostri obiettivi, secondo Leroy (co-autore di CompCert): *operazionale*
    *big-step*, simile ad un interprete che mette in relazione risultato finale e programma iniziale 
]


#slide[
  == Comportamenti osservabili
  #v(20pt, weak:true)
  - Vogliamo modellare (tra i vari) anche *fallimento* (crash, e.g. divisione per
    zero, identificatore non inizializzato a runtime), e *divergenza*
  - Possiamo mostrare che se `p` diverge allora anche `t(p)` diverge e che se `p`
    fallisce anche `t(p)` fallisce, non solo che se `p` converge allora anche `t(p)`
    converge (allo stesso risultato)
  - Già fatto in letteratura, usando definizioni non equazionali e regole che portavano a dimostrazioni complesse
  - Scopo della tesi è farlo utilizzando un'unica semantica espressa come funzione che modella i tre comportamenti in maniera che faciliti le dimostrazioni
]

#slide[
  == Proof assistants
  #v(30pt, weak: true)
  - Uso generale: aiutare utenti a fare dimostrazioni, a volte in maniera
    (semi-)automatica

  - Sono anche linguaggi di programmazione: i tipi sono proposizioni e i termini
    sono dimostrazioni (corrispondenza di Curry-Howard)

  - Internalizzano una logica, ma per mantenere la consistenza della logica tutte le definizioni devono essere *terminanti*

  - All'interno possiamo definire la semantica come relazione (ad uso _deduttivo_) o come funzione (per _calcolare_)
]

#slide[
  == Effetti
  

  - Possiamo modellare i comportamenti come _effetti_
  

  - Nei linguaggi funzionali gli effetti sono rappresentati tramite *monadi*

    - *Convergenza* l'interprete produce un risultato

    - *Fallimento* monade `Maybe`, effetto del fallimento

    - *Divergenza* (da Capretta: _"divergence is an effect"_) monade `Delay`, effetto della divergenza
]
#slide[
  == Effetti

  - La semantica è espressa come un interprete che avrà una segnatura simile a
  #align(center, ```hs eval : Program -> Store -> Delay (Maybe Store)```)
  

  - `Maybe` è un tipo induttivo, i valori di tipo `Maybe A` sono
    oggetti (matematici) finiti
  

  - `Delay` deve rappresentare valori infiniti e non può essere induttivo
  

  #box(
    width: 100%,
    inset: 10pt,
    align(
      center,
      [serve uno strumento matematico che permetta di formalizzare oggetti infiniti],
    ),
  )

]

#align(center + horizon, [= Coinduzione e Agda])
#slide[
  == Coinduzione

  - Duale all'induzione
  

  - Molte interpretazioni: categorie, linguaggi formali e automi, punti fissi..

  - In generale, se l'induzione definisce l'insieme più piccolo che soddisfa un
    insieme di regole, la coinduzione definisce l'insieme più grande

  - Esempi di definizioni coinduttive sono stream, parole finite ed infinite in un
    linguaggio formale, alberi infiniti...
  

  - Induzione richiede terminazione, coinduzione richiede *produttività*
]

#slide[
  == Agda
  - Proof assistant e linguaggio di programmazione (non general-purpose)

  - Infrastruttura migliore per la coinduzione tra i proof-assistant maturi
    attualmente

  - Vari approcci per gestire la coinduzione: _musical notation_, _guardedness_ e
    *size-types*
    - Terminazione e produttività sintattiche
    - _size_ è un numero naturale associato ai tipi, controllo terminazione e produttività nel type system
]

#align(center + horizon, [= Sviluppo formale])
#slide[
  == Linguaggio e semantica
  - *Imp* è un linguaggio imperativo molto semplice ma Turing-completo
  #box(
    width: 100%,
    stroke: 1pt,
    inset: 10pt,
    radius: 4pt,
  )[
    #set text(size: 15pt)
    #grid(
      columns: (65pt, 30pt, auto),
      row-gutter: 10pt,
      [*aexp*],
      $:=$,
      $n | id | "plus" a_1 a_2$,
      [*bexp*],
      $:=$,
      $b | "le" a_1 a_2 | "and" b_1 b_2 | "not" b$,
      [*comm*],
      $:=$,
      [skip | assign $id$ $a$ | if $b$ then $c^t$ else $c^f$ | seq $c_1$ $c_2$ | while $b$ do $c'$],
    )
  ]

  - Semantica -- `Store` rappresenta la memoria durante l'esecuzione

  #align(
    center,
    ```hs ceval : ∀ {i} (c : Command) -> (s : Store) -> Delay (Maybe Store) i```,
  )

  #box(
    width: 100%,
    inset: 10pt,
    align(center, [`ceval` è *un'unica funzione* e modella tutti e tre i comportamenti]),
  )
]

#slide[
  == Trasformazioni
  

  - Un'analisi e una trasformazione

  - _Definite initialization analysis_: controlla se vengono utilizzate variabili
    inizializzate

  - _Constant folding_: esegue calcoli staticamente prima dell'esecuzione del
    programma
]

#slide[
  == Definite initialization analysis
  #v(20pt, weak: true)
  #block(
    width: 100%,
    stroke: 1pt,
    radius: 4pt,
    inset: 10pt,
  )[
    *Teorema*

    Per ogni comando `c`, per ogni insieme di variabili `v` e `v'`, per ogni
    store `s`, se vale `Dia v c v'` e `v ⊆ s` allora l'esecuzione di `c` diverge
    o converge, ma non fallisce.
  ]
  In Agda: 
```hs
dia-safe : ∀ (c : Command) (s : Store) (v v' : VarsSet) 
  (dia : Dia v c v') (v⊆s : v ⊆ dom s) -> (h-err : (ceval c s) ↯) ->  ⊥
```
]
#slide[
  ==  Constant folding 

  - E' una trasformazione, quindi una funzione che opera sugli elementi sintattici di Imp
  
  - In Agda: 

  #align(
    center,
    ```hs cpfold : (c : Command) -> Command```
  )

  - Vogliamo dimostrare che `cpfold` non cambia la semantica del programma
]
#slide[
  ==  Constant folding 
  #v(20pt, weak: true)
  #block(
    width: 100%,
    stroke: 1pt,
    radius: 4pt,
    inset: 10pt,
  )[
    *Teorema*

    Per ogni comando `c` e per ogni store `s`, la valutazione di `c` in `s` è 
    _uguale_ alla valutazione di `(cpfold c)` in `s`.
  ]
  In Agda: 
  #align(center,
```hs
cpfold-safe : ∀ (c : Command) (s : Store) -> 
 ∞ ⊢ (ceval c s) ≋ (ceval (cpfold c) s)
```)
]


#align(center + horizon, [= Conclusioni])
#slide[
  == Semantica, delay e size

  - Abbiamo definito la semantica come un'unica funzione che modella i tre effetti 

  - Abbiamo usato il tipo coinduttivo `Delay` utilizzando il type system come termination checker grazie alle size 

  - Abbiamo dimostrato che le trasformazioni che abbiamo scelto non cambiano la semantica del programma


]

#slide[
  == Lavori futuri
  
  - Modellare altri effetti: I/O, altri tipi di fallimento

  - Considerare linguaggi più ampi

  - Implementare trasformazioni più complesse
]
