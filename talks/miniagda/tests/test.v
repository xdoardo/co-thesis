(* Questo file contiene definizioni induttive e co-induttive usate come esempio
* nelle slides. *)
(* Semplice definizione induttiva. *)
Inductive Nat : Type := 
  | zero : Nat 
  | succ : Nat -> Nat.

Fixpoint minus (x y: Nat): Nat:= 
match x with 
| zero => zero 
| succ x' => match y with 
             | zero => succ x'
             | succ y' => minus x' y' 
             end
end.

Compute minus (succ (succ zero)) zero.
Compute minus (succ (succ zero)) (succ zero).

(* Questa definizione fallisce perché Coq non riesce a "capire" che l'utilizzo di 
   ~minus~ implica che gli argomenti diminuiscano in ogni caso: 
  y == 0 
      => minus (succ x') 0 = succ x' (uguale, ma nessuna chiamata ricorsiva)
  y == succ y' 
      => minus (succ x') (succ y') = minus x' y' (diminuito)
. *)
Fail Fixpoint div (x y: Nat) :  Nat := 
match x with 
| zero => zero
| succ x' => succ (div (minus x y) y)
end.
(* Compute div (succ (succ (succ (succ zero)))) (succ (succ zero)). *)



(*  *)
CoInductive Stream {A: Type} : Type := cons {
  hd: A;
  tail: Stream
}.

CoFixpoint repeat {A:Type} (a:A) : Stream := cons A a (repeat a).
Compute hd (repeat 0).
Compute hd (tail (repeat 0)).

CoFixpoint countFrom (n:Nat) := cons Nat n (countFrom (succ n)).

