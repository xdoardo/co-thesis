(* Esempio basilare *)
CoInductive Stream {A: Type} : Type := cons {
  hd: A;
  tail: Stream
}.

CoFixpoint countFrom (n:nat) := cons nat n (countFrom (n+1)).

Compute hd (countFrom 0).
Compute hd (tail (countFrom 0)).
Compute hd (tail (countFrom 0)).
