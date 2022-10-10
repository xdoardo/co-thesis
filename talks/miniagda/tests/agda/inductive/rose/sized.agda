data List (A : Set) : Set where
  nil : List A 
  cons : A -> List A -> List A

mapList : {A : Set} -> {B : Set} -> (A -> B) -> List A -> List B
mapList f nil = nil 
mapList f (cons a x) = cons (f a) (mapList f x)

data Rose (A : Set) : Set where
  rose : A -> List (Rose A) → Rose A

mapRose : {A : Set} -> {B : Set} -> (A -> B) -> Rose A -> Rose B 
mapRose f (rose a rs) = rose (f a) (mapList (mapRose f) rs)
