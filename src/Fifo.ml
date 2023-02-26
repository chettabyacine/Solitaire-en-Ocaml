(** A FIFO structure (First-In First-Out),
    implemented in functional style
    (NB: the Queue module of OCaml stdlib is imperative)

    NB: l'implémentation fournie initialement ci-dessous est inefficace,
    l'améliorer (tout en restant fonctionnel). Par exemple on peut utiliser
    une paire de listes pour implémenter ['a t].

*)

type 'a t = 'a list (* head of list = first out *)
let empty = []
let push x q = q@[x]
let pop q = match q with x::q' -> x, q' | [] -> raise Not_found
let of_list l = List.rev l
let to_list l = l
let is_empty q = match q with |[]-> true |x::r-> false
let summit q = match q with x::q' -> x | [] -> raise Not_found
let insert_card x q = x::q
let after_pop_will_be_empty q = match q with |[]-> raise Not_found |x::[] -> true | x::y::r -> false