open Fifo 

let randmax = 1_000_000_000;;

let reduce n limit =
  Int.(of_float (to_float n /. to_float randmax *. to_float limit))

let rec sous_list i j l = 
  match l with
  |[] -> failwith "sous_list"
  |h :: t -> 
      let tail = 
        if j=0 then [] 
        else sous_list (i-1) (j-1) t 
      in
      if i>0 then tail
      else h :: tail ;;


(************************)
                         
let diff a b = 
  if(a>b || a=b) then a-b else a-b+randmax;;


let tirage f1 f2 =  (* f1 de taille 31 derniers, et f2 de taille 24 premiers*)
  let n1= pop f1 in
  let n2 = pop f2 in
  let new_f1 = push (fst n2) (snd n1) in 
  let d = diff (fst n1) (fst n2) in
  let new_f2 = push d (snd n2) in
  (d, (new_f1, new_f2));;

let compare_pair pair1 pair2 =(fst pair1) - (fst pair2);; 

let init_list_de_la_permutation graine= 
  let rec loop i list lastPair beforeLastPair = match i with
    |55 -> list
    |_ -> 
        let a = ((fst lastPair + 21) mod 55) in
        let b = diff (snd beforeLastPair) (snd lastPair) in
        let x  = (a,b) in
        loop (i+1) (x::list) (x) lastPair
  in
  loop 2 ((21, 1)::(0,graine)::[]) (21, 1) (0,graine);;


let tirages n f1 f2 =
  let rec loop i (file1,file2) list =
    let res_tirage = tirage file1 file2 in (* res_tirage de type (int, (list int, list int)) *)
    if (n-1)= i then ((fst res_tirage)::list, snd res_tirage) 
    else loop (i+1) (snd (tirage file1 file2)) ((fst res_tirage)::list)
  in 
  loop 0 (f1, f2) [];;

let tirages_52 f1 f2 =
  let rec loop i (file1,file2) list =
    let res_tirage = tirage file1 file2 in (* res_tirage de type (int, (list int, list int)) *)
    match i with 
    |51 ->  ((fst res_tirage)::list, snd res_tirage) 
    |_ ->  loop (i+1) (snd (tirage file1 file2)) ((fst res_tirage)::list)
  in 
  loop 0 (f1, f2) [];;


let rec reduce_list list limit = match list with
  |[]-> []
  |x::r -> (reduce x limit)::(reduce_list r (limit -1));;

let construct =
  let rec loop i list= match i with
    |52-> list
    |_-> loop (i+1) (i::list)
  in List.rev (loop 0 []);;




let permute l= 
  let rec loop i list autorises res = match list with (* loop list list array *)
    |[]-> res
    |indice::r->
        let valeur =  List.nth autorises indice in 
        Array.set res i valeur;
        loop (i-1) (r) (List.filter (fun y -> (List.nth autorises indice)<>y) autorises) (res)
  in Array.to_list (loop 51 l construct (Array.make 52 (-1))) ;;
  


let shuffle n = 
  let les_paires = init_list_de_la_permutation n in
  let f2_f1 =snd (List.split (List.sort compare_pair (les_paires))) in
  let f2_init = of_list ( (sous_list 0 23 f2_f1)) in
  let f1_init = of_list ((sous_list 24 54 f2_f1)) in
  let tirages_165_fois = tirages 165  (f1_init) (f2_init) in
  let f1 =fst (snd tirages_165_fois) in
  let f2 = snd (snd tirages_165_fois) in
  let tirages_52_2 = List.rev (fst (tirages 52 f1 f2)) in
  permute (reduce_list tirages_52_2 52);;