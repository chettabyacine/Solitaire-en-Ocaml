open Stdlib
open XpatLib

let echec n = print_string "ECHEC "; print_int n;  print_newline () ; exit 1;;

type game = Freecell | Seahaven | Midnight | Baker

type mode =
  | Check of string (* filename of a solution file to check *)
  | Search of string (* filename where to write the solution *)

type config = { mutable game : game; mutable seed: int; mutable mode: mode }
let config = { game = Freecell; seed = 1; mode = Search "" }

type distination_coup = 
| Card of int
| V
| T

type game_state = { (* une structure qui représente l'état du jeu dans un instant t*)
  mutable colonnes : ((Card.card Fifo.t) option) list;
  mutable depots: (Card.suit * int) list; 
  mutable registrestemp: Card.card list;
  mutable historique_coup: (int * distination_coup) list;
  mutable nb_registres_restants : int;
  }


type remplissage_colonne_vide = Toutes | Roi | Aucune
type reception_nouvelle_carte = MemeCouleur | Alternee | DeuxCouleurs
type emplacement_roi = PeuImporte | Fond

type rules_game = { (* codification des régles à respecter pour chaque mode*)
     taille_init_colonnes : int list;
     taille_init_registres: int list;
     nb_registres_maximal : int;
     reception_nouvelle_carte: reception_nouvelle_carte;
     remplissage_colonne_vide: remplissage_colonne_vide;
     emplacement_roi: emplacement_roi;
}

  
let get_rules gamename = match gamename with (*définir 4 instances de rules, une pour chaque mode. On peut définir autres modes plustard*)
  |Freecell -> {
    taille_init_colonnes = [7;6;7;6;7;6;7;6];
    taille_init_registres = [0;0;0;0];
    reception_nouvelle_carte = Alternee;
    remplissage_colonne_vide = Toutes;
    emplacement_roi = PeuImporte ;
    nb_registres_maximal = 4;
  }
  |Seahaven -> {
    taille_init_colonnes = [5;5;5;5;5;5;5;5;5;5];
    taille_init_registres = [1;1;0;0];
    reception_nouvelle_carte = MemeCouleur;
    remplissage_colonne_vide = Roi;
    emplacement_roi = PeuImporte;
    nb_registres_maximal = 4;
  }
  |Midnight -> {
    taille_init_colonnes = [3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;3;1];
    taille_init_registres = [];
    reception_nouvelle_carte = MemeCouleur;
    remplissage_colonne_vide = Aucune;
    emplacement_roi= PeuImporte;
    nb_registres_maximal = 0;
  }
  |Baker -> {
    taille_init_colonnes = [4;4;4;4;4;4;4;4;4;4;4;4;4];
    taille_init_registres = [];
    reception_nouvelle_carte = DeuxCouleurs;
    remplissage_colonne_vide = Toutes;
    emplacement_roi= Fond;
    nb_registres_maximal = 0;
  }
;;


let getgame = function
  | "FreeCell"|"fc" -> Freecell
  | "Seahaven"|"st" -> Seahaven
  | "MidnightOil"|"mo" -> Midnight
  | "BakersDozen"|"bd" -> Baker
  | _ ->  raise Not_found

let split_on_dot name =
  match String.split_on_char '.' name with
  | [string1;string2] -> (string1,string2)
  | _ ->   raise Not_found

let set_game_seed name =
  try
    let (sname,snum) = split_on_dot name in
    config.game <- getgame sname;
    config.seed <- int_of_string snum
  with _ -> failwith ("Error: <game>.<number> expected, with <game> in "^
                      "FreeCell Seahaven MidnightOil BakersDozen");;


let get_new_depots depots card = (* copier depots en ajoutant card*)
(* de type (card suit * int) list -> card -> (card suit * int) *) 
  let rec loop liste resultat = match liste with
  |[]-> resultat
  |(a,b)::r-> if (a= (snd card)) then loop r ((a, b+1)::resultat) else loop r ((a,b)::resultat) 
  in loop depots [];;                 

let add_depot game_status card = (*ajouter card dans les dépots de games_status 
   ,renvoie vrai si la carte est déposée, faux sinon *)
  let current_card_rank_in_depots = List.assoc (snd card) (game_status.depots) in
  if current_card_rank_in_depots = ((fst card)-1) then 
    let _ = game_status.depots <- get_new_depots game_status.depots card in true
else false;;

let rec normalise game_status= (* normalisation apres chaque coup *)
(* on normalise les registres d'abord, et puis les colonnes *)
  let rec constuire_new_colonnes liste colonnes found = 
    (*recopie toutes les colonnes en supprimant une carte qui est admissible dans dépots*)
  match  liste with
  |[]-> (*apres avoir parcouru toute la liste, si une carte est déposée donc il faut refaire la normalisation,
     sinon, y a aucun truc à faire*)
    if (found) then let _ = (game_status.colonnes <- colonnes) in normalise game_status 
    else ()
  |None::r -> constuire_new_colonnes r (colonnes@[None]) found (* laisses les fifos vides intouchées*)
  |Some(x)::r when (found = false) && (add_depot game_status (Fifo.summit x))->  (* cas ou la carte est admissible dans les dépots
     ,on recopie la fifo apres le pop de la carte concernée*)
    let new_fifo = if (Fifo.after_pop_will_be_empty x) then None
    else  Some(snd (Fifo.pop x)) in
    constuire_new_colonnes r (colonnes@[new_fifo]) true  
  |Some(x)::r -> constuire_new_colonnes r (colonnes@[Some(x)]) found in (* cas d'une fifo qui ne contient aucune carte à déposer *)

  let rec construire_new_registres liste registres found = match liste with
  (*recopie toutes les registres en supprimant toutes les cartes qui sont admissibles dans dépots*)
  (* le meme raisonnement de la fct précédente*)
  |[]-> if (found= true) then
    let _ = game_status.registrestemp <- registres in
    let _ = game_status.nb_registres_restants <- game_status.nb_registres_restants + 1 
   in constuire_new_colonnes game_status.colonnes [] false 
  else constuire_new_colonnes game_status.colonnes [] false 
  |(a,b)::r when (add_depot game_status (a,b))->  construire_new_registres r registres true  
  |(a,b)::r -> construire_new_registres r ((a,b)::registres) found in

  construire_new_registres game_status.registrestemp [] false;;
 
   
let insert_card_destination game_status card_source card_destination n = 
  (* inserer la carte source dans la carte destination *)
  let rec remove_source_card_from_registres liste registres removed = match liste with
  (* pour supprimer la carte des registres, on recopie tous les registres sauf la carte en question*)
  |[] -> (registres, removed)
  |x::r -> if(x<>card_source) then  remove_source_card_from_registres r (registres@[x]) removed
  else remove_source_card_from_registres  r registres true in

  let rec add_in_destination liste colonnes pushed = match liste with
  (* pour ajouter une carte source dans une carte destination 
  (dans le cas ou la carte source est trouvée dans un registre)
  : on recopie toutes les colonnes
     on insert la carte une fois la destination est trouvée.*)
  |[]-> if pushed=true then colonnes else let _ =  echec n in [] (* assuming card has been already removed from registrestemp*)
  |None::r -> add_in_destination r (colonnes@[None]) pushed (* fifo vide, rien à faire *)
  |Some(x)::r when (pushed=false) && (Fifo.summit x = card_destination)-> (* cas où inserer la carte *)
    let new_fifo = Some(Fifo.insert_card card_source x) in
    add_in_destination r (colonnes@[new_fifo]) true
  |Some(x)::r -> 
    add_in_destination r (colonnes@[Some(x)]) pushed (* cas général*) in


  let rec constuire_new_colonnes liste colonnes pushed popped= 
  (*si la carte source n'est pas dans les registres, alors on parcous les colonnes
     pour à la fois pop la carte source et l'inserer dans la destination*)
  match  liste with
  |[]-> if (pushed && popped) then colonnes else let _ = echec n in []
  |None::r -> constuire_new_colonnes r (colonnes@[None]) pushed popped (* fifo vide*)
  |Some(x)::r when (pushed = false) && (Fifo.summit x =card_destination) -> (*ajouter à la destination*)
    let new_fifo = Some(Fifo.insert_card card_source x) in
    constuire_new_colonnes r (colonnes@[new_fifo]) true popped 
  |Some(x)::r when (popped = false) && (Fifo.summit x =card_source) -> (*supprimer la carte source*)
    let new_fifo = if (Fifo.after_pop_will_be_empty x) then None
    else Some(snd (Fifo.pop x)) in
      constuire_new_colonnes r (colonnes@[new_fifo]) pushed true 
  |Some(x)::r -> constuire_new_colonnes r (colonnes@[Some(x)]) pushed popped (*cas général*)in

  (*vérifier d'abord si la carte source est dans les registres temp*)
  let h = remove_source_card_from_registres game_status.registrestemp [] false in
  if ((snd h)= true) then (*carte trouvée dans les registres*)
    let _ = game_status.registrestemp <- (fst h) in 
    let _ = game_status.nb_registres_restants <-game_status.nb_registres_restants +1 in
    let j = add_in_destination (game_status.colonnes) [] false in
    game_status.colonnes <- j
   
  else (* carte est donc dans les colonnes*)
     game_status.colonnes <- (constuire_new_colonnes (game_status.colonnes) [] false false);;


let apply_coup_to_card game_state source destination rules n = 
  (* cette fonction traite les droits d'interser une carte selon les couleurs autorisées 
     puis fait appel de la fonction d'insersion dans une carte destination *)
  let card_source = Card.of_num source in
  let card_destination = Card.of_num destination in
  if ((fst card_destination) <> ((fst card_source)+1)) then let _ =echec n in () 
  else 
    match rules.reception_nouvelle_carte with
  |MemeCouleur -> if (Card.same_color card_source card_destination) then insert_card_destination game_state card_source card_destination n else let _ = echec n in ()
  |Alternee ->  if (Card.same_color card_source card_destination) then  let _ = echec n in ()  else insert_card_destination game_state card_source card_destination n
  |DeuxCouleurs -> insert_card_destination game_state card_source card_destination n ;;


let insert_card_colonne_vide game_status card n = 
  let rec remove_source_card_from_registres liste registres removed = match liste with (* rechercher la carte source
   dans registres et la supprimer en copiant tous les registres sauf la carte en question*)
  |[] -> (registres, removed)
  |x::r -> if(x<>card) then  remove_source_card_from_registres r (registres@[x]) removed
  else remove_source_card_from_registres  r registres true in

  let rec add_in_empty_colonne liste colonnes pushed = match liste with (*inserer concretement dans une fifo vide
     en copiant toutes les colonnes, et transformer un None à Some(_)*)
  |[]-> if pushed=true then colonnes else  let _ = echec n in []
  |None::r when (pushed=false) ->
    add_in_empty_colonne r (colonnes@[Some(Fifo.push card Fifo.empty)]) true
  |None::r-> add_in_empty_colonne r (colonnes@[None]) pushed
  |Some(x)::r -> add_in_empty_colonne r (colonnes@[Some(x)]) pushed in

  let rec constuire_new_colonnes liste colonnes pushed popped= match  liste with
  (*supprimer la carte source et la transformer une fifo None en Some(_) *)
    |[]-> if (pushed && popped) then colonnes else  let _ = echec n in []
    |None::r when (pushed = false) ->  (* cas de transformation *)
      constuire_new_colonnes r (colonnes@[Some(Fifo.push card (Fifo.empty))]) true popped
    |None::r ->  (* si une colonne vide à déja recu la carte source *)
      constuire_new_colonnes r (colonnes@[None]) pushed popped
    |Some(x)::r when (popped = false) && (Fifo.summit x = card) -> (* cas carte source est trouvée et à supprimer*) 
      let new_fifo = if (Fifo.after_pop_will_be_empty x) then None
      else Some(snd (Fifo.pop x)) in
      constuire_new_colonnes r (colonnes@[new_fifo]) pushed true
    |Some(x)::r -> constuire_new_colonnes r (colonnes@[Some(x)]) pushed popped (* cas général*) in

    (*rechercher la carte source dans les registres d'abord*)
  let h = remove_source_card_from_registres game_status.registrestemp [] false in

  if ((snd h)= true) then (* si la carte est trouvée dans les registres*)
    let _ = game_status.colonnes <-add_in_empty_colonne game_status.colonnes [] false in 
    let _ = game_status.registrestemp <- (fst h) in 
    game_status.nb_registres_restants <-game_status.nb_registres_restants +1 ;
  else game_status.colonnes <- (constuire_new_colonnes (game_status.colonnes) [] false false);;


let apply_coup_to_colnne_vide game_state source rules n =
  (*vérifie selon le mode du jeu quelle carte à le droit d'etre intserée dans une colonne vide*)
  let card_source = Card.of_num source in
  match rules.remplissage_colonne_vide with
    |Aucune -> let _ = echec n in ()
    |Roi -> if (fst card_source) <> 13 then
      let _ = echec n in  ()
            else insert_card_colonne_vide game_state card_source n 
    |Toutes -> insert_card_colonne_vide game_state card_source n;;

let insert_card_registre game_state card_source n = 
  (*insersion effective de la carte dans un registre libre*)
  let rec constuire_new_colonnes liste colonnes popped= 
  match  liste with
    |[]-> if (popped) then colonnes else let _ = echec n in []
    |None::r -> constuire_new_colonnes r (colonnes@[None]) popped (*fifo vide est ignorée*)
    |Some(x)::r when (popped = false) && (Fifo.summit x = card_source) -> (* cas où supprimer la carte*)
      let new_fifo = if (Fifo.after_pop_will_be_empty x) then None
      else Some(snd (Fifo.pop x)) in
      constuire_new_colonnes r (colonnes@[new_fifo]) true
    |Some(x)::r -> constuire_new_colonnes r (colonnes@[Some(x)]) popped (* cas général *) in

    (*vérifier si la carte est dans un registre*)
    let h = List.mem card_source game_state.registrestemp in
    if (h=true) then () (*si elle est trouvée dans un registre: 
       rien à faire car l'ordre n'est pas important*)
    else (*la carte est recherchée en suite dans les colonnes pour etre supprimée*)
      let _ = game_state.registrestemp <- card_source::(game_state.registrestemp)in
      let _ = game_state.nb_registres_restants <- game_state.nb_registres_restants - 1 in
      game_state.colonnes <- constuire_new_colonnes (game_state.colonnes) [] false ;;


let apply_coup_to_registre game_state source rules n =
  (*vérifier d'abord s'il y a un registre libre*)
  let card_source = Card.of_num source in
  if (game_state.nb_registres_restants <1) then echec n
  else insert_card_registre game_state card_source n;;

  let game_is_won game_state = 
    (* vérifier si tout les dépots contiennent des rois  et toutes les colonnes sont vides-< vrai, sinon faux*)
    let rec loop liste  = match liste with
    |[]-> true
    |(a,b)::r-> (b=13) && loop r in 

    let rec loop2 liste = match liste with
    |[]-> true
    |None::r-> loop2 r
    |Some(x)::r -> (Fifo.is_empty x) && loop2 r
  in loop game_state.depots && loop2 game_state.colonnes;; 


let validate_coup coup n = match coup with
(*vérifier si les valeurs du coup sont correctes*)
  |(a,Card(b)) when (a<0 || ( b<0 || (a>51 || b>51))) ->let _ = echec n in false
  |(_, V) -> true
  |(_, T)-> true
  |(a, Card(b)) (*when a>=0 && b>=0*) -> true;;

  
                
let check game_status rules fname  = 
  let file = open_in fname in (* ouverture du fichier*)
  let rec parcours_fichier file n = (* parcours recursive du fichier sol qui renvoie le nombre de la ligne*)
  let _ = normalise game_status in (* on commence toujours par un normalisaion récursive *)
    try
      (*lecture du coup et vérification qu'il soit correcte*)
      let x = input_line file in
      let deux_data = String.split_on_char ' ' x in
      let coup = match deux_data with 
      |[] -> let _ =  echec n in (-1,Card(-1)) 
      |a::[]-> let _ = echec n in (-1, Card(-1))
      |a::b::c::r -> let _ = echec n in (-1, Card(-1))
      |a::b::[] ->
        match b with
        |"V" -> (int_of_string a, V)
        |"T" -> (int_of_string a, T)
        |_ -> (int_of_string a, Card(int_of_string b)) in 
      let isValid = validate_coup coup n  in
      match coup with 
      (* fair selon la valeur du deuxieme element du coup*)
      |(source, Card(destination)) ->
        apply_coup_to_card game_status source destination rules n; 
        game_status.historique_coup <- coup::(game_status.historique_coup);
        parcours_fichier file (n+1)
      |(source, V) -> if rules.remplissage_colonne_vide=Aucune then echec n else
        (if ((rules.remplissage_colonne_vide = Roi) && ( (source lsr 2)+1 <>13)) then echec n else
        apply_coup_to_colnne_vide game_status source rules n;
        game_status.historique_coup <- coup::(game_status.historique_coup);
        parcours_fichier file (n+1))
      |(source, T) -> if (game_status.nb_registres_restants<=0) then echec n else
        apply_coup_to_registre game_status source rules n;
        game_status.historique_coup <- coup::(game_status.historique_coup);
        parcours_fichier file (n+1)
    with End_of_file -> let _ = normalise game_status in n (* terminer par faire une derniere normalisation *)
  in
let res = parcours_fichier file 1 in
let _ = close_in file in 
(* vérifier si la partie est gagnée*)
if (game_is_won game_status = true) then print_string "SUCCES"
else echec res ;;


 


  (* Fonction qui vérifie si une carte peut être empilée sur une autre carte dans une colonne donnée, en fonction des règles du jeu *)
  let destination_autorisee carte carte_dest (*destination*) rules =
    let couleur_ok =
      match rules.reception_nouvelle_carte with
      | MemeCouleur -> Card.same_color carte carte_dest
      | Alternee -> not (Card.same_color carte carte_dest)
      | DeuxCouleurs -> true
      in
      (* Vérification de la valeur de la carte *)
      let valeur_ok = ((fst carte) = ((fst carte_dest) - 1)) in
      couleur_ok && valeur_ok;;

      let rec find_destinations_dans_colonnes card colonnes res  rules= match colonnes with 
      (*recherche de destinations dans colonnes (vide ou pas)*)
      |[]-> List.rev res
      |None::r-> if (rules.remplissage_colonne_vide = Aucune) then find_destinations_dans_colonnes card r res rules
      else if ((rules.remplissage_colonne_vide = Roi) && ((fst card)<>13)) then find_destinations_dans_colonnes card r res rules
      else find_destinations_dans_colonnes card r ((Card.to_num card, V)::res) rules
      |Some(f)::r-> if not (Fifo.is_empty f) then
        let destination = (Fifo.summit f) in
        if (destination_autorisee card destination rules)=true then
          find_destinations_dans_colonnes card r ((Card.to_num card,Card(Card.to_num destination))::res) rules
        else find_destinations_dans_colonnes card r res rules
      else find_destinations_dans_colonnes card r res rules;;

      let find_destinations card (state: game_state) rules= 
        (* recherche de tous les déplacements possibles d'une carte donnée (vers destination, T ou V)*)
      if state.nb_registres_restants=0 then find_destinations_dans_colonnes card state.colonnes [] rules
      else (Card.to_num card, T)::(find_destinations_dans_colonnes card state.colonnes [] rules);;
    
         
    let coups_possibles state rules = 
      (* elle renvoie une liste de tous les coups possibles à partir d'un état de jeu*)
      let rec parcours_registres registres = match registres with
       (*cas où la carte source est dans un registres*)
      |[]-> []
      |carte::r -> (find_destinations carte state rules)@(parcours_registres r)
    
    in 
    let rec parcours_colonnes colonnes = match colonnes with
    (* cas où la carte source est dans une colonne*)
    |[]-> []
    |None::r-> parcours_colonnes r
    |Some(f)::r -> if not (Fifo.is_empty f) then
      let source = Fifo.summit f in
      let destinations = find_destinations source state rules in 
      destinations@(parcours_colonnes r)
    else parcours_colonnes r
    in
    let _ =
    (parcours_registres state.registrestemp)@(parcours_colonnes state.colonnes) in [];; (*TODO: à completer*)
    


let play_coup game_status coup rules = 
  (* modifier la variable game_status selon un coup*)
let _ = match coup with 
(* fair selon la valeur du deuxieme element du coup*)
|(source, Card(destination)) ->
  apply_coup_to_card game_status source destination rules 0; 
  game_status.historique_coup <- coup::(game_status.historique_coup);
|(source, V) -> if rules.remplissage_colonne_vide=Aucune then print_string "INSOLUBLE" else
  (if ((rules.remplissage_colonne_vide = Roi) && ( (source lsr 2)+1 <>13)) then print_string "INSOLUBLE" else
  apply_coup_to_colnne_vide game_status source rules 0);
  game_status.historique_coup <- coup::(game_status.historique_coup);
|(source, T) -> if (game_status.nb_registres_restants<=0) then print_string "INSOLUBLE" else
  apply_coup_to_registre game_status source rules 0;
  game_status.historique_coup <- coup::(game_status.historique_coup)
in 
let _ = normalise game_status in game_status;;

let search game_status rules fname  =
(*recherche d'une solution*)
let rec get_historique_solution treated_states to_be_treated_states =
  (*recherche un historique qui donne un état gagnant - parcours en largeur*)
  let current_state_option = match to_be_treated_states with |x::r -> Some(x) | []-> None in
  if (current_state_option<> None) && (game_is_won(Option.get (current_state_option))) then Some ((Option.get (current_state_option)).historique_coup)
  else if to_be_treated_states=[] then None
  else
    let current_state = (match to_be_treated_states  with |x::r-> x |[]-> raise Not_found) in
    let coups_possibles = coups_possibles current_state  rules  in
    let new_states = List.map (fun coup ->
      let state_temp = {
        colonnes = current_state.colonnes;
        depots = current_state.depots;
        registrestemp = current_state.registrestemp;
        historique_coup = current_state.historique_coup;
        nb_registres_restants = current_state.nb_registres_restants
      } in
      let _ = (play_coup state_temp coup rules) in state_temp) coups_possibles in
    let new_to_be_treated_states_full = (new_states @ (match to_be_treated_states  with |x::r-> r |[]->[]))  in
    let new_to_be_treated_states = List.filter (fun e -> not (List.mem e treated_states)) new_to_be_treated_states_full in 
    let new_treated_states = current_state::treated_states in
    get_historique_solution new_treated_states new_to_be_treated_states
in
let rec ecrire_historique file hist = 
  (* écrire l'historique trouvé dans le fichier de sortie*)
  try
    if(hist=[]) then close_out file 
    else
      (*let _ = Printf.printf "\nlenght of list of hist à écrire= %d" (List.length hist) in*)
      let coup = List.hd hist in
      let s = fst coup in
      let s_string = Int.to_string s in
      let d = snd coup in
      match d with
      |Card(d2) -> let d_string = Int.to_string d2 in 
                    let _ = output_string file (s_string^" "^d_string^"\n") in
                    ecrire_historique file (List.tl hist)
      |T -> let _ = output_string file (s_string^" T\n" )in
            ecrire_historique file (List.tl hist)
      |V-> let _ = output_string file (s_string^" V\n") in
            ecrire_historique file (List.tl hist)
  with e -> print_string "erreur dans ecriture\n"
in
let _ = normalise game_status in 
let historique = get_historique_solution  [] (game_status::[]) in
if historique=None then print_string "INSOLUBLE\n" else
let myfile = open_out fname in
let _ = ecrire_historique myfile (Option.get historique)
in print_string "SUCCESS\n";;


let arrange_kings_baker fifo =
  (* filtrer les rois deux autres cartes puis les concatener en inverse pour obtenir une fifo bonne pour Baker*) 
  let list_of_fifo = Fifo.to_list fifo in
  let kings = List.rev (List.filter (fun x -> (fst x)=13) list_of_fifo) in
  let reste = List.rev (List.filter (fun x -> (fst x)<>13) list_of_fifo) in
  Fifo.of_list(kings@reste) ;;

let place_king_back game_status = 
  (* modifier le contenu des colonnes dans game_status pour placer les rois au fond
     en construissant une nouvelle liste de colonnes*)
  let rec constuire_new_colonnes liste colonnes = match liste with
  |[]-> colonnes
  |None::r -> constuire_new_colonnes r (colonnes@[None]) (* fifo vide est ignorée*)
  |Some(x)::r -> (* pour chaque fifo non vide, vérifier l'emplacement des rois et le corriger si besoin*)
    constuire_new_colonnes r (colonnes@[Some(arrange_kings_baker x)]) 
in let _ = (game_status.colonnes <- (constuire_new_colonnes (game_status.colonnes) []))
in game_status;;

let initialise_game rules permut = (* retourner game_state selon rules de chaque mode*)
  let colonnes = [] in
  let depots = [( Card.Trefle, 0) ;(Card.Pique,0);(Card.Coeur, 0);(Card.Carreau, 0)] in
  let registrestemp = [] in
  let nb_registres_restants = rules.nb_registres_maximal in 
  let historique_coup = (-1, Card(-1))::[] in
  let empty_state = {colonnes; depots;registrestemp; historique_coup; nb_registres_restants;} (*var game_state initiale*)in

  let rec remplir_colonnes game_status permutx nb_cards list_taille_colonnes= match list_taille_colonnes with
  |[]-> (* si toutes les colonnes sont bien remplies, remplir les registres avec le reste de la permutation*)
    let _ = (game_status.registrestemp <- List.stable_sort (fun a b -> compare (Card.to_num a) (Card.to_num b)) (List.map (fun x -> Card.of_num x) (permutx))) in
    let _ = (game_status.nb_registres_restants <- ((rules.nb_registres_maximal ) - (List.length permutx))) in
    game_status
  |x::r->  (*la prochaine fifo devrait avoir une tille=x*)
    let list1 = Some(Fifo.of_list ((List.map (fun y -> Card.of_num y) (XpatRandom.sous_list 0 (x-1) permutx))) )in
    let permutx2 = XpatRandom.sous_list x (nb_cards -1) permutx in
    let _ = (game_status.colonnes <- (game_status.colonnes)@[list1]) in
    remplir_colonnes game_status permutx2 (nb_cards - x) r
  in
  (*vérifier si on doit mettre les rois au fond, puis renvoyer game_status*)
  let state = remplir_colonnes empty_state permut 52 rules.taille_init_colonnes in
  if(rules.emplacement_roi = PeuImporte) then state 
  else place_king_back state;;

  


let treat_game conf =
  (*génerer la permutation, rules, puis l'état initiale*)
  let permut = XpatRandom.shuffle conf.seed in 
  let rules = get_rules conf.game in
  let initialised_game_state = initialise_game rules permut in
  match conf.mode with
  |Search(filename) -> search initialised_game_state rules filename 
  |Check(filename) -> check  initialised_game_state rules filename ;;

let main () =
  Arg.parse
    [("-check", String (fun filename -> config.mode <- Check filename),
        "<filename>:\tValidate a solution file");
     ("-search", String (fun filename -> config.mode <- Search filename),
        "<filename>:\tSearch a solution and write it to a solution file")]
    set_game_seed (* pour les arguments seuls, sans option devant *)
    "XpatSolver <game>.<number> : search solution for Xpat2 game <number>";
  treat_game config

let _ = if not !Sys.interactive then main () else ()

