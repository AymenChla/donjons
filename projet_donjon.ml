open Graph.Pack.Graph;;

(* Quelques fonctions auxiliaires *)
let rec add_vertices g list_v =
    match list_v with
    | [] -> ()
    | t::q ->
        add_vertex g t;
        add_vertices g q;;

let rec add_edges g list_e =
    match list_e with
    | [] -> ()
    | t::q ->
        add_edge_e g t;
        add_edges g q;;

let true_copy g =
    let g_prime = Graph.Pack.Graph.create() in
    let sommets = fold_vertex (fun v l -> v::l) g [] in
    let edges = fold_edges_e (fun e l -> e::l) g [] in
    add_vertices g_prime sommets;
    add_edges g_prime edges;
    g_prime;;


(**********************************************************************)
(************************ PARTIE 1 ************************************)
(**********************************************************************)

(**================Fonction auxiliaires==================*)
let rec difference_liste_cle cles1 cles2 =
  match cles1 with 
  | [] -> []
  | t::q -> if List.mem t cles2 then (difference_liste_cle q cles2) else t::(difference_liste_cle q cles2) ;;
                        
(** Question 1:*)
(** Retourne la liste des sommets accessibles depuis un sommet s*)
let v_reach g s = 
  Mark.clear g;
  Mark.set s 1;
  let rec aux i =
    ( fold_succ (fun v lsucc -> if (Mark.get v) = 0 then let () = (Mark.set v 1) in (lsucc)@(aux v)  else lsucc) g i [i] )
  in aux s;
  ;;

(** Question 2:*)
(** renvoie la liste des couples (sommet des clé, liste des portes ouvertes par cette clé) qui sont atteignables depuis vi. *)
let cles_accessibles g vi cles =
  let lreach = (v_reach g vi) in 
  List.fold_right (fun (c,l) res -> if (List.mem c lreach) then (c,l)::res else res) cles []
  ;; 
  
(** Question 3:*)
(** Retourne une copie de g à laquelle elle ajoute les arêtes correspondant aux portes ouvertes par la clé*)
let ouvre_porte g cle = 
  let g' = true_copy g in 
    (add_edges g' (snd cle));
    g'
  ;;

(**auxiliaire: retourne une copie de g à laquelle elle ajoute les arêtes correspondant aux portes ouvertes par touts les clés*)
let ouvre_portes g cles = 
    List.fold_left (fun res cle -> ouvre_porte res cle) g cles
    ;;
  





(** Question 4:*)
(** renvoie un booléen indiquant si le donjon est faisable*)
let faisable gi vi vf cles =   
  let rec aux g cles_aux =
    if List.mem vf (v_reach g vi) then true 
    else
        let cles_acc = (cles_accessibles g vi cles_aux) in
        let g' = (ouvre_portes g cles_acc) in  
        if  (cles_accessibles gi vi cles_aux) <> (cles_accessibles g' vi cles_aux ) then 
          aux g' (difference_liste_cle cles_aux (cles_accessibles g vi cles_aux))
      else false 

  in aux gi cles
  ;;
      


(** Question 5:*)
(**auxiliaire: renvoie toutes les clés*)   
let rec getAllCles g vi cles acc = 
  let l = (cles_accessibles g vi cles) in
    match l with
    | [] -> acc
    | t::q -> getAllCles (ouvre_porte g t) vi q (acc@[fst(t)]) ;;

(** renvoie renvoie la liste des salles principales*)   
let parcours_salles_principales g vi vf cles = 
  let g' = true_copy g in 
  if (faisable g' vi vf cles) then 
    let rec aux gi cles_aux acc =
      let cles_acc = (cles_accessibles gi vi cles_aux) in 
            if List.mem vf (v_reach gi vi) then acc@[vf] 
            else 
                if (cles_accessibles g vi cles_aux) <> (cles_accessibles (ouvre_portes gi cles_acc) vi cles_aux ) then 
                aux (ouvre_portes gi cles_acc) (difference_liste_cle cles_aux (cles_accessibles gi vi cles_aux)) (getAllCles gi vi cles_aux acc)
            else [] 
    in aux g' cles [vi]
  else []
  ;;


(** Question 6:*)
      (**auxiliaire: transforme un arc en sommet*)
    let edge2Vertex g v edge = 
          let listesucc = succ g v in 
            let rec aux l = match l with 
                      | [] -> v
                      | t::q -> if (find_edge g v t) = edge then t
                                else aux q
            in aux listesucc;;

      (**auxiliaire: transforme des arcs en sommets*)
    let edges2vertexes g vi edges =
      let rec aux v edges_aux =
        match edges_aux with 
        | [] -> []
        | t::q ->  let x = edge2Vertex g v t in x::(aux x q)
      in aux vi edges;;

      (** renvoie la liste des salles à parcourir dans l’ordre pour atteindre le trésor*)     
    let parcours g vi vf cles = 
      let cles_acc = cles_accessibles g vi cles in
      let rec aux lv g_aux =
        match lv with
          | [] -> []
          | t::[] -> []
          | t1::t2::[] -> (edges2vertexes g_aux t1 (fst(shortest_path g_aux t1 t2)))
          | t1::t2::q -> let cles_acc_t2 = (cles_accessibles g_aux t2 cles) in (edges2vertexes g_aux t1  (fst(shortest_path g_aux t1 t2)))@(aux (t2::q) (ouvre_portes g_aux cles_acc_t2))

      in vi::(aux (parcours_salles_principales g vi vf cles) (ouvre_portes g cles_acc)) ;;

                
    




(**********************************************************************)
(************************ PARTIE 2 ************************************)
(**********************************************************************)




(**====== Etape 1: Création d'un graphe pour chaque état ======*)

                (** retourne les combinaison d'ordre n d'une liste*)
                let rec comb l n =
                  match l,n with
                  | _ , 0  -> [[]]
                  | [] , _ -> [] 
                  | t::q , _ -> List.append (List.map ( fun l -> t::l ) (comb q (n-1))) (comb q (n));;

                (** retourne les combinaisons d’états des n différentes couleurs d’interrupteurs disposés dans le donjon*)
                let comb_etats l =
                  let rec aux p =
                    match p with 
                    | 0 -> [[]]
                    | _ -> (comb l p)@(aux (p-1))
                  in aux (List.length l) ;;


                    
                (** regroupe les interrupteurs de même couleur*)
                  let rec add_inter cl licl = 
                    let (x,y) = cl in
                      match licl with 
                        | [] -> [([x],y)]
                        |(t,l)::q -> if y=l then (x::t,l)::q
                                    else  (t,l)::(add_inter cl q) ;;
                
                (** Transforme la liste d'interrupteur initiale en une liste regroupant les interrupteurs de même couleur*)
                  let rec regrouper_inters li = 
                    let rec aux l acc =
                      match l with
                      |[] -> acc 
                      |cl::q -> aux q (add_inter cl acc) 
                      in aux li []
                  ;;
                
                (** Retourne un graphe correspondant au changement d'etat apres l'appui sur un interrupteur*)  
                let appui_inter g g_prec inter =
                  let lportes = snd inter in 
                  let rec aux g' l =
                    match l with 
                    | [] -> g'
                    | t1::q -> if ( mem_edge_e g_prec t1 ) then (remove_edge_e g' t1; aux g' q;) 
                               else (add_edge_e g' t1;  aux g' q)
                in aux g lportes ;;
                
                (** Retourne un graphe correspondant au changement d'etat apres l'appui sur plusieurs interrupteurs*)  
                let appui_inters g inters =
                  let g' = true_copy g in
                  let rec aux gi inters' =
                      match inters' with 
                      | [] -> gi
                      | t::q -> aux (appui_inter gi g t) q
                in aux g' inters ;;


                (** Renvoie le nouveau label d'un vertex dans un graphe d'indice i*)
                let get_label g i label =
                  (nb_vertex g )*i + label ;;

                (* Etats des intérrepteurs d'un graphe  *)
                let rec etats_inter inters comb_etats =
                  match comb_etats with
                  | [] -> []
                  | t::q -> if List.mem t inters then (fst(t),1)::(etats_inter inters q) 
                            else (fst(t),0)::(etats_inter inters q) ;;


                (* Retourne une liste de graphes chaque graphe represente une combinaison d'états d'interrupteurs*)
                let liste_graphes_etats g inters =
                  let comb_etats = comb_etats (regrouper_inters inters) in
                  let rec aux l ig =
                    match l with 
                    | [] -> []
                    | t::q -> (etats_inter t (regrouper_inters inters),(appui_inters g t,ig))::(aux q (ig+1)) 
                  in aux comb_etats 0 ;;


                (* Retourne le graphe englobant tout les sommets des graphes (combinaison d'états) *)
                let graphe_final_sommet liste_graphes =
                  let rec aux g_final l =
                    match l with
                    | [] -> g_final
                    | (_ , (g,ig))::q -> iter_vertex (fun v ->let x = V.create (get_label g ig (V.label v)) in 
                                        add_vertex g_final x ) g ; aux g_final q 
                in aux (create ()) liste_graphes ;;

                (** Retourne le graphe englobant toutes les arêtes de chaque graphe d'état*)
                let graphe_final_edges g li =
                  let rec aux g_final l = 
                    match l with 
                    | [] -> g_final
                    | (_ , (g,p))::q -> iter_edges_e (fun e -> let (src,dest) = 
                      ( get_label g p (V.label (E.src e)),get_label g p (V.label (E.dst e))) in let (x,y) =
                      (E.create (find_vertex g_final src) 1 (find_vertex g_final dest),
                      E.create (find_vertex g_final dest) 1 (find_vertex g_final src)) in
                      add_edge_e g_final x ; add_edge_e g_final y  ) g ; aux g_final q
                  in aux g li ;;

                  
(**====== Etape 2: Ajout des transitions entres graphes correspondants ======*)

                (* Retourne un sommet de transition entre 2 états s'il la difference d'état et de 1*)
                let sommet_trans etat1 etat2 = 
                  let rec aux e1 e2 diff res =
                    match e1,e2 with 
                    | [],_
                    | _ ,[] -> if diff=1 then res else None
                    | (v,e1)::q1,(_,e2)::q2 -> if e1=e2 then (aux q1 q2 diff res) 
                                               else (aux q1 q2 (diff+1) (Some(v)))
                in aux etat1 etat2 0 None;;
                
                (** Ajout des transitions entre 2 graphes correspondants*)
                let rec ajout_trans g_final lv (g,ig1) (g2,ig2) =
                      match lv with 
                      | [] -> ()
                      | t::q ->  let label = V.label t in 
                                 let (label1,label2) = (get_label g ig1 label,get_label g2 ig2 label) in 
                                 let (x,y)=
                                      (E.create (find_vertex g_final label1) 1 (find_vertex g_final label2),E.create (find_vertex g_final label2) 1 (find_vertex g_final label1)) in
                                      add_edge_e g_final x ; add_edge_e g_final y; ajout_trans g_final q (g,ig1) (g2,ig2)
                                      ;;


                (** Ajout des transitions entres tous les graphes correspondants*)
                let graphe_final_trans g_final li =
                  let rec aux g_final l =
                    match l with 
                    | [] -> g_final
                    | (etat1 ,(g,p))::q -> List.fold_right (fun (etat2,(g2,p2)) () -> 
                                            match (sommet_trans etat1 etat2) with 
                                            | None -> ()
                                            | Some(lv) -> ajout_trans g_final lv (g,p) (g2,p2)
                                        )  q (); aux g_final q 
                    in aux g_final li ;;


                  (** Retoune la liste des sommets des états finaux dans le graphes final *)
                  let etats_finaux g_final g vf l_comb = 
                    let rec aux l acc p  =
                      match l with
                      | [] -> acc
                      | t::q -> aux q ((find_vertex g_final (get_label g p (V.label vf)))::acc ) (p+1)
                  in aux l_comb [] 0 ;;





(**====== Etape 3: — Algorithme de Dijkstra dans le graphe global ======*)
              
              (** Construit le graphe global et applique l'algorithme de dijsktra*)
              let faisable_interrupteurs gi vi vf inters =
                    let l_graphes = liste_graphes_etats gi inters in
                    let gf_v = graphe_final_sommet l_graphes in 
                    let gf_e = graphe_final_edges gf_v l_graphes in
                    let g_glob = graphe_final_trans gf_e l_graphes in 
                    let l_vf = etats_finaux g_glob gi vf l_graphes in
                    let vi = find_vertex g_glob (get_label gi ((List.length l_graphes)-1) (V.label vi)) in  
                        let rec aux l =
                          match l with 
                          | [] -> [],0
                          | t::q -> try (shortest_path g_glob vi t) with
                                            | Not_found ->  aux q
                                            | x -> (shortest_path g_glob vi t)
                    in aux l_vf;; 
      

  






