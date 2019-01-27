open Graph.Pack

module type PrintGraph =
  sig
    type t
    module V : module type of Graph.V
    module E : sig
      type t
      type label = int
      val src : t -> V.t
      val dst : t -> V.t
      val label : t -> label
    end
    module Mark : sig
      val get : V.t -> int
    end

    val succ_e : t -> V.t -> E.t list
    val fold_vertex : (V.t -> 'a -> 'a) -> t -> 'a -> 'a
  end
  
module GraphPrinting (Gr : PrintGraph) =
  struct
    open Gr
(* ------------------- Fonctions d'affichage ------------------ *)

(* affiche_liste : (_,_,_,_,_,_) format6                        *)
(* 		 -> (Format.formatter -> 'a -> unit)            *)
(*   		 -> Format.formatter -> 'a list -> unit         *)
(* affiche les elements d'une liste avec la fonction f,         *)
(* separes par la chaine de formatage sep                       *)
let rec affiche_liste ~sep:sep f fmt =
  function
  | []   -> ()
  | [t]  -> Format.fprintf fmt "%a"
    	    		   f t
  | t::q -> Format.fprintf fmt "%a%(%)%a"
    	    		   f t
			   sep
			   (affiche_liste ~sep f) q;;

(* affiche_sommet : (_,_,_,_,_,_) format6                       *)
(*                -> Format.formatter -> V.t -> unit            *)
(* affiche le label d'un sommet v d'un graphe,                  *)
(* suivi d'une chaine de formatage trm                          *)
let affiche_sommet ?mark:(mark=false) ~trm:trm fmt v =
  if mark
  then
	Format.fprintf fmt "v_%i |-> %i%(%)" (V.label v) (Mark.get v) trm
  else
	Format.fprintf fmt "v_%i%(%)" (V.label v) trm;;

(* affiche_arete : (_,_,_,_,_,_) format6                        *)
(*               -> Format.formatter -> E.t -> unit             *)
(* affiche les sommets d'une arete e d'un graphe,               *)
(* suivi d'une chaine de formatage trm                          *)
let affiche_arete ~trm:trm fmt e =
  Format.fprintf fmt "%a -- %i -- > %a%(%)"
  		 (affiche_sommet ~mark:false ~trm:"") (E.src e)
		 (E.label e)
		 (affiche_sommet ~mark:false ~trm:"") (E.dst e)
		 trm;;

(* affiche un sommet v d'un graphe g et ses aretes sortantes,   *)
(* chacun suivi de la chaine de formatage trm                   *)
let affiche_sommet_et_aretes ~trm:trm g fmt v =
  Format.fprintf fmt "%a:%(%)  @[<v0>%a@]%(%)"
  		 (affiche_sommet ~mark:false ~trm:"") v
		 trm
		 (affiche_liste ~sep:"@," (affiche_arete ~trm:""))
		 	        (succ_e g v)
		 trm;;

(* affiche les sommets et les aretes sortantes d'un graphe g    *)
let affiche_graphe ~trm:trm fmt g =
  Format.fprintf fmt "{@[<v0>@,%a@]}"
  		 (affiche_liste ~sep:"" (affiche_sommet_et_aretes ~trm:"@," g))
		 		(fold_vertex (fun v q -> v::q) g []);;

type marked_t = Marked of t;;

(* affiche les sommets et les marques d'un graphe g             *)
let affiche_graphe_marque ~trm:trm fmt (Marked g) =
  Format.fprintf fmt "{@[<v0>@,%a@]}"
  		 (affiche_liste ~sep:"" (affiche_sommet ~mark:true ~trm:"@,"))
		 		(fold_vertex (fun v q -> v::q) g []);;
				
(*---------------------- Installation --------------------------*)
(* installe les procédures d'affichage de sommets et de graphes *)
(* dans l'interprète Ocaml                                      *)

let affiche_sommet_ocaml = affiche_sommet ~mark:false ~trm:"";;
let affiche_arete_ocaml = affiche_arete ~trm:"";;
let affiche_graphe_ocaml = affiche_graphe ~trm:"";;
let affiche_graphe_marque_ocaml = affiche_graphe_marque ~trm:"";;
  end

module PrintGraph = GraphPrinting (Graph)
module PrintDigraph = GraphPrinting (Digraph)

#install_printer PrintGraph.affiche_sommet_ocaml;;
#install_printer PrintGraph.affiche_arete_ocaml;;
#install_printer PrintGraph.affiche_graphe_ocaml;;
#install_printer PrintGraph.affiche_graphe_marque_ocaml;;

#install_printer PrintDigraph.affiche_sommet_ocaml;;
#install_printer PrintDigraph.affiche_arete_ocaml;;
#install_printer PrintDigraph.affiche_graphe_ocaml;;
#install_printer PrintDigraph.affiche_graphe_marque_ocaml;;
