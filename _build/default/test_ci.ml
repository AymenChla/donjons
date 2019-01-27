open Graph.Pack.Graph;;

let dj = Graph.Pack.Graph.create();;

let v_11 = V.create 11;;
add_vertex dj v_11;;
let v_12 = V.create 12;;
add_vertex dj v_12;;
let v_13 = V.create 13;;
add_vertex dj v_13;;

let e_11_12 = E.create v_11 1 v_12;;
let e_12_13 = E.create v_12 1 v_13;;
add_edge_e dj e_12_13;;
let e_12_11 = E.create v_12 1 v_11;;
let e_13_12 = E.create v_13 1 v_12;;
add_edge_e dj e_13_12;;

let doors = [ (v_12, [e_11_12; e_12_11]) ]

let vi = v_11;;

let vf = v_13;;
