open MyGc
let assoc xs x =
  try
    Some (List.assoc x xs)
  with Not_found ->
    None

let nodes = [ "a"; "b"; "c"; "d"; "e" ];;
let mem = {
  roots  = [ "a" ];
  nodes  = nodes;
  frees  = [];
  marker = (fun _ -> Unmarked);
  pointer = (assoc [("a", "e"); ("e", "d")])
}

let dec x y = x = y;;

let of_list xs =
  Printf.sprintf "[ %s ]" (String.concat "; " xs)

let of_marker = function
    Marked -> "M"
  | Unmarked -> " "

let of_pointer = function
    Some n -> Printf.sprintf "-> %s" n
  | None -> ""

let show { roots  = roots;
	   nodes  = nodes;
	   frees  = frees;
	   marker = marker;
	   pointer = pointer; } =
  Printf.sprintf "ROOTS: %s\nFREES: %s\nNODES:\n%s"
    (of_list roots)
    (of_list frees)
    (String.concat "\n" (List.map (fun n ->
				     Printf.sprintf "%s %s %s"
				       (of_marker  (marker n))
				       n
				       (of_pointer (pointer n)))
			   nodes))
let _ =
  print_endline "=== init ===";
  print_endline (show mem);
  print_endline "";
  print_endline "=== mark ===";
  print_endline (show (markerPhase dec mem));
  print_endline "";
  print_endline "=== sweep ===";
  print_endline (show (gc dec mem));
