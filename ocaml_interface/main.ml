
let main () =
  let res = Checker.TestTranslation.check in
    Printf.fprintf stdout "%B\n%!" res;;


let _ = main ();;

