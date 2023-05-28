open Infer
open Infertypes
open Res

let () =
  let file = Sys.argv.(1) in
  let code = In_channel.with_open_bin file In_channel.input_all in
  let codes = Parse.implementation (Lexing.from_string code) in
  let ts =
    List.fold_left
      (fun acc s ->
        let* env = acc in
        top_infer env s)
      Preinit.get_env codes
  in
  let open Format in
  match ts with
  | Ok _ -> printf "types are correct"
  | Error err -> pp_err std_formatter err
