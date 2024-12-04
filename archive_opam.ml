let reason_field = "x-reason-for-archiving"

let commit_field = "x-opam-repository-commit-hash-at-time-of-archiving"

type reason =
  | OCaml_version
  | Source_unavailable
  | Maintenance_intent
  | Uninstallable

let reason_to_string = function
  | OCaml_version -> "ocaml-version"
  | Source_unavailable -> "source-unavailable"
  | Maintenance_intent -> "maintenance-intent"
  | Uninstallable -> "uninstallable"

let reason_of_string = function
  | "ocaml-version" -> Ok OCaml_version
  | "source-unavailable" -> Ok Source_unavailable
  | "maintenance-intent" -> Ok Maintenance_intent
  | "uninstallable" -> Ok Uninstallable
  | x -> Error (`Msg ("unknown reason: " ^ x))

let reason_enum = [
  "ocaml-version", OCaml_version ;
  "source-unavailable", Source_unavailable ;
  "maintenance-intent", Maintenance_intent ;
  "uninstallable", Uninstallable
]

module S = Set.Make(String)

(* This list has been generated by (in opam-repository at 9f34991c038ca38ca54a43232b9cae1c14a3f1e3):
   for x in $(git grep "source tarball not available" | cut -d '/' -f 3) ; do
     echo "\"$x\";";
   done

*)
let source_unavailable =
  S.of_list [
"amf.0.1.2";
"genet.0.6";
"glical.0.0.1";
"glical.0.0.2";
"glical.0.0.3";
"monocypher.0.1.0";
"mpp.0.1.0";
"mpp.0.1.1";
"mpp.0.1.2";
"mpp.0.1.3";
"mpp.0.1.4";
"mpp.0.1.5";
"mpp.0.1.7";
"mpp.0.1.8";
"mpp.0.2.0";
"mpp.0.2.1";
"mpp.0.3.0";
"ocamldot.1.0";
"ocf.0.1.0";
"ocf.0.3.0";
"ojs-base.0.1.0";
"qinap.1.0";
"rdf.0.9.0";
"rosa.0.1.0";
"sawja.1.5.4";
"stog-writing.0.8.0";
"stog.0.13.0";
"stog.0.4";
"taglog.0.1.0";
"taglog.0.2.0";
"taglog.0.3.0";
"toml.1.0.0";
"toml.2.0.0";
"toml.2.1.0";
]

let v_with_pos filename v =
  let pos = OpamParserTypes.FullPos.{ filename ; start = 0, 0 ; stop = 0, 0 } in
  OpamParserTypes.FullPos.{ pelem = v ; pos }

let pkg_name_and_version path =
  match List.rev (Fpath.segs path) with
  | _opam :: pkg_ver :: pkg :: _rest -> pkg, pkg_ver
  | _ -> assert false

let opam_archive commit reason deps fpath opam =
  let filename = Fpath.to_string fpath in
  let commit = v_with_pos filename (OpamParserTypes.FullPos.String commit) in
  let opam = OpamFile.OPAM.add_extension opam commit_field commit in
  let reason =
    let open OpamParserTypes.FullPos in
    let r = reason_to_string (reason fpath) in
    v_with_pos filename
      (List (v_with_pos filename ([ v_with_pos filename (String r) ] )))
  in
  let opam = OpamFile.OPAM.add_extension opam reason_field reason in
  let opam = OpamFile.OPAM.with_depends deps opam in
  (* remove potential available: false *)
  let opam =
    if match OpamFile.OPAM.available opam with
      | OpamTypes.FBool b -> b = false
      | _ -> false
    then
      OpamFile.OPAM.with_available (OpamTypes.FBool true) opam
    else
      opam
  in
  let opam =
    let flags = OpamFile.OPAM.flags opam in
    let flags = List.filter (function
        | OpamTypes.Pkgflag_AvoidVersion | Pkgflag_Deprecated -> false
        | _ -> true)
        flags
    in
    OpamFile.OPAM.with_flags flags opam
  in
  opam

let pp_pkg ppf fpath =
  let _, pkg_ver = pkg_name_and_version fpath in
  Fmt.string ppf pkg_ver

let pick_latest opams name =
  OpamPackage.Set.fold (fun pkg acc ->
      if OpamPackage.Name.equal pkg.OpamPackage.name name then
        match acc with
        | None, _ -> Some pkg, false
        | Some pkg', _ ->
          let str pkg = OpamPackage.to_string pkg in
          if OpamVersionCompare.compare (str pkg) (str pkg') <= 0 then
            Some pkg', true
          else
            Some pkg, true
      else
        acc) opams (None, false)

let string_of_relop = OpamPrinter.FullPos.relop_kind

let rec filter_to_string = function
  | OpamTypes.FBool b -> string_of_bool b
  | FString s -> s
  | FIdent (_opt_names, var, _env) ->
    "ident " ^ OpamVariable.to_string var
  | FOp (f, rel, g) ->
    filter_to_string f ^ " " ^ string_of_relop rel ^ " " ^ filter_to_string g
  | FAnd (f, g) ->
    filter_to_string f ^ " && " ^ filter_to_string g
  | FOr (f, g) ->
    filter_to_string f ^ " || " ^ filter_to_string g
  | FNot f -> "not " ^ filter_to_string f
  | FDefined f -> "defined " ^ filter_to_string f
  | FUndef f -> "undefined " ^ filter_to_string f

let f_to_string = function
  | OpamTypes.Filter filter -> "filter: " ^ filter_to_string filter
  | Constraint (relop, filter) ->
    string_of_relop relop ^ " " ^ filter_to_string filter

let adapt_deps no_upper_bound opams opam =
  let current_deps = OpamFile.OPAM.depends opam in
  let rec locked_deps = function
    | OpamFormula.Empty as a -> a
    | Atom (name, condition) ->
      if OpamPackage.Name.Set.mem name no_upper_bound then begin
        Atom (name, condition)
      end else begin
        match pick_latest opams name with
        | None, _ ->
          Logs.err (fun m -> m "couldn't find latest for %s"
                       (OpamPackage.Name.to_string name));
          Atom (name, condition)
        | Some { OpamPackage.version = highest ; _ }, multiple_versions ->
          (* this adds the <= highest constrain to the existing depends clause.
             now, we try to be smart:
             - if there's a {= X} constraint, we don't need to add anything
               (has_equal_constraint)
             - if there's a {< X} or {<= X} constraint where X is smaller or
               equal highest, we don't add anything (has_leq_lt_constraint)
             - if there's a {>= X} constraint where X = highest, we add {= X}
               (has_geq_constraint)

             Also, keep in mind that "multiple_versions" is true if there's only
             a single opam version. If this is the case, we use {= highest}
             instead.
          *)
          let h = OpamPackage.Version.to_string highest in
          let upper_bound, equal_bound =
            let op = if multiple_versions then `Leq else `Eq in
            let bound op = OpamTypes.(Atom (Constraint (op, FString h))) in
            bound op, bound `Eq
          in
          let has_equal_constraint = function
            | OpamTypes.(Atom (Constraint (`Eq, _))) (* = *) -> true
            | _ -> false
          and has_leq_lt_constraint = function
            | OpamTypes.(Atom (Constraint ((`Lt | `Leq), FString ver)))
              when OpamVersionCompare.compare ver h <= 0
              (* < X or <= X with X <= h *) -> true
            | _ -> false
          and has_geq_constraint = function
            | OpamTypes.(Atom (Constraint (`Geq, FString ver)))
              when OpamVersionCompare.compare ver h = 0
              (* >= X with X = h *) -> true
            | _ -> false
          in
          let add_to_condition = function
            | OpamTypes.Empty -> upper_bound
            | Atom (OpamTypes.Filter f) -> And (Atom (Filter f), upper_bound)
            | Atom (Constraint (relop, f)) as c ->
              if has_equal_constraint c || has_leq_lt_constraint c then
                (* there is = X or <= h, leave it alone *)
                Atom (Constraint (relop, f))
              else if has_geq_constraint c then
                (* there is >= h, add = h *)
                equal_bound
              else
                And (Atom (Constraint (relop, f)), upper_bound)
            | Block a ->
              if has_equal_constraint a || has_leq_lt_constraint a then
                (* there is = X or <= h, leave it alone *)
                Block a
              else if has_geq_constraint a then
                (* there is >= h, add = h *)
                Block equal_bound
              else
                Block (And (a, upper_bound))
            | And (a, b) ->
              (* there is = X or <= h in either part of the conjunction, leave
                 it alone *)
              if has_equal_constraint a || has_equal_constraint b
                 || has_leq_lt_constraint a || has_leq_lt_constraint b
              then
                And (a, b)
              else if has_geq_constraint a || has_geq_constraint b then
                (* there is >= h in either part of the conjunction, add = h *)
                equal_bound
              else
                And (And (a, b), upper_bound)
            | Or (a, b) -> And (Or (a, b), upper_bound)
          in
          let c' = add_to_condition condition in
          OpamFormula.Atom (name, c')
      end
    | Block x -> Block (locked_deps x)
    | And (a, b) -> And (locked_deps a, locked_deps b)
    | Or (a, b) -> Or (locked_deps a, locked_deps b)
  in
  locked_deps current_deps

let move reason no_upper_bound archive opams git_commit dry_run opam opam_fpath =
  let ( let* ) = Result.bind in
  let opams = OpamPackage.keys (Lazy.force opams) in
  let new_deps = adapt_deps no_upper_bound opams opam in
  let opam' = opam_archive git_commit reason new_deps opam_fpath opam in
  let pkg_name, pkg_ver = pkg_name_and_version opam_fpath in
  let target = Fpath.(v archive / "packages" / pkg_name / pkg_ver / "opam") in
  let old_opam = OpamFile.make (OpamFilename.raw (Fpath.to_string opam_fpath)) in
  let data = OpamFile.OPAM.to_string_with_preserved_format old_opam opam' in
  if dry_run then begin
    let* tmp = Bos.OS.File.tmp "new_opam_%s" in
    let* () = Bos.OS.File.write tmp data in
    let* diff, _ =
      let cmd =
        let color = match Fmt.style_renderer Fmt.stdout with
          | `Ansi_tty -> "always"
          | `None -> "never"
        in
        Bos.Cmd.(v "diff" % "-u" % ("--color=" ^ color) % p opam_fpath % p tmp)
      in
      Bos.OS.Cmd.(run_out cmd |> out_string)
    in
    Logs.info (fun m -> m "%s@.@." diff);
    Ok ()
  end else begin
    let* _ = Bos.OS.Dir.create (Fpath.parent target) in
    let* () = Bos.OS.File.write target data in
    let* () = Bos.OS.File.delete opam_fpath in
    let* () = Bos.OS.Dir.delete (Fpath.parent opam_fpath) in
    ignore (Bos.OS.Dir.delete (Fpath.parent (Fpath.parent opam_fpath)));
    Ok ()
  end

let opam_matches filter opam =
  match filter with
  | `Unavailable ->
    (* available: flags *)
    let available = match OpamFile.OPAM.available opam with
      | OpamTypes.FBool b -> b = false
      | _ -> false
    in
    (* flags: avoid-version | deprecated *)
    let avoid_version_or_deprecated =
      List.exists (function
          | OpamTypes.Pkgflag_AvoidVersion | Pkgflag_Deprecated -> true
          | _ -> false)
        (OpamFile.OPAM.flags opam)
    in
    available || avoid_version_or_deprecated
  | `Ocaml v ->
    (* should return true if there's an upper bound on ocaml <= v *)
    let ocaml_dep = OpamPackage.Name.of_string "ocaml" in
    let deps = OpamFile.OPAM.depends opam in
    let dep_matches op filter =
      match filter with
      | OpamTypes.FString ver ->
        begin
          match op with
          | `Lt -> OpamVersionCompare.compare ver v <= 0
          | `Leq | `Eq -> OpamVersionCompare.compare ver v < 0
          | _ -> false
        end
      | _ -> false
    in
    let rec walk_formula p = function
      | OpamTypes.Empty -> false
      | Atom f -> p f
      | Block formula -> walk_formula p formula
      | And (a, b) -> walk_formula p a || walk_formula p b
      | Or (a, b) -> walk_formula p a && walk_formula p b
    in
    let p = function
      | OpamTypes.Filter _ -> false
      | Constraint (op, filter) -> dep_matches op filter
    in
    let rec find_dep = function
      | OpamFormula.Empty -> false
      | Atom (name, cond) ->
        if OpamPackage.Name.equal ocaml_dep name then
          walk_formula p cond
        else
          false
      | Block x -> find_dep x
      | And (a, b) -> find_dep a || find_dep b
      | Or (a, b) -> find_dep a && find_dep b
    in
    find_dep deps

let jump () unavailable ocaml_lower_bound ignore_pkgs no_upper_bound
    opam_repository archive dry_run ignore_tezos pkgs reason =
  let ( let* ) = Result.bind in
  let pkg_dir = Fpath.(v opam_repository / "packages") in
  let* _ = Bos.OS.Dir.must_exist pkg_dir in
  let* git_commit =
    let cmd = Bos.Cmd.(v "git" % "rev-parse" % "HEAD") in
    Bos.OS.Cmd.(run_out cmd |> out_string ~trim:true |> success)
  in
  let* _ =
    if dry_run then
      Ok ()
    else
      let* _ = Bos.OS.Dir.must_exist (Fpath.v archive) in
      Ok ()
  in
  let opams =
    lazy
      (OpamRepositoryState.load_opams_from_dir
         (OpamRepositoryName.of_string "temporary")
         (OpamFilename.Dir.of_string opam_repository))
  in
  let no_upper_bound =
    OpamPackage.Name.Set.of_list
      (List.map OpamPackage.Name.of_string no_upper_bound)
  in
  let filter, default_reason =
    match unavailable, ocaml_lower_bound with
    | true, None -> `Unavailable, Uninstallable
    | false, Some v -> `Ocaml v, OCaml_version
    | false, None ->
      if pkgs = [] then
        failwith "neither unavailable nor lower bound nor packages specified"
      else
        `Package, Uninstallable
    | true, Some _ ->
      failwith "only either --unavailable or --ocaml bound allowed"
  in
  let reason =
    match reason with
    | None ->
      (fun fpath ->
         let _, pkg_name_ver = pkg_name_and_version fpath in
         if S.mem pkg_name_ver source_unavailable then
           Source_unavailable
         else
           default_reason)
    | Some reason -> (fun _fpath -> reason)
  in
  let ignored_pkgs = S.of_list ignore_pkgs
  and pkgs = S.of_list pkgs
  in
  let foreach path acc =
    let* () = acc in
    let move_it, opam =
      if Fpath.filename path = "opam" then
        let pkg_name, pkg_version = pkg_name_and_version path in
        if S.mem pkg_version ignored_pkgs || S.mem pkg_name ignored_pkgs then
          (Logs.info (fun m -> m "ignoring %a (--ignore)" pp_pkg path) ;
           false, None)
        else if ignore_tezos &&
                (String.starts_with ~prefix:"tezos" pkg_name
                 || String.starts_with ~prefix:"octez" pkg_name) then
          false, None
        else if S.is_empty pkgs || S.mem pkg_name pkgs || S.mem pkg_version pkgs then
          let opam =
            let opam_file =
              OpamFile.make (OpamFilename.raw (Fpath.to_string path))
            in
            OpamFile.OPAM.read opam_file
          in
          match filter with
          | `Unavailable | `Ocaml _ as f ->
            opam_matches f opam, Some opam
          | `Package ->
            true, Some opam
        else
          false, None
      else
        false, None
    in
    if move_it then begin
      Logs.app (fun m -> m "%a will be moved"
                   Fmt.(styled (`Fg `Red) pp_pkg) path);
      let opam = Option.get opam in
      let* () =
        move reason no_upper_bound archive opams git_commit dry_run opam path
      in
      Ok ()
    end else
      Ok ()
  in
  let* r = Bos.OS.Dir.fold_contents foreach (Ok ()) pkg_dir in
  r

let setup_log style_renderer level =
  Fmt_tty.setup_std_outputs ?style_renderer ();
  Logs.set_level level;
  Logs.set_reporter (Logs_fmt.reporter ~dst:Format.std_formatter ())

open Cmdliner

let setup_log =
  Term.(const setup_log
        $ Fmt_cli.style_renderer ()
        $ Logs_cli.level ())

let unavailable =
  let doc =
    "Filter unavailable packages: either the field 'available' is 'false' or \
     the field 'flags' contains either 'avoid-version' or 'deprecated')"
  in
  Arg.(value & flag & info ~doc ["unavailable"])

let ocaml_lower_bound =
  let doc = "Filter packages depending on OCaml smaller than X" in
  Arg.(value & opt (some string) None & info ~doc ["ocaml-lower-bound"])

let ignore_pkgs =
  let doc = "Ignore this package" in
  Arg.(value & opt_all string [ "arch-x86_32" ] & info ~doc ["ignore"])

let no_upper_bound =
  let doc = "Do not emit an upper bound for dependencies to this package" in
  Arg.(value & opt_all string ["ocaml"]  & info ~doc ["no-upper-bound"])

let opam_repository =
  let doc = "Opam repository directory to work on (must be a git checkout)" in
  Arg.(value & opt dir "." & info ~doc ["opam-repository"])

let opam_repository_archive =
  let doc = "Opam repository archive directory to work on" in
  Arg.(value & opt string "../opam-repository-archive" &
       info ~doc ~docv:"DIR" ["opam-repository-archive"])

let dry_run =
  let doc = "Do not modify anything, just print what would be done" in
  Arg.(value & flag & info ~doc ["dryrun" ; "dry-run"])

let ignore_tezos =
  let doc = "Ignore tezos and octez packages" in
  Arg.(value & flag & info ~doc ["ignore-tezos"])

let pkg =
  let doc = "Archive this package (may be package name or package.version)" in
  Arg.(value & opt_all string [] & info ~doc ["pkg"])

let reason =
  let doc =
    "Reason for archival (default is uninstallable). If ocaml-lower-bound is \
     provided, ocaml-version is used by default."
  in
  Arg.(value & opt (some (enum reason_enum)) None & info ~doc ["reason"])

let cmd =
  let info = Cmd.info "archive-opam" ~version:"%%VERSION_NUM%%"
  and term =
    Term.(term_result (const jump $ setup_log $ unavailable
                       $ ocaml_lower_bound $ ignore_pkgs $ no_upper_bound
                       $ opam_repository $ opam_repository_archive $ dry_run
                       $ ignore_tezos $ pkg $ reason))
  in
  Cmd.v info term

let () = exit (Cmd.eval cmd)
